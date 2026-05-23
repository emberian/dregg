//! Cross-federation promise pipelining for CapTP.
//!
//! In E-language parlance, promise pipelining allows sending messages to an
//! UNRESOLVED promise without waiting for resolution. The messages are queued
//! and delivered once the promise resolves — or propagated as broken if the
//! promise breaks. This eliminates round-trips in cross-federation communication.
//!
//! # Latency Win
//!
//! Without pipelining, a 3-step operation across federations requires 3 round trips:
//!
//! ```text
//! A → B: "give me X"
//! B → A: "here's X"             (round trip 1)
//! A → B: "call method on X"
//! B → A: "result"               (round trip 2)
//! A → B: "call another method"
//! B → A: "result"               (round trip 3)
//! ```
//!
//! With pipelining, all 3 steps are batched in ONE message:
//!
//! ```text
//! A → B: [pipeline_msg_1, pipeline_msg_2, pipeline_msg_3]
//! B → A: "final result"         (ONE round trip)
//! ```
//!
//! # Architecture
//!
//! - [`PipelineRegistry`] queues messages for unresolved promises and resolves them.
//! - [`PipelineWireMessage`] defines the cross-federation wire format.
//! - [`CrossFedPipelineBridge`] bridges the local `PendingTurnRegistry` with
//!   per-peer pipeline registries.

use std::collections::HashMap;

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::FederationId;

// =============================================================================
// Core types
// =============================================================================

/// A pipelined message: sent to an unresolved promise.
///
/// The message is queued until the promise resolves, then delivered to the
/// resolved cell. If the promise breaks, the failure cascades to the
/// `result_promise_id` (if any).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PipelinedMessage {
    /// The promise this message targets (an EventualRef on the remote side).
    pub target_promise_id: u64,
    /// The action to execute once the promise resolves.
    pub action: PipelinedAction,
    /// Where to send the result (a promise on the SENDER's side).
    /// If `None`, the result is discarded (fire-and-forget).
    pub result_promise_id: Option<u64>,
    /// The federation that sent this pipelined message.
    pub sender: FederationId,
}

/// An action to execute on a resolved capability.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PipelinedAction {
    /// The method to invoke on the resolved cell.
    pub method: String,
    /// Serialized action arguments (opaque bytes; the receiver deserializes).
    pub args: Vec<u8>,
    /// Serialized authorization proving the sender's right to invoke this action.
    pub authorization: Vec<u8>,
}

/// The state of a promise in the pipeline registry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PipelinePromiseState {
    /// The promise has not yet resolved.
    Pending,
    /// The promise resolved to a concrete cell.
    Fulfilled { resolved_cell: CellId },
    /// The promise was broken; no delivery will occur.
    Broken { reason: String },
}

/// A notification that a pipelined result promise has been broken due to
/// cascading failure from an upstream promise.
#[derive(Clone, Debug)]
pub struct BrokenPromiseNotification {
    /// The promise ID that was broken (the `result_promise_id` of a queued message).
    pub promise_id: u64,
    /// The reason for the breakage.
    pub reason: String,
    /// The federation that should be notified (the original sender).
    pub notify_federation: FederationId,
}

/// Errors from pipeline operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    /// The target promise does not exist in this registry.
    PromiseNotFound { promise_id: u64 },
    /// The target promise has already been broken — cannot pipeline to it.
    PromiseAlreadyBroken { promise_id: u64, reason: String },
    /// An empty chain was provided (need at least one step).
    EmptyChain,
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PipelineError::PromiseNotFound { promise_id } => {
                write!(f, "promise {promise_id} not found in pipeline registry")
            }
            PipelineError::PromiseAlreadyBroken { promise_id, reason } => {
                write!(f, "promise {promise_id} already broken: {reason}")
            }
            PipelineError::EmptyChain => write!(f, "pipeline chain must have at least one step"),
        }
    }
}

impl std::error::Error for PipelineError {}

// =============================================================================
// Pipeline Registry
// =============================================================================

/// The pipeline registry: queues messages for unresolved promises and delivers
/// them upon resolution, or cascades failure upon breakage.
///
/// Each peer federation has its own `PipelineRegistry` — messages are queued
/// per-promise and delivered in order when the promise resolves.
#[derive(Clone, Debug)]
pub struct PipelineRegistry {
    /// Messages waiting for promise resolution, keyed by target promise ID.
    queued: HashMap<u64, Vec<PipelinedMessage>>,
    /// Promise states (pending, fulfilled, broken).
    promises: HashMap<u64, PipelinePromiseState>,
    /// Next promise ID to allocate.
    next_id: u64,
}

impl PipelineRegistry {
    /// Create a new, empty pipeline registry.
    pub fn new() -> Self {
        Self {
            queued: HashMap::new(),
            promises: HashMap::new(),
            next_id: 0,
        }
    }

    /// Create a new pending promise. Returns the promise ID.
    ///
    /// This is called when we send an eventual message to a remote federation
    /// and need a local handle for the result.
    pub fn create_promise(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.promises.insert(id, PipelinePromiseState::Pending);
        self.queued.insert(id, Vec::new());
        id
    }

    /// Queue a pipelined message for an unresolved promise.
    ///
    /// If the promise is already fulfilled, returns `Ok(())` but the caller
    /// should use [`resolve_promise`](Self::resolve_promise) results instead.
    /// If the promise is already broken, returns an error immediately.
    /// If the promise is pending, the message is queued for later delivery.
    pub fn pipeline_message(&mut self, msg: PipelinedMessage) -> Result<(), PipelineError> {
        let target = msg.target_promise_id;

        match self.promises.get(&target) {
            None => {
                return Err(PipelineError::PromiseNotFound { promise_id: target });
            }
            Some(PipelinePromiseState::Broken { reason }) => {
                return Err(PipelineError::PromiseAlreadyBroken {
                    promise_id: target,
                    reason: reason.clone(),
                });
            }
            Some(PipelinePromiseState::Fulfilled { .. }) => {
                // Promise already resolved — queue it anyway; caller should
                // drain via resolve_promise or use pipeline_to_resolved.
                self.queued.entry(target).or_default().push(msg);
                return Ok(());
            }
            Some(PipelinePromiseState::Pending) => {
                self.queued.entry(target).or_default().push(msg);
            }
        }
        Ok(())
    }

    /// Resolve a promise — mark it fulfilled and return all queued messages.
    ///
    /// The caller is responsible for delivering the returned messages to the
    /// resolved cell (e.g., by converting them into turns for the executor).
    pub fn resolve_promise(
        &mut self,
        promise_id: u64,
        resolved_cell: CellId,
    ) -> Vec<PipelinedMessage> {
        // Mark fulfilled.
        if let Some(state) = self.promises.get_mut(&promise_id) {
            *state = PipelinePromiseState::Fulfilled { resolved_cell };
        }

        // Drain queued messages.
        self.queued.remove(&promise_id).unwrap_or_default()
    }

    /// Break a promise — mark it broken and propagate failure to all waiting
    /// messages' result promises (cascading breakage).
    ///
    /// Returns notifications for each result promise that must be broken on
    /// the sender's side.
    pub fn break_promise(
        &mut self,
        promise_id: u64,
        reason: String,
    ) -> Vec<BrokenPromiseNotification> {
        // Mark broken.
        if let Some(state) = self.promises.get_mut(&promise_id) {
            *state = PipelinePromiseState::Broken {
                reason: reason.clone(),
            };
        }

        // Drain queued messages and cascade breakage.
        let messages = self.queued.remove(&promise_id).unwrap_or_default();
        let mut notifications = Vec::new();

        for msg in messages {
            if let Some(result_id) = msg.result_promise_id {
                let cascade_reason = format!("upstream promise {} broken: {}", promise_id, reason);

                notifications.push(BrokenPromiseNotification {
                    promise_id: result_id,
                    reason: cascade_reason.clone(),
                    notify_federation: msg.sender,
                });

                // If the result promise is also in THIS registry (local chain),
                // recursively break it.
                if self.promises.contains_key(&result_id) {
                    let inner = self.break_promise(result_id, cascade_reason);
                    notifications.extend(inner);
                }
            }
        }

        notifications
    }

    /// Pipeline a CHAIN of actions: each step targets the previous step's result.
    ///
    /// Creates intermediate promises for each step in the chain, queues each
    /// step targeting the previous step's result promise, and returns the final
    /// promise ID (representing the output of the last step).
    ///
    /// The `initial_promise_id` is the promise that the first step targets.
    /// The `sender` is the federation originating the chain.
    pub fn pipeline_chain(
        &mut self,
        initial_promise_id: u64,
        steps: Vec<PipelinedAction>,
        sender: FederationId,
    ) -> Result<u64, PipelineError> {
        if steps.is_empty() {
            return Err(PipelineError::EmptyChain);
        }

        // Verify the initial promise exists and is not broken.
        match self.promises.get(&initial_promise_id) {
            None => {
                return Err(PipelineError::PromiseNotFound {
                    promise_id: initial_promise_id,
                });
            }
            Some(PipelinePromiseState::Broken { reason }) => {
                return Err(PipelineError::PromiseAlreadyBroken {
                    promise_id: initial_promise_id,
                    reason: reason.clone(),
                });
            }
            _ => {}
        }

        let mut current_target = initial_promise_id;

        for action in steps {
            // Create a promise for this step's result.
            let result_promise = self.create_promise();

            // Queue this step targeting the current target.
            let msg = PipelinedMessage {
                target_promise_id: current_target,
                action,
                result_promise_id: Some(result_promise),
                sender,
            };
            // We already verified the initial promise is valid, and intermediate
            // promises are freshly created (Pending), so this won't fail.
            let _ = self.pipeline_message(msg);

            // The next step targets this step's result.
            current_target = result_promise;
        }

        Ok(current_target)
    }

    /// Get the current state of a promise.
    pub fn promise_state(&self, promise_id: u64) -> Option<&PipelinePromiseState> {
        self.promises.get(&promise_id)
    }

    /// Returns the number of messages queued for a given promise.
    pub fn queued_count(&self, promise_id: u64) -> usize {
        self.queued.get(&promise_id).map_or(0, |q| q.len())
    }

    /// Returns the total number of tracked promises.
    pub fn promise_count(&self) -> usize {
        self.promises.len()
    }
}

impl Default for PipelineRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Wire Messages
// =============================================================================

/// Wire messages for cross-federation promise pipelining.
///
/// These are the messages exchanged between federations to coordinate
/// promise resolution and pipelined message delivery.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PipelineWireMessage {
    /// "I'm sending a pipelined message to a promise on your side."
    ///
    /// The receiver queues this message until the promise resolves.
    PipelineToPromise {
        /// The promise ID (on the RECEIVER's side) to target.
        promise_id: u64,
        /// The action to execute when the promise resolves.
        action: PipelinedAction,
        /// A promise ID on the SENDER's side where the result should be sent.
        result_promise_id: Option<u64>,
        /// The federation sending this pipelined message.
        sender_federation: FederationId,
    },

    /// "That promise I told you about? It resolved to this cell."
    ///
    /// The receiver should deliver all queued messages targeting this promise
    /// to the resolved cell.
    PromiseResolved {
        /// The promise ID that resolved.
        promise_id: u64,
        /// The cell that the promise resolved to.
        resolved_cell: CellId,
    },

    /// "That promise broke. Propagate failure."
    ///
    /// The receiver should break the promise and cascade failure to all
    /// messages queued against it.
    PromiseBroken {
        /// The promise ID that broke.
        promise_id: u64,
        /// Why the promise broke.
        reason: String,
    },

    /// "Here's the result of a pipelined message you sent me."
    ///
    /// The receiver should resolve or break the indicated result promise.
    PipelineResult {
        /// The result_promise_id from the original PipelineToPromise message.
        original_result_promise_id: u64,
        /// The result of executing the pipelined action.
        result: PipelineResultValue,
    },
}

/// The result of executing a pipelined action.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PipelineResultValue {
    /// The action succeeded; the result is a cell.
    Success {
        /// The cell produced by the action.
        cell_id: CellId,
        /// BLAKE3 hash of the execution receipt (for auditability).
        receipt_hash: [u8; 32],
    },
    /// The action failed.
    Failure {
        /// Description of why the action failed.
        error: String,
    },
}

// =============================================================================
// Cross-Federation Bridge
// =============================================================================

/// Bridge between local promise tracking and cross-federation pipeline registries.
///
/// Each remote peer gets its own `PipelineRegistry` instance. The bridge
/// coordinates creating local promises for remote results and dispatching
/// incoming resolutions.
#[derive(Clone, Debug)]
pub struct CrossFedPipelineBridge {
    /// Per-peer pipeline registries (messages WE have queued for THEIR promises).
    peers: HashMap<FederationId, PipelineRegistry>,
    /// Local promise registry (promises that WE own, awaiting results from peers).
    local: PipelineRegistry,
    /// Outbound message queue: wire messages that need to be sent to peers.
    /// The networking layer should drain this after each operation.
    outbox: Vec<(FederationId, PipelineWireMessage)>,
}

impl CrossFedPipelineBridge {
    /// Create a new bridge with no connected peers.
    pub fn new() -> Self {
        Self {
            peers: HashMap::new(),
            local: PipelineRegistry::new(),
            outbox: Vec::new(),
        }
    }

    /// Send a pipelined message to a remote federation's promise.
    ///
    /// Creates a LOCAL promise for the result (so the caller can pipeline MORE
    /// onto that result) and enqueues a wire message for the target federation.
    ///
    /// Returns the local promise ID representing the eventual result.
    pub fn pipeline_to_remote(
        &mut self,
        target_federation: FederationId,
        promise_id: u64,
        action: PipelinedAction,
    ) -> u64 {
        // Create a local promise for the result of this pipelined action.
        let local_result_promise = self.local.create_promise();

        // Enqueue the wire message.
        self.outbox.push((
            target_federation,
            PipelineWireMessage::PipelineToPromise {
                promise_id,
                action,
                result_promise_id: Some(local_result_promise),
                sender_federation: self.local_federation_placeholder(),
            },
        ));

        local_result_promise
    }

    /// Pipeline a chain of actions to a remote federation.
    ///
    /// The first action targets `initial_promise_id` on the remote.
    /// Each subsequent action targets the result of the previous action.
    /// All steps are batched in a single message burst.
    ///
    /// Returns the local promise ID for the final step's result.
    pub fn pipeline_chain_to_remote(
        &mut self,
        target_federation: FederationId,
        initial_promise_id: u64,
        steps: Vec<PipelinedAction>,
    ) -> Result<u64, PipelineError> {
        if steps.is_empty() {
            return Err(PipelineError::EmptyChain);
        }

        let local_federation = self.local_federation_placeholder();
        let mut current_remote_promise = initial_promise_id;
        let mut final_local_promise = 0;

        for (i, action) in steps.into_iter().enumerate() {
            let local_result = self.local.create_promise();
            final_local_promise = local_result;

            // For intermediate steps, the remote also needs a promise for the
            // next step to target. We communicate this via result_promise_id.
            // The remote will create a corresponding promise and link them.
            self.outbox.push((
                target_federation,
                PipelineWireMessage::PipelineToPromise {
                    promise_id: current_remote_promise,
                    action,
                    result_promise_id: Some(local_result),
                    sender_federation: local_federation,
                },
            ));

            // For subsequent steps, the remote promise is the result of this step.
            // We use a convention: the remote creates a promise for each
            // PipelineToPromise message and its ID equals the result_promise_id.
            // This is handled by the receiving side's on_pipeline_message.
            current_remote_promise = local_result;
            let _ = i; // suppress unused warning
        }

        Ok(final_local_promise)
    }

    /// Handle an incoming promise resolution from a remote peer.
    ///
    /// This resolves our local promise and returns any messages that were
    /// queued against it (which may trigger further local turns).
    pub fn on_remote_resolution(
        &mut self,
        _from: FederationId,
        promise_id: u64,
        cell: CellId,
    ) -> Vec<PipelinedMessage> {
        self.local.resolve_promise(promise_id, cell)
    }

    /// Handle an incoming promise breakage from a remote peer.
    ///
    /// This breaks our local promise and cascades to any pipelined messages
    /// that depended on it.
    pub fn on_remote_breakage(
        &mut self,
        _from: FederationId,
        promise_id: u64,
        reason: String,
    ) -> Vec<BrokenPromiseNotification> {
        self.local.break_promise(promise_id, reason)
    }

    /// Handle an incoming PipelineToPromise message from a peer.
    ///
    /// This is called on the RECEIVING side: a peer wants to send a message
    /// to one of OUR promises. We queue it in the appropriate peer registry.
    pub fn on_pipeline_message(
        &mut self,
        from: FederationId,
        promise_id: u64,
        action: PipelinedAction,
        result_promise_id: Option<u64>,
    ) -> Result<(), PipelineError> {
        let registry = self.peers.entry(from).or_insert_with(PipelineRegistry::new);

        // Ensure the promise exists in the peer's registry.
        // If it doesn't, it might be a promise we track in our local registry.
        // Try local first.
        if self.local.promises.contains_key(&promise_id) {
            let msg = PipelinedMessage {
                target_promise_id: promise_id,
                action,
                result_promise_id,
                sender: from,
            };
            return self.local.pipeline_message(msg);
        }

        // Otherwise, ensure it exists in the peer registry.
        if !registry.promises.contains_key(&promise_id) {
            // Implicitly create the promise — the remote knows about a promise
            // we don't track yet (it was created on their side).
            registry
                .promises
                .insert(promise_id, PipelinePromiseState::Pending);
            registry.queued.insert(promise_id, Vec::new());
        }

        let msg = PipelinedMessage {
            target_promise_id: promise_id,
            action,
            result_promise_id,
            sender: from,
        };
        registry.pipeline_message(msg)
    }

    /// Handle an incoming PipelineResult from a peer (the result of a pipelined
    /// action we sent them).
    pub fn on_pipeline_result(
        &mut self,
        _from: FederationId,
        original_result_promise_id: u64,
        result: PipelineResultValue,
    ) -> Vec<PipelinedMessage> {
        match result {
            PipelineResultValue::Success {
                cell_id,
                receipt_hash: _,
            } => self
                .local
                .resolve_promise(original_result_promise_id, cell_id),
            PipelineResultValue::Failure { error } => {
                self.local.break_promise(original_result_promise_id, error);
                Vec::new()
            }
        }
    }

    /// Resolve a local promise (e.g., a turn we executed completed).
    ///
    /// Returns messages from any peer that pipelined to this promise.
    pub fn resolve_local_promise(
        &mut self,
        promise_id: u64,
        cell: CellId,
    ) -> Vec<PipelinedMessage> {
        // Check all peer registries for messages targeting this promise.
        let mut all_messages = Vec::new();

        for registry in self.peers.values_mut() {
            if registry.promises.contains_key(&promise_id) {
                let msgs = registry.resolve_promise(promise_id, cell);
                all_messages.extend(msgs);
            }
        }

        // Also resolve in local registry (if we have self-pipelined messages).
        let local_msgs = self.local.resolve_promise(promise_id, cell);
        all_messages.extend(local_msgs);

        all_messages
    }

    /// Break a local promise (e.g., a turn we executed failed).
    ///
    /// Cascades failure to any messages pipelined against this promise.
    pub fn break_local_promise(
        &mut self,
        promise_id: u64,
        reason: String,
    ) -> Vec<BrokenPromiseNotification> {
        let mut all_notifications = Vec::new();

        for registry in self.peers.values_mut() {
            if registry.promises.contains_key(&promise_id) {
                let notifs = registry.break_promise(promise_id, reason.clone());
                all_notifications.extend(notifs);
            }
        }

        let local_notifs = self.local.break_promise(promise_id, reason);
        all_notifications.extend(local_notifs);

        all_notifications
    }

    /// Drain the outbox of wire messages to send to peers.
    ///
    /// The networking layer should call this after each operation and dispatch
    /// the messages to the appropriate federations.
    pub fn drain_outbox(&mut self) -> Vec<(FederationId, PipelineWireMessage)> {
        std::mem::take(&mut self.outbox)
    }

    /// Get a reference to the local pipeline registry.
    pub fn local_registry(&self) -> &PipelineRegistry {
        &self.local
    }

    /// Get a mutable reference to the local pipeline registry.
    pub fn local_registry_mut(&mut self) -> &mut PipelineRegistry {
        &mut self.local
    }

    /// Get a reference to a peer's pipeline registry (if it exists).
    pub fn peer_registry(&self, peer: &FederationId) -> Option<&PipelineRegistry> {
        self.peers.get(peer)
    }

    /// Placeholder: in a real deployment, the bridge would be configured with
    /// the local federation's ID. For now, returns a zero ID.
    fn local_federation_placeholder(&self) -> FederationId {
        FederationId([0u8; 32])
    }
}

impl Default for CrossFedPipelineBridge {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_action(method: &str) -> PipelinedAction {
        PipelinedAction {
            method: method.to_string(),
            args: vec![],
            authorization: vec![],
        }
    }

    fn fed_a() -> FederationId {
        FederationId([0xAA; 32])
    }

    fn fed_b() -> FederationId {
        FederationId([0xBB; 32])
    }

    fn cell(byte: u8) -> CellId {
        CellId([byte; 32])
    }

    // ─── Test 1: Create promise → pipeline message → resolve → message delivered ──

    #[test]
    fn pipeline_message_delivered_on_resolution() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();

        let msg = PipelinedMessage {
            target_promise_id: p,
            action: make_action("set_balance"),
            result_promise_id: Some(99),
            sender: fed_a(),
        };
        reg.pipeline_message(msg).unwrap();

        assert_eq!(reg.queued_count(p), 1);

        // Resolve the promise.
        let delivered = reg.resolve_promise(p, cell(0x11));
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].action.method, "set_balance");
        assert_eq!(delivered[0].result_promise_id, Some(99));

        // Queue is now empty.
        assert_eq!(reg.queued_count(p), 0);
    }

    // ─── Test 2: Break promise → cascading break to pipelined result promises ──

    #[test]
    fn break_promise_cascades_to_result_promises() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();
        let result_p = reg.create_promise();

        let msg = PipelinedMessage {
            target_promise_id: p,
            action: make_action("do_thing"),
            result_promise_id: Some(result_p),
            sender: fed_a(),
        };
        reg.pipeline_message(msg).unwrap();

        // Break the target promise.
        let notifications = reg.break_promise(p, "remote disconnected".into());

        // We should get a notification about the result promise being broken.
        assert!(!notifications.is_empty());
        assert!(notifications.iter().any(|n| n.promise_id == result_p));

        // The result promise itself should now be broken.
        assert!(matches!(
            reg.promise_state(result_p),
            Some(PipelinePromiseState::Broken { .. })
        ));
    }

    // ─── Test 3: Pipeline chain (3 steps) → resolve first → all cascade ──

    #[test]
    fn pipeline_chain_resolves_in_sequence() {
        let mut reg = PipelineRegistry::new();
        let initial = reg.create_promise();

        let steps = vec![
            make_action("step_1"),
            make_action("step_2"),
            make_action("step_3"),
        ];

        let final_promise = reg.pipeline_chain(initial, steps, fed_a()).unwrap();

        // We should have: initial + 3 intermediate promises = 4 total.
        assert_eq!(reg.promise_count(), 4);

        // Resolve the initial promise → delivers step_1.
        let step1_msgs = reg.resolve_promise(initial, cell(0x01));
        assert_eq!(step1_msgs.len(), 1);
        assert_eq!(step1_msgs[0].action.method, "step_1");

        // The result of step_1 is a promise. Resolve it → delivers step_2.
        let step1_result = step1_msgs[0].result_promise_id.unwrap();
        let step2_msgs = reg.resolve_promise(step1_result, cell(0x02));
        assert_eq!(step2_msgs.len(), 1);
        assert_eq!(step2_msgs[0].action.method, "step_2");

        // Resolve step_2's result → delivers step_3.
        let step2_result = step2_msgs[0].result_promise_id.unwrap();
        let step3_msgs = reg.resolve_promise(step2_result, cell(0x03));
        assert_eq!(step3_msgs.len(), 1);
        assert_eq!(step3_msgs[0].action.method, "step_3");

        // step_3's result is the final promise.
        assert_eq!(step3_msgs[0].result_promise_id, Some(final_promise));
    }

    // ─── Test 4: Cross-federation: pipeline to remote → remote resolves → result flows back ──

    #[test]
    fn cross_federation_pipeline_and_resolution() {
        let mut bridge = CrossFedPipelineBridge::new();

        // Pipeline an action to federation B's promise #42.
        let local_promise = bridge.pipeline_to_remote(fed_b(), 42, make_action("get_balance"));

        // We should have an outbound wire message.
        let outbox = bridge.drain_outbox();
        assert_eq!(outbox.len(), 1);
        assert_eq!(outbox[0].0, fed_b());
        match &outbox[0].1 {
            PipelineWireMessage::PipelineToPromise {
                promise_id,
                action,
                result_promise_id,
                ..
            } => {
                assert_eq!(*promise_id, 42);
                assert_eq!(action.method, "get_balance");
                assert_eq!(*result_promise_id, Some(local_promise));
            }
            _ => panic!("expected PipelineToPromise"),
        }

        // The local promise should be pending.
        assert!(matches!(
            bridge.local_registry().promise_state(local_promise),
            Some(PipelinePromiseState::Pending)
        ));

        // Simulate the remote resolving our result.
        let delivered = bridge.on_remote_resolution(fed_b(), local_promise, cell(0xFF));
        // No messages were pipelined to the local promise, so nothing delivered.
        assert!(delivered.is_empty());

        // The local promise should now be fulfilled.
        assert!(matches!(
            bridge.local_registry().promise_state(local_promise),
            Some(PipelinePromiseState::Fulfilled { resolved_cell }) if *resolved_cell == cell(0xFF)
        ));
    }

    // ─── Test 5: Concurrent pipelines to same promise → all delivered on resolution ──

    #[test]
    fn concurrent_pipelines_to_same_promise() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();

        // Queue 3 messages to the same promise.
        for method in &["alpha", "beta", "gamma"] {
            let msg = PipelinedMessage {
                target_promise_id: p,
                action: make_action(method),
                result_promise_id: None,
                sender: fed_a(),
            };
            reg.pipeline_message(msg).unwrap();
        }

        assert_eq!(reg.queued_count(p), 3);

        // Resolve: all 3 should be delivered.
        let delivered = reg.resolve_promise(p, cell(0x22));
        assert_eq!(delivered.len(), 3);

        let methods: Vec<&str> = delivered.iter().map(|m| m.action.method.as_str()).collect();
        assert_eq!(methods, vec!["alpha", "beta", "gamma"]);
    }

    // ─── Test 6: Pipeline to already-resolved promise → immediate delivery ──

    #[test]
    fn pipeline_to_already_resolved_promise() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();

        // Resolve first.
        reg.resolve_promise(p, cell(0x33));

        // Now pipeline to it — the message is queued (for drain).
        let msg = PipelinedMessage {
            target_promise_id: p,
            action: make_action("late_arrival"),
            result_promise_id: None,
            sender: fed_a(),
        };
        let result = reg.pipeline_message(msg);
        assert!(result.is_ok());

        // The message is in the queue (caller should drain resolved promises).
        assert_eq!(reg.queued_count(p), 1);

        // Calling resolve_promise again drains it (idempotent delivery).
        let delivered = reg.resolve_promise(p, cell(0x33));
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].action.method, "late_arrival");
    }

    // ─── Test 7: Pipeline to broken promise → immediate failure propagation ──

    #[test]
    fn pipeline_to_broken_promise_fails_immediately() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();

        // Break the promise.
        reg.break_promise(p, "timeout".into());

        // Attempt to pipeline to it.
        let msg = PipelinedMessage {
            target_promise_id: p,
            action: make_action("too_late"),
            result_promise_id: Some(99),
            sender: fed_a(),
        };
        let result = reg.pipeline_message(msg);
        assert!(matches!(
            result,
            Err(PipelineError::PromiseAlreadyBroken { promise_id, .. }) if promise_id == p
        ));
    }

    // ─── Test 8: Pipeline to nonexistent promise → error ──

    #[test]
    fn pipeline_to_nonexistent_promise_errors() {
        let mut reg = PipelineRegistry::new();

        let msg = PipelinedMessage {
            target_promise_id: 999,
            action: make_action("nope"),
            result_promise_id: None,
            sender: fed_a(),
        };
        let result = reg.pipeline_message(msg);
        assert!(matches!(
            result,
            Err(PipelineError::PromiseNotFound { promise_id: 999 })
        ));
    }

    // ─── Test 9: Chain with break at step 2 → step 3 cascades ──

    #[test]
    fn chain_break_cascades_through_steps() {
        let mut reg = PipelineRegistry::new();
        let initial = reg.create_promise();

        let steps = vec![
            make_action("step_1"),
            make_action("step_2"),
            make_action("step_3"),
        ];

        let final_promise = reg.pipeline_chain(initial, steps, fed_a()).unwrap();

        // Resolve initial → delivers step_1.
        let step1_msgs = reg.resolve_promise(initial, cell(0x01));
        let step1_result = step1_msgs[0].result_promise_id.unwrap();

        // Break step_1's result → should cascade to step_2 and step_3.
        let notifications = reg.break_promise(step1_result, "execution failed".into());

        // We should have cascading notifications.
        assert!(!notifications.is_empty());

        // The final promise should be broken.
        assert!(matches!(
            reg.promise_state(final_promise),
            Some(PipelinePromiseState::Broken { .. })
        ));
    }

    // ─── Test 10: CrossFedPipelineBridge incoming pipeline message ──

    #[test]
    fn bridge_incoming_pipeline_message() {
        let mut bridge = CrossFedPipelineBridge::new();

        // Create a local promise that a peer will pipeline to.
        let local_p = bridge.local_registry_mut().create_promise();

        // Peer A sends a pipelined message to our promise.
        bridge
            .on_pipeline_message(fed_a(), local_p, make_action("remote_call"), Some(77))
            .unwrap();

        // Resolve the local promise → delivers the pipelined message.
        let delivered = bridge.resolve_local_promise(local_p, cell(0x44));
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].action.method, "remote_call");
        assert_eq!(delivered[0].result_promise_id, Some(77));
        assert_eq!(delivered[0].sender, fed_a());
    }

    // ─── Test 11: CrossFedPipelineBridge break local → notifies remote ──

    #[test]
    fn bridge_break_local_notifies_remote() {
        let mut bridge = CrossFedPipelineBridge::new();

        let local_p = bridge.local_registry_mut().create_promise();

        // Peer B pipelines to our promise.
        bridge
            .on_pipeline_message(fed_b(), local_p, make_action("will_fail"), Some(88))
            .unwrap();

        // Break the local promise.
        let notifications = bridge.break_local_promise(local_p, "cell revoked".into());

        // Should notify federation B about promise 88 being broken.
        assert!(
            notifications
                .iter()
                .any(|n| n.promise_id == 88 && n.notify_federation == fed_b())
        );
    }

    // ─── Test 12: PipelineResult success resolves local promise ──

    #[test]
    fn pipeline_result_success_resolves_local() {
        let mut bridge = CrossFedPipelineBridge::new();

        // Pipeline to remote, get a local result promise.
        let local_p = bridge.pipeline_to_remote(fed_b(), 1, make_action("query"));
        let _ = bridge.drain_outbox();

        // Receive a success result.
        let result = PipelineResultValue::Success {
            cell_id: cell(0x55),
            receipt_hash: [0xAB; 32],
        };
        bridge.on_pipeline_result(fed_b(), local_p, result);

        assert!(matches!(
            bridge.local_registry().promise_state(local_p),
            Some(PipelinePromiseState::Fulfilled { resolved_cell }) if *resolved_cell == cell(0x55)
        ));
    }

    // ─── Test 13: PipelineResult failure breaks local promise ──

    #[test]
    fn pipeline_result_failure_breaks_local() {
        let mut bridge = CrossFedPipelineBridge::new();

        let local_p = bridge.pipeline_to_remote(fed_b(), 1, make_action("query"));
        let _ = bridge.drain_outbox();

        // Receive a failure result.
        let result = PipelineResultValue::Failure {
            error: "permission denied".into(),
        };
        bridge.on_pipeline_result(fed_b(), local_p, result);

        assert!(matches!(
            bridge.local_registry().promise_state(local_p),
            Some(PipelinePromiseState::Broken { reason }) if reason == "permission denied"
        ));
    }

    // ─── Test 14: Empty chain rejected ──

    #[test]
    fn empty_chain_rejected() {
        let mut reg = PipelineRegistry::new();
        let p = reg.create_promise();

        let result = reg.pipeline_chain(p, vec![], fed_a());
        assert!(matches!(result, Err(PipelineError::EmptyChain)));
    }

    // ─── Test 15: Wire message serialization roundtrip ──

    #[test]
    fn wire_message_serde_roundtrip() {
        let msg = PipelineWireMessage::PipelineToPromise {
            promise_id: 42,
            action: PipelinedAction {
                method: "transfer".into(),
                args: vec![1, 2, 3, 4],
                authorization: vec![0xDE, 0xAD],
            },
            result_promise_id: Some(100),
            sender_federation: fed_a(),
        };

        let serialized = serde_json::to_string(&msg).unwrap();
        let deserialized: PipelineWireMessage = serde_json::from_str(&serialized).unwrap();

        match deserialized {
            PipelineWireMessage::PipelineToPromise {
                promise_id,
                action,
                result_promise_id,
                sender_federation,
            } => {
                assert_eq!(promise_id, 42);
                assert_eq!(action.method, "transfer");
                assert_eq!(action.args, vec![1, 2, 3, 4]);
                assert_eq!(result_promise_id, Some(100));
                assert_eq!(sender_federation, fed_a());
            }
            _ => panic!("wrong variant"),
        }
    }
}
