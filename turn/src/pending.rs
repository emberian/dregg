//! PendingTurnRegistry: async resolution, cross-federation EventualRefs, and
//! broken-promise propagation for distributed promise semantics.
//!
//! # Overview
//!
//! The pipeline system (eventual.rs) provides synchronous batched execution with
//! output forwarding. This module extends it with REAL distributed coordination:
//!
//! 1. A turn can be Pending (awaiting external resolution)
//! 2. EventualRefs can reference turns on OTHER federations
//! 3. When a promise breaks (turn rejected, timeout, federation offline),
//!    all dependents are notified via broken-promise propagation
//!
//! # Design
//!
//! ```text
//! ┌───────────────────────────────────────────────────────────────────┐
//! │ PendingTurnRegistry                                               │
//! │                                                                   │
//! │  pending: HashMap<[u8;32], PendingEntry>                         │
//! │     │                                                             │
//! │     ├─ turn_hash_A → PendingEntry { condition, dependents: [C] } │
//! │     ├─ turn_hash_B → PendingEntry { condition, dependents: [C] } │
//! │     └─ turn_hash_C → PendingEntry { condition: AwaitReceipt(A) } │
//! │                                                                   │
//! │  resolve(A, Resolved(receipt)) → cascading resolution of C       │
//! │  resolve(B, Broken(Timeout))   → cascading broken propagation    │
//! └───────────────────────────────────────────────────────────────────┘
//! ```

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::conditional::ProofCondition;
use crate::error::TurnError;
use crate::turn::{Turn, TurnReceipt};

// ─── Core Types ─────────────────────────────────────────────────────────────

/// A pending turn entry awaiting resolution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PendingEntry {
    /// The turn that will execute once its condition is met.
    pub turn: Turn,
    /// The condition that must be satisfied before execution.
    pub condition: ResolutionCondition,
    /// Hashes of turns that are waiting on THIS turn to resolve.
    pub dependents: Vec<[u8; 32]>,
    /// Block height at which this pending entry was submitted.
    pub submitted_at: u64,
    /// Block height at which this pending entry times out.
    pub timeout_height: u64,
}

/// A condition that must be met before a pending turn can execute.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ResolutionCondition {
    /// Waiting for a specific turn receipt to arrive.
    /// If `federation_id` is Some, the receipt comes from a remote federation.
    AwaitReceipt {
        /// Hash of the turn whose receipt we are waiting for.
        turn_hash: [u8; 32],
        /// If Some, the receipt comes from a remote federation.
        federation_id: Option<[u8; 32]>,
    },
    /// Waiting for a ProofCondition to be satisfied (same as ConditionalTurn).
    AwaitCondition(ProofCondition),
    /// Waiting for a specific block height to be reached.
    AwaitHeight(u64),
}

/// The outcome of resolving a pending turn.
#[derive(Clone, Debug)]
pub enum ResolutionOutcome {
    /// The turn was executed successfully; here is its receipt.
    Resolved(TurnReceipt),
    /// The promise is broken; the turn will never execute.
    Broken(BrokenReason),
}

/// Why a promise was broken.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BrokenReason {
    /// The turn was rejected during execution.
    TurnRejected(TurnError),
    /// The pending turn timed out (timeout_height exceeded).
    Timeout,
    /// The remote federation is unreachable.
    FederationUnreachable,
    /// An upstream dependency broke, causing this promise to break.
    DependencyBroken(Box<BrokenReason>),
}

impl std::fmt::Display for BrokenReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BrokenReason::TurnRejected(err) => write!(f, "turn rejected: {err}"),
            BrokenReason::Timeout => write!(f, "timeout"),
            BrokenReason::FederationUnreachable => write!(f, "federation unreachable"),
            BrokenReason::DependencyBroken(inner) => {
                write!(f, "dependency broken: {inner}")
            }
        }
    }
}

/// An event emitted by the registry during resolution or timeout checking.
#[derive(Clone, Debug)]
pub enum ResolutionEvent {
    /// A pending turn was resolved (executed successfully).
    Resolved {
        /// The hash of the turn that was resolved.
        turn_hash: [u8; 32],
        /// The receipt from executing the turn.
        receipt: TurnReceipt,
    },
    /// A dependent turn's condition has been met and it is ready to execute.
    /// The node must run TurnExecutor on it and then call `resolve()` with the
    /// real receipt (or Broken if execution fails).
    ReadyToExecute {
        /// The hash of the turn that is ready.
        turn_hash: [u8; 32],
        /// The turn that needs to be executed.
        turn: Turn,
    },
    /// A pending turn's promise was broken.
    Broken {
        /// The hash of the turn whose promise was broken.
        turn_hash: [u8; 32],
        /// Why the promise was broken.
        reason: BrokenReason,
    },
}

/// A handle returned when a pending turn is submitted.
#[derive(Clone, Debug)]
pub struct PendingHandle {
    /// The hash identifying the pending turn.
    pub turn_hash: [u8; 32],
    /// The current status of this pending turn.
    pub status: PendingStatus,
}

/// The current status of a pending turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingStatus {
    /// Still waiting for its condition to be met.
    Pending,
    /// Successfully resolved with a receipt.
    Resolved,
    /// Promise broken.
    Broken,
}

// ─── Registry ───────────────────────────────────────────────────────────────

/// Registry tracking all unresolved pending turns and their dependency graph.
///
/// The registry provides:
/// - Submit: register a pending turn with a resolution condition
/// - Resolve: mark a turn as resolved or broken, cascading to dependents
/// - Timeout: check for expired pending turns and propagate broken promises
#[derive(Clone, Debug, Default)]
pub struct PendingTurnRegistry {
    /// Map from turn hash to pending entry.
    pending: HashMap<[u8; 32], PendingEntry>,
}

impl PendingTurnRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            pending: HashMap::new(),
        }
    }

    /// Submit a new pending turn with a resolution condition and timeout.
    ///
    /// Returns the turn hash that identifies this pending entry.
    pub fn submit_pending(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
    ) -> [u8; 32] {
        let turn_hash = turn.hash();
        let entry = PendingEntry {
            turn,
            condition,
            dependents: Vec::new(),
            submitted_at: 0, // Caller should set via submit_pending_at
            timeout_height,
        };
        self.pending.insert(turn_hash, entry);
        turn_hash
    }

    /// Submit a new pending turn with a resolution condition, timeout, and submission height.
    ///
    /// Returns the turn hash that identifies this pending entry.
    pub fn submit_pending_at(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
        submitted_at: u64,
    ) -> [u8; 32] {
        let turn_hash = turn.hash();
        let entry = PendingEntry {
            turn,
            condition,
            dependents: Vec::new(),
            submitted_at,
            timeout_height,
        };
        self.pending.insert(turn_hash, entry);
        turn_hash
    }

    /// Register a dependency: `dependent_hash` is waiting on `pending_hash`.
    ///
    /// When `pending_hash` resolves (or breaks), `dependent_hash` will be notified.
    pub fn register_dependent(&mut self, pending_hash: [u8; 32], dependent_hash: [u8; 32]) {
        if let Some(entry) = self.pending.get_mut(&pending_hash) {
            if !entry.dependents.contains(&dependent_hash) {
                entry.dependents.push(dependent_hash);
            }
        }
    }

    /// Resolve a pending turn with the given outcome.
    ///
    /// If `Resolved`: the turn executed successfully. Check all dependents to see
    /// if their conditions are now met (cascading resolution).
    ///
    /// If `Broken`: propagate `BrokenReason::DependencyBroken` to all dependents
    /// recursively.
    ///
    /// Returns a list of all resolution events that occurred (including cascading).
    pub fn resolve(
        &mut self,
        turn_hash: [u8; 32],
        outcome: ResolutionOutcome,
    ) -> Vec<ResolutionEvent> {
        let Some(entry) = self.pending.remove(&turn_hash) else {
            return vec![];
        };

        match outcome {
            ResolutionOutcome::Resolved(receipt) => {
                let mut events = vec![ResolutionEvent::Resolved {
                    turn_hash,
                    receipt: receipt.clone(),
                }];

                // Cascade resolution to dependents whose conditions are now met.
                self.cascade_resolved(turn_hash, &entry.dependents, &receipt, &mut events);

                events
            }
            ResolutionOutcome::Broken(reason) => {
                self.propagate_broken(turn_hash, &entry.dependents, reason)
            }
        }
    }

    /// Cascade to dependents whose conditions are met: emit ReadyToExecute events.
    ///
    /// Unlike the old approach that fabricated fake receipts, this keeps the entry
    /// in the registry and signals the caller (the node) to actually execute it.
    /// The node should then call `resolve()` with the real receipt, which will
    /// remove the entry and cascade to further dependents.
    fn cascade_resolved(
        &mut self,
        resolved_hash: [u8; 32],
        dependents: &[[u8; 32]],
        _trigger_receipt: &TurnReceipt,
        events: &mut Vec<ResolutionEvent>,
    ) {
        for &dep_hash in dependents {
            // Check condition without removing.
            let should_resolve = self
                .pending
                .get(&dep_hash)
                .map(|e| self.condition_met_by_receipt(&e.condition, &resolved_hash))
                .unwrap_or(false);

            if should_resolve {
                // The entry stays in the registry. The node is responsible for executing
                // this turn and then calling resolve() with a real receipt (or Broken).
                // That call will remove it from the registry and cascade to its dependents.
                let turn = self.pending.get(&dep_hash).unwrap().turn.clone();
                events.push(ResolutionEvent::ReadyToExecute {
                    turn_hash: dep_hash,
                    turn,
                });
                // NOTE: We do NOT recursively cascade here. The node will execute the
                // turn, get a real receipt, and call resolve() again, which will cascade
                // to any further dependents at that point.
            }
        }
    }

    /// Check all pending turns for timeout at the given block height.
    ///
    /// Returns resolution events for all turns that have timed out.
    /// Timed-out turns are removed and their dependents get broken-promise propagation.
    pub fn check_timeouts(&mut self, current_height: u64) -> Vec<ResolutionEvent> {
        // Collect timed-out turn hashes first to avoid borrow conflicts.
        let timed_out: Vec<[u8; 32]> = self
            .pending
            .iter()
            .filter(|(_, entry)| current_height > entry.timeout_height)
            .map(|(hash, _)| *hash)
            .collect();

        let mut events = Vec::new();
        for hash in timed_out {
            let sub_events = self.resolve(hash, ResolutionOutcome::Broken(BrokenReason::Timeout));
            events.extend(sub_events);
        }
        events
    }

    /// Look up a pending entry by its turn hash.
    pub fn get_pending(&self, hash: &[u8; 32]) -> Option<&PendingEntry> {
        self.pending.get(hash)
    }

    /// Returns the number of currently pending turns.
    pub fn len(&self) -> usize {
        self.pending.len()
    }

    /// Returns true if the registry has no pending turns.
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// Check if a resolution condition is satisfied by a specific receipt arrival.
    fn condition_met_by_receipt(
        &self,
        condition: &ResolutionCondition,
        receipt_turn_hash: &[u8; 32],
    ) -> bool {
        match condition {
            ResolutionCondition::AwaitReceipt { turn_hash, .. } => turn_hash == receipt_turn_hash,
            ResolutionCondition::AwaitCondition(_) => {
                // ProofCondition requires explicit proof presentation, not just receipt arrival.
                false
            }
            ResolutionCondition::AwaitHeight(_) => {
                // Height-based conditions are checked by check_timeouts / check_heights.
                false
            }
        }
    }

    /// Propagate a broken promise to all dependents recursively.
    fn propagate_broken(
        &mut self,
        broken_hash: [u8; 32],
        dependents: &[[u8; 32]],
        reason: BrokenReason,
    ) -> Vec<ResolutionEvent> {
        let mut events = vec![ResolutionEvent::Broken {
            turn_hash: broken_hash,
            reason: reason.clone(),
        }];

        for &dep_hash in dependents {
            if let Some(dep_entry) = self.pending.remove(&dep_hash) {
                let dep_reason = BrokenReason::DependencyBroken(Box::new(reason.clone()));
                let sub_events = self.propagate_broken(dep_hash, &dep_entry.dependents, dep_reason);
                events.extend(sub_events);
            }
        }

        events
    }

    /// Check for pending turns whose AwaitHeight condition is now satisfied.
    ///
    /// Returns the turn hashes of entries whose height condition is met.
    /// The caller is responsible for actually executing these turns and calling
    /// `resolve()` with the outcome.
    pub fn check_height_conditions(&self, current_height: u64) -> Vec<[u8; 32]> {
        self.pending
            .iter()
            .filter(|(_, entry)| {
                matches!(
                    entry.condition,
                    ResolutionCondition::AwaitHeight(h) if current_height >= h
                )
            })
            .map(|(hash, _)| *hash)
            .collect()
    }
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use crate::forest::CallForest;
    use pyana_cell::{CellId, Preconditions};

    /// Helper: create a minimal turn for testing.
    fn make_turn(agent_byte: u8, nonce: u64) -> Turn {
        let agent = CellId::from_bytes([agent_byte; 32]);
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 1000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            previous_receipt_hash: None,
        }
    }

    /// Helper: create a dummy receipt for a turn.
    fn make_receipt(turn: &Turn) -> TurnReceipt {
        TurnReceipt {
            turn_hash: turn.hash(),
            forest_hash: turn.call_forest.compute_hash(),
            pre_state_hash: [0u8; 32],
            post_state_hash: [1u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash: None,
            agent: turn.agent,
            federation_id: [0u8; 32],
            routing_directives: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
        }
    }

    // ─── Test 1: Submit pending → resolve with receipt → turn executes ────

    #[test]
    fn test_submit_and_resolve() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_a_hash = turn_a.hash();

        // Submit turn A as pending, awaiting receipt of some external turn.
        let external_hash = [0xAB; 32];
        let hash = registry.submit_pending(
            turn_a.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: external_hash,
                federation_id: None,
            },
            100,
        );
        assert_eq!(hash, turn_a_hash);
        assert_eq!(registry.len(), 1);

        // Resolve with a receipt.
        let receipt = make_receipt(&turn_a);
        let events = registry.resolve(turn_a_hash, ResolutionOutcome::Resolved(receipt.clone()));

        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Resolved { turn_hash, receipt: r }
            if *turn_hash == turn_a_hash && r.turn_hash == receipt.turn_hash
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 2: Submit pending → timeout → broken propagated ─────────────

    #[test]
    fn test_timeout_propagates_broken() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_a_hash = turn_a.hash();

        registry.submit_pending_at(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xBB; 32],
                federation_id: None,
            },
            50, // timeout at height 50
            10, // submitted at height 10
        );

        // At height 40: no timeout yet.
        let events = registry.check_timeouts(40);
        assert!(events.is_empty());
        assert_eq!(registry.len(), 1);

        // At height 51: timeout triggered.
        let events = registry.check_timeouts(51);
        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == turn_a_hash && matches!(reason, BrokenReason::Timeout)
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 3: Chain A → B → C: C resolves → B resolves → A resolves ───

    #[test]
    fn test_cascading_resolution() {
        let mut registry = PendingTurnRegistry::new();

        let turn_c = make_turn(3, 0);
        let turn_b = make_turn(2, 0);
        let turn_a = make_turn(1, 0);

        let hash_c = turn_c.hash();
        let hash_b = turn_b.hash();
        let hash_a = turn_a.hash();

        // C awaits an external receipt.
        registry.submit_pending(
            turn_c.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xEE; 32],
                federation_id: None,
            },
            1000,
        );

        // B awaits C's receipt.
        registry.submit_pending(
            turn_b.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_c,
                federation_id: None,
            },
            1000,
        );

        // A awaits B's receipt.
        registry.submit_pending(
            turn_a.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_b,
                federation_id: None,
            },
            1000,
        );

        // Register dependencies: C's resolution triggers B, B's triggers A.
        registry.register_dependent(hash_c, hash_b);
        registry.register_dependent(hash_b, hash_a);

        assert_eq!(registry.len(), 3);

        // Resolve C → should emit Resolved for C + ReadyToExecute for B (immediate dependent).
        let receipt_c = make_receipt(&turn_c);
        let events = registry.resolve(hash_c, ResolutionOutcome::Resolved(receipt_c));

        // Should have 2 events: C resolved, B ready to execute.
        assert_eq!(events.len(), 2, "expected 2 events, got {}", events.len());
        assert!(
            matches!(&events[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_c),
            "first event should be Resolved for C"
        );
        assert!(
            matches!(&events[1], ResolutionEvent::ReadyToExecute { turn_hash, .. } if *turn_hash == hash_b),
            "second event should be ReadyToExecute for B"
        );

        // B and A are still in the registry (B awaiting real execution, A awaiting B).
        assert_eq!(registry.len(), 2);

        // Now simulate the node executing B and resolving it with a real receipt.
        let receipt_b = make_receipt(&turn_b);
        let events2 = registry.resolve(hash_b, ResolutionOutcome::Resolved(receipt_b));

        // Should have 2 events: B resolved, A ready to execute.
        assert_eq!(events2.len(), 2, "expected 2 events, got {}", events2.len());
        assert!(
            matches!(&events2[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_b),
            "first event should be Resolved for B"
        );
        assert!(
            matches!(&events2[1], ResolutionEvent::ReadyToExecute { turn_hash, .. } if *turn_hash == hash_a),
            "second event should be ReadyToExecute for A"
        );

        // A is still in registry (awaiting real execution).
        assert_eq!(registry.len(), 1);

        // Node executes A and resolves it.
        let receipt_a = make_receipt(&turn_a);
        let events3 = registry.resolve(hash_a, ResolutionOutcome::Resolved(receipt_a));

        // Just A resolved, no further dependents.
        assert_eq!(events3.len(), 1);
        assert!(
            matches!(&events3[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_a),
        );

        // Registry should be empty now.
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 4: Chain A → B: B breaks → A immediately broken ─────────────

    #[test]
    fn test_broken_propagation() {
        let mut registry = PendingTurnRegistry::new();

        let turn_b = make_turn(2, 0);
        let turn_a = make_turn(1, 0);

        let hash_b = turn_b.hash();
        let hash_a = turn_a.hash();

        // B awaits external.
        registry.submit_pending(
            turn_b,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xFF; 32],
                federation_id: None,
            },
            1000,
        );

        // A awaits B.
        registry.submit_pending(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_b,
                federation_id: None,
            },
            1000,
        );

        // Register A as dependent of B.
        registry.register_dependent(hash_b, hash_a);

        // B breaks.
        let events = registry.resolve(
            hash_b,
            ResolutionOutcome::Broken(BrokenReason::TurnRejected(TurnError::PreconditionFailed {
                description: "test failure".to_string(),
            })),
        );

        // Should have 2 events: B broken, A broken (dependency).
        assert_eq!(events.len(), 2);

        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == hash_b && matches!(reason, BrokenReason::TurnRejected(_))
        ));

        assert!(matches!(
            &events[1],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == hash_a && matches!(reason, BrokenReason::DependencyBroken(_))
        ));

        assert_eq!(registry.len(), 0);
    }

    // ─── Test 5: Cross-fed EventualRef → receipt arrives → resolves ───────

    #[test]
    fn test_cross_federation_resolution() {
        let mut registry = PendingTurnRegistry::new();

        let remote_federation_id = [0x42; 32];
        let remote_turn_hash = [0xDE; 32];

        let local_turn = make_turn(1, 0);
        let local_hash = local_turn.hash();

        // Local turn depends on a remote federation's receipt.
        registry.submit_pending(
            local_turn.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: remote_turn_hash,
                federation_id: Some(remote_federation_id),
            },
            500,
        );

        assert_eq!(registry.len(), 1);
        let entry = registry.get_pending(&local_hash).unwrap();
        assert!(matches!(
            &entry.condition,
            ResolutionCondition::AwaitReceipt { federation_id: Some(fid), .. }
            if *fid == remote_federation_id
        ));

        // Remote receipt arrives → resolve.
        let receipt = make_receipt(&local_turn);
        let events = registry.resolve(local_hash, ResolutionOutcome::Resolved(receipt));

        assert_eq!(events.len(), 1);
        assert!(matches!(&events[0], ResolutionEvent::Resolved { .. }));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 6: Cross-fed remote offline → timeout → broken ──────────────

    #[test]
    fn test_cross_federation_timeout() {
        let mut registry = PendingTurnRegistry::new();

        let remote_federation_id = [0x42; 32];
        let remote_turn_hash = [0xDE; 32];

        let local_turn = make_turn(1, 0);
        let local_hash = local_turn.hash();

        registry.submit_pending_at(
            local_turn,
            ResolutionCondition::AwaitReceipt {
                turn_hash: remote_turn_hash,
                federation_id: Some(remote_federation_id),
            },
            100, // timeout at height 100
            50,  // submitted at height 50
        );

        // Height 99: not timed out yet.
        let events = registry.check_timeouts(99);
        assert!(events.is_empty());

        // Height 101: timed out.
        let events = registry.check_timeouts(101);
        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == local_hash && matches!(reason, BrokenReason::Timeout)
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 7: AwaitHeight condition ────────────────────────────────────

    #[test]
    fn test_await_height_condition() {
        let mut registry = PendingTurnRegistry::new();

        let turn = make_turn(1, 0);
        let hash = turn.hash();

        registry.submit_pending(turn, ResolutionCondition::AwaitHeight(200), 1000);

        // At height 100: not ready.
        let ready = registry.check_height_conditions(100);
        assert!(ready.is_empty());

        // At height 200: ready.
        let ready = registry.check_height_conditions(200);
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0], hash);

        // At height 300: still ready (hasn't been resolved yet).
        let ready = registry.check_height_conditions(300);
        assert_eq!(ready.len(), 1);
    }

    // ─── Test 8: Duplicate dependent registration is idempotent ───────────

    #[test]
    fn test_duplicate_dependent_idempotent() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_b = make_turn(2, 0);
        let hash_a = turn_a.hash();
        let hash_b = turn_b.hash();

        registry.submit_pending(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xFF; 32],
                federation_id: None,
            },
            1000,
        );
        registry.submit_pending(
            turn_b,
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_a,
                federation_id: None,
            },
            1000,
        );

        // Register same dependent twice.
        registry.register_dependent(hash_a, hash_b);
        registry.register_dependent(hash_a, hash_b);

        let entry = registry.get_pending(&hash_a).unwrap();
        assert_eq!(entry.dependents.len(), 1, "should not duplicate");
    }

    // ─── Test 9: Resolving non-existent hash is a no-op ──────────────────

    #[test]
    fn test_resolve_nonexistent() {
        let mut registry = PendingTurnRegistry::new();
        let events = registry.resolve([0xFF; 32], ResolutionOutcome::Broken(BrokenReason::Timeout));
        assert!(events.is_empty());
    }

    // ─── Test 10: Deep chain propagation ──────────────────────────────────

    #[test]
    fn test_deep_chain_broken_propagation() {
        let mut registry = PendingTurnRegistry::new();

        // Create a chain of 5 turns: E → D → C → B → A (E is deepest dependency).
        let turns: Vec<Turn> = (0..5).map(|i| make_turn(i + 1, 0)).collect();
        let hashes: Vec<[u8; 32]> = turns.iter().map(|t| t.hash()).collect();

        // Submit all as pending.
        for (i, turn) in turns.into_iter().enumerate() {
            let condition = if i == 0 {
                // First turn awaits external.
                ResolutionCondition::AwaitReceipt {
                    turn_hash: [0xEE; 32],
                    federation_id: None,
                }
            } else {
                // Each subsequent turn awaits the previous.
                ResolutionCondition::AwaitReceipt {
                    turn_hash: hashes[i - 1],
                    federation_id: None,
                }
            };
            registry.submit_pending(turn, condition, 1000);
        }

        // Register chain: each turn is a dependent of the previous.
        for i in 0..4 {
            registry.register_dependent(hashes[i], hashes[i + 1]);
        }

        assert_eq!(registry.len(), 5);

        // Break the first turn in the chain. Broken propagation IS recursive
        // (unlike resolution which requires actual execution), so all dependents break.
        let events = registry.resolve(
            hashes[0],
            ResolutionOutcome::Broken(BrokenReason::FederationUnreachable),
        );

        // All 5 should be broken.
        assert_eq!(events.len(), 5);
        for event in &events {
            assert!(matches!(event, ResolutionEvent::Broken { .. }));
        }
        assert_eq!(registry.len(), 0);
    }
}
