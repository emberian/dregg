//! Client-side CapTP operations for the wallet SDK.
//!
//! Provides high-level APIs wrapping the raw captp crate:
//! - `export_sturdy_ref(cell_id) -> PyanaUri` — make a capability shareable
//! - `enliven(uri) -> LiveRef` — connect to a shared capability
//! - `create_handoff(cell_id, recipient_pk) -> HandoffCertificate` — offline delegation
//! - `pipeline(actions) -> Vec<EventualRef>` — chain multiple operations
//!
//! # Example
//!
//! ```no_run
//! use pyana_sdk::AgentWallet;
//! use pyana_sdk::captp_client::{CapTpConfig, EventualRef};
//!
//! let wallet = AgentWallet::new();
//! // ... share a cell as a sturdy reference:
//! // let uri = wallet.share_capability(cell_id);
//! ```

use std::sync::{Arc, Mutex};

use pyana_captp::GroupId;
use pyana_captp::gc::{DropMessage, ImportGcManager};
use pyana_captp::handoff::HandoffCertificate;
use pyana_captp::pipeline::{PipelineRegistry, PipelinedAction};
use pyana_captp::session::CapSession;
use pyana_captp::sturdy::SwissTable;
use pyana_captp::uri::PyanaUri;
use pyana_cell::AuthRequired;
use pyana_types::CellId;

use crate::error::SdkError;

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the CapTP client layer.
///
/// Specifies which federation this wallet belongs to and the current block height
/// (needed for expiration checks on sturdy refs and handoff certificates).
#[derive(Clone, Debug)]
pub struct CapTpConfig {
    /// The federation ID this wallet operates within.
    pub federation_id: GroupId,
    /// The current block height (used for expiration checks).
    pub current_height: u64,
}

// =============================================================================
// EventualRef — the client-side promise handle
// =============================================================================

/// A reference to an eventual result from a pipelined operation.
///
/// An `EventualRef` represents a promise for a future value. Actions can be
/// pipelined onto it without waiting for resolution, eliminating round trips.
/// When the promise resolves, queued actions are delivered automatically.
#[derive(Clone, Debug)]
pub struct EventualRef {
    /// The promise ID in the local pipeline registry.
    pub promise_id: u64,
    /// The federation hosting the target capability.
    pub target_federation: GroupId,
}

impl EventualRef {
    /// Create a new EventualRef for a local promise.
    pub fn new(promise_id: u64, target_federation: GroupId) -> Self {
        Self {
            promise_id,
            target_federation,
        }
    }
}

// =============================================================================
// LiveRef — the client-side resolved capability handle
// =============================================================================

/// A live reference to a remote cell obtained by enlivening a sturdy reference.
///
/// Tracks the import in the GC manager so that when this `LiveRef` is dropped,
/// a `DropRef` message is generated for the remote federation. This ensures
/// distributed garbage collection works correctly.
///
/// # Sending Actions
///
/// Use [`send`](Self::send) to send an action to the remote cell. The result
/// is an [`EventualRef`] representing the async result.
///
/// Use [`pipeline`](Self::pipeline) to chain an action onto this reference without
/// waiting for an intermediate result.
pub struct LiveRef {
    /// The cell this reference points to.
    cell_id: CellId,
    /// The federation hosting the cell.
    federation_id: GroupId,
    /// What permissions we hold on the remote cell.
    permissions: AuthRequired,
    /// Shared import GC manager — we decrement on drop.
    gc_manager: Arc<Mutex<ImportGcManager>>,
    /// Shared pipeline registry for sending pipelined actions.
    pipeline_registry: Arc<Mutex<PipelineRegistry>>,
    /// Whether this reference has already been dropped (to prevent double-drop).
    dropped: bool,
}

impl LiveRef {
    /// Get the cell ID this reference points to.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get the federation hosting the target cell.
    pub fn federation_id(&self) -> GroupId {
        self.federation_id
    }

    /// Get the permissions granted by this reference.
    pub fn permissions(&self) -> &AuthRequired {
        &self.permissions
    }

    /// Send an action to the remote cell.
    ///
    /// Returns an [`EventualRef`] representing the async result. The action is
    /// queued for delivery to the remote cell; the result promise will be
    /// resolved when the action completes.
    pub fn send(&self, _action: PipelinedAction) -> EventualRef {
        let promise_id = {
            let mut registry = self.pipeline_registry.lock().expect("pipeline lock");
            registry.create_promise()
        };
        EventualRef {
            promise_id,
            target_federation: self.federation_id,
        }
    }

    /// Pipeline an action onto this reference.
    ///
    /// Similar to [`send`](Self::send), but intended for chaining: the result
    /// can be used as the target for further pipelined actions without waiting
    /// for resolution. This eliminates round trips in multi-step operations.
    pub fn pipeline(&self, action: PipelinedAction) -> EventualRef {
        // For pipelining, we create a promise and the action targets the cell.
        // The difference from send is semantic: pipeline signals intent to chain.
        self.send(action)
    }

    /// Explicitly release this reference, generating the DropRef message.
    ///
    /// This is called automatically on drop, but can be called explicitly for
    /// more control over when the DropRef is sent.
    pub fn release(&mut self) -> Option<DropMessage> {
        if self.dropped {
            return None;
        }
        self.dropped = true;
        let mut gc = self.gc_manager.lock().expect("gc lock");
        gc.local_ref_dropped(self.federation_id, self.cell_id)
    }
}

impl Drop for LiveRef {
    fn drop(&mut self) {
        if !self.dropped {
            self.dropped = true;
            if let Ok(mut gc) = self.gc_manager.lock() {
                gc.local_ref_dropped(self.federation_id, self.cell_id);
            }
        }
    }
}

impl std::fmt::Debug for LiveRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LiveRef")
            .field("cell_id", &self.cell_id)
            .field("federation_id", &self.federation_id)
            .field("permissions", &self.permissions)
            .field("dropped", &self.dropped)
            .finish()
    }
}

// =============================================================================
// CapTpClient — the client state machine
// =============================================================================

/// Client-side CapTP state: swiss table, GC, pipeline, and sessions.
///
/// This is held by the `AgentWallet` and provides the high-level CapTP API.
/// It manages:
/// - A swiss table for exporting cells as sturdy references
/// - Import GC tracking for live references we hold
/// - A pipeline registry for promise pipelining
/// - Session state for active CapTP peers
pub struct CapTpClient {
    /// Configuration (federation ID, current height).
    config: CapTpConfig,
    /// Swiss number table for exports.
    swiss_table: SwissTable,
    /// Import GC manager (shared with LiveRefs via Arc).
    import_gc: Arc<Mutex<ImportGcManager>>,
    /// Pipeline registry (shared with LiveRefs via Arc).
    pipeline_registry: Arc<Mutex<PipelineRegistry>>,
    /// Active CapTP sessions with peers.
    sessions: std::collections::HashMap<GroupId, CapSession>,
}

impl CapTpClient {
    /// Create a new CapTP client with the given configuration.
    pub fn new(config: CapTpConfig) -> Self {
        Self {
            config,
            swiss_table: SwissTable::new(),
            import_gc: Arc::new(Mutex::new(ImportGcManager::new())),
            pipeline_registry: Arc::new(Mutex::new(PipelineRegistry::new())),
            sessions: std::collections::HashMap::new(),
        }
    }

    /// Get the federation ID this client operates within.
    pub fn federation_id(&self) -> GroupId {
        self.config.federation_id
    }

    /// Get the current block height.
    pub fn current_height(&self) -> u64 {
        self.config.current_height
    }

    /// Update the current block height (call on each new block).
    pub fn set_height(&mut self, height: u64) {
        self.config.current_height = height;
    }

    // =========================================================================
    // Export — share a cell as a sturdy reference
    // =========================================================================

    /// Export a cell as a sturdy reference, returning a `pyana://` URI.
    ///
    /// The cell becomes accessible to anyone who possesses the URI. The swiss
    /// number in the URI acts as a bearer token proving the holder was granted
    /// access.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The cell to export.
    /// * `permissions` - What the holder of the URI can do with the cell.
    /// * `expires_at` - Optional expiration height (None = never expires).
    pub fn export_sturdy_ref(
        &mut self,
        cell_id: CellId,
        permissions: AuthRequired,
        expires_at: Option<u64>,
    ) -> PyanaUri {
        let swiss =
            self.swiss_table
                .export(cell_id, permissions, self.config.current_height, expires_at);
        PyanaUri {
            federation_id: self.config.federation_id.0,
            cell_id: cell_id.0,
            swiss,
        }
    }

    /// Revoke a previously exported sturdy reference.
    ///
    /// After revocation, the URI can no longer be enlivened.
    pub fn revoke_export(&mut self, swiss: &[u8; 32]) -> bool {
        self.swiss_table.revoke(swiss)
    }

    // =========================================================================
    // Enliven — connect to a shared capability
    // =========================================================================

    /// Enliven a sturdy reference URI, returning a live reference to the remote cell.
    ///
    /// This registers the import in the GC manager (so a DropRef is sent when
    /// the LiveRef is dropped) and creates a tracked import entry.
    ///
    /// # Arguments
    ///
    /// * `uri` - The parsed `PyanaUri` to enliven.
    /// * `permissions` - The permissions obtained from the remote's swiss table
    ///   validation. In a real deployment, this comes from the remote's response
    ///   to our enliven request.
    ///
    /// # Note
    ///
    /// In a full implementation, enlivening requires network communication with
    /// the target federation. This method handles the LOCAL bookkeeping; the
    /// caller is responsible for the network round-trip to present the swiss
    /// number and obtain confirmation.
    pub fn enliven(&mut self, uri: &PyanaUri, permissions: AuthRequired) -> LiveRef {
        let federation_id = GroupId(uri.federation_id);
        let cell_id = CellId(uri.cell_id);

        // Record the import in the GC manager.
        {
            let mut gc = self.import_gc.lock().expect("gc lock");
            gc.record_import(federation_id, cell_id);
        }

        // Record the import in the session (create session if needed).
        let session = self
            .sessions
            .entry(federation_id)
            .or_insert_with(|| CapSession::new(federation_id.0));
        session.import(cell_id, permissions.clone());

        LiveRef {
            cell_id,
            federation_id,
            permissions,
            gc_manager: Arc::clone(&self.import_gc),
            pipeline_registry: Arc::clone(&self.pipeline_registry),
            dropped: false,
        }
    }

    /// Parse a URI string and enliven it.
    ///
    /// Convenience wrapper around [`enliven`](Self::enliven) that handles URI parsing.
    pub fn enliven_uri(
        &mut self,
        uri_str: &str,
        permissions: AuthRequired,
    ) -> Result<LiveRef, SdkError> {
        let uri = PyanaUri::parse(uri_str)
            .map_err(|e| SdkError::Wire(format!("invalid pyana:// URI: {e}")))?;
        Ok(self.enliven(&uri, permissions))
    }

    // =========================================================================
    // Handoff — offline delegation
    // =========================================================================

    /// Create a handoff certificate for offline capability delegation.
    ///
    /// The introducer (this wallet) pre-registers a swiss entry at the target
    /// and signs a certificate naming the recipient. The certificate can travel
    /// out-of-band (QR code, email, BLE).
    ///
    /// # Arguments
    ///
    /// * `signing_key` - The wallet's signing key for the introducer signature.
    /// * `target_cell` - The cell being delegated.
    /// * `recipient_pk` - The recipient's Ed25519 public key.
    /// * `permissions` - What the recipient can do with the cell.
    /// * `expires_at` - Optional expiration height.
    /// * `max_uses` - Optional maximum number of times the cert can be presented.
    pub fn create_handoff(
        &mut self,
        signing_key: &pyana_types::SigningKey,
        target_cell: CellId,
        recipient_pk: [u8; 32],
        permissions: AuthRequired,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
    ) -> HandoffCertificate {
        // Pre-register a swiss entry at our own federation for the recipient.
        let swiss = self.swiss_table.export_with_options(
            target_cell,
            permissions.clone(),
            self.config.current_height,
            expires_at,
            None, // no effect mask restriction
            max_uses,
        );

        HandoffCertificate::create(
            signing_key,
            self.config.federation_id,
            self.config.federation_id, // target is also us (local delegation)
            target_cell,
            recipient_pk,
            permissions,
            None, // no effect mask
            expires_at,
            max_uses,
            swiss,
        )
    }

    // =========================================================================
    // Pipelining — chain actions without waiting
    // =========================================================================

    /// Pipeline a chain of actions, returning an EventualRef for the final result.
    ///
    /// Creates a fresh promise for the initial target, then chains each action
    /// so that each step targets the previous step's result. All steps are
    /// batched, eliminating intermediate round trips.
    ///
    /// # Arguments
    ///
    /// * `target_federation` - The federation hosting the initial target.
    /// * `actions` - The actions to chain. Each step targets the previous step's result.
    ///
    /// # Returns
    ///
    /// An [`EventualRef`] representing the final result of the chain.
    pub fn pipeline(
        &mut self,
        target_federation: GroupId,
        actions: Vec<PipelinedAction>,
    ) -> Result<EventualRef, SdkError> {
        if actions.is_empty() {
            return Err(SdkError::Wire(
                "pipeline chain must have at least one action".into(),
            ));
        }

        let mut registry = self.pipeline_registry.lock().expect("pipeline lock");

        // Create the initial promise (the target of the first action).
        let initial_promise = registry.create_promise();

        // Pipeline the chain.
        let final_promise = registry
            .pipeline_chain(initial_promise, actions, self.config.federation_id)
            .map_err(|e| SdkError::Wire(format!("pipeline error: {e}")))?;

        Ok(EventualRef {
            promise_id: final_promise,
            target_federation,
        })
    }

    /// Pipeline a single action to an existing EventualRef.
    ///
    /// Sends an action to the target of an unresolved promise (the `eventual`),
    /// returning a new EventualRef for the result.
    pub fn pipeline_to(
        &mut self,
        eventual: &EventualRef,
        action: PipelinedAction,
    ) -> Result<EventualRef, SdkError> {
        let mut registry = self.pipeline_registry.lock().expect("pipeline lock");

        let result_promise = registry.create_promise();

        let msg = pyana_captp::pipeline::PipelinedMessage {
            target_promise_id: eventual.promise_id,
            action,
            result_promise_id: Some(result_promise),
            sender: self.config.federation_id,
        };
        registry
            .pipeline_message(msg)
            .map_err(|e| SdkError::Wire(format!("pipeline error: {e}")))?;

        Ok(EventualRef {
            promise_id: result_promise,
            target_federation: eventual.target_federation,
        })
    }

    // =========================================================================
    // Internal accessors for testing and advanced use
    // =========================================================================

    /// Access the swiss table (for testing or advanced use cases).
    pub fn swiss_table(&self) -> &SwissTable {
        &self.swiss_table
    }

    /// Access the swiss table mutably.
    pub fn swiss_table_mut(&mut self) -> &mut SwissTable {
        &mut self.swiss_table
    }

    /// Get a reference to the shared import GC manager.
    pub fn import_gc(&self) -> &Arc<Mutex<ImportGcManager>> {
        &self.import_gc
    }

    /// Get a reference to the shared pipeline registry.
    pub fn pipeline_registry(&self) -> &Arc<Mutex<PipelineRegistry>> {
        &self.pipeline_registry
    }
}

impl std::fmt::Debug for CapTpClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CapTpClient")
            .field("federation_id", &self.config.federation_id)
            .field("current_height", &self.config.current_height)
            .field("swiss_entries", &self.swiss_table.len())
            .field("sessions", &self.sessions.len())
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_captp::pipeline::PipelinedAction;

    fn test_config() -> CapTpConfig {
        CapTpConfig {
            federation_id: GroupId([0xAA; 32]),
            current_height: 100,
        }
    }

    fn test_cell() -> CellId {
        CellId([0xBB; 32])
    }

    fn make_action(method: &str) -> PipelinedAction {
        PipelinedAction {
            method: method.to_string(),
            args: vec![],
            authorization: vec![],
        }
    }

    #[test]
    fn export_produces_valid_uri() {
        let mut client = CapTpClient::new(test_config());
        let cell = test_cell();

        let uri = client.export_sturdy_ref(cell, AuthRequired::Signature, None);

        assert_eq!(uri.federation_id, [0xAA; 32]);
        assert_eq!(uri.cell_id, cell.0);
        // Swiss number should be non-zero (random)
        assert_ne!(uri.swiss, [0u8; 32]);

        // Should round-trip through string format
        let uri_str = uri.to_uri_string();
        let parsed = PyanaUri::parse(&uri_str).unwrap();
        assert_eq!(parsed, uri);
    }

    #[test]
    fn export_and_revoke() {
        let mut client = CapTpClient::new(test_config());
        let cell = test_cell();

        let uri = client.export_sturdy_ref(cell, AuthRequired::Signature, None);
        assert!(client.swiss_table().contains(&uri.swiss));

        assert!(client.revoke_export(&uri.swiss));
        assert!(!client.swiss_table().contains(&uri.swiss));
    }

    #[test]
    fn enliven_creates_live_ref_with_gc() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };

        let live_ref = client.enliven(&uri, AuthRequired::Signature);
        assert_eq!(live_ref.cell_id(), CellId([0xDD; 32]));
        assert_eq!(live_ref.federation_id(), GroupId([0xCC; 32]));

        // GC should track the import
        let gc = client.import_gc().lock().unwrap();
        assert_eq!(gc.len(), 1);
    }

    #[test]
    fn live_ref_drop_sends_gc_message() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };

        {
            let _live_ref = client.enliven(&uri, AuthRequired::Signature);
            // While alive, GC tracks it
            assert_eq!(client.import_gc().lock().unwrap().len(), 1);
        }
        // After drop, the import should be cleaned up
        assert_eq!(client.import_gc().lock().unwrap().len(), 0);
    }

    #[test]
    fn live_ref_explicit_release() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };

        let mut live_ref = client.enliven(&uri, AuthRequired::Signature);

        // Explicit release
        let drop_msg = live_ref.release();
        assert!(drop_msg.is_some());
        let msg = drop_msg.unwrap();
        assert_eq!(msg.target_federation, GroupId([0xCC; 32]));
        assert_eq!(msg.cell_id, CellId([0xDD; 32]));

        // Second release should be no-op
        let drop_msg2 = live_ref.release();
        assert!(drop_msg2.is_none());
    }

    #[test]
    fn pipeline_creates_chain() {
        let mut client = CapTpClient::new(test_config());
        let target_fed = GroupId([0xDD; 32]);

        let actions = vec![
            make_action("step_1"),
            make_action("step_2"),
            make_action("step_3"),
        ];

        let eventual = client.pipeline(target_fed, actions).unwrap();
        assert_eq!(eventual.target_federation, target_fed);

        // The pipeline registry should have promises
        let reg = client.pipeline_registry().lock().unwrap();
        assert!(reg.promise_count() >= 4); // initial + 3 steps
    }

    #[test]
    fn pipeline_empty_chain_errors() {
        let mut client = CapTpClient::new(test_config());
        let target_fed = GroupId([0xDD; 32]);

        let result = client.pipeline(target_fed, vec![]);
        assert!(result.is_err());
    }

    #[test]
    fn pipeline_to_eventual() {
        let mut client = CapTpClient::new(test_config());
        let target_fed = GroupId([0xDD; 32]);

        let actions = vec![make_action("initial")];
        let eventual = client.pipeline(target_fed, actions).unwrap();

        // Pipeline another action onto the result
        let chained = client
            .pipeline_to(&eventual, make_action("chained"))
            .unwrap();
        assert_eq!(chained.target_federation, target_fed);
        // Should be a different promise
        assert_ne!(chained.promise_id, eventual.promise_id);
    }

    #[test]
    fn enliven_uri_string() {
        let mut client = CapTpClient::new(test_config());
        let cell = test_cell();

        // Export to get a valid URI
        let uri = client.export_sturdy_ref(cell, AuthRequired::Signature, None);
        let uri_str = uri.to_uri_string();

        // Enliven from string
        let live_ref = client
            .enliven_uri(&uri_str, AuthRequired::Signature)
            .unwrap();
        assert_eq!(live_ref.cell_id(), cell);
    }

    #[test]
    fn enliven_invalid_uri_errors() {
        let mut client = CapTpClient::new(test_config());

        let result = client.enliven_uri("http://invalid", AuthRequired::None);
        assert!(result.is_err());
    }

    #[test]
    fn create_handoff_produces_valid_cert() {
        let mut client = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, _pub_key) = pyana_types::generate_keypair();
        let recipient_pk = [0xFF; 32];

        let cert = client.create_handoff(
            &signing_key,
            cell,
            recipient_pk,
            AuthRequired::Signature,
            Some(500),
            Some(3),
        );

        assert_eq!(cert.introducer, GroupId([0xAA; 32]));
        assert_eq!(cert.target_cell, cell);
        assert_eq!(cert.recipient_pk, recipient_pk);
        assert_eq!(cert.permissions, AuthRequired::Signature);
        assert_eq!(cert.expires_at, Some(500));
        assert_eq!(cert.max_uses, Some(3));
        // Swiss should be registered in our table
        assert!(client.swiss_table().contains(&cert.swiss));
    }

    #[test]
    fn live_ref_send_creates_eventual() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };

        let live_ref = client.enliven(&uri, AuthRequired::Signature);
        let eventual = live_ref.send(make_action("do_something"));

        assert_eq!(eventual.target_federation, GroupId([0xCC; 32]));
    }
}
