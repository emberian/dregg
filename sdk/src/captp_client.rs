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

use pyana_captp::FederationId as GroupId;
use pyana_captp::gc::{DropMessage, ImportGcManager};
use pyana_captp::handoff::HandoffCertificate;
use pyana_captp::pipeline::{PipelineRegistry, PipelinedAction};
use pyana_captp::session::CapSession;
use pyana_captp::sturdy::SwissTable;
use pyana_captp::uri::PyanaUri;
use pyana_cell::AuthRequired;
use pyana_types::CellId;
use pyana_wire::message::WireMessage;

use crate::error::SdkError;

// =============================================================================
// Wire outbox
// =============================================================================

/// A wire-level outbox shared between the `CapTpClient` and every `LiveRef` it
/// vends. When CapTP operations (`send`, `pipeline_to`, `Drop`, `release`,
/// `pipeline`) need to escape the local process they push a `WireMessage` here.
/// The transport layer drains the outbox via [`CapTpClient::drain_wire_outbox`]
/// and writes the messages to the appropriate peers.
///
/// This is the wiring point that closes audit GAP-4 (PipelinedMsg never
/// dispatched) and GAP-9 (DropMessage produced-then-discarded).
pub type WireOutbox = Arc<Mutex<Vec<WireMessage>>>;

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the CapTP client layer.
///
/// Specifies which group (formerly "federation") this wallet belongs to and the
/// current block height (needed for expiration checks on sturdy refs and handoff
/// certificates).
///
/// In the unified lace model, `GroupId` is semantically equivalent to `FederationId`.
/// Both types are accepted interchangeably (they are the same struct).
#[derive(Clone, Debug)]
pub struct CapTpConfig {
    /// The group/federation ID this wallet operates within.
    ///
    /// Accepts both `FederationId` and `GroupId` (they are the same type).
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
    /// Sender-side disambiguator (shared with the parent `CapTpClient`).
    /// See [`CapTpClient::import_table`].
    import_table: Arc<Mutex<std::collections::HashMap<u64, CellId>>>,
    /// Shared wire outbox — pushed to on send/pipeline/drop.
    outbox: WireOutbox,
    /// The federation identity that the local node speaks as. Stamped onto
    /// every outgoing `PipelinedMsg` / `DropRemoteRef` as `sender_federation`
    /// / `from_strand` so the receiving server can attribute the message to
    /// the correct `CapSession`.
    local_federation: GroupId,
    /// The session epoch we last observed with the remote. Stamped onto
    /// outgoing wire messages so the receiver can reject stale-epoch
    /// chatter when sessions are reset.
    session_epoch: u64,
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

    /// Send an action to the remote cell (fire-and-forget unless the caller
    /// observes the returned promise via the registry).
    ///
    /// Allocates a fresh promise id in the local pipeline registry, records
    /// a pending entry against it, and enqueues a [`WireMessage::PipelinedMsg`]
    /// in the shared wire outbox. The transport layer drains the outbox via
    /// [`CapTpClient::drain_wire_outbox`] and writes the message to the
    /// owning federation. The receiving server queues the message in its
    /// `CrossFedPipelineBridge` until the target promise resolves.
    ///
    /// Closes audit GAP-4 (PipelinedMsg never dispatched) and the SDK side of
    /// C-2 (LiveRef::send dropped its action).
    pub fn send(&self, action: PipelinedAction) -> EventualRef {
        // Allocate a fresh `target_promise_id` from the pipeline registry
        // and immediately resolve it to this LiveRef's cell. The receiving
        // server treats `target_promise_id` as opaque, so the only
        // requirement is that the sender pick distinct ids for distinct
        // bearer cells; using a counter-allocated promise eliminates the
        // 32→8 byte truncation collision class flagged by audit B
        // (`bytes_to_promise_id` truncation). The reverse map in
        // `import_table` lets later wire replies disambiguate.
        let (target_promise_id, result_promise_id) = {
            let mut registry = self.pipeline_registry.lock().expect("pipeline lock");
            let target = registry.create_promise();
            let _ = registry.resolve_promise(target, self.cell_id);
            let result = registry.create_promise();
            (target, result)
        };
        self.import_table
            .lock()
            .expect("import_table lock")
            .insert(target_promise_id, self.cell_id);

        let msg = WireMessage::PipelinedMsg {
            target_promise_id,
            method: action.method.clone(),
            args: action.args.clone(),
            authorization: action.authorization.clone(),
            result_promise_id: Some(result_promise_id),
            sender_federation: self.local_federation.0,
            session_epoch: self.session_epoch,
        };
        self.outbox.lock().expect("outbox lock").push(msg);

        EventualRef {
            promise_id: result_promise_id,
            target_federation: self.federation_id,
        }
    }

    /// Pipeline an action onto this reference, returning an `EventualRef` for
    /// the action's result.
    ///
    /// Distinct from [`send`](Self::send) in that pipelined messages are
    /// expected to participate in further chaining: the local registry queues
    /// the action against the *bearer cell promise* (not the bearer cell
    /// directly), so a subsequent `pipeline_to` can target the result.
    /// Mechanically: allocate a result promise, queue a `PipelinedMessage` in
    /// the local registry so cascading breakage works, and emit the wire
    /// message.
    pub fn pipeline(&self, action: PipelinedAction) -> EventualRef {
        let (target_promise_id, result_promise_id) = {
            let mut registry = self.pipeline_registry.lock().expect("pipeline lock");
            // Allocate a promise that represents the bearer cell on the
            // local side and immediately resolve it to the live cell so
            // pipelined chains can target it.
            let bearer_promise = registry.create_promise();
            let _ = registry.resolve_promise(bearer_promise, self.cell_id);
            let result_promise = registry.create_promise();
            // Queue locally so break_promise cascades correctly if the
            // result is later broken on the wire.
            let msg = pyana_captp::pipeline::PipelinedMessage {
                target_promise_id: bearer_promise,
                action: action.clone(),
                result_promise_id: Some(result_promise),
                sender: self.local_federation,
            };
            let _ = registry.pipeline_message(msg);
            (bearer_promise, result_promise)
        };
        self.import_table
            .lock()
            .expect("import_table lock")
            .insert(target_promise_id, self.cell_id);

        let wire = WireMessage::PipelinedMsg {
            target_promise_id,
            method: action.method,
            args: action.args,
            authorization: action.authorization,
            result_promise_id: Some(result_promise_id),
            sender_federation: self.local_federation.0,
            session_epoch: self.session_epoch,
        };
        self.outbox.lock().expect("outbox lock").push(wire);

        EventualRef {
            promise_id: result_promise_id,
            target_federation: self.federation_id,
        }
    }

    /// Explicitly release this reference, generating the DropRef message and
    /// enqueuing it on the wire outbox.
    ///
    /// This is called automatically on drop, but can be called explicitly for
    /// more control over when the DropRef is sent. The returned
    /// [`DropMessage`] is also pushed onto the shared wire outbox as a
    /// [`WireMessage::DropRemoteRef`] so the transport actually delivers it
    /// (closes audit GAP-9).
    pub fn release(&mut self) -> Option<DropMessage> {
        if self.dropped {
            return None;
        }
        self.dropped = true;
        let drop_msg = {
            let mut gc = self.gc_manager.lock().expect("gc lock");
            gc.local_ref_dropped(self.federation_id, self.cell_id)
        };
        if let Some(ref m) = drop_msg {
            let wire = WireMessage::DropRemoteRef {
                from_strand: self.local_federation.0,
                cell_id: m.cell_id.0,
                session_epoch: self.session_epoch,
            };
            self.outbox.lock().expect("outbox lock").push(wire);
        }
        drop_msg
    }
}

impl Drop for LiveRef {
    fn drop(&mut self) {
        if !self.dropped {
            self.dropped = true;
            let drop_msg = if let Ok(mut gc) = self.gc_manager.lock() {
                gc.local_ref_dropped(self.federation_id, self.cell_id)
            } else {
                None
            };
            if let Some(m) = drop_msg {
                if let Ok(mut outbox) = self.outbox.lock() {
                    outbox.push(WireMessage::DropRemoteRef {
                        from_strand: self.local_federation.0,
                        cell_id: m.cell_id.0,
                        session_epoch: self.session_epoch,
                    });
                }
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
    /// Sender-side disambiguator: `target_promise_id` → `CellId`. Populated
    /// every time `LiveRef::send` / `LiveRef::pipeline` allocates a fresh
    /// promise id for a wire `PipelinedMsg`. Replaces the previous 32→8 byte
    /// truncation in `bytes_to_promise_id`, which could collide across cells
    /// whose ids shared their first 8 bytes (audit lane B).
    import_table: Arc<Mutex<std::collections::HashMap<u64, CellId>>>,
    /// Active CapTP sessions with peers.
    sessions: std::collections::HashMap<GroupId, CapSession>,
    /// Shared wire outbox. Every CapTP operation that crosses the trust
    /// boundary (`pipeline_to`, `LiveRef::send`, `LiveRef::pipeline`, drop)
    /// pushes a `WireMessage` here. The transport drains it via
    /// [`Self::drain_wire_outbox`].
    outbox: WireOutbox,
    /// Per-peer session epoch tracking: when the SDK observes a `CapHello`
    /// (or other epoch-bearing handshake) for a peer it records the epoch
    /// here so that subsequently-issued wire messages stamp the right value.
    session_epochs: std::collections::HashMap<GroupId, u64>,
}

impl CapTpClient {
    /// Create a new CapTP client with the given configuration.
    pub fn new(config: CapTpConfig) -> Self {
        Self {
            config,
            swiss_table: SwissTable::new(),
            import_gc: Arc::new(Mutex::new(ImportGcManager::new())),
            pipeline_registry: Arc::new(Mutex::new(PipelineRegistry::new())),
            import_table: Arc::new(Mutex::new(std::collections::HashMap::new())),
            sessions: std::collections::HashMap::new(),
            outbox: Arc::new(Mutex::new(Vec::new())),
            session_epochs: std::collections::HashMap::new(),
        }
    }

    /// Look up the cell a previously-allocated `target_promise_id`
    /// represents on this client side. Returns `None` if the id is unknown
    /// (the receiver allocated it, the entry was reaped, or it predates
    /// the import-table wiring).
    pub fn import_table_lookup(&self, target_promise_id: u64) -> Option<CellId> {
        self.import_table
            .lock()
            .ok()
            .and_then(|t| t.get(&target_promise_id).copied())
    }

    /// Drain pending wire messages.
    ///
    /// The transport layer calls this after every operation (or on a tick)
    /// and writes the resulting messages to the appropriate peer connections.
    /// Returns the drained messages in the order they were enqueued.
    pub fn drain_wire_outbox(&self) -> Vec<WireMessage> {
        std::mem::take(&mut *self.outbox.lock().expect("outbox lock"))
    }

    /// Get a clone of the shared wire outbox handle.
    ///
    /// Useful for tests and for transport integrations that want to share
    /// the outbox with non-SDK code (e.g., a connection pool).
    pub fn wire_outbox(&self) -> WireOutbox {
        Arc::clone(&self.outbox)
    }

    /// Record the session epoch most recently negotiated with a peer.
    ///
    /// The SDK stamps this onto outgoing `PipelinedMsg` / `DropRemoteRef`
    /// messages so the server can reject messages bearing an old epoch.
    /// Callers should invoke this after sending a `CapHello` and receiving
    /// the peer's reply.
    pub fn record_session_epoch(&mut self, peer: GroupId, epoch: u64) {
        self.session_epochs.insert(peer, epoch);
    }

    /// Look up the session epoch we observed for a peer (defaults to 0).
    pub fn session_epoch(&self, peer: GroupId) -> u64 {
        self.session_epochs.get(&peer).copied().unwrap_or(0)
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
    /// # Safety / Trust
    ///
    /// **The `permissions` argument is a caller-supplied claim, not a fact**.
    /// This constructor performs no remote attestation: a holder of this URI
    /// can fabricate any [`AuthRequired`] value and the resulting `LiveRef`
    /// will *appear* to carry those permissions for downstream `send` /
    /// `pipeline` calls (which do not re-check). Earlier doc strings said
    /// "obtained from the remote's response to our enliven request" — that
    /// was misleading; no such request happens here. (AUDIT-sdk-rest.md P2-1.)
    ///
    /// This API only handles the LOCAL bookkeeping (GC tracking, session
    /// import). For permission claims that travel across a trust boundary,
    /// use [`Self::enliven_with_proof`] which verifies a signed
    /// [`HandoffCertificate`].
    ///
    /// # Arguments
    ///
    /// * `uri` - The parsed `PyanaUri` to enliven.
    /// * `permissions` - The caller's claim about what authority the import
    ///   carries. Trust class: same-process.
    pub fn enliven(&mut self, uri: &PyanaUri, permissions: AuthRequired) -> LiveRef {
        self.enliven_internal(uri, permissions)
    }

    /// Same as [`Self::enliven`] but explicitly named for the local-only use case.
    ///
    /// Identical semantics; the rename communicates the trust assumption to
    /// future readers.
    #[doc(hidden)]
    pub fn enliven_local(&mut self, uri: &PyanaUri, permissions: AuthRequired) -> LiveRef {
        self.enliven_internal(uri, permissions)
    }

    /// Enliven a sturdy reference URI by verifying a [`HandoffCertificate`].
    ///
    /// Unlike [`Self::enliven`], the permissions come from the certificate
    /// (which was signed by the introducer) rather than from a caller claim.
    /// The certificate is verified end-to-end:
    /// 1. The introducer's signature over the certificate must verify under
    ///    `introducer_pk`.
    /// 2. The certificate's `target_federation` / `target_cell` must match the
    ///    URI's `federation_id` / `cell_id`.
    /// 3. The certificate's `recipient_pk` must equal the supplied
    ///    `recipient_pk` (binds the certificate to us).
    /// 4. If `expires_at` is set on the certificate, the configured
    ///    `current_height` must be strictly less than it.
    ///
    /// On success the returned `LiveRef` carries the permissions named in the
    /// certificate, not a caller claim.
    ///
    /// # Errors
    ///
    /// Returns [`SdkError::Wire`] if any of the four checks above fails.
    pub fn enliven_with_proof(
        &mut self,
        uri: &PyanaUri,
        handoff_cert: &HandoffCertificate,
        introducer_pk: &pyana_types::PublicKey,
        recipient_pk: &[u8; 32],
    ) -> Result<LiveRef, SdkError> {
        // (1) Signature verification.
        if !handoff_cert.verify_signature(introducer_pk) {
            return Err(SdkError::Wire(
                "handoff certificate signature verification failed".into(),
            ));
        }

        // (2) URI ↔ certificate target match.
        if handoff_cert.target_federation.0 != uri.federation_id {
            return Err(SdkError::Wire(format!(
                "handoff certificate target_federation {:?} does not match URI federation {:?}",
                handoff_cert.target_federation.0, uri.federation_id,
            )));
        }
        if handoff_cert.target_cell.0 != uri.cell_id {
            return Err(SdkError::Wire(format!(
                "handoff certificate target_cell {:?} does not match URI cell {:?}",
                handoff_cert.target_cell.0, uri.cell_id,
            )));
        }

        // (3) Recipient binding.
        if &handoff_cert.recipient_pk != recipient_pk {
            return Err(SdkError::Wire(
                "handoff certificate recipient does not match the wallet enlivening it".into(),
            ));
        }

        // (4) Expiry (if set, current_height must be strictly less).
        if let Some(expires_at) = handoff_cert.expires_at {
            if self.config.current_height >= expires_at {
                return Err(SdkError::Wire(format!(
                    "handoff certificate expired at height {expires_at} \
                     (current height {})",
                    self.config.current_height,
                )));
            }
        }

        Ok(self.enliven_internal(uri, handoff_cert.permissions.clone()))
    }

    /// Internal helper: shared bookkeeping for all enliven entrypoints.
    fn enliven_internal(&mut self, uri: &PyanaUri, permissions: AuthRequired) -> LiveRef {
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

        let epoch = self
            .session_epochs
            .get(&federation_id)
            .copied()
            .unwrap_or(0);
        LiveRef {
            cell_id,
            federation_id,
            permissions,
            gc_manager: Arc::clone(&self.import_gc),
            pipeline_registry: Arc::clone(&self.pipeline_registry),
            import_table: Arc::clone(&self.import_table),
            outbox: Arc::clone(&self.outbox),
            local_federation: self.config.federation_id,
            session_epoch: epoch,
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

    /// Create a handoff certificate for offline capability delegation, with
    /// the introducer and target being the same federation (us). This is the
    /// "Alice introduces Bob to a cell on Alice" topology.
    ///
    /// For the full OCapN Alice→Bob→Carol topology (where the introducer's
    /// federation differs from the target's), use
    /// [`Self::create_handoff_for_remote`]: it parameterizes
    /// `target_federation` and accepts a pre-registered `swiss` number so a
    /// caller that already negotiated a swiss with the target federation can
    /// mint a cross-federation handoff certificate without needing to host
    /// the target cell themselves.
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

    /// Create a handoff certificate naming a **remote** target federation.
    ///
    /// This is the OCapN three-party (Alice→Bob→Carol) topology: the
    /// introducer (us) authorizes a recipient (Bob) to enliven a cell on a
    /// remote federation (Carol). The caller must have already pre-registered
    /// a swiss number at the target federation out-of-band (typically via
    /// a prior CapTP session or a custodial swiss-registration flow); the
    /// `swiss` argument carries it.
    ///
    /// Closes audit GAP-1 (three-party handoff non-constructible).
    ///
    /// # Arguments
    ///
    /// * `signing_key` - The introducer's signing key.
    /// * `target_federation` - The federation hosting the cell (Carol).
    /// * `target_cell` - The cell being delegated, on `target_federation`.
    /// * `recipient_pk` - The recipient's Ed25519 public key (Bob).
    /// * `permissions` - Permissions to delegate.
    /// * `allowed_effects` - Optional effect-mask restriction.
    /// * `expires_at` - Optional expiration height.
    /// * `max_uses` - Optional max presentation count.
    /// * `swiss` - The pre-registered swiss number at `target_federation`.
    #[allow(clippy::too_many_arguments)]
    pub fn create_handoff_for_remote(
        &self,
        signing_key: &pyana_types::SigningKey,
        target_federation: GroupId,
        target_cell: CellId,
        recipient_pk: [u8; 32],
        permissions: AuthRequired,
        allowed_effects: Option<pyana_cell::EffectMask>,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
        swiss: [u8; 32],
    ) -> HandoffCertificate {
        HandoffCertificate::create(
            signing_key,
            self.config.federation_id,
            target_federation,
            target_cell,
            recipient_pk,
            permissions,
            allowed_effects,
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
    /// returning a new EventualRef for the result. The action is queued in
    /// the local pipeline registry (so local breakage cascades work) **and**
    /// emitted as a `WireMessage::PipelinedMsg` in the shared outbox so the
    /// remote federation actually receives it. (Closes audit GAP-4.)
    pub fn pipeline_to(
        &mut self,
        eventual: &EventualRef,
        action: PipelinedAction,
    ) -> Result<EventualRef, SdkError> {
        let local_fed = self.config.federation_id;
        let epoch = self
            .session_epochs
            .get(&eventual.target_federation)
            .copied()
            .unwrap_or(0);

        let result_promise = {
            let mut registry = self.pipeline_registry.lock().expect("pipeline lock");

            let result_promise = registry.create_promise();

            let msg = pyana_captp::pipeline::PipelinedMessage {
                target_promise_id: eventual.promise_id,
                action: action.clone(),
                result_promise_id: Some(result_promise),
                sender: local_fed,
            };
            registry
                .pipeline_message(msg)
                .map_err(|e| SdkError::Wire(format!("pipeline error: {e}")))?;
            result_promise
        };

        // Emit the wire message so the remote actually gets the pipelined
        // action. The target_promise_id is the promise as known on the
        // sender's side; the receiving server bridges through its
        // CrossFedPipelineBridge which dual-keys (local + per-peer).
        let wire = WireMessage::PipelinedMsg {
            target_promise_id: eventual.promise_id,
            method: action.method,
            args: action.args,
            authorization: action.authorization,
            result_promise_id: Some(result_promise),
            sender_federation: local_fed.0,
            session_epoch: epoch,
        };
        self.outbox.lock().expect("outbox lock").push(wire);

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

    /// P2-1: `enliven_with_proof` accepts a valid handoff cert and binds the
    /// LiveRef's permissions to the cert (not to a caller claim).
    #[test]
    fn enliven_with_proof_accepts_valid_cert() {
        let mut introducer = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, intro_pk) = pyana_types::generate_keypair();
        let (_recipient_sk, recipient_pk) = pyana_types::generate_keypair();

        // Introducer creates a cert for the recipient.
        let cert = introducer.create_handoff(
            &signing_key,
            cell,
            recipient_pk.0,
            AuthRequired::Signature,
            Some(500),
            Some(3),
        );

        // Recipient holds their own client (different config).
        let mut recipient = CapTpClient::new(CapTpConfig {
            federation_id: GroupId([0x11; 32]),
            current_height: 100,
        });
        let uri = PyanaUri {
            federation_id: introducer.config.federation_id.0,
            cell_id: cell.0,
            swiss: cert.swiss,
        };

        let live_ref = recipient
            .enliven_with_proof(&uri, &cert, &intro_pk, &recipient_pk.0)
            .expect("valid cert must enliven");
        assert_eq!(live_ref.cell_id(), cell);
        assert_eq!(live_ref.permissions(), &AuthRequired::Signature);
    }

    /// P2-1: tampered cert (mutated permissions after signing) must be rejected.
    #[test]
    fn enliven_with_proof_rejects_tampered_cert() {
        let mut introducer = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, intro_pk) = pyana_types::generate_keypair();
        let (_recipient_sk, recipient_pk) = pyana_types::generate_keypair();

        let mut cert = introducer.create_handoff(
            &signing_key,
            cell,
            recipient_pk.0,
            AuthRequired::Signature,
            None,
            None,
        );
        // Tamper: try to escalate permissions to `None` (more permissive).
        cert.permissions = AuthRequired::None;

        let mut recipient = CapTpClient::new(CapTpConfig {
            federation_id: GroupId([0x11; 32]),
            current_height: 100,
        });
        let uri = PyanaUri {
            federation_id: introducer.config.federation_id.0,
            cell_id: cell.0,
            swiss: cert.swiss,
        };

        let result = recipient.enliven_with_proof(&uri, &cert, &intro_pk, &recipient_pk.0);
        assert!(result.is_err(), "tampered cert must be rejected");
        let msg = format!("{}", result.err().unwrap());
        assert!(
            msg.contains("signature"),
            "expected signature failure, got: {msg}"
        );
    }

    /// P2-1: cert with non-matching `recipient_pk` must be rejected.
    #[test]
    fn enliven_with_proof_rejects_wrong_recipient() {
        let mut introducer = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, intro_pk) = pyana_types::generate_keypair();
        let (_alice_sk, alice_pk) = pyana_types::generate_keypair();
        let (_mallory_sk, mallory_pk) = pyana_types::generate_keypair();

        // Cert is for Alice.
        let cert = introducer.create_handoff(
            &signing_key,
            cell,
            alice_pk.0,
            AuthRequired::Signature,
            None,
            None,
        );

        // Mallory tries to enliven against it.
        let mut mallory = CapTpClient::new(CapTpConfig {
            federation_id: GroupId([0x22; 32]),
            current_height: 100,
        });
        let uri = PyanaUri {
            federation_id: introducer.config.federation_id.0,
            cell_id: cell.0,
            swiss: cert.swiss,
        };

        let result = mallory.enliven_with_proof(&uri, &cert, &intro_pk, &mallory_pk.0);
        assert!(result.is_err(), "wrong recipient must be rejected");
        let msg = format!("{}", result.err().unwrap());
        assert!(
            msg.contains("recipient"),
            "expected recipient mismatch, got: {msg}"
        );
    }

    /// P2-1: cert whose target_cell does not match the URI must be rejected.
    #[test]
    fn enliven_with_proof_rejects_uri_mismatch() {
        let mut introducer = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, intro_pk) = pyana_types::generate_keypair();
        let (_recipient_sk, recipient_pk) = pyana_types::generate_keypair();

        let cert = introducer.create_handoff(
            &signing_key,
            cell,
            recipient_pk.0,
            AuthRequired::Signature,
            None,
            None,
        );

        let mut recipient = CapTpClient::new(CapTpConfig {
            federation_id: GroupId([0x11; 32]),
            current_height: 100,
        });
        // URI with a different cell_id.
        let uri = PyanaUri {
            federation_id: introducer.config.federation_id.0,
            cell_id: [0x99; 32],
            swiss: cert.swiss,
        };

        let result = recipient.enliven_with_proof(&uri, &cert, &intro_pk, &recipient_pk.0);
        assert!(result.is_err(), "URI/cert target mismatch must be rejected");
        let msg = format!("{}", result.err().unwrap());
        assert!(
            msg.contains("target_cell"),
            "expected URI mismatch error, got: {msg}"
        );
    }

    /// P2-1: expired cert must be rejected.
    #[test]
    fn enliven_with_proof_rejects_expired() {
        let mut introducer = CapTpClient::new(test_config());
        let cell = test_cell();
        let (signing_key, intro_pk) = pyana_types::generate_keypair();
        let (_recipient_sk, recipient_pk) = pyana_types::generate_keypair();

        // Cert that expires at height 50.
        let cert = introducer.create_handoff(
            &signing_key,
            cell,
            recipient_pk.0,
            AuthRequired::Signature,
            Some(50),
            None,
        );

        // Recipient at current_height = 100 > 50.
        let mut recipient = CapTpClient::new(CapTpConfig {
            federation_id: GroupId([0x11; 32]),
            current_height: 100,
        });
        let uri = PyanaUri {
            federation_id: introducer.config.federation_id.0,
            cell_id: cell.0,
            swiss: cert.swiss,
        };

        let result = recipient.enliven_with_proof(&uri, &cert, &intro_pk, &recipient_pk.0);
        assert!(result.is_err(), "expired cert must be rejected");
        let msg = format!("{}", result.err().unwrap());
        assert!(msg.contains("expired"), "expected expiry error, got: {msg}");
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

    // =========================================================================
    // Wire-delivery seam tests (GAP-4, GAP-9, GAP-7, GAP-1 closure)
    // =========================================================================

    /// GAP-4: `LiveRef::send` now emits a `WireMessage::PipelinedMsg` on the
    /// shared outbox in addition to allocating a local promise id.
    #[test]
    fn live_ref_send_enqueues_wire_message() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };
        let live_ref = client.enliven(&uri, AuthRequired::Signature);
        let _eventual = live_ref.send(make_action("hello"));

        let drained = client.drain_wire_outbox();
        assert_eq!(drained.len(), 1, "expected exactly one wire message");
        match &drained[0] {
            WireMessage::PipelinedMsg {
                method,
                sender_federation,
                result_promise_id,
                ..
            } => {
                assert_eq!(method, "hello");
                // The sender stamp is our local federation id.
                assert_eq!(*sender_federation, [0xAA; 32]);
                assert!(result_promise_id.is_some());
            }
            other => panic!("expected PipelinedMsg, got {:?}", other.variant_name()),
        }
    }

    /// GAP-4: `LiveRef::pipeline` distinguishes from send by queueing a local
    /// pipeline message AND emitting a wire message.
    #[test]
    fn live_ref_pipeline_enqueues_wire_message() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };
        let live_ref = client.enliven(&uri, AuthRequired::Signature);
        let _eventual = live_ref.pipeline(make_action("chain_step"));

        let drained = client.drain_wire_outbox();
        assert_eq!(drained.len(), 1);
        assert!(matches!(drained[0], WireMessage::PipelinedMsg { .. }));
    }

    /// GAP-4: `CapTpClient::pipeline_to` emits a wire message stamped with the
    /// peer's session epoch.
    #[test]
    fn pipeline_to_emits_wire_message_with_epoch() {
        let mut client = CapTpClient::new(test_config());
        let peer = GroupId([0xCC; 32]);
        client.record_session_epoch(peer, 7);

        let actions = vec![make_action("first")];
        let eventual = client.pipeline(peer, actions).unwrap();
        // pipeline() is local-only; clear the outbox.
        let _ = client.drain_wire_outbox();

        let _chained = client
            .pipeline_to(&eventual, make_action("second"))
            .unwrap();
        let drained = client.drain_wire_outbox();
        assert_eq!(drained.len(), 1);
        match &drained[0] {
            WireMessage::PipelinedMsg {
                method,
                session_epoch,
                ..
            } => {
                assert_eq!(method, "second");
                assert_eq!(*session_epoch, 7);
            }
            _ => panic!("expected PipelinedMsg"),
        }
    }

    /// GAP-9: dropping a LiveRef emits a `WireMessage::DropRemoteRef` on the
    /// shared outbox.
    #[test]
    fn live_ref_drop_emits_drop_remote_ref() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };
        {
            let _live_ref = client.enliven(&uri, AuthRequired::Signature);
        }
        // After the live_ref is dropped, the outbox should have a
        // DropRemoteRef stamped with our local federation id.
        let drained = client.drain_wire_outbox();
        assert_eq!(drained.len(), 1);
        match &drained[0] {
            WireMessage::DropRemoteRef {
                from_strand,
                cell_id,
                ..
            } => {
                assert_eq!(*from_strand, [0xAA; 32]);
                assert_eq!(*cell_id, [0xDD; 32]);
            }
            _ => panic!("expected DropRemoteRef"),
        }
    }

    /// GAP-9: explicit `release` also emits the wire DropRemoteRef.
    #[test]
    fn live_ref_release_emits_drop_remote_ref() {
        let mut client = CapTpClient::new(test_config());
        let uri = PyanaUri {
            federation_id: [0xCC; 32],
            cell_id: [0xDD; 32],
            swiss: [0xEE; 32],
        };
        let mut live_ref = client.enliven(&uri, AuthRequired::Signature);
        let dm = live_ref.release();
        assert!(dm.is_some());

        let drained = client.drain_wire_outbox();
        assert_eq!(drained.len(), 1);
        assert!(matches!(drained[0], WireMessage::DropRemoteRef { .. }));
    }

    /// GAP-1: `create_handoff_for_remote` allows constructing a cert whose
    /// `target_federation` is **not** the introducer's federation — the OCapN
    /// three-party Alice→Bob→Carol topology.
    #[test]
    fn create_handoff_for_remote_supports_three_party() {
        let alice_fed = GroupId([0xAA; 32]);
        let carol_fed = GroupId([0xCC; 32]); // remote target
        let alice = CapTpClient::new(CapTpConfig {
            federation_id: alice_fed,
            current_height: 100,
        });
        let (signing_key, _intro_pk) = pyana_types::generate_keypair();
        let recipient_pk = [0xBB; 32]; // bob
        let target_cell = CellId([0x42; 32]);
        let pre_registered_swiss = [0x77; 32];

        let cert = alice.create_handoff_for_remote(
            &signing_key,
            carol_fed,
            target_cell,
            recipient_pk,
            AuthRequired::Signature,
            None,
            Some(500),
            Some(3),
            pre_registered_swiss,
        );

        assert_eq!(cert.introducer, alice_fed, "introducer is alice");
        assert_eq!(cert.target_federation, carol_fed, "target is carol");
        assert_ne!(
            cert.introducer, cert.target_federation,
            "GAP-1: cert spans federations"
        );
        assert_eq!(cert.target_cell, target_cell);
        assert_eq!(cert.swiss, pre_registered_swiss);
    }
}
