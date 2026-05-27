//! Node state management.
//!
//! Holds the AgentCipherclerk, Ledger, and PersistentStore handles behind
//! Arc<RwLock<>> for concurrent access from HTTP handlers and the
//! federation sync background task.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use tokio::sync::{RwLock, broadcast};

use dregg_cell::{CellId, Ledger};
use dregg_circuit::field::BabyBear;
use dregg_commit::accumulator::PolynomialAccumulator;
use dregg_coord::Coordinator;
use dregg_coord::budget::{
    BudgetError, FastUnlockManager, SiloId, SpendingCertificate, StingrayCounter,
    UnlockCertificate, UnlockRequest, UnlockVote,
};
use dregg_dsl_runtime::ProgramRegistry;
use dregg_persist::{PersistentStore, Poseidon2NoteTree};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::WitnessedReceipt;

use crate::gossip::GossipHandle;
use crate::routing_table::RoutingTable;

// =============================================================================
// Events (broadcast to WebSocket clients)
// =============================================================================

/// Events emitted when node state changes, broadcast to WebSocket subscribers.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum NodeEvent {
    /// A new attested root was received from the federation.
    Root {
        height: u64,
        merkle_root: String,
        timestamp: i64,
    },
    /// A token was revoked.
    Revocation { token_id: String },
    /// A new receipt was appended to the local chain.
    Receipt { hash: String },
    /// An intent was received (from WS or HTTP) and added to the pool.
    Intent { intent: serde_json::Value },
}

/// Shared node state accessible from all async tasks.
#[derive(Clone)]
pub struct NodeState {
    inner: Arc<RwLock<NodeStateInner>>,
    /// Broadcast channel for real-time events (WebSocket push).
    events_tx: broadcast::Sender<NodeEvent>,
    /// Optional gossip handle (set after federation sync starts).
    gossip: Arc<RwLock<Option<GossipHandle>>>,
}

/// The inner mutable state of the node.
pub struct NodeStateInner {
    /// The agent cipherclerk (identity, wallet, receipts).
    pub cclerk: AgentCipherclerk,
    /// The cell ledger (local cell state).
    pub ledger: Ledger,
    /// Persistent storage backend.
    pub store: PersistentStore,
    /// Federation peer addresses.
    pub peers: Vec<String>,
    /// Whether the cipherclerk is unlocked for signing operations.
    pub unlocked: bool,
    /// Argon2id hash of the cipherclerk passphrase in PHC string format, set on first
    /// `set-passphrase` call. When `Some`, unlock attempts must verify against
    /// this hash. When `None`, the first unlock sets the passphrase.
    pub passphrase_hash: Option<String>,
    /// Bearer token seed derived from the passphrase + salt via BLAKE3.
    /// Stored separately so the bearer token can be computed without re-hashing.
    pub bearer_seed: Option<[u8; 32]>,
    /// Local intent pool: content-addressed ID -> validated Intent.
    pub intent_pool: HashMap<[u8; 32], dregg_intent::Intent>,
    /// Queue of signed turns ready for consensus ordering.
    /// Turns are added here when they require multi-party agreement (e.g.,
    /// fulfillment turns, cross-cell operations). The blocklace sync driver
    /// drains this queue when assembling new blocks.
    pub consensus_queue: Vec<dregg_sdk::SignedTurn>,
    /// Pending conditional turns awaiting proof resolution.
    /// Garbage-collected on access when timeout_height is exceeded.
    pub pending_conditionals: Vec<dregg_turn::ConditionalTurn>,
    /// Registry of pending turns with distributed promise semantics.
    /// Tracks turns awaiting async resolution (cross-federation receipts, height
    /// conditions, etc.) and propagates broken promises to dependents.
    pub pending_turns: dregg_turn::PendingTurnRegistry,
    /// Set of proof hashes that have already been used (nullifiers).
    /// Prevents the same proof from satisfying multiple conditional turns.
    pub used_proof_hashes: HashSet<[u8; 32]>,
    /// Known federation public keys for attested root quorum verification.
    ///
    /// Per FEDERATION-UNIFICATION-DESIGN.md §5/§8 this is now a *derived*
    /// view over [`Self::known_federations`]; for backward compat with the
    /// ~30 call sites that read this Vec it stays as a real field, kept in
    /// sync by [`Self::set_federation_keys`] / [`Self::register_federation`].
    pub known_federation_keys: Vec<dregg_types::PublicKey>,
    /// Registry of federations the local node knows about (both the local
    /// federation and any peer federations registered out-of-band).
    /// Replaces the disjoint pair of (known_federation_keys, federation_id)
    /// per the unification design §3.
    pub known_federations: dregg_federation::KnownFederations,
    /// Whether federation keys have been configured. When `false`, the node operates
    /// in "discovery mode" and will not finalize attested roots (Issue 10).
    pub federation_configured: bool,
    /// Canonical federation_id — derived from `known_federation_keys` +
    /// `committee_epoch` via [`dregg_federation::derive_federation_id_with_epoch`].
    /// Recomputed whenever the committee changes via [`Self::set_federation_keys`].
    /// Closes audit F1: this id is bound to the committee, not a random tag.
    pub federation_id: [u8; 32],
    /// Current committee epoch (rotates with key rotations).
    pub committee_epoch: u64,
    /// Maximum age (in seconds) for accepting incoming attested roots. Default: 3600.
    pub max_root_age_secs: u64,
    /// This validator's threshold decryption key share (Phase 2 turn privacy).
    /// Set during epoch initialization when the validator receives their share
    /// from the key generation ceremony.
    pub threshold_key_share: Option<dregg_federation::KeyShare>,
    /// Threshold required for decryption (t in t-of-n).
    pub decryption_threshold: usize,
    /// Pending decryption shares for encrypted turns awaiting collaborative decryption.
    /// Key: ciphertext_id, Value: collected shares so far.
    pub pending_decryption_shares: HashMap<[u8; 32], Vec<dregg_federation::DecryptionShare>>,
    /// Local routing table populated from RoutingDirectives in turn receipts.
    /// Maps CellId -> reachable peers, enabling three-party introductions to
    /// produce actual network-level connectivity.
    pub routing_table: RoutingTable,
    /// Whether automatic pruning is enabled (--enable-pruning flag).
    /// When true, old blocks/roots/audit entries are deleted after each checkpoint.
    /// Archival nodes should leave this false.
    pub pruning_enabled: bool,
    /// Checkpoint interval in blocks. Defaults to 1000.
    pub checkpoint_interval: u64,
    /// Whether to generate STARK proofs of block state transitions (--prove-transitions).
    /// When true, after each finalized block the node generates a transition proof
    /// and gossips it to peers.
    pub prove_transitions: bool,
    /// Cached PIR intent index. Invalidated on intent pool mutations.
    /// Avoids O(n) rebuild on every PIR request (prevents CPU DoS).
    pub pir_index_cache: Option<dregg_intent::pir::IntentIndex>,

    /// Persistent discharge gateway instance for replay prevention.
    /// SECURITY: This MUST persist across requests so the `issued` set actually
    /// tracks previously-discharged tickets. Creating a fresh gateway per request
    /// (the old behavior) made the replay set useless since it was dropped immediately.
    pub discharge_gateway: Option<dregg_macaroon::DischargeGateway>,

    /// Program registry for the smart contract runtime (DSL circuit programs).
    /// Maps verification key hashes to deployed CellPrograms. Used by the executor
    /// to verify proof-carrying turns against custom programs.
    pub program_registry: ProgramRegistry,

    // ─── Stingray Budget Coordination ─────────────────────────────────────────
    /// Per-agent budget coordinators for bounded-counter resource metering.
    /// Each agent with an active budget slice has an entry here.
    /// The node's silo_id is derived from the node's public key.
    pub budget_coordinators: HashMap<CellId, StingrayCounter>,
    /// Fast unlock manager for releasing locked resources after 2PC aborts.
    pub fast_unlock_manager: Option<FastUnlockManager>,
    /// This node's silo ID (derived from public key, set at startup).
    pub silo_id: SiloId,
    /// Spending certificates accumulated during this epoch, awaiting submission
    /// at the next epoch boundary for rebalancing.
    pub pending_spending_certificates: Vec<SpendingCertificate>,
    /// Pending unlock requests from remote nodes awaiting quorum votes.
    pub pending_unlock_requests: Vec<UnlockRequest>,
    /// Budget epoch version (tracks coordinator rebalance cycles).
    pub budget_epoch: u64,

    // ─── Fast-Path Cell Lock Table ─────────────────────────────────────────────
    /// Cell lock table for the owned-cell fast path (LUTRIS-style).
    /// Maps (CellId, nonce) -> CellLockEntry. Used by the fast-path API endpoints
    /// and periodically expired by the federation sync background task.
    pub cell_lock_table: dregg_turn::CellLockTable,

    // ─── Atomic Multi-Party Turn Coordination ─────────────────────────────────
    /// Active 2PC coordinators keyed by proposal_id (hex string).
    /// Each entry holds the coordinator state machine plus creation timestamp
    /// for timeout-based expiry.
    pub atomic_proposals: HashMap<[u8; 32], ActiveProposal>,

    // ─── Cross-Federation Bridge State ───────────────────────────────────────
    /// Revocations from remote federations (federation_id -> set of revoked token hashes).
    /// Populated by the bridge node when it receives revocation messages from
    /// remote federation gossip networks.
    pub cross_federation_revocations: HashMap<[u8; 32], HashSet<[u8; 32]>>,

    // ─── Polynomial Accumulator for Non-Revocation ─────────────────────────────
    /// O(1) polynomial accumulator over all revoked token hashes (BabyBear elements).
    ///
    /// When the revocation set grows large (>1000 entries), clients can use
    /// `prove_not_revoked_accumulator()` from the SDK which produces a constant-size
    /// witness rather than the sorted-Merkle proof whose size grows with tree depth.
    ///
    /// Updated on every new revocation via `insert()`. The alpha challenge is
    /// derived via Fiat-Shamir from the current revocation set commitment.
    pub revocation_accumulator: Option<PolynomialAccumulator>,

    // ─── Poseidon2 Note Commitment Tree ────────────────────────────────────────
    /// ZK-friendly Poseidon2 Merkle tree tracking all note commitments.
    ///
    /// Used to produce membership proofs for note spending (NoteSpendingAir) and
    /// for stake proof verification on intent submission.
    ///
    /// Depth 16 supports up to 4^16 = ~4 billion notes.
    pub note_tree: Poseidon2NoteTree,

    // ─── Privacy Primitives ─────────────────────────────────────────────────────
    /// Encrypted intent pool: content-addressed ID -> EncryptedIntent.
    /// These are intents propagated via gossip with SSE search tokens for
    /// privacy-preserving matching (body hidden until a fulfiller matches tokens).
    pub encrypted_intent_pool: HashMap<[u8; 32], dregg_intent::sse::EncryptedIntent>,

    /// Trustless intent engine: the production-wired path for
    /// threshold-encrypted intent submission, t-of-n decryption,
    /// solver auction, challenge window, and atomic settlement.
    ///
    /// Replaces the unhardened `encrypted_intent_pool` for the federation-
    /// keyed trustless flow. The SSE pool above remains the
    /// single-recipient sealed-box pool (used by direct fulfiller match,
    /// not the batched auction).
    pub trustless_intent_engine: dregg_intent::trustless::TrustlessIntentEngine,

    /// Delay pool for timing decorrelation of fulfillment reveals.
    /// Items are accumulated and released in batches at fixed intervals to prevent
    /// timing correlation between intent matching and fulfillment publication.
    pub delay_pool: dregg_intent::delay_pool::DelayPool,

    // ─── Event Log (REST polling endpoint) ────────────────────────────────────
    /// Bounded ring buffer of recent committed events for the REST event stream
    /// endpoint (`GET /api/events?since_height=N`). Capped at `MAX_EVENT_LOG` entries.
    pub event_log: VecDeque<CommittedEvent>,

    /// Node-local witness artifacts keyed by receipt hash.
    ///
    /// MCP/devnet mutation paths can produce `WitnessedReceipt`s at commit time.
    /// Keeping them here lets later HTTP, explorer, and verifier flows retrieve
    /// the same artifact instead of relying on the original tool response.
    pub witnessed_receipts: HashMap<[u8; 32], Vec<WitnessedReceipt>>,
    witnessed_receipt_order: VecDeque<[u8; 32]>,

    /// Solo consensus state: nullifier log, height tracking, auto-upgrade detection.
    /// `Some(_)` when this node was configured as solo (committee of one)
    /// at startup. Per FEDERATION-UNIFICATION-DESIGN.md §5, "solo" is no
    /// longer a separate runtime mode enum — the presence of this state
    /// (and the inner `is_solo` flag) is the operational signal.
    pub solo_consensus: Option<dregg_federation::solo::SoloConsensusState>,
    /// Blocklace consensus handle (set after federation sync starts).
    pub blocklace_handle: Option<crate::blocklace_sync::BlocklaceHandle>,
}

/// Maximum number of events retained in the ring buffer for REST polling.
pub const MAX_EVENT_LOG: usize = 1000;
pub const MAX_WITNESSED_RECEIPTS: usize = 1000;

#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ActivityStatus {
    Committed,
    Rejected,
}

#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ActivityProofStatus {
    Proved,
    NotRequired,
    MissingPreState,
    ProofGenerationFailed,
    NotCommitted,
}

/// A committed event stored in the ring buffer for the REST event stream.
#[derive(Clone, Debug, serde::Serialize)]
pub struct CommittedEvent {
    /// Block height at which this event was committed.
    pub height: u64,
    /// Typed lifecycle status for explorer/devnet consumers.
    pub status: ActivityStatus,
    /// Typed proof status; null/absent proof material must not be read as proved.
    pub proof_status: ActivityProofStatus,
    /// Hex-encoded turn hash.
    pub turn_hash: String,
    /// Hex-encoded cell ID affected.
    pub cell_id: String,
    /// Effects applied (human-readable summary strings).
    pub effects: Vec<String>,
    /// Unix timestamp (seconds).
    pub timestamp: i64,
}

/// An active atomic proposal tracked by the node.
///
/// Wraps a `Coordinator` instance together with metadata needed for
/// timeout-based garbage collection and status reporting.
pub struct ActiveProposal {
    /// The 2PC coordinator state machine.
    pub coordinator: Coordinator,
    /// When this proposal was created (wall-clock, for expiry).
    pub created_at: Instant,
    /// The atomic forest associated with this proposal (kept for status/commit).
    pub forest: dregg_coord::AtomicForest,
}

/// Default proposal expiry: coordinators older than this are garbage-collected.
pub const PROPOSAL_EXPIRY_SECS: u64 = 120;

/// Summary of the cipherclerk state for the cipherclerk endpoint.
#[derive(Clone, Debug, serde::Serialize)]
pub struct CipherclerkStatus {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

impl NodeState {
    /// Create a new NodeState from a data directory path and peer list.
    ///
    /// Uses the default key file name "node.key" in the data directory.
    pub fn new(data_dir: &Path, peers: Vec<String>) -> Result<Self, String> {
        Self::new_with_key_file(data_dir, peers, "node.key")
    }

    /// Create a new NodeState with a configurable key file path.
    ///
    /// The `key_file` is resolved relative to `data_dir` unless it is an absolute path.
    ///
    /// Issue 4 fix: Loads the key file from the data directory to initialize
    /// the cipherclerk identity. If no key file exists, generates a fresh identity
    /// and writes the key (first-run behavior).
    ///
    /// Issue 3 fix: Loads persisted passphrase hash from the store.
    /// Issue 5 fix: Loads persisted proof hashes (nullifiers) from the store.
    pub fn new_with_key_file(
        data_dir: &Path,
        peers: Vec<String>,
        key_file: &str,
    ) -> Result<Self, String> {
        let db_path = data_dir.join("dregg.redb");
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        // Resolve key file path: absolute paths are used as-is,
        // relative paths are resolved from the data directory.
        let key_path = if std::path::Path::new(key_file).is_absolute() {
            std::path::PathBuf::from(key_file)
        } else {
            data_dir.join(key_file)
        };

        let cclerk = if key_path.exists() {
            let key_bytes_vec = std::fs::read(&key_path)
                .map_err(|e| format!("failed to read {}: {e}", key_path.display()))?;
            if key_bytes_vec.len() != 32 {
                return Err(format!(
                    "{} has invalid length: expected 32, got {}",
                    key_path.display(),
                    key_bytes_vec.len()
                ));
            }
            let mut key_bytes = [0u8; 32];
            key_bytes.copy_from_slice(&key_bytes_vec);
            AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key_bytes))
        } else {
            // First run: generate a key and persist it.
            let mut key_bytes = [0u8; 32];
            getrandom::fill(&mut key_bytes).map_err(|e| format!("getrandom failed: {e}"))?;
            std::fs::write(&key_path, key_bytes)
                .map_err(|e| format!("failed to write {}: {e}", key_path.display()))?;
            // Restrict file permissions to owner-only (0o600) to prevent other
            // users from reading the private key.
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = std::fs::Permissions::from_mode(0o600);
                std::fs::set_permissions(&key_path, perms).map_err(|e| {
                    format!("failed to set {} permissions: {e}", key_path.display())
                })?;
            }
            AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key_bytes))
        };

        // Issue 3: Load persisted passphrase hash from the store.
        // Migration: old BLAKE3 hashes are exactly 32 bytes; discard them and force
        // re-setup with Argon2id.
        let passphrase_hash = match store.get_config("passphrase_hash") {
            Ok(Some(bytes)) if bytes.len() > 32 => {
                // PHC string format (Argon2id) — keep it.
                String::from_utf8(bytes).ok()
            }
            Ok(Some(bytes)) if bytes.len() == 32 => {
                // Legacy BLAKE3 hash — discard and force re-setup.
                tracing::warn!(
                    "discarding legacy BLAKE3 passphrase hash; user must set a new passphrase"
                );
                let _ = store.set_config("passphrase_hash", &[]);
                let _ = store.set_config("bearer_seed", &[]);
                None
            }
            _ => None,
        };

        let bearer_seed = match store.get_config("bearer_seed") {
            Ok(Some(bytes)) if bytes.len() == 32 => {
                let mut seed = [0u8; 32];
                seed.copy_from_slice(&bytes);
                Some(seed)
            }
            _ => None,
        };

        // Issue 5: Load persisted proof hashes from the store.
        let used_proof_hashes = store.load_all_proof_hashes().unwrap_or_default();

        // Restore ledger from the latest checkpoint (if one exists).
        let ledger = match store.load_latest_ledger_checkpoint() {
            Ok(Some((height, restored_ledger))) => {
                tracing::info!(
                    checkpoint_height = height,
                    cells = restored_ledger.len(),
                    "restored ledger from checkpoint"
                );
                restored_ledger
            }
            Ok(None) => {
                tracing::info!("no ledger checkpoint found, starting with empty ledger");
                Ledger::new()
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    "failed to load ledger checkpoint, starting with empty ledger"
                );
                Ledger::new()
            }
        };
        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the cipherclerk's public key.
        let silo_id: SiloId = *blake3::hash(cclerk.public_key().as_bytes()).as_bytes();

        // Issue 10: Log a warning — node starts in discovery mode with no federation keys.
        tracing::warn!(
            "node starting with zero federation keys — operating in discovery mode. \
             Attested roots will NOT be finalized until federation keys are loaded."
        );

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                cclerk,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash,
                bearer_seed,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                pending_conditionals: Vec::new(),
                pending_turns: dregg_turn::PendingTurnRegistry::new(),
                used_proof_hashes,
                known_federation_keys: Vec::new(),
                known_federations: dregg_federation::KnownFederations::new(),
                federation_configured: false,
                federation_id: [0u8; 32],
                committee_epoch: 0,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: dregg_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                pir_index_cache: None,
                discharge_gateway: None,
                program_registry: ProgramRegistry::new(),
                budget_coordinators: HashMap::new(),
                fast_unlock_manager: None,
                silo_id,
                pending_spending_certificates: Vec::new(),
                pending_unlock_requests: Vec::new(),
                budget_epoch: 0,
                cell_lock_table: dregg_turn::CellLockTable::with_defaults(),
                atomic_proposals: HashMap::new(),
                cross_federation_revocations: HashMap::new(),
                revocation_accumulator: None,
                note_tree: Poseidon2NoteTree::with_depth(16),
                encrypted_intent_pool: HashMap::new(),
                trustless_intent_engine: dregg_intent::trustless::TrustlessIntentEngine::new(
                    // Defaults: 1-of-1 (solo); upgraded when threshold_key_share
                    // is configured via the federation epoch ceremony.
                    1, 1,
                ),
                delay_pool: dregg_intent::delay_pool::DelayPool::new(
                    dregg_intent::delay_pool::DelayPoolConfig::default(),
                ),
                event_log: VecDeque::new(),
                witnessed_receipts: HashMap::new(),
                witnessed_receipt_order: VecDeque::new(),
                solo_consensus: None,
                blocklace_handle: None,
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
        })
    }

    /// Create a NodeState with a pre-existing cipherclerk (restored from key material).
    #[allow(dead_code)]
    pub fn with_cclerk(
        data_dir: &Path,
        peers: Vec<String>,
        key_bytes: [u8; 32],
    ) -> Result<Self, String> {
        let db_path = data_dir.join("dregg.redb");
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        let cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key_bytes));

        // Restore ledger from the latest checkpoint (if one exists).
        let ledger = match store.load_latest_ledger_checkpoint() {
            Ok(Some((_height, restored_ledger))) => restored_ledger,
            _ => Ledger::new(),
        };

        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the cipherclerk's public key.
        let silo_id: SiloId = *blake3::hash(cclerk.public_key().as_bytes()).as_bytes();

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                cclerk,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash: None,
                bearer_seed: None,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                pending_conditionals: Vec::new(),
                pending_turns: dregg_turn::PendingTurnRegistry::new(),
                used_proof_hashes: HashSet::new(),
                known_federation_keys: Vec::new(),
                known_federations: dregg_federation::KnownFederations::new(),
                federation_configured: false,
                federation_id: [0u8; 32],
                committee_epoch: 0,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: dregg_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                pir_index_cache: None,
                discharge_gateway: None,
                program_registry: ProgramRegistry::new(),
                budget_coordinators: HashMap::new(),
                fast_unlock_manager: None,
                silo_id,
                pending_spending_certificates: Vec::new(),
                pending_unlock_requests: Vec::new(),
                budget_epoch: 0,
                cell_lock_table: dregg_turn::CellLockTable::with_defaults(),
                atomic_proposals: HashMap::new(),
                cross_federation_revocations: HashMap::new(),
                revocation_accumulator: None,
                note_tree: Poseidon2NoteTree::with_depth(16),
                encrypted_intent_pool: HashMap::new(),
                trustless_intent_engine: dregg_intent::trustless::TrustlessIntentEngine::new(
                    // Defaults: 1-of-1 (solo); upgraded when threshold_key_share
                    // is configured via the federation epoch ceremony.
                    1, 1,
                ),
                delay_pool: dregg_intent::delay_pool::DelayPool::new(
                    dregg_intent::delay_pool::DelayPoolConfig::default(),
                ),
                event_log: VecDeque::new(),
                witnessed_receipts: HashMap::new(),
                witnessed_receipt_order: VecDeque::new(),
                solo_consensus: None,
                blocklace_handle: None,
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
        })
    }

    /// Acquire a read lock on the inner state.
    pub async fn read(&self) -> tokio::sync::RwLockReadGuard<'_, NodeStateInner> {
        self.inner.read().await
    }

    /// Acquire a write lock on the inner state.
    pub async fn write(&self) -> tokio::sync::RwLockWriteGuard<'_, NodeStateInner> {
        self.inner.write().await
    }

    /// Get the current cipherclerk status.
    pub async fn cclerk_status(&self) -> CipherclerkStatus {
        let state = self.inner.read().await;
        let pk = state.cclerk.public_key();
        CipherclerkStatus {
            unlocked: state.unlocked,
            public_key: hex::encode(&pk.0),
            token_count: state.cclerk.tokens().len(),
            receipt_chain_length: state.cclerk.receipt_chain_length(),
        }
    }

    /// Subscribe to node events (returns a broadcast receiver).
    pub fn subscribe_events(&self) -> broadcast::Receiver<NodeEvent> {
        self.events_tx.subscribe()
    }

    /// Emit a node event to all connected WebSocket clients.
    pub fn emit(&self, event: NodeEvent) {
        // Ignore send errors (no active receivers is fine).
        let _ = self.events_tx.send(event);
    }

    pub async fn set_gossip(&self, handle: GossipHandle) {
        let mut g = self.gossip.write().await;
        *g = Some(handle);
    }

    /// Get a clone of the gossip handle, if available.
    pub async fn gossip(&self) -> Option<GossipHandle> {
        let g = self.gossip.read().await;
        g.clone()
    }

    /// Set the blocklace consensus handle.
    pub async fn set_blocklace(&self, handle: crate::blocklace_sync::BlocklaceHandle) {
        let mut s = self.inner.write().await;
        s.blocklace_handle = Some(handle);
    }

    /// Get a clone of the blocklace handle, if available.
    pub async fn blocklace(&self) -> Option<crate::blocklace_sync::BlocklaceHandle> {
        let s = self.inner.read().await;
        s.blocklace_handle.clone()
    }

    /// Persist critical state before shutdown.
    ///
    /// Note: Replay-prevention state (discharge issued set, proof nullifiers)
    /// is now persisted at USE time for crash safety. This shutdown hook serves
    /// as a final consistency checkpoint only.
    pub async fn persist_on_shutdown(&self) {
        let s = self.inner.read().await;
        if let Some(gateway) = &s.discharge_gateway {
            let data = gateway.serialize_issued_set();
            if !data.is_empty() {
                if let Err(e) = s.store.set_config("discharge_issued_set", &data) {
                    tracing::warn!(error = %e, "failed to persist discharge replay set on shutdown");
                } else {
                    tracing::info!(entries = data.len() / 32, "persisted discharge replay set");
                }
            }
        }

        // Checkpoint the ledger on shutdown for fast restart.
        let current_height = s
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        match s.store.checkpoint_ledger(&s.ledger, current_height) {
            Ok(()) => {
                tracing::info!(
                    height = current_height,
                    cells = s.ledger.len(),
                    "ledger checkpoint persisted on shutdown"
                );
            }
            Err(e) => {
                tracing::warn!(error = %e, "failed to persist ledger checkpoint on shutdown");
            }
        }
    }
}

// =============================================================================
// Atomic Proposal Management Methods
// =============================================================================

impl NodeStateInner {
    /// Append a committed event to the ring buffer, evicting the oldest if at capacity.
    pub fn push_event(&mut self, event: CommittedEvent) {
        if self.event_log.len() >= MAX_EVENT_LOG {
            self.event_log.pop_front();
        }
        self.event_log.push_back(event);
    }

    /// Store replay material for a committed receipt, evicting oldest receipt
    /// keys at capacity. Multiple witnesses may share one receipt hash, e.g. a
    /// bilateral turn with per-side witnessed receipts.
    pub fn push_witnessed_receipt(&mut self, receipt_hash: [u8; 32], witnessed: WitnessedReceipt) {
        if !self.witnessed_receipts.contains_key(&receipt_hash) {
            if self.witnessed_receipt_order.len() >= MAX_WITNESSED_RECEIPTS {
                if let Some(oldest) = self.witnessed_receipt_order.pop_front() {
                    self.witnessed_receipts.remove(&oldest);
                }
            }
            self.witnessed_receipt_order.push_back(receipt_hash);
        }
        self.witnessed_receipts
            .entry(receipt_hash)
            .or_default()
            .push(witnessed);
    }

    pub fn witnessed_receipt_count(&self, receipt_hash: &[u8; 32]) -> usize {
        self.witnessed_receipts
            .get(receipt_hash)
            .map(Vec::len)
            .unwrap_or(0)
    }

    /// Remove proposals older than `PROPOSAL_EXPIRY_SECS`.
    ///
    /// Called lazily from the proposal/vote handlers to bound memory usage.
    /// Returns the number of expired proposals removed.
    pub fn expire_stale_proposals(&mut self) -> usize {
        let now = Instant::now();
        let expiry = std::time::Duration::from_secs(PROPOSAL_EXPIRY_SECS);
        let before = self.atomic_proposals.len();
        self.atomic_proposals
            .retain(|_, p| now.duration_since(p.created_at) < expiry);
        before - self.atomic_proposals.len()
    }
}

// =============================================================================
// Budget Coordination Methods
// =============================================================================

impl NodeStateInner {
    /// Initialize or update a budget coordinator for an agent.
    ///
    /// Called when the node learns about an agent's budget allocation
    /// (e.g., from a genesis block or epoch transition). Sets up the
    /// bounded-counter slice for this silo.
    pub fn init_budget_coordinator(
        &mut self,
        agent: CellId,
        total_balance: u64,
        silos: Vec<SiloId>,
        byzantine_tolerance: usize,
    ) -> Result<(), BudgetError> {
        let mut coordinator =
            StingrayCounter::new(agent, total_balance, silos, byzantine_tolerance)?;

        // Register THIS node's silo pubkey so the coordinator can verify our
        // own spending certificates at rebalance time. Remote silos' pubkeys
        // must be registered separately before their certificates / unlock
        // votes will be accepted (fail-closed). Wiring that registry from
        // federation membership is out of scope for this lane.
        let my_pubkey = *self.cclerk.public_key().as_bytes();
        coordinator.register_silo_pubkey(self.silo_id, my_pubkey);

        self.budget_coordinators.insert(agent, coordinator);

        // Initialize fast unlock manager if not already present.
        if self.fast_unlock_manager.is_none() {
            let total_silos = self
                .budget_coordinators
                .values()
                .next()
                .map(|c| c.silos.len())
                .unwrap_or(4);
            let mut mgr = FastUnlockManager::new(byzantine_tolerance, total_silos);
            mgr.register_silo_pubkey(self.silo_id, my_pubkey);
            self.fast_unlock_manager = Some(mgr);
        } else if let Some(mgr) = self.fast_unlock_manager.as_mut() {
            mgr.register_silo_pubkey(self.silo_id, my_pubkey);
        }

        Ok(())
    }

    /// Try to debit from an agent's budget slice on this silo.
    ///
    /// This is the hot path called by the executor's budget gate: no coordination
    /// with other silos is needed as long as the local slice has budget remaining.
    ///
    /// On success, records the spending certificate for later epoch submission.
    pub fn try_budget_debit(
        &mut self,
        agent: &CellId,
        amount: u64,
        digest: [u8; 32],
    ) -> Result<(), BudgetError> {
        let silo_id = self.silo_id;
        let coordinator = self
            .budget_coordinators
            .get_mut(agent)
            .ok_or(BudgetError::UnknownSilo { silo: silo_id })?;
        coordinator.try_debit(silo_id, amount, digest)
    }

    /// Collect spending certificates from all local budget coordinators.
    ///
    /// Called at epoch boundaries to gather this silo's spending summaries
    /// for submission to the federation rebalancing process.
    pub fn collect_spending_certificates(&mut self) -> Vec<SpendingCertificate> {
        let silo_id = self.silo_id;
        let signing_key = self.cclerk.gossip_signing_key();
        let signing_key_bytes = &signing_key.to_bytes();
        let mut certificates = Vec::new();
        for coordinator in self.budget_coordinators.values() {
            if let Some(slice) = coordinator.silo_states.get(&silo_id) {
                if slice.spent > 0 {
                    certificates.push(slice.certificate(silo_id, signing_key_bytes));
                }
            }
        }
        certificates
    }

    /// Process received spending certificates and rebalance agent budgets.
    ///
    /// Called during epoch transitions when the federation has collected
    /// certificates from all (or enough) silos. Updates balances and
    /// redistributes slices for the new epoch.
    ///
    /// Returns a vector of (agent, total_spent) pairs for ledger settlement.
    pub fn rebalance_budgets(
        &mut self,
        all_certificates: &[SpendingCertificate],
    ) -> Vec<(CellId, u64)> {
        let mut settlements = Vec::new();

        // Group certificates by agent.
        let mut by_agent: HashMap<CellId, Vec<&SpendingCertificate>> = HashMap::new();
        for cert in all_certificates {
            by_agent.entry(cert.agent).or_default().push(cert);
        }

        // Rebalance each agent's coordinator.
        for (agent, certs) in by_agent {
            if let Some(coordinator) = self.budget_coordinators.get_mut(&agent) {
                let owned_certs: Vec<SpendingCertificate> = certs.into_iter().cloned().collect();
                match coordinator.rebalance(&owned_certs) {
                    Ok(total_spent) => {
                        if total_spent > 0 {
                            settlements.push((agent, total_spent));
                        }
                    }
                    Err(e) => {
                        tracing::warn!(
                            agent = %hex::encode(agent.as_bytes()),
                            error = %e,
                            "budget rebalance failed for agent"
                        );
                    }
                }
            }
        }

        self.budget_epoch += 1;
        self.pending_spending_certificates.clear();
        settlements
    }

    /// Create an unlock request for resources locked by a failed/aborted turn.
    ///
    /// The request is gossiped to other nodes for quorum voting.
    pub fn create_unlock_request(
        &self,
        proposal_id: [u8; 32],
        agent: CellId,
        amount: u64,
    ) -> UnlockRequest {
        UnlockRequest {
            proposal_id,
            agent,
            amount,
            requester: self.silo_id,
        }
    }

    /// Vote on an unlock request from a remote node.
    ///
    /// A node votes "no conflict" if it has NOT signed a commit for this proposal.
    /// Returns the vote to be gossiped back.
    pub fn vote_on_unlock(&self, request: &UnlockRequest) -> Option<UnlockVote> {
        let mgr = self.fast_unlock_manager.as_ref()?;
        // Check if we have a conflicting lock (i.e., we signed a commit for this proposal).
        let has_conflict = mgr.is_locked(&request.proposal_id);
        let signing_key = self.cclerk.gossip_signing_key();
        Some(mgr.vote_unlock(request, self.silo_id, has_conflict, &signing_key.to_bytes()))
    }

    /// Apply an unlock certificate that has achieved quorum.
    ///
    /// Releases the locked resources and refunds the budget slice.
    pub fn apply_unlock_certificate(
        &mut self,
        certificate: &UnlockCertificate,
    ) -> Result<u64, BudgetError> {
        let mgr = self
            .fast_unlock_manager
            .as_mut()
            .ok_or(BudgetError::LockNotFound {
                proposal_id: certificate.request.proposal_id,
            })?;
        let (amount, _silo) = mgr.apply_unlock_certificate(certificate)?;
        Ok(amount)
    }

    /// Check if a token is revoked in a remote federation.
    ///
    /// Used by the bridge to check cross-federation token revocation status
    /// before accepting tokens that originate from another federation.
    pub fn is_cross_federation_revoked(
        &self,
        federation_id: &[u8; 32],
        token_hash: &[u8; 32],
    ) -> bool {
        self.cross_federation_revocations
            .get(federation_id)
            .map(|set| set.contains(token_hash))
            .unwrap_or(false)
    }

    /// Add a revocation to the cross-federation revocation cache.
    pub fn add_cross_federation_revocation(
        &mut self,
        federation_id: [u8; 32],
        token_hash: [u8; 32],
    ) {
        self.cross_federation_revocations
            .entry(federation_id)
            .or_default()
            .insert(token_hash);
    }

    /// Load federation keys and mark the federation as configured.
    ///
    /// Once called with a non-empty key set, the node transitions out of
    /// "discovery mode" and will verify attested root quorum signatures.
    ///
    /// Also recomputes [`Self::federation_id`] as
    /// `derive_federation_id(keys, committee_epoch)` — closes audit F1.
    pub fn set_federation_keys(&mut self, keys: Vec<dregg_types::PublicKey>) {
        if keys.is_empty() {
            tracing::warn!(
                "set_federation_keys called with empty key set — remaining in discovery mode"
            );
            return;
        }
        let id = dregg_federation::derive_federation_id_with_epoch(&keys, self.committee_epoch);
        tracing::info!(
            key_count = keys.len(),
            committee_epoch = self.committee_epoch,
            federation_id = %dregg_types::hex_encode(&id),
            "federation keys loaded — exiting discovery mode; federation_id derived",
        );
        // Self-register the local federation in KnownFederations so receipt
        // verification can route through one lookup path for both own and
        // remote federations.
        let local_pk = self.cclerk.public_key();
        let threshold = dregg_federation::quorum_threshold(keys.len()) as u32;
        let local_seat = if keys.iter().any(|pk| pk.0 == local_pk.0) {
            let signing_key_bytes = self.cclerk.gossip_signing_key().to_bytes();
            let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
            Some(dregg_federation::LocalSeat {
                index: 0, // re-indexed by Federation::from_committee
                signing_key,
                bls_secret: None,
            })
        } else {
            None
        };
        let fed = dregg_federation::Federation::from_committee(
            keys.clone(),
            self.committee_epoch,
            threshold,
            None,
            local_seat,
        );
        self.known_federations.register(std::sync::Arc::new(fed));
        self.known_federation_keys = keys;
        self.federation_id = id;
        self.federation_configured = true;
    }

    /// Register a peer federation in [`Self::known_federations`].
    ///
    /// This is the canonical entry point for cross-federation receipt
    /// verification: once registered, `known_federations.verify_receipt(&r)`
    /// will succeed for any receipt carrying this federation's id.
    pub fn register_federation(&mut self, fed: std::sync::Arc<dregg_federation::Federation>) {
        let id = fed.id();
        tracing::info!(
            federation_id = %id.hex(),
            members = fed.members().len(),
            threshold = fed.threshold(),
            epoch = fed.epoch(),
            "registered federation in KnownFederations",
        );
        self.known_federations.register(fed);
    }

    /// Persist the known federations registry to `$DATA_DIR/known_federations/`.
    ///
    /// One JSON file per federation, named by its hex id. Append-only by
    /// convention.
    ///
    /// Schema-reconciliation note (P0 #87): writes the **canonical genesis
    /// descriptor schema** —
    /// `{federation_id, committee_epoch, threshold, validators: [{public_key}]}`
    /// — matching what `dregg-node register-federation` and `genesis.json`
    /// produce. Prior to this fix, this writer emitted `{epoch, members}`
    /// while the loader expected `{committee_epoch, validators[].public_key}`,
    /// causing every cross-federation descriptor to be silently dropped
    /// at startup.
    pub fn persist_known_federations(&self, data_dir: &std::path::Path) -> std::io::Result<()> {
        let dir = data_dir.join("known_federations");
        std::fs::create_dir_all(&dir)?;
        for (id, fed) in self.known_federations.iter() {
            let validators: Vec<serde_json::Value> = fed
                .members()
                .iter()
                .map(|pk| serde_json::json!({ "public_key": pk.hex() }))
                .collect();
            let descriptor = serde_json::json!({
                "federation_id": id.hex(),
                "committee_epoch": fed.epoch(),
                "threshold": fed.threshold(),
                "validators": validators,
                "is_local": fed.local_seat().is_some(),
            });
            let path = dir.join(format!("{}.json", id.hex()));
            std::fs::write(&path, serde_json::to_string_pretty(&descriptor)?)?;
        }
        Ok(())
    }

    /// Load known federations from `$DATA_DIR/known_federations/`.
    ///
    /// Accepts two on-disk schemas (P0 #87):
    ///   - Canonical (genesis / `register-federation`):
    ///     `{committee_epoch, threshold, validators: [{public_key: <hex>}]}`
    ///   - Legacy (pre-fix `persist_known_federations`):
    ///     `{epoch, threshold, members: [<hex>]}`
    ///
    /// A descriptor in either shape that yields ≥1 valid pubkey is
    /// registered. Descriptors with zero parseable pubkeys log a warning
    /// and are skipped. Both schemas are accepted so that nodes that
    /// previously wrote the legacy shape continue to load their on-disk
    /// state after upgrade.
    pub fn load_known_federations(&mut self, data_dir: &std::path::Path) -> std::io::Result<usize> {
        let dir = data_dir.join("known_federations");
        if !dir.exists() {
            return Ok(0);
        }
        let mut loaded = 0usize;
        for entry in std::fs::read_dir(&dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("json") {
                continue;
            }
            let text = std::fs::read_to_string(&path)?;
            let v: serde_json::Value = serde_json::from_str(&text)?;
            match parse_federation_descriptor(&v) {
                Some((members, epoch, threshold)) => {
                    let fed =
                        dregg_federation::Federation::verifier_only(members, epoch, threshold);
                    self.known_federations.register(std::sync::Arc::new(fed));
                    loaded += 1;
                }
                None => {
                    tracing::warn!(
                        path = %path.display(),
                        has_validators = v["validators"].is_array(),
                        has_members = v["members"].is_array(),
                        "skipping federation descriptor (no parseable pubkeys under validators[].public_key or members[]); this may be empty, corrupted, or an unrecognized schema. Cross-federation verification for this peer may be unavailable until fixed.",
                    );
                }
            }
        }
        tracing::info!(count = loaded, "loaded known_federations from disk");
        Ok(loaded)
    }

    /// Set the active committee epoch and recompute `federation_id`.
    pub fn set_committee_epoch(&mut self, epoch: u64) {
        self.committee_epoch = epoch;
        if !self.known_federation_keys.is_empty() {
            self.federation_id = dregg_federation::derive_federation_id_with_epoch(
                &self.known_federation_keys,
                epoch,
            );
            tracing::info!(
                committee_epoch = epoch,
                federation_id = %dregg_types::hex_encode(&self.federation_id),
                "committee epoch rotated — federation_id recomputed",
            );
        }
    }

    // =========================================================================
    // Revocation Accumulator Methods
    // =========================================================================

    /// Initialize the revocation accumulator from the current revocation set.
    ///
    /// Called at startup (after loading revocations from the store) or when
    /// the federation transitions to accumulator-based non-revocation proofs.
    ///
    /// The alpha challenge is derived via Fiat-Shamir from a domain separator
    /// and the BLAKE3 hash of all current revocation entries.
    pub fn init_revocation_accumulator(&mut self, revocation_hashes: &[BabyBear]) {
        // Compute a set commitment from the revocation hashes (deterministic).
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-revocation-accumulator-set-commitment");
        for h in revocation_hashes {
            hasher.update(&h.as_u32().to_le_bytes());
        }
        let set_commitment: [u8; 32] = *hasher.finalize().as_bytes();

        // Derive alpha using the accumulator's Fiat-Shamir construction.
        let domain = &[BabyBear::new(0x5059_414E)]; // "PYAN" domain tag
        let alpha = PolynomialAccumulator::derive_alpha(domain, &set_commitment);

        // Build the accumulator from the revocation set.
        let accumulator = PolynomialAccumulator::from_set(revocation_hashes, alpha);

        tracing::info!(
            set_size = revocation_hashes.len(),
            "revocation accumulator initialized"
        );

        self.revocation_accumulator = Some(accumulator);
    }

    /// Insert a newly-revoked hash into the polynomial accumulator.
    ///
    /// Called when a revocation message is received via gossip. The accumulator
    /// value is updated in O(1) (single extension-field multiplication).
    pub fn accumulator_insert_revocation(&mut self, revocation_hash: BabyBear) {
        if let Some(ref mut acc) = self.revocation_accumulator {
            acc.insert(revocation_hash);
        }
    }

    // =========================================================================
    // Poseidon2 Note Tree Methods
    // =========================================================================

    /// Append a note commitment (BLAKE3 bytes) to the Poseidon2 note tree.
    ///
    /// Converts the 32-byte BLAKE3 commitment to a BabyBear field element
    /// via Poseidon2 hashing, then appends to the 4-ary Merkle tree.
    ///
    /// Returns the position of the newly appended leaf.
    pub fn note_tree_append_commitment(&mut self, commitment: &[u8; 32]) -> usize {
        self.note_tree.append_blake3_commitment(commitment)
    }

    /// Get the current Poseidon2 note tree root.
    pub fn note_tree_root_value(&mut self) -> BabyBear {
        self.note_tree.root()
    }

    /// Generate a Poseidon2 Merkle membership proof for a note at the given position.
    ///
    /// The returned proof can be used as a witness in `NoteSpendingWitness` for
    /// STARK proof generation via `prove_note_spend`.
    pub fn note_tree_prove_membership(
        &self,
        position: usize,
    ) -> Option<dregg_commit::poseidon2_tree::Poseidon2MerkleProof> {
        self.note_tree.prove_membership(position)
    }
}

/// Minimal hex encoding (no extra dep needed).
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Parse a federation descriptor JSON value into `(members, epoch, threshold)`.
///
/// Accepts both the canonical genesis schema
/// (`{committee_epoch, threshold, validators: [{public_key}]}`) and the
/// legacy `persist_known_federations` schema
/// (`{epoch, threshold, members: [hex]}`). Returns `None` if the
/// descriptor has zero parseable 32-byte pubkeys, mirroring the
/// reject-on-empty-members guard the loader has always enforced.
///
/// Extracted as a standalone function so the schema-discrimination
/// behavior (P0 #87) can be exercised by unit tests without constructing
/// a full `NodeStateInner`. The loader (`load_known_federations`) is the
/// only caller.
pub(crate) fn parse_federation_descriptor(
    v: &serde_json::Value,
) -> Option<(Vec<dregg_types::PublicKey>, u64, u32)> {
    let epoch = v["committee_epoch"]
        .as_u64()
        .or_else(|| v["epoch"].as_u64())
        .unwrap_or(0);
    let threshold = v["threshold"].as_u64().unwrap_or(1) as u32;
    let members_hex: Vec<String> = if let Some(vals) = v["validators"].as_array() {
        vals.iter()
            .filter_map(|val| val["public_key"].as_str().map(str::to_string))
            .collect()
    } else if let Some(mems) = v["members"].as_array() {
        mems.iter()
            .filter_map(|x| x.as_str().map(str::to_string))
            .collect()
    } else {
        Vec::new()
    };
    let members: Vec<dregg_types::PublicKey> = members_hex
        .iter()
        .filter_map(|h| {
            if h.len() != 64 {
                return None;
            }
            // Use the same robust hex decode pattern as hex_decode_32 in main.rs
            // (from_str_radix) rather than the previous char-cast + to_digit
            // version. This eliminates a source of spurious "malformed descriptor"
            // skips for valid cross-federation descriptors written by
            // register-federation or genesis flows. Inconsistent decode impls
            // were a latent footgun for operators running multi-federation setups.
            let mut out = [0u8; 32];
            let mut ok = true;
            for (i, byte) in out.iter_mut().enumerate() {
                match u8::from_str_radix(&h[i * 2..i * 2 + 2], 16) {
                    Ok(b) => *byte = b,
                    Err(_) => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                Some(dregg_types::PublicKey(out))
            } else {
                None
            }
        })
        .collect();
    if members.is_empty() {
        return None;
    }
    Some((members, epoch, threshold))
}

#[cfg(test)]
mod federation_descriptor_tests {
    //! Regression tests for the federation-descriptor schema-mismatch
    //! bug (#87 / MULTI-NODE-DEVNET-RUN.md §5.2): the on-disk descriptor
    //! schema used `{committee_epoch, validators[].public_key}` while
    //! the loader expected `{epoch, members[]}`, silently dropping every
    //! peer federation at startup. This test pins the fix.
    use super::parse_federation_descriptor;
    use serde_json::json;

    fn pk_hex(byte: u8) -> String {
        let bytes = [byte; 32];
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn canonical_genesis_schema_parses() {
        // The exact shape `node register-federation` writes (and
        // `genesis.json` emits) to `<data-dir>/known_federations/`.
        let v = json!({
            "federation_id": pk_hex(0xAA),
            "committee_epoch": 7,
            "threshold": 3,
            "validators": [
                { "public_key": pk_hex(0x01) },
                { "public_key": pk_hex(0x02) },
                { "public_key": pk_hex(0x03) },
                { "public_key": pk_hex(0x04) },
            ],
        });
        let parsed = parse_federation_descriptor(&v).expect("canonical schema must parse");
        let (members, epoch, threshold) = parsed;
        assert_eq!(
            epoch, 7,
            "committee_epoch must round-trip as the federation epoch"
        );
        assert_eq!(threshold, 3);
        assert_eq!(members.len(), 4, "all 4 validators must register");
        assert_eq!(members[0].0[0], 0x01);
        assert_eq!(members[3].0[0], 0x04);
    }

    #[test]
    fn legacy_members_schema_still_parses_for_backward_compat() {
        // Older nodes wrote this shape via `persist_known_federations`
        // before P0 #87 reconciled the writer to the genesis schema.
        // The loader must still accept these descriptors so on-disk
        // state from a pre-fix run survives the upgrade.
        let v = json!({
            "federation_id": pk_hex(0xBB),
            "epoch": 2,
            "threshold": 1,
            "members": [pk_hex(0x10), pk_hex(0x20)],
        });
        let parsed = parse_federation_descriptor(&v).expect("legacy schema must still parse");
        let (members, epoch, threshold) = parsed;
        assert_eq!(epoch, 2);
        assert_eq!(threshold, 1);
        assert_eq!(members.len(), 2);
        assert_eq!(members[0].0[0], 0x10);
        assert_eq!(members[1].0[0], 0x20);
    }

    #[test]
    fn empty_descriptor_is_rejected() {
        // Defensive: a descriptor with neither field, or with both
        // present-but-empty, yields None so the loader skips it
        // rather than registering a zero-validator federation.
        assert!(parse_federation_descriptor(&json!({})).is_none());
        assert!(parse_federation_descriptor(&json!({ "validators": [] })).is_none());
        assert!(parse_federation_descriptor(&json!({ "members": [] })).is_none());
    }

    #[test]
    fn mixed_load_counts_descriptors_in_both_schemas() {
        // End-to-end: write one descriptor in each schema to a temp
        // dir, run the loader, and confirm count == 2. This is the
        // "loaded known_federations from disk count=0" warning from
        // MULTI-NODE-DEVNET-RUN.md becoming "count=2".
        let tmp =
            std::env::temp_dir().join(format!("dregg-fed-descriptor-test-{}", std::process::id()));
        let dir = tmp.join("known_federations");
        std::fs::create_dir_all(&dir).unwrap();

        // Canonical-schema descriptor.
        let id_a = pk_hex(0xAA);
        let canonical = json!({
            "federation_id": id_a,
            "committee_epoch": 1,
            "threshold": 1,
            "validators": [{ "public_key": pk_hex(0x01) }],
        });
        std::fs::write(
            dir.join(format!("{id_a}.json")),
            serde_json::to_string_pretty(&canonical).unwrap(),
        )
        .unwrap();

        // Legacy-schema descriptor.
        let id_b = pk_hex(0xBB);
        let legacy = json!({
            "federation_id": id_b,
            "epoch": 2,
            "threshold": 1,
            "members": [pk_hex(0x02)],
        });
        std::fs::write(
            dir.join(format!("{id_b}.json")),
            serde_json::to_string_pretty(&legacy).unwrap(),
        )
        .unwrap();

        // Re-parse both files via the same function the loader uses.
        let mut loaded = 0usize;
        for entry in std::fs::read_dir(&dir).unwrap() {
            let entry = entry.unwrap();
            let text = std::fs::read_to_string(entry.path()).unwrap();
            let v: serde_json::Value = serde_json::from_str(&text).unwrap();
            if parse_federation_descriptor(&v).is_some() {
                loaded += 1;
            }
        }
        assert_eq!(
            loaded, 2,
            "both schemas must be loaded; was the #87 schema mismatch reintroduced?"
        );

        // Cleanup.
        let _ = std::fs::remove_dir_all(&tmp);
    }
}
