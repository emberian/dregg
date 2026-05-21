//! Node state management.
//!
//! Holds the AgentWallet, Ledger, and PersistentStore handles behind
//! Arc<RwLock<>> for concurrent access from HTTP handlers and the
//! federation sync background task.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use tokio::sync::{RwLock, broadcast};

use pyana_cell::{CellId, Ledger};
use pyana_circuit::field::BabyBear;
use pyana_commit::accumulator::{BabyBear4, PolynomialAccumulator};
use pyana_coord::budget::{
    BudgetCoordinator, BudgetError, FastUnlockManager, SiloId, SpendingCertificate,
    UnlockCertificate, UnlockRequest, UnlockVote,
};
use pyana_sdk::AgentWallet;
use pyana_store::{PersistentStore, Poseidon2NoteTree};

use crate::federation_sync::GossipHandle;
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
    /// The agent wallet (identity, tokens, receipts).
    pub wallet: AgentWallet,
    /// The cell ledger (local cell state).
    pub ledger: Ledger,
    /// Persistent storage backend.
    pub store: PersistentStore,
    /// Federation peer addresses.
    pub peers: Vec<String>,
    /// Whether the wallet is unlocked for signing operations.
    pub unlocked: bool,
    /// BLAKE3 hash of the wallet passphrase, set on first `set-passphrase` call.
    /// When `Some`, unlock attempts must provide a passphrase whose BLAKE3 hash
    /// matches this value. When `None`, the first unlock sets the passphrase.
    pub passphrase_hash: Option<[u8; 32]>,
    /// Local intent pool: content-addressed ID -> validated Intent.
    pub intent_pool: HashMap<[u8; 32], pyana_intent::Intent>,
    /// Queue of signed turns ready for consensus ordering.
    /// Turns are added here when they require multi-party agreement (e.g.,
    /// fulfillment turns, cross-cell operations). The Morpheus consensus driver
    /// drains this queue each tick.
    pub consensus_queue: Vec<pyana_sdk::SignedTurn>,
    /// Pending conditional turns awaiting proof resolution.
    /// Garbage-collected on access when timeout_height is exceeded.
    pub pending_conditionals: Vec<pyana_turn::ConditionalTurn>,
    /// Registry of pending turns with distributed promise semantics.
    /// Tracks turns awaiting async resolution (cross-federation receipts, height
    /// conditions, etc.) and propagates broken promises to dependents.
    pub pending_turns: pyana_turn::PendingTurnRegistry,
    /// Set of proof hashes that have already been used (nullifiers).
    /// Prevents the same proof from satisfying multiple conditional turns.
    pub used_proof_hashes: HashSet<[u8; 32]>,
    /// Known federation public keys for attested root quorum verification.
    pub known_federation_keys: Vec<pyana_types::PublicKey>,
    /// Whether federation keys have been configured. When `false`, the node operates
    /// in "discovery mode" and will not finalize attested roots (Issue 10).
    pub federation_configured: bool,
    /// Maximum age (in seconds) for accepting incoming attested roots. Default: 3600.
    pub max_root_age_secs: u64,
    /// This validator's threshold decryption key share (Phase 2 turn privacy).
    /// Set during epoch initialization when the validator receives their share
    /// from the key generation ceremony.
    pub threshold_key_share: Option<pyana_federation::KeyShare>,
    /// Threshold required for decryption (t in t-of-n).
    pub decryption_threshold: usize,
    /// Pending decryption shares for encrypted turns awaiting collaborative decryption.
    /// Key: ciphertext_id, Value: collected shares so far.
    pub pending_decryption_shares: HashMap<[u8; 32], Vec<pyana_federation::DecryptionShare>>,
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
    pub pir_index_cache: Option<pyana_intent::pir::IntentIndex>,

    /// Persistent discharge gateway instance for replay prevention.
    /// SECURITY: This MUST persist across requests so the `issued` set actually
    /// tracks previously-discharged tickets. Creating a fresh gateway per request
    /// (the old behavior) made the replay set useless since it was dropped immediately.
    pub discharge_gateway: Option<pyana_macaroon::DischargeGateway>,

    // ─── Stingray Budget Coordination ─────────────────────────────────────────
    /// Per-agent budget coordinators for bounded-counter resource metering.
    /// Each agent with an active budget slice has an entry here.
    /// The node's silo_id is derived from the node's public key.
    pub budget_coordinators: HashMap<CellId, BudgetCoordinator>,
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
    pub cell_lock_table: pyana_turn::CellLockTable,

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
}

/// Summary of the node's sync state for the status endpoint.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SyncStatus {
    pub peer_count: usize,
    pub latest_height: u64,
    pub revocation_count: u64,
    pub note_count: u64,
}

/// Summary of the wallet state for the wallet endpoint.
#[derive(Clone, Debug, serde::Serialize)]
pub struct WalletStatus {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

impl NodeState {
    /// Create a new NodeState from a data directory path and peer list.
    ///
    /// Issue 4 fix: Loads `node.key` from the data directory to initialize
    /// the wallet identity. If no key file exists, generates a fresh identity
    /// and writes the key (first-run behavior).
    ///
    /// Issue 3 fix: Loads persisted passphrase hash from the store.
    /// Issue 5 fix: Loads persisted proof hashes (nullifiers) from the store.
    pub fn new(data_dir: &Path, peers: Vec<String>) -> Result<Self, String> {
        let db_path = data_dir.join("pyana.redb");
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        // Issue 4: Load or generate node identity key.
        let key_path = data_dir.join("node.key");
        let wallet = if key_path.exists() {
            let key_bytes_vec =
                std::fs::read(&key_path).map_err(|e| format!("failed to read node.key: {e}"))?;
            if key_bytes_vec.len() != 32 {
                return Err(format!(
                    "node.key has invalid length: expected 32, got {}",
                    key_bytes_vec.len()
                ));
            }
            let mut key_bytes = [0u8; 32];
            key_bytes.copy_from_slice(&key_bytes_vec);
            AgentWallet::from_key_bytes(zeroize::Zeroizing::new(key_bytes))
        } else {
            // First run: generate a key and persist it.
            let mut key_bytes = [0u8; 32];
            getrandom::fill(&mut key_bytes).map_err(|e| format!("getrandom failed: {e}"))?;
            std::fs::write(&key_path, key_bytes)
                .map_err(|e| format!("failed to write node.key: {e}"))?;
            // Restrict file permissions to owner-only (0o600) to prevent other
            // users from reading the private key.
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = std::fs::Permissions::from_mode(0o600);
                std::fs::set_permissions(&key_path, perms)
                    .map_err(|e| format!("failed to set node.key permissions: {e}"))?;
            }
            AgentWallet::from_key_bytes(zeroize::Zeroizing::new(key_bytes))
        };

        // Issue 3: Load persisted passphrase hash from the store.
        let passphrase_hash = match store.get_config("passphrase_hash") {
            Ok(Some(bytes)) if bytes.len() == 32 => {
                let mut hash = [0u8; 32];
                hash.copy_from_slice(&bytes);
                Some(hash)
            }
            _ => None,
        };

        // Issue 5: Load persisted proof hashes from the store.
        let used_proof_hashes = store.load_all_proof_hashes().unwrap_or_default();

        let ledger = Ledger::new();
        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the wallet's public key.
        let silo_id: SiloId = *blake3::hash(wallet.public_key().as_bytes()).as_bytes();

        // Issue 10: Log a warning — node starts in discovery mode with no federation keys.
        tracing::warn!(
            "node starting with zero federation keys — operating in discovery mode. \
             Attested roots will NOT be finalized until federation keys are loaded."
        );

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                pending_conditionals: Vec::new(),
                pending_turns: pyana_turn::PendingTurnRegistry::new(),
                used_proof_hashes,
                known_federation_keys: Vec::new(),
                federation_configured: false,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: pyana_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                pir_index_cache: None,
                discharge_gateway: None,
                budget_coordinators: HashMap::new(),
                fast_unlock_manager: None,
                silo_id,
                pending_spending_certificates: Vec::new(),
                pending_unlock_requests: Vec::new(),
                budget_epoch: 0,
                cell_lock_table: pyana_turn::CellLockTable::with_defaults(),
                cross_federation_revocations: HashMap::new(),
                revocation_accumulator: None,
                note_tree: Poseidon2NoteTree::with_depth(16),
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
        })
    }

    /// Create a NodeState with a pre-existing wallet (restored from key material).
    #[allow(dead_code)]
    pub fn with_wallet(
        data_dir: &Path,
        peers: Vec<String>,
        key_bytes: [u8; 32],
    ) -> Result<Self, String> {
        let db_path = data_dir.join("pyana.redb");
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        let wallet = AgentWallet::from_key_bytes(zeroize::Zeroizing::new(key_bytes));
        let ledger = Ledger::new();
        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the wallet's public key.
        let silo_id: SiloId = *blake3::hash(wallet.public_key().as_bytes()).as_bytes();

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash: None,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                pending_conditionals: Vec::new(),
                pending_turns: pyana_turn::PendingTurnRegistry::new(),
                used_proof_hashes: HashSet::new(),
                known_federation_keys: Vec::new(),
                federation_configured: false,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: pyana_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                pir_index_cache: None,
                discharge_gateway: None,
                budget_coordinators: HashMap::new(),
                fast_unlock_manager: None,
                silo_id,
                pending_spending_certificates: Vec::new(),
                pending_unlock_requests: Vec::new(),
                budget_epoch: 0,
                cell_lock_table: pyana_turn::CellLockTable::with_defaults(),
                cross_federation_revocations: HashMap::new(),
                revocation_accumulator: None,
                note_tree: Poseidon2NoteTree::with_depth(16),
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

    /// Get the current sync status.
    pub async fn sync_status(&self) -> SyncStatus {
        let state = self.inner.read().await;
        let latest_height = state
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        let revocation_count = state.store.revocation_count().unwrap_or(0);
        let note_count = state.store.note_count().unwrap_or(0);

        SyncStatus {
            peer_count: state.peers.len(),
            latest_height,
            revocation_count,
            note_count,
        }
    }

    /// Get the current wallet status.
    pub async fn wallet_status(&self) -> WalletStatus {
        let state = self.inner.read().await;
        let pk = state.wallet.public_key();
        WalletStatus {
            unlocked: state.unlocked,
            public_key: hex::encode(&pk.0),
            token_count: state.wallet.tokens().len(),
            receipt_chain_length: state.wallet.receipt_chain_length(),
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

    /// Set the gossip handle (called by federation_sync once initialized).
    pub async fn set_gossip(&self, handle: GossipHandle) {
        let mut g = self.gossip.write().await;
        *g = Some(handle);
    }

    /// Get a clone of the gossip handle, if available.
    pub async fn gossip(&self) -> Option<GossipHandle> {
        let g = self.gossip.read().await;
        g.clone()
    }

    /// Persist critical state before shutdown.
    ///
    /// Currently persists:
    /// - Discharge gateway replay set (prevents replay after restart)
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
        let coordinator = BudgetCoordinator::new(agent, total_balance, silos, byzantine_tolerance)?;
        self.budget_coordinators.insert(agent, coordinator);

        // Initialize fast unlock manager if not already present.
        if self.fast_unlock_manager.is_none() {
            let total_silos = self
                .budget_coordinators
                .values()
                .next()
                .map(|c| c.silos.len())
                .unwrap_or(4);
            self.fast_unlock_manager =
                Some(FastUnlockManager::new(byzantine_tolerance, total_silos));
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
        let signing_key = self.wallet.gossip_signing_key();
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
        let signing_key = self.wallet.gossip_signing_key();
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
    pub fn set_federation_keys(&mut self, keys: Vec<pyana_types::PublicKey>) {
        if keys.is_empty() {
            tracing::warn!(
                "set_federation_keys called with empty key set — remaining in discovery mode"
            );
            return;
        }
        tracing::info!(
            key_count = keys.len(),
            "federation keys loaded — exiting discovery mode"
        );
        self.known_federation_keys = keys;
        self.federation_configured = true;
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
        hasher.update(b"pyana-revocation-accumulator-set-commitment");
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
    ) -> Option<pyana_commit::poseidon2_tree::Poseidon2MerkleProof> {
        self.note_tree.prove_membership(position)
    }
}

/// Minimal hex encoding (no extra dep needed).
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
