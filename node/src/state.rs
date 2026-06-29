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

use dregg_cell::{Cell, CellId, Ledger};
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

/// THE SWAP (FLIPPED DEFAULT) — the verified Lean executor is now the authoritative state producer
/// on the commit path BY DEFAULT, with the legacy Rust executor demoted to a differential
/// cross-check. The producer installs the verified post-state only for the swap-safe COVERED set
/// (`lean_shadow::forest_is_root_agreeing` — every effect root-agreeing); a turn touching a
/// characterized root-gap or unmappable effect falls back to Rust for that turn with a logged
/// reason (no silent divergence).
///
/// This reads an opt-OUT: set `DREGG_LEAN_PRODUCER=0` (or `false`/`off`/`no`) to fall back to the
/// legacy Rust-producer path entirely. Any other value (or unset) keeps the verified producer ON.
pub fn lean_producer_env_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_LEAN_PRODUCER").ok().as_deref(),
        Some("0")
            | Some("false")
            | Some("FALSE")
            | Some("off")
            | Some("OFF")
            | Some("no")
            | Some("NO")
    )
}

/// MCP per-tool capability enforcement opt-in (`DREGG_MCP_CAP_ENFORCE=1`).
///
/// When enabled, the MCP `tools/call` surface REQUIRES every call to present an
/// `Authorization::Token` capability whose biscuit scope covers the tool's
/// declared `(action, resource)` scope, verified by the EXECUTOR's
/// `verify_token_for_scope`. A missing or non-covering credential is rejected
/// (the call never reaches the tool body).
///
/// Independently of this flag, a credential that IS presented is ALWAYS verified
/// — presenting a wrong/over-broad token always rejects. The flag only governs
/// whether a *missing* credential is rejected, so existing callers are
/// unaffected by default while the gate is genuinely enforced when armed.
pub fn mcp_cap_enforce_env_enabled() -> bool {
    matches!(
        std::env::var("DREGG_MCP_CAP_ENFORCE").ok().as_deref(),
        Some("1") | Some("true") | Some("TRUE")
    )
}

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
    /// A blocklace turn bundle carried malformed or non-matching artifacts.
    InvalidBlocklaceBundle { block_id: String, reason: String },
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
    /// Async STARK prove pool (F-DOS-1: proving runs OFF the commit/request
    /// path). `None` until [`Self::set_prove_pool`] is called at startup. When
    /// present, the submit/commit handlers FRI-free-revalidate the witness
    /// inline (sound, sub-ms) and hand full STARK proving to this pool instead
    /// of running it under the global state-write lock.
    prove_pool: Arc<RwLock<Option<crate::prove_pool::ProvePool>>>,
}

/// The inner mutable state of the node.
// Some fields back cfg-conditional / not-yet-consulted node surfaces (routing,
// cross-federation revocation, threshold shares); retained as wired scaffolding.
#[allow(dead_code)]
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
    /// In-flight (reserved) nonce floor for the faucet cell, enabling turn
    /// PIPELINING. The faucet's authoritative nonce only advances when a faucet
    /// turn FINALIZES through consensus; reading it directly meant a second
    /// faucet request submitted before the first finalized re-used the same
    /// nonce and replayed (`nonce replay: expected 1, got 0`). This tracks the
    /// next nonce the faucet has already HANDED OUT, so each rapid submission
    /// gets a fresh, monotonic, consecutive nonce. The issued nonce is
    /// `max(authoritative, faucet_reserved_nonce)`; finalization advances the
    /// authoritative side, and `max` keeps the two reconciled (no permanent gap
    /// once the in-flight turns drain). `None` until the first faucet request.
    pub faucet_reserved_nonce: Option<u64>,
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
    /// Whether the node proves EVERY finalized turn on the commit path
    /// (--prove-turns / devnet). When true,
    /// [`crate::blocklace_sync::execute_finalized_turn`] generates a real
    /// full-turn STARK proof for each committed turn, gates acceptance on the
    /// proof verifying (verify→accept leg), and persists the proof bytes keyed
    /// by turn hash. This is what makes the public "every state transition is
    /// proven" claim TRUE for the running node. Default `false` because full
    /// proving per turn is on the hot path; the devnet enables it.
    pub full_turn_proving_enabled: bool,
    /// THE SWAP — producer mode (authority inversion). When true, the commit path
    /// ([`crate::blocklace_sync::execute_finalized_turn`]) makes the VERIFIED Lean executor the
    /// authoritative state PRODUCER (`dregg_turn::lean_apply::produce_via_lean`): the committed
    /// ledger is reconstituted from the Lean FFI's post-state, and the legacy Rust
    /// `dregg_turn::TurnExecutor` is demoted to a parallel runtime DIFFERENTIAL cross-check (its
    /// post-state root is compared against the Lean-produced root; a divergence is logged loudly as
    /// a real soundness finding). Default `true` — THE SWAP: the verified Lean executor produces the
    /// committed state by default for the swap-safe COVERED set. Opt OUT via `DREGG_LEAN_PRODUCER=0`
    /// (read at state construction) or by clearing this field. A turn touching a characterized
    /// root-gap effect (root provably diverges) or an unmappable effect falls back to the Rust
    /// producer for that turn, with a logged reason — never a silent commit of divergent state.
    pub lean_producer_enabled: bool,
    /// THE EPOCH §5 ("fees as moves"): the FEE WELL cell from genesis
    /// (`genesis.json` `fee_well`). Wired onto every executor via
    /// [`crate::executor_setup::configure_turn_executor`] so undelivered fee
    /// shares MOVE here instead of burning — committed turns conserve
    /// exactly.
    pub fee_well: Option<CellId>,
    /// THE EPOCH §5 ("burn as issuer-move"): (token_id → issuer well cell)
    /// registrations from genesis (`genesis.json` `issuer_well`, registered
    /// for the default asset). Wired onto every executor so `Burn` executes
    /// as a move target→well.
    pub issuer_wells: Vec<([u8; 32], CellId)>,
    /// MCP per-tool capability enforcement. When `true`, the `tools/call`
    /// surface REQUIRES a covering `Authorization::Token` for every call (a
    /// missing credential is rejected). Independent of this flag, any presented
    /// credential is always verified against the tool's scope. Default mirrors
    /// [`mcp_cap_enforce_env_enabled`] (`DREGG_MCP_CAP_ENFORCE`). See
    /// [`crate::mcp`] for the tool→scope table and the gate.
    pub mcp_cap_enforce: bool,
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

    /// The receipt-index MMR — the non-omission certificate index dregg-query
    /// serves over `/api/receipts/index/{root,range}`. Leaf `i` is the 32-byte
    /// `receipt_hash()` of receipt-chain entry `i`. Maintained incrementally
    /// (lazily synced from the chain by [`Self::sync_receipt_index`]) — ADDITIVE:
    /// it hangs off the already-committed chain and NEVER gates the commit path.
    ///
    /// Trust-anchor residual (THE ROTATION): the root here is blake3 with
    /// arity-separated domains, NOT the model's in-circuit Poseidon2. Binding
    /// this root into `recStateCommit` (so the IVC aggregate pins it) is THE
    /// ROTATION's `CommitBindsMMR` weld — until then the served root is an
    /// out-of-band trust anchor.
    pub receipt_index: dregg_query::Mmr<dregg_query::Blake3Mmr>,

    /// Node-local witness artifacts keyed by receipt hash.
    ///
    /// MCP/devnet mutation paths can produce `WitnessedReceipt`s at commit time.
    /// Keeping them here lets later HTTP, explorer, and verifier flows retrieve
    /// the same artifact instead of relying on the original tool response.
    pub witnessed_receipts: HashMap<[u8; 32], Vec<WitnessedReceipt>>,
    witnessed_receipt_order: VecDeque<[u8; 32]>,

    /// Receipt hashes whose state is COMMITTED but whose async STARK
    /// attestation has not landed yet (F-DOS-1: proving runs off the commit
    /// path). The commit handler inserts the receipt hash here when it hands a
    /// proving job to the async pool; the pool's worker removes it via
    /// [`Self::clear_proof_pending`] once the proof is attached. A receipt that
    /// is pending here is fully committed and was witness-revalidated inline —
    /// only its succinct attestation is in flight. Bounded by
    /// [`MAX_WITNESSED_RECEIPTS`] insertion order to cap memory under a flood.
    proof_pending: HashSet<[u8; 32]>,
    proof_pending_order: VecDeque<[u8; 32]>,

    /// Solo consensus state: nullifier log, height tracking, auto-upgrade detection.
    /// `Some(_)` when this node was configured as solo (committee of one)
    /// at startup. Per FEDERATION-UNIFICATION-DESIGN.md §5, "solo" is no
    /// longer a separate runtime mode enum — the presence of this state
    /// (and the inner `is_solo` flag) is the operational signal.
    pub solo_consensus: Option<dregg_federation::solo::SoloConsensusState>,
    /// THE DEOS-HOST published surfaces (the `deos-host` feature): per hosted private
    /// server cell, its cap-gated affordance surface `(name, required)`, published by the
    /// deos-host thread after the server program's setup ran. The discovery route
    /// (`GET /api/server/{cell}/affordances`) projects this per-viewer. Plain data (no
    /// mozjs/gpui) so it lives in the lean node state unconditionally.
    pub deos_server_surfaces: HashMap<CellId, Vec<(String, dregg_cell::AuthRequired)>>,
    /// Blocklace consensus handle (set after federation sync starts).
    pub blocklace_handle: Option<crate::blocklace_sync::BlocklaceHandle>,
    /// Storage gateway service (ORGANS §3 weld): the content-addressed store
    /// plus the object index, admitted under the StorageGatewayMandate cell.
    pub storage_gateway: crate::storage_service::StorageGatewayService,
    /// Trustline registry (ORGANS §1 weld): the forever draw-digest
    /// anti-replay set per trustline cell (`no_double_draw_forever`).
    pub trustlines: crate::trustline_service::TrustlineRegistry,
    /// Equivocation court ledger (ORGANS §5 weld): the witness-first court
    /// (burned evidence digests + the slashable admission registry) and the
    /// strand-key → bond-cell bindings, so blocklace fork evidence executes
    /// as an ordinary conserved move from the bonded cell.
    pub equivocation_court: crate::equivocation_court_service::CourtLedger,
    /// Channels registry (ORGANS §4 weld): per-group room state — the open
    /// roster (re-commits to the on-cell membership root), the epoch keys
    /// this node minted, and the off-cell ciphertext ring + SSE bus.
    pub channels: crate::channels_service::ChannelRegistry,
    /// DKG ceremony registry (ORGANS §6 weld): per-ceremony room state — the
    /// node's copy of the deterministic common view (signed round messages)
    /// and the sealed-share ciphertexts held for pickup. The chain holds the
    /// pinned round roots; the view re-derives them for comparison.
    pub dkg: crate::dkg_service::DkgRegistry,
    /// pg-dregg M2: the LIVE node → postgres mirror writer. `Some` only when
    /// `DREGG_PG_MIRROR_URL` is set (opt-in, off by default — the node runs
    /// unchanged without it). After each DURABLY committed turn the commit path
    /// projects the `CommitRecord` into a verified-turn `MirrorBatch`, chains it
    /// (the same anti-substitution tooth the pg side re-checks), and ships it.
    /// The node is the ONLY writer; reads on the pg side are free SQL.
    /// (`crate::pg_mirror`; docs/PG-DREGG.md §8.)
    pub pg_mirror: Option<crate::pg_mirror::NodeMirror>,
}

/// Maximum number of events retained in the ring buffer for REST polling.
pub const MAX_EVENT_LOG: usize = 1000;
pub const MAX_WITNESSED_RECEIPTS: usize = 1000;
const WITNESSED_RECEIPT_ORDER_CONFIG: &str = "witnessed_receipt_order";

fn persist_witnessed_receipt_order(store: &PersistentStore, order: &VecDeque<[u8; 32]>) {
    let order: Vec<[u8; 32]> = order.iter().copied().collect();
    match postcard::to_stdvec(&order) {
        Ok(encoded) => {
            if let Err(e) = store.set_config(WITNESSED_RECEIPT_ORDER_CONFIG, &encoded) {
                tracing::warn!(
                    error = %e,
                    "failed to persist witnessed receipt artifact order"
                );
            }
        }
        Err(e) => {
            tracing::warn!(
                error = %e,
                "failed to serialize witnessed receipt artifact order"
            );
        }
    }
}

/// Last-writer-wins install of a recovery-overlay cell into the ledger.
///
/// `dregg_cell::Ledger::insert_cell` is a STRICT insert: it returns
/// `Err(CellAlreadyExists)` and KEEPS the existing cell when the id is already
/// present. That is first-writer-wins — wrong for crash recovery. The durable
/// commit-log overlay carries the POST-state of every cell touched since the
/// checkpoint; a cell the checkpoint already holds must be OVERWRITTEN by its
/// later overlay value, in ordinal order. The verified recovery model
/// (`CrashRecovery.upd`, mirrored by `dregg_persist`'s snapshot overlay) is a
/// last-writer-WINS point update: remove-then-insert. Recovery converges to the
/// committing node's finalized root precisely under this semantics.
fn upsert_cell(ledger: &mut Ledger, cell: Cell) {
    let _ = ledger.remove(&cell.id());
    let _ = ledger.insert_cell(cell);
}

fn load_witnessed_receipts(
    store: &PersistentStore,
) -> (HashMap<[u8; 32], Vec<WitnessedReceipt>>, VecDeque<[u8; 32]>) {
    let mut witnessed_receipts = HashMap::new();
    let mut witnessed_receipt_order = VecDeque::new();
    match store.load_witnessed_receipts_raw() {
        Ok(entries) => {
            let mut raw_by_hash: HashMap<[u8; 32], Vec<u8>> = entries.into_iter().collect();
            let ordered_hashes = store
                .get_config(WITNESSED_RECEIPT_ORDER_CONFIG)
                .ok()
                .flatten()
                .and_then(|bytes| postcard::from_bytes::<Vec<[u8; 32]>>(&bytes).ok())
                .filter(|order| !order.is_empty())
                .unwrap_or_else(|| raw_by_hash.keys().copied().collect());
            let skip = ordered_hashes.len().saturating_sub(MAX_WITNESSED_RECEIPTS);
            for receipt_hash in ordered_hashes.into_iter().skip(skip) {
                let Some(encoded) = raw_by_hash.remove(&receipt_hash) else {
                    continue;
                };
                match decode_witnessed_receipt_artifacts(&encoded) {
                    Ok(witnesses) => {
                        witnessed_receipt_order.push_back(receipt_hash);
                        witnessed_receipts.insert(receipt_hash, witnesses);
                    }
                    Err(e) => {
                        tracing::warn!(
                            receipt_hash = ?receipt_hash,
                            error = %e,
                            "skipping corrupt persisted witnessed receipt artifact"
                        );
                    }
                }
            }
        }
        Err(e) => {
            tracing::warn!(
                error = %e,
                "failed to load persisted witnessed receipt artifacts"
            );
        }
    }
    (witnessed_receipts, witnessed_receipt_order)
}

fn encode_witnessed_receipt_artifacts(witnesses: &[WitnessedReceipt]) -> Result<Vec<u8>, String> {
    let artifacts = witnesses
        .iter()
        .map(WitnessedReceipt::to_artifact_bytes)
        .collect::<Result<Vec<_>, _>>()?;
    postcard::to_allocvec(&artifacts)
        .map_err(|e| format!("failed to encode witnessed receipt artifact list: {e}"))
}

fn decode_witnessed_receipt_artifacts(encoded: &[u8]) -> Result<Vec<WitnessedReceipt>, String> {
    if let Ok(artifacts) = postcard::from_bytes::<Vec<Vec<u8>>>(encoded) {
        return artifacts
            .iter()
            .map(|artifact| WitnessedReceipt::from_artifact_bytes(artifact))
            .collect();
    }

    // Backward compatibility for short-lived node DBs written before the DWR1
    // artifact envelope was threaded through persistence.
    serde_json::from_slice::<Vec<WitnessedReceipt>>(encoded)
        .map_err(|e| format!("invalid witnessed receipt artifact list: {e}"))
}

#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ActivityStatus {
    Committed,
    #[allow(dead_code)] // Retained activity-status variant for the rejected-turn surface.
    Rejected,
}

#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ActivityProofStatus {
    Proved,
    /// The turn is COMMITTED and was witness-revalidated inline (sound), but its
    /// succinct STARK attestation is being generated asynchronously off the
    /// commit path (F-DOS-1). The receipt is final/Tentative as usual; only the
    /// proof artifact is in flight and will be attached when the prove pool
    /// finishes. Light-clients/cross-trust peers poll the witnessed-receipt
    /// endpoint until the attestation lands.
    ProofPending,
    NotRequired,
    #[allow(dead_code)] // Retained proof-status variant for the failed-prestate path.
    MissingPreState,
    #[allow(dead_code)] // Retained proof-status variant for the prove-failure path.
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
    /// Typed per-effect summaries (the dregg-query EDB enrichment): from/to/
    /// asset/amount for transfers, holder/cap for grants, and post-state balance
    /// observations for touched cells. This is what lets the LIVE receipt log
    /// yield `transfer`/`balance`/`granted` facts, not just effect-kind strings.
    /// Empty when the commit path had no decoded effects in hand (e.g. encrypted
    /// or blocklace-finalized turns).
    #[serde(default)]
    pub summaries: Vec<dregg_query::EffectSummary>,
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
        // Boot crash-recovery: a torn/poisoned commit-log tail (e.g. a process
        // killed between the input-turn config write and the commit-record txn, or
        // an unclean power-cycle) leaves the log's head inconsistent with its
        // durably-recorded finalized root, so the convergence check below would
        // REFUSE the whole image and strand the node (observed 2026-06-29 after a
        // homelab PSU swap). Truncate any divergent tail to the last commit ordinal
        // whose reconstructed root matches; peers backfill the dropped turn(s) via
        // normal blocklace sync. No-op (returns 0) when already consistent; a
        // genuinely divergent image with NO matching prefix still Errs (fail-closed
        // on tampering). Uses the existing `PersistentStore::recover_to_last_consistent`
        // (persist/src/commit_log.rs); mirrors starbridge `World::open_recovering`.
        match store.recover_to_last_consistent() {
            Ok(0) => {}
            Ok(n) => tracing::warn!(
                truncated = n,
                "boot recovery: truncated {n} divergent commit-log record(s) to the \
                 last-consistent ordinal (torn-tail crash recovery); peers will backfill"
            ),
            Err(e) => {
                return Err(format!("boot recovery (recover_to_last_consistent) failed: {e}"));
            }
        }

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
        let (witnessed_receipts, witnessed_receipt_order) = load_witnessed_receipts(&store);

        // Restore the forever-digest registries (docs/PERSISTENCE.md): the
        // trustline draw/settle anti-replay set and the court's resolved-
        // evidence set are node-local-but-load-bearing — NOT derivable from
        // the cells — so their refusal teeth must survive the restart.
        let trustlines = crate::trustline_service::TrustlineRegistry::load(&store);
        let equivocation_court = crate::equivocation_court_service::CourtLedger::load(&store);

        // Restore ledger from the latest checkpoint (if one exists), then apply
        // the durable commit-log overlay (CRASH-CONSISTENT RECOVERY).
        //
        // The periodic full ledger checkpoint lags behind the finalized turn
        // stream by up to `LEDGER_CHECKPOINT_INTERVAL` turns. The commit log
        // (written atomically per turn) carries the post-state of every cell
        // touched since that checkpoint. Overlaying those post-states onto the
        // checkpoint reconstructs the EXACT finalized ledger up to the durable
        // commit cursor — without replaying/re-executing any turn (no
        // double-apply) and without losing any finalized turn that lies in the
        // gap (no torn state). `upsert_cell` (remove-then-insert) makes the
        // overlay last-writer-wins, matching the log's ordinal order — a strict
        // `insert_cell` would first-writer-WIN and silently DROP a post-checkpoint
        // write to an already-checkpointed cell. This is LaceMerge convergence
        // applied to recovery: the recovered node reaches the same finalized
        // state the committing node recorded.
        let (mut ledger, checkpoint_height) = match store.load_latest_ledger_checkpoint() {
            Ok(Some((height, restored_ledger))) => {
                tracing::info!(
                    checkpoint_height = height,
                    cells = restored_ledger.len(),
                    "restored ledger from checkpoint"
                );
                (restored_ledger, height)
            }
            Ok(None) => {
                tracing::info!("no ledger checkpoint found, starting with empty ledger");
                (Ledger::new(), 0)
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    "failed to load ledger checkpoint, starting with empty ledger"
                );
                (Ledger::new(), 0)
            }
        };
        match store.cell_overlay_since(checkpoint_height) {
            Ok(overlay) if !overlay.is_empty() => {
                let overlay_len = overlay.len();
                for cell in overlay {
                    upsert_cell(&mut ledger, cell);
                }
                // The recovery-convergence verdict is DEFERRED to
                // `verify_recovery_convergence`, which `run_node` calls AFTER it
                // reconstructs the FULL finalized ledger in the SOUND order
                // (`reseed_genesis_then_overlay`): the genesis BASELINE is built
                // first on a fresh ledger — `genesis_moves` replayed EXACTLY ONCE
                // — and THEN this recovered overlay is re-applied last-writer-wins
                // ON TOP, so every bot-touched cell's finalized post-state wins.
                //
                // A node that finalized turns BELOW the first ledger checkpoint
                // has NO checkpoint to restore its UNTOUCHED genesis cells from,
                // and `cell_overlay_since` carries only the cells a turn TOUCHED.
                // So the ledger reconstructed HERE is the touched-cell delta on
                // an empty base — NOT yet the full finalized ledger. The recorded
                // finalized root commits the FULL ledger (genesis ⊕ touched);
                // comparing against it before the genesis baseline is rebuilt
                // would fail-close every legitimate sub-checkpoint restart (the
                // node would need a redb wipe to rejoin). The verdict still runs,
                // still fail-CLOSED on genuine divergence — just once the
                // baseline is in place and the root is meaningful.
                tracing::info!(
                    overlaid_cells = overlay_len,
                    commit_cursor = store.commit_cursor().unwrap_or(0),
                    "applied durable commit-log overlay — recovery convergence is verified \
                     after the genesis baseline is reseeded (see verify_recovery_convergence)"
                );
            }
            Ok(_) => {}
            Err(e) => {
                tracing::warn!(error = %e, "failed to apply durable commit-log overlay on recovery");
            }
        }
        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the cipherclerk's public key.
        let silo_id: SiloId = *blake3::hash(cclerk.public_key().as_bytes()).as_bytes();

        // Restore node-held channel rooms from the durable roster table
        // (docs/PERSISTENCE.md §3, the roster caveat): each stored roster is
        // RE-COMMITTED against the recovered ledger's on-cell membership root;
        // a stale durable roster is discarded (and durably removed). This is
        // built against the just-recovered `ledger`, before it moves into the
        // state.
        let mut channels = crate::channels_service::ChannelRegistry::default();
        channels.restore_rosters(&store, &ledger);

        // Issue 10: the freshly-constructed state has no federation keys yet.
        // This is expected: `run_node` loads them from `genesis.json` (via
        // `set_federation_keys`) immediately after construction, which emits the
        // definitive "federation keys loaded — exiting discovery mode" line. We
        // log this at DEBUG (not WARN) so a normal genesis boot does not surface
        // a spurious "zero federation keys" alarm; a node that truly never loads
        // keys still reveals itself by the ABSENCE of the "keys loaded" line.
        tracing::debug!(
            "node state constructed with zero federation keys — awaiting genesis \
             load. Attested roots will not finalize until federation keys are set."
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
                faucet_reserved_nonce: None,
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
                full_turn_proving_enabled: false,
                lean_producer_enabled: lean_producer_env_enabled(),
                fee_well: None,
                issuer_wells: Vec::new(),
                mcp_cap_enforce: mcp_cap_enforce_env_enabled(),
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
                    //
                    // `::new` installs the STRICT (fail-CLOSED) verifier: a
                    // solver submission that omits `witnessed_predicate` is
                    // rejected, so the `validity_proof` is always
                    // cryptographically dispatched through the registry rather
                    // than waved through (SILVER-DEBT T1.2 fail-open: closed).
                    1, 1,
                ),
                delay_pool: dregg_intent::delay_pool::DelayPool::new(
                    dregg_intent::delay_pool::DelayPoolConfig::default(),
                ),
                event_log: VecDeque::new(),
                receipt_index: dregg_query::Mmr::new(dregg_query::Blake3Mmr),
                witnessed_receipts,
                witnessed_receipt_order,
                proof_pending: HashSet::new(),
                proof_pending_order: VecDeque::new(),
                solo_consensus: None,
                deos_server_surfaces: HashMap::new(),
                blocklace_handle: None,
                storage_gateway: crate::storage_service::StorageGatewayService::from_env(),
                trustlines,
                equivocation_court,
                channels,
                dkg: crate::dkg_service::DkgRegistry::default(),
                // pg-dregg M2: lazily initialized on the first commit when
                // DREGG_PG_MIRROR_URL is set (resumes from the store head); stays
                // None when mirroring is off. See `NodeStateInner::mirror_committed_record`.
                pg_mirror: None,
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
            prove_pool: Arc::new(RwLock::new(None)),
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
        // Boot crash-recovery: a torn/poisoned commit-log tail (e.g. a process
        // killed between the input-turn config write and the commit-record txn, or
        // an unclean power-cycle) leaves the log's head inconsistent with its
        // durably-recorded finalized root, so the convergence check below would
        // REFUSE the whole image and strand the node (observed 2026-06-29 after a
        // homelab PSU swap). Truncate any divergent tail to the last commit ordinal
        // whose reconstructed root matches; peers backfill the dropped turn(s) via
        // normal blocklace sync. No-op (returns 0) when already consistent; a
        // genuinely divergent image with NO matching prefix still Errs (fail-closed
        // on tampering). Uses the existing `PersistentStore::recover_to_last_consistent`
        // (persist/src/commit_log.rs); mirrors starbridge `World::open_recovering`.
        match store.recover_to_last_consistent() {
            Ok(0) => {}
            Ok(n) => tracing::warn!(
                truncated = n,
                "boot recovery: truncated {n} divergent commit-log record(s) to the \
                 last-consistent ordinal (torn-tail crash recovery); peers will backfill"
            ),
            Err(e) => {
                return Err(format!("boot recovery (recover_to_last_consistent) failed: {e}"));
            }
        }

        let cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key_bytes));
        let (witnessed_receipts, witnessed_receipt_order) = load_witnessed_receipts(&store);

        // Restore the forever-digest registries (docs/PERSISTENCE.md): the
        // trustline draw/settle anti-replay set and the court's resolved-
        // evidence set are node-local-but-load-bearing — NOT derivable from
        // the cells — so their refusal teeth must survive the restart.
        let trustlines = crate::trustline_service::TrustlineRegistry::load(&store);
        let equivocation_court = crate::equivocation_court_service::CourtLedger::load(&store);

        // Restore ledger from the latest checkpoint, then apply the durable
        // commit-log overlay (crash-consistent recovery; see `new_with_key_file`).
        let (mut ledger, checkpoint_height) = match store.load_latest_ledger_checkpoint() {
            Ok(Some((height, restored_ledger))) => (restored_ledger, height),
            _ => (Ledger::new(), 0),
        };
        if let Ok(overlay) = store.cell_overlay_since(checkpoint_height)
            && !overlay.is_empty()
        {
            for cell in overlay {
                // Last-writer-wins point update (`CrashRecovery.upd`); a strict
                // `insert_cell` would silently drop a post-checkpoint write to an
                // already-checkpointed cell. See `new_with_key_file` / `upsert_cell`.
                upsert_cell(&mut ledger, cell);
            }
            // Convergence assertion, mirroring `new_with_key_file`: the
            // reconstructed root MUST equal the root the committing node durably
            // recorded. A mismatch means serving a SILENTLY-WRONG ledger as truth
            // — a soundness event. FAIL CLOSED rather than fall through. (Parity
            // fix: this secondary recovery entry previously applied the overlay
            // without the convergence check the primary path enforces.)
            let recovered_root = crate::blocklace_sync::canonical_ledger_root(&ledger);
            if let Ok(Some(expected)) = store.recovered_ledger_root()
                && expected != recovered_root
            {
                tracing::error!(
                    recovered_root = %dregg_types::hex_encode(&recovered_root),
                    expected_root = %dregg_types::hex_encode(&expected),
                    "commit-log overlay (cclerk path) recovered a ledger root that does \
                     NOT match the durably recorded finalized root — STORE INTEGRITY \
                     EVENT, refusing to start"
                );
                return Err(format!(
                    "recovery convergence failed: reconstructed ledger root {} does not \
                             match the durably recorded finalized root {} — refusing to serve a \
                             divergent ledger (STORE INTEGRITY EVENT)",
                    dregg_types::hex_encode(&recovered_root),
                    dregg_types::hex_encode(&expected),
                ));
            }
        }

        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the cipherclerk's public key.
        let silo_id: SiloId = *blake3::hash(cclerk.public_key().as_bytes()).as_bytes();

        // Restore node-held channel rooms from the durable roster table
        // (docs/PERSISTENCE.md §3), re-committed against the recovered ledger.
        let mut channels = crate::channels_service::ChannelRegistry::default();
        channels.restore_rosters(&store, &ledger);

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
                faucet_reserved_nonce: None,
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
                full_turn_proving_enabled: false,
                lean_producer_enabled: lean_producer_env_enabled(),
                fee_well: None,
                issuer_wells: Vec::new(),
                mcp_cap_enforce: mcp_cap_enforce_env_enabled(),
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
                    //
                    // `::new` installs the STRICT (fail-CLOSED) verifier: a
                    // solver submission that omits `witnessed_predicate` is
                    // rejected, so the `validity_proof` is always
                    // cryptographically dispatched through the registry rather
                    // than waved through (SILVER-DEBT T1.2 fail-open: closed).
                    1, 1,
                ),
                delay_pool: dregg_intent::delay_pool::DelayPool::new(
                    dregg_intent::delay_pool::DelayPoolConfig::default(),
                ),
                event_log: VecDeque::new(),
                receipt_index: dregg_query::Mmr::new(dregg_query::Blake3Mmr),
                witnessed_receipts,
                witnessed_receipt_order,
                proof_pending: HashSet::new(),
                proof_pending_order: VecDeque::new(),
                solo_consensus: None,
                deos_server_surfaces: HashMap::new(),
                blocklace_handle: None,
                storage_gateway: crate::storage_service::StorageGatewayService::from_env(),
                trustlines,
                equivocation_court,
                channels,
                dkg: crate::dkg_service::DkgRegistry::default(),
                // pg-dregg M2: lazily initialized on the first commit when
                // DREGG_PG_MIRROR_URL is set (resumes from the store head); stays
                // None when mirroring is off. See `NodeStateInner::mirror_committed_record`.
                pg_mirror: None,
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
            prove_pool: Arc::new(RwLock::new(None)),
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

    /// Verify recovery convergence: the canonical root of the CURRENTLY-LOADED
    /// ledger must equal the durably recorded finalized root.
    ///
    /// This is the recovery-side analogue of LaceMerge convergence: independent
    /// of HOW the ledger was rebuilt (checkpoint + commit-log overlay + genesis
    /// baseline), the resulting root MUST equal the root the committing node
    /// recorded. A mismatch means the reconstructed ledger does NOT equal the
    /// finalized state that was committed — serving it would serve a
    /// SILENTLY-WRONG ledger as truth (a soundness event). FAIL CLOSED: return
    /// `Err` so the caller refuses to start rather than serve divergent state.
    ///
    /// MUST be called AFTER the full finalized ledger has been reconstructed in
    /// the SOUND order (`reseed_genesis_then_overlay`): the genesis BASELINE
    /// built first on a fresh ledger (`genesis_moves` applied EXACTLY ONCE), the
    /// recovered commit-log overlay re-applied last-writer-wins ON TOP. The
    /// verdict is deliberately deferred out of `NodeState::new_with_key_file`: a
    /// node that finalized turns BELOW the first ledger checkpoint has no
    /// checkpoint to restore its UNTOUCHED genesis cells from, and the commit-log
    /// overlay carries only the cells a turn touched — so the ledger at
    /// construction time is the touched-cell delta on an empty base, not yet the
    /// full finalized ledger. Rebuilding `genesis_baseline ⊕ overlay` completes
    /// the ledger to the exact state the recorded root commits. Only then is the
    /// comparison meaningful.
    ///
    /// Returns `Ok(())` when there is no recorded finalized root (a fresh genesis
    /// boot has nothing to converge to) or when the roots match.
    pub async fn verify_recovery_convergence(&self) -> Result<(), String> {
        let s = self.read().await;
        let expected = match s.store.recovered_ledger_root() {
            Ok(Some(root)) => root,
            Ok(None) => {
                // No finalized turn recorded — a fresh genesis boot. Nothing to
                // converge to.
                return Ok(());
            }
            Err(e) => {
                // Could not read the recorded root; do not treat a read failure
                // as a soundness violation (matches the pre-deferral behavior,
                // which logged-and-continued when no comparable root was found).
                tracing::warn!(error = %e, "could not read recorded finalized root for recovery convergence");
                return Ok(());
            }
        };
        let recovered_root = crate::blocklace_sync::canonical_ledger_root(&s.ledger);
        if recovered_root == expected {
            tracing::info!(
                cells = s.ledger.len(),
                commit_cursor = s.store.commit_cursor().unwrap_or(0),
                recovered_root = %dregg_types::hex_encode(&recovered_root),
                "recovery convergence verified — reconstructed ledger CONVERGED to the \
                 recorded finalized root (crash-consistent)"
            );
            Ok(())
        } else {
            tracing::error!(
                cells = s.ledger.len(),
                recovered_root = %dregg_types::hex_encode(&recovered_root),
                expected_root = %dregg_types::hex_encode(&expected),
                "reconstructed ledger root does NOT match the durably recorded finalized \
                 root — STORE INTEGRITY EVENT, refusing to start"
            );
            Err(format!(
                "recovery convergence failed: reconstructed ledger root {} does not match \
                 the durably recorded finalized root {} — refusing to serve a divergent \
                 ledger (STORE INTEGRITY EVENT)",
                dregg_types::hex_encode(&recovered_root),
                dregg_types::hex_encode(&expected),
            ))
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

    /// Install the async STARK prove pool (F-DOS-1). Called once at startup
    /// AFTER the `NodeState` exists, because the pool's workers capture the same
    /// `NodeState` to write completed proofs back (the gossip-handle chicken-and-
    /// egg pattern). Once set, the submit/commit handlers offload proving here.
    pub async fn set_prove_pool(&self, pool: crate::prove_pool::ProvePool) {
        let mut p = self.prove_pool.write().await;
        *p = Some(pool);
    }

    /// Get a clone of the async prove-pool handle, if installed. When `None`,
    /// callers fall back to inline proving (the legacy path) — but the running
    /// node always installs it at startup, so the commit path stays off the lock.
    pub async fn prove_pool(&self) -> Option<crate::prove_pool::ProvePool> {
        let p = self.prove_pool.read().await;
        p.clone()
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

    /// THE REFLEXIVE IMAGE — project the node's OWN live runtime state AS A CELL.
    ///
    /// Reads the blocklace DAG facts (its own async lock, exactly as `api::get_status`
    /// does), then the inner state under the read lock, and collects the already-served
    /// self-status (`/api/node/identity` + `/api/node/producer` + `/status`) onto ONE
    /// cell-shaped view: a real `dregg_cell::Cell` in a one-cell ledger, reflectable by
    /// the SAME `deos_reflect::reflect_cell` deos-js's crawl uses. The node stops being
    /// an opaque server and becomes an inspectable cell (`crate::self_cell`).
    ///
    /// Every field is LIVE — re-call after a turn and the cell view moves
    /// (`ledger_height`, the operator balance/nonce, `block_count`, the producer mode).
    // Consumed by the `GET /api/node/self` route in `api.rs` (a parallel lane); the
    // projection it returns is covered by `self_cell` unit tests.
    #[allow(dead_code)]
    pub async fn self_cell(&self) -> crate::self_cell::NodeSelfCell {
        let dag = match self.blocklace().await {
            Some(handle) => crate::self_cell::BlocklaceFacts {
                dag_height: handle.dag_height().await,
                block_count: handle.block_count().await as u64,
                consensus_live: true,
            },
            None => crate::self_cell::BlocklaceFacts::default(),
        };
        let inner = self.inner.read().await;
        crate::self_cell::NodeSelfCell::project(&inner, dag)
    }
}

// =============================================================================
// Atomic Proposal Management Methods
// =============================================================================

impl NodeStateInner {
    /// pg-dregg M2: mirror one DURABLY committed turn to postgres.
    ///
    /// Called from the commit path AFTER `commit_finalized_turn` succeeds, with
    /// the record carrying its assigned `ordinal`. A no-op when mirroring is off
    /// (`DREGG_PG_MIRROR_URL` unset). On first use it lazily builds the mirror
    /// resuming from this turn's pre-state (the store's prior head) and the
    /// assigned ordinal, so the chain is correct even on a node that enables
    /// mirroring mid-life. The batch is projected from the real `CommitRecord`,
    /// chained (the anti-substitution tooth the pg side re-checks), and shipped;
    /// a refusal is logged loudly (it means the local chain disagrees — a real
    /// finding), never silently dropped.
    pub fn mirror_committed_record(&mut self, record: &dregg_persist::CommitRecord) {
        // Lazy init: only when configured. Resume from THIS record's pre-state:
        // the store's recorded head before this turn is the prior turn's
        // ledger_root (or genesis for ordinal 0), and next_ordinal == this
        // record's ordinal.
        if self.pg_mirror.is_none() {
            let head = if record.ordinal == 0 {
                crate::pg_mirror::GENESIS_ROOT
            } else {
                // The prior committed turn's post-state root is this turn's
                // pre-state root.
                self.store
                    .commit_record_at(record.ordinal - 1)
                    .ok()
                    .flatten()
                    .map(|r| r.ledger_root)
                    .unwrap_or(crate::pg_mirror::GENESIS_ROOT)
            };
            self.pg_mirror = crate::pg_mirror::NodeMirror::from_env(head, record.ordinal);
        }
        let Some(mirror) = self.pg_mirror.as_mut() else {
            return; // mirroring off
        };
        if let Err(e) = mirror.mirror_record(record) {
            tracing::error!(
                ordinal = record.ordinal,
                error = %e,
                "pg-mirror: REFUSED a committed turn — local mirror chain disagrees \
                 with the durable commit log (a real finding; not silently dropped)"
            );
        }
    }

    /// Bring the receipt-index MMR up to the receipt chain length: push the
    /// `receipt_hash()` leaf of every chain entry not yet indexed. `O(new
    /// leaves)` — the incremental maintenance the index needs, run lazily off
    /// the read path (the query handlers call this before serving). It is purely
    /// additive over the already-committed, append-only chain, so it can never
    /// affect commit soundness.
    pub fn sync_receipt_index(&mut self) {
        let have = self.receipt_index.len() as usize;
        let chain = self.cclerk.receipt_chain();
        if have >= chain.len() {
            return;
        }
        // Collect the new leaves first so the immutable chain borrow ends before
        // the mutable push.
        let new_leaves: Vec<[u8; 32]> = chain[have..].iter().map(|r| r.receipt_hash()).collect();
        for leaf in new_leaves {
            self.receipt_index.push(leaf);
        }
    }

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
            if self.witnessed_receipt_order.len() >= MAX_WITNESSED_RECEIPTS
                && let Some(oldest) = self.witnessed_receipt_order.pop_front()
            {
                self.witnessed_receipts.remove(&oldest);
                if let Err(e) = self.store.remove_witnessed_receipts_raw(&oldest) {
                    tracing::warn!(
                        receipt_hash = ?oldest,
                        error = %e,
                        "failed to remove evicted persisted witnessed receipt artifacts"
                    );
                }
            }
            self.witnessed_receipt_order.push_back(receipt_hash);
            persist_witnessed_receipt_order(&self.store, &self.witnessed_receipt_order);
        }
        self.witnessed_receipts
            .entry(receipt_hash)
            .or_default()
            .push(witnessed);
        if let Some(witnesses) = self.witnessed_receipts.get(&receipt_hash) {
            match encode_witnessed_receipt_artifacts(witnesses) {
                Ok(encoded) => {
                    if let Err(e) = self
                        .store
                        .store_witnessed_receipts_raw(&receipt_hash, &encoded)
                    {
                        tracing::warn!(
                            receipt_hash = ?receipt_hash,
                            error = %e,
                            "failed to persist witnessed receipt artifacts"
                        );
                    }
                }
                Err(e) => {
                    tracing::warn!(
                        receipt_hash = ?receipt_hash,
                        error = %e,
                        "failed to serialize witnessed receipt artifacts"
                    );
                }
            }
        }
    }

    pub fn witnessed_receipt_count(&self, receipt_hash: &[u8; 32]) -> usize {
        self.witnessed_receipts
            .get(receipt_hash)
            .map(Vec::len)
            .unwrap_or(0)
    }

    /// Mark a committed receipt as awaiting its async STARK attestation
    /// (F-DOS-1). Called by the commit handler right after it hands a proving
    /// job to the async pool. Insertion-order bounded by `MAX_WITNESSED_RECEIPTS`
    /// so a proving flood cannot grow this set without bound.
    pub fn mark_proof_pending(&mut self, receipt_hash: [u8; 32]) {
        if self.proof_pending.insert(receipt_hash) {
            self.proof_pending_order.push_back(receipt_hash);
            while self.proof_pending_order.len() > MAX_WITNESSED_RECEIPTS {
                if let Some(oldest) = self.proof_pending_order.pop_front() {
                    self.proof_pending.remove(&oldest);
                }
            }
        }
    }

    /// Clear the pending-proof marker once the async pool attaches the proof.
    pub fn clear_proof_pending(&mut self, receipt_hash: &[u8; 32]) {
        self.proof_pending.remove(receipt_hash);
    }

    /// Whether a committed receipt's async attestation is still in flight.
    #[allow(dead_code)] // Retained query on the async-attestation tracking surface.
    pub fn is_proof_pending(&self, receipt_hash: &[u8; 32]) -> bool {
        self.proof_pending.contains(receipt_hash)
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

#[allow(dead_code)] // Some methods back cfg-conditional / not-yet-wired node surfaces; retained.
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
            if let Some(slice) = coordinator.silo_states.get(&silo_id)
                && slice.spent > 0
            {
                certificates.push(slice.certificate(silo_id, signing_key_bytes));
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

#[cfg(test)]
mod witnessed_receipt_persistence_tests {
    use super::*;

    fn witnessed_with_marker(marker: u8) -> WitnessedReceipt {
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: [marker; 32],
            effects_hash: [marker.wrapping_add(1); 32],
            agent: CellId::from_bytes([marker.wrapping_add(2); 32]),
            ..Default::default()
        };
        WitnessedReceipt::from_components(
            receipt,
            vec![marker, marker.wrapping_add(1)],
            vec![marker as u32],
            None,
        )
    }

    #[tokio::test]
    async fn witnessed_receipt_artifacts_survive_node_restart() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [7u8; 32];
        let receipt_hash = [42u8; 32];

        {
            let state =
                NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("create node state");
            state
                .write()
                .await
                .push_witnessed_receipt(receipt_hash, witnessed_with_marker(9));
            assert_eq!(state.read().await.witnessed_receipt_count(&receipt_hash), 1);
            let raw_entries = state
                .read()
                .await
                .store
                .load_witnessed_receipts_raw()
                .expect("load raw persisted artifacts");
            let (_, encoded) = raw_entries
                .iter()
                .find(|(hash, _)| hash == &receipt_hash)
                .expect("raw artifact entry");
            let artifact_bytes: Vec<Vec<u8>> =
                postcard::from_bytes(encoded).expect("DWR1 artifact list encoding");
            assert_eq!(artifact_bytes.len(), 1);
            let decoded = WitnessedReceipt::from_artifact_bytes(&artifact_bytes[0])
                .expect("DWR1 artifact decodes");
            assert_eq!(decoded.proof_bytes, vec![9, 10]);
        }

        let restored =
            NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("restore node state");
        let guard = restored.read().await;
        let witnesses = guard
            .witnessed_receipts
            .get(&receipt_hash)
            .expect("persisted witness vector");
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0].proof_bytes, vec![9, 10]);
        assert_eq!(witnesses[0].public_inputs, vec![9]);
    }

    #[tokio::test]
    async fn witnessed_receipt_retention_eviction_removes_persisted_artifact() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [8u8; 32];
        let first_hash = [1u8; 32];

        {
            let state =
                NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("create node state");
            let mut guard = state.write().await;
            guard.push_witnessed_receipt(first_hash, witnessed_with_marker(1));
            for marker in 2..=(MAX_WITNESSED_RECEIPTS as u16 + 1) {
                let mut hash = [0u8; 32];
                hash[..2].copy_from_slice(&marker.to_le_bytes());
                guard.push_witnessed_receipt(hash, witnessed_with_marker(marker as u8));
            }
            assert!(!guard.witnessed_receipts.contains_key(&first_hash));
        }

        let restored =
            NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("restore node state");
        let guard = restored.read().await;
        assert!(!guard.witnessed_receipts.contains_key(&first_hash));
        assert_eq!(guard.witnessed_receipts.len(), MAX_WITNESSED_RECEIPTS);
    }
}

#[cfg(test)]
mod crash_recovery_overlay_tests {
    //! Recovery-soundness regressions (docs/ARCHEOLOGY-LEDGER.md, HIGH tier).
    //!
    //! 1. LAST-WRITER-WINS OVERLAY: a post-checkpoint commit-log write to a cell
    //!    the checkpoint ALREADY holds must OVERWRITE it (the verified
    //!    `CrashRecovery.upd` point update), not be silently dropped. A strict
    //!    `insert_cell` is first-writer-wins and would keep the stale
    //!    checkpoint value — a silently-wrong recovered ledger served as truth.
    //! 2. CONVERGENCE FAILS CLOSED: if the reconstructed ledger root does NOT
    //!    match the durably recorded finalized root, recovery must REFUSE to
    //!    start (return Err) rather than log-and-continue serving a divergent
    //!    ledger (a soundness event).
    use super::*;
    use dregg_cell::Cell;
    use dregg_persist::PersistentStore;

    // A cell whose CONTENT-ADDRESSED id is fixed by (public_key, token_id); the
    // balance varies, so the checkpoint value and the later overlay value share
    // one id — exactly the "post-checkpoint write to an already-held cell" case.
    fn cell(seed: u8, balance: i64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance)
    }

    /// Build a store at `dir` with: a checkpoint at height 1 holding `cell(X)`
    /// at `checkpoint_balance`, then a finalized turn at height 2 that rewrites
    /// the SAME cell to `overlay_balance`. The committed `ledger_root` is set to
    /// `record_root` (pass the genuine post-overlay root for the converging
    /// case; a wrong root for the fail-closed case).
    fn seed_store_with_overlay(
        dir: &Path,
        seed: u8,
        checkpoint_balance: i64,
        overlay_balance: i64,
        record_root: [u8; 32],
    ) {
        let db_path = dir.join("dregg.redb");
        let store = PersistentStore::open(&db_path).expect("open store");

        // Checkpoint at height 1 holds the cell at the OLD value.
        let mut checkpoint_ledger = Ledger::new();
        checkpoint_ledger
            .insert_cell(cell(seed, checkpoint_balance))
            .expect("seed checkpoint cell");
        store
            .checkpoint_ledger(&checkpoint_ledger, 1)
            .expect("write checkpoint");

        // A finalized turn at height 2 > 1 rewrites the SAME cell to the NEW
        // value. `cell_overlay_since(1)` returns this post-state.
        let rec = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 2,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xc1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xc2; 32],
            ledger_root: record_root,
            touched_cells: vec![cell(seed, overlay_balance)],
        };
        store
            .commit_finalized_turn(0, &rec)
            .expect("commit overlay turn");
    }

    /// The genuine post-overlay canonical root: checkpoint ⊕ overlay applied
    /// last-writer-wins, then committed by the node's own root function.
    fn converged_root(seed: u8, overlay_balance: i64) -> [u8; 32] {
        let mut ledger = Ledger::new();
        ledger
            .insert_cell(cell(seed, overlay_balance))
            .expect("post-overlay cell");
        crate::blocklace_sync::canonical_ledger_root(&ledger)
    }

    #[tokio::test]
    async fn post_checkpoint_overlay_write_wins_over_checkpoint_value() {
        // The checkpoint holds balance 100; the durable commit log says the
        // finalized value is 999. Recovery MUST surface 999 (last-writer-wins),
        // not the stale 100 a strict insert_cell would keep.
        let seed = 0x5a;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 100, 999, converged_root(seed, 999));

        let key_bytes = [0x11u8; 32];
        let state = NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("recovery with a converging overlay must succeed");
        let guard = state.read().await;
        let recovered = guard
            .ledger
            .get(&cell(seed, 0).id())
            .expect("recovered cell present");
        assert_eq!(
            recovered.state.balance(),
            999,
            "post-checkpoint overlay write must WIN (last-writer-wins); a dropped \
             overlay would leave the stale checkpoint value 100"
        );
    }

    #[tokio::test]
    async fn convergence_root_mismatch_refuses_to_start() {
        // Same overlay, but the durably recorded finalized root is WRONG (does
        // not match the reconstructed root). The convergence verdict
        // (`verify_recovery_convergence`, deferred out of construction so the
        // genesis baseline can be reseeded first) MUST fail closed.
        let seed = 0x3c;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(
            tmp.path(),
            seed,
            7,
            42,
            [0xde; 32], // deliberately NOT the post-overlay root
        );

        // Construction itself succeeds (it reconstructs the overlay); the verdict
        // is the separate fail-closed step.
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay; the verdict is a separate step");
        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a convergence-root mismatch must FAIL CLOSED, not log-and-continue");
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }

    #[tokio::test]
    async fn convergence_root_match_starts_normally() {
        // Control: the SAME path with a CORRECT recorded root must pass the
        // verdict (proves the fail-closed Err is reached only on genuine
        // divergence, not always). With a checkpoint present, the reconstructed
        // ledger is already complete, so the verdict converges with no reseed.
        let seed = 0x77;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("a converging recovery must construct");
        state
            .verify_recovery_convergence()
            .await
            .expect("a converging recovery must pass the verdict");
        let guard = state.read().await;
        let recovered = guard
            .ledger
            .get(&cell(seed, 0).id())
            .expect("recovered cell present");
        assert_eq!(recovered.state.balance(), 42);
    }

    /// Seed a store with NO checkpoint (the sub-first-checkpoint case) and a
    /// single finalized turn at `height` whose ONLY touched cell is `touched`.
    /// The recorded finalized root is `record_root`. This reproduces the
    /// federation bring-up bug: a node that finalized a turn while still below
    /// `LEDGER_CHECKPOINT_INTERVAL` has no checkpoint to restore its UNTOUCHED
    /// genesis cells from, and the commit-log overlay carries only `touched`.
    fn seed_sub_checkpoint_store(dir: &Path, height: u64, touched: &Cell, record_root: [u8; 32]) {
        let db_path = dir.join("dregg.redb");
        let store = PersistentStore::open(&db_path).expect("open store");
        let rec = dregg_persist::CommitRecord {
            ordinal: 0,
            height,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xa1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xa2; 32],
            ledger_root: record_root,
            touched_cells: vec![touched.clone()],
        };
        store
            .commit_finalized_turn(0, &rec)
            .expect("commit sub-checkpoint turn");
    }

    /// The federation bring-up bug, fixed: a node that finalized ONE turn below
    /// the first ledger checkpoint, then RESTARTED with its redb intact (NOT
    /// wiped), recovers cleanly — same finalized state/root, no STORE INTEGRITY
    /// EVENT — once the genesis baseline is reseeded (as `run_node` does).
    #[tokio::test]
    async fn sub_checkpoint_restart_with_untouched_genesis_recovers() {
        let tmp = tempfile::tempdir().expect("tempdir");

        // A turn rewrote cell A; the genesis cells G1/G2 were NEVER touched.
        let touched = cell(0xa1, 500);
        let g1 = cell(0xb1, 10);
        let g2 = cell(0xb2, 20);

        // The committing node recorded the root of the FULL ledger {A', G1, G2}.
        let mut full = Ledger::new();
        full.insert_cell(touched.clone()).expect("A'");
        full.insert_cell(g1.clone()).expect("G1");
        full.insert_cell(g2.clone()).expect("G2");
        let recorded_root = crate::blocklace_sync::canonical_ledger_root(&full);

        // Store: NO checkpoint, one finalized turn at height 5 (< 100) touching
        // ONLY A. recovered_ledger_root() == recorded_root (the full ledger).
        seed_sub_checkpoint_store(tmp.path(), 5, &touched, recorded_root);

        // Construction reconstructs ONLY {A'} (no checkpoint → empty base; the
        // overlay carries only the touched cell).
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the touched-cell overlay");

        // BEFORE reseeding the genesis baseline the verdict FAILS — exactly the
        // sub-checkpoint fail-close the fix targets. (This also proves the verdict
        // is non-vacuous: the missing untouched cells DO move the root.)
        assert!(
            state.verify_recovery_convergence().await.is_err(),
            "without the genesis baseline the reconstructed root is incomplete"
        );

        // Reseed the genesis baseline (move-FREE genesis: the untouched cells
        // G1/G2 just need restoring). `run_node` reconstructs genesis-then-
        // overlay via `reseed_genesis_then_overlay`; for a move-free genesis with
        // no id collision that is equivalent to inserting the untouched cells, so
        // we simulate it directly here (no genesis.json plumbing needed). The
        // issuer-well + genesis_moves case — where the ordering MATTERS — is
        // covered by `issuer_well_genesis_recovery_*` below.
        {
            let mut s = state.write().await;
            let _ = s.ledger.insert_cell(g1.clone());
            let _ = s.ledger.insert_cell(g2.clone());
        }

        // AFTER reseed the ledger is the full finalized ledger {A', G1, G2}; the
        // verdict converges and the node recovers cleanly — no wipe required.
        state
            .verify_recovery_convergence()
            .await
            .expect("a legitimate sub-checkpoint restart must recover after genesis reseed");

        let guard = state.read().await;
        assert_eq!(
            guard
                .ledger
                .get(&touched.id())
                .expect("touched cell present")
                .state
                .balance(),
            500,
            "the finalized turn's post-state must survive the restart"
        );
        assert_eq!(
            guard
                .ledger
                .get(&g1.id())
                .expect("G1 reseeded")
                .state
                .balance(),
            10
        );
        assert_eq!(
            crate::blocklace_sync::canonical_ledger_root(&guard.ledger),
            recorded_root,
            "the recovered root must equal the finalized root the committing node recorded"
        );
    }

    /// The integrity guarantee is PRESERVED: a genuinely corrupt store still
    /// fails closed even AFTER the genesis baseline is reseeded. The overlay
    /// carries a TAMPERED value for the touched cell; reseeding is insert-if-
    /// absent and cannot overwrite it, so the verdict MUST still refuse to start.
    #[tokio::test]
    async fn sub_checkpoint_corrupt_overlay_still_fails_closed_after_reseed() {
        let tmp = tempfile::tempdir().expect("tempdir");

        let genuine = cell(0xa1, 500); // what the recorded root commits
        let corrupt = cell(0xa1, 999); // SAME id, tampered balance (in the overlay)
        let g1 = cell(0xb1, 10);

        let mut full = Ledger::new();
        full.insert_cell(genuine.clone()).expect("genuine A");
        full.insert_cell(g1.clone()).expect("G1");
        let recorded_root = crate::blocklace_sync::canonical_ledger_root(&full);

        // Store records the genuine root but the overlay holds the TAMPERED cell.
        seed_sub_checkpoint_store(tmp.path(), 5, &corrupt, recorded_root);

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the (tampered) overlay");

        // Reseed the genesis baseline — insert-if-absent leaves the tampered
        // touched cell untouched (it is already present in the overlay).
        {
            let mut s = state.write().await;
            let _ = s.ledger.insert_cell(g1.clone());
        }

        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a corrupt overlay must STILL fail closed even after genesis reseed");
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }

    // ---- Issuer-well genesis recovery (the genesis_moves ordering fix) ----
    //
    // THE EPOCH §5 genesis is an ISSUER-WELL economy: a negative-balance issuer
    // well funds its recipients via `genesis_moves` (Σδ = 0). On a
    // sub-checkpoint restart the recovered commit-log overlay already carries
    // the FINALIZED post-state of every cell a turn TOUCHED — INCLUDING any
    // move RECIPIENT (e.g. the faucet) the bot drew from. Recovery must
    // reconstruct `genesis_baseline ⊕ overlay` in the SOUND order
    // (`reseed_genesis_then_overlay`): build the genesis baseline FIRST on a
    // fresh ledger so the `genesis_moves` run EXACTLY ONCE, THEN re-apply the
    // overlay so the touched recipient's finalized post-state WINS. The old
    // order (genesis reseed OVER the overlay) replayed the moves across the
    // whole ledger and re-credited the already-overlaid recipient — a
    // double-credit that produced the WRONG root and fail-closed a healthy node
    // (the move-free recovery tests above never exercised a `genesis_move`, so
    // this hid).

    /// hex of a `[seed; 32]` byte array (the `cell(seed, _)` public key).
    fn hx(seed: u8) -> String {
        dregg_types::hex_encode(&[seed; 32])
    }

    /// hex of the content-addressed id of `cell(seed, _)` (balance-independent).
    fn id_hex(seed: u8) -> String {
        dregg_types::hex_encode(&cell(seed, 0).id().0)
    }

    /// An issuer-well genesis: the well (`WELL`) funds the faucet (`FAUCET`,
    /// `faucet_amount`) and alice (`ALICE`, `alice_amount`) via two
    /// `genesis_moves`. Cell ids/keys are the `cell(seed, _)` derivation so the
    /// overlay (built from the SAME helper) shares ids with the genesis cells.
    fn issuer_well_genesis(
        well: u8,
        faucet: u8,
        alice: u8,
        faucet_amount: u64,
        alice_amount: u64,
    ) -> serde_json::Value {
        let supply = (faucet_amount + alice_amount) as i64;
        serde_json::json!({
            "issuer_well": id_hex(well),
            "genesis_moves": [
                { "from": id_hex(well), "to": id_hex(faucet), "amount": faucet_amount },
                { "from": id_hex(well), "to": id_hex(alice),  "amount": alice_amount  },
            ],
            "initial_cells": [
                // The well carries −supply; the column sums to zero.
                { "id": id_hex(well),   "public_key": hx(well),   "token_id": hx(well.wrapping_add(7)),   "balance": -supply },
                { "id": id_hex(faucet), "public_key": hx(faucet), "token_id": hx(faucet.wrapping_add(7)), "balance": faucet_amount as i64 },
                { "id": id_hex(alice),  "public_key": hx(alice),  "token_id": hx(alice.wrapping_add(7)),  "balance": alice_amount as i64 },
            ],
        })
    }

    /// The issuer-well recovery: a move RECIPIENT (faucet) is ALSO in the
    /// commit-log overlay (bot-touched, post-bot value). Recovery must apply the
    /// `genesis_moves` ONCE and let the overlay's post-state WIN — NOT
    /// double-credit the faucet — reconstructing the correct finalized root.
    #[tokio::test]
    async fn issuer_well_genesis_recovery_applies_moves_once() {
        let (well, faucet, alice) = (0xe1u8, 0xf1u8, 0xa2u8);
        let (faucet_amount, alice_amount) = (1_000u64, 250u64);
        let supply = (faucet_amount + alice_amount) as i64; // 1250

        // The bot drew on the faucet AFTER genesis: its FINALIZED balance is the
        // post-bot value carried by the commit-log overlay (NOT the genesis
        // 1000, and emphatically NOT the double-credited 2000).
        let faucet_post_bot = 1_750i64;

        // The committing node recorded the root of the FULL finalized ledger:
        // genesis baseline {WELL −1250, faucet 1000, alice 250} with the faucet
        // OVERWRITTEN by its post-bot value.
        let mut full = Ledger::new();
        full.insert_cell(cell(well, -supply)).expect("well");
        full.insert_cell(cell(faucet, faucet_post_bot))
            .expect("faucet");
        full.insert_cell(cell(alice, alice_amount as i64))
            .expect("alice");
        let recorded_root = crate::blocklace_sync::canonical_ledger_root(&full);

        // Store: NO checkpoint (sub-first-checkpoint), one finalized turn at
        // height 5 touching ONLY the faucet (its post-bot value). The recorded
        // finalized root is the FULL ledger root.
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_sub_checkpoint_store(tmp.path(), 5, &cell(faucet, faucet_post_bot), recorded_root);

        // Construction reconstructs the overlay = {faucet @ post-bot}.
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the touched-faucet overlay");

        // Reconstruct in the SOUND order exactly as `run_node` does.
        let genesis = issuer_well_genesis(well, faucet, alice, faucet_amount, alice_amount);
        {
            let mut s = state.write().await;
            let stats = crate::reseed_genesis_then_overlay(&genesis, &mut s.ledger);
            assert_eq!(
                stats.invalid, 0,
                "genesis baseline must materialize cleanly — the moves run ONCE on the \
                 fresh ledger, so every declared balance matches"
            );
        }

        let guard = state.read().await;
        let faucet_bal = guard
            .ledger
            .get(&cell(faucet, 0).id())
            .expect("faucet present")
            .state
            .balance();
        assert_eq!(
            faucet_bal,
            faucet_post_bot,
            "the overlay's FINALIZED faucet post-state must WIN; the genesis move must \
             NOT be re-applied on top of it (double-credit would yield {})",
            faucet_post_bot + faucet_amount as i64
        );
        assert_ne!(
            faucet_bal,
            faucet_post_bot + faucet_amount as i64,
            "guard against the double-credit bug specifically"
        );
        assert_eq!(
            guard
                .ledger
                .get(&cell(well, 0).id())
                .expect("well present")
                .state
                .balance(),
            -supply,
            "the issuer well must be debited EXACTLY −supply (each move applied once)"
        );
        assert_eq!(
            guard
                .ledger
                .get(&cell(alice, 0).id())
                .expect("alice present")
                .state
                .balance(),
            alice_amount as i64,
            "an UNtouched recipient keeps its single genesis credit"
        );
        assert_eq!(
            crate::blocklace_sync::canonical_ledger_root(&guard.ledger),
            recorded_root,
            "recovery must reconstruct the recorded finalized root (genesis ⊕ overlay)"
        );
        drop(guard);

        // The deferred verdict converges — a clean issuer-well restart recovers.
        state
            .verify_recovery_convergence()
            .await
            .expect("an issuer-well recovery in the sound order must pass the verdict");
    }

    /// Fail-closed is PRESERVED with an issuer-well genesis: a genuinely
    /// divergent overlay (a TAMPERED faucet post-state) still reconstructs a
    /// wrong root, so the verdict STILL refuses to start. The reorder fixes the
    /// double-credit; it does NOT loosen the integrity check.
    #[tokio::test]
    async fn issuer_well_genesis_recovery_corrupt_overlay_fails_closed() {
        let (well, faucet, alice) = (0xe1u8, 0xf1u8, 0xa2u8);
        let (faucet_amount, alice_amount) = (1_000u64, 250u64);
        let supply = (faucet_amount + alice_amount) as i64;

        // The recorded root commits the GENUINE finalized faucet value (1750).
        let genuine_faucet = 1_750i64;
        let mut full = Ledger::new();
        full.insert_cell(cell(well, -supply)).expect("well");
        full.insert_cell(cell(faucet, genuine_faucet))
            .expect("faucet");
        full.insert_cell(cell(alice, alice_amount as i64))
            .expect("alice");
        let recorded_root = crate::blocklace_sync::canonical_ledger_root(&full);

        // But the overlay carries a TAMPERED faucet post-state.
        let tampered_faucet = 9_999i64;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_sub_checkpoint_store(tmp.path(), 5, &cell(faucet, tampered_faucet), recorded_root);

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the (tampered) overlay");

        let genesis = issuer_well_genesis(well, faucet, alice, faucet_amount, alice_amount);
        {
            let mut s = state.write().await;
            let _ = crate::reseed_genesis_then_overlay(&genesis, &mut s.ledger);
        }

        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a tampered issuer-well overlay must STILL fail closed");
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }
}
