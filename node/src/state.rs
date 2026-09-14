//! Node state management.
//!
//! Holds the AgentCipherclerk, Ledger, and PersistentStore handles behind
//! Arc<RwLock<>> for concurrent access from HTTP handlers and the
//! federation sync background task.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;
use std::sync::{Arc, Mutex};
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
use dregg_cell::Requirement;

fn restore_and_verify_faithful_note_tree(
    store: &PersistentStore,
    cclerk: &AgentCipherclerk,
) -> Result<Poseidon2NoteTree, String> {
    let durable_note_commitments: Vec<[u8; 32]> = store
        .load_all_note_commitments()
        .map_err(|e| format!("failed to restore faithful note tree: {e}"))?
        .into_iter()
        .map(|commitment| commitment.0)
        .collect();
    let tree = Poseidon2NoteTree::from_blake3_commitments(&durable_note_commitments, 16);

    let Some(expected) = store
        .faithful_note_root_expectation()
        .map_err(|e| format!("faithful note-root restart seal refused: {e}"))?
    else {
        return Ok(tree);
    };
    let durable_count = u64::try_from(tree.size())
        .map_err(|_| "faithful note-tree size does not fit u64".to_string())?;
    let durable_root =
        dregg_persist::CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
    if expected.note_count != durable_count || expected.root != durable_root {
        return Err(format!(
            "faithful note-root restart mismatch: sealed count/root ({}, {:?}) != durable tree ({durable_count}, {:?})",
            expected.note_count, expected.root, durable_root
        ));
    }
    let latest = store
        .latest_attested_root()
        .map_err(|e| format!("failed to load faithful live attestation: {e}"))?
        .ok_or_else(|| "faithful history exists without a live attested root".to_string())?;
    if latest.height != expected.height || latest.note_tree_root != Some(expected.root.to_bytes()) {
        return Err(
            "faithful history head and latest live attestation disagree on height/root".to_string(),
        );
    }

    // The live history is node-author authenticated: reconstruct that exact
    // local hybrid identity and replay every row, so a checksum-preserving row
    // edit or deleted suffix refuses before the node serves.
    let seed = cclerk.gossip_signing_key().to_bytes();
    let local_ed = cclerk.public_key();
    let (local_pq, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
    store
        .load_faithful_note_root_history_hybrid(
            std::slice::from_ref(&local_ed),
            std::slice::from_ref(&local_pq),
            1,
            expected,
        )
        .map_err(|e| format!("faithful note-root authenticated replay refused: {e}"))?;
    Ok(tree)
}

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

/// The EFFECTIVE lean-producer setting for a freshly constructed node state: the
/// operator's env intent (`lean_producer_env_enabled`) AND the build-time fact that
/// the verified Lean executor archive is actually linked
/// (`dregg_lean_ffi::lean_available`).
///
/// A marshal-only binary (no `libdregg_lean.a`) cannot run the verified producer no
/// matter what the env says — and `lean_producer_enabled` is the field every
/// reporting surface reads (`/status` `state_producer`/`lean_producer`, doctor,
/// MCP). Leaving it `true` on a marshal-only build makes those surfaces present an
/// UN-verified node as verified — the exact "serve as if verified" failure the
/// marshal-only startup tripwire in `main.rs` exists to prevent, surviving on the
/// API surface after the tripwire was bypassed with
/// `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`.
pub fn lean_producer_effective(env_enabled: bool, lean_linked: bool) -> bool {
    env_enabled && lean_linked
}

#[cfg(test)]
mod lean_producer_effective_tests {
    use super::lean_producer_effective;

    /// A marshal-only build must never report the lean producer, regardless of
    /// env intent — `/status` would otherwise present an un-verified node as
    /// verified.
    #[test]
    fn marshal_only_build_never_reports_lean_producer() {
        assert!(!lean_producer_effective(true, false));
        assert!(!lean_producer_effective(false, false));
    }

    /// A lean-linked build honors the operator's env opt-out.
    #[test]
    fn linked_build_respects_env_intent() {
        assert!(lean_producer_effective(true, true));
        assert!(!lean_producer_effective(false, true));
    }
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
    /// A promise outcome derived from an already-durable finalized commit.
    PromiseResolution {
        resolution: crate::promise_resolutions::PromiseResolutionRecord,
    },
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
    /// The node-hosted, restart-durable REALM substrate (`realm-model` graduated
    /// into the running node). Realm/instance turns are admitted through
    /// realm-model's gate and persisted to the durable `REALM_LOG`, reloaded on
    /// boot so a realm created through the node survives a restart. See
    /// [`crate::realm_service`].
    realms: Arc<RwLock<crate::realm_service::NodeRealms>>,
    /// The node-hosted ENCRYPTED CALL AUCTION ([`crate::dark_clearing_service`]): live clearing
    /// sessions (each with its own Shamir BFV custody quorum and pinned trader roster) plus this
    /// surface's receipt chain. In-memory by design — a clearing session's custody shares are
    /// deliberately not persisted, so a restart ends every open session rather than reviving a
    /// key from disk.
    dark_clearing: Arc<RwLock<crate::dark_clearing_service::NodeDarkClearing>>,
}

/// One fixed-size, cursor-only page of the public append-only faithful note
/// mirror.  Callers cannot select a note or page number: the supported client
/// path starts at cursor zero and consumes every returned continuation.
#[derive(Clone, Debug)]
pub struct FaithfulNoteMirrorPage {
    pub commitment_cursor: u64,
    pub next_commitment_cursor: u64,
    pub history_cursor: u64,
    pub next_history_cursor: u64,
    pub nullifier_cursor: u64,
    pub next_nullifier_cursor: u64,
    pub nullifier_count: u64,
    pub commitments: Vec<[u8; 32]>,
    pub nullifiers: Vec<([u8; 32], u64, u64)>,
    pub anchor: dregg_persist::FaithfulNoteRootAnchorV1,
    pub history: Vec<dregg_persist::FaithfulNoteRootEnvelopeV1>,
    pub head: dregg_persist::FaithfulNoteRootExpectationV1,
    pub latest_attested_root: dregg_persist::StoredAttestedRoot,
    /// Target-independent FNMS-v1 certificate over the exact mirror head,
    /// hybrid-signed by the same pinned node author as FNHR rows.
    pub head_hybrid_quorum: Vec<dregg_types::HybridQuorumSig>,
}

pub const FAITHFUL_MIRROR_COMMITMENT_PAGE_SIZE: usize = 256;
pub const FAITHFUL_MIRROR_HISTORY_PAGE_SIZE: usize = 16;
pub const FAITHFUL_MIRROR_NULLIFIER_PAGE_SIZE: usize = 256;

fn faithful_mirror_head_signing_message(
    anchor: &dregg_persist::FaithfulNoteRootAnchorV1,
    head: dregg_persist::FaithfulNoteRootExpectationV1,
    nullifier_count: u64,
    nullifier_root: [u8; 32],
) -> [u8; 176] {
    let mut out = [0u8; 176];
    out[0..4].copy_from_slice(b"FNMS");
    out[4..6].copy_from_slice(&1u16.to_le_bytes());
    out[6..8].copy_from_slice(&0u16.to_le_bytes());
    out[8..40].copy_from_slice(&anchor.session_id);
    out[40..72].copy_from_slice(&anchor.federation_id);
    out[72..80].copy_from_slice(&anchor.committee_epoch.to_le_bytes());
    out[80..88].copy_from_slice(&head.records.to_le_bytes());
    out[88..96].copy_from_slice(&head.height.to_le_bytes());
    out[96..104].copy_from_slice(&head.note_count.to_le_bytes());
    out[104..136].copy_from_slice(head.root.as_bytes());
    out[136..144].copy_from_slice(&nullifier_count.to_le_bytes());
    out[144..176].copy_from_slice(&nullifier_root);
    out
}

/// Fail-closed refusal from the target-independent faithful mirror surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulMirrorError {
    /// No sealed faithful history/latest attestation exists yet.
    NoAuthenticatedHead,
    /// Durable state could not be read or reconstructed exactly.
    DurableState(String),
    /// Two supposedly authoritative views of the current head disagree.
    InconsistentHead(String),
}

impl std::fmt::Display for FaithfulMirrorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAuthenticatedHead => {
                write!(f, "no authenticated faithful note-root head is available")
            }
            Self::DurableState(reason) => write!(f, "durable faithful state refused: {reason}"),
            Self::InconsistentHead(reason) => {
                write!(f, "faithful head/tree consistency check refused: {reason}")
            }
        }
    }
}

impl std::error::Error for FaithfulMirrorError {}

/// Every coordinate that can change the public faithful mirror.  A cache hit
/// requires exact equality, including the authenticated history segment and
/// the complete attested-root record (not merely its height).
#[derive(Clone, Debug, PartialEq, Eq)]
struct FaithfulMirrorSnapshotKey {
    expectation: dregg_persist::FaithfulNoteRootExpectationV1,
    segment_head: dregg_persist::FaithfulNoteRootAnchorV1,
    latest_attested_root: dregg_persist::StoredAttestedRoot,
    nullifier_count: u64,
}

/// One immutable exact-head image shared by every cursor page at that head.
/// The cache holds at most one of these O(chain state) snapshots; replacing it
/// on a head change drops the old image once in-flight pages release their Arc.
#[derive(Clone, Debug)]
struct FaithfulMirrorSnapshot {
    key: FaithfulMirrorSnapshotKey,
    commitments: Arc<[[u8; 32]]>,
    nullifiers: Arc<[([u8; 32], u64, u64)]>,
    anchor: dregg_persist::FaithfulNoteRootAnchorV1,
    history: Arc<[dregg_persist::FaithfulNoteRootEnvelopeV1]>,
    head_hybrid_quorum: Arc<[dregg_types::HybridQuorumSig]>,
}

#[derive(Debug, Default)]
struct FaithfulMirrorSnapshotCache {
    snapshot: Option<Arc<FaithfulMirrorSnapshot>>,
    #[cfg(test)]
    builds: u64,
}

/// The inner mutable state of the node.
// Some fields back cfg-conditional / not-yet-consulted node surfaces (routing,
// cross-federation revocation, threshold shares); retained as wired scaffolding.
pub struct NodeStateInner {
    /// The agent cipherclerk (identity, wallet, receipts).
    pub cclerk: AgentCipherclerk,
    /// The cell ledger (local cell state).
    pub ledger: Ledger,
    /// Persistent storage backend.
    ///
    /// `Arc` so the cipherclerk's receipt-chain durability sink
    /// ([`AgentCipherclerk::set_receipt_persist`]) can hold its own handle and
    /// persist each appended receipt under the state lock. Transparent to the
    /// `&self` store calls elsewhere (deref coercion).
    pub store: Arc<PersistentStore>,
    /// Exact-head-keyed, single-entry faithful mirror cache.  Interior
    /// mutability permits concurrent HTTP readers to share one reconstruction
    /// and one ML-DSA signature while the outer node-state read lock prevents a
    /// finalization transition from racing page extraction.
    faithful_mirror_cache: Mutex<FaithfulMirrorSnapshotCache>,
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
    /// HYBRID-PQ: the committee's ML-DSA-65 public keys, INDEX-ALIGNED with
    /// [`Self::known_federation_keys`] — element `i` is the ML-DSA key of the
    /// member whose ed25519 key is `known_federation_keys[i]` (both derived
    /// from the same 32-byte seed; genesis publishes them side by side).
    /// EMPTY means "hybrid not configured": the finalization-vote collector
    /// then holds no PQ keys and counts NO votes toward quorum (fail-closed —
    /// never a silent ed25519-only downgrade).
    pub known_federation_ml_dsa_keys: Vec<dregg_federation::frost::MlDsaPublicKey>,
    /// Registry of federations the local node knows about (both the local
    /// federation and any peer federations registered out-of-band).
    /// Replaces the disjoint pair of (known_federation_keys, federation_id)
    /// per the unification design §3.
    pub known_federations: dregg_federation::KnownFederations,
    /// Whether federation keys have been configured. When `false`, the node operates
    /// in "discovery mode" and will not finalize attested roots (Issue 10).
    pub federation_configured: bool,
    /// Canonical federation_id. COUPLED-CORE: derived from the HYBRID committee
    /// member ids (`hybrid_id_commitment` over `known_federation_keys` +
    /// `known_federation_ml_dsa_keys`) + `committee_epoch` via
    /// [`dregg_federation::derive_federation_id_hybrid_with_epoch`], so it commits
    /// to the ML-DSA roster and matches what genesis wrote. Recomputed whenever
    /// the committee changes via [`Self::set_federation_keys_hybrid`]. Closes
    /// audit F1: this id is bound to the committee, not a random tag.
    pub federation_id: [u8; 32],
    /// Current committee epoch (rotates with key rotations).
    pub committee_epoch: u64,
    /// Committees derived from the persisted lace's finalized membership
    /// history at boot (`committee_replay::derive_from_lace`), genesis first.
    /// Empty when the chain carries no amendments.
    ///
    /// ⚑ The signed-anchor recovery check verifies each attested-root quorum
    /// against exactly ONE of these: the version that was current at the
    /// root's anchored block ([`Self::derived_committee_version_at_block`]).
    /// It used to accept ANY entry, justified as "every entry is unforgeable
    /// to an adversary holding no committee keys" — but a member rotated OUT
    /// (an evicted equivocator above all) holds exactly the keys of a former
    /// version, and a quorum verified against the wrong roster is not a
    /// verified quorum.
    pub derived_committee_history: Vec<Vec<dregg_types::PublicKey>>,
    /// HYBRID-PQ twin of [`Self::derived_committee_history`]: element `i` is
    /// the ENROLLED ML-DSA-65 roster aligned index-for-index with
    /// `derived_committee_history[i]`. Derived at boot from the
    /// genesis-published roster plus each ratified `Join` block's carried
    /// `ml_dsa_pubkey` (the same signed source the live
    /// `learn_committee_member_hybrid_key` trusts). An entry is EMPTY (never
    /// partial) when any of its members' keys is underivable — the restart
    /// hybrid re-verify (`verify_finalization_quorum`) then REFUSES a root
    /// attributed to that version rather than downgrade to ed25519-only
    /// (fail-closed; the documented bound).
    pub derived_committee_ml_dsa_history: Vec<Vec<dregg_federation::frost::MlDsaPublicKey>>,
    /// For every finalized actionable block of the restored lace: the
    /// committee VERSION (index into [`Self::derived_committee_history`]) that
    /// was current when the boot replay served it — the committee whose quorum
    /// legitimately finalizes that block. Keyed by the raw `BlockId` bytes.
    /// Empty when the chain carries no amendments (single version, no
    /// ambiguity). The recovery anchor resolves every attested root through
    /// this map; a root whose anchored block cannot be resolved does NOT
    /// verify (fail closed).
    pub derived_committee_version_at_block: std::collections::HashMap<[u8; 32], u64>,
    /// Boot handoff: the REPLAYED `ConstitutionManager` from
    /// `committee_replay::derive_from_lace` (main sets it right after the
    /// derivation; `run_blocklace_sync` `take()`s it as the consensus
    /// constitution seed). Carrying the full manager — not just the participant
    /// list — preserves IN-FLIGHT proposal/vote state across a restart, so a
    /// proposal that had gathered votes before shutdown can still pass after,
    /// exactly as on peers that never restarted. `None` = no derivation ran
    /// (fresh chain / solo bootstrap): seed from the configured committee.
    pub boot_constitution: Option<dregg_blocklace::constitution::ConstitutionManager>,
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
    /// (read at state construction) or by clearing this field. On a marshal-only binary (no linked
    /// `libdregg_lean.a`) this is FORCED `false` at construction (`lean_producer_effective`) so
    /// `/status` and every other reporting surface never present an un-verified node as verified. A turn touching a characterized
    /// root-gap effect (root provably diverges) or an unmappable effect falls back to the Rust
    /// producer for that turn, with a logged reason — never a silent commit of divergent state.
    pub lean_producer_enabled: bool,
    /// THE EPOCH §5 ("fees as moves"): the FEE WELL cell from genesis
    /// (`genesis.json` `fee_well`). Wired onto every executor via
    /// [`crate::executor_setup::configure_turn_executor`] so undelivered fee
    /// shares MOVE here instead of burning — committed turns conserve
    /// exactly.
    pub fee_well: Option<CellId>,
    /// COORDINATION-TURN fee exemption from genesis (`genesis.json`
    /// `coordination_fee_exempt`, default `false`). Genesis-declared so every
    /// committee node agrees — admission is consensus-relevant. Wired onto
    /// every executor via
    /// [`crate::executor_setup::configure_turn_executor`] as
    /// `costs.coordination_exempt`: EmitEvent-only turns with no
    /// `balance_change` may then carry `fee = 0` ("leash, not ledger" — the
    /// computron is an oversight budget, and coordination turns ARE the
    /// oversight traffic). Economic turns charge exactly as before; receipts
    /// keep the true `computrons_used`.
    pub coordination_fee_exempt: bool,
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
    /// ROTATION's `CommitBindsMMR` weld. Until then the strongest served
    /// binding is `GET /api/receipts/index/head`: the same root SIGNED by the
    /// node's federation key and anchored to the latest quorum-pinned
    /// attested root — node-bound + consensus-ANCHORED, deliberately NOT
    /// claimed as quorum-bound (receipt hashes absorb the local wall clock
    /// and the chain interleaves node-local turns, so a committee cannot
    /// co-sign this per-node root; the rung ladder toward the real quorum
    /// weld is docs/deos/CONSENSUS-BINDS-INDEX.md).
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
    pub deos_server_surfaces: HashMap<CellId, Vec<(String, dregg_cell::Requirement)>>,
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
    /// (`crate::pg_mirror`; .docs-history-noclaude/PG-DREGG.md §8.)
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

/// Apply one resolved durable-overlay operation to the recovering ledger — the
/// Rust denotation of the Lean `CrashRecovery.applyWrites` step over the
/// `Write = insert | remove` alphabet.
///
/// * `Upsert` is last-writer-wins ([`upsert_cell`], remove-then-insert): a
///   post-checkpoint write must OVERWRITE the checkpoint value, never be dropped.
/// * `Remove` is a tombstone ([`Ledger::remove`]): a cell the finalized turn
///   stream removed from the hosted set (MakeSovereign) must NOT survive
///   `checkpoint ⊕ overlay`. Dropping the removal (an insert-only overlay) would
///   RESURRECT it as hosted and diverge the reconstructed root — the bug this
///   dimension closes, and exactly what the Lean `recover_eq_replay` catch forbids.
fn apply_overlay_op(ledger: &mut Ledger, op: dregg_persist::CellOverlayOp) {
    match op {
        dregg_persist::CellOverlayOp::Upsert(cell) => upsert_cell(ledger, cell),
        dregg_persist::CellOverlayOp::Remove(id) => {
            let _ = ledger.remove(&id);
        }
    }
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

/// Recovery-convergence read-error policy (finding F3): a READ ERROR of the
/// recorded finalized-root row is FATAL (fail closed) exactly when the node has
/// finalized state to protect — a NON-ZERO commit cursor. On a fresh/zero-cursor
/// node there is nothing to converge to, so the error is non-fatal (boot). If
/// the cursor ITSELF is unreadable we cannot prove the node is fresh, so we fail
/// closed rather than laundering a corrupt store into a clean boot.
fn recovery_read_error_is_fatal(cursor: Result<u64, dregg_persist::StoreError>) -> bool {
    match cursor {
        Ok(0) => false,
        Ok(_) => true,
        Err(_) => true,
    }
}

/// Resolve the ONE committee entitled to have quorum-signed `root`: the
/// committee version that was current at the root's anchored block, per the
/// boot replay of the chain's own membership history
/// (`committee_replay::derive_from_lace` →
/// [`NodeStateInner::derived_committee_version_at_block`]).
///
/// This is the committee-specificity weld for the restart path: a quorum is a
/// quorum OF the committee that was current when the root was finalized —
/// "verifies against some committee we once knew" admits every rotated-out
/// member's keys (an evicted equivocator's above all) as anchor authority
/// forever. The same defect class as a missing `config_seq`.
///
/// * No amendments on this chain ⇒ one committee for its whole history: the
///   configured one (`known_federation_keys` + its aligned ML-DSA roster).
/// * Amended chain ⇒ the root must carry a `blocklace_block_id` that resolves
///   through the version map; the derived history entry for that version is
///   the ONLY committee consulted. `Err` (fail closed) when the root carries
///   no anchor block or anchors a block the restored lace does not know — the
///   caller must treat the root as unverifiable, and an unverifiable root
///   that CLAIMS a quorum as forged.
pub(crate) fn anchor_committee_for_root<'a>(
    s: &'a NodeStateInner,
    root: &dregg_persist::StoredAttestedRoot,
) -> Result<
    (
        &'a [dregg_types::PublicKey],
        &'a [dregg_federation::frost::MlDsaPublicKey],
    ),
    String,
> {
    if s.derived_committee_history.len() <= 1 {
        // No amendments: the configured committee is the only committee this
        // chain has ever had. (An empty configured committee is the caller's
        // "no keys loaded" fail-safe, not an error here.)
        return Ok((
            s.known_federation_keys.as_slice(),
            s.known_federation_ml_dsa_keys.as_slice(),
        ));
    }
    let Some(block_id) = root.blocklace_block_id else {
        return Err(format!(
            "attested root at height {} carries no blocklace_block_id on an amended chain — the \
             committee version that signed it cannot be resolved",
            root.height
        ));
    };
    let Some(version) = s.derived_committee_version_at_block.get(&block_id).copied() else {
        return Err(format!(
            "attested root at height {} anchors block {} which the restored lace does not know — \
             no committee version can vouch for it",
            root.height,
            dregg_types::hex_encode(&block_id)
        ));
    };
    let committee = s
        .derived_committee_history
        .get(version as usize)
        .ok_or_else(|| {
            format!(
                "attested root at height {} resolves to committee version {version} but the \
                 derived history has {} entries — inconsistent boot derivation",
                root.height,
                s.derived_committee_history.len()
            )
        })?;
    let roster = s
        .derived_committee_ml_dsa_history
        .get(version as usize)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    Ok((committee.as_slice(), roster))
}

/// Boot torn-tail recovery, with the ONE case where a non-converging walk is
/// INCONCLUSIVE rather than fatal.
///
/// [`PersistentStore::recover_to_last_consistent`] reconstructs
/// `base ⊕ checkpoint ⊕ overlay` and keeps the last commit ordinal whose
/// reconstructed root matches the root that record committed — with an EMPTY
/// base. That comparison is only meaningful when a ledger CHECKPOINT exists,
/// because a checkpoint is a full snapshot that carries the genesis cells, while
/// the commit-log overlay carries only the cells a turn TOUCHED and every
/// record's `ledger_root` commits the FULL ledger (genesis ⊕ touched).
///
/// With NO checkpoint the reconstruction is the touched-cell delta on an empty
/// base, so it mismatches at EVERY ordinal and the walk reports "no salvageable
/// prefix" for a perfectly consistent image. persist proves exactly this about
/// its own no-baseline variant (`recover_from_base_does_not_falsely_strand_a_sub_checkpoint_image`,
/// persist/src/commit_log.rs) and ships the remedy —
/// `recover_to_last_consistent_from_base` — which had NO production caller.
///
/// It is not theoretical. Measured 2026-07-26: `kill -9` on a devnet node that
/// had finalized three faucet turns and never checkpointed left an image that
/// REFUSED TO BOOT AGAIN ("NO commit-log prefix reconstructs to its recorded
/// root"). The first ledger checkpoint lands at `--checkpoint-interval` blocks
/// (default 1000) or on graceful shutdown, so every young node — every devnet —
/// sits inside that window, where any crash that is not a clean SIGTERM is
/// terminal for the data dir.
///
/// SEMANTICS, out loud: what is skipped is the tail TRUNCATION, never the
/// integrity VERDICT. "No converging prefix" is exactly the case where there is
/// no last-good ordinal to truncate TO, so truncation could not have helped
/// anyway; when a prefix DOES converge the tail is still truncated as before.
/// The verdict belongs to [`NodeStateInner::verify_recovery_convergence`] — which
/// `run_node` calls after `reseed_genesis_then_overlay` rebuilds the genesis
/// baseline, which exits the process on mismatch, and which carries the
/// quorum-signed-anchor and anti-rollback legs.
///
/// That deferral is the design this file already documents twice: the overlay
/// step ~130 lines below ("the recovery-convergence verdict is DEFERRED to
/// `verify_recovery_convergence` ... comparing against it before the genesis
/// baseline is rebuilt would fail-close every legitimate sub-checkpoint
/// restart"), and the tests `convergence_root_mismatch_refuses_to_start` and
/// `dropped_removal_resurrects_and_diverges_the_root`, which assert construction
/// SUCCEEDS and "the verdict is a separate step". Both of those tests were RED —
/// the early fatal had been overriding the intent, unnoticed.
///
/// A non-Integrity store error is a different animal — a broken database rather
/// than a comparison that cannot be made — and stays FATAL.
fn run_boot_torn_tail_recovery(store: &PersistentStore) -> Result<(), String> {
    let error = match store.recover_to_last_consistent() {
        Ok(0) => return Ok(()),
        Ok(n) => {
            tracing::warn!(
                truncated = n,
                "boot recovery: truncated {n} divergent commit-log record(s) to the \
                 last-consistent ordinal (torn-tail crash recovery); peers will backfill"
            );
            return Ok(());
        }
        Err(e) => e,
    };

    if !matches!(error, dregg_persist::StoreError::Integrity(_)) {
        return Err(format!(
            "boot recovery (recover_to_last_consistent) failed: {error}"
        ));
    }

    // Was the base the walk used able to reproduce a full-ledger root at all?
    // Only a checkpoint carries the genesis cells. `latest_ledger_checkpoint_height`
    // cannot answer this — a real checkpoint AT height 0 is exactly what a
    // graceful shutdown writes on a young node — so ask for the checkpoint itself.
    let checkpointed = matches!(store.load_latest_ledger_checkpoint(), Ok(Some(_)));
    tracing::warn!(
        error = %error,
        checkpointed,
        "boot recovery: the torn-tail walk found NO converging commit-log prefix, so there \
         is no last-good ordinal to truncate to and the tail is left intact. With no ledger \
         checkpoint this is INCONCLUSIVE rather than a corruption finding — the walk \
         reconstructs the touched-cell delta on an EMPTY base and cannot reproduce any \
         record's full-ledger root. The verdict is deferred to verify_recovery_convergence, \
         which runs once the genesis baseline is reseeded and still REFUSES to start on \
         genuine divergence"
    );
    Ok(())
}

/// Make the cipherclerk's receipt chain durable across a restart.
///
/// THE WELD the deep-reads converged on: the served `/api/receipts*` chain and
/// its receipt-index MMR head are projected from `cclerk.receipt_chain()` (via
/// [`NodeStateInner::sync_receipt_index`]), which used to rebuild EMPTY every
/// boot — so `/api/receipts/index/head` served `len = 0` after a restart even
/// though the durable ledger recovered. This does two things, in order:
///
/// 1. RESTORE: reload the complete dense durable receipt chain back into the
///    cipherclerk. A gap, undecodable entry, or bad agent-scoped predecessor
///    fails node construction; none may be laundered into a shorter accepted
///    history. After this the MMR head rebuilds to its true pre-restart value on
///    the first `sync_receipt_index`.
/// 2. ARM: install the persistence sink so every subsequent `append_receipt`
///    (HTTP ingress, blocklace finalization, MCP, trustline/storage — all paths)
///    writes the receipt to the durable store at its dense index, under the state
///    lock. The sink holds its own `Arc` of the store.
///
/// Called from every constructor right after the cipherclerk is built and before
/// it moves into the state. Recovery and future append failures are fail-closed:
/// a node must not serve an in-memory receipt head it cannot recover durably.
fn install_receipt_chain_durability(
    store: &Arc<PersistentStore>,
    cclerk: &mut AgentCipherclerk,
) -> Result<(), String> {
    // 1. RESTORE the durable chain into the cipherclerk.
    let encoded = store
        .load_receipt_chain()
        .map_err(|e| format!("failed to load durable receipt chain: {e}"))?;
    if !encoded.is_empty() {
        let receipts: Vec<dregg_turn::TurnReceipt> = encoded
            .iter()
            .enumerate()
            .map(|(index, bytes)| {
                postcard::from_bytes(bytes)
                    .map_err(|e| format!("invalid durable receipt at log index {index}: {e}"))
            })
            .collect::<Result<_, _>>()?;
        let persisted = encoded.len();
        let loaded = cclerk
            .restore_receipt_chain(receipts)
            .map_err(|e| format!("invalid durable receipt chain: {e}"))?;
        tracing::info!(
            loaded,
            persisted,
            "restored durable receipt chain on boot (served /api/receipts* + MMR \
             head survive the restart)"
        );
    } else {
        tracing::debug!("no durable receipt chain to restore (fresh node)");
    }

    // 2. ARM the durability sink for all future appends.
    let sink_store = Arc::clone(store);
    cclerk.set_receipt_persist(Arc::new(move |index, receipt| {
        let bytes = postcard::to_stdvec(receipt)
            .map_err(|e| format!("failed to serialize receipt at log index {index}: {e}"))?;
        sink_store
            .append_receipt_chain_entry(index, &bytes)
            .map_err(|e| format!("failed to persist receipt at log index {index}: {e}"))
    }));
    Ok(())
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
    Rejected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
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
        Self::new_with_key_file_and_poa_compact_trust(data_dir, peers, key_file, None)
    }

    /// Construct a node while supplying the independently authenticated Path of Angels
    /// compaction policy derived from the exact deployment/genesis descriptor.
    ///
    /// A positive-floor PoA store can only reopen through this entry.  Passing `None` keeps the
    /// generic-node behavior, but [`PersistentStore::open`] itself refuses any positive compaction
    /// floor, so omission can never silently downgrade verification of stored anchors.
    pub fn new_with_key_file_and_poa_compact_trust(
        data_dir: &Path,
        peers: Vec<String>,
        key_file: &str,
        poa_compact_trust: Option<&dregg_persist::PoaCompactTrustPolicyV1>,
    ) -> Result<Self, String> {
        // A node exists ⇒ its verified coordination gates are armed. See
        // [`crate::install_verified_distributed_gates`] for why this cannot live only in `run()`.
        crate::install_verified_distributed_gates();
        // ⚑ AND ITS DEPLOYED-EXECUTOR ORACLES. This was the half left behind when the gates above
        // were lifted out of `run()`: the constraint + conservation registrations stayed inline in
        // the CLI, so a node obtained any other way (this constructor, the in-process axum router,
        // an embedder linking `dregg-node` as a library) had its coordination seams armed and its
        // executor oracles absent. On a native release build an absent constraint oracle makes
        // `dregg_cell::program::eval` refuse the ENTIRE Lean constraint subset, so such a node could
        // only ever refuse a programmed-cell turn. See [`crate::install_verified_executor_oracles`].
        crate::install_verified_executor_oracles();
        let db_path = data_dir.join("dregg.redb");
        let store = Arc::new(
            match poa_compact_trust {
                Some(policy) => PersistentStore::open_with_poa_compact_trust_v1(&db_path, policy),
                None => PersistentStore::open(&db_path),
            }
            .map_err(|e| format!("failed to open store: {e}"))?,
        );
        // Boot crash-recovery: a torn/poisoned commit-log tail (e.g. a process
        // killed between the input-turn config write and the commit-record txn, or
        // an unclean power-cycle) leaves the log's head inconsistent with its
        // durably-recorded finalized root, so the convergence check below would
        // REFUSE the whole image and strand the node (observed 2026-06-29 after a
        // homelab PSU swap). Truncate any divergent tail to the last commit ordinal
        // whose reconstructed root matches; peers backfill the dropped turn(s) via
        // normal blocklace sync. See `run_boot_torn_tail_recovery` for the one case
        // the walk cannot adjudicate (no checkpoint => empty base => the recorded
        // full-ledger root is unreproducible) and what still fails closed.
        run_boot_torn_tail_recovery(&store)?;

        // Resolve key file path: absolute paths are used as-is,
        // relative paths are resolved from the data directory.
        let key_path = if std::path::Path::new(key_file).is_absolute() {
            std::path::PathBuf::from(key_file)
        } else {
            data_dir.join(key_file)
        };

        let mut cclerk = if key_path.exists() {
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

        // Restore the forever-digest registries (.docs-history-noclaude/PERSISTENCE.md): the
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
                for op in overlay {
                    apply_overlay_op(&mut ledger, op);
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

        // Restore the durable receipt chain into the cipherclerk and arm its
        // durability sink, so the served `/api/receipts*` chain + the receipt-index
        // MMR head survive this restart instead of rebuilding empty.
        install_receipt_chain_durability(&store, &mut cclerk)?;

        let (events_tx, _) = broadcast::channel(4096);

        // Derive the silo ID from the cipherclerk's public key.
        let silo_id: SiloId = *blake3::hash(cclerk.public_key().as_bytes()).as_bytes();

        // Restore node-held channel rooms from the durable roster table
        // (.docs-history-noclaude/PERSISTENCE.md §3, the roster caveat): each stored roster is
        // RE-COMMITTED against the recovered ledger's on-cell membership root;
        // a stale durable roster is discarded (and durably removed). This is
        // built against the just-recovered `ledger`, before it moves into the
        // state.
        let mut channels = crate::channels_service::ChannelRegistry::default();
        channels.restore_rosters(&store, &ledger);

        // The positional note tree is live consensus state, not a disposable
        // cache.  Rebuild both its legacy scalar view and faithful sixteen-lane
        // authority from the exact durable leaf order before serving.  Starting
        // empty after a restart would make the next finalized history edge name
        // the wrong predecessor even though redb held every note.
        let note_tree = restore_and_verify_faithful_note_tree(&store, &cclerk)?;

        // Caller-deployed custom programs are verifier configuration, not
        // process-local cache. Revalidate the canonical durable snapshot before
        // serving; corrupt/invalid bytes fail the boot instead of silently
        // making custom-program cells unverifiable after a restart.
        let program_registry = crate::program_registry_persistence::load_program_registry(&store)?;

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

        // Restore the node-hosted realm substrate from the durable REALM_LOG
        // (realm-model graduated into the node): replay the log through a fresh
        // RealmWorld so a realm/instance/identity created through the node — and
        // its receipt-chain head — survive this restart. Fail-closed on a corrupt
        // log (a node must not serve a realm head it cannot recover durably).
        let realms = crate::realm_service::NodeRealms::restore(Arc::clone(&store))?;

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                cclerk,
                ledger,
                store,
                faithful_mirror_cache: Mutex::new(FaithfulMirrorSnapshotCache::default()),
                peers,
                unlocked: false,
                passphrase_hash,
                bearer_seed,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                faucet_reserved_nonce: None,
                pending_conditionals: Vec::new(),
                used_proof_hashes,
                known_federation_keys: Vec::new(),
                known_federation_ml_dsa_keys: Vec::new(),
                known_federations: dregg_federation::KnownFederations::new(),
                federation_configured: false,
                federation_id: [0u8; 32],
                committee_epoch: 0,
                derived_committee_history: Vec::new(),
                derived_committee_ml_dsa_history: Vec::new(),
                derived_committee_version_at_block: std::collections::HashMap::new(),
                boot_constitution: None,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: dregg_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                full_turn_proving_enabled: false,
                lean_producer_enabled: lean_producer_effective(
                    lean_producer_env_enabled(),
                    dregg_lean_ffi::lean_available(),
                ),
                fee_well: None,
                coordination_fee_exempt: false,
                issuer_wells: Vec::new(),
                mcp_cap_enforce: mcp_cap_enforce_env_enabled(),
                pir_index_cache: None,
                discharge_gateway: None,
                program_registry,
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
                note_tree,
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
            realms: Arc::new(RwLock::new(realms)),
            dark_clearing: Arc::new(RwLock::new(
                crate::dark_clearing_service::NodeDarkClearing::new(),
            )),
        })
    }

    /// Create a NodeState with a pre-existing cipherclerk (restored from key material).
    pub fn with_cclerk(
        data_dir: &Path,
        peers: Vec<String>,
        key_bytes: [u8; 32],
    ) -> Result<Self, String> {
        let db_path = data_dir.join("dregg.redb");
        let store = Arc::new(
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?,
        );
        // Boot crash-recovery: a torn/poisoned commit-log tail (e.g. a process
        // killed between the input-turn config write and the commit-record txn, or
        // an unclean power-cycle) leaves the log's head inconsistent with its
        // durably-recorded finalized root, so the convergence check below would
        // REFUSE the whole image and strand the node (observed 2026-06-29 after a
        // homelab PSU swap). Truncate any divergent tail to the last commit ordinal
        // whose reconstructed root matches; peers backfill the dropped turn(s) via
        // normal blocklace sync. See `run_boot_torn_tail_recovery` for the one case
        // the walk cannot adjudicate (no checkpoint => empty base => the recorded
        // full-ledger root is unreproducible) and what still fails closed.
        run_boot_torn_tail_recovery(&store)?;

        let mut cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key_bytes));
        // Restore the durable receipt chain into the cipherclerk and arm its
        // durability sink (see `install_receipt_chain_durability`): the served
        // `/api/receipts*` chain + MMR head survive this restart.
        install_receipt_chain_durability(&store, &mut cclerk)?;
        let (witnessed_receipts, witnessed_receipt_order) = load_witnessed_receipts(&store);

        // Restore the forever-digest registries (.docs-history-noclaude/PERSISTENCE.md): the
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
            for op in overlay {
                // Last-writer-wins point update (`CrashRecovery.applyWrites` over
                // the `Write = insert | remove` alphabet): an Upsert overwrites
                // (a strict `insert_cell` would silently drop a post-checkpoint
                // write to an already-checkpointed cell); a Remove DELETES (a
                // dropped removal would resurrect the cell as hosted). See
                // `new_with_key_file` / `apply_overlay_op`.
                apply_overlay_op(&mut ledger, op);
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
        // (.docs-history-noclaude/PERSISTENCE.md §3), re-committed against the recovered ledger.
        let mut channels = crate::channels_service::ChannelRegistry::default();
        channels.restore_rosters(&store, &ledger);

        let note_tree = restore_and_verify_faithful_note_tree(&store, &cclerk)?;
        let program_registry = crate::program_registry_persistence::load_program_registry(&store)?;

        // Restore the node-hosted realm substrate from the durable REALM_LOG (see
        // `new_with_key_file`): realm/instance/identity + the realm receipt-chain
        // head survive this restart. Fail-closed on a corrupt durable log.
        let realms = crate::realm_service::NodeRealms::restore(Arc::clone(&store))?;

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                cclerk,
                ledger,
                store,
                faithful_mirror_cache: Mutex::new(FaithfulMirrorSnapshotCache::default()),
                peers,
                unlocked: false,
                passphrase_hash: None,
                bearer_seed: None,
                intent_pool: HashMap::new(),
                consensus_queue: Vec::new(),
                faucet_reserved_nonce: None,
                pending_conditionals: Vec::new(),
                used_proof_hashes: HashSet::new(),
                known_federation_keys: Vec::new(),
                known_federation_ml_dsa_keys: Vec::new(),
                known_federations: dregg_federation::KnownFederations::new(),
                federation_configured: false,
                federation_id: [0u8; 32],
                committee_epoch: 0,
                derived_committee_history: Vec::new(),
                derived_committee_ml_dsa_history: Vec::new(),
                derived_committee_version_at_block: std::collections::HashMap::new(),
                boot_constitution: None,
                max_root_age_secs: 3600,
                threshold_key_share: None,
                decryption_threshold: 0,
                pending_decryption_shares: HashMap::new(),
                routing_table: RoutingTable::new(),
                pruning_enabled: false,
                checkpoint_interval: dregg_federation::DEFAULT_CHECKPOINT_INTERVAL,
                prove_transitions: false,
                full_turn_proving_enabled: false,
                lean_producer_enabled: lean_producer_effective(
                    lean_producer_env_enabled(),
                    dregg_lean_ffi::lean_available(),
                ),
                fee_well: None,
                coordination_fee_exempt: false,
                issuer_wells: Vec::new(),
                mcp_cap_enforce: mcp_cap_enforce_env_enabled(),
                pir_index_cache: None,
                discharge_gateway: None,
                program_registry,
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
                note_tree,
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
            realms: Arc::new(RwLock::new(realms)),
            dark_clearing: Arc::new(RwLock::new(
                crate::dark_clearing_service::NodeDarkClearing::new(),
            )),
        })
    }

    /// Read-only handle to the node-hosted realm substrate (`realm-model`
    /// graduated into the node). Realm/instance turns admitted through this route
    /// via realm-model's gate and are durable across a restart.
    pub fn realms(&self) -> Arc<RwLock<crate::realm_service::NodeRealms>> {
        Arc::clone(&self.realms)
    }

    /// Handle to the node-hosted encrypted call auction
    /// ([`crate::dark_clearing_service`]). Every accept through it leaves a receipt, and it
    /// refuses fail-closed when the committee, the verified core, or the certificate is
    /// unavailable.
    pub fn dark_clearing(&self) -> Arc<RwLock<crate::dark_clearing_service::NodeDarkClearing>> {
        Arc::clone(&self.dark_clearing)
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

    // (`recovery_read_error_is_fatal` is a free fn below the impl.)

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
                // A READ FAILURE of the recorded root is NOT the same as its
                // absence (finding F3). On a node that has committed at least one
                // finalized turn (a NON-ZERO commit cursor) the recorded root is
                // the strongest boot integrity gate; a present-but-unreadable
                // (corrupt) row must FAIL CLOSED rather than silently disable the
                // gate on a node that has real finalized state to protect. Only a
                // genuinely fresh / zero-cursor node (no finalized state, nothing
                // to converge to) may continue on a read error.
                if recovery_read_error_is_fatal(s.store.commit_cursor()) {
                    tracing::error!(
                        error = %e,
                        "recorded finalized-root row is UNREADABLE at a non-zero commit cursor \
                         — refusing to start (STORE INTEGRITY EVENT)"
                    );
                    return Err(format!(
                        "recovery convergence: the recorded finalized-root row is unreadable at a \
                         non-zero commit cursor — refusing to serve a store whose strongest boot \
                         integrity gate is corrupt (STORE INTEGRITY EVENT): {e}"
                    ));
                }
                tracing::warn!(
                    error = %e,
                    "could not read recorded finalized root at a zero/fresh commit cursor \
                     (no finalized state to converge to) — continuing"
                );
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
            // ── NODE-1 (signed anchor) + NODE-2 (anti-rollback) ──────────────
            // The check above is crash-consistency: it binds the recovered ledger to a
            // SELF-STORED root in the SAME redb, which an offline attacker with write
            // access can tamper alongside the ledger. Anchor it instead to the
            // federation's QUORUM-SIGNED finalization — which an attacker cannot forge
            // (no committee keys) — and refuse a store rolled back below a witnessed
            // finalized height.
            Self::verify_signed_anchor_and_rollback(&s, recovered_root)
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

    /// NODE-1 (signed anchor) + NODE-2 (anti-rollback). Called only AFTER the
    /// crash-consistency convergence above passes. Anchors the recovered ledger to
    /// the federation's QUORUM-SIGNED finalization (which an offline attacker cannot
    /// forge — they hold no committee keys) and enforces a monotonic anti-rollback
    /// floor so a node refuses to boot on an older internally-consistent snapshot.
    ///
    /// ⚑ COMMITTEE-SPECIFIC (2026-08-08): each attested root is verified against
    /// exactly ONE committee — the version that was current at its anchored
    /// block ([`anchor_committee_for_root`]) — never "any committee we have
    /// ever known". The old any-candidate scan let a member rotated out at
    /// version `v` (an evicted equivocator above all) quorum-sign a fabricated
    /// root at any later height and anchor a restart with keys the chain had
    /// already withdrawn. The same pass removed three unjustified skip doors:
    /// a `threshold_qc` root (nothing in this codebase produces one — its
    /// presence is a tamper/corruption claim and REFUSES), a foreign
    /// `federation_id` on the latest root (a store from another federation
    /// refuses to anchor this one — re-genesis instead of a silently
    /// unanchored boot), and an unreadable attested-root row on a node with
    /// finalized state (fail closed, mirroring the F3 recorded-root rule).
    ///
    /// Returns `Err` (refuse to start) on: a same-epoch attested root whose committee
    /// quorum signature does NOT verify (a forged/unsigned finalization); a recovered
    /// head whose canonical root contradicts the committee-signed root at the attested
    /// height; or a recovered head BELOW a witnessed finalized height (rollback).
    ///
    /// Fail-SAFE where no signed anchor exists: a fresh/young chain (no attested root)
    /// or a node with no committee keys loaded (solo / pre-federation) falls through
    /// to the best-effort high-water mark and does not refuse on that basis.
    fn verify_signed_anchor_and_rollback(
        s: &NodeStateInner,
        recovered_root: [u8; 32],
    ) -> Result<(), String> {
        let head_height = s.store.recovered_head_height().ok().flatten().unwrap_or(0);

        // The UNFORGEABLE floor: the height of the latest VALIDLY-SIGNED attested root.
        let mut signed_floor: u64 = 0;
        match s.store.latest_attested_root() {
            Ok(Some(signed)) => {
                // Resolve the ONE committee entitled to have signed this root
                // (the version current at its anchored block). `Err` means no
                // committee can vouch for it — a root that nonetheless CLAIMS
                // a quorum is treated as forged below.
                let resolved = anchor_committee_for_root(s, &signed);
                if signed.threshold_qc.is_some() {
                    // ⚑ Nothing in this codebase produces a threshold-QC
                    // attested root (`threshold_qc: Some` appears in no
                    // production constructor). Its presence on the LATEST root
                    // is a corruption/tamper claim whose acceptance used to
                    // DISABLE the anchor for the whole boot — the exact
                    // "unverifiable ⇒ unenforced" door an offline attacker
                    // wants. Refuse.
                    tracing::error!(
                        height = signed.height,
                        "the latest stored attested root claims a BLS threshold QC, which no \
                         production path emits — STORE INTEGRITY EVENT (NODE-1), refusing to start"
                    );
                    return Err(format!(
                        "recovery anchor failed: the latest stored attested root at height {} \
                         claims a BLS threshold QC that this node cannot verify and no production \
                         path produces — refusing to boot with the signed anchor disabled (NODE-1)",
                        signed.height
                    ));
                } else if signed.federation_id.0 != s.federation_id {
                    // ⚑ A store whose LATEST finalization belongs to another
                    // federation is not this federation's store. Skipping the
                    // anchor here (the old behavior) let one flipped, unsigned
                    // byte disable NODE-1 for the whole boot. Refuse loudly:
                    // the honest remedy is a re-genesis, not an unanchored boot.
                    tracing::error!(
                        height = signed.height,
                        stored = %dregg_types::hex_encode(&signed.federation_id.0),
                        ours = %dregg_types::hex_encode(&s.federation_id),
                        "the latest stored attested root belongs to a DIFFERENT federation — \
                         refusing to boot this store under this federation (NODE-1); re-genesis \
                         the data dir if the federation really changed"
                    );
                    return Err(format!(
                        "recovery anchor failed: the latest stored attested root at height {} was \
                         finalized under a different federation id — this store does not belong \
                         to this federation; re-genesis instead of booting unanchored (NODE-1)",
                        signed.height
                    ));
                } else if matches!(&resolved, Ok((c, _)) if c.is_empty()) {
                    tracing::warn!(
                        height = signed.height,
                        "recovery signed-anchor SKIPPED: no committee keys loaded — cannot verify \
                         the attested-root quorum signature (NODE-1); using the best-effort \
                         high-water mark only"
                    );
                } else if matches!(&resolved, Ok((c, pq)) if signed.verify_signatures(c)
                    || signed.verify_finalization_quorum(c, pq))
                {
                    // A genuine committee quorum over this root: EITHER the
                    // light-client attestation (`verify_signatures`, the local
                    // node's sig over the full preimage — solo / threshold-1) OR
                    // the assembled committee finalization-vote quorum
                    // (`verify_finalization_quorum`, the N3 restart anchor for a
                    // full-mode node). Its `merkle_root` IS the canonical ledger
                    // root at finalization; an offline attacker cannot forge it.
                    signed_floor = signed.height;
                    // Binding: if the recovered head IS the attested height, its canonical
                    // root MUST equal the SIGNED merkle_root. A ledger tampered to a state
                    // the federation never signed fails here.
                    if head_height == signed.height && recovered_root != signed.merkle_root {
                        tracing::error!(
                            height = signed.height,
                            recovered = %dregg_types::hex_encode(&recovered_root),
                            signed = %dregg_types::hex_encode(&signed.merkle_root),
                            "recovered ledger root does NOT match the FEDERATION-SIGNED attested \
                             root at the head height — STORE INTEGRITY EVENT (NODE-1), refusing"
                        );
                        return Err(format!(
                            "recovery anchor failed: recovered ledger root {} != the \
                             committee-signed attested root {} at height {} — refusing to serve a \
                             ledger the federation never signed (NODE-1)",
                            dregg_types::hex_encode(&recovered_root),
                            dregg_types::hex_encode(&signed.merkle_root),
                            signed.height
                        ));
                    }
                } else if signed.quorum_signatures.len() >= signed.threshold
                    || signed.has_finalization_quorum()
                {
                    // The root CLAIMS a quorum (enough signatures / a non-empty
                    // finalization quorum) but it does NOT verify against the
                    // one committee entitled to have signed it — a forged or
                    // wrong-committee attestation (including a quorum from a
                    // committee version the chain had already rotated out, and
                    // a root whose anchored block resolves to no known
                    // version). Refuse.
                    let why = match &resolved {
                        Ok(_) => "does not verify against the committee current at its anchored \
                                  block"
                            .to_string(),
                        Err(e) => format!("cannot be attributed to any committee version: {e}"),
                    };
                    tracing::error!(
                        height = signed.height,
                        why = %why,
                        "the latest stored attested root CLAIMS a committee quorum that does NOT \
                         verify — STORE INTEGRITY EVENT (NODE-1), refusing to start"
                    );
                    return Err(format!(
                        "recovery anchor failed: the latest stored attested root at height {} \
                         claims a committee quorum that {} — refusing to trust a forged \
                         finalization (NODE-1)",
                        signed.height, why
                    ));
                } else {
                    // A TRAILING full-mode head: persisted synchronously with only
                    // the local node's single signature (`1 < threshold`), its
                    // cross-node finalization-vote quorum not yet assembled (the
                    // votes converge a gossip round or two after the head — the
                    // deliberate liveness cost of Fix B). This is NOT forgery — it
                    // makes no quorum CLAIM. Anchor instead to the highest LOWER
                    // root that DOES carry a valid quorum; the unaggregated head is
                    // replayable tail (the executed set is recovered separately).
                    //
                    // Tamper-check preserved: even without a quorum, the head
                    // carries the local node's OWN signature binding its
                    // merkle_root. A ledger recovered to a root that does NOT match
                    // that self-signed root at the head height is refused — the
                    // integrity guarantee the lone signature provides is kept.
                    if head_height == signed.height
                        && recovered_root != signed.merkle_root
                        && matches!(&resolved, Ok((c, pq))
                            if signed.has_any_valid_committee_signature(c, pq))
                    {
                        tracing::error!(
                            height = signed.height,
                            recovered = %dregg_types::hex_encode(&recovered_root),
                            signed = %dregg_types::hex_encode(&signed.merkle_root),
                            "recovered ledger root does NOT match the SELF-SIGNED attested root at \
                             the head height — STORE INTEGRITY EVENT (NODE-1), refusing"
                        );
                        return Err(format!(
                            "recovery anchor failed: recovered ledger root {} != the self-signed \
                             attested root {} at height {} — refusing to serve a tampered ledger \
                             (NODE-1)",
                            dregg_types::hex_encode(&recovered_root),
                            dregg_types::hex_encode(&signed.merkle_root),
                            signed.height
                        ));
                    }
                    let mut best: u64 = 0;
                    if let Ok(roots) = s.store.all_attested_roots() {
                        for r in &roots {
                            // Each lower root is verified against the ONE
                            // committee version current at ITS anchored block
                            // (never any-candidate): the anchor a restart
                            // falls back to must clear the same bar as the
                            // head it replaces.
                            if r.height < signed.height
                                && r.federation_id.0 == s.federation_id
                                && r.threshold_qc.is_none()
                                && matches!(anchor_committee_for_root(s, r), Ok((c, pq))
                                    if !c.is_empty()
                                        && (r.verify_signatures(c)
                                            || r.verify_finalization_quorum(c, pq)))
                                && r.height > best
                            {
                                best = r.height;
                            }
                        }
                    }
                    signed_floor = best;
                    tracing::warn!(
                        head = signed.height,
                        anchored = signed_floor,
                        "recovery signed-anchor: the latest attested root has no assembled \
                         committee quorum yet (trailing head) — anchored to the last \
                         quorum-signed height; the unaggregated tail is replayed (NODE-1)"
                    );
                }
            }
            Ok(None) => {
                // No attestation yet (a young chain) — nothing to anchor; the best-effort
                // high-water mark below still applies.
            }
            Err(e) => {
                // Same rule as the recorded-root read (finding F3): on a node
                // WITH finalized state, an unreadable attested-root row is a
                // corrupt strongest-gate and FAILS CLOSED — a read error must
                // not silently disable the anchor. Only a genuinely fresh
                // node (zero commit cursor) may continue.
                if recovery_read_error_is_fatal(s.store.commit_cursor()) {
                    tracing::error!(
                        error = %e,
                        "latest attested root is UNREADABLE at a non-zero commit cursor — \
                         refusing to start with the signed anchor disabled (NODE-1)"
                    );
                    return Err(format!(
                        "recovery anchor failed: the latest attested root is unreadable at a \
                         non-zero commit cursor — refusing to boot with the signed anchor \
                         silently disabled (NODE-1): {e}"
                    ));
                }
                tracing::warn!(error = %e, "could not read latest attested root for recovery anchor (fresh node — continuing)");
            }
        }

        // NODE-2 anti-rollback: the recovered head must not be BELOW a previously
        // witnessed finalized height. The floor is the max of the just-verified signed
        // height (the unforgeable part) and a persisted monotonic high-water mark (a
        // best-effort backstop within the attestation window — it shares the redb's
        // tamperability, so it is not the primary anchor).
        const HWM_KEY: &str = "recovery_finalized_high_water";
        let persisted_hwm: u64 = s
            .store
            .get_config(HWM_KEY)
            .ok()
            .flatten()
            .and_then(|b| <[u8; 8]>::try_from(b.as_slice()).ok())
            .map(u64::from_le_bytes)
            .unwrap_or(0);
        let floor = signed_floor.max(persisted_hwm);
        if head_height < floor {
            tracing::error!(
                head_height,
                floor,
                signed_floor,
                persisted_hwm,
                "recovered head height is BELOW a witnessed finalized height — ANTI-ROLLBACK \
                 violation (NODE-2), refusing to start"
            );
            return Err(format!(
                "recovery anti-rollback failed: recovered head height {head_height} is below the \
                 witnessed finalized floor {floor} (signed={signed_floor}, watermark={persisted_hwm}) \
                 — refusing to revert finalized state / resurrect spent nullifiers (NODE-2)"
            ));
        }
        // Advance the monotonic high-water mark (never decreases).
        let new_hwm = floor.max(head_height);
        if new_hwm > persisted_hwm {
            if let Err(e) = s.store.set_config(HWM_KEY, &new_hwm.to_le_bytes()) {
                tracing::warn!(error = %e, "failed to persist recovery high-water mark (NODE-2)");
            }
        }
        tracing::info!(
            head_height,
            signed_floor,
            high_water = new_hwm,
            "recovery signed-anchor + anti-rollback verified (NODE-1/NODE-2)"
        );
        Ok(())
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
                // A WARNING IS CORRECT HERE, and only became correct on 2026-08-05.
                // `post_discharge` now persists each burn BEFORE it answers and
                // REFUSES (503) if that write fails, so by the time we reach
                // shutdown every issued and every denied ticket is already durable
                // and this write is genuinely the redundant checkpoint the doc
                // comment above claims. Until then it was the only durable write
                // on some paths, and losing it lost replay prevention outright.
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
    /// `receipt_hash()` leaf of every chain entry not yet indexed, then refresh
    /// the durable head anchor (finding F5). Runs lazily off the read path (the
    /// query handlers call this before serving) and is purely additive over the
    /// already-committed, append-only chain, so it can never affect commit
    /// soundness. When nothing is new it EARLY-RETURNS in `O(1)`; the head-anchor
    /// refresh (an `O(len)` root recompute + one durable write) fires only when
    /// the index actually GREW — the same growth that a serving query already
    /// pays a root recompute for — so it is bounded by receipt-arrival rate, not
    /// query rate.
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
        self.refresh_receipt_index_head_anchor();
    }

    /// Refresh the durable receipt-index HEAD anchor `{ len, root }` (finding F5)
    /// and, on the FIRST sync after a restart (the served length still equals the
    /// recorded anchor length), verify the recovered chain still reproduces the
    /// head served before the restart. The receipt index is ADDITIVE and never
    /// commit-gating, so a divergence is a LOUD detection/alert (not a panic);
    /// the anchor then advances forward. A persist failure is best-effort — the
    /// anchor is a rebuildable cache and boot rebuilds it from the chain.
    fn refresh_receipt_index_head_anchor(&self) {
        let len = self.receipt_index.len();
        let root = self.receipt_index.root();
        match self.store.load_receipt_index_head() {
            Ok(Some((anchor_len, anchor_root))) if anchor_len == len && anchor_root != root => {
                tracing::error!(
                    len,
                    "receipt-index head MISMATCH on recovery — the served non-omission root \
                     diverged from the durable anchor: the recovered receipt chain no longer \
                     reproduces the head served before restart (STORE INTEGRITY EVENT)"
                );
            }
            Ok(Some((anchor_len, _))) if anchor_len > len => {
                tracing::error!(
                    anchor_len,
                    len,
                    "durable receipt-index anchor is AHEAD of the recovered chain — possible \
                     receipt-log rollback (STORE INTEGRITY EVENT)"
                );
            }
            Ok(_) => {}
            Err(e) => {
                tracing::warn!(error = %e, "could not read receipt-index head anchor for recovery check");
            }
        }
        if let Err(e) = self.store.persist_receipt_index_head(len, &root) {
            tracing::warn!(
                error = %e,
                "failed to persist receipt-index head anchor (rebuildable cache; boot rebuilds it)"
            );
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
        // No ML-DSA committee supplied on this legacy path: hybrid stays
        // unconfigured (fail-closed — the vote collector then counts no votes),
        // and any PREVIOUS ML-DSA vec is dropped so it can never be read
        // misaligned against the new committee.
        self.set_federation_keys_hybrid(keys, Vec::new());
    }

    /// HYBRID-PQ variant of [`Self::set_federation_keys`]: load the committee's
    /// ed25519 keys AND the INDEX-ALIGNED ML-DSA-65 keys genesis published next
    /// to them (element `i` of each vec is the same member).
    ///
    /// `ml_dsa_keys` may be empty ("hybrid not configured" — fail-closed: the
    /// finalization-vote collector will hold no PQ keys and form no quorum). A
    /// NON-empty vec whose length differs from `keys` is a corrupt/misaligned
    /// genesis: it is REJECTED (treated as empty, loudly) rather than risking
    /// attributing member i's ML-DSA key to member j.
    pub fn set_federation_keys_hybrid(
        &mut self,
        keys: Vec<dregg_types::PublicKey>,
        ml_dsa_keys: Vec<dregg_federation::frost::MlDsaPublicKey>,
    ) {
        if keys.is_empty() {
            tracing::warn!(
                "set_federation_keys called with empty key set — remaining in discovery mode"
            );
            return;
        }
        let ml_dsa_keys = if !ml_dsa_keys.is_empty() && ml_dsa_keys.len() != keys.len() {
            tracing::error!(
                ed25519_keys = keys.len(),
                ml_dsa_keys = ml_dsa_keys.len(),
                "ML-DSA committee key count does not match the ed25519 committee — \
                 REJECTING the ML-DSA set (hybrid votes will not verify; fail-closed) \
                 rather than misaligning member identities"
            );
            Vec::new()
        } else {
            ml_dsa_keys
        };
        // COUPLED-CORE: the committee identity is the HYBRID id — a commitment to
        // both the Ed25519 and the ML-DSA-65 key per member — so this runtime
        // re-derivation matches what genesis wrote. `ml_dsa_keys` is aligned
        // index-for-index with `keys`; `derive_federation_id_hybrid_with_epoch`
        // sorts the resulting member ids internally, so the pre-sort pairing here
        // yields the same id genesis / the sorted Federation compute. An empty
        // (unconfigured) ML-DSA set falls back to the legacy Ed25519-only id.
        let id = dregg_federation::derive_federation_id_hybrid_with_epoch(
            &keys,
            &ml_dsa_keys,
            self.committee_epoch,
        );
        tracing::info!(
            key_count = keys.len(),
            committee_epoch = self.committee_epoch,
            federation_id = %dregg_types::hex_encode(&id),
            "federation keys loaded — exiting discovery mode; federation_id derived (hybrid)",
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
        let mut fed = dregg_federation::Federation::from_committee(
            keys.clone(),
            self.committee_epoch,
            threshold,
            None,
            local_seat,
        );
        // COUPLED-CORE: attach the ML-DSA roster PERMUTED to the sorted committee
        // (`Federation::from_committee` sorts members by ed25519 bytes) so the
        // roster stays aligned index-for-index and the Federation's cached id is
        // the same HYBRID id as `id` above. Without a configured roster the
        // Federation keeps its legacy Ed25519 id.
        if !ml_dsa_keys.is_empty() && ml_dsa_keys.len() == keys.len() {
            let mut pairs: Vec<(
                dregg_types::PublicKey,
                dregg_federation::frost::MlDsaPublicKey,
            )> = keys
                .iter()
                .cloned()
                .zip(ml_dsa_keys.iter().cloned())
                .collect();
            pairs.sort_by_key(|(ed, _)| ed.0);
            let sorted_ml_dsa: Vec<dregg_federation::frost::MlDsaPublicKey> =
                pairs.into_iter().map(|(_, ml)| ml).collect();
            fed = fed.with_ml_dsa_members(sorted_ml_dsa);
        }
        self.known_federations.register(std::sync::Arc::new(fed));
        self.known_federation_keys = keys;
        self.known_federation_ml_dsa_keys = ml_dsa_keys;
        self.federation_id = id;
        self.federation_configured = true;
    }

    /// HYBRID-PQ lookup: the ML-DSA-65 key of the committee member whose
    /// ed25519 key is `ed25519`, via the index alignment of
    /// [`Self::known_federation_keys`] / [`Self::known_federation_ml_dsa_keys`].
    /// `None` when the member is unknown OR hybrid is not configured — the
    /// caller must treat that as "this member's votes cannot count" (fail-closed).
    pub fn ml_dsa_key_for(
        &self,
        ed25519: &[u8; 32],
    ) -> Option<&dregg_federation::frost::MlDsaPublicKey> {
        let idx = self
            .known_federation_keys
            .iter()
            .position(|k| k.0 == *ed25519)?;
        self.known_federation_ml_dsa_keys.get(idx)
    }

    /// Learn a LIVE-JOINED committee member's `(ed25519, ML-DSA-65)` pair, so
    /// [`Self::ml_dsa_key_for`] resolves for a validator that was not in genesis.
    ///
    /// ⚑ WITHOUT THIS A SUCCESSFUL JOIN HALTS THE FEDERATION. The genesis roster
    /// is the only writer of the index-aligned key pair, so an admitted
    /// non-genesis member had no committed ML-DSA half. `blocklace_sync::
    /// project_committed_participants` DROPS such a member, and
    /// `poll_finalized_blocks` then FAILS CLOSED (correctly — ordering over a
    /// subset would fork) and finalizes NOTHING, on every node, forever. The
    /// deadlock this repairs is therefore not only "the join never arrives" but
    /// "and if it had, the chain would stop".
    ///
    /// The source of truth is the RATIFIED `MembershipAction::Join` payload,
    /// which every node sees identically at the same point in the order — the
    /// only thing that makes this deterministic rather than a node-local key
    /// view (which would fork). Never call it from an unratified path.
    ///
    /// Idempotent. A pair already present is left alone; a DIFFERENT ML-DSA key
    /// for a known ed25519 is REFUSED (returns `false`) rather than overwritten:
    /// silently rebinding a member's PQ half would change its hybrid id and its
    /// tau slot underneath a running committee.
    ///
    /// `federation_id` / `committee_epoch` are deliberately untouched — a
    /// committee change never re-points the stable chain root.
    pub fn learn_committee_member_hybrid_key(
        &mut self,
        ed25519: &[u8; 32],
        ml_dsa: dregg_federation::frost::MlDsaPublicKey,
    ) -> bool {
        // Hybrid must be CONFIGURED for the alignment to mean anything: with an
        // empty ML-DSA vector the indices do not correspond and appending would
        // manufacture a bogus alignment.
        if self.known_federation_ml_dsa_keys.len() != self.known_federation_keys.len() {
            return false;
        }
        if let Some(idx) = self
            .known_federation_keys
            .iter()
            .position(|k| k.0 == *ed25519)
        {
            return self
                .known_federation_ml_dsa_keys
                .get(idx)
                .is_some_and(|existing| *existing == ml_dsa);
        }
        self.known_federation_keys
            .push(dregg_types::PublicKey(*ed25519));
        self.known_federation_ml_dsa_keys.push(ml_dsa);
        true
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

    fn load_authenticated_faithful_history(
        &self,
        expectation: dregg_persist::FaithfulNoteRootExpectationV1,
    ) -> Result<dregg_persist::FaithfulNoteRootHistoryV1, FaithfulMirrorError> {
        let seed = self.cclerk.gossip_signing_key().to_bytes();
        let local_ed = self.cclerk.public_key();
        let (local_pq, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
        self.store
            .load_faithful_note_root_history_hybrid(
                std::slice::from_ref(&local_ed),
                std::slice::from_ref(&local_pq),
                1,
                expectation,
            )
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))
    }

    fn faithful_mirror_snapshot_key(
        &self,
    ) -> Result<FaithfulMirrorSnapshotKey, FaithfulMirrorError> {
        let expectation = self
            .store
            .faithful_note_root_expectation()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?
            .ok_or(FaithfulMirrorError::NoAuthenticatedHead)?;
        let segment_head = self
            .store
            .faithful_note_root_head()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?
            .ok_or(FaithfulMirrorError::NoAuthenticatedHead)?;
        let latest_attested_root = self
            .store
            .latest_attested_root()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?
            .ok_or(FaithfulMirrorError::NoAuthenticatedHead)?;
        let nullifier_count = self
            .store
            .faithful_nullifier_record_count()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?;

        if segment_head.height != expectation.height
            || segment_head.note_count != expectation.note_count
            || segment_head.root != expectation.root
            || latest_attested_root.height != expectation.height
            || latest_attested_root.note_tree_root != Some(expectation.root.to_bytes())
            || latest_attested_root.nullifier_set_root.is_none()
            || latest_attested_root.federation_id.0 != segment_head.federation_id
        {
            return Err(FaithfulMirrorError::InconsistentHead(
                "history seal, segment head, and latest faithful attestation do not share exact coordinates"
                    .to_string(),
            ));
        }
        Ok(FaithfulMirrorSnapshotKey {
            expectation,
            segment_head,
            latest_attested_root,
            nullifier_count,
        })
    }

    fn validate_live_faithful_mirror_head(
        &self,
        key: &FaithfulMirrorSnapshotKey,
    ) -> Result<(), FaithfulMirrorError> {
        const FAITHFUL_NOTE_DEPTH: usize = 16;
        if self.note_tree.depth() != FAITHFUL_NOTE_DEPTH {
            return Err(FaithfulMirrorError::InconsistentHead(format!(
                "live note-tree depth {} != required {FAITHFUL_NOTE_DEPTH}",
                self.note_tree.depth()
            )));
        }
        let durable_count = self
            .store
            .note_count()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?;
        let live_count = u64::try_from(self.note_tree.size()).map_err(|_| {
            FaithfulMirrorError::InconsistentHead("live note count does not fit u64".to_string())
        })?;
        let live_root = dregg_persist::CanonicalFaithfulRoot::from_faithful(
            self.note_tree.faithful_root_immutable(),
        );
        if durable_count != key.expectation.note_count
            || live_count != key.expectation.note_count
            || live_root != key.expectation.root
        {
            return Err(FaithfulMirrorError::InconsistentHead(
                "durable note count, live tree, and authenticated faithful head disagree"
                    .to_string(),
            ));
        }
        Ok(())
    }

    fn build_faithful_mirror_snapshot(
        &self,
        key: &FaithfulMirrorSnapshotKey,
    ) -> Result<FaithfulMirrorSnapshot, FaithfulMirrorError> {
        let history = self.load_authenticated_faithful_history(key.expectation)?;
        let anchor = history.anchor().clone();
        if anchor.session_id != key.segment_head.session_id
            || anchor.federation_id != key.segment_head.federation_id
            || anchor.committee_epoch != key.segment_head.committee_epoch
        {
            return Err(FaithfulMirrorError::InconsistentHead(
                "authenticated history segment identity changed under its sealed head".to_string(),
            ));
        }
        let commitments: Vec<[u8; 32]> = self
            .store
            .load_all_note_commitments()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?
            .into_iter()
            .map(|commitment| commitment.0)
            .collect();
        let durable_count = u64::try_from(commitments.len()).map_err(|_| {
            FaithfulMirrorError::InconsistentHead("durable note count does not fit u64".to_string())
        })?;
        let history_count = u64::try_from(history.envelopes().len()).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "authenticated history count does not fit u64".to_string(),
            )
        })?;
        let durable_tree = dregg_persist::Poseidon2NoteTree::from_blake3_commitments(
            &commitments,
            self.note_tree.depth(),
        );
        let durable_root = dregg_persist::CanonicalFaithfulRoot::from_faithful(
            durable_tree.faithful_root_immutable(),
        );
        if durable_count != key.expectation.note_count
            || history_count != key.expectation.records
            || durable_root != key.expectation.root
        {
            return Err(FaithfulMirrorError::InconsistentHead(
                "durable commitment bytes/root or authenticated history length disagree with the exact sealed head"
                    .to_string(),
            ));
        }

        let durable_nullifiers = self
            .store
            .load_faithful_nullifier_records()
            .map_err(|error| FaithfulMirrorError::DurableState(error.to_string()))?;
        let decoded_nullifier_count = u64::try_from(durable_nullifiers.len()).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "durable nullifier count does not fit u64".to_string(),
            )
        })?;
        if decoded_nullifier_count != key.nullifier_count {
            return Err(FaithfulMirrorError::InconsistentHead(
                "cheap and decoded durable nullifier counts disagree".to_string(),
            ));
        }
        let durable_nullifier_set =
            dregg_cell::nullifier_set::NullifierSet::from_records(durable_nullifiers.clone())
                .map_err(|error| {
                    FaithfulMirrorError::DurableState(format!(
                        "exact nullifier accumulator reconstruction failed: {error}"
                    ))
                })?;
        let nullifier_root = durable_nullifier_set.root8().to_bytes32();
        if key.latest_attested_root.nullifier_set_root != Some(nullifier_root) {
            return Err(FaithfulMirrorError::InconsistentHead(
                "durable nullifier records do not reconstruct the latest attested root".to_string(),
            ));
        }

        let head_message = faithful_mirror_head_signing_message(
            &anchor,
            key.expectation,
            key.nullifier_count,
            nullifier_root,
        );
        let seed = self.cclerk.gossip_signing_key().to_bytes();
        let local_ed = self.cclerk.public_key();
        let signing_key = dregg_types::SigningKey::from_bytes(&seed);
        let classical_signature = dregg_types::sign(&signing_key, &head_message);
        let (local_pq, local_pq_signing_key) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
        let pq_signature = local_pq_signing_key.sign(&head_message).ok_or_else(|| {
            FaithfulMirrorError::DurableState(
                "ML-DSA faithful mirror-head signing failed".to_string(),
            )
        })?;
        let head_hybrid_quorum: Arc<[dregg_types::HybridQuorumSig]> =
            Arc::from(vec![dregg_types::HybridQuorumSig {
                pubkey: local_ed,
                signature: classical_signature,
                ml_dsa_pubkey: local_pq.0.to_vec(),
                pq_signature,
            }]);
        let nullifiers: Vec<_> = durable_nullifiers
            .into_iter()
            .map(|(nullifier, value, seq)| (nullifier.0, value, seq))
            .collect();

        Ok(FaithfulMirrorSnapshot {
            key: key.clone(),
            commitments: Arc::from(commitments),
            nullifiers: Arc::from(nullifiers),
            anchor,
            history: Arc::from(history.envelopes().to_vec()),
            head_hybrid_quorum,
        })
    }

    fn faithful_mirror_snapshot(&self) -> Result<Arc<FaithfulMirrorSnapshot>, FaithfulMirrorError> {
        // Serialize misses so concurrent public requests cannot each trigger a
        // full replay/reconstruction and ML-DSA signature for the same head.
        let mut cache = self.faithful_mirror_cache.lock().map_err(|_| {
            FaithfulMirrorError::DurableState("faithful mirror cache lock poisoned".to_string())
        })?;
        let key = self.faithful_mirror_snapshot_key()?;
        self.validate_live_faithful_mirror_head(&key)?;
        if let Some(snapshot) = &cache.snapshot
            && snapshot.key == key
        {
            return Ok(snapshot.clone());
        }

        let snapshot = self.build_faithful_mirror_snapshot(&key)?;
        // The outer NodeState read lock already prevents ordinary finalization
        // from racing this build.  Re-read anyway so an out-of-band durable
        // mutation cannot publish a mixed-head cache image.
        let confirmed_key = self.faithful_mirror_snapshot_key()?;
        self.validate_live_faithful_mirror_head(&confirmed_key)?;
        if confirmed_key != key {
            return Err(FaithfulMirrorError::InconsistentHead(
                "faithful mirror head changed while its immutable snapshot was built".to_string(),
            ));
        }
        let snapshot = Arc::new(snapshot);
        cache.snapshot = Some(snapshot.clone());
        #[cfg(test)]
        {
            cache.builds = cache.builds.saturating_add(1);
        }
        Ok(snapshot)
    }

    #[cfg(test)]
    fn faithful_mirror_snapshot_builds(&self) -> u64 {
        self.faithful_mirror_cache
            .lock()
            .map(|cache| cache.builds)
            .unwrap_or(u64::MAX)
    }

    /// Return one target-independent mirror page.  Both cursors are prefix
    /// lengths, never note selectors.  The production SDK starts at `(0, 0, 0)`
    /// and follows only the returned continuations, downloading every
    /// intervening commitment and authenticated history row.
    pub fn faithful_note_mirror_page(
        &self,
        commitment_cursor: u64,
        history_cursor: u64,
        nullifier_cursor: u64,
    ) -> Result<FaithfulNoteMirrorPage, FaithfulMirrorError> {
        let snapshot = self.faithful_mirror_snapshot()?;
        if commitment_cursor > snapshot.key.expectation.note_count
            || history_cursor > snapshot.key.expectation.records
            || nullifier_cursor > snapshot.key.nullifier_count
        {
            return Err(FaithfulMirrorError::InconsistentHead(
                "mirror cursor is beyond the authenticated append-only head".to_string(),
            ));
        }

        let commitment_start = usize::try_from(commitment_cursor).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "commitment cursor does not fit usize".to_string(),
            )
        })?;
        let history_start = usize::try_from(history_cursor).map_err(|_| {
            FaithfulMirrorError::InconsistentHead("history cursor does not fit usize".to_string())
        })?;
        let nullifier_start = usize::try_from(nullifier_cursor).map_err(|_| {
            FaithfulMirrorError::InconsistentHead("nullifier cursor does not fit usize".to_string())
        })?;
        let commitment_end = commitment_start
            .checked_add(FAITHFUL_MIRROR_COMMITMENT_PAGE_SIZE)
            .ok_or_else(|| {
                FaithfulMirrorError::InconsistentHead(
                    "commitment page end does not fit usize".to_string(),
                )
            })?
            .min(snapshot.commitments.len());
        let history_end = history_start
            .checked_add(FAITHFUL_MIRROR_HISTORY_PAGE_SIZE)
            .ok_or_else(|| {
                FaithfulMirrorError::InconsistentHead(
                    "history page end does not fit usize".to_string(),
                )
            })?
            .min(snapshot.history.len());
        let nullifier_end = nullifier_start
            .checked_add(FAITHFUL_MIRROR_NULLIFIER_PAGE_SIZE)
            .ok_or_else(|| {
                FaithfulMirrorError::InconsistentHead(
                    "nullifier page end does not fit usize".to_string(),
                )
            })?
            .min(snapshot.nullifiers.len());
        let next_commitment_cursor = u64::try_from(commitment_end).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "next commitment cursor does not fit u64".to_string(),
            )
        })?;
        let next_history_cursor = u64::try_from(history_end).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "next history cursor does not fit u64".to_string(),
            )
        })?;
        let next_nullifier_cursor = u64::try_from(nullifier_end).map_err(|_| {
            FaithfulMirrorError::InconsistentHead(
                "next nullifier cursor does not fit u64".to_string(),
            )
        })?;
        Ok(FaithfulNoteMirrorPage {
            commitment_cursor,
            next_commitment_cursor,
            history_cursor,
            next_history_cursor,
            nullifier_cursor,
            next_nullifier_cursor,
            nullifier_count: snapshot.key.nullifier_count,
            commitments: snapshot.commitments[commitment_start..commitment_end].to_vec(),
            nullifiers: snapshot.nullifiers[nullifier_start..nullifier_end].to_vec(),
            anchor: snapshot.anchor.clone(),
            history: snapshot.history[history_start..history_end].to_vec(),
            head: snapshot.key.expectation,
            latest_attested_root: snapshot.key.latest_attested_root.clone(),
            head_hybrid_quorum: snapshot.head_hybrid_quorum.to_vec(),
        })
    }

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

#[cfg(test)]
mod faithful_mirror_snapshot_tests {
    use super::*;

    fn attested(
        height: u64,
        note_root: [u8; 32],
        nullifier_root: [u8; 32],
        marker: u8,
    ) -> dregg_persist::StoredAttestedRoot {
        dregg_persist::StoredAttestedRoot {
            merkle_root: [marker; 32],
            note_tree_root: Some(note_root),
            nullifier_set_root: Some(nullifier_root),
            height,
            timestamp: 1_700_000_000 + i64::from(marker),
            blocklace_block_id: Some([marker.wrapping_add(1); 32]),
            finality_round: Some(u64::from(marker)),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId([0x52; 32]),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        }
    }

    fn signed_history_edge(
        state: &NodeStateInner,
        record: dregg_persist::FaithfulNoteRootRecordV1,
    ) -> (
        dregg_persist::FaithfulNoteRootEnvelopeV1,
        dregg_types::PublicKey,
        dregg_federation::frost::MlDsaPublicKey,
    ) {
        let seed = state.cclerk.gossip_signing_key().to_bytes();
        let signing_key = dregg_types::SigningKey::from_bytes(&seed);
        let public_key = signing_key.public_key();
        let (pq_public_key, pq_signing_key) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
        let message = record.signing_message();
        (
            dregg_persist::FaithfulNoteRootEnvelopeV1 {
                record,
                hybrid_quorum: vec![dregg_types::HybridQuorumSig {
                    pubkey: public_key,
                    signature: dregg_types::sign(&signing_key, &message),
                    ml_dsa_pubkey: pq_public_key.0.to_vec(),
                    pq_signature: pq_signing_key.sign(&message).expect("ML-DSA test sign"),
                }],
            },
            public_key,
            pq_public_key,
        )
    }

    #[tokio::test]
    async fn fixed_head_pages_build_and_sign_once_then_head_advance_invalidates() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construct test node state");
        let mut state = state.write().await;

        let commitments: Vec<[u8; 32]> = (0..(FAITHFUL_MIRROR_COMMITMENT_PAGE_SIZE + 1))
            .map(|index| {
                let mut commitment = [0x31; 32];
                commitment[..8].copy_from_slice(&(index as u64).to_le_bytes());
                commitment
            })
            .collect();
        for commitment in &commitments {
            state
                .store
                .store_note_commitment(&dregg_cell::note::NoteCommitment(*commitment))
                .expect("persist note commitment");
            state.note_tree_append_commitment(commitment);
        }
        let root = dregg_persist::CanonicalFaithfulRoot::from_faithful(
            state.note_tree.faithful_root_immutable(),
        );
        let anchor = dregg_persist::FaithfulNoteRootAnchorV1::new(
            [0x51; 32],
            [0x52; 32],
            7,
            40,
            commitments.len() as u64,
            root,
        )
        .expect("canonical faithful anchor");
        state
            .store
            .initialize_faithful_note_root_history(&anchor)
            .expect("initialize history");
        let empty_nullifier_root = dregg_cell::nullifier_set::NullifierSet::new()
            .root8()
            .to_bytes32();
        state
            .store
            .store_attested_root(&attested(
                anchor.height,
                anchor.root.to_bytes(),
                empty_nullifier_root,
                1,
            ))
            .expect("store initial attested root");

        let first = state
            .faithful_note_mirror_page(0, 0, 0)
            .expect("first cached page");
        let second = state
            .faithful_note_mirror_page(FAITHFUL_MIRROR_COMMITMENT_PAGE_SIZE as u64, 0, 0)
            .expect("second cached page");
        let repeated = state
            .faithful_note_mirror_page(0, 0, 0)
            .expect("repeat cached page");
        assert_eq!(
            first.commitments.len(),
            FAITHFUL_MIRROR_COMMITMENT_PAGE_SIZE
        );
        assert_eq!(second.commitments.len(), 1);
        assert_eq!(first.head_hybrid_quorum, second.head_hybrid_quorum);
        assert_eq!(first.head_hybrid_quorum, repeated.head_hybrid_quorum);
        assert_eq!(state.faithful_mirror_snapshot_builds(), 1);

        let appended = [0xA7; 32];
        let record = dregg_persist::plan_faithful_note_root_transition_v1(
            &state.note_tree,
            &anchor,
            [0x61; 32],
            &[appended],
        )
        .expect("plan exact successor");
        let (envelope, public_key, pq_public_key) = signed_history_edge(&state, record.clone());
        state
            .store
            .store_note_commitment(&dregg_cell::note::NoteCommitment(appended))
            .expect("persist successor commitment");
        state.note_tree_append_commitment(&appended);
        state
            .store
            .append_faithful_note_root_hybrid(
                &envelope,
                std::slice::from_ref(&public_key),
                std::slice::from_ref(&pq_public_key),
                1,
            )
            .expect("append authenticated history edge");
        state
            .store
            .store_attested_root(&attested(
                record.height,
                record.successor.to_bytes(),
                empty_nullifier_root,
                2,
            ))
            .expect("store successor attested root");

        let advanced = state
            .faithful_note_mirror_page(commitments.len() as u64, 0, 0)
            .expect("advanced head page");
        assert_eq!(advanced.commitments, vec![appended]);
        assert_eq!(advanced.history, vec![envelope]);
        assert_eq!(advanced.head.height, record.height);
        assert_ne!(advanced.head_hybrid_quorum, first.head_hybrid_quorum);
        assert_eq!(state.faithful_mirror_snapshot_builds(), 2);
    }

    #[tokio::test]
    async fn same_count_durable_commitment_tamper_refuses_before_cache_publish() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construct test node state");
        let mut state = state.write().await;
        let durable_commitment = [0x81; 32];
        let authenticated_commitment = [0x82; 32];
        state
            .store
            .store_note_commitment(&dregg_cell::note::NoteCommitment(durable_commitment))
            .expect("persist mismatching durable row");
        state.note_tree_append_commitment(&authenticated_commitment);
        let authenticated_root = dregg_persist::CanonicalFaithfulRoot::from_faithful(
            state.note_tree.faithful_root_immutable(),
        );
        let anchor = dregg_persist::FaithfulNoteRootAnchorV1::new(
            [0x71; 32],
            [0x52; 32],
            3,
            9,
            1,
            authenticated_root,
        )
        .expect("canonical faithful anchor");
        state
            .store
            .initialize_faithful_note_root_history(&anchor)
            .expect("initialize history");
        let empty_nullifier_root = dregg_cell::nullifier_set::NullifierSet::new()
            .root8()
            .to_bytes32();
        state
            .store
            .store_attested_root(&attested(
                anchor.height,
                anchor.root.to_bytes(),
                empty_nullifier_root,
                3,
            ))
            .expect("store attested root");

        let error = state
            .faithful_note_mirror_page(0, 0, 0)
            .expect_err("same-count durable row substitution must refuse");
        assert!(
            error.to_string().contains("durable commitment bytes/root"),
            "refusal should name the durable commitment divergence: {error}"
        );
        assert_eq!(state.faithful_mirror_snapshot_builds(), 0);
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
            if !h.is_ascii() || h.len() != 64 {
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

    /// THE RESTART-DURABILITY CANARY (the weld the deep-reads converged on).
    ///
    /// Pre-fix, the cipherclerk `receipt_chain` was rebuilt EMPTY every boot, so
    /// after a restart `/api/receipts/index/head` (which projects the MMR from the
    /// chain via `sync_receipt_index`) served `len = 0` even though the ledger
    /// recovered. This drives a real restart at the `NodeState` level: append a
    /// chain, record the head, DROP the node, reopen the SAME data dir, and assert
    /// the head is the SAME real head — not `len = 0`. Without the durability weld
    /// (`install_receipt_chain_durability` + the cipherclerk persist sink) the two
    /// `post_len` assertions below fail with `len = 0`.
    #[tokio::test]
    async fn receipt_chain_and_mmr_head_survive_node_restart() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [11u8; 32];

        let pre_root;
        let pre_len;
        let sample_hash;
        {
            let state =
                NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("create node state");
            let mut s = state.write().await;
            // Append five independent agents' genesis receipts. The node-wide
            // log is total while causal receipt links are agent-scoped; every
            // append fires the durable persist sink installed at construction.
            for i in 0u8..5 {
                let receipt = dregg_turn::TurnReceipt {
                    turn_hash: [i.wrapping_add(1); 32],
                    post_state_hash: [i.wrapping_add(100); 32],
                    agent: CellId::from_bytes([i.wrapping_add(50); 32]),
                    previous_receipt_hash: None,
                    ..Default::default()
                };
                s.cclerk.append_receipt(receipt).expect("append receipt");
            }
            s.sync_receipt_index();
            pre_root = s.receipt_index.root();
            pre_len = s.receipt_index.len();
            sample_hash = s.cclerk.receipt_chain()[2].receipt_hash();
            assert_eq!(pre_len, 5, "5 receipts on the chain pre-restart");
            // The durability weld persisted each appended receipt synchronously.
            assert_eq!(
                s.store.receipt_chain_len().expect("durable len"),
                5,
                "every appended receipt is durable the moment it lands on the chain"
            );
            // F5: the served head was durably anchored by `sync_receipt_index`.
            assert_eq!(
                s.store.load_receipt_index_head().expect("load head anchor"),
                Some((pre_len, pre_root)),
                "sync_receipt_index anchored the served receipt-index head durably"
            );
        }

        // ── RESTART ── reopen the SAME data dir (crash recovery).
        let restored =
            NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("restore node state");
        let mut s = restored.write().await;
        s.sync_receipt_index();
        let post_root = s.receipt_index.root();
        let post_len = s.receipt_index.len();

        // THE CANARY: same head after restart (len=0 before the fix).
        assert_eq!(
            post_len, 5,
            "restart preserves the receipt-index length (was 0 pre-fix)"
        );
        assert_eq!(
            post_root, pre_root,
            "restart preserves the receipt-index MMR root"
        );
        assert_eq!(
            s.cclerk.receipt_chain().len(),
            5,
            "the durable receipt chain reloaded into the cipherclerk"
        );
        assert_eq!(
            s.cclerk.receipt_chain()[2].receipt_hash(),
            sample_hash,
            "the previously-fetched receipt is still present and replayable"
        );
        s.cclerk
            .verify_own_chain()
            .expect("every reloaded agent-scoped receipt chain verifies");

        // F5: the durable head anchor survived the restart AND the rebuilt MMR
        // reproduces it (the recovery check in `refresh_receipt_index_head_anchor`
        // saw `anchor_len == len` with a matching root — no integrity event).
        assert_eq!(
            s.store.load_receipt_index_head().expect("load head anchor"),
            Some((post_len, post_root)),
            "the receipt-index head anchor survives restart and matches the rebuilt MMR"
        );
    }

    /// THE REALM-SUBSTRATE RESTART CANARY (realm-model graduated into the node).
    ///
    /// A realm/instance/identity created THROUGH THE NODE — every turn admitted
    /// through realm-model's own gate (`RealmWorld::admit` / `settle_instance`),
    /// not ad-hoc JS — is persisted to the durable `REALM_LOG` and reloaded on
    /// boot. This drives a real `NodeState` restart: build a realm, settle a
    /// result into it, record the realm receipt-chain head, DROP the node, reopen
    /// the SAME data dir, and assert the realm survived (same head, same hoard,
    /// surface still resolves, catalog still committed). It ALSO shows the deployed
    /// refusal: a turn citing an UNLISTED `ruleset_root` is refused by realm-model's
    /// gate on the node path and persists nothing.
    #[tokio::test]
    async fn realm_created_through_node_survives_restart_and_refuses_false_catalog() {
        use realm_model::identity::{Surface, SurfaceRef};
        use realm_model::realm::Membrane;

        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [21u8; 32];
        let law: realm_model::RulesetRoot = *blake3::hash(b"descent-v1").as_bytes();
        let rogue: realm_model::RulesetRoot = *blake3::hash(b"rogue-law-v1").as_bytes();
        let actor = SurfaceRef::new(Surface::Discord, "p1#0001");

        let pre_head;
        let pre_count;
        let realm_id;
        {
            let state =
                NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("create node state");
            let realms = state.realms();
            let mut r = realms.write().await;

            // Build a realm THROUGH THE NODE (each op durable + gate-routed).
            r.mint_identity("player-one", "seed-p1").expect("mint");
            r.bind_surface("seed-p1", &actor).expect("bind");
            let realm = r
                .create_realm("the-burrow", Membrane::PinAtBirth)
                .expect("realm");
            realm_id = realm.id;
            r.list_ruleset("the-burrow", law).expect("list");

            let inst_a = r.open_instance("the-burrow", "day-1").expect("open a");
            assert_eq!(inst_a.parent_pin, 0, "instance A pins parent hoard 0");
            r.play(
                &actor,
                inst_a.id,
                law,
                realm_model::instance::field::RESULT,
                40,
            )
            .expect("play a");
            r.settle(&actor, inst_a.id, law).expect("settle a");
            assert_eq!(r.world().realm_hoard(&realm_id), 40, "realm accrued 40");
            assert_eq!(r.world().realm_epoch(&realm_id), 1);

            // ── the DEPLOYED refusal: an unlisted ruleset_root is refused by
            //    realm-model's gate on the node path, and persists nothing.
            let inst_b = r.open_instance("the-burrow", "day-2").expect("open b");
            let log_len_before_bad = r.durable_log_len();
            let bad = r.admit_turn(
                &actor,
                inst_b.id,
                rogue,
                vec![dregg_turn::action::Effect::SetField {
                    cell: inst_b.id,
                    index: realm_model::instance::field::RESULT as u64,
                    value: realm_model::pack_u64(1),
                }],
            );
            assert!(
                matches!(
                    bad,
                    Err(crate::realm_service::RealmError::Refused(
                        realm_model::Refused::RulesetNotInCatalog { .. }
                    ))
                ),
                "unlisted ruleset_root refused by the deployed realm gate; got {bad:?}"
            );
            assert_eq!(
                r.durable_log_len(),
                log_len_before_bad,
                "a refused realm turn persists NOTHING"
            );
            {
                let s = state.read().await;
                assert_eq!(
                    s.store.realm_log_len().expect("durable realm len"),
                    log_len_before_bad,
                    "the durable REALM_LOG did not grow on the refused turn"
                );
            }

            pre_head = r.receipt_head().expect("a realm receipt head exists");
            pre_count = r.receipt_count();
        }

        // ── RESTART ── reopen the SAME data dir (crash recovery).
        let restored =
            NodeState::with_cclerk(tmp.path(), vec![], key_bytes).expect("restore node state");
        let realms = restored.realms();
        let r = realms.read().await;

        // THE CANARY: the realm survived the restart on the durable log.
        assert_eq!(
            r.receipt_head(),
            Some(pre_head),
            "realm receipt-chain head survives the node restart (durable REALM_LOG replay)"
        );
        assert_eq!(
            r.receipt_count(),
            pre_count,
            "every admitted realm turn reloaded"
        );
        assert_eq!(
            r.world().realm_hoard(&realm_id),
            40,
            "the persistent realm's durable hoard survived the restart"
        );
        assert_eq!(r.world().realm_epoch(&realm_id), 1);
        // The canonical identity still resolves from its surface across the reboot.
        let resolved = r
            .world()
            .resolve_surface(&actor)
            .expect("surface resolves to canonical id after restart");
        assert_eq!(resolved.label, "player-one");
        // The committed law survived; the rogue root is still not law.
        assert!(r.world().is_listed(&realm_id, &law), "law still committed");
        assert!(
            !r.world().is_listed(&realm_id, &rogue),
            "rogue root still refused"
        );
    }

    #[test]
    fn corrupt_durable_receipt_bytes_refuse_node_boot() {
        let tmp = tempfile::tempdir().expect("tempdir");
        {
            let store = PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open store");
            store
                .append_receipt_chain_entry(0, b"not-a-postcard-turn-receipt")
                .expect("inject structurally corrupt durable entry");
        }

        let error = match NodeState::with_cclerk(tmp.path(), vec![], [12u8; 32]) {
            Ok(_) => panic!("corrupt durable receipt bytes must refuse node construction"),
            Err(error) => error,
        };
        assert!(
            error.contains("invalid durable receipt at log index 0"),
            "boot error identifies the corrupt durable index: {error}"
        );
    }

    #[test]
    fn corrupt_durable_receipt_link_refuses_node_boot_without_prefix_rollback() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let agent = CellId::from_bytes([0xA1; 32]);
        let first = dregg_turn::TurnReceipt {
            turn_hash: [1; 32],
            post_state_hash: [2; 32],
            agent,
            ..Default::default()
        };
        let second = dregg_turn::TurnReceipt {
            turn_hash: [3; 32],
            pre_state_hash: [2; 32],
            post_state_hash: [4; 32],
            previous_receipt_hash: Some([0xFF; 32]),
            agent,
            ..Default::default()
        };
        {
            let store = PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open store");
            store
                .append_receipt_chain_entry(0, &postcard::to_stdvec(&first).unwrap())
                .unwrap();
            store
                .append_receipt_chain_entry(1, &postcard::to_stdvec(&second).unwrap())
                .unwrap();
        }

        let error = match NodeState::with_cclerk(tmp.path(), vec![], [13u8; 32]) {
            Ok(_) => panic!("a corrupt durable tail must not boot at the valid prefix"),
            Err(error) => error,
        };
        assert!(
            error.contains("invalid durable receipt chain: receipt chain mismatch"),
            "boot refuses the whole corrupt chain: {error}"
        );
    }
}

#[cfg(test)]
mod crash_recovery_overlay_tests {
    //! Recovery-soundness regressions (.docs-history-noclaude/ARCHEOLOGY-LEDGER.md, HIGH tier).
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
            removed: Vec::new(),
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

    /// THE HARD-CRASH BRICK (measured 2026-07-26 on a real devnet node).
    ///
    /// `kill -9` on a node that had finalized three faucet turns and never
    /// written a ledger checkpoint left a data dir that REFUSED TO BOOT AGAIN:
    /// "NO commit-log prefix reconstructs to its recorded root". The boot walk
    /// reconstructs `empty ⊕ overlay`, but every record's `ledger_root` commits
    /// the FULL ledger (genesis ⊕ touched), so nothing converges — and the node
    /// turned that into a fatal store-integrity verdict. The first checkpoint
    /// lands at `--checkpoint-interval` blocks (default 1000) or on graceful
    /// shutdown, so every young node sits inside that window and only a clean
    /// SIGTERM was survivable.
    ///
    /// Two poles, so this cannot pass by being lenient:
    ///   * NO checkpoint + a CONSISTENT sub-checkpoint image → boots (the fix),
    ///     while the raw no-baseline walk still reports Integrity (the wound is
    ///     still there to be exercised).
    ///   * A checkpoint present + a genuinely DIVERGENT image → still REFUSES.
    #[tokio::test]
    async fn hard_crash_before_first_checkpoint_boots_but_a_divergent_store_still_refuses() {
        // ── pole 1: the crash window ──────────────────────────────────────────
        let tmp = tempfile::tempdir().expect("tempdir");
        let store = PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open store");

        // Genesis baseline: cells genesis established that NO turn touches, so
        // the commit-log overlay cannot carry them and — with no checkpoint —
        // nothing can. High seeds so they never collide with the touched cells.
        let mut ledger = Ledger::new();
        for seed in [0xf0u8, 0xf1, 0xf2] {
            ledger
                .insert_cell(cell(seed, 1_000_000))
                .expect("genesis baseline cell");
        }

        // Finalized turns whose recorded root commits genesis ⊕ touched — the
        // real shape a node commits. No checkpoint is ever written.
        for k in 0u64..3 {
            let touched = cell(k as u8, 100 + k as i64);
            let _ = ledger.remove(&touched.id());
            ledger.insert_cell(touched.clone()).expect("touched cell");
            let rec = dregg_persist::CommitRecord {
                ordinal: k,
                height: k + 1,
                block_id: [0u8; 32],
                block_executed_up_to: 0,
                turn_hash: [0xc0 | k as u8; 32],
                creator: [0u8; 32],
                receipt_hash: [0xd0 | k as u8; 32],
                ledger_root: crate::blocklace_sync::canonical_ledger_root(&ledger),
                touched_cells: vec![touched],
                removed: Vec::new(),
            };
            store.commit_finalized_turn(k, &rec).expect("commit turn");
        }

        assert!(
            store
                .load_latest_ledger_checkpoint()
                .expect("read checkpoint")
                .is_none(),
            "the crash window is DEFINED by having no checkpoint yet"
        );
        // THE WOUND, still real: the no-baseline walk cannot reproduce any
        // record's full-ledger root, so it calls a consistent image unsalvageable.
        assert!(
            store.recover_to_last_consistent().is_err(),
            "the no-baseline walk must still misread this consistent image — if it \
             stops, this test no longer exercises the hard-crash mechanism"
        );

        // THE FIX: the node reads that as INCONCLUSIVE (empty base, no checkpoint)
        // and boots, deferring the verdict to verify_recovery_convergence.
        run_boot_torn_tail_recovery(&store)
            .expect("a hard crash before the first checkpoint must not brick the data dir");

        // ── pole 2: the lenient branch must not launder a CORRUPT store ───────
        // The adversarial case for the change above: a store in the SAME
        // no-checkpoint crash window, but genuinely divergent — its records
        // commit a root the ledger does not reconstruct to. Boot recovery lets it
        // through (it cannot tell), so the deferred verdict is the whole defence.
        // If this stops refusing, the crash-window branch has become a hole.
        let tmp2 = tempfile::tempdir().expect("tempdir");
        let store2 = PersistentStore::open(&tmp2.path().join("dregg.redb")).expect("open store");
        let touched = cell(0x5e, 500);
        let rec = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xe1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xe2; 32],
            ledger_root: [0xde; 32], // deliberately NOT the post-overlay root
            touched_cells: vec![touched],
            removed: Vec::new(),
        };
        store2.commit_finalized_turn(0, &rec).expect("commit turn");
        assert!(
            store2
                .load_latest_ledger_checkpoint()
                .expect("read checkpoint")
                .is_none(),
            "pole 2 must sit in the SAME no-checkpoint window as pole 1"
        );
        drop(store2);

        // Construction proceeds (the verdict is the separate step) …
        let state = NodeState::new_with_key_file(tmp2.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay; the verdict is a separate step");
        // … and the deferred verdict REFUSES the divergent store.
        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a divergent store recovered in the crash window must still FAIL CLOSED");
        assert!(
            err.contains("convergence"),
            "the refusal must name the convergence failure; got: {err}"
        );
    }

    /// Build a store whose checkpoint at height 1 holds `cell(seed)` HOSTED, then
    /// a finalized turn at height 2 that REMOVES it (a `MakeSovereign` tombstone).
    /// `removed` carries the tombstone iff `carry_removal`; the recorded
    /// `ledger_root` is always the genuine post-removal root (an empty ledger).
    /// With the tombstone, `checkpoint ⊕ overlay` erases the cell and converges;
    /// WITHOUT it (the pre-fix insert-only overlay) the cell is resurrected as
    /// hosted and the root diverges — the falsifier's two poles.
    fn seed_store_with_removal(dir: &Path, seed: u8, carry_removal: bool) -> [u8; 32] {
        let db_path = dir.join("dregg.redb");
        let store = PersistentStore::open(&db_path).expect("open store");

        let mut checkpoint_ledger = Ledger::new();
        checkpoint_ledger
            .insert_cell(cell(seed, 100))
            .expect("seed hosted cell");
        store
            .checkpoint_ledger(&checkpoint_ledger, 1)
            .expect("write checkpoint");

        // The finalized root the removing turn recorded commits the cell GONE.
        let removed_root = crate::blocklace_sync::canonical_ledger_root(&Ledger::new());

        let removed = if carry_removal {
            vec![cell(seed, 0).id().0]
        } else {
            Vec::new()
        };
        let rec = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 2,
            block_id: [0u8; 32],
            block_executed_up_to: 0,
            turn_hash: [0xd1; 32],
            creator: [0u8; 32],
            receipt_hash: [0xd2; 32],
            ledger_root: removed_root,
            touched_cells: vec![], // a removal is NOT a post-state write
            removed,
        };
        store
            .commit_finalized_turn(0, &rec)
            .expect("commit removal turn");
        removed_root
    }

    #[tokio::test]
    async fn make_sovereign_removal_is_not_resurrected_on_recovery() {
        // Bug #57 falsifier (GREEN pole): a checkpoint holds hosted C; a finalized
        // MakeSovereign(C) turn commits above it, carrying C in the `removed`
        // tombstone. Recovery from checkpoint ⊕ overlay MUST erase C (not
        // resurrect it as hosted) AND reconstruct the recorded finalized root.
        let seed = 0x71;
        let tmp = tempfile::tempdir().expect("tempdir");
        let recorded_root = seed_store_with_removal(tmp.path(), seed, /*carry_removal=*/ true);

        let key_bytes = [0x22u8; 32];
        let state = NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("recovery with a converging removal overlay must succeed");
        let guard = state.read().await;
        assert!(
            guard.ledger.get(&cell(seed, 0).id()).is_none(),
            "a cell REMOVED (MakeSovereign) post-checkpoint must NOT be resurrected as \
             hosted by checkpoint ⊕ overlay recovery"
        );
        assert_eq!(
            crate::blocklace_sync::canonical_ledger_root(&guard.ledger),
            recorded_root,
            "the reconstructed ledger root must MATCH the durably recorded finalized \
             root once the removal is applied"
        );
    }

    #[tokio::test]
    async fn dropped_removal_resurrects_and_diverges_the_root() {
        // Bug #57 falsifier (RED pole / mutation canary): the SAME scenario with
        // the `removed` tombstone DROPPED (an insert-only overlay — the pre-fix
        // shape). The overlay carries no erasure, so C is resurrected as hosted
        // from the checkpoint and the reconstructed root DIVERGES from the recorded
        // finalized root. This proves the `removed` dimension is load-bearing: were
        // it absent, recovery would serve a silently-wrong (over-populated) ledger.
        let seed = 0x71;
        let tmp = tempfile::tempdir().expect("tempdir");
        let recorded_root =
            seed_store_with_removal(tmp.path(), seed, /*carry_removal=*/ false);

        let key_bytes = [0x22u8; 32];
        let state = NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("construction reconstructs the overlay (verdict is a separate step)");
        let guard = state.read().await;
        assert!(
            guard.ledger.get(&cell(seed, 0).id()).is_some(),
            "without the tombstone the removed cell is RESURRECTED as hosted — the bug"
        );
        assert_ne!(
            crate::blocklace_sync::canonical_ledger_root(&guard.ledger),
            recorded_root,
            "the resurrected ledger root must DIVERGE from the recorded finalized root — \
             the tombstone dimension is what makes recovery converge"
        );
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

    /// F3 (integrity gate skippable on read-error): the read-error policy that
    /// [`NodeStateInner::verify_recovery_convergence`] uses. Both directions —
    /// a read error is non-fatal ONLY on a fresh/zero-cursor node; on a node with
    /// finalized state (non-zero cursor) an unreadable recorded root FAILS CLOSED,
    /// and an unreadable cursor also fails closed (freshness unprovable).
    #[test]
    fn recovery_read_error_is_fatal_only_with_finalized_state() {
        assert!(
            !recovery_read_error_is_fatal(Ok(0)),
            "fresh/zero-cursor node: a root read error must NOT block boot"
        );
        assert!(
            recovery_read_error_is_fatal(Ok(1)),
            "non-zero cursor: an unreadable recorded root FAILS CLOSED"
        );
        assert!(recovery_read_error_is_fatal(Ok(9_999)));
        assert!(
            recovery_read_error_is_fatal(Err(dregg_persist::StoreError::Database(
                "cursor unreadable".to_string()
            ))),
            "cursor itself unreadable: cannot prove freshness → fail closed"
        );
    }

    /// F3 "still succeeds" direction: a genuinely fresh node (zero commit cursor,
    /// no recorded finalized root) has nothing to converge to and MUST boot — the
    /// read-error fail-closed path must never break first boot.
    #[tokio::test]
    async fn fresh_zero_cursor_boot_passes_convergence_with_no_recorded_root() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("fresh construction");
        assert_eq!(
            state.read().await.store.commit_cursor().expect("cursor"),
            0,
            "fresh node has a zero commit cursor"
        );
        state
            .verify_recovery_convergence()
            .await
            .expect("a fresh zero-cursor node with no recorded root must boot");
    }

    /// A small deterministic committee (signing keys → public keys) for the NODE-1/2 tests.
    fn test_committee(n: u8) -> Vec<dregg_types::PublicKey> {
        (0..n)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i;
                seed[31] = 0x5a;
                dregg_types::SigningKey::from_bytes(&seed).public_key()
            })
            .collect()
    }

    #[tokio::test]
    async fn node1_forged_attested_root_refuses_to_start() {
        // **NODE-1.** A converging store (crash-consistency passes), but the latest
        // federation attested root carries committee public keys with GARBAGE signatures
        // (a forged/unsigned finalization an offline attacker fabricated). The signed
        // anchor verifies the quorum signature against the loaded committee — it does NOT
        // verify — so the node REFUSES to start rather than serve a ledger the federation
        // never signed.
        let seed = 0x5a;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        let committee = test_committee(3);
        let fed_id;
        {
            let mut s = state.write().await;
            s.set_federation_keys(committee.clone());
            fed_id = s.federation_id;
        }
        {
            let s = state.read().await;
            let forged = dregg_persist::StoredAttestedRoot {
                merkle_root: converged_root(seed, 42),
                note_tree_root: None,
                nullifier_set_root: None,
                height: 2, // the head height
                timestamp: 0,
                blocklace_block_id: None,
                finality_round: None,
                // in-committee keys, but NO valid signature (forged).
                quorum_signatures: committee
                    .iter()
                    .map(|pk| (*pk, dregg_types::Signature([0u8; 64])))
                    .collect(),
                threshold_qc: None,
                threshold: 3,
                federation_id: dregg_types::FederationId(fed_id),
                receipt_stream_root: None,
                finalization_quorum: Vec::new(),
            };
            s.store
                .store_attested_root(&forged)
                .expect("store the forged attested root");
        }

        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a forged/unsigned attested root must FAIL CLOSED (NODE-1)");
        assert!(
            err.contains("NODE-1") || err.contains("quorum signature"),
            "the refusal must name the signed-anchor failure; got: {err}"
        );
    }

    /// Signing keys whose public halves are exactly `test_committee(n)`.
    fn test_committee_keys(n: u8) -> Vec<dregg_types::SigningKey> {
        (0..n)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i;
                seed[31] = 0x5a;
                dregg_types::SigningKey::from_bytes(&seed)
            })
            .collect()
    }

    /// The byte-identical public twin of `StoredAttestedRoot::signing_message`
    /// (which is `pub(crate)` to dregg-persist), via `dregg_types::AttestedRoot`.
    fn stored_root_signing_message(r: &dregg_persist::StoredAttestedRoot) -> Vec<u8> {
        dregg_types::AttestedRoot {
            merkle_root: r.merkle_root,
            note_tree_root: r.note_tree_root,
            nullifier_set_root: r.nullifier_set_root,
            height: r.height,
            timestamp: r.timestamp,
            blocklace_block_id: r.blocklace_block_id,
            finality_round: r.finality_round,
            quorum_signatures: r.quorum_signatures.clone(),
            threshold_qc: r.threshold_qc.clone(),
            threshold: r.threshold,
            federation_id: r.federation_id,
            receipt_stream_root: r.receipt_stream_root,
            hybrid_quorum: Vec::new(),
        }
        .signing_message()
    }

    /// ⚑ **NODE-1, WRONG-COMMITTEE POLE.** A GENUINE quorum — real signatures,
    /// full threshold — from a committee version the chain had ROTATED OUT
    /// before the anchored block must NOT anchor a restart. This is the
    /// "restart accepts a quorum from any historical committee" defect: the
    /// rotated-out members (an evicted equivocator above all) still hold their
    /// old keys, so "verifies against some committee we once knew" is not a
    /// verified quorum. The control half proves the same root DOES anchor when
    /// the chain says that committee WAS current at that block — the refusal
    /// is committee-specificity, not signature checking.
    #[tokio::test]
    async fn node1_wrong_committee_version_quorum_refuses() {
        let seed = 0x5c;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        // Committee A = version 0 (rotated out). Committee B = version 1
        // (current at the anchored block). Disjoint key sets.
        let sks_a: Vec<dregg_types::SigningKey> = (10u8..13)
            .map(|i| dregg_types::SigningKey::from_bytes(&[i; 32]))
            .collect();
        let committee_a: Vec<dregg_types::PublicKey> =
            sks_a.iter().map(|k| k.public_key()).collect();
        let committee_b = test_committee(3);
        let anchored_block = [0xB0; 32];
        let fed_id;
        {
            let mut s = state.write().await;
            s.set_federation_keys(committee_b.clone());
            fed_id = s.federation_id;
            s.derived_committee_history = vec![committee_a.clone(), committee_b.clone()];
            s.derived_committee_ml_dsa_history = vec![Vec::new(), Vec::new()];
            // The chain's own replay: at the anchored block, committee B
            // (version 1) was current.
            s.derived_committee_version_at_block =
                std::iter::once((anchored_block, 1u64)).collect();
        }

        let mut root = dregg_persist::StoredAttestedRoot {
            merkle_root: converged_root(seed, 42),
            note_tree_root: None,
            nullifier_set_root: None,
            height: 2,
            timestamp: 0,
            blocklace_block_id: Some(anchored_block),
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 3,
            federation_id: dregg_types::FederationId(fed_id),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        let msg = stored_root_signing_message(&root);
        root.quorum_signatures = sks_a
            .iter()
            .map(|k| (k.public_key(), dregg_types::sign(k, &msg)))
            .collect();
        // MUTATION ASSERTED LIVE: this is a GENUINE full quorum of committee A
        // — the falsifier is real signatures from the wrong roster, not junk.
        assert!(
            root.verify_signatures(&committee_a),
            "the wrong-committee quorum must be genuine under committee A for this \
             test to falsify anything"
        );
        {
            let s = state.read().await;
            s.store
                .store_attested_root(&root)
                .expect("attacker/store writes the wrong-committee root");
        }

        let err = state.verify_recovery_convergence().await.err().expect(
            "a quorum from a committee version that was NOT current at the anchored \
                 block must be REFUSED (NODE-1 committee specificity)",
        );
        assert!(
            err.contains("claims a committee quorum"),
            "the refusal names the unverifiable quorum claim; got: {err}"
        );

        // CONTROL (honest pole): the SAME root anchors once the chain says
        // committee A WAS current at that block (version 0).
        {
            let mut s = state.write().await;
            s.derived_committee_version_at_block =
                std::iter::once((anchored_block, 0u64)).collect();
        }
        state
            .verify_recovery_convergence()
            .await
            .expect("the same quorum anchors when its committee version matches the chain");
    }

    /// ⚑ **NODE-1, TAMPERED-THRESHOLD POLE.** `StoredAttestedRoot.threshold`
    /// is in NO signed preimage — an offline tamper can rewrite it. A root
    /// whose stored threshold says `1` with ONE genuine committee signature
    /// (of a 3-member committee) must NOT anchor: the committee's own
    /// supermajority floors the bar regardless of what the row claims.
    #[tokio::test]
    async fn node1_tampered_threshold_cannot_lower_the_quorum_bar() {
        let seed = 0x5d;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        let committee = test_committee(3);
        let sks = test_committee_keys(3);
        let fed_id;
        {
            let mut s = state.write().await;
            s.set_federation_keys(committee.clone());
            fed_id = s.federation_id;
        }
        let mut root = dregg_persist::StoredAttestedRoot {
            merkle_root: converged_root(seed, 42),
            note_tree_root: None,
            nullifier_set_root: None,
            height: 2,
            timestamp: 0,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            // The tamper: the unsigned threshold field lowered to 1.
            threshold: 1,
            federation_id: dregg_types::FederationId(fed_id),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };
        let msg = stored_root_signing_message(&root);
        let sig = dregg_types::sign(&sks[0], &msg);
        // MUTATION ASSERTED LIVE: the lone signature is GENUINE (member 0 over
        // this exact preimage) and satisfies the tampered threshold count.
        assert!(
            committee[0].verify(&msg, &sig),
            "the lone signature is real"
        );
        root.quorum_signatures = vec![(committee[0], sig)];
        assert!(
            root.quorum_signatures.len() >= root.threshold,
            "the tampered row claims quorum sufficiency"
        );
        {
            let s = state.read().await;
            s.store.store_attested_root(&root).expect("store the row");
        }

        let err = state.verify_recovery_convergence().await.err().expect(
            "one genuine signature under a tampered threshold must NOT anchor a \
             3-member committee (NODE-1)",
        );
        assert!(
            err.contains("claims a committee quorum"),
            "the refusal names the unverifiable quorum claim; got: {err}"
        );
    }

    /// ⚑ **NODE-1, SKIP-DOOR POLES.** The two unsigned fields whose mere
    /// presence used to DISABLE the anchor for the whole boot ("not enforced
    /// this boot") now refuse: a claimed BLS threshold-QC (no production path
    /// emits one) and a latest root from a different federation (this store is
    /// not this federation's store — re-genesis, don't boot unanchored).
    #[tokio::test]
    async fn node1_qc_claim_and_foreign_federation_refuse_instead_of_skipping() {
        let seed = 0x5e;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        let committee = test_committee(3);
        let fed_id;
        {
            let mut s = state.write().await;
            s.set_federation_keys(committee.clone());
            fed_id = s.federation_id;
        }
        let base = dregg_persist::StoredAttestedRoot {
            merkle_root: converged_root(seed, 42),
            note_tree_root: None,
            nullifier_set_root: None,
            height: 2,
            timestamp: 0,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 3,
            federation_id: dregg_types::FederationId(fed_id),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        };

        // Pole 1: a threshold-QC claim (unsigned field, nothing produces it).
        let qc = dregg_persist::StoredAttestedRoot {
            threshold_qc: Some(dregg_types::ThresholdQC(vec![0xFF; 48])),
            ..base.clone()
        };
        assert!(
            qc.threshold_qc.is_some(),
            "mutation live: the QC claim is present"
        );
        {
            let s = state.read().await;
            s.store.store_attested_root(&qc).expect("store the QC row");
        }
        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a claimed threshold-QC must refuse, not disable the anchor");
        assert!(
            err.contains("threshold QC"),
            "the refusal names the QC claim; got: {err}"
        );

        // Pole 2: a foreign federation id on the latest root (higher height so
        // it IS the latest).
        let foreign = dregg_persist::StoredAttestedRoot {
            height: 3,
            federation_id: dregg_types::FederationId([0x99; 32]),
            ..base
        };
        assert_ne!(
            foreign.federation_id.0, fed_id,
            "mutation live: the row belongs to another federation"
        );
        {
            let s = state.read().await;
            s.store
                .store_attested_root(&foreign)
                .expect("store the foreign row");
        }
        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a foreign-federation latest root must refuse, not skip the anchor");
        assert!(
            err.contains("different federation"),
            "the refusal names the federation mismatch; got: {err}"
        );
    }

    #[tokio::test]
    async fn node2_rollback_below_high_water_refuses_to_start() {
        // **NODE-2.** A converging store at head height 2, but a persisted high-water
        // mark records a previously-witnessed finalized height of 100 — i.e. an attacker
        // swapped in an OLDER internally-consistent snapshot. The boot-time anti-rollback
        // check refuses to start rather than revert finalized spends / resurrect spent
        // nullifiers.
        let seed = 0x6b;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));
        // Persist a high-water mark ABOVE the recovered head (a prior boot saw height 100).
        {
            let store = PersistentStore::open(&tmp.path().join("dregg.redb")).expect("open store");
            store
                .set_config("recovery_finalized_high_water", &100u64.to_le_bytes())
                .expect("persist high-water mark");
        }

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        let err = state
            .verify_recovery_convergence()
            .await
            .err()
            .expect("a head below the high-water mark must FAIL CLOSED (NODE-2 anti-rollback)");
        assert!(
            err.contains("anti-rollback") || err.contains("NODE-2"),
            "the refusal must name the anti-rollback violation; got: {err}"
        );
    }

    #[tokio::test]
    async fn node2_high_water_allows_equal_or_higher_head_and_advances() {
        // **NODE-2 control (non-vacuous).** A converging store at head 2 with no prior
        // watermark boots cleanly, persists the watermark at 2, and a SECOND convergence
        // at the SAME head still passes (monotonic ALLOWS equal — the gate refuses only a
        // strictly-lower head). Proves the anti-rollback does not false-refuse a normal
        // restart.
        let seed = 0x77;
        let tmp = tempfile::tempdir().expect("tempdir");
        seed_store_with_overlay(tmp.path(), seed, 7, 42, converged_root(seed, 42));

        let state = NodeState::new_with_key_file(tmp.path(), vec![], "node.key")
            .expect("construction reconstructs the overlay");
        // First boot: persists the high-water mark at the head (2).
        state
            .verify_recovery_convergence()
            .await
            .expect("first boot at a fresh head must pass and set the watermark");
        // Second boot at the SAME head: equal height is allowed (monotonic, not strict).
        state
            .verify_recovery_convergence()
            .await
            .expect("a restart at the same finalized head must NOT be flagged as a rollback");
        // The watermark is now pinned at the head height.
        let s = state.read().await;
        let hwm = s
            .store
            .get_config("recovery_finalized_high_water")
            .unwrap()
            .and_then(|b| <[u8; 8]>::try_from(b.as_slice()).ok())
            .map(u64::from_le_bytes)
            .unwrap_or(0);
        assert_eq!(hwm, 2, "the high-water mark advanced to the recovered head");
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
            removed: Vec::new(),
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
            let stats = crate::reseed_genesis_then_overlay(&genesis, &mut s.ledger, &[]);
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
            let _ = crate::reseed_genesis_then_overlay(&genesis, &mut s.ledger, &[]);
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
