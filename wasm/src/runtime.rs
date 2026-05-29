//! DreggRuntime: full in-browser distributed system simulation.
//!
//! Encapsulates a complete dregg environment with:
//! - A Ledger (cells + Merkle state)
//! - A TurnExecutor
//! - A NullifierSet (note double-spend tracking)
//! - An IntentPool (simplified)
//! - A RevocationChannelSet
//! - Multiple AgentCipherclerk instances (for multi-party simulation)
//! - Federation simulation (in-memory, no networking)

use std::collections::HashMap;

use serde::Serialize;
use zeroize::Zeroizing;

use crate::{hex_encode, js_sys_now_secs};

use dregg_cell::CellMode;
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Note, NoteCommitment, Nullifier, NullifierSet,
    PeerExchange, RevocationChannel, RevocationChannelSet,
};
use dregg_intent::matcher::{HeldCapability, MatchResult, Sensitivity, match_intent};
use dregg_intent::{
    ActionPattern, CommitmentId, Constraint, Intent, IntentKind, MatchSpec, VerificationMode,
};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::{Authorization, WitnessBlob};
use dregg_turn::builder::ActionBuilder;
use dregg_turn::conditional::{ConditionalTurn, ProofCondition};
use dregg_turn::forest::CallTree;
use dregg_turn::{
    ComputronCosts, Effect, Turn, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
    WitnessedReceipt,
};

// Observability live feed (STARBRIDGE-03 Task #30). Emitter provides the
// canonical EventLog; we surface snapshots via the `events` field for
// wasm-bindgen + JS signal caching. No JS reimplementation per substrate rule.
use dregg_observability::{
    Emitter, EventBody, EventEnvelope, EventLog, TraceEvent, TurnLifecyclePayload,
};

/// Cell-ID domain shared by every wasm-sim agent. AgentCipherclerk derives the
/// CellId deterministically as `f(public_key, domain)` so this string is part
/// of the agent's identity surface.
const WASM_SIM_DOMAIN: &str = "dregg-wasm-default-domain";

/// Fee charged on the system turn that mints a new cell from the genesis
/// agent. Must cover the computron cost of `Effect::CreateCellFromFactory`
/// (~850 with default costs — same as `CreateCell`) plus the optional
/// `Effect::Transfer` to fund the new cell (~125 extra). 2000 leaves
/// comfortable headroom and is debited from the genesis agent's balance.
const GENESIS_MINT_FEE: u64 = 2000;

/// Derive-key tag for the default test-cipherclerk factory VK. The factory
/// is a constructor-transparency anchor — every wasm-runtime agent
/// (other than genesis) is born from this factory, so every cell's
/// provenance points at the same VK. The VK string is part of the
/// agent's identity surface; changing it changes the factory hash and
/// invalidates any test fixtures that pin the factory VK.
const WASM_DEFAULT_FACTORY_DOMAIN: &str = "dregg-wasm-default-test-cclerk-factory-v1";

/// Build the default "test cipherclerk" `FactoryDescriptor` used by
/// [`DreggRuntime`] when an agent is created without an explicit factory.
///
/// The descriptor is intentionally permissive:
/// - `child_program_vk = None` and `child_vk_strategy = None` —
///   created cells have no installed program VK; the factory is a
///   pure agent-cell mint, not a program-deploying factory.
/// - `allowed_cap_templates = []` — created cells get no initial
///   capabilities (the runtime's `grant_capability` does that
///   separately, post-creation).
/// - `field_constraints = []` — the descriptor does not constrain
///   initial fields; the wasm runtime never sets initial fields.
/// - `state_constraints = []` — no perpetual slot caveats.
/// - `default_mode = Hosted` — matches the previous `Cell::new_hosted`
///   shape used by the pre-factory `Effect::CreateCell` path.
/// - `creation_budget = None` — unbounded mints (the wasm runtime is
///   a sim; the budget would just be a denial-of-service knob for
///   tests, not a useful invariant).
///
/// The `factory_vk` field is BLAKE3 derived from
/// [`WASM_DEFAULT_FACTORY_DOMAIN`], so it is deterministic and
/// reproducible across browser sessions. Apps that want their own
/// factory can deploy one via [`DreggRuntime::deploy_factory`] and
/// pass its VK to [`DreggRuntime::try_create_agent_with_factory`].
pub fn default_cipherclerk_factory_descriptor() -> FactoryDescriptor {
    let factory_vk: [u8; 32] = *blake3::Hasher::new_derive_key(WASM_DEFAULT_FACTORY_DOMAIN)
        .update(b"factory-vk")
        .finalize()
        .as_bytes();
    FactoryDescriptor {
        factory_vk,
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: Vec::new(),
        field_constraints: Vec::new(),
        state_constraints: Vec::new(),
        default_mode: CellMode::Hosted,
        creation_budget: None,
    }
}

// ============================================================================
// Internal state types
// ============================================================================

/// An agent in the wasm runtime: a real `dregg_sdk::AgentCipherclerk` plus the
/// auxiliary state we need for in-browser scenarios (cached cell_id, an
/// intent-matcher-shaped token list, a commitment id, a counter for token-id
/// generation, and a friendly name).
///
/// `held_tokens` here is the `dregg_intent::matcher::HeldCapability` shape
/// used by the intent matcher — distinct from `cclerk.tokens()` which is
/// the SDK's macaroon-backed `HeldToken`. Both legitimately coexist.
pub struct SimAgent {
    pub name: String,
    pub cclerk: AgentCipherclerk,
    pub public_key: [u8; 32],
    pub cell_id: CellId,
    pub held_tokens: Vec<HeldCapability>,
    pub commitment_id: CommitmentId,
    pub token_counter: u64,
    /// Canonical `PeerExchange` session for this agent. Built once at agent
    /// creation via `AgentCipherclerk::peer_exchange(WASM_SIM_DOMAIN)`, so the
    /// signing key used by the exchange is the cipherclerk's real Ed25519 key —
    /// no JS-side or wasm-side reimplementation. Mutated by `register_peer`,
    /// `create_transition`, and `verify_transition`.
    pub peer_exchange: PeerExchange,
    /// Notes this agent has minted via `create_note`, in mint order. Each entry
    /// carries the canonical `Note` (so the commitment / nullifier are recomputed
    /// from real `dregg_cell::Note` math, not stored separately) plus the spent
    /// nullifier once `spend_note` reveals it. This is the note index that
    /// `get_notes` and `dregg://note/*` URI lookups read — closing #45, where
    /// minted notes were not tracked so `get_notes` always returned `[]`.
    pub held_notes: Vec<HeldNote>,
}

/// A note minted by a [`SimAgent`] via [`DreggRuntime::create_note`]. Holds the
/// canonical `dregg_cell::Note` so the commitment/value/asset_type all come from
/// the real note math; `nullifier` is `Some` once the note has been spent
/// (`spend_note` reveals it into the `NullifierSet`).
#[derive(Clone, Debug)]
pub struct HeldNote {
    /// The canonical note. `commitment()` / `value()` / `asset_type()` are
    /// derived from this — no shadow copies that could drift.
    pub note: Note,
    /// The revealed nullifier, present iff the note has been spent. Derived from
    /// the same deterministic spending key `spend_note` uses.
    pub nullifier: Option<Nullifier>,
}

// Federation is wired via the canonical `dregg_federation::Federation`
// (attestation context, no simulator). The async TCP transport and the old
// Morpheus BFT simulator (`node.rs` / `transport.rs`) are native-only and
// have been deleted. The wasm runtime keeps a lightweight local consensus
// stub — a `HashSet` of revoked tokens + monotonically increasing height —
// that lets the Studio UI exercise `propose_block` / `simulate_consensus_round`
// without any wasm-incompatible I/O.
//
// Surface exposed to wasm: `create_federation`, `propose_block`,
// `simulate_consensus_round`. These build a real `AttestedRoot` via
// `Federation::build_attested_root` — the federation_id, threshold, and
// member keys are all canonical; only the BLS aggregate signature is elided
// (the wasm Studio does not run the BLS pipeline).

/// Summary of one finalized consensus round, stored in `SimFederation::finalized_blocks`.
/// Replaces the `(RevocationBlock, QuorumCertificate)` entries in the deleted
/// `node::Federation::finalized_history`. The fields match what `get_federation_block`
/// and `list_federation_blocks` expose to JS.
#[derive(Clone, Debug)]
pub struct FinalizedBlock {
    pub height: u64,
    pub view: u64,
    pub block_hash: [u8; 32],
    /// Hash of the predecessor block (chain integrity). Mirrors the canonical
    /// `dregg_federation::RevocationBlock::prev_hash`. Populated from the
    /// previous finalized block's `block_hash` (the linear height-(N-1)
    /// predecessor); the genesis-most block in this sim has `[0u8; 32]`. Bound
    /// into `block_hash` so the chain is cryptographically linked, matching
    /// `RevocationBlock::compute_hash` which folds `prev_hash` into the digest.
    pub prev_hash: [u8; 32],
    pub revoked_token_ids: Vec<String>,
    pub qc_votes: usize,
    pub qc_threshold: usize,
    /// Ledger state Merkle root captured immediately before this consensus round
    /// finalized. Real value from `Ledger::root()` (canonical binary-BLAKE3
    /// state tree) — not a placeholder. In the wasm sim a federation consensus
    /// round only finalizes *revocations* (it does not apply turns to the
    /// ledger), so `pre_state_root == post_state_root` for any given round; both
    /// are nonetheless the ledger's genuine root at block time, giving
    /// `<dregg-block>` a real anchor instead of all-zeros.
    pub pre_state_root: [u8; 32],
    /// Ledger state Merkle root captured immediately after this consensus round
    /// finalized. See `pre_state_root`.
    pub post_state_root: [u8; 32],
}

/// A named in-browser federation. The handle the JS UI uses to address a
/// federation is its index in `DreggRuntime::federations`; the friendly name
/// is informational only (used by `<dregg-federation>` for display).
pub struct SimFederation {
    pub name: String,
    /// Canonical `dregg_federation::Federation` — owns the committee pubkeys,
    /// epoch, threshold, and derived federation_id. Every `AttestedRoot` built
    /// by this sim carries the federation's real id and threshold.
    pub federation: dregg_federation::Federation,
    /// Number of simulated nodes in this federation (committee size).
    pub node_count: usize,
    /// Revoked token ids accumulated since the last consensus round.
    pub pending_revocations: Vec<String>,
    /// All token ids ever revoked (for membership queries).
    pub revoked_set: std::collections::HashSet<String>,
    /// Monotonically increasing block height, bumped on each finalized round.
    pub height: u64,
    /// Monotonically increasing view number, bumped on each round attempt.
    pub view: u64,
    /// Ordered history of finalized rounds; replaces `node::Federation::finalized_history`.
    pub finalized_blocks: Vec<FinalizedBlock>,
    /// History of `propose_block` calls: one entry per call, each a list of
    /// token IDs that were *submitted*. Used by `<dregg-block>` so the
    /// inspector can surface input intent alongside the canonical
    /// `RevocationBlock`.
    pub submitted_token_ids: Vec<Vec<String>>,
}

/// Carrier for an `Authorization::Custom` attached to an app turn: the
/// witnessed predicate plus the proof bytes that discharge it.
struct CustomAuth {
    predicate: dregg_cell::WitnessedPredicate,
    proof_bytes: Vec<u8>,
}

/// A pending conditional turn.
#[derive(Clone, Debug)]
pub struct PendingConditional {
    pub id: [u8; 32],
    pub conditional: ConditionalTurn,
    pub submitted_height: u64,
}

/// Execution trace step (for step-by-step visualization).
#[derive(Clone, Debug, Serialize)]
pub struct TraceStep {
    pub action_path: Vec<usize>,
    pub target_cell: String,
    pub method: String,
    pub effects: Vec<String>,
    pub result: String,
    pub computrons_used: u64,
}

// Local hex32 for observability payloads (lowercase, no prefix; matches
// schema::hex32 contract). Placed here (free fn) so it is usable from
// execute_turn_for_agent without being an inherent method.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push_str(&format!("{:02x}", b));
    }
    out
}

/// Build a minimal `TurnReceipt` for the γ.2 bilateral-aggregate demo's
/// per-cell `WitnessedReceipt`s. The aggregator's soundness gate is the PI
/// bilateral roots + the canonical-Turn schedule replay (not the receipt body),
/// so a zeroed receipt with the correct `agent` is sufficient — mirroring the
/// `dummy_receipt` helpers in the aggregator's own happy-path tests.
fn bilateral_demo_receipt(agent: CellId) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
    }
}

// ============================================================================
// DreggRuntime: the core state container
// ============================================================================

/// The main runtime struct holding all simulation state.
/// NOT exposed directly via wasm_bindgen (we use an index-based handle instead).
pub struct DreggRuntime {
    pub ledger: Ledger,
    pub executor: TurnExecutor,
    pub nullifier_set: NullifierSet,
    pub agents: Vec<SimAgent>,
    pub agent_names: HashMap<String, usize>,
    pub intents: Vec<Intent>,
    pub revocation_channels: RevocationChannelSet,
    pub conditionals: Vec<PendingConditional>,
    pub current_height: u64,
    pub current_timestamp: i64,
    pub receipts: Vec<TurnReceipt>,
    /// Committed turns stored in parallel with `receipts` (index i in
    /// `turns` corresponds to index i in `receipts`). Stored so
    /// `get_receipt_chain` can surface per-action authorization details
    /// (Refactor 3 / Studio bindings enrichment).
    pub turns: Vec<Turn>,
    /// `dregg_federation::Federation` instances (attestation contexts), addressed
    /// by index. Each `SimFederation` pairs the canonical committee context with
    /// a lightweight local consensus stub — see `SimFederation` for details.
    pub federations: Vec<SimFederation>,
    /// VK of the default test-cipherclerk factory deployed at runtime
    /// construction. See [`default_cipherclerk_factory_descriptor`]. Subsequent
    /// agents (post-genesis) and cells minted from genesis are born via
    /// `Effect::CreateCellFromFactory` against this VK by default —
    /// closing the previous "genesis-by-fiat" gap (see
    /// `STUDIO-REFACTOR-PICKUP.md`).
    pub default_factory_vk: [u8; 32],

    /// dregg-observability Emitter (internal; drives seq + timestamps for trace events).
    emitter: Emitter,
    /// Snapshot of the event log (populated on turn lifecycle results for
    /// Committed/Rejected/Expired). Exposed to bindings for get_trace_events_json
    /// and JS <dregg-activity> live feed. Canonical Rust types only (substrate rule).
    pub events: EventLog,

    /// Per-turn EffectVM STARK proof records, keyed by `turn_hash`. Populated
    /// lazily by [`DreggRuntime::prove_turn`] (NOT on every commit — STARK
    /// proving is expensive in wasm). `get_receipt_chain` reads this cache to
    /// surface a real `proof_view` for `<dregg-proof>`; an absent entry means
    /// the turn has not yet been proved (scope-0 / Placeholder until proved).
    pub turn_proofs: HashMap<[u8; 32], TurnProofRecord>,

    /// Cached GOLDEN-tier cross-cell bilateral aggregate proof (Stage 7-γ.2),
    /// produced lazily by [`DreggRuntime::prove_bilateral_aggregate`]. There is
    /// at most one (the canonical two-cell transfer demo); `None` until the
    /// inspector triggers proving. Proving + self-verification is expensive, so
    /// like `turn_proofs` it is NOT run at boot.
    pub bilateral_aggregate: Option<BilateralAggregateRecord>,
}

/// A real EffectVM STARK proof attestation for one committed turn.
///
/// Produced by [`DreggRuntime::prove_turn`] via the canonical
/// `generate_effect_vm_trace` → `stark::prove` → `stark::verify` pipeline
/// (the same path `circuit/tests/integration_effect_vm_prove_verify.rs`
/// exercises). The proof is self-verified before the record is cached, so a
/// cached record is a genuinely sound attestation — never a placeholder.
#[derive(Clone, Debug)]
pub struct TurnProofRecord {
    /// Proof system identifier surfaced to the inspector (`"stark-effect-vm"`).
    pub kind: String,
    /// Canonical EffectVM public inputs (raw u32 felts) as produced by
    /// `generate_effect_vm_trace`. The inspector renders these directly.
    pub public_inputs: Vec<u32>,
    /// Serialized proof size in bytes (post `proof_to_bytes`). Surfaced for
    /// the proof-size stat; the full bytes are not retained.
    pub proof_size_bytes: usize,
    /// Net balance delta the proof attests (signed). Honest, derived from the
    /// proof's NET_DELTA public inputs via `extract_net_delta`.
    pub net_delta: i64,
    /// Trace row count (power-of-two-padded) the proof was generated over.
    pub trace_rows: usize,
    /// True iff PI[IS_AGENT_CELL] == 1.
    pub is_agent_cell: bool,
    /// True iff PI[IS_SOVEREIGN_CELL] == 1.
    pub is_sovereign_cell: bool,
}

/// A real Stage 7-γ.2 cross-cell bilateral *aggregate* attestation — the
/// GOLDEN tier.
///
/// Unlike [`TurnProofRecord`] (a single-turn EffectVM STARK whose γ.2 bilateral
/// accumulator roots are left as zero sentinels → executor-trusted cross-cell
/// boundary → SILVER), this record is produced by the canonical γ.2 aggregator
/// `dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle` over a real
/// two-cell scenario: alice's OUTGOING transfer and bob's INCOMING transfer,
/// both projected from the same canonical `Turn`'s bilateral schedule. The
/// outer STARK (`BilateralAggregationAir`) binds, in one algebraic pass, that
/// every per-cell PI's bilateral counts + roots equal the schedule the Turn
/// predicts — i.e. that alice's `OUTGOING_TRANSFER_ROOT` matches bob's
/// `INCOMING_TRANSFER_ROOT` for the same transfer.
///
/// The record is produced AND self-verified (`verify_aggregated_bundle`) before
/// being cached, so a present record is a genuinely sound cross-cell aggregate
/// — never a faked tier. The matched roots are read back out of the
/// proof-bound `outer_trace` (the trace the verifier binds to the proof's
/// `trace_commitment`), not recomputed independently.
#[derive(Clone, Debug)]
pub struct BilateralAggregateRecord {
    /// Aggregation AIR identifier (`dregg-bilateral-aggregation-v1`).
    pub kind: String,
    /// Outer STARK proof size in bytes (post `proof_to_bytes`).
    pub proof_size_bytes: usize,
    /// Number of participating cells in the bundle (2 for the transfer demo).
    pub n_cells: usize,
    /// `outer_pi[OUTER_BILATERAL_CONSISTENT]` — pinned to 1 by the AIR.
    pub bilateral_consistent: bool,
    /// Alice's (sender) OUTGOING_TRANSFER_ROOT, 4 felts as hex (32 hex chars).
    pub outgoing_transfer_root: String,
    /// Bob's (receiver) INCOMING_TRANSFER_ROOT, 4 felts as hex.
    pub incoming_transfer_root: String,
    /// The shared canonical `transfer_id` (4 felts as hex) that BOTH the
    /// sender's OUTGOING root and the receiver's INCOMING root are folded over.
    /// This — not byte-equality of the two roots — is the cross-cell quantity
    /// that binds the two sides: the outgoing and incoming accumulators use
    /// distinct domain-separation salts (`OTX2` vs `ITX2`) and distinct peer
    /// ids by design, so the roots are intentionally NOT byte-equal, but both
    /// absorb this same `derive_transfer_id(from, to, amount, nonce)`.
    pub shared_transfer_id: String,
    /// True iff this is a genuinely sound cross-cell bilateral binding:
    /// the outer aggregate STARK self-verified (`bilateral_consistent`), the
    /// Turn-derived schedule re-check passed (implied by
    /// `verify_aggregated_bundle` returning Ok), AND both transfer roots are
    /// present (non-zero — both sides participated in the same transfer). This
    /// is the honest GOLDEN signal.
    pub roots_matched: bool,
    /// Sender cell-id (hex32) — alice.
    pub sender_cell: String,
    /// Receiver cell-id (hex32) — bob.
    pub receiver_cell: String,
    /// Transfer amount the demo turn carries.
    pub amount: u64,
}

impl DreggRuntime {
    pub fn new() -> Self {
        let costs = ComputronCosts::default_costs();
        let mut executor = TurnExecutor::new(costs);
        executor.set_timestamp(1000);
        executor.set_block_height(0);

        // Deploy the default "test cipherclerk" factory so subsequent
        // `try_create_agent` calls can mint cells via the canonical
        // `Effect::CreateCellFromFactory` path. The factory's VK is
        // recorded here so the runtime can default to it when no
        // factory is specified by the caller — every cell minted by
        // the wasm runtime (other than genesis) carries a `Provenance`
        // record pointing at this VK, mirroring the
        // constructor-transparency behavior of the native node.
        let default_factory = default_cipherclerk_factory_descriptor();
        let default_factory_vk = executor.deploy_factory(default_factory);

        DreggRuntime {
            ledger: Ledger::new(),
            executor,
            nullifier_set: NullifierSet::new(),
            agents: Vec::new(),
            agent_names: HashMap::new(),
            intents: Vec::new(),
            revocation_channels: RevocationChannelSet::new(),
            conditionals: Vec::new(),
            current_height: 0,
            current_timestamp: 1000,
            receipts: Vec::new(),
            turns: Vec::new(),
            federations: Vec::new(),
            default_factory_vk,
            emitter: Emitter::new(),
            events: EventLog::new(),
            turn_proofs: HashMap::new(),
            bilateral_aggregate: None,
        }
    }

    /// Produce (and cache) a REAL Stage 7-γ.2 cross-cell bilateral *aggregate*
    /// proof — the GOLDEN tier — over a minimal honest two-cell transfer
    /// scenario, then self-verify it before caching.
    ///
    /// This is NOT a tier flip on the single-turn EffectVM proof (that path
    /// leaves the bilateral accumulator roots as zero sentinels → SILVER).
    /// Instead it constructs the canonical scenario the γ.2 aggregator is
    /// designed for:
    ///
    ///   * a Turn carrying `Effect::Transfer(alice → bob, amount)`;
    ///   * two per-cell `WitnessedReceipt`s — alice's (carrying her OUTGOING
    ///     transfer root) and bob's (carrying his INCOMING transfer root) —
    ///     each projected from the SAME canonical Turn's bilateral schedule
    ///     (`ExpectedBilateral::roots_for`), so the two roots coincide;
    ///   * the canonical aggregator
    ///     `dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle`,
    ///     which builds the outer `BilateralAggregationAir` trace, runs the
    ///     real outer STARK (FRI + Merkle + Fiat-Shamir), and emits an
    ///     `AggregatedBundle`.
    ///
    /// The bundle is then verified with `verify_aggregated_bundle` — a real
    /// outer-STARK verification plus the Turn-derived cross-cell schedule
    /// re-check — before the record is cached. A cached record is therefore a
    /// genuinely sound GOLDEN aggregate, never a faked tier.
    ///
    /// Idempotent: re-calling once cached is a cheap no-op.
    ///
    /// Returns `Err` only if proving or self-verification fails (which would
    /// indicate a substrate bug, not a sim gap) — in which case the inspector
    /// honestly leaves the aggregate absent (the single-turn SILVER proof
    /// stands).
    pub fn prove_bilateral_aggregate(&mut self) -> Result<(), String> {
        use dregg_circuit::bilateral_aggregation_air as ag;
        use dregg_circuit::effect_vm::pi as p;
        use dregg_circuit::field::BabyBear;
        use dregg_turn::aggregate_bilateral_prover::{
            prove_aggregated_bundle, verify_aggregated_bundle,
        };
        use dregg_turn::bilateral_schedule::{ExpectedBilateral, project_into_pi};

        if self.bilateral_aggregate.is_some() {
            return Ok(());
        }

        // Two distinct demo cells. These are dedicated bilateral-demo cell-ids
        // (not the runtime's live agent cells) — the aggregate proof is a
        // standalone γ.2 artifact over a canonical Turn, parallel to the
        // single-turn EffectVM proof rather than derived from a committed turn.
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);
        let amount: u64 = 100;
        let nonce: u64 = 1;

        // Canonical Turn: alice transfers `amount` to bob.
        let mut builder = TurnBuilder::new(alice, nonce);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, amount)
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        // Honestly fabricate each per-cell WitnessedReceipt from the SAME
        // canonical schedule (mirrors the aggregator's own happy-path test +
        // `dregg_verifier::bilateral_pair::fabricate_witnessed_receipt`, using
        // only public APIs). The PI's bilateral roots come straight from
        // `ExpectedBilateral::roots_for`, so alice's OUTGOING and bob's
        // INCOMING transfer roots match by construction — exactly what the
        // aggregator's CG-3 schedule-replay constraint enforces.
        let sched = ExpectedBilateral::from_turn(&turn);
        let (th, eg, _n, prev) = TurnExecutor::compute_turn_identity_pi(&turn);

        let fabricate = |cell: &CellId| -> WitnessedReceipt {
            let counts = sched.counts_for(cell);
            let roots = sched.roots_for(cell, turn.nonce);
            let mut pi_bb = vec![BabyBear::ZERO; p::BASE_COUNT];
            for i in 0..4 {
                pi_bb[p::TURN_HASH_BASE + i] = th[i];
                pi_bb[p::EFFECTS_HASH_GLOBAL_BASE + i] = eg[i];
                pi_bb[p::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
            }
            pi_bb[p::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
            project_into_pi(&mut pi_bb, &counts, &roots);
            pi_bb[p::IS_AGENT_CELL] = if cell == &turn.agent {
                BabyBear::new(1)
            } else {
                BabyBear::ZERO
            };
            let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();
            // Minimal scope-2 witness trace so the WR is a full scope-(2)
            // artifact (the aggregator requires scope-2 inputs).
            let trace = vec![vec![
                BabyBear::ZERO;
                dregg_circuit::effect_vm::EFFECT_VM_WIDTH
            ]];
            WitnessedReceipt::from_components(
                bilateral_demo_receipt(turn.agent),
                vec![],
                pi_u32,
                Some(trace.as_slice()),
            )
        };

        let entries = vec![(alice, fabricate(&alice)), (bob, fabricate(&bob))];

        // Real outer STARK over the aggregation AIR.
        let bundle = prove_aggregated_bundle(&turn, &entries)
            .map_err(|e| format!("bilateral aggregate proving failed: {e:?}"))?;
        // Real outer STARK verification + Turn-derived cross-cell re-check.
        verify_aggregated_bundle(&bundle)
            .map_err(|e| format!("bilateral aggregate self-verification failed: {e:?}"))?;

        // Read the matched roots out of the proof-bound outer trace. Row 0 is
        // alice (sender), row 1 is bob (receiver); the verifier has bound this
        // exact trace to the proof's `trace_commitment`, so these are the
        // roots the proof attests, not an independent recomputation.
        let root_hex = |row: &[u32], base: usize| -> (String, bool) {
            let mut s = String::with_capacity(32);
            let mut nz = false;
            for i in 0..4 {
                let v = row.get(base + i).copied().unwrap_or(0);
                if v != 0 {
                    nz = true;
                }
                s.push_str(&format!("{v:08x}"));
            }
            (s, nz)
        };
        let pi_out_base = ag::PI_BUFFER_BASE + p::OUTGOING_TRANSFER_ROOT_BASE;
        let pi_in_base = ag::PI_BUFFER_BASE + p::INCOMING_TRANSFER_ROOT_BASE;
        let (outgoing, out_nz) = root_hex(&bundle.outer_trace[0], pi_out_base);
        let (incoming, in_nz) = root_hex(&bundle.outer_trace[1], pi_in_base);

        let consistent = bundle
            .outer_pi
            .get(ag::OUTER_BILATERAL_CONSISTENT)
            .copied()
            .unwrap_or(0)
            == 1;

        // The shared transfer_id both sides fold over. The outgoing/incoming
        // accumulators are domain-separated (distinct salts) and absorb distinct
        // peer ids, so the roots are NOT byte-equal by design — the binding is
        // this shared id. The verified aggregate (consistent + the Turn-derived
        // schedule re-check inside `verify_aggregated_bundle`) is what proves
        // alice's OUTGOING and bob's INCOMING describe the SAME transfer.
        let transfer_id = sched
            .transfers
            .first()
            .map(|t| t.id(turn.nonce))
            .unwrap_or([BabyBear::ZERO; 4]);
        let shared_transfer_id: String = transfer_id
            .iter()
            .map(|f| format!("{:08x}", f.as_u32()))
            .collect();

        // Honest GOLDEN signal: verified aggregate + both sides present.
        let roots_matched = consistent && out_nz && in_nz;

        self.bilateral_aggregate = Some(BilateralAggregateRecord {
            kind: dregg_circuit::bilateral_aggregation_air::BilateralAggregationAir::AIR_NAME
                .to_string(),
            proof_size_bytes: bundle.outer_proof_bytes.len(),
            n_cells: bundle.participating_cells.len(),
            bilateral_consistent: consistent,
            outgoing_transfer_root: outgoing,
            incoming_transfer_root: incoming,
            shared_transfer_id,
            roots_matched,
            sender_cell: hex_encode_bytes(&alice.0),
            receiver_cell: hex_encode_bytes(&bob.0),
            amount,
        });
        Ok(())
    }

    /// Generate (and cache) a real EffectVM STARK proof for the committed turn
    /// identified by `turn_hash`.
    ///
    /// This is the canonical Effect VM prove path — the same
    /// `generate_effect_vm_trace` → `stark::prove` → `stark::verify` pipeline
    /// `circuit/tests/integration_effect_vm_prove_verify.rs` exercises. We
    /// project the committed turn's balance-affecting effects into circuit
    /// `Effect`s over a `CellState` whose initial balance covers the outgoing
    /// flow, prove the transition, self-verify it, and cache a
    /// [`TurnProofRecord`].
    ///
    /// Deliberately NOT called from the commit path: STARK proving is
    /// expensive in wasm, so callers (the `<dregg-proof>` inspector) invoke
    /// this lazily on first view. Idempotent — re-proving a cached turn is a
    /// no-op.
    ///
    /// Returns `Err` only when the turn is unknown or the proof fails its own
    /// verification (which would indicate a substrate bug, not a sim gap).
    pub fn prove_turn(&mut self, turn_hash: [u8; 32]) -> Result<(), String> {
        use dregg_circuit::{
            BabyBear, CellState, Effect as VmEffect, EffectVmAir, extract_net_delta,
            generate_effect_vm_trace,
            stark::{self, proof_to_bytes},
        };

        if self.turn_proofs.contains_key(&turn_hash) {
            return Ok(());
        }

        // Locate the committed turn (parallel `turns`/`receipts` vectors).
        let idx = self
            .receipts
            .iter()
            .position(|r| r.turn_hash == turn_hash)
            .ok_or_else(|| format!("no committed turn with hash {}", hex_encode(&turn_hash)))?;
        let turn = &self.turns[idx];

        // Project the turn's balance-affecting effects into circuit effects.
        // We walk the call forest and translate each `Transfer` into the
        // EffectVM `Transfer { amount, direction }` schema. Non-balance
        // effects are surfaced as `NoOp` rows so the trace still attests the
        // turn shape (row count) without claiming a balance change they don't
        // make. `direction = 1` (outgoing) when the actor cell is the sender.
        let actor_cell = turn.call_forest.roots.first().map(|t| t.action.target);
        let mut vm_effects: Vec<VmEffect> = Vec::new();
        let mut total_outgoing: u64 = 0;
        collect_vm_effects_from_forest(turn, actor_cell, &mut vm_effects, &mut total_outgoing);
        if vm_effects.is_empty() {
            vm_effects.push(VmEffect::NoOp);
        }

        // Initial CellState: a balance comfortably covering the outgoing flow
        // (the trace generator asserts no underflow). This makes the proof an
        // honest attestation of the turn's net delta + commitment transition.
        let init_balance = total_outgoing.saturating_add(1_000_000);
        let state = CellState::new(init_balance, 0);

        let (trace, pi) = generate_effect_vm_trace(&state, &vm_effects);
        let air = EffectVmAir::new(trace.len());

        // Real STARK prove.
        let proof = stark::prove(&air, &trace, &pi);

        // Self-verify before caching: a cached record is a genuinely sound
        // attestation. Also round-trips through serialization to size it.
        stark::verify(&air, &proof, &pi)
            .map_err(|e| format!("effect-vm proof failed self-verification: {e}"))?;
        let proof_size_bytes = proof_to_bytes(&proof).len();

        let net_delta = extract_net_delta(&pi).unwrap_or(0);
        let is_agent_cell = pi
            .get(dregg_circuit::effect_vm::pi::IS_AGENT_CELL)
            .map(|v| *v != BabyBear::ZERO)
            .unwrap_or(false);
        let is_sovereign_cell = pi
            .get(dregg_circuit::effect_vm::pi::IS_SOVEREIGN_CELL)
            .map(|v| *v != BabyBear::ZERO)
            .unwrap_or(false);

        let record = TurnProofRecord {
            kind: "stark-effect-vm".to_string(),
            public_inputs: pi.iter().map(|b| b.as_u32()).collect(),
            proof_size_bytes,
            net_delta,
            trace_rows: trace.len(),
            is_agent_cell,
            is_sovereign_cell,
        };
        self.turn_proofs.insert(turn_hash, record);
        Ok(())
    }

    /// Deploy a factory descriptor into the runtime's executor. The
    /// returned VK can be passed to
    /// [`try_create_agent_with_factory`] /
    /// [`mint_cell_from_genesis_with_factory`] to mint cells from this
    /// factory. Exposed so apps (and tests) can register their own
    /// factories alongside the runtime's default test-cipherclerk factory.
    pub fn deploy_factory(&mut self, descriptor: FactoryDescriptor) -> [u8; 32] {
        self.executor.deploy_factory(descriptor)
    }

    /// The VK of the runtime's default "test cipherclerk" factory — the
    /// factory used by `create_agent` / `create_cell` when no explicit
    /// factory is named. Exposed so the bindings can surface it to JS
    /// (e.g. for `verifyProvenance` against the canonical wasm-runtime
    /// factory set).
    pub fn default_factory_vk(&self) -> [u8; 32] {
        self.default_factory_vk
    }

    /// Create a new federation with `num_nodes` nodes named `<name>-<idx>`.
    ///
    /// Builds a real `dregg_federation::Federation` committee: each node gets a
    /// deterministic Ed25519 keypair derived from its name. The federation_id,
    /// threshold (n − ⌊n/3⌋), and member pubkeys are all canonical. Returns
    /// the new federation's index.
    pub fn create_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        use dregg_federation::{Federation, LocalSeat};
        use dregg_types::{PublicKey as FedPublicKey, SigningKey};

        let mut members: Vec<FedPublicKey> = Vec::with_capacity(num_nodes);
        let mut local_sk: Option<SigningKey> = None;

        for i in 0..num_nodes {
            // Deterministic seed: BLAKE3(name || "-" || i)
            let mut hasher = blake3::Hasher::new_derive_key("dregg-wasm-fed-node-key-v1");
            hasher.update(name.as_bytes());
            hasher.update(b"-");
            hasher.update(&(i as u64).to_le_bytes());
            let seed: [u8; 32] = *hasher.finalize().as_bytes();
            let sk = SigningKey::from_bytes(&seed);
            let pk = sk.public_key();
            if i == 0 {
                local_sk = Some(sk);
            }
            members.push(pk);
        }

        // BFT threshold: n − ⌊n/3⌋ (same formula as the deleted node.rs).
        let threshold = (num_nodes - num_nodes / 3) as u32;
        // `LocalSeat::bls_secret` is gated on `dregg-federation/runtime`; that
        // feature is unified-on across the workspace (e.g. `node/` enables
        // it), so the field is always present in any cargo invocation that
        // also builds dregg-wasm.
        let local_seat = local_sk.map(|sk| LocalSeat {
            index: 0,
            signing_key: sk,
            bls_secret: None,
        });
        let federation = Federation::from_committee(members, 0, threshold, None, local_seat);

        let idx = self.federations.len();
        self.federations.push(SimFederation {
            name: name.to_string(),
            federation,
            node_count: num_nodes,
            pending_revocations: Vec::new(),
            revoked_set: std::collections::HashSet::new(),
            height: 0,
            view: 0,
            finalized_blocks: Vec::new(),
            submitted_token_ids: Vec::new(),
        });
        idx
    }

    /// Submit a batch of revocation events and immediately run a consensus
    /// round. Returns the finalized block hash; `None` if there are no
    /// pending revocations to finalize.
    ///
    /// The block hash is BLAKE3(height || view || sorted token_ids) — a
    /// deterministic function of the committed state, not a network round-trip.
    /// The produced `AttestedRoot` (accessible via `get_federation_state`)
    /// carries the real `federation_id` and `threshold` from the canonical
    /// `Federation` committee.
    pub fn propose_block(&mut self, fed_index: usize, token_ids: Vec<String>) -> Option<[u8; 32]> {
        // Capture the ledger's real Merkle root before taking the mutable
        // federation borrow. A consensus round finalizes revocations only (no
        // ledger turns), so this root is both the pre- and post-state root for
        // the block — a genuine value, not [0u8; 32].
        let state_root = self.ledger.root();
        let fed = self.federations.get_mut(fed_index)?;
        if token_ids.is_empty() {
            return None;
        }
        for tid in &token_ids {
            fed.pending_revocations.push(tid.clone());
            fed.revoked_set.insert(tid.clone());
        }
        fed.submitted_token_ids.push(token_ids);
        fed.view += 1;
        fed.height += 1;

        // Real predecessor link: the prior finalized block's hash (linear
        // height-(N-1) predecessor). Genesis-most block links to [0u8; 32].
        // Folded into the digest below so the chain is cryptographically linked
        // (mirrors `RevocationBlock::compute_hash`).
        let prev_hash = fed
            .finalized_blocks
            .last()
            .map(|b| b.block_hash)
            .unwrap_or([0u8; 32]);

        // Block hash = BLAKE3(height || view || prev_hash || each pending token id).
        let mut hasher = blake3::Hasher::new_derive_key("dregg-wasm-consensus-block-v1");
        hasher.update(&fed.height.to_le_bytes());
        hasher.update(&fed.view.to_le_bytes());
        hasher.update(&prev_hash);
        for tid in &fed.pending_revocations {
            hasher.update(tid.as_bytes());
        }
        let block_hash: [u8; 32] = *hasher.finalize().as_bytes();
        let qc_threshold = fed.federation.threshold() as usize;
        let qc_votes = fed.node_count;
        let revoked = std::mem::take(&mut fed.pending_revocations);
        fed.finalized_blocks.push(FinalizedBlock {
            height: fed.height,
            view: fed.view,
            block_hash,
            prev_hash,
            revoked_token_ids: revoked,
            qc_votes,
            qc_threshold,
            pre_state_root: state_root,
            post_state_root: state_root,
        });
        Some(block_hash)
    }

    /// Run an additional consensus round (e.g. to flush any pending events
    /// submitted out-of-band). Returns the finalized block hash + height +
    /// view + event count, or `None` if there are no pending revocations.
    pub fn simulate_consensus_round(&mut self, fed_index: usize) -> Option<ConsensusRoundResult> {
        // Real ledger Merkle root at block time (see `propose_block`).
        let state_root = self.ledger.root();
        let fed = self.federations.get_mut(fed_index)?;
        if fed.pending_revocations.is_empty() {
            return None;
        }
        fed.view += 1;
        fed.height += 1;
        let num_events = fed.pending_revocations.len();

        // Real predecessor link (see `propose_block`).
        let prev_hash = fed
            .finalized_blocks
            .last()
            .map(|b| b.block_hash)
            .unwrap_or([0u8; 32]);

        let mut hasher = blake3::Hasher::new_derive_key("dregg-wasm-consensus-block-v1");
        hasher.update(&fed.height.to_le_bytes());
        hasher.update(&fed.view.to_le_bytes());
        hasher.update(&prev_hash);
        for tid in &fed.pending_revocations {
            hasher.update(tid.as_bytes());
        }
        let block_hash: [u8; 32] = *hasher.finalize().as_bytes();
        let qc_threshold = fed.federation.threshold() as usize;
        // Simulated quorum: all nodes vote (wasm doesn't run BLS pipeline).
        let qc_votes = fed.node_count;
        let revoked = std::mem::take(&mut fed.pending_revocations);
        fed.finalized_blocks.push(FinalizedBlock {
            height: fed.height,
            view: fed.view,
            block_hash,
            prev_hash,
            revoked_token_ids: revoked,
            qc_votes,
            qc_threshold,
            pre_state_root: state_root,
            post_state_root: state_root,
        });
        Some(ConsensusRoundResult {
            block_hash: hex_encode_bytes(&block_hash),
            height: fed.height,
            view: fed.view,
            num_events,
            proposer: 0,
            qc_threshold,
            qc_votes,
        })
    }

    /// Create an agent with a name. The Ed25519 key is derived deterministically
    /// from (name, idx) so a reproducible browser session can replay an
    /// identical history. The derivation is BLAKE3-of-name-and-index for the
    /// seed; the rest of the agent — public key, cell id, signing — comes
    /// from `dregg_sdk::AgentCipherclerk`, the same cipherclerk implementation used by native callers.
    /// This is not a sim-shaped reimplementation; the cipherclerk IS the canonical
    /// implementation, just constructed with a deterministic seed for
    /// reproducibility.
    ///
    /// # Cell birth
    ///
    /// The **first** agent (idx 0) is the genesis agent: its cell is inserted
    /// directly into the ledger. This mirrors `dregg_node::genesis`'s
    /// `initial_cells` field — there must be at least one cell before any turn
    /// can run, because a turn is always issued by some existing cell.
    ///
    /// **Subsequent** agents are minted from genesis via a real turn that emits
    /// `Effect::CreateCell` (and, if `initial_balance > 0`, `Effect::Transfer`
    /// from genesis). The executor requires `CreateCell` to have `balance: 0`
    /// (see `turn::executor::Effect::CreateCell` arm), so we always pass 0 and
    /// fund the new cell with a follow-up Transfer effect within the same turn.
    pub fn create_agent(&mut self, name: &str, initial_balance: u64) -> usize {
        self.try_create_agent(name, initial_balance)
            .unwrap_or_else(|e| panic!("create_agent failed: {e}"))
    }

    /// Fallible cell-creation path. Same as [`create_agent`] but returns a
    /// String error rather than panicking, so wasm bindings can surface the
    /// error to JS rather than triggering an `unreachable` trap.
    ///
    /// Uses the runtime's default test-cipherclerk factory. To mint from a
    /// specific factory descriptor (e.g. an app-deployed one), use
    /// [`Self::try_create_agent_with_factory`].
    pub fn try_create_agent(&mut self, name: &str, initial_balance: u64) -> Result<usize, String> {
        let factory_vk = self.default_factory_vk;
        self.try_create_agent_with_factory(name, initial_balance, &factory_vk)
    }

    /// Like [`try_create_agent`] but mints the new cell from an explicit
    /// `factory_vk`. The factory must have been deployed previously via
    /// [`Self::deploy_factory`].
    ///
    /// **Genesis (idx 0)** is still a cell birth-by-fiat: there is no
    /// signer yet, so the executor cannot accept a turn. Genesis is the
    /// canonical bootstrap; the factory binding only governs subsequent
    /// agents. Genesis's provenance is `Provenance::genesis` per
    /// `dregg_cell::factory`.
    ///
    /// **Subsequent agents** are minted via
    /// `Effect::CreateCellFromFactory` — the canonical constructor
    /// transparency path. The new cell's provenance points at the
    /// factory VK, so a downstream `verify_provenance` against the
    /// runtime's default factory set will return true.
    pub fn try_create_agent_with_factory(
        &mut self,
        name: &str,
        initial_balance: u64,
        factory_vk: &[u8; 32],
    ) -> Result<usize, String> {
        let idx = self.agents.len();

        // Deterministic Ed25519 seed.
        let mut hasher = blake3::Hasher::new_derive_key("dregg-wasm-agent-key");
        hasher.update(name.as_bytes());
        hasher.update(&(idx as u64).to_le_bytes());
        let key_hash = hasher.finalize();
        let seed_bytes: [u8; 32] = *key_hash.as_bytes();

        // CommitmentId derivation needs the raw seed; compute it before the
        // seed is moved into the cipherclerk (where it's zeroized).
        let commitment_id = CommitmentId::derive(&seed_bytes, "dregg-wasm-commitment");

        let cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed_bytes));
        let public_key = cclerk.public_key().0;
        let cell_id = cclerk.cell_id(WASM_SIM_DOMAIN);
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();

        if idx == 0 {
            // Genesis: insert the root cell directly. This is the same pattern
            // dregg-node uses (see node/src/genesis.rs::initial_cells).
            // Genesis cannot itself be born from a factory because no signer
            // exists yet — this is the canonical "Provenance::genesis"
            // bootstrap point.
            let cell = Cell::with_balance(public_key, token_id, initial_balance);
            self.ledger.insert_cell(cell).unwrap();
        } else {
            // Subsequent agents: mint the cell via a real turn issued by the
            // genesis agent (agent 0), through the canonical
            // `Effect::CreateCellFromFactory` path. The factory descriptor's
            // `default_mode` determines whether the new cell is Hosted or
            // Sovereign; the runtime's default factory uses Hosted.
            //
            // We look up the factory's required mode from the registry so
            // the params match what `validate_creation` expects — passing
            // a mismatched mode would trip `FactoryError::ModeMismatch`.
            let factory_mode = self
                .executor
                .factory_registry
                .borrow()
                .get(factory_vk)
                .ok_or_else(|| {
                    format!(
                        "unknown factory VK {} — call deploy_factory first",
                        hex_encode_bytes(factory_vk)
                    )
                })?
                .default_mode
                .clone();

            let params = FactoryCreationParams {
                mode: factory_mode,
                program_vk: None,
                initial_fields: Vec::new(),
                initial_caps: Vec::new(),
                owner_pubkey: public_key,
            };

            let mut effects = vec![Effect::CreateCellFromFactory {
                factory_vk: *factory_vk,
                owner_pubkey: public_key,
                token_id,
                params,
            }];
            if initial_balance > 0 {
                effects.push(Effect::Transfer {
                    from: self.agents[0].cell_id,
                    to: cell_id,
                    amount: initial_balance,
                });
            }

            // Execute the turn signed by genesis. Fees match
            // `Effect::CreateCell` (the executor's cost table maps both
            // variants to `EFFECT_CREATE_CELL`), so `GENESIS_MINT_FEE`
            // covers either path.
            match self.execute_turn_for_agent(0, effects, GENESIS_MINT_FEE) {
                TurnResult::Committed { .. } => {}
                other => {
                    return Err(format!(
                        "minting cell for '{name}' via Effect::CreateCellFromFactory failed: {:?}",
                        other
                    ));
                }
            }
        }

        // Build the canonical `PeerExchange` for this agent using the cipherclerk's
        // real Ed25519 signing key. `AgentCipherclerk::peer_exchange(domain)` is
        // the SDK's factory — same code path the native API uses — so we do
        // not need a public signing-key accessor on the cipherclerk.
        let peer_exchange = cclerk.peer_exchange(WASM_SIM_DOMAIN);

        let agent = SimAgent {
            name: name.to_string(),
            cclerk,
            public_key,
            cell_id,
            held_tokens: Vec::new(),
            commitment_id,
            token_counter: 0,
            peer_exchange,
            held_notes: Vec::new(),
        };

        self.agent_names.insert(name.to_string(), idx);
        self.agents.push(agent);
        Ok(idx)
    }

    /// Mint a cell from a raw public key (used by the wasm `create_cell` JS
    /// binding). Uses the canonical factory-turn path: a turn signed by the
    /// genesis agent that emits `Effect::CreateCellFromFactory` against the
    /// runtime's default test-cipherclerk factory (plus an optional
    /// `Effect::Transfer` to fund the new cell).
    ///
    /// Returns the new cell's `CellId`. Requires at least one prior agent
    /// (the genesis agent, idx 0) to exist as the signer.
    pub fn mint_cell_from_genesis(
        &mut self,
        owner_public_key: [u8; 32],
        initial_balance: u64,
    ) -> Result<CellId, String> {
        let factory_vk = self.default_factory_vk;
        self.mint_cell_from_genesis_with_factory(owner_public_key, initial_balance, &factory_vk)
    }

    /// Like [`Self::mint_cell_from_genesis`] but allows specifying an
    /// explicit factory VK (which must have been deployed via
    /// [`Self::deploy_factory`]).
    pub fn mint_cell_from_genesis_with_factory(
        &mut self,
        owner_public_key: [u8; 32],
        initial_balance: u64,
        factory_vk: &[u8; 32],
    ) -> Result<CellId, String> {
        if self.agents.is_empty() {
            return Err(
                "wasm runtime: cannot mint cell — no genesis agent yet (call create_agent first)"
                    .to_string(),
            );
        }
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();
        let new_cell_id = CellId::derive_raw(&owner_public_key, &token_id);

        let factory_mode = self
            .executor
            .factory_registry
            .borrow()
            .get(factory_vk)
            .ok_or_else(|| {
                format!(
                    "unknown factory VK {} — call deploy_factory first",
                    hex_encode_bytes(factory_vk)
                )
            })?
            .default_mode
            .clone();

        let params = FactoryCreationParams {
            mode: factory_mode,
            program_vk: None,
            initial_fields: Vec::new(),
            initial_caps: Vec::new(),
            owner_pubkey: owner_public_key,
        };

        let mut effects = vec![Effect::CreateCellFromFactory {
            factory_vk: *factory_vk,
            owner_pubkey: owner_public_key,
            token_id,
            params,
        }];
        if initial_balance > 0 {
            effects.push(Effect::Transfer {
                from: self.agents[0].cell_id,
                to: new_cell_id,
                amount: initial_balance,
            });
        }

        match self.execute_turn_for_agent(0, effects, GENESIS_MINT_FEE) {
            TurnResult::Committed { .. } => Ok(new_cell_id),
            other => Err(format!(
                "wasm runtime: mint_cell_from_genesis_with_factory failed: {:?}",
                other
            )),
        }
    }

    /// Mint a token for an agent (adds to their held_tokens for intent matching).
    pub fn agent_mint_token(
        &mut self,
        agent_idx: usize,
        resource: &str,
        actions: &[String],
        expiry: Option<u64>,
    ) -> usize {
        let agent = &mut self.agents[agent_idx];
        agent.token_counter += 1;
        let token_id = format!("tok_{}_{}", agent.name, agent.token_counter);

        let held = HeldCapability {
            token_id: token_id.clone(),
            actions: actions.to_vec(),
            resource: resource.to_string(),
            app_id: None,
            service: None,
            user_id: None,
            features: Vec::new(),
            oauth_provider: None,
            expiry,
            budget: None,
            sensitivity: Sensitivity::Normal,
        };

        let idx = agent.held_tokens.len();
        agent.held_tokens.push(held);

        // Also mint a REAL macaroon-backed `HeldToken` into the cipherclerk so
        // the canonical `AgentCipherclerk::tokens()` surface (what
        // `get_agent_tokens` / `<dregg-cipherclerk>` #36 reads) reflects this
        // grant — not just the intent-matcher `HeldCapability` shape. The root
        // key is derived deterministically from the cipherclerk's signing key
        // (no random material, reproducible) via the same `derive_symmetric_key`
        // path `create_note` uses. The `resource` is used as the macaroon
        // service name so the two views correlate.
        let root_key = agent
            .cclerk
            .derive_symmetric_key(&format!("dregg-wasm-token-root-{token_id}"));
        let _ = agent.cclerk.mint_token(&root_key, resource);

        idx
    }

    /// Grant a capability from one agent's cell to another agent's cell.
    pub fn grant_capability(
        &mut self,
        from_agent: usize,
        to_agent: usize,
        permissions: AuthRequired,
    ) -> Option<u32> {
        let from_cell_id = self.agents[from_agent].cell_id;
        let to_cell_id = self.agents[to_agent].cell_id;

        // Grant capability on the target cell (to_agent gets cap pointing to from_agent).
        let to_cell = self.ledger.get_mut(&to_cell_id)?;
        to_cell.capabilities.grant(from_cell_id, permissions)
    }

    /// Build and execute a turn using the TurnBuilder API.
    ///
    /// The legacy `TurnBuilder::action()` API stamps every action with
    /// `Authorization::Unchecked`, which gets rejected by cells with default
    /// (`Signature`-required) permissions. We post-process the built turn,
    /// walking the call forest and replacing every `Unchecked` authorization
    /// with a real Ed25519 signature from the agent's signing key. The
    /// TurnExecutor verifies these signatures against the cell's stored
    /// public key — the same code path real cipherclerks exercise.
    pub fn execute_turn_for_agent(
        &mut self,
        agent_idx: usize,
        effects: Vec<Effect>,
        fee: u64,
    ) -> TurnResult {
        let cell_id = self.agents[agent_idx].cell_id;

        // Get current nonce.
        let nonce = self
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);

        {
            let mut ab = ActionBuilder::new_unchecked_for_tests(cell_id, "execute", cell_id);
            for effect in effects {
                ab = ab.effect(effect);
            }
            builder.add_action(ab.build());
        }

        let mut turn = builder.build();

        // Receipt chaining: every turn after the first from a given agent must
        // reference the previous turn's receipt hash. The executor tracks the
        // per-agent head; reuse it so callers don't have to.
        if turn.previous_receipt_hash.is_none() {
            if let Some(prev) = self.executor.get_last_receipt_hash(&cell_id) {
                turn.previous_receipt_hash = Some(prev);
            }
        }

        // Sign every Unchecked action with the agent's cipherclerk — same code
        // path native callers exercise via `AgentCipherclerk::sign_action`.
        let federation_id = self.executor.local_federation_id;
        let cclerk = &self.agents[agent_idx].cclerk;
        sign_call_forest(&mut turn, cclerk, &federation_id);

        let result = self.executor.execute(&turn, &mut self.ledger);

        // Wire Emitter (STARBRIDGE §4.4 Task #30) into the three result paths
        // that the Studio <dregg-activity> live feed cares about. Other 6 event
        // kinds (Authorization etc) require deeper hooks into TurnExecutor/apply
        // (future work); here we at least anchor every turn with lifecycle.
        // All construction uses canonical dregg_observability types (substrate).
        {
            let (seq, ts) = self.emitter.next_envelope_seed();
            let env = EventEnvelope::new(seq, ts)
                .with_turn_hash(&turn.hash())
                .with_actor(&cell_id);
            match &result {
                TurnResult::Committed { receipt, .. } => {
                    self.receipts.push(receipt.clone());
                    self.turns.push(turn.clone());
                    let payload = TurnLifecyclePayload::Committed {
                        receipt_hash: hex32(&receipt.turn_hash),
                        forest_hash: hex32(&receipt.forest_hash),
                        pre_state_hash: hex32(&receipt.pre_state_hash),
                        post_state_hash: hex32(&receipt.post_state_hash),
                        effects_hash: hex32(&receipt.effects_hash),
                        timestamp: receipt.timestamp,
                        action_count: receipt.action_count,
                        computrons_used: receipt.computrons_used,
                        finality: format!("{:?}", receipt.finality),
                    };
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                TurnResult::Rejected { reason, at_action } => {
                    let payload = TurnLifecyclePayload::Rejected {
                        reason: format!("{}", reason),
                        at_action: at_action.clone(),
                    };
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                TurnResult::Expired => {
                    let payload = TurnLifecyclePayload::Expired;
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                _ => { /* Pending: no lifecycle emit yet */ }
            }
            self.events = self.emitter.snapshot();
        }

        result
    }

    /// Create a note for an agent. Randomness derives deterministically from
    /// the cipherclerk (so the same agent + same value yields the same commitment
    /// for reproducibility), via `AgentCipherclerk::derive_symmetric_key` rather
    /// than exposing raw signing material.
    pub fn create_note(&mut self, agent_idx: usize, value: u64, asset_type: u64) -> NoteCommitment {
        let agent = &mut self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let randomness = agent
            .cclerk
            .derive_symmetric_key("dregg-wasm-note-randomness");
        let note = Note::with_randomness(agent.public_key, fields, randomness);
        let commitment = note.commitment();
        // Index the minted note so `get_notes` (and `dregg://note/*` lookups)
        // resolve it. We dedupe by commitment because `create_note` is
        // deterministic (same agent + value + asset_type ⇒ same note), so a
        // repeated lab-mode "create" must not stack duplicate entries.
        if !agent
            .held_notes
            .iter()
            .any(|hn| hn.note.commitment() == commitment)
        {
            agent.held_notes.push(HeldNote {
                note,
                nullifier: None,
            });
        }
        commitment
    }

    /// Spend a note (reveal nullifier). Spending key derived from the cipherclerk
    /// the same way `create_note` derives randomness — same deterministic
    /// key so the nullifier is reproducible.
    pub fn spend_note(
        &mut self,
        agent_idx: usize,
        value: u64,
        asset_type: u64,
    ) -> Result<Nullifier, String> {
        let agent = &mut self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let randomness = agent
            .cclerk
            .derive_symmetric_key("dregg-wasm-note-randomness");
        let spending = agent
            .cclerk
            .derive_symmetric_key("dregg-wasm-note-spending");
        let note = Note::with_randomness(agent.public_key, fields, randomness);
        let commitment = note.commitment();
        let nullifier = note.nullifier(&spending);
        self.nullifier_set
            .insert(nullifier)
            .map_err(|e| e.to_string())?;
        // Reflect the spend in the agent's note index so `get_notes` reports the
        // note as spent (with its revealed nullifier). If the note was never
        // surfaced via `create_note` (spend-without-prior-create in the sim),
        // index it now so the spent note is still visible to the inspector.
        match agent
            .held_notes
            .iter_mut()
            .find(|hn| hn.note.commitment() == commitment)
        {
            Some(hn) => hn.nullifier = Some(nullifier),
            None => agent.held_notes.push(HeldNote {
                note,
                nullifier: Some(nullifier),
            }),
        }
        Ok(nullifier)
    }

    // create_federation / propose_block / simulate_consensus_round are
    // defined above (alongside the federations field initializer) and
    // delegate to the real `dregg_federation::Federation` API.

    /// Create an intent.
    pub fn create_intent(
        &mut self,
        agent_idx: usize,
        kind: IntentKind,
        actions: Vec<ActionPattern>,
        constraints: Vec<Constraint>,
        resource_pattern: Option<String>,
        expiry: u64,
    ) -> [u8; 32] {
        let agent = &self.agents[agent_idx];
        let spec = MatchSpec {
            actions,
            constraints,
            min_budget: None,
            resource_pattern,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(kind, spec, agent.commitment_id, expiry, None);
        let id = intent.id;
        self.intents.push(intent);
        id
    }

    /// Match an intent against an agent's held tokens.
    pub fn match_intent_for_agent(&self, intent_idx: usize, agent_idx: usize) -> MatchResult {
        let intent = &self.intents[intent_idx];
        let agent = &self.agents[agent_idx];
        match_intent(
            intent,
            &agent.held_tokens,
            agent.commitment_id,
            VerificationMode::Trusted,
            self.current_timestamp as u64,
        )
    }

    /// Submit a conditional turn.
    pub fn submit_conditional(
        &mut self,
        agent_idx: usize,
        effects: Vec<Effect>,
        fee: u64,
        condition: ProofCondition,
        timeout_blocks: u64,
    ) -> [u8; 32] {
        let agent = &self.agents[agent_idx];
        let cell_id = agent.cell_id;
        let nonce = self
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);
        {
            let mut ab = ActionBuilder::new_unchecked_for_tests(cell_id, "conditional", cell_id);
            for effect in effects {
                ab = ab.effect(effect);
            }
            builder.add_action(ab.build());
        }
        let turn = builder.build();
        let turn_hash = turn.hash();

        let deposit_amount = dregg_turn::compute_conditional_deposit(
            self.current_height + timeout_blocks,
            self.current_height,
        );
        let conditional = ConditionalTurn {
            turn,
            condition,
            timeout_height: self.current_height + timeout_blocks,
            submitted_at: self.current_height,
            deposit_amount,
        };

        self.conditionals.push(PendingConditional {
            id: turn_hash,
            conditional,
            submitted_height: self.current_height,
        });

        turn_hash
    }

    /// Advance the block height (for timeout simulation).
    pub fn advance_height(&mut self, blocks: u64) {
        self.current_height += blocks;
        self.current_timestamp += (blocks * 12) as i64; // ~12s per block
        self.executor.set_block_height(self.current_height);
        self.executor.set_timestamp(self.current_timestamp);
    }

    /// Create a revocation channel.
    pub fn create_revocation_channel(&mut self, revoker_agent: usize) -> [u8; 32] {
        let revoker_cell_id = self.agents[revoker_agent].cell_id;
        let nonce = self.revocation_channels.len() as u64;
        let channel = RevocationChannel::new(revoker_cell_id, nonce, self.current_height);
        let channel_id = channel.channel_id;
        self.revocation_channels.register(channel).unwrap();
        channel_id
    }

    /// Trip (revoke) a channel.
    pub fn trip_channel(
        &mut self,
        channel_id: &[u8; 32],
        revoker_agent: usize,
        reason: [u8; 32],
    ) -> bool {
        let revoker_cell_id = self.agents[revoker_agent].cell_id;
        self.revocation_channels
            .trip_channel(channel_id, &revoker_cell_id, reason, self.current_height)
            .is_ok()
    }

    /// Check if a channel is active.
    pub fn is_channel_active(&self, channel_id: &[u8; 32]) -> bool {
        self.revocation_channels
            .get(channel_id)
            .map(|ch| ch.state.is_active())
            .unwrap_or(false)
    }

    // =========================================================================
    // PeerExchange (canonical sovereign-cell peer protocol)
    //
    // These methods are thin facades over `dregg_cell::PeerExchange` stored on
    // each `SimAgent`. The bindings layer doesn't reach into the agent's
    // `peer_exchange` field directly — it goes through these. All cryptography
    // and protocol logic lives inside the canonical `PeerExchange` type, no
    // reimplementation here.
    // =========================================================================

    /// Register a peer cell with an initial commitment from the agent's POV.
    /// Required before `verify_peer_transition` will accept transitions from
    /// that peer (canonical `PeerExchange::register_peer` semantics — the
    /// initial commitment is the "introduction" the two peers must agree on
    /// out-of-band).
    pub fn agent_register_peer(
        &mut self,
        agent_idx: usize,
        peer_cell_id: CellId,
        initial_commitment: [u8; 32],
    ) -> Result<(), String> {
        let agent = self
            .agents
            .get_mut(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        agent
            .peer_exchange
            .register_peer(peer_cell_id, initial_commitment);
        Ok(())
    }

    /// Sign and package a state transition from this agent's exchange session.
    /// Returns the postcard-encoded `PeerStateTransition` bytes — the compact
    /// signed blob meant for the "Discord paste" UX. Mutates the agent's
    /// internal sequence counter.
    pub fn agent_create_peer_transition(
        &mut self,
        agent_idx: usize,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
    ) -> Result<Vec<u8>, String> {
        // PeerExchange's `create_transition` reads the system clock via
        // `SystemTime::now()`, which panics on wasm32-unknown-unknown. We
        // use the explicit-timestamp variant and feed it the runtime's
        // canonical clock (`current_timestamp`, in seconds — matching the
        // `i64` shape PeerExchange already uses).
        let ts = self.current_timestamp;
        let agent = self
            .agents
            .get_mut(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        let transition = agent.peer_exchange.create_transition_at(
            old_commitment,
            new_commitment,
            effects_hash,
            ts,
        );
        postcard::to_stdvec(&transition)
            .map_err(|e| format!("failed to encode peer transition: {e}"))
    }

    /// Verify a transition from a peer (postcard-decoded inside). On success
    /// the agent's `peer_views` is updated to the new commitment + sequence
    /// and the updated view is returned. On failure returns the typed
    /// variant name (e.g. `"InvalidSignature"`) alongside the human-readable
    /// display so JS can switch on the variant for UX.
    pub fn agent_verify_peer_transition(
        &mut self,
        agent_idx: usize,
        transition_bytes: &[u8],
        peer_pubkey: [u8; 32],
    ) -> Result<dregg_cell::PeerCellView, (String, String)> {
        let agent = self.agents.get_mut(agent_idx).ok_or_else(|| {
            (
                "InvalidAgent".to_string(),
                format!("invalid agent index: {agent_idx}"),
            )
        })?;
        let transition: dregg_cell::PeerStateTransition = postcard::from_bytes(transition_bytes)
            .map_err(|e| {
                (
                    "DecodeError".to_string(),
                    format!("failed to decode peer transition: {e}"),
                )
            })?;
        let peer_cell_id = transition.cell_id;
        agent
            .peer_exchange
            .verify_transition(&transition, &peer_pubkey)
            .map_err(|e| (peer_exchange_error_variant(&e), e.to_string()))?;
        Ok(agent
            .peer_exchange
            .peer_view(&peer_cell_id)
            .cloned()
            .expect("verify_transition succeeded; view must exist"))
    }

    /// Get the agent's current view of a peer cell (commitment + sequence +
    /// last-updated). Returns `None` if not registered.
    pub fn agent_get_peer_view(
        &self,
        agent_idx: usize,
        peer_cell_id: CellId,
    ) -> Result<Option<dregg_cell::PeerCellView>, String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.peer_view(&peer_cell_id).cloned())
    }

    /// List all peer cell ids the agent has registered.
    pub fn agent_list_peers(&self, agent_idx: usize) -> Result<Vec<CellId>, String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.registered_peers().collect())
    }

    /// Get this agent's PeerExchange public key. Equivalent to the cipherclerk's
    /// Ed25519 verifying key — sourced from the exchange so the binding is
    /// self-contained.
    pub fn agent_peer_pubkey(&self, agent_idx: usize) -> Result<[u8; 32], String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.public_key())
    }

    /// Read the current canonical state-commitment of a cell. Convenience
    /// for the peer-exchange flow: a sender needs the post-state commitment
    /// after running a turn, and the receiver needs an initial commitment
    /// to register the peer with. Goes through `Cell::state_commitment()`,
    /// the canonical sovereign-witness commitment function.
    pub fn cell_state_commitment(&self, cell_id: &CellId) -> Option<[u8; 32]> {
        self.ledger.get(cell_id).map(|c| c.state_commitment())
    }

    // =========================================================================
    // Starbridge-app cell surface: multi-agent turns + Authorization::Custom.
    //
    // These methods are what makes the subscription `grant` flow and the
    // governed-namespace propose/vote/commit flow REAL in-browser. They drive
    // the canonical `TurnExecutor` against an app cell whose canonical
    // cell-program is installed via `app_programs` (which mirrors the
    // starbridge-app crates' program values; those crates can't be a wasm dep
    // because they pull axum/tokio). Every turn is a real signed turn; the
    // commit turn is a real `Authorization::Custom` discharged by a real
    // Ed25519 threshold verifier.
    // =========================================================================

    /// Install a canonical app cell-program + initial state on a cell, opening
    /// permissions so that turns from agents other than the cell's owner apply
    /// (the slot-caveat cell-program is the load-bearing enforcement; this
    /// mirrors the integration tests' `install_program` + relaxed permissions).
    ///
    /// `program_kind` ∈ {"subscription", "governed-namespace"}. The cell must
    /// already exist in the ledger (mint it via `mint_cell_from_genesis` first).
    pub fn install_app_program(
        &mut self,
        cell_id: &CellId,
        program: dregg_cell::CellProgram,
        initial_state: dregg_cell::CellState,
    ) -> Result<(), String> {
        let cell = self
            .ledger
            .get_mut(cell_id)
            .ok_or_else(|| format!("cell {} not found in ledger", hex_encode_bytes(&cell_id.0)))?;
        cell.program = program;
        cell.permissions = app_programs::open_permissions();
        cell.state = initial_state;
        Ok(())
    }

    /// Grant the acting agent's cell a capability to *reach* `target_cell`.
    /// The executor's cross-cell reachability check requires the actor cell to
    /// hold a `CapabilityRef` to any non-self target it acts on. A publisher /
    /// consumer / committee member acting on an app cell they don't own needs
    /// this cap inserted first (the integration tests sidestep it by having the
    /// actor BE the cell owner; the in-browser multi-agent flow grants it
    /// explicitly). `AuthRequired::None` matches the open target permissions.
    pub fn grant_reach_capability(
        &mut self,
        agent_idx: usize,
        target_cell: CellId,
    ) -> Result<u32, String> {
        let actor_cell = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?
            .cell_id;
        let cell = self
            .ledger
            .get_mut(&actor_cell)
            .ok_or_else(|| "actor cell not found in ledger".to_string())?;
        cell.capabilities
            .grant(target_cell, AuthRequired::None)
            .ok_or_else(|| "capability slot counter overflow".to_string())
    }

    /// Read a single 32-byte slot of a cell's state.
    pub fn cell_field(&self, cell_id: &CellId, index: usize) -> Option<[u8; 32]> {
        self.ledger
            .get(cell_id)
            .and_then(|c| c.state.fields.get(index).copied())
    }

    /// Build + execute a real signed turn where `agent_idx` is the actor/signer
    /// and the action targets a DIFFERENT cell (`target_cell`) using an explicit
    /// `method` symbol. This is the multi-agent path: a publisher (agent B) can
    /// drive a `publish` turn against a topic cell owned by the publisher (agent
    /// A), and a consumer (agent C) can `consume` it — all distinct cipherclerks
    /// signing real turns through the canonical executor.
    ///
    /// The cell-program on `target_cell` (installed via `install_app_program`)
    /// enforces the per-method slot caveats; the actor's signature is verified
    /// against the actor cell's stored key (open target permissions let a
    /// non-owner's turn apply, exactly as the integration tests' harness does).
    pub fn execute_app_turn_for_agent(
        &mut self,
        agent_idx: usize,
        target_cell: CellId,
        method: &str,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<TurnResult, String> {
        self.execute_app_turn_inner(agent_idx, target_cell, method, effects, None, fee)
    }

    /// Like [`execute_app_turn_for_agent`] but the action carries an
    /// `Authorization::Custom { predicate }` discharged by a registered
    /// `WitnessedPredicateKind::Custom { vk_hash }` verifier, with the
    /// threshold-signature proof bytes in `witness_blobs[0]`. This is the
    /// governed-namespace `commit_table_update` path.
    ///
    /// `vk_hash` must have a verifier registered via
    /// [`register_threshold_verifier`]; `committee_commitment` is carried in the
    /// predicate's `commitment` field (the governance committee root). The proof
    /// bytes are `t` concatenated `(pubkey[32] ‖ sig[64])` records over the
    /// canonical custom signing message — produced by [`sign_custom_commit`].
    pub fn execute_custom_auth_turn_for_agent(
        &mut self,
        agent_idx: usize,
        target_cell: CellId,
        method: &str,
        effects: Vec<Effect>,
        vk_hash: [u8; 32],
        committee_commitment: [u8; 32],
        proof_bytes: Vec<u8>,
        fee: u64,
    ) -> Result<TurnResult, String> {
        let predicate = dregg_cell::WitnessedPredicate::custom(
            vk_hash,
            committee_commitment,
            dregg_cell::InputRef::SigningMessage,
            0,
        );
        let auth = CustomAuth {
            predicate,
            proof_bytes,
        };
        self.execute_app_turn_inner(agent_idx, target_cell, method, effects, Some(auth), fee)
    }

    fn execute_app_turn_inner(
        &mut self,
        agent_idx: usize,
        target_cell: CellId,
        method: &str,
        effects: Vec<Effect>,
        custom: Option<CustomAuth>,
        fee: u64,
    ) -> Result<TurnResult, String> {
        let actor_cell = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?
            .cell_id;

        let nonce = self
            .ledger
            .get(&actor_cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(actor_cell, nonce);
        builder.set_fee(fee);

        // The action target is the APP cell; caller is the actor. For the Custom
        // path we attach the predicate + witness blob directly (no signature
        // override — the predicate is the load-bearing auth). For the signed
        // path we leave Unchecked so `sign_call_forest` stamps a real Ed25519
        // signature from the actor's cipherclerk.
        {
            let mut ab = ActionBuilder::new_unchecked_for_tests(target_cell, method, actor_cell);
            for effect in effects {
                ab = ab.effect(effect);
            }
            builder.add_action(ab.build());
        }

        let mut turn = builder.build();

        if turn.previous_receipt_hash.is_none() {
            if let Some(prev) = self.executor.get_last_receipt_hash(&actor_cell) {
                turn.previous_receipt_hash = Some(prev);
            }
        }

        let federation_id = self.executor.local_federation_id;

        if let Some(custom) = custom {
            // Attach the Custom predicate + threshold-sig witness blob to the
            // single root action, replacing the Unchecked authorization.
            if let Some(root) = turn.call_forest.roots.first_mut() {
                root.action.authorization = Authorization::Custom {
                    predicate: custom.predicate,
                };
                root.action.witness_blobs = vec![WitnessBlob::proof(custom.proof_bytes)];
                root.hash = [0u8; 32];
            }
            turn.call_forest.forest_hash = [0u8; 32];
        } else {
            let cclerk = &self.agents[agent_idx].cclerk;
            sign_call_forest(&mut turn, cclerk, &federation_id);
        }

        let result = self.executor.execute(&turn, &mut self.ledger);
        if let TurnResult::Committed { receipt, .. } = &result {
            self.receipts.push(receipt.clone());
            self.turns.push(turn.clone());
        }
        Ok(result)
    }

    /// Compute the canonical custom signing message the executor will recompute
    /// for a `commit_table_update` action carrying the given effects. Committee
    /// members sign THIS exact message; the signatures are bundled into the
    /// threshold proof. Mirrors the executor's
    /// `TurnExecutor::compute_custom_signing_message`, parameterized by the
    /// actor's current nonce.
    pub fn custom_commit_signing_message(
        &self,
        agent_idx: usize,
        target_cell: CellId,
        method: &str,
        effects: &[Effect],
        vk_hash: [u8; 32],
        committee_commitment: [u8; 32],
    ) -> Result<Vec<u8>, String> {
        let actor_cell = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?
            .cell_id;
        let nonce = self
            .ledger
            .get(&actor_cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let predicate = dregg_cell::WitnessedPredicate::custom(
            vk_hash,
            committee_commitment,
            dregg_cell::InputRef::SigningMessage,
            0,
        );

        // Reconstruct the exact Action the executor will hash. ActionBuilder
        // with the Custom authorization produces the canonical body.
        let mut ab = ActionBuilder::new_unchecked_for_tests(target_cell, method, actor_cell);
        for effect in effects {
            ab = ab.effect(effect.clone());
        }
        let mut action = ab.build();
        action.authorization = Authorization::Custom {
            predicate: predicate.clone(),
        };
        action.witness_blobs = Vec::new();

        Ok(TurnExecutor::compute_custom_signing_message(
            &action,
            &predicate,
            0,
            &self.executor.local_federation_id,
            nonce,
        ))
    }

    /// Register a real Ed25519 threshold verifier under `vk_hash`. The verifier
    /// requires `threshold` distinct valid committee signatures over the
    /// canonical custom signing message before any `Authorization::Custom`
    /// commit turn against that `vk_hash` is accepted.
    pub fn register_threshold_verifier(
        &mut self,
        vk_hash: [u8; 32],
        committee: Vec<[u8; 32]>,
        threshold: usize,
    ) {
        let mut registry = dregg_cell::WitnessedPredicateRegistry::empty();
        registry.register_custom(
            vk_hash,
            std::sync::Arc::new(EdThresholdVerifier::new(vk_hash, committee, threshold)),
        );
        self.executor.set_witnessed_registry(registry);
    }

    /// Sign the canonical custom commit message with a specific agent's
    /// cipherclerk, returning a `(pubkey[32] ‖ sig[64])` 96-byte record. The
    /// caller concatenates `threshold` such records into the proof bytes passed
    /// to [`execute_custom_auth_turn_for_agent`].
    pub fn sign_custom_commit(
        &self,
        signer_agent_idx: usize,
        message: &[u8],
    ) -> Result<Vec<u8>, String> {
        let agent = self
            .agents
            .get(signer_agent_idx)
            .ok_or_else(|| format!("invalid agent index: {signer_agent_idx}"))?;
        let sig = agent.cclerk.sign_bytes(message);
        let mut out = Vec::with_capacity(96);
        out.extend_from_slice(&agent.public_key);
        out.extend_from_slice(&sig.0);
        Ok(out)
    }

    /// Export a minimal snapshot of runtime state (STARBRIDGE-FOLLOWUP-03
    /// progress on §5.9 / §5.10 / Q4).
    ///
    /// Returns a JSON string containing:
    /// - genesis metadata (factory_vk, current_height, timestamp base)
    /// - counts of receipts, turns, events, agents, federations
    /// - placeholder note for the canonical "WitnessedReceipt stream
    ///   (Vec<Turn> + genesis header)" format required for node ingest and
    ///   time-travel replay.
    ///
    /// This is a **stub surface** for the blocked snapshot format design.
    /// It uses only in-memory projections (no proving stack, no circuit
    /// changes). Full bidirectional (export + import that produces a
    /// live runtime at prior height) awaits the §8 Q4 resolution + §5.9
    /// format spec. The shape here is intentionally minimal so that
    /// extension/inspector code can start wiring against the future API
    /// without waiting for the human cargo session.
    ///
    /// Houyhnhnm note: must eventually be a protocol-level stream
    /// importable by real nodes (not sim-only).
    pub fn export_runtime_snapshot_stub(&self) -> String {
        #[derive(Serialize)]
        struct SnapshotStub {
            schema: String,
            exported_at: u64,
            current_height: u64,
            num_agents: usize,
            num_federations: usize,
            num_receipts: usize,
            num_turns: usize,
            num_events: usize,
            default_factory_vk_hex: String,
            note: String,
            // Future: witnessed_receipt_chain: Vec<...> or canonical bytes
        }

        let now = js_sys_now_secs() as u64;
        let stub = SnapshotStub {
            schema: "dregg-runtime-snapshot-v0-stub".to_string(),
            exported_at: now,
            current_height: self.current_height,
            num_agents: self.agents.len(),
            num_federations: self.federations.len(),
            num_receipts: self.receipts.len(),
            num_turns: self.turns.len(),
            num_events: self.events.len(),
            default_factory_vk_hex: hex_encode(&self.default_factory_vk),
            note: "PLACEHOLDER: full WitnessedReceipt stream format + import \
                   pending design resolution (§5.9 + §8 Q4 snapshot-and-replay). \
                   This stub is safe (no proving stack) and unblocks JS prep. \
                   See STARBRIDGE-PLAN §5.9/5.10 and SOVEREIGN-WITNESS etc for context. \
                   Time-travel cursor remains forward-only until format lands."
                .to_string(),
        };

        serde_json::to_string_pretty(&stub).unwrap_or_else(|_| "{}".to_string())
    }

    /// Stub for time-travel / rewind cursor on the InMemoryRuntime
    /// (STARBRIDGE-FOLLOWUP-03 on §5.10 + Q4).
    ///
    /// Currently returns Err with guidance. Recommended path once §5.9
    /// lands: snapshot at height N, destroy/recreate runtime from the
    /// snapshot bytes (canonical stream), then replay forward if needed.
    /// Alternative (Explorer-only) or N parallel runtimes are out of scope
    /// for the sim core.
    ///
    /// `caps.timeTravel` in JS surfaces should remain false until this
    /// is real. This stub provides the Rust surface + error contract
    /// for inspector code to target.
    ///
    /// Safe: pure control flow, no mutation on success path, no circuit.
    pub fn time_travel_to_stub(&mut self, target_height: u64) -> Result<(), String> {
        if target_height > self.current_height {
            return Err(format!(
                "time travel only supports rewind (target {target_height} > current {}); \
                 forward simulation only via advance_height + turns",
                self.current_height
            ));
        }
        if target_height == self.current_height {
            return Ok(()); // no-op
        }
        Err(format!(
            "time-travel rewind to {} requires the §5.9 snapshot format + \
             snapshot-and-replay (see plan §8 Q4 and Houyhnhnm persistence stream). \
             Current runtime is cumulative-only (advance_height). \
             Use export_runtime_snapshot_stub() for future compatibility. \
             (STARBRIDGE-FOLLOWUP-03 stub; no proving stack changes.)",
            target_height
        ))
    }
}

/// Walk a committed turn's call forest and project its balance-affecting
/// effects into circuit-level EffectVM `Effect`s for [`DreggRuntime::prove_turn`].
///
/// This is an intentionally lossy projection scoped to what the sim runtime
/// surfaces: `Transfer` is the only balance-mutating effect the wasm runtime's
/// `execute_turn` path emits today. A `Transfer` whose sender (`from`) is the
/// actor cell becomes an outgoing EffectVM `Transfer { amount, direction: 1 }`;
/// one whose `to` is the actor becomes incoming (`direction: 0`). Outgoing
/// totals are accumulated so the prover can size the initial balance to avoid
/// a (correct) underflow assertion in the trace generator.
fn collect_vm_effects_from_forest(
    turn: &Turn,
    actor_cell: Option<dregg_cell::CellId>,
    out: &mut Vec<dregg_circuit::Effect>,
    total_outgoing: &mut u64,
) {
    fn walk(
        tree: &CallTree,
        actor_cell: Option<dregg_cell::CellId>,
        out: &mut Vec<dregg_circuit::Effect>,
        total_outgoing: &mut u64,
    ) {
        for effect in &tree.action.effects {
            if let Effect::Transfer { from, amount, .. } = effect {
                let outgoing = actor_cell.map(|a| a == *from).unwrap_or(true);
                if outgoing {
                    *total_outgoing = total_outgoing.saturating_add(*amount);
                }
                out.push(dregg_circuit::Effect::Transfer {
                    amount: *amount,
                    direction: if outgoing { 1 } else { 0 },
                });
            }
        }
        for child in &tree.children {
            walk(child, actor_cell, out, total_outgoing);
        }
    }
    for tree in &turn.call_forest.roots {
        walk(tree, actor_cell, out, total_outgoing);
    }
}

// ============================================================================
// Starbridge-app cell-programs (multi-agent + Authorization::Custom surface)
//
// The subscription + governed-namespace starbridge-apps live in crates that
// depend on `dregg-app-framework` (axum + tokio(full) + reqwest), which is NOT
// wasm32-safe. We therefore cannot pull those crates into the wasm cdylib.
// Instead we re-materialize the *program values* they author from canonical
// `dregg_cell` types here. The constraint sets below mirror
// `starbridge_subscription::subscription_program` and
// `starbridge_governed_namespace::governance_program` EXACTLY — minus the
// `SenderAuthorized` constraints, which the apps' own executor-level
// integration tests also strip (they require Merkle-witness bundles that the
// in-browser harness doesn't carry; see
// `integration_publish_consume.rs::executor_shape_program` and
// `integration_propose_vote_commit.rs::stripped_governance_program`). Slot
// indices, method symbols, monotonic/immutable invariants, and the
// MonotonicSequence(version) commit caveat are all preserved, so the executor
// enforces the same real shape end-to-end.
// ============================================================================

pub mod app_programs {
    use dregg_cell::program::{
        CellProgram, SimpleStateConstraint, StateConstraint, TransitionCase, TransitionGuard,
    };
    use dregg_cell::{CellState, FieldElement, Permissions};
    use dregg_turn::action::symbol;

    // ---- subscription slot layout (mirrors starbridge_subscription) ----
    pub const SUB_SEQ_HEAD_SLOT: u8 = 0;
    pub const SUB_SEQ_TAIL_SLOT: u8 = 1;
    pub const SUB_CAPACITY_SLOT: u8 = 2;
    pub const SUB_PUBLISHERS_ROOT_SLOT: u8 = 3;
    pub const SUB_CONSUMERS_ROOT_SLOT: u8 = 4;
    pub const SUB_OWNER_PK_HASH_SLOT: u8 = 5;
    pub const SUB_MESSAGE_ROOT_SLOT: u8 = 6;
    pub const SUB_LATEST_PAYLOAD_SLOT: u8 = 7;

    // ---- governed-namespace slot layout (mirrors starbridge_governed_namespace) ----
    pub const GOV_ROUTE_TABLE_ROOT_SLOT: u8 = 0;
    pub const GOV_VERSION_SLOT: u8 = 1;
    pub const GOV_COMMITTEE_ROOT_SLOT: u8 = 2;
    pub const GOV_THRESHOLD_SLOT: u8 = 3;
    pub const GOV_DISPUTE_WINDOW_HEIGHT_SLOT: u8 = 4;
    pub const GOV_PENDING_PROPOSAL_ROOT_SLOT: u8 = 5;
    pub const GOV_RESERVED_SLOT_6: u8 = 6;
    pub const GOV_RESERVED_SLOT_7: u8 = 7;

    fn u64_field(value: u64) -> FieldElement {
        let mut out = [0u8; 32];
        out[24..32].copy_from_slice(&value.to_be_bytes());
        out
    }

    fn slot_changed(index: u8) -> StateConstraint {
        StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::Immutable { index },
            ))],
        }
    }

    /// Permissions with every action open. The integration tests relax
    /// permissions to `AuthRequired::None` so multi-agent turns (a publisher
    /// or voter that is NOT the cell owner) can apply; the cell-program slot
    /// caveats remain the load-bearing enforcement. We mirror that here.
    pub fn open_permissions() -> Permissions {
        use dregg_cell::AuthRequired::None as N;
        Permissions {
            send: N,
            receive: N,
            set_state: N,
            set_permissions: N,
            set_verification_key: N,
            increment_nonce: N,
            delegate: N,
            access: N,
        }
    }

    /// Canonical subscription cell-program (SenderAuthorized stripped, exactly
    /// as `integration_publish_consume.rs::executor_shape_program`).
    pub fn subscription_program() -> CellProgram {
        CellProgram::Cases(vec![
            TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![
                    StateConstraint::Immutable {
                        index: SUB_CAPACITY_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_OWNER_PK_HASH_SLOT,
                    },
                    StateConstraint::FieldLteField {
                        left_index: SUB_SEQ_TAIL_SLOT,
                        right_index: SUB_SEQ_HEAD_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("publish"),
                },
                constraints: vec![
                    StateConstraint::MonotonicSequence {
                        seq_index: SUB_SEQ_HEAD_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_TAIL_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_PUBLISHERS_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_CONSUMERS_ROOT_SLOT,
                    },
                    slot_changed(SUB_MESSAGE_ROOT_SLOT),
                    StateConstraint::FieldGte {
                        index: SUB_MESSAGE_ROOT_SLOT,
                        value: u64_field(1),
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("consume"),
                },
                constraints: vec![
                    StateConstraint::MonotonicSequence {
                        seq_index: SUB_SEQ_TAIL_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_HEAD_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_MESSAGE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_LATEST_PAYLOAD_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_PUBLISHERS_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_CONSUMERS_ROOT_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("grant_publisher"),
                },
                constraints: vec![
                    slot_changed(SUB_PUBLISHERS_ROOT_SLOT),
                    StateConstraint::FieldGte {
                        index: SUB_PUBLISHERS_ROOT_SLOT,
                        value: u64_field(1),
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_HEAD_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_TAIL_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_CONSUMERS_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_MESSAGE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_LATEST_PAYLOAD_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("grant_consumer"),
                },
                constraints: vec![
                    slot_changed(SUB_CONSUMERS_ROOT_SLOT),
                    StateConstraint::FieldGte {
                        index: SUB_CONSUMERS_ROOT_SLOT,
                        value: u64_field(1),
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_HEAD_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_SEQ_TAIL_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_PUBLISHERS_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_MESSAGE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: SUB_LATEST_PAYLOAD_SLOT,
                    },
                ],
            },
        ])
    }

    /// Build the initial subscription cell state. `capacity` immutable; head/tail
    /// zero; owner_pk_hash set so the `Immutable` invariant has a concrete anchor.
    pub fn subscription_initial_state(owner_pk_hash: FieldElement, capacity: u64) -> CellState {
        let mut state = CellState::new(1_000_000);
        state.fields[SUB_CAPACITY_SLOT as usize] = u64_field(capacity);
        state.fields[SUB_OWNER_PK_HASH_SLOT as usize] = owner_pk_hash;
        state
    }

    /// Canonical governed-namespace cell-program (SenderAuthorized stripped,
    /// exactly as `integration_propose_vote_commit.rs::stripped_governance_program`).
    pub fn governance_program() -> CellProgram {
        CellProgram::Cases(vec![
            TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![
                    StateConstraint::Immutable {
                        index: GOV_COMMITTEE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_THRESHOLD_SLOT,
                    },
                    StateConstraint::Monotonic {
                        index: GOV_VERSION_SLOT,
                    },
                    StateConstraint::Monotonic {
                        index: GOV_DISPUTE_WINDOW_HEIGHT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_RESERVED_SLOT_6,
                    },
                    StateConstraint::Immutable {
                        index: GOV_RESERVED_SLOT_7,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("propose_table_update"),
                },
                constraints: vec![
                    StateConstraint::Immutable {
                        index: GOV_ROUTE_TABLE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_VERSION_SLOT,
                    },
                    StateConstraint::Monotonic {
                        index: GOV_PENDING_PROPOSAL_ROOT_SLOT,
                    },
                    StateConstraint::Monotonic {
                        index: GOV_DISPUTE_WINDOW_HEIGHT_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("vote_on_proposal"),
                },
                constraints: vec![
                    StateConstraint::Immutable {
                        index: GOV_ROUTE_TABLE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_VERSION_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_DISPUTE_WINDOW_HEIGHT_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("commit_table_update"),
                },
                constraints: vec![
                    StateConstraint::MonotonicSequence {
                        seq_index: GOV_VERSION_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_DISPUTE_WINDOW_HEIGHT_SLOT,
                    },
                ],
            },
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol("register_service"),
                },
                constraints: vec![
                    StateConstraint::Immutable {
                        index: GOV_ROUTE_TABLE_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_VERSION_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_PENDING_PROPOSAL_ROOT_SLOT,
                    },
                    StateConstraint::Immutable {
                        index: GOV_DISPUTE_WINDOW_HEIGHT_SLOT,
                    },
                ],
            },
        ])
    }

    /// Build the initial governed-namespace cell state, mirroring
    /// `integration_propose_vote_commit.rs::init_namespace_cell`.
    pub fn governance_initial_state(
        committee_root: FieldElement,
        threshold: u64,
        initial_route_table_root: FieldElement,
    ) -> CellState {
        let mut state = CellState::new(1_000_000);
        state.fields[GOV_ROUTE_TABLE_ROOT_SLOT as usize] = initial_route_table_root;
        state.fields[GOV_VERSION_SLOT as usize] = u64_field(0);
        state.fields[GOV_COMMITTEE_ROOT_SLOT as usize] = committee_root;
        state.fields[GOV_THRESHOLD_SLOT as usize] = u64_field(threshold);
        state.fields[GOV_DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(0);
        state.fields[GOV_PENDING_PROPOSAL_ROOT_SLOT as usize] = [0u8; 32];
        state
    }
}

/// A real Ed25519 threshold-signature verifier for the governed-namespace
/// `commit_table_update` flow's `Authorization::Custom`.
///
/// This is NOT a stub: the `proof_bytes` carry `t` concatenated 96-byte records
/// `(committee_member_pubkey[32] ‖ ed25519_signature[64])`; the verifier checks
/// that there are at least `threshold` records, that every signature is a valid
/// Ed25519 signature (via the canonical `dregg_types::verify`) over the exact
/// canonical custom signing message the executor recomputes, and that all
/// signing members are distinct and belong to the committee. Only then does it
/// return `Ok(())`, and only then does the executor commit the atomic route-table
/// swap. This is the in-browser realization of
/// `dregg_dfa::ThresholdVerifier::verify` over a real committee.
pub struct EdThresholdVerifier {
    vk_hash: [u8; 32],
    /// Committee member public keys; a valid signature must come from one of these.
    committee: Vec<[u8; 32]>,
    /// Number of distinct committee signatures required.
    threshold: usize,
}

impl EdThresholdVerifier {
    pub fn new(vk_hash: [u8; 32], committee: Vec<[u8; 32]>, threshold: usize) -> Self {
        Self {
            vk_hash,
            committee,
            threshold,
        }
    }
}

impl dregg_cell::WitnessedPredicateVerifier for EdThresholdVerifier {
    fn name(&self) -> &'static str {
        "wasm-ed25519-threshold"
    }
    fn kind(&self) -> dregg_cell::WitnessedPredicateKind {
        dregg_cell::WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }
    fn verify(
        &self,
        _commitment: &[u8; 32],
        input: &dregg_cell::PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), dregg_cell::WitnessedPredicateError> {
        use dregg_cell::WitnessedPredicateError as E;
        use dregg_types::{PublicKey, Signature, verify};

        let message = match input {
            dregg_cell::PredicateInput::SigningMessage(bytes) => *bytes,
            _ => {
                return Err(E::InputShapeMismatch {
                    kind_name: "wasm-ed25519-threshold",
                    expected: "SigningMessage",
                    actual: "other",
                });
            }
        };

        // Each record is pubkey[32] ‖ sig[64] = 96 bytes.
        const REC: usize = 96;
        if proof_bytes.is_empty() || proof_bytes.len() % REC != 0 {
            return Err(E::Rejected {
                kind_name: "wasm-ed25519-threshold",
                reason: format!(
                    "proof bytes not a multiple of {REC} (got {})",
                    proof_bytes.len()
                ),
            });
        }

        let mut seen: Vec<[u8; 32]> = Vec::new();
        for chunk in proof_bytes.chunks_exact(REC) {
            let mut pk = [0u8; 32];
            pk.copy_from_slice(&chunk[..32]);
            let mut sig = [0u8; 64];
            sig.copy_from_slice(&chunk[32..96]);

            if !self.committee.contains(&pk) {
                return Err(E::Rejected {
                    kind_name: "wasm-ed25519-threshold",
                    reason: "signer is not a committee member".to_string(),
                });
            }
            if seen.contains(&pk) {
                return Err(E::Rejected {
                    kind_name: "wasm-ed25519-threshold",
                    reason: "duplicate committee signer".to_string(),
                });
            }
            if !verify(&PublicKey(pk), message, &Signature(sig)) {
                return Err(E::Rejected {
                    kind_name: "wasm-ed25519-threshold",
                    reason: "invalid Ed25519 signature over the canonical custom message"
                        .to_string(),
                });
            }
            seen.push(pk);
        }

        if seen.len() < self.threshold {
            return Err(E::Rejected {
                kind_name: "wasm-ed25519-threshold",
                reason: format!(
                    "threshold not met: {} valid distinct committee signatures, need {}",
                    seen.len(),
                    self.threshold
                ),
            });
        }
        Ok(())
    }
}

/// Map a `PeerExchangeError` to its variant name (without payload), used by
/// the bindings to surface a typed error code to JS alongside the
/// human-readable message.
fn peer_exchange_error_variant(e: &dregg_cell::PeerExchangeError) -> String {
    use dregg_cell::PeerExchangeError as E;
    match e {
        E::InvalidSignature => "InvalidSignature",
        E::CommitmentMismatch { .. } => "CommitmentMismatch",
        E::SequenceGap { .. } => "SequenceGap",
        E::TimestampRegression => "TimestampRegression",
        E::UnknownPeer(_) => "UnknownPeer",
        E::InvalidTransitionProof(_) => "InvalidTransitionProof",
    }
    .to_string()
}

/// One-shot summary of a finalized consensus round, suitable for JS-side
/// rendering. The fields surface what's actually on the
/// `dregg_federation::RevocationBlock` + `QuorumCertificate` returned from
/// `Federation::run_consensus_round` — no inferred values.
#[derive(Clone, Debug, Serialize)]
pub struct ConsensusRoundResult {
    pub block_hash: String,
    pub height: u64,
    pub view: u64,
    pub num_events: usize,
    pub proposer: usize,
    pub qc_threshold: usize,
    pub qc_votes: usize,
}

/// Walk the turn's call forest and replace every `Authorization::Unchecked`
/// with a real Ed25519 signature via `AgentCipherclerk::sign_action`. Existing
/// non-Unchecked authorizations are left intact so callers can pre-sign or
/// pre-prove specific actions. Uses the SDK's canonical signing path — no
/// hand-rolled cryptography.
pub(crate) fn sign_call_forest(
    turn: &mut Turn,
    cclerk: &AgentCipherclerk,
    federation_id: &[u8; 32],
) {
    for tree in &mut turn.call_forest.roots {
        sign_call_tree(tree, cclerk, federation_id);
    }
    // Mutating actions invalidates any cached forest hash; clear so the
    // executor recomputes from the now-signed actions.
    turn.call_forest.forest_hash = [0u8; 32];
}

fn sign_call_tree(tree: &mut CallTree, cclerk: &AgentCipherclerk, federation_id: &[u8; 32]) {
    if matches!(tree.action.authorization, Authorization::Unchecked) {
        // Clone the action because sign_action returns a fresh one; replace in place.
        tree.action = cclerk.sign_action(tree.action.clone(), federation_id);
    }
    tree.hash = [0u8; 32]; // invalidate cached action hash
    for child in &mut tree.children {
        sign_call_tree(child, cclerk, federation_id);
    }
}

/// Lowercase hex encode without pulling the `hex` crate (which isn't a
/// direct wasm dep). The bindings module has its own copy; this one is
/// internal to runtime so `ConsensusRoundResult` can hold a pre-encoded
/// hash string.
fn hex_encode_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        out.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
    }
    out
}
