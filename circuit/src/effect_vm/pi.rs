//! Public input layout for the Effect VM AIR.
//!
//! Stage 1 widening (`EFFECT-VM-SHAPE-A.md`): commitments grow from 1 felt
//! (~31-bit binding) to 4 felts (~124-bit binding), via the typed
//! `Commitment4<T>` framework (`pyana_commit::typed`). Position 0 of each
//! 4-tuple corresponds to the in-trace `state::STATE_COMMIT` continuity
//! column; positions 1..3 are bound to the canonical cell state by the
//! executor PI matching loop.
//!
//! AUDIT[stage1-trace-widen]: For Stage 1 the trace `state::STATE_COMMIT`
//! remains a 1-column continuity hash (Constraint Group 4 unchanged). The
//! extra 3 PI elements get their security from the executor PI matching
//! loop. Stage 2 (`EFFECT-VM-SHAPE-A.md` Phase 1) widens the trace column.

// ---- Commitments (Stage 1 widened to 4 felts each, ~124-bit) ----
/// Old state commitment, 4-felt Poseidon2 form.
pub const OLD_COMMIT_BASE: usize = 0;
pub const OLD_COMMIT_LEN: usize = 4;
/// New state commitment, 4-felt Poseidon2 form.
pub const NEW_COMMIT_BASE: usize = 4;
pub const NEW_COMMIT_LEN: usize = 4;
/// Effects-tree hash, 4-felt Poseidon2 form. Promotes the prior 2-felt
/// (lo+synthetic-hi) form to 4 felts; synthetic-hi is dropped.
pub const EFFECTS_HASH_BASE: usize = 8;
pub const EFFECTS_HASH_LEN: usize = 4;

// ---- Backwards-compatible aliases (position 0 only) ----
/// Legacy alias: position 0 of OLD_COMMIT_BASE (single-felt continuity binding).
pub const OLD_COMMIT: usize = OLD_COMMIT_BASE;
/// Legacy alias: position 0 of NEW_COMMIT_BASE.
pub const NEW_COMMIT: usize = NEW_COMMIT_BASE;
/// Legacy alias: position 0 of EFFECTS_HASH_BASE.
pub const EFFECTS_HASH_LO: usize = EFFECTS_HASH_BASE;
/// Legacy alias: position 1 of EFFECTS_HASH_BASE. AUDIT[stage1-effects-hash]:
/// callers reading this should switch to absorbing all 4 elements via the
/// EFFECTS_HASH_LEN range; the prior synthetic-hi binding is replaced by
/// independent Poseidon2 squeezes.
pub const EFFECTS_HASH_HI: usize = EFFECTS_HASH_BASE + 1;

// ---- Per-cell balance limbs (P0-1 net_delta binding) ----
/// Initial balance low limb (30 bits) — pinned to row 0 state_before.
pub const INIT_BAL_LO: usize = 12;
/// Initial balance high limb — pinned to row 0 state_before.
pub const INIT_BAL_HI: usize = 13;
/// Final balance low limb — pinned to last row state_after.
pub const FINAL_BAL_LO: usize = 14;
/// Final balance high limb — pinned to last row state_after.
pub const FINAL_BAL_HI: usize = 15;

// ---- Net balance delta (P0-1 binding) ----
pub const NET_DELTA_MAG: usize = 16;
pub const NET_DELTA_SIGN: usize = 17;

// ---- Stage 1 additions (per EFFECT-VM-SHAPE-A.md G, E, F) ----
/// Federation block height supplied by the verifier. Used by effects
/// that take a timeout (escrow refund, bridge cancel) — those land in
/// later stages; the PI slot exists now so they have it.
pub const CURRENT_BLOCK_HEIGHT: usize = 18;
/// Per-cell maximum custom effects (from cell program manifest).
/// Verifier supplies from `cell.program.max_custom_effects`.
pub const MAX_CUSTOM_EFFECTS: usize = 19;
/// Number of custom effects in this turn (0 if none). The AIR enforces
/// `Σ s_custom == PI[CUSTOM_EFFECT_COUNT]` (sum-check, soundness
/// prerequisite per `DESIGN-max-custom-effects.md` §7 threat 3).
pub const CUSTOM_EFFECT_COUNT: usize = 20;

// ---- CapTP federation-state root (Stage 1 prep; populated in Stage 7) ----
/// Federation-scoped approved-handoffs Merkle root, 4-felt Poseidon2 form.
/// Initial value: empty-tree sentinel (Commitment4::empty()).
pub const APPROVED_HANDOFFS_BASE: usize = 21;
pub const APPROVED_HANDOFFS_LEN: usize = 4;

// ---- Stage 7-γ.0a additions: turn-level identity bindings ----
//
// These four fields are *shared across all per-cell proofs of one turn*.
// Each per-cell proof carries the same values; the verifier's
// cross-proof PI matching loop (`verify_proof_carrying_turn_bundle`)
// enforces equality across the N proofs. Per-proof binding to the
// canonical Turn::hash and call_forest projection is executor-trusted
// for γ.0; γ.1 elevates the effects_hash_global -> Σ effects_local
// merge to an aggregation micro-AIR.
//
/// Poseidon2 of the canonical `Turn::hash()` (v3, post-Stage-7-α.1).
/// All per-cell proofs of one turn share this value; the verifier
/// rejects bundles whose per-cell proofs disagree.
pub const TURN_HASH_BASE: usize = 25;
pub const TURN_HASH_LEN: usize = 4;
/// Poseidon2 over the canonical-DFS-order traversal of the whole
/// `call_forest`'s effects (not per-cell). Closes P2 (projection
/// totality) at γ.1; for γ.0 it's a shared PI the executor verifies
/// against the turn's recomputed value.
pub const EFFECTS_HASH_GLOBAL_BASE: usize = 29;
pub const EFFECTS_HASH_GLOBAL_LEN: usize = 4;
/// Outer `Turn::nonce`, promoted to PI. Closes the differential-test
/// gap from task #49 (AIR previously did not witness the agent's
/// outer nonce bump). The verifier's PI-match loop rejects bundles
/// whose per-cell proofs disagree on the actor nonce, and the
/// executor checks PI[ACTOR_NONCE] == turn.nonce.
pub const ACTOR_NONCE: usize = 33;
/// Poseidon2 of `previous_receipt_hash` (32 bytes -> 4 felts) when
/// present, or the zero sentinel when absent. Binds each per-cell
/// proof to a specific receipt-chain position.
pub const PREVIOUS_RECEIPT_HASH_BASE: usize = 34;
pub const PREVIOUS_RECEIPT_HASH_LEN: usize = 4;

// ---- Stage 7-γ.2 Phase 1: bilateral cross-cell algebraic binding ----
//
// These slots project each per-cell proof's bilateral-effect participation
// (Transfer, GrantCapability, Introduce) into shared PI fields that the
// off-AIR verifier reconstructs from the turn's call_forest + ACTOR_NONCE.
// The verifier rejects any per-cell PI that doesn't match the
// schedule-derived expectation, closing the executor-trust gap for cross-
// cell agreement (EXECUTOR-HONESTY-AUDIT.md T1, T3, T15 multi-cell tails).
//
// All bilateral fields default to the zero sentinel
// (`Commitment4::empty()` for the 4-felt roots; 0 for the scalar counts)
// when this cell has no bilateral effects of that kind. The verifier
// short-circuits matching against sentinel entries.
//
// Sub-stage status:
//   γ.2.0  PI surface + sentinels                  ✅ (this commit)
//   γ.2.1  AIR aux columns + boundary binding      pending (TODO[γ.2.1])
//   γ.2.2  Verifier cross-cell match loop          ✅ (this commit)
//   γ.2.3  IS_AGENT_CELL gate                      ✅ (this commit)

/// Count of Transfer rows in this cell's projection where direction == 1
/// (outflow). The verifier's expected-schedule reconstruction must agree.
pub const OUTBOUND_TRANSFER_COUNT: usize = 38;
/// Count of Transfer rows where direction == 0 (inflow).
pub const INBOUND_TRANSFER_COUNT: usize = 39;
/// Count of GrantCapability rows where this cell is the grantor.
pub const OUTBOUND_GRANT_COUNT: usize = 40;
/// Count of GrantCapability rows where this cell is the grantee.
pub const INBOUND_GRANT_COUNT: usize = 41;
/// Count of Introduce rows where this cell is the introducer.
pub const INTRO_AS_INTRODUCER_COUNT: usize = 42;
/// Count of Introduce rows where this cell is the recipient.
pub const INTRO_AS_RECIPIENT_COUNT: usize = 43;
/// Count of Introduce rows where this cell is the target.
pub const INTRO_AS_TARGET_COUNT: usize = 44;

/// 4-felt Poseidon2 accumulator over all outbound bilateral transfer_ids
/// in this turn, absorbed in trace-row-index order. Each step folds
/// `(transfer_id_4, peer_cell_id_4)` into the running state. Domain
/// separator distinguishes from inbound + grant + introduce roots.
/// Sentinel: `[BabyBear::ZERO; 4]` when count == 0.
pub const OUTGOING_TRANSFER_ROOT_BASE: usize = 45;
pub const OUTGOING_TRANSFER_ROOT_LEN: usize = 4;
/// Mirror of OUTGOING_TRANSFER_ROOT for the inbound side.
pub const INCOMING_TRANSFER_ROOT_BASE: usize = 49;
pub const INCOMING_TRANSFER_ROOT_LEN: usize = 4;

/// 4-felt accumulator over outbound grant_ids (this cell as grantor).
pub const OUTGOING_GRANT_ROOT_BASE: usize = 53;
pub const OUTGOING_GRANT_ROOT_LEN: usize = 4;
/// 4-felt accumulator over inbound grant_ids (this cell as grantee).
pub const INCOMING_GRANT_ROOT_BASE: usize = 57;
pub const INCOMING_GRANT_ROOT_LEN: usize = 4;

/// 4-felt accumulator over intro_ids where this cell is the introducer.
pub const INTRO_AS_INTRODUCER_ROOT_BASE: usize = 61;
pub const INTRO_AS_INTRODUCER_ROOT_LEN: usize = 4;
/// 4-felt accumulator over intro_ids where this cell is the recipient.
pub const INTRO_AS_RECIPIENT_ROOT_BASE: usize = 65;
pub const INTRO_AS_RECIPIENT_ROOT_LEN: usize = 4;
/// 4-felt accumulator over intro_ids where this cell is the target.
pub const INTRO_AS_TARGET_ROOT_BASE: usize = 69;
pub const INTRO_AS_TARGET_ROOT_LEN: usize = 4;

/// Single-felt boolean: 1 iff this per-cell proof was the actor's
/// (signer's) cell for the turn. Exactly one proof in a bundle must
/// carry IS_AGENT_CELL == 1; all others must be 0. The agent-cell
/// proof's row-0 NONCE column is pinned to PI[ACTOR_NONCE] (γ.0a
/// constraint), and non-agent cells are exempt from that pin. The
/// verifier enforces the exactly-one-agent rule across the bundle.
pub const IS_AGENT_CELL: usize = 73;

// ---- Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
//
// Phase 1: bind the witness's signing identity + replay counter to the
// AIR at row 0 via gated boundary constraints. When IS_SOVEREIGN_CELL
// == 1, the prover and verifier must agree on
//   PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4] == Poseidon2(owner_pubkey)
//   PI[SOVEREIGN_WITNESS_SEQUENCE]            == witness.sequence
// When IS_SOVEREIGN_CELL == 0 (hosted-cell proofs), the prover writes
// the zero sentinel into both PI slots and the in-trace aux columns,
// and the boundary holds trivially (the columns and PI both zero).
// The verifier sets the PI sentinel when not sovereign.
//
// Phase 2 (Option B per design §3.2): an additional proof-commitment
// pair binds an inner transition_proof. The off-AIR verifier reads
// SOVEREIGN_TRANSITION_PROOF_VK_HASH + SOVEREIGN_TRANSITION_PROOF_COMMITMENT
// and recursively verifies the inner STARK via Lane Golden-Edge's
// generalized recursive verifier.
/// 4-felt Poseidon2 hash of the sovereign cell's owning pubkey (the
/// key that signed the witness). Zero sentinel when IS_SOVEREIGN_CELL == 0.
pub const SOVEREIGN_WITNESS_KEY_COMMIT_BASE: usize = 74;
pub const SOVEREIGN_WITNESS_KEY_COMMIT_LEN: usize = 4;
/// Per-cell monotonic sequence counter from the witness. Zero sentinel
/// when IS_SOVEREIGN_CELL == 0. Replay protection via the verifier's
/// chain-walk (each turn's PI[SOVEREIGN_WITNESS_SEQUENCE] must equal
/// the federation's last-known + 1, enforced at executor injection
/// time).
pub const SOVEREIGN_WITNESS_SEQUENCE: usize = 78;
/// Single-felt boolean: 1 iff this per-cell proof attests to a
/// sovereign-witnessed effect. 0 for hosted cells. Drives the gating
/// for SOVEREIGN_WITNESS_KEY_COMMIT / SOVEREIGN_WITNESS_SEQUENCE.
pub const IS_SOVEREIGN_CELL: usize = 79;
/// 4-felt VK hash of the AIR under which the inner transition_proof
/// was produced (typically the Effect VM AIR — see design §3.2). Zero
/// sentinel when no transition_proof was supplied or IS_SOVEREIGN_CELL
/// == 0. Bound only when HAS_TRANSITION_PROOF == 1.
pub const SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE: usize = 80;
pub const SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN: usize = 4;
/// 4-felt Poseidon2 hash of the inner transition_proof bytes (after
/// canonical serialization). Zero sentinel when no proof was supplied.
pub const SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE: usize = 84;
pub const SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN: usize = 4;
/// Single-felt boolean: 1 iff a STARK transition_proof was supplied
/// alongside the witness AND IS_SOVEREIGN_CELL == 1.
pub const HAS_TRANSITION_PROOF: usize = 88;

// ---- 30-bit value-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5) ----
//
// Three effects (BridgeMint, BridgeLock, CreateEscrow) project a u64
// `value` into a single BabyBear via `value & ((1 << 30) - 1)`. Above
// 2^30, the high 34 bits are unrecoverable from the proof: a malicious
// prover could re-mint / re-lock / escrow with arbitrary high-bit
// collisions.
//
// Fix: bind the full u64 into the PI via four 16-bit limbs (positive,
// each < 2^16, summing as v_l + v_ml*2^16 + v_mh*2^32 + v_h*2^48 == value).
// The executor populates the limbs from the runtime u64; the verifier
// PI-matching loop catches any disagreement. The existing per-row
// value_lo param is preserved for backwards-compatibility and is
// tied to the lo+mid_lo+mid_hi via boundary at row 0 (the
// 30-bit-limb form is now demonstrably one *shadow* of the full
// four-limb form).
//
// Each effect gets a 4-element PI slot; populated only when that
// effect appears in the trace. When absent, the slot is the zero
// sentinel.
/// 4-limb (16-bit each) decomposition of `BridgeMint.value`. Limbs are
/// little-endian: limbs[0] is the low 16 bits, limbs[3] is the high 16.
pub const BRIDGE_MINT_VALUE_LIMBS_BASE: usize = 89;
pub const BRIDGE_MINT_VALUE_LIMBS_LEN: usize = 4;
/// 4-limb decomposition of `BridgeLock.value`.
pub const BRIDGE_LOCK_VALUE_LIMBS_BASE: usize = 93;
pub const BRIDGE_LOCK_VALUE_LIMBS_LEN: usize = 4;
/// 4-limb decomposition of `CreateEscrow.amount`.
pub const CREATE_ESCROW_AMOUNT_LIMBS_BASE: usize = 97;
pub const CREATE_ESCROW_AMOUNT_LIMBS_LEN: usize = 4;

// ---- Custom proof commitments ----
/// For each custom effect i (0..custom_count):
///   PI[CUSTOM_PROOFS_BASE + i*12 + 0..8]  = custom_program_vk_hash (8 elements, full 32B)
///   PI[CUSTOM_PROOFS_BASE + i*12 + 8..12] = custom_proof_commitment (4 elements)
///
/// **PI layout v2** (`VK_PI_LAYOUT_VERSION == 2`): vk_hash widened from 4
/// to 8 felts (~16B → 32B) per `AIR-SOUNDNESS-AUDIT.md` #70. Pre-v2
/// callers wrote a 4-felt low half and zero-padded the upper 16 bytes for
/// registry lookup, allowing two VKs that collide in the lower half to
/// dispatch to the same handler (80-bit security in a 128-bit system).
/// Post-v2 proofs are NOT verifier-compatible with pre-v2 proofs (the PI
/// length differs by 4 felts/custom-entry); the verifier rejects on PI
/// length mismatch.
///
/// Note: CUSTOM_PROOFS_BASE is computed from BASE_COUNT so that adding
/// new γ.2 PI fields shifts the custom-proof entries automatically. All
/// callers compute from `BASE_COUNT` rather than the literal constant.
pub const CUSTOM_PROOFS_BASE: usize = BASE_COUNT;

/// PI layout version for custom-effect dispatch. Bumped from 1 to 2 when
/// vk_hash widened from 4 to 8 felts. Verifiers MAY consult this constant
/// to gate compatibility (the PI length itself is also a deterministic
/// check).
pub const VK_PI_LAYOUT_VERSION: u32 = 2;
/// Base public inputs (without custom proof data).
///
/// Layout (post sovereign-witness teeth + unilateral binding; BASE_COUNT 173):
///   0..21   pre-γ.0a slots (commitments, balances, block height, etc.)
///   21..25  APPROVED_HANDOFFS[4]
///   25..29  TURN_HASH[4]                       (γ.0a)
///   29..33  EFFECTS_HASH_GLOBAL[4]             (γ.0a)
///   33      ACTOR_NONCE                        (γ.0a)
///   34..38  PREVIOUS_RECEIPT_HASH[4]           (γ.0a)
///   38..45  bilateral counts (transfer/grant/intro per direction/role) (γ.2)
///   45..49  OUTGOING_TRANSFER_ROOT[4]          (γ.2)
///   49..53  INCOMING_TRANSFER_ROOT[4]          (γ.2)
///   53..57  OUTGOING_GRANT_ROOT[4]             (γ.2)
///   57..61  INCOMING_GRANT_ROOT[4]             (γ.2)
///   61..65  INTRO_AS_INTRODUCER_ROOT[4]        (γ.2)
///   65..69  INTRO_AS_RECIPIENT_ROOT[4]         (γ.2)
///   69..73  INTRO_AS_TARGET_ROOT[4]            (γ.2)
///   73      IS_AGENT_CELL                      (γ.2)
///   74..78  SOVEREIGN_WITNESS_KEY_COMMIT[4]    (sovereign teeth)
///   78      SOVEREIGN_WITNESS_SEQUENCE         (sovereign teeth)
///   79      IS_SOVEREIGN_CELL                  (sovereign teeth)
///   80..84  SOVEREIGN_TRANSITION_PROOF_VK_HASH[4]    (sovereign teeth Phase 2)
///   84..88  SOVEREIGN_TRANSITION_PROOF_COMMITMENT[4] (sovereign teeth Phase 2)
///   88      HAS_TRANSITION_PROOF               (sovereign teeth Phase 2)
///   89..93  BRIDGE_MINT_VALUE_LIMBS[4]          (30-bit-trunc fix)
///   93..97  BRIDGE_LOCK_VALUE_LIMBS[4]          (30-bit-trunc fix)
///   97..101 CREATE_ESCROW_AMOUNT_LIMBS[4]       (30-bit-trunc fix)
///   101     SLOT_CAVEAT_COUNT                   (Cav-Codex Block 3)
///   102..126 SLOT_CAVEAT_MANIFEST[24]            (Cav-Codex Block 3)
///   126     CROSS_EFFECT_DEPS_COUNT             (Proof-to-Action §3.3)
///   127..151 CROSS_EFFECT_DEPS_MANIFEST[24]     (Proof-to-Action §3.3)
///   151     WITNESS_INDEX_MAP_COUNT             (Proof-to-Action §3.2)
///   152..168 WITNESS_INDEX_MAP[16]              (Proof-to-Action §3.2)
///   168     UNILATERAL_ATTESTATIONS_COUNT       (γ.2 unilateral)
///   169..173 UNILATERAL_ATTESTATIONS_ROOT[4]    (γ.2 unilateral)
///   173     EMIT_EVENT_COUNT                    (closes #110)
///   174..182 EMIT_EVENT_TOPIC_HASH[8]            (closes #110)
///   182..190 EMIT_EVENT_PAYLOAD_HASH[8]          (closes #110)
///
/// ---- Slot-caveat manifest (Cav-Codex Block 3) ----
///
/// Per `SLOT-CAVEATS-DESIGN.md` §4: AIR enforcement of slot caveats
/// is opt-in per variant. Block 3 lands the *manifest surface*: a
/// single PI section that carries the cell-program's declared
/// `StateConstraint` set so that
///   (a) the verifier can re-evaluate the same caveats against the
///       state_before/state_after columns this AIR already binds,
///       and
///   (b) a future row-bound AIR gadget can pin specific
///       (state_before.fields[i], state_after.fields[i]) columns to
///       the manifest entries.
///
/// The manifest is fixed-size — up to `MAX_SLOT_CAVEATS` entries of
/// `SLOT_CAVEAT_ENTRY_SIZE` felts each, prefixed by a single-felt
/// count. Unused entries are zero-padded. Each entry is a 6-felt
/// tuple: `[type_tag, slot_index, p0, p1, p2, p3]`. Variants with
/// fewer than 4 numeric parameters leave trailing felts at zero;
/// variants whose parameters don't fit (e.g. `AllowedTransitions`
/// with a variable-length transition list) carry a 32B→4-felt
/// commitment in `(p0, p1, p2, p3)`.
///
/// Type tags (kept in sync with `pyana_cell::program::StateConstraint`):
pub const SLOT_CAVEAT_COUNT: usize = 101;
/// Maximum number of slot caveats bindable through the PI manifest.
/// Cells declaring more than this fall back to executor-only
/// enforcement (the AIR cannot bind them).
pub const MAX_SLOT_CAVEATS: usize = 4;
/// Felts per slot-caveat entry: [type_tag, slot_index, p0, p1, p2, p3].
pub const SLOT_CAVEAT_ENTRY_SIZE: usize = 6;
/// Base of the manifest array. Entry `i` lives at
/// `SLOT_CAVEAT_MANIFEST_BASE + i * SLOT_CAVEAT_ENTRY_SIZE`.
pub const SLOT_CAVEAT_MANIFEST_BASE: usize = 102;

// Type tags for the manifest (numerically distinct from any
// existing PI sentinel and from zero — zero means "no caveat").
pub const SLOT_CAVEAT_TAG_FIELD_EQUALS: u32 = 1;
pub const SLOT_CAVEAT_TAG_FIELD_GTE: u32 = 2;
pub const SLOT_CAVEAT_TAG_FIELD_LTE: u32 = 3;
pub const SLOT_CAVEAT_TAG_WRITE_ONCE: u32 = 4;
pub const SLOT_CAVEAT_TAG_IMMUTABLE: u32 = 5;
pub const SLOT_CAVEAT_TAG_MONOTONIC: u32 = 6;
pub const SLOT_CAVEAT_TAG_STRICT_MONOTONIC: u32 = 7;
pub const SLOT_CAVEAT_TAG_FIELD_DELTA: u32 = 8;
pub const SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE: u32 = 9;
pub const SLOT_CAVEAT_TAG_TEMPORAL_GATE: u32 = 10;
pub const SLOT_CAVEAT_TAG_SENDER_AUTHORIZED: u32 = 11;
pub const SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS: u32 = 12;

// ---- Cross-effect within-turn chain pinning (Proof-to-Action Binding §3.3) ----
//
// Per `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.3: when two effects in
// the same turn chain (e.g., `SpendNote` produces a nullifier that
// a later `BridgeMint` consumes in the same turn), the AIR needs to
// witness that the producer's output equals the consumer's input.
// Without this, a malicious executor could route the consumer to a
// different value than what the producer actually produced.
//
// The manifest is fixed-size — up to `MAX_CROSS_EFFECT_DEPS` entries
// of `CROSS_EFFECT_DEP_ENTRY_SIZE` felts each, prefixed by a
// single-felt count. Each entry is a 6-felt tuple:
//   [producer_index, consumer_index, field_tag, vc0, vc1, vc2]
// where:
//   - producer_index, consumer_index: u32-as-BabyBear indices into
//     the canonical DFS-traversal order of the call_forest;
//   - field_tag: discriminator for the named field (nullifier=1,
//     note_commitment=2, escrow_id=3, destination=4, note_tree_root=5);
//   - vc0..vc2: 3 of the 8 limbs of the chained 32-byte value
//     commitment, providing ~93-bit binding strength (one
//     commitment cell can pack 32 bytes only with 8 limbs; the
//     fixed manifest entry size of 6 felts holds the first 3 limbs;
//     callers that need stronger binding should additionally
//     submit an `EffectBindingProof` schema entry which carries the
//     full 8 limbs).
//
// The verifier-side off-AIR check (`TurnExecutor::verify_effect_binding_proofs`)
// enforces the full 32-byte algebraic match; the AIR slot here is the
// shared-PI surface that future row-bound enforcement (Stage 7-γ.3)
// will tie to specific trace rows of the producer/consumer effects.
pub const CROSS_EFFECT_DEPS_COUNT: usize =
    SLOT_CAVEAT_MANIFEST_BASE + MAX_SLOT_CAVEATS * SLOT_CAVEAT_ENTRY_SIZE; // 126
pub const MAX_CROSS_EFFECT_DEPS: usize = 4;
pub const CROSS_EFFECT_DEP_ENTRY_SIZE: usize = 6;
pub const CROSS_EFFECT_DEPS_BASE: usize = CROSS_EFFECT_DEPS_COUNT + 1; // 127

/// Field-name tags for cross-effect dependencies. Kept in sync with
/// `pyana_turn::binding_proof::EffectDependency::field_name` string
/// match in `TurnExecutor::extract_named_field_32b`.
pub const CROSS_EFFECT_FIELD_TAG_NULLIFIER: u32 = 1;
pub const CROSS_EFFECT_FIELD_TAG_NOTE_COMMITMENT: u32 = 2;
pub const CROSS_EFFECT_FIELD_TAG_ESCROW_ID: u32 = 3;
pub const CROSS_EFFECT_FIELD_TAG_DESTINATION: u32 = 4;
pub const CROSS_EFFECT_FIELD_TAG_NOTE_TREE_ROOT: u32 = 5;

// ---- Witness-blob → Effect indexing (Proof-to-Action Binding §3.2) ----
//
// Per `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.2: the runtime `Action`
// carries `witness_blobs: Vec<WitnessBlob>` and witness-attached
// predicates reference blobs by `proof_witness_index`. The Effect VM
// currently does not bind which witness blob feeds which effect: a
// malicious executor could shuffle blobs so that an effect needing
// witness K reads bytes meant for effect L.
//
// Fix: a per-effect `witness_blob_index` manifest. Each entry is a
// 2-felt tuple:
//   [effect_index, witness_index]
// both as u32-as-BabyBear. Unused entries are zero-padded; the
// count prefix tells the verifier how many entries are live.
//
// The off-AIR verifier checks well-formedness (bounds, no-dupes); a
// future per-effect AIR slot binds the witness blob's BLAKE3 hash to
// the effect's row-0 columns for full algebraic enforcement.
pub const WITNESS_INDEX_MAP_COUNT: usize =
    CROSS_EFFECT_DEPS_BASE + MAX_CROSS_EFFECT_DEPS * CROSS_EFFECT_DEP_ENTRY_SIZE; // 127 + 24 = 151
pub const MAX_WITNESS_INDEX_ENTRIES: usize = 8;
pub const WITNESS_INDEX_ENTRY_SIZE: usize = 2;
pub const WITNESS_INDEX_MAP_BASE: usize = WITNESS_INDEX_MAP_COUNT + 1; // 152

// ---- Stage 7-γ.2 unilateral binding (1-arity sibling of bilateral) ----
//
// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.5: γ.2 binds pairs (Transfer,
// Grant) and triples (Introduce) but has no 1-arity sibling. *Unilateral*
// attestations are the dual — a single cell self-attests to a property
// over its own transitions (state, nonce bump, sovereign-witness signing)
// *without a counterparty*. They compose with `peer_exchange`'s
// federation-bypass primitive: a peer state transition can carry one
// unilateral attestation, and the receiver verifies it against the
// sender's cell-id-derived canonical encoding.
//
// PI shape (append-only after `WITNESS_INDEX_MAP`):
//   - `UNILATERAL_ATTESTATIONS_COUNT` (1 felt): number of unilateral
//     attestations this turn produced for this cell.
//   - `UNILATERAL_ATTESTATIONS_ROOT_BASE` (4 felts): Merkle/Poseidon2
//     accumulator over the `(attestation_kind, attestation_data)` tuples,
//     order-preserving DFS. The future AIR boundary constraint pins the
//     in-trace `unilateral_root` aux column to this PI slot — same shape
//     as the bilateral roots (γ.2.1 work). Today the off-AIR verifier
//     recomputes the expected accumulator from the bundle's declared
//     attestation list and rejects any mismatch.
//
// Sentinel: `[BabyBear::ZERO; 4]` when count == 0. Distinct salt per
// attestation kind ensures `SelfStateTransition` cannot be confused with
// `SelfNonceBump` even at colliding data.
pub const UNILATERAL_ATTESTATIONS_COUNT: usize =
    WITNESS_INDEX_MAP_BASE + MAX_WITNESS_INDEX_ENTRIES * WITNESS_INDEX_ENTRY_SIZE; // 168
pub const UNILATERAL_ATTESTATIONS_ROOT_BASE: usize = UNILATERAL_ATTESTATIONS_COUNT + 1; // 169
pub const UNILATERAL_ATTESTATIONS_ROOT_LEN: usize = 4;

/// Maximum unilateral attestations the off-AIR verifier walks per turn.
/// The accumulator size is independent of this cap (4-felt root); the
/// cap is a guardrail on the schedule reconstruction.
pub const MAX_UNILATERAL_ATTESTATIONS: usize = 8;

// Type tags for `UnilateralAttestationKind` — kept in sync with
// `pyana_turn::bilateral_schedule::UnilateralAttestationKind`. Zero is
// the "no attestation" sentinel (count == 0 → all data zero).
pub const UNILATERAL_ATTESTATION_KIND_SELF_STATE_TRANSITION: u32 = 1;
pub const UNILATERAL_ATTESTATION_KIND_SELF_NONCE_BUMP: u32 = 2;
pub const UNILATERAL_ATTESTATION_KIND_SOVEREIGN_WITNESS: u32 = 3;
/// `Custom { kind_tag }` flattens to the high half of u32 space: bit 31
/// would put us out of canonical BabyBear, so kind_tag is masked to 30
/// bits and OR'd with this discriminant.
pub const UNILATERAL_ATTESTATION_KIND_CUSTOM_BASE: u32 = 0x4000_0000;

// ---- EmitEvent algebraic binding (closes #110) ----
//
// Per `EFFECT-VM-EMIT-EVENT.md` (lane Opus AIR-structural, 2026-05-25):
// the EffectVmAir previously only carried a single-felt `event_hash` for
// `Effect::EmitEvent`, which collided with the runtime `Event { topic,
// data }` canonical encoding (32B topic ‖ 32B payload). The MCP
// `pyana_register_service` tool was synthesising a `SetField` row as a
// workaround. These PI slots replace that workaround with a real
// algebraic binding:
//
//   PI[EMIT_EVENT_COUNT]                          number of EmitEvent rows
//                                                 in this trace.
//   PI[EMIT_EVENT_TOPIC_HASH_BASE..+8]            8-felt projection of the
//                                                 canonical topic hash (full
//                                                 256-bit binding).
//   PI[EMIT_EVENT_PAYLOAD_HASH_BASE..+8]          8-felt projection of the
//                                                 canonical payload hash
//                                                 (full 256-bit binding).
//
// The AIR per-row constraint (gated by `sel::EMIT_EVENT`) pins
// `params[0..4]` to `PI[EMIT_EVENT_TOPIC_HASH][0..4]` and `params[4..8]`
// to `PI[EMIT_EVENT_PAYLOAD_HASH][0..4]`, giving algebraic ~124-bit
// binding inside the AIR. The high halves (`[4..8]` of each) are bound
// via `compute_effects_hash` absorption (which ingests all 16 felts
// per emit-event row) and via the off-AIR verifier's PI-match loop
// (which recomputes the canonical hashes from the runtime `Event`).
//
// Sentinel: when count == 0, both 8-felt slots are `[BabyBear::ZERO; 8]`.
// Soundness: with the per-row equality constraint, all emit-event rows
// in one proof must share the same hashes. Multi-emit-distinct-hashes
// requires PI extension (deferred).
pub const EMIT_EVENT_COUNT: usize =
    UNILATERAL_ATTESTATIONS_ROOT_BASE + UNILATERAL_ATTESTATIONS_ROOT_LEN; // 173
pub const EMIT_EVENT_TOPIC_HASH_BASE: usize = EMIT_EVENT_COUNT + 1; // 174
pub const EMIT_EVENT_TOPIC_HASH_LEN: usize = 8;
pub const EMIT_EVENT_PAYLOAD_HASH_BASE: usize =
    EMIT_EVENT_TOPIC_HASH_BASE + EMIT_EVENT_TOPIC_HASH_LEN; // 182
pub const EMIT_EVENT_PAYLOAD_HASH_LEN: usize = 8;

pub const BASE_COUNT: usize = EMIT_EVENT_PAYLOAD_HASH_BASE + EMIT_EVENT_PAYLOAD_HASH_LEN; // 190
/// Elements per custom effect entry in PI (8 vk_hash + 4 proof_commit).
/// Was 8 in PI layout v1; widened to 12 in v2 (`VK_PI_LAYOUT_VERSION == 2`).
pub const CUSTOM_ENTRY_SIZE: usize = 12;

// ---- Hard cap on declared max_custom_effects ----
/// Hard ceiling: a cell declaring more than this is refused at registration
/// time. Per `DESIGN-max-custom-effects.md` §5, bounds worst-case verifier
/// child-proof work to ~3.2s/turn at 50ms/proof.
pub const MAX_CUSTOM_EFFECTS_HARD_CAP: u8 = 64;
/// Soft cap: the recommended workspace ceiling. Cells declaring up to this
/// are uncontroversial; cells declaring 17..64 should justify the choice.
pub const MAX_CUSTOM_EFFECTS_SOFT_CAP: u8 = 16;
/// Default value for cells that don't declare a per-cell max. Matches the
/// pre-Stage-1 workspace constant.
pub const MAX_CUSTOM_EFFECTS_DEFAULT: u8 = 4;

// AUDIT[stage1-pi-only-bound]: PI[OLD_COMMIT_BASE+1..+4],
// PI[NEW_COMMIT_BASE+1..+4], PI[EFFECTS_HASH_BASE+1..+4], and the entire
// PI[APPROVED_HANDOFFS_BASE..+4] are bound only by the executor's PI
// matching loop (deterministic recomputation from cell/federation
// state), not by per-row AIR constraints. Stage 2 may add aux columns
// to anchor positions 1..3 of state-commit forms inside the trace.
