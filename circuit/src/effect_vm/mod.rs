//! Effect VM AIR: Multi-row DSL circuit proving arbitrary sequences of effects
//! (turns) in a single STARK proof.
//!
//! Inspired by o1vm (RISC-V execution trace proving), but for dregg Effects instead
//! of CPU instructions. Each trace row represents one effect execution step.
//!
//! # Instruction Set (Effect Types)
//!
//! - NoOp (0): Padding effect; all constraints trivially satisfied.
//! - Transfer (1): Balance transfer with direction (in/out).
//! - SetField (2): Update a custom field slot.
//! - GrantCapability (3): Add capability to c-list (capability_root update).
//! - NoteSpend (4): Spend a note (nullifier reveal, balance credit).
//! - NoteCreate (5): Create a note (commitment creation, balance debit).
//! - CreateObligation (6): Lock stake from balance as a bonded obligation.
//! - FulfillObligation (7): Return locked stake on successful fulfillment.
//! - Custom (8): CellProgram dispatch — state flows unchanged, domain constraints
//!   proven externally. Params carry program VK hash + proof commitment.
//! - SlashObligation (9): Slash an expired obligation.
//! - Seal (10): Lock a field against mutation.
//! - Unseal (11): Unlock a sealed field.
//! - MakeSovereign (12): Transition cell from managed to sovereign.
//! - CreateCellFromFactory (13): Record factory provenance.
//! - ExportSturdyRef (14): Export cell as sturdy ref (CapTP).
//! - EnlivenRef (15): Enliven a sturdy ref (CapTP).
//! - DropRef (16): Drop a remote reference / GC decrement (CapTP).
//! - ValidateHandoff (17): Validate a handoff certificate (CapTP).
//! - AllocateQueue (18): Create a new MerkleQueue (storage Phase 2).
//! - EnqueueMessage (19): Append message to queue (storage Phase 2).
//! - DequeueMessage (20): Advance queue head, reveal message (storage Phase 2).
//! - ResizeQueue (21): Change queue capacity (storage Phase 2).
//! - AtomicQueueTx (22): Prove atomic cross-queue transaction (storage Phase 3).
//! - PipelineStep (23): Prove pipeline step correctly routed a message (storage Phase 3).
//! - Burn (46): Explicit non-conservation balance reduction (near-miss aliasing closure).
//! - CellDestroy (47): Permanently retire a cell (near-miss aliasing closure).
//! - AttenuateCapability (48): Narrow a c-list cap (near-miss aliasing closure).
//! - CellSeal (49): Transition cell lifecycle to Sealed (AIR-impl lane #119).
//! - CellUnseal (50): Reverse a cell seal (AIR-impl lane #119).
//! - ReceiptArchive (51): Summarize receipt-chain prefix (AIR-impl lane #119).
//! - Refusal (52): Evidence-of-absence attestation (AIR-impl lane #119).
//!
//! # Trace Layout (one row per effect)
//!
//! ```text
//! | selector[24] | state_before[14] | effect_params[8] | state_after[14] | aux[11] |
//! ```
//!
//! Total width: 71 columns
//!
//! ## Column Breakdown
//!
//! Selectors (cols 0..9): Exactly one active per row.
//!   - sel_noop, sel_transfer, sel_setfield, sel_grantcap, sel_notespend, sel_notecreate,
//!     sel_create_obligation, sel_fulfill_obligation, sel_custom
//!
//! State Before (cols 9..23):
//!   - balance_lo, balance_hi (u64 as two BabyBear limbs, 30+34 bits)
//!   - nonce
//!   - field_values[0..7] (8 custom fields)
//!   - capability_root
//!   - state_commitment (running Poseidon2 hash of full state)
//!   - reserved
//!
//! Effect Params (cols 23..31):
//!   - param0..param7 (meaning depends on effect type)
//!
//! State After (cols 31..45):
//!   - Same layout as state_before
//!
//! Aux (cols 50..61):
//!   - Auxiliary witness values (intermediate hashes, commitment tree nodes)
//!   - aux[8..10]: state commitment tree intermediates (hash_4_to_1 outputs)
//!
//! # Constraints
//!
//! 1. Selector exclusivity: sum(selectors) == 1, each selector is boolean.
//! 2. Per-effect constraints (gated by selector):
//!    - Transfer: new_balance = old_balance +/- amount
//!    - SetField: one field updated, others unchanged
//!    - GrantCap: capability_root = hash(old_root, new_entry)
//!    - NoteSpend: nullifier valid, balance increases
//!    - NoteCreate: commitment valid, balance decreases
//!    - CreateObligation: balance decreases by stake_amount
//!    - FulfillObligation: balance increases by stake_return
//!    - Custom: state unchanged (domain constraints proven externally)
//! 3. Transition constraints (row-to-row continuity):
//!    - next_row.state_before == this_row.state_after
//!    - next_row.nonce == this_row.nonce + 1 (or same for NoOp padding)
//! 4. Boundary constraints:
//!    - First row: state_before matches old_commitment (public input)
//!    - Last non-padding row: state_after matches new_commitment
//!    - Conservation: net balance delta == public input
//!
//! # Public Inputs
//!
//! Base layout (`pi::BASE_COUNT` felts, Stage 7-γ.2 Phase 1 widening):
//!
//! ```text
//!   [ 0.. 4]  OLD_COMMIT[4]                   cell pre-state commitment (Poseidon2)
//!   [ 4.. 8]  NEW_COMMIT[4]                   cell post-state commitment (Poseidon2)
//!   [ 8..12]  EFFECTS_HASH[4]                 Poseidon2 over per-cell projected effects
//!   [12]      INIT_BAL_LO                     row 0 balance low limb
//!   [13]      INIT_BAL_HI                     row 0 balance high limb
//!   [14]      FINAL_BAL_LO                    last row balance low limb
//!   [15]      FINAL_BAL_HI                    last row balance high limb
//!   [16]      NET_DELTA_MAG                   |Δbalance|
//!   [17]      NET_DELTA_SIGN                  0 = +, 1 = −
//!   [18]      CURRENT_BLOCK_HEIGHT            federation block height
//!   [19]      MAX_CUSTOM_EFFECTS              per-cell manifest cap
//!   [20]      CUSTOM_EFFECT_COUNT             Σ sel_custom in trace
//!   [21..25]  APPROVED_HANDOFFS[4]            CapTP federation-scoped Merkle root
//!   [25..29]  TURN_HASH[4]                    Poseidon2 of Turn::hash() (7-γ.0a)
//!   [29..33]  EFFECTS_HASH_GLOBAL[4]          Poseidon2 over canonical-DFS call_forest effects (7-γ.0a)
//!   [33]      ACTOR_NONCE                     outer Turn::nonce (7-γ.0a; closes W-1 nonce gap)
//!   [34..38]  PREVIOUS_RECEIPT_HASH[4]        Poseidon2 of previous_receipt_hash (7-γ.0a)
//!   [38..45]  bilateral counts (7-γ.2): outbound_transfer, inbound_transfer,
//!                                       outbound_grant, inbound_grant,
//!                                       intro_introducer, intro_recipient, intro_target
//!   [45..49]  OUTGOING_TRANSFER_ROOT[4]       (7-γ.2)
//!   [49..53]  INCOMING_TRANSFER_ROOT[4]       (7-γ.2)
//!   [53..57]  OUTGOING_GRANT_ROOT[4]          (7-γ.2)
//!   [57..61]  INCOMING_GRANT_ROOT[4]          (7-γ.2)
//!   [61..65]  INTRO_AS_INTRODUCER_ROOT[4]     (7-γ.2)
//!   [65..69]  INTRO_AS_RECIPIENT_ROOT[4]      (7-γ.2)
//!   [69..73]  INTRO_AS_TARGET_ROOT[4]         (7-γ.2)
//!   [73]      IS_AGENT_CELL                   (7-γ.2; 1 iff this proof is the actor's)
//!   ... (sovereign-witness teeth, value-limbs, slot-caveat / cross-effect /
//!        witness-index manifests; see `pi::BASE_COUNT` for the precise tail
//!        layout) ...
//!   [168]     UNILATERAL_ATTESTATIONS_COUNT   (7-γ.2 unilateral; number of self-attestations this turn)
//!   [169..173] UNILATERAL_ATTESTATIONS_ROOT[4] (7-γ.2 unilateral; Merkle/Poseidon2 accumulator over (kind, data) tuples)
//!   [173..]   CUSTOM_PROOFS                   per-custom-effect (vk_hash[4], proof_commit[4])
//! ```
//!
//! The four 7-γ.0a additions (TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//! PREVIOUS_RECEIPT_HASH) are *shared across all per-cell proofs of one
//! turn*. The verifier's cross-proof PI matching loop
//! (`verify_proof_carrying_turn_bundle` in `turn::executor`) enforces
//! equality across the N proofs; per-proof binding to the canonical
//! Turn::hash / call_forest is the executor's responsibility for now and
//! becomes algebraic at Stage 7-γ.1.

// ============================================================================
// Sub-module layout
// ============================================================================
//
// The Effect VM AIR was originally one monolithic 10k-line file. It now
// decomposes by concern:
//   columns   — trace width + per-block column index sub-modules (sel,
//                state, param, aux_off).
//   pi        — public-input slot constants.
//   effect    — the `Effect` enum (one variant per effect type).
//   cell_state — the `CellState` struct + commitment helpers.
//   helpers   — limb split/join, reserved-bit fill, compute_effects_hash[_4].
//   air       — `AIR_DESCRIPTOR`, `EffectVmAir`, `StarkAir` impl.
//   trace     — witness/trace generation + `EffectVmContext`.
//   verify    — verifier-side range / slot-caveat checks.
//   tests     — the (large) #[cfg(test)] module.
//
// External callers see the pre-decomp public surface preserved via
// re-exports below (no path changes needed).

pub mod columns;
pub mod pi;

mod air;
mod cell_state;
mod effect;
mod helpers;
mod trace;
mod verify;

#[cfg(test)]
mod tests;

// ---- Re-export column layout (preserves pre-decomp paths) ----
pub use columns::{
    AUX_BASE, EFFECT_VM_WIDTH, NUM_AUX, NUM_EFFECTS, NUM_PARAMS, PARAM_BASE, STATE_AFTER_BASE,
    STATE_BEFORE_BASE, aux_off, param, sel, state,
};

// ---- Re-export types ----
pub use cell_state::CellState;
pub use effect::Effect;

// ---- Re-export helpers ----
pub use helpers::{
    bytes32_to_8_limbs, compute_effects_hash, compute_effects_hash_4, fold_bytes32_to_bb,
    split_u64, u64_from_4_limbs_16, u64_to_4_limbs_16,
};
// Re-export so sibling modules can write `use super::fill_reserved_bits`
// (mirrors the pre-decomp module-level visibility).
pub(crate) use helpers::fill_reserved_bits;

// ---- Re-export AIR ----
pub use air::{AIR_DESCRIPTOR, EffectVmAir};

// ---- Re-export trace generation ----
pub use trace::{
    EffectVmContext, SlotCaveatEntry, canonical_id_to_felts_4, encode_net_delta,
    extract_custom_proof_commitments, extract_net_delta, extract_slot_caveat_manifest,
    generate_effect_vm_trace, generate_effect_vm_trace_ext,
};

// ---- Re-export verify ----
pub use verify::{
    verify_balance_limb_pis, verify_balance_limb_ranges, verify_slot_caveat_manifest,
    verify_state_integrity,
};
