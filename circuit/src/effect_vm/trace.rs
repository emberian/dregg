//! Witness/trace generation for the Effect VM AIR.
//!
//! Builds the trace matrix and PI vector for each variant of `Effect`,
//! including the widened `EffectVmContext` carrying turn-identity,
//! slot-caveat manifests, and per-effect commitment witnesses.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};

use super::{
    AUX_BASE, CellState, EFFECT_VM_WIDTH, Effect, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE,
    aux_off, compute_effects_hash, compute_effects_hash_4, fill_balance_limb_bits,
    fill_reserved_bits, param, pi, sel, split_u64, state, u64_to_4_limbs_16,
};

/// Compress a 32-byte canonical id (federation id or cell id) into 4 BabyBear
/// felts (γ.2 #131/#132 per-cell federation + owner binding).
///
/// This is bit-identical to `dregg_commit::typed::canonical_32_to_felts_4`,
/// re-implemented here so the `dregg-circuit` crate stays free of a
/// `dregg-commit` dependency while still producing the same felts the
/// off-AIR verifier (`turn::executor::proof_verify`) reconstructs. Any drift
/// between the two would show up immediately as a PI-match rejection in the
/// `federation_owner_binding_round_trip` test and the executor PI loop — and,
/// since that claim was never actually tested between the two functions,
/// `commit/tests/key_octet_f2_twins_and_the_hole.rs` pins them directly.
///
/// ## ⚑ 2026-08-01 — twin #4 of the nonet
///
/// The inlined packing here was the 30-bit octet (`hi & 0x3F`, sixteen source bits discarded),
/// and the four `hash_4_to_1` folds ran over it, so any two ids the packer merged produced the
/// identical four felts: the `federation_id` / `owner_cell_id` PI binding was `2^16`-degenerate
/// by construction, one XOR from any id. It is now one `CHIP_NODE8_ARITY` absorb over the
/// base-`2^29` **nonet** `‖ 0⁷`, first four output lanes — the same permutation
/// `dregg_commit::typed::compress_member` rides.
///
/// ## ⚑ 2026-08-02 — the inline copy is GONE
///
/// The nonet loop used to be re-typed here, in the body, which meant the twin corpus in
/// `commit/tests/key_octet_f2_twins_and_the_hole.rs` pinned three transcriptions and could not
/// see the fourth: an unnamed inline copy is exactly the copy a twin test cannot reach. It now
/// calls [`crate::effect_vm::key_limbs9`], which the corpus DOES pin. Zero felts moved — the
/// hoisted body is the same loop — and the drift surface is one name shorter.
pub fn canonical_id_to_felts_4(canonical: &[u8; 32]) -> [BabyBear; 4] {
    use crate::descriptor_ir2::{CHIP_NODE8_ARITY, chip_absorb_all_lanes};
    let mut ins = [BabyBear::ZERO; 16];
    ins[..9].copy_from_slice(&crate::effect_vm::key_limbs9(canonical));
    let out = chip_absorb_all_lanes(CHIP_NODE8_ARITY, &ins);
    [out[0], out[1], out[2], out[3]]
}

/// The Effect-VM selector column index for one `Effect` — the single source of truth the
/// trace generator writes into the selector block AND the rotated descriptor resolver reads
/// (`effect_vm::trace_rotated::rotated_descriptor_name_for_effect`).
pub fn effect_selector(effect: &Effect) -> usize {
    match effect {
        Effect::NoOp => sel::NOOP,
        Effect::Transfer { .. } => sel::TRANSFER,
        Effect::SetField { .. } => sel::SET_FIELD,
        Effect::GrainTurn { .. } => sel::GRAIN_TURN,
        Effect::GrantCapability { .. } => sel::GRANT_CAP,
        Effect::NoteSpend { .. } => sel::NOTE_SPEND,
        Effect::NoteCreate { .. } => sel::NOTE_CREATE,
        Effect::Custom { .. } => sel::CUSTOM,
        Effect::MakeSovereign => sel::MAKE_SOVEREIGN,
        Effect::CreateCellFromFactory { .. } => sel::CREATE_CELL_FROM_FACTORY,
        Effect::RevokeCapability { .. } => sel::REVOKE_CAPABILITY,
        Effect::EmitEvent { .. } => sel::EMIT_EVENT,
        Effect::SetPermissions { .. } => sel::SET_PERMISSIONS,
        Effect::SetVerificationKey { .. } => sel::SET_VERIFICATION_KEY,
        Effect::RefreshDelegation { .. } => sel::REFRESH_DELEGATION,
        Effect::IncrementNonce => sel::INCREMENT_NONCE,
        Effect::RevokeDelegation { .. } => sel::REVOKE_DELEGATION,
        Effect::CreateCell { .. } => sel::CREATE_CELL,
        Effect::SpawnWithDelegation { .. } => sel::SPAWN_WITH_DELEGATION,
        Effect::ExerciseViaCapability { .. } => sel::EXERCISE_VIA_CAPABILITY,
        Effect::Introduce { .. } => sel::INTRODUCE,
        Effect::PipelinedSend { .. } => sel::PIPELINED_SEND,
        Effect::BridgeMint { .. } => sel::BRIDGE_MINT,
        Effect::Mint { .. } => sel::MINT,
        Effect::Burn { .. } => sel::BURN,
        Effect::CellDestroy { .. } => sel::CELL_DESTROY,
        Effect::AttenuateCapability { .. } => sel::ATTENUATE_CAPABILITY,
        Effect::CellSeal { .. } => sel::CELL_SEAL,
        Effect::CellUnseal { .. } => sel::CELL_UNSEAL,
        Effect::ReceiptArchive { .. } => sel::RECEIPT_ARCHIVE,
        Effect::Refusal { .. } => sel::REFUSAL,
    }
}

/// Generate the execution trace and public inputs for an effect VM proof.
///
/// # Arguments
/// * `initial_state` - The cell state before executing effects.
/// * `effects` - The sequence of effects to prove.
///
/// # Returns
/// (trace, public_inputs) suitable for `stark::prove`.
///
/// PANICS on a witness outside the AIR's domain — use [`try_generate_effect_vm_trace`]
/// from anywhere a COMMITTED turn can reach.
pub fn generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // Stage 7 / §B: for the default-context wrapper, set actor_nonce
    // from the initial cell nonce. This is the natural invariant for
    // single-cell proofs (the cell IS the agent), and it preserves
    // backwards-compat with the dozens of tests that pass a non-zero
    // initial nonce to CellState::new and rely on the row-0 boundary
    // (state_before.nonce == PI[ACTOR_NONCE]) holding.
    let ctx = EffectVmContext {
        actor_nonce: initial_state.nonce as u64,
        ..Default::default()
    };
    generate_effect_vm_trace_ext(initial_state, effects, ctx)
}

/// The CHECKED default-context trace generator — [`generate_effect_vm_trace`]'s
/// refusal-returning twin. Every prover entry point a committed turn can reach
/// (`node::turn_proving`, the async prove pool behind it) goes through this one, so a
/// witness the AIR cannot carry becomes a typed error at the caller instead of an
/// unwind that skips whatever the caller was going to do next — which, on the
/// finalized path, is the durable commit-log write (#62).
pub fn try_generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), EffectVmTraceError> {
    let ctx = EffectVmContext {
        actor_nonce: initial_state.nonce as u64,
        ..Default::default()
    };
    try_generate_effect_vm_trace_ext(initial_state, effects, ctx)
}

/// Extra context that goes into the widened PI layout (Stage 1 + 7-γ.0a).
///
/// All fields have safe defaults for backwards-compat: zero block height,
/// default `max_custom_effects`, empty approved-handoffs root, and
/// all-zero Stage 7-γ.0a turn-identity fields. Callers that produce
/// real per-cell proofs in the executor populate the γ.0a fields from
/// the live `Turn` and call_forest.
#[derive(Clone, Copy, Debug)]
pub struct EffectVmContext {
    /// Per-cell maximum custom effects (from cell program manifest). Read only by this
    /// module's own `custom_count <= max_custom_effects` assertion — the enforcing bound is
    /// the VERIFIER's, off-circuit, from its own ledger
    /// (`TurnExecutor::read_cell_max_custom_effects`).
    pub max_custom_effects: u8,
    // ⚑ `current_block_height` and `approved_handoffs_root` were DELETED here on 2026-08-07
    // with the PI slots they fed (`docs/PI-DISPOSITION.md` §6). Each had exactly one reader —
    // the `PI[CURRENT_BLOCK_HEIGHT]` / `PI[APPROVED_HANDOFFS_BASE..+4]` fill below — and
    // NOTHING ever wrote either: every producer took the `Default` (`0`, and the empty-tree
    // sentinel), so both published a constant on every proof in the system. The live temporal
    // binding is `v3::COMMITTED_HEIGHT`, which the verifier overrides from the trusted
    // committed state; `ValidateHandoff` has not been an effect since the verb-lockstep pass.
    /// Stage 7-γ.0a: Poseidon2 of canonical `Turn::hash()` (v3). Shared
    /// across all per-cell proofs of one turn.
    pub turn_hash: [BabyBear; 4],
    /// Stage 7-γ.0a: Poseidon2 over the canonical-DFS-order traversal
    /// of the entire call_forest's effects. Shared across the bundle.
    pub effects_hash_global: [BabyBear; 4],
    /// Stage 7-γ.0a: outer `Turn::nonce` promoted to PI; closes the
    /// differential-test gap from task #49 (AIR did not witness the
    /// agent's outer nonce bump). Shared across the bundle.
    pub actor_nonce: u64,
    /// Stage 7-γ.0a: Poseidon2 of `previous_receipt_hash` (or zero
    /// sentinel when None). Shared across the bundle.
    pub previous_receipt_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): when this proof attests to a
    /// sovereign-witnessed effect, the 4-felt Poseidon2 hash of the
    /// witness's owning pubkey. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4]. Zero sentinel for
    /// hosted-cell proofs.
    pub sovereign_witness_key_commit: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): per-cell monotonic sequence
    /// from the witness. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_SEQUENCE]. Zero sentinel for hosted-cell
    /// proofs.
    pub sovereign_witness_sequence: u64,
    /// Sovereign-witness teeth (Phase 1): 1 iff this is a sovereign
    /// witnessed proof; 0 otherwise. Drives the (a)-style sentinel
    /// agreement between prover and verifier (no actual gating in the
    /// AIR — sentinel zeros on both sides make the boundary trivial
    /// when off).
    pub is_sovereign_cell: bool,
    /// Sovereign-witness teeth (Phase 2): 4-felt VK hash of the AIR the
    /// inner transition_proof was generated under. Zero sentinel when
    /// no transition_proof is supplied.
    pub sovereign_transition_proof_vk_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 4-felt Poseidon2 hash of the
    /// canonical inner-proof bytes. Zero sentinel when no transition_proof
    /// is supplied.
    pub sovereign_transition_proof_commitment: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 1 iff a transition_proof
    /// was supplied AND `is_sovereign_cell` is true.
    pub has_transition_proof: bool,

    /// 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5): 4×16-bit
    /// little-endian limbs of the full u64 `BridgeMint.value`. Position 0
    /// is the low 16 bits; position 3 is the high. Each limb < 2^16.
    /// Zero sentinel when no BridgeMint effect is in the trace.
    pub bridge_mint_value_limbs: [BabyBear; 4],
    /// RETIRED (VERB-LOCKSTEP): `BridgeLock` is gone; always zero.
    pub bridge_lock_value_limbs: [BabyBear; 4],
    /// RETIRED (VERB-LOCKSTEP): `CreateEscrow` is gone; always zero.
    pub create_escrow_amount_limbs: [BabyBear; 4],

    /// Slot-caveat manifest (Cav-Codex Block 3). Cell-program-declared
    /// `StateConstraint` set, projected into a fixed-size table for
    /// row-boundary AIR enforcement. `slot_caveat_count` ∈ [0,
    /// `pi::MAX_SLOT_CAVEATS`]; `slot_caveat_manifest[..count]`
    /// carries the entries.
    pub slot_caveat_count: u32,
    pub slot_caveat_manifest: [SlotCaveatEntry; pi::MAX_SLOT_CAVEATS],

    /// γ.2 follow-up (#131): the 32-byte federation id under which this proof
    /// is minted. Compressed to 4 felts via [`canonical_id_to_felts_4`] and
    /// pinned to PI[FEDERATION_ID_BASE..+4] + the row-0 aux columns. Zero by
    /// default (a fresh federation id of all-zeros is the local-federation
    /// sentinel, matching `TurnExecutor::local_federation_id`'s default).
    pub federation_id: [u8; 32],
    /// γ.2 follow-up (#132): the 32-byte owner cell id whose state transition
    /// this proof attests. Compressed to 4 felts via
    /// [`canonical_id_to_felts_4`] and pinned to PI[OWNER_CELL_ID_BASE..+4] +
    /// the row-0 aux columns. Zero by default (back-compat for callers that
    /// do not yet thread the owner id through; the off-AIR verifier supplies
    /// the same sentinel so the binding holds trivially).
    pub owner_cell_id: [u8; 32],

    /// PI v3 (THE ROTATION): the block height at which this cell's state was
    /// last committed. Bound to the canonical commitment as a commitment limb,
    /// so the PI face cannot be prover-chosen. Zero default (legacy / fresh
    /// cells) is a valid committed height.
    pub committed_height: u64,
    /// PI v3: rate-bound caveat tag. Semantics are staged: today this is the
    /// zero sentinel; the optimistic-proving mode (#169) will populate it.
    pub rate_bound_tag: u32,
    /// PI v3: challenge-window caveat tag. Semantics are staged: today this is
    /// the zero sentinel; the dispute/slashing mode (#169) will populate it.
    pub challenge_window_tag: u32,

    /// PI v3 (light-client conservation): the per-cell ASSET CLASS, a single
    /// field element folding the cell's committed `token_id` (dregg3: AssetId :=
    /// issuer-cell). Surfaced to `PI[v3::ASSET_CLASS]` and pinned to the row-0
    /// `aux_off::ASSET_CLASS` aux column by a boundary constraint, so the proof
    /// COMMITS to its asset class. The per-asset cross-cell conservation gate
    /// groups each per-cell proof's NET_DELTA by this PI-bound class, enforcing
    /// per-asset Σδ=0 WITHOUT a ledger lookup. Zero by default (the native /
    /// computron asset, and back-compat for callers that do not yet thread the
    /// asset class through — the executor reconstructs the expected value from
    /// the trusted ledger token_id and the boundary holds trivially at zero).
    pub asset_class: BabyBear,
}

/// A single entry in the slot-caveat manifest (Cav-Codex Block 3).
///
/// `type_tag` is one of `pi::SLOT_CAVEAT_TAG_*` (zero means "no
/// caveat"); `slot_index` is the cell-state field index; `params` are
/// up to 4 numeric parameters or a 4-felt commitment (the variant
/// determines the encoding — see `populate_slot_caveat_manifest`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SlotCaveatEntry {
    pub type_tag: u32,
    pub slot_index: u8,
    pub params: [BabyBear; 4],
}

impl SlotCaveatEntry {
    pub const fn zero() -> Self {
        Self {
            type_tag: 0,
            slot_index: 0,
            params: [BabyBear::ZERO; 4],
        }
    }

    /// Encode this entry into `out[..SLOT_CAVEAT_ENTRY_SIZE]` as
    /// (type_tag, slot_index, p0, p1, p2, p3).
    pub fn write_to(&self, out: &mut [BabyBear]) {
        debug_assert!(out.len() >= pi::SLOT_CAVEAT_ENTRY_SIZE);
        out[0] = BabyBear::new(self.type_tag);
        out[1] = BabyBear::new(self.slot_index as u32);
        out[2..6].copy_from_slice(&self.params);
    }
}

/// STAGED (THE ROTATION — the widened caveat operand,
/// `.docs-history-noclaude/ROTATION-CUTOVER.md` §3 pre-gate). NOTHING live reads this type:
/// the live `SlotCaveatEntry` manifest at PI 101..126 is untouched; the
/// staged probe + tamper teeth ride the recursion-gated IR-v2 path
/// (`descriptor_ir2.rs`).
///
/// The rotated caveat entry widens `SlotCaveatEntry`'s `slot_index: u8` into
/// a DOMAIN-TAGGED operand `(domain_tag, key)` on the universal-memory
/// `UDomain` wire codes (registers 0 · heap 1 — `turn/src/umem.rs`): the
/// heap is the app-state lane, so capability attenuation must scope to heap
/// keys, and heap keys are FELTS (no u8 can carry them). A register (slot)
/// operand can NEVER alias a heap operand — domain separation is a THEOREM
/// (`caveat_operand_no_aliasing`,
/// `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean`), the
/// same discipline as the umem `Domain` tags. 7-felt packing:
/// `[type_tag, domain_tag, key, p0, p1, p2, p3]`
/// (`columns::rotation::caveat::ENTRY_SIZE`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotCaveatEntry {
    /// One of `pi::SLOT_CAVEAT_TAG_*` (the slot and heap planes share ONE
    /// tag space); zero means "no caveat".
    pub type_tag: u32,
    /// `caveat::DOMAIN_REGISTERS` (0) or `caveat::DOMAIN_HEAP` (1). Decode
    /// REFUSES anything else (fail closed — there is no default plane).
    pub domain_tag: u32,
    /// The in-domain key: a register index (`< caveat::R`) in the registers
    /// domain; an arbitrary heap-key felt in the heap domain.
    pub key: BabyBear,
    pub params: [BabyBear; 4],
}

impl RotCaveatEntry {
    pub const SIZE: usize = super::columns::rotation::caveat::ENTRY_SIZE;

    pub const fn zero() -> Self {
        Self {
            type_tag: 0,
            domain_tag: 0,
            key: BabyBear::ZERO,
            params: [BabyBear::ZERO; 4],
        }
    }

    /// Encode this entry into `out[..SIZE]` as
    /// `(type_tag, domain_tag, key, p0, p1, p2, p3)`.
    pub fn write_to(&self, out: &mut [BabyBear]) {
        debug_assert!(out.len() >= Self::SIZE);
        out[0] = BabyBear::new(self.type_tag);
        out[1] = BabyBear::new(self.domain_tag);
        out[2] = self.key;
        out[3..7].copy_from_slice(&self.params);
    }

    /// Decode an entry from its 7-felt packing — FAIL CLOSED:
    ///   * a forged/unknown domain tag REFUSES (only registers/heap are
    ///     caveat-scopable; caps/nullifiers/index are kernel planes);
    ///   * a registers-domain key outside the rotated register file
    ///     (`>= caveat::R`, the CONFIRMED R=24) REFUSES;
    ///   * a heap-domain key is any felt (heap keys are felts — the point).
    ///
    /// The zero entry (`type_tag == 0`) decodes as "no caveat" with no
    /// further checks (the all-zero padding rows).
    pub fn from_felts(f: &[BabyBear]) -> Result<Self, String> {
        use super::columns::rotation::caveat;
        if f.len() < Self::SIZE {
            return Err(format!(
                "RotCaveatEntry: need {} felts, got {}",
                Self::SIZE,
                f.len()
            ));
        }
        let entry = Self {
            type_tag: f[0].0,
            domain_tag: f[1].0,
            key: f[2],
            params: [f[3], f[4], f[5], f[6]],
        };
        if entry.type_tag == 0 {
            return Ok(entry);
        }
        match entry.domain_tag {
            caveat::DOMAIN_REGISTERS => {
                if (entry.key.0 as usize) >= caveat::R {
                    return Err(format!(
                        "RotCaveatEntry: registers-domain key {} outside the \
                         R={} register file (refused)",
                        entry.key.0,
                        caveat::R
                    ));
                }
            }
            caveat::DOMAIN_HEAP => {}
            other => {
                return Err(format!(
                    "RotCaveatEntry: unknown domain tag {other} (refused — \
                     only registers 0 / heap 1 are caveat-scopable)"
                ));
            }
        }
        Ok(entry)
    }
}

impl Default for EffectVmContext {
    fn default() -> Self {
        Self {
            max_custom_effects: pi::MAX_CUSTOM_EFFECTS_DEFAULT,
            turn_hash: [BabyBear::ZERO; 4],
            effects_hash_global: [BabyBear::ZERO; 4],
            actor_nonce: 0,
            previous_receipt_hash: [BabyBear::ZERO; 4],
            sovereign_witness_key_commit: [BabyBear::ZERO; 4],
            sovereign_witness_sequence: 0,
            is_sovereign_cell: false,
            sovereign_transition_proof_vk_hash: [BabyBear::ZERO; 4],
            sovereign_transition_proof_commitment: [BabyBear::ZERO; 4],
            has_transition_proof: false,
            bridge_mint_value_limbs: [BabyBear::ZERO; 4],
            bridge_lock_value_limbs: [BabyBear::ZERO; 4],
            create_escrow_amount_limbs: [BabyBear::ZERO; 4],
            slot_caveat_count: 0,
            slot_caveat_manifest: [SlotCaveatEntry::zero(); pi::MAX_SLOT_CAVEATS],
            federation_id: [0u8; 32],
            owner_cell_id: [0u8; 32],
            committed_height: 0,
            rate_bound_tag: 0,
            challenge_window_tag: 0,
            asset_class: BabyBear::ZERO,
        }
    }
}

/// A witness the deployed EffectVM AIR cannot carry, reported as a VALUE.
///
/// ═══ WHY THIS TYPE EXISTS (GitHub #61 / #62, measured 2026-07-30) ═════════════════
/// These conditions used to be bare `assert!`s inside the trace generator, and one of
/// them — `SetField field_idx < 8` — is reachable from a turn the executor has ALREADY
/// accepted, committed and receipted. `dregg_cell::state::STATE_SLOTS` is 16, so a
/// write to slot 8..15 is legal cell state; the AIR carries only the first eight as
/// columns. The result was a prover that died AFTER the commit:
///
///   * on the async HTTP path (`node::prove_pool`) `spawn_blocking` catches the panic
///     and the receipt is left "committed-but-unattested" forever — finality never
///     reaches the attested tier for that traffic class (#61);
///   * on the finalized path (`node::blocklace_sync::execute_finalized_turn`, with
///     `--prove-turns`) the proving leg runs INLINE and the durable commit-log write
///     is LATER IN THE SAME FUNCTION, so the unwind skips the durable barrier and the
///     turn is never written to redb (#62).
///
/// A panic cannot be routed, logged with the offending index, or turned into a
/// refusal. A value can. The bound itself is CORRECT and is not raised here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectVmTraceError {
    /// A `SetField` naming a slot the deployed state block has no column for.
    /// `lanes` is [`state::NUM_FIELDS`] — derived from the block layout, matching the
    /// Lean `Fin 8` the descriptor is authored over.
    FieldIndexOutOfRange { field_idx: u32, lanes: usize },
    /// An outgoing `Transfer` whose amount exceeds the running balance. The AIR's
    /// `NET_DELTA = FINAL − INIT` algebra is satisfied just as happily by a modular
    /// wrap, so the generator refuses to build the trace rather than emit one.
    TransferUnderflow { amount: u64, running_balance: u64 },
    /// A `Burn` whose low-30-bit amount exceeds the running balance (same reasoning).
    BurnUnderflow { amount: u64, running_balance: u64 },
    /// A `GrainTurn` whose fee the single-tick grain member cannot express: the fee exceeds the
    /// member's 15-bit fee range (`EffectVmEmitGrainTurn.FEE_BITS`), or debiting it would borrow
    /// from `bal_hi` (the member debits `bal_lo` only and freezes `bal_hi`). A refusal, never a
    /// wrapped trace.
    GrainTurnFeeOutOfDomain { fee: u64, balance_lo: u64 },
}

impl core::fmt::Display for EffectVmTraceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::FieldIndexOutOfRange { field_idx, lanes } => write!(
                f,
                "SetField field_idx out of bounds: {field_idx} (must be 0..{last}). The deployed \
                 EffectVM state block carries {lanes} developer field columns \
                 (`state::FIELD_BASE..state::CAP_ROOT`), and the AIR is authored over exactly that \
                 many (Lean `setFieldVmDescriptor (slot : Fin {lanes})`). A cell holds \
                 STATE_SLOTS = 16 indexed slots; `fields[{lanes}..16]` fold into the authority \
                 residue (`record_digest`), NOT into a state-block column, so there is no lane to \
                 write and no proof to make. This is a REFUSAL, not a bound to raise",
                last = lanes.saturating_sub(1)
            ),
            Self::TransferUnderflow {
                amount,
                running_balance,
            } => write!(
                f,
                "Transfer underflow: amount {amount} > running balance {running_balance} \
                 (executor rejects; STARK constraint would wrap in BabyBear)"
            ),
            Self::BurnUnderflow {
                amount,
                running_balance,
            } => write!(
                f,
                "Burn underflow: amount_lo {amount} > running balance {running_balance}"
            ),
            Self::GrainTurnFeeOutOfDomain { fee, balance_lo } => write!(
                f,
                "GrainTurn fee {fee} is outside the single-tick grain member's domain: the fee must \
                 be < 2^15 (the member's fee range) and <= bal_lo {balance_lo} (the member debits \
                 bal_lo and freezes bal_hi, so a borrowing debit has no witness)"
            ),
        }
    }
}

impl std::error::Error for EffectVmTraceError {}

/// Stage 1 trace generator. Same as [`generate_effect_vm_trace`] but accepts
/// the widened PI inputs ([`EffectVmContext`]).
///
/// PANICS on a witness outside the AIR's domain. Any caller that can be reached by a
/// COMMITTED turn must use [`try_generate_effect_vm_trace_ext`] instead and surface the
/// refusal — see [`EffectVmTraceError`] for the two live incidents that motivated the
/// split. This wrapper stays for fixtures, benches and callers that have already
/// established the domain, mirroring the `convert_turn_effects_to_vm` /
/// `try_convert_turn_effects_to_vm` pair the executor bridge already uses.
pub fn generate_effect_vm_trace_ext(
    initial_state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    try_generate_effect_vm_trace_ext(initial_state, effects, context)
        .unwrap_or_else(|reason| panic!("{reason}"))
}

/// The CHECKED trace generator: every witness-domain condition the AIR cannot express
/// is returned as an [`EffectVmTraceError`] instead of panicking.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn try_generate_effect_vm_trace_ext(
    initial_state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), EffectVmTraceError> {
    assert!(!effects.is_empty(), "Need at least one effect");

    // ====================================================================
    // THE WITNESS-GENERATION PRECONDITION on the initial state.
    // ====================================================================
    // Runs at proof-generation time. It adds NO constraint to the STARK (the AIR is
    // Lean-authored and unchanged by this call); it stops the prover from building a
    // trace over a malformed state in the first place. Two things are decided:
    //
    //   * balance limbs inside their declared widths — out-of-width limbs satisfy the
    //     Group 6 `NET_DELTA = FINAL - INIT` algebra just as happily by modular wrap;
    //   * the carried `state_commitment` equals the commitment its own fields hash to —
    //     `to_trace_cols` copies that carried felt verbatim into row 0's
    //     `state_before.state_commit`, while `PI[OLD_COMMIT_BASE..]` is recomputed FRESH
    //     from the fields below, so a stale carry silently splits the trace from the
    //     public input the descriptor recomputes.
    //
    // Both halves are `verify_state_integrity`. Until this call it had ZERO call sites
    // anywhere in the tree — the range half was hand-inlined HERE as two `assert!`s (that
    // is what this replaced) and the commitment half was checked by nobody, while every
    // direct-mutation site in the tree repaired it by hand with `refresh_commitment()`.
    // ====================================================================
    if let Err(reason) = super::verify::verify_state_integrity(initial_state) {
        panic!("EffectVM trace generation refused a malformed initial CellState: {reason}");
    }

    // Validate field_idx bounds and balance underflow for all effects.
    // We track a running balance to catch underflow across multi-effect turns.
    {
        let mut running_balance = initial_state.balance;
        for effect in effects {
            match effect {
                Effect::SetField { field_idx, .. } => {
                    // THE AIR'S REAL CEILING, derived from the deployed block layout — see
                    // `state::NUM_FIELDS`. A slot at or above it has no column to write, so
                    // there is nothing to prove; the caller is told WHICH index and HOW MANY
                    // lanes exist rather than losing its stack.
                    if (*field_idx as usize) >= state::NUM_FIELDS {
                        return Err(EffectVmTraceError::FieldIndexOutOfRange {
                            field_idx: *field_idx,
                            lanes: state::NUM_FIELDS,
                        });
                    }
                }

                Effect::Transfer {
                    amount, direction, ..
                } => {
                    if *direction == 1 {
                        // Outgoing: validate no underflow.
                        if *amount > running_balance {
                            return Err(EffectVmTraceError::TransferUnderflow {
                                amount: *amount,
                                running_balance,
                            });
                        }
                        running_balance -= amount;
                    } else {
                        running_balance = running_balance.saturating_add(*amount);
                    }
                }
                Effect::NoteCreate { .. } => {
                    // BALANCE-NEUTRAL: a NoteCreate moves NO transparent value (the
                    // note value lives in the commitment, never on the ledger), so it
                    // cannot underflow the running balance and does not decrement it.
                    // Matches the verified executor (`apply_note_create`) + Lean
                    // descriptor (`EffectVmEmitNoteCreate`, balance-neutral).
                }

                Effect::NoteSpend { value, .. } => {
                    running_balance = running_balance.saturating_add(*value);
                }

                Effect::GrainTurn { fee, .. } => {
                    let balance_lo = running_balance & 0x3FFF_FFFF;
                    if *fee >= (1 << 15) || *fee > balance_lo {
                        return Err(EffectVmTraceError::GrainTurnFeeOutOfDomain {
                            fee: *fee,
                            balance_lo,
                        });
                    }
                    running_balance -= fee;
                }

                Effect::Burn {
                    amount_lo,
                    amount_full,
                    ..
                } => {
                    // Burn debits balance by the low-30-bit amount the AIR
                    // constraint uses (mirrors NoteCreate / CreateEscrow).
                    // `amount_full` binds via effects_hash but doesn't drive
                    // the per-row balance arithmetic.
                    let _ = amount_full;
                    let amt = amount_lo.as_u32() as u64;
                    if amt > running_balance {
                        return Err(EffectVmTraceError::BurnUnderflow {
                            amount: amt,
                            running_balance,
                        });
                    }
                    running_balance -= amt;
                }
                _ => {}
            }
        }
    }

    // Determine trace height (pad to power of 2, minimum MIN_TRACE_HEIGHT).
    //
    // MIN_TRACE_HEIGHT = 64 closes the FRI single-row-gap (task #90 /
    // TEST-REALITY-AUDIT A1). With a 2-row trace the FRI folding tree has only
    // one round and a single-row tamper can slip through probabilistically.
    // With 64 rows (domain_size = 256 at blowup-4, 6 FRI rounds) the quotient
    // polynomial deviation from low-degree is detectable with overwhelming
    // probability for any single-row tamper: the high-degree quotient is at
    // Hamming distance ≥ 3/4 · domain_size from any valid codeword, so
    // P(miss with 80 queries) ≤ (1/4)^80 ≈ 10^-48. Tradeoff: proofs for
    // short effect sequences use 64 NoOp padding rows instead of 2; the Merkle
    // tree and FRI layers are correspondingly larger but still fast.
    //
    // Stage 2 (REVIEW[stage1-acc-row0]): if the last real effect is a Custom, we
    // reserve a trailing NoOp row so that the exclusive-sum accumulator ends at
    // the true total.
    //
    // ⚠ THE BOUNDARY THIS PAD EXISTS FOR DOES NOT EXIST (measured 2026-08-06,
    // re-checked 2026-08-07). This read "so the exclusive-sum boundary
    // `acc[last] == PI[CUSTOM_EFFECT_COUNT]` holds". No constraint anywhere
    // references `aux_off::CUSTOM_COUNT_ACC` — see its declaration in
    // `columns.rs` — so nothing "holds"; the pad keeps a prover-filled column
    // self-consistent and buys no soundness. Kept because removing it would
    // change the emitted trace height (a VK rotation) for no gain; do not read
    // it as evidence of a check.
    const MIN_TRACE_HEIGHT: usize = 64;
    let n_effects = effects.len();
    let need_extra_pad = matches!(effects.last(), Some(Effect::Custom { .. }));
    let trace_height = if need_extra_pad {
        (n_effects + 1).next_power_of_two().max(MIN_TRACE_HEIGHT)
    } else {
        n_effects.next_power_of_two().max(MIN_TRACE_HEIGHT)
    };

    let mut trace = Vec::with_capacity(trace_height);
    let mut current_state = initial_state.clone();

    // Track net balance delta.
    let mut net_delta: i64 = 0;

    for effect in effects {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

        // Set selector.
        let sel_idx = effect_selector(effect);
        row[sel_idx] = BabyBear::ONE;

        // Write state_before.
        let state_before_cols = current_state.to_trace_cols();
        for (i, &val) in state_before_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }

        // Apply effect and compute state_after + params.
        let mut new_state = current_state.clone();
        match effect {
            Effect::NoOp => {
                // No state change, no nonce increment for padding.
            }
            Effect::Transfer { amount, direction } => {
                let (lo, _hi) = split_u64(*amount);
                row[PARAM_BASE + param::AMOUNT] = lo;
                row[PARAM_BASE + param::DIRECTION] = BabyBear::new(*direction);

                if *direction == 1 {
                    // Outgoing.
                    new_state.balance = new_state.balance.saturating_sub(*amount);
                    net_delta -= *amount as i64;
                } else {
                    // Incoming.
                    new_state.balance = new_state.balance.saturating_add(*amount);
                    net_delta += *amount as i64;
                }
                new_state.nonce += 1;
            }
            Effect::SetField { field_idx, value } => {
                row[PARAM_BASE + param::FIELD_INDEX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::NEW_VALUE] = *value;

                // Store old value at target index in aux[0] for the constraint.
                //
                // ⚠ THIS USED TO BE `idx.min(7)`, on BOTH lines. A silent clamp behind an
                // `assert!` is a wrong-proof waiting for the assert to be relaxed: with the
                // bound raised to 16 "because STATE_SLOTS is 16", a write to slot 9 would have
                // proven a write to slot 7 — the exact failure the bound exists to prevent,
                // with a valid proof attached. The refusal above makes the clamp dead, so it
                // is GONE rather than left as a trap for the next reader.
                let idx = *field_idx as usize;
                row[AUX_BASE] = current_state.fields[idx];

                new_state.fields[idx] = *value;
                new_state.nonce += 1;
            }
            Effect::GrainTurn { values, fee } => {
                // ONE executor grain turn as ONE row (Lean `EffectVmEmitGrainTurn`): slot `j`
                // (3..=7) takes `param (j-3)`, `param5` carries the fee debited from `bal_lo`,
                // and the nonce ticks ONCE. The domain check above guarantees no `bal_lo` borrow.
                for (k, v) in values.iter().enumerate() {
                    row[PARAM_BASE + k] = *v;
                    new_state.fields[3 + k] = *v;
                }
                row[PARAM_BASE + 5] = BabyBear::new(*fee as u32);
                new_state.balance -= *fee;
                net_delta -= *fee as i64;
                new_state.nonce += 1;
            }
            Effect::GrantCapability { cap_entry, phase_b } => {
                // 32-byte widening: anchor limb[0] into params[0]; the AIR's
                // cap_root advance uses limb[0]. The full 8 limbs bind via
                // compute_effects_hash → PI[EFFECTS_HASH].
                row[PARAM_BASE + param::CAP_ENTRY] = cap_entry[0];

                match phase_b {
                    // ---- Phase B2: GRANTER-side delegation row ----
                    // The row covers the GRANTER, whose seeded cap_root holds
                    // the delegated-from cap; the p3 AIR's gates membership-open
                    // the held leaf against state_before.cap_root, enforce
                    // granted ⊑ held (submask + AuthRequired lattice + expiry),
                    // and pin params[0] to the granted leaf's in-circuit
                    // 7-field digest. Delegating does NOT move the granter's
                    // own tree (the install lands in the RECIPIENT's c-list),
                    // so cap_root passes through unchanged.
                    Some(w) => {
                        row[PARAM_BASE + param::GRANT_DIRECTION] = BabyBear::ONE;
                        row[PARAM_BASE + param::GRANT_HELD_SLOT_HASH] = w.held.slot_hash;
                        // capability_root: passthrough (no mutation).
                    }
                    // ---- Legacy: RECIPIENT install (direction 0) ----
                    None => {
                        let new_cap = hash_2_to_1(current_state.capability_root, cap_entry[0]);
                        new_state.capability_root = new_cap;
                    }
                }
                new_state.nonce += 1;
            }
            Effect::RevokeCapability { slot_hash, phase_b } => {
                // The slot_hash limb[0] shares param slot 0 with cap_entry.
                row[PARAM_BASE + param::CAP_ENTRY] = slot_hash[0];

                match phase_b {
                    // ---- Phase B (GRADUATED): GENUINE sorted-tree slot DELETION.
                    // The cap_root advances from the held leaf's authenticated
                    // position to the tree with that slot removed — the ZERO/
                    // padding leaf recomputed over the real Merkle path.
                    // `state_before.cap_root` MUST already equal the witness's
                    // `old_root` (the caller seeds the actor's tree root), and
                    // `state_after.cap_root` becomes the zero-fold `new_root`. The
                    // p3 AIR's revoke gates (membership-open + zero-fold recompute)
                    // prove the held leaf WAS in the tree over THIS move. ----
                    Some(w) => {
                        // Recompute the new root over the witnessed sibling path
                        // with the ZERO/padding 8-felt leaf at the revoked position
                        // (Phase H-CAP-8 `cap_node8` fold); the deployed 1-felt
                        // `cap_root` column carries LANE 0 of the 8-felt top.
                        let cur = crate::cap_root::recompose_membership(
                            crate::cap_root::CAP_ZERO8,
                            &w.siblings,
                            &w.directions,
                        );
                        new_state.capability_root = cur[0];
                    }
                    // ---- Legacy (pre-graduation): opaque 2-of-2 fold. NOT a
                    // genuine sorted-tree deletion and NOT provable through the
                    // audited p3 revoke gates. ----
                    None => {
                        let new_cap = hash_2_to_1(current_state.capability_root, slot_hash[0]);
                        new_state.capability_root = new_cap;
                    }
                }
                new_state.nonce += 1;
            }
            Effect::EmitEvent {
                topic_hash,
                payload_hash,
            } => {
                // Park the low 4 felts of topic_hash into params[0..4] and the
                // low 4 felts of payload_hash into params[4..8]. The AIR's
                // per-row PI-equality constraint pins these to
                // `PI[EMIT_EVENT_TOPIC_HASH][0..4]` and
                // `PI[EMIT_EVENT_PAYLOAD_HASH][0..4]`. The high 4 felts of
                // each hash are bound via `compute_effects_hash` (which
                // absorbs all 16 felts) and via the off-AIR verifier's
                // PI-match loop (which recomputes the full canonical
                // (topic, payload) hashes from the runtime Event). No state
                // column changes — pure side-effect.
                for i in 0..4 {
                    row[PARAM_BASE + i] = topic_hash[i];
                    row[PARAM_BASE + 4 + i] = payload_hash[i];
                }
                new_state.nonce += 1;
            }
            Effect::SetPermissions { permissions_hash } => {
                // v10 perms faithful-8-felt weld: carry ALL 8 declared-hash limbs in the param
                // columns (params[0..8]) so the rotated `permsVKWeldGate` can force every committed
                // perms-digest limb (limb-0 at B_PERMS + the 7 completion felts at extras 37..=43) to
                // the declared param. Byte-identical to the 8 felts `compute_effects_hash` absorbs, so
                // the effects_hash PI is unchanged. AIR forbids any state column change; nonce ticks.
                row[PARAM_BASE..PARAM_BASE + 8].copy_from_slice(permissions_hash);
                new_state.nonce += 1;
            }
            Effect::SetVerificationKey { vk_hash } => {
                // Same shape as SetPermissions (v10 vk weld): carry all 8 vk-hash limbs in params[0..8]
                // (None → all-zero) so the vk weld forces the 8 committed vk-digest limbs.
                row[PARAM_BASE..PARAM_BASE + 8].copy_from_slice(vk_hash);
                new_state.nonce += 1;
            }

            Effect::RefreshDelegation { child_hash, .. } => {
                // 32-byte widening: anchor the refreshed child key limb[0]; all
                // 16 limbs (child + snapshot) bind via compute_effects_hash.
                row[PARAM_BASE] = child_hash[0];
                new_state.nonce += 1;
            }
            Effect::IncrementNonce => {
                // Explicit nonce-only runtime effect. The selector distinguishes
                // it from delegation refresh and other passthrough siblings.
                new_state.nonce += 1;
            }
            Effect::RevokeDelegation { child_hash } => {
                // 32-byte widening: anchor limb[0]; full 8 limbs bind via effects_hash.
                row[PARAM_BASE] = child_hash[0];
                new_state.nonce += 1;
            }
            Effect::CreateCell { create_hash } => {
                row[PARAM_BASE] = create_hash[0];
                new_state.nonce += 1;
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                row[PARAM_BASE] = spawn_hash[0];
                new_state.nonce += 1;
            }

            Effect::ExerciseViaCapability { exercise_hash } => {
                row[PARAM_BASE] = exercise_hash[0];
                new_state.nonce += 1;
            }
            Effect::Introduce { intro_hash } => {
                row[PARAM_BASE] = intro_hash[0];
                new_state.nonce += 1;
            }
            Effect::PipelinedSend { send_hash } => {
                row[PARAM_BASE] = send_hash[0];
                new_state.nonce += 1;
            }

            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full: _,
            } => {
                // Mirror NoteSpend: balance credit by value_lo.
                row[PARAM_BASE] = *mint_hash;
                row[PARAM_BASE + 1] = *value_lo;
                let value_u64 = value_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_add(value_u64);
                net_delta += value_u64 as i64;
                new_state.nonce += 1;
            }

            Effect::Mint {
                value_lo,
                mint_hash,
                value_full: _,
            } => {
                // SUPPLY-MODEL.md Stage 2b: the dedicated supply-mint row is
                // byte-identical in body to BridgeMint (credit at param1), but
                // sits on `sel::MINT` (set by `effect_selector`), so it routes
                // to `supplyMintVmDescriptor2R24` rather than the bridge member.
                row[PARAM_BASE] = *mint_hash;
                row[PARAM_BASE + 1] = *value_lo;
                let value_u64 = value_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_add(value_u64);
                net_delta += value_u64 as i64;
                new_state.nonce += 1;
            }

            Effect::NoteSpend { nullifier, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NULLIFIER] = *nullifier;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_add(*value);
                net_delta += *value as i64;
                new_state.nonce += 1;
            }
            Effect::NoteCreate { commitment, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NOTE_COMMITMENT] = *commitment;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                // BALANCE-NEUTRAL: the note value is hidden in the commitment and is
                // NEVER moved on the transparent ledger (the shielding convention; the
                // executor `apply_note_create` records the commitment and does not touch
                // balance). So the balance is FROZEN and `net_delta` is unchanged. This
                // matches the verified Lean descriptor (`EffectVmEmitNoteCreate`,
                // balance-neutral `gBalLoFreeze`/`CellNoteSpec`). (A prior version
                // subtracted `value`, which diverged from the executor; closed.)
                new_state.nonce += 1;
            }

            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                // Write VK hash into params[0..4]: the trace row carries the
                // low 4 felts of the 8-felt VK hash. On the rotated custom
                // member the high 4 ride exact member-local VK-teeth columns,
                // and all eight are PI-pinned for the recursion fold.
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + i] = program_vk_hash[i];
                }
                // Write proof-commitment limbs 0..4 into params[4..8] (the param
                // union has exactly 8 slots). The full 8-felt commitment (flag-day
                // rotation) is bound through PI[CUSTOM_PROOFS_BASE + 8..16]; on the
                // rotated wide member limbs 4..8 additionally ride the member-local
                // commit-teeth columns (`trace_rotated::CUSTOM_COMMIT_TEETH_BASE`).
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + i] = proof_commitment[i];
                }
                // Custom effects do NOT change state (state flows through unchanged).
                // The nonce still increments (it's a real effect, not padding).
                new_state.nonce += 1;
                // No balance change from the Effect VM perspective.
            }

            Effect::MakeSovereign => {
                // Mode flag transitions from 0 to 1.
                new_state.mode_flag = 1;
                new_state.nonce += 1;
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                row[PARAM_BASE + param::FACTORY_VK_HASH] = *factory_vk;
                row[PARAM_BASE + param::CHILD_VK_DERIVED] = *child_vk_derived;
                // Store in aux columns for constraint verification.
                row[AUX_BASE + 6] = *factory_vk;
                row[AUX_BASE + 7] = *child_vk_derived;
                new_state.nonce += 1;
            }

            Effect::Burn {
                target_hash,
                amount_lo,
                amount_full: _,
            } => {
                // Near-miss aliasing closure (#100 follow-up): a dedicated
                // Burn variant. Mirrors NoteCreate's balance-debit shape but
                // (a) uses its own selector (so a verifier can distinguish
                //     Burn from Transfer-dir-1 at the algebraic level), and
                // (b) pins `was_burn_flag == 1` into params[2] so a forged
                //     trace that drops the disclosure flag fails the AIR.
                // 32-byte widening (felt-width #25): anchor limb[0] into params[0]
                // (the CellDestroy shape below); all 8 limbs bind via
                // compute_effects_hash. No deployed constraint reads this column —
                // `burnVmDescriptor2R24` references col 68 zero times — so the
                // anchor is a trace-shape convention, not a binding.
                row[PARAM_BASE + param::BURN_TARGET] = target_hash[0];
                row[PARAM_BASE + param::BURN_AMOUNT_LO] = *amount_lo;
                row[PARAM_BASE + param::BURN_WAS_BURN_FLAG] = BabyBear::ONE;

                let amt = amount_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_sub(amt);
                net_delta -= amt as i64;
                new_state.nonce += 1;
            }
            Effect::CellDestroy {
                target_hash,
                death_certificate_hash,
            } => {
                // State passthrough (lifecycle lives off-trace), but the
                // two params bind the cell + death certificate. Distinct
                // from `SetPermissions` (which only binds a single hash)
                // both by selector and by a second-PARAM constraint that
                // a SetPermissions row can't satisfy.
                // 32-byte widening: anchor limb[0] of each into params; the
                // full 8 limbs of both bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_DESTROY_TARGET] = target_hash[0];
                row[PARAM_BASE + param::CELL_DESTROY_CERT_HASH] = death_certificate_hash[0];
                new_state.nonce += 1;
            }
            Effect::AttenuateCapability {
                cap_slot_hash,
                narrower_commitment,
                phase_b,
            } => {
                row[PARAM_BASE + param::ATTN_CAP_SLOT_HASH] = cap_slot_hash[0];
                row[PARAM_BASE + param::ATTN_NARROWER_COMMITMENT] = narrower_commitment[0];

                match phase_b {
                    // ---- Phase B: GENUINE sorted-tree leaf-update ----
                    // The cap_root advances from the held leaf's authenticated
                    // position to the narrowed leaf, recomputed over the real
                    // Merkle path. `state_before.cap_root` MUST already equal the
                    // witness's `old_root` (the caller seeds the actor's tree
                    // root), and `state_after.cap_root` becomes the recomputed
                    // `new_root`. The p3 AIR's Phase-B gates (membership-open +
                    // submask + AuthRequired lattice + expiry) prove
                    // granted ⊑ held over THIS move. The params[1] narrower
                    // commitment is pinned in-circuit to the granted leaf digest.
                    Some(w) => {
                        // Recompute the new root over the witnessed sibling path with
                        // the native 8-felt `cap_node8` compression (Phase H-CAP-8); the
                        // deployed 1-felt `cap_root` column carries LANE 0 of the 8-felt top.
                        let cur = crate::cap_root::recompose_membership(
                            w.granted.digest(),
                            &w.siblings,
                            &w.directions,
                        );
                        new_state.capability_root = cur[0];
                    }
                    // ---- Legacy (pre-Phase-B): opaque 2-of-2 fold ----
                    // Algebraically distinct from RevokeCapability's single-hash
                    // advance, but NOT a genuine sorted-tree update and NOT
                    // provable through the audited p3 Phase-B gates.
                    None => {
                        let leaf = hash_2_to_1(cap_slot_hash[0], narrower_commitment[0]);
                        new_state.capability_root = hash_2_to_1(new_state.capability_root, leaf);
                    }
                }
                new_state.nonce += 1;
            }

            // ---- AIR-impl lane #119 ----
            Effect::CellSeal {
                target,
                reason_hash,
            } => {
                // State passthrough: balance/fields/cap_root/reserved unchanged.
                // Both params bind so the proof cannot alias SetPermissions
                // (which only carries one non-zero param).
                // 32-byte widening: anchor limb[0] of each into params; the
                // full 8 limbs of both bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_SEAL_TARGET] = target[0];
                row[PARAM_BASE + param::CELL_SEAL_REASON_HASH] = reason_hash[0];
                new_state.nonce += 1;
            }
            Effect::CellUnseal { target } => {
                // State passthrough; mirror the single target param (limb[0])
                // into aux so AIR rejects post-generation param swaps. All 8
                // limbs bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_UNSEAL_TARGET] = target[0];
                row[AUX_BASE] = target[0];
                new_state.nonce += 1;
            }
            Effect::ReceiptArchive {
                target,
                archive_end_height,
                terminal_receipt_hash,
            } => {
                // State passthrough; three params make this algebraically
                // distinct from any 1- or 2-param passthrough sibling. 32-byte
                // widening: anchor limb[0] of target / terminal_receipt_hash;
                // archive_end_height is a scalar height (single felt).
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_TARGET] = target[0];
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_END_HEIGHT] = *archive_end_height;
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_TERMINAL_HASH] = terminal_receipt_hash[0];
                new_state.nonce += 1;
            }
            Effect::Refusal {
                target,
                reason_hash,
            } => {
                // State passthrough; two params — same count as CellSeal —
                // but algebraically distinct because the selector gate is
                // different (`sel::REFUSAL` vs. `sel::CELL_SEAL`). 32-byte
                // widening: anchor limb[0]; full 8 limbs bind via effects_hash.
                row[PARAM_BASE + param::REFUSAL_TARGET] = target[0];
                row[PARAM_BASE + param::REFUSAL_REASON_HASH] = reason_hash[0];
                new_state.nonce += 1;
            }
        }

        // Refresh state commitment.
        new_state.refresh_commitment();

        // Fill state commitment tree intermediate columns (aux[8..10]).
        // These are constrained by the evaluator to match hash_4_to_1 computations
        // on the state_after columns.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            new_state.balance,
            new_state.nonce,
            &new_state.fields,
            new_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;
        // P0-2: the authority-residue digest absorbed as the fourth root input.
        // The EffectVM kernel turns carry no authority-residue mutation, so the
        // state_after digest equals the state_before digest (the residue rides the
        // rotated weld's r23 / the cell-side `compute_authority_digest_felt`); a
        // residue-free cell carries `empty_record_digest()` (ZERO). The Group-4
        // constraint reads this column as the fourth `hash_4_to_1` input.
        row[AUX_BASE + aux_off::STATE_RECORD_DIGEST] = new_state.record_digest;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved on every row.
        // The constraint in eval_constraints requires that
        //   Σ b_i * 2^i + mode * 256 == old_reserved
        // hold unconditionally for every row.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        // W9-RANGECHECK: bit-decompose the new (state_after) balance limbs so
        // the per-row in-circuit range / underflow constraint is satisfied.
        fill_balance_limb_bits(&mut row, new_state.balance);

        // Write state_after.
        let state_after_cols = new_state.to_trace_cols();
        for (i, &val) in state_after_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        current_state = new_state;
    }

    // Compute effects hash and net delta for public inputs.
    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(effects);
    let (delta_mag, delta_sign) = if net_delta < 0 {
        ((-net_delta) as u32, 1u32)
    } else {
        (net_delta as u32, 0u32)
    };

    // Fill aux columns on the first row with public-input-bound values.
    // Stage 1: effects_hash is widened to 4 felts; positions 0..1 are bound
    // to AUX[4..5] via boundary constraints (preserves the legacy 2-felt
    // witness binding), positions 2..3 are PI-only (see AUDIT[stage1-pi-only-bound]).
    let effects_hash_4_witness = compute_effects_hash_4(effects);
    if !trace.is_empty() {
        trace[0][AUX_BASE + 2] = BabyBear::new(delta_mag);
        trace[0][AUX_BASE + 3] = BabyBear::new(delta_sign);
        trace[0][AUX_BASE + 4] = effects_hash_4_witness[0];
        trace[0][AUX_BASE + 5] = effects_hash_4_witness[1];

        // Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.1):
        // bind the witness's key-commit + sequence into row-0 aux columns.
        // The boundary constraints pin these to the matching PI slots.
        // When IS_SOVEREIGN_CELL == 0, the prover writes zero sentinels
        // and the verifier supplies zero sentinels — the boundary holds
        // trivially.
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0] =
            context.sovereign_witness_key_commit[0];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1] =
            context.sovereign_witness_key_commit[1];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2] =
            context.sovereign_witness_key_commit[2];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3] =
            context.sovereign_witness_key_commit[3];
        trace[0][AUX_BASE + aux_off::WITNESS_SEQUENCE] =
            BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);

        // γ.2 follow-up (#131/#132): bind the federation id + owner cell id
        // into row-0 aux columns. The boundary constraints pin these to
        // PI[FEDERATION_ID_BASE..+4] / PI[OWNER_CELL_ID_BASE..+4]. The
        // off-AIR verifier recomputes both 4-felt commitments from the
        // trusted federation id + owner cell id, so a proof minted under a
        // different federation (or for a different owner cell) cannot satisfy
        // both the boundary (vs. its own PI) AND the verifier's PI-match loop
        // (vs. the expected federation/owner).
        let fed_id_4 = canonical_id_to_felts_4(&context.federation_id);
        let owner_id_4 = canonical_id_to_felts_4(&context.owner_cell_id);
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_0] = fed_id_4[0];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_1] = fed_id_4[1];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_2] = fed_id_4[2];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_3] = fed_id_4[3];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_0] = owner_id_4[0];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_1] = owner_id_4[1];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_2] = owner_id_4[2];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_3] = owner_id_4[3];

        // Light-client conservation: bind the per-cell asset class into the
        // row-0 aux column. The boundary constraint pins it to
        // PI[v3::ASSET_CLASS], so the proof commits to its asset class and the
        // per-asset conservation gate can partition by the PI-bound class.
        trace[0][AUX_BASE + aux_off::ASSET_CLASS] = context.asset_class;
    }
    // Silence unused warnings on the legacy 2-felt return values.
    let _ = (effects_hash_lo, effects_hash_hi);

    // Pad with NoOp rows.
    for _ in n_effects..trace_height {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE; // NoOp selector

        // State before = current state (carried from last real row).
        let state_cols = current_state.to_trace_cols();
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }
        // State after = same (NoOp doesn't change state).
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        // Fill state commitment tree intermediates for padding rows too.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            current_state.balance,
            current_state.nonce,
            &current_state.fields,
            current_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;
        // P0-2: NoOp pad rows pass state through unchanged, so the record_digest is
        // the carried `current_state.record_digest` (the Group-4 fourth root input).
        row[AUX_BASE + aux_off::STATE_RECORD_DIGEST] = current_state.record_digest;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        // W9-RANGECHECK: NoOp pad rows pass balance through unchanged, so
        // state_after.balance == current_state.balance — decompose it.
        fill_balance_limb_bits(&mut row, current_state.balance);

        trace.push(row);
        // current_state stays the same for padding.
    }

    // Populate aux[CUSTOM_COUNT_ACC] as the EXCLUSIVE running sum of `s_custom`
    // indicators. Convention: acc[i] = count of s_custom rows in [0..i) (NOT
    // including row i).
    //
    // ⚠ **"Stage 2 sum-check" NAMES NOTHING. THERE IS NO SUM-CHECK.** This block
    // read: "acc[0] == 0 always (pinned by row-0 boundary) · Transition:
    // next.acc == this.acc + this.s_custom (Group 7) · acc[last] == total count,
    // pinned to PI[CUSTOM_EFFECT_COUNT] by the last-row boundary." Measured
    // 2026-08-06 and re-checked 2026-08-07: **"Group 7" does not exist**, no
    // boundary or transition constraint references `aux_off::CUSTOM_COUNT_ACC`
    // (three tree-wide hits: the const, this fill, one comment), the v1 hand-AIR
    // that was to host it is retired, and the deployed registries carry zero
    // `pi_binding`s at PI 28. So all three bullets described constraints that
    // were never emitted. What this loop actually produces is a prover-filled
    // column that no verifier consults; the three-docblock "Group 7" citation is
    // the reason `PI[CUSTOM_EFFECT_COUNT]` was believed to be algebraically
    // bound. `docs/PI-DISPOSITION.md` §6 has the disposition (STOP PUBLISHING).
    //
    // For the last-row boundary to equal the total custom count, the last
    // row must contribute 0 to the running sum — i.e., the last row must
    // be a NoOp pad row. The pad loop above already pads with NoOp; the
    // `need_extra_pad` check at trace_height computation guarantees a NoOp
    // slot exists when the last real effect is Custom.
    {
        let mut acc: u32 = 0;
        for i in 0..trace.len() {
            // Exclusive sum: record acc BEFORE adding this row's contribution.
            trace[i][AUX_BASE + aux_off::CUSTOM_COUNT_ACC] = BabyBear::new(acc);
            if trace[i][sel::CUSTOM] == BabyBear::ONE {
                acc = acc.saturating_add(1);
            }
        }
    }

    // Collect custom effect entries for public inputs.
    let custom_entries: Vec<_> = effects
        .iter()
        .filter_map(|e| {
            if let Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = e
            {
                Some((*program_vk_hash, *proof_commitment))
            } else {
                None
            }
        })
        .collect();
    let custom_count = custom_entries.len();
    assert!(
        custom_count <= context.max_custom_effects as usize,
        "Too many custom effects: {} (max {})",
        custom_count,
        context.max_custom_effects
    );
    assert!(
        context.max_custom_effects <= pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
        "max_custom_effects {} exceeds hard cap {}",
        context.max_custom_effects,
        pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
    );

    // Build public inputs in the PI v3 layout (see `pi` module).
    let pi_len = pi::ACTIVE_BASE_COUNT + custom_count * pi::CUSTOM_ENTRY_SIZE;
    let mut public_inputs = vec![BabyBear::ZERO; pi_len];

    // ---- Commitments (8 genuine Poseidon2 felts each, Phase C ~124-bit) ----
    let old_commit_8 = CellState::compute_commitment_8(
        initial_state.balance,
        initial_state.nonce,
        &initial_state.fields,
        initial_state.capability_root,
        initial_state.record_digest,
    );
    let new_commit_8 = CellState::compute_commitment_8(
        current_state.balance,
        current_state.nonce,
        &current_state.fields,
        current_state.capability_root,
        current_state.record_digest,
    );
    public_inputs[pi::OLD_COMMIT_BASE..pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN]
        .copy_from_slice(&old_commit_8[..pi::OLD_COMMIT_LEN]);
    public_inputs[pi::NEW_COMMIT_BASE..pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN]
        .copy_from_slice(&new_commit_8[..pi::NEW_COMMIT_LEN]);

    // ---- Effects hash (4 felts) ----
    let effects_hash_4 = compute_effects_hash_4(effects);
    public_inputs[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN]
        .copy_from_slice(&effects_hash_4[..pi::EFFECTS_HASH_LEN]);
    // Suppress unused-variable warning for the legacy 2-felt form.
    let _ = (effects_hash_lo, effects_hash_hi);

    // ---- Balance limbs (P0-1) ----
    let (i_lo, i_hi) = split_u64(initial_state.balance);
    let (f_lo, f_hi) = split_u64(current_state.balance);
    public_inputs[pi::INIT_BAL_LO] = i_lo;
    public_inputs[pi::INIT_BAL_HI] = i_hi;
    public_inputs[pi::FINAL_BAL_LO] = f_lo;
    public_inputs[pi::FINAL_BAL_HI] = f_hi;

    // ---- Net delta (P0-1) ----
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::new(delta_mag);
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::new(delta_sign);

    // ⚑ THE SEVEN WRITES THAT USED TO BE HERE ARE GONE (flag day 2026-08-07). This block filled
    // `CURRENT_BLOCK_HEIGHT` (with a constant 0 — nothing ever set the context field, which is
    // deleted too), `MAX_CUSTOM_EFFECTS` (with the library default — nothing plumbs the cell's),
    // `CUSTOM_EFFECT_COUNT` and the four `APPROVED_HANDOFFS` sentinel felts. All seven slots were deleted from
    // `pi.rs`: zero `pi_binding`s on all 117 deployed registry members, and the one class of
    // off-circuit reader now derives its count from the PI vector's own length
    // (`pi::custom_entry_count`). `docs/PI-DISPOSITION.md` §6.
    //
    // ---- Stage 7-γ.0a turn-identity bindings ----
    // These four fields are *shared across all per-cell proofs of one turn*.
    // The verifier's cross-proof PI matching loop enforces equality across
    // the bundle; per-proof binding to the canonical Turn::hash and
    // call_forest projection is executor-trusted at γ.0 and becomes
    // algebraic at γ.1.
    public_inputs[pi::TURN_HASH_BASE..pi::TURN_HASH_BASE + pi::TURN_HASH_LEN]
        .copy_from_slice(&context.turn_hash[..pi::TURN_HASH_LEN]);
    public_inputs
        [pi::EFFECTS_HASH_GLOBAL_BASE..pi::EFFECTS_HASH_GLOBAL_BASE + pi::EFFECTS_HASH_GLOBAL_LEN]
        .copy_from_slice(&context.effects_hash_global[..pi::EFFECTS_HASH_GLOBAL_LEN]);
    public_inputs[pi::ACTOR_NONCE] = BabyBear::new((context.actor_nonce & 0x7FFF_FFFF) as u32);
    public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE
        ..pi::PREVIOUS_RECEIPT_HASH_BASE + pi::PREVIOUS_RECEIPT_HASH_LEN]
        .copy_from_slice(&context.previous_receipt_hash[..pi::PREVIOUS_RECEIPT_HASH_LEN]);

    // ---- Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    //
    // Phase 1: PI carries the witness's owning-key commitment, monotonic
    // sequence, and a flag indicating sovereign vs. hosted. The boundary
    // constraint binds the in-trace aux columns to these PI values at
    // row 0. When IS_SOVEREIGN_CELL == 0, the sentinel-zero on both
    // sides makes the constraint trivially satisfied.
    //
    // Phase 2: PI additionally carries the inner transition_proof's
    // VK hash + 4-felt commitment + a presence flag. The off-AIR
    // verifier reads these and recursively verifies the inner STARK.
    public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE
        ..pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN]
        .copy_from_slice(
            &context.sovereign_witness_key_commit[..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN],
        );
    public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] =
        BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);
    public_inputs[pi::IS_SOVEREIGN_CELL] = if context.is_sovereign_cell {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE
        ..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE + pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN]
        .copy_from_slice(
            &context.sovereign_transition_proof_vk_hash
                [..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN],
        );
    public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE
        ..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE
            + pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN]
        .copy_from_slice(
            &context.sovereign_transition_proof_commitment
                [..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN],
        );
    public_inputs[pi::HAS_TRANSITION_PROOF] = if context.has_transition_proof {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };

    // ---- 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5) ----
    //
    // Each of the three affected effects gets its own 4×16-bit limb slot.
    // We aggregate per-turn: each BridgeMint/BridgeLock/CreateEscrow in
    // the trace contributes its full u64 value via wrap-add (the AIR's
    // per-row balance arithmetic uses the legacy 30-bit-truncated
    // `value_lo`; the new limb slots independently attest to the FULL
    // u64 the executor saw, summed across the trace). A future
    // refinement (per-row limb columns) sits behind a separate
    // PI/aux-column widening.
    //
    // Each limb is < 2^16 by construction (`u64_to_4_limbs_16` masks).
    // The verifier's PI match loop catches any out-of-range limb a
    // malicious prover supplies, and the on-trace effects also bind to
    // the same 4-limb form via the absorbed-into-effects-hash path
    // (see `compute_effects_hash` arms for BridgeMint/BridgeLock/
    // CreateEscrow). Together the two paths give the bit-injective
    // u64 binding that closes §6.5.
    let mint_sum = {
        let mut m: u64 = 0;
        for eff in effects {
            // SUPPLY-MODEL.md Stage 2b: both mint-family credits (the portable-proof
            // BridgeMint and the dedicated supply Mint) attest their FULL u64 here,
            // so the §6.5 bit-injective binding covers a supply-mint's value too —
            // not just the 30-bit `value_lo` the per-row arithmetic uses.
            match eff {
                Effect::BridgeMint { value_full, .. } | Effect::Mint { value_full, .. } => {
                    m = m.wrapping_add(*value_full);
                }
                _ => {}
            }
        }
        m
    };
    let mint_limbs = u64_to_4_limbs_16(mint_sum);
    public_inputs[pi::BRIDGE_MINT_VALUE_LIMBS_BASE
        ..pi::BRIDGE_MINT_VALUE_LIMBS_BASE + pi::BRIDGE_MINT_VALUE_LIMBS_LEN]
        .copy_from_slice(&mint_limbs[..pi::BRIDGE_MINT_VALUE_LIMBS_LEN]);
    // RETIRED slots (VERB-LOCKSTEP): BridgeLock / CreateEscrow no longer exist,
    // so their limb slots are pinned to the zero sentinel (PI layout unchanged
    // until the descriptor-regeneration lane compacts it).
    for i in 0..pi::BRIDGE_LOCK_VALUE_LIMBS_LEN {
        public_inputs[pi::BRIDGE_LOCK_VALUE_LIMBS_BASE + i] = BabyBear::ZERO;
    }
    for i in 0..pi::CREATE_ESCROW_AMOUNT_LIMBS_LEN {
        public_inputs[pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE + i] = BabyBear::ZERO;
    }
    // Unused context-field shadows (the context-supplied limbs remain in
    // EffectVmContext for forward-compat with a per-effect-instance
    // refinement; today they're recomputed from `effects`).
    let _ = (
        context.bridge_mint_value_limbs,
        context.bridge_lock_value_limbs,
        context.create_escrow_amount_limbs,
    );

    // ---- EmitEvent binding (closes #110) ----
    //
    // Project the canonical (topic_hash, payload_hash) of the first
    // EmitEvent row into PI[EMIT_EVENT_TOPIC_HASH] / PI[EMIT_EVENT_PAYLOAD_HASH]
    // and pin the count. The AIR's per-row PI-equality constraint (gated by
    // `sel::EMIT_EVENT`) pins each emit-event row's params[0..8] to the low
    // 4 felts of each hash; the high 4 felts are bound via
    // `compute_effects_hash` absorption and the off-AIR PI-match loop.
    //
    // Sentinel: when no EmitEvent rows are present, both 8-felt slots stay
    // at the zero default. When multiple emit-event rows are present, the
    // per-row equality constraint forces them all to share the same
    // (topic, payload); the off-AIR verifier rejects bundles whose
    // EMIT_EVENT_COUNT > 1 disagree on hashes (out-of-scope for this lane;
    // documented in the EmitEvent variant docstring).
    let mut emit_event_count: u32 = 0;
    let mut first_emit_topic: Option<[BabyBear; 8]> = None;
    let mut first_emit_payload: Option<[BabyBear; 8]> = None;
    for eff in effects {
        if let Effect::EmitEvent {
            topic_hash,
            payload_hash,
        } = eff
        {
            emit_event_count += 1;
            if first_emit_topic.is_none() {
                first_emit_topic = Some(*topic_hash);
                first_emit_payload = Some(*payload_hash);
            }
        }
    }
    public_inputs[pi::EMIT_EVENT_COUNT] = BabyBear::new(emit_event_count);
    if let (Some(t), Some(p)) = (first_emit_topic, first_emit_payload) {
        public_inputs[pi::EMIT_EVENT_TOPIC_HASH_BASE
            ..pi::EMIT_EVENT_TOPIC_HASH_BASE + pi::EMIT_EVENT_TOPIC_HASH_LEN]
            .copy_from_slice(&t[..pi::EMIT_EVENT_TOPIC_HASH_LEN]);
        public_inputs[pi::EMIT_EVENT_PAYLOAD_HASH_BASE
            ..pi::EMIT_EVENT_PAYLOAD_HASH_BASE + pi::EMIT_EVENT_PAYLOAD_HASH_LEN]
            .copy_from_slice(&p[..pi::EMIT_EVENT_PAYLOAD_HASH_LEN]);
    }

    // ---- D5: NoteSpend nullifier cross-binding (approach A) ----
    //
    // Surface the first NoteSpend row's folded nullifier (param0) into
    // PI[NOTESPEND_NULLIFIER]. The AIR's per-row gated constraint pins every
    // sel::NOTE_SPEND row's param0 to this slot.
    //
    // ⚠ CORRECTED 2026-08-02. This comment used to continue "and the off-AIR verifier
    // reconstructs the same value from the SCHEMA_NOTE_SPEND binding proof's fields[0]".
    // THAT VERIFIER DOES NOT EXIST — `grep -rn NOTESPEND_NULLIFIER turn/src` returns only an
    // unrelated test name, and no crate outside `circuit/` reads the constant at all. The
    // binding proof does carry the RAW 32 bytes as `fields[0]`
    // (`turn/src/executor/proof_verify.rs`), but nothing folds them and nothing compares them
    // to PI 198. So this slot is pinned felt-to-felt against the trace's own param0 and
    // NOTHING ELSE. See the same correction above `pi::NOTESPEND_NULLIFIER`.
    //
    // Sentinel: ZERO when no NoteSpend row is present. Multiple
    // NoteSpend rows must share the same folded nullifier (the per-row
    // constraint forces it) — multi-distinct-nullifier proofs need PI
    // extension (deferred, same as EmitEvent's EMIT_EVENT_COUNT > 1 note).
    let first_notespend_nullifier: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::NoteSpend { nullifier, .. } = eff {
            Some(*nullifier)
        } else {
            None
        }
    });
    if let Some(n) = first_notespend_nullifier {
        public_inputs[pi::NOTESPEND_NULLIFIER] = n;
    }

    // ---- D5b: NoteCreate commitment cross-binding (approach A) ----
    //
    // Surface the first NoteCreate row's folded commitment (param0,
    // NOTE_COMMITMENT) into PI[NOTECREATE_COMMITMENT]. The AIR's per-row gated
    // constraint pins every sel::NOTE_CREATE row's param0 to this slot, and the
    // off-AIR verifier reconstructs the same value from the SCHEMA_NOTE_CREATE
    // binding proof's fields[0]. Sentinel: ZERO when no NoteCreate row is
    // present. Multi-distinct-commitment proofs need PI extension (deferred,
    // same posture as NoteSpend).
    let first_notecreate_commitment: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::NoteCreate { commitment, .. } = eff {
            Some(*commitment)
        } else {
            None
        }
    });
    if let Some(c) = first_notecreate_commitment {
        public_inputs[pi::NOTECREATE_COMMITMENT] = c;
    }

    // ---- D5c: Burn target cross-binding (approach A) ----
    //
    // Surface the first Burn row's folded target (param0, BURN_TARGET) into
    // PI[BURN_TARGET_PI]. The AIR's per-row gated constraint pins every
    // sel::BURN row's param0 to this slot, and the off-AIR verifier
    // reconstructs the same value from the SCHEMA_BURN binding proof's
    // fields[0] (the ledger-validated burn target). Sentinel: ZERO when no
    // Burn row is present.
    let first_burn_target: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::Burn { target_hash, .. } = eff {
            Some(target_hash[0])
        } else {
            None
        }
    });
    if let Some(t) = first_burn_target {
        public_inputs[pi::BURN_TARGET_PI] = t;
    }

    // ---- γ.2 follow-up (#131/#132): per-cell federation + owner binding ----
    //
    // Surface the 4-felt commitments to the federation id + owner cell id.
    // The row-0 boundary constraints (air.rs) pin these to the matching aux
    // columns, and the off-AIR verifier reconstructs the expected values from
    // the trusted federation id + owner cell id and rejects any disagreement.
    let fed_id_4 = canonical_id_to_felts_4(&context.federation_id);
    let owner_id_4 = canonical_id_to_felts_4(&context.owner_cell_id);
    public_inputs[pi::FEDERATION_ID_BASE..pi::FEDERATION_ID_BASE + pi::FEDERATION_ID_LEN]
        .copy_from_slice(&fed_id_4[..pi::FEDERATION_ID_LEN]);
    public_inputs[pi::OWNER_CELL_ID_BASE..pi::OWNER_CELL_ID_BASE + pi::OWNER_CELL_ID_LEN]
        .copy_from_slice(&owner_id_4[..pi::OWNER_CELL_ID_LEN]);

    // ---- Slot-caveat manifest (Cav-Codex Block 3) ----
    //
    // Project the cell-program-declared `StateConstraint` set into a
    // fixed-size PI table. The verifier extracts the table and
    // re-evaluates each entry against the state_before / state_after
    // columns; the *executor* is responsible for honestly populating
    // the manifest from `CellProgram::Predicate(...)`. Any tampering
    // with an entry shows up as a PI-match mismatch at receipt
    // verification time (the receipt re-computes the expected PI from
    // the cell's program).
    let cav_count = context.slot_caveat_count.min(pi::MAX_SLOT_CAVEATS as u32);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(cav_count);
    for i in 0..(cav_count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        context.slot_caveat_manifest[i]
            .write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }

    // ---- PI v3 tail (THE ROTATION) ----
    //
    // Surface the committed-height commitment limb and the staged caveat
    // tags. The committed-height slot closes the temporal-gate anti-ghost
    // tooth: the prover cannot choose a height because the canonical
    // commitment already absorbed it. The tag slots are staged zero
    // sentinels today; the optimistic-proving / dispute modes (#169) will
    // populate them later.
    public_inputs[pi::v3::COMMITTED_HEIGHT] =
        BabyBear::new((context.committed_height & 0x7FFF_FFFF) as u32);
    public_inputs[pi::v3::RATE_BOUND_TAG] = BabyBear::new(context.rate_bound_tag);
    public_inputs[pi::v3::CHALLENGE_WINDOW_TAG] = BabyBear::new(context.challenge_window_tag);

    // ---- Light-client conservation: ASSET_CLASS (PI v3) ----
    //
    // Surface the per-cell asset class (the folded committed token_id) into
    // PI[v3::ASSET_CLASS]. The row-0 boundary constraint (air.rs) pins the
    // in-trace `aux_off::ASSET_CLASS` aux column to this slot, so the proof
    // commits to its asset class. The per-asset cross-cell conservation gate
    // partitions each proof's NET_DELTA by this PI-bound class — enforcing
    // per-asset Σδ=0 WITHOUT a ledger lookup. Zero sentinel = the native asset.
    public_inputs[pi::v3::ASSET_CLASS] = context.asset_class;

    // ---- Custom proof entries (PI layout v3 + proof-bind rotation: 8 vk + 8 commit) ----
    for (i, (vk_hash, proof_commit)) in custom_entries.iter().enumerate() {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        public_inputs[base..base + 8].copy_from_slice(&vk_hash[..]);
        public_inputs[base + 8..base + 16].copy_from_slice(&proof_commit[..]);
    }

    assert_eq!(public_inputs.len(), pi_len);
    Ok((trace, public_inputs))
}

/// Encode a signed balance delta as (magnitude, sign_bit) for public inputs.
pub fn encode_net_delta(delta: i64) -> (BabyBear, BabyBear) {
    if delta < 0 {
        (BabyBear::new((-delta) as u32), BabyBear::ONE)
    } else {
        (BabyBear::new(delta as u32), BabyBear::ZERO)
    }
}

/// Extract the net balance delta from public inputs.
pub fn extract_net_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < pi::BASE_COUNT {
        return None;
    }
    let magnitude = public_inputs[pi::NET_DELTA_MAG].0 as i64;
    let sign_bit = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign_bit == 1 {
        Some(-magnitude)
    } else {
        Some(magnitude)
    }
}

/// Extract the PI-bound ASSET CLASS (PI v3) from public inputs.
///
/// This is the per-cell asset / issuer-cell class the per-asset cross-cell
/// conservation gate partitions on, surfaced as `PI[v3::ASSET_CLASS]` and
/// pinned (row-0 boundary) to the trace's `aux_off::ASSET_CLASS` column. The
/// executor and the light-client bundle path read it FROM HERE — not from a
/// ledger lookup — so per-asset Σδ=0 is enforced WITHOUT a ledger. Returns
/// `None` when the PI vector is too short to carry the active layout.
pub fn extract_asset_class(public_inputs: &[BabyBear]) -> Option<BabyBear> {
    if public_inputs.len() < pi::ACTIVE_BASE_COUNT {
        return None;
    }
    Some(public_inputs[pi::v3::ASSET_CLASS])
}

/// Extract the custom proof commitments from public inputs.
/// Returns a vec of (program_vk_hash, proof_commitment) tuples.
/// Cav-Codex Block 3: extract the (count, entries) slot-caveat
/// manifest from a public-inputs vector. Returns up to
/// `pi::MAX_SLOT_CAVEATS` entries; trailing entries past `count` are
/// dropped. Use [`verify_slot_caveat_manifest`] to re-evaluate each
/// against state_before / state_after.
pub fn extract_slot_caveat_manifest(public_inputs: &[BabyBear]) -> Vec<SlotCaveatEntry> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let count = (public_inputs[pi::SLOT_CAVEAT_COUNT].0 as usize).min(pi::MAX_SLOT_CAVEATS);
    let mut result = Vec::with_capacity(count);
    for i in 0..count {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        result.push(SlotCaveatEntry {
            type_tag: public_inputs[base].0,
            slot_index: (public_inputs[base + 1].0 & 0xFF) as u8,
            params: [
                public_inputs[base + 2],
                public_inputs[base + 3],
                public_inputs[base + 4],
                public_inputs[base + 5],
            ],
        });
    }
    result
}

pub fn extract_custom_proof_commitments(
    public_inputs: &[BabyBear],
) -> Vec<([BabyBear; 8], [BabyBear; 8])> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    // ⚑ DERIVED, not read. This was `public_inputs[pi::CUSTOM_EFFECT_COUNT]` — a felt the PROVER
    // wrote and no constraint read — used to slice the vector the VERIFIER holds. The length is a
    // fact about that vector; take it from there. (Seven-slot compaction, 2026-08-07.)
    let custom_count = pi::custom_entry_count(public_inputs.len());
    let mut result = Vec::with_capacity(custom_count);
    for i in 0..custom_count {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        if base + pi::CUSTOM_ENTRY_SIZE > public_inputs.len() {
            break;
        }
        // Proof-bind flag-day rotation: 8 vk_hash felts + 8 proof_commit felts
        // per entry (`CUSTOM_ENTRY_SIZE == 16`). A legacy 12-felt entry vector
        // fails the length guard above (PI length mismatch) — never mis-sliced.
        let vk_hash = core::array::from_fn(|j| public_inputs[base + j]);
        let proof_commit = core::array::from_fn(|j| public_inputs[base + 8 + j]);
        result.push((vk_hash, proof_commit));
    }
    result
}
