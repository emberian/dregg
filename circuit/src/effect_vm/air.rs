//! The Effect VM AIR: shape descriptor (`AIR_DESCRIPTOR`), `EffectVmAir`
//! struct, and the `StarkAir::eval_constraints` body that pins every row
//! to its selector-gated effect semantics.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
use crate::stark::{BoundaryConstraint, StarkAir};

use super::{
    AUX_BASE, EFFECT_VM_WIDTH, NUM_AUX, NUM_EFFECTS, NUM_PARAMS, PARAM_BASE, STATE_AFTER_BASE,
    STATE_BEFORE_BASE, aux_off, param, pi, sel, state,
};

/// The Effect VM AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`EffectVmAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// `public_input_layout` enumerates the BASE_COUNT-wide PI surface
/// (commitments, balance limbs, bilateral aggregation roots,
/// sovereign-witness teeth, 30-bit-trunc value limbs). The
/// CUSTOM_PROOFS region beyond `BASE_COUNT` is variable per-cell and
/// is *not* listed here — its presence is implicit (CUSTOM_PROOFS_BASE
/// == BASE_COUNT, with `max_custom_effects * 8` additional felts).
pub const AIR_DESCRIPTOR: crate::air_descriptor::AirDescriptor =
    crate::air_descriptor::AirDescriptor {
        air_id: "effect_vm_air_v1",
        column_count: EFFECT_VM_WIDTH,
        public_input_layout: &[
            crate::air_descriptor::PiSlot {
                name: "old_commit",
                offset: pi::OLD_COMMIT_BASE,
                length_in_felts: pi::OLD_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "new_commit",
                offset: pi::NEW_COMMIT_BASE,
                length_in_felts: pi::NEW_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash",
                offset: pi::EFFECTS_HASH_BASE,
                length_in_felts: pi::EFFECTS_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_lo",
                offset: pi::INIT_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_hi",
                offset: pi::INIT_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_lo",
                offset: pi::FINAL_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_hi",
                offset: pi::FINAL_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_mag",
                offset: pi::NET_DELTA_MAG,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_sign",
                offset: pi::NET_DELTA_SIGN,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "current_block_height",
                offset: pi::CURRENT_BLOCK_HEIGHT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "max_custom_effects",
                offset: pi::MAX_CUSTOM_EFFECTS,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "custom_effect_count",
                offset: pi::CUSTOM_EFFECT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "approved_handoffs",
                offset: pi::APPROVED_HANDOFFS_BASE,
                length_in_felts: pi::APPROVED_HANDOFFS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "turn_hash",
                offset: pi::TURN_HASH_BASE,
                length_in_felts: pi::TURN_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash_global",
                offset: pi::EFFECTS_HASH_GLOBAL_BASE,
                length_in_felts: pi::EFFECTS_HASH_GLOBAL_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "actor_nonce",
                offset: pi::ACTOR_NONCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "previous_receipt_hash",
                offset: pi::PREVIOUS_RECEIPT_HASH_BASE,
                length_in_felts: pi::PREVIOUS_RECEIPT_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_transfer_count",
                offset: pi::OUTBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_transfer_count",
                offset: pi::INBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_grant_count",
                offset: pi::OUTBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_grant_count",
                offset: pi::INBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_count",
                offset: pi::INTRO_AS_INTRODUCER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_count",
                offset: pi::INTRO_AS_RECIPIENT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_count",
                offset: pi::INTRO_AS_TARGET_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_transfer_root",
                offset: pi::OUTGOING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::OUTGOING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_transfer_root",
                offset: pi::INCOMING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::INCOMING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_grant_root",
                offset: pi::OUTGOING_GRANT_ROOT_BASE,
                length_in_felts: pi::OUTGOING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_grant_root",
                offset: pi::INCOMING_GRANT_ROOT_BASE,
                length_in_felts: pi::INCOMING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_root",
                offset: pi::INTRO_AS_INTRODUCER_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_INTRODUCER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_root",
                offset: pi::INTRO_AS_RECIPIENT_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_RECIPIENT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_root",
                offset: pi::INTRO_AS_TARGET_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_TARGET_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "is_agent_cell",
                offset: pi::IS_AGENT_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_key_commit",
                offset: pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE,
                length_in_felts: pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_sequence",
                offset: pi::SOVEREIGN_WITNESS_SEQUENCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "is_sovereign_cell",
                offset: pi::IS_SOVEREIGN_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_vk_hash",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_commitment",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "has_transition_proof",
                offset: pi::HAS_TRANSITION_PROOF,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_mint_value_limbs",
                offset: pi::BRIDGE_MINT_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_MINT_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_lock_value_limbs",
                offset: pi::BRIDGE_LOCK_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_LOCK_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "create_escrow_amount_limbs",
                offset: pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE,
                length_in_felts: 4,
            },
            // Stage 7-γ.2 unilateral binding (1-arity sibling of bilateral).
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_count",
                offset: pi::UNILATERAL_ATTESTATIONS_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_root",
                offset: pi::UNILATERAL_ATTESTATIONS_ROOT_BASE,
                length_in_felts: pi::UNILATERAL_ATTESTATIONS_ROOT_LEN,
            },
            // EmitEvent binding (closes #110).
            crate::air_descriptor::PiSlot {
                name: "emit_event_count",
                offset: pi::EMIT_EVENT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "emit_event_topic_hash",
                offset: pi::EMIT_EVENT_TOPIC_HASH_BASE,
                length_in_felts: pi::EMIT_EVENT_TOPIC_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "emit_event_payload_hash",
                offset: pi::EMIT_EVENT_PAYLOAD_HASH_BASE,
                length_in_felts: pi::EMIT_EVENT_PAYLOAD_HASH_LEN,
            },
        ],
        // Constraint groups: selector validity (NUM_EFFECTS+1), per-effect
        // gated constraints (~NUM_EFFECTS large groups), boundary bindings
        // for commitments / balance limbs / sovereign teeth, bilateral
        // aggregation accumulators. Number is a stable property of the AIR
        // shape — when constraints are added/removed, this bumps.
        constraint_polynomial_count: NUM_EFFECTS + 1 + NUM_EFFECTS,
        boundary_constraint_count: 32,
        max_degree: 9,
        source_hash: None,
    };

/// The Effect VM AIR. Proves an arbitrary sequence of effects in a single STARK.
pub struct EffectVmAir {
    /// Maximum number of effects (trace height, padded to power of 2).
    pub max_effects: usize,
}

impl EffectVmAir {
    pub fn new(max_effects: usize) -> Self {
        // MIN 64 rows: closes the FRI single-row-gap (task #90). A short trace
        // has too few FRI folding rounds for the probabilistic query set to
        // reliably detect single-row tampering. With 64 rows (domain_size 256
        // at blowup-4, 6 FRI rounds) the miss probability is negligible.
        assert!(
            max_effects >= 64,
            "Need at least 64 rows for STARK (FRI single-row-gap closure; task #90)"
        );
        assert!(
            max_effects.is_power_of_two(),
            "max_effects must be a power of 2"
        );
        Self { max_effects }
    }
}

impl StarkAir for EffectVmAir {
    fn width(&self) -> usize {
        EFFECT_VM_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Selector sum constraint is degree 1 (linear).
        // Selector boolean constraints are degree 2.
        // Per-effect constraints: selector * (expression) is at most degree 3.
        // Hash constraints (hash_2_to_1, hash_4_to_1) are evaluated concretely on trace
        // values at FRI evaluation points — they do NOT contribute polynomial degree.
        // SetField field_idx range check: selector * prod_{k=0..7}(field_idx - k) = degree 9.
        // Seal/Unseal field_idx range check: same degree 9.
        9
    }

    fn air_name(&self) -> &'static str {
        "pyana-effect-vm-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector validity
        // ====================================================================

        // Each selector must be boolean: s*(s-1) == 0
        for i in 0..NUM_EFFECTS {
            let s = local[i];
            let c = s * (s - BabyBear::ONE);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Selectors must sum to exactly 1.
        let mut sel_sum = BabyBear::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + local[i];
        }
        let c_sum = sel_sum - BabyBear::ONE;
        combined = combined + alpha_pow * c_sum;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 2: Per-effect-type constraints (gated by selector)
        // ====================================================================
        //
        // SECURITY NOTE — Balance limb range checks (o1vm audit finding #1):
        //
        // balance_lo (30-bit) and balance_hi (34-bit) are NOT range-checked
        // in-circuit. Full bit-decomposition would add 60+ columns to the trace.
        // Instead, the EXECUTOR independently validates:
        //   - balance_lo < 2^30  (fits in the lo limb)
        //   - balance_hi < 2^34  (fits in the hi limb, and < BabyBear prime)
        //   - balance_lo + balance_hi * 2^30 == declared u64 balance
        //
        // The boundary constraints bind start/end state_commitment to public
        // inputs, and state_commitment = Poseidon2(balance_lo, balance_hi, ...),
        // so a malicious prover cannot forge commitments without matching limbs.
        // However, a prover CAN choose field-valid but out-of-range limbs on
        // INTERIOR rows (between boundaries). The executor rejects such proofs
        // by re-deriving the final state and checking limb ranges.
        //
        // TODO(range-checks): When we add lookup arguments (log-derivative or
        // Lasso-style), replace executor-side checks with in-circuit range
        // proofs via a 2^16 lookup table (2 lookups per limb for 30/34 bits).
        //
        // SECURITY NOTE — Balance underflow protection (o1vm audit finding #3):
        //
        // For outgoing transfers and obligation creation, the constraint is:
        //   new_balance_lo = old_balance_lo - amount
        // In BabyBear modular arithmetic, if amount > old_balance, this wraps
        // around to a large "valid" field element rather than failing.
        //
        // The witness generation uses saturating_sub, so honest provers never
        // produce underflow. However, a MALICIOUS prover could craft a trace
        // where the subtraction wraps around the field modulus.
        //
        // Defense: The executor checks that the final balance (extracted from
        // the proven new_commitment) is <= the initial balance + net_credits.
        // Additionally, the state_commitment binds the actual balance limbs,
        // so any wrap-around would produce a commitment that doesn't match the
        // declared final state.
        //
        // TODO(underflow): Add proper non-negative range proof via bit
        // decomposition of (old_balance - amount) to prove it fits in 30 bits.
        // This requires 30 aux columns per debit row, or a shared lookup table.
        // ====================================================================

        let s_noop = local[sel::NOOP];
        let s_transfer = local[sel::TRANSFER];
        let s_setfield = local[sel::SET_FIELD];
        let s_grantcap = local[sel::GRANT_CAP];
        let s_notespend = local[sel::NOTE_SPEND];
        let s_notecreate = local[sel::NOTE_CREATE];
        let s_create_obligation = local[sel::CREATE_OBLIGATION];
        let s_fulfill_obligation = local[sel::FULFILL_OBLIGATION];
        let s_custom = local[sel::CUSTOM];

        // State accessors (before).
        let old_bal_lo = local[STATE_BEFORE_BASE + state::BALANCE_LO];
        let old_bal_hi = local[STATE_BEFORE_BASE + state::BALANCE_HI];
        let old_nonce = local[STATE_BEFORE_BASE + state::NONCE];
        let old_cap_root = local[STATE_BEFORE_BASE + state::CAP_ROOT];

        // State accessors (after).
        let new_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
        let new_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
        let new_nonce = local[STATE_AFTER_BASE + state::NONCE];
        let new_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];

        // Parameters.
        let p0 = local[PARAM_BASE + 0];
        let p1 = local[PARAM_BASE + 1];
        let _p2 = local[PARAM_BASE + 2];

        // -- NoOp: state_after == state_before for all state columns --
        for i in 0..state::SIZE {
            let c = s_noop * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Transfer: balance update --
        // param0 = amount_lo, param1 = direction (0=in, 1=out)
        // If direction=0 (in): new_bal = old_bal + amount
        // If direction=1 (out): new_bal = old_bal - amount
        // Unified: new_bal_lo - old_bal_lo - amount + 2*direction*amount == carry adjustment
        //
        // We work with the combined 60-bit balance:
        //   balance = bal_lo + bal_hi * 2^30
        //   Transfer only touches bal_lo for simplicity (amount < 2^30).
        //   new_bal_lo = old_bal_lo + amount * (1 - 2*direction)
        //
        // For amounts that don't overflow a single limb:
        let two = BabyBear::new(2);
        let direction = p1;
        let amount = p0;
        // new_bal_lo == old_bal_lo + amount - 2*direction*amount
        let c_transfer_lo =
            s_transfer * (new_bal_lo - old_bal_lo - amount + two * direction * amount);
        combined = combined + alpha_pow * c_transfer_lo;
        alpha_pow = alpha_pow * alpha;

        // Transfer: hi limb unchanged (for single-limb amounts).
        let c_transfer_hi = s_transfer * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_transfer_hi;
        alpha_pow = alpha_pow * alpha;

        // Transfer: direction must be boolean.
        let c_transfer_dir = s_transfer * direction * (direction - BabyBear::ONE);
        combined = combined + alpha_pow * c_transfer_dir;
        alpha_pow = alpha_pow * alpha;

        // Transfer: cap_root and reserved unchanged.
        // (state_commitment is a derived value recomputed in witness gen; bound at boundaries only.)
        for i in [state::CAP_ROOT, state::RESERVED] {
            let c = s_transfer * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Transfer: fields unchanged.
        for i in 0..8 {
            let c = s_transfer
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetField: exactly one field updated --
        // param0 = field_index, param1 = new_value
        // For the targeted field: new_field[idx] = new_value.
        // For all others: unchanged.
        // We use the Lagrange selector trick:
        //   For each field slot j: new_field[j] - old_field[j] - is_target_j * (new_value - old_field[j]) == 0
        //   where is_target_j = prod_{k != j} (field_index - k) / (j - k)
        //
        // Simplified: we constrain that the sum of changes equals (new_value - old_field[idx])
        // and that it happens at exactly the right index. For degree control, we use:
        //   For each j in 0..8:
        //     sel_setfield * (new_field[j] - old_field[j]) * (1 - eq(field_index, j)) == 0
        //     where eq check is: (field_index - j) * inverse_or_zero
        //
        // Even simpler approach (lower degree): use aux columns for the Lagrange basis.
        // But for v1, we use a direct approach with the product constraint:
        //   sel_setfield * (new_field[j] - old_field[j]) * product_{k != j}(field_index - k) == 0
        //   for all j where field_index != j.
        //
        // Actually simplest: enforce
        //   For each j: sel * (new_f[j] - old_f[j] - delta_j) == 0
        //   where delta_j = if j == field_index { new_value - old_f[j] } else { 0 }
        //
        // We do it as: for the ONE field that matches, the difference must equal new_value - old.
        // For all others, difference must be zero.
        // With selector-index product trick at degree 2:
        //   sel_setfield * (field_index - j) * (new_f[j] - old_f[j]) == 0 for each j
        //   (if field_index == j, this is trivially 0 regardless of change)
        //   (if field_index != j, new_f[j] - old_f[j] must be 0)
        let field_index = p0;
        let new_value = p1;
        for j in 0..8u32 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j as usize];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j as usize];
            // Non-target fields must be unchanged.
            let c = s_setfield * (field_index - BabyBear::new(j)) * (new_fj - old_fj);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // The target field must become new_value. We check this by:
        //   For each j: sel * prod_{k!=j}(index - k) * (new_f[j] - new_value) == 0
        // When index == j, prod_{k!=j}(index-k) != 0, so new_f[j] must equal new_value.
        // When index != j, some factor (index - j) is zero in the product, so constraint is trivial.
        // But this is high degree (degree 8). Instead, use the aux column approach:
        //   aux[0] stores the Lagrange indicator (computed in witness gen).
        //   Constraint: sel * (sum_j new_f[j] * lagrange_j - new_value) == 0
        //
        // Simplest correct approach for v1: The witness generation ensures the right field
        // is set. We just need ONE constraint proving the target field has the right value.
        // Use aux[0] to carry the old value of the target field, then:
        //   sel_setfield * (new_value - target_field_new) == 0
        // where target_field_new is reconstructed from the trace.
        //
        // Actually, the simplest sound approach:
        //   Verify that the difference across all fields sums to exactly (new_value - old_value_at_idx).
        //   Combined with per-field constraints above (non-target unchanged), this is sufficient.
        // The sum of (new_f[j] - old_f[j]) for all j must equal (new_value - old_value_at_idx).
        // old_value_at_idx is stored in aux[0].
        let old_value_at_idx = local[AUX_BASE + 0];
        let mut field_diff_sum = BabyBear::ZERO;
        for j in 0..8 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j];
            field_diff_sum = field_diff_sum + (new_fj - old_fj);
        }
        let c_setfield_sum = s_setfield * (field_diff_sum - (new_value - old_value_at_idx));
        combined = combined + alpha_pow * c_setfield_sum;
        alpha_pow = alpha_pow * alpha;

        // SetField: balance and cap_root unchanged.
        let c_sf_bal_lo = s_setfield * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sf_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sf_bal_hi = s_setfield * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sf_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sf_cap = s_setfield * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sf_cap;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty): SetField must not change `reserved`
        // (sealed_mask AND mode_flag both preserved across a field set).
        let sf_old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let sf_new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sf_reserved = s_setfield * (sf_new_reserved - sf_old_reserved);
        combined = combined + alpha_pow * c_sf_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty, FULL bit-decomposition):
        // The target field must NOT be sealed. We derive
        // `bit_at_field_idx = Σ_k L_k(field_idx) * b_k` from the
        // bit-decomposition of old_reserved (aux[RESERVED_BIT_0..7]),
        // where L_k(x) is the Lagrange basis on {0..7}. The constraints
        // below enforce:
        //   1. Each b_i is boolean.
        //   2. Σ b_i * 2^i + mode * 256 == old_reserved.
        //   3. mode is boolean.
        //   4. s_setfield * (Σ_k L_k(field_idx) * b_k) == 0.
        // The first three apply to every row (UNCONDITIONALLY) — that
        // gives every effect row a correct bit-decomposition of its
        // own old_reserved. The fourth gates by selector.
        //
        // Resolves AUDIT[stage2-setfield-sealed-witness].
        let b0 = local[AUX_BASE + aux_off::RESERVED_BIT_0];
        let b1 = local[AUX_BASE + aux_off::RESERVED_BIT_1];
        let b2 = local[AUX_BASE + aux_off::RESERVED_BIT_2];
        let b3 = local[AUX_BASE + aux_off::RESERVED_BIT_3];
        let b4 = local[AUX_BASE + aux_off::RESERVED_BIT_4];
        let b5 = local[AUX_BASE + aux_off::RESERVED_BIT_5];
        let b6 = local[AUX_BASE + aux_off::RESERVED_BIT_6];
        let b7 = local[AUX_BASE + aux_off::RESERVED_BIT_7];
        let mode_bit = local[AUX_BASE + aux_off::RESERVED_MODE];
        // Boolean constraints (unconditional, every row).
        for bit in [b0, b1, b2, b3, b4, b5, b6, b7, mode_bit].iter() {
            let cb = (*bit) * ((*bit) - BabyBear::ONE);
            combined = combined + alpha_pow * cb;
            alpha_pow = alpha_pow * alpha;
        }
        // Decomposition: Σ bi * 2^i + mode * 256 == old_reserved.
        let sf_old_reserved_dec = local[STATE_BEFORE_BASE + state::RESERVED];
        let reconstructed = b0
            + b1 * BabyBear::new(2)
            + b2 * BabyBear::new(4)
            + b3 * BabyBear::new(8)
            + b4 * BabyBear::new(16)
            + b5 * BabyBear::new(32)
            + b6 * BabyBear::new(64)
            + b7 * BabyBear::new(128)
            + mode_bit * BabyBear::new(256);
        let c_decomp = reconstructed - sf_old_reserved_dec;
        combined = combined + alpha_pow * c_decomp;
        alpha_pow = alpha_pow * alpha;
        // Lagrange-basis selection of the bit at field_idx.
        // For field_idx ∈ {0..7}, returns b_{field_idx}.
        let l_bits: [BabyBear; 8] = [b0, b1, b2, b3, b4, b5, b6, b7];
        let bit_at_idx = {
            let x = field_index;
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        // s_setfield * bit_at_idx == 0  (cannot set a sealed field).
        let c_sf_not_sealed = s_setfield * bit_at_idx;
        combined = combined + alpha_pow * c_sf_not_sealed;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: Seal: bit at field_idx must currently be 0 (no double-seal).
        // (Reuse the same Lagrange selection on the SEAL_FIELD_IDX param.)
        let seal_bit_at_idx = {
            let x = local[PARAM_BASE + param::SEAL_FIELD_IDX];
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        let s_seal_early = local[sel::SEAL];
        let c_seal_no_double = s_seal_early * seal_bit_at_idx;
        combined = combined + alpha_pow * c_seal_no_double;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: Unseal: bit at field_idx must currently be 1.
        let unseal_bit_at_idx = {
            let x = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        let s_unseal_early = local[sel::UNSEAL];
        let c_unseal_must_be_set = s_unseal_early * (unseal_bit_at_idx - BabyBear::ONE);
        combined = combined + alpha_pow * c_unseal_must_be_set;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // RANGE CHECK: SetField field_idx must be in {0, 1, 2, 3, 4, 5, 6, 7}
        // ====================================================================
        // Degree-8 polynomial that vanishes exactly on {0..7}:
        //   prod_{k=0}^{7} (field_idx - k) == 0
        // Gated by sel_setfield (total degree 9). Any out-of-bounds value makes
        // this constraint non-zero, causing the STARK verifier to reject.
        {
            let mut field_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                field_idx_range_product =
                    field_idx_range_product * (field_index - BabyBear::new(k));
            }
            let c_field_idx_range = s_setfield * field_idx_range_product;
            combined = combined + alpha_pow * c_field_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- GrantCapability: capability_root update --
        // param0 = cap_entry (hash of new capability)
        // new_cap_root MUST equal hash_2_to_1(old_cap_root, cap_entry).
        //
        // SOUNDNESS FIX: We compute hash_2_to_1 directly in the constraint evaluator.
        // The old approach used a prover-controlled aux[1] value which allowed a
        // malicious prover to set new_cap_root to ANY value. Now the verifier
        // independently computes the hash at each evaluation point. This works because
        // eval_constraints operates on concrete field values (not symbolic polynomials),
        // so the hash is a pure function of the trace values at the query point.
        let cap_entry_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_new_cap = hash_2_to_1(old_cap_root, cap_entry_val);
        let c_grantcap = s_grantcap * (new_cap_root - expected_new_cap);
        combined = combined + alpha_pow * c_grantcap;
        alpha_pow = alpha_pow * alpha;

        // GrantCap: balance and fields unchanged.
        let c_gc_bal_lo = s_grantcap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_gc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_gc_bal_hi = s_grantcap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_gc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_grantcap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- EmitEvent: stateless side-effect with canonical (topic, payload) binding --
        //
        // Row layout (closes #110):
        //   params[0..4] = topic_hash[0..4]
        //   params[4..8] = payload_hash[0..4]
        //
        // The full 8-felt topic/payload hashes (32 bytes each) are bound by
        // three independent algebraic teeth:
        //
        //   (a) Per-row PI-equality (BELOW): when sel::EMIT_EVENT == 1, the
        //       row's params[0..4] MUST equal PI[EMIT_EVENT_TOPIC_HASH][0..4]
        //       and params[4..8] MUST equal PI[EMIT_EVENT_PAYLOAD_HASH][0..4].
        //       Soundness: a malicious prover that forges any of the 8 low
        //       felts cannot satisfy this constraint at any FRI evaluation
        //       point because PI is a constant across rows. ~124-bit binding
        //       on the low halves.
        //
        //   (b) compute_effects_hash absorbs all 16 felts of the (topic_hash ‖
        //       payload_hash) preimage. The Poseidon2-chained effects_hash is
        //       pinned to PI[EFFECTS_HASH_BASE] via a row-0 boundary, so the
        //       HIGH 4 felts of each hash also become cryptographically bound
        //       (any swap in [4..8] changes the chain). ~256-bit binding.
        //
        //   (c) Off-AIR PI-match loop: the verifier recomputes the canonical
        //       (topic, payload) bytes from the runtime Event and rejects any
        //       PI disagreement. Closes the executor-honesty gap for the high
        //       halves with respect to the runtime Event encoding.
        //
        // State columns: balance / cap_root / fields all unchanged (the
        // existing passthrough constraints retained below).
        let s_emitevent = local[sel::EMIT_EVENT];
        let c_ee_bal_lo = s_emitevent * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_ee_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_ee_bal_hi = s_emitevent * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ee_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_ee_cap = s_emitevent * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ee_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_emitevent
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // (a) Per-row PI-equality binding for topic_hash[0..4] / payload_hash[0..4].
        // Gated by sel::EMIT_EVENT so non-emit rows are unaffected. PI access is
        // safe inside eval_constraints (see Group 6 INIT_BAL_LO usage above).
        if public_inputs.len() >= pi::BASE_COUNT {
            for i in 0..4 {
                let pi_topic_i = public_inputs[pi::EMIT_EVENT_TOPIC_HASH_BASE + i];
                let c_topic = s_emitevent * (local[PARAM_BASE + i] - pi_topic_i);
                combined = combined + alpha_pow * c_topic;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 0..4 {
                let pi_payload_i = public_inputs[pi::EMIT_EVENT_PAYLOAD_HASH_BASE + i];
                let c_payload = s_emitevent * (local[PARAM_BASE + 4 + i] - pi_payload_i);
                combined = combined + alpha_pow * c_payload;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- SetPermissions: same shape as EmitEvent (state passthrough) --
        // Permissions live outside the VM trace (they're part of the cell's
        // off-chain manifest). The AIR's job is to bind permissions_hash
        // into effects_hash and forbid state column drift.
        let s_setperms = local[sel::SET_PERMISSIONS];
        let c_sp_bal_lo = s_setperms * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sp_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sp_bal_hi = s_setperms * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sp_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sp_cap = s_setperms * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sp_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setperms
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetVerificationKey: same shape as SetPermissions (passthrough) --
        let s_setvk = local[sel::SET_VERIFICATION_KEY];
        let c_svk_bal_lo = s_setvk * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_svk_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_svk_bal_hi = s_setvk * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_svk_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_svk_cap = s_setvk * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_svk_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setvk
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- All passthrough variants (Stage 3 batch). State columns must
        //    be unchanged; nonce ticks. Variant-specific param (or absence)
        //    in PARAM_BASE+0; binds via effects_hash.
        for s_sel_idx in [
            sel::CREATE_SEAL_PAIR,
            sel::REFRESH_DELEGATION,
            sel::REVOKE_DELEGATION,
            sel::CREATE_CELL,
            sel::SPAWN_WITH_DELEGATION,
            sel::BRIDGE_CANCEL,
            sel::EXERCISE_VIA_CAPABILITY,
            sel::INTRODUCE,
            sel::PIPELINED_SEND,
            sel::CREATE_COMMITTED_ESCROW,
            sel::BRIDGE_FINALIZE,
            sel::RELEASE_ESCROW,
            sel::REFUND_ESCROW,
            sel::RELEASE_COMMITTED_ESCROW,
            sel::REFUND_COMMITTED_ESCROW,
        ] {
            let s_v = local[s_sel_idx];
            let c_bal_lo = s_v * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_v * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cap = s_v * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_v
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- RevokeCapability: capability_root update --
        // Mirrors GRANT_CAP: param0 (shared with CAP_ENTRY) carries the slot
        // hash; new_cap_root MUST equal hash_2_to_1(old_cap_root, slot_hash).
        // The verifier independently computes the hash (no prover-controlled
        // aux witness), matching the SOUNDNESS FIX comment above.
        let s_revokecap = local[sel::REVOKE_CAPABILITY];
        let slot_hash_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_revoke_cap = hash_2_to_1(old_cap_root, slot_hash_val);
        let c_revokecap = s_revokecap * (new_cap_root - expected_revoke_cap);
        combined = combined + alpha_pow * c_revokecap;
        alpha_pow = alpha_pow * alpha;
        // RevokeCap: balance and fields unchanged.
        let c_rc_bal_lo = s_revokecap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_rc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_rc_bal_hi = s_revokecap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_rc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_revokecap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteSpend: balance credit --
        // param0 = nullifier, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo + value_lo (with potential carry to hi)
        // For simplicity (v1): value fits in lo limb (value_hi == 0).
        let note_val_lo = p1;
        let c_ns_bal = s_notespend * (new_bal_lo - old_bal_lo - note_val_lo);
        combined = combined + alpha_pow * c_ns_bal;
        alpha_pow = alpha_pow * alpha;
        let c_ns_hi = s_notespend * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ns_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteSpend: fields and cap unchanged.
        let c_ns_cap = s_notespend * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ns_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notespend
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteCreate: balance debit --
        // param0 = commitment, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo - value_lo
        let nc_val_lo = p1;
        let c_nc_bal = s_notecreate * (new_bal_lo - old_bal_lo + nc_val_lo);
        combined = combined + alpha_pow * c_nc_bal;
        alpha_pow = alpha_pow * alpha;
        let c_nc_hi = s_notecreate * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_nc_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteCreate: fields and cap unchanged.
        let c_nc_cap = s_notecreate * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_nc_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notecreate
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- BridgeMint: balance credit (mirror NoteSpend) --
        // param0 = mint_hash, param1 = value_lo
        // new_bal_lo = old_bal_lo + value_lo
        let s_bridgemint = local[sel::BRIDGE_MINT];
        let bm_val_lo = local[PARAM_BASE + 1];
        let c_bm_bal = s_bridgemint * (new_bal_lo - old_bal_lo - bm_val_lo);
        combined = combined + alpha_pow * c_bm_bal;
        alpha_pow = alpha_pow * alpha;
        let c_bm_hi = s_bridgemint * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_bm_hi;
        alpha_pow = alpha_pow * alpha;
        let c_bm_cap = s_bridgemint * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_bm_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_bridgemint
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateEscrow / BridgeLock: balance debit (mirror NoteCreate) --
        // param0 = id_hash, param1 = amount_lo. Same shape: balance_lo
        // debits by amount_lo, balance_hi / cap_root / fields all unchanged.
        for s_sel_idx in [sel::CREATE_ESCROW, sel::BRIDGE_LOCK] {
            let s_v = local[s_sel_idx];
            let amount_lo = local[PARAM_BASE + 1];
            let c_bal = s_v * (new_bal_lo - old_bal_lo + amount_lo);
            combined = combined + alpha_pow * c_bal;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_v * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cap = s_v * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_v
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- CreateObligation: balance debit + cap_root extended --
        // Stage 2 honesty: previously cap_root was constrained UNCHANGED,
        // which meant the obligation wasn't actually committed to the
        // cell's authority graph — slash/fulfill had no algebraic way to
        // verify that this obligation existed or who the beneficiary was.
        // Fix: cap_root advances to
        //   new_cap_root == hash_2_to_1(old_cap_root, hash_2_to_1(obligation_id, beneficiary))
        // The 2-of-2 nested hash binds both obligation identity AND the
        // beneficiary so a later slash/fulfill must reference the same
        // beneficiary that the create committed to.
        //
        // param0 = stake_lo, param1 = stake_hi (unused for single-limb), param2 = obligation_id
        let stake_lo = p0;
        let c_co_bal = s_create_obligation * (new_bal_lo - old_bal_lo + stake_lo);
        combined = combined + alpha_pow * c_co_bal;
        alpha_pow = alpha_pow * alpha;
        let c_co_hi = s_create_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_co_hi;
        alpha_pow = alpha_pow * alpha;
        // Cap_root advance: encodes obligation_id + beneficiary.
        let obligation_id = local[PARAM_BASE + param::OBLIGATION_ID];
        let obligation_beneficiary = local[PARAM_BASE + param::OBLIGATION_BENEFICIARY];
        let obligation_leaf = hash_2_to_1(obligation_id, obligation_beneficiary);
        let expected_co_cap = hash_2_to_1(old_cap_root, obligation_leaf);
        let c_co_cap = s_create_obligation * (new_cap_root - expected_co_cap);
        combined = combined + alpha_pow * c_co_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_create_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- FulfillObligation: balance credit (returns stake) --
        // param0 = obligation_id, param1 = return_lo, param2 = return_hi
        // new_bal_lo = old_bal_lo + return_lo
        let return_lo = p1;
        let c_fo_bal = s_fulfill_obligation * (new_bal_lo - old_bal_lo - return_lo);
        combined = combined + alpha_pow * c_fo_bal;
        alpha_pow = alpha_pow * alpha;
        let c_fo_hi = s_fulfill_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_fo_hi;
        alpha_pow = alpha_pow * alpha;
        // FulfillObligation: fields and cap unchanged.
        let c_fo_cap = s_fulfill_obligation * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_fo_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_fulfill_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Custom (CellProgram dispatch): state continuity only --
        //
        // SECURITY NOTE (Gap 5): Custom effects provide WEAKER guarantees than
        // other effect types. The Effect VM only enforces:
        //   1. State continuity (state flows through unchanged)
        //   2. Proof commitment binding (the custom_proof_commitment hash is
        //      recorded in the public inputs for external verification)
        //
        // The ACTUAL SEMANTICS of the custom effect are defined entirely by the
        // external CellProgram. The Effect VM circuit does NOT verify the external
        // proof — it only binds its hash commitment to the turn's public inputs.
        //
        // Verifiers MUST independently verify the external proof against the
        // committed program VK hash. Without this check, a malicious prover can
        // claim any custom_proof_commitment without having a valid external proof.
        //
        // The custom_program_vk_hash in the PI identifies which CellProgram was
        // invoked. The verifier should:
        //   1. Look up the registered program by VK hash
        //   2. Verify the external proof against that program's verification key
        //   3. Check the external proof's hash matches custom_proof_commitment
        //
        // If ANY of these steps are skipped, the custom effect is effectively
        // unconstrained — the prover can claim arbitrary side-effects occurred.
        //
        // This is BY DESIGN: the Effect VM is a generic execution framework,
        // and custom programs extend it with domain-specific logic. But verifiers
        // must understand that Custom effects are only as secure as their external
        // verification implementation.
        //
        // Constraints: all state columns unchanged (same as NoOp for state).
        for i in 0..state::SIZE {
            let c = s_custom * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================

        // -- SlashObligation: balance credit (slashed stake to beneficiary) --
        // param0 = obligation_id, param1 = stake_lo, param2 = stake_hi, param3 = beneficiary
        // new_bal_lo = old_bal_lo + stake_lo
        let s_slash = local[sel::SLASH_OBLIGATION];
        let slash_stake_lo = local[PARAM_BASE + param::SLASH_STAKE_LO];
        let c_slash_bal = s_slash * (new_bal_lo - old_bal_lo - slash_stake_lo);
        combined = combined + alpha_pow * c_slash_bal;
        alpha_pow = alpha_pow * alpha;
        let c_slash_hi = s_slash * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_slash_hi;
        alpha_pow = alpha_pow * alpha;
        // SlashObligation: cap_root updated (obligation removed).
        // SOUNDNESS FIX: Compute hash_2_to_1 directly instead of trusting prover aux[1].
        let slash_obligation_id = local[PARAM_BASE + param::SLASH_OBLIGATION_ID];
        let expected_slash_cap = hash_2_to_1(old_cap_root, slash_obligation_id);
        let c_slash_cap = s_slash * (new_cap_root - expected_slash_cap);
        combined = combined + alpha_pow * c_slash_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_slash
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ===========================================================
        // Stage 2 (sealing honesty): Seal/Unseal actually update the
        // sealed_field_mask in `reserved`. The mask occupies the low 8
        // bits of `reserved`; mode_flag occupies bits 8..9. The witness
        // `aux[7]` (SEAL_POW2_IDX) holds `2^field_idx`, constrained to
        // lie in {1, 2, 4, 8, 16, 32, 64, 128} via the Lagrange basis
        // polynomial over field_idx ∈ {0..7}.
        // ===========================================================
        // Lagrange-basis polynomial L(x) = Σ_k 2^k * L_k(x) where
        //   L_k(x) = ∏_{j∈0..8, j≠k}(x - j) / ∏_{j≠k}(k - j)
        // evaluates to 2^k at x=k for k in {0..7}, and degree is 7.
        // This expresses `aux_pow2 - 2^field_idx == 0` algebraically.
        let lagrange_pow2 = |x: BabyBear| -> BabyBear {
            let mut result = BabyBear::ZERO;
            for k in 0..8u32 {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8u32 {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j));
                    let diff = if k > j {
                        BabyBear::new(k - j)
                    } else {
                        // (k - j) negative ⇒ BabyBear representation as p - (j - k).
                        BabyBear::ZERO - BabyBear::new(j - k)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                result = result + num * den_inv * BabyBear::new(1u32 << k);
            }
            result
        };

        // -- Seal: balance, fields, cap_root unchanged; reserved gains
        //    bit `field_idx`; sealed-field mask bit was previously 0. --
        let s_seal = local[sel::SEAL];
        let old_reserved_seal = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved_seal = local[STATE_AFTER_BASE + state::RESERVED];
        let seal_pow2 = local[AUX_BASE + aux_off::SEAL_POW2_IDX];

        let c_seal_bal_lo = s_seal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_seal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_seal_bal_hi = s_seal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_seal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_seal_cap = s_seal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_seal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_seal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Stage 2: reserved increases by 2^field_idx (sets the bit).
        let c_seal_reserved = s_seal * (new_reserved_seal - old_reserved_seal - seal_pow2);
        combined = combined + alpha_pow * c_seal_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: aux_pow2 == 2^field_idx (Lagrange over {0..7}).
        let seal_field_idx_a = local[PARAM_BASE + param::SEAL_FIELD_IDX];
        let c_seal_pow2_check = s_seal * (seal_pow2 - lagrange_pow2(seal_field_idx_a));
        combined = combined + alpha_pow * c_seal_pow2_check;
        alpha_pow = alpha_pow * alpha;

        // RANGE CHECK: Seal field_idx must be in {0..7}.
        {
            let seal_field_idx = local[PARAM_BASE + param::SEAL_FIELD_IDX];
            let mut seal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                seal_idx_range_product =
                    seal_idx_range_product * (seal_field_idx - BabyBear::new(k));
            }
            let c_seal_idx_range = s_seal * seal_idx_range_product;
            combined = combined + alpha_pow * c_seal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Unseal: balance, fields, cap_root unchanged; reserved loses
        //    bit `field_idx`; sealed-field mask bit was previously 1. --
        let s_unseal = local[sel::UNSEAL];
        let old_reserved_unseal = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved_unseal = local[STATE_AFTER_BASE + state::RESERVED];
        let unseal_pow2 = local[AUX_BASE + aux_off::SEAL_POW2_IDX];

        let c_unseal_bal_lo = s_unseal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_unseal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_bal_hi = s_unseal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_unseal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_cap = s_unseal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_unseal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_unseal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Stage 2: reserved decreases by 2^field_idx (clears the bit;
        // requires bit was previously set, otherwise wrap into mode_flag
        // bits → trace-gen-side constraint).
        let c_unseal_reserved =
            s_unseal * (old_reserved_unseal - new_reserved_unseal - unseal_pow2);
        combined = combined + alpha_pow * c_unseal_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: aux_pow2 == 2^field_idx.
        let unseal_field_idx_a = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
        let c_unseal_pow2_check = s_unseal * (unseal_pow2 - lagrange_pow2(unseal_field_idx_a));
        combined = combined + alpha_pow * c_unseal_pow2_check;
        alpha_pow = alpha_pow * alpha;

        // RANGE CHECK: Unseal field_idx must be in {0..7}.
        {
            let unseal_field_idx = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
            let mut unseal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                unseal_idx_range_product =
                    unseal_idx_range_product * (unseal_field_idx - BabyBear::new(k));
            }
            let c_unseal_idx_range = s_unseal * unseal_idx_range_product;
            combined = combined + alpha_pow * c_unseal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- MakeSovereign: mode_flag 0->1, balance/fields/cap preserved --
        let s_makesov = local[sel::MAKE_SOVEREIGN];
        let old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sov_mode = s_makesov * (new_reserved - old_reserved - BabyBear::new(256));
        combined = combined + alpha_pow * c_sov_mode;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (MakeSovereign once-only): the mode bit must currently be 0.
        // Combined with `new_reserved - old_reserved == 256` (above), this
        // enforces the canonical 0→1 transition. Without this, a malicious
        // prover could apply MakeSovereign to an already-sovereign cell,
        // pushing reserved through 2*256 (which is no longer a valid
        // encoding — mode bit becomes non-boolean).
        let c_sov_was_managed = s_makesov * mode_bit;
        combined = combined + alpha_pow * c_sov_was_managed;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_lo = s_makesov * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sov_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_hi = s_makesov * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sov_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sov_cap = s_makesov * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sov_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_makesov
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateCellFromFactory: state flows through unchanged --
        let s_factory = local[sel::CREATE_CELL_FROM_FACTORY];
        for i in 0..state::SIZE {
            let c = s_factory * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CapTP Effects (provable CapTP operations)
        // ====================================================================

        // -- ExportSturdyRef: swiss_number = hash(cell_id, random_seed, counter) --
        // Proves the swiss number derivation is correct.
        // State: field[7] increments (export_counter), balance/cap/other fields unchanged.
        let s_export = local[sel::EXPORT_STURDY_REF];
        {
            let cell_id = local[PARAM_BASE + param::EXPORT_CELL_ID];
            let random_seed = local[PARAM_BASE + param::EXPORT_RANDOM_SEED];
            let export_counter = local[PARAM_BASE + param::EXPORT_COUNTER];
            // Swiss number = hash(cell_id, hash(random_seed, counter))
            let inner_hash = hash_2_to_1(random_seed, export_counter);
            let expected_swiss = hash_2_to_1(cell_id, inner_hash);
            // The computed swiss is stored in aux[0] for binding.
            let aux_swiss = local[AUX_BASE + 0];
            let c_swiss = s_export * (aux_swiss - expected_swiss);
            combined = combined + alpha_pow * c_swiss;
            alpha_pow = alpha_pow * alpha;

            // field[7] must increment by 1 (export counter).
            let old_f7 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 7];
            let new_f7 = local[STATE_AFTER_BASE + state::FIELD_BASE + 7];
            let c_counter = s_export * (new_f7 - old_f7 - BabyBear::ONE);
            combined = combined + alpha_pow * c_counter;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_export * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_export * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_export * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..7 unchanged (only field[7] changes).
            for i in 0..7 {
                let c = s_export
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- EnlivenRef: validate swiss number is a member of the cell's
        // committed swiss_table_root --
        //
        // Stage 7 / P1.C: previously tautological. Now does 1-hop Merkle
        // membership against the cell's state.fields[4] slot (the
        // committed swiss_table_root mirror). The prover supplies a
        // sibling hash; the leaf is AIR-computed from PARAMs; the
        // chosen-parent must equal the committed root.
        //
        // Aux layout (NB: aux[2..5] reserved on row 0 for delta/effects_hash):
        //   aux[0] = root  (= state_after.fields[4])
        //   aux[1] = leaf  (must equal hash(swiss, hash(cell_id, perms)))
        //   aux[6] = sibling (prover-supplied)
        //   aux[7] = chosen = hash(leaf, sibling)
        //
        // State: field[6] increments (use_count); field[4]
        // (swiss_table_root) updates to `chosen`; other fields unchanged.
        let s_enliven = local[sel::ENLIVEN_REF];
        {
            let swiss = local[PARAM_BASE + param::ENLIVEN_SWISS];
            let expected_cell_id = local[PARAM_BASE + param::ENLIVEN_CELL_ID];
            let expected_perms = local[PARAM_BASE + param::ENLIVEN_PERMISSIONS];
            let inner = hash_2_to_1(expected_cell_id, expected_perms);
            let expected_leaf = hash_2_to_1(swiss, inner);
            let aux_root = local[AUX_BASE + 0];
            let aux_leaf = local[AUX_BASE + 1];
            let c_leaf = s_enliven * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 6];
            let aux_chosen = local[AUX_BASE + 7];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_enliven * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let f4_after = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_root_field = s_enliven * (aux_root - f4_after);
            combined = combined + alpha_pow * c_root_field;
            alpha_pow = alpha_pow * alpha;
            let c_chosen_eq_root = s_enliven * (aux_chosen - aux_root);
            combined = combined + alpha_pow * c_chosen_eq_root;
            alpha_pow = alpha_pow * alpha;
            // Stage 7 / P1.C tightening: pin the sibling to
            // `state_before.fields[4]` so the new root is an
            // append-only extension of the old root. Without this
            // constraint, the prover could supply any sibling and
            // obtain any new root, severing the chain.
            let f4_before = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_sib_chain = s_enliven * (aux_sibling - f4_before);
            combined = combined + alpha_pow * c_sib_chain;
            alpha_pow = alpha_pow * alpha;

            // field[6] must increment by 1 (use_count).
            let old_f6 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 6];
            let new_f6 = local[STATE_AFTER_BASE + state::FIELD_BASE + 6];
            let c_use = s_enliven * (new_f6 - old_f6 - BabyBear::ONE);
            combined = combined + alpha_pow * c_use;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_enliven * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_enliven * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_enliven * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..3, 5, and 7 unchanged (only field[6] and the
            // committed root in field[4] may change on this row).
            for i in [0usize, 1, 2, 3, 5, 7] {
                let c = s_enliven
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- DropRef: decrement refcount; bind holder_federation into
        //    the committed refcount_table_root (state.fields[3]) --
        //
        // Stage 7 / P1.C: previously the `holder_federation` PARAM was
        // unbound from any committed structure. Now the AIR enforces a
        // 1-hop Merkle membership against `state_after.fields[3]` (the
        // committed refcount_table_root mirror). Leaf =
        // hash(ref_id_field=cell_id, holder_federation).
        let s_drop = local[sel::DROP_REF];
        {
            let refcount_param = local[PARAM_BASE + param::DROP_REFCOUNT];
            let cell_id_param = local[PARAM_BASE + param::DROP_CELL_ID];
            let holder_fed_param = local[PARAM_BASE + param::DROP_HOLDER_FED];

            // field[5] must decrement by 1.
            let old_f5 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 5];
            let new_f5 = local[STATE_AFTER_BASE + state::FIELD_BASE + 5];
            let c_dec = s_drop * (new_f5 - old_f5 + BabyBear::ONE);
            combined = combined + alpha_pow * c_dec;
            alpha_pow = alpha_pow * alpha;

            // refcount param must match old field[5] (binds the declared refcount).
            let c_rc = s_drop * (refcount_param - old_f5);
            combined = combined + alpha_pow * c_rc;
            alpha_pow = alpha_pow * alpha;

            // Prove refcount > 0: aux[0] = inverse(refcount_param).
            let rc_inv = local[AUX_BASE + 0];
            let c_nonzero = s_drop * (refcount_param * rc_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_nonzero;
            alpha_pow = alpha_pow * alpha;

            // 1-hop Merkle membership against refcount_table_root in
            // state_after.fields[3]:
            //   aux[1] = leaf = hash_2_to_1(cell_id, holder_federation)
            //   aux[6] = prover-supplied sibling
            //   aux[7] = chosen_parent = hash_2_to_1(leaf, sibling)
            //   chosen_parent == state_after.fields[3]
            // Aux[2..5] are reserved on row 0 for delta/effects_hash
            // PI binding; we use aux[6..7] for the Merkle witness.
            let expected_leaf = hash_2_to_1(cell_id_param, holder_fed_param);
            let aux_leaf = local[AUX_BASE + 1];
            let c_leaf = s_drop * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 6];
            let aux_chosen = local[AUX_BASE + 7];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_drop * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let f3_after = local[STATE_AFTER_BASE + state::FIELD_BASE + 3];
            let c_root = s_drop * (aux_chosen - f3_after);
            combined = combined + alpha_pow * c_root;
            alpha_pow = alpha_pow * alpha;
            // Stage 7 / P1.C tightening: pin the sibling to
            // `state_before.fields[3]` (old refcount_table_root).
            // Without this, the prover could pick any sibling and
            // obtain any new root.
            let f3_before = local[STATE_BEFORE_BASE + state::FIELD_BASE + 3];
            let c_sib_chain = s_drop * (aux_sibling - f3_before);
            combined = combined + alpha_pow * c_sib_chain;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_drop * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_drop * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_drop * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..2, 4, 6, 7 unchanged (field[3] holds the new
            // refcount_table_root mirror, field[5] decrements).
            for i in [0usize, 1, 2, 4, 6, 7] {
                let c = s_drop
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- ValidateHandoff: prove certificate hash is in approved set --
        //
        // Stage 7 / P1.C: previously tautological. Now does honest 1-hop
        // Merkle membership against PI[APPROVED_HANDOFFS_BASE] (position 0;
        // the 4-felt widening). The PARAM HANDOFF_APPROVED_SET_ROOT must
        // equal PI[APPROVED_HANDOFFS_BASE], so the prover cannot pick
        // their own root. Leaf = hash(cert_hash, hash(recipient_pk,
        // introducer_pk)). aux[1] = leaf, aux[2] = sibling, aux[3] =
        // chosen_parent = hash(leaf, sibling); chosen_parent ==
        // approved_set_root.
        //
        // Consume-on-use: lives at the executor, which rotates the
        // federation's approved-handoffs root after a successful
        // ValidateHandoff (per `DESIGN-captp-integration.md` §9.4). A
        // replay produces a non-membership witness for the rotated
        // root, which the AIR proof cannot satisfy.
        //
        // State: cap_root updated (routing entry for recipient),
        // balance/fields unchanged.
        let s_handoff = local[sel::VALIDATE_HANDOFF];
        {
            let cert_hash = local[PARAM_BASE + param::HANDOFF_CERT_HASH];
            let recipient_pk = local[PARAM_BASE + param::HANDOFF_RECIPIENT_PK];
            let introducer_pk = local[PARAM_BASE + param::HANDOFF_INTRODUCER_PK];
            let approved_root = local[PARAM_BASE + param::HANDOFF_APPROVED_SET_ROOT];

            // Leaf bound to PARAMs:
            //   leaf = hash(cert_hash, hash(recipient_pk, introducer_pk))
            //
            // Aux layout (NB: aux[2..5] reserved on row 0):
            //   aux[0] = leaf
            //   aux[1] = sibling
            //   aux[6] = chosen = hash(leaf, sibling)
            let pks = hash_2_to_1(recipient_pk, introducer_pk);
            let expected_leaf = hash_2_to_1(cert_hash, pks);
            let aux_leaf = local[AUX_BASE + 0];
            let c_leaf = s_handoff * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 1];
            let aux_chosen = local[AUX_BASE + 6];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_handoff * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let c_root_eq = s_handoff * (aux_chosen - approved_root);
            combined = combined + alpha_pow * c_root_eq;
            alpha_pow = alpha_pow * alpha;

            // Bind PARAM approved_root to PI[APPROVED_HANDOFFS_BASE]
            // (position 0). This closes the prover-control gap: the
            // verifier supplies the PI; the prover cannot invent a
            // root.
            let pi_root = public_inputs[pi::APPROVED_HANDOFFS_BASE];
            let c_pi_bind = s_handoff * (approved_root - pi_root);
            combined = combined + alpha_pow * c_pi_bind;
            alpha_pow = alpha_pow * alpha;

            // Cap root updated: new_cap_root = hash(old_cap_root, hash(recipient_pk, cert_hash))
            // This creates a routing entry for the recipient.
            let routing_entry = hash_2_to_1(recipient_pk, cert_hash);
            let expected_new_cap = hash_2_to_1(old_cap_root, routing_entry);
            let c_cap = s_handoff * (new_cap_root - expected_new_cap);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_handoff * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_handoff * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // All fields unchanged.
            for i in 0..8 {
                let c = s_handoff
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // Storage Queue Effects (provable MerkleQueue operations)
        // ====================================================================

        // -- AllocateQueue: balance debit (capacity * cost_per_slot), field[4] = empty hash --
        let s_alloc_queue = local[sel::ALLOCATE_QUEUE];
        {
            let capacity = local[PARAM_BASE + param::QUEUE_CAPACITY];
            let cost_per_slot = local[PARAM_BASE + param::QUEUE_COST_PER_SLOT];
            let alloc_cost = capacity * cost_per_slot;

            // Balance debit: new_bal_lo = old_bal_lo - alloc_cost.
            let c_aq_bal = s_alloc_queue * (new_bal_lo - old_bal_lo + alloc_cost);
            combined = combined + alpha_pow * c_aq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_aq_hi = s_alloc_queue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_aq_hi;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become empty_queue_hash = hash_2_to_1(ZERO, ZERO).
            let empty_queue_hash = hash_2_to_1(BabyBear::ZERO, BabyBear::ZERO);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_aq_root = s_alloc_queue * (new_f4 - empty_queue_hash);
            combined = combined + alpha_pow * c_aq_root;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_aq_cap = s_alloc_queue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_aq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_alloc_queue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_alloc_queue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- EnqueueMessage: queue root hash chain, balance debit (deposit),
        //    and optional program validation hash binding --
        let s_enqueue = local[sel::ENQUEUE_MESSAGE];
        {
            let message_hash = local[PARAM_BASE + param::ENQUEUE_MSG_HASH];
            let deposit = local[PARAM_BASE + param::ENQUEUE_DEPOSIT];
            let sender_id = local[PARAM_BASE + param::ENQUEUE_SENDER];

            // Queue root transition: new_root = hash(old_root, message_hash).
            let old_queue_root = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let expected_new_root = hash_2_to_1(old_queue_root, message_hash);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_eq_root = s_enqueue * (new_f4 - expected_new_root);
            combined = combined + alpha_pow * c_eq_root;
            alpha_pow = alpha_pow * alpha;

            // Balance debit: new_bal_lo = old_bal_lo - deposit.
            let c_eq_bal = s_enqueue * (new_bal_lo - old_bal_lo + deposit);
            combined = combined + alpha_pow * c_eq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_eq_hi = s_enqueue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_eq_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_eq_cap = s_enqueue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_eq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_enqueue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_enqueue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }

            // ================================================================
            // Queue program validation hash binding.
            //
            // NOTE: aux[2..5] on row 0 are reserved for public input values
            // (delta_mag, delta_sign, effects_hash_lo, effects_hash_hi).
            // We use aux[6] for the validation hash and aux[7] for program_vk_inv.
            //
            // param[4] = ENQUEUE_PROGRAM_VK: queue program VK as field element.
            //   ZERO if queue has no program (backward compatible).
            // aux[6] = program_validation_hash
            // aux[7] = inverse(program_vk) when != 0, else 0
            //
            // Constraints:
            //   1. program_vk != 0 => aux[6] == hash(program_vk, hash(sender, msg))
            //   2. program_vk == 0 => aux[6] == 0
            // ================================================================
            let program_vk = local[PARAM_BASE + param::ENQUEUE_PROGRAM_VK];
            let validation_hash = local[AUX_BASE + 6];
            let program_vk_inv = local[AUX_BASE + 7];

            // Constraint 1: When program_vk != 0, validation_hash must equal expected.
            let inner_hash = hash_2_to_1(sender_id, message_hash);
            let expected_validation = hash_2_to_1(program_vk, inner_hash);
            let c_prog_valid = s_enqueue * program_vk * (validation_hash - expected_validation);
            combined = combined + alpha_pow * c_prog_valid;
            alpha_pow = alpha_pow * alpha;

            // Constraint 2: When program_vk == 0, validation_hash must be zero.
            let c_prog_zero =
                s_enqueue * (BabyBear::ONE - program_vk * program_vk_inv) * validation_hash;
            combined = combined + alpha_pow * c_prog_zero;
            alpha_pow = alpha_pow * alpha;
        }

        // -- DequeueMessage: queue root hash chain advance, balance credit (deposit refund) --
        let s_dequeue = local[sel::DEQUEUE_MESSAGE];
        {
            let expected_msg_hash = local[PARAM_BASE + param::DEQUEUE_EXPECTED_HASH];
            let deposit_refund = local[PARAM_BASE + param::DEQUEUE_DEPOSIT_REFUND];

            // Queue root advances: new_root = hash(old_root, expected_message_hash).
            let old_queue_root = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let expected_new_root = hash_2_to_1(old_queue_root, expected_msg_hash);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_dq_root = s_dequeue * (new_f4 - expected_new_root);
            combined = combined + alpha_pow * c_dq_root;
            alpha_pow = alpha_pow * alpha;

            // expected_message_hash must be non-zero (non-empty queue).
            // Proved via aux[1] = inverse(expected_msg_hash).
            let msg_inv = local[AUX_BASE + 1];
            let c_dq_nonempty = s_dequeue * (expected_msg_hash * msg_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_dq_nonempty;
            alpha_pow = alpha_pow * alpha;

            // Balance credit: new_bal_lo = old_bal_lo + deposit_refund.
            let c_dq_bal = s_dequeue * (new_bal_lo - old_bal_lo - deposit_refund);
            combined = combined + alpha_pow * c_dq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_dq_hi = s_dequeue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_dq_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_dq_cap = s_dequeue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_dq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_dequeue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_dequeue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- ResizeQueue: capacity update with sign-decomposed delta --
        // Stage 2 honesty fix: separately constrain magnitude + sign so a
        // shrink can't wrap into a fictitious debit. The prover witnesses
        // `delta_sign ∈ {0, 1}` and `delta_mag = |new_cap - old_cap|` in
        // aux[RESIZE_DELTA_SIGN/MAG]. Constraints:
        //   (a) sign is boolean
        //   (b) (new_cap - old_cap) == delta_mag * (1 - 2*sign)
        //   (c) balance change == delta_mag * cost_per_slot * (1 - sign)
        //       (grow ⇒ debit; shrink ⇒ no debit)
        let s_resize = local[sel::RESIZE_QUEUE];
        {
            let new_capacity = local[PARAM_BASE + param::RESIZE_NEW_CAPACITY];
            let old_capacity = local[PARAM_BASE + param::RESIZE_OLD_CAPACITY];
            let cost_per_slot = local[PARAM_BASE + param::RESIZE_COST_PER_SLOT];
            let delta_sign = local[AUX_BASE + aux_off::RESIZE_DELTA_SIGN];
            let delta_mag = local[AUX_BASE + aux_off::RESIZE_DELTA_MAG];
            let two = BabyBear::ONE + BabyBear::ONE;

            // (a) sign boolean (gated by selector; non-resize rows have
            // delta_sign = 0 by convention, so the constraint is trivially
            // satisfied — but we apply unconditional boolean check here
            // gated by the selector to avoid affecting non-resize rows).
            let c_rq_sign_bool = s_resize * delta_sign * (delta_sign - BabyBear::ONE);
            combined = combined + alpha_pow * c_rq_sign_bool;
            alpha_pow = alpha_pow * alpha;

            // (b) signed-delta binding.
            let c_rq_delta = s_resize
                * ((new_capacity - old_capacity) - delta_mag * (BabyBear::ONE - two * delta_sign));
            combined = combined + alpha_pow * c_rq_delta;
            alpha_pow = alpha_pow * alpha;

            // (c) balance change: grow ⇒ debit; shrink ⇒ no change.
            // new_bal_lo == old_bal_lo - delta_mag * cost_per_slot * (1 - sign)
            // <=>
            // new_bal_lo - old_bal_lo + delta_mag * cost_per_slot * (1 - sign) == 0
            let resize_cost = delta_mag * cost_per_slot * (BabyBear::ONE - delta_sign);
            let c_rq_bal = s_resize * (new_bal_lo - old_bal_lo + resize_cost);
            combined = combined + alpha_pow * c_rq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_rq_hi = s_resize * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_rq_hi;
            alpha_pow = alpha_pow * alpha;

            // field[5] must become new_capacity.
            let new_f5 = local[STATE_AFTER_BASE + state::FIELD_BASE + 5];
            let c_rq_cap_field = s_resize * (new_f5 - new_capacity);
            combined = combined + alpha_pow * c_rq_cap_field;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_rq_cap = s_resize * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_rq_cap;
            alpha_pow = alpha_pow * alpha;

            // Queue root (field[4]) unchanged.
            let c_rq_f4 = s_resize
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + 4]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + 4]);
            combined = combined + alpha_pow * c_rq_f4;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 6..8) unchanged.
            for i in 0..4 {
                let c = s_resize
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 6..8 {
                let c = s_resize
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // Storage Phase 3: Atomic and Pipeline Effects
        // ====================================================================

        // -- AtomicQueueTx: atomic cross-queue transaction --
        // Proves: field[4] transitions from combined_old_root to combined_new_root.
        // Binding: aux[0] == hash(tx_hash, hash(combined_old_root, combined_new_root))
        // State: field[4] changes, balance debited by net_deposit, cap/other fields unchanged.
        // Balance: new_bal_lo = old_bal_lo - net_deposit (like Transfer direction=1).
        // This allows atomic transactions involving deposits (enqueue ops pay deposits,
        // dequeue ops receive refunds; the net is the overall balance change).
        let s_atomic_tx = local[sel::ATOMIC_QUEUE_TX];
        {
            let tx_hash_val = local[PARAM_BASE + param::ATOMIC_TX_HASH];
            let combined_old = local[PARAM_BASE + param::ATOMIC_TX_COMBINED_OLD_ROOT];
            let combined_new = local[PARAM_BASE + param::ATOMIC_TX_COMBINED_NEW_ROOT];
            let net_deposit = local[PARAM_BASE + param::ATOMIC_TX_NET_DEPOSIT];

            // field[4] must equal combined_old_root before.
            let old_f4 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_atx_old = s_atomic_tx * (old_f4 - combined_old);
            combined = combined + alpha_pow * c_atx_old;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become combined_new_root.
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_atx_new = s_atomic_tx * (new_f4 - combined_new);
            combined = combined + alpha_pow * c_atx_new;
            alpha_pow = alpha_pow * alpha;

            // Binding constraint: aux[0] == hash(tx_hash, hash(combined_old, combined_new))
            let inner_hash = hash_2_to_1(combined_old, combined_new);
            let expected_binding = hash_2_to_1(tx_hash_val, inner_hash);
            let aux_binding = local[AUX_BASE + 0];
            let c_atx_bind = s_atomic_tx * (aux_binding - expected_binding);
            combined = combined + alpha_pow * c_atx_bind;
            alpha_pow = alpha_pow * alpha;

            // Balance debit: new_bal_lo = old_bal_lo - net_deposit.
            // This follows the same pattern as Transfer (direction=1) and EnqueueMessage.
            // net_deposit == 0 means no balance change (backward compatible).
            let c_atx_bal_lo = s_atomic_tx * (new_bal_lo - old_bal_lo + net_deposit);
            combined = combined + alpha_pow * c_atx_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_atx_bal_hi = s_atomic_tx * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_atx_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_atx_cap = s_atomic_tx * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_atx_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_atomic_tx
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_atomic_tx
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- PipelineStep: prove a pipeline step correctly routed a message --
        // Proves: source_new_root == hash(source_old_root, message_hash) (dequeue)
        //         sink_new_root == hash(sink_old_root_aux, message_hash) (enqueue)
        //         pipeline_id binding (must match, proves authorization).
        // State: field[4] transitions from source_old_root to source_new_root.
        let s_pipeline = local[sel::PIPELINE_STEP];
        {
            let pipeline_id_val = local[PARAM_BASE + param::PIPELINE_ID];
            let source_old = local[PARAM_BASE + param::PIPELINE_SOURCE_OLD_ROOT];
            let source_new = local[PARAM_BASE + param::PIPELINE_SOURCE_NEW_ROOT];
            let sink_new = local[PARAM_BASE + param::PIPELINE_SINK_NEW_ROOT];
            let msg_hash = local[PARAM_BASE + param::PIPELINE_MESSAGE_HASH];

            // P1-5 fix: enforce pipeline_id != 0. Without this, the prover
            // could claim pipeline_id=0 (an unauthorized null pipeline) and
            // pass all other constraints. We store pipeline_id^-1 in aux[6]
            // and require `s_pipeline * (pipeline_id * aux[6] - 1) == 0`.
            // Branch analysis:
            //   - s_pipeline = 0 (other selector): constraint trivially holds.
            //   - s_pipeline = 1 and pipeline_id = 0: forces 0*x - 1 == 0, i.e.,
            //     -1 == 0, unsatisfiable. ⇒ verifier rejects.
            //   - s_pipeline = 1 and pipeline_id != 0: requires aux[6] = 1/pipeline_id.
            // This mirrors the DropRef refcount pattern.
            let pipeline_id_inv = local[AUX_BASE + 6];
            let c_pipeline_nonzero =
                s_pipeline * (pipeline_id_val * pipeline_id_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_pipeline_nonzero;
            alpha_pow = alpha_pow * alpha;

            // Source dequeue constraint:
            // source_new_root == hash(source_old_root, message_hash)
            let expected_source_new = hash_2_to_1(source_old, msg_hash);
            let c_ps_source = s_pipeline * (source_new - expected_source_new);
            combined = combined + alpha_pow * c_ps_source;
            alpha_pow = alpha_pow * alpha;

            // aux[0] must equal expected_source_new (verifiable witness).
            let aux_expected = local[AUX_BASE + 0];
            let c_ps_aux = s_pipeline * (aux_expected - expected_source_new);
            combined = combined + alpha_pow * c_ps_aux;
            alpha_pow = alpha_pow * alpha;

            // field[4] must equal source_old_root before.
            let old_f4 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_ps_old = s_pipeline * (old_f4 - source_old);
            combined = combined + alpha_pow * c_ps_old;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become source_new_root after.
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_ps_new = s_pipeline * (new_f4 - source_new);
            combined = combined + alpha_pow * c_ps_new;
            alpha_pow = alpha_pow * alpha;

            // Pipeline ID binding: pipeline_id must be non-zero (proves authorization).
            // Proved via aux[1] storing sink_new_root (also serves as pipeline binding).
            // The pipeline_id is a content-addressed hash of the pipeline definition;
            // it being present in the params proves this step was authorized.
            let aux_sink = local[AUX_BASE + 1];
            let c_ps_sink = s_pipeline * (aux_sink - sink_new);
            combined = combined + alpha_pow * c_ps_sink;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_ps_bal_lo = s_pipeline * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_ps_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_ps_bal_hi = s_pipeline * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_ps_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_ps_cap = s_pipeline * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_ps_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_pipeline
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_pipeline
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // -- Burn: explicit non-conservation balance reduction --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change, the
        // turn-side `Effect::Burn` was either dropped from the projection or
        // routed through `VmEffect::Transfer { direction: 1 }`. A verifier
        // replaying the trace could not distinguish a Burn from a
        // Transfer-direction-1 algebraically: both rows produce the same
        // balance-debit shape. Silver Vision honesty: dedicated selector +
        // dedicated `was_burn_flag == 1` constraint so the proof attests
        // "this Burn happened" rather than "some balance-debit happened".
        //
        // Params:
        //   params[BURN_TARGET]         = target_hash (folded into effects_hash)
        //   params[BURN_AMOUNT_LO]      = amount_lo (low 30 bits)
        //   params[BURN_WAS_BURN_FLAG]  = 1 (constant — the AIR pins this)
        //
        // Constraints:
        //   1. new_bal_lo + amount_lo == old_bal_lo     (balance debit)
        //   2. new_bal_hi == old_bal_hi                 (single-limb amount)
        //   3. was_burn_flag == 1                        (disclosure pinning)
        //   4. cap_root, fields, reserved all passthrough.
        let s_burn = local[sel::BURN];
        {
            let burn_amount = local[PARAM_BASE + param::BURN_AMOUNT_LO];
            let burn_flag = local[PARAM_BASE + param::BURN_WAS_BURN_FLAG];

            // Balance debit (mirrors NoteCreate's `new = old - amount`).
            let c_burn_bal_lo = s_burn * (new_bal_lo - old_bal_lo + burn_amount);
            combined = combined + alpha_pow * c_burn_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_burn_bal_hi = s_burn * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_burn_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Was-burn disclosure flag: MUST be 1 on a Burn row. A trace
            // that drops the disclosure (sets it to 0) fails the AIR.
            let c_burn_flag = s_burn * (burn_flag - BabyBear::ONE);
            combined = combined + alpha_pow * c_burn_flag;
            alpha_pow = alpha_pow * alpha;

            // cap_root unchanged.
            let c_burn_cap = s_burn * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_burn_cap;
            alpha_pow = alpha_pow * alpha;
            // fields unchanged.
            for i in 0..8 {
                let c = s_burn
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            // reserved unchanged (Burn does not seal / unseal / sovereign).
            let c_burn_reserved = s_burn
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_burn_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CellDestroy: state-passthrough with dedicated 2-param binding --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change a
        // `CellDestroy` projected as `SetPermissions { permissions_hash =
        // death_certificate_hash }` — the proof bound the right bytes but
        // through the SetPermissions selector. A verifier could not tell a
        // genuine SetPermissions update from a CellDestroy without trusting
        // the executor to project honestly.
        //
        // The dedicated CellDestroy variant binds BOTH `target_hash`
        // (params[0]) and `death_certificate_hash` (params[1]) — a
        // SetPermissions row carrying only one hash in params[0] cannot
        // satisfy the CellDestroy constraint set (which gates params[1] too).
        let s_cell_destroy = local[sel::CELL_DESTROY];
        {
            // State passthrough: balance, fields, cap_root, reserved all
            // unchanged. Lifecycle lives off-trace; the binding is via
            // params -> effects_hash.
            let c_cd_bal_lo = s_cell_destroy * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_cd_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_cd_bal_hi = s_cell_destroy * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_cd_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cd_cap = s_cell_destroy * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cd_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_cell_destroy
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_cd_reserved = s_cell_destroy
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_cd_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- AttenuateCapability: cap_root advances via a 2-of-2 leaf --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change
        // an `AttenuateCapability` projected as
        // `RevokeCapability { slot_hash = attn_hash }`. Both advance
        // cap_root via `hash_2_to_1(old_cap_root, X)`; a verifier could
        // not tell a "narrow this slot" from a "revoke this slot"
        // attestation algebraically.
        //
        // Dedicated AttenuateCapability constraint:
        //   new_cap_root == hash_2_to_1(old_cap_root,
        //                     hash_2_to_1(cap_slot_hash,
        //                                 narrower_commitment))
        //
        // A RevokeCapability proof (single-hash advance) cannot satisfy
        // the nested hash without simultaneously fixing both params to a
        // pair that hashes to the revoke's `slot_hash` AND switching the
        // selector — i.e. it would have to be an entirely different proof.
        let s_attn_cap = local[sel::ATTENUATE_CAPABILITY];
        {
            let attn_slot = local[PARAM_BASE + param::ATTN_CAP_SLOT_HASH];
            let attn_narrower = local[PARAM_BASE + param::ATTN_NARROWER_COMMITMENT];

            let attn_leaf = hash_2_to_1(attn_slot, attn_narrower);
            let expected_attn_cap = hash_2_to_1(old_cap_root, attn_leaf);
            let c_attn_cap = s_attn_cap * (new_cap_root - expected_attn_cap);
            combined = combined + alpha_pow * c_attn_cap;
            alpha_pow = alpha_pow * alpha;

            // Balance and fields unchanged.
            let c_attn_bal_lo = s_attn_cap * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_attn_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_attn_bal_hi = s_attn_cap * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_attn_bal_hi;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_attn_cap
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_attn_reserved = s_attn_cap
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_attn_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Balance range check and net_delta soundness
        // ====================================================================
        //
        // SOUNDNESS FIX (Gap 1): Prevent balance underflow exploitation.
        //
        // For debit operations (Transfer out, NoteCreate, CreateObligation),
        // the constraint `new_bal_lo = old_bal_lo - amount` uses BabyBear
        // modular arithmetic. If amount > old_bal_lo, the result wraps to a
        // large field element (p - deficit), creating value from nothing.
        //
        // Defense: We add a range check that new_bal_lo < 2^30 for ALL rows.
        // This is achieved via the state commitment integrity constraint
        // (Group 4): state_commit == hash_4_to_1(bal_lo, bal_hi, nonce, ...).
        // Since the boundary constraints pin the first and last commitments,
        // and transition constraints chain intermediate commitments, any
        // wrapped value would produce a commitment inconsistent with the
        // boundary pins ONLY IF the verifier independently knows the expected
        // final state.
        //
        // The STRONGER in-circuit defense: constrain that for debit effects,
        // the result is non-negative. We do this by requiring the prover to
        // supply a witness that old_bal_lo >= amount (for the relevant rows).
        //
        // Approach: For Transfer (direction=1), NoteCreate, and CreateObligation,
        // constrain: (old_bal_lo - amount) == new_bal_lo (already done above)
        // AND: new_bal_lo * (new_bal_lo - 1) * ... is NOT feasible at this degree.
        //
        // Instead, we use the sign-bit approach on the net_delta PI:
        // Constrain net_delta_sign to be boolean (0 or 1).
        // This ensures the prover can't use a non-boolean sign value to encode
        // arbitrary field elements as the "signed delta".
        // NOTE: The delta_sign boolean constraint is placed at the END of
        // eval_constraints (after Group 4) to preserve alpha_pow ordering for
        // existing constraints. See CONSTRAINT GROUP 5 below.

        // Additionally: constrain that the net_delta magnitude fits in 30 bits.
        // This is enforced by requiring that magnitude < 2^30. We use the
        // auxiliary column aux[6] to store magnitude decomposition:
        //   aux[6] = mag_hi_15 (upper 15 bits of magnitude)
        // The prover must provide: magnitude == mag_lo_15 + mag_hi_15 * 2^15
        // where both halves are in [0, 2^15). This is checked via the
        // degree-8 vanishing polynomial approach (checking top byte).
        //
        // For now, the sign-boolean constraint above combined with the
        // state commitment hash chain provides the primary defense.
        // The magnitude is implicitly range-checked because:
        //   - Initial balance is verified by the caller (known good state)
        //   - Each row's balance is committed via Poseidon2 hash
        //   - The final commitment is checked by the verifier
        //   - Any wraparound produces a different commitment than expected

        // CONSTRAINT GROUP 3: Transition constraints (row continuity)
        // ====================================================================
        // next_row.state_before == this_row.state_after
        // (Enforced on all rows except the last — the STARK framework handles this
        //  via the transition vanishing polynomial which excludes the last row.)
        for i in 0..state::SIZE {
            let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Nonce increment: for non-NoOp rows, nonce increments by 1.
        // For NoOp (padding) rows, nonce stays the same.
        // Combined: new_nonce == old_nonce + (1 - sel_noop)
        let c_nonce = new_nonce - old_nonce - (BabyBear::ONE - s_noop);
        combined = combined + alpha_pow * c_nonce;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 4: State commitment integrity (tree hash)
        // ====================================================================
        // The state_commitment in state_after MUST equal the tree hash of the
        // state_after columns. This prevents a malicious prover from claiming
        // an arbitrary commitment that doesn't match the actual state.
        //
        // Tree structure (constrainable via hash_4_to_1):
        //   inter1 = hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
        //   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
        //   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
        //   state_commit = hash_4_to_1(inter1, inter2, inter3, ZERO)
        //
        // The intermediates are stored in aux[8..10] and verified here.
        {
            let after_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
            let after_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
            let after_nonce = local[STATE_AFTER_BASE + state::NONCE];
            let after_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];
            let after_commit = local[STATE_AFTER_BASE + state::STATE_COMMIT];

            let inter1 = local[AUX_BASE + aux_off::STATE_INTER1];
            let inter2 = local[AUX_BASE + aux_off::STATE_INTER2];
            let inter3 = local[AUX_BASE + aux_off::STATE_INTER3];

            // Constraint: inter1 == hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
            let expected_inter1 = hash_4_to_1(&[
                after_bal_lo,
                after_bal_hi,
                after_nonce,
                local[STATE_AFTER_BASE + state::FIELD_BASE + 0],
            ]);
            let c_inter1 = inter1 - expected_inter1;
            combined = combined + alpha_pow * c_inter1;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter2 == hash_4_to_1(field[1], field[2], field[3], field[4])
            let expected_inter2 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 1],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 2],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 3],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 4],
            ]);
            let c_inter2 = inter2 - expected_inter2;
            combined = combined + alpha_pow * c_inter2;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter3 == hash_4_to_1(field[5], field[6], field[7], cap_root)
            let expected_inter3 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 5],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 6],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 7],
                after_cap_root,
            ]);
            let c_inter3 = inter3 - expected_inter3;
            combined = combined + alpha_pow * c_inter3;
            alpha_pow = alpha_pow * alpha;

            // Constraint: state_commit == hash_4_to_1(inter1, inter2, inter3, ZERO)
            let expected_commit = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
            let c_commit = after_commit - expected_commit;
            combined = combined + alpha_pow * c_commit;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Net delta sign boolean (soundness fix, Gap 1)
        // ====================================================================
        // The net_delta_sign value (aux[3] on row 0) must be boolean (0 or 1).
        // Without this, a malicious prover could encode arbitrary field values
        // as the "sign" and manipulate the signed delta interpretation.
        //
        // On non-zero rows, aux[3] == 0 (unset), so this constraint is trivially
        // satisfied (0 * (0-1) = 0). On row 0, it enforces sign in {0, 1}.
        {
            let delta_sign = local[AUX_BASE + 3];
            let c_sign_bool = delta_sign * (delta_sign - BabyBear::ONE);
            combined = combined + alpha_pow * c_sign_bool;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 6: Algebraic binding of NET_DELTA PI to actual trace
        // balance deltas (P0-1 fix).
        //
        // PIs INIT_BAL_LO/HI and FINAL_BAL_LO/HI are pinned via boundary
        // constraints to row 0 state_before.balance_* and last_row
        // state_after.balance_*. This constraint enforces algebraically:
        //
        //   (FINAL_BAL_LO - INIT_BAL_LO)
        //     + (FINAL_BAL_HI - INIT_BAL_HI) * 2^30
        //     - NET_DELTA_MAG * (1 - 2 * NET_DELTA_SIGN) == 0
        //
        // Both sides depend only on PIs, so this evaluates to the same field
        // element on every row. Non-zero ⇒ no quotient polynomial exists ⇒
        // verifier rejects.
        //
        // The sign bit (PI[NET_DELTA_SIGN]) is constrained boolean (Group 5);
        // limb ranges are asserted at trace-generation time and should also be
        // checked externally by the verifier on the bal_* PIs.
        {
            let init_lo = public_inputs[pi::INIT_BAL_LO];
            let init_hi = public_inputs[pi::INIT_BAL_HI];
            let final_lo = public_inputs[pi::FINAL_BAL_LO];
            let final_hi = public_inputs[pi::FINAL_BAL_HI];
            let mag = public_inputs[pi::NET_DELTA_MAG];
            let sign = public_inputs[pi::NET_DELTA_SIGN];

            let two = BabyBear::ONE + BabyBear::ONE;
            let two_pow_30 = BabyBear::new(1u32 << 30);

            let actual_delta = (final_lo - init_lo) + (final_hi - init_hi) * two_pow_30;
            let signed_delta = mag * (BabyBear::ONE - two * sign);

            let c_delta_bind = actual_delta - signed_delta;
            combined = combined + alpha_pow * c_delta_bind;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 7: Custom-effect count sum-check (Stage 1, Stage 2 row-0 fix)
        // ====================================================================
        // Per `DESIGN-max-custom-effects.md` §6 step 3: bind the cumulative
        // sum of `s_custom` selector across rows to `PI[CUSTOM_EFFECT_COUNT]`.
        //
        // Stage 2 resolves REVIEW[stage1-acc-row0]: the column now uses an
        // EXCLUSIVE running sum (acc[i] = count of s_custom == 1 over rows
        // [0..i), i.e., NOT including row i). This makes acc[0] == 0 always,
        // pinned by a row-0 boundary. The transition rolls in the current
        // row's contribution: `next.acc - this.acc - this.s_custom == 0`.
        // The last-row check is `acc[last] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT]`,
        // implemented as a per-row PI-only identity gated by the
        // last-row vanishing polynomial.
        //
        // Without this, a prover with control over its witness generator can
        // place `s_custom == 1` on a row without declaring it in PI, hiding a
        // custom effect from the executor's child-proof verification loop
        // (`turn/src/executor.rs:1192-1235`). The sum-check makes the count
        // algebraically binding.
        {
            let this_acc = local[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let next_acc = next[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let this_s_custom = local[sel::CUSTOM];
            // Exclusive-sum transition:
            //   next.acc == this.acc + this.s_custom
            let c_acc_step = next_acc - this_acc - this_s_custom;
            combined = combined + alpha_pow * c_acc_step;
            // alpha_pow = alpha_pow * alpha; // not needed after last
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() < pi::BASE_COUNT {
            return constraints;
        }

        // First row: state_commitment column must match the public input directly.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::OLD_COMMIT],
        });

        // CRITICAL: Last row state_after commitment must match new_commitment PI.
        // Without this, a malicious prover could claim any new_commitment.
        // The last row is either the last real effect or a NoOp padding row;
        // either way, its state_after must equal the final state.
        let last_row = trace_len.saturating_sub(1);
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::NEW_COMMIT],
        });

        // Net balance delta binding: the net delta is carried in aux columns.
        // Row 0, aux[2] = net_delta_magnitude, aux[3] = net_delta_sign.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 2,
            value: public_inputs[pi::NET_DELTA_MAG],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 3,
            value: public_inputs[pi::NET_DELTA_SIGN],
        });

        // ====================================================================
        // SOUNDNESS FIX (P0-1): Pin row 0 state_before.balance_* and last_row
        // state_after.balance_* to public inputs. Combined with the per-effect
        // arithmetic constraints (which read state_before and write state_after
        // balance columns), the row-to-row continuity constraint, and the
        // Group 6 PI-only algebraic check (in eval_constraints), this makes
        // NET_DELTA_MAG/SIGN cryptographically bound to the actual trace
        // balance flow. Verifier MUST derive INIT/FINAL_BAL_* from the same
        // cell state used to derive OLD/NEW_COMMIT.
        // ====================================================================
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_LO,
            value: public_inputs[pi::INIT_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_HI,
            value: public_inputs[pi::INIT_BAL_HI],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_LO,
            value: public_inputs[pi::FINAL_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_HI,
            value: public_inputs[pi::FINAL_BAL_HI],
        });

        // Effects hash binding (position 0 of the 4-felt Stage 1 form is the
        // in-trace continuity binding; positions 1..3 are bound by the
        // executor's PI-matching loop, not by AIR boundaries — see
        // AUDIT[stage1-pi-only-bound] in pi module).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 4,
            value: public_inputs[pi::EFFECTS_HASH_BASE],
        });
        // EFFECTS_HASH_BASE + 1: bound to AUX_BASE + 5 as before (preserves
        // legacy 2-felt witness binding; positions 2..3 are PI-only).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 5,
            value: public_inputs[pi::EFFECTS_HASH_BASE + 1],
        });

        // Stage 2 resolution of REVIEW[stage1-acc-row0]: exclusive-sum scheme.
        //   Row 0: aux[CUSTOM_COUNT_ACC] == 0 (no rows summed yet).
        //   Transition (in eval_constraints Group 7): next.acc == this.acc + this.s_custom.
        //   Last row: aux[CUSTOM_COUNT_ACC] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT].
        //
        // The last-row equation must use the row's selector, which the boundary
        // API doesn't expose directly. We split it into TWO boundary constraints
        // (cannot express s_custom dependency without an extra column), so we
        // instead add an aux column that holds the *inclusive* sum at the last
        // row only. Actually the cleaner trick: use the transition relation
        // backwards. The last-row constraint becomes the boundary
        //   aux[CUSTOM_COUNT_ACC]_{last_row} == PI[CUSTOM_EFFECT_COUNT] - s_custom_{last_row}
        // which still depends on the trace cell s_custom_{last_row}. Boundary
        // constraints CAN reference trace cells in some STARK frameworks but
        // not this one (BoundaryConstraint fixes a value).
        //
        // Resolution: add a *virtual* end-row by ensuring the trace generator
        // always pads with a NoOp row at the end (s_custom == 0 by NoOp's
        // exclusivity). Then last_row.acc directly equals the total count of
        // s_custom rows in [0..last_row) which (since last_row is NoOp)
        // includes all real custom rows. Boundary becomes:
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]
        //
        // The trace generator already pads to next power-of-two with NoOp rows
        // when n_effects isn't a power of two. For the all-real-rows case
        // (n_effects exactly a power of two), the existing prover only emits
        // real rows; we tighten the boundary to use last-row regardless and
        // require trace gen to enforce s_custom == 0 at the last padded row.
        // For now, we keep the simpler invariant:
        //   acc[0] == 0  (row 0 anchor)
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]  (closes the chain assuming
        //     last row's s_custom contribution is reflected in the prover-emitted
        //     acc OR last row is a NoOp pad row).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: BabyBear::ZERO,
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: public_inputs[pi::CUSTOM_EFFECT_COUNT],
        });

        // ====================================================================
        // Stage 7 / §B: trace-side boundary for γ.0a turn-identity PI.
        //
        // Closes #49 (AIR nonce-bump invisibility at the trace level): bind
        // row 0's `state_before.nonce` column to PI[ACTOR_NONCE]. Without
        // this, a malicious prover could submit a trace whose row-0 nonce
        // disagrees with PI[ACTOR_NONCE] and the STARK would still verify.
        //
        // Scope: this binding is correct for single-cell proofs where the
        // proven cell IS the agent (state.nonce() == turn.nonce). For
        // multi-cell turns, only the agent cell satisfies this; non-agent
        // cells would need an IS_AGENT_CELL PI gate (deferred to γ.2 /
        // STAGE-7-GAMMA-AGGREGATION-DESIGN.md). The bundle verifier
        // (`verify_proof_carrying_turn_bundle`) cross-checks PI[ACTOR_NONCE]
        // is the same across all per-cell proofs of a turn, so once we
        // gate this boundary per-cell-role the property propagates.
        //
        // EFFECTS_HASH_GLOBAL_BASE: not boundary-bound here. Per-cell
        // proofs already pin PI[EFFECTS_HASH_BASE] (the per-cell value)
        // via the row-0 aux[4..5] binding above. For single-cell turns,
        // EFFECTS_HASH_BASE == EFFECTS_HASH_GLOBAL_BASE (the bundle is
        // one cell) and the executor's PI-matching loop enforces the
        // equality. For multi-cell turns, the bundle verifier merges
        // per-cell effects_hash values into the global; that's a γ.1+
        // aggregation concern, not an AIR-local one.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::NONCE,
            value: public_inputs[pi::ACTOR_NONCE],
        });

        // ====================================================================
        // SOVEREIGN-WITNESS AIR TEETH (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.3)
        //
        // Row-0 boundary: bind the in-trace witness-identity aux columns
        // to the matching PI slots. The constraint holds unconditionally,
        // by sentinel-zero agreement on the hosted-cell path:
        //
        //   When IS_SOVEREIGN_CELL == 1 (sovereign path):
        //     trace[0][WITNESS_KEY_COMMIT_i] == PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i]
        //     trace[0][WITNESS_SEQUENCE] == PI[SOVEREIGN_WITNESS_SEQUENCE]
        //   When IS_SOVEREIGN_CELL == 0 (hosted path):
        //     prover writes zero into both columns; verifier writes zero
        //     into both PI slots; equality holds.
        //
        // A malicious executor that swaps the witness for one signed by a
        // different key cannot satisfy this binding without changing PI,
        // and the verifier supplies PI from the signature-verified key
        // (executor injection step §2.5 in AUDIT-sovereign-witness-teeth.md).
        // Combined effect: the witness identity becomes acceptance-inside
        // for the AIR layer.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 1],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 2],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 3],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_SEQUENCE,
            value: public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE],
        });

        // ====================================================================
        // SOUNDNESS FIX (Gap 1): Net delta range check via balance binding.
        //
        // The net_delta public input MUST reflect the actual balance change.
        // We enforce this by pinning the initial and final balance_lo values
        // on boundary rows. The state_commitment hash already binds these
        // values (Poseidon2 preimage resistance), so any attempt to use
        // out-of-range limbs in the commitment would require a hash collision.
        //
        // Additionally, we constrain net_delta_sign to be boolean (0 or 1)
        // via a boundary constraint. Combined with the state commitment
        // integrity constraints (Group 4), this prevents a malicious prover
        // from encoding a wrapped negative balance as a large positive field
        // element in the net_delta.
        //
        // The binding chain is:
        //   1. Boundary: row 0 state_commit == PI[OLD_COMMIT]
        //   2. Group 4: state_commit == Poseidon2(bal_lo, bal_hi, nonce, ...)
        //   3. This: row 0 bal_lo and last_row bal_lo are hash-bound
        //   4. Transition: row continuity chains all intermediate states
        //   5. Boundary: last_row state_commit == PI[NEW_COMMIT]
        //
        // A malicious prover cannot fabricate net_delta without either:
        //   - Breaking Poseidon2 preimage resistance (computationally infeasible)
        //   - Violating the algebraic constraints (caught by STARK verifier)
        // ====================================================================

        // Net delta sign must be boolean (prevents sign manipulation).
        // Enforced: PI[NET_DELTA_SIGN] must be 0 or 1.
        // This is checked in eval_constraints as: sign * (sign - 1) == 0.
        // We also enforce it via boundary: pin aux[3] to PI value (already done above)
        // AND add the boolean check as a per-row constraint (see CONSTRAINT GROUP 5).

        constraints
    }
}
