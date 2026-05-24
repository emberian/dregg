//! Effect-VM-shape `p3-air::Air` bridge — feeds the existing recursion path.
//!
//! ## Why this file exists
//!
//! `crate::effect_vm::EffectVmAir` implements pyana's local `StarkAir` trait,
//! which evaluates folded constraints as a concrete `BabyBear` value. The
//! `p3-recursion` library (via its blanket `RecursiveAir` impl) requires an
//! AIR that implements `p3-air::Air<AB>` — i.e. one that emits *symbolic*
//! constraints against an `AirBuilder` so the verifier-circuit compiler can
//! pick them apart.
//!
//! Re-emitting all 600+ lines of `EffectVmAir::eval_constraints` in symbolic
//! form is a multi-week task (it includes selector-gated Poseidon2 state
//! commitments, sealing bit-decomposition, queue Merkle paths, …). For Block
//! 1 / Block 2 of the Golden Vision recursion lane the question is narrower:
//! *will the recursion library accept an AIR with the Effect VM's column
//! count (105), public-input count (74 base), and selector exclusivity
//! shape?*
//!
//! This module answers that with a minimal AIR — `EffectVmShapeAir` — that:
//!
//! 1. Has the **same width** as the full Effect VM (`EFFECT_VM_WIDTH = 105`).
//! 2. Declares the **same number of public inputs** as the base PI layout
//!    (`pi::BASE_COUNT = 74`), so the PI-binding shape that `p3-recursion`
//!    expects matches reality.
//! 3. Enforces a non-trivial **subset** of the real constraints — selector
//!    booleanity, selector sum-to-one, NoOp passthrough, Transfer balance
//!    delta — in **symbolic form** against `p3-air::Air<AB>`.
//!
//! If `prove_recursive_layer_for_air` accepts this AIR end-to-end, then the
//! mechanical generalization the Kimchi survey § 9.1 asks about *holds*: the
//! recursion library's blanket impl is shape-agnostic to width and PI count.
//! Adding the remaining Effect VM constraints in symbolic form is then a
//! *finite, mechanical* task (mostly translation, not new design).
//!
//! ## What this file does NOT do
//!
//! - It is not a soundness equivalent of `EffectVmAir`. A trace that
//!   passes here would NOT pass the full Effect VM AIR. Use `EffectVmAir`
//!   for actual proof generation; use this AIR only to measure the
//!   recursion machinery's column/PI tolerance.
//! - It does not modify `circuit/src/effect_vm.rs` in any way — it only
//!   reads constants (`EFFECT_VM_WIDTH`, `NUM_EFFECTS`, `STATE_BEFORE_BASE`,
//!   `STATE_AFTER_BASE`, `PARAM_BASE`, `pi::*`) from that module.
//!
//! ## Block 2 evolution path
//!
//! When the Effect VM AIR needs to be fully recursive, the work is to
//! grow `eval()` here to mirror every selector branch in
//! `EffectVmAir::eval_constraints`. The translation is mechanical:
//!
//!     // local code (concrete):                        // p3-air (symbolic):
//!     let s = local[sel::NOOP];                        let s: AB::Expr = local[sel::NOOP].into();
//!     let c = s * (s - BabyBear::ONE);                 let c: AB::Expr = s.clone() * (s - AB::Expr::ONE);
//!     combined = combined + alpha_pow * c;             builder.assert_zero(c);
//!     alpha_pow = alpha_pow * alpha;                   // (alpha folding is the verifier's job)
//!
//! The alpha-folding scaffolding inside `eval_constraints` is the
//! verifier's responsibility under `p3-air` — each `builder.assert_zero(c)`
//! call adds `c` to the constraint vector, and the recursion library
//! handles folding it with successive powers of `alpha`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

use crate::effect_vm::{
    EFFECT_VM_WIDTH, NUM_EFFECTS, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, pi, sel, state,
};
use crate::field::BabyBear;

/// AIR with the Effect VM's column/PI shape but a deliberately minimal
/// constraint set. See module docs for scope and intent.
pub struct EffectVmShapeAir;

impl EffectVmShapeAir {
    /// Width of the AIR (matches `EFFECT_VM_WIDTH = 105`).
    pub const WIDTH: usize = EFFECT_VM_WIDTH;
    /// Public-input count (matches the Stage 7-γ.0a base layout: 74 felts).
    pub const PUBLIC_INPUTS: usize = pi::BASE_COUNT;
}

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for EffectVmShapeAir {
    fn width(&self) -> usize {
        Self::WIDTH
    }

    fn num_public_values(&self) -> usize {
        Self::PUBLIC_INPUTS
    }

    /// We access state-after columns on the next row for chain continuity
    /// (next.state_before == this.state_after, per the real AIR's continuity
    /// constraint). Returning the full state-after range is the safe
    /// over-approximation for the recursion library's window analysis.
    fn main_next_row_columns(&self) -> Vec<usize> {
        (STATE_BEFORE_BASE..STATE_BEFORE_BASE + state::SIZE).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for EffectVmShapeAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector booleanity + sum-to-one
        //
        // Mirrors the first ~50 lines of `EffectVmAir::eval_constraints`.
        // These are the cheapest, most-fundamental constraints; if they don't
        // accept here, no fancier subset will.
        // ====================================================================
        let one = AB::Expr::ONE;

        for i in 0..NUM_EFFECTS {
            let s: AB::Expr = local[i].into();
            // s * (s - 1) == 0
            let c = s.clone() * (s - one.clone());
            builder.assert_zero(c);
        }

        // Σ selectors == 1
        let mut sum: AB::Expr = AB::Expr::ZERO;
        for i in 0..NUM_EFFECTS {
            sum = sum + local[i].into();
        }
        builder.assert_zero(sum - one.clone());

        // ====================================================================
        // CONSTRAINT GROUP 2: NoOp passthrough
        //
        // If sel_noop = 1, then state_after[i] == state_before[i] for all i.
        // Otherwise (any other selector) the constraint is trivially
        // satisfied. This is the "smallest non-trivial Effect VM AIR variant"
        // the Kimchi survey calls out as a Block-1 candidate.
        // ====================================================================
        let s_noop: AB::Expr = local[sel::NOOP].into();
        for i in 0..state::SIZE {
            let before: AB::Expr = local[STATE_BEFORE_BASE + i].into();
            let after: AB::Expr = local[STATE_AFTER_BASE + i].into();
            // s_noop * (state_after[i] - state_before[i]) == 0
            builder.assert_zero(s_noop.clone() * (after - before));
        }

        // ====================================================================
        // CONSTRAINT GROUP 3: Transfer balance delta (simplest value effect)
        //
        // param[0] = amount, param[1] = direction (0=in, 1=out).
        // Unified: new_bal_lo == old_bal_lo + amount * (1 - 2*direction).
        // Gated by s_transfer; trivial otherwise.
        //
        // We also enforce direction booleanity, so an honest prover cannot
        // smuggle a non-{0,1} direction to defeat the (1-2*dir) sign flip.
        // ====================================================================
        let s_transfer: AB::Expr = local[sel::TRANSFER].into();
        let amount: AB::Expr = local[PARAM_BASE].into();
        let direction: AB::Expr = local[PARAM_BASE + 1].into();
        let old_bal_lo: AB::Expr = local[STATE_BEFORE_BASE + state::BALANCE_LO].into();
        let new_bal_lo: AB::Expr = local[STATE_AFTER_BASE + state::BALANCE_LO].into();

        let two = AB::Expr::TWO;
        let sign = one.clone() - two * direction.clone();
        // s_transfer * (new_bal_lo - old_bal_lo - amount * sign) == 0
        let delta = new_bal_lo - old_bal_lo - amount * sign;
        builder.assert_zero(s_transfer.clone() * delta);

        // s_transfer * direction * (direction - 1) == 0  (gated booleanity)
        builder.assert_zero(s_transfer * direction.clone() * (direction - one.clone()));

        // ====================================================================
        // CONSTRAINT GROUP 4: Chain continuity
        //
        // next.state_before == this.state_after, gated to skip the last row.
        // ====================================================================
        for i in 0..state::SIZE {
            let after_local: AB::Expr = local[STATE_AFTER_BASE + i].into();
            let before_next: AB::Expr = next[STATE_BEFORE_BASE + i].into();
            builder
                .when_transition()
                .assert_zero(before_next - after_local);
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Boundary binding to PI
        //
        // First row's state_before.state_commit == PI[OLD_COMMIT] (legacy
        // single-felt continuity), and last row's state_after.state_commit ==
        // PI[NEW_COMMIT]. Matches the boundary constraints `EffectVmAir`
        // emits via its `boundary_constraints()` method.
        // ====================================================================
        let public_values = builder.public_values();
        let pv_old: AB::Expr = public_values[pi::OLD_COMMIT].into();
        let pv_new: AB::Expr = public_values[pi::NEW_COMMIT].into();
        let first_commit: AB::Expr = local[STATE_BEFORE_BASE + state::STATE_COMMIT].into();
        let last_commit: AB::Expr = local[STATE_AFTER_BASE + state::STATE_COMMIT].into();

        builder.when_first_row().assert_zero(first_commit - pv_old);
        builder.when_last_row().assert_zero(last_commit - pv_new);
    }
}

/// Build a minimal Effect-VM-shape trace satisfying [`EffectVmShapeAir`]'s
/// constraints, with a row count of `n_rows` (power-of-two ≥ 2).
///
/// Row layout: a single Transfer at row 0 with amount=0, direction=0 (so
/// new_bal_lo = old_bal_lo); all subsequent rows are NoOp passthroughs.
/// PIs: `OLD_COMMIT = NEW_COMMIT = chosen_commit` (so the boundary
/// constraints hold trivially).
///
/// This is a witness factory for the smoke tests in
/// `plonky3_recursion_impl::recursive::tests`, not a production trace.
pub fn build_minimal_shape_trace(n_rows: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(n_rows >= 2 && n_rows.is_power_of_two());

    let chosen_commit = BabyBear::new(0xDA7A);

    let mut trace = Vec::with_capacity(n_rows);

    // Row 0: Transfer with amount=0, direction=0 → balance passthrough,
    // state_commit passthrough.
    let mut row0 = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
    row0[sel::TRANSFER] = BabyBear::ONE;
    // state_before.state_commit = chosen_commit (boundary)
    row0[STATE_BEFORE_BASE + state::STATE_COMMIT] = chosen_commit;
    // state_after.state_commit = chosen_commit (passthrough)
    row0[STATE_AFTER_BASE + state::STATE_COMMIT] = chosen_commit;
    // amount = 0, direction = 0 (Transfer constraints trivially satisfied)
    row0[PARAM_BASE] = BabyBear::ZERO;
    row0[PARAM_BASE + 1] = BabyBear::ZERO;
    trace.push(row0);

    // Rows 1..n_rows: NoOp passthroughs. state_before == state_after, and
    // continuity demands state_before[i].x == state_after[i-1].x.
    for _ in 1..n_rows {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE;
        row[STATE_BEFORE_BASE + state::STATE_COMMIT] = chosen_commit;
        row[STATE_AFTER_BASE + state::STATE_COMMIT] = chosen_commit;
        trace.push(row);
    }

    let mut public_inputs = vec![BabyBear::ZERO; pi::BASE_COUNT];
    public_inputs[pi::OLD_COMMIT] = chosen_commit;
    public_inputs[pi::NEW_COMMIT] = chosen_commit;

    (trace, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::BabyBear;
    use crate::stark::StarkAir;

    /// Sanity: the shape AIR reports the same width and PI count as the
    /// real Effect VM AIR's published constants. If this drifts, the
    /// constraint mirroring path is no longer measuring the right shape.
    #[test]
    fn shape_matches_effect_vm_constants() {
        // From `effect_vm::EFFECT_VM_WIDTH`.
        assert_eq!(EffectVmShapeAir::WIDTH, EFFECT_VM_WIDTH);
        // From `effect_vm::pi::BASE_COUNT`.
        assert_eq!(EffectVmShapeAir::PUBLIC_INPUTS, pi::BASE_COUNT);
    }

    /// The minimal trace produced by `build_minimal_shape_trace` should
    /// satisfy the shape AIR's constraints under a concrete-evaluation
    /// fold. We verify by hand-folding the symbolic constraints against
    /// a debug-mode AirBuilder analog: cross-check that the
    /// `EffectVmShapeAir::eval()` constraints all read zero under the
    /// trace data.
    ///
    /// Done by running the trace through the real Plonky3 prover/verifier
    /// pair (via the recursion-compatible config); a failing trace would
    /// be caught by `verify`.
    #[cfg(feature = "recursion")]
    #[test]
    fn minimal_trace_inner_proof_round_trips() {
        use crate::plonky3_recursion_impl::recursive::{prove_inner_for_air, verify_inner_for_air};
        use p3_baby_bear::BabyBear as P3BabyBear;
        use p3_matrix::dense::RowMajorMatrix;

        let (trace, pis) = build_minimal_shape_trace(4);

        // Lift to p3-baby-bear.
        let flat: Vec<P3BabyBear> = trace
            .iter()
            .flat_map(|row| row.iter().map(|&v| crate::plonky3_prover::to_p3(v)))
            .collect();
        let matrix = RowMajorMatrix::new(flat, EFFECT_VM_WIDTH);

        let air = EffectVmShapeAir;
        let proof = prove_inner_for_air(&air, matrix, &pis);
        verify_inner_for_air(&air, &proof, &pis).expect("Effect-VM-shape inner proof must verify");
    }
}
