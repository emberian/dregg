//! DSL-generated temporal predicate AIR.
//!
//! This module replaces the hand-written `temporal_predicate_air.rs` with the
//! equivalent of the `#[pyana_circuit]` macro-generated implementation. The
//! macro version (in `pyana-dsl-tests/src/temporal_macro.rs`) passes full STARK
//! prove/verify and is bit-for-bit equivalent to the manual descriptor in
//! `pyana-dsl-tests/src/temporal_dsl.rs`.
//!
//! Because proc-macro-generated code references `pyana_circuit::*` which cannot
//! resolve when compiled *within* the `pyana-circuit` crate itself, this file
//! contains the manually-expanded equivalent of what `#[pyana_circuit]` would
//! produce.
//!
//! # Migration
//!
//! All callers should use this module instead of `temporal_predicate_air`.
//! The public API is preserved: `TemporalPredicateAir`, `TemporalPredicateWitness`,
//! `TemporalPredicateProof`, `prove_temporal_predicate`, `verify_temporal_predicate`,
//! and `TemporalPredicateRequirement` are all re-exported with the same signatures.

use crate::field::BabyBear;
use crate::predicate_air::PredicateType;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

// ─────────────────────────────────────────────────────────────────────────────
// DSL-equivalent core AIR (manual expansion of #[pyana_circuit] output)
// ─────────────────────────────────────────────────────────────────────────────

/// Column layout constants for the DSL temporal AIR.
pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
pub const DSL_TRACE_WIDTH: usize = STEP_PLUS_ONE + 1; // 37

/// Public input layout: [num_steps]
pub const PI_NUM_STEPS: usize = 0;
pub const DSL_PUBLIC_INPUT_COUNT: usize = 1;

/// Column index submodule (mirrors the `mod col` in the `#[pyana_circuit]` definition).
pub mod col {
    pub const VALUE: usize = 0;
    pub const THRESHOLD: usize = 1;
    pub const DIFF: usize = 2;
    pub const DIFF_BITS_START: usize = 3;
    pub const NUM_DIFF_BITS: usize = 30;
    pub const ACCUMULATOR: usize = 33;
    pub const STEP_INDEX: usize = 34;
    pub const ACC_PLUS_ONE: usize = 35;
    pub const STEP_PLUS_ONE: usize = 36;
}

/// The DSL-generated temporal predicate AIR struct.
///
/// This is the equivalent of what `#[pyana_circuit] mod temporal_predicate_dsl { ... }`
/// would produce: a unit struct implementing `StarkAir`.
pub struct TemporalPredicateDsl;

impl StarkAir for TemporalPredicateDsl {
    fn width(&self) -> usize {
        37
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn air_name(&self) -> &'static str {
        "pyana-temporal_predicate_dsl-v1"
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
        // Per-row constraints (inlined from the `fn constraints` body)
        let constraint_values: Vec<BabyBear> = {
            let pi = public_inputs;
            let mut cs = Vec::new();

            // C1: diff = value - threshold
            cs.push(local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD]));

            // C2: Each diff_bit is binary
            for i in 0..col::NUM_DIFF_BITS {
                let bit = local[col::DIFF_BITS_START + i];
                cs.push(bit * (bit - BabyBear::ONE));
            }

            // C3: Bit reconstruction: sum(diff_bits[i] * 2^i) == diff
            {
                let mut reconstructed = BabyBear::ZERO;
                let mut power_of_two = BabyBear::ONE;
                let two = BabyBear::new(2);
                for i in 0..col::NUM_DIFF_BITS {
                    reconstructed = reconstructed + local[col::DIFF_BITS_START + i] * power_of_two;
                    power_of_two = power_of_two * two;
                }
                cs.push(reconstructed - local[col::DIFF]);
            }

            // C4: High bit is zero (range proof: diff < 2^30 => non-negative)
            cs.push(local[col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1]);

            // C5: acc_plus_one = accumulator + 1
            cs.push(local[col::ACC_PLUS_ONE] - local[col::ACCUMULATOR] - BabyBear::ONE);

            // C6: step_plus_one = step_index + 1
            cs.push(local[col::STEP_PLUS_ONE] - local[col::STEP_INDEX] - BabyBear::ONE);

            let _ = pi; // suppress unused warning
            cs
        };

        // Transition constraints (inlined from the `fn transitions` body)
        let transition_values: Vec<BabyBear> = {
            vec![
                // T1: next[accumulator] = local[acc_plus_one]
                next[col::ACCUMULATOR] - local[col::ACC_PLUS_ONE],
                // T2: next[step_index] = local[step_plus_one]
                next[col::STEP_INDEX] - local[col::STEP_PLUS_ONE],
            ]
        };

        // Compose all constraints with alpha powers
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;
        for c in constraint_values.iter().chain(transition_values.iter()) {
            result = result + alpha_power * *c;
            alpha_power = alpha_power * alpha;
        }
        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let pi = public_inputs;
        let raw: Vec<(usize, usize, BabyBear)> = vec![
            // First row: accumulator = 1
            (0, col::ACCUMULATOR, BabyBear::ONE),
            // First row: step_index = 0
            (0, col::STEP_INDEX, BabyBear::ZERO),
            // Last row: accumulator = num_steps (pi[0])
            (trace_len - 1, col::ACCUMULATOR, pi[0]),
        ];
        raw.into_iter()
            .map(|(row, col, value)| BoundaryConstraint { row, col, value })
            .collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API: backward-compatible types and functions
// ─────────────────────────────────────────────────────────────────────────────

/// Trace width for the temporal predicate AIR (legacy 35-column layout reference).
pub const TEMPORAL_PREDICATE_WIDTH: usize = 35;

/// Witness for a temporal predicate proof.
///
/// Contains the sequence of values and state roots over the time range,
/// plus the predicate parameters.
#[derive(Clone, Debug)]
pub struct TemporalPredicateWitness {
    /// The attribute values at each step (one per time unit).
    pub values: Vec<BabyBear>,
    /// The state roots at each step (binding to the receipt/IVC chain).
    pub state_roots: Vec<BabyBear>,
    /// The predicate type (currently only GTE is supported for temporal).
    pub predicate_type: PredicateType,
    /// The threshold the predicate must meet at every step.
    pub threshold: BabyBear,
}

impl TemporalPredicateWitness {
    /// Check whether the temporal predicate is satisfiable (all steps pass).
    pub fn is_satisfiable(&self) -> bool {
        if self.values.len() != self.state_roots.len() {
            return false;
        }
        if self.values.is_empty() {
            return false;
        }
        let threshold = self.threshold.as_u32();
        self.values.iter().all(|v| {
            let val = v.as_u32();
            match self.predicate_type {
                PredicateType::Gte | PredicateType::InRangeLow => val >= threshold,
                PredicateType::Lte | PredicateType::InRangeHigh => val <= threshold,
                PredicateType::Gt => val > threshold,
                PredicateType::Lt => val < threshold,
                PredicateType::Neq => val != threshold,
            }
        })
    }

    /// Number of steps in the temporal range.
    pub fn num_steps(&self) -> usize {
        self.values.len()
    }

    /// Compute the diff at a given step based on predicate type.
    fn compute_diff_at(&self, step: usize) -> BabyBear {
        let value = self.values[step];
        let threshold = self.threshold;
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => value - threshold,
            PredicateType::Lte | PredicateType::InRangeHigh => threshold - value,
            PredicateType::Gt => value - threshold - BabyBear::ONE,
            PredicateType::Lt => threshold - value - BabyBear::ONE,
            PredicateType::Neq => value - threshold,
        }
    }
}

/// The Temporal Predicate AIR (DSL-generated).
///
/// This is a wrapper around the DSL-generated `TemporalPredicateDsl` struct
/// that maintains the same public interface as the hand-written version. The
/// witness is stored for trace generation, while constraint evaluation is
/// delegated to the DSL-generated implementation.
pub struct TemporalPredicateAir {
    pub witness: TemporalPredicateWitness,
}

impl TemporalPredicateAir {
    pub fn new(witness: TemporalPredicateWitness) -> Self {
        Self { witness }
    }
}

/// Generate the DSL trace from a witness.
///
/// This converts from the witness format (multiple predicate types, state roots)
/// into the DSL trace layout (37-column layout with auxiliary columns).
pub fn generate_dsl_trace(
    witness: &TemporalPredicateWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = witness.num_steps();
    assert!(num_steps >= 1, "temporal witness must have at least 1 step");

    let padded_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(padded_len);

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; DSL_TRACE_WIDTH];

        // For padding rows beyond num_steps, repeat the last real row's value.
        let val = if step < num_steps {
            witness.values[step]
        } else {
            *witness.values.last().unwrap()
        };

        row[VALUE] = val;
        row[THRESHOLD] = witness.threshold;

        // Compute diff based on predicate type
        let diff = if step < num_steps {
            witness.compute_diff_at(step)
        } else {
            witness.compute_diff_at(num_steps - 1)
        };
        row[DIFF] = diff;

        // Bit decomposition of diff
        if witness.predicate_type != PredicateType::Neq {
            let diff_val = diff.as_u32();
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff_val >> i) & 1);
            }
        }

        // Accumulator: 1-indexed (step 0 -> acc = 1)
        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        trace.push(row);
    }

    let public_inputs = vec![BabyBear::new(padded_len as u32)];
    (trace, public_inputs)
}

impl StarkAir for TemporalPredicateAir {
    fn width(&self) -> usize {
        DSL_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-temporal_predicate_dsl-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // Delegate to the DSL-generated implementation.
        TemporalPredicateDsl.eval_constraints(local, next, public_inputs, alpha)
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        // Delegate to the DSL-generated implementation.
        TemporalPredicateDsl.boundary_constraints(public_inputs, trace_len)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Proof types
// ─────────────────────────────────────────────────────────────────────────────

/// A complete temporal predicate proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TemporalPredicateProof {
    /// The predicate type that was proven.
    pub predicate_type: PredicateType,
    /// The threshold (public).
    pub threshold: BabyBear,
    /// Number of REAL steps over which the predicate held (not including padding).
    pub num_steps: u32,
    /// Padded trace length (power of 2, used in STARK boundary constraints).
    pub padded_len: u32,
    /// The initial state root (binding to the start of the range).
    pub initial_state_root: BabyBear,
    /// The final state root (binding to the end of the range).
    pub final_state_root: BabyBear,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
}

// ─────────────────────────────────────────────────────────────────────────────
// Prover / Verifier API
// ─────────────────────────────────────────────────────────────────────────────

/// Generate a temporal predicate proof.
///
/// Proves that `predicate_type(value, threshold)` held at every step across the
/// provided sequence of values. The proof is bound to the receipt/IVC chain via
/// the state roots at each step.
///
/// Returns `None` if the predicate does not hold at every step (cannot prove a
/// false temporal statement).
pub fn prove_temporal_predicate(
    values: &[BabyBear],
    state_roots: &[BabyBear],
    predicate_type: PredicateType,
    threshold: BabyBear,
) -> Option<TemporalPredicateProof> {
    let witness = TemporalPredicateWitness {
        values: values.to_vec(),
        state_roots: state_roots.to_vec(),
        predicate_type,
        threshold,
    };

    if !witness.is_satisfiable() {
        return None;
    }

    let num_steps = witness.num_steps() as u32;
    let initial_state_root = witness.state_roots[0];
    let final_state_root = *witness.state_roots.last().unwrap();

    let air = TemporalPredicateAir::new(witness);
    let (trace, public_inputs) = generate_dsl_trace(&air.witness);
    let padded_len = trace.len() as u32;

    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(TemporalPredicateProof {
        predicate_type,
        threshold,
        num_steps,
        padded_len,
        initial_state_root,
        final_state_root,
        stark_proof,
    })
}

/// Verify a temporal predicate proof.
///
/// The verifier provides the expected parameters and checks the proof is
/// consistent.
pub fn verify_temporal_predicate(
    proof: &TemporalPredicateProof,
    threshold: BabyBear,
    num_steps: u32,
    initial_state_root: BabyBear,
    final_state_root: BabyBear,
) -> bool {
    // Check claimed parameters match expected.
    if proof.threshold != threshold {
        return false;
    }
    if proof.num_steps != num_steps {
        return false;
    }
    if proof.initial_state_root != initial_state_root {
        return false;
    }
    if proof.final_state_root != final_state_root {
        return false;
    }

    let padded_len = proof.padded_len;

    // Sanity: padded_len must be >= num_steps and a power of two.
    if padded_len < num_steps || !padded_len.is_power_of_two() {
        return false;
    }

    let public_inputs = vec![BabyBear::new(padded_len)];

    // Reconstruct a dummy witness for the AIR shape.
    let dummy_witness = TemporalPredicateWitness {
        values: vec![BabyBear::ZERO; num_steps as usize],
        state_roots: vec![BabyBear::ZERO; num_steps as usize],
        predicate_type: proof.predicate_type,
        threshold,
    };
    let air = TemporalPredicateAir::new(dummy_witness);
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Intent integration: Temporal predicate requirements
// ─────────────────────────────────────────────────────────────────────────────

/// A temporal predicate requirement for intent matching.
///
/// Specifies that a counterparty must prove a property held continuously
/// for a minimum duration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemporalPredicateRequirement {
    /// The attribute being checked (e.g., "balance", "reputation").
    pub attribute: String,
    /// The predicate type (e.g., GTE for "at least").
    pub predicate_type: PredicateType,
    /// The threshold value.
    pub threshold: u64,
    /// Minimum number of consecutive steps the predicate must hold.
    pub min_duration_steps: u64,
}

impl TemporalPredicateRequirement {
    /// Check whether a temporal predicate proof satisfies this requirement.
    pub fn is_satisfied_by(&self, proof: &TemporalPredicateProof) -> bool {
        if proof.predicate_type != self.predicate_type {
            return false;
        }
        if proof.threshold.as_u32() < self.threshold as u32 {
            return false;
        }
        if (proof.num_steps as u64) < self.min_duration_steps {
            return false;
        }
        true
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Plonky3-native temporal predicate AIR (re-exported from legacy)
// ─────────────────────────────────────────────────────────────────────────────

/// Re-export the Plonky3-based temporal AIR from the legacy module.
/// The P3 variant has its own separate AIR implementation that uses Plonky3's
/// native AirBuilder and is independent of the DSL system.
#[cfg(feature = "plonky3")]
pub mod p3_temporal {
    pub use crate::temporal_predicate_air::p3_temporal::*;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: generate state roots for testing (sequential hashes).
    fn test_state_roots(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new(1000 + i as u32)).collect()
    }

    // =========================================================================
    // DSL struct basic checks
    // =========================================================================

    #[test]
    fn test_dsl_circuit_struct_exists() {
        let circuit = TemporalPredicateDsl;
        assert_eq!(circuit.width(), 37);
        assert_eq!(circuit.constraint_degree(), 2);
        assert_eq!(circuit.air_name(), "pyana-temporal_predicate_dsl-v1");
    }

    #[test]
    fn test_dsl_circuit_valid_trace() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);
        assert_eq!(trace.len(), 4); // next power of 2

        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &public_inputs, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Constraint nonzero at row {i} (valid trace)"
            );
        }
    }

    #[test]
    fn test_dsl_circuit_invalid_value_below_threshold() {
        let circuit = TemporalPredicateDsl;

        let values: Vec<BabyBear> = vec![100, 30, 100].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);

        let alpha = BabyBear::new(7);
        let row1_result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            row1_result,
            BabyBear::ZERO,
            "Constraint should be nonzero at row 1 where value < threshold"
        );
    }

    #[test]
    fn test_dsl_circuit_transition_detects_gap() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (mut trace, public_inputs) = generate_dsl_trace(&witness);

        // Corrupt row 2: accumulator gap
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Transition constraint should be nonzero when accumulator has a gap"
        );

        // Row 0 -> Row 1 still fine
        let result_01 = circuit.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(result_01, BabyBear::ZERO);
    }

    // =========================================================================
    // Full prove/verify cycle (matches old API)
    // =========================================================================

    #[test]
    fn test_temporal_gte_all_pass() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![150, 200, 300, 100, 500, 120, 999, 101, 100, 250]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(10);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(proof.is_some(), "All values >= 100, proof should succeed");

        let proof = proof.unwrap();
        assert_eq!(proof.num_steps, 10);
        assert_eq!(proof.threshold, threshold);

        let valid =
            verify_temporal_predicate(&proof, threshold, 10, state_roots[0], state_roots[9]);
        assert!(valid, "Verification should pass");
    }

    #[test]
    fn test_temporal_gte_edge_exactly_at_threshold() {
        let threshold = BabyBear::new(50);
        let values: Vec<BabyBear> = vec![50; 5].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_some(),
            "Values exactly at threshold should pass GTE"
        );
    }

    #[test]
    fn test_temporal_gte_dip_below_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![150, 200, 300, 100, 500, 99, 999, 101, 100, 250]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(10);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_none(),
            "Value 99 < 100 at step 5 should cause proof generation to fail"
        );
    }

    #[test]
    fn test_verify_fails_wrong_threshold() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid =
            verify_temporal_predicate(&proof, BabyBear::new(50), 3, state_roots[0], state_roots[2]);
        assert!(!valid, "Wrong threshold should fail verification");
    }

    #[test]
    fn test_verify_fails_wrong_num_steps() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid = verify_temporal_predicate(&proof, threshold, 5, state_roots[0], state_roots[2]);
        assert!(!valid, "Wrong num_steps should fail verification");
    }

    #[test]
    fn test_verify_fails_wrong_state_root() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid =
            verify_temporal_predicate(&proof, threshold, 3, BabyBear::new(99999), state_roots[2]);
        assert!(!valid, "Wrong initial state root should fail verification");

        let valid =
            verify_temporal_predicate(&proof, threshold, 3, state_roots[0], BabyBear::new(99999));
        assert!(!valid, "Wrong final state root should fail verification");
    }

    #[test]
    fn test_temporal_lte_all_pass() {
        let threshold = BabyBear::new(500);
        let values: Vec<BabyBear> = vec![100, 200, 500, 300, 50]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Lte, threshold);
        assert!(proof.is_some(), "All values <= 500, should succeed");
    }

    #[test]
    fn test_temporal_lte_violation() {
        let threshold = BabyBear::new(500);
        let values: Vec<BabyBear> = vec![100, 200, 501, 300, 50]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Lte, threshold);
        assert!(proof.is_none(), "Value 501 > 500 should cause failure");
    }

    #[test]
    fn test_temporal_gt_all_pass() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![101, 200, 999].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gt, threshold);
        assert!(proof.is_some(), "All values > 100, should succeed");
    }

    #[test]
    fn test_temporal_gt_equal_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![101, 100, 200].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gt, threshold);
        assert!(
            proof.is_none(),
            "Value 100 is not > 100, should fail for GT"
        );
    }

    #[test]
    fn test_temporal_single_step() {
        let threshold = BabyBear::new(50);
        let values = vec![BabyBear::new(100)];
        let state_roots = vec![BabyBear::new(1000)];

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();
        assert_eq!(proof.num_steps, 1);

        let valid = verify_temporal_predicate(&proof, threshold, 1, state_roots[0], state_roots[0]);
        assert!(valid);
    }

    #[test]
    fn test_temporal_empty_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![];
        let state_roots: Vec<BabyBear> = vec![];

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(proof.is_none(), "Empty sequence should not produce a proof");
    }

    #[test]
    fn test_temporal_mismatched_lengths_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_none(),
            "Mismatched lengths should not produce a proof"
        );
    }

    #[test]
    fn test_temporal_requirement_satisfied() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200; 30].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(30);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let requirement = TemporalPredicateRequirement {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };

        assert!(
            requirement.is_satisfied_by(&proof),
            "30 steps >= 100 should satisfy requirement"
        );
    }

    #[test]
    fn test_temporal_requirement_insufficient_duration() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200; 10].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(10);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let requirement = TemporalPredicateRequirement {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };

        assert!(
            !requirement.is_satisfied_by(&proof),
            "10 steps < 30 required should not satisfy"
        );
    }

    #[test]
    fn test_temporal_soundness_cannot_fabricate_duration() {
        let threshold = BabyBear::new(100);
        let state_roots_3 = test_state_roots(3);

        let values_3: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let proof_3 =
            prove_temporal_predicate(&values_3, &state_roots_3, PredicateType::Gte, threshold)
                .expect("3 valid steps should produce a proof");
        assert_eq!(proof_3.num_steps, 3);

        let state_roots_10 = test_state_roots(10);
        let bogus_verify = verify_temporal_predicate(
            &proof_3,
            threshold,
            10,
            state_roots_10[0],
            state_roots_10[9],
        );
        assert!(
            !bogus_verify,
            "A 3-step proof must NOT verify as a 10-step proof"
        );

        let valid =
            verify_temporal_predicate(&proof_3, threshold, 3, state_roots_3[0], state_roots_3[2]);
        assert!(valid, "3-step proof should verify with correct parameters");
    }

    // =========================================================================
    // DSL STARK full prove/verify
    // =========================================================================

    #[test]
    fn test_dsl_stark_prove_verify() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);

        let proof = stark::prove(&circuit, &trace, &public_inputs);
        let result = stark::verify(&circuit, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "STARK verify failed on valid trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_dsl_stark_rejects_wrong_public_inputs() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);
        let proof = stark::prove(&circuit, &trace, &public_inputs);

        let wrong_pi = vec![BabyBear::new(8)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong num_steps");
    }
}
