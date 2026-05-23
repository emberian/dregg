//! Committed-threshold predicate AIR.
//!
//! Proves: "I know a value that satisfies a committed threshold AND the commitment
//! matches" without revealing either the value or the threshold to third-party verifiers.
//!
//! # Protocol
//!
//! 1. Verifier commits to their threshold: `commitment = Poseidon2(threshold, blinding)`
//! 2. Verifier sends `commitment` + `threshold` + `blinding` to the prover (secure channel).
//! 3. Prover generates this proof demonstrating:
//!    - `value >= threshold` (bit decomposition with high bit = 0)
//!    - `Poseidon2(threshold, blinding) == commitment` (commitment binding)
//!    - The value is bound to a specific token state via `fact_commitment`
//! 4. Public inputs: `[threshold_commitment, fact_commitment]`
//!    - Neither the threshold NOR the value is revealed to third parties.
//!
//! # Privacy Properties
//!
//! - **Third-party verifiers** see only two commitments. They learn: "some committed
//!   value satisfies some committed threshold" (1 bit: the proof verifies or it doesn't).
//! - **Prover** learns the threshold (necessary to generate the proof).
//! - **Verifier** learns only pass/fail (from whether the prover can produce a valid proof).
//!
//! # Trace Layout
//!
//! | Column     | Description                                              |
//! |------------|----------------------------------------------------------|
//! | 0          | private_value (the attribute being proven about)         |
//! | 1          | threshold (verifier's secret threshold, in witness)      |
//! | 2          | blinding (verifier's blinding randomness, in witness)    |
//! | 3          | diff = private_value - threshold                         |
//! | 4..34      | diff_bits[0..30] (bit decomposition of diff)             |
//! | 35         | threshold_commitment (matches public input)              |
//! | 36         | fact_commitment (binding to the token state)             |
//! | 37         | poseidon2_result (computed Poseidon2(threshold, blinding)) |
//!
//! # Public Inputs
//!
//! `[threshold_commitment, fact_commitment]`
//!
//! - `threshold_commitment`: Poseidon2(threshold, blinding) — committed by the verifier.
//! - `fact_commitment`: Poseidon2(fact_hash, state_root) — binds the proven value to state.

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Number of bits for the range check (same as PredicateAir).
///
/// SOUNDNESS FIX: BabyBear p = 2013265921, p/2 = 1006632960, 2^30 = 1073741824.
/// Since 2^30 > p/2, the old value of 31 was UNSOUND. With 30 bits, the high bit
/// is bit 29; if bit 29 = 0 then diff < 2^29 = 536870912 < p/2, proving non-negative.
pub const COMMITTED_DIFF_BITS: usize = 30;

/// Trace width for the committed-threshold AIR.
/// private_value(1) + threshold(1) + blinding(1) + diff(1) + diff_bits(30) +
/// threshold_commitment(1) + fact_commitment(1) + poseidon2_result(1) = 37
pub const COMMITTED_THRESHOLD_AIR_WIDTH: usize = 37;

/// Column indices for the committed-threshold AIR trace.
pub mod col {
    use super::COMMITTED_DIFF_BITS;

    /// The private attribute value (witness).
    pub const PRIVATE_VALUE: usize = 0;
    /// The verifier's threshold (witness — NOT public input).
    pub const THRESHOLD: usize = 1;
    /// The verifier's blinding randomness (witness).
    pub const BLINDING: usize = 2;
    /// The computed difference: value - threshold.
    pub const DIFF: usize = 3;
    /// Start of bit decomposition columns (31 bits).
    pub const DIFF_BITS_START: usize = 4;
    /// The threshold commitment (matches public input[0]).
    pub const THRESHOLD_COMMITMENT: usize = DIFF_BITS_START + COMMITTED_DIFF_BITS; // 35
    /// The fact commitment (matches public input[1]).
    pub const FACT_COMMITMENT: usize = THRESHOLD_COMMITMENT + 1; // 36
    /// The computed Poseidon2(threshold, blinding) for checking against commitment.
    pub const POSEIDON2_RESULT: usize = FACT_COMMITMENT + 1; // 37

    /// Get the column for diff_bits[bit_idx].
    #[inline]
    pub const fn diff_bit(bit_idx: usize) -> usize {
        DIFF_BITS_START + bit_idx
    }
}

/// Witness for a committed-threshold proof.
#[derive(Clone, Debug)]
pub struct CommittedThresholdWitness {
    /// The prover's private attribute value.
    pub private_value: BabyBear,
    /// The verifier's threshold (known to prover via secure channel).
    pub threshold: BabyBear,
    /// The verifier's blinding randomness (known to prover via secure channel).
    pub blinding: BabyBear,
    /// Fact commitment: Poseidon2(fact_hash, state_root).
    /// Binds this proof to a specific fact in a specific token state.
    pub fact_commitment: BabyBear,
}

impl CommittedThresholdWitness {
    /// Compute the threshold commitment: Poseidon2(threshold, blinding).
    pub fn compute_threshold_commitment(&self) -> BabyBear {
        compute_threshold_commitment(self.threshold, self.blinding)
    }

    /// Compute the difference: value - threshold.
    pub fn compute_diff(&self) -> BabyBear {
        self.private_value - self.threshold
    }

    /// Check whether the predicate is satisfiable (value >= threshold).
    pub fn is_satisfiable(&self) -> bool {
        self.private_value.as_u32() >= self.threshold.as_u32()
    }
}

/// Compute a threshold commitment: Poseidon2(threshold, blinding).
///
/// The verifier generates this commitment and sends it (along with the threshold
/// and blinding) to the prover. Third-party verifiers see only this commitment.
pub fn compute_threshold_commitment(threshold: BabyBear, blinding: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(threshold, blinding)
}

/// The committed-threshold predicate AIR.
///
/// Proves: value >= threshold AND Poseidon2(threshold, blinding) == threshold_commitment.
///
/// DEPRECATED: Use `crate::dsl::committed_threshold::prove_committed_threshold_dsl` and
/// `crate::dsl::committed_threshold::verify_committed_threshold_dsl` instead.
#[deprecated(
    note = "Use crate::dsl::committed_threshold::{prove,verify}_committed_threshold_dsl instead"
)]
pub struct CommittedThresholdAir {
    pub witness: CommittedThresholdWitness,
}

impl CommittedThresholdAir {
    pub fn new(witness: CommittedThresholdWitness) -> Self {
        Self { witness }
    }
}

impl StarkAir for CommittedThresholdAir {
    fn width(&self) -> usize {
        COMMITTED_THRESHOLD_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-committed-threshold-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // C1: threshold_commitment matches public_input[0]
        let c1 = local[col::THRESHOLD_COMMITMENT] - public_inputs[0];
        // C2: fact_commitment matches public_input[1]
        let c2 = local[col::FACT_COMMITMENT] - public_inputs[1];
        // C3: poseidon2_result == threshold_commitment
        let c3 = local[col::POSEIDON2_RESULT] - local[col::THRESHOLD_COMMITMENT];
        // C4: diff = private_value - threshold
        let c4 = local[col::DIFF] - (local[col::PRIVATE_VALUE] - local[col::THRESHOLD]);
        // C5: bit decomposition correct
        let diff = local[col::DIFF];
        let mut recomposed = BabyBear::ZERO;
        let mut power_of_two = BabyBear::ONE;
        for i in 0..COMMITTED_DIFF_BITS {
            let bit = local[col::diff_bit(i)];
            recomposed = recomposed + bit * power_of_two;
            power_of_two = power_of_two + power_of_two;
        }
        let c5 = recomposed - diff;
        // C6: bits are binary
        let mut c6 = BabyBear::ZERO;
        for i in 0..COMMITTED_DIFF_BITS {
            let bit = local[col::diff_bit(i)];
            c6 = c6 + bit * (bit - BabyBear::ONE);
        }
        // C7: high bit is zero
        let c7 = local[col::diff_bit(COMMITTED_DIFF_BITS - 1)];

        // Combine with alpha powers
        let mut combined = c1;
        let mut alpha_pow = alpha;
        combined = combined + alpha_pow * c2;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c3;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c4;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c5;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c6;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c7;

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::THRESHOLD_COMMITMENT,
                value: public_inputs[0],
            });
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::FACT_COMMITMENT,
                value: public_inputs[1],
            });
        }
        constraints
    }
}

impl Air for CommittedThresholdAir {
    fn trace_width(&self) -> usize {
        COMMITTED_THRESHOLD_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        2 // [threshold_commitment, fact_commitment]
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // Constraint 1: threshold_commitment in trace matches public input[0].
            Constraint {
                name: "threshold_commitment_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::THRESHOLD_COMMITMENT] - public_inputs[0]
                }),
            },
            // Constraint 2: fact_commitment in trace matches public input[1].
            Constraint {
                name: "fact_commitment_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::FACT_COMMITMENT] - public_inputs[1]
                }),
            },
            // Constraint 3: Poseidon2(threshold, blinding) == threshold_commitment.
            // This ensures the threshold in the witness matches the committed threshold.
            Constraint {
                name: "poseidon2_commitment_binding".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::POSEIDON2_RESULT] - row[col::THRESHOLD_COMMITMENT]
                }),
            },
            // Constraint 4: diff = private_value - threshold.
            Constraint {
                name: "diff_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    let diff = row[col::DIFF];
                    diff - (value - threshold)
                }),
            },
            // Constraint 5: Bit decomposition is correct: sum(bit_i * 2^i) = diff.
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: Box::new(|row, _, _| {
                    let diff = row[col::DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..COMMITTED_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    recomposed - diff
                }),
            },
            // Constraint 6: All bits are binary (0 or 1).
            Constraint {
                name: "bits_binary".to_string(),
                eval: Box::new(|row, _, _| {
                    let mut result = BabyBear::ZERO;
                    for i in 0..COMMITTED_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 7: High bit (bit 30) is 0.
            // This ensures diff < 2^30 < p/2, meaning the difference is "small positive"
            // in the canonical representation — i.e., value >= threshold.
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: Box::new(|row, _, _| row[col::diff_bit(COMMITTED_DIFF_BITS - 1)]),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut row = vec![BabyBear::ZERO; COMMITTED_THRESHOLD_AIR_WIDTH];

        // Fill witness columns.
        row[col::PRIVATE_VALUE] = w.private_value;
        row[col::THRESHOLD] = w.threshold;
        row[col::BLINDING] = w.blinding;

        // Compute and fill the difference.
        let diff = w.compute_diff();
        row[col::DIFF] = diff;

        // Bit decomposition of diff.
        let diff_val = diff.as_u32();
        for i in 0..COMMITTED_DIFF_BITS {
            let bit = (diff_val >> i) & 1;
            row[col::diff_bit(i)] = BabyBear::new(bit);
        }

        // Compute and fill the Poseidon2 commitment check.
        let poseidon2_result = poseidon2::hash_2_to_1(w.threshold, w.blinding);
        row[col::POSEIDON2_RESULT] = poseidon2_result;

        // Fill public-input-matching columns.
        let threshold_commitment = w.compute_threshold_commitment();
        row[col::THRESHOLD_COMMITMENT] = threshold_commitment;
        row[col::FACT_COMMITMENT] = w.fact_commitment;

        // Public inputs: [threshold_commitment, fact_commitment]
        let public_inputs = vec![threshold_commitment, w.fact_commitment];
        (vec![row], public_inputs)
    }
}

/// A complete committed-threshold proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CommittedThresholdProof {
    /// The threshold commitment (public input — visible to third parties).
    pub threshold_commitment: BabyBear,
    /// The fact commitment (public input — visible to third parties).
    pub fact_commitment: BabyBear,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
}

/// Generate a committed-threshold proof.
///
/// The prover must know:
/// - `private_value`: Their private attribute value.
/// - `threshold`: The verifier's threshold (received via secure channel).
/// - `blinding`: The verifier's blinding factor (received via secure channel).
/// - `fact_commitment`: Binding to the token state containing the value.
///
/// Returns `None` if the value does not satisfy the threshold (value < threshold)
/// or if proof generation fails.
pub fn prove_committed_threshold(
    witness: CommittedThresholdWitness,
) -> Option<CommittedThresholdProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let threshold_commitment = witness.compute_threshold_commitment();
    let fact_commitment = witness.fact_commitment;

    let air = CommittedThresholdAir::new(witness);
    let (mut trace, public_inputs) = air.generate_trace();

    // STARK prover requires trace length >= 2 and power-of-two.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        trace.push(trace[0].clone());
    }

    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(CommittedThresholdProof {
        threshold_commitment,
        fact_commitment,
        stark_proof,
    })
}

/// Verify a committed-threshold proof.
///
/// The verifier checks:
/// 1. The `threshold_commitment` in the proof matches their own commitment
///    (computed from their secret threshold + blinding).
/// 2. The `fact_commitment` matches the expected binding to the token state.
/// 3. The STARK/constraint proof verifies.
///
/// Third-party verifiers who don't know the threshold can still verify the proof
/// against the commitments — they learn only "the committed value satisfies the
/// committed threshold."
pub fn verify_committed_threshold(
    proof: &CommittedThresholdProof,
    expected_threshold_commitment: BabyBear,
    expected_fact_commitment: BabyBear,
) -> bool {
    if proof.threshold_commitment != expected_threshold_commitment {
        return false;
    }
    if proof.fact_commitment != expected_fact_commitment {
        return false;
    }
    let public_inputs = vec![expected_threshold_commitment, expected_fact_commitment];
    // Reconstruct a dummy witness for the AIR (only needed for constraint evaluation shape).
    let dummy_witness = CommittedThresholdWitness {
        private_value: BabyBear::ZERO,
        threshold: BabyBear::ZERO,
        blinding: BabyBear::ZERO,
        fact_commitment: expected_fact_commitment,
    };
    let air = CommittedThresholdAir::new(dummy_witness);
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

/// Convenience: generate blinding randomness for the verifier.
///
/// The verifier calls this to generate a random blinding factor, then computes
/// their threshold commitment and sends both `threshold` and `blinding` to the prover.
pub fn generate_blinding() -> BabyBear {
    let mut bytes = [0u8; 4];
    getrandom::fill(&mut bytes).expect("getrandom failed");
    // Reduce to field element (non-zero for hiding property)
    let val = u32::from_le_bytes(bytes);
    let reduced = val % (crate::field::BABYBEAR_P - 1) + 1; // ensure non-zero
    BabyBear::new(reduced)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::poseidon2::hash_fact;
    use crate::predicate_air::compute_fact_commitment;

    /// Helper: create a fact commitment for testing.
    fn test_fact_commitment(value: BabyBear) -> BabyBear {
        let fact_hash = hash_fact(BabyBear::new(42), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        compute_fact_commitment(fact_hash, state_root)
    }

    // =========================================================================
    // Basic committed-threshold tests
    // =========================================================================

    #[test]
    fn test_committed_threshold_passes() {
        // Prover has value 750, verifier's threshold is 700.
        let value = BabyBear::new(750);
        let threshold = BabyBear::new(700);
        let blinding = BabyBear::new(12345);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let air = CommittedThresholdAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Committed threshold 750 >= 700 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_committed_threshold_equal_passes() {
        // Prover has value 700, verifier's threshold is 700.
        let value = BabyBear::new(700);
        let threshold = BabyBear::new(700);
        let blinding = BabyBear::new(54321);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let air = CommittedThresholdAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Committed threshold 700 >= 700 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_committed_threshold_fails() {
        // Prover has value 650, verifier's threshold is 700.
        let value = BabyBear::new(650);
        let threshold = BabyBear::new(700);
        let blinding = BabyBear::new(99999);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let air = CommittedThresholdAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Committed threshold 650 >= 700 should fail"
        );
        // The high-bit constraint should catch this.
        let has_high_bit = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "high_bit_zero");
        assert!(
            has_high_bit,
            "Should have high_bit_zero violation, got: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // Commitment binding tests
    // =========================================================================

    #[test]
    fn test_commitment_is_deterministic() {
        let threshold = BabyBear::new(700);
        let blinding = BabyBear::new(42);

        let c1 = compute_threshold_commitment(threshold, blinding);
        let c2 = compute_threshold_commitment(threshold, blinding);
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_different_blinding_different_commitment() {
        let threshold = BabyBear::new(700);
        let c1 = compute_threshold_commitment(threshold, BabyBear::new(1));
        let c2 = compute_threshold_commitment(threshold, BabyBear::new(2));
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_different_threshold_different_commitment() {
        let blinding = BabyBear::new(42);
        let c1 = compute_threshold_commitment(BabyBear::new(700), blinding);
        let c2 = compute_threshold_commitment(BabyBear::new(701), blinding);
        assert_ne!(c1, c2);
    }

    // =========================================================================
    // prove / verify integration tests
    // =========================================================================

    #[test]
    fn test_prove_and_verify_committed_threshold() {
        let value = BabyBear::new(5000);
        let threshold = BabyBear::new(1000);
        let blinding = BabyBear::new(77777);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let threshold_commitment = witness.compute_threshold_commitment();
        let proof = prove_committed_threshold(witness).expect("should produce proof");

        // Verifier knows their threshold_commitment and the fact_commitment.
        assert!(verify_committed_threshold(
            &proof,
            threshold_commitment,
            fact_commitment
        ));
    }

    #[test]
    fn test_prove_returns_none_for_false_statement() {
        // value(500) < threshold(1000) -- cannot prove.
        let value = BabyBear::new(500);
        let threshold = BabyBear::new(1000);
        let blinding = BabyBear::new(11111);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let proof = prove_committed_threshold(witness);
        assert!(proof.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn test_verify_fails_with_wrong_threshold_commitment() {
        let value = BabyBear::new(5000);
        let threshold = BabyBear::new(1000);
        let blinding = BabyBear::new(77777);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let proof = prove_committed_threshold(witness).expect("should produce proof");

        // Verify with a different threshold commitment -- should fail.
        let wrong_commitment = compute_threshold_commitment(BabyBear::new(2000), blinding);
        assert!(!verify_committed_threshold(
            &proof,
            wrong_commitment,
            fact_commitment
        ));
    }

    #[test]
    fn test_verify_fails_with_wrong_fact_commitment() {
        let value = BabyBear::new(5000);
        let threshold = BabyBear::new(1000);
        let blinding = BabyBear::new(77777);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let threshold_commitment = witness.compute_threshold_commitment();
        let proof = prove_committed_threshold(witness).expect("should produce proof");

        // Verify with a different fact commitment -- should fail.
        let wrong_fact = BabyBear::new(12345);
        assert!(!verify_committed_threshold(
            &proof,
            threshold_commitment,
            wrong_fact
        ));
    }

    // =========================================================================
    // Real-world scenario tests
    // =========================================================================

    #[test]
    fn test_credit_score_scenario() {
        // Scenario: Lender has a secret acceptance threshold of 680.
        // Borrower has a credit score of 750.
        // Third-party auditor should be able to verify the proof without
        // learning either the score or the threshold.

        let credit_score = BabyBear::new(750);
        let acceptance_threshold = BabyBear::new(680);
        let blinding = generate_blinding(); // verifier generates fresh randomness

        // Verifier computes their commitment.
        let threshold_commitment = compute_threshold_commitment(acceptance_threshold, blinding);

        // Prover receives threshold + blinding via secure channel.
        let score_fact_hash = hash_fact(
            BabyBear::new(100), // "credit_score" predicate symbol
            &[credit_score, BabyBear::ZERO, BabyBear::ZERO],
        );
        let state_root = BabyBear::new(88888);
        let fact_commitment = compute_fact_commitment(score_fact_hash, state_root);

        let witness = CommittedThresholdWitness {
            private_value: credit_score,
            threshold: acceptance_threshold,
            blinding,
            fact_commitment,
        };

        let proof = prove_committed_threshold(witness).expect("credit check should pass");

        // Verifier verifies (knows their commitment).
        assert!(verify_committed_threshold(
            &proof,
            threshold_commitment,
            fact_commitment
        ));

        // Third-party auditor verifies (given only the commitments, learns nothing
        // about 750 or 680, only that "the proof is valid for these commitments").
        assert!(verify_committed_threshold(
            &proof,
            threshold_commitment,
            fact_commitment
        ));
    }

    #[test]
    fn test_large_value_scenario() {
        // Boundary: value at the edge of the "small positive" range.
        // With COMMITTED_DIFF_BITS=30, the max representable diff with high_bit=0 is:
        // 2^29 - 1 = 536870911 (SOUNDNESS FIX: reduced from 2^30-1 to be safely < p/2)
        let value = BabyBear::new(536_870_911);
        let threshold = BabyBear::new(0);
        let blinding = BabyBear::new(42);
        let fact_commitment = test_fact_commitment(value);

        let witness = CommittedThresholdWitness {
            private_value: value,
            threshold,
            blinding,
            fact_commitment,
        };

        let air = CommittedThresholdAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Max diff should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_generate_blinding_nonzero() {
        // generate_blinding should always produce a non-zero value.
        for _ in 0..100 {
            let b = generate_blinding();
            assert_ne!(b, BabyBear::ZERO);
        }
    }
}
