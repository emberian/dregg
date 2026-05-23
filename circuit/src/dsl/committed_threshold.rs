//! DSL-native committed-threshold predicate proving and verification.
//!
//! This module provides a DSL `CircuitDescriptor` equivalent of the hand-written
//! `CommittedThresholdAir` from `circuit/src/committed_threshold.rs`.
//!
//! # Constraints
//!
//! 1. `threshold_commitment == pi[0]` (boundary)
//! 2. `fact_commitment == pi[1]` (boundary)
//! 3. `poseidon2_result == hash_2_to_1(threshold, blinding)` (Hash2to1 constraint)
//! 4. `poseidon2_result == threshold_commitment` (equality)
//! 5. `diff == private_value - threshold` (polynomial)
//! 6. Bit decomposition: `sum(diff_bit[i] * 2^i) == diff` (polynomial)
//! 7. Each diff_bit is binary (Binary constraint)
//! 8. High bit (bit 29) is zero (boundary: fixed value 0)
//!
//! # Public Inputs
//!
//! `[threshold_commitment, fact_commitment]`

use crate::committed_threshold::{
    COMMITTED_DIFF_BITS, COMMITTED_THRESHOLD_AIR_WIDTH, CommittedThresholdWitness, col,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2;
use crate::stark;

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Re-exports
// ============================================================================

pub use crate::committed_threshold::{
    COMMITTED_DIFF_BITS as DSL_COMMITTED_DIFF_BITS,
    COMMITTED_THRESHOLD_AIR_WIDTH as DSL_COMMITTED_THRESHOLD_WIDTH, CommittedThresholdProof,
    CommittedThresholdWitness as CommittedThresholdWitnessType, compute_threshold_commitment,
    generate_blinding,
};

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the production committed-threshold CircuitDescriptor.
///
/// This is the DSL equivalent of `CommittedThresholdAir`. All constraints are
/// encoded as `ConstraintExpr` variants that the `DslCircuit` interprets at runtime.
pub fn committed_threshold_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1: poseidon2_result == hash_2_to_1(threshold, blinding)
    constraints.push(ConstraintExpr::Hash2to1 {
        output_col: col::POSEIDON2_RESULT,
        input_col_a: col::THRESHOLD,
        input_col_b: col::BLINDING,
    });

    // C2: poseidon2_result == threshold_commitment (equality)
    constraints.push(ConstraintExpr::Equality {
        col_a: col::POSEIDON2_RESULT,
        col_b: col::THRESHOLD_COMMITMENT,
    });

    // C3: diff == private_value - threshold
    // Expressed as: diff - private_value + threshold == 0
    let neg_one = BabyBear::new(BABYBEAR_P - 1);
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::DIFF],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![col::PRIVATE_VALUE],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::THRESHOLD],
            },
        ],
    });

    // C4: Bit decomposition: sum(diff_bit[i] * 2^i) - diff == 0
    // This is a polynomial with 31 terms (30 bit terms + 1 diff term).
    {
        let mut terms = Vec::with_capacity(COMMITTED_DIFF_BITS + 1);
        let mut power_of_two = BabyBear::ONE;
        for i in 0..COMMITTED_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![col::diff_bit(i)],
            });
            power_of_two = power_of_two + power_of_two; // 2^(i+1)
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![col::DIFF],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // C5: Each diff_bit is binary (0 or 1)
    for i in 0..COMMITTED_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: col::diff_bit(i),
        });
    }

    // Boundary constraints
    let boundaries = vec![
        // Row 0: threshold_commitment == pi[0]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::THRESHOLD_COMMITMENT,
            pi_index: 0,
        },
        // Row 0: fact_commitment == pi[1]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::FACT_COMMITMENT,
            pi_index: 1,
        },
        // Row 0: high bit (bit 29) must be zero — enforces value >= threshold
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::diff_bit(COMMITTED_DIFF_BITS - 1),
            value: BabyBear::ZERO,
        },
    ];

    // Column definitions
    let columns = vec![
        ColumnDef {
            name: "private_value".into(),
            index: col::PRIVATE_VALUE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "threshold".into(),
            index: col::THRESHOLD,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "blinding".into(),
            index: col::BLINDING,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff".into(),
            index: col::DIFF,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "threshold_commitment".into(),
            index: col::THRESHOLD_COMMITMENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "fact_commitment".into(),
            index: col::FACT_COMMITMENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "poseidon2_result".into(),
            index: col::POSEIDON2_RESULT,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "pyana-committed-threshold-dsl-v1".to_string(),
        trace_width: COMMITTED_THRESHOLD_AIR_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Build the DSL circuit for committed-threshold verification.
pub fn committed_threshold_dsl_circuit() -> DslCircuit {
    DslCircuit::new(committed_threshold_circuit_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate the DSL trace from a `CommittedThresholdWitness`.
///
/// Returns (trace, public_inputs) where trace is padded to power-of-2 length.
pub fn generate_committed_threshold_trace(
    witness: &CommittedThresholdWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; COMMITTED_THRESHOLD_AIR_WIDTH];

    // Fill witness columns
    row[col::PRIVATE_VALUE] = witness.private_value;
    row[col::THRESHOLD] = witness.threshold;
    row[col::BLINDING] = witness.blinding;

    // Compute diff
    let diff = witness.private_value - witness.threshold;
    row[col::DIFF] = diff;

    // Bit decomposition
    let diff_val = diff.as_u32();
    for i in 0..COMMITTED_DIFF_BITS {
        let bit = (diff_val >> i) & 1;
        row[col::diff_bit(i)] = BabyBear::new(bit);
    }

    // Poseidon2 commitment
    let poseidon2_result = poseidon2::hash_2_to_1(witness.threshold, witness.blinding);
    row[col::POSEIDON2_RESULT] = poseidon2_result;

    // Public-input-matching columns
    let threshold_commitment = witness.compute_threshold_commitment();
    row[col::THRESHOLD_COMMITMENT] = threshold_commitment;
    row[col::FACT_COMMITMENT] = witness.fact_commitment;

    let public_inputs = vec![threshold_commitment, witness.fact_commitment];

    // Pad to power of 2 (min 2 rows for STARK)
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a DSL-native committed-threshold STARK proof.
///
/// Returns `None` if the value does not satisfy the threshold (value < threshold).
pub fn prove_committed_threshold_dsl(
    witness: &CommittedThresholdWitness,
) -> Option<CommittedThresholdProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let threshold_commitment = witness.compute_threshold_commitment();
    let fact_commitment = witness.fact_commitment;

    let circuit = committed_threshold_dsl_circuit();
    let (trace, public_inputs) = generate_committed_threshold_trace(witness);
    let stark_proof = stark::prove(&circuit, &trace, &public_inputs);

    Some(CommittedThresholdProof {
        threshold_commitment,
        fact_commitment,
        stark_proof,
    })
}

/// Verify a DSL-native committed-threshold STARK proof.
pub fn verify_committed_threshold_dsl(
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
    let circuit = committed_threshold_dsl_circuit();
    stark::verify(&circuit, &proof.stark_proof, &public_inputs).is_ok()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_fact;
    use crate::predicate_air::compute_fact_commitment;

    fn test_fact_commitment(value: BabyBear) -> BabyBear {
        let fact_hash = hash_fact(BabyBear::new(42), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        compute_fact_commitment(fact_hash, state_root)
    }

    #[test]
    fn dsl_committed_threshold_passes() {
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

        let proof = prove_committed_threshold_dsl(&witness).expect("should produce proof");
        let threshold_commitment = witness.compute_threshold_commitment();
        assert!(verify_committed_threshold_dsl(
            &proof,
            threshold_commitment,
            fact_commitment
        ));
    }

    #[test]
    fn dsl_committed_threshold_fails_for_false() {
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

        let proof = prove_committed_threshold_dsl(&witness);
        assert!(proof.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn dsl_committed_threshold_wrong_commitment_rejected() {
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

        let proof = prove_committed_threshold_dsl(&witness).expect("should produce proof");
        let wrong_commitment = compute_threshold_commitment(BabyBear::new(2000), blinding);
        assert!(!verify_committed_threshold_dsl(
            &proof,
            wrong_commitment,
            fact_commitment
        ));
    }
}
