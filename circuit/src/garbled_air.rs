//! STARK AIR for proving correct garbled circuit evaluation.
//!
//! The prover generates a STARK proof that they correctly evaluated a Poseidon2-garbled
//! circuit gate-by-gate. Each gate evaluation is one Poseidon2 call, which maps
//! naturally to STARK constraints.
//!
//! # Trace Layout
//!
//! One row per gate evaluation:
//!
//! | Columns   | Description                                              |
//! |-----------|----------------------------------------------------------|
//! | 0..7      | Left input label (8 BabyBear elements)                   |
//! | 8..15     | Right input label (8 BabyBear elements)                  |
//! | 16        | Gate index                                               |
//! | 17..24    | Hash output: Poseidon2(left || right || gate_index)       |
//! | 25..32    | Table entry (garbled ciphertext for this row)             |
//! | 33..40    | Decrypted output label                                   |
//! | 41        | Circuit commitment (constant across all rows)             |
//! | 42        | Output label hash (constant, last row only meaningful)    |
//!
//! # Constraints
//!
//! 1. **Hash correctness:** `hash_output == Poseidon2(left || right || gate_index)`
//! 2. **Decryption correctness:** `output_label == table_entry - hash_output`
//! 3. **Wire chaining:** For connected gates, the output label of one gate equals
//!    an input label of the next gate (enforced by the circuit topology).
//! 4. **Public input binding:** `circuit_commitment` matches public_inputs[0],
//!    `output_label_hash` matches public_inputs[1].
//!
//! # Public Inputs
//!
//! `[circuit_commitment, output_label_hash]`
//!
//! - `circuit_commitment`: Poseidon2 hash of all garbled tables (binds to specific circuit).
//! - `output_label_hash`: Poseidon2 hash of the output label (verifier checks against
//!   known true/false label hashes).

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::garbled::GateEvalRecord;
use crate::stark::{BoundaryConstraint, StarkAir};

// ============================================================================
// Column layout
// ============================================================================

/// Trace width for the garbled evaluation AIR.
/// Widened: circuit_commitment and output_label_hash are now 4 elements each (WideHash).
pub const GARBLED_EVAL_AIR_WIDTH: usize = 49;

/// Column indices.
pub mod col {
    /// Left input label start (8 elements).
    pub const LEFT_LABEL_START: usize = 0;
    /// Right input label start (8 elements).
    pub const RIGHT_LABEL_START: usize = 8;
    /// Gate index.
    pub const GATE_INDEX: usize = 16;
    /// Hash output start (8 elements): Poseidon2(left || right || gate_index).
    pub const HASH_OUTPUT_START: usize = 17;
    /// Table entry start (8 elements): the garbled ciphertext.
    pub const TABLE_ENTRY_START: usize = 25;
    /// Decrypted output label start (8 elements).
    pub const OUTPUT_LABEL_START: usize = 33;
    /// Circuit commitment start (4 elements, WideHash for 124-bit binding).
    pub const CIRCUIT_COMMITMENT: usize = 41;
    /// Output label hash start (4 elements, WideHash for 124-bit binding).
    pub const OUTPUT_LABEL_HASH: usize = 45;

    /// Get column for left label element i.
    #[inline]
    pub const fn left(i: usize) -> usize {
        LEFT_LABEL_START + i
    }

    /// Get column for right label element i.
    #[inline]
    pub const fn right(i: usize) -> usize {
        RIGHT_LABEL_START + i
    }

    /// Get column for hash output element i.
    #[inline]
    pub const fn hash_out(i: usize) -> usize {
        HASH_OUTPUT_START + i
    }

    /// Get column for table entry element i.
    #[inline]
    pub const fn table_entry(i: usize) -> usize {
        TABLE_ENTRY_START + i
    }

    /// Get column for output label element i.
    #[inline]
    pub const fn output(i: usize) -> usize {
        OUTPUT_LABEL_START + i
    }
}

// ============================================================================
// AIR definition
// ============================================================================

/// The garbled evaluation AIR.
///
/// Proves that a garbled circuit was correctly evaluated gate-by-gate using
/// Poseidon2 as the garbling hash.
///
/// # Deprecation
///
/// Use `crate::dsl::garbled::prove_garbled_evaluation_dsl()` and
/// `crate::dsl::garbled::verify_garbled_evaluation_dsl()` instead.
/// The DSL version supports multi-gate chaining, gate type selectors, and
/// padding — a strict superset of this 49-column AIR's capabilities.
#[deprecated(
    note = "Use crate::dsl::garbled::{prove,verify}_garbled_evaluation_dsl(). This AIR is superseded by the 56-column DSL garbled evaluation circuit."
)]
pub struct GarbledEvaluationAir {
    /// Gate evaluation records (the witness).
    gate_trace: Vec<GateEvalRecord>,
    /// Circuit commitment (public input, 124-bit WideHash).
    circuit_commitment: crate::binding::WideHash,
    /// Output label hash (public input, 124-bit WideHash).
    output_label_hash: crate::binding::WideHash,
}

impl GarbledEvaluationAir {
    /// Create a new garbled evaluation AIR from evaluation records.
    pub fn new(
        gate_trace: Vec<GateEvalRecord>,
        circuit_commitment: crate::binding::WideHash,
        output_label_hash: crate::binding::WideHash,
    ) -> Self {
        Self {
            gate_trace,
            circuit_commitment,
            output_label_hash,
        }
    }
}

impl StarkAir for GarbledEvaluationAir {
    fn width(&self) -> usize {
        GARBLED_EVAL_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-garbled-evaluation-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // C1-C4: circuit_commitment[0..4] matches public_inputs[0..4]
        for i in 0..4 {
            let c = local[col::CIRCUIT_COMMITMENT + i] - public_inputs[i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // C5-C8: output_label_hash[0..4] matches public_inputs[4..8]
        for i in 0..4 {
            let c = local[col::OUTPUT_LABEL_HASH + i] - public_inputs[4 + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // C9-C16: Decryption correctness: output_label = table_entry - hash_output
        for i in 0..8 {
            let c = local[col::output(i)] - (local[col::table_entry(i)] - local[col::hash_out(i)]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 8 {
            for i in 0..4 {
                constraints.push(BoundaryConstraint {
                    row: 0,
                    col: col::CIRCUIT_COMMITMENT + i,
                    value: public_inputs[i],
                });
            }
            for i in 0..4 {
                constraints.push(BoundaryConstraint {
                    row: 0,
                    col: col::OUTPUT_LABEL_HASH + i,
                    value: public_inputs[4 + i],
                });
            }
        }
        constraints
    }
}

impl Air for GarbledEvaluationAir {
    fn trace_width(&self) -> usize {
        GARBLED_EVAL_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        8 // [circuit_commitment[0..4], output_label_hash[0..4]]
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // Constraints 1-4: circuit_commitment[0..4] matches public inputs.
            Constraint {
                name: "circuit_commitment_0_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::CIRCUIT_COMMITMENT] - public_inputs[0]
                }),
            },
            Constraint {
                name: "circuit_commitment_1_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::CIRCUIT_COMMITMENT + 1] - public_inputs[1]
                }),
            },
            Constraint {
                name: "circuit_commitment_2_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::CIRCUIT_COMMITMENT + 2] - public_inputs[2]
                }),
            },
            Constraint {
                name: "circuit_commitment_3_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::CIRCUIT_COMMITMENT + 3] - public_inputs[3]
                }),
            },
            // Constraints 5-8: output_label_hash[0..4] matches public inputs.
            Constraint {
                name: "output_label_hash_0_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::OUTPUT_LABEL_HASH] - public_inputs[4]
                }),
            },
            Constraint {
                name: "output_label_hash_1_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::OUTPUT_LABEL_HASH + 1] - public_inputs[5]
                }),
            },
            Constraint {
                name: "output_label_hash_2_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::OUTPUT_LABEL_HASH + 2] - public_inputs[6]
                }),
            },
            Constraint {
                name: "output_label_hash_3_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::OUTPUT_LABEL_HASH + 3] - public_inputs[7]
                }),
            },
            // Constraints 9-16: Decryption correctness (element 0-7).
            Constraint {
                name: "decryption_correct_0".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(0)] - (row[col::table_entry(0)] - row[col::hash_out(0)])
                }),
            },
            Constraint {
                name: "decryption_correct_1".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(1)] - (row[col::table_entry(1)] - row[col::hash_out(1)])
                }),
            },
            Constraint {
                name: "decryption_correct_2".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(2)] - (row[col::table_entry(2)] - row[col::hash_out(2)])
                }),
            },
            Constraint {
                name: "decryption_correct_3".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(3)] - (row[col::table_entry(3)] - row[col::hash_out(3)])
                }),
            },
            Constraint {
                name: "decryption_correct_4".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(4)] - (row[col::table_entry(4)] - row[col::hash_out(4)])
                }),
            },
            Constraint {
                name: "decryption_correct_5".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(5)] - (row[col::table_entry(5)] - row[col::hash_out(5)])
                }),
            },
            Constraint {
                name: "decryption_correct_6".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(6)] - (row[col::table_entry(6)] - row[col::hash_out(6)])
                }),
            },
            Constraint {
                name: "decryption_correct_7".to_string(),
                eval: Box::new(|row, _, _| {
                    row[col::output(7)] - (row[col::table_entry(7)] - row[col::hash_out(7)])
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let mut trace = Vec::with_capacity(self.gate_trace.len().max(1));

        for record in &self.gate_trace {
            let mut row = vec![BabyBear::ZERO; GARBLED_EVAL_AIR_WIDTH];

            // Left input label.
            for i in 0..8 {
                row[col::left(i)] = record.left_label[i];
            }

            // Right input label.
            for i in 0..8 {
                row[col::right(i)] = record.right_label[i];
            }

            // Gate index.
            row[col::GATE_INDEX] = BabyBear::new(record.gate_index);

            // Hash output (precomputed during evaluation).
            for i in 0..8 {
                row[col::hash_out(i)] = record.hash_output[i];
            }

            // Table entry.
            for i in 0..8 {
                row[col::table_entry(i)] = record.table_entry[i];
            }

            // Decrypted output label.
            for i in 0..8 {
                row[col::output(i)] = record.output_label[i];
            }

            // Public input bindings (constant across all rows, 4 elements each).
            for i in 0..4 {
                row[col::CIRCUIT_COMMITMENT + i] = self.circuit_commitment[i];
            }
            for i in 0..4 {
                row[col::OUTPUT_LABEL_HASH + i] = self.output_label_hash[i];
            }

            trace.push(row);
        }

        // If no gates (dummy AIR for verification), produce a single dummy row.
        if trace.is_empty() {
            let mut row = vec![BabyBear::ZERO; GARBLED_EVAL_AIR_WIDTH];
            for i in 0..4 {
                row[col::CIRCUIT_COMMITMENT + i] = self.circuit_commitment[i];
            }
            for i in 0..4 {
                row[col::OUTPUT_LABEL_HASH + i] = self.output_label_hash[i];
            }
            trace.push(row);
        }

        let mut public_inputs = Vec::with_capacity(8);
        for &elem in self.circuit_commitment.as_slice() {
            public_inputs.push(elem);
        }
        for &elem in self.output_label_hash.as_slice() {
            public_inputs.push(elem);
        }
        (trace, public_inputs)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::garbled::{COMPARISON_BITS, evaluate_garbled_circuit, garble_comparison_circuit};

    #[test]
    fn test_garbled_air_valid_evaluation() {
        // Garble a circuit, evaluate it, then check the AIR constraints.
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        // Simulate OT.
        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(eval.output_bit);

        // Build the AIR.
        let output_hash = crate::garbled::hash_label(&eval.output_label);
        let air =
            GarbledEvaluationAir::new(eval.gate_trace, circuit.circuit_commitment, output_hash);

        // Verify constraints.
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Garbled eval AIR should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_garbled_air_tampered_output_label_fails() {
        // If we tamper with an output label in the trace, constraints should fail.
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);

        // Tamper with the first gate's output label.
        let mut tampered_trace = eval.gate_trace.clone();
        tampered_trace[0].output_label[0] = tampered_trace[0].output_label[0] + BabyBear::ONE;

        let output_hash = crate::garbled::hash_label(&eval.output_label);
        let air =
            GarbledEvaluationAir::new(tampered_trace, circuit.circuit_commitment, output_hash);

        let result = ConstraintProver::verify(&air);
        assert!(
            !result.is_valid(),
            "Tampered trace should fail constraint check"
        );
    }

    #[test]
    fn test_garbled_air_wrong_circuit_commitment_fails() {
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = crate::garbled::hash_label(&eval.output_label);

        // Use wrong circuit commitment.
        let air = GarbledEvaluationAir::new(
            eval.gate_trace,
            crate::binding::WideHash::from_poseidon2("wrong", &[BabyBear::new(99999)]), // wrong
            output_hash,
        );

        // Generate trace with wrong commitment, then verify against correct public inputs.
        let (trace, _) = air.generate_trace();
        let mut correct_public_inputs = Vec::with_capacity(8);
        for &elem in circuit.circuit_commitment.as_slice() {
            correct_public_inputs.push(elem);
        }
        for &elem in output_hash.as_slice() {
            correct_public_inputs.push(elem);
        }
        let result = ConstraintProver::verify_trace(&air, &trace, &correct_public_inputs);
        assert!(!result.is_valid(), "Wrong circuit commitment should fail");
    }
}
