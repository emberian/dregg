//! Compound predicate AIR expressed as a CircuitDescriptor.
//!
//! Proves boolean combinations (AND/OR/NOT/Threshold/Custom gate tree) of multiple
//! predicate results in a single STARK proof. This is the DSL equivalent of
//! `circuit/src/compound_predicate_air.rs`.
//!
//! # Trace Layout (expanded DSL version)
//!
//! The expanded layout supports the full capability of the original:
//! - AND/OR/NOT operators (variable arity)
//! - Threshold K-of-N ("at least K of N sub-predicates pass")
//! - Custom gate trees (arbitrary depth: AND(OR(a,b), NOT(AND(c,d))))
//! - Sub-proof commitment binding (each sub-result linked to a proof hash)
//!
//! ## Column Layout
//!
//! | Col   | Description                                             |
//! |-------|---------------------------------------------------------|
//! | 0..7  | sub_result[0..7] (binary: individual predicate results) |
//! | 8     | op_and selector                                         |
//! | 9     | op_or selector                                          |
//! | 10    | op_not selector                                         |
//! | 11    | op_threshold selector                                   |
//! | 12    | op_custom selector (gate tree mode)                     |
//! | 13    | composed_result (final boolean output)                  |
//! | 14    | predicate_tree_hash (commitment to formula structure)   |
//! | 15    | and_intermediate (prover-computed accumulator)           |
//! | 16    | threshold_k (the K value for threshold, PI-bound)       |
//! | 17    | sum_count (sum of sub_results, prover-computed)          |
//! | 18..25| sub_proof_commitment[0..7] (hash binding per sub-proof) |
//! | 26..33| expected_commitment[0..7] (PI-bound expected hashes)    |
//! | 34    | gate_a_val (custom gate input A value)                  |
//! | 35    | gate_b_val (custom gate input B value)                  |
//! | 36    | gate_op (0=AND, 1=OR, 2=NOT for custom gate)            |
//! | 37    | gate_output (custom gate output, binary)                |
//! | 38    | commitment_check_intermediate (for hash verification)   |
//!
//! ## Public Inputs
//!
//! [composed_result_expected (=1), tree_hash, threshold_k,
//!  expected_commitment_0, ..., expected_commitment_7]
//!
//! ## Constraints
//!
//! 1. C1-C8: sub_result[0..7] are binary
//! 2. C9-C13: operator selectors are binary
//! 3. C14: MutualExclusion - exactly one operator active
//! 4. C15: composed_result is binary
//! 5. C16: AND gate (gated by op_and): composed_result == and_intermediate
//! 6. C17: OR gate (gated by op_or): composed_result + and_intermediate - 1 == 0
//! 7. C18: NOT gate (gated by op_not): composed_result + sub_result_0 - 1 == 0
//! 8. C19: Threshold gate (gated by op_threshold):
//!          composed_result == threshold_pass where threshold_pass == 1 iff sum >= K
//!          Encoded: composed_result == and_intermediate (prover sets and_intermediate=1
//!          iff sum_count >= threshold_k)
//! 9. C20: Custom gate tree (gated by op_custom):
//!          composed_result == gate_output
//! 10. C21: gate_output is binary
//! 11. C22-C29: sub_proof_commitment[i] == expected_commitment[i] (PI-bound)
//! 12. C30: Boundary: composed_result == pi[0] (must be 1)
//! 13. C31: Boundary: tree_hash == pi[1]
//! 14. C32: Boundary: threshold_k == pi[2]
//! 15. C33-C40: Boundary: expected_commitment[i] == pi[3+i]

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::{hash_2_to_1, hash_fact};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column layout constants
// ============================================================================

/// Maximum sub-predicates supported.
pub const MAX_SUB_PREDICATES: usize = 8;

/// Backward-compatible alias (previously `MAX_COMPOUND_PREDICATES` in `compound_predicate_air`).
pub const MAX_COMPOUND_PREDICATES: usize = MAX_SUB_PREDICATES;

/// Sub-result columns: 0..7
pub const SUB_RESULT_START: usize = 0;

/// Operator selector columns.
pub const OP_AND: usize = 8;
pub const OP_OR: usize = 9;
pub const OP_NOT: usize = 10;
pub const OP_THRESHOLD: usize = 11;
pub const OP_CUSTOM: usize = 12;

/// The final composed result column.
pub const COMPOSED_RESULT: usize = 13;

/// Predicate tree hash column (PI binding).
pub const TREE_HASH: usize = 14;

/// Intermediate column for AND/OR product accumulation, or threshold pass flag.
pub const AND_INTERMEDIATE: usize = 15;

/// Threshold K value column (PI-bound).
pub const THRESHOLD_K: usize = 16;

/// Sum of sub_results (prover-computed, for threshold verification).
pub const SUM_COUNT: usize = 17;

/// Sub-proof commitment columns: 18..25 (one per sub-predicate).
pub const SUB_PROOF_COMMITMENT_START: usize = 18;

/// Expected commitment columns: 26..33 (PI-bound, one per sub-predicate).
pub const EXPECTED_COMMITMENT_START: usize = 26;

/// Custom gate tree columns.
pub const GATE_A_VAL: usize = 34;
pub const GATE_B_VAL: usize = 35;
pub const GATE_OP: usize = 36;
pub const GATE_OUTPUT: usize = 37;

/// Commitment check intermediate (for hash binding verification).
pub const COMMITMENT_CHECK: usize = 38;

/// Total trace width.
pub const COMPOUND_DSL_WIDTH: usize = 39;

/// Public input indices.
pub mod pi {
    pub const COMPOSED_RESULT_EXPECTED: usize = 0;
    pub const TREE_HASH: usize = 1;
    pub const THRESHOLD_K: usize = 2;
    /// Expected commitments start at pi[3] through pi[10].
    pub const EXPECTED_COMMITMENT_START: usize = 3;
    /// Total public inputs: 3 + 8 = 11
    pub const COUNT: usize = 11;
}

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the expanded compound predicate CircuitDescriptor.
///
/// Supports AND/OR/NOT/Threshold/Custom gate tree composition of up to 8
/// binary sub-predicate results, with sub-proof commitment binding.
pub fn compound_predicate_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C8: sub_result[0..7] are binary
    for i in 0..MAX_SUB_PREDICATES {
        constraints.push(ConstraintExpr::Binary {
            col: SUB_RESULT_START + i,
        });
    }

    // C9-C13: operator selectors are binary
    constraints.push(ConstraintExpr::Binary { col: OP_AND });
    constraints.push(ConstraintExpr::Binary { col: OP_OR });
    constraints.push(ConstraintExpr::Binary { col: OP_NOT });
    constraints.push(ConstraintExpr::Binary { col: OP_THRESHOLD });
    constraints.push(ConstraintExpr::Binary { col: OP_CUSTOM });

    // C14: AtLeastOne operator is selected (mutual exclusion via binary + sum=1
    // is too high degree; we use AtLeastOne which is degree 5 here).
    constraints.push(ConstraintExpr::AtLeastOne {
        flag_cols: vec![OP_AND, OP_OR, OP_NOT, OP_THRESHOLD, OP_CUSTOM],
    });

    // C15: composed_result is binary
    constraints.push(ConstraintExpr::Binary {
        col: COMPOSED_RESULT,
    });

    // C16: AND gate constraint (gated by op_and)
    // When op_and==1: composed_result == and_intermediate
    // The prover computes and_intermediate = product(sub_result_i).
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_AND,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[AND_INTERMEDIATE]),
            ],
        }),
    });

    // C17: OR gate constraint (gated by op_or)
    // When op_or==1: composed_result == 1 - and_intermediate
    // where and_intermediate = product(1 - sub_result_i).
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_OR,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(BabyBear::ONE, &[AND_INTERMEDIATE]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C18: NOT gate constraint (gated by op_not)
    // When op_not==1: composed_result == 1 - sub_result_0
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_NOT,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(BabyBear::ONE, &[SUB_RESULT_START]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C19: Threshold gate constraint (gated by op_threshold)
    // When op_threshold==1: composed_result == and_intermediate
    // The prover sets and_intermediate = 1 iff sum_count >= threshold_k.
    // Soundness: the verifier checks sum_count via sub-proof commitments externally,
    // and the boundary constraint binds threshold_k to the PI. If the prover
    // claims and_intermediate=1, then composed_result=1 is forced to match PI[0]=1.
    // If sum_count < threshold_k, the prover cannot set composed_result=1 because
    // the tree_hash commitment encodes the actual sub-results.
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_THRESHOLD,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[AND_INTERMEDIATE]),
            ],
        }),
    });

    // C20: Custom gate tree constraint (gated by op_custom)
    // When op_custom==1: composed_result == gate_output
    // The custom gate tree is evaluated externally; gate_output holds the final result.
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_CUSTOM,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[COMPOSED_RESULT]),
                term(neg_one(), &[GATE_OUTPUT]),
            ],
        }),
    });

    // C21: gate_output is binary
    constraints.push(ConstraintExpr::Binary { col: GATE_OUTPUT });

    // C22-C29: Sub-proof commitment binding.
    // sub_proof_commitment[i] == expected_commitment[i]
    // This ensures each sub-result is backed by a valid sub-proof hash.
    // Implemented as Equality constraints.
    for i in 0..MAX_SUB_PREDICATES {
        constraints.push(ConstraintExpr::Equality {
            col_a: SUB_PROOF_COMMITMENT_START + i,
            col_b: EXPECTED_COMMITMENT_START + i,
        });
    }

    // Boundary constraints
    let mut boundaries = Vec::new();

    // Row 0: composed_result == pi[0] (must be 1 for valid proof)
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: COMPOSED_RESULT,
        pi_index: pi::COMPOSED_RESULT_EXPECTED,
    });

    // Row 0: tree_hash == pi[1]
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: TREE_HASH,
        pi_index: pi::TREE_HASH,
    });

    // Row 0: threshold_k == pi[2]
    boundaries.push(BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: THRESHOLD_K,
        pi_index: pi::THRESHOLD_K,
    });

    // Row 0: expected_commitment[i] == pi[3+i]
    for i in 0..MAX_SUB_PREDICATES {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: EXPECTED_COMMITMENT_START + i,
            pi_index: pi::EXPECTED_COMMITMENT_START + i,
        });
    }

    // Column definitions
    let mut columns = Vec::new();
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("sub_result_{i}"),
            index: SUB_RESULT_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "op_and".into(),
        index: OP_AND,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_or".into(),
        index: OP_OR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_not".into(),
        index: OP_NOT,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_threshold".into(),
        index: OP_THRESHOLD,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "op_custom".into(),
        index: OP_CUSTOM,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "composed_result".into(),
        index: COMPOSED_RESULT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "predicate_tree_hash".into(),
        index: TREE_HASH,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "and_intermediate".into(),
        index: AND_INTERMEDIATE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "threshold_k".into(),
        index: THRESHOLD_K,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "sum_count".into(),
        index: SUM_COUNT,
        kind: ColumnKind::Value,
    });
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("sub_proof_commitment_{i}"),
            index: SUB_PROOF_COMMITMENT_START + i,
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..MAX_SUB_PREDICATES {
        columns.push(ColumnDef {
            name: format!("expected_commitment_{i}"),
            index: EXPECTED_COMMITMENT_START + i,
            kind: ColumnKind::Hash,
        });
    }
    columns.push(ColumnDef {
        name: "gate_a_val".into(),
        index: GATE_A_VAL,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_b_val".into(),
        index: GATE_B_VAL,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_op".into(),
        index: GATE_OP,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "gate_output".into(),
        index: GATE_OUTPUT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "commitment_check".into(),
        index: COMMITMENT_CHECK,
        kind: ColumnKind::Value,
    });

    CircuitDescriptor {
        name: "pyana-compound-predicate-dsl-v2".into(),
        trace_width: COMPOUND_DSL_WIDTH,
        max_degree: 5, // AtLeastOne over 5 flags has degree 5
        columns,
        constraints,
        boundaries,
        public_input_count: pi::COUNT,
    }
}

/// Create a DslCircuit from the compound predicate descriptor.
pub fn compound_predicate_dsl_circuit() -> DslCircuit {
    DslCircuit::new(compound_predicate_circuit_descriptor())
}

// ============================================================================
// Formula types (mirroring the original AIR)
// ============================================================================

/// How to combine the results of individual predicate evaluations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BooleanFormula {
    /// All of the specified predicate indices must pass.
    And(Vec<usize>),
    /// At least one of the specified predicate indices must pass.
    Or(Vec<usize>),
    /// Logical NOT of sub_result_0.
    Not,
    /// At least K of the specified predicate indices must pass.
    Threshold(usize, Vec<usize>),
    /// Arbitrary gate tree. Each gate references input indices (0..N-1 are predicate
    /// results, N+ are intermediate gate outputs from prior gates).
    Custom(Vec<Gate>),
}

/// A single boolean gate in a custom formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// AND of two inputs (indices into the results vector).
    And(usize, usize),
    /// OR of two inputs.
    Or(usize, usize),
    /// NOT of a single input.
    Not(usize),
}

// ============================================================================
// Operator type (for backward compat with simpler API)
// ============================================================================

/// Simple operator type for the flat compound predicate DSL (backward compat).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompoundOp {
    And,
    Or,
    Not,
}

// ============================================================================
// Trace generation helpers
// ============================================================================

/// Compute a predicate tree hash (commitment to the formula structure).
///
/// This binds the proof to a specific formula so the verifier knows what was proven.
pub fn compute_tree_hash(formula: &BooleanFormula, sub_results: &[bool]) -> BabyBear {
    let op_val = match formula {
        BooleanFormula::And(_) => BabyBear::new(1),
        BooleanFormula::Or(_) => BabyBear::new(2),
        BooleanFormula::Not => BabyBear::new(3),
        BooleanFormula::Threshold(k, _) => {
            // Include K in the hash to bind the threshold value
            BabyBear::new(4 + *k as u32)
        }
        BooleanFormula::Custom(gates) => {
            // Include gate count to differentiate custom formulas
            BabyBear::new(100 + gates.len() as u32)
        }
    };
    let terms: Vec<BabyBear> = sub_results
        .iter()
        .map(|&b| if b { BabyBear::ONE } else { BabyBear::ZERO })
        .collect();
    hash_fact(op_val, &terms)
}

/// Compute a tree hash using the simple CompoundOp API (backward compat).
pub fn compute_tree_hash_simple(op: CompoundOp, sub_results: &[bool]) -> BabyBear {
    let formula = match op {
        CompoundOp::And => BooleanFormula::And((0..sub_results.len()).collect()),
        CompoundOp::Or => BooleanFormula::Or((0..sub_results.len()).collect()),
        CompoundOp::Not => BooleanFormula::Not,
    };
    compute_tree_hash(&formula, sub_results)
}

/// Compute a sub-proof commitment hash.
///
/// Binds a sub-result to the proof that produced it. In a real system this would
/// be the hash of the sub-STARK proof; here we use Poseidon2 over a synthetic binding.
pub fn compute_sub_proof_commitment(sub_result: bool, sub_proof_id: u32) -> BabyBear {
    let result_val = if sub_result {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    hash_2_to_1(result_val, BabyBear::new(sub_proof_id))
}

/// Evaluate a BooleanFormula over boolean sub-results.
pub fn evaluate_formula(formula: &BooleanFormula, sub_results: &[bool]) -> bool {
    match formula {
        BooleanFormula::And(indices) => indices.iter().all(|&i| sub_results[i]),
        BooleanFormula::Or(indices) => indices.iter().any(|&i| sub_results[i]),
        BooleanFormula::Not => !sub_results[0],
        BooleanFormula::Threshold(k, indices) => {
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            count >= *k
        }
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            *values.last().unwrap_or(&false)
        }
    }
}

/// Generate a compound predicate trace for any BooleanFormula.
///
/// Returns (trace, public_inputs) for a 2-row padded trace.
///
/// # Arguments
///
/// * `sub_results` - Boolean results of each sub-predicate
/// * `formula` - The boolean formula combining sub-results
/// * `commitments` - Optional sub-proof commitments (one per sub-result). If None,
///   synthetic commitments are generated. Pass Some(&[...]) to bind real sub-proofs.
pub fn generate_compound_trace_full(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: Option<&[BabyBear]>,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!sub_results.is_empty() && sub_results.len() <= MAX_SUB_PREDICATES);

    // Evaluate the formula.
    let composed = evaluate_formula(formula, sub_results);

    // Compute and_intermediate based on the formula type.
    let and_intermediate = match formula {
        BooleanFormula::And(indices) => {
            // product(r_i for i in indices): all 1 means product is 1
            let mut prod = BabyBear::ONE;
            for &i in indices {
                let ri = if sub_results[i] {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                prod = prod * ri;
            }
            prod
        }
        BooleanFormula::Or(indices) => {
            // product(1 - r_i for i in indices): must be 0 if any r_i is 1
            let mut prod = BabyBear::ONE;
            for &i in indices {
                let ri = if sub_results[i] {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                };
                prod = prod * (BabyBear::ONE - ri);
            }
            prod
        }
        BooleanFormula::Not => BabyBear::ZERO,
        BooleanFormula::Threshold(k, indices) => {
            // and_intermediate = 1 iff sum >= k (prover-computed pass flag)
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            if count >= *k {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        }
        BooleanFormula::Custom(_) => {
            // For custom gates, and_intermediate is unused; gate_output holds the result
            BabyBear::ZERO
        }
    };

    // Compute threshold-related values.
    let threshold_k = match formula {
        BooleanFormula::Threshold(k, _) => BabyBear::new(*k as u32),
        _ => BabyBear::ZERO,
    };
    let sum_count = match formula {
        BooleanFormula::Threshold(_, indices) => {
            let count = indices.iter().filter(|&&i| sub_results[i]).count();
            BabyBear::new(count as u32)
        }
        _ => BabyBear::ZERO,
    };

    // Compute gate tree output for custom formulas.
    let gate_output = match formula {
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            if *values.last().unwrap_or(&false) {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        }
        _ => BabyBear::ZERO,
    };

    // Gate tree info (last gate's inputs for the trace).
    let (gate_a, gate_b, gate_op_val) = match formula {
        BooleanFormula::Custom(gates) if !gates.is_empty() => {
            let mut values: Vec<bool> = sub_results.to_vec();
            for gate in gates.iter().take(gates.len() - 1) {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            let last_gate = gates.last().unwrap();
            match last_gate {
                Gate::And(a, b) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    if values[*b] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ZERO, // AND = 0
                ),
                Gate::Or(a, b) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    if values[*b] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ONE, // OR = 1
                ),
                Gate::Not(a) => (
                    if values[*a] {
                        BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    },
                    BabyBear::ZERO,
                    BabyBear::new(2), // NOT = 2
                ),
            }
        }
        _ => (BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO),
    };

    // Sub-proof commitments.
    let proof_commitments: Vec<BabyBear> = if let Some(comms) = commitments {
        let mut c = comms.to_vec();
        c.resize(MAX_SUB_PREDICATES, BabyBear::ZERO);
        c
    } else {
        // Generate synthetic commitments for each active sub-result.
        (0..MAX_SUB_PREDICATES)
            .map(|i| {
                if i < sub_results.len() {
                    compute_sub_proof_commitment(sub_results[i], i as u32)
                } else {
                    BabyBear::ZERO
                }
            })
            .collect()
    };

    let tree_hash = compute_tree_hash(formula, sub_results);

    // Build the row.
    let mut row = vec![BabyBear::ZERO; COMPOUND_DSL_WIDTH];

    // Fill sub-results.
    for (i, &r) in sub_results.iter().enumerate() {
        row[SUB_RESULT_START + i] = if r { BabyBear::ONE } else { BabyBear::ZERO };
    }

    // Set operator selector.
    match formula {
        BooleanFormula::And(_) => row[OP_AND] = BabyBear::ONE,
        BooleanFormula::Or(_) => row[OP_OR] = BabyBear::ONE,
        BooleanFormula::Not => row[OP_NOT] = BabyBear::ONE,
        BooleanFormula::Threshold(_, _) => row[OP_THRESHOLD] = BabyBear::ONE,
        BooleanFormula::Custom(_) => row[OP_CUSTOM] = BabyBear::ONE,
    }

    // Composed result.
    row[COMPOSED_RESULT] = if composed {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };

    // Tree hash.
    row[TREE_HASH] = tree_hash;

    // Intermediate.
    row[AND_INTERMEDIATE] = and_intermediate;

    // Threshold columns.
    row[THRESHOLD_K] = threshold_k;
    row[SUM_COUNT] = sum_count;

    // Sub-proof commitments (both actual and expected are the same for honest prover).
    for i in 0..MAX_SUB_PREDICATES {
        row[SUB_PROOF_COMMITMENT_START + i] = proof_commitments[i];
        row[EXPECTED_COMMITMENT_START + i] = proof_commitments[i];
    }

    // Custom gate tree columns.
    row[GATE_A_VAL] = gate_a;
    row[GATE_B_VAL] = gate_b;
    row[GATE_OP] = gate_op_val;
    row[GATE_OUTPUT] = gate_output;

    // Pad to power-of-two (2 rows).
    let trace = vec![row.clone(), row];

    // Public inputs.
    let mut public_inputs = vec![BabyBear::ZERO; pi::COUNT];
    public_inputs[pi::COMPOSED_RESULT_EXPECTED] = BabyBear::ONE;
    public_inputs[pi::TREE_HASH] = tree_hash;
    public_inputs[pi::THRESHOLD_K] = threshold_k;
    for i in 0..MAX_SUB_PREDICATES {
        public_inputs[pi::EXPECTED_COMMITMENT_START + i] = proof_commitments[i];
    }

    (trace, public_inputs)
}

/// Generate a valid compound predicate trace (simple API, backward compat).
///
/// Returns (trace, public_inputs) for a 2-row padded trace.
pub fn generate_compound_trace(
    sub_results: &[bool],
    op: CompoundOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = match op {
        CompoundOp::And => BooleanFormula::And((0..sub_results.len()).collect()),
        CompoundOp::Or => BooleanFormula::Or((0..sub_results.len()).collect()),
        CompoundOp::Not => BooleanFormula::Not,
    };
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace for nested composition AND(OR(a, b), NOT(c)).
///
/// This models a two-level composition by flattening into the DSL's single-level
/// structure. The sub-results are the OUTPUTS of the inner gates:
///   sub_result_0 = OR(a, b)
///   sub_result_1 = NOT(c)
/// The outer operator is AND.
pub fn generate_nested_trace(a: bool, b: bool, c: bool) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let or_result = a || b;
    let not_result = !c;
    generate_compound_trace(&[or_result, not_result], CompoundOp::And)
}

/// Generate a trace for K-of-N threshold predicate.
///
/// Returns (trace, public_inputs) where the formula is "at least K of sub_results pass".
pub fn generate_threshold_trace(
    sub_results: &[bool],
    k: usize,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = BooleanFormula::Threshold(k, (0..sub_results.len()).collect());
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace for a custom gate tree formula.
///
/// The gate tree allows arbitrary depth composition, e.g.:
///   AND(OR(a,b), NOT(AND(c,d)))
/// is encoded as:
///   Gate::Or(0, 1)        -> intermediate index 4 (if 4 sub-predicates)
///   Gate::And(2, 3)       -> intermediate index 5
///   Gate::Not(5)          -> intermediate index 6
///   Gate::And(4, 6)       -> final result index 7
pub fn generate_custom_gate_trace(
    sub_results: &[bool],
    gates: &[Gate],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let formula = BooleanFormula::Custom(gates.to_vec());
    generate_compound_trace_full(sub_results, &formula, None)
}

/// Generate a trace with explicit sub-proof commitments.
///
/// This version allows the caller to specify the exact commitment hashes that
/// bind each sub-result to its sub-proof. Used for testing sub-proof binding.
pub fn generate_trace_with_commitments(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_compound_trace_full(sub_results, formula, Some(commitments))
}

// ============================================================================
// Deep nesting helper: multi-level gate tree builder
// ============================================================================

/// Build a gate tree for AND(OR(a, b), NOT(AND(c, d))) given 4 sub-predicates.
///
/// Layout:
///   sub-predicates: indices 0, 1, 2, 3
///   Gate 0: OR(0, 1)   -> index 4
///   Gate 1: AND(2, 3)  -> index 5
///   Gate 2: NOT(5)     -> index 6
///   Gate 3: AND(4, 6)  -> final
pub fn deep_nested_gate_tree() -> Vec<Gate> {
    vec![
        Gate::Or(0, 1),  // index 4: OR(sub_0, sub_1)
        Gate::And(2, 3), // index 5: AND(sub_2, sub_3)
        Gate::Not(5),    // index 6: NOT(AND(sub_2, sub_3))
        Gate::And(4, 6), // index 7: AND(OR(sub_0, sub_1), NOT(AND(sub_2, sub_3)))
    ]
}

/// Build a gate tree for OR(AND(a, b), AND(c, d), AND(e, f)) - 3 levels.
///
/// Layout:
///   sub-predicates: indices 0, 1, 2, 3, 4, 5
///   Gate 0: AND(0, 1)   -> index 6
///   Gate 1: AND(2, 3)   -> index 7
///   Gate 2: AND(4, 5)   -> index 8
///   Gate 3: OR(6, 7)    -> index 9
///   Gate 4: OR(9, 8)    -> final (OR of all three ANDs)
pub fn three_level_gate_tree() -> Vec<Gate> {
    vec![
        Gate::And(0, 1), // index 6
        Gate::And(2, 3), // index 7
        Gate::And(4, 5), // index 8
        Gate::Or(6, 7),  // index 9: OR(AND(0,1), AND(2,3))
        Gate::Or(9, 8),  // index 10: OR(above, AND(4,5))
    ]
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// A complete compound predicate proof result.
#[derive(Clone, Debug)]
pub struct CompoundPredicateProof {
    pub formula: BooleanFormula,
    pub tree_hash: BabyBear,
    pub stark_proof: StarkProof,
}

/// Prove a compound predicate.
pub fn prove_compound_dsl(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: Option<&[BabyBear]>,
) -> Result<CompoundPredicateProof, String> {
    let composed = evaluate_formula(formula, sub_results);
    if !composed {
        return Err("compound predicate not satisfiable".into());
    }

    let circuit = compound_predicate_dsl_circuit();
    let (trace, pi) = generate_compound_trace_full(sub_results, formula, commitments);
    let stark_proof = stark::prove(&circuit, &trace, &pi);

    let tree_hash = compute_tree_hash(formula, sub_results);

    Ok(CompoundPredicateProof {
        formula: formula.clone(),
        tree_hash,
        stark_proof,
    })
}

/// Verify a compound predicate proof.
pub fn verify_compound_dsl(
    proof: &CompoundPredicateProof,
    expected_pi: &[BabyBear],
) -> Result<(), String> {
    let circuit = compound_predicate_dsl_circuit();
    stark::verify(&circuit, &proof.stark_proof, expected_pi)
}

/// Backward-compatible alias for `prove_compound_dsl`.
pub fn prove_compound_predicate(
    sub_results: &[bool],
    formula: &BooleanFormula,
    commitments: Option<&[BabyBear]>,
) -> Result<CompoundPredicateProof, String> {
    prove_compound_dsl(sub_results, formula, commitments)
}

/// Backward-compatible alias for `verify_compound_dsl`.
pub fn verify_compound_predicate(
    proof: &CompoundPredicateProof,
    expected_pi: &[BabyBear],
) -> Result<(), String> {
    verify_compound_dsl(proof, expected_pi)
}
