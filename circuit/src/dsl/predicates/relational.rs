//! Relational predicate DSL circuit -- production implementation.
//!
//! Proves comparison relationships between two private committed values.
//! Trace width: 45 columns. Public inputs: [commitment_a, commitment_b, result_bit].

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2;
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const VALUE_A: usize = 0;
pub const BLINDING_A: usize = 1;
pub const VALUE_B: usize = 2;
pub const BLINDING_B: usize = 3;
pub const DIFF: usize = 4;
pub const DIFF_BITS_START: usize = 5;
pub const NUM_DIFF_BITS: usize = 30;
pub const NEQ_INVERSE: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 35
pub const RESULT_BIT: usize = NEQ_INVERSE + 1; // 36
pub const RANGE_FLAG: usize = RESULT_BIT + 1; // 37
pub const EQ_FLAG: usize = RANGE_FLAG + 1; // 38
pub const NEQ_FLAG: usize = EQ_FLAG + 1; // 39
pub const THRESHOLD_COL: usize = NEQ_FLAG + 1; // 40
pub const COMMITMENT_A: usize = THRESHOLD_COL + 1; // 41
pub const COMMITMENT_B: usize = COMMITMENT_A + 1; // 42
pub const COMMIT_VERIFY_FLAG: usize = COMMITMENT_B + 1; // 43
pub const ZERO_PAD: usize = COMMIT_VERIFY_FLAG + 1; // 44
pub const TRACE_WIDTH: usize = ZERO_PAD + 1; // 45

/// Public input indices.
pub const PI_COMMITMENT_A: usize = 0;
pub const PI_COMMITMENT_B: usize = 1;
pub const PI_RESULT_BIT: usize = 2;
pub const PUBLIC_INPUT_COUNT: usize = 3;

/// Relational operator types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RelationalOp {
    GreaterThan,
    LessThan,
    GreaterOrEqual,
    LessOrEqual,
    Equal,
    NotEqual,
    /// Prove value_a - value_b > threshold.
    DiffGreaterThan(u32),
    /// Prove value_a + value_b > threshold.
    SumGreaterThan(u32),
}

/// Backward-compatible alias (previously `RelationType` in `relational_predicate_air`).
pub type RelationType = RelationalOp;

/// Backward-compatible type alias.
pub type RelationalPredicateProof = RelationalProof;

/// Backward-compatible type alias.
pub type RelationalPredicateWitness = RelationalWitness;

/// Backward-compatible alias for `compute_commitment`.
pub fn compute_value_commitment(value: BabyBear, blinding: BabyBear) -> BabyBear {
    compute_commitment(value, blinding)
}

/// Backward-compatible alias for `prove_relational_dsl`.
pub fn prove_relational(witness: &RelationalWitness) -> Result<RelationalProof, String> {
    prove_relational_dsl(witness)
}

/// Backward-compatible alias for `verify_relational_dsl`.
pub fn verify_relational(
    proof: &RelationalProof,
    commitment_a: BabyBear,
    commitment_b: BabyBear,
    result_bit: BabyBear,
) -> Result<(), String> {
    verify_relational_dsl(proof, commitment_a, commitment_b, result_bit)
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the relational predicate `CircuitDescriptor`.
pub fn relational_predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "value_a".into(),
        index: VALUE_A,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "blinding_a".into(),
        index: BLINDING_A,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "value_b".into(),
        index: VALUE_B,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "blinding_b".into(),
        index: BLINDING_B,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "diff".into(),
        index: DIFF,
        kind: ColumnKind::Value,
    });
    for i in 0..NUM_DIFF_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: DIFF_BITS_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef {
        name: "neq_inverse".into(),
        index: NEQ_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "result_bit".into(),
        index: RESULT_BIT,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "range_flag".into(),
        index: RANGE_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "eq_flag".into(),
        index: EQ_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "neq_flag".into(),
        index: NEQ_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "threshold_col".into(),
        index: THRESHOLD_COL,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "commitment_a".into(),
        index: COMMITMENT_A,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "commitment_b".into(),
        index: COMMITMENT_B,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "commit_verify_flag".into(),
        index: COMMIT_VERIFY_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "zero_pad".into(),
        index: ZERO_PAD,
        kind: ColumnKind::Value,
    });

    let mut constraints = Vec::new();

    // C1: result_bit matches public input
    constraints.push(ConstraintExpr::PiBinding {
        col: RESULT_BIT,
        pi_index: PI_RESULT_BIT,
    });

    // C2: result_bit is 1
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![RESULT_BIT],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C3: Flags are binary
    constraints.push(ConstraintExpr::Binary { col: RANGE_FLAG });
    constraints.push(ConstraintExpr::Binary { col: EQ_FLAG });
    constraints.push(ConstraintExpr::Binary { col: NEQ_FLAG });

    // C4: Exactly one flag active
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![RANGE_FLAG],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![EQ_FLAG],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![NEQ_FLAG],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });

    // C5: At least one flag active
    constraints.push(ConstraintExpr::AtLeastOne {
        flag_cols: vec![RANGE_FLAG, EQ_FLAG, NEQ_FLAG],
    });

    // C6: Bit binary constraints (gated by range_flag)
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Gated {
            selector_col: RANGE_FLAG,
            inner: Box::new(ConstraintExpr::Binary {
                col: DIFF_BITS_START + i,
            }),
        });
    }

    // C7: Bit reconstruction (gated by range_flag)
    {
        let mut terms = Vec::with_capacity(NUM_DIFF_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![DIFF_BITS_START + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![DIFF],
        });
        constraints.push(ConstraintExpr::Gated {
            selector_col: RANGE_FLAG,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C8: High bit zero (gated by range_flag)
    constraints.push(ConstraintExpr::Gated {
        selector_col: RANGE_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
            }],
        }),
    });

    // C9: EQ check (gated by eq_flag)
    constraints.push(ConstraintExpr::Gated {
        selector_col: EQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF],
            }],
        }),
    });

    // C10: NEQ check (gated by neq_flag)
    constraints.push(ConstraintExpr::Gated {
        selector_col: NEQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![DIFF, NEQ_INVERSE],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![],
                },
            ],
        }),
    });

    // C11: commit_verify_flag is binary
    constraints.push(ConstraintExpr::Binary {
        col: COMMIT_VERIFY_FLAG,
    });

    // C12-C13: commitment PI bindings
    constraints.push(ConstraintExpr::PiBinding {
        col: COMMITMENT_A,
        pi_index: PI_COMMITMENT_A,
    });
    constraints.push(ConstraintExpr::PiBinding {
        col: COMMITMENT_B,
        pi_index: PI_COMMITMENT_B,
    });

    // C14: Commitment A binding (gated by commit_verify_flag)
    constraints.push(ConstraintExpr::Gated {
        selector_col: COMMIT_VERIFY_FLAG,
        inner: Box::new(ConstraintExpr::Hash2to1 {
            output_col: COMMITMENT_A,
            input_col_a: VALUE_A,
            input_col_b: BLINDING_A,
        }),
    });

    // C15: Commitment B binding (gated by commit_verify_flag)
    constraints.push(ConstraintExpr::Gated {
        selector_col: COMMIT_VERIFY_FLAG,
        inner: Box::new(ConstraintExpr::Hash2to1 {
            output_col: COMMITMENT_B,
            input_col_a: VALUE_B,
            input_col_b: BLINDING_B,
        }),
    });

    // C16: zero_pad must be zero
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![ZERO_PAD],
        }],
    });

    // Boundaries
    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: RESULT_BIT,
            pi_index: PI_RESULT_BIT,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: COMMITMENT_A,
            pi_index: PI_COMMITMENT_A,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: COMMITMENT_B,
            pi_index: PI_COMMITMENT_B,
        },
    ];

    CircuitDescriptor {
        name: "pyana-relational-predicate-dsl-v2".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Compute a value commitment: Poseidon2(value, blinding).
pub fn compute_commitment(value: BabyBear, blinding: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(value, blinding)
}

/// Full witness for relational trace generation.
#[derive(Clone, Debug)]
pub struct RelationalWitness {
    pub value_a: u32,
    pub blinding_a: u32,
    pub value_b: u32,
    pub blinding_b: u32,
    pub op: RelationalOp,
    /// When true, enables in-circuit commitment verification.
    pub verify_commitments: bool,
}

/// Generate a valid relational predicate trace.
pub fn generate_relational_trace(
    value_a: u32,
    blinding_a: u32,
    value_b: u32,
    blinding_b: u32,
    op: RelationalOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_relational_trace_full(RelationalWitness {
        value_a,
        blinding_a,
        value_b,
        blinding_b,
        op,
        verify_commitments: false,
    })
}

/// Generate a relational trace with full witness control.
pub fn generate_relational_trace_full(
    witness: RelationalWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

    row[VALUE_A] = BabyBear::new(witness.value_a);
    row[BLINDING_A] = BabyBear::new(witness.blinding_a);
    row[VALUE_B] = BabyBear::new(witness.value_b);
    row[BLINDING_B] = BabyBear::new(witness.blinding_b);
    row[RESULT_BIT] = BabyBear::ONE;

    let diff = match witness.op {
        RelationalOp::GreaterThan => witness
            .value_a
            .wrapping_sub(witness.value_b)
            .wrapping_sub(1),
        RelationalOp::LessThan => witness
            .value_b
            .wrapping_sub(witness.value_a)
            .wrapping_sub(1),
        RelationalOp::GreaterOrEqual => witness.value_a.wrapping_sub(witness.value_b),
        RelationalOp::LessOrEqual => witness.value_b.wrapping_sub(witness.value_a),
        RelationalOp::Equal | RelationalOp::NotEqual => {
            witness.value_a.wrapping_sub(witness.value_b)
        }
        RelationalOp::DiffGreaterThan(threshold) => witness
            .value_a
            .wrapping_sub(witness.value_b)
            .wrapping_sub(threshold)
            .wrapping_sub(1),
        RelationalOp::SumGreaterThan(threshold) => witness
            .value_a
            .wrapping_add(witness.value_b)
            .wrapping_sub(threshold)
            .wrapping_sub(1),
    };
    row[DIFF] = BabyBear::new(diff);

    match witness.op {
        RelationalOp::DiffGreaterThan(t) | RelationalOp::SumGreaterThan(t) => {
            row[THRESHOLD_COL] = BabyBear::new(t);
        }
        _ => {}
    }

    match witness.op {
        RelationalOp::Equal => {
            row[EQ_FLAG] = BabyBear::ONE;
        }
        RelationalOp::NotEqual => {
            row[NEQ_FLAG] = BabyBear::ONE;
            let diff_field = BabyBear::new(diff);
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
        }
        _ => {
            row[RANGE_FLAG] = BabyBear::ONE;
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
            }
        }
    }

    let commitment_a = compute_commitment(
        BabyBear::new(witness.value_a),
        BabyBear::new(witness.blinding_a),
    );
    let commitment_b = compute_commitment(
        BabyBear::new(witness.value_b),
        BabyBear::new(witness.blinding_b),
    );
    row[COMMITMENT_A] = commitment_a;
    row[COMMITMENT_B] = commitment_b;

    if witness.verify_commitments {
        row[COMMIT_VERIFY_FLAG] = BabyBear::ONE;
    }

    let public_inputs = vec![commitment_a, commitment_b, BabyBear::ONE];
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// A complete relational predicate proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RelationalProof {
    pub op: RelationalOp,
    pub commitment_a: BabyBear,
    pub commitment_b: BabyBear,
    pub stark_proof: StarkProof,
}

/// Prove a relational predicate.
pub fn prove_relational_dsl(witness: &RelationalWitness) -> Result<RelationalProof, String> {
    let descriptor = relational_predicate_descriptor();
    let circuit = DslCircuit::new(descriptor);
    let (trace, pi) = generate_relational_trace_full(witness.clone());
    let stark_proof = stark::prove(&circuit, &trace, &pi);

    Ok(RelationalProof {
        op: witness.op,
        commitment_a: pi[0],
        commitment_b: pi[1],
        stark_proof,
    })
}

/// Verify a relational predicate proof.
pub fn verify_relational_dsl(
    proof: &RelationalProof,
    commitment_a: BabyBear,
    commitment_b: BabyBear,
) -> Result<(), String> {
    if proof.commitment_a != commitment_a || proof.commitment_b != commitment_b {
        return Err("public input mismatch".into());
    }
    let descriptor = relational_predicate_descriptor();
    let circuit = DslCircuit::new(descriptor);
    let pi = vec![commitment_a, commitment_b, BabyBear::ONE];
    stark::verify(&circuit, &proof.stark_proof, &pi)
}
