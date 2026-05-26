//! Base predicate DSL circuit -- production implementation.
//!
//! Proves comparison predicates over a private attribute bound to a fact commitment:
//! GTE, LTE, GT, LT, NEQ, InRangeLow, InRangeHigh.
//!
//! Trace width: 51 columns. Public inputs: [threshold, fact_commitment, op_tag].

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

pub const PRIVATE_VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const FACT_COMMITMENT: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const NEQ_INVERSE: usize = FACT_COMMITMENT + 1; // 34
pub const NEQ_FLAG: usize = NEQ_INVERSE + 1; // 35
pub const BLINDING: usize = NEQ_FLAG + 1; // 36
pub const FACT_HASH: usize = BLINDING + 1; // 37
pub const STATE_ROOT: usize = FACT_HASH + 1; // 38
pub const DERIVATION_FLAG: usize = STATE_ROOT + 1; // 39
pub const BLINDING_ACTIVE_FLAG: usize = DERIVATION_FLAG + 1; // 40
pub const BLINDING_INVERSE: usize = BLINDING_ACTIVE_FLAG + 1; // 41
pub const ZERO_PAD: usize = BLINDING_INVERSE + 1; // 42
pub const OP_TAG: usize = ZERO_PAD + 1; // 43
pub const OP_GTE: usize = OP_TAG + 1; // 44
pub const OP_LTE: usize = OP_GTE + 1; // 45
pub const OP_GT: usize = OP_LTE + 1; // 46
pub const OP_LT: usize = OP_GT + 1; // 47
pub const OP_NEQ: usize = OP_LT + 1; // 48
pub const OP_IN_RANGE_LOW: usize = OP_NEQ + 1; // 49
pub const OP_IN_RANGE_HIGH: usize = OP_IN_RANGE_LOW + 1; // 50
pub const TRACE_WIDTH: usize = OP_IN_RANGE_HIGH + 1; // 51

/// Public input indices.
pub const PI_THRESHOLD: usize = 0;
pub const PI_FACT_COMMITMENT: usize = 1;
pub const PI_OP_TAG: usize = 2;
pub const PUBLIC_INPUT_COUNT: usize = 3;

/// Predicate types supported by the DSL circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PredicateOp {
    Gte,
    Lte,
    Gt,
    Lt,
    Neq,
    InRangeLow,
    InRangeHigh,
}

impl PredicateOp {
    pub fn tag(self) -> u32 {
        match self {
            PredicateOp::Gte => 1,
            PredicateOp::Lte => 2,
            PredicateOp::Gt => 3,
            PredicateOp::Lt => 4,
            PredicateOp::Neq => 5,
            PredicateOp::InRangeLow => 6,
            PredicateOp::InRangeHigh => 7,
        }
    }

    fn selector_col(self) -> usize {
        match self {
            PredicateOp::Gte => OP_GTE,
            PredicateOp::Lte => OP_LTE,
            PredicateOp::Gt => OP_GT,
            PredicateOp::Lt => OP_LT,
            PredicateOp::Neq => OP_NEQ,
            PredicateOp::InRangeLow => OP_IN_RANGE_LOW,
            PredicateOp::InRangeHigh => OP_IN_RANGE_HIGH,
        }
    }
}

/// Backward-compatible alias for `PredicateOp` (previously `PredicateType` in `predicate_air`).
pub type PredicateType = PredicateOp;

/// Number of bits used for range proofs (backward-compatible constant).
pub const PREDICATE_DIFF_BITS: usize = NUM_DIFF_BITS;

/// Backward-compatible alias: prove a predicate using the DSL circuit.
pub fn prove_predicate(witness: PredicateWitness) -> Option<PredicateProof> {
    prove_predicate_dsl(&witness).ok()
}

/// Backward-compatible alias: verify a predicate proof.
pub fn verify_predicate(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> Result<(), String> {
    verify_predicate_dsl(proof, threshold, fact_commitment)
}

/// Legacy AIR struct (constraint-prover interface).
pub struct PredicateAir;

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the predicate `CircuitDescriptor`.
pub fn predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef {
        name: "private_value".into(),
        index: PRIVATE_VALUE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "threshold".into(),
        index: THRESHOLD,
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
        name: "fact_commitment".into(),
        index: FACT_COMMITMENT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "neq_inverse".into(),
        index: NEQ_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "neq_flag".into(),
        index: NEQ_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "blinding".into(),
        index: BLINDING,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "fact_hash".into(),
        index: FACT_HASH,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "state_root".into(),
        index: STATE_ROOT,
        kind: ColumnKind::Hash,
    });
    columns.push(ColumnDef {
        name: "derivation_flag".into(),
        index: DERIVATION_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "blinding_active_flag".into(),
        index: BLINDING_ACTIVE_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "blinding_inverse".into(),
        index: BLINDING_INVERSE,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "zero_pad".into(),
        index: ZERO_PAD,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "op_tag".into(),
        index: OP_TAG,
        kind: ColumnKind::Value,
    });
    for (name, index) in [
        ("op_gte", OP_GTE),
        ("op_lte", OP_LTE),
        ("op_gt", OP_GT),
        ("op_lt", OP_LT),
        ("op_neq", OP_NEQ),
        ("op_in_range_low", OP_IN_RANGE_LOW),
        ("op_in_range_high", OP_IN_RANGE_HIGH),
    ] {
        columns.push(ColumnDef {
            name: name.into(),
            index,
            kind: ColumnKind::Selector,
        });
    }

    let mut constraints = Vec::new();

    // C1: threshold matches public input
    constraints.push(ConstraintExpr::PiBinding {
        col: THRESHOLD,
        pi_index: PI_THRESHOLD,
    });

    // C2: fact_commitment matches public input
    constraints.push(ConstraintExpr::PiBinding {
        col: FACT_COMMITMENT,
        pi_index: PI_FACT_COMMITMENT,
    });

    // C3: op_tag matches public input
    constraints.push(ConstraintExpr::PiBinding {
        col: OP_TAG,
        pi_index: PI_OP_TAG,
    });

    // C4: operation selectors are one-hot and op_tag is their weighted sum.
    let op_cols = [
        OP_GTE,
        OP_LTE,
        OP_GT,
        OP_LT,
        OP_NEQ,
        OP_IN_RANGE_LOW,
        OP_IN_RANGE_HIGH,
    ];
    for col in op_cols {
        constraints.push(ConstraintExpr::Binary { col });
    }
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_GTE],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_LTE],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_GT],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_LT],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_NEQ],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_IN_RANGE_LOW],
            },
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_IN_RANGE_HIGH],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            },
        ],
    });
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![OP_TAG],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::Gte.tag()),
                col_indices: vec![OP_GTE],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::Lte.tag()),
                col_indices: vec![OP_LTE],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::Gt.tag()),
                col_indices: vec![OP_GT],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::Lt.tag()),
                col_indices: vec![OP_LT],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::Neq.tag()),
                col_indices: vec![OP_NEQ],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::InRangeLow.tag()),
                col_indices: vec![OP_IN_RANGE_LOW],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - PredicateOp::InRangeHigh.tag()),
                col_indices: vec![OP_IN_RANGE_HIGH],
            },
        ],
    });

    // C5: diff semantics are gated by the claimed predicate operation.
    let value_minus_threshold_terms = vec![
        PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![DIFF],
        },
        PolyTerm {
            coeff: neg_one,
            col_indices: vec![PRIVATE_VALUE],
        },
        PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![THRESHOLD],
        },
    ];
    let threshold_minus_value_terms = vec![
        PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![DIFF],
        },
        PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![PRIVATE_VALUE],
        },
        PolyTerm {
            coeff: neg_one,
            col_indices: vec![THRESHOLD],
        },
    ];
    let value_minus_threshold_minus_one_terms = {
        let mut terms = value_minus_threshold_terms.clone();
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![],
        });
        terms
    };
    let threshold_minus_value_minus_one_terms = {
        let mut terms = threshold_minus_value_terms.clone();
        terms.push(PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![],
        });
        terms
    };
    for selector_col in [OP_GTE, OP_NEQ, OP_IN_RANGE_LOW] {
        constraints.push(ConstraintExpr::Gated {
            selector_col,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: value_minus_threshold_terms.clone(),
            }),
        });
    }
    for selector_col in [OP_LTE, OP_IN_RANGE_HIGH] {
        constraints.push(ConstraintExpr::Gated {
            selector_col,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: threshold_minus_value_terms.clone(),
            }),
        });
    }
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_GT,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: value_minus_threshold_minus_one_terms,
        }),
    });
    constraints.push(ConstraintExpr::Gated {
        selector_col: OP_LT,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: threshold_minus_value_minus_one_terms,
        }),
    });

    // C6: neq_flag must match the selected operation.
    constraints.push(ConstraintExpr::Equality {
        col_a: NEQ_FLAG,
        col_b: OP_NEQ,
    });

    // C7: neq_flag is binary
    constraints.push(ConstraintExpr::Binary { col: NEQ_FLAG });

    // C4: Each diff_bit is binary (gated by NOT neq_flag)
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_FLAG,
            inner: Box::new(ConstraintExpr::Binary {
                col: DIFF_BITS_START + i,
            }),
        });
    }

    // C5: Bit reconstruction matches diff (gated by NOT neq_flag)
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
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: NEQ_FLAG,
            inner: Box::new(ConstraintExpr::Polynomial { terms }),
        });
    }

    // C6: High bit is zero (gated by NOT neq_flag)
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: NEQ_FLAG,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
            }],
        }),
    });

    // C7: NEQ inverse check (gated by neq_flag)
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

    // C8: derivation_flag is binary
    constraints.push(ConstraintExpr::Binary {
        col: DERIVATION_FLAG,
    });

    // C9: blinding_active_flag is binary
    constraints.push(ConstraintExpr::Binary {
        col: BLINDING_ACTIVE_FLAG,
    });

    // C10: Unblinded commitment derivation
    constraints.push(ConstraintExpr::Gated {
        selector_col: DERIVATION_FLAG,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: BLINDING_ACTIVE_FLAG,
            inner: Box::new(ConstraintExpr::Hash2to1 {
                output_col: FACT_COMMITMENT,
                input_col_a: FACT_HASH,
                input_col_b: STATE_ROOT,
            }),
        }),
    });

    // C11: Blinded commitment derivation
    constraints.push(ConstraintExpr::Gated {
        selector_col: DERIVATION_FLAG,
        inner: Box::new(ConstraintExpr::Gated {
            selector_col: BLINDING_ACTIVE_FLAG,
            inner: Box::new(ConstraintExpr::Hash4to1 {
                output_col: FACT_COMMITMENT,
                input_cols: [FACT_HASH, STATE_ROOT, BLINDING, ZERO_PAD],
            }),
        }),
    });

    // C12: blinding_active_flag consistency
    constraints.push(ConstraintExpr::ConditionalNonzero {
        selector_col: BLINDING_ACTIVE_FLAG,
        value_col: BLINDING,
        inverse_col: BLINDING_INVERSE,
    });

    // C13: ZERO_PAD must be zero
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
            col: THRESHOLD,
            pi_index: PI_THRESHOLD,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: FACT_COMMITMENT,
            pi_index: PI_FACT_COMMITMENT,
        },
    ];

    CircuitDescriptor {
        name: "dregg-predicate-dsl-v2".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Witness for trace generation.
#[derive(Clone, Debug)]
pub struct PredicateWitness {
    pub private_value: BabyBear,
    pub threshold: BabyBear,
    pub predicate_type: PredicateOp,
    pub fact_commitment: BabyBear,
    /// When Some, enables in-circuit commitment derivation verification.
    pub fact_hash: Option<BabyBear>,
    /// When Some, enables in-circuit commitment derivation verification.
    pub state_root: Option<BabyBear>,
    /// Per-proof blinding factor. When nonzero, uses blinded commitment.
    pub blinding: Option<BabyBear>,
}

/// Generate a valid predicate trace row.
///
/// Returns `(trace, public_inputs)`.
pub fn generate_predicate_trace(
    private_value: u32,
    threshold: u32,
    fact_commitment: BabyBear,
    op: PredicateOp,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_predicate_trace_full(PredicateWitness {
        private_value: BabyBear::new(private_value),
        threshold: BabyBear::new(threshold),
        predicate_type: op,
        fact_commitment,
        fact_hash: None,
        state_root: None,
        blinding: None,
    })
}

/// Generate a predicate trace with full witness (including optional commitment derivation).
pub fn generate_predicate_trace_full(
    witness: PredicateWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

    row[PRIVATE_VALUE] = witness.private_value;
    row[THRESHOLD] = witness.threshold;
    row[FACT_COMMITMENT] = witness.fact_commitment;
    row[OP_TAG] = BabyBear::new(witness.predicate_type.tag());
    row[witness.predicate_type.selector_col()] = BabyBear::ONE;

    // Compute diff based on operation (using inner u32 for wrapping arithmetic).
    let pv = witness.private_value.0;
    let th = witness.threshold.0;
    let diff = match witness.predicate_type {
        PredicateOp::Gte | PredicateOp::InRangeLow => pv.wrapping_sub(th),
        PredicateOp::Lte | PredicateOp::InRangeHigh => th.wrapping_sub(pv),
        PredicateOp::Gt => pv.wrapping_sub(th).wrapping_sub(1),
        PredicateOp::Lt => th.wrapping_sub(pv).wrapping_sub(1),
        PredicateOp::Neq => pv.wrapping_sub(th),
    };

    match witness.predicate_type {
        PredicateOp::Neq => {
            let diff_field = witness.private_value - witness.threshold;
            row[DIFF] = diff_field;
            row[NEQ_FLAG] = BabyBear::ONE;
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
        }
        _ => {
            row[DIFF] = BabyBear::new(diff);
            row[NEQ_FLAG] = BabyBear::ZERO;
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
            }
        }
    }

    // Commitment derivation columns.
    let derivation_active = witness.fact_hash.is_some() && witness.state_root.is_some();
    if derivation_active {
        row[DERIVATION_FLAG] = BabyBear::ONE;
        let fh = witness.fact_hash.unwrap();
        let sr = witness.state_root.unwrap();
        row[FACT_HASH] = fh;
        row[STATE_ROOT] = sr;

        let blinding = witness.blinding.unwrap_or(BabyBear::ZERO);
        row[BLINDING] = blinding;

        if blinding != BabyBear::ZERO {
            row[BLINDING_ACTIVE_FLAG] = BabyBear::ONE;
            if let Some(inv) = blinding.inverse() {
                row[BLINDING_INVERSE] = inv;
            }
        } else {
            row[BLINDING_ACTIVE_FLAG] = BabyBear::ZERO;
        }
    } else {
        row[DERIVATION_FLAG] = BabyBear::ZERO;
        row[BLINDING_ACTIVE_FLAG] = BabyBear::ZERO;
    }

    row[ZERO_PAD] = BabyBear::ZERO;

    let public_inputs = vec![
        witness.threshold,
        witness.fact_commitment,
        BabyBear::new(witness.predicate_type.tag()),
    ];

    // Pad to 2 rows (minimum for STARK).
    let trace = vec![row.clone(), row];
    (trace, public_inputs)
}

/// Compute unblinded fact commitment: Poseidon2_2to1(fact_hash, state_root).
pub fn compute_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(fact_hash, state_root)
}

/// Compute blinded fact commitment: Poseidon2_4to1([fact_hash, state_root, blinding, 0]).
pub fn compute_blinded_fact_commitment(
    fact_hash: BabyBear,
    state_root: BabyBear,
    blinding: BabyBear,
) -> BabyBear {
    if blinding == BabyBear::ZERO {
        poseidon2::hash_2_to_1(fact_hash, state_root)
    } else {
        poseidon2::hash_4_to_1(&[fact_hash, state_root, blinding, BabyBear::ZERO])
    }
}

/// Prove an InRange predicate: value >= low AND value <= high.
/// Returns two traces (one for low bound, one for high bound).
pub fn generate_in_range_traces(
    private_value: u32,
    low: u32,
    high: u32,
    fact_commitment: BabyBear,
) -> Option<(
    (Vec<Vec<BabyBear>>, Vec<BabyBear>),
    (Vec<Vec<BabyBear>>, Vec<BabyBear>),
)> {
    if private_value < low || private_value > high {
        return None;
    }
    let low_trace =
        generate_predicate_trace(private_value, low, fact_commitment, PredicateOp::InRangeLow);
    let high_trace = generate_predicate_trace(
        private_value,
        high,
        fact_commitment,
        PredicateOp::InRangeHigh,
    );
    Some((low_trace, high_trace))
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// A complete predicate proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PredicateProof {
    /// The type of predicate that was proven.
    pub op: PredicateOp,
    /// The threshold (public input).
    pub threshold: BabyBear,
    /// The fact commitment (public input).
    pub fact_commitment: BabyBear,
    /// The STARK proof.
    pub stark_proof: StarkProof,
}

/// Generate a predicate proof from a witness.
///
/// Returns `Err` if the predicate is not satisfiable or proof generation fails.
pub fn prove_predicate_dsl(witness: &PredicateWitness) -> Result<PredicateProof, String> {
    // Check satisfiability.
    let satisfiable = match witness.predicate_type {
        PredicateOp::Gte | PredicateOp::InRangeLow => witness.private_value >= witness.threshold,
        PredicateOp::Lte | PredicateOp::InRangeHigh => witness.private_value <= witness.threshold,
        PredicateOp::Gt => witness.private_value > witness.threshold,
        PredicateOp::Lt => witness.private_value < witness.threshold,
        PredicateOp::Neq => witness.private_value != witness.threshold,
    };
    if !satisfiable {
        return Err("predicate not satisfiable".into());
    }

    let descriptor = predicate_descriptor();
    let circuit = DslCircuit::new(descriptor);
    let (trace, pi) = generate_predicate_trace_full(witness.clone());
    let stark_proof = stark::prove(&circuit, &trace, &pi);

    Ok(PredicateProof {
        op: witness.predicate_type,
        threshold: witness.threshold,
        fact_commitment: witness.fact_commitment,
        stark_proof,
    })
}

/// Verify a predicate proof against expected public inputs.
pub fn verify_predicate_dsl(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> Result<(), String> {
    if proof.threshold != threshold || proof.fact_commitment != fact_commitment {
        return Err("public input mismatch".into());
    }
    let descriptor = predicate_descriptor();
    let circuit = DslCircuit::new(descriptor);
    let pi = vec![threshold, fact_commitment, BabyBear::new(proof.op.tag())];
    stark::verify(&circuit, &proof.stark_proof, &pi)
}

/// Prove an in-range predicate: value >= low AND value <= high.
///
/// Returns a pair of proofs (low_bound, high_bound) or an error.
pub fn prove_in_range(
    value: BabyBear,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> Result<(PredicateProof, PredicateProof), String> {
    let low_witness = PredicateWitness {
        private_value: value,
        threshold: low,
        predicate_type: PredicateOp::InRangeLow,
        fact_commitment,
        fact_hash: None,
        state_root: None,
        blinding: None,
    };
    let high_witness = PredicateWitness {
        private_value: value,
        threshold: high,
        predicate_type: PredicateOp::InRangeHigh,
        fact_commitment,
        fact_hash: None,
        state_root: None,
        blinding: None,
    };
    let low_proof = prove_predicate_dsl(&low_witness)?;
    let high_proof = prove_predicate_dsl(&high_witness)?;
    Ok((low_proof, high_proof))
}

/// Verify an in-range proof pair: value >= low AND value <= high.
pub fn verify_in_range(
    low_proof: &PredicateProof,
    high_proof: &PredicateProof,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> bool {
    verify_predicate_dsl(low_proof, low, fact_commitment).is_ok()
        && verify_predicate_dsl(high_proof, high, fact_commitment).is_ok()
}
