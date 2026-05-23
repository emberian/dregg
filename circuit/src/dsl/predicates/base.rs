//! Base predicate DSL circuit -- production implementation.
//!
//! Proves comparison predicates over a private attribute bound to a fact commitment:
//! GTE, LTE, GT, LT, NEQ, InRangeLow, InRangeHigh.
//!
//! Trace width: 43 columns. Public inputs: [threshold, fact_commitment].

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
pub const TRACE_WIDTH: usize = ZERO_PAD + 1; // 43

/// Public input indices.
pub const PI_THRESHOLD: usize = 0;
pub const PI_FACT_COMMITMENT: usize = 1;
pub const PUBLIC_INPUT_COUNT: usize = 2;

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

    // C3: neq_flag is binary
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
        name: "pyana-predicate-dsl-v2".into(),
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
        private_value,
        threshold,
        op,
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

    row[PRIVATE_VALUE] = BabyBear::new(witness.private_value);
    row[THRESHOLD] = BabyBear::new(witness.threshold);
    row[FACT_COMMITMENT] = witness.fact_commitment;

    // Compute diff based on operation.
    let diff = match witness.predicate_type {
        PredicateOp::Gte | PredicateOp::InRangeLow => {
            witness.private_value.wrapping_sub(witness.threshold)
        }
        PredicateOp::Lte | PredicateOp::InRangeHigh => {
            witness.threshold.wrapping_sub(witness.private_value)
        }
        PredicateOp::Gt => witness
            .private_value
            .wrapping_sub(witness.threshold)
            .wrapping_sub(1),
        PredicateOp::Lt => witness
            .threshold
            .wrapping_sub(witness.private_value)
            .wrapping_sub(1),
        PredicateOp::Neq => witness.private_value.wrapping_sub(witness.threshold),
    };
    row[DIFF] = BabyBear::new(diff);

    match witness.predicate_type {
        PredicateOp::Neq => {
            row[NEQ_FLAG] = BabyBear::ONE;
            let diff_field = BabyBear::new(diff);
            if let Some(inv) = diff_field.inverse() {
                row[NEQ_INVERSE] = inv;
            }
        }
        _ => {
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

    let public_inputs = vec![BabyBear::new(witness.threshold), witness.fact_commitment];

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
        threshold: BabyBear::new(witness.threshold),
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
    let pi = vec![threshold, fact_commitment];
    stark::verify(&circuit, &proof.stark_proof, &pi)
}
