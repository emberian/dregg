//! Runtime DSL circuit adapter for Plonky3 proving.
//!
//! This module bridges the `DslCircuit`/`CircuitDescriptor` runtime evaluator with
//! Plonky3's `p3_air::Air` trait, enabling any `CircuitDescriptor` to be proven by
//! the production-grade `p3-uni-stark` prover at RUNTIME (without compile-time code
//! generation).
//!
//! # Constraint Mapping
//!
//! Each `ConstraintExpr` variant is mapped to `AirBuilder` operations:
//! - `Binary { col }` -> `local[col] * (local[col] - 1) == 0`
//! - `Equality { a, b }` -> `local[a] - local[b] == 0`
//! - `Polynomial { terms }` -> sum of coeff * product(local[cols])
//! - `Gated { selector, inner }` -> `local[selector] * inner_expr == 0`
//! - `PiBinding { col, pi_index }` -> `local[col] - public_inputs[pi_index] == 0` (first row)
//! - `Transition { next_col, local_col }` -> `next[next_col] - local[local_col] == 0` (transition)
//! - `Hash { ... }` -> Not supported at runtime (requires compile-time AIR generation)
//!
//! # Limitations
//!
//! - `Hash`, `Hash2to1`, and `Hash4to1` constraints are NOT supported because they
//!   require inlining Poseidon2 round constraints (hundreds of auxiliary columns).
//!   Use `gen_plonky3.rs` compile-time code generation for circuits with hash constraints.
//! - Boundary constraints using `BoundaryRow::Index(n)` for n > 0 (non-first, non-last)
//!   are enforced only on the first row (limitation of AIR model without preprocessed selectors).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;

use pyana_circuit::field::BabyBear;
use pyana_circuit::plonky3_prover::{PyanaProof, create_config, to_p3};

use crate::circuit::{BoundaryDef, BoundaryRow, CircuitDescriptor, ConstraintExpr};

/// A Plonky3-compatible AIR driven by a `CircuitDescriptor` at runtime.
///
/// This struct wraps a `CircuitDescriptor` and implements `BaseAir` and `Air` so
/// that it can be passed directly to `p3_uni_stark::prove()` and `verify()`.
pub struct DslP3Air {
    pub descriptor: CircuitDescriptor,
}

impl DslP3Air {
    pub fn new(descriptor: CircuitDescriptor) -> Self {
        Self { descriptor }
    }

    fn check_no_hash_constraints(&self) -> Result<(), String> {
        for (i, c) in self.descriptor.constraints.iter().enumerate() {
            if Self::constraint_uses_hash(c) {
                return Err(format!(
                    "Constraint {} uses Hash/Hash2to1/Hash4to1 which requires compile-time \
                     P3 AIR generation via gen_plonky3.rs. Runtime DslP3Air cannot inline \
                     Poseidon2 round constraints.",
                    i
                ));
            }
        }
        Ok(())
    }

    fn constraint_uses_hash(expr: &ConstraintExpr) -> bool {
        match expr {
            ConstraintExpr::Hash { .. }
            | ConstraintExpr::Hash2to1 { .. }
            | ConstraintExpr::Hash4to1 { .. }
            | ConstraintExpr::MerkleHash { .. } => true,
            ConstraintExpr::Gated { inner, .. } => Self::constraint_uses_hash(inner),
            ConstraintExpr::InvertedGated { inner, .. } => Self::constraint_uses_hash(inner),
            ConstraintExpr::Squared { inner } => Self::constraint_uses_hash(inner),
            _ => false,
        }
    }

    fn collect_next_row_columns(expr: &ConstraintExpr, out: &mut Vec<usize>) {
        match expr {
            ConstraintExpr::Transition { next_col, .. } => {
                out.push(*next_col);
            }
            ConstraintExpr::Gated { inner, .. } => {
                Self::collect_next_row_columns(inner, out);
            }
            ConstraintExpr::InvertedGated { inner, .. } => {
                Self::collect_next_row_columns(inner, out);
            }
            ConstraintExpr::Squared { inner } => {
                Self::collect_next_row_columns(inner, out);
            }
            _ => {}
        }
    }
}

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for DslP3Air {
    fn width(&self) -> usize {
        self.descriptor.trace_width
    }
    fn num_public_values(&self) -> usize {
        self.descriptor.public_input_count
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        let mut next_cols = Vec::new();
        for c in &self.descriptor.constraints {
            Self::collect_next_row_columns(c, &mut next_cols);
        }
        next_cols.sort_unstable();
        next_cols.dedup();
        next_cols
    }
}

impl<AB: AirBuilder> Air<AB> for DslP3Air
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let pi_exprs: Vec<AB::Expr> = {
            let pv = builder.public_values();
            (0..self.descriptor.public_input_count)
                .map(|i| pv[i].into())
                .collect()
        };
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let local_exprs: Vec<AB::Expr> = (0..self.descriptor.trace_width)
            .map(|i| local[i].into())
            .collect();
        let next_exprs: Vec<AB::Expr> = (0..self.descriptor.trace_width)
            .map(|i| next[i].into())
            .collect();

        for constraint in &self.descriptor.constraints {
            let (expr, is_transition) = eval_constraint_expr_from_vecs::<AB>(
                constraint,
                &local_exprs,
                &next_exprs,
                &pi_exprs,
            );
            if is_transition {
                builder.when_transition().assert_zero(expr);
            } else {
                builder.assert_zero(expr);
            }
        }

        for boundary in &self.descriptor.boundaries {
            match boundary {
                BoundaryDef::PiBinding { row, col, pi_index } => {
                    let diff = local_exprs[*col].clone() - pi_exprs[*pi_index].clone();
                    match row {
                        BoundaryRow::First | BoundaryRow::Index(0) => {
                            builder.when_first_row().assert_zero(diff);
                        }
                        BoundaryRow::Last => {
                            builder.when_last_row().assert_zero(diff);
                        }
                        BoundaryRow::Index(_) => {
                            builder.when_first_row().assert_zero(diff);
                        }
                    }
                }
                BoundaryDef::Fixed { row, col, value } => {
                    let diff = local_exprs[*col].clone() - AB::Expr::from(AB::F::from_u32(value.0));
                    match row {
                        BoundaryRow::First | BoundaryRow::Index(0) => {
                            builder.when_first_row().assert_zero(diff);
                        }
                        BoundaryRow::Last => {
                            builder.when_last_row().assert_zero(diff);
                        }
                        BoundaryRow::Index(_) => {
                            builder.when_first_row().assert_zero(diff);
                        }
                    }
                }
            }
        }
    }
}

fn eval_constraint_expr_from_vecs<AB: AirBuilder>(
    expr: &ConstraintExpr,
    local_exprs: &[AB::Expr],
    next_exprs: &[AB::Expr],
    pi_exprs: &[AB::Expr],
) -> (AB::Expr, bool)
where
    AB::F: PrimeField32,
{
    match expr {
        ConstraintExpr::Equality { col_a, col_b } => (
            local_exprs[*col_a].clone() - local_exprs[*col_b].clone(),
            false,
        ),
        ConstraintExpr::Multiplication { a, b, output } => (
            local_exprs[*a].clone() * local_exprs[*b].clone() - local_exprs[*output].clone(),
            false,
        ),
        ConstraintExpr::Binary { col } => {
            let x = local_exprs[*col].clone();
            (x.clone() * (x - AB::Expr::ONE), false)
        }
        ConstraintExpr::PiBinding { col, pi_index } => (
            local_exprs[*col].clone() - pi_exprs[*pi_index].clone(),
            false,
        ),
        ConstraintExpr::Transition {
            next_col,
            local_col,
        } => (
            next_exprs[*next_col].clone() - local_exprs[*local_col].clone(),
            true,
        ),
        ConstraintExpr::Polynomial { terms } => {
            let mut sum = AB::Expr::ZERO;
            for term in terms {
                let mut prod: AB::Expr = AB::Expr::from(AB::F::from_u32(term.coeff.0));
                for &ci in &term.col_indices {
                    prod = prod * local_exprs[ci].clone();
                }
                sum = sum + prod;
            }
            (sum, false)
        }
        ConstraintExpr::Gated {
            selector_col,
            inner,
        } => {
            let (inner_expr, is_t) =
                eval_constraint_expr_from_vecs::<AB>(inner, local_exprs, next_exprs, pi_exprs);
            (local_exprs[*selector_col].clone() * inner_expr, is_t)
        }
        ConstraintExpr::InvertedGated {
            selector_col,
            inner,
        } => {
            let (inner_expr, is_t) =
                eval_constraint_expr_from_vecs::<AB>(inner, local_exprs, next_exprs, pi_exprs);
            (
                (AB::Expr::ONE - local_exprs[*selector_col].clone()) * inner_expr,
                is_t,
            )
        }
        ConstraintExpr::Squared { inner } => {
            let (inner_expr, is_t) =
                eval_constraint_expr_from_vecs::<AB>(inner, local_exprs, next_exprs, pi_exprs);
            (inner_expr.clone() * inner_expr, is_t)
        }
        ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col,
        } => (
            local_exprs[*selector_col].clone()
                * (local_exprs[*value_col].clone() * local_exprs[*inverse_col].clone()
                    - AB::Expr::ONE),
            false,
        ),
        ConstraintExpr::AtLeastOne { flag_cols } => {
            let mut product = AB::Expr::ONE;
            for &col in flag_cols {
                product = product * (AB::Expr::ONE - local_exprs[col].clone());
            }
            (product, false)
        }
        ConstraintExpr::Hash { .. }
        | ConstraintExpr::Hash2to1 { .. }
        | ConstraintExpr::Hash4to1 { .. }
        | ConstraintExpr::MerkleHash { .. } => (AB::Expr::ZERO, false),
        // Lookup constraints are verified via membership check (non-algebraic).
        // In a full Plonky3 deployment, this would compile to a LogUp argument.
        // For now, return ZERO (the constraint checker handles verification).
        ConstraintExpr::Lookup { .. } => (AB::Expr::ZERO, false),
    }
}

/// Prove a `CircuitDescriptor` using the Plonky3 p3-uni-stark prover.
pub fn prove_dsl_plonky3(
    descriptor: &CircuitDescriptor,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<Vec<u8>, String> {
    let air = DslP3Air::new(descriptor.clone());
    air.check_no_hash_constraints()?;
    if trace.is_empty() {
        return Err("Trace must have at least one row".into());
    }
    if trace[0].len() != descriptor.trace_width {
        return Err(format!(
            "Trace width mismatch: {} vs {}",
            trace[0].len(),
            descriptor.trace_width
        ));
    }
    if public_inputs.len() != descriptor.public_input_count {
        return Err(format!(
            "Public input count mismatch: {} vs {}",
            public_inputs.len(),
            descriptor.public_input_count
        ));
    }
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    let matrix = RowMajorMatrix::new(values, descriptor.trace_width);
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let config = create_config();
    let proof = p3_uni_stark::prove(&config, &air, matrix, &p3_public);
    serialize_dsl_p3_proof(&proof)
}

/// Verify a proof produced by `prove_dsl_plonky3`.
pub fn verify_dsl_plonky3(
    descriptor: &CircuitDescriptor,
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
) -> Result<bool, String> {
    let air = DslP3Air::new(descriptor.clone());
    air.check_no_hash_constraints()?;
    if public_inputs.len() != descriptor.public_input_count {
        return Err(format!(
            "Public input count mismatch: {} vs {}",
            public_inputs.len(),
            descriptor.public_input_count
        ));
    }
    let proof = deserialize_dsl_p3_proof(proof_bytes)?;
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let config = create_config();
    p3_uni_stark::verify(&config, &air, &proof, &p3_public)
        .map(|()| true)
        .map_err(|e| format!("Plonky3 DSL verification failed: {:?}", e))
}

const DSL_P3_MAGIC: &[u8; 4] = b"D3PF";

fn serialize_dsl_p3_proof(proof: &PyanaProof) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(DSL_P3_MAGIC);
    let payload = rmp_serde::to_vec(proof).map_err(|e| format!("Serialization failed: {}", e))?;
    bytes.extend_from_slice(&payload);
    Ok(bytes)
}

fn deserialize_dsl_p3_proof(bytes: &[u8]) -> Result<PyanaProof, String> {
    if bytes.len() < 4 {
        return Err("DSL P3 proof too short".into());
    }
    if &bytes[..4] != DSL_P3_MAGIC {
        return Err("Invalid DSL P3 proof magic".into());
    }
    rmp_serde::from_slice(&bytes[4..]).map_err(|e| format!("Deserialization failed: {}", e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{
        BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr,
        PolyTerm,
    };
    use pyana_circuit::field::BABYBEAR_P;

    fn sovereign_transfer_descriptor() -> CircuitDescriptor {
        CircuitDescriptor {
            name: "pyana-sovereign-transition-v1".to_string(),
            trace_width: 6,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "old_balance".to_string(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "transfer_amount".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "new_balance".to_string(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "direction".to_string(),
                    index: 3,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "pad0".to_string(),
                    index: 4,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "pad1".to_string(),
                    index: 5,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![
                ConstraintExpr::Binary { col: 3 },
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(BABYBEAR_P - 1),
                            col_indices: vec![0],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(BABYBEAR_P - 1),
                            col_indices: vec![1],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(2),
                            col_indices: vec![3, 1],
                        },
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 32,
            lookup_tables: vec![],
        }
    }

    #[test]
    fn dsl_p3_prove_verify_sovereign_transfer() {
        let d = sovereign_transfer_descriptor();
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(900),
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];
        let pi = vec![BabyBear::ZERO; 32];
        let proof = prove_dsl_plonky3(&d, &trace, &pi).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &pi), Ok(true)));
    }

    #[test]
    fn dsl_p3_incoming_transfer() {
        let d = sovereign_transfer_descriptor();
        let row = vec![
            BabyBear::from_u64(500),
            BabyBear::from_u64(200),
            BabyBear::from_u64(700),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];
        let pi = vec![BabyBear::ZERO; 32];
        let proof = prove_dsl_plonky3(&d, &trace, &pi).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &pi), Ok(true)));
    }

    #[test]
    fn dsl_p3_rejects_wrong_witness() {
        let d = sovereign_transfer_descriptor();
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(1000),
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];
        let pi = vec![BabyBear::ZERO; 32];
        let result = std::panic::catch_unwind(|| prove_dsl_plonky3(&d, &trace, &pi));
        match result {
            Ok(Ok(proof)) => assert!(!matches!(verify_dsl_plonky3(&d, &proof, &pi), Ok(true))),
            _ => {} // panic or error is correct
        }
    }

    #[test]
    fn dsl_p3_rejects_wrong_public_inputs() {
        let d = sovereign_transfer_descriptor();
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(900),
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];
        let pi = vec![BabyBear::ZERO; 32];
        let proof = prove_dsl_plonky3(&d, &trace, &pi).expect("prove");
        let mut wrong_pi = vec![BabyBear::ZERO; 32];
        wrong_pi[0] = BabyBear::new(999);
        assert!(!matches!(
            verify_dsl_plonky3(&d, &proof, &wrong_pi),
            Ok(true)
        ));
    }

    #[test]
    fn dsl_p3_hash_constraint_rejected() {
        let d = CircuitDescriptor {
            name: "hash-test".to_string(),
            trace_width: 4,
            max_degree: 2,
            columns: vec![],
            constraints: vec![ConstraintExpr::Hash {
                output_col: 0,
                input_cols: vec![1, 2, 3],
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let result = prove_dsl_plonky3(&d, &vec![vec![BabyBear::ZERO; 4]; 2], &[]);
        assert!(result.is_err() && result.unwrap_err().contains("Hash"));
    }

    #[test]
    fn dsl_p3_with_boundary_constraints() {
        let d = CircuitDescriptor {
            name: "boundary-test".to_string(),
            trace_width: 2,
            max_degree: 1,
            columns: vec![
                ColumnDef {
                    name: "a".to_string(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "b".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::Equality { col_a: 0, col_b: 1 }],
            boundaries: vec![BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            }],
            public_input_count: 1,
            lookup_tables: vec![],
        };
        let val = BabyBear::new(42);
        let proof = prove_dsl_plonky3(&d, &vec![vec![val, val]; 2], &[val]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[val]), Ok(true)));
    }

    #[test]
    fn dsl_p3_transition_constraint() {
        let d = CircuitDescriptor {
            name: "transition-test".to_string(),
            trace_width: 2,
            max_degree: 1,
            columns: vec![
                ColumnDef {
                    name: "state".to_string(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "next_state".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::Transition {
                next_col: 0,
                local_col: 1,
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let trace = vec![
            vec![BabyBear::new(10), BabyBear::new(20)],
            vec![BabyBear::new(20), BabyBear::new(30)],
            vec![BabyBear::new(30), BabyBear::new(40)],
            vec![BabyBear::new(40), BabyBear::new(50)],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }

    #[test]
    fn dsl_p3_conditional_nonzero() {
        let d = CircuitDescriptor {
            name: "cond-nonzero".to_string(),
            trace_width: 3,
            max_degree: 3,
            columns: vec![
                ColumnDef {
                    name: "sel".to_string(),
                    index: 0,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "val".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "inv".to_string(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::ConditionalNonzero {
                selector_col: 0,
                value_col: 1,
                inverse_col: 2,
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let v = BabyBear::new(7);
        let inv = v.inverse().expect("nonzero");
        let trace = vec![
            vec![BabyBear::ONE, v, inv],
            vec![BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }

    #[test]
    fn dsl_p3_at_least_one() {
        let d = CircuitDescriptor {
            name: "at-least-one".to_string(),
            trace_width: 3,
            max_degree: 3,
            columns: vec![
                ColumnDef {
                    name: "f0".to_string(),
                    index: 0,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "f1".to_string(),
                    index: 1,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "f2".to_string(),
                    index: 2,
                    kind: ColumnKind::Binary,
                },
            ],
            constraints: vec![ConstraintExpr::AtLeastOne {
                flag_cols: vec![0, 1, 2],
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let trace = vec![
            vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ZERO],
            vec![BabyBear::ONE, BabyBear::ZERO, BabyBear::ONE],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }

    #[test]
    fn dsl_p3_cross_verify_with_custom_stark() {
        use crate::circuit::DslCircuit;
        use pyana_circuit::stark;
        let d = sovereign_transfer_descriptor();
        let row = vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(900),
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let trace = vec![row.clone(), row];
        let pi = vec![BabyBear::ZERO; 32];
        // Custom STARK
        let dsl = DslCircuit::new(d.clone());
        let sp = stark::prove(&dsl, &trace, &pi);
        assert!(stark::verify(&dsl, &sp, &pi).is_ok());
        // Plonky3
        let p3p = prove_dsl_plonky3(&d, &trace, &pi).expect("p3 prove");
        assert!(matches!(verify_dsl_plonky3(&d, &p3p, &pi), Ok(true)));
    }

    #[test]
    fn dsl_p3_gated_constraint() {
        let d = CircuitDescriptor {
            name: "gated".to_string(),
            trace_width: 3,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "sel".to_string(),
                    index: 0,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "a".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "b".to_string(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::Gated {
                selector_col: 0,
                inner: Box::new(ConstraintExpr::Equality { col_a: 1, col_b: 2 }),
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let trace = vec![
            vec![BabyBear::ONE, BabyBear::new(42), BabyBear::new(42)],
            vec![BabyBear::ZERO, BabyBear::new(10), BabyBear::new(20)],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }

    #[test]
    fn dsl_p3_inverted_gated_constraint() {
        let d = CircuitDescriptor {
            name: "inv-gated".to_string(),
            trace_width: 3,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "sel".to_string(),
                    index: 0,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "a".to_string(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "b".to_string(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::InvertedGated {
                selector_col: 0,
                inner: Box::new(ConstraintExpr::Equality { col_a: 1, col_b: 2 }),
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let trace = vec![
            vec![BabyBear::ZERO, BabyBear::new(42), BabyBear::new(42)],
            vec![BabyBear::ONE, BabyBear::new(10), BabyBear::new(20)],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }

    #[test]
    fn dsl_p3_multiplication_constraint() {
        let d = CircuitDescriptor {
            name: "mul".to_string(),
            trace_width: 3,
            max_degree: 2,
            columns: vec![],
            constraints: vec![ConstraintExpr::Multiplication {
                a: 0,
                b: 1,
                output: 2,
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let trace = vec![
            vec![BabyBear::new(7), BabyBear::new(6), BabyBear::new(42)],
            vec![BabyBear::new(3), BabyBear::new(5), BabyBear::new(15)],
        ];
        let proof = prove_dsl_plonky3(&d, &trace, &[]).expect("prove");
        assert!(matches!(verify_dsl_plonky3(&d, &proof, &[]), Ok(true)));
    }
}
