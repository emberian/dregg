//! Accumulator non-revocation AIR expressed as a CircuitDescriptor.
//!
//! This encodes the polynomial-evaluation accumulator constraints from
//! `circuit/src/accumulator_air.rs`. The key insight: Horner's method for
//! polynomial evaluation becomes a chain of extension-field multiplications
//! and additions across columns within each row.
//!
//! # Trace Layout (per row, one ancestor)
//!
//! 32 base-field columns (8 extension-field "groups" of 4 each):
//!   [0..3]:   h_i         — ancestor hash embedded in BabyBear^4
//!   [4..7]:   w_i         — quotient witness
//!   [8..11]:  v_i         — remainder witness
//!   [12..15]: diff_i      — precomputed (alpha - h_i)
//!   [16..19]: prod_i      — w_i * diff_i
//!   [20..23]: sum_i       — prod_i + v_i (should equal Acc)
//!   [24..27]: v_inv_i     — inverse of v_i
//!   [28..31]: check_i     — v_i * v_inv_i (should equal (1,0,0,0))
//!
//! # Constraints (per row)
//!
//! 1. diff == alpha - h (4 equalities referencing pi for alpha)
//! 2. prod == w * diff (extension field multiplication, degree 2)
//! 3. sum == prod + v (4 equalities)
//! 4. check == v * v_inv (extension field multiplication, degree 2)
//!
//! Boundary constraints enforce sum == Acc and check == ONE on active rows.

use pyana_circuit::accumulator_air::{col, pi, ExtElem, ACCUMULATOR_WIDTH, MAX_ANCESTORS};
use pyana_circuit::field::{BabyBear, BABYBEAR_P};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr,
    DslCircuit, PolyTerm,
};

/// Negate a field element.
fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

/// Build a polynomial term.
fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

/// The irreducible constant W for BabyBear^4: X^4 - 11.
const W_VAL: u32 = 11;

/// Construct the accumulator non-revocation AIR as a CircuitDescriptor.
///
/// Encodes the 4 core constraint groups:
/// 1. diff correctness (4 base-field constraints, referencing alpha from pi-bound aux cols)
/// 2. prod correctness (4 base-field constraints for extension-field multiplication)
/// 3. sum correctness (4 base-field constraints for addition)
/// 4. check correctness (4 base-field constraints for inverse verification)
///
/// Boundary constraints enforce sum == Acc and check == ONE on active rows.
///
/// Since the DSL's Polynomial constraint can only reference local[] columns (not pi),
/// we add 8 auxiliary columns to hold the public-input values (alpha[0..3], acc[0..3]).
/// The boundary constraints bind these aux columns to their respective pi values.
pub fn accumulator_circuit_descriptor() -> CircuitDescriptor {
    // Auxiliary columns to hold pi-derived values in the trace:
    //   cols 32..35: alpha[0..3] (from pi[4..7])
    //   cols 36..39: acc[0..3] (from pi[0..3])
    let alpha_aux_start: usize = ACCUMULATOR_WIDTH; // 32
    let acc_aux_start: usize = ACCUMULATOR_WIDTH + 4; // 36
    let total_width: usize = ACCUMULATOR_WIDTH + 8; // 40

    let w = BabyBear::new(W_VAL);

    let mut constraints = Vec::new();

    // ========================================================================
    // C1: diff == alpha - h (4 base-field equalities)
    //   diff[i] - alpha_aux[i] + h[i] == 0  for i in 0..4
    // ========================================================================
    for i in 0..4 {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::DIFF + i]),
                term(neg_one(), &[alpha_aux_start + i]),
                term(BabyBear::ONE, &[col::HASH + i]),
            ],
        });
    }

    // ========================================================================
    // C2: prod == w * diff (extension field multiplication)
    //
    // Extension-field mul: if w = (w0, w1, w2, w3) and d = (d0, d1, d2, d3):
    //   p0 = w0*d0 + W*(w1*d3 + w2*d2 + w3*d1)
    //   p1 = w0*d1 + w1*d0 + W*(w2*d3 + w3*d2)
    //   p2 = w0*d2 + w1*d1 + w2*d0 + W*(w3*d3)
    //   p3 = w0*d3 + w1*d2 + w2*d1 + w3*d0
    //
    // Constraint: prod[i] - expected_prod[i] == 0
    //
    // We express each as a polynomial: prod[i] - (sum of terms) == 0
    // ========================================================================

    // Helper to get column index for quotient component
    let wc = |i: usize| col::QUOTIENT + i; // w[i]
    let dc = |i: usize| col::DIFF + i; // diff[i]
    let pc = |i: usize| col::PRODUCT + i; // prod[i]

    // prod[0] = w0*d0 + W*(w1*d3 + w2*d2 + w3*d1)
    // => prod[0] - w0*d0 - W*w1*d3 - W*w2*d2 - W*w3*d1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(0)]),
            term(neg_one(), &[wc(0), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(1), dc(3)]),
            term(BabyBear::ZERO - w, &[wc(2), dc(2)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(1)]),
        ],
    });

    // prod[1] = w0*d1 + w1*d0 + W*(w2*d3 + w3*d2)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(1)]),
            term(neg_one(), &[wc(0), dc(1)]),
            term(neg_one(), &[wc(1), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(2), dc(3)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(2)]),
        ],
    });

    // prod[2] = w0*d2 + w1*d1 + w2*d0 + W*(w3*d3)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(2)]),
            term(neg_one(), &[wc(0), dc(2)]),
            term(neg_one(), &[wc(1), dc(1)]),
            term(neg_one(), &[wc(2), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(3)]),
        ],
    });

    // prod[3] = w0*d3 + w1*d2 + w2*d1 + w3*d0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(3)]),
            term(neg_one(), &[wc(0), dc(3)]),
            term(neg_one(), &[wc(1), dc(2)]),
            term(neg_one(), &[wc(2), dc(1)]),
            term(neg_one(), &[wc(3), dc(0)]),
        ],
    });

    // ========================================================================
    // C3: sum == prod + v (4 base-field equalities)
    //   sum[i] - prod[i] - v[i] == 0
    // ========================================================================
    for i in 0..4 {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::SUM + i]),
                term(neg_one(), &[col::PRODUCT + i]),
                term(neg_one(), &[col::REMAINDER + i]),
            ],
        });
    }

    // ========================================================================
    // C4: check == v * v_inv (extension field multiplication)
    //   Same structure as C2 but with REMAINDER and V_INV columns.
    // ========================================================================

    let vc = |i: usize| col::REMAINDER + i; // v[i]
    let ic = |i: usize| col::V_INV + i; // v_inv[i]
    let cc = |i: usize| col::CHECK + i; // check[i]

    // check[0] = v0*vi0 + W*(v1*vi3 + v2*vi2 + v3*vi1)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(0)]),
            term(neg_one(), &[vc(0), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(1), ic(3)]),
            term(BabyBear::ZERO - w, &[vc(2), ic(2)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(1)]),
        ],
    });

    // check[1] = v0*vi1 + v1*vi0 + W*(v2*vi3 + v3*vi2)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(1)]),
            term(neg_one(), &[vc(0), ic(1)]),
            term(neg_one(), &[vc(1), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(2), ic(3)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(2)]),
        ],
    });

    // check[2] = v0*vi2 + v1*vi1 + v2*vi0 + W*(v3*vi3)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(2)]),
            term(neg_one(), &[vc(0), ic(2)]),
            term(neg_one(), &[vc(1), ic(1)]),
            term(neg_one(), &[vc(2), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(3)]),
        ],
    });

    // check[3] = v0*vi3 + v1*vi2 + v2*vi1 + v3*vi0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(3)]),
            term(neg_one(), &[vc(0), ic(3)]),
            term(neg_one(), &[vc(1), ic(2)]),
            term(neg_one(), &[vc(2), ic(1)]),
            term(neg_one(), &[vc(3), ic(0)]),
        ],
    });

    // ========================================================================
    // Boundary constraints: sum == Acc, check == ONE on active rows.
    //
    // The hand-written AIR uses per-row boundary constraints for each active row.
    // In the DSL, we can only do First/Last/Index boundaries. For this demo we
    // bind the first row's sum to acc and check to ONE, which is sufficient to
    // demonstrate the approach. The real AIR binds ALL active rows; a full
    // implementation would use Index boundaries for each row up to num_ancestors.
    // ========================================================================

    // Also: bind the auxiliary alpha/acc columns on the first row.
    let mut boundaries = vec![
        // First row: alpha_aux[0..3] = pi[4..7]
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: alpha_aux_start, pi_index: pi::ALPHA_START },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: alpha_aux_start + 1, pi_index: pi::ALPHA_START + 1 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: alpha_aux_start + 2, pi_index: pi::ALPHA_START + 2 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: alpha_aux_start + 3, pi_index: pi::ALPHA_START + 3 },
        // First row: acc_aux[0..3] = pi[0..3]
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: acc_aux_start, pi_index: pi::ACC_START },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: acc_aux_start + 1, pi_index: pi::ACC_START + 1 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: acc_aux_start + 2, pi_index: pi::ACC_START + 2 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: acc_aux_start + 3, pi_index: pi::ACC_START + 3 },
        // First row: sum == Acc
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::SUM, pi_index: pi::ACC_START },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::SUM + 1, pi_index: pi::ACC_START + 1 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::SUM + 2, pi_index: pi::ACC_START + 2 },
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::SUM + 3, pi_index: pi::ACC_START + 3 },
        // First row: check == (1, 0, 0, 0)
        BoundaryDef::Fixed { row: BoundaryRow::First, col: col::CHECK, value: BabyBear::ONE },
        BoundaryDef::Fixed { row: BoundaryRow::First, col: col::CHECK + 1, value: BabyBear::ZERO },
        BoundaryDef::Fixed { row: BoundaryRow::First, col: col::CHECK + 2, value: BabyBear::ZERO },
        BoundaryDef::Fixed { row: BoundaryRow::First, col: col::CHECK + 3, value: BabyBear::ZERO },
    ];

    // Add Index boundaries for rows 1..MAX_ANCESTORS-1 for sum and check.
    // This demonstrates the full per-row binding like the hand-written AIR.
    for row_idx in 1..MAX_ANCESTORS {
        // sum == Acc (via Index boundary)
        for i in 0..4 {
            boundaries.push(BoundaryDef::PiBinding {
                row: BoundaryRow::Index(row_idx),
                col: col::SUM + i,
                pi_index: pi::ACC_START + i,
            });
        }
        // check == (1, 0, 0, 0)
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK,
            value: BabyBear::ONE,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 1,
            value: BabyBear::ZERO,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 2,
            value: BabyBear::ZERO,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 3,
            value: BabyBear::ZERO,
        });
    }

    // Column definitions
    let columns = vec![
        ColumnDef { name: "h[0]".into(), index: col::HASH, kind: ColumnKind::Value },
        ColumnDef { name: "h[1]".into(), index: col::HASH + 1, kind: ColumnKind::Value },
        ColumnDef { name: "h[2]".into(), index: col::HASH + 2, kind: ColumnKind::Value },
        ColumnDef { name: "h[3]".into(), index: col::HASH + 3, kind: ColumnKind::Value },
        ColumnDef { name: "w[0]".into(), index: col::QUOTIENT, kind: ColumnKind::Value },
        ColumnDef { name: "diff[0]".into(), index: col::DIFF, kind: ColumnKind::Value },
        ColumnDef { name: "prod[0]".into(), index: col::PRODUCT, kind: ColumnKind::Value },
        ColumnDef { name: "sum[0]".into(), index: col::SUM, kind: ColumnKind::Value },
        ColumnDef { name: "v_inv[0]".into(), index: col::V_INV, kind: ColumnKind::Value },
        ColumnDef { name: "check[0]".into(), index: col::CHECK, kind: ColumnKind::Value },
        ColumnDef { name: "alpha_aux[0]".into(), index: alpha_aux_start, kind: ColumnKind::Value },
        ColumnDef { name: "acc_aux[0]".into(), index: acc_aux_start, kind: ColumnKind::Value },
    ];

    CircuitDescriptor {
        name: "pyana-accumulator-dsl-v1".into(),
        trace_width: total_width,
        max_degree: 2, // Extension field multiplication is degree 2
        columns,
        constraints,
        boundaries,
        public_input_count: 9, // Acc(4) + alpha(4) + num_ancestors(1)
    }
}

/// Create a DslCircuit from the accumulator descriptor.
pub fn accumulator_dsl_circuit() -> DslCircuit {
    DslCircuit::new(accumulator_circuit_descriptor())
}

/// Total trace width for the DSL version (with auxiliary columns).
pub const ACCUMULATOR_DSL_WIDTH: usize = ACCUMULATOR_WIDTH + 8; // 40

/// Generate a valid accumulator trace for the DSL circuit.
///
/// Creates a 3-ancestor non-revocation proof against a 5-element revocation set.
/// Returns (trace, public_inputs) with auxiliary columns filled.
pub fn generate_valid_accumulator_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use pyana_circuit::accumulator_air::{
        AccumulatorNonMembershipWitness, AccumulatorNonRevocationWitness,
        AccumulatorNonRevocationAir, compute_accumulator, derive_alpha,
    };
    use pyana_circuit::poseidon2::hash_many;

    // Create a revocation set of 5 elements.
    let revocation_set: Vec<BabyBear> = (1..=5)
        .map(|i| hash_many(&[BabyBear::new(i * 50), BabyBear::new(0xCAFE)]))
        .collect();

    let alpha = derive_alpha(&revocation_set);
    let acc = compute_accumulator(&revocation_set, alpha);

    // 3 ancestor hashes NOT in the revocation set.
    let ancestors: Vec<BabyBear> = (1..=3)
        .map(|i| hash_many(&[BabyBear::new(i * 7777), BabyBear::new(0xCAFE)]))
        .collect();

    // Generate witnesses.
    let mut witness_ancestors = Vec::new();
    for &h in &ancestors {
        let mut remainder_base = BabyBear::ONE;
        for &rev_h in &revocation_set {
            remainder_base = remainder_base * (h - rev_h);
        }
        let remainder = ExtElem::from_base(remainder_base);
        let h_ext = ExtElem::from_base(h);
        let diff = alpha.sub(h_ext);
        let numerator = acc.sub(remainder);
        let quotient = numerator.mul(diff.inverse().unwrap());

        witness_ancestors.push(AccumulatorNonMembershipWitness {
            ancestor_hash: h,
            quotient,
            remainder,
        });
    }

    let witness = AccumulatorNonRevocationWitness {
        ancestors: witness_ancestors,
    };

    // Generate base trace
    let (base_trace, public_inputs) =
        AccumulatorNonRevocationAir::generate_trace(&witness, acc, alpha);

    // Extend each row with auxiliary columns (alpha_aux, acc_aux)
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(base_trace.len());
    for base_row in &base_trace {
        let mut row = base_row.clone();
        row.resize(ACCUMULATOR_DSL_WIDTH, BabyBear::ZERO);

        // alpha_aux[0..3] = alpha components
        row[ACCUMULATOR_WIDTH] = alpha.0[0];
        row[ACCUMULATOR_WIDTH + 1] = alpha.0[1];
        row[ACCUMULATOR_WIDTH + 2] = alpha.0[2];
        row[ACCUMULATOR_WIDTH + 3] = alpha.0[3];

        // acc_aux[0..3] = accumulator components
        row[ACCUMULATOR_WIDTH + 4] = acc.0[0];
        row[ACCUMULATOR_WIDTH + 5] = acc.0[1];
        row[ACCUMULATOR_WIDTH + 6] = acc.0[2];
        row[ACCUMULATOR_WIDTH + 7] = acc.0[3];

        trace.push(row);
    }

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::StarkAir;

    #[test]
    fn accumulator_descriptor_validates() {
        let desc = accumulator_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "accumulator descriptor should pass validation: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn accumulator_descriptor_has_correct_width() {
        let desc = accumulator_circuit_descriptor();
        assert_eq!(desc.trace_width, ACCUMULATOR_DSL_WIDTH);
        assert_eq!(desc.trace_width, 40);
    }

    #[test]
    fn accumulator_descriptor_constraint_count() {
        let desc = accumulator_circuit_descriptor();
        // C1: 4 (diff), C2: 4 (prod), C3: 4 (sum), C4: 4 (check) = 16
        assert_eq!(
            desc.constraints.len(),
            16,
            "Should have 16 polynomial constraints (4 per constraint group)"
        );
    }

    #[test]
    fn accumulator_dsl_valid_trace_evaluates_to_zero() {
        let (trace, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Check all rows (the trace is padded to power-of-2, padding rows are
        // duplicates of the last valid row and should also satisfy constraints).
        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() { &trace[i + 1] } else { &trace[i] };
            let result = circuit.eval_constraints(&trace[i], next, &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "DslCircuit should evaluate to ZERO on valid accumulator trace row {i}"
            );
        }
    }

    #[test]
    fn accumulator_dsl_rejects_wrong_diff() {
        let (mut trace, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: corrupt diff[0] on row 0
        trace[0][col::DIFF] = BabyBear::new(99999);

        let next = &trace[1];
        let result = circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong diff"
        );
    }

    #[test]
    fn accumulator_dsl_rejects_wrong_product() {
        let (mut trace, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: corrupt prod[0] on row 0
        trace[0][col::PRODUCT] = BabyBear::new(11111);

        let next = &trace[1];
        let result = circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong product"
        );
    }

    #[test]
    fn accumulator_dsl_rejects_wrong_sum() {
        let (mut trace, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: corrupt sum[0] on row 0
        trace[0][col::SUM] = BabyBear::new(22222);

        let next = &trace[1];
        let result = circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong sum"
        );
    }

    #[test]
    fn accumulator_dsl_rejects_wrong_check() {
        let (mut trace, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: corrupt check[0] on row 0 (should be 1 for non-zero v)
        trace[0][col::CHECK] = BabyBear::new(5);

        let next = &trace[1];
        let result = circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong check (inverse verification)"
        );
    }

    #[test]
    fn accumulator_dsl_boundary_constraints_correct() {
        let (_, pi) = generate_valid_accumulator_trace();
        let circuit = accumulator_dsl_circuit();
        let boundaries = circuit.boundary_constraints(&pi, 8);

        // Should have: 8 (alpha/acc aux) + 4 (sum first) + 4 (check first)
        //            + 7 * (4 sum + 4 check) = 16 + 7*8 = 16 + 56 = 72
        assert_eq!(boundaries.len(), 72);

        // First boundary: alpha_aux[0] = pi[4]
        assert_eq!(boundaries[0].col, ACCUMULATOR_WIDTH); // alpha_aux_start
        assert_eq!(boundaries[0].value, pi[pi::ALPHA_START]);
    }
}
