//! Merkle membership AIR expressed as a CircuitDescriptor.
//!
//! Proves: "this leaf exists in the committed 4-ary Merkle tree at this root."
//!
//! # Constraint strategy
//!
//! The hand-written AIR (`circuit/src/merkle_air.rs`) has 6 columns per row (one row
//! per tree level, leaf to root):
//!
//! | Col | Name     | Description                              |
//! |-----|----------|------------------------------------------|
//! | 0   | current  | Hash at this level (leaf hash on row 0)  |
//! | 1   | sib0     | First sibling hash                       |
//! | 2   | sib1     | Second sibling hash                      |
//! | 3   | sib2     | Third sibling hash                       |
//! | 4   | position | Child position index (0..3)              |
//! | 5   | parent   | Computed parent = hash_node(children)     |
//!
//! # Constraints
//!
//! - C1: Position validity — `pos*(pos-1)*(pos-2)*(pos-3) == 0`
//!   Expressed as a degree-4 polynomial.
//! - C2: Parent hash correctness — uses `Hash` constraint variant.
//!   The DSL `Hash` constraint uses `hash_fact(input_cols[0], &input_cols[1..])`.
//!   We encode the parent as `hash_fact(current, [sib0, sib1, sib2, position])`.
//!   NOTE: This is a DSL approximation — the hand-written AIR uses `hash_4_to_1`
//!   with children reordered by position. For the DSL version we use `hash_fact`
//!   which binds all five values (current, sib0, sib1, sib2, position) into the
//!   parent hash. The security property (parent is uniquely determined by children
//!   + position) is preserved.
//! - C3: Chain continuity — `next[current] == local[parent]`
//!   Expressed as a `Transition` constraint.
//!
//! # Boundary Constraints
//!
//! - First row: `current == pi[0]` (leaf hash)
//! - Last row: `parent == pi[1]` (expected root)
//!
//! # Public Inputs
//!
//! [leaf_hash, expected_root]

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_fact;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

/// Column indices (matching the hand-written AIR).
pub mod col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
}

/// Public input indices.
pub mod pi {
    pub const LEAF_HASH: usize = 0;
    pub const EXPECTED_ROOT: usize = 1;
}

/// Trace width for the Merkle DSL circuit.
pub const MERKLE_DSL_WIDTH: usize = 6;

/// Number of public inputs.
pub const MERKLE_DSL_PUBLIC_INPUTS: usize = 2;

/// Build the Merkle membership CircuitDescriptor.
pub fn merkle_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // ========================================================================
    // C1: Position validity (degree 4 polynomial).
    // pos * (pos - 1) * (pos - 2) * (pos - 3) == 0
    //
    // Expanded: pos^4 - 6*pos^3 + 11*pos^2 - 6*pos == 0
    //
    // Terms:
    //   +1 * pos^4
    //   -6 * pos^3
    //  +11 * pos^2
    //   -6 * pos
    // ========================================================================
    let p = pyana_circuit::field::BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            // pos^4
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION, col::POSITION],
            },
            // -6 * pos^3
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION],
            },
            // +11 * pos^2
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![col::POSITION, col::POSITION],
            },
            // -6 * pos
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION],
            },
        ],
    });

    // ========================================================================
    // C2: Parent hash correctness.
    // parent == hash_fact(current, [sib0, sib1, sib2, position])
    //
    // The Hash constraint evaluates: hash_fact(input_cols[0], &input_cols[1..]) - output_col
    // ========================================================================
    constraints.push(ConstraintExpr::Hash {
        output_col: col::PARENT,
        input_cols: vec![col::CURRENT, col::SIB0, col::SIB1, col::SIB2, col::POSITION],
    });

    // ========================================================================
    // C3: Chain continuity — next[CURRENT] == local[PARENT].
    // Transition { next_col, local_col } evaluates: next[next_col] - local[local_col]
    // ========================================================================
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CURRENT,
        local_col: col::PARENT,
    });

    // ========================================================================
    // Boundary constraints
    // ========================================================================
    let boundaries = vec![
        // First row: current == leaf_hash (pi[0])
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CURRENT,
            pi_index: pi::LEAF_HASH,
        },
        // Last row: parent == expected_root (pi[1])
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: pi::EXPECTED_ROOT,
        },
    ];

    // ========================================================================
    // Column definitions
    // ========================================================================
    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: col::PARENT,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "pyana-merkle-membership-dsl-v1".into(),
        trace_width: MERKLE_DSL_WIDTH,
        max_degree: 5, // Hash with 5 input_cols has degree 5; position_valid is degree 4
        columns,
        constraints,
        boundaries,
        public_input_count: MERKLE_DSL_PUBLIC_INPUTS,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the Merkle membership descriptor.
pub fn merkle_dsl_circuit() -> DslCircuit {
    DslCircuit::new(merkle_circuit_descriptor())
}

/// Generate a valid Merkle membership trace for the DSL circuit.
///
/// Produces a trace of `depth` rows (padded to next power of two if needed).
/// Each row represents one level of the 4-ary Merkle tree.
///
/// The DSL version uses `hash_fact(current, [sib0, sib1, sib2, position])` for
/// the parent hash, matching the `Hash` constraint semantics.
///
/// Returns (trace, public_inputs) where public_inputs = [leaf_hash, root].
pub fn generate_merkle_trace(
    leaf_hash: BabyBear,
    depth: usize,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let position = BabyBear::new((i % 4) as u32);
        let sib0 = BabyBear::new((i * 3 + 1) as u32);
        let sib1 = BabyBear::new((i * 3 + 2) as u32);
        let sib2 = BabyBear::new((i * 3 + 3) as u32);

        // Parent = hash_fact(current, [sib0, sib1, sib2, position])
        let parent = hash_fact(current, &[sib0, sib1, sib2, position]);

        let row = vec![current, sib0, sib1, sib2, position, parent];
        trace.push(row);
        current = parent;
    }

    // Pad trace to power of two (minimum 2 rows).
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        // Padding rows: chain continuity requires next[CURRENT] == local[PARENT].
        // So each padding row starts with the previous row's parent.
        let prev_parent = trace.last().unwrap()[col::PARENT];
        let pad_position = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_parent = hash_fact(prev_parent, &[pad_sib0, pad_sib1, pad_sib2, pad_position]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_position,
            pad_parent,
        ]);
    }

    // The root is the parent of the last row.
    let root = trace.last().unwrap()[col::PARENT];
    let public_inputs = vec![leaf_hash, root];

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    #[test]
    fn descriptor_has_correct_structure() {
        let desc = merkle_circuit_descriptor();
        assert_eq!(desc.trace_width, MERKLE_DSL_WIDTH);
        assert_eq!(desc.public_input_count, MERKLE_DSL_PUBLIC_INPUTS);
        assert_eq!(desc.name, "pyana-merkle-membership-dsl-v1");
        assert_eq!(desc.max_degree, 5);

        // Should have: 1 Polynomial (position) + 1 Hash (parent) + 1 Transition (chain) = 3
        assert_eq!(desc.constraints.len(), 3);

        // Should have 2 boundary constraints (leaf + root)
        assert_eq!(desc.boundaries.len(), 2);

        // Column count
        assert_eq!(desc.columns.len(), 6);
    }

    #[test]
    fn descriptor_validates() {
        let desc = merkle_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "merkle descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn valid_trace_evaluates_to_zero() {
        let leaf = BabyBear::new(12345);
        let (trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Check every row except the last (Transition constraint references next row).
        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Row {i} should satisfy all constraints, got nonzero"
            );
        }

        // Last row: Transition constraint evaluates next[CURRENT] - local[PARENT].
        // For the last row, "next" wraps to the first row in the STARK verifier.
        // This wrap-around may produce a nonzero value, which is expected —
        // the STARK verifier handles boundary enforcement separately.
    }

    #[test]
    fn tampered_parent_hash_detected() {
        let leaf = BabyBear::new(12345);
        let (mut trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper with the parent hash on row 1
        trace[1][col::PARENT] = BabyBear::new(99999);

        let result = circuit.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered parent hash should violate Hash constraint"
        );
    }

    #[test]
    fn tampered_sibling_detected() {
        let leaf = BabyBear::new(12345);
        let (mut trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper with sib0 on row 2 (parent hash will no longer match)
        trace[2][col::SIB0] = BabyBear::new(777777);

        let result = circuit.eval_constraints(&trace[2], &trace[3], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Tampered sibling should violate Hash constraint"
        );
    }

    #[test]
    fn invalid_position_detected() {
        let leaf = BabyBear::new(12345);
        let (mut trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Set position to 5 (invalid: only 0-3 allowed)
        trace[0][col::POSITION] = BabyBear::new(5);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Invalid position (5) should violate polynomial constraint"
        );
    }

    #[test]
    fn chain_continuity_violation_detected() {
        let leaf = BabyBear::new(12345);
        let (mut trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Break chain: change row 2's current so it no longer matches row 1's parent
        let original_current = trace[2][col::CURRENT];
        trace[2][col::CURRENT] = original_current + BabyBear::ONE;

        // Evaluate row 1 with next=row 2: Transition checks next[CURRENT] == local[PARENT]
        let result = circuit.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Broken chain continuity should violate Transition constraint"
        );
    }

    #[test]
    fn stark_prove_verify() {
        let leaf = BabyBear::new(42);
        let (trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify should succeed on valid Merkle trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn stark_rejects_wrong_leaf_pi() {
        let leaf = BabyBear::new(42);
        let (trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Verify with wrong leaf hash
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::LEAF_HASH] = BabyBear::new(99999);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong leaf hash public input"
        );
    }

    #[test]
    fn stark_rejects_wrong_root_pi() {
        let leaf = BabyBear::new(42);
        let (trace, pi) = generate_merkle_trace(leaf, 4);
        let circuit = merkle_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Verify with wrong root
        let mut wrong_pi = pi.clone();
        wrong_pi[pi::EXPECTED_ROOT] = BabyBear::new(11111);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "STARK should reject proof with wrong root public input"
        );
    }

    #[test]
    fn boundary_constraints_correct() {
        let circuit = merkle_dsl_circuit();
        let pi = vec![
            BabyBear::new(100), // leaf_hash
            BabyBear::new(200), // expected_root
        ];
        let boundaries = circuit.boundary_constraints(&pi, 4);

        assert_eq!(boundaries.len(), 2);

        // First: leaf hash on row 0, col CURRENT
        assert_eq!(boundaries[0].row, 0);
        assert_eq!(boundaries[0].col, col::CURRENT);
        assert_eq!(boundaries[0].value, BabyBear::new(100));

        // Last: root on last row, col PARENT
        assert_eq!(boundaries[1].row, 3);
        assert_eq!(boundaries[1].col, col::PARENT);
        assert_eq!(boundaries[1].value, BabyBear::new(200));
    }

    #[test]
    fn larger_depth_prove_verify() {
        // Test with depth 8 (already a power of two, no padding needed)
        let leaf = BabyBear::new(7777);
        let (trace, pi) = generate_merkle_trace(leaf, 8);
        let circuit = merkle_dsl_circuit();

        assert_eq!(trace.len(), 8);

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify with depth 8 should succeed: {:?}",
            result.err()
        );
    }
}
