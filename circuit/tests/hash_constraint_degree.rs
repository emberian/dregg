//! Regression tests for BUG 1: hash-constraint degree misreport.
//!
//! A `ConstraintExpr::Hash { output, inputs }` enforces `hash_fact(inputs) - output == 0`.
//! The `hash_fact` value is an opaque, non-algebraic helper supplied by the witness, so the
//! committed AIR constraint is degree 1 in the trace columns (exactly like Hash2to1 /
//! Hash4to1 / MerkleHash). Previously `degree()` returned `input_cols.len()`, conflating the
//! number of inputs with algebraic degree. That caused `validate()` to reject perfectly valid
//! hash circuits with `ConstraintDegreeExceeded`.
//!
//! These tests prove:
//!  1. A valid hash-constraint circuit (many inputs, low max_degree) now validates.
//!  2. `Hash::degree()` reports exactly 1, matching the other opaque-hash variants.
//!  3. Genuinely-too-high-degree circuits are STILL rejected (validation stays sound).

use dregg_circuit::dsl::circuit::{
    CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, MAX_CONSTRAINT_DEGREE, PolyTerm,
    ProgramValidationError,
};
use dregg_circuit::field::BabyBear;

/// Build a descriptor with a single Hash constraint over `n_inputs` input columns plus one
/// output column. `max_degree` is set deliberately low (2) to demonstrate that a degree-1
/// hash constraint must pass even when many input columns are referenced.
fn hash_descriptor(n_inputs: usize, max_degree: usize) -> CircuitDescriptor {
    let trace_width = n_inputs + 1; // inputs in [0..n_inputs), output at index n_inputs
    let output_col = n_inputs;
    let input_cols: Vec<usize> = (0..n_inputs).collect();

    let columns: Vec<ColumnDef> = (0..trace_width)
        .map(|i| ColumnDef {
            name: format!("c{i}"),
            index: i,
            kind: if i == output_col {
                ColumnKind::Hash
            } else {
                ColumnKind::Value
            },
        })
        .collect();

    CircuitDescriptor {
        name: "hash_degree_test".to_string(),
        trace_width,
        max_degree,
        columns,
        constraints: vec![ConstraintExpr::Hash {
            output_col,
            input_cols,
        }],
        boundaries: vec![],
        public_input_count: 0,
        lookup_tables: vec![],
    }
}

#[test]
fn hash_constraint_reports_degree_one() {
    // Many inputs, but the algebraic degree of `hash(inputs) - output` is 1.
    for n in [1usize, 2, 4, 8, 16, 33] {
        let c = ConstraintExpr::Hash {
            output_col: n,
            input_cols: (0..n).collect(),
        };
        assert_eq!(
            c.degree(),
            1,
            "Hash with {n} inputs should report algebraic degree 1, matching Hash2to1/Hash4to1/MerkleHash"
        );
    }

    // Sanity: the other opaque-hash variants already report 1, confirming consistency.
    assert_eq!(
        ConstraintExpr::Hash2to1 {
            output_col: 2,
            input_col_a: 0,
            input_col_b: 1,
        }
        .degree(),
        1
    );
    assert_eq!(
        ConstraintExpr::Hash4to1 {
            output_col: 4,
            input_cols: [0, 1, 2, 3],
        }
        .degree(),
        1
    );
}

#[test]
fn valid_hash_circuit_previously_rejected_now_validates() {
    // 16 inputs with a strict max_degree of 2. Under the old bug this reported degree 16
    // and was rejected with ConstraintDegreeExceeded. It must now validate cleanly.
    let descriptor = hash_descriptor(16, 2);
    let result = descriptor.validate();
    assert!(
        result.is_ok(),
        "valid 16-input hash circuit must validate (was over-conservatively rejected by BUG 1): {:?}",
        result.err()
    );

    // Even with max_degree == 1 the degree-1 hash constraint must pass.
    let tight = hash_descriptor(8, 1);
    assert!(
        tight.validate().is_ok(),
        "degree-1 hash constraint must pass under max_degree=1: {:?}",
        tight.validate().err()
    );
}

#[test]
fn genuinely_high_degree_constraint_still_rejected() {
    // A Polynomial term that multiplies 5 distinct columns has algebraic degree 5.
    // With max_degree == 4 it MUST be rejected. This guards that the BUG 1 fix did not
    // simply loosen / disable degree validation.
    let trace_width = 6;
    let columns: Vec<ColumnDef> = (0..trace_width)
        .map(|i| ColumnDef {
            name: format!("c{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();

    let descriptor = CircuitDescriptor {
        name: "high_degree_poly".to_string(),
        trace_width,
        max_degree: 4,
        columns,
        constraints: vec![ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![0, 1, 2, 3, 4], // product of 5 columns => degree 5
            }],
        }],
        boundaries: vec![],
        public_input_count: 0,
        lookup_tables: vec![],
    };

    match descriptor.validate() {
        Err(ProgramValidationError::ConstraintDegreeExceeded {
            constraint_index,
            degree,
            max_degree,
        }) => {
            assert_eq!(constraint_index, 0);
            assert_eq!(degree, 5);
            assert_eq!(max_degree, 4);
        }
        other => panic!("expected ConstraintDegreeExceeded for degree-5 polynomial, got {other:?}"),
    }
}

#[test]
fn descriptor_max_degree_over_global_cap_still_rejected() {
    // The global cap on max_degree itself must still be enforced.
    let mut descriptor = hash_descriptor(4, 2);
    descriptor.max_degree = MAX_CONSTRAINT_DEGREE + 1;
    match descriptor.validate() {
        Err(ProgramValidationError::DegreeTooHigh { degree }) => {
            assert_eq!(degree, MAX_CONSTRAINT_DEGREE + 1);
        }
        other => panic!("expected DegreeTooHigh, got {other:?}"),
    }
}
