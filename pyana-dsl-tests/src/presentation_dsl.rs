//! Presentation composition AIR expressed as a CircuitDescriptor.
//!
//! The presentation proof is a "meta-AIR" that binds multiple sub-proofs together
//! via a composition commitment. Its constraints are primarily EQUALITY checks
//! (public inputs match trace columns) and one NON-ZERO check (composition
//! commitment is not all zeros).
//!
//! # Trace Layout (single row, 11 columns)
//!
//! | Column | Name                          | Description                       |
//! |--------|-------------------------------|-----------------------------------|
//! | 0      | federation_root               | Root of trust (public)            |
//! | 1..4   | request_predicate[0..3]       | Action binding commitment (4 elems)|
//! | 5      | timestamp                     | Freshness timestamp               |
//! | 6      | presentation_tag              | Blinded tag (unlinkable)          |
//! | 7..10  | revealed_facts_commitment[0..3]| Selective disclosure commitment  |
//!
//! # Constraints
//!
//! 1. Each trace column equals its corresponding public input (11 PiBinding constraints).
//!    These are simple consistency checks: the trace row must match the declared
//!    public inputs exactly.
//!
//! # Boundary Constraints
//!
//! - All 11 columns bound to their respective pi values on the first (only) row.
//!
//! # Non-zero check (TODO)
//!
//! The real presentation AIR also enforces that the composition_commitment is non-zero
//! (preventing unbound sub-proofs). This requires a `ConditionalNonzero` constraint
//! variant that is being added by another agent. We note it as a TODO.

use pyana_circuit::field::BabyBear;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr,
    DslCircuit,
};

/// Presentation trace width (11 columns).
pub const PRESENTATION_WIDTH: usize = 11;

/// Public input count (11 values matching the trace columns).
pub const PRESENTATION_PI_COUNT: usize = 11;

/// Column indices for the presentation trace.
pub mod col {
    pub const FEDERATION_ROOT: usize = 0;
    pub const REQUEST_PRED_START: usize = 1; // 1..4
    pub const TIMESTAMP: usize = 5;
    pub const PRESENTATION_TAG: usize = 6;
    pub const REVEALED_FACTS_START: usize = 7; // 7..10
}

/// Construct the presentation composition AIR as a CircuitDescriptor.
///
/// This encodes 11 PiBinding constraints (one per trace column) that enforce
/// the trace row matches the public inputs. The presentation AIR's real purpose
/// is as a composition layer that cryptographically binds sub-proofs together.
pub fn presentation_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // ========================================================================
    // C1-C11: Each column equals its corresponding public input.
    //   trace[col] - pi[col] == 0
    // ========================================================================
    for i in 0..PRESENTATION_WIDTH {
        constraints.push(ConstraintExpr::PiBinding { col: i, pi_index: i });
    }

    // ========================================================================
    // TODO: Non-zero check on composition_commitment.
    //
    // The real presentation verifier rejects proofs where composition_commitment
    // is all zeros (meaning sub-proofs are not bound together). This requires a
    // `ConditionalNonzero` or `AtLeastOne` constraint variant. When available:
    //
    //   constraints.push(ConstraintExpr::AtLeastOne {
    //       cols: vec![7, 8, 9, 10], // revealed_facts_commitment columns
    //   });
    //
    // For now, this is enforced at the verification level (not in-circuit).
    // ========================================================================

    // ========================================================================
    // Boundary constraints: bind all columns to their pi values on the first row.
    // ========================================================================
    let boundaries: Vec<BoundaryDef> = (0..PRESENTATION_WIDTH)
        .map(|i| BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: i,
            pi_index: i,
        })
        .collect();

    // Column definitions
    let columns = vec![
        ColumnDef { name: "federation_root".into(), index: col::FEDERATION_ROOT, kind: ColumnKind::Hash },
        ColumnDef { name: "request_predicate[0]".into(), index: col::REQUEST_PRED_START, kind: ColumnKind::Hash },
        ColumnDef { name: "request_predicate[1]".into(), index: col::REQUEST_PRED_START + 1, kind: ColumnKind::Hash },
        ColumnDef { name: "request_predicate[2]".into(), index: col::REQUEST_PRED_START + 2, kind: ColumnKind::Hash },
        ColumnDef { name: "request_predicate[3]".into(), index: col::REQUEST_PRED_START + 3, kind: ColumnKind::Hash },
        ColumnDef { name: "timestamp".into(), index: col::TIMESTAMP, kind: ColumnKind::Value },
        ColumnDef { name: "presentation_tag".into(), index: col::PRESENTATION_TAG, kind: ColumnKind::Hash },
        ColumnDef { name: "revealed_facts[0]".into(), index: col::REVEALED_FACTS_START, kind: ColumnKind::Hash },
        ColumnDef { name: "revealed_facts[1]".into(), index: col::REVEALED_FACTS_START + 1, kind: ColumnKind::Hash },
        ColumnDef { name: "revealed_facts[2]".into(), index: col::REVEALED_FACTS_START + 2, kind: ColumnKind::Hash },
        ColumnDef { name: "revealed_facts[3]".into(), index: col::REVEALED_FACTS_START + 3, kind: ColumnKind::Hash },
    ];

    CircuitDescriptor {
        name: "pyana-presentation-dsl-v1".into(),
        trace_width: PRESENTATION_WIDTH,
        max_degree: 1, // All constraints are degree 1 (linear)
        columns,
        constraints,
        boundaries,
        public_input_count: PRESENTATION_PI_COUNT,
    }
}

/// Create a DslCircuit from the presentation descriptor.
pub fn presentation_dsl_circuit() -> DslCircuit {
    DslCircuit::new(presentation_circuit_descriptor())
}

/// Generate a valid presentation trace (single row matching public inputs).
///
/// Returns (trace, public_inputs).
pub fn generate_valid_presentation_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let federation_root = BabyBear::new(1000000);
    let request_pred = [
        BabyBear::new(111),
        BabyBear::new(222),
        BabyBear::new(333),
        BabyBear::new(444),
    ];
    let timestamp = BabyBear::new(1716000000);
    let presentation_tag = BabyBear::new(987654);
    let revealed_facts = [
        BabyBear::new(555),
        BabyBear::new(666),
        BabyBear::new(777),
        BabyBear::new(888),
    ];

    // Build the trace row
    let row = vec![
        federation_root,
        request_pred[0],
        request_pred[1],
        request_pred[2],
        request_pred[3],
        timestamp,
        presentation_tag,
        revealed_facts[0],
        revealed_facts[1],
        revealed_facts[2],
        revealed_facts[3],
    ];

    // Public inputs match the trace exactly
    let public_inputs = row.clone();

    // Pad to 2 rows (STARK minimum)
    let trace = vec![row.clone(), row];

    (trace, public_inputs)
}

/// Generate an INVALID presentation trace (federation_root mismatch).
pub fn generate_invalid_presentation_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, pi) = generate_valid_presentation_trace();
    // Tamper: change federation_root in the trace but not in pi
    trace[0][col::FEDERATION_ROOT] = BabyBear::new(999);
    trace[1][col::FEDERATION_ROOT] = BabyBear::new(999);
    (trace, pi)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    #[test]
    fn presentation_descriptor_validates() {
        let desc = presentation_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "presentation descriptor should pass validation: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn presentation_descriptor_has_correct_width() {
        let desc = presentation_circuit_descriptor();
        assert_eq!(desc.trace_width, PRESENTATION_WIDTH);
        assert_eq!(desc.trace_width, 11);
    }

    #[test]
    fn presentation_descriptor_constraint_count() {
        let desc = presentation_circuit_descriptor();
        // 11 PiBinding constraints (one per column)
        assert_eq!(desc.constraints.len(), 11);
    }

    #[test]
    fn presentation_descriptor_all_pi_bindings() {
        let desc = presentation_circuit_descriptor();
        let pi_binding_count = desc.constraints.iter().filter(|c| {
            matches!(c, ConstraintExpr::PiBinding { .. })
        }).count();
        assert_eq!(pi_binding_count, 11, "All constraints should be PiBinding");
    }

    #[test]
    fn presentation_dsl_valid_trace_evaluates_to_zero() {
        let (trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() { &trace[i + 1] } else { &trace[i] };
            let result = circuit.eval_constraints(&trace[i], next, &pi, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "DslCircuit should evaluate to ZERO on valid presentation trace row {i}"
            );
        }
    }

    #[test]
    fn presentation_dsl_invalid_trace_evaluates_nonzero() {
        let (trace, pi) = generate_invalid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        let next = &trace[1];
        let result = circuit.eval_constraints(&trace[0], next, &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "DslCircuit should produce NON-ZERO on invalid presentation trace"
        );
    }

    #[test]
    fn presentation_dsl_rejects_wrong_request_predicate() {
        let (mut trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change request_predicate[1] in the trace
        trace[0][col::REQUEST_PRED_START + 1] = BabyBear::new(9999);
        trace[1][col::REQUEST_PRED_START + 1] = BabyBear::new(9999);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong request predicate"
        );
    }

    #[test]
    fn presentation_dsl_rejects_wrong_presentation_tag() {
        let (mut trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change presentation_tag in the trace
        trace[0][col::PRESENTATION_TAG] = BabyBear::new(11111);
        trace[1][col::PRESENTATION_TAG] = BabyBear::new(11111);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong presentation tag"
        );
    }

    #[test]
    fn presentation_dsl_rejects_wrong_timestamp() {
        let (mut trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change timestamp in the trace
        trace[0][col::TIMESTAMP] = BabyBear::new(0);
        trace[1][col::TIMESTAMP] = BabyBear::new(0);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong timestamp"
        );
    }

    #[test]
    fn presentation_dsl_rejects_wrong_revealed_facts() {
        let (mut trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        // Tamper: change revealed_facts[2] in the trace
        trace[0][col::REVEALED_FACTS_START + 2] = BabyBear::new(42);
        trace[1][col::REVEALED_FACTS_START + 2] = BabyBear::new(42);

        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject trace with wrong revealed facts commitment"
        );
    }

    #[test]
    fn presentation_dsl_boundary_constraints_correct() {
        let (_, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let boundaries = circuit.boundary_constraints(&pi, 2);

        // 11 boundary constraints (one per column, all on first row)
        assert_eq!(boundaries.len(), 11);

        // Verify each boundary matches the corresponding pi value
        for (i, bc) in boundaries.iter().enumerate() {
            assert_eq!(bc.col, i, "boundary {i} should target column {i}");
            assert_eq!(bc.row, 0, "all boundaries should be on row 0");
            assert_eq!(bc.value, pi[i], "boundary {i} value should match pi[{i}]");
        }
    }

    #[test]
    fn presentation_dsl_stark_prove_verify() {
        let (trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Presentation DSL STARK prove/verify should succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn presentation_dsl_stark_rejects_wrong_pi() {
        let (trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();

        let proof = stark::prove(&circuit, &trace, &pi);

        // Tamper with public inputs
        let mut wrong_pi = pi;
        wrong_pi[0] = BabyBear::new(11111);

        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(
            result.is_err(),
            "Should reject proof with wrong public inputs"
        );
    }
}
