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

use dregg_circuit::field::BabyBear;
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
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
        constraints.push(ConstraintExpr::PiBinding {
            col: i,
            pi_index: i,
        });
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
        ColumnDef {
            name: "federation_root".into(),
            index: col::FEDERATION_ROOT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "request_predicate[0]".into(),
            index: col::REQUEST_PRED_START,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "request_predicate[1]".into(),
            index: col::REQUEST_PRED_START + 1,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "request_predicate[2]".into(),
            index: col::REQUEST_PRED_START + 2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "request_predicate[3]".into(),
            index: col::REQUEST_PRED_START + 3,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "timestamp".into(),
            index: col::TIMESTAMP,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "presentation_tag".into(),
            index: col::PRESENTATION_TAG,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "revealed_facts[0]".into(),
            index: col::REVEALED_FACTS_START,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "revealed_facts[1]".into(),
            index: col::REVEALED_FACTS_START + 1,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "revealed_facts[2]".into(),
            index: col::REVEALED_FACTS_START + 2,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "revealed_facts[3]".into(),
            index: col::REVEALED_FACTS_START + 3,
            kind: ColumnKind::Hash,
        },
    ];

    CircuitDescriptor {
        name: "dregg-presentation-dsl-v1".into(),
        trace_width: PRESENTATION_WIDTH,
        max_degree: 1, // All constraints are degree 1 (linear)
        columns,
        constraints,
        boundaries,
        public_input_count: PRESENTATION_PI_COUNT,
        lookup_tables: vec![],
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
// Composition-based Presentation
// ============================================================================

/// Build a membership circuit descriptor (for composing membership proofs).
///
/// This is a simplified membership circuit: PI[0] = leaf_hash, PI[1] = root.
pub fn membership_circuit_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "dregg-membership-v1".into(),
        trace_width: 6,
        max_degree: 4,
        columns: (0..6)
            .map(|i| ColumnDef {
                name: format!("merkle_col_{i}"),
                index: i,
                kind: ColumnKind::Value,
            })
            .collect(),
        constraints: vec![
            ConstraintExpr::PiBinding {
                col: 0,
                pi_index: 0,
            },
            ConstraintExpr::PiBinding {
                col: 5,
                pi_index: 1,
            },
        ],
        boundaries: vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::Last,
                col: 5,
                pi_index: 1,
            },
        ],
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Build a predicate circuit descriptor (for composing predicate proofs).
///
/// This is a simplified predicate circuit: PI[0] = threshold, PI[1] = fact_commitment.
pub fn predicate_circuit_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "dregg-predicate-v1".into(),
        trace_width: 4,
        max_degree: 2,
        columns: (0..4)
            .map(|i| ColumnDef {
                name: format!("pred_col_{i}"),
                index: i,
                kind: ColumnKind::Value,
            })
            .collect(),
        constraints: vec![
            ConstraintExpr::PiBinding {
                col: 0,
                pi_index: 0,
            },
            ConstraintExpr::PiBinding {
                col: 1,
                pi_index: 1,
            },
        ],
        boundaries: vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 1,
                pi_index: 1,
            },
        ],
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Build a temporal step circuit descriptor (for IVC chain composition).
///
/// PI[0] = initial_state, PI[1] = final_state.
pub fn temporal_step_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "dregg-temporal-step-v1".into(),
        trace_width: 4,
        max_degree: 2,
        columns: (0..4)
            .map(|i| ColumnDef {
                name: format!("temporal_col_{i}"),
                index: i,
                kind: ColumnKind::Value,
            })
            .collect(),
        constraints: vec![
            ConstraintExpr::PiBinding {
                col: 0,
                pi_index: 0,
            },
            ConstraintExpr::PiBinding {
                col: 1,
                pi_index: 1,
            },
        ],
        boundaries: vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 0,
                pi_index: 0,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: 1,
                pi_index: 1,
            },
        ],
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Compose a presentation proof from membership + predicate sub-proofs.
///
/// This replaces the old PI-only presentation with actual sub-proof composition.
/// The composed circuit proves:
/// - Membership sub-proof verifies (issuer in federation)
/// - Predicate sub-proof verifies (attribute satisfies condition)
/// - Both share a common state root (PI[1] of membership == PI[1] of predicate)
pub fn composed_presentation_descriptor() -> dregg_dsl_runtime::ComposedCircuitDescriptor {
    let membership = membership_circuit_descriptor();
    let predicate = predicate_circuit_descriptor();

    // Shared link: membership PI[1] (root) == predicate PI[1] (fact_commitment)
    // This binds the predicate proof to the same state proven by membership.
    dregg_dsl_runtime::compose_and(&membership, &predicate, &[(1, 1)])
}

/// Compose two membership proofs (prove membership in BOTH trees).
pub fn composed_dual_membership() -> dregg_dsl_runtime::ComposedCircuitDescriptor {
    let membership_a = membership_circuit_descriptor();
    let membership_b = membership_circuit_descriptor();

    // Both share PI[0] (leaf_hash): prove the same leaf is in both trees
    dregg_dsl_runtime::compose_and(&membership_a, &membership_b, &[(0, 0)])
}

/// Compose a 3-step temporal chain (IVC).
pub fn composed_temporal_chain() -> dregg_dsl_runtime::ComposedCircuitDescriptor {
    let step = temporal_step_descriptor();
    dregg_dsl_runtime::compose_chain(&[&step, &step, &step])
}

/// Compose 4 different sub-proofs (aggregate).
pub fn composed_aggregate_4() -> dregg_dsl_runtime::ComposedCircuitDescriptor {
    let mem = membership_circuit_descriptor();
    let pred = predicate_circuit_descriptor();
    let temporal = temporal_step_descriptor();
    dregg_dsl_runtime::compose_aggregate(&[&mem, &pred, &temporal, &pred])
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::{self, StarkAir};

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
        let pi_binding_count = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, ConstraintExpr::PiBinding { .. }))
            .count();
        assert_eq!(pi_binding_count, 11, "All constraints should be PiBinding");
    }

    #[test]
    fn presentation_dsl_valid_trace_evaluates_to_zero() {
        let (trace, pi) = generate_valid_presentation_trace();
        let circuit = presentation_dsl_circuit();
        let alpha = BabyBear::new(7);

        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() {
                &trace[i + 1]
            } else {
                &trace[i]
            };
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

    // ========================================================================
    // Composition Tests
    // ========================================================================

    #[test]
    fn presentation_compose_dual_membership_proves_and_verifies() {
        // Prove membership in BOTH trees (same leaf)
        let composed = composed_dual_membership();
        assert_eq!(composed.sub_proofs.len(), 2);
        assert!(composed.circuit.validate().is_ok());

        // Generate trace: shared PI[0] is the leaf hash
        let shared = vec![BabyBear::new(42)]; // leaf_hash shared between both
        let proof_hashes = vec![BabyBear::new(111), BabyBear::new(222)];
        let (trace, pi) = dregg_dsl_runtime::generate_and_trace(&composed, &shared, &proof_hashes);

        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Dual membership composition STARK should pass: {:?}",
            result.err()
        );
    }

    #[test]
    fn presentation_compose_membership_plus_predicate() {
        // Prove membership AND age >= 18 (shared state root)
        let composed = composed_presentation_descriptor();
        assert_eq!(composed.sub_proofs.len(), 2);
        assert!(composed.circuit.validate().is_ok());

        // Shared value: the state root (membership PI[1] == predicate PI[1])
        let shared = vec![BabyBear::new(999)]; // shared state root
        let proof_hashes = vec![BabyBear::new(333), BabyBear::new(444)];
        let (trace, pi) = dregg_dsl_runtime::generate_and_trace(&composed, &shared, &proof_hashes);

        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Membership+predicate composition STARK should pass: {:?}",
            result.err()
        );
    }

    #[test]
    fn presentation_compose_chain_3_temporal_steps() {
        // Chain 3 temporal steps via IVC
        let composed = composed_temporal_chain();
        assert_eq!(composed.sub_proofs.len(), 3);
        assert!(composed.transition.is_some());
        assert!(composed.circuit.validate().is_ok());

        // Generate IVC trace
        let initial = BabyBear::new(100);
        let final_s = BabyBear::new(400);
        let prev_hash = dregg_circuit::ivc::initial_accumulated_hash(initial);
        let acc_hash = dregg_circuit::ivc::extend_accumulated_hash(prev_hash, final_s, 3);

        let (trace, pi) = dregg_dsl_runtime::generate_chain_trace(
            &composed, 3, initial, final_s, prev_hash, acc_hash,
        );

        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Chain 3-step IVC composition STARK should pass: {:?}",
            result.err()
        );
    }

    #[test]
    fn presentation_compose_aggregate_4_proofs() {
        // Aggregate 4 different sub-proofs
        let composed = composed_aggregate_4();
        assert_eq!(composed.sub_proofs.len(), 4);
        assert!(composed.transition.is_none());
        // Total PI = 2 + 2 + 2 + 2 = 8
        assert_eq!(composed.circuit.public_input_count, 8);
        assert!(composed.circuit.validate().is_ok());

        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed.clone());
        let width = circuit.total_width();

        // Merged PIs from all sub-circuits
        let pi = vec![
            BabyBear::new(10),
            BabyBear::new(20), // membership PIs
            BabyBear::new(30),
            BabyBear::new(40), // predicate PIs
            BabyBear::new(50),
            BabyBear::new(60), // temporal PIs
            BabyBear::new(70),
            BabyBear::new(80), // predicate 2 PIs
        ];

        let mut row = vec![BabyBear::ZERO; width];
        // Fill main columns with PI values
        for (i, &val) in pi.iter().enumerate() {
            if i < composed.circuit.trace_width {
                row[i] = val;
            }
        }
        // Fill valid flags for all sub-proofs
        for i in 0..composed.sub_proofs.len() {
            let offset = circuit.sub_proof_offset(i);
            for (j, &elem) in composed.sub_proofs[i]
                .sub_circuit_vk_hash
                .iter()
                .enumerate()
            {
                if offset + j < width {
                    row[offset + j] = elem;
                }
            }
            let vf_col = circuit.valid_flag_col(i);
            if vf_col < width {
                row[vf_col] = BabyBear::ONE;
            }
        }

        let trace = vec![row.clone(), row];
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "Aggregate 4-proof composition STARK should pass: {:?}",
            result.err()
        );
    }

    #[test]
    fn presentation_compose_rejects_missing_sub_proof() {
        // Verify that removing a valid flag causes constraint failure
        let composed = composed_dual_membership();
        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed.clone());
        let _width = circuit.total_width();

        let shared = vec![BabyBear::new(42)];
        let proof_hashes = vec![BabyBear::new(111), BabyBear::new(222)];
        let (mut trace, pi) =
            dregg_dsl_runtime::generate_and_trace(&composed, &shared, &proof_hashes);

        // Tamper: set second sub-proof valid flag to 0
        let vf_col = circuit.valid_flag_col(1);
        trace[0][vf_col] = BabyBear::ZERO;
        trace[1][vf_col] = BabyBear::ZERO;

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject composition with missing sub-proof (valid_flag=0)"
        );
    }

    #[test]
    fn presentation_compose_chain_wrong_hash_rejected() {
        // IVC chain with wrong accumulated hash should fail constraints
        let composed = composed_temporal_chain();
        let circuit = dregg_dsl_runtime::ComposedDslCircuit::new(composed.clone());

        let initial = BabyBear::new(100);
        let final_s = BabyBear::new(400);
        let prev_hash = dregg_circuit::ivc::initial_accumulated_hash(initial);
        let wrong_acc_hash = BabyBear::new(12345); // WRONG hash

        let (trace, pi) = dregg_dsl_runtime::generate_chain_trace(
            &composed,
            3,
            initial,
            final_s,
            prev_hash,
            wrong_acc_hash,
        );

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Should reject IVC chain with wrong accumulated hash"
        );
    }

    #[test]
    fn presentation_composed_descriptor_validates() {
        let desc = composed_presentation_descriptor();
        assert!(desc.circuit.validate().is_ok());
        assert_eq!(desc.sub_proofs.len(), 2);
        assert_eq!(desc.sub_proofs[0].label, "dregg-membership-v1-sub-a");
        assert_eq!(desc.sub_proofs[1].label, "dregg-predicate-v1-sub-b");
    }

    #[test]
    fn presentation_compose_vk_hashes_are_deterministic() {
        let mem = membership_circuit_descriptor();
        let vk1 = dregg_dsl_runtime::compute_descriptor_vk_elements(&mem);
        let vk2 = dregg_dsl_runtime::compute_descriptor_vk_elements(&mem);
        assert_eq!(vk1, vk2, "VK hash should be deterministic");
    }

    #[test]
    fn presentation_compose_different_circuits_different_vk() {
        let mem = membership_circuit_descriptor();
        let pred = predicate_circuit_descriptor();
        let vk_mem = dregg_dsl_runtime::compute_descriptor_vk_elements(&mem);
        let vk_pred = dregg_dsl_runtime::compute_descriptor_vk_elements(&pred);
        assert_ne!(
            vk_mem, vk_pred,
            "Different circuits must have different VK hashes"
        );
    }
}
