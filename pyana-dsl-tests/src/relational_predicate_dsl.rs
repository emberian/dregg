//! Relational predicate DSL tests.
//!
//! The production implementation has been moved to `pyana_dsl_runtime::predicates::relational`.
//! This file re-exports from there and adds tests.

pub use pyana_dsl_runtime::predicates::relational::*;

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};
    use pyana_dsl_runtime::circuit::DslCircuit;

    #[test]
    fn test_relational_descriptor_validates() {
        let descriptor = relational_predicate_descriptor();
        let result = descriptor.validate();
        assert!(
            result.is_ok(),
            "Descriptor validation failed: {:?}",
            result.err()
        );
        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
    }

    #[test]
    fn test_relational_gt_valid() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GT 100 > 50 should pass");
    }

    #[test]
    fn test_relational_stark_prove_verify_gt() {
        let descriptor = relational_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_relational_trace(100, 111, 50, 222, RelationalOp::GreaterThan);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify GT failed: {:?}", result.err());
    }

    #[test]
    fn test_prove_relational_dsl_api() {
        let witness = RelationalWitness {
            value_a: 100,
            blinding_a: 111,
            value_b: 50,
            blinding_b: 222,
            op: RelationalOp::GreaterThan,
            verify_commitments: true,
        };
        let proof = prove_relational_dsl(&witness).expect("should produce proof");
        let ca = compute_commitment(BabyBear::new(100), BabyBear::new(111));
        let cb = compute_commitment(BabyBear::new(50), BabyBear::new(222));
        let result = verify_relational_dsl(&proof, ca, cb);
        assert!(result.is_ok(), "DSL verify failed: {:?}", result.err());
    }
}
