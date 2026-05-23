//! Predicate proof DSL tests.
//!
//! The production implementation has been moved to `pyana_dsl_runtime::predicates::base`.
//! This file re-exports from there and adds tests.

pub use pyana_dsl_runtime::predicates::base::*;

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::poseidon2::hash_fact;
    use pyana_circuit::stark::{self, StarkAir};
    use pyana_dsl_runtime::circuit::DslCircuit;

    /// Dummy fact commitment for basic tests.
    fn test_commitment() -> BabyBear {
        BabyBear::new(999999)
    }

    /// Helper: create a fact commitment and its components for derivation tests.
    fn test_fact_commitment_parts(value: BabyBear) -> (BabyBear, BabyBear, BabyBear) {
        let fact_hash = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        let commitment = compute_fact_commitment(fact_hash, state_root);
        (commitment, fact_hash, state_root)
    }

    #[test]
    fn test_predicate_descriptor_validates() {
        let descriptor = predicate_descriptor();
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
    fn test_predicate_gte_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace(25, 18, test_commitment(), PredicateOp::Gte);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "GTE 25 >= 18 should pass");
    }

    #[test]
    fn test_predicate_neq_valid() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace(42, 0, test_commitment(), PredicateOp::Neq);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "NEQ 42 != 0 should pass");
    }

    #[test]
    fn test_predicate_stark_prove_verify_gte() {
        let descriptor = predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_predicate_trace(1000, 500, test_commitment(), PredicateOp::Gte);
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(result.is_ok(), "STARK verify failed: {:?}", result.err());
    }

    #[test]
    fn test_prove_predicate_dsl_api() {
        let fh = hash_fact(
            BabyBear::new(100),
            &[BabyBear::new(1000), BabyBear::ZERO, BabyBear::ZERO],
        );
        let sr = BabyBear::new(99999);
        let commitment = compute_fact_commitment(fh, sr);

        let witness = PredicateWitness {
            private_value: 1000,
            threshold: 500,
            op: PredicateOp::Gte,
            fact_commitment: commitment,
            fact_hash: Some(fh),
            state_root: Some(sr),
            blinding: None,
        };

        let proof = prove_predicate_dsl(&witness).expect("should produce proof");
        let result = verify_predicate_dsl(&proof, BabyBear::new(500), commitment);
        assert!(result.is_ok(), "DSL verify failed: {:?}", result.err());
    }
}
