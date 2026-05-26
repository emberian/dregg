//! Arithmetic predicate DSL tests.
//!
//! The production implementation has been moved to `dregg_dsl_runtime::predicates::arithmetic`.
//! This file re-exports from there and adds tests.

pub use dregg_dsl_runtime::predicates::arithmetic::*;

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::stark::StarkAir;
    use dregg_dsl_runtime::circuit::DslCircuit;

    fn test_commitment() -> BabyBear {
        BabyBear::new(888888)
    }

    fn build_and_trace(
        inputs: &[u32],
        predicate: &ArithPredicate,
    ) -> (DslCircuit, Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let num_inputs = inputs.len();
        let (descriptor, _layout, _ca, _cb, _dk) =
            build_arithmetic_predicate_descriptor(predicate, num_inputs);
        let circuit = DslCircuit::new(descriptor);
        let (trace, pi) = generate_full_trace(inputs, predicate, test_commitment());
        (circuit, trace, pi)
    }

    fn assert_valid(inputs: &[u32], predicate: &ArithPredicate) {
        let (circuit, trace, pi) = build_and_trace(inputs, predicate);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "Expected valid for {:?}", predicate);
    }

    fn assert_invalid(inputs: &[u32], predicate: &ArithPredicate) {
        let (circuit, trace, pi) = build_and_trace(inputs, predicate);
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Expected invalid for {:?}",
            predicate
        );
    }

    #[test]
    fn test_arithmetic_add_valid() {
        let predicate = ArithPredicate::ExprGte(
            ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1))),
            250,
        );
        assert_valid(&[100, 200], &predicate);
    }

    #[test]
    fn test_arithmetic_add_adversarial() {
        let predicate = ArithPredicate::ExprGte(
            ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1))),
            100,
        );
        assert_invalid(&[10, 20], &predicate);
    }

    #[test]
    fn test_prove_arithmetic_dsl_api() {
        let predicate = ArithPredicate::ExprGte(
            ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1))),
            250,
        );
        let proof = prove_arithmetic_dsl(&[100, 200], &predicate, test_commitment())
            .expect("should produce proof");
        let result = verify_arithmetic_dsl(&proof, proof.threshold, test_commitment());
        assert!(result.is_ok(), "DSL verify failed: {:?}", result.err());
    }
}
