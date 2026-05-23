//! Compound predicate DSL tests.
//!
//! The production implementation has been moved to `pyana_dsl_runtime::predicates::compound`.
//! This file re-exports from there and adds tests.

pub use pyana_dsl_runtime::predicates::compound::*;

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, StarkAir};

    #[test]
    fn descriptor_validates() {
        let desc = compound_predicate_circuit_descriptor();
        assert!(
            desc.validate().is_ok(),
            "compound predicate descriptor should validate: {:?}",
            desc.validate().err()
        );
    }

    #[test]
    fn compound_and_true_true_equals_true() {
        let (trace, pi) = generate_compound_trace(&[true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "AND(true, true) should pass");
    }

    #[test]
    fn compound_or_true_false_equals_true() {
        let (trace, pi) = generate_compound_trace(&[true, false], CompoundOp::Or);
        let circuit = compound_predicate_dsl_circuit();
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(result, BabyBear::ZERO, "OR(true, false) should pass");
    }

    #[test]
    fn compound_stark_prove_verify() {
        let (trace, pi) = generate_compound_trace(&[true, true], CompoundOp::And);
        let circuit = compound_predicate_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &pi);
        let result = stark::verify(&circuit, &proof, &pi);
        assert!(
            result.is_ok(),
            "STARK prove/verify failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_prove_compound_dsl_api() {
        let formula = BooleanFormula::And(vec![0, 1]);
        let proof =
            prove_compound_dsl(&[true, true], &formula, None).expect("should produce proof");
        assert_eq!(proof.formula, formula);
    }
}
