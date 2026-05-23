//! Backward-compatible re-exports for arithmetic predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates::arithmetic`].

pub use crate::dsl::predicates::{
    ArithExpr, ArithPredicate, ArithmeticPredicateProof, CompareOp,
    compute_arithmetic_fact_commitment, prove_arithmetic_dsl, verify_arithmetic_dsl,
    verify_arithmetic_predicate,
};
