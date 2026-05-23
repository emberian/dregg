//! Backward-compatible re-exports for compound predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates::compound`].

pub use crate::dsl::predicates::{
    BooleanFormula, CompoundOp, CompoundPredicateProof, Gate, MAX_COMPOUND_PREDICATES,
    prove_compound_predicate, verify_compound_predicate,
};
