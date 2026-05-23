//! Backward-compatible re-exports for predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates`].

pub use crate::dsl::predicates::{
    PREDICATE_DIFF_BITS, PredicateAir, PredicateProof, PredicateType, PredicateWitness,
    compute_fact_commitment, prove_predicate, prove_predicate_dsl, verify_predicate,
    verify_predicate_dsl,
};
