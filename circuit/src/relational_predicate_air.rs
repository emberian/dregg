//! Backward-compatible re-exports for relational predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates::relational`].

pub use crate::dsl::predicates::{
    RelationalOp as RelationType, RelationalPredicateProof, RelationalPredicateWitness,
    RelationalProof, RelationalWitness, compute_value_commitment, prove_relational,
    prove_relational_dsl, verify_relational, verify_relational_dsl,
};
