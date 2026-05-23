//! Backward-compatible re-exports for fold types.
//!
//! The production implementation lives in [`crate::dsl::fold`].

pub use crate::dsl::fold::{
    FOLD_AIR_WIDTH, FoldAir, FoldWitness, RemovedFact, build_membership_proof, build_shared_tree,
    col, compute_root_transition_hash, compute_test_checks_commitment, create_test_fold,
    prove_fold_stark, verify_fold_stark, verify_root_transition,
};

pub use crate::merkle_types::{MerkleAir, MerkleLevelWitness, MerkleWitness};
