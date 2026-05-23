//! Backward-compatible re-exports for Merkle AIR types.
//!
//! The production implementation lives in [`crate::dsl::membership`].
//! Legacy types are defined in [`crate::merkle_types`].

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH, create_test_witness,
};
