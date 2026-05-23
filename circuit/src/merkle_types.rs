//! Merkle types, witnesses, and helpers extracted from merkle_air.
//!
//! The `Air` implementation for `MerkleAir` remains in [`super::merkle_air`].

use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;

/// The tree depth (number of levels from leaf to root).
pub const TREE_DEPTH: usize = 16;

/// Trace width for the Merkle AIR.
pub const MERKLE_AIR_WIDTH: usize = 6;

/// Column indices.
pub mod col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
}

/// Witness for a single Merkle membership proof.
#[derive(Clone, Debug)]
pub struct MerkleWitness {
    /// The leaf hash (as a field element).
    pub leaf_hash: BabyBear,
    /// At each level: the position index (0..3) and three sibling hashes.
    pub levels: Vec<MerkleLevelWitness>,
    /// The expected root.
    pub expected_root: BabyBear,
}

/// Witness data for one level of the Merkle tree.
#[derive(Clone, Debug)]
pub struct MerkleLevelWitness {
    /// Position of the current node among its siblings (0..3).
    pub position: u8,
    /// The three sibling hashes at this level.
    pub siblings: [BabyBear; 3],
}

/// The Merkle membership AIR.
pub struct MerkleAir {
    /// The witness for the proof.
    pub witness: MerkleWitness,
}

impl MerkleAir {
    /// Create a new Merkle AIR from a witness.
    pub fn new(witness: MerkleWitness) -> Self {
        Self { witness }
    }

    /// Compute what the parent hash should be given the current hash, position, and siblings.
    /// If position is out of range (>3), returns ZERO (constraint will catch this).
    pub fn compute_parent(current: BabyBear, position: u8, siblings: &[BabyBear; 3]) -> BabyBear {
        if position > 3 {
            return BabyBear::ZERO;
        }
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for i in 0..4u8 {
            if i == position {
                children[i as usize] = current;
            } else {
                children[i as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        hash_4_to_1(&children)
    }
}

/// Helper: Create a Merkle witness for testing with a given depth.
pub fn create_test_witness(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let parent = MerkleAir::compute_parent(current, position, &siblings);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}
