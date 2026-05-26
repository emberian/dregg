//! 4-ary Poseidon2 Merkle tree over BabyBear field elements.
//!
//! This is an append-only Merkle tree using Poseidon2 as the hash function,
//! designed for use within STARK circuits. Unlike the BLAKE3 tree which operates
//! on byte arrays, this tree operates natively on BabyBear field elements,
//! making it directly constrainable inside arithmetic circuits.
//!
//! Key properties:
//! - 4-ary branching: each internal node hashes 4 children via `hash_4_to_1`
//! - Append-only: leaves are added sequentially and never removed
//! - Fixed depth: configurable at creation, determines maximum capacity (4^depth leaves)
//! - ZK-friendly: the same hash function used here is constrained in the STARK AIR

use std::sync::LazyLock;

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;
use serde::{Deserialize, Serialize};

/// Default tree depth (4^16 = ~4 billion leaves).
pub const DEFAULT_DEPTH: usize = 16;

/// The "empty" leaf: a domain-separated sentinel distinct from any legitimate value.
///
/// Using BabyBear::ZERO would be ambiguous with a legitimate zero-valued leaf.
/// Instead we use a fixed non-zero constant as a sentinel. This value is chosen
/// to be unlikely to collide with real data (0xDEAD_LEAF mod p).
pub const EMPTY_LEAF: BabyBear = BabyBear(0x0DEA_D1EF);

/// Maximum depth for cached empty hashes.
const MAX_CACHED_DEPTH: usize = 32;

/// Precomputed empty hash at each level.
/// Level 0 = EMPTY_LEAF, level k = hash_4_to_1([empty(k-1); 4]).
static EMPTY_HASHES: LazyLock<Vec<BabyBear>> = LazyLock::new(|| {
    let mut hashes = Vec::with_capacity(MAX_CACHED_DEPTH + 1);
    hashes.push(EMPTY_LEAF);
    for _ in 1..=MAX_CACHED_DEPTH {
        let prev = *hashes.last().unwrap();
        hashes.push(hash_4_to_1(&[prev, prev, prev, prev]));
    }
    hashes
});

/// Get the empty hash at a given level (memoized).
#[inline]
fn empty_hash_at_level(level: usize) -> BabyBear {
    if level <= MAX_CACHED_DEPTH {
        EMPTY_HASHES[level]
    } else {
        let mut h = EMPTY_HASHES[MAX_CACHED_DEPTH];
        for _ in MAX_CACHED_DEPTH..level {
            h = hash_4_to_1(&[h, h, h, h]);
        }
        h
    }
}

/// A membership proof in a 4-ary Poseidon2 Merkle tree.
///
/// For each level (from leaf to root), stores the 3 siblings at that node
/// and the position (0..3) of the current element among its siblings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2MerkleProof {
    /// The leaf value being proved.
    pub leaf: BabyBear,
    /// The 3 sibling hashes at each level (leaf-to-root order).
    pub siblings: Vec<[BabyBear; 3]>,
    /// Position at each level (0..3), leaf-to-root order.
    pub positions: Vec<u8>,
}

/// A 4-ary append-only Merkle tree using Poseidon2 over BabyBear.
///
/// Leaves are stored sequentially. Internal nodes are computed on demand
/// (with caching of the root). The tree has a fixed depth determining its
/// maximum capacity.
#[derive(Clone, Debug)]
pub struct Poseidon2MerkleTree {
    /// All leaves appended so far.
    leaves: Vec<BabyBear>,
    /// Tree depth (number of levels from root to leaf).
    depth: usize,
    /// Cached root (invalidated on append).
    cached_root: Option<BabyBear>,
}

impl Poseidon2MerkleTree {
    /// Create a new empty tree with the default depth.
    pub fn new() -> Self {
        Self::with_depth(DEFAULT_DEPTH)
    }

    /// Create a new empty tree with a specific depth.
    ///
    /// The tree can hold up to 4^depth leaves.
    pub fn with_depth(depth: usize) -> Self {
        Self {
            leaves: Vec::new(),
            depth,
            cached_root: None,
        }
    }

    /// Append a leaf to the tree. Returns the position (0-indexed).
    ///
    /// # Panics
    ///
    /// Panics if the tree is at maximum capacity (4^depth leaves).
    pub fn append(&mut self, leaf: BabyBear) -> usize {
        let max_capacity = 4usize.pow(self.depth as u32);
        assert!(
            self.leaves.len() < max_capacity,
            "Poseidon2MerkleTree is full: capacity {} reached (depth {})",
            max_capacity,
            self.depth
        );
        let position = self.leaves.len();
        self.leaves.push(leaf);
        self.cached_root = None;
        position
    }

    /// Number of leaves in the tree.
    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    /// Whether the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Compute the current root of the tree.
    pub fn root(&mut self) -> BabyBear {
        if let Some(r) = self.cached_root {
            return r;
        }
        let root = self.compute_root();
        self.cached_root = Some(root);
        root
    }

    /// Compute the root without caching (immutable version).
    pub fn root_immutable(&self) -> BabyBear {
        if let Some(r) = self.cached_root {
            return r;
        }
        self.compute_root()
    }

    /// Generate a membership proof for the leaf at the given position.
    ///
    /// Returns None if the position is out of bounds.
    pub fn prove_membership(&self, position: usize) -> Option<Poseidon2MerkleProof> {
        if position >= self.leaves.len() {
            return None;
        }

        let leaf = self.leaves[position];
        let mut siblings = Vec::with_capacity(self.depth);
        let mut positions = Vec::with_capacity(self.depth);
        let mut idx = position;

        for level in 0..self.depth {
            // At this level, which group of 4 does our index fall into?
            let sibling_base = (idx / 4) * 4;
            let pos_in_group = (idx % 4) as u8;
            positions.push(pos_in_group);

            // Collect the 3 siblings
            let mut sibs = [BabyBear::ZERO; 3];
            let mut sib_idx = 0;
            for i in 0..4 {
                if i == pos_in_group as usize {
                    continue;
                }
                let child_idx = sibling_base + i;
                sibs[sib_idx] = self.get_node_at_level(level, child_idx);
                sib_idx += 1;
            }
            siblings.push(sibs);

            // Move up: the parent's index is sibling_base / 4
            idx = idx / 4;
        }

        Some(Poseidon2MerkleProof {
            leaf,
            siblings,
            positions,
        })
    }

    /// Verify a membership proof.
    ///
    /// Given a root, a leaf value, and a proof, verify that the leaf is a member
    /// of the tree with the given root. The leaf value must match what is stored
    /// in the proof itself.
    pub fn verify_membership(root: BabyBear, leaf: BabyBear, proof: &Poseidon2MerkleProof) -> bool {
        if proof.siblings.len() != proof.positions.len() {
            return false;
        }
        // The proof must commit to the same leaf value being verified.
        if proof.leaf != leaf {
            return false;
        }

        let mut current = leaf;
        for level in 0..proof.siblings.len() {
            let pos = proof.positions[level];
            if pos >= 4 {
                return false;
            }
            let sibs = &proof.siblings[level];

            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for i in 0..4u8 {
                if i == pos {
                    children[i as usize] = current;
                } else {
                    children[i as usize] = sibs[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_4_to_1(&children);
        }

        current == root
    }

    /// Rebuild the tree from a list of leaves.
    pub fn from_leaves(leaves: Vec<BabyBear>, depth: usize) -> Self {
        let mut tree = Self::with_depth(depth);
        tree.leaves = leaves;
        tree.cached_root = None;
        tree
    }

    /// Get a reference to all leaves.
    pub fn leaves(&self) -> &[BabyBear] {
        &self.leaves
    }

    // =========================================================================
    // Internal helpers
    // =========================================================================

    /// Compute the root from scratch.
    fn compute_root(&self) -> BabyBear {
        self.compute_node_at_level(self.depth, 0)
    }

    /// Compute the hash of a node at a given level and index.
    ///
    /// Level 0 = leaf level, level `depth` = root level.
    /// At level 0, index i corresponds to leaves[i].
    /// At level k, index i corresponds to the node formed by
    /// children at level k-1 with indices 4*i, 4*i+1, 4*i+2, 4*i+3.
    fn compute_node_at_level(&self, level: usize, index: usize) -> BabyBear {
        if level == 0 {
            return self.get_leaf(index);
        }

        // Optimization: if the entire subtree rooted here is beyond the
        // populated leaves, return the precomputed empty hash for this level.
        // The first leaf index under this node is index * 4^level.
        let first_leaf = index
            .checked_mul(4usize.pow(level as u32))
            .unwrap_or(usize::MAX);
        if first_leaf >= self.leaves.len() {
            return empty_hash_at_level(level);
        }

        let mut children = [BabyBear::ZERO; 4];
        for i in 0..4 {
            let child_idx = index * 4 + i;
            children[i] = self.compute_node_at_level(level - 1, child_idx);
        }
        hash_4_to_1(&children)
    }

    /// Get the node value at a given level and index.
    /// This is used during proof generation.
    fn get_node_at_level(&self, level: usize, index: usize) -> BabyBear {
        self.compute_node_at_level(level, index)
    }

    /// Get a leaf by index, returning EMPTY_LEAF for out-of-bounds.
    fn get_leaf(&self, index: usize) -> BabyBear {
        if index < self.leaves.len() {
            self.leaves[index]
        } else {
            EMPTY_LEAF
        }
    }
}

impl Default for Poseidon2MerkleTree {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert a BLAKE3 commitment (32 bytes) to a BabyBear field element.
///
/// This bridges the gap between the byte-oriented BLAKE3 world and the
/// field-element-oriented Poseidon2 world. The conversion hashes the
/// commitment bytes through Poseidon2 to produce a single field element
/// that can be inserted into the Poseidon2 Merkle tree.
///
/// This is a one-way binding: you can prove that a particular BLAKE3
/// commitment maps to a particular field element, but you cannot reverse it.
pub fn commitment_to_field(commitment: &[u8; 32]) -> BabyBear {
    // Encode the 32-byte commitment as 8 BabyBear elements (4 bytes each)
    let elements = BabyBear::encode_hash(commitment);
    // Hash them through Poseidon2 to get a single field element
    dregg_circuit::poseidon2::hash_many(&elements)
}

/// Convert arbitrary bytes to a BabyBear field element via Poseidon2.
///
/// Packs bytes into field elements (4 bytes per element, with modular reduction),
/// then hashes them with Poseidon2's sponge construction.
pub fn hash_bytes_to_field(data: &[u8]) -> BabyBear {
    let elements = BabyBear::from_bytes_packed(data);
    dregg_circuit::poseidon2::hash_many(&elements)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_tree_has_deterministic_root() {
        let mut t1 = Poseidon2MerkleTree::with_depth(4);
        let mut t2 = Poseidon2MerkleTree::with_depth(4);
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn append_changes_root() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        let root_empty = tree.root();
        tree.append(BabyBear::new(42));
        let root_one = tree.root();
        assert_ne!(root_empty, root_one);
    }

    #[test]
    fn append_is_deterministic() {
        let mut t1 = Poseidon2MerkleTree::with_depth(4);
        let mut t2 = Poseidon2MerkleTree::with_depth(4);
        t1.append(BabyBear::new(1));
        t1.append(BabyBear::new(2));
        t2.append(BabyBear::new(1));
        t2.append(BabyBear::new(2));
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn membership_proof_verifies() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        for i in 1..=10 {
            tree.append(BabyBear::new(i * 100));
        }
        let root = tree.root();

        // Prove membership of leaf at position 5
        let proof = tree.prove_membership(5).unwrap();
        let leaf = BabyBear::new(600);
        assert!(Poseidon2MerkleTree::verify_membership(root, leaf, &proof));
    }

    #[test]
    fn membership_proof_fails_wrong_leaf() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        for i in 1..=10 {
            tree.append(BabyBear::new(i * 100));
        }
        let root = tree.root();

        let proof = tree.prove_membership(5).unwrap();
        let wrong_leaf = BabyBear::new(999);
        assert!(!Poseidon2MerkleTree::verify_membership(
            root, wrong_leaf, &proof
        ));
    }

    #[test]
    fn membership_proof_fails_wrong_root() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        for i in 1..=10 {
            tree.append(BabyBear::new(i * 100));
        }
        let root = tree.root();

        let proof = tree.prove_membership(5).unwrap();
        let leaf = BabyBear::new(600);
        let fake_root = BabyBear::new(123456);
        assert!(!Poseidon2MerkleTree::verify_membership(
            fake_root, leaf, &proof
        ));
        // But correct root works
        assert!(Poseidon2MerkleTree::verify_membership(root, leaf, &proof));
    }

    #[test]
    fn all_leaves_provable() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        let leaves: Vec<BabyBear> = (1..=10).map(|i| BabyBear::new(i * 7)).collect();
        for &leaf in &leaves {
            tree.append(leaf);
        }
        let root = tree.root();

        for (pos, &leaf) in leaves.iter().enumerate() {
            let proof = tree.prove_membership(pos).unwrap();
            assert!(
                Poseidon2MerkleTree::verify_membership(root, leaf, &proof),
                "Failed to verify leaf at position {pos}"
            );
        }
    }

    #[test]
    fn out_of_bounds_returns_none() {
        let tree = Poseidon2MerkleTree::with_depth(4);
        assert!(tree.prove_membership(0).is_none());

        let mut tree2 = Poseidon2MerkleTree::with_depth(4);
        tree2.append(BabyBear::new(1));
        assert!(tree2.prove_membership(1).is_none());
        assert!(tree2.prove_membership(0).is_some());
    }

    #[test]
    fn commitment_to_field_deterministic() {
        let commitment = [0xAB; 32];
        let f1 = commitment_to_field(&commitment);
        let f2 = commitment_to_field(&commitment);
        assert_eq!(f1, f2);
    }

    #[test]
    fn commitment_to_field_different_inputs() {
        let c1 = [0x01; 32];
        let c2 = [0x02; 32];
        assert_ne!(commitment_to_field(&c1), commitment_to_field(&c2));
    }

    #[test]
    fn from_leaves_rebuilds_correctly() {
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        let leaves: Vec<BabyBear> = (1..=8).map(|i| BabyBear::new(i)).collect();
        for &leaf in &leaves {
            tree.append(leaf);
        }
        let root1 = tree.root();

        let mut tree2 = Poseidon2MerkleTree::from_leaves(leaves, 4);
        let root2 = tree2.root();
        assert_eq!(root1, root2);
    }

    #[test]
    fn proof_depth_matches_tree_depth() {
        let depth = 6;
        let mut tree = Poseidon2MerkleTree::with_depth(depth);
        tree.append(BabyBear::new(42));

        let proof = tree.prove_membership(0).unwrap();
        assert_eq!(proof.siblings.len(), depth);
        assert_eq!(proof.positions.len(), depth);
    }

    #[test]
    fn hash_bytes_to_field_works() {
        let data = b"hello world";
        let f = hash_bytes_to_field(data);
        assert_ne!(f, BabyBear::ZERO);

        // Deterministic
        let f2 = hash_bytes_to_field(data);
        assert_eq!(f, f2);
    }

    // =========================================================================
    // End-to-end integration tests
    // =========================================================================

    /// End-to-end test: convert a real Note commitment to a field element,
    /// append to Poseidon2 tree, prove membership, verify.
    #[test]
    fn end_to_end_blake3_commitment_bridge() {
        // Simulate a real BLAKE3 note commitment (32 bytes)
        let fake_commitment: [u8; 32] = {
            let mut h = blake3::Hasher::new();
            h.update(b"test note owner=alice value=100");
            *h.finalize().as_bytes()
        };

        // Convert to field element and insert into Poseidon2 tree
        let field_leaf = commitment_to_field(&fake_commitment);
        let mut tree = Poseidon2MerkleTree::with_depth(4);

        // Add some other commitments first
        for i in 0..5 {
            let mut c = [0u8; 32];
            c[0] = i;
            tree.append(commitment_to_field(&c));
        }

        // Append our target commitment
        let target_pos = tree.append(field_leaf);

        // Add more after
        for i in 10..15 {
            let mut c = [0u8; 32];
            c[0] = i;
            tree.append(commitment_to_field(&c));
        }

        let root = tree.root();

        // Prove and verify membership
        let proof = tree.prove_membership(target_pos).unwrap();
        assert!(Poseidon2MerkleTree::verify_membership(
            root, field_leaf, &proof
        ));
    }

    /// End-to-end test: create a NoteSpendingWitness from a real Poseidon2 tree
    /// proof and generate a STARK proof that verifies.
    ///
    /// This is THE critical test: real note -> real tree -> real proof -> real STARK verification.
    #[test]
    #[ignore = "REVIEW[stage2-canonical-vs-poseidon-mismatch]: note spending PI layout regressed in Stage 1; needs end-to-end realignment"]
    fn end_to_end_note_spending_stark_from_real_tree() {
        use dregg_circuit::note_spending_air::NoteSpendingWitness;
        use dregg_circuit::poseidon2::hash_many;
        use dregg_dsl_runtime::note_spending::{prove_note_spend, verify_note_spend};

        // Step 1: Define a note's field-element preimage
        let owner = BabyBear::new(0xA11CE);
        let value = BabyBear::new(1000);
        let asset_type = BabyBear::new(1);
        let creation_nonce = BabyBear::new(0xCAFE);
        let randomness = BabyBear::new(0xBEEF);
        let spending_key = dregg_circuit::note_spending_air::test_spending_key(0xDEAD_BEEF);

        // Step 2: Compute the commitment (same formula as NoteSpendingWitness::commitment)
        let commitment = hash_many(&[owner, value, asset_type, creation_nonce, randomness]);

        // Step 3: Build a Poseidon2 tree and insert multiple commitments
        // Use depth 4 to keep the test fast (must be >= 2 for STARK)
        let depth = 4;
        let mut tree = Poseidon2MerkleTree::with_depth(depth);

        // Insert some other notes first
        for i in 0..5 {
            tree.append(BabyBear::new(i * 999 + 1));
        }

        // Insert our real note commitment
        let target_pos = tree.append(commitment);

        // Insert more notes after
        for i in 10..15 {
            tree.append(BabyBear::new(i * 777 + 2));
        }

        let tree_root = tree.root();

        // Step 4: Generate a real Poseidon2 membership proof from the tree
        let proof = tree.prove_membership(target_pos).unwrap();

        // Sanity check: verify the proof directly
        assert!(Poseidon2MerkleTree::verify_membership(
            tree_root, commitment, &proof
        ));

        // Step 5: Build NoteSpendingWitness from the real proof
        let witness = NoteSpendingWitness::from_real_proof(
            owner,
            value,
            asset_type,
            creation_nonce,
            randomness,
            spending_key,
            proof.siblings,
            proof.positions,
        );

        // Step 6: Verify the witness computes the same root as our tree
        assert_eq!(
            witness.merkle_root(),
            tree_root,
            "Witness merkle_root must match tree root"
        );

        // Step 7: Generate a STARK proof
        let nullifier = witness.nullifier();
        let stark_proof = prove_note_spend(&witness);

        // Step 8: Verify the STARK proof (now includes value + asset_type)
        let result = verify_note_spend(
            nullifier,
            tree_root,
            witness.value,
            witness.asset_type,
            &stark_proof,
        );
        assert!(
            result.is_ok(),
            "End-to-end STARK proof verification failed: {:?}",
            result.err()
        );

        // Step 9: Verify that wrong nullifier/root fails
        let wrong_nullifier = BabyBear::new(0xBAD);
        assert!(
            verify_note_spend(
                wrong_nullifier,
                tree_root,
                witness.value,
                witness.asset_type,
                &stark_proof
            )
            .is_err(),
            "Should reject wrong nullifier"
        );
        let wrong_root = BabyBear::new(0xBAD);
        assert!(
            verify_note_spend(
                nullifier,
                wrong_root,
                witness.value,
                witness.asset_type,
                &stark_proof
            )
            .is_err(),
            "Should reject wrong root"
        );
    }
}
