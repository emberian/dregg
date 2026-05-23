//! Nullifier set: an append-only set of revealed nullifiers.
//!
//! When a note is spent, its nullifier is revealed and added to this set.
//! Double-spend detection is simply checking set membership. The set also
//! supports non-membership proofs (proving a note is NOT spent) via a
//! Merkle tree over the nullifier hashes.
//!
//! # Performance
//!
//! Uses `BTreeSet<Nullifier>` internally for O(log N) insert and lookup.
//! Previous implementation used `Vec::insert` at a binary-search position
//! which was O(N) due to element shifting on every insert.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::note::{NoteError, Nullifier};

/// A Merkle membership proof for a single nullifier in the set.
///
/// This proves that a specific nullifier exists at a given position in the
/// Merkle tree built over all nullifiers. Used as part of non-membership proofs
/// to demonstrate that neighbor elements are genuinely in the set.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleMembershipProof {
    /// The nullifier whose membership is being proved.
    pub element: Nullifier,
    /// Index of the element in the sorted nullifier list.
    pub index: usize,
    /// Sibling hashes along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[u8; 32]>,
}

/// A non-membership proof: demonstrates that a nullifier is NOT in the set.
///
/// Uses adjacent-neighbor technique: shows two consecutive nullifiers in the
/// sorted set that bracket the absent value, plus Merkle membership proofs for
/// each neighbor (proving they ARE in the set).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The nullifier being proved absent.
    pub absent: Nullifier,
    /// The nullifier just before the absent one (if any).
    pub left_neighbor: Option<Nullifier>,
    /// The nullifier just after the absent one (if any).
    pub right_neighbor: Option<Nullifier>,
    /// Merkle membership proof for the left neighbor (if present).
    pub left_membership_proof: Option<MerkleMembershipProof>,
    /// Merkle membership proof for the right neighbor (if present).
    pub right_membership_proof: Option<MerkleMembershipProof>,
    /// Root of the nullifier tree at the time of proof generation.
    pub root: [u8; 32],
}

/// Append-only set of revealed nullifiers.
/// Supports efficient membership checks and non-membership proofs.
///
/// Uses `BTreeSet` for O(log N) insert and contains operations.
/// For non-membership proofs, the set is materialized into a sorted vec
/// on demand (the BTreeSet iterator yields elements in sorted order).
#[derive(Clone, Debug)]
pub struct NullifierSet {
    /// All nullifiers ever published, kept in a BTreeSet for O(log N) operations.
    nullifiers: BTreeSet<Nullifier>,
}

impl NullifierSet {
    /// Create an empty nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: BTreeSet::new(),
        }
    }

    /// Number of nullifiers in the set.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }

    /// Add a nullifier (note is now spent). Returns error if already present (double-spend).
    ///
    /// O(log N) via BTreeSet insertion.
    pub fn insert(&mut self, nullifier: Nullifier) -> Result<(), NoteError> {
        if !self.nullifiers.insert(nullifier) {
            Err(NoteError::DoubleSpend { nullifier })
        } else {
            Ok(())
        }
    }

    /// Check if a nullifier is in the set (note is spent).
    ///
    /// O(log N) via BTreeSet contains.
    pub fn contains(&self, nullifier: &Nullifier) -> bool {
        self.nullifiers.contains(nullifier)
    }

    /// Get the sorted list of nullifiers (materializes from BTreeSet iterator).
    /// Used internally for Merkle tree construction and non-membership proofs.
    fn sorted_vec(&self) -> Vec<Nullifier> {
        self.nullifiers.iter().copied().collect()
    }

    /// Prove non-membership (note is NOT spent).
    /// Returns None if the nullifier IS in the set.
    pub fn prove_non_membership(&self, nullifier: &Nullifier) -> Option<NonMembershipProof> {
        if self.nullifiers.contains(nullifier) {
            return None; // It IS in the set, can't prove non-membership.
        }

        let sorted = self.sorted_vec();
        // Binary search in the sorted vec to find the adjacent neighbors.
        let idx = sorted.binary_search(nullifier).unwrap_err();

        let left_neighbor = if idx > 0 { Some(sorted[idx - 1]) } else { None };
        let right_neighbor = if idx < sorted.len() {
            Some(sorted[idx])
        } else {
            None
        };
        let left_membership_proof = if idx > 0 {
            Some(self.prove_membership_from_sorted(&sorted, idx - 1))
        } else {
            None
        };
        let right_membership_proof = if idx < sorted.len() {
            Some(self.prove_membership_from_sorted(&sorted, idx))
        } else {
            None
        };
        Some(NonMembershipProof {
            absent: *nullifier,
            left_neighbor,
            right_neighbor,
            left_membership_proof,
            right_membership_proof,
            root: self.root(),
        })
    }

    /// Generate a Merkle membership proof for the element at the given index
    /// in the sorted nullifier list.
    ///
    /// The Merkle tree is built over the sorted list of nullifier hashes as leaves.
    /// Each leaf is: BLAKE3("pyana-nullifier-leaf v1", nullifier).
    /// Internal nodes are: BLAKE3("pyana-nullifier-node v1", left || right).
    fn prove_membership_from_sorted(
        &self,
        sorted: &[Nullifier],
        index: usize,
    ) -> MerkleMembershipProof {
        let leaves: Vec<[u8; 32]> = sorted.iter().map(|n| Self::leaf_hash(&n.0)).collect();
        let siblings = Self::merkle_path(&leaves, index);
        MerkleMembershipProof {
            element: sorted[index],
            index,
            siblings,
        }
    }

    /// Hash a leaf node.
    fn leaf_hash(data: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-nullifier-leaf v1");
        hasher.update(data);
        *hasher.finalize().as_bytes()
    }

    /// Hash two children into a parent node.
    fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-nullifier-node v1");
        hasher.update(left);
        hasher.update(right);
        *hasher.finalize().as_bytes()
    }

    /// Compute the Merkle path (sibling hashes from leaf to root) for a given index.
    fn merkle_path(leaves: &[[u8; 32]], index: usize) -> Vec<[u8; 32]> {
        if leaves.len() <= 1 {
            return vec![];
        }
        let mut siblings = Vec::new();
        let mut current_level = leaves.to_vec();
        let mut idx = index;

        while current_level.len() > 1 {
            // Pad to even length with a zero hash.
            if current_level.len() % 2 != 0 {
                current_level.push([0u8; 32]);
            }
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            siblings.push(current_level[sibling_idx]);

            // Build next level.
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
            idx /= 2;
        }
        siblings
    }

    /// Compute the Merkle root from leaves.
    fn merkle_root_from_leaves(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return [0u8; 32];
        }
        let mut current_level = leaves.to_vec();
        while current_level.len() > 1 {
            if current_level.len() % 2 != 0 {
                current_level.push([0u8; 32]);
            }
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
        }
        current_level[0]
    }

    /// Verify a Merkle membership proof against a given root.
    fn verify_membership_proof(proof: &MerkleMembershipProof, root: &[u8; 32]) -> bool {
        let mut current = Self::leaf_hash(&proof.element.0);
        let mut idx = proof.index;
        for sibling in &proof.siblings {
            if idx % 2 == 0 {
                current = Self::node_hash(&current, sibling);
            } else {
                current = Self::node_hash(sibling, &current);
            }
            idx /= 2;
        }
        current == *root
    }

    /// Current root of the nullifier set (Merkle tree root over all nullifier hashes).
    ///
    /// Leaves are domain-separated hashes of each nullifier (in sorted order).
    /// Internal nodes hash their two children. This produces a proper Merkle tree
    /// that supports membership proofs for non-membership verification.
    pub fn root(&self) -> [u8; 32] {
        if self.nullifiers.is_empty() {
            return [0u8; 32];
        }
        // BTreeSet iterates in sorted order, matching the old Vec behavior.
        let leaves: Vec<[u8; 32]> = self
            .nullifiers
            .iter()
            .map(|n| Self::leaf_hash(&n.0))
            .collect();
        Self::merkle_root_from_leaves(&leaves)
    }

    /// Verify a non-membership proof against the current root.
    ///
    /// This verifies:
    /// 1. The proof's root matches the given root.
    /// 2. The neighbors (if present) are properly ordered around the absent value.
    /// 3. The neighbors are actually IN the set (via Merkle membership proofs).
    /// 4. The neighbors are adjacent (no element between them).
    pub fn verify_non_membership(proof: &NonMembershipProof, root: &[u8; 32]) -> bool {
        if proof.root != *root {
            return false;
        }

        // Check ordering: left < absent < right.
        if let Some(left) = &proof.left_neighbor {
            if left.0 >= proof.absent.0 {
                return false;
            }
        }
        if let Some(right) = &proof.right_neighbor {
            if right.0 <= proof.absent.0 {
                return false;
            }
        }

        // Verify the left neighbor's Merkle membership proof.
        if let Some(left) = &proof.left_neighbor {
            match &proof.left_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *left {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Left neighbor claimed but no membership proof
            }
        }

        // Verify the right neighbor's Merkle membership proof.
        if let Some(right) = &proof.right_neighbor {
            match &proof.right_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *right {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Right neighbor claimed but no membership proof
            }
        }

        // Verify adjacency: left and right neighbors must be at consecutive indices.
        if let (Some(left_proof), Some(right_proof)) =
            (&proof.left_membership_proof, &proof.right_membership_proof)
        {
            if right_proof.index != left_proof.index + 1 {
                return false;
            }
        }

        true
    }
}

impl Default for NullifierSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::note::Note;

    fn make_nullifier(seed: u8) -> Nullifier {
        let owner = {
            let mut k = [0u8; 32];
            k[0] = seed;
            k
        };
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [seed; 32];
        let note = Note::with_randomness(owner, fields, randomness);
        let spending_key = [seed.wrapping_add(100); 32];
        note.nullifier(&spending_key)
    }

    #[test]
    fn test_nullifier_set_insert_and_contains() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        assert!(!set.contains(&n));
        set.insert(n).unwrap();
        assert!(set.contains(&n));
    }

    #[test]
    fn test_nullifier_set_double_spend_rejected() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        set.insert(n).unwrap();
        let result = set.insert(n);
        assert_eq!(result, Err(NoteError::DoubleSpend { nullifier: n }));
    }

    #[test]
    fn test_nullifier_set_multiple_inserts() {
        let mut set = NullifierSet::new();
        for i in 0..10 {
            let n = make_nullifier(i);
            set.insert(n).unwrap();
        }
        assert_eq!(set.len(), 10);

        // All should be present.
        for i in 0..10 {
            assert!(set.contains(&make_nullifier(i)));
        }
    }

    #[test]
    fn test_nullifier_set_non_membership_proof() {
        let mut set = NullifierSet::new();
        let n1 = make_nullifier(1);
        let n2 = make_nullifier(2);
        let absent = make_nullifier(3);

        set.insert(n1).unwrap();
        set.insert(n2).unwrap();

        // absent is not in the set.
        assert!(!set.contains(&absent));

        let proof = set.prove_non_membership(&absent).unwrap();
        let root = set.root();
        assert!(NullifierSet::verify_non_membership(&proof, &root));
    }

    #[test]
    fn test_nullifier_set_non_membership_present_returns_none() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);
        set.insert(n).unwrap();

        // Can't prove non-membership for something that IS in the set.
        assert!(set.prove_non_membership(&n).is_none());
    }

    #[test]
    fn test_nullifier_set_root_changes_on_insert() {
        let mut set = NullifierSet::new();
        let root_empty = set.root();

        set.insert(make_nullifier(1)).unwrap();
        let root_one = set.root();
        assert_ne!(root_empty, root_one);

        set.insert(make_nullifier(2)).unwrap();
        let root_two = set.root();
        assert_ne!(root_one, root_two);
    }
}
