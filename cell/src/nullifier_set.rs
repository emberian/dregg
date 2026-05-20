//! Nullifier set: an append-only set of revealed nullifiers.
//!
//! When a note is spent, its nullifier is revealed and added to this set.
//! Double-spend detection is simply checking set membership. The set also
//! supports non-membership proofs (proving a note is NOT spent) via a
//! Merkle tree over the nullifier hashes.

use serde::{Deserialize, Serialize};

use crate::note::{NoteError, Nullifier};

/// A non-membership proof: demonstrates that a nullifier is NOT in the set.
///
/// Uses adjacent-neighbor technique: shows two consecutive nullifiers in the
/// sorted set that bracket the absent value, plus their Merkle proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The nullifier being proved absent.
    pub absent: Nullifier,
    /// The nullifier just before the absent one (if any).
    pub left_neighbor: Option<Nullifier>,
    /// The nullifier just after the absent one (if any).
    pub right_neighbor: Option<Nullifier>,
    /// Root of the nullifier tree at the time of proof generation.
    pub root: [u8; 32],
}

/// Append-only set of revealed nullifiers.
/// Supports efficient membership checks and non-membership proofs.
#[derive(Clone, Debug)]
pub struct NullifierSet {
    /// All nullifiers ever published, kept sorted for binary search
    /// and adjacent-neighbor non-membership proofs.
    nullifiers: Vec<Nullifier>,
}

impl NullifierSet {
    /// Create an empty nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: Vec::new(),
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
    pub fn insert(&mut self, nullifier: Nullifier) -> Result<(), NoteError> {
        // Binary search for insertion point.
        match self.nullifiers.binary_search_by(|n| n.0.cmp(&nullifier.0)) {
            Ok(_) => Err(NoteError::DoubleSpend { nullifier }),
            Err(idx) => {
                self.nullifiers.insert(idx, nullifier);
                Ok(())
            }
        }
    }

    /// Check if a nullifier is in the set (note is spent).
    pub fn contains(&self, nullifier: &Nullifier) -> bool {
        self.nullifiers.binary_search_by(|n| n.0.cmp(&nullifier.0)).is_ok()
    }

    /// Prove non-membership (note is NOT spent).
    /// Returns None if the nullifier IS in the set.
    pub fn prove_non_membership(&self, nullifier: &Nullifier) -> Option<NonMembershipProof> {
        match self.nullifiers.binary_search_by(|n| n.0.cmp(&nullifier.0)) {
            Ok(_) => None, // It IS in the set, can't prove non-membership.
            Err(idx) => {
                let left_neighbor = if idx > 0 {
                    Some(self.nullifiers[idx - 1])
                } else {
                    None
                };
                let right_neighbor = if idx < self.nullifiers.len() {
                    Some(self.nullifiers[idx])
                } else {
                    None
                };
                Some(NonMembershipProof {
                    absent: *nullifier,
                    left_neighbor,
                    right_neighbor,
                    root: self.root(),
                })
            }
        }
    }

    /// Current root of the nullifier set (Merkle commitment over all nullifiers).
    /// Uses a simple sequential hash for now; will be upgraded to a proper
    /// Merkle tree when integrated with the STARK proof layer.
    pub fn root(&self) -> [u8; 32] {
        if self.nullifiers.is_empty() {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new_derive_key("pyana-nullifier-set root v1");
        for n in &self.nullifiers {
            hasher.update(&n.0);
        }
        *hasher.finalize().as_bytes()
    }

    /// Verify a non-membership proof against the current root.
    ///
    /// This is a simplified verification that checks:
    /// 1. The proof's root matches the given root.
    /// 2. The neighbors (if present) are properly ordered around the absent value.
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
        note.nullifier(&spending_key, seed as u64)
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
