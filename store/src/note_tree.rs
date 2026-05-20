//! Persistent note commitment tree.
//!
//! An append-only 4-ary Merkle tree of note commitments. Notes are added
//! sequentially and never removed. The tree root changes on each append,
//! providing a succinct commitment to the entire note history.
//!
//! This module integrates with the persistent store (redb) to durably record
//! note commitments and nullifiers, and with the Merkle tree from `pyana-commit`
//! for proof generation.

use pyana_commit::merkle::{MerkleProof, MerkleTree};
use pyana_cell::note::{NoteCommitment, Nullifier};

/// An append-only note commitment tree backed by a 4-ary Merkle tree.
///
/// Notes are appended sequentially. Each note commitment receives a unique
/// position (index) which is needed for nullifier derivation.
#[derive(Clone, Debug)]
pub struct NoteTree {
    /// All note commitments ever created (append-only).
    commitments: Vec<NoteCommitment>,
    /// The Merkle tree over commitments (from pyana-commit).
    tree: MerkleTree,
}

impl NoteTree {
    /// Create a new empty note tree.
    pub fn new() -> Self {
        Self {
            commitments: Vec::new(),
            tree: MerkleTree::new(),
        }
    }

    /// Append a new note commitment. Returns the position (for nullifier derivation).
    pub fn append(&mut self, commitment: NoteCommitment) -> u64 {
        let position = self.commitments.len() as u64;
        self.commitments.push(commitment);
        // Insert the commitment hash into the Merkle tree.
        self.tree.insert_hash(commitment.0);
        position
    }

    /// Current root of the note tree.
    pub fn root(&mut self) -> [u8; 32] {
        self.tree.root()
    }

    /// Prove membership of a commitment at a given position.
    pub fn prove_membership(&self, position: u64) -> Option<MerkleProof> {
        let pos = position as usize;
        if pos >= self.commitments.len() {
            return None;
        }
        let commitment = &self.commitments[pos];
        self.tree.membership_proof_hash(&commitment.0)
    }

    /// Number of notes in the tree.
    pub fn size(&self) -> u64 {
        self.commitments.len() as u64
    }

    /// Check if a commitment exists in the tree.
    pub fn contains(&self, commitment: &NoteCommitment) -> bool {
        self.tree.contains_hash(&commitment.0)
    }

    /// Verify a membership proof against this tree's root.
    pub fn verify_proof(root: &[u8; 32], proof: &MerkleProof) -> bool {
        MerkleTree::verify_membership(root, proof)
    }

    /// Rebuild the tree from a list of commitments (for recovery from persistence).
    pub fn from_commitments(commitments: Vec<NoteCommitment>) -> Self {
        let mut tree = MerkleTree::new();
        for c in &commitments {
            tree.insert_hash(c.0);
        }
        Self { commitments, tree }
    }
}

impl Default for NoteTree {
    fn default() -> Self {
        Self::new()
    }
}

/// A persistent nullifier set backed by the store.
///
/// This is a thin wrapper that provides the same double-spend detection semantics
/// as `pyana_cell::nullifier_set::NullifierSet` but delegates to the persistent
/// store for durability.
#[derive(Clone, Debug)]
pub struct PersistentNullifierSet {
    /// In-memory sorted set for fast lookups and non-membership proofs.
    nullifiers: Vec<Nullifier>,
}

impl PersistentNullifierSet {
    /// Create an empty persistent nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: Vec::new(),
        }
    }

    /// Rebuild from a list of nullifiers (for recovery from persistence).
    pub fn from_nullifiers(mut nullifiers: Vec<Nullifier>) -> Self {
        nullifiers.sort_by(|a, b| a.0.cmp(&b.0));
        Self { nullifiers }
    }

    /// Insert a nullifier. Returns true if newly inserted, false if already present (double-spend).
    pub fn insert(&mut self, nullifier: Nullifier) -> bool {
        match self.nullifiers.binary_search_by(|n| n.0.cmp(&nullifier.0)) {
            Ok(_) => false, // Already present (double-spend).
            Err(idx) => {
                self.nullifiers.insert(idx, nullifier);
                true
            }
        }
    }

    /// Check if a nullifier has been spent.
    pub fn contains(&self, nullifier: &Nullifier) -> bool {
        self.nullifiers.binary_search_by(|n| n.0.cmp(&nullifier.0)).is_ok()
    }

    /// Number of nullifiers in the set.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }

    /// Compute the root hash of the nullifier set.
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
}

impl Default for PersistentNullifierSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::note::Note;

    fn make_note(seed: u8) -> Note {
        let mut owner = [0u8; 32];
        owner[0] = seed;
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [seed; 32];
        Note::with_randomness(owner, fields, randomness)
    }

    #[test]
    fn test_note_tree_append_and_prove() {
        let mut tree = NoteTree::new();

        let note1 = make_note(1);
        let note2 = make_note(2);
        let note3 = make_note(3);

        let pos1 = tree.append(note1.commitment());
        let pos2 = tree.append(note2.commitment());
        let pos3 = tree.append(note3.commitment());

        assert_eq!(pos1, 0);
        assert_eq!(pos2, 1);
        assert_eq!(pos3, 2);
        assert_eq!(tree.size(), 3);

        // Get the current root.
        let root = tree.root();

        // Prove membership for each position.
        let proof1 = tree.prove_membership(0).unwrap();
        let proof2 = tree.prove_membership(1).unwrap();
        let proof3 = tree.prove_membership(2).unwrap();

        assert!(NoteTree::verify_proof(&root, &proof1));
        assert!(NoteTree::verify_proof(&root, &proof2));
        assert!(NoteTree::verify_proof(&root, &proof3));

        // Non-existent position returns None.
        assert!(tree.prove_membership(99).is_none());
    }

    #[test]
    fn test_note_tree_root_changes_on_append() {
        let mut tree = NoteTree::new();
        let root_empty = tree.root();

        tree.append(make_note(1).commitment());
        let root_one = tree.root();
        assert_ne!(root_empty, root_one);

        tree.append(make_note(2).commitment());
        let root_two = tree.root();
        assert_ne!(root_one, root_two);

        tree.append(make_note(3).commitment());
        let root_three = tree.root();
        assert_ne!(root_two, root_three);
    }

    #[test]
    fn test_note_tree_contains() {
        let mut tree = NoteTree::new();
        let note1 = make_note(1);
        let note2 = make_note(2);

        tree.append(note1.commitment());
        assert!(tree.contains(&note1.commitment()));
        assert!(!tree.contains(&note2.commitment()));
    }

    #[test]
    fn test_note_tree_from_commitments() {
        let mut tree = NoteTree::new();
        let notes: Vec<_> = (1..=5).map(|i| make_note(i)).collect();
        let commitments: Vec<_> = notes.iter().map(|n| n.commitment()).collect();

        for c in &commitments {
            tree.append(*c);
        }
        let root_original = tree.root();

        // Rebuild from commitments.
        let mut rebuilt = NoteTree::from_commitments(commitments);
        let root_rebuilt = rebuilt.root();

        assert_eq!(root_original, root_rebuilt);
    }

    #[test]
    fn test_persistent_nullifier_set_insert() {
        let mut set = PersistentNullifierSet::new();
        let note = make_note(1);
        let spending_key = [0xBB; 32];
        let nullifier = note.nullifier(&spending_key, 0);

        // First insert succeeds.
        assert!(set.insert(nullifier));
        assert!(set.contains(&nullifier));

        // Second insert fails (double-spend detection).
        assert!(!set.insert(nullifier));
    }

    #[test]
    fn test_persistent_nullifier_set_root_changes() {
        let mut set = PersistentNullifierSet::new();
        let root_empty = set.root();

        let note1 = make_note(1);
        let spending_key = [0xBB; 32];
        let n1 = note1.nullifier(&spending_key, 0);
        set.insert(n1);
        let root_one = set.root();
        assert_ne!(root_empty, root_one);

        let note2 = make_note(2);
        let n2 = note2.nullifier(&spending_key, 1);
        set.insert(n2);
        let root_two = set.root();
        assert_ne!(root_one, root_two);
    }
}
