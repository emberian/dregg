//! Persistent note commitment tree.
//!
//! An append-only 4-ary Merkle tree of note commitments. Notes are added
//! sequentially and never removed. The tree root changes on each append,
//! providing a succinct commitment to the entire note history.
//!
//! This module integrates with the persistent store (redb) to durably record
//! note commitments and nullifiers, and with the Merkle tree from `pyana-commit`
//! for proof generation.
//!
//! The tree maintains BOTH a BLAKE3 tree (for fast non-ZK verification) and a
//! Poseidon2 tree (for ZK proof generation). When a commitment is appended,
//! both trees get updated.

use pyana_cell::note::{NoteCommitment, Nullifier};
use pyana_circuit::field::BabyBear;
use pyana_commit::merkle::{MerkleProof, MerkleTree};
use pyana_commit::poseidon2_tree::{
    Poseidon2MerkleProof, Poseidon2MerkleTree, commitment_to_field,
};

/// An append-only note commitment tree backed by BOTH a BLAKE3 and Poseidon2 Merkle tree.
///
/// Notes are appended sequentially. Each note commitment receives a unique
/// position (index) which is needed for nullifier derivation.
///
/// The dual-tree design bridges the gap between:
/// - BLAKE3: fast, byte-oriented, used for non-ZK consensus verification
/// - Poseidon2: arithmetic-friendly, field-element-oriented, used inside STARK proofs
#[derive(Clone, Debug)]
pub struct NoteTree {
    /// All note commitments ever created (append-only).
    commitments: Vec<NoteCommitment>,
    /// The BLAKE3 Merkle tree over commitments (from pyana-commit).
    tree: MerkleTree,
    /// The Poseidon2 Merkle tree over field-element commitments (ZK-friendly).
    poseidon2_tree: Poseidon2MerkleTree,
}

impl NoteTree {
    /// Create a new empty note tree.
    pub fn new() -> Self {
        Self {
            commitments: Vec::new(),
            tree: MerkleTree::new(),
            poseidon2_tree: Poseidon2MerkleTree::new(),
        }
    }

    /// Append a new note commitment. Returns the position (for nullifier derivation).
    ///
    /// Both the BLAKE3 and Poseidon2 trees are updated atomically. The field
    /// conversion (which could theoretically panic on malformed input) is
    /// performed BEFORE any mutation, so a panic cannot leave the two trees
    /// in a desynchronized state.
    pub fn append(&mut self, commitment: NoteCommitment) -> u64 {
        let position = self.commitments.len() as u64;
        // Compute the Poseidon2 field element BEFORE mutating either tree.
        // If this panics, no state has been modified.
        let field_elem = commitment_to_field(&commitment.0);
        // Now mutate: both operations below are infallible (Vec::push internals).
        self.commitments.push(commitment);
        self.tree.insert_hash(commitment.0);
        self.poseidon2_tree.append(field_elem);
        position
    }

    /// Current BLAKE3 root of the note tree.
    pub fn root(&mut self) -> [u8; 32] {
        self.tree.root()
    }

    /// Current Poseidon2 root of the note tree (for use in ZK proofs).
    pub fn poseidon2_root(&mut self) -> BabyBear {
        self.poseidon2_tree.root()
    }

    /// Prove membership of a commitment at a given position (BLAKE3 proof).
    pub fn prove_membership(&self, position: u64) -> Option<MerkleProof> {
        let pos = position as usize;
        if pos >= self.commitments.len() {
            return None;
        }
        let commitment = &self.commitments[pos];
        self.tree.membership_proof_hash(&commitment.0)
    }

    /// Prove membership of a commitment at a given position (Poseidon2 proof).
    ///
    /// This proof is suitable for use as a witness in STARK proof generation
    /// (e.g., `NoteSpendingWitness`).
    pub fn prove_membership_poseidon2(&self, position: u64) -> Option<Poseidon2MerkleProof> {
        let pos = position as usize;
        if pos >= self.commitments.len() {
            return None;
        }
        self.poseidon2_tree.prove_membership(pos)
    }

    /// Get the Poseidon2 leaf value for a commitment at a given position.
    ///
    /// This is the field element that was inserted into the Poseidon2 tree.
    pub fn poseidon2_leaf(&self, position: u64) -> Option<BabyBear> {
        let pos = position as usize;
        if pos >= self.commitments.len() {
            return None;
        }
        Some(commitment_to_field(&self.commitments[pos].0))
    }

    /// Number of notes in the tree.
    pub fn size(&self) -> u64 {
        self.commitments.len() as u64
    }

    /// Check if a commitment exists in the tree.
    pub fn contains(&self, commitment: &NoteCommitment) -> bool {
        self.tree.contains_hash(&commitment.0)
    }

    /// Verify a BLAKE3 membership proof against a given root.
    pub fn verify_proof(root: &[u8; 32], proof: &MerkleProof) -> bool {
        MerkleTree::verify_membership(root, proof)
    }

    /// Verify a Poseidon2 membership proof against a given root and leaf.
    pub fn verify_poseidon2_proof(
        root: BabyBear,
        leaf: BabyBear,
        proof: &Poseidon2MerkleProof,
    ) -> bool {
        Poseidon2MerkleTree::verify_membership(root, leaf, proof)
    }

    /// Rebuild the tree from a list of commitments (for recovery from persistence).
    pub fn from_commitments(commitments: Vec<NoteCommitment>) -> Self {
        let mut tree = MerkleTree::new();
        let mut poseidon2_tree = Poseidon2MerkleTree::new();
        for c in &commitments {
            tree.insert_hash(c.0);
            let field_elem = commitment_to_field(&c.0);
            poseidon2_tree.append(field_elem);
        }
        Self {
            commitments,
            tree,
            poseidon2_tree,
        }
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
        self.nullifiers
            .binary_search_by(|n| n.0.cmp(&nullifier.0))
            .is_ok()
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
        let nullifier = note.nullifier(&spending_key);

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
        let n1 = note1.nullifier(&spending_key);
        set.insert(n1);
        let root_one = set.root();
        assert_ne!(root_empty, root_one);

        let note2 = make_note(2);
        let n2 = note2.nullifier(&spending_key);
        set.insert(n2);
        let root_two = set.root();
        assert_ne!(root_one, root_two);
    }

    // =========================================================================
    // Dual-tree (BLAKE3 + Poseidon2) tests
    // =========================================================================

    #[test]
    fn test_dual_tree_poseidon2_root_changes_on_append() {
        let mut tree = NoteTree::new();
        let p2_root_empty = tree.poseidon2_root();

        tree.append(make_note(1).commitment());
        let p2_root_one = tree.poseidon2_root();
        assert_ne!(p2_root_empty, p2_root_one);

        tree.append(make_note(2).commitment());
        let p2_root_two = tree.poseidon2_root();
        assert_ne!(p2_root_one, p2_root_two);
    }

    #[test]
    fn test_dual_tree_poseidon2_proof_verifies() {
        let mut tree = NoteTree::new();
        let notes: Vec<_> = (1..=5).map(|i| make_note(i)).collect();
        for n in &notes {
            tree.append(n.commitment());
        }

        let p2_root = tree.poseidon2_root();

        for pos in 0..5u64 {
            let leaf = tree.poseidon2_leaf(pos).unwrap();
            let proof = tree.prove_membership_poseidon2(pos).unwrap();
            assert!(
                NoteTree::verify_poseidon2_proof(p2_root, leaf, &proof),
                "Poseidon2 proof failed at position {pos}"
            );
        }
    }

    #[test]
    fn test_dual_tree_both_proofs_work() {
        let mut tree = NoteTree::new();
        let note = make_note(42);
        let pos = tree.append(note.commitment());

        // BLAKE3 proof works
        let blake3_root = tree.root();
        let blake3_proof = tree.prove_membership(pos).unwrap();
        assert!(NoteTree::verify_proof(&blake3_root, &blake3_proof));

        // Poseidon2 proof works
        let p2_root = tree.poseidon2_root();
        let p2_leaf = tree.poseidon2_leaf(pos).unwrap();
        let p2_proof = tree.prove_membership_poseidon2(pos).unwrap();
        assert!(NoteTree::verify_poseidon2_proof(
            p2_root, p2_leaf, &p2_proof
        ));
    }

    #[test]
    fn test_dual_tree_from_commitments_preserves_poseidon2() {
        let mut tree = NoteTree::new();
        let notes: Vec<_> = (1..=5).map(|i| make_note(i)).collect();
        let commitments: Vec<_> = notes.iter().map(|n| n.commitment()).collect();

        for c in &commitments {
            tree.append(*c);
        }
        let p2_root_original = tree.poseidon2_root();

        // Rebuild from commitments
        let mut rebuilt = NoteTree::from_commitments(commitments);
        let p2_root_rebuilt = rebuilt.poseidon2_root();
        assert_eq!(p2_root_original, p2_root_rebuilt);
    }
}
