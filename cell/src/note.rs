//! Anonymous note model: consume-once cells with private state.
//!
//! A note is a committed tuple: (owner, fields[8], randomness, creation_nonce) with a unique commitment.
//! Spending a note = revealing its nullifier (only the owner can compute this).
//! Creating a note = adding a commitment to the note tree.
//!
//! Notes are self-proving: the STARK proof + Merkle path is enough to verify,
//! no federation callback needed.
//!
//! Nullifiers are derived from note-intrinsic data only (no tree position), making
//! them globally unique and federation-independent. This ensures double-spend
//! protection works across federation boundaries without export ceremonies.
//!
//! All commitments use domain-separated BLAKE3 (placeholder for Poseidon2 over
//! the STARK-native field). The API is designed so that swapping to algebraic
//! Poseidon2 requires changing only the hash calls in this module.

use serde::{Deserialize, Serialize};

/// A note commitment (published to the note tree).
/// commitment = H("pyana-note commitment v1", owner || fields[0..8] || randomness || creation_nonce)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NoteCommitment(pub [u8; 32]);

/// A nullifier (published when spending a note).
/// nullifier = H("pyana-note nullifier v1", commitment || spending_key || creation_nonce)
/// Only the owner can compute this. Publishing it "spends" the note.
/// Derived from note-intrinsic data only — no tree position — so the same note
/// produces the same nullifier regardless of which tree it lives in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Nullifier(pub [u8; 32]);

/// The content of a note (known only to the owner).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Note {
    /// The owner's public key (spending authority).
    pub owner: [u8; 32],
    /// 8 field elements of application data.
    /// Convention: fields[0] = asset_type, fields[1] = amount (for fungible).
    /// For NFTs: fields[0] = unique_asset_id (immutable across transfers).
    pub fields: [u64; 8],
    /// Random blinding factor (ensures commitment uniqueness).
    pub randomness: [u8; 32],
    /// Unique per-note nonce chosen at creation time. Embedded in the commitment
    /// and used in nullifier derivation. Makes nullifiers federation-independent:
    /// the same note produces the same nullifier regardless of tree position.
    pub creation_nonce: [u8; 32],
}

/// A note with its computed commitment and position info.
/// The tree position is metadata used for Merkle proof generation only —
/// it does NOT participate in nullifier derivation.
#[derive(Clone, Debug)]
pub struct PositionedNote {
    pub note: Note,
    pub commitment: NoteCommitment,
    /// Position in the note tree (needed for Merkle proof generation, NOT for nullifiers).
    pub tree_position: u64,
}

/// Errors that can occur in note operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NoteError {
    /// Attempted to spend a note that has already been spent (double-spend).
    DoubleSpend { nullifier: Nullifier },
    /// Conservation law violated: inputs do not equal outputs for an asset type.
    ConservationViolation {
        asset_type: u64,
        input_total: u64,
        output_total: u64,
    },
}

impl core::fmt::Display for NoteError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NoteError::DoubleSpend { nullifier } => {
                write!(
                    f,
                    "double-spend: nullifier {:?} already revealed",
                    &nullifier.0[..4]
                )
            }
            NoteError::ConservationViolation {
                asset_type,
                input_total,
                output_total,
            } => {
                write!(
                    f,
                    "conservation violated for asset {asset_type}: inputs={input_total}, outputs={output_total}"
                )
            }
        }
    }
}

impl std::error::Error for NoteError {}

impl Note {
    /// Create a new note with cryptographically random blinding and a unique creation nonce.
    ///
    /// The randomness field is filled with OS randomness via `getrandom` to ensure
    /// the blinding factor is cryptographically unpredictable. The creation_nonce is
    /// derived from the randomness for domain separation. Two calls at the same
    /// nanosecond will produce distinct notes.
    #[cfg(feature = "crypto")]
    pub fn new(owner: [u8; 32], fields: [u64; 8]) -> Self {
        // Use OS randomness for the blinding factor — MUST be cryptographically random.
        let mut randomness = [0u8; 32];
        getrandom::fill(&mut randomness).expect("getrandom failed");

        // Derive creation_nonce from randomness (independent domain separation).
        let mut nonce_hasher = blake3::Hasher::new_derive_key("pyana-note creation-nonce v1");
        nonce_hasher.update(&owner);
        nonce_hasher.update(&randomness);
        let mut creation_nonce = [0u8; 32];
        creation_nonce.copy_from_slice(nonce_hasher.finalize().as_bytes());

        Self {
            owner,
            fields,
            randomness,
            creation_nonce,
        }
    }

    /// Create a note with explicit randomness and creation nonce (for deterministic tests).
    pub fn with_randomness(owner: [u8; 32], fields: [u64; 8], randomness: [u8; 32]) -> Self {
        // Derive a deterministic creation_nonce from the randomness.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note creation-nonce v1");
        hasher.update(&owner);
        hasher.update(&randomness);
        let mut creation_nonce = [0u8; 32];
        creation_nonce.copy_from_slice(hasher.finalize().as_bytes());
        Self {
            owner,
            fields,
            randomness,
            creation_nonce,
        }
    }

    /// Create a note with explicit randomness AND explicit creation nonce.
    /// Use when you need full control over both values (e.g., testing nonce uniqueness).
    pub fn with_nonce(
        owner: [u8; 32],
        fields: [u64; 8],
        randomness: [u8; 32],
        creation_nonce: [u8; 32],
    ) -> Self {
        Self {
            owner,
            fields,
            randomness,
            creation_nonce,
        }
    }

    /// Compute the commitment for this note.
    /// Uses domain-separated BLAKE3 over (owner || fields || randomness || creation_nonce).
    pub fn commitment(&self) -> NoteCommitment {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note commitment v1");
        hasher.update(&self.owner);
        for f in &self.fields {
            hasher.update(&f.to_le_bytes());
        }
        hasher.update(&self.randomness);
        hasher.update(&self.creation_nonce);
        NoteCommitment(*hasher.finalize().as_bytes())
    }

    /// Compute the nullifier for this note given the owner's secret key.
    /// nullifier = H("pyana-note nullifier v1", commitment || spending_key || creation_nonce)
    ///
    /// Derived from note-intrinsic data only. No tree position is used, so the same
    /// note produces the same nullifier regardless of which tree (or federation) it
    /// lives in. This makes double-spend detection global by construction.
    ///
    /// This is the **canonical in-protocol nullifier** consumed by the
    /// note-spending STARK AIR (`circuit/src/note_spending_air.rs`) and the
    /// production `NullifierSet` in the turn executor. The separate EVM
    /// withdrawal path (`pyana_chain::withdraw::derive_nullifier`) uses a
    /// different, domain-separated scheme (`pyana-withdrawal-nullifier-v1`)
    /// because it commits to a different SP1 circuit; see that function's
    /// doc-comment for why the schemes are intentionally distinct.
    pub fn nullifier(&self, spending_key: &[u8; 32]) -> Nullifier {
        let commitment = self.commitment();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note nullifier v1");
        hasher.update(&commitment.0);
        hasher.update(spending_key);
        hasher.update(&self.creation_nonce);
        Nullifier(*hasher.finalize().as_bytes())
    }

    /// Check if this note represents a fungible asset.
    /// A note is fungible if both asset_type and amount are non-zero.
    pub fn is_fungible(&self) -> bool {
        self.fields[0] != 0 && self.fields[1] != 0
    }

    /// Get the value (for fungible notes: fields[1]).
    pub fn value(&self) -> u64 {
        self.fields[1]
    }

    /// Get the asset type (fields[0]).
    pub fn asset_type(&self) -> u64 {
        self.fields[0]
    }

    /// Compute the ZK-compatible Poseidon2 commitment for this note.
    ///
    /// This is the commitment used in the NOTE TREE (Poseidon2 Merkle tree) and
    /// verified inside the STARK circuit. It differs from `commitment()` which uses
    /// BLAKE3 for non-ZK use cases (simple hash-based lookups, encryption key derivation).
    ///
    /// The Poseidon2 commitment is authoritative for:
    /// - Note tree membership proofs (ZK Merkle paths)
    /// - STARK spending proofs (the circuit recomputes this from witness columns)
    /// - Nullifier derivation inside the circuit
    ///
    /// The BLAKE3 commitment (`commitment()`) is authoritative for:
    /// - Cleartext note identity / deduplication
    /// - Non-ZK lookups and indexing
    /// - Encryption key derivation
    ///
    /// # Field mapping
    ///
    /// The Poseidon2 commitment maps note fields to BabyBear as follows:
    /// - owner: first 4 bytes of self.owner as little-endian u32, reduced mod p
    /// - value: self.fields[1] as u32, reduced mod p
    /// - asset_type: self.fields[0] as u32, reduced mod p
    /// - creation_nonce: first 4 bytes of self.creation_nonce as LE u32, reduced mod p
    /// - randomness: first 4 bytes of self.randomness as LE u32, reduced mod p
    #[cfg(feature = "zkvm")]
    pub fn poseidon2_commitment(&self) -> pyana_circuit::field::BabyBear {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::poseidon2::hash_many;

        let owner = BabyBear::new_canonical(u32::from_le_bytes([
            self.owner[0],
            self.owner[1],
            self.owner[2],
            self.owner[3],
        ]));
        let value = BabyBear::new_canonical(self.fields[1] as u32);
        let asset_type = BabyBear::new_canonical(self.fields[0] as u32);
        let creation_nonce = BabyBear::new_canonical(u32::from_le_bytes([
            self.creation_nonce[0],
            self.creation_nonce[1],
            self.creation_nonce[2],
            self.creation_nonce[3],
        ]));
        let randomness = BabyBear::new_canonical(u32::from_le_bytes([
            self.randomness[0],
            self.randomness[1],
            self.randomness[2],
            self.randomness[3],
        ]));

        hash_many(&[owner, value, asset_type, creation_nonce, randomness])
    }

    /// Position this note in the tree.
    pub fn positioned(self, tree_position: u64) -> PositionedNote {
        let commitment = self.commitment();
        PositionedNote {
            note: self,
            commitment,
            tree_position,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_owner(seed: u8) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = seed;
        key[31] = seed.wrapping_mul(37);
        key
    }

    fn test_spending_key(seed: u8) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = seed;
        key[1] = 0xBB;
        key
    }

    #[test]
    fn test_note_commitment_deterministic() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [42u8; 32];

        let note1 = Note::with_randomness(owner, fields, randomness);
        let note2 = Note::with_randomness(owner, fields, randomness);

        assert_eq!(note1.commitment(), note2.commitment());
    }

    #[test]
    fn test_note_commitment_unique_with_randomness() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];

        let note1 = Note::with_randomness(owner, fields, [1u8; 32]);
        let note2 = Note::with_randomness(owner, fields, [2u8; 32]);

        assert_ne!(note1.commitment(), note2.commitment());
    }

    #[test]
    fn test_nullifier_requires_spending_key() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);

        let key1 = test_spending_key(1);
        let key2 = test_spending_key(2);

        let nullifier1 = note.nullifier(&key1);
        let nullifier2 = note.nullifier(&key2);

        // Different spending keys produce different nullifiers.
        assert_ne!(nullifier1, nullifier2);
    }

    #[test]
    fn test_nullifier_same_regardless_of_tree_position() {
        // CRITICAL: same note in two different trees produces the SAME nullifier.
        // This is the core property that enables federation-independent double-spend detection.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);
        let key = test_spending_key(1);

        // Nullifier is deterministic and position-independent.
        let n1 = note.nullifier(&key);
        let n2 = note.nullifier(&key);
        assert_eq!(n1, n2);

        // Even if positioned at different tree locations, nullifier is the same.
        let positioned_a = note.clone().positioned(0);
        let positioned_b = note.clone().positioned(999);
        assert_eq!(
            positioned_a.note.nullifier(&key),
            positioned_b.note.nullifier(&key)
        );
    }

    #[test]
    fn test_nullifier_unique_per_note() {
        // Different creation_nonce = different nullifier, even with same content.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let key = test_spending_key(1);

        let note1 = Note::with_nonce(owner, fields, [42u8; 32], [1u8; 32]);
        let note2 = Note::with_nonce(owner, fields, [42u8; 32], [2u8; 32]);

        assert_ne!(note1.nullifier(&key), note2.nullifier(&key));
    }

    #[test]
    fn test_double_spend_across_contexts() {
        // A nullifier computed once is valid everywhere — no tree-specific derivation.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let key = test_spending_key(1);
        let note = Note::with_randomness(owner, fields, [42u8; 32]);

        // Compute nullifier (simulating one federation).
        let nullifier = note.nullifier(&key);

        // In a different context (different federation, different tree position),
        // the same note still produces the same nullifier.
        let same_nullifier = note.nullifier(&key);
        assert_eq!(nullifier, same_nullifier);

        // A nullifier set in any federation can detect the double-spend.
        let mut set = crate::nullifier_set::NullifierSet::new();
        set.insert(nullifier).unwrap();
        let double_spend = set.insert(same_nullifier);
        assert!(matches!(double_spend, Err(NoteError::DoubleSpend { .. })));
    }

    #[test]
    fn test_note_is_fungible() {
        let owner = test_owner(1);

        // Fungible: both asset_type and amount non-zero.
        let fungible = Note::with_randomness(owner, [1, 100, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(fungible.is_fungible());

        // Not fungible: amount is zero.
        let nft = Note::with_randomness(owner, [1, 0, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(!nft.is_fungible());

        // Not fungible: asset_type is zero.
        let empty = Note::with_randomness(owner, [0, 100, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(!empty.is_fungible());
    }

    #[test]
    fn test_note_value_and_asset_type() {
        let owner = test_owner(1);
        let note = Note::with_randomness(owner, [42, 1000, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert_eq!(note.asset_type(), 42);
        assert_eq!(note.value(), 1000);
    }

    #[test]
    fn test_nft_transfer_preserves_identity() {
        let owner_a = test_owner(1);
        let owner_b = test_owner(2);
        let unique_asset_id: u64 = 0xDEAD_BEEF_CAFE_0001;

        // NFT note: fields[0] = unique asset ID, fields[1] = 0 (not fungible).
        let nft_note_a =
            Note::with_randomness(owner_a, [unique_asset_id, 0, 0, 0, 0, 0, 0, 0], [10u8; 32]);

        // Transfer: create a new note with same asset_id but new owner.
        let nft_note_b =
            Note::with_randomness(owner_b, [unique_asset_id, 0, 0, 0, 0, 0, 0, 0], [20u8; 32]);

        // Asset identity is preserved (same fields[0]).
        assert_eq!(nft_note_a.asset_type(), nft_note_b.asset_type());
        assert_eq!(nft_note_a.asset_type(), unique_asset_id);

        // But commitments differ (different owner and randomness).
        assert_ne!(nft_note_a.commitment(), nft_note_b.commitment());
    }

    // ─── NoteBatcher tests ──────────────────────────────────────────────────

    #[test]
    fn test_note_batcher_add_and_should_flush() {
        let mut batcher = super::NoteBatcher::new(5, 16);
        let commitment = NoteCommitment([0xAA; 32]);

        assert!(!batcher.should_flush(0));

        batcher.add(commitment);
        assert_eq!(batcher.pending_count(), 1);
        // Not at interval yet
        assert!(!batcher.should_flush(3));
        // At interval boundary
        assert!(batcher.should_flush(5));
    }

    #[test]
    fn test_note_batcher_max_batch_size() {
        let mut batcher = super::NoteBatcher::new(100, 4);
        for i in 0..4 {
            batcher.add(NoteCommitment([i as u8; 32]));
        }
        // Should flush at max batch size regardless of height
        assert!(batcher.should_flush(1));
    }

    #[test]
    fn test_note_batcher_flush() {
        let mut batcher = super::NoteBatcher::new(5, 16);
        for i in 0..3 {
            batcher.add(NoteCommitment([i as u8; 32]));
        }
        let flushed = batcher.flush(5);
        assert_eq!(flushed.len(), 3);
        assert_eq!(batcher.pending_count(), 0);
        assert_eq!(batcher.last_batch_height, 5);
    }
}

// ─── Note Batcher (timing correlation mitigation) ─────────────────────────────

/// Batch note commitments to reduce timing correlation attacks.
///
/// Without batching, an observer can correlate when a note commitment appears in
/// the tree with when a specific user was online or submitted a turn. By accumulating
/// notes and committing them in fixed-interval batches, all notes in a batch appear
/// at the same height, making it impossible to correlate individual note creation
/// times with user activity.
///
/// # Usage
///
/// The executor (or federation sync layer) calls [`add`](NoteBatcher::add) when a
/// turn creates a note. At each block, it calls [`should_flush`](NoteBatcher::should_flush)
/// and if true, commits all pending notes to the tree in a single batch.
///
/// # Privacy Properties
///
/// - All notes in a batch share the same tree insertion height.
/// - An observer cannot determine which block (within the batch interval) created
///   a specific note.
/// - The batch size is bounded to prevent a single batch from becoming too distinctive.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NoteBatcher {
    /// Pending note commitments waiting to be committed to the tree.
    pending: Vec<NoteCommitment>,
    /// Minimum interval (in blocks) between batch flushes.
    batch_interval_blocks: u64,
    /// The block height at which the last batch was flushed.
    pub last_batch_height: u64,
    /// Maximum number of notes per batch. When reached, flush even if the
    /// interval hasn't elapsed. Prevents unbounded memory growth.
    max_batch_size: usize,
}

impl NoteBatcher {
    /// Create a new note batcher.
    ///
    /// # Arguments
    ///
    /// * `batch_interval_blocks` - Minimum blocks between flushes (e.g., 10).
    /// * `max_batch_size` - Maximum notes per batch before forced flush (e.g., 16).
    pub fn new(batch_interval_blocks: u64, max_batch_size: usize) -> Self {
        Self {
            pending: Vec::new(),
            batch_interval_blocks,
            last_batch_height: 0,
            max_batch_size,
        }
    }

    /// Add a note commitment to the pending batch.
    pub fn add(&mut self, commitment: NoteCommitment) {
        self.pending.push(commitment);
    }

    /// Check whether the batch should be flushed at the given block height.
    ///
    /// Returns true if:
    /// - The batch interval has elapsed since the last flush, OR
    /// - The pending batch has reached `max_batch_size`.
    pub fn should_flush(&self, current_height: u64) -> bool {
        if self.pending.is_empty() {
            return false;
        }
        current_height.saturating_sub(self.last_batch_height) >= self.batch_interval_blocks
            || self.pending.len() >= self.max_batch_size
    }

    /// Flush all pending notes, returning them for insertion into the note tree.
    ///
    /// All returned notes should be committed to the tree at the same height,
    /// preventing timing correlation of individual note creation.
    pub fn flush(&mut self, current_height: u64) -> Vec<NoteCommitment> {
        self.last_batch_height = current_height;
        std::mem::take(&mut self.pending)
    }

    /// Get the number of pending notes.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Check if there are any pending notes.
    pub fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }
}
