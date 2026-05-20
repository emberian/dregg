//! Anonymous note model: consume-once cells with private state.
//!
//! A note is a committed tuple: (owner, fields[8], randomness) with a unique commitment.
//! Spending a note = revealing its nullifier (only the owner can compute this).
//! Creating a note = adding a commitment to the note tree.
//!
//! Notes are self-proving: the STARK proof + Merkle path is enough to verify,
//! no federation callback needed.
//!
//! All commitments use domain-separated BLAKE3 (placeholder for Poseidon2 over
//! the STARK-native field). The API is designed so that swapping to algebraic
//! Poseidon2 requires changing only the hash calls in this module.

use serde::{Deserialize, Serialize};

/// A note commitment (published to the note tree).
/// commitment = H("pyana-note commitment v1", owner || fields[0..8] || randomness)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NoteCommitment(pub [u8; 32]);

/// A nullifier (published when spending a note).
/// nullifier = H("pyana-note nullifier v1", commitment || spending_key || position_in_tree)
/// Only the owner can compute this. Publishing it "spends" the note.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
}

/// A note with its computed commitment and position info.
#[derive(Clone, Debug)]
pub struct PositionedNote {
    pub note: Note,
    pub commitment: NoteCommitment,
    /// Position in the note tree (needed for nullifier derivation).
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
                write!(f, "double-spend: nullifier {:?} already revealed", &nullifier.0[..4])
            }
            NoteError::ConservationViolation { asset_type, input_total, output_total } => {
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
    /// Create a new note with random blinding.
    pub fn new(owner: [u8; 32], fields: [u64; 8]) -> Self {
        let mut randomness = [0u8; 32];
        // Use BLAKE3 keyed hash of owner + fields as deterministic "randomness"
        // for reproducibility in tests. Real usage should supply external randomness.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note randomness v1");
        hasher.update(&owner);
        for f in &fields {
            hasher.update(&f.to_le_bytes());
        }
        // Mix in a counter to avoid collisions when creating multiple notes
        // with same owner+fields. In production, this would be `getrandom`.
        hasher.update(&std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
            .to_le_bytes());
        randomness.copy_from_slice(hasher.finalize().as_bytes());
        Self { owner, fields, randomness }
    }

    /// Create a note with explicit randomness (for deterministic tests).
    pub fn with_randomness(owner: [u8; 32], fields: [u64; 8], randomness: [u8; 32]) -> Self {
        Self { owner, fields, randomness }
    }

    /// Compute the commitment for this note.
    /// Uses domain-separated BLAKE3 over (owner || fields || randomness).
    pub fn commitment(&self) -> NoteCommitment {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note commitment v1");
        hasher.update(&self.owner);
        for f in &self.fields {
            hasher.update(&f.to_le_bytes());
        }
        hasher.update(&self.randomness);
        NoteCommitment(*hasher.finalize().as_bytes())
    }

    /// Compute the nullifier for this note given the owner's secret key and tree position.
    /// nullifier = H("pyana-note nullifier v1", commitment || spending_key || tree_position)
    pub fn nullifier(&self, spending_key: &[u8; 32], tree_position: u64) -> Nullifier {
        let commitment = self.commitment();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-note nullifier v1");
        hasher.update(&commitment.0);
        hasher.update(spending_key);
        hasher.update(&tree_position.to_le_bytes());
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

        let nullifier1 = note.nullifier(&key1, 0);
        let nullifier2 = note.nullifier(&key2, 0);

        // Different spending keys produce different nullifiers.
        assert_ne!(nullifier1, nullifier2);
    }

    #[test]
    fn test_nullifier_depends_on_position() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);
        let key = test_spending_key(1);

        let n1 = note.nullifier(&key, 0);
        let n2 = note.nullifier(&key, 1);

        assert_ne!(n1, n2);
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
        let nft_note_a = Note::with_randomness(
            owner_a,
            [unique_asset_id, 0, 0, 0, 0, 0, 0, 0],
            [10u8; 32],
        );

        // Transfer: create a new note with same asset_id but new owner.
        let nft_note_b = Note::with_randomness(
            owner_b,
            [unique_asset_id, 0, 0, 0, 0, 0, 0, 0],
            [20u8; 32],
        );

        // Asset identity is preserved (same fields[0]).
        assert_eq!(nft_note_a.asset_type(), nft_note_b.asset_type());
        assert_eq!(nft_note_a.asset_type(), unique_asset_id);

        // But commitments differ (different owner and randomness).
        assert_ne!(nft_note_a.commitment(), nft_note_b.commitment());
    }
}
