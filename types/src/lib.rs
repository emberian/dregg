//! Canonical shared types for the pyana federation protocol.
//!
//! This crate defines the ONE TRUE version of cryptographic primitives and
//! consensus types used across `pyana-wire`, `pyana-store`, `pyana-federation`,
//! and other crates.
//!
//! # Key invariants
//!
//! - [`Signature`] is ALWAYS 64 bytes (Ed25519).
//! - [`PublicKey`] is ALWAYS 32 bytes (Ed25519).
//! - [`AttestedRoot`] carries `Vec<(PublicKey, Signature)>` with correct sizes.
//!
//! # Serde
//!
//! All types derive `Serialize`/`Deserialize` and are compatible with both
//! postcard (compact binary) and JSON serialization.

pub mod causal;

use std::collections::HashSet;
use std::fmt;

use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

pub use causal::{CausalDag, CausalError};

// =============================================================================
// Cryptographic Primitives
// =============================================================================

/// Ed25519 public key (32 bytes).
///
/// # Serialization
///
/// Uses `serde_32` which serializes as a length-prefixed byte sequence (Vec<u8>)
/// for format compatibility. Note that this differs from `pyana_cell::NoteCommitment`
/// which derives Serialize/Deserialize directly on its `[u8; 32]` (raw fixed array,
/// no length prefix in postcard). Both are correct for their respective wire formats:
/// `PublicKey` appears in variable-length structures (AttestedRoot signatures) while
/// NoteCommitment appears in fixed-layout note trees.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PublicKey(#[serde(with = "serde_32")] pub [u8; 32]);

impl PublicKey {
    /// Short hex representation for display (first 4 bytes).
    pub fn short_hex(&self) -> String {
        self.0[..4].iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Full hex representation.
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Return the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Convert to the underlying ed25519_dalek verifying key.
    fn to_verifying_key(&self) -> Option<ed25519_dalek::VerifyingKey> {
        ed25519_dalek::VerifyingKey::from_bytes(&self.0).ok()
    }

    /// Verify that a signature over `message` was produced by this key.
    ///
    /// Uses `verify_strict` to reject non-canonical S values, preventing
    /// signature malleability (transaction malleability attacks).
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        match self.to_verifying_key() {
            Some(vk) => {
                let sig = ed25519_dalek::Signature::from_bytes(&signature.0);
                vk.verify_strict(message, &sig).is_ok()
            }
            None => false,
        }
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PubKey({})", self.short_hex())
    }
}

impl fmt::Display for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.short_hex())
    }
}

/// Ed25519 signature (64 bytes).
///
/// This is the CORRECT size for Ed25519 signatures. Previous versions of
/// `pyana-wire` and `pyana-store` incorrectly used 32-byte arrays, which
/// truncated signatures and made verification impossible.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Signature(#[serde(with = "serde_64")] pub [u8; 64]);

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Sig({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

/// An Ed25519 signing key (private key).
///
/// NOTE: Clone is intentionally retained for key derivation workflows, but each
/// clone is an untracked copy of the secret material. Prefer passing references
/// where possible.
#[derive(Clone)]
pub struct SigningKey(ed25519_dalek::SigningKey);

impl SigningKey {
    /// Create a signing key from raw 32-byte secret key material.
    ///
    /// # Security
    ///
    /// The caller is responsible for ensuring the key material is from a
    /// trusted source and is properly zeroized after use.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self(ed25519_dalek::SigningKey::from_bytes(bytes))
    }

    /// Derive the corresponding public key from this signing key.
    pub fn public_key(&self) -> PublicKey {
        PublicKey(self.0.verifying_key().to_bytes())
    }

    /// Return the raw 32-byte secret key material.
    ///
    /// # Security
    ///
    /// The returned bytes are sensitive. The caller must ensure they are not
    /// leaked or persisted without appropriate protections.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

// Safety: ed25519_dalek::SigningKey (with the "zeroize" feature enabled in Cargo.toml)
// implements ZeroizeOnDrop. When this wrapper is dropped, the inner SigningKey's
// Drop impl scrubs the secret_key bytes from memory. No additional Drop impl is
// needed on the wrapper itself -- the inner type handles key hygiene.

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SigningKey(<redacted>)")
    }
}

/// Generate an Ed25519 keypair.
pub fn generate_keypair() -> (SigningKey, PublicKey) {
    let mut key_bytes = [0u8; 32];
    getrandom::fill(&mut key_bytes).expect("getrandom failed");
    let sk = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
    key_bytes.zeroize();
    let vk = sk.verifying_key();
    (SigningKey(sk), PublicKey(vk.to_bytes()))
}

/// Sign a message with a signing key (Ed25519).
pub fn sign(key: &SigningKey, message: &[u8]) -> Signature {
    use ed25519_dalek::Signer;
    let sig = key.0.sign(message);
    Signature(sig.to_bytes())
}

/// Verify a signature against a public key (Ed25519).
pub fn verify(public_key: &PublicKey, message: &[u8], signature: &Signature) -> bool {
    public_key.verify(message, signature)
}

/// Hex-encode a byte slice.
pub fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// BLS threshold quorum certificate (opaque bytes, constant size regardless of committee).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThresholdQC(pub Vec<u8>);

// =============================================================================
// FederationId
// =============================================================================

/// Identifies a federation in the unified model.
///
/// **Canonical home.** Previously, two disjoint definitions lived in
/// `pyana-captp` and `pyana-blocklace`; both now re-export this single type
/// (see `FEDERATION-UNIFICATION-DESIGN.md` step 2). The id is a commitment to
/// the federation's committee — `H(sorted(members) || epoch)` — derived via
/// `pyana_federation::derive_federation_id_with_epoch`.
///
/// In the unified lace model, a `FederationId` is semantically equivalent to a
/// `GroupId` (the content-hash of a reference group's strands). Routing layers
/// treat them interchangeably.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct FederationId(pub [u8; 32]);

impl FederationId {
    /// All-zeros placeholder. Used during boot before the local federation's
    /// members are known. Real federations always have a non-zero id (the
    /// hash of a non-empty committee).
    pub const PLACEHOLDER: FederationId = FederationId([0u8; 32]);

    /// Construct from raw bytes.
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        FederationId(bytes)
    }

    /// Borrow the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Short hex representation for logging (first 4 bytes).
    pub fn short_hex(&self) -> String {
        self.0[..4].iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Full hex representation.
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }
}

impl fmt::Debug for FederationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FedId({})", self.short_hex())
    }
}

impl fmt::Display for FederationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl From<[u8; 32]> for FederationId {
    fn from(bytes: [u8; 32]) -> Self {
        FederationId(bytes)
    }
}

impl From<FederationId> for [u8; 32] {
    fn from(id: FederationId) -> Self {
        id.0
    }
}

// =============================================================================
// Consensus / Federation Types
// =============================================================================

/// Attested revocation root with quorum signatures.
///
/// This is the canonical definition. It carries FULL 64-byte signatures.
///
/// Closes finding F3 in `AUDIT-federation.md` / gap D in
/// `AUDIT-blocklace-consensus.md`: an attested root now binds to a specific
/// blocklace block id and finality round. Two attested roots at the same
/// `height` from different blocklace forks are distinguishable because their
/// `blocklace_block_id` differs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedRoot {
    /// The Merkle root of the revocation tree (cell state).
    pub merkle_root: [u8; 32],
    /// The note commitment tree root (append-only Merkle tree of note commitments).
    /// `None` if the federation has not yet integrated note tree attestation.
    pub note_tree_root: Option<[u8; 32]>,
    /// The nullifier set root (commitment to all spent nullifiers).
    /// `None` if the federation has not yet integrated nullifier attestation.
    pub nullifier_set_root: Option<[u8; 32]>,
    /// The block height at which this root was finalized.
    pub height: u64,
    /// Unix timestamp (seconds) when finalized.
    pub timestamp: i64,
    /// The blocklace block id (32-byte BLAKE3) this attestation is anchored
    /// to. `None` for legacy roots produced before F3 was wired; production
    /// roots from the live consensus path always carry it.
    #[serde(default)]
    pub blocklace_block_id: Option<[u8; 32]>,
    /// The Cordial Miners "round" (DAG depth, monotone per-participant) at
    /// the anchoring block. `None` for legacy roots.
    #[serde(default)]
    pub finality_round: Option<u64>,
    /// Quorum signatures: (public_key, signature) pairs with FULL 64-byte sigs.
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold aggregate QC (constant-size BLS, preferred over individual sigs).
    pub threshold_qc: Option<ThresholdQC>,
    /// The number of signatures required for validity.
    pub threshold: usize,
    /// The federation id this attestation is produced by. Bound into the
    /// signing message preimage so that a verifier who reconstructs the
    /// message can detect cross-federation attestation swaps without
    /// consulting any out-of-band state. `FederationId::PLACEHOLDER`
    /// (all-zero) for legacy roots produced before v3 was wired.
    #[serde(default)]
    pub federation_id: FederationId,
}

impl AttestedRoot {
    /// Convenience constructor for the common "no blocklace binding yet" case
    /// (tests, legacy fixtures). Production code in `node/` always sets
    /// `blocklace_block_id` and `finality_round` directly.
    pub fn new_legacy(
        merkle_root: [u8; 32],
        height: u64,
        timestamp: i64,
        quorum_signatures: Vec<(PublicKey, Signature)>,
        threshold_qc: Option<ThresholdQC>,
        threshold: usize,
    ) -> Self {
        Self {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height,
            timestamp,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures,
            threshold_qc,
            threshold,
            federation_id: FederationId::PLACEHOLDER,
        }
    }

    /// Check if this root has sufficient signatures (count-only check, no crypto).
    ///
    /// **STRUCTURAL VALIDATION ONLY.** This performs no cryptographic verification.
    /// For Ed25519 signatures it checks count >= threshold. For a ThresholdQC it
    /// checks minimum byte length (>= 48 bytes for BLS12-381 G1 compressed point).
    /// Full cryptographic BLS verification of ThresholdQC requires the `hints`
    /// crate and is performed at a higher layer.
    ///
    /// Use `is_valid()` for Ed25519 cryptographic verification against known keys.
    pub fn has_quorum(&self) -> bool {
        if let Some(ref qc) = self.threshold_qc {
            // A ThresholdQC must be non-empty and meet minimum BLS12-381 G1 size.
            return qc.0.len() >= 48;
        }
        self.quorum_signatures.len() >= self.threshold
    }

    /// Alias for [`has_quorum`](Self::has_quorum) that makes the non-cryptographic
    /// nature of the check explicit in calling code.
    ///
    /// **STRUCTURAL VALIDATION ONLY.** This checks signature count and QC byte
    /// length but does NOT perform any cryptographic verification. Full BLS
    /// verification of ThresholdQC requires the `hints` crate and is done at a
    /// higher layer.
    pub fn is_structurally_valid(&self) -> bool {
        self.has_quorum()
    }

    /// Verify that this attested root has sufficient valid signatures.
    ///
    /// Performs **cryptographic verification** of the Ed25519 signatures against
    /// the provided set of known federation public keys. Each signer must be in
    /// `known_keys` and each signature must be cryptographically valid over the
    /// canonical signing message.
    ///
    /// Duplicate signers are rejected: if the same public key appears more than
    /// once in `quorum_signatures`, only the first occurrence counts toward the
    /// threshold. This prevents replay of a single valid (key, signature) pair
    /// to satisfy quorum.
    ///
    /// **NOTE on ThresholdQC:** If a threshold QC is present, this method performs
    /// STRUCTURAL validation only (>= 48 bytes for BLS12-381 G1 compressed). Full
    /// cryptographic BLS verification of the aggregate signature requires the
    /// `hints` crate and is done at a higher layer.
    pub fn is_valid(&self, known_keys: &[PublicKey]) -> bool {
        if let Some(ref qc) = self.threshold_qc {
            // ThresholdQC must be non-empty and at least BLS12-381 G1 size.
            // Full BLS verification is done at a higher layer; reject obviously
            // invalid (empty/truncated) QCs here.
            return qc.0.len() >= 48;
        }
        if self.quorum_signatures.len() < self.threshold {
            return false;
        }
        let message = self.signing_message();
        let mut seen_signers: HashSet<[u8; 32]> = HashSet::new();
        let mut valid_count = 0usize;
        for (pubkey, sig) in &self.quorum_signatures {
            if !known_keys.contains(pubkey) {
                return false;
            }
            if !pubkey.verify(&message, sig) {
                return false;
            }
            // Only count unique signers toward the threshold.
            if seen_signers.insert(pubkey.0) {
                valid_count += 1;
            }
        }
        // Require that the number of UNIQUE valid signers meets the threshold.
        valid_count >= self.threshold
    }

    /// Alias for [`is_valid`](Self::is_valid) for API compatibility with the
    /// federation crate's previous local definition.
    pub fn is_valid_with_keys(&self, known_keys: &[PublicKey]) -> bool {
        self.is_valid(known_keys)
    }

    /// Compute the canonical message that quorum members sign.
    ///
    /// Each optional field is encoded with a tag byte prefix:
    /// - `0x00` for `None`
    /// - `0x01` followed by the 32-byte value for `Some`
    ///
    /// This ensures unambiguous encoding: `note_tree_root = Some(X), nullifier_set_root = None`
    /// produces a different message than `note_tree_root = None, nullifier_set_root = Some(X)`.
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        // v3 binds the federation_id into the preimage so a verifier
        // reconstructing the message can detect cross-federation attestation
        // swaps without consulting any out-of-band state (audit F2 applied to
        // attested roots).
        // v2 binds the blocklace block_id + finality_round so that two
        // attested roots at the same `height` from different blocklace forks
        // are distinguishable (closes audit F3).
        msg.extend_from_slice(b"pyana-attested-root-v3");
        msg.extend_from_slice(&self.federation_id.0);
        msg.extend_from_slice(&self.merkle_root);
        match self.note_tree_root {
            Some(ref note_root) => {
                msg.push(0x01);
                msg.extend_from_slice(note_root);
            }
            None => {
                msg.push(0x00);
            }
        }
        match self.nullifier_set_root {
            Some(ref nullifier_root) => {
                msg.push(0x01);
                msg.extend_from_slice(nullifier_root);
            }
            None => {
                msg.push(0x00);
            }
        }
        msg.extend_from_slice(&self.height.to_le_bytes());
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        match self.blocklace_block_id {
            Some(ref id) => {
                msg.push(0x01);
                msg.extend_from_slice(id);
            }
            None => {
                msg.push(0x00);
            }
        }
        match self.finality_round {
            Some(round) => {
                msg.push(0x01);
                msg.extend_from_slice(&round.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        msg
    }

    /// Verify that this attested root is valid AND recent enough.
    ///
    /// Combines cryptographic verification with a freshness check:
    /// - Negative timestamps are rejected (invalid state)
    /// - Signatures must be valid against `known_keys`
    /// - The root must not be older than `max_age_secs`
    /// - The root's timestamp must not be more than 60s in the future (clock skew tolerance)
    pub fn is_valid_at(&self, known_keys: &[PublicKey], now: u64, max_age_secs: u64) -> bool {
        // Reject negative timestamps: they are invalid and would wrap to huge
        // u64 values when cast, bypassing the staleness check.
        if self.timestamp < 0 {
            return false;
        }
        if !self.is_valid(known_keys) {
            return false;
        }
        let ts = self.timestamp as u64;
        if now > ts + max_age_secs {
            return false; // too old
        }
        if ts > now + 60 {
            return false; // clock skew tolerance
        }
        true
    }

    /// Short hex of the Merkle root for display.
    pub fn root_hex(&self) -> String {
        self.merkle_root[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }
}

impl fmt::Display for AttestedRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.threshold_qc.is_some() {
            write!(
                f,
                "AttestedRoot(root={}, height={}, threshold_qc=yes, threshold={})",
                self.root_hex(),
                self.height,
                self.threshold
            )
        } else {
            write!(
                f,
                "AttestedRoot(root={}, height={}, sigs={}/{})",
                self.root_hex(),
                self.height,
                self.quorum_signatures.len(),
                self.threshold
            )
        }
    }
}

/// A revocation event submitted to consensus.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RevocationEvent {
    /// The token ID being revoked.
    pub token_id: String,
    /// The revoking authority's public key.
    pub authority: PublicKey,
    /// Signature over the token_id by the revoking authority (64 bytes).
    pub signature: Signature,
}

/// Cell identity (32 bytes, derived from public key + domain).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CellId(pub [u8; 32]);

impl CellId {
    /// Derive a CellId by hashing a public key and domain string.
    pub fn derive(pubkey: &PublicKey, domain: &str) -> Self {
        let hash = blake3::derive_key("pyana-cell-id-v1", &{
            let mut buf = Vec::with_capacity(32 + domain.len());
            buf.extend_from_slice(&pubkey.0);
            buf.extend_from_slice(domain.as_bytes());
            buf
        });
        CellId(hash)
    }

    /// Derive a CellId from raw byte arrays (public key + token domain bytes).
    ///
    /// Uses domain-separated BLAKE3. This is the derivation method used by the
    /// cell/agent model where both inputs are 32-byte arrays.
    pub fn derive_raw(public_key: &[u8; 32], token_id: &[u8; 32]) -> Self {
        let hash = blake3::derive_key("pyana-cell-id-v1", &{
            let mut buf = Vec::with_capacity(64);
            buf.extend_from_slice(public_key);
            buf.extend_from_slice(token_id);
            buf
        });
        CellId(hash)
    }

    /// Create from raw bytes.
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        CellId(bytes)
    }

    /// Get the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// The zero/null cell ID.
    pub const ZERO: CellId = CellId([0u8; 32]);
}

impl fmt::Debug for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CellId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl fmt::Display for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

// =============================================================================
// Serde helpers for fixed-size byte arrays
// =============================================================================

mod serde_32 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 32], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 32 bytes"))
    }
}

mod serde_64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pubkey_size() {
        assert_eq!(std::mem::size_of::<PublicKey>(), 32);
    }

    #[test]
    fn signature_size() {
        assert_eq!(std::mem::size_of::<Signature>(), 64);
    }

    #[test]
    fn attested_root_has_quorum() {
        let root = AttestedRoot {
            merkle_root: [0xAB; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1700000000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![
                (PublicKey([0x11; 32]), Signature([0x22; 64])),
                (PublicKey([0x33; 32]), Signature([0x44; 64])),
                (PublicKey([0x55; 32]), Signature([0x66; 64])),
            ],
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId::PLACEHOLDER,
        };
        assert!(root.has_quorum()); // 3 sigs >= threshold 2

        let invalid = AttestedRoot {
            threshold: 5,
            ..root.clone()
        };
        assert!(!invalid.has_quorum()); // 3 sigs < threshold 5

        let with_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![0xFF; 48])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root.clone()
        };
        assert!(with_qc.has_quorum()); // Valid QC (48 bytes = BLS12-381 G1 minimum)

        // Empty ThresholdQC must NOT bypass verification.
        let empty_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root.clone()
        };
        assert!(!empty_qc.has_quorum()); // Empty QC is rejected

        // Truncated ThresholdQC (< 48 bytes) must also fail.
        let truncated_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![0xFF; 10])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root
        };
        assert!(!truncated_qc.has_quorum()); // Truncated QC is rejected
    }

    #[test]
    fn attested_root_is_valid_verifies_signatures() {
        // Generate real keypairs.
        let (sk1, pk1) = generate_keypair();
        let (sk2, pk2) = generate_keypair();
        let (_sk3, pk3) = generate_keypair();

        let mut root = AttestedRoot {
            merkle_root: [0xAB; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1700000000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId::PLACEHOLDER,
        };

        // Sign with real keys.
        let message = root.signing_message();
        let sig1 = sign(&sk1, &message);
        let sig2 = sign(&sk2, &message);
        root.quorum_signatures = vec![(pk1, sig1), (pk2, sig2)];

        // Valid: both signers are in known_keys and signatures are correct.
        let known_keys = vec![
            root.quorum_signatures[0].0,
            root.quorum_signatures[1].0,
            pk3,
        ];
        assert!(root.is_valid(&known_keys));

        // Invalid: signer not in known_keys.
        let partial_keys = vec![root.quorum_signatures[0].0];
        assert!(!root.is_valid(&partial_keys));

        // Invalid: tampered signature.
        let mut tampered = root.clone();
        tampered.quorum_signatures[0].1 = Signature([0xFF; 64]);
        assert!(!tampered.is_valid(&known_keys));
    }

    #[test]
    fn postcard_roundtrip_attested_root() {
        let root = AttestedRoot {
            merkle_root: [0x01; 32],
            note_tree_root: Some([0x02; 32]),
            nullifier_set_root: Some([0x03; 32]),
            height: 99,
            timestamp: 1700000000,
            blocklace_block_id: Some([0x04; 32]),
            finality_round: Some(7),
            quorum_signatures: vec![(PublicKey([0xAA; 32]), Signature([0xBB; 64]))],
            threshold_qc: None,
            threshold: 1,
            federation_id: FederationId::PLACEHOLDER,
        };
        let bytes = postcard::to_stdvec(&root).unwrap();
        let decoded: AttestedRoot = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(root, decoded);
    }

    #[test]
    fn postcard_roundtrip_revocation_event() {
        let event = RevocationEvent {
            token_id: "tok-abc".to_string(),
            authority: PublicKey([0x42; 32]),
            signature: Signature([0x77; 64]),
        };
        let bytes = postcard::to_stdvec(&event).unwrap();
        let decoded: RevocationEvent = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(event, decoded);
    }

    #[test]
    fn cell_id_derive_deterministic() {
        let pk = PublicKey([0x42; 32]);
        let id1 = CellId::derive(&pk, "example.com");
        let id2 = CellId::derive(&pk, "example.com");
        assert_eq!(id1, id2);

        let id3 = CellId::derive(&pk, "other.com");
        assert_ne!(id1, id3);
    }

    #[test]
    fn cell_id_derive_raw_deterministic() {
        let pk = [0x42u8; 32];
        let token = [0x99u8; 32];
        let id1 = CellId::derive_raw(&pk, &token);
        let id2 = CellId::derive_raw(&pk, &token);
        assert_eq!(id1, id2);

        let other_token = [0xAA; 32];
        let id3 = CellId::derive_raw(&pk, &other_token);
        assert_ne!(id1, id3);
    }

    #[test]
    fn sign_and_verify() {
        let (sk, pk) = generate_keypair();
        let message = b"hello world";
        let sig = sign(&sk, message);
        assert!(pk.verify(message, &sig));
        assert!(!pk.verify(b"wrong message", &sig));
    }
}
