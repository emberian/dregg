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

use std::fmt;

use ed25519_dalek::Verifier;
use serde::{Deserialize, Serialize};

pub use causal::{CausalDag, CausalError};

// =============================================================================
// Cryptographic Primitives
// =============================================================================

/// Ed25519 public key (32 bytes).
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
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        match self.to_verifying_key() {
            Some(vk) => {
                let sig = ed25519_dalek::Signature::from_bytes(&signature.0);
                vk.verify(message, &sig).is_ok()
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
            self.0[..4].iter().map(|b| format!("{b:02x}")).collect::<String>()
        )
    }
}

/// An Ed25519 signing key (private key).
#[derive(Clone)]
pub struct SigningKey(ed25519_dalek::SigningKey);

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
// Consensus / Federation Types
// =============================================================================

/// Attested revocation root with quorum signatures.
///
/// This is the canonical definition. It carries FULL 64-byte signatures.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedRoot {
    /// The Merkle root of the revocation tree.
    pub merkle_root: [u8; 32],
    /// The block height at which this root was finalized.
    pub height: u64,
    /// Unix timestamp (seconds) when finalized.
    pub timestamp: i64,
    /// Quorum signatures: (public_key, signature) pairs with FULL 64-byte sigs.
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold aggregate QC (constant-size BLS, preferred over individual sigs).
    pub threshold_qc: Option<ThresholdQC>,
    /// The number of signatures required for validity.
    pub threshold: usize,
}

impl AttestedRoot {
    /// Check if this root has sufficient signatures (count-only check, no crypto).
    ///
    /// Use `is_valid()` for full cryptographic verification.
    pub fn has_quorum(&self) -> bool {
        if self.threshold_qc.is_some() {
            return true;
        }
        self.quorum_signatures.len() >= self.threshold
    }

    /// Verify that this attested root has sufficient valid signatures.
    ///
    /// Performs **cryptographic verification** of the Ed25519 signatures against
    /// the provided set of known federation public keys. Each signer must be in
    /// `known_keys` and each signature must be cryptographically valid over the
    /// canonical signing message.
    ///
    /// If a threshold QC is present, it is considered valid (must be verified
    /// separately via BLS verification at a higher layer).
    pub fn is_valid(&self, known_keys: &[PublicKey]) -> bool {
        if self.threshold_qc.is_some() {
            return true;
        }
        if self.quorum_signatures.len() < self.threshold {
            return false;
        }
        let message = self.signing_message();
        for (pubkey, sig) in &self.quorum_signatures {
            if !known_keys.contains(pubkey) {
                return false;
            }
            if !pubkey.verify(&message, sig) {
                return false;
            }
        }
        true
    }

    /// Compute the canonical message that quorum members sign.
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-attested-root-v1");
        msg.extend_from_slice(&self.merkle_root);
        msg.extend_from_slice(&self.height.to_le_bytes());
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        msg
    }

    /// Short hex of the Merkle root for display.
    pub fn root_hex(&self) -> String {
        self.merkle_root[..4].iter().map(|b| format!("{b:02x}")).collect()
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
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
            self.0[..4].iter().map(|b| format!("{b:02x}")).collect::<String>()
        )
    }
}

impl fmt::Display for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8].iter().map(|b| format!("{b:02x}")).collect::<String>()
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
            height: 42,
            timestamp: 1700000000,
            quorum_signatures: vec![
                (PublicKey([0x11; 32]), Signature([0x22; 64])),
                (PublicKey([0x33; 32]), Signature([0x44; 64])),
                (PublicKey([0x55; 32]), Signature([0x66; 64])),
            ],
            threshold_qc: None,
            threshold: 2,
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
            ..root
        };
        assert!(with_qc.has_quorum()); // QC present = always valid
    }

    #[test]
    fn attested_root_is_valid_verifies_signatures() {
        // Generate real keypairs.
        let (sk1, pk1) = generate_keypair();
        let (sk2, pk2) = generate_keypair();
        let (_sk3, pk3) = generate_keypair();

        let mut root = AttestedRoot {
            merkle_root: [0xAB; 32],
            height: 42,
            timestamp: 1700000000,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 2,
        };

        // Sign with real keys.
        let message = root.signing_message();
        let sig1 = sign(&sk1, &message);
        let sig2 = sign(&sk2, &message);
        root.quorum_signatures = vec![(pk1, sig1), (pk2, sig2)];

        // Valid: both signers are in known_keys and signatures are correct.
        let known_keys = vec![root.quorum_signatures[0].0, root.quorum_signatures[1].0, pk3];
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
            height: 99,
            timestamp: 1700000000,
            quorum_signatures: vec![
                (PublicKey([0xAA; 32]), Signature([0xBB; 64])),
            ],
            threshold_qc: None,
            threshold: 1,
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
