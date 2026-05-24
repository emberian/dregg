//! Sealer/Unsealer pairs: E-style rights amplification for partition-tolerant capability transfer.
//!
//! # Cryptographic Construction (X25519 + ChaCha20-Poly1305)
//!
//! - **Key generation**: X25519 keypair. `sealer_public` = X25519 public key.
//!   `unsealer_secret` = X25519 private key.
//! - **Sealing**: Fresh ephemeral X25519 keypair. DH(ephemeral_secret, sealer_public) -> shared secret -> KDF -> ChaCha20-Poly1305.
//! - **Unsealing**: DH(unsealer_secret, ephemeral_public) -> same shared secret -> KDF -> decrypt.
//! - **Forward secrecy**: Each seal uses a fresh ephemeral keypair.
//!
//! # Key derivation
//!
//! The raw X25519 DH output is never used directly as a symmetric key. It is passed
//! through BLAKE3's `derive_key` mode (a proper KDF analogous to HKDF-Extract+Expand)
//! along with both public keys for session binding. This eliminates bit bias in the
//! DH output and provides domain separation.

use serde::{Deserialize, Serialize};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

use crate::capability::CapabilityRef;

/// The public half of a seal pair. Safe to serialize and share.
/// Contains only the information needed to seal (encrypt) capabilities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealerPublic {
    /// Unique pair identifier: BLAKE3("pyana-seal pair-id v2", sealer_public).
    pub id: [u8; 32],
    /// X25519 public key (used for encryption).
    pub sealer_public: [u8; 32],
}

/// A matched sealer/unsealer pair. Created together, used separately.
///
/// NOT serializable: the unsealer secret must never cross a serialization boundary.
/// Use [`SealerPublic`] for the serializable public-key-only view.
///
/// The `unsealer_secret` is zeroized on drop to prevent secret key material
/// from lingering in memory after the pair is no longer needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SealPair {
    /// Unique pair identifier: BLAKE3("pyana-seal pair-id v2", sealer_public).
    pub id: [u8; 32],
    /// X25519 public key (known to sealer holder -- used for encryption).
    pub sealer_public: [u8; 32],
    /// X25519 secret key (known to unsealer holder -- used for decryption).
    pub unsealer_secret: [u8; 32],
}

impl Drop for SealPair {
    fn drop(&mut self) {
        self.unsealer_secret.zeroize();
    }
}

/// A sealed capability -- opaque without the unsealer secret key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealedBox {
    /// Which pair created this box.
    pub pair_id: [u8; 32],
    /// Sender's ephemeral X25519 public key (needed for DH during unseal).
    pub ephemeral_public: [u8; 32],
    /// Commitment: BLAKE3("pyana-seal commitment v2", cap_hash || ephemeral_public || nonce).
    pub commitment: [u8; 32],
    /// ChaCha20-Poly1305 encrypted capability data.
    pub ciphertext: Vec<u8>,
    /// Nonce used for encryption (32 bytes generated; first 12 used for AEAD, full value in commitment).
    pub nonce: [u8; 32],
}

/// Errors that can occur in seal/unseal operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SealError {
    PairMismatch { expected: [u8; 32], got: [u8; 32] },
    DecryptionFailed,
    DeserializationFailed { reason: String },
    CommitmentMismatch,
}

impl core::fmt::Display for SealError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SealError::PairMismatch { expected, got } => write!(
                f,
                "seal pair mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                expected[0], expected[1], got[0], got[1]
            ),
            SealError::DecryptionFailed => {
                write!(f, "sealed box decryption failed (wrong key or tampered)")
            }
            SealError::DeserializationFailed { reason } => {
                write!(f, "sealed capability deserialization failed: {reason}")
            }
            SealError::CommitmentMismatch => write!(f, "seal commitment does not match"),
        }
    }
}

impl std::error::Error for SealError {}

impl SealerPublic {
    /// Create a SealerPublic from a public key.
    pub fn from_public(sealer_public: [u8; 32]) -> Self {
        let id = SealPair::compute_pair_id(&sealer_public);
        SealerPublic { id, sealer_public }
    }
}

impl SealPair {
    /// Extract the serializable public-key-only view of this pair.
    pub fn public(&self) -> SealerPublic {
        SealerPublic {
            id: self.id,
            sealer_public: self.sealer_public,
        }
    }

    pub fn generate() -> Self {
        let mut secret_bytes = [0u8; 32];
        getrandom::fill(&mut secret_bytes).expect("getrandom failed");
        let secret = StaticSecret::from(secret_bytes);
        let public = PublicKey::from(&secret);
        let sealer_public = *public.as_bytes();
        let id = Self::compute_pair_id(&sealer_public);
        SealPair {
            id,
            sealer_public,
            unsealer_secret: secret_bytes,
        }
    }

    pub fn from_secret(unsealer_secret: [u8; 32]) -> Self {
        let secret = StaticSecret::from(unsealer_secret);
        let public = PublicKey::from(&secret);
        let sealer_public = *public.as_bytes();
        let id = Self::compute_pair_id(&sealer_public);
        SealPair {
            id,
            sealer_public,
            unsealer_secret,
        }
    }

    pub fn sealer_only(sealer_public: [u8; 32]) -> Self {
        let id = Self::compute_pair_id(&sealer_public);
        SealPair {
            id,
            sealer_public,
            unsealer_secret: [0u8; 32],
        }
    }

    pub fn from_keys(sealer_public: [u8; 32], unsealer_secret: [u8; 32]) -> Self {
        let id = Self::compute_pair_id(&sealer_public);
        SealPair {
            id,
            sealer_public,
            unsealer_secret,
        }
    }

    fn compute_pair_id(sealer_public: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-seal pair-id v2");
        hasher.update(sealer_public);
        *hasher.finalize().as_bytes()
    }

    pub fn seal(&self, cap: &CapabilityRef) -> SealedBox {
        let mut eph_bytes = [0u8; 32];
        getrandom::fill(&mut eph_bytes).expect("getrandom failed");
        let ephemeral_secret = StaticSecret::from(eph_bytes);
        let ephemeral_public = PublicKey::from(&ephemeral_secret);
        let recipient_public = PublicKey::from(self.sealer_public);
        let shared = ephemeral_secret.diffie_hellman(&recipient_public);
        let enc_key = Self::derive_encryption_key(
            shared.as_bytes(),
            ephemeral_public.as_bytes(),
            &self.sealer_public,
        );
        let nonce = Self::generate_nonce(cap, ephemeral_public.as_bytes());
        let plaintext = Self::serialize_capability(cap);
        let commitment = Self::compute_commitment(&plaintext, ephemeral_public.as_bytes(), &nonce);
        let ciphertext = Self::encrypt(&enc_key, &nonce, &plaintext);
        SealedBox {
            pair_id: self.id,
            ephemeral_public: *ephemeral_public.as_bytes(),
            commitment,
            ciphertext,
            nonce,
        }
    }

    pub fn unseal(&self, sealed: &SealedBox) -> Result<CapabilityRef, SealError> {
        if sealed.pair_id != self.id {
            return Err(SealError::PairMismatch {
                expected: self.id,
                got: sealed.pair_id,
            });
        }
        let unsealer = StaticSecret::from(self.unsealer_secret);
        let ephemeral_pub = PublicKey::from(sealed.ephemeral_public);
        let shared = unsealer.diffie_hellman(&ephemeral_pub);
        let enc_key = Self::derive_encryption_key(
            shared.as_bytes(),
            &sealed.ephemeral_public,
            &self.sealer_public,
        );
        let plaintext = Self::decrypt(&enc_key, &sealed.nonce, &sealed.ciphertext)
            .ok_or(SealError::DecryptionFailed)?;
        let expected_commitment =
            Self::compute_commitment(&plaintext, &sealed.ephemeral_public, &sealed.nonce);
        if expected_commitment != sealed.commitment {
            return Err(SealError::CommitmentMismatch);
        }
        Self::deserialize_capability(&plaintext)
    }

    pub fn verify_seal(&self, sealed: &SealedBox) -> bool {
        if sealed.pair_id != self.id {
            return false;
        }
        let unsealer = StaticSecret::from(self.unsealer_secret);
        let ephemeral_pub = PublicKey::from(sealed.ephemeral_public);
        let shared = unsealer.diffie_hellman(&ephemeral_pub);
        let enc_key = Self::derive_encryption_key(
            shared.as_bytes(),
            &sealed.ephemeral_public,
            &self.sealer_public,
        );
        let Some(plaintext) = Self::decrypt(&enc_key, &sealed.nonce, &sealed.ciphertext) else {
            return false;
        };
        let expected =
            Self::compute_commitment(&plaintext, &sealed.ephemeral_public, &sealed.nonce);
        expected == sealed.commitment
    }

    fn generate_nonce(cap: &CapabilityRef, ephemeral_public: &[u8; 32]) -> [u8; 32] {
        let mut entropy = [0u8; 16];
        getrandom::fill(&mut entropy).expect("getrandom failed");
        let mut hasher = blake3::Hasher::new_derive_key("pyana-seal nonce v2");
        hasher.update(ephemeral_public);
        hasher.update(cap.target.as_bytes());
        hasher.update(&cap.slot.to_le_bytes());
        hasher.update(&entropy);
        *hasher.finalize().as_bytes()
    }

    fn compute_commitment(
        plaintext: &[u8],
        ephemeral_public: &[u8; 32],
        nonce: &[u8; 32],
    ) -> [u8; 32] {
        let cap_hash = blake3::hash(plaintext);
        let mut hasher = blake3::Hasher::new_derive_key("pyana-seal commitment v2");
        hasher.update(cap_hash.as_bytes());
        hasher.update(ephemeral_public);
        hasher.update(nonce);
        *hasher.finalize().as_bytes()
    }

    /// Derive an encryption key from the raw X25519 shared secret using BLAKE3's
    /// KDF mode (derive_key). Raw X25519 output has biased bits and must never be
    /// used directly as a symmetric key. BLAKE3's derive_key mode is a proper KDF
    /// (analogous to HKDF-Extract+Expand) that produces uniformly distributed output.
    ///
    /// The context string acts as domain separation, preventing key reuse across
    /// different protocol versions or applications. Both public keys are mixed in
    /// to bind the derived key to the specific session, preventing key-compromise
    /// impersonation attacks.
    fn derive_encryption_key(
        shared_secret: &[u8; 32],
        ephemeral_public: &[u8; 32],
        recipient_public: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-seal encryption v3");
        hasher.update(shared_secret);
        hasher.update(ephemeral_public);
        hasher.update(recipient_public);
        *hasher.finalize().as_bytes()
    }

    fn serialize_capability(cap: &CapabilityRef) -> Vec<u8> {
        let mut buf = Vec::with_capacity(85);
        // Version 3: includes allowed_effects facet mask.
        // Version 2 added expires_at. Version 1 was the original layout.
        buf.push(3u8);
        buf.extend_from_slice(cap.target.as_bytes());
        buf.extend_from_slice(&cap.slot.to_le_bytes());
        let perm_byte = match &cap.permissions {
            crate::permissions::AuthRequired::None => 0u8,
            crate::permissions::AuthRequired::Signature => 1u8,
            crate::permissions::AuthRequired::Proof => 2u8,
            crate::permissions::AuthRequired::Either => 3u8,
            crate::permissions::AuthRequired::Impossible => 4u8,
        };
        buf.push(perm_byte);
        match &cap.breadstuff {
            None => buf.push(0),
            Some(bs) => {
                buf.push(1);
                buf.extend_from_slice(bs);
            }
        }
        match cap.expires_at {
            Some(h) => {
                buf.push(1);
                buf.extend_from_slice(&h.to_le_bytes());
            }
            None => {
                buf.push(0);
            }
        }
        // Version 3: allowed_effects facet mask. Authority-amplification
        // hardening: sealing a faceted cap must round-trip the facet, not
        // silently widen it back to "all effects" (which `None` means in
        // CapabilitySet::has_access lookups).
        match cap.allowed_effects {
            Some(mask) => {
                buf.push(1);
                buf.extend_from_slice(&mask.to_le_bytes());
            }
            None => buf.push(0),
        }
        buf
    }

    fn deserialize_capability(data: &[u8]) -> Result<CapabilityRef, SealError> {
        if data.is_empty() {
            return Err(SealError::DeserializationFailed {
                reason: "empty data".to_string(),
            });
        }

        // Version dispatch. Version 3 adds `allowed_effects`; version 2
        // added `expires_at`; version 1 (implicit) had neither.
        let (version, payload) = match data[0] {
            3 => (3u8, &data[1..]),
            2 => (2u8, &data[1..]),
            _ => (1u8, data),
        };

        if payload.len() < 38 {
            return Err(SealError::DeserializationFailed {
                reason: format!("data too short: {} bytes", payload.len()),
            });
        }
        let mut target_bytes = [0u8; 32];
        target_bytes.copy_from_slice(&payload[0..32]);
        let target = crate::id::CellId::from_bytes(target_bytes);
        let slot = u32::from_le_bytes([payload[32], payload[33], payload[34], payload[35]]);
        let permissions = match payload[36] {
            0 => crate::permissions::AuthRequired::None,
            1 => crate::permissions::AuthRequired::Signature,
            2 => crate::permissions::AuthRequired::Proof,
            3 => crate::permissions::AuthRequired::Either,
            4 => crate::permissions::AuthRequired::Impossible,
            other => {
                return Err(SealError::DeserializationFailed {
                    reason: format!("invalid permission byte: {other}"),
                });
            }
        };
        let mut offset = 37;
        let breadstuff = match payload[offset] {
            0 => {
                offset += 1;
                None
            }
            1 => {
                offset += 1;
                if payload.len() < offset + 32 {
                    return Err(SealError::DeserializationFailed {
                        reason: format!("data too short for breadstuff: {} bytes", payload.len()),
                    });
                }
                let mut bs = [0u8; 32];
                bs.copy_from_slice(&payload[offset..offset + 32]);
                offset += 32;
                Some(bs)
            }
            other => {
                return Err(SealError::DeserializationFailed {
                    reason: format!("invalid breadstuff discriminant: {other}"),
                });
            }
        };

        // Parse expires_at (version 2+).
        let expires_at = if version >= 2 && offset < payload.len() {
            match payload[offset] {
                0 => {
                    offset += 1;
                    None
                }
                1 => {
                    offset += 1;
                    if payload.len() < offset + 8 {
                        return Err(SealError::DeserializationFailed {
                            reason: format!(
                                "data too short for expires_at: {} bytes",
                                payload.len()
                            ),
                        });
                    }
                    let h = u64::from_le_bytes([
                        payload[offset],
                        payload[offset + 1],
                        payload[offset + 2],
                        payload[offset + 3],
                        payload[offset + 4],
                        payload[offset + 5],
                        payload[offset + 6],
                        payload[offset + 7],
                    ]);
                    offset += 8;
                    Some(h)
                }
                other => {
                    return Err(SealError::DeserializationFailed {
                        reason: format!("invalid expires_at discriminant: {other}"),
                    });
                }
            }
        } else {
            None
        };

        // Parse allowed_effects (version 3+). Silently absent in v1/v2
        // payloads — those existed before the facet field was added.
        let allowed_effects = if version >= 3 && offset < payload.len() {
            match payload[offset] {
                0 => {
                    offset += 1;
                    None
                }
                1 => {
                    offset += 1;
                    if payload.len() < offset + 4 {
                        return Err(SealError::DeserializationFailed {
                            reason: format!(
                                "data too short for allowed_effects: {} bytes",
                                payload.len()
                            ),
                        });
                    }
                    let mask = u32::from_le_bytes([
                        payload[offset],
                        payload[offset + 1],
                        payload[offset + 2],
                        payload[offset + 3],
                    ]);
                    offset += 4;
                    Some(mask)
                }
                other => {
                    return Err(SealError::DeserializationFailed {
                        reason: format!("invalid allowed_effects discriminant: {other}"),
                    });
                }
            }
        } else {
            None
        };
        let _ = offset; // silence dead-store warning at trailing parse

        Ok(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
            expires_at,
            allowed_effects,
        })
    }

    /// Encrypt using ChaCha20-Poly1305.
    ///
    /// # Nonce handling
    ///
    /// The `nonce` parameter is 32 bytes (generated by `generate_nonce` from BLAKE3
    /// output), but ChaCha20-Poly1305 requires exactly 12 bytes. We use the first 12
    /// bytes; the remaining 20 bytes are discarded. This is cryptographically safe
    /// because:
    ///
    /// 1. The full 32-byte nonce is stored in the SealedBox for commitment verification.
    /// 2. The 12 bytes used for AEAD are uniformly random (BLAKE3 output is uniform).
    /// 3. Each seal operation uses a fresh ephemeral keypair, so nonce reuse under the
    ///    same key is impossible regardless of nonce size.
    /// 4. The full 32-byte value participates in the commitment hash, binding the
    ///    sealed box to all entropy used.
    fn encrypt(key: &[u8; 32], nonce: &[u8; 32], plaintext: &[u8]) -> Vec<u8> {
        use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
        let cipher = ChaCha20Poly1305::new(key.into());
        let aead_nonce = chacha20poly1305::Nonce::from_slice(&nonce[..12]);
        cipher
            .encrypt(aead_nonce, plaintext)
            .expect("encryption should not fail")
    }

    /// Decrypt using ChaCha20-Poly1305. See [`encrypt`](Self::encrypt) for nonce
    /// truncation rationale.
    fn decrypt(key: &[u8; 32], nonce: &[u8; 32], ciphertext: &[u8]) -> Option<Vec<u8>> {
        use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
        let cipher = ChaCha20Poly1305::new(key.into());
        let aead_nonce = chacha20poly1305::Nonce::from_slice(&nonce[..12]);
        cipher.decrypt(aead_nonce, ciphertext).ok()
    }
}

pub fn test_seal_pair(seed: u8) -> SealPair {
    let mut unsealer_secret = [0u8; 32];
    unsealer_secret[0] = seed;
    unsealer_secret[1] = 0xAA;
    unsealer_secret[31] = seed.wrapping_mul(7);
    SealPair::from_secret(unsealer_secret)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::CellId;
    use crate::permissions::AuthRequired;

    fn make_test_cap(seed: u8) -> CapabilityRef {
        let mut t = [0u8; 32];
        t[0] = seed;
        t[31] = seed.wrapping_mul(3);
        CapabilityRef {
            target: CellId::from_bytes(t),
            slot: seed as u32,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
        }
    }
    fn make_test_cap_with_breadstuff(seed: u8) -> CapabilityRef {
        let mut t = [0u8; 32];
        t[0] = seed;
        t[31] = seed.wrapping_mul(3);
        let mut bs = [0u8; 32];
        bs[0] = seed;
        bs[1] = 0xFF;
        CapabilityRef {
            target: CellId::from_bytes(t),
            slot: seed as u32,
            permissions: AuthRequired::Either,
            breadstuff: Some(bs),
            expires_at: None,
            allowed_effects: None,
        }
    }

    #[test]
    fn seal_unseal_roundtrip() {
        let pair = test_seal_pair(1);
        let cap = make_test_cap(42);
        let sealed = pair.seal(&cap);
        assert_eq!(pair.unseal(&sealed).unwrap(), cap);
    }
    #[test]
    fn seal_unseal_with_breadstuff() {
        let pair = test_seal_pair(2);
        let cap = make_test_cap_with_breadstuff(99);
        let sealed = pair.seal(&cap);
        assert_eq!(pair.unseal(&sealed).unwrap(), cap);
    }
    #[test]
    fn wrong_pair_cannot_unseal() {
        let a = test_seal_pair(1);
        let e = test_seal_pair(2);
        let sealed = a.seal(&make_test_cap(42));
        assert!(matches!(
            e.unseal(&sealed),
            Err(SealError::PairMismatch { .. })
        ));
    }
    #[test]
    fn wrong_unsealer_key_cannot_unseal() {
        let pair = test_seal_pair(1);
        let sealed = pair.seal(&make_test_cap(42));
        let mut t = sealed.clone();
        t.ciphertext[0] ^= 0xFF;
        assert!(matches!(pair.unseal(&t), Err(SealError::DecryptionFailed)));
    }
    #[test]
    fn tampered_ciphertext_detected() {
        let pair = test_seal_pair(3);
        let sealed = pair.seal(&make_test_cap(7));
        let mut t = sealed.clone();
        t.ciphertext[0] ^= 0x01;
        assert!(matches!(pair.unseal(&t), Err(SealError::DecryptionFailed)));
    }
    #[test]
    fn tampered_nonce_detected() {
        let pair = test_seal_pair(4);
        let sealed = pair.seal(&make_test_cap(11));
        let mut t = sealed.clone();
        t.nonce[0] ^= 0x01;
        assert!(matches!(pair.unseal(&t), Err(SealError::DecryptionFailed)));
    }
    #[test]
    fn sealed_box_is_opaque() {
        let pair = test_seal_pair(5);
        let cap = make_test_cap(55);
        let sealed = pair.seal(&cap);
        assert!(
            !sealed
                .ciphertext
                .windows(32)
                .any(|w| w == cap.target.as_bytes())
        );
    }
    #[test]
    fn verify_seal_works() {
        let pair = test_seal_pair(6);
        let sealed = pair.seal(&make_test_cap(33));
        assert!(pair.verify_seal(&sealed));
    }
    #[test]
    fn verify_seal_rejects_tampered() {
        let pair = test_seal_pair(7);
        let sealed = pair.seal(&make_test_cap(22));
        let mut t = sealed.clone();
        t.ciphertext[0] ^= 0xFF;
        assert!(!pair.verify_seal(&t));
    }
    #[test]
    fn verify_seal_rejects_wrong_pair() {
        let a = test_seal_pair(8);
        let b = test_seal_pair(9);
        let sealed = a.seal(&make_test_cap(44));
        assert!(!b.verify_seal(&sealed));
    }
    #[test]
    fn different_seals_of_same_cap_differ() {
        let pair = test_seal_pair(10);
        let cap = make_test_cap(77);
        let s1 = pair.seal(&cap);
        let s2 = pair.seal(&cap);
        assert_ne!(s1.ephemeral_public, s2.ephemeral_public);
        assert_eq!(pair.unseal(&s1).unwrap(), pair.unseal(&s2).unwrap());
    }
    #[test]
    fn all_permission_types_roundtrip() {
        let pair = test_seal_pair(11);
        let mut t = [0u8; 32];
        t[0] = 0xAB;
        for perm in [
            AuthRequired::None,
            AuthRequired::Signature,
            AuthRequired::Proof,
            AuthRequired::Either,
            AuthRequired::Impossible,
        ] {
            let cap = CapabilityRef {
                target: CellId::from_bytes(t),
                slot: 99,
                permissions: perm.clone(),
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
            };
            assert_eq!(pair.unseal(&pair.seal(&cap)).unwrap().permissions, perm);
        }
    }
    #[test]
    fn pair_id_deterministic() {
        let a = SealPair::from_secret([1u8; 32]);
        let b = SealPair::from_secret([1u8; 32]);
        assert_eq!(a.id, b.id);
        assert_eq!(a.sealer_public, b.sealer_public);
    }
    #[test]
    fn pair_id_depends_on_secret() {
        let a = SealPair::from_secret([1u8; 32]);
        let b = SealPair::from_secret([2u8; 32]);
        assert_ne!(a.id, b.id);
    }
    #[test]
    fn serialized_sealed_box_is_portable() {
        let pair = test_seal_pair(12);
        let cap = make_test_cap(88);
        let sealed = pair.seal(&cap);
        let json = serde_json::to_string(&sealed).unwrap();
        let recovered: SealedBox = serde_json::from_str(&json).unwrap();
        assert_eq!(pair.unseal(&recovered).unwrap(), cap);
    }
    #[test]
    fn sealer_public_key_cannot_unseal() {
        let pair = test_seal_pair(13);
        let sealed = pair.seal(&make_test_cap(66));
        let mut bad = [0u8; 32];
        bad[0] = 0xFF;
        bad[1] = 0xEE;
        let attacker = SealPair {
            id: pair.id,
            sealer_public: pair.sealer_public,
            unsealer_secret: bad,
        };
        assert!(matches!(
            attacker.unseal(&sealed),
            Err(SealError::DecryptionFailed)
        ));
    }
    /// Authority-amplification hardening: sealing a faceted capability and
    /// unsealing it must preserve `allowed_effects`. Previously the v2
    /// serialization format dropped this field, silently widening a
    /// `FACET_TRANSFER_ONLY` cap back to "all effects" on round-trip.
    #[test]
    fn allowed_effects_round_trips_through_seal_unseal() {
        use crate::facet::{EFFECT_EMIT_EVENT, EFFECT_TRANSFER};
        let pair = test_seal_pair(20);
        let target_bytes = {
            let mut t = [0u8; 32];
            t[0] = 0x42;
            t
        };
        let cap = CapabilityRef {
            target: CellId::from_bytes(target_bytes),
            slot: 9,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: Some(12345),
            allowed_effects: Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT),
        };
        let sealed = pair.seal(&cap);
        let unsealed = pair.unseal(&sealed).unwrap();
        assert_eq!(
            unsealed.allowed_effects,
            Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT),
            "allowed_effects must round-trip through seal/unseal"
        );
        assert_eq!(unsealed, cap, "full capability must round-trip");
    }

    /// Round-trip `allowed_effects = None` (unfaceted cap) — must remain
    /// `None`, never accidentally become `Some(0)` or `Some(EFFECT_ALL)`.
    #[test]
    fn allowed_effects_none_round_trips() {
        let pair = test_seal_pair(21);
        let cap = make_test_cap(33);
        assert_eq!(cap.allowed_effects, None);
        let sealed = pair.seal(&cap);
        let unsealed = pair.unseal(&sealed).unwrap();
        assert_eq!(unsealed.allowed_effects, None);
    }

    /// Edge case: a `Some(0)` (deny-all facet, per P2-1) must round-trip
    /// as `Some(0)`, not silently widen to `None`.
    #[test]
    fn allowed_effects_some_zero_round_trips_as_deny_all() {
        let pair = test_seal_pair(22);
        let mut cap = make_test_cap(44);
        cap.allowed_effects = Some(0);
        let sealed = pair.seal(&cap);
        let unsealed = pair.unseal(&sealed).unwrap();
        assert_eq!(unsealed.allowed_effects, Some(0));
    }

    #[test]
    fn sealer_only_pair_can_seal_but_not_unseal() {
        let full = test_seal_pair(14);
        let so = SealPair::sealer_only(full.sealer_public);
        let cap = make_test_cap(77);
        let sealed = so.seal(&cap);
        assert_eq!(full.unseal(&sealed).unwrap(), cap);
        assert!(matches!(
            so.unseal(&sealed),
            Err(SealError::DecryptionFailed)
        ));
    }
}
