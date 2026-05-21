//! Cryptographic primitives for macaroon operations.
//!
//! - **HMAC-SHA256**: Used for the caveat chain signature. Each caveat is HMACed
//!   with the previous tag as key, producing a new tag.
//! - **XChaCha20-Poly1305**: Used for third-party caveat ticket/VID encryption.
//!   Chosen for its 192-bit nonce (no collision concerns) and AEAD properties.

use chacha20poly1305::aead::{Aead, KeyInit, OsRng};
use chacha20poly1305::{AeadCore, XChaCha20Poly1305, XNonce};
use hmac::Mac;
use sha2::Sha256;

use crate::error::MacaroonError;

type HmacSha256 = hmac::Hmac<Sha256>;

/// HMAC-SHA256: compute tag over data using the given key.
///
/// This is the core primitive for macaroon signatures. The HMAC chain works:
/// - T₀ = HMAC(root_key, nonce)
/// - T₁ = HMAC(T₀, encode(caveat₁))
/// - T₂ = HMAC(T₁, encode(caveat₂))
/// - ...
pub fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut mac = <HmacSha256 as Mac>::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(data);
    mac.finalize().into_bytes().into()
}

/// Constant-time comparison of two 32-byte values.
///
/// Uses `subtle::ConstantTimeEq` to prevent timing side-channels.
pub fn constant_time_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
    use subtle::ConstantTimeEq;
    a.ct_eq(b).into()
}

/// Generate cryptographically random bytes.
pub fn random_bytes<const N: usize>() -> [u8; N] {
    let mut buf = [0u8; N];
    getrandom::fill(&mut buf).expect("getrandom failed");
    buf
}

/// Generate a random 32-byte key.
pub fn random_key() -> [u8; 32] {
    random_bytes::<32>()
}

/// Sealed box: encrypt plaintext under a symmetric key using XChaCha20-Poly1305.
///
/// Returns `[24-byte nonce][ciphertext + 16-byte tag]`.
///
/// Used for:
/// - **VID (Verifier ID)**: Encrypts the discharge key `r` under the current
///   HMAC tail. Only the verifier (who can replay the HMAC chain) can decrypt.
/// - **CID/Ticket**: Encrypts `{discharge_key, caveats}` under the shared key
///   `KA` between the macaroon creator and the third party.
pub fn seal(key: &[u8; 32], plaintext: &[u8]) -> Result<Vec<u8>, MacaroonError> {
    let cipher = XChaCha20Poly1305::new(key.into());
    let nonce = XChaCha20Poly1305::generate_nonce(&mut OsRng);
    let ciphertext = cipher
        .encrypt(&nonce, plaintext)
        .map_err(|e| MacaroonError::EncryptionFailed(e.to_string()))?;

    let mut result = Vec::with_capacity(24 + ciphertext.len());
    result.extend_from_slice(&nonce);
    result.extend_from_slice(&ciphertext);
    Ok(result)
}

/// Unseal: decrypt ciphertext encrypted with `seal()`.
///
/// Input format: `[24-byte nonce][ciphertext + 16-byte tag]`.
pub fn unseal(key: &[u8; 32], sealed: &[u8]) -> Result<Vec<u8>, MacaroonError> {
    if sealed.len() < 24 {
        return Err(MacaroonError::DecryptionFailed(
            "sealed data too short".into(),
        ));
    }
    let (nonce_bytes, ciphertext) = sealed.split_at(24);
    let nonce = XNonce::from_slice(nonce_bytes);
    let cipher = XChaCha20Poly1305::new(key.into());
    cipher
        .decrypt(nonce, ciphertext)
        .map_err(|e| MacaroonError::DecryptionFailed(e.to_string()))
}

/// Derive a binding key from a macaroon's tail.
///
/// Used to bind discharge macaroons to a specific root macaroon,
/// preventing replay with less-attenuated versions of the root.
///
/// Returns the full 32 bytes of SHA-256(tail).
pub fn binding_hash(tail: &[u8; 32]) -> [u8; 32] {
    use sha2::Digest;
    let hash = sha2::Sha256::digest(tail);
    let mut result = [0u8; 32];
    result.copy_from_slice(&hash[..32]);
    result
}

/// Constant-time comparison of two binding hashes (32-byte values).
///
/// Rejects inputs that are not exactly 32 bytes — oversized slices
/// could indicate malformed or padded bindings.
pub fn binding_hash_eq(a: &[u8], b: &[u8; 32]) -> bool {
    use subtle::ConstantTimeEq;
    if a.len() != 32 {
        return false;
    }
    a.ct_eq(b.as_slice()).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hmac_chain() {
        let root_key = random_key();
        let nonce = b"test-nonce";

        let t0 = hmac_sha256(&root_key, nonce);
        let t1 = hmac_sha256(&t0, b"caveat-1");
        let t2 = hmac_sha256(&t1, b"caveat-2");

        // Replaying the chain produces the same result
        let t0_check = hmac_sha256(&root_key, nonce);
        let t1_check = hmac_sha256(&t0_check, b"caveat-1");
        let t2_check = hmac_sha256(&t1_check, b"caveat-2");

        assert_eq!(t2, t2_check);

        // Different key produces different result
        let other_key = random_key();
        let t0_other = hmac_sha256(&other_key, nonce);
        assert_ne!(t0, t0_other);
    }

    #[test]
    fn test_seal_unseal_roundtrip() {
        let key = random_key();
        let plaintext = b"secret discharge key material";

        let sealed = seal(&key, plaintext).unwrap();
        let decrypted = unseal(&key, &sealed).unwrap();

        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_seal_wrong_key_fails() {
        let key1 = random_key();
        let key2 = random_key();
        let plaintext = b"secret";

        let sealed = seal(&key1, plaintext).unwrap();
        let result = unseal(&key2, &sealed);

        assert!(result.is_err());
    }

    #[test]
    fn test_seal_tamper_fails() {
        let key = random_key();
        let plaintext = b"secret";

        let mut sealed = seal(&key, plaintext).unwrap();
        // Flip a bit in the ciphertext
        if let Some(byte) = sealed.last_mut() {
            *byte ^= 0x01;
        }
        let result = unseal(&key, &sealed);
        assert!(result.is_err());
    }

    #[test]
    fn test_binding_hash_deterministic() {
        let tail = random_key();
        let h1 = binding_hash(&tail);
        let h2 = binding_hash(&tail);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 32);
    }
}
