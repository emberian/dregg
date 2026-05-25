//! Subscriber-bound content encryption.
//!
//! # Authority
//!
//! - **Recipient identity key**: each subscriber publishes a 32-byte X25519 *receive
//!   public key* (`recv_pubkey`) when they subscribe. The corresponding 32-byte
//!   X25519 *receive private key* (`recv_privkey`) is held ONLY by the subscriber
//!   (in their cclerk, derived from their mnemonic, etc.). The server never sees
//!   the private key.
//! - **Authority model**: anyone who knows `recv_pubkey` can encrypt content
//!   *to* the subscriber (one-way). Only the holder of `recv_privkey` can
//!   decrypt. The server (delivery.rs) calls `encrypt_for` before pushing into
//!   the subscriber's inbox; the inbox therefore stores opaque ciphertext, not
//!   plaintext. A subscriber drains the inbox and runs `decrypt_with` locally.
//! - **Ephemeral sender keys**: each ciphertext carries a fresh X25519 ephemeral
//!   public key. This gives forward secrecy: even if a subscriber's long-term
//!   `recv_privkey` is compromised tomorrow, previously sent ciphertexts cannot
//!   be decrypted retroactively unless the attacker also captured the sender's
//!   ephemeral private key (which is discarded after one use).
//! - **AEAD binding**: ChaCha20-Poly1305 with associated data = the ephemeral
//!   public key, so the ciphertext is bound to the session.
//!
//! # Wire format of a ciphertext returned by `encrypt_for`
//!
//! ```text
//! [0..32]    : sender ephemeral X25519 public key
//! [32..44]   : 12-byte ChaCha20-Poly1305 nonce (random)
//! [44..]     : ciphertext || 16-byte Poly1305 tag
//! ```
//!
//! This format is self-contained: a receiver does not need any side-channel
//! metadata other than their own `recv_privkey`.

use chacha20poly1305::{
    ChaCha20Poly1305, KeyInit,
    aead::{Aead, Payload},
};
use thiserror::Error;
use x25519_dalek::{PublicKey, StaticSecret};

/// Domain separation for the BLAKE3 KDF that converts a raw X25519 shared
/// secret into a 32-byte ChaCha20-Poly1305 key.
///
/// X25519's raw output is biased (the high bit is clamped) and MUST be passed
/// through a KDF before being used as a symmetric key. BLAKE3's `derive_key`
/// mode is a proper extract-and-expand KDF.
const KDF_CONTEXT: &str = "pyana-subscription content encryption v1";

/// Number of bytes prepended to a ciphertext: ephemeral pubkey (32) + nonce (12).
pub const HEADER_LEN: usize = 32 + 12;

/// Errors from the crypto layer.
#[derive(Debug, Error)]
pub enum CryptoError {
    #[error(
        "ciphertext too short: {len} bytes (need at least {} for header)",
        HEADER_LEN
    )]
    TooShort { len: usize },
    #[error("AEAD decryption failed (wrong key, tampered ciphertext, or bad nonce)")]
    DecryptionFailed,
}

/// Encrypt `plaintext` so that only the holder of the X25519 private key
/// matching `recv_pubkey` can decrypt it.
///
/// Returns a self-contained ciphertext (see module docs for the wire format).
///
/// # Determinism
///
/// This function is **not** deterministic: it draws a fresh ephemeral keypair
/// AND a fresh nonce from `getrandom` on every call. Two calls with identical
/// inputs produce different ciphertexts. This is by design — it gives forward
/// secrecy and prevents nonce-reuse oracle attacks.
pub fn encrypt_for(recv_pubkey: &[u8; 32], plaintext: &[u8]) -> Vec<u8> {
    // 1. Fresh ephemeral X25519 keypair.
    let mut eph_secret_bytes = [0u8; 32];
    getrandom::fill(&mut eph_secret_bytes).expect("getrandom failed");
    let eph_secret = StaticSecret::from(eph_secret_bytes);
    let eph_public = PublicKey::from(&eph_secret);

    // 2. Diffie-Hellman with the receiver's long-term public key.
    let recipient_pub = PublicKey::from(*recv_pubkey);
    let shared = eph_secret.diffie_hellman(&recipient_pub);

    // 3. Derive a 32-byte symmetric key via BLAKE3 KDF. Bind to both pubkeys
    //    so the same shared secret cannot be reused for different sessions.
    let aead_key = derive_aead_key(shared.as_bytes(), eph_public.as_bytes(), recv_pubkey);

    // 4. Fresh 12-byte ChaCha20-Poly1305 nonce.
    let mut nonce = [0u8; 12];
    getrandom::fill(&mut nonce).expect("getrandom failed");

    // 5. Encrypt with AAD = ephemeral public key, so a third party cannot
    //    splice ciphertexts between sessions.
    let cipher = ChaCha20Poly1305::new((&aead_key).into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(&nonce);
    let ciphertext = cipher
        .encrypt(
            aead_nonce,
            Payload {
                msg: plaintext,
                aad: eph_public.as_bytes(),
            },
        )
        .expect("chacha20poly1305 encryption is infallible for valid keys");

    // 6. Assemble: eph_pub || nonce || aead_ciphertext_with_tag.
    let mut out = Vec::with_capacity(HEADER_LEN + ciphertext.len());
    out.extend_from_slice(eph_public.as_bytes());
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&ciphertext);
    out
}

/// Decrypt a ciphertext produced by [`encrypt_for`] using the subscriber's
/// long-term X25519 private key.
///
/// Returns `Err(CryptoError::DecryptionFailed)` if the key does not match
/// (i.e. the ciphertext was encrypted to someone else) or if the ciphertext
/// has been tampered with.
pub fn decrypt_with(recv_privkey: &[u8; 32], ciphertext: &[u8]) -> Result<Vec<u8>, CryptoError> {
    if ciphertext.len() < HEADER_LEN {
        return Err(CryptoError::TooShort {
            len: ciphertext.len(),
        });
    }

    let mut eph_pub_bytes = [0u8; 32];
    eph_pub_bytes.copy_from_slice(&ciphertext[0..32]);
    let eph_public = PublicKey::from(eph_pub_bytes);

    let mut nonce_bytes = [0u8; 12];
    nonce_bytes.copy_from_slice(&ciphertext[32..HEADER_LEN]);

    let body = &ciphertext[HEADER_LEN..];

    // Reproduce shared secret.
    let secret = StaticSecret::from(*recv_privkey);
    let recv_pub = PublicKey::from(&secret);
    let shared = secret.diffie_hellman(&eph_public);

    let aead_key = derive_aead_key(shared.as_bytes(), &eph_pub_bytes, recv_pub.as_bytes());

    let cipher = ChaCha20Poly1305::new((&aead_key).into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    cipher
        .decrypt(
            aead_nonce,
            Payload {
                msg: body,
                aad: &eph_pub_bytes,
            },
        )
        .map_err(|_| CryptoError::DecryptionFailed)
}

/// Derive a subscriber's X25519 public key from their 32-byte private key.
///
/// Convenience for test wiring: in production, the subscriber's cclerk derives
/// the X25519 keypair from their mnemonic and publishes only the pubkey.
pub fn pubkey_from_privkey(recv_privkey: &[u8; 32]) -> [u8; 32] {
    let secret = StaticSecret::from(*recv_privkey);
    *PublicKey::from(&secret).as_bytes()
}

/// Mix the X25519 shared secret with both pubkeys through BLAKE3's KDF mode,
/// producing a 32-byte AEAD key.
fn derive_aead_key(
    shared_secret: &[u8; 32],
    ephemeral_pub: &[u8; 32],
    recipient_pub: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(KDF_CONTEXT);
    hasher.update(shared_secret);
    hasher.update(ephemeral_pub);
    hasher.update(recipient_pub);
    *hasher.finalize().as_bytes()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn fixed_privkey(seed: u8) -> [u8; 32] {
        let mut k = [0u8; 32];
        k[0] = seed;
        k[31] = seed.wrapping_mul(7);
        k
    }

    #[test]
    fn roundtrip_alice() {
        let alice_priv = fixed_privkey(0x11);
        let alice_pub = pubkey_from_privkey(&alice_priv);
        let plaintext = b"only alice should see this";

        let ct = encrypt_for(&alice_pub, plaintext);
        let pt = decrypt_with(&alice_priv, &ct).unwrap();
        assert_eq!(pt, plaintext);
    }

    /// ADVERSARIAL: ciphertext bytes are not equal to plaintext bytes.
    #[test]
    fn ciphertext_is_not_plaintext() {
        let alice_priv = fixed_privkey(0x22);
        let alice_pub = pubkey_from_privkey(&alice_priv);
        let plaintext = b"This is the article text. It should NOT appear in the inbox.";

        let ct = encrypt_for(&alice_pub, plaintext);

        // Sanity: ciphertext is longer than plaintext (header + tag).
        assert!(ct.len() > plaintext.len() + HEADER_LEN);

        // Critical: plaintext bytes do not appear contiguously in ciphertext.
        // (This is a weak check, but it's the kind of thing that catches the
        // "InboxMessage::Encrypted { ciphertext: plaintext_bytes }" bug.)
        assert!(
            !ct.windows(plaintext.len()).any(|w| w == plaintext),
            "plaintext appears verbatim inside ciphertext — not actually encrypted!"
        );

        // Even the first 16 ASCII characters shouldn't appear.
        let needle = &plaintext[..16];
        assert!(
            !ct.windows(needle.len()).any(|w| w == needle),
            "plaintext prefix appears verbatim inside ciphertext"
        );
    }

    /// ADVERSARIAL: Bob's privkey returns Err on a ciphertext encrypted to Alice.
    #[test]
    fn decryption_fails_for_wrong_recipient() {
        let alice_priv = fixed_privkey(0x33);
        let alice_pub = pubkey_from_privkey(&alice_priv);
        let bob_priv = fixed_privkey(0x44);

        let ct = encrypt_for(&alice_pub, b"alice-only");
        let result = decrypt_with(&bob_priv, &ct);
        assert!(
            matches!(result, Err(CryptoError::DecryptionFailed)),
            "Bob should not be able to decrypt Alice's ciphertext"
        );
    }

    /// ADVERSARIAL: tampered ciphertext fails AEAD authentication.
    #[test]
    fn tampered_ciphertext_fails() {
        let alice_priv = fixed_privkey(0x55);
        let alice_pub = pubkey_from_privkey(&alice_priv);
        let mut ct = encrypt_for(&alice_pub, b"important");
        // Flip a byte in the payload.
        let i = ct.len() - 5;
        ct[i] ^= 0x01;
        let result = decrypt_with(&alice_priv, &ct);
        assert!(matches!(result, Err(CryptoError::DecryptionFailed)));
    }

    /// Two encryptions of the same plaintext produce different ciphertexts
    /// (non-determinism — fresh ephemeral keys + fresh nonces).
    #[test]
    fn two_encryptions_differ() {
        let alice_priv = fixed_privkey(0x66);
        let alice_pub = pubkey_from_privkey(&alice_priv);
        let ct1 = encrypt_for(&alice_pub, b"same input");
        let ct2 = encrypt_for(&alice_pub, b"same input");
        assert_ne!(ct1, ct2);
    }

    #[test]
    fn truncated_ciphertext_returns_too_short() {
        let alice_priv = fixed_privkey(0x77);
        let result = decrypt_with(&alice_priv, &[1, 2, 3]);
        assert!(matches!(result, Err(CryptoError::TooShort { len: 3 })));
    }
}
