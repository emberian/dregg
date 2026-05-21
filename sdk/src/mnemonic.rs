//! BIP39-style mnemonic generation and BLAKE3-based HD key derivation.
//!
//! This module provides:
//! - 24-word mnemonic generation from 256 bits of entropy
//! - Mnemonic-to-seed conversion with optional passphrase
//! - BLAKE3-based hierarchical key derivation for Ed25519 keypairs
//!
//! Unlike BIP32 (which targets secp256k1), we use BLAKE3's `derive_key` for
//! Ed25519-native key derivation. The derivation path uses the scheme:
//! - `pyana/0` for the main agent identity
//! - `pyana/1`, `pyana/2`, ... for sub-agents

use sha2::{Digest, Sha256};
use zeroize::Zeroize;

use crate::wordlist::WORDLIST;

/// Errors that can occur during mnemonic operations.
#[derive(Debug, thiserror::Error)]
pub enum MnemonicError {
    /// The mnemonic has an invalid word count (must be 24).
    #[error("invalid word count: expected 24, got {0}")]
    InvalidWordCount(usize),

    /// A word in the mnemonic is not in the BIP39 word list.
    #[error("unknown word: {0}")]
    UnknownWord(String),

    /// The mnemonic checksum is invalid.
    #[error("invalid checksum")]
    InvalidChecksum,
}

/// Generate a new 24-word mnemonic from 256 bits of cryptographic entropy.
///
/// The mnemonic encodes 256 bits of entropy plus an 8-bit SHA-256 checksum,
/// yielding 264 bits total, which maps to 24 words (11 bits each).
///
/// # Example
/// ```
/// use pyana_sdk::mnemonic::generate_mnemonic;
/// let words = generate_mnemonic();
/// assert_eq!(words.split_whitespace().count(), 24);
/// ```
pub fn generate_mnemonic() -> String {
    let mut entropy = [0u8; 32];
    getrandom::fill(&mut entropy).expect("getrandom failed");
    let mnemonic = entropy_to_mnemonic(&entropy);
    entropy.zeroize();
    mnemonic
}

/// Convert 256 bits of entropy into a 24-word mnemonic string.
///
/// Computes the SHA-256 checksum (first byte) and concatenates it to the entropy,
/// then splits the resulting 264 bits into 24 groups of 11 bits, each indexing
/// into the BIP39 word list.
fn entropy_to_mnemonic(entropy: &[u8; 32]) -> String {
    let checksum = Sha256::digest(entropy)[0];

    // Build 264-bit buffer: 256 bits entropy + 8 bits checksum.
    let mut bits = [false; 264];
    for (i, byte) in entropy.iter().enumerate() {
        for bit in 0..8 {
            bits[i * 8 + bit] = (byte >> (7 - bit)) & 1 == 1;
        }
    }
    for bit in 0..8 {
        bits[256 + bit] = (checksum >> (7 - bit)) & 1 == 1;
    }

    // Split into 24 groups of 11 bits.
    let mut words = Vec::with_capacity(24);
    for i in 0..24 {
        let mut index: u16 = 0;
        for bit in 0..11 {
            if bits[i * 11 + bit] {
                index |= 1 << (10 - bit);
            }
        }
        words.push(WORDLIST[index as usize]);
    }

    words.join(" ")
}

/// Validate a mnemonic and return the entropy bytes if valid.
///
/// Checks:
/// 1. Exactly 24 words
/// 2. All words are in the BIP39 word list
/// 3. The embedded checksum matches
pub fn validate_mnemonic(mnemonic: &str) -> Result<[u8; 32], MnemonicError> {
    let words: Vec<&str> = mnemonic.split_whitespace().collect();
    if words.len() != 24 {
        return Err(MnemonicError::InvalidWordCount(words.len()));
    }

    // Convert words back to 11-bit indices.
    let mut bits = [false; 264];
    for (i, word) in words.iter().enumerate() {
        let index = WORDLIST
            .iter()
            .position(|&w| w == *word)
            .ok_or_else(|| MnemonicError::UnknownWord(word.to_string()))?;
        for bit in 0..11 {
            bits[i * 11 + bit] = (index >> (10 - bit)) & 1 == 1;
        }
    }

    // Extract entropy (first 256 bits) and checksum (last 8 bits).
    let mut entropy = [0u8; 32];
    for i in 0..32 {
        for bit in 0..8 {
            if bits[i * 8 + bit] {
                entropy[i] |= 1 << (7 - bit);
            }
        }
    }

    let mut checksum_byte: u8 = 0;
    for bit in 0..8 {
        if bits[256 + bit] {
            checksum_byte |= 1 << (7 - bit);
        }
    }

    // Verify checksum.
    let expected_checksum = Sha256::digest(&entropy)[0];
    if checksum_byte != expected_checksum {
        return Err(MnemonicError::InvalidChecksum);
    }

    Ok(entropy)
}

/// Convert a mnemonic and passphrase into a 64-byte seed.
///
/// Uses BLAKE3 keyed derivation with the context string incorporating the
/// passphrase. This differs from BIP39's PBKDF2 approach but provides
/// equivalent security with better performance.
///
/// # Arguments
///
/// * `mnemonic` - A valid 24-word mnemonic string.
/// * `passphrase` - An optional passphrase for additional protection. Use `""` for no passphrase.
///
/// # Returns
///
/// A 64-byte seed suitable for key derivation, or an error if the mnemonic is invalid.
pub fn mnemonic_to_seed(mnemonic: &str, passphrase: &str) -> Result<[u8; 64], MnemonicError> {
    let entropy = validate_mnemonic(mnemonic)?;
    Ok(seed_from_entropy(&entropy, passphrase))
}

/// Derive a 64-byte seed from raw entropy and a passphrase.
///
/// Uses two rounds of BLAKE3 derive_key to produce 64 bytes:
/// - First 32 bytes from context "pyana mnemonic seed v1 <passphrase>" over entropy
/// - Last 32 bytes from context "pyana mnemonic seed v1 extend <passphrase>" over entropy
fn seed_from_entropy(entropy: &[u8; 32], passphrase: &str) -> [u8; 64] {
    let context_a = format!("pyana mnemonic seed v1 {}", passphrase);
    let context_b = format!("pyana mnemonic seed v1 extend {}", passphrase);

    let first_half = blake3::derive_key(&context_a, entropy);
    let second_half = blake3::derive_key(&context_b, entropy);

    let mut seed = [0u8; 64];
    seed[..32].copy_from_slice(&first_half);
    seed[32..].copy_from_slice(&second_half);
    seed
}

/// Derive an Ed25519 keypair from a seed and derivation path.
///
/// Uses BLAKE3's `derive_key` with the path as context string and the seed as
/// input key material. This produces a deterministic 32-byte secret key from
/// which the Ed25519 public key is derived.
///
/// # Derivation paths
///
/// - `"pyana/0"` - Main agent identity
/// - `"pyana/1"` - First sub-agent
/// - `"pyana/N"` - Nth sub-agent
///
/// # Arguments
///
/// * `seed` - A 64-byte seed (from [`mnemonic_to_seed`]).
/// * `path` - The derivation path string.
///
/// # Returns
///
/// A tuple of `(public_key_bytes, secret_key_bytes)`.
///
/// # Example
///
/// ```
/// use pyana_sdk::mnemonic::{mnemonic_to_seed, derive_keypair, generate_mnemonic};
/// let mnemonic = generate_mnemonic();
/// let seed = mnemonic_to_seed(&mnemonic, "").unwrap();
/// let (public, secret) = derive_keypair(&seed, "pyana/0");
/// assert_ne!(public, [0u8; 32]);
/// ```
pub fn derive_keypair(seed: &[u8; 64], path: &str) -> ([u8; 32], [u8; 32]) {
    let derived = blake3::derive_key(path, seed);
    let secret = ed25519_dalek::SigningKey::from_bytes(&derived);
    let public = secret.verifying_key();
    (public.to_bytes(), derived)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_mnemonic_24_words() {
        let mnemonic = generate_mnemonic();
        let words: Vec<&str> = mnemonic.split_whitespace().collect();
        assert_eq!(words.len(), 24);
        // All words should be in the word list.
        for word in &words {
            assert!(WORDLIST.contains(word), "word not in list: {}", word);
        }
    }

    #[test]
    fn test_mnemonic_roundtrip() {
        let mnemonic = generate_mnemonic();
        let result = validate_mnemonic(&mnemonic);
        assert!(result.is_ok(), "valid mnemonic failed validation: {:?}", result.err());
    }

    #[test]
    fn test_mnemonic_to_seed_deterministic() {
        let mnemonic = generate_mnemonic();
        let seed1 = mnemonic_to_seed(&mnemonic, "test").unwrap();
        let seed2 = mnemonic_to_seed(&mnemonic, "test").unwrap();
        assert_eq!(seed1, seed2);
    }

    #[test]
    fn test_different_passphrase_different_seed() {
        let mnemonic = generate_mnemonic();
        let seed1 = mnemonic_to_seed(&mnemonic, "pass1").unwrap();
        let seed2 = mnemonic_to_seed(&mnemonic, "pass2").unwrap();
        assert_ne!(seed1, seed2);
    }

    #[test]
    fn test_derive_keypair_deterministic() {
        let mnemonic = generate_mnemonic();
        let seed = mnemonic_to_seed(&mnemonic, "").unwrap();
        let (pub1, sec1) = derive_keypair(&seed, "pyana/0");
        let (pub2, sec2) = derive_keypair(&seed, "pyana/0");
        assert_eq!(pub1, pub2);
        assert_eq!(sec1, sec2);
    }

    #[test]
    fn test_different_paths_different_keys() {
        let mnemonic = generate_mnemonic();
        let seed = mnemonic_to_seed(&mnemonic, "").unwrap();
        let (pub0, _) = derive_keypair(&seed, "pyana/0");
        let (pub1, _) = derive_keypair(&seed, "pyana/1");
        assert_ne!(pub0, pub1);
    }

    #[test]
    fn test_invalid_word_count() {
        let result = validate_mnemonic("abandon ability able");
        assert!(matches!(result, Err(MnemonicError::InvalidWordCount(3))));
    }

    #[test]
    fn test_unknown_word() {
        let mut mnemonic = generate_mnemonic();
        // Replace the first word with something not in the list.
        let words: Vec<&str> = mnemonic.split_whitespace().collect();
        let mut modified = vec!["xyzzyplugh"];
        modified.extend_from_slice(&words[1..]);
        let bad_mnemonic = modified.join(" ");
        let result = validate_mnemonic(&bad_mnemonic);
        assert!(matches!(result, Err(MnemonicError::UnknownWord(_))));
    }

    #[test]
    fn test_invalid_checksum() {
        let mnemonic = generate_mnemonic();
        let words: Vec<&str> = mnemonic.split_whitespace().collect();
        // Swap two words to break the checksum.
        let mut modified: Vec<&str> = words.clone();
        // Replace last word with a different valid word.
        let last_word = modified[23];
        let replacement = if last_word == "abandon" { "ability" } else { "abandon" };
        modified[23] = replacement;
        let bad_mnemonic = modified.join(" ");
        let result = validate_mnemonic(&bad_mnemonic);
        assert!(matches!(result, Err(MnemonicError::InvalidChecksum)));
    }

    #[test]
    fn test_entropy_to_mnemonic_known_vector() {
        // All-zero entropy should produce a deterministic mnemonic.
        let entropy = [0u8; 32];
        let mnemonic = entropy_to_mnemonic(&entropy);
        let words: Vec<&str> = mnemonic.split_whitespace().collect();
        assert_eq!(words.len(), 24);
        // First word from all-zero bits (index 0) = "abandon".
        assert_eq!(words[0], "abandon");
        // Validate roundtrips.
        let recovered = validate_mnemonic(&mnemonic).unwrap();
        assert_eq!(recovered, entropy);
    }
}
