//! Key management with encryption at rest.
//!
//! Signing keys are stored encrypted using ChaCha20-Poly1305 (a standard AEAD).
//! The encryption key is derived from the master key via BLAKE3's KDF mode with
//! a domain-separated context string.
//!
//! Public keys are stored in plaintext since they are not secret.

use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
use redb::ReadableTable;
use subtle::ConstantTimeEq;

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Size of the nonce used for ChaCha20-Poly1305.
const NONCE_SIZE: usize = 12;

/// Size of the Poly1305 authentication tag.
const TAG_SIZE: usize = 16;

/// Total size of an encrypted key blob: nonce(12) + ciphertext(32) + tag(16).
const ENCRYPTED_BLOB_SIZE: usize = NONCE_SIZE + 32 + TAG_SIZE;

impl PersistentStore {
    /// Store a signing key encrypted with the given master key.
    ///
    /// The key is encrypted using ChaCha20-Poly1305 with a key derived from the
    /// master key via BLAKE3's KDF mode. The nonce is randomly generated and stored
    /// alongside the ciphertext.
    pub fn store_signing_key(
        &self,
        name: &str,
        key: &[u8; 32],
        master_key: &[u8; 32],
    ) -> Result<()> {
        let encrypted = encrypt_key(key, master_key)?;

        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::SIGNING_KEYS)?;
            table.insert(name, encrypted.as_slice())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load and decrypt a signing key using the given master key.
    ///
    /// Returns `None` if no key exists with the given name.
    /// Returns `Err(Crypto)` if decryption/authentication fails (wrong master key).
    pub fn load_signing_key(&self, name: &str, master_key: &[u8; 32]) -> Result<Option<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::SIGNING_KEYS)?;

        match table.get(name)? {
            Some(value) => {
                let blob = value.value();
                let key = decrypt_key(blob, master_key)?;
                Ok(Some(key))
            }
            None => Ok(None),
        }
    }

    /// Delete a signing key by name.
    ///
    /// Returns true if a key was removed.
    pub fn delete_signing_key(&self, name: &str) -> Result<bool> {
        let write_txn = self.db.begin_write()?;
        let removed = {
            let mut table = write_txn.open_table(tables::SIGNING_KEYS)?;
            table.remove(name)?.is_some()
        };
        write_txn.commit()?;
        Ok(removed)
    }

    /// List all signing key names.
    pub fn list_signing_keys(&self) -> Result<Vec<String>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::SIGNING_KEYS)?;

        let mut names = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            names.push(entry.0.value().to_string());
        }
        Ok(names)
    }

    /// Store a public key (plaintext, not encrypted).
    pub fn store_public_key(&self, name: &str, key: &[u8; 32]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::PUBLIC_KEYS)?;
            table.insert(name, key)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load a public key by name.
    ///
    /// Returns `None` if no key exists with the given name.
    pub fn load_public_key(&self, name: &str) -> Result<Option<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::PUBLIC_KEYS)?;

        match table.get(name)? {
            Some(value) => Ok(Some(*value.value())),
            None => Ok(None),
        }
    }

    /// Delete a public key by name.
    pub fn delete_public_key(&self, name: &str) -> Result<bool> {
        let write_txn = self.db.begin_write()?;
        let removed = {
            let mut table = write_txn.open_table(tables::PUBLIC_KEYS)?;
            table.remove(name)?.is_some()
        };
        write_txn.commit()?;
        Ok(removed)
    }

    /// List all public key names.
    pub fn list_public_keys(&self) -> Result<Vec<String>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::PUBLIC_KEYS)?;

        let mut names = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            names.push(entry.0.value().to_string());
        }
        Ok(names)
    }

    /// Check if a signing key exists.
    pub fn has_signing_key(&self, name: &str) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::SIGNING_KEYS)?;
        Ok(table.get(name)?.is_some())
    }

    /// Check if a public key exists.
    pub fn has_public_key(&self, name: &str) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::PUBLIC_KEYS)?;
        Ok(table.get(name)?.is_some())
    }
}

// =============================================================================
// Key Encryption/Decryption (ChaCha20-Poly1305)
// =============================================================================

/// Encrypt a 32-byte key using ChaCha20-Poly1305.
///
/// Format: nonce (12 bytes) || ciphertext+tag (32 + 16 bytes)
///
/// The AEAD key is derived from the master key using BLAKE3's KDF mode with
/// a domain-separated context string. This is a standard AEAD construction
/// providing both confidentiality and authenticity.
fn encrypt_key(key: &[u8; 32], master_key: &[u8; 32]) -> Result<Vec<u8>> {
    // Generate random nonce.
    let mut nonce_bytes = [0u8; NONCE_SIZE];
    getrandom::fill(&mut nonce_bytes).map_err(|e| StoreError::Crypto(e.to_string()))?;

    // Derive the AEAD key from the master key.
    let aead_key = derive_aead_key(master_key);
    let cipher = ChaCha20Poly1305::new((&aead_key).into());
    let nonce = chacha20poly1305::Nonce::from(nonce_bytes);

    let ciphertext = cipher
        .encrypt(&nonce, key.as_slice())
        .map_err(|e| StoreError::Crypto(format!("encryption failed: {e}")))?;

    // Assemble blob: nonce || ciphertext (which includes the 16-byte Poly1305 tag).
    let mut blob = Vec::with_capacity(NONCE_SIZE + ciphertext.len());
    blob.extend_from_slice(&nonce_bytes);
    blob.extend_from_slice(&ciphertext);
    Ok(blob)
}

/// Decrypt a 32-byte key from an encrypted blob.
///
/// Uses ChaCha20-Poly1305 which provides authenticated decryption: if the master
/// key is wrong or the data has been tampered with, decryption will fail with an
/// authentication error (constant-time tag verification is built into the AEAD).
fn decrypt_key(blob: &[u8], master_key: &[u8; 32]) -> Result<[u8; 32]> {
    if blob.len() != ENCRYPTED_BLOB_SIZE {
        return Err(StoreError::Crypto(format!(
            "invalid encrypted blob size: expected {ENCRYPTED_BLOB_SIZE}, got {}",
            blob.len()
        )));
    }

    let nonce_bytes = &blob[..NONCE_SIZE];
    let ciphertext_and_tag = &blob[NONCE_SIZE..];

    // Derive the AEAD key from the master key.
    let aead_key = derive_aead_key(master_key);
    let cipher = ChaCha20Poly1305::new((&aead_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(nonce_bytes);

    let plaintext = cipher
        .decrypt(nonce, ciphertext_and_tag)
        .map_err(|_| {
            StoreError::Crypto(
                "authentication failed: invalid master key or corrupted data".to_string(),
            )
        })?;

    let mut key = [0u8; 32];
    if plaintext.len() != 32 {
        return Err(StoreError::Crypto(format!(
            "decrypted key has wrong length: expected 32, got {}",
            plaintext.len()
        )));
    }
    key.copy_from_slice(&plaintext);
    Ok(key)
}

/// Derive a 32-byte AEAD key from the master key using BLAKE3's KDF mode.
///
/// The context string provides domain separation ensuring the derived key
/// cannot be confused with keys derived for other purposes from the same master.
fn derive_aead_key(master_key: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key("pyana-store key-encryption v2", master_key)
}

/// Constant-time comparison using the `subtle` crate.
///
/// This is used for any security-sensitive comparisons where timing side-channels
/// could leak information about the expected value.
#[allow(dead_code)]
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    a.ct_eq(b).into()
}
