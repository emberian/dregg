//! `pyana-store`: Persistent storage for the pyana token system.
//!
//! This crate provides durable storage for token chains, federation state
//! (revocation trees, attested roots), key management, and audit logs using
//! `redb` as the embedded key-value store backend.
//!
//! # Design
//!
//! All state that was previously in-memory (in `pyana-commit`, `pyana-federation`,
//! and `pyana-audit`) can be persisted and recovered across restarts. The store
//! is designed to be crash-safe: `redb` uses write-ahead logging to ensure
//! atomicity.
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                     PersistentStore                           │
//! │                                                              │
//! │  ┌─────────────┐ ┌──────────────┐ ┌────────────────────┐   │
//! │  │ Token Chains │ │  Federation  │ │    Key Management   │   │
//! │  │             │ │  State       │ │                     │   │
//! │  │ store/load  │ │ revocations  │ │  signing keys       │   │
//! │  │ list        │ │ attested     │ │  (encrypted)        │   │
//! │  │             │ │ roots        │ │  public keys        │   │
//! │  └─────────────┘ └──────────────┘ └────────────────────┘   │
//! │                                                              │
//! │  ┌─────────────────────────────────────────────────────┐    │
//! │  │                   Audit Log                          │    │
//! │  │  append / retrieve / query by token                  │    │
//! │  └─────────────────────────────────────────────────────┘    │
//! │                                                              │
//! │  ┌─────────────────────────────────────────────────────┐    │
//! │  │                   Recovery                           │    │
//! │  │  recover_federation_state() → RecoveredState         │    │
//! │  └─────────────────────────────────────────────────────┘    │
//! │                                                              │
//! │                    redb (embedded KV)                         │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Encryption
//!
//! Signing keys are encrypted at rest using XChaCha20-Poly1305 (via BLAKE3
//! key derivation from the master key). Public keys are stored in plaintext.

pub mod audit;
pub mod federation;
pub mod keys;
pub mod note_tree;
pub mod poseidon2_note_tree;
pub mod recovery;
pub mod tables;
pub mod tokens;

#[cfg(test)]
mod tests;

use std::path::Path;

use redb::{Database, ReadableTable};

pub use audit::StoredAuditEvent;
pub use federation::StoredAttestedRoot;
pub use note_tree::{NoteTree, PersistentNullifierSet};
pub use poseidon2_note_tree::Poseidon2NoteTree;
pub use recovery::RecoveredState;
pub use tokens::{StoredFoldStep, TokenChain};

/// Errors that can occur during store operations.
#[derive(Debug)]
pub enum StoreError {
    /// The underlying database returned an error.
    Database(String),
    /// Serialization/deserialization failure.
    Serialization(String),
    /// Encryption or decryption failure.
    Crypto(String),
    /// The requested item was not found.
    NotFound,
    /// Data integrity check failed.
    Integrity(String),
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Database(msg) => write!(f, "database error: {msg}"),
            Self::Serialization(msg) => write!(f, "serialization error: {msg}"),
            Self::Crypto(msg) => write!(f, "crypto error: {msg}"),
            Self::NotFound => write!(f, "not found"),
            Self::Integrity(msg) => write!(f, "integrity error: {msg}"),
        }
    }
}

impl std::error::Error for StoreError {}

impl From<redb::DatabaseError> for StoreError {
    fn from(e: redb::DatabaseError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TableError> for StoreError {
    fn from(e: redb::TableError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TransactionError> for StoreError {
    fn from(e: redb::TransactionError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::CommitError> for StoreError {
    fn from(e: redb::CommitError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::StorageError> for StoreError {
    fn from(e: redb::StorageError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<postcard::Error> for StoreError {
    fn from(e: postcard::Error) -> Self {
        Self::Serialization(e.to_string())
    }
}

/// Result type alias for store operations.
pub type Result<T> = std::result::Result<T, StoreError>;

/// The persistent store for all pyana state.
///
/// Backed by `redb`, an embedded ACID key-value store. All operations are
/// crash-safe through redb's write-ahead logging.
pub struct PersistentStore {
    db: Database,
}

impl PersistentStore {
    /// Open a persistent store backed by a file on disk.
    ///
    /// Creates the file and all necessary tables if they don't exist.
    pub fn open(path: &Path) -> Result<Self> {
        let db = Database::create(path).map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self { db };
        store.initialize_tables()?;
        Ok(store)
    }

    /// Open an in-memory store (useful for testing).
    ///
    /// Data is lost when the store is dropped.
    pub fn open_in_memory() -> Result<Self> {
        let backend = redb::backends::InMemoryBackend::new();
        let db = Database::builder()
            .create_with_backend(backend)
            .map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self { db };
        store.initialize_tables()?;
        Ok(store)
    }

    /// Initialize all tables in the database.
    fn initialize_tables(&self) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            // Token chain tables.
            let _ = write_txn.open_table(tables::TOKEN_CHAINS)?;
            // Federation tables.
            let _ = write_txn.open_table(tables::REVOCATIONS)?;
            let _ = write_txn.open_table(tables::ATTESTED_ROOTS)?;
            // Key management tables.
            let _ = write_txn.open_table(tables::SIGNING_KEYS)?;
            let _ = write_txn.open_table(tables::PUBLIC_KEYS)?;
            // Audit log tables.
            let _ = write_txn.open_table(tables::AUDIT_LOG)?;
            let _ = write_txn.open_table(tables::AUDIT_TOKEN_INDEX)?;
            // Note tree tables.
            let _ = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            let _ = write_txn.open_table(tables::NULLIFIERS)?;
            // Metadata table.
            let _ = write_txn.open_table(tables::METADATA)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Compact the database file, reclaiming unused space.
    pub fn compact(&mut self) -> Result<bool> {
        self.db
            .compact()
            .map_err(|e| StoreError::Database(e.to_string()))
    }

    // =========================================================================
    // Note Tree Storage
    // =========================================================================

    /// Store a note commitment at the next position. Returns the position assigned.
    pub fn store_note_commitment(
        &self,
        commitment: &pyana_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            table.insert(position, &commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;
        }
        write_txn.commit()?;
        Ok(position)
    }

    /// Store a nullifier (mark a note as spent).
    ///
    /// Returns Ok(()) if the nullifier was newly added, or an integrity error
    /// if it was already present (double-spend).
    pub fn store_nullifier(&self, nullifier: &pyana_cell::note::Nullifier) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::NULLIFIERS)?;
            if table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            table.insert(&nullifier.0, ())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Check whether a nullifier has been spent (is in the set).
    pub fn is_nullifier_spent(&self, nullifier: &pyana_cell::note::Nullifier) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;
        Ok(table.get(&nullifier.0)?.is_some())
    }

    /// Compute the current note tree root by loading all commitments and
    /// rebuilding the Merkle tree.
    pub fn note_tree_root(&self) -> Result<[u8; 32]> {
        let commitments = self.load_all_note_commitments()?;
        let mut tree = note_tree::NoteTree::from_commitments(commitments);
        Ok(tree.root())
    }

    /// Get the number of note commitments stored.
    pub fn note_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Load all note commitments in order (for tree reconstruction).
    pub fn load_all_note_commitments(&self) -> Result<Vec<pyana_cell::note::NoteCommitment>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NOTE_COMMITMENTS)?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let count = meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0);

        let mut commitments = Vec::with_capacity(count as usize);
        for pos in 0..count {
            match table.get(pos)? {
                Some(guard) => {
                    commitments.push(pyana_cell::note::NoteCommitment(*guard.value()));
                }
                None => {
                    return Err(StoreError::Integrity(format!(
                        "missing note commitment at position {pos}"
                    )));
                }
            }
        }
        Ok(commitments)
    }

    /// Load all nullifiers from persistent storage.
    pub fn load_all_nullifiers(&self) -> Result<Vec<pyana_cell::note::Nullifier>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;

        let mut nullifiers = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            nullifiers.push(pyana_cell::note::Nullifier(*entry.0.value()));
        }
        Ok(nullifiers)
    }

    /// Compute the nullifier set root from all stored nullifiers.
    pub fn nullifier_set_root(&self) -> Result<[u8; 32]> {
        let nullifiers = self.load_all_nullifiers()?;
        let set = note_tree::PersistentNullifierSet::from_nullifiers(nullifiers);
        Ok(set.root())
    }

    /// Atomically spend a note: insert the nullifier and store the new commitment
    /// in a single transaction.
    ///
    /// This prevents the case where a nullifier is recorded but the new commitment
    /// is lost (or vice versa) due to a crash between two separate transactions.
    ///
    /// Returns the position of the new commitment in the note tree.
    /// Returns an integrity error if the nullifier was already spent (double-spend).
    pub fn spend_note_atomic(
        &self,
        nullifier: &pyana_cell::note::Nullifier,
        new_commitment: &pyana_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            // Check and insert nullifier.
            let mut nullifier_table = write_txn.open_table(tables::NULLIFIERS)?;
            if nullifier_table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            nullifier_table.insert(&nullifier.0, ())?;

            // Insert new commitment at the next position.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut commitment_table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            commitment_table.insert(position, &new_commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;
        }
        write_txn.commit()?;
        Ok(position)
    }
}
