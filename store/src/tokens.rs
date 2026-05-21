//! Token chain persistent storage.
//!
//! Stores the full attenuation chain for each token: the initial root, all fold
//! steps (each with its delta bytes), and the current root. This enables full
//! reconstruction and verification of the token's history after restart.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// A complete token chain: the full history of attenuation steps from issuance
/// to the current state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TokenChain {
    /// The Merkle root of the initial (unattenuated) token state.
    pub initial_root: [u8; 32],
    /// Ordered sequence of fold steps (attenuations).
    pub steps: Vec<StoredFoldStep>,
    /// The current Merkle root (after all attenuations).
    pub current_root: [u8; 32],
    /// The issuer's public key (32 bytes).
    pub issuer_key: [u8; 32],
    /// Unix timestamp (seconds) when the token was created.
    pub created_at: i64,
}

/// A single attenuation step in the token chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredFoldStep {
    /// The Merkle root before this step.
    pub old_root: [u8; 32],
    /// The Merkle root after this step.
    pub new_root: [u8; 32],
    /// The serialized FoldDelta (opaque bytes from pyana-commit).
    pub delta_bytes: Vec<u8>,
    /// Unix timestamp (seconds) when this step was applied.
    pub timestamp: i64,
}

impl PersistentStore {
    /// Store a token chain, keyed by the token's 32-byte identifier.
    ///
    /// Overwrites any existing chain for the same token_id.
    pub fn store_token_chain(&self, token_id: &[u8; 32], chain: &TokenChain) -> Result<()> {
        let serialized = postcard::to_stdvec(chain)?;

        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::TOKEN_CHAINS)?;
            table.insert(token_id, serialized.as_slice())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load a token chain by its 32-byte identifier.
    ///
    /// Returns `None` if no chain exists for the given token_id.
    pub fn load_token_chain(&self, token_id: &[u8; 32]) -> Result<Option<TokenChain>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::TOKEN_CHAINS)?;

        match table.get(token_id)? {
            Some(value) => {
                let chain: TokenChain = postcard::from_bytes(value.value())?;
                Ok(Some(chain))
            }
            None => Ok(None),
        }
    }

    /// List all stored token IDs.
    ///
    /// Returns the 32-byte identifiers of all tokens that have stored chains.
    pub fn list_tokens(&self) -> Result<Vec<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::TOKEN_CHAINS)?;

        let mut ids = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            ids.push(*entry.0.value());
        }
        Ok(ids)
    }

    /// Delete a token chain by its identifier.
    ///
    /// Returns true if a chain was actually removed, false if it didn't exist.
    pub fn delete_token_chain(&self, token_id: &[u8; 32]) -> Result<bool> {
        let write_txn = self.db.begin_write()?;
        let removed = {
            let mut table = write_txn.open_table(tables::TOKEN_CHAINS)?;
            table.remove(token_id)?.is_some()
        };
        write_txn.commit()?;
        Ok(removed)
    }

    /// Count the total number of stored token chains.
    pub fn token_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::TOKEN_CHAINS)?;
        Ok(table.len()?)
    }

    /// Append a fold step to an existing token chain.
    ///
    /// Loads the chain, appends the step, updates the current_root, and saves
    /// within a single write transaction to prevent TOCTOU races.
    /// Returns an error if no chain exists for the token_id.
    pub fn append_fold_step(&self, token_id: &[u8; 32], step: StoredFoldStep) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::TOKEN_CHAINS)?;

            // Load the existing chain within the write transaction.
            let mut chain: TokenChain = {
                let existing = table
                    .get(token_id)?
                    .ok_or(StoreError::NotFound)?;
                postcard::from_bytes(existing.value())?
            };

            // Verify chain continuity: the step's old_root must match the current root.
            if step.old_root != chain.current_root {
                return Err(StoreError::Integrity(format!(
                    "fold step old_root {:?} does not match chain current_root {:?}",
                    &step.old_root[..4],
                    &chain.current_root[..4],
                )));
            }

            chain.current_root = step.new_root;
            chain.steps.push(step);

            let serialized = postcard::to_stdvec(&chain)?;
            table.insert(token_id, serialized.as_slice())?;
        }
        write_txn.commit()?;
        Ok(())
    }
}
