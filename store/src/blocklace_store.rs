//! Blocklace persistence: incremental block storage and metadata for crash recovery.
//!
//! Stores individual blocks by their ID and blocklace metadata (tips, equivocators,
//! ordering state) so the DAG can be reconstructed on restart without re-syncing
//! from peers.
//!
//! Design:
//! - Blocks are stored individually on each insert (incremental, not full snapshots).
//! - Metadata (tips, equivocators, finality state) is persisted periodically.
//! - On startup, all blocks are loaded and fed into `Blocklace::from_checkpoint()`.

use std::collections::HashMap;

use redb::ReadableTable;
use serde::{Deserialize, Serialize};

use pyana_blocklace::finality::{Block, BlockId, Blocklace, CheckpointData};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Metadata for the blocklace state, persisted alongside blocks.
///
/// This captures the mutable state that is derived from block processing but
/// expensive to recompute (equivocators, tips, ordering). Stored as a single
/// postcard-serialized blob under `BLOCKLACE_META_KEY`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceMeta {
    /// Creator -> tip block ID (latest known block per participant).
    pub tips: HashMap<[u8; 32], BlockId>,
    /// Known equivocator public keys.
    pub equivocators: Vec<[u8; 32]>,
    /// Block IDs in their total order (tau output).
    pub ordered_block_ids: Vec<BlockId>,
    /// Block IDs that have been attested by quorum.
    pub attested_block_ids: Vec<BlockId>,
}

impl PersistentStore {
    // =========================================================================
    // Blocklace Block Storage
    // =========================================================================

    /// Persist a single block to the store.
    ///
    /// Called on every new block (local or received from peers). Uses the block's
    /// ID as the key and postcard-serialized bytes as the value.
    ///
    /// This is idempotent: re-inserting the same block is a no-op at the storage
    /// level (redb overwrites with identical data).
    pub fn persist_block(&self, block: &Block) -> Result<()> {
        let key = block.id().0;
        let value = block.to_bytes();
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            table.insert(&key, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist multiple blocks in a single transaction (batch write).
    ///
    /// More efficient than individual `persist_block` calls when receiving
    /// a delta of multiple blocks from a peer.
    pub fn persist_blocks(&self, blocks: &[Block]) -> Result<()> {
        if blocks.is_empty() {
            return Ok(());
        }
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            for block in blocks {
                let key = block.id().0;
                let value = block.to_bytes();
                table.insert(&key, value.as_slice())?;
            }
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist blocklace metadata (tips, equivocators, ordering state).
    ///
    /// Called periodically (e.g., after finality advances) rather than on every
    /// block insert, since metadata can be reconstructed from blocks if needed.
    pub fn persist_blocklace_meta(&self, meta: &BlocklaceMeta) -> Result<()> {
        let value =
            postcard::to_stdvec(meta).map_err(|e| StoreError::Serialization(e.to_string()))?;
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_META_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist the executed_up_to index (how far the finality executor has processed).
    ///
    /// This prevents re-executing already-processed turns on restart.
    pub fn persist_executed_up_to(&self, index: u64) -> Result<()> {
        let value = index.to_le_bytes();
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_EXECUTED_UP_TO_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Load the executed_up_to index from the store.
    ///
    /// Returns 0 if not previously persisted (fresh start).
    pub fn load_executed_up_to(&self) -> Result<u64> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_EXECUTED_UP_TO_KEY)? {
            Some(guard) => {
                let bytes = guard.value();
                if bytes.len() == 8 {
                    Ok(u64::from_le_bytes(bytes.try_into().unwrap()))
                } else {
                    Ok(0)
                }
            }
            None => Ok(0),
        }
    }

    // =========================================================================
    // Blocklace Restoration
    // =========================================================================

    /// Load all persisted blocks from the store.
    ///
    /// Returns the raw block list (unordered). The caller is responsible for
    /// feeding them into `Blocklace::from_checkpoint()` with the appropriate
    /// metadata.
    pub fn load_all_blocks(&self) -> Result<Vec<Block>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;

        let mut blocks = Vec::new();
        for entry in table.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let bytes = entry.1.value();
            let block = Block::from_bytes(bytes).ok_or_else(|| {
                StoreError::Serialization("failed to deserialize persisted block".to_string())
            })?;
            blocks.push(block);
        }
        Ok(blocks)
    }

    /// Load blocklace metadata from the store.
    ///
    /// Returns `None` if no metadata has been persisted yet (first run).
    pub fn load_blocklace_meta(&self) -> Result<Option<BlocklaceMeta>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_META_KEY)? {
            Some(guard) => {
                let meta: BlocklaceMeta = postcard::from_bytes(guard.value())?;
                Ok(Some(meta))
            }
            None => Ok(None),
        }
    }

    /// Restore a complete blocklace from persisted state.
    ///
    /// Loads all blocks and metadata, then reconstructs the blocklace using
    /// `Blocklace::from_checkpoint()`. This trusts the persisted data (no
    /// signature re-verification) since it came from our own local store.
    ///
    /// Returns `None` if no blocks have been persisted (fresh start).
    pub fn load_blocklace(
        &self,
        signing_key: ed25519_dalek::SigningKey,
        quorum_threshold: usize,
    ) -> Result<Option<(Blocklace, usize)>> {
        let blocks = self.load_all_blocks()?;
        if blocks.is_empty() {
            return Ok(None);
        }

        let meta = self.load_blocklace_meta()?;
        let executed_up_to = self.load_executed_up_to()? as usize;

        // Build a CheckpointData from our persisted state.
        let checkpoint = CheckpointData {
            blocks: blocks.iter().map(|b| b.to_bytes()).collect(),
            tips: meta.as_ref().map(|m| m.tips.clone()).unwrap_or_default(),
            equivocators: meta
                .as_ref()
                .map(|m| m.equivocators.clone())
                .unwrap_or_default(),
            ordered_block_ids: meta
                .as_ref()
                .map(|m| m.ordered_block_ids.clone())
                .unwrap_or_default(),
            attested_block_ids: meta
                .as_ref()
                .map(|m| m.attested_block_ids.clone())
                .unwrap_or_default(),
        };

        let blocklace = Blocklace::from_checkpoint(&checkpoint, signing_key, quorum_threshold)
            .map_err(|e| StoreError::Integrity(e))?;

        Ok(Some((blocklace, executed_up_to)))
    }

    /// Get the number of blocks stored in the blocklace table.
    pub fn blocklace_block_count(&self) -> Result<u64> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
        Ok(table.len()?)
    }
}
