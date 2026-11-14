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

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_blocklace::finality::{Block, BlockId, Blocklace, CheckpointData, CreatorTips};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Metadata for the blocklace state, persisted alongside blocks.
///
/// This captures the mutable state that is derived from block processing but
/// expensive to recompute (equivocators, tips, ordering). Stored as a single
/// postcard-serialized blob under `BLOCKLACE_META_KEY`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceMeta {
    /// Creator -> tips: the chain head, or — for a detected equivocator — the
    /// pinned incomparable evidence PAIR (`CreatorTips::Pair`, the CM Alg. 1:5
    /// two-tips floor). ⚑ schema flag day 2026-08-08 (exclusion-by-past): the
    /// value type changed from a bare `BlockId`; an old blob refuses to decode
    /// and the `CANONICAL_STATE_SCHEMA_EPOCH` bump re-genesises the store.
    pub tips: HashMap<[u8; 32], CreatorTips>,
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
        if self
            .fail_persist_block
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return Err(StoreError::Database(
                "persist_block fault injected (test-only fail_persist_block seam)".to_string(),
            ));
        }
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

    /// Test-only: arm/disarm the [`Self::persist_block`] fault seam (finding F2).
    /// Never called in production — a node durability test sets it to exercise the
    /// authored-block fail-closed rollback + no-broadcast path through the real
    /// producer, then clears it to let subsequent persists succeed.
    #[doc(hidden)]
    pub fn set_fail_persist_block(&self, fail: bool) {
        self.fail_persist_block
            .store(fail, std::sync::atomic::Ordering::Relaxed);
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

    /// Persist the executed finalized-block IDENTITY set (first-served order).
    ///
    /// This is the durable half of the node's identity execution cursor (the
    /// TauPrefixMonotone closure): on restart, execution resumes from this set
    /// (∪ the commit log's per-turn `block_id`s, which atomically cover the
    /// turn-carrying blocks), NEVER from an index into the tau order — the
    /// order can shift under honest catch-up growth. Written at the same batch
    /// cadence as [`Self::persist_blocklace_meta`]; if it lags a crash, the
    /// uncovered non-turn blocks re-process idempotently and turns are covered
    /// exactly by the commit log.
    pub fn persist_executed_block_ids(&self, ids: &[BlockId]) -> Result<()> {
        let value =
            postcard::to_stdvec(ids).map_err(|e| StoreError::Serialization(e.to_string()))?;
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_EXECUTED_IDS_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Load the executed finalized-block identity set.
    ///
    /// Returns an empty vector if never persisted (fresh start or pre-upgrade
    /// DB — in the latter case the commit log still recovers every turn
    /// exactly, and non-turn blocks re-process idempotently once).
    pub fn load_executed_block_ids(&self) -> Result<Vec<BlockId>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_EXECUTED_IDS_KEY)? {
            Some(guard) => {
                let ids: Vec<BlockId> = postcard::from_bytes(guard.value())?;
                Ok(ids)
            }
            None => Ok(Vec::new()),
        }
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

    /// Load every persisted block's stored bytes, undecoded and unordered.
    pub fn load_all_block_bytes(&self) -> Result<Vec<Vec<u8>>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
        table
            .iter()?
            .map(|entry| {
                entry
                    .map(|(_, bytes)| bytes.value().to_vec())
                    .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))
            })
            .collect()
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
    /// Loads all blocks and metadata, then reconstructs the blocklace using the
    /// AUTHENTICATING `Blocklace::from_checkpoint()`: every block's Ed25519
    /// signature is re-verified, causal closure is enforced (a dangling
    /// predecessor refuses the whole restore), equivocation is re-derived, and
    /// tips are re-derived from the authenticated blocks rather than copied
    /// from metadata. The persisted `equivocators` set is folded in only as a
    /// LOWER bound — an offline tamper of the metadata can never UN-flag a
    /// creator whose evidence pair is still in the blocks.
    ///
    /// ⚑ Until 2026-08-08 this used `from_checkpoint_trusted` on the grounds
    /// that "it came from our own local store". That justification contradicts
    /// the node's own recovery threat model: the NODE-1 signed-anchor exists
    /// precisely because an offline attacker with write access to this redb can
    /// rewrite it. The restart path must not trust what the running path
    /// verifies. What this still does NOT re-check (and why): the ML-DSA half
    /// of each block (the enrolled PQ roster is derived from committee state
    /// that is itself derived from this lace — checking it here would be
    /// circular; the ed25519 half plus the hybrid `creator` commitment carries
    /// the binding, and only a quantum adversary WITH store write access beats
    /// it), and the ordering/attested frontier (asserted; bounded by the
    /// NODE-1 root convergence and the commit-log identity cursor).
    ///
    /// Returns `None` if no blocks have been persisted (fresh start).
    pub fn load_blocklace(
        &self,
        signing_key: ed25519_dalek::SigningKey,
        quorum_threshold: usize,
    ) -> Result<Option<(Blocklace, usize)>> {
        // The stored bytes go to `from_checkpoint` as they are: it decodes and
        // authenticates every one itself. Decoding them here and re-encoding
        // held three copies of the whole lace at once (decoded blocks, their
        // re-encoded bytes, and the restored lace), the boot peak that grows
        // with history.
        let blocks = self.load_all_block_bytes()?;
        if blocks.is_empty() {
            return Ok(None);
        }

        let meta = self.load_blocklace_meta()?;
        let executed_up_to = self.load_executed_up_to()? as usize;

        // Build a CheckpointData from our persisted state.
        let checkpoint = CheckpointData {
            blocks,
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

        // AUTHENTICATE on restore. Local-disk provenance is not an integrity
        // boundary (the NODE-1 anchor's own threat model: an offline attacker
        // can write this redb), so the restart path runs the same signature +
        // closure + equivocation checks the live receive path runs. A refusal
        // here is a STORE INTEGRITY EVENT and the node must not start on it.
        let blocklace = Blocklace::from_checkpoint_owned(checkpoint, signing_key, quorum_threshold)
            .map_err(StoreError::Integrity)?;

        Ok(Some((blocklace, executed_up_to)))
    }

    /// Get the number of blocks stored in the blocklace table.
    pub fn blocklace_block_count(&self) -> Result<u64> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
        Ok(table.len()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(seed: u8) -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[seed; 32])
    }

    /// A small honest lace persisted the way the node persists it (blocks
    /// individually + meta blob).
    fn persist_honest_lace(store: &PersistentStore, sk: &ed25519_dalek::SigningKey) -> Blocklace {
        let mut lace = Blocklace::new(sk.clone(), 1);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        let blocks: Vec<Block> = lace.iter().map(|(_, b)| b.clone()).collect();
        store.persist_blocks(&blocks).expect("persist blocks");
        let cp = lace.checkpoint();
        store
            .persist_blocklace_meta(&BlocklaceMeta {
                tips: cp.tips.clone(),
                equivocators: cp.equivocators.clone(),
                ordered_block_ids: cp.ordered_block_ids.clone(),
                attested_block_ids: cp.attested_block_ids.clone(),
            })
            .expect("persist meta");
        lace
    }

    /// HONEST POLE: a restart over an untampered store restores the same lace
    /// through the AUTHENTICATING loader (every block re-verified).
    #[test]
    fn honest_restart_restores_through_authentication() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        let lace = persist_honest_lace(&store, &sk);
        let (restored, _) = store
            .load_blocklace(sk, 1)
            .expect("load")
            .expect("blocks were persisted");
        assert_eq!(restored.len(), lace.len(), "every honest block restores");
        assert_eq!(restored.tips(), lace.tips(), "tips re-derive identically");
    }

    /// ⚑ CORRUPTED-CHECKPOINT POLE: a forged block in the store (valid shape,
    /// signature that does NOT verify — what an offline attacker with redb
    /// write access plants) REFUSES the whole restart. Until 2026-08-08 the
    /// restart path used `from_checkpoint_trusted` and this block sailed into
    /// the restored DAG unverified.
    #[test]
    fn forged_block_in_store_refuses_restart() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        persist_honest_lace(&store, &sk);

        // The mutation: an honestly-created block whose payload is altered
        // AFTER signing (the signature no longer covers the content).
        let mut forged = Block::new(
            &key(9),
            0,
            dregg_blocklace::finality::Payload::Ack,
            Vec::new(),
        );
        forged.payload = dregg_blocklace::finality::Payload::Checkpoint {
            root: [0xEE; 32],
            height: 99,
        };
        // ASSERT THE MUTATION IS PRESENT before reading the verdict: the
        // forged block genuinely fails authentication on its own.
        assert!(
            forged.verify_signature().is_err(),
            "the falsifier must be live: the tampered block's signature must not verify"
        );
        store
            .persist_block(&forged)
            .expect("attacker writes the row");

        // `expect_err` is unavailable here: the Ok payload is `(Blocklace, usize)`
        // and `Blocklace` is not `Debug`. Match, so the refusal is read explicitly.
        let err = match store.load_blocklace(key(7), 1) {
            Err(e) => e,
            Ok(_) => panic!("a store carrying a forged block must REFUSE the restart"),
        };
        assert!(
            format!("{err}").contains("signature"),
            "the refusal names the failed authentication: {err}"
        );
    }

    /// ⚑ EQUIVOCATOR-UNFLAG POLE (the `auto_evict` reversion class): the store
    /// holds a creator's incomparable pair (real, signed equivocation
    /// evidence) while the persisted metadata claims NO equivocators — the
    /// mutation an attacker (or a stale meta write) uses to launder a fork
    /// through a restart. The authenticating loader re-DERIVES equivocation
    /// from the blocks, so the flag comes back.
    #[test]
    fn cleared_equivocator_meta_cannot_unflag_on_restart() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        persist_honest_lace(&store, &sk);

        // A genuine equivocation: same creator, same seq, different payloads,
        // neither in the other's past.
        let eq = key(11);
        let a = Block::new(&eq, 0, dregg_blocklace::finality::Payload::Ack, Vec::new());
        let b = Block::new(
            &eq,
            0,
            dregg_blocklace::finality::Payload::Checkpoint {
                root: [0xAA; 32],
                height: 0,
            },
            Vec::new(),
        );
        assert!(
            a.verify_signature().is_ok() && b.verify_signature().is_ok(),
            "both halves of the pair are REAL signed blocks"
        );
        assert_eq!(a.creator, b.creator);
        store
            .persist_blocks(&[a.clone(), b.clone()])
            .expect("persist the pair");
        // ASSERT THE MUTATION: the persisted meta names NO equivocators.
        let meta = store
            .load_blocklace_meta()
            .expect("meta")
            .expect("meta present");
        assert!(
            meta.equivocators.is_empty(),
            "the falsifier must be live: the meta claims a clean creator set"
        );

        let (restored, _) = store
            .load_blocklace(key(7), 1)
            .expect("load")
            .expect("blocks present");
        assert!(
            restored.equivocators().contains(&a.creator),
            "restart re-derives the equivocation from the blocks — cleared metadata \
             cannot un-flag a creator whose evidence pair is persisted"
        );
    }

    /// The executed-block identity set round-trips (the durable resume state of
    /// the node's identity execution cursor — TauPrefixMonotone closure), and a
    /// never-persisted store reads back EMPTY (pre-upgrade/fresh DB: the commit
    /// log alone then covers every durably applied turn).
    #[test]
    fn executed_block_ids_round_trip_and_default_empty() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        assert_eq!(
            store.load_executed_block_ids().expect("load"),
            Vec::<BlockId>::new(),
            "fresh/pre-upgrade store has no executed-id set"
        );

        let ids: Vec<BlockId> = (0u8..5).map(|i| BlockId([i; 32])).collect();
        store.persist_executed_block_ids(&ids).expect("persist");
        assert_eq!(store.load_executed_block_ids().expect("load"), ids);

        // Re-persisting (batch cadence) overwrites, preserving order.
        let grown: Vec<BlockId> = (0u8..7).map(|i| BlockId([i; 32])).collect();
        store.persist_executed_block_ids(&grown).expect("persist");
        assert_eq!(store.load_executed_block_ids().expect("load"), grown);
    }
}
