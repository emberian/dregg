//! Content-addressed blob store (nameless writes).
//!
//! Write returns hash. No allocation, no indirection.
//! Each write has a computron cost (proportional to size).
//! Each stored blob has an OWNER (quota cell that paid for it).
//! Deletion refunds a portion of the computron cost.

use std::collections::HashMap;

use crate::quota::SpaceBank;
use crate::{ComputronRefund, ContentHash, QuotaId, StorageError};

/// Metadata about a stored blob.
#[derive(Debug, Clone)]
struct BlobMeta {
    /// The quota cell that paid for this blob.
    owner: QuotaId,
    /// Size in bytes.
    size: u64,
    /// Original write cost (computrons charged).
    write_cost: u64,
    /// Reference count (for deduplication — same content, multiple owners).
    ref_count: u32,
}

/// Content-addressed store. Nameless writes: data in, hash out.
#[derive(Debug)]
pub struct ContentStore {
    /// Blob data keyed by content hash.
    blobs: HashMap<ContentHash, Vec<u8>>,
    /// Metadata keyed by content hash.
    meta: HashMap<ContentHash, BlobMeta>,
    /// The space bank governing quota.
    pub bank: SpaceBank,
}

impl ContentStore {
    /// Create a new content store with the given space bank.
    pub fn new(bank: SpaceBank) -> Self {
        Self {
            blobs: HashMap::new(),
            meta: HashMap::new(),
            bank,
        }
    }

    /// Hash data using blake3.
    fn hash(data: &[u8]) -> ContentHash {
        let h = blake3::hash(data);
        ContentHash(*h.as_bytes())
    }

    /// Write data to the store. Returns the content hash.
    /// The payer's quota is charged for the write.
    pub fn write(&mut self, data: &[u8], payer: &QuotaId) -> Result<ContentHash, StorageError> {
        let hash = Self::hash(data);
        let size = data.len() as u64;

        // If content already exists, handle deduplication.
        if let Some(meta) = self.meta.get_mut(&hash) {
            meta.ref_count += 1;
            // Still charge the payer (they're claiming storage under their quota).
            self.bank.charge_write(payer, size)?;
            return Ok(hash);
        }

        // Charge the payer.
        let cost = self.bank.charge_write(payer, size)?;

        // Store the data.
        self.blobs.insert(hash, data.to_vec());
        self.meta.insert(
            hash,
            BlobMeta {
                owner: *payer,
                size,
                write_cost: cost,
                ref_count: 1,
            },
        );

        Ok(hash)
    }

    /// Read data by content hash.
    pub fn read(&self, hash: &ContentHash) -> Option<&[u8]> {
        self.blobs.get(hash).map(|v| v.as_slice())
    }

    /// Splice: replace a subrange of an existing blob, producing a new blob.
    /// This is delete(old) + write(new) atomically.
    pub fn splice(
        &mut self,
        old_hash: &ContentHash,
        offset: usize,
        new_data: &[u8],
        payer: &QuotaId,
    ) -> Result<ContentHash, StorageError> {
        // Read old data.
        let old_data = self
            .blobs
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?
            .clone();

        // Verify ownership.
        let old_meta = self
            .meta
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?;
        if old_meta.owner != *payer {
            return Err(StorageError::NotOwner {
                hash: *old_hash,
                owner: old_meta.owner,
                caller: *payer,
            });
        }

        // Construct new data: old[..offset] + new_data + old[offset+new_data.len()..]
        let end = (offset + new_data.len()).min(old_data.len());
        let mut spliced = Vec::with_capacity(old_data.len());
        spliced.extend_from_slice(&old_data[..offset.min(old_data.len())]);
        spliced.extend_from_slice(new_data);
        if end < old_data.len() {
            spliced.extend_from_slice(&old_data[end..]);
        }

        // Delete old (with refund).
        self.delete(old_hash, payer)?;

        // Write new.
        self.write(&spliced, payer)
    }

    /// Delete a blob. Only the owner can delete. Returns a computron refund.
    pub fn delete(
        &mut self,
        hash: &ContentHash,
        owner: &QuotaId,
    ) -> Result<ComputronRefund, StorageError> {
        let meta = self
            .meta
            .get(hash)
            .ok_or(StorageError::NotFound(*hash))?
            .clone();

        if meta.owner != *owner {
            return Err(StorageError::NotOwner {
                hash: *hash,
                owner: meta.owner,
                caller: *owner,
            });
        }

        // Remove from store.
        if meta.ref_count <= 1 {
            self.blobs.remove(hash);
            self.meta.remove(hash);
        } else {
            if let Some(m) = self.meta.get_mut(hash) {
                m.ref_count -= 1;
            }
        }

        // Process refund through the bank.
        self.bank.process_refund(owner, meta.write_cost, meta.size)
    }

    /// Check if a blob exists.
    pub fn contains(&self, hash: &ContentHash) -> bool {
        self.blobs.contains_key(hash)
    }

    /// Get the size of a blob.
    pub fn blob_size(&self, hash: &ContentHash) -> Option<u64> {
        self.meta.get(hash).map(|m| m.size)
    }

    /// Total bytes stored in this content store.
    pub fn total_bytes(&self) -> u64 {
        self.meta.values().map(|m| m.size).sum()
    }

    /// Number of blobs stored.
    pub fn blob_count(&self) -> usize {
        self.blobs.len()
    }
}
