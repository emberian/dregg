//! # pyana-storage
//!
//! Resource-accountable, quota-bounded, computron-metered storage.
//!
//! Design principles:
//! 1. ALL resources are owned and bounded (Robigalia principle)
//! 2. Storage is RENTED (per-epoch cost), not purchased (one-time)
//! 3. Deletion is incentivized (partial refund)
//! 4. Relay buffering has explicit cost (prevents store-and-forward abuse)
//! 5. Light clients can verify availability without full download (erasure sampling)
//! 6. Content-addressing eliminates indirection (nameless writes = cheap proofs)
//! 7. Quotas compose with computrons (quota IS a computron allocation)

pub mod content;
pub mod erasure;
pub mod inbox;
pub mod metering;
pub mod multi_asset;
pub mod namespace_mount;
pub mod operator;
pub mod programmable;
pub mod pubsub;
pub mod queue;
pub mod quota;
pub mod relay;

/// A content hash (blake3) identifying a blob.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ContentHash(pub [u8; 32]);

/// Identifies a quota cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct QuotaId(pub u64);

/// Computron refund returned on deletion or expiry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComputronRefund {
    pub quota_id: QuotaId,
    pub amount: u64,
}

/// Errors from storage operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageError {
    /// The payer's quota is exhausted (insufficient computrons).
    QuotaExhausted { available: u64, required: u64 },
    /// The payer's byte cap would be exceeded.
    ByteCapExceeded { current: u64, max: u64, attempted: u64 },
    /// The referenced content hash does not exist.
    NotFound(ContentHash),
    /// The caller is not the owner of the referenced content.
    NotOwner { hash: ContentHash, owner: QuotaId, caller: QuotaId },
    /// Quota cell not found.
    QuotaNotFound(QuotaId),
    /// Erasure reconstruction failed (insufficient chunks).
    InsufficientChunks { have: usize, need: usize },
    /// Relay queue rejected (quota exhausted or invalid).
    RelayRejected(String),
}

#[cfg(test)]
mod tests;
