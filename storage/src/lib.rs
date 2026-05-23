//! # pyana-storage
//!
//! # Trust Model
//!
//! This crate operates at the **OPERATOR-TRUSTED** trust level.
//!
//! - **Soundness**: Storage operators (relay nodes) are bonded and subject to dispute
//!   resolution. Content-addressing (BLAKE3 hashes) provides integrity -- any corruption
//!   is detectable. Erasure coding provides availability even if some operators are offline.
//! - **Assumptions**: Relay operators honestly store data for the rental period. They are
//!   economically incentivized (bond slashing on proven data withholding). Operators cannot
//!   forge content (content-addressed), but CAN withhold it (availability fault).
//! - **Verifiable by**: Anyone can verify content integrity via BLAKE3 hash. Data
//!   availability is verified via erasure sampling (probabilistic guarantee). Quota
//!   accounting is verified by the federation executor during turn execution.
//!
//! ## Dispute Path
//! If an operator withholds data:
//! 1. Client requests erasure-coded chunks from multiple operators
//! 2. If insufficient chunks are returned, client files a dispute
//! 3. Federation slashes the operator's bond and redistributes
//! 4. Client can reconstruct from remaining honest operators
//!
//! ## Path to Trustless
//! Full trustlessness requires data availability sampling (DAS) at the consensus layer,
//! where the blocklace participants collectively guarantee availability without trusting
//! any individual operator.
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
pub mod dedup;
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
pub mod wal;

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
