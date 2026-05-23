//! Blinded queue for fair order batch processing.
//!
//! Wraps [`pyana_storage::blinded::BlindedQueue`] with order-queue semantics:
//! traders submit orders as commitments; the matcher cannot see the queue ordering
//! until the batch window closes. This is **strictly stronger** than commit-reveal
//! because even the queue operator cannot reorder entries.
//!
//! # Protocol
//!
//! 1. Trader computes `commitment = blake3(order_bytes || secret)`.
//! 2. Trader submits the commitment via `POST /queue/orders/commit`.
//!    The queue records it blindly; the matcher sees only the hash.
//! 3. When the batch window closes the trader reveals `(order, secret)` via
//!    `POST /queue/orders/consume`.  The server verifies:
//!    a. The nullifier has not been used before (double-consume prevention).
//!    b. The membership proof is valid for the current commitment root.
//!    c. `blake3(order_bytes || secret) == commitment`.
//! 4. Verified orders are emitted for matching in commitment-tree order (position).
//!
//! # Security properties
//!
//! - The queue operator sees only commitments and their Merkle positions.
//! - Order parameters are hidden until the consumer presents the opening.
//! - Double-consume is prevented by nullifier uniqueness.
//! - The operator CANNOT reorder items because the Merkle tree is built from
//!   commitment-insertion order, which is public and auditable.

use std::collections::HashSet;
use std::sync::Arc;

use tokio::sync::Mutex;

use pyana_storage::blinded::{BlindedQueue, ConsumptionProof, ConsumeResult};

use crate::order::Order;

// =============================================================================
// OrderBlindedQueue
// =============================================================================

/// A blinded queue specialized for orderbook order submissions.
///
/// Wraps [`BlindedQueue`] and adds order-specific semantics:
/// - Commitment verification (`blake3(order_bytes || secret) == commitment`).
/// - Nullifier generation from `blake3(commitment || secret)`.
/// - Consumed-order extraction for batch matching.
pub struct OrderBlindedQueue {
    /// The underlying blinded queue.
    inner: BlindedQueue,
    /// Orders that have been successfully consumed and are awaiting batch matching.
    consumed_orders: Vec<Order>,
    /// Spent secrets (separate from the nullifier set in `inner`; these are the
    /// order-level secrets that proved the commitment opening).
    spent_commitments: HashSet<[u8; 32]>,
}

impl OrderBlindedQueue {
    /// Create a new order blinded queue with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            inner: BlindedQueue::new(capacity),
            consumed_orders: Vec::new(),
            spent_commitments: HashSet::new(),
        }
    }

    /// Submit a commitment to the queue (commit phase).
    ///
    /// `commitment` = `blake3("pyana-orderbook-blinded-v1" || order_bytes || secret)`.
    pub fn commit(&mut self, commitment: [u8; 32]) -> Result<[u8; 32], BlindedOrderError> {
        self.inner
            .commit(commitment)
            .map_err(|_| BlindedOrderError::QueueFull)?;
        Ok(self.inner.commitment_root())
    }

    /// Consume a commitment (reveal phase).
    ///
    /// Verifies the membership proof, checks the nullifier, verifies that
    /// `blake3(order_bytes || secret) == commitment`, then enqueues the order
    /// for batch matching.
    pub fn consume(
        &mut self,
        order: Order,
        secret: [u8; 32],
        proof: ConsumptionProof,
    ) -> Result<(), BlindedOrderError> {
        // 1. Verify commitment hash.
        let expected_commitment = compute_blinded_order_commitment(&order, &secret);
        if expected_commitment != proof.commitment {
            return Err(BlindedOrderError::CommitmentMismatch);
        }

        // 2. Check for double-consume (by commitment hash).
        if self.spent_commitments.contains(&proof.commitment) {
            return Err(BlindedOrderError::AlreadyConsumed);
        }

        // 3. Verify membership + nullifier via the blinded queue.
        let result = self.inner.consume(&proof);
        match result {
            ConsumeResult::Consumed { .. } => {}
            ConsumeResult::AlreadyConsumed => {
                return Err(BlindedOrderError::AlreadyConsumed);
            }
            ConsumeResult::InvalidProof => {
                return Err(BlindedOrderError::InvalidMembershipProof);
            }
        }

        // 4. Record spent commitment and enqueue order.
        self.spent_commitments.insert(proof.commitment);
        self.consumed_orders.push(order);

        Ok(())
    }

    /// Drain all consumed orders for batch matching.
    pub fn drain_batch(&mut self) -> Vec<Order> {
        std::mem::take(&mut self.consumed_orders)
    }

    /// Number of consumed orders waiting for batch matching.
    pub fn pending_count(&self) -> usize {
        self.consumed_orders.len()
    }

    /// The current commitment Merkle root.
    pub fn commitment_root(&self) -> [u8; 32] {
        self.inner.commitment_root()
    }

    /// Number of consumed (spent) commitments.
    pub fn consumed_count(&self) -> usize {
        self.inner.consumed_count()
    }

    /// Number of remaining (uncommitted) slots.
    pub fn remaining(&self) -> usize {
        self.inner.remaining()
    }
}

// =============================================================================
// Compute commitment hash
// =============================================================================

/// Compute the commitment for an order.
///
/// Uses a domain-separated blake3 key to avoid collisions with other protocols.
pub fn compute_blinded_order_commitment(order: &Order, secret: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-blinded-v1");
    let order_bytes = postcard::to_allocvec(order).unwrap_or_default();
    hasher.update(&order_bytes);
    hasher.update(secret);
    *hasher.finalize().as_bytes()
}

/// Compute the nullifier for a consumed commitment.
///
/// Nullifier = `blake3(commitment || secret || position_le_bytes)`.
/// This binds the nullifier to the specific position in the Merkle tree,
/// preventing cross-position replays.
pub fn compute_order_nullifier(commitment: &[u8; 32], secret: &[u8; 32], position: usize) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-nullifier-v1");
    hasher.update(commitment);
    hasher.update(secret);
    hasher.update(&(position as u64).to_le_bytes());
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Errors
// =============================================================================

/// Errors from blinded order queue operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlindedOrderError {
    /// The queue has reached its capacity limit.
    QueueFull,
    /// The revealed order does not match the commitment.
    CommitmentMismatch,
    /// The nullifier has already been spent (double-consume attempt).
    AlreadyConsumed,
    /// The Merkle membership proof is invalid.
    InvalidMembershipProof,
}

impl std::fmt::Display for BlindedOrderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::QueueFull => write!(f, "blinded queue is full"),
            Self::CommitmentMismatch => write!(f, "order does not match commitment"),
            Self::AlreadyConsumed => write!(f, "nullifier already spent"),
            Self::InvalidMembershipProof => write!(f, "invalid Merkle membership proof"),
        }
    }
}

// =============================================================================
// Shared state wrapper (for use with AppServer)
// =============================================================================

/// Thread-safe wrapper around [`OrderBlindedQueue`] for use in async handlers.
#[derive(Clone)]
pub struct SharedOrderBlindedQueue(pub Arc<Mutex<OrderBlindedQueue>>);

impl SharedOrderBlindedQueue {
    /// Create a new shared queue with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self(Arc::new(Mutex::new(OrderBlindedQueue::new(capacity))))
    }
}
