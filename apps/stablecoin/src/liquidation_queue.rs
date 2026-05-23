//! Programmable liquidation queue for the CDP stablecoin system.
//!
//! This module wraps [`ProgrammableQueue`] to provide a spam-resistant submission
//! channel for liquidation candidates. Only genuinely undercollateralized positions
//! may be enqueued; the queue drains in priority order (lowest health factor first)
//! so the most-at-risk positions are always liquidated first.
//!
//! # Design
//!
//! - Uses `programs::open(min_deposit)` for the queue program (any caller with a
//!   minimum deposit can submit).
//!
//!   TODO (Phase 3): Replace with a custom validation program that checks the CDP
//!   health factor in-circuit. The in-circuit check would verify:
//!   `collateral_value * 10_000 < debt * ratio_bps` against an oracle commitment,
//!   so that a position cannot be enqueued unless it is provably undercollateralized
//!   at the submitted oracle price. This eliminates the current application-layer
//!   check and makes the constraint cryptographically enforced.
//!
//! - At application layer we additionally gate enqueue on `position.is_liquidatable(price)`,
//!   preventing spam attempts against healthy positions before the queue even validates.
//!
//! - The queue is drained in priority order via [`LiquidationQueue::drain_priority`]:
//!   positions with the lowest health factor (most undercollateralized) are returned
//!   first, enabling liquidators to act on the most-at-risk positions immediately.

use std::sync::Arc;

use tokio::sync::Mutex;

use pyana_app_framework::queue_endpoint::QueueEndpoint;
use pyana_storage::{
    programmable::{ProgrammableQueue, programs},
    queue::QueueEntry,
};

use crate::cdp::CollateralPosition;

// =============================================================================
// Configuration
// =============================================================================

/// Minimum deposit required to submit a liquidation candidate to the queue.
///
/// Acts as a spam-prevention measure: callers must stake a small deposit,
/// which is forfeited if the position turns out to be healthy (rejected
/// at dequeue time). In a future version this will be enforced in-circuit.
pub const LIQUIDATION_QUEUE_MIN_DEPOSIT: u64 = 100;

/// Capacity of the liquidation queue (maximum pending candidates).
pub const LIQUIDATION_QUEUE_CAPACITY: usize = 256;

// =============================================================================
// LiquidationQueue
// =============================================================================

/// A spam-resistant, priority-ordered queue of liquidation candidates.
///
/// Wraps [`ProgrammableQueue`] and adds:
/// - Application-layer health-factor gate (position must be liquidatable).
/// - Priority ordering: drain returns positions sorted lowest-health-first.
/// - Deduplication: a position ID can only appear once in the queue.
#[derive(Clone)]
pub struct LiquidationQueue {
    inner: Arc<Mutex<ProgrammableQueue>>,
    /// Tracks position IDs currently in the queue to prevent duplicate entries.
    pending: Arc<Mutex<Vec<PendingEntry>>>,
}

/// Metadata stored alongside each pending liquidation submission.
#[derive(Clone, Debug)]
struct PendingEntry {
    /// CDP position ID.
    position_id: [u8; 32],
    /// Oracle price at time of submission (used for health-factor ordering).
    oracle_price: u64,
    /// Health factor in basis points at submission time (lower = worse).
    health_factor_bps: u64,
}

/// A single liquidation candidate ready for execution.
#[derive(Clone, Debug)]
pub struct LiquidationCandidate {
    /// CDP position ID to be liquidated.
    pub position_id: [u8; 32],
    /// Oracle price used to assess health at submission time.
    pub oracle_price: u64,
    /// Collateral ratio in basis points at submission (lower = more urgent).
    pub health_factor_bps: u64,
}

/// Errors from the liquidation queue.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum LiquidationQueueError {
    #[error("position is not liquidatable at oracle price {price}")]
    NotLiquidatable { price: u64 },
    #[error("position {position_id:?} is already pending in the queue")]
    AlreadyPending { position_id: [u8; 32] },
    #[error("queue is full (capacity {capacity})")]
    QueueFull { capacity: usize },
    #[error("queue is empty")]
    Empty,
    #[error("queue constraint violation: {detail}")]
    ConstraintViolation { detail: String },
}

impl LiquidationQueue {
    /// Create a new liquidation queue with the configured min deposit.
    pub fn new() -> Self {
        // Use programs::open(min_deposit) for the queue program.
        //
        // TODO (Phase 3): Replace with a custom QueueProgram that enforces
        // undercollateralization in-circuit by checking the health factor
        // against a committed oracle price. The circuit would encode:
        //   collateral_value * BPS_SCALE < debt * ratio_bps
        // as a STARK constraint, making the check cryptographically sound
        // rather than application-layer enforced.
        let program = programs::open(LIQUIDATION_QUEUE_MIN_DEPOSIT);
        let queue = ProgrammableQueue::new(
            "liquidations".into(),
            [0u8; 32], // system-owned queue
            program,
            None,
            LIQUIDATION_QUEUE_CAPACITY,
        );
        Self {
            inner: Arc::new(Mutex::new(queue)),
            pending: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Submit a position as a liquidation candidate.
    ///
    /// Rejects the submission if:
    /// - The position is not currently liquidatable at `oracle_price`.
    /// - The position is already in the queue (deduplication).
    /// - The queue program rejects the entry (e.g., insufficient deposit).
    pub async fn submit(
        &self,
        position: &CollateralPosition,
        oracle_price: u64,
        sender: [u8; 32],
        deposit: u64,
    ) -> Result<(), LiquidationQueueError> {
        // Application-layer gate: must be genuinely undercollateralized.
        if !position.is_liquidatable(oracle_price) {
            return Err(LiquidationQueueError::NotLiquidatable { price: oracle_price });
        }

        let mut pending = self.pending.lock().await;

        // Deduplication: reject if already queued.
        if pending.iter().any(|e| e.position_id == position.id) {
            return Err(LiquidationQueueError::AlreadyPending {
                position_id: position.id,
            });
        }

        // Compute health factor for priority ordering.
        let health_factor_bps = position
            .collateral_ratio_bps(oracle_price)
            .unwrap_or(u64::MAX);

        // Hash position_id into content_hash for the queue entry.
        let content_hash = *blake3::hash(&position.id).as_bytes();

        let entry = QueueEntry {
            content_hash,
            sender,
            deposit,
            enqueued_at: 0, // height tracking handled externally
            size: 32,
        };

        let ctx = pyana_storage::programmable::ValidationContext {
            sender,
            current_height: 0,
            current_epoch: 0,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };

        let mut q = self.inner.lock().await;
        q.enqueue_validated(entry, &ctx)
            .map_err(|e| LiquidationQueueError::ConstraintViolation {
                detail: format!("{e:?}"),
            })?;

        pending.push(PendingEntry {
            position_id: position.id,
            oracle_price,
            health_factor_bps,
        });

        Ok(())
    }

    /// Drain the queue in priority order (lowest health factor first).
    ///
    /// Returns all pending candidates sorted by health factor ascending.
    /// Does NOT modify the underlying queue — this is a read-only priority view.
    /// Use [`remove`] to consume individual candidates after inspection.
    pub async fn drain_priority(&self) -> Vec<LiquidationCandidate> {
        let mut pending = self.pending.lock().await.clone();
        // Sort by health_factor_bps ascending (most-at-risk first).
        pending.sort_by_key(|e| e.health_factor_bps);
        pending
            .into_iter()
            .map(|e| LiquidationCandidate {
                position_id: e.position_id,
                oracle_price: e.oracle_price,
                health_factor_bps: e.health_factor_bps,
            })
            .collect()
    }

    /// Remove a position from the pending set (after liquidation is executed).
    pub async fn remove(&self, position_id: &[u8; 32]) {
        let mut pending = self.pending.lock().await;
        pending.retain(|e| &e.position_id != position_id);
    }

    /// Returns the number of pending liquidation candidates.
    pub async fn len(&self) -> usize {
        self.pending.lock().await.len()
    }

    /// Returns true if no candidates are pending.
    pub async fn is_empty(&self) -> bool {
        self.pending.lock().await.is_empty()
    }

    /// Build a [`QueueEndpoint`] backed by a fresh programmable queue with the
    /// same program configuration, suitable for mounting at
    /// `AppServer::with_queue_endpoint("/queue/liquidations", endpoint)`.
    ///
    /// The HTTP endpoint provides raw queue access (enqueue/dequeue/status).
    /// Application-layer health-factor validation is enforced by [`LiquidationQueue::submit`],
    /// not by the HTTP endpoint directly.
    pub fn make_endpoint() -> QueueEndpoint {
        let program = pyana_storage::programmable::programs::open(LIQUIDATION_QUEUE_MIN_DEPOSIT);
        let queue = ProgrammableQueue::new(
            "liquidations".into(),
            [0u8; 32],
            program,
            None,
            LIQUIDATION_QUEUE_CAPACITY,
        );
        QueueEndpoint::new(queue)
    }
}

impl Default for LiquidationQueue {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cdp::{CollateralPosition, ETH_ASSET_TYPE};
    use crate::circuit::MIN_RATIO_BPS;
    use pyana_cell::CellId;

    fn alice() -> CellId {
        CellId([0xAA; 32])
    }

    /// Create an undercollateralized position: 100 ETH collateral, 200k PUSD debt.
    /// At price=1200: ratio = 100*1200*10000/200000 = 6000 bps = 60% < 150%.
    fn undercollateralized_position(height: u64) -> CollateralPosition {
        let mut pos =
            CollateralPosition::open(alice(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, height)
                .unwrap();
        pos.debt_amount = 200_000;
        pos
    }

    /// Create a healthy position: 1000 ETH, 100k debt.
    /// At price=2000: ratio = 1000*2000*10000/100000 = 200000 bps = well over 150%.
    fn healthy_position(height: u64) -> CollateralPosition {
        let mut pos =
            CollateralPosition::open(alice(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, height)
                .unwrap();
        pos.debt_amount = 100_000;
        pos
    }

    // ---- Upgrade 1, Test 1: healthy position is rejected ---
    #[tokio::test]
    async fn healthy_position_rejected_from_queue() {
        let queue = LiquidationQueue::new();
        let pos = healthy_position(100);
        // At price=2000, ratio is ~200% — well above 150% threshold.
        let result = queue.submit(&pos, 2000, [0xAA; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT).await;
        assert!(
            matches!(result, Err(LiquidationQueueError::NotLiquidatable { .. })),
            "expected NotLiquidatable, got {result:?}"
        );
        assert_eq!(queue.len().await, 0);
    }

    // ---- Upgrade 1, Test 2: undercollateralized position is accepted ---
    #[tokio::test]
    async fn undercollateralized_position_accepted_into_queue() {
        let queue = LiquidationQueue::new();
        let pos = undercollateralized_position(100);
        // At price=1200: ratio = 60% < 150%
        assert!(pos.is_liquidatable(1200));
        let result = queue.submit(&pos, 1200, [0xBB; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT).await;
        assert!(result.is_ok(), "expected Ok, got {result:?}");
        assert_eq!(queue.len().await, 1);
    }

    // ---- Upgrade 1, Test 3: duplicate submission rejected ---
    #[tokio::test]
    async fn duplicate_position_rejected() {
        let queue = LiquidationQueue::new();
        let pos = undercollateralized_position(100);
        queue
            .submit(&pos, 1200, [0xBB; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT)
            .await
            .unwrap();
        let result = queue
            .submit(&pos, 1200, [0xBB; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT)
            .await;
        assert!(
            matches!(result, Err(LiquidationQueueError::AlreadyPending { .. })),
            "expected AlreadyPending, got {result:?}"
        );
        assert_eq!(queue.len().await, 1); // still only 1
    }

    // ---- Upgrade 1, Test 4: drain returns lowest-health-factor first ---
    #[tokio::test]
    async fn drain_priority_lowest_health_first() {
        let queue = LiquidationQueue::new();

        // Position A: 100 ETH, 200k debt. At price=1200: ratio=6000 bps (60%).
        let pos_a = undercollateralized_position(100);

        // Position B: 50 ETH, 80k debt. At price=1200: ratio=50*1200*10000/80000=7500 bps (75%).
        let mut pos_b =
            CollateralPosition::open(CellId([0xBB; 32]), 50, ETH_ASSET_TYPE, MIN_RATIO_BPS, 101)
                .unwrap();
        pos_b.debt_amount = 80_000;

        // Position C: 200 ETH, 1M debt. At price=1200: ratio=200*1200*10000/1_000_000=2400 bps (24%).
        let mut pos_c =
            CollateralPosition::open(CellId([0xCC; 32]), 200, ETH_ASSET_TYPE, MIN_RATIO_BPS, 102)
                .unwrap();
        pos_c.debt_amount = 1_000_000;

        assert!(pos_a.is_liquidatable(1200));
        assert!(pos_b.is_liquidatable(1200));
        assert!(pos_c.is_liquidatable(1200));

        // Submit in arbitrary order.
        queue.submit(&pos_b, 1200, [0x01; 32], 200).await.unwrap();
        queue.submit(&pos_a, 1200, [0x01; 32], 200).await.unwrap();
        queue.submit(&pos_c, 1200, [0x01; 32], 200).await.unwrap();

        let candidates = queue.drain_priority().await;
        assert_eq!(candidates.len(), 3);

        // Must be in ascending health_factor_bps order (most-at-risk first).
        // C: 2400, A: 6000, B: 7500
        assert_eq!(candidates[0].position_id, pos_c.id, "C should be first (most at risk)");
        assert_eq!(candidates[1].position_id, pos_a.id, "A should be second");
        assert_eq!(candidates[2].position_id, pos_b.id, "B should be last (least at risk)");

        // Health factors are ascending.
        assert!(candidates[0].health_factor_bps <= candidates[1].health_factor_bps);
        assert!(candidates[1].health_factor_bps <= candidates[2].health_factor_bps);
    }

    // ---- Upgrade 1, Test 5: remove after liquidation ---
    #[tokio::test]
    async fn remove_after_liquidation_clears_entry() {
        let queue = LiquidationQueue::new();
        let pos = undercollateralized_position(100);
        queue
            .submit(&pos, 1200, [0xBB; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT)
            .await
            .unwrap();
        assert_eq!(queue.len().await, 1);

        queue.remove(&pos.id).await;
        assert_eq!(queue.len().await, 0);
        assert!(queue.is_empty().await);
    }

    // ---- Upgrade 1, Test 6: insufficient deposit rejected by queue program ---
    #[tokio::test]
    async fn insufficient_deposit_rejected() {
        let queue = LiquidationQueue::new();
        let pos = undercollateralized_position(100);
        // Deposit below LIQUIDATION_QUEUE_MIN_DEPOSIT.
        let result = queue
            .submit(&pos, 1200, [0xBB; 32], LIQUIDATION_QUEUE_MIN_DEPOSIT - 1)
            .await;
        assert!(
            matches!(result, Err(LiquidationQueueError::ConstraintViolation { .. })),
            "expected ConstraintViolation for insufficient deposit, got {result:?}"
        );
    }
}
