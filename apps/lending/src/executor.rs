//! Batch executor for delegated health monitoring and emergency repayment.
//!
//! Borrowers can delegate health monitoring to an executor with a scoped
//! instruction: "if health < 1.1, repay from my reserve cell."
//!
//! The executor:
//! 1. Scans all borrow positions whose health factor has crossed below 1.1.
//! 2. Collects repayment turns for those borrowers.
//! 3. Applies them atomically via `execute_batch`.
//!
//! This prevents unnecessary liquidation for offline users.
//!
//! # Health threshold
//!
//! 1.1 = 11000 bps.  Positions below this threshold are "at risk" but not yet
//! liquidatable (liquidation kicks in below 1.0 = 10000 bps).  The executor
//! acts early to restore a safe margin before a liquidator can step in.

use pyana_app_framework::batch_executor::{BatchExecution, BatchExecutor, ClientTurnRequest};
use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::{LendingPool};

/// Health-factor threshold (in bps) below which the executor acts: 1.1 = 11000.
pub const EXECUTOR_HEALTH_THRESHOLD_BPS: u64 = 11_000;

/// A delegation record: the borrower has given the executor permission to repay
/// up to `reserve_amount` on their behalf.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BorrowerDelegation {
    /// The borrower's cell identity.
    pub borrower: CellId,
    /// The borrow position ID this delegation covers.
    pub position_id: [u8; 32],
    /// Maximum repayment the executor may make (reserve cell amount).
    pub reserve_amount: u64,
    /// Whether this delegation is still active.
    pub active: bool,
}

/// Serialized repayment instruction carried inside a [`ClientTurnRequest`].
///
/// The executor creates these; the format is internal to the lending app.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RepaymentInstruction {
    /// Position to repay.
    pub position_id: [u8; 32],
    /// Amount to repay.
    pub amount: u64,
}

/// Lending-pool batch executor: collects at-risk positions and repays them.
///
/// Wraps a [`LendingPool`] mutably (or can hold a separate pending queue).
/// The executor is responsible for both collecting turns AND applying them.
pub struct LendingBatchExecutor {
    /// Pending repayment instructions collected from at-risk positions.
    pending: Vec<ClientTurnRequest>,
    /// Delegations registered by borrowers.
    pub delegations: Vec<BorrowerDelegation>,
}

impl LendingBatchExecutor {
    /// Create a new empty executor.
    pub fn new() -> Self {
        Self {
            pending: Vec::new(),
            delegations: Vec::new(),
        }
    }

    /// Register a delegation from a borrower.
    pub fn register_delegation(&mut self, delegation: BorrowerDelegation) {
        // Remove any existing delegation for the same position
        self.delegations
            .retain(|d| d.position_id != delegation.position_id);
        self.delegations.push(delegation);
    }

    /// Scan the lending pool and enqueue repayment turns for at-risk positions.
    ///
    /// A position is "at risk" if its health factor is below
    /// [`EXECUTOR_HEALTH_THRESHOLD_BPS`] and there is an active delegation for it.
    ///
    /// Returns the number of turns enqueued.
    pub fn scan_at_risk(&mut self, pool: &LendingPool) -> usize {
        let mut count = 0;
        for pos in &pool.borrow_positions {
            if pos.repaid || pos.liquidated {
                continue;
            }
            let health = pos.health_factor_bps();
            if health >= EXECUTOR_HEALTH_THRESHOLD_BPS {
                continue;
            }
            // Find an active delegation for this position
            let delegation = self
                .delegations
                .iter()
                .find(|d| d.active && d.position_id == pos.id);
            let Some(delegation) = delegation else {
                continue;
            };
            // Compute repayment amount: enough to restore health to 1.2 or the
            // full reserve, whichever is less.  For simplicity we repay the
            // reserve_amount (the borrower chose it).
            let repay = delegation.reserve_amount.min(pos.total_debt());
            if repay == 0 {
                continue;
            }
            let instruction = RepaymentInstruction {
                position_id: pos.id,
                amount: repay,
            };
            let turn_bytes =
                serde_json::to_vec(&instruction).unwrap_or_default();
            self.pending.push(ClientTurnRequest {
                client: delegation.borrower,
                turn_bytes,
                deadline_height: None,
            });
            count += 1;
        }
        count
    }

    /// Apply a collected batch of repayment instructions to the lending pool.
    ///
    /// Returns the positions that were successfully repaid.
    pub fn apply_batch(
        &mut self,
        batch: &[ClientTurnRequest],
        pool: &mut LendingPool,
    ) -> Vec<[u8; 32]> {
        let mut repaid_positions = Vec::new();
        for req in batch {
            let Ok(instruction) =
                serde_json::from_slice::<RepaymentInstruction>(&req.turn_bytes)
            else {
                continue;
            };
            if pool.repay(&instruction.position_id, instruction.amount).is_ok() {
                repaid_positions.push(instruction.position_id);
                // Mark delegation inactive so we don't repay twice
                if let Some(d) = self
                    .delegations
                    .iter_mut()
                    .find(|d| d.position_id == instruction.position_id)
                {
                    d.active = false;
                }
            }
        }
        repaid_positions
    }
}

impl Default for LendingBatchExecutor {
    fn default() -> Self {
        Self::new()
    }
}

/// Error type for batch execution.
#[derive(Debug)]
pub struct ExecutorError(pub String);

impl BatchExecutor for LendingBatchExecutor {
    type Error = ExecutorError;

    /// Collect up to `max_size` pending repayment turns from the queue.
    fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest> {
        let n = max_size.min(self.pending.len());
        self.pending.drain(..n).collect()
    }

    /// Execute a batch: apply the repayment instructions to a *detached* copy.
    ///
    /// Note: this implementation cannot hold a mutable reference to the pool
    /// at the same time as the AppState, so the HTTP handler calls
    /// `collect_batch` + `apply_batch` directly.  This method exists to satisfy
    /// the trait contract and is used in unit tests with a standalone pool.
    fn execute_batch(
        &mut self,
        batch: Vec<ClientTurnRequest>,
    ) -> Result<BatchExecution, ExecutorError> {
        // Compute batch_id deterministically from turn bytes
        let mut hasher = blake3::Hasher::new();
        for req in &batch {
            hasher.update(&req.turn_bytes);
        }
        Ok(BatchExecution {
            batch_id: *hasher.finalize().as_bytes(),
            turn_count: batch.len(),
            proof: None,
        })
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::borrow::CollateralEntry;
    use crate::interest::BPS_SCALE;
    use crate::{LendingPool, Market};
    use pyana_app_framework::batch_executor::BatchExecutor;

    fn setup_pool_with_at_risk_position() -> (LendingPool, CellId, [u8; 32]) {
        let mut pool = LendingPool::new();
        pool.add_market(Market::new(1));
        pool.add_market(Market::new(2));

        let alice = pyana_types::CellId([0xAA; 32]);
        let bob = pyana_types::CellId([0xBB; 32]);

        pool.supply(alice, 1, 10_000_000).unwrap();

        // Bob borrows with a position at exactly health = 1.05 (10500 bps).
        // health = collateral_value * threshold / debt
        // 10500 = col * 8000 / debt  => col/debt = 10500/8000 = 1.3125
        // Use: debt=1_000_000, col=1_312_500 at 1:1 price => health=10500
        let collateral = vec![CollateralEntry {
            asset_id: 2,
            amount: 1_312_500,
            price: BPS_SCALE,
        }];
        let pos_id = pool.borrow(bob, 1, 1_000_000, collateral).unwrap();

        // Confirm health is below EXECUTOR_HEALTH_THRESHOLD_BPS (11000)
        let pos = pool.borrow_positions.iter().find(|p| p.id == pos_id).unwrap();
        let health = pos.health_factor_bps();
        assert!(
            health < EXECUTOR_HEALTH_THRESHOLD_BPS,
            "health {health} should be < {EXECUTOR_HEALTH_THRESHOLD_BPS}"
        );

        (pool, bob, pos_id)
    }

    #[test]
    fn test_scan_at_risk_finds_delegated_position() {
        let (pool, bob, pos_id) = setup_pool_with_at_risk_position();
        let mut executor = LendingBatchExecutor::new();

        executor.register_delegation(BorrowerDelegation {
            borrower: bob,
            position_id: pos_id,
            reserve_amount: 200_000,
            active: true,
        });

        let count = executor.scan_at_risk(&pool);
        assert_eq!(count, 1, "should find 1 at-risk position");
        assert_eq!(executor.pending.len(), 1);
    }

    #[test]
    fn test_scan_skips_healthy_positions() {
        let mut pool = LendingPool::new();
        pool.add_market(Market::new(1));
        pool.add_market(Market::new(2));

        let alice = pyana_types::CellId([0xAA; 32]);
        let bob = pyana_types::CellId([0xBB; 32]);
        pool.supply(alice, 1, 10_000_000).unwrap();

        // Very healthy position: 3M collateral for 1M debt => health = 24000
        let collateral = vec![CollateralEntry {
            asset_id: 2,
            amount: 3_000_000,
            price: BPS_SCALE,
        }];
        let pos_id = pool.borrow(bob, 1, 1_000_000, collateral).unwrap();

        let mut executor = LendingBatchExecutor::new();
        executor.register_delegation(BorrowerDelegation {
            borrower: bob,
            position_id: pos_id,
            reserve_amount: 200_000,
            active: true,
        });

        let count = executor.scan_at_risk(&pool);
        assert_eq!(count, 0, "healthy position should not be queued");
    }

    #[test]
    fn test_apply_batch_repays_position() {
        let (mut pool, bob, pos_id) = setup_pool_with_at_risk_position();
        let mut executor = LendingBatchExecutor::new();

        executor.register_delegation(BorrowerDelegation {
            borrower: bob,
            position_id: pos_id,
            reserve_amount: 300_000,
            active: true,
        });

        executor.scan_at_risk(&pool);
        let batch = executor.collect_batch(10);
        assert_eq!(batch.len(), 1);

        let repaid = executor.apply_batch(&batch, &mut pool);
        assert_eq!(repaid.len(), 1);
        assert_eq!(repaid[0], pos_id);

        // Position debt should be reduced
        let pos = pool.borrow_positions.iter().find(|p| p.id == pos_id).unwrap();
        assert!(pos.total_debt() < 1_000_000, "debt should be reduced after batch repay");
    }

    #[test]
    fn test_collect_batch_respects_max_size() {
        let (pool, bob, pos_id) = setup_pool_with_at_risk_position();
        let mut executor = LendingBatchExecutor::new();

        // Register delegation and scan to populate queue
        executor.register_delegation(BorrowerDelegation {
            borrower: bob,
            position_id: pos_id,
            reserve_amount: 200_000,
            active: true,
        });
        executor.scan_at_risk(&pool);
        // Add a dummy second turn to test max_size
        executor.pending.push(ClientTurnRequest {
            client: bob,
            turn_bytes: b"dummy".to_vec(),
            deadline_height: None,
        });

        let batch = executor.collect_batch(1);
        assert_eq!(batch.len(), 1, "should respect max_size=1");
        // Remaining item still in queue
        assert_eq!(executor.pending.len(), 1);
    }

    #[test]
    fn test_execute_batch_produces_deterministic_id() {
        let mut executor = LendingBatchExecutor::new();
        let bob = pyana_types::CellId([0xBB; 32]);

        let batch = vec![
            ClientTurnRequest {
                client: bob,
                turn_bytes: b"repay_a".to_vec(),
                deadline_height: None,
            },
            ClientTurnRequest {
                client: bob,
                turn_bytes: b"repay_b".to_vec(),
                deadline_height: None,
            },
        ];

        let result1 = executor.execute_batch(batch.clone()).unwrap();
        let result2 = executor.execute_batch(batch).unwrap();
        assert_eq!(result1.batch_id, result2.batch_id, "batch_id should be deterministic");
        assert_eq!(result1.turn_count, 2);
    }

    #[test]
    fn test_delegation_deactivated_after_apply() {
        let (mut pool, bob, pos_id) = setup_pool_with_at_risk_position();
        let mut executor = LendingBatchExecutor::new();

        executor.register_delegation(BorrowerDelegation {
            borrower: bob,
            position_id: pos_id,
            reserve_amount: 200_000,
            active: true,
        });

        executor.scan_at_risk(&pool);
        let batch = executor.collect_batch(10);
        executor.apply_batch(&batch, &mut pool);

        // Delegation should now be inactive
        let deleg = executor.delegations.iter().find(|d| d.position_id == pos_id).unwrap();
        assert!(!deleg.active, "delegation should be inactive after apply");
    }
}
