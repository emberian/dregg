//! Cell migration two-phase commit protocol and state tracking.

use std::collections::HashMap;

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

/// State of a cell migration operation (two-phase commit protocol).
///
/// Cell migration moves a cell from one federation to another. Without a two-phase
/// protocol, a network partition after the source freezes the cell but before the
/// target receives the bundle would leave the cell in limbo (source thinks it's
/// gone, target never received it).
///
/// The protocol:
/// 1. Source freezes the cell (prevents further turns) and transitions to `Frozen`.
/// 2. Source sends the migration bundle to the target.
/// 3. Target acknowledges receipt -> source transitions to `AwaitingReceipt`.
/// 4. On receipt confirmation, source permanently removes the cell (migration complete).
/// 5. On timeout without receipt: source unfreezes the cell (migration cancelled).
///
/// The target checks for cancellation before accepting: if the source cancelled,
/// the target must not accept the bundle (preventing double-existence).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationState {
    /// No migration in progress for this cell.
    Idle,
    /// The cell is frozen for migration. No turns may execute against it.
    /// If `timeout` blocks elapse without transitioning to `AwaitingReceipt`,
    /// the migration is cancelled and the cell is unfrozen.
    Frozen {
        /// The cell being migrated.
        cell_id: CellId,
        /// The target federation receiving the cell.
        target: [u8; 32],
        /// Block height at which the cell was frozen.
        frozen_at: u64,
        /// Maximum blocks to wait before auto-cancellation.
        timeout: u64,
    },
    /// The migration bundle was sent and we are waiting for the target's receipt.
    /// If `timeout` blocks elapse without confirmation, migration is cancelled.
    AwaitingReceipt {
        /// The cell being migrated.
        cell_id: CellId,
        /// The target federation.
        target: [u8; 32],
        /// Block height at which the bundle was sent.
        sent_at: u64,
        /// Maximum blocks to wait for receipt confirmation.
        timeout: u64,
    },
    /// The migration completed successfully. The cell now lives on the target federation.
    Completed {
        /// The cell that was migrated.
        cell_id: CellId,
        /// The target federation that now owns the cell.
        target: [u8; 32],
        /// Block height at which the migration was confirmed.
        confirmed_at: u64,
    },
    /// The migration was cancelled (timeout or explicit cancel).
    /// The cell is unfrozen and available for local turns again.
    Cancelled {
        /// The cell whose migration was cancelled.
        cell_id: CellId,
        /// Reason for cancellation.
        reason: MigrationCancelReason,
    },
}

/// Reason a cell migration was cancelled.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationCancelReason {
    /// Timed out waiting for the target to acknowledge the bundle.
    Timeout,
    /// Explicitly cancelled by the source (e.g., operator intervention).
    Explicit,
    /// The target rejected the migration bundle.
    TargetRejected,
}

/// Manages cell migration state for a federation's executor.
///
/// Tracks which cells are currently being migrated and enforces the two-phase
/// commit protocol with timeout-based cancellation.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CellMigrationManager {
    /// Active migration states, keyed by cell ID.
    migrations: HashMap<CellId, MigrationState>,
}

impl CellMigrationManager {
    /// Create a new empty migration manager.
    pub fn new() -> Self {
        Self {
            migrations: HashMap::new(),
        }
    }

    /// Begin a cell migration: freeze the cell for transfer to the target federation.
    ///
    /// Returns `Err` if the cell is already being migrated.
    pub fn begin_migration(
        &mut self,
        cell_id: CellId,
        target: [u8; 32],
        current_height: u64,
        timeout: u64,
    ) -> Result<(), MigrationError> {
        if let Some(state) = self.migrations.get(&cell_id) {
            match state {
                MigrationState::Idle | MigrationState::Cancelled { .. } => {
                    // Can start a new migration (previous was idle or cancelled)
                }
                _ => return Err(MigrationError::AlreadyMigrating),
            }
        }

        self.migrations.insert(
            cell_id,
            MigrationState::Frozen {
                cell_id,
                target,
                frozen_at: current_height,
                timeout,
            },
        );
        Ok(())
    }

    /// Record that the migration bundle was sent to the target.
    ///
    /// Transitions from `Frozen` to `AwaitingReceipt`.
    pub fn bundle_sent(
        &mut self,
        cell_id: CellId,
        current_height: u64,
        receipt_timeout: u64,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::Frozen { target, .. } => {
                let target = *target;
                self.migrations.insert(
                    cell_id,
                    MigrationState::AwaitingReceipt {
                        cell_id,
                        target,
                        sent_at: current_height,
                        timeout: receipt_timeout,
                    },
                );
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Confirm that the target received and accepted the migration bundle.
    ///
    /// Transitions to `Completed`. After this, the cell can be removed from the
    /// local ledger.
    pub fn confirm_receipt(
        &mut self,
        cell_id: CellId,
        current_height: u64,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::AwaitingReceipt { target, .. } => {
                let target = *target;
                self.migrations.insert(
                    cell_id,
                    MigrationState::Completed {
                        cell_id,
                        target,
                        confirmed_at: current_height,
                    },
                );
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Check for timed-out migrations and cancel them.
    ///
    /// Returns the cell IDs of migrations that were cancelled due to timeout.
    /// For each cancelled migration, the cell is unfrozen and available for local
    /// turns again.
    pub fn check_timeouts(&mut self, current_height: u64) -> Vec<CellId> {
        let mut cancelled = Vec::new();

        let timed_out: Vec<CellId> = self
            .migrations
            .iter()
            .filter_map(|(cell_id, state)| match state {
                MigrationState::Frozen {
                    frozen_at, timeout, ..
                } => {
                    if current_height.saturating_sub(*frozen_at) > *timeout {
                        Some(*cell_id)
                    } else {
                        None
                    }
                }
                MigrationState::AwaitingReceipt {
                    sent_at, timeout, ..
                } => {
                    if current_height.saturating_sub(*sent_at) > *timeout {
                        Some(*cell_id)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect();

        for cell_id in timed_out {
            self.migrations.insert(
                cell_id,
                MigrationState::Cancelled {
                    cell_id,
                    reason: MigrationCancelReason::Timeout,
                },
            );
            cancelled.push(cell_id);
        }

        cancelled
    }

    /// Explicitly cancel a migration (e.g., operator intervention).
    ///
    /// The cell is unfrozen and available for local turns again.
    pub fn cancel(
        &mut self,
        cell_id: CellId,
        reason: MigrationCancelReason,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::Frozen { .. } | MigrationState::AwaitingReceipt { .. } => {
                self.migrations
                    .insert(cell_id, MigrationState::Cancelled { cell_id, reason });
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Check if a cell is currently frozen for migration.
    ///
    /// Returns `true` if the cell is in `Frozen` or `AwaitingReceipt` state,
    /// meaning no local turns should execute against it.
    pub fn is_frozen(&self, cell_id: &CellId) -> bool {
        matches!(
            self.migrations.get(cell_id),
            Some(MigrationState::Frozen { .. } | MigrationState::AwaitingReceipt { .. })
        )
    }

    /// Check if a migration was cancelled (target should reject the bundle).
    pub fn is_cancelled(&self, cell_id: &CellId) -> bool {
        matches!(
            self.migrations.get(cell_id),
            Some(MigrationState::Cancelled { .. })
        )
    }

    /// Get the migration state for a cell.
    pub fn get(&self, cell_id: &CellId) -> Option<&MigrationState> {
        self.migrations.get(cell_id)
    }

    /// Remove completed or cancelled migration entries (cleanup).
    pub fn gc_completed(&mut self) -> Vec<CellId> {
        let removable: Vec<CellId> = self
            .migrations
            .iter()
            .filter_map(|(cell_id, state)| match state {
                MigrationState::Completed { .. } | MigrationState::Cancelled { .. } => {
                    Some(*cell_id)
                }
                _ => None,
            })
            .collect();

        for cell_id in &removable {
            self.migrations.remove(cell_id);
        }

        removable
    }
}

/// Errors that can occur during cell migration operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrationError {
    /// The cell is already being migrated.
    AlreadyMigrating,
    /// The cell is not currently in a migration state.
    NotMigrating,
    /// The requested state transition is not valid from the current state.
    InvalidTransition,
}

impl std::fmt::Display for MigrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MigrationError::AlreadyMigrating => write!(f, "cell is already being migrated"),
            MigrationError::NotMigrating => write!(f, "cell is not in a migration state"),
            MigrationError::InvalidTransition => {
                write!(f, "invalid migration state transition")
            }
        }
    }
}

impl std::error::Error for MigrationError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell() -> CellId {
        CellId([0xCC; 32])
    }

    fn target_federation() -> [u8; 32] {
        [0xDD; 32]
    }

    #[test]
    fn migration_happy_path() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();
        let target = target_federation();

        // Begin migration: freeze the cell
        mgr.begin_migration(cell, target, 100, 50).unwrap();
        assert!(mgr.is_frozen(&cell));
        assert!(!mgr.is_cancelled(&cell));

        // Bundle sent
        mgr.bundle_sent(cell, 105, 30).unwrap();
        assert!(mgr.is_frozen(&cell)); // Still frozen while awaiting receipt

        // Receipt confirmed
        mgr.confirm_receipt(cell, 110).unwrap();
        assert!(!mgr.is_frozen(&cell)); // No longer frozen after completion

        // Verify final state
        match mgr.get(&cell) {
            Some(MigrationState::Completed {
                confirmed_at,
                target: t,
                ..
            }) => {
                assert_eq!(*confirmed_at, 110);
                assert_eq!(*t, target);
            }
            other => panic!("expected Completed, got {:?}", other),
        }
    }

    #[test]
    fn migration_timeout_during_freeze_cancels() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // Freeze with timeout of 50 blocks
        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        assert!(mgr.is_frozen(&cell));

        // At height 140 (40 blocks elapsed): not yet timed out
        let cancelled = mgr.check_timeouts(140);
        assert!(cancelled.is_empty());
        assert!(mgr.is_frozen(&cell));

        // At height 160 (60 blocks elapsed > 50 timeout): should cancel
        let cancelled = mgr.check_timeouts(160);
        assert_eq!(cancelled, vec![cell]);
        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));

        match mgr.get(&cell) {
            Some(MigrationState::Cancelled { reason, .. }) => {
                assert_eq!(*reason, MigrationCancelReason::Timeout);
            }
            other => panic!("expected Cancelled, got {:?}", other),
        }
    }

    #[test]
    fn migration_timeout_during_awaiting_receipt_cancels() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        mgr.bundle_sent(cell, 110, 20).unwrap(); // receipt timeout = 20 blocks

        // At height 125 (15 blocks since send): not timed out
        let cancelled = mgr.check_timeouts(125);
        assert!(cancelled.is_empty());

        // At height 135 (25 blocks since send > 20 timeout): cancel
        let cancelled = mgr.check_timeouts(135);
        assert_eq!(cancelled, vec![cell]);
        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_cannot_start_while_already_migrating() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();

        // Second migration attempt fails
        let err = mgr.begin_migration(cell, [0xEE; 32], 105, 50).unwrap_err();
        assert_eq!(err, MigrationError::AlreadyMigrating);
    }

    #[test]
    fn migration_can_restart_after_cancellation() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // First attempt: times out
        mgr.begin_migration(cell, target_federation(), 100, 10)
            .unwrap();
        mgr.check_timeouts(120);
        assert!(mgr.is_cancelled(&cell));

        // Can start a new migration after cancellation
        mgr.begin_migration(cell, [0xEE; 32], 130, 50).unwrap();
        assert!(mgr.is_frozen(&cell));
        assert!(!mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_explicit_cancel() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        mgr.cancel(cell, MigrationCancelReason::Explicit).unwrap();

        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_invalid_transitions_rejected() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // Can't send bundle before freezing
        assert_eq!(
            mgr.bundle_sent(cell, 100, 20),
            Err(MigrationError::NotMigrating)
        );

        // Can't confirm receipt before sending bundle
        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        assert_eq!(
            mgr.confirm_receipt(cell, 105),
            Err(MigrationError::InvalidTransition)
        );
    }

    #[test]
    fn migration_gc_removes_terminal_states() {
        let mut mgr = CellMigrationManager::new();
        let cell1 = CellId([0x11; 32]);
        let cell2 = CellId([0x22; 32]);
        let cell3 = CellId([0x33; 32]);

        // cell1: completed
        mgr.begin_migration(cell1, target_federation(), 100, 50)
            .unwrap();
        mgr.bundle_sent(cell1, 105, 30).unwrap();
        mgr.confirm_receipt(cell1, 110).unwrap();

        // cell2: cancelled
        mgr.begin_migration(cell2, target_federation(), 100, 10)
            .unwrap();
        mgr.check_timeouts(120);

        // cell3: still frozen (active)
        mgr.begin_migration(cell3, target_federation(), 100, 50)
            .unwrap();

        // GC should remove completed and cancelled, keep active
        let removed = mgr.gc_completed();
        assert_eq!(removed.len(), 2);
        assert!(removed.contains(&cell1));
        assert!(removed.contains(&cell2));
        assert!(mgr.is_frozen(&cell3)); // still tracked
        assert!(mgr.get(&cell1).is_none()); // cleaned up
    }
}
