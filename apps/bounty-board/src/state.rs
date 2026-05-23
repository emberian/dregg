//! In-memory board state with snapshot support.
//!
//! The board stores all bounties, worker history, and escrow cell mappings.
//! Uses `ContentStore` from the app framework for concurrent access from axum handlers.
//!
//! Persistence is handled externally: callers use [`BoardState::snapshot`] to take a
//! serializable snapshot and [`BoardState::restore_from_snapshot`] to reload. The
//! framework's `JsonPersistence` handles the actual I/O.

use std::sync::Arc;

use tokio::sync::RwLock;

use pyana_app_framework::CellId;
use pyana_app_framework::store::ContentStore;

use crate::persist::{BoardSnapshot, bytes32_hex, hex_bytes32};
use crate::{
    Bounty, BountyFilter, BountyStatus, BountySummary, bounty_id_hex, qualification_label,
    status_label,
};

/// Wrapper for worker history (needed for ContentStore's Serialize/Deserialize bounds).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WorkerHistory {
    pub completed_bounty_ids: Vec<[u8; 32]>,
}

/// The shared application state for the bounty board.
#[derive(Clone)]
pub struct BoardState {
    /// All bounties indexed by ID.
    bounties: ContentStore<Bounty>,
    /// Worker commitment -> list of completed bounty IDs.
    worker_history: ContentStore<WorkerHistory>,
    /// Bounty ID -> escrow cell holding the reward.
    escrow_cells: ContentStore<CellId>,
    /// Current simulated block height (for deadline checking).
    current_height: Arc<RwLock<u64>>,
}

impl BoardState {
    /// Create a new empty board state.
    pub fn new() -> Self {
        Self {
            bounties: ContentStore::new(),
            worker_history: ContentStore::new(),
            escrow_cells: ContentStore::new(),
            current_height: Arc::new(RwLock::new(0)),
        }
    }

    /// Restore state from a snapshot (loaded from disk).
    pub async fn restore_from_snapshot(&self, snapshot: BoardSnapshot) {
        // Restore bounties.
        for bounty in snapshot.bounties {
            self.bounties.insert(bounty.id, bounty).await;
        }

        // Restore worker histories.
        for (commitment_hex, history) in snapshot.worker_histories {
            if let Some(commitment) = hex_bytes32(&commitment_hex) {
                self.worker_history.insert(commitment, history).await;
            }
        }

        // Restore escrow mappings.
        for (bounty_id_hex, escrow_id_hex) in snapshot.escrows {
            if let (Some(bounty_id), Some(escrow_bytes)) =
                (hex_bytes32(&bounty_id_hex), hex_bytes32(&escrow_id_hex))
            {
                self.escrow_cells
                    .insert(bounty_id, CellId::from_bytes(escrow_bytes))
                    .await;
            }
        }

        // Restore height.
        *self.current_height.write().await = snapshot.current_height;
    }

    /// Take a snapshot of the current state (for persistence).
    pub async fn snapshot(&self) -> BoardSnapshot {
        let bounties: Vec<Bounty> = self
            .bounties
            .list()
            .await
            .into_iter()
            .map(|(_, b)| b)
            .collect();

        let worker_histories: Vec<(String, WorkerHistory)> = self
            .worker_history
            .list()
            .await
            .into_iter()
            .map(|(k, v)| (bytes32_hex(&k), v))
            .collect();

        let escrows: Vec<(String, String)> = self
            .escrow_cells
            .list()
            .await
            .into_iter()
            .map(|(k, v)| (bytes32_hex(&k), bytes32_hex(v.as_bytes())))
            .collect();

        let current_height = *self.current_height.read().await;

        BoardSnapshot {
            bounties,
            worker_histories,
            current_height,
            escrows,
        }
    }

    /// Get the current block height.
    pub async fn current_height(&self) -> u64 {
        *self.current_height.read().await
    }

    /// Advance the block height (for testing / simulation).
    pub async fn advance_height(&self, delta: u64) {
        let mut height = self.current_height.write().await;
        *height += delta;
    }

    /// Set the block height explicitly.
    pub async fn set_height(&self, height: u64) {
        let mut h = self.current_height.write().await;
        *h = height;
    }

    /// Insert a new bounty.
    pub async fn insert_bounty(&self, bounty: Bounty) {
        self.bounties.insert(bounty.id, bounty).await;
    }

    /// Get a bounty by ID.
    pub async fn get_bounty(&self, id: &[u8; 32]) -> Option<Bounty> {
        self.bounties.get(id).await
    }

    /// Update a bounty's status.
    pub async fn update_status(&self, id: &[u8; 32], status: BountyStatus) -> bool {
        self.bounties
            .update(id, |bounty| {
                bounty.status = status;
            })
            .await
    }

    /// Record a completed bounty for a worker commitment.
    pub async fn record_completion(&self, worker_commitment: [u8; 32], bounty_id: [u8; 32]) {
        // Try to update existing history entry.
        let updated = self
            .worker_history
            .update(&worker_commitment, |history| {
                history.completed_bounty_ids.push(bounty_id);
            })
            .await;

        // If no existing entry, create one.
        if !updated {
            self.worker_history
                .insert(
                    worker_commitment,
                    WorkerHistory {
                        completed_bounty_ids: vec![bounty_id],
                    },
                )
                .await;
        }
    }

    /// Get a worker's completed bounty count.
    pub async fn worker_completed_count(&self, worker_commitment: &[u8; 32]) -> u64 {
        self.worker_history
            .get(worker_commitment)
            .await
            .map(|h| h.completed_bounty_ids.len() as u64)
            .unwrap_or(0)
    }

    /// Get a worker's bounty history (IDs of bounties they've completed).
    pub async fn worker_bounty_ids(&self, worker_commitment: &[u8; 32]) -> Vec<[u8; 32]> {
        self.worker_history
            .get(worker_commitment)
            .await
            .map(|h| h.completed_bounty_ids)
            .unwrap_or_default()
    }

    /// Store an escrow cell mapping.
    pub async fn set_escrow_cell(&self, bounty_id: [u8; 32], cell_id: CellId) {
        self.escrow_cells.insert(bounty_id, cell_id).await;
    }

    /// Get the escrow cell for a bounty.
    pub async fn get_escrow_cell(&self, bounty_id: &[u8; 32]) -> Option<CellId> {
        self.escrow_cells.get(bounty_id).await
    }

    /// List bounties matching a filter.
    pub async fn list_bounties(&self, filter: &BountyFilter) -> Vec<BountySummary> {
        self.bounties
            .find(|b| {
                // Filter by tag.
                if let Some(ref tag) = filter.tag {
                    if !b.tags.iter().any(|t| t == tag) {
                        return false;
                    }
                }
                // Filter by min reward.
                if let Some(min) = filter.min_reward {
                    if b.reward_amount < min {
                        return false;
                    }
                }
                // Filter by max reward.
                if let Some(max) = filter.max_reward {
                    if b.reward_amount > max {
                        return false;
                    }
                }
                // Filter by status.
                if let Some(ref status_filter) = filter.status {
                    if status_label(&b.status) != status_filter.as_str() {
                        return false;
                    }
                }
                true
            })
            .await
            .into_iter()
            .map(|(_, b)| BountySummary {
                id: bounty_id_hex(&b.id),
                title: b.title,
                reward_amount: b.reward_amount,
                reward_asset: b.reward_asset,
                deadline_height: b.deadline_height,
                status: status_label(&b.status).to_string(),
                tags: b.tags,
                qualification: qualification_label(&b.qualification),
            })
            .collect()
    }

    /// Expire all bounties past their deadline.
    pub async fn expire_stale_bounties(&self) -> usize {
        let height = self.current_height().await;
        let candidates = self
            .bounties
            .find(|b| {
                b.deadline_height <= height
                    && matches!(b.status, BountyStatus::Open | BountyStatus::Claimed { .. })
            })
            .await;

        let mut expired_count = 0;
        for (id, _) in &candidates {
            let updated = self
                .bounties
                .update(id, |b| {
                    b.status = BountyStatus::Expired;
                })
                .await;
            if updated {
                expired_count += 1;
            }
        }
        expired_count
    }

    /// Get bounties that a worker has claimed or completed (by commitment).
    pub async fn worker_active_bounties(&self, worker_commitment: &[u8; 32]) -> Vec<BountySummary> {
        let wc = *worker_commitment;
        self.bounties
            .find(move |b| match &b.status {
                BountyStatus::Claimed {
                    worker_commitment: wc_inner,
                    ..
                } => *wc_inner == wc,
                BountyStatus::Submitted {
                    worker_commitment: wc_inner,
                    ..
                } => *wc_inner == wc,
                _ => false,
            })
            .await
            .into_iter()
            .map(|(_, b)| BountySummary {
                id: bounty_id_hex(&b.id),
                title: b.title,
                reward_amount: b.reward_amount,
                reward_asset: b.reward_asset,
                deadline_height: b.deadline_height,
                status: status_label(&b.status).to_string(),
                tags: b.tags,
                qualification: qualification_label(&b.qualification),
            })
            .collect()
    }
}
