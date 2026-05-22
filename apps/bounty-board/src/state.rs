//! In-memory board state with persistence hooks.
//!
//! The board stores all bounties, worker history, and escrow cell mappings.
//! Currently backed by in-memory data structures with `tokio::sync::RwLock`
//! for concurrent access from axum handlers.

use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;

use pyana_types::CellId;

use crate::{
    Bounty, BountyFilter, BountyStatus, BountySummary, bounty_id_hex, qualification_label,
    status_label,
};

/// The shared application state for the bounty board.
#[derive(Clone)]
pub struct BoardState {
    inner: Arc<RwLock<BoardStateInner>>,
}

/// Inner mutable state (behind RwLock).
struct BoardStateInner {
    /// All bounties indexed by ID.
    bounties: HashMap<[u8; 32], Bounty>,
    /// Worker commitment -> list of completed bounty IDs.
    worker_history: HashMap<[u8; 32], Vec<[u8; 32]>>,
    /// Bounty ID -> escrow cell holding the reward.
    escrow_cells: HashMap<[u8; 32], CellId>,
    /// Current simulated block height (for deadline checking).
    current_height: u64,
}

impl BoardState {
    /// Create a new empty board state.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(BoardStateInner {
                bounties: HashMap::new(),
                worker_history: HashMap::new(),
                escrow_cells: HashMap::new(),
                current_height: 0,
            })),
        }
    }

    /// Get the current block height.
    pub async fn current_height(&self) -> u64 {
        self.inner.read().await.current_height
    }

    /// Advance the block height (for testing / simulation).
    pub async fn advance_height(&self, delta: u64) {
        let mut state = self.inner.write().await;
        state.current_height += delta;
    }

    /// Set the block height explicitly.
    pub async fn set_height(&self, height: u64) {
        let mut state = self.inner.write().await;
        state.current_height = height;
    }

    /// Insert a new bounty.
    pub async fn insert_bounty(&self, bounty: Bounty) {
        let mut state = self.inner.write().await;
        state.bounties.insert(bounty.id, bounty);
    }

    /// Get a bounty by ID.
    pub async fn get_bounty(&self, id: &[u8; 32]) -> Option<Bounty> {
        let state = self.inner.read().await;
        state.bounties.get(id).cloned()
    }

    /// Update a bounty's status.
    pub async fn update_status(&self, id: &[u8; 32], status: BountyStatus) -> bool {
        let mut state = self.inner.write().await;
        if let Some(bounty) = state.bounties.get_mut(id) {
            bounty.status = status;
            true
        } else {
            false
        }
    }

    /// Record a completed bounty for a worker commitment.
    pub async fn record_completion(&self, worker_commitment: [u8; 32], bounty_id: [u8; 32]) {
        let mut state = self.inner.write().await;
        state
            .worker_history
            .entry(worker_commitment)
            .or_default()
            .push(bounty_id);
    }

    /// Get a worker's completed bounty count.
    pub async fn worker_completed_count(&self, worker_commitment: &[u8; 32]) -> u64 {
        let state = self.inner.read().await;
        state
            .worker_history
            .get(worker_commitment)
            .map(|v| v.len() as u64)
            .unwrap_or(0)
    }

    /// Get a worker's bounty history (IDs of bounties they've completed).
    pub async fn worker_bounty_ids(&self, worker_commitment: &[u8; 32]) -> Vec<[u8; 32]> {
        let state = self.inner.read().await;
        state
            .worker_history
            .get(worker_commitment)
            .cloned()
            .unwrap_or_default()
    }

    /// Store an escrow cell mapping.
    pub async fn set_escrow_cell(&self, bounty_id: [u8; 32], cell_id: CellId) {
        let mut state = self.inner.write().await;
        state.escrow_cells.insert(bounty_id, cell_id);
    }

    /// Get the escrow cell for a bounty.
    pub async fn get_escrow_cell(&self, bounty_id: &[u8; 32]) -> Option<CellId> {
        let state = self.inner.read().await;
        state.escrow_cells.get(bounty_id).copied()
    }

    /// List bounties matching a filter.
    pub async fn list_bounties(&self, filter: &BountyFilter) -> Vec<BountySummary> {
        let state = self.inner.read().await;
        state
            .bounties
            .values()
            .filter(|b| {
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
            .map(|b| BountySummary {
                id: bounty_id_hex(&b.id),
                title: b.title.clone(),
                reward_amount: b.reward_amount,
                reward_asset: b.reward_asset,
                deadline_height: b.deadline_height,
                status: status_label(&b.status).to_string(),
                tags: b.tags.clone(),
                qualification: qualification_label(&b.qualification),
            })
            .collect()
    }

    /// Expire all bounties past their deadline.
    pub async fn expire_stale_bounties(&self) -> usize {
        let mut state = self.inner.write().await;
        let height = state.current_height;
        let mut expired_count = 0;
        for bounty in state.bounties.values_mut() {
            if bounty.deadline_height <= height {
                if matches!(
                    bounty.status,
                    BountyStatus::Open | BountyStatus::Claimed { .. }
                ) {
                    bounty.status = BountyStatus::Expired;
                    expired_count += 1;
                }
            }
        }
        expired_count
    }

    /// Get bounties that a worker has claimed or completed (by commitment).
    pub async fn worker_active_bounties(&self, worker_commitment: &[u8; 32]) -> Vec<BountySummary> {
        let state = self.inner.read().await;
        state
            .bounties
            .values()
            .filter(|b| match &b.status {
                BountyStatus::Claimed {
                    worker_commitment: wc,
                    ..
                } => wc == worker_commitment,
                BountyStatus::Submitted {
                    worker_commitment: wc,
                    ..
                } => wc == worker_commitment,
                _ => false,
            })
            .map(|b| BountySummary {
                id: bounty_id_hex(&b.id),
                title: b.title.clone(),
                reward_amount: b.reward_amount,
                reward_asset: b.reward_asset,
                deadline_height: b.deadline_height,
                status: status_label(&b.status).to_string(),
                tags: b.tags.clone(),
                qualification: qualification_label(&b.qualification),
            })
            .collect()
    }
}
