//! File-based state persistence for the compute exchange.
//!
//! Serializes all mutable state to JSON files in a state directory on every mutation.
//! On startup, loads the last persisted state from disk. This provides crash recovery
//! without requiring a full database.
//!
//! # File layout
//!
//! ```text
//! <state-dir>/
//!   offerings.json       — all compute offerings
//!   orders.json          — all orders
//!   settlements.json     — all settlements
//!   disputes.json        — all disputes
//!   escrows.json         — all escrow records
//!   scalar_state.json    — block height, federation root
//! ```

use std::path::Path;

use serde::{Deserialize, Serialize};
use tracing::error;

use pyana_app_framework::EscrowRecord;

use crate::orderbook::{Offering, Order};
use crate::settlement::{Dispute, Settlement};
use crate::state::AppState;

// =============================================================================
// Persisted state snapshot
// =============================================================================

/// Scalar state that doesn't fit in content stores.
#[derive(Debug, Serialize, Deserialize)]
pub struct PersistedScalarState {
    pub current_height: u64,
    pub federation_root: [u8; 32],
}

/// A single entry in a persisted store (key + value).
#[derive(Debug, Serialize, Deserialize)]
pub struct StoreEntry<T> {
    pub id: [u8; 32],
    pub value: T,
}

/// Complete state snapshot for persistence.
#[derive(Debug, Serialize, Deserialize)]
pub struct StateSnapshot {
    pub scalar: PersistedScalarState,
    pub offerings: Vec<StoreEntry<Offering>>,
    pub orders: Vec<StoreEntry<Order>>,
    pub settlements: Vec<StoreEntry<Settlement>>,
    pub disputes: Vec<StoreEntry<Dispute>>,
    pub escrows: Vec<StoreEntry<EscrowRecord>>,
}

// =============================================================================
// Load
// =============================================================================

/// Load persisted state from a directory.
///
/// Returns an `AppState` initialized from the snapshot, or an error if
/// no valid snapshot exists.
///
/// The state is loaded without persistence enabled initially (to avoid a
/// write-back loop during restoration), then the state_dir is set afterwards.
pub fn load_state(dir: &Path, federation_root: [u8; 32]) -> Result<AppState, String> {
    let snapshot_path = dir.join("state.json");
    if !snapshot_path.exists() {
        return Err("no state.json found".to_string());
    }

    let data = std::fs::read_to_string(&snapshot_path).map_err(|e| format!("read error: {e}"))?;
    let snapshot: StateSnapshot =
        serde_json::from_str(&data).map_err(|e| format!("parse error: {e}"))?;

    // Build state WITHOUT persistence first (avoids write-back during restore).
    let state = AppState::new(federation_root, None);

    // Restore state from snapshot. This uses block_on since load_state is called
    // at startup before the async context is fully set up for handlers.
    tokio::runtime::Handle::current().block_on(async {
        // Set height from persisted state.
        let delta = snapshot.scalar.current_height;
        if delta > 0 {
            state.advance_height(delta).await;
        }

        // Restore offerings.
        for entry in snapshot.offerings {
            state.insert_offering(entry.value).await;
        }

        // Restore orders.
        for entry in snapshot.orders {
            state.insert_order(entry.value).await;
        }

        // Restore settlements.
        for entry in snapshot.settlements {
            state.insert_settlement(entry.value).await;
        }

        // Restore disputes.
        for entry in snapshot.disputes {
            state.insert_dispute(entry.value).await;
        }

        // Restore escrows.
        for entry in snapshot.escrows {
            state.insert_escrow(entry.id, entry.value).await;
        }

        // NOW enable persistence for future mutations.
        state.set_state_dir(dir.to_path_buf()).await;
    });

    Ok(state)
}

// =============================================================================
// Save
// =============================================================================

/// Persist the current state to disk.
///
/// Writes atomically: writes to a temp file, then renames. This prevents
/// corrupted state files from partial writes during a crash.
pub async fn save_state(state: &AppState, dir: &Path) {
    let snapshot = state.snapshot().await;

    let snapshot_path = dir.join("state.json");
    let tmp_path = dir.join("state.json.tmp");

    let data = match serde_json::to_string_pretty(&snapshot) {
        Ok(d) => d,
        Err(e) => {
            error!("failed to serialize state: {e}");
            return;
        }
    };

    if let Err(e) = std::fs::write(&tmp_path, &data) {
        error!("failed to write tmp state file: {e}");
        return;
    }

    if let Err(e) = std::fs::rename(&tmp_path, &snapshot_path) {
        error!("failed to rename state file: {e}");
        // Try to clean up the tmp file.
        let _ = std::fs::remove_file(&tmp_path);
    }
}
