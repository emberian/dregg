//! State persistence for the bounty board — delegated to `pyana-app-framework`.
//!
//! Uses the framework's [`JsonPersistence`] for atomic write-then-rename state
//! snapshots. This module defines the [`BoardSnapshot`] type and provides the
//! legacy `PersistConfig` / `PersistManager` types as thin wrappers for backward
//! compatibility with existing code (e.g., the in-process server module).
//!
//! # File layout
//!
//! State is persisted as a single JSON file at the configured path. Writes are
//! atomic: data is serialized to a `.tmp` sibling, then renamed into place.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use tracing::{error, info};

use pyana_app_framework::persistence::JsonPersistence;

use crate::Bounty;
use crate::state::WorkerHistory;

/// The serializable snapshot of board state.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BoardSnapshot {
    /// All bounties.
    pub bounties: Vec<Bounty>,
    /// Worker histories: (commitment_hex, history).
    pub worker_histories: Vec<(String, WorkerHistory)>,
    /// Current simulated block height.
    pub current_height: u64,
    /// Escrow mappings: (bounty_id_hex, escrow_id_hex).
    pub escrows: Vec<(String, String)>,
}

/// Persistence configuration (legacy wrapper around a file path).
///
/// New code should use `JsonPersistence` directly from the framework.
#[derive(Clone, Debug)]
pub struct PersistConfig {
    /// Path to the state file.
    pub state_file: PathBuf,
}

impl PersistConfig {
    /// Create a new persist config. The path should point to the state JSON file.
    ///
    /// For backward compatibility with the old `--state-dir` flag, if the path
    /// is a directory, appends `board-state.json`.
    pub fn new(path: PathBuf) -> Self {
        let state_file = if path.extension().is_none() || path.is_dir() {
            path.join("board-state.json")
        } else {
            path
        };
        Self { state_file }
    }

    /// Get the underlying file path.
    pub fn state_file(&self) -> &PathBuf {
        &self.state_file
    }
}

/// Persist manager that wraps the framework's `JsonPersistence`.
///
/// Provides backward-compatible async API for code that hasn't been migrated
/// to use `JsonPersistence` directly.
#[derive(Clone)]
pub struct PersistManager {
    inner: Option<JsonPersistence>,
}

impl PersistManager {
    /// Create a persist manager. If `config` is None, persistence is disabled.
    pub fn new(config: Option<PersistConfig>) -> Self {
        Self {
            inner: config.map(|c| JsonPersistence::new(c.state_file)),
        }
    }

    /// Initialize persistence: create parent directory, check writability.
    pub async fn initialize(&self) -> bool {
        match &self.inner {
            Some(persist) => match persist.initialize() {
                Ok(()) => {
                    info!(path = %persist.path().display(), "persistence initialized");
                    true
                }
                Err(e) => {
                    error!(error = %e, "failed to initialize persistence");
                    false
                }
            },
            None => {
                info!("persistence disabled (no state file configured)");
                false
            }
        }
    }

    /// Load state from disk. Returns None if no state file exists or persistence is disabled.
    pub async fn load(&self) -> Option<BoardSnapshot> {
        let persist = self.inner.as_ref()?;
        match persist.load::<BoardSnapshot>() {
            Ok(Some(snapshot)) => {
                info!(
                    bounties = snapshot.bounties.len(),
                    height = snapshot.current_height,
                    "loaded state from disk"
                );
                Some(snapshot)
            }
            Ok(None) => {
                info!("no existing state file, starting fresh");
                None
            }
            Err(e) => {
                error!(error = %e, "failed to load state file, starting fresh");
                None
            }
        }
    }

    /// Persist the given snapshot to disk (atomic write).
    ///
    /// No-op if persistence is not configured.
    pub async fn save(&self, snapshot: &BoardSnapshot) {
        if let Some(ref persist) = self.inner {
            if let Err(e) = persist.save(snapshot) {
                error!(error = %e, "failed to persist state");
            }
        }
    }

    /// Whether persistence is configured.
    pub fn is_configured(&self) -> bool {
        self.inner.is_some()
    }

    /// Get a reference to the underlying JsonPersistence (if configured).
    pub fn persistence(&self) -> Option<&JsonPersistence> {
        self.inner.as_ref()
    }
}

/// Encode a [u8; 32] as hex for JSON serialization.
pub fn bytes32_hex(bytes: &[u8; 32]) -> String {
    pyana_app_framework::hex::bytes32_to_hex(bytes)
}

/// Decode hex back to [u8; 32].
pub fn hex_bytes32(hex: &str) -> Option<[u8; 32]> {
    pyana_app_framework::hex::hex_to_bytes32(hex).ok()
}
