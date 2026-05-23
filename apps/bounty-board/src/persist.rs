//! File-based persistence for the bounty board state.
//!
//! Serializes the full board state to a JSON file on every mutation, and reloads
//! from file on startup. The file path is configured via `--state-dir`.
//!
//! # File layout
//!
//! ```text
//! <state-dir>/
//!   board-state.json    — serialized bounty board (bounties, worker history, height)
//! ```
//!
//! # Write strategy
//!
//! Writes are atomic: data is first written to a `.tmp` file, then renamed into place.
//! This prevents corruption from partial writes on crash.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::{error, info, warn};

use crate::Bounty;
use crate::state::WorkerHistory;

/// The filename used for the serialized board state.
const STATE_FILENAME: &str = "board-state.json";

/// Persistence configuration.
#[derive(Clone, Debug)]
pub struct PersistConfig {
    /// Directory where state files are stored.
    pub state_dir: PathBuf,
}

impl PersistConfig {
    /// Create a new persist config for the given directory.
    pub fn new(state_dir: PathBuf) -> Self {
        Self { state_dir }
    }

    /// Full path to the state file.
    pub fn state_file(&self) -> PathBuf {
        self.state_dir.join(STATE_FILENAME)
    }

    /// Full path to the temporary state file (used for atomic writes).
    fn tmp_file(&self) -> PathBuf {
        self.state_dir.join(format!("{STATE_FILENAME}.tmp"))
    }
}

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

/// Persist manager that handles saving/loading state.
#[derive(Clone)]
pub struct PersistManager {
    config: Option<PersistConfig>,
    /// Track whether persistence is available (dir exists, writable).
    available: std::sync::Arc<RwLock<bool>>,
}

impl PersistManager {
    /// Create a persist manager. If `config` is None, persistence is disabled (in-memory only).
    pub fn new(config: Option<PersistConfig>) -> Self {
        Self {
            config,
            available: std::sync::Arc::new(RwLock::new(false)),
        }
    }

    /// Initialize persistence: create state directory if needed, check writability.
    pub async fn initialize(&self) -> bool {
        let config = match &self.config {
            Some(c) => c,
            None => {
                info!("persistence disabled (no --state-dir)");
                return false;
            }
        };

        // Create directory if it doesn't exist.
        if let Err(e) = std::fs::create_dir_all(&config.state_dir) {
            error!(
                dir = %config.state_dir.display(),
                error = %e,
                "failed to create state directory, persistence disabled"
            );
            return false;
        }

        // Check writability by touching the tmp file.
        let tmp = config.tmp_file();
        match std::fs::write(&tmp, b"pyana-bounty-board-init") {
            Ok(_) => {
                let _ = std::fs::remove_file(&tmp);
            }
            Err(e) => {
                error!(
                    dir = %config.state_dir.display(),
                    error = %e,
                    "state directory not writable, persistence disabled"
                );
                return false;
            }
        }

        *self.available.write().await = true;
        info!(dir = %config.state_dir.display(), "persistence initialized");
        true
    }

    /// Load state from disk. Returns None if no state file exists or persistence is disabled.
    pub async fn load(&self) -> Option<BoardSnapshot> {
        let config = self.config.as_ref()?;
        let path = config.state_file();

        if !path.exists() {
            info!(path = %path.display(), "no existing state file, starting fresh");
            return None;
        }

        match std::fs::read_to_string(&path) {
            Ok(contents) => match serde_json::from_str::<BoardSnapshot>(&contents) {
                Ok(snapshot) => {
                    info!(
                        path = %path.display(),
                        bounties = snapshot.bounties.len(),
                        height = snapshot.current_height,
                        "loaded state from disk"
                    );
                    Some(snapshot)
                }
                Err(e) => {
                    error!(
                        path = %path.display(),
                        error = %e,
                        "failed to parse state file, starting fresh"
                    );
                    None
                }
            },
            Err(e) => {
                error!(
                    path = %path.display(),
                    error = %e,
                    "failed to read state file, starting fresh"
                );
                None
            }
        }
    }

    /// Persist the given snapshot to disk (atomic write).
    ///
    /// This is a no-op if persistence is not configured or not available.
    pub async fn save(&self, snapshot: &BoardSnapshot) {
        if !*self.available.read().await {
            return;
        }

        let config = match &self.config {
            Some(c) => c,
            None => return,
        };

        let json = match serde_json::to_string_pretty(snapshot) {
            Ok(j) => j,
            Err(e) => {
                error!(error = %e, "failed to serialize state");
                return;
            }
        };

        let tmp = config.tmp_file();
        let target = config.state_file();

        // Write to temp file first (atomic write pattern).
        if let Err(e) = std::fs::write(&tmp, json.as_bytes()) {
            error!(
                path = %tmp.display(),
                error = %e,
                "failed to write temporary state file"
            );
            return;
        }

        // Rename into place (atomic on POSIX).
        if let Err(e) = std::fs::rename(&tmp, &target) {
            error!(
                from = %tmp.display(),
                to = %target.display(),
                error = %e,
                "failed to rename state file into place"
            );
            return;
        }
    }

    /// Whether persistence is enabled and available.
    pub async fn is_available(&self) -> bool {
        *self.available.read().await
    }

    /// Whether persistence is configured (even if not yet initialized).
    pub fn is_configured(&self) -> bool {
        self.config.is_some()
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
