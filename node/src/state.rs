//! Node state management.
//!
//! Holds the AgentWallet, Ledger, and PersistentStore handles behind
//! Arc<RwLock<>> for concurrent access from HTTP handlers and the
//! federation sync background task.

use std::path::Path;
use std::sync::Arc;

use tokio::sync::RwLock;

use pyana_cell::Ledger;
use pyana_sdk::AgentWallet;
use pyana_store::PersistentStore;

/// Shared node state accessible from all async tasks.
#[derive(Clone)]
pub struct NodeState {
    inner: Arc<RwLock<NodeStateInner>>,
}

/// The inner mutable state of the node.
pub struct NodeStateInner {
    /// The agent wallet (identity, tokens, receipts).
    pub wallet: AgentWallet,
    /// The cell ledger (local cell state).
    pub ledger: Ledger,
    /// Persistent storage backend.
    pub store: PersistentStore,
    /// Federation peer addresses.
    pub peers: Vec<String>,
    /// Whether the wallet is unlocked for signing operations.
    pub unlocked: bool,
}

/// Summary of the node's sync state for the status endpoint.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SyncStatus {
    pub peer_count: usize,
    pub latest_height: u64,
    pub revocation_count: u64,
    pub note_count: u64,
}

/// Summary of the wallet state for the wallet endpoint.
#[derive(Clone, Debug, serde::Serialize)]
pub struct WalletStatus {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

impl NodeState {
    /// Create a new NodeState from a data directory path and peer list.
    pub fn new(data_dir: &Path, peers: Vec<String>) -> Result<Self, String> {
        let db_path = data_dir.join("pyana.redb");
        let store = PersistentStore::open(&db_path)
            .map_err(|e| format!("failed to open store: {e}"))?;

        let wallet = AgentWallet::new();
        let ledger = Ledger::new();

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
            })),
        })
    }

    /// Create a NodeState with a pre-existing wallet (restored from key material).
    #[allow(dead_code)]
    pub fn with_wallet(
        data_dir: &Path,
        peers: Vec<String>,
        key_bytes: [u8; 32],
    ) -> Result<Self, String> {
        let db_path = data_dir.join("pyana.redb");
        let store = PersistentStore::open(&db_path)
            .map_err(|e| format!("failed to open store: {e}"))?;

        let wallet = AgentWallet::from_key_bytes(key_bytes);
        let ledger = Ledger::new();

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
            })),
        })
    }

    /// Acquire a read lock on the inner state.
    pub async fn read(&self) -> tokio::sync::RwLockReadGuard<'_, NodeStateInner> {
        self.inner.read().await
    }

    /// Acquire a write lock on the inner state.
    pub async fn write(&self) -> tokio::sync::RwLockWriteGuard<'_, NodeStateInner> {
        self.inner.write().await
    }

    /// Get the current sync status.
    pub async fn sync_status(&self) -> SyncStatus {
        let state = self.inner.read().await;
        let latest_height = state
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        let revocation_count = state.store.revocation_count().unwrap_or(0);
        let note_count = state.store.note_count().unwrap_or(0);

        SyncStatus {
            peer_count: state.peers.len(),
            latest_height,
            revocation_count,
            note_count,
        }
    }

    /// Get the current wallet status.
    pub async fn wallet_status(&self) -> WalletStatus {
        let state = self.inner.read().await;
        let pk = state.wallet.public_key();
        WalletStatus {
            unlocked: state.unlocked,
            public_key: hex::encode(&pk.0),
            token_count: state.wallet.tokens().len(),
            receipt_chain_length: state.wallet.receipt_chain_length(),
        }
    }
}

/// Minimal hex encoding (no extra dep needed).
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
