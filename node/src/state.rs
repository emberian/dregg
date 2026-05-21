//! Node state management.
//!
//! Holds the AgentWallet, Ledger, and PersistentStore handles behind
//! Arc<RwLock<>> for concurrent access from HTTP handlers and the
//! federation sync background task.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use tokio::sync::{RwLock, broadcast};

use pyana_cell::Ledger;
use pyana_sdk::AgentWallet;
use pyana_store::PersistentStore;

use crate::federation_sync::GossipHandle;

// =============================================================================
// Events (broadcast to WebSocket clients)
// =============================================================================

/// Events emitted when node state changes, broadcast to WebSocket subscribers.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum NodeEvent {
    /// A new attested root was received from the federation.
    Root {
        height: u64,
        merkle_root: String,
        timestamp: i64,
    },
    /// A token was revoked.
    Revocation { token_id: String },
    /// A new receipt was appended to the local chain.
    Receipt { hash: String },
    /// An intent was received (from WS or HTTP) and added to the pool.
    Intent { intent: serde_json::Value },
}

/// Shared node state accessible from all async tasks.
#[derive(Clone)]
pub struct NodeState {
    inner: Arc<RwLock<NodeStateInner>>,
    /// Broadcast channel for real-time events (WebSocket push).
    events_tx: broadcast::Sender<NodeEvent>,
    /// Optional gossip handle (set after federation sync starts).
    gossip: Arc<RwLock<Option<GossipHandle>>>,
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
    /// BLAKE3 hash of the wallet passphrase, set on first `set-passphrase` call.
    /// When `Some`, unlock attempts must provide a passphrase whose BLAKE3 hash
    /// matches this value. When `None`, the first unlock sets the passphrase.
    pub passphrase_hash: Option<[u8; 32]>,
    /// Local intent pool: id -> intent JSON.
    pub intent_pool: HashMap<String, serde_json::Value>,
    /// Pending conditional turns awaiting proof resolution.
    /// Garbage-collected on access when timeout_height is exceeded.
    pub pending_conditionals: Vec<pyana_turn::ConditionalTurn>,
    /// Set of proof hashes that have already been used (nullifiers).
    /// Prevents the same proof from satisfying multiple conditional turns.
    pub used_proof_hashes: HashSet<[u8; 32]>,
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
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        let wallet = AgentWallet::new();
        let ledger = Ledger::new();
        let (events_tx, _) = broadcast::channel(256);

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash: None,
                intent_pool: HashMap::new(),
                pending_conditionals: Vec::new(),
                used_proof_hashes: HashSet::new(),
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
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
        let store =
            PersistentStore::open(&db_path).map_err(|e| format!("failed to open store: {e}"))?;

        let wallet = AgentWallet::from_key_bytes(key_bytes);
        let ledger = Ledger::new();
        let (events_tx, _) = broadcast::channel(256);

        Ok(Self {
            inner: Arc::new(RwLock::new(NodeStateInner {
                wallet,
                ledger,
                store,
                peers,
                unlocked: false,
                passphrase_hash: None,
                intent_pool: HashMap::new(),
                pending_conditionals: Vec::new(),
                used_proof_hashes: HashSet::new(),
            })),
            events_tx,
            gossip: Arc::new(RwLock::new(None)),
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

    /// Subscribe to node events (returns a broadcast receiver).
    pub fn subscribe_events(&self) -> broadcast::Receiver<NodeEvent> {
        self.events_tx.subscribe()
    }

    /// Emit a node event to all connected WebSocket clients.
    pub fn emit(&self, event: NodeEvent) {
        // Ignore send errors (no active receivers is fine).
        let _ = self.events_tx.send(event);
    }

    /// Set the gossip handle (called by federation_sync once initialized).
    pub async fn set_gossip(&self, handle: GossipHandle) {
        let mut g = self.gossip.write().await;
        *g = Some(handle);
    }

    /// Get a clone of the gossip handle, if available.
    pub async fn gossip(&self) -> Option<GossipHandle> {
        let g = self.gossip.read().await;
        g.clone()
    }
}

/// Minimal hex encoding (no extra dep needed).
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
