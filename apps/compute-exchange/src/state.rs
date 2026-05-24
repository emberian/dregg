//! In-memory application state for the compute exchange with optional file persistence.
//!
//! Tracks offerings, orders, settlements, disputes, and the commit-reveal registry.
//! Uses `ContentStore<T>` from the app-framework for concurrent storage.
//!
//! When a `state_dir` is configured, every mutation triggers an async persist to disk.

use std::path::PathBuf;
use std::sync::Arc;

use tokio::sync::{Mutex, RwLock};

use pyana_app_framework::authorizer::{Authorizer, SignedAuthorizer};
use pyana_app_framework::escrow::EscrowManager;
use pyana_app_framework::store::ContentStore;
use pyana_app_framework::{EngineConfig, EscrowRecord, FulfillmentRegistry, PyanaEngine};

use crate::auction::OrderCommitment;
use crate::orderbook::{Offering, Order, OrderId, OrderStatus};
use crate::persistence::{self, PersistedScalarState, StateSnapshot, StoreEntry};
use crate::settlement::{Dispute, DisputeStatus, Settlement, SettlementId, SettlementStatus};

/// Shared application state.
#[derive(Clone)]
pub struct AppState {
    /// Compute offerings indexed by ID.
    offerings: ContentStore<Offering>,
    /// Orders indexed by ID.
    orders: ContentStore<Order>,
    /// Settlements indexed by ID.
    settlements: ContentStore<Settlement>,
    /// Disputes indexed by settlement ID.
    disputes: ContentStore<Dispute>,
    /// Escrow records indexed by escrow ID.
    escrows: ContentStore<EscrowRecord>,
    /// Commit-reveal registry + scalar state behind a single lock.
    inner: Arc<RwLock<ScalarState>>,
    /// The pyana engine for executing real turns.
    /// Uses Mutex instead of RwLock because PyanaEngine contains RefCell (!Sync).
    engine: Arc<Mutex<PyanaEngine>>,
    /// Optional directory for persisting state to disk.
    /// Behind RwLock so it can be set after construction (during state load).
    state_dir: Arc<RwLock<Option<PathBuf>>>,
}

/// Scalar state fields that don't fit in content stores.
struct ScalarState {
    /// Commit-reveal registry for order anti-frontrunning.
    fulfillment_registry: FulfillmentRegistry,
    /// Simulated block height for timeout/deadline checking.
    current_height: u64,
    /// Federation root for qualification proofs.
    federation_root: [u8; 32],
}

impl AppState {
    /// Create a new empty state with the given federation root and optional persistence dir.
    pub fn new(federation_root: [u8; 32], state_dir: Option<PathBuf>) -> Self {
        Self {
            offerings: ContentStore::new(),
            orders: ContentStore::new(),
            settlements: ContentStore::new(),
            disputes: ContentStore::new(),
            escrows: ContentStore::new(),
            inner: Arc::new(RwLock::new(ScalarState {
                fulfillment_registry: FulfillmentRegistry::new(),
                current_height: 0,
                federation_root,
            })),
            engine: Arc::new(Mutex::new(PyanaEngine::new(EngineConfig::new(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_secs() as i64)
                    .unwrap_or(0),
            )))),
            state_dir: Arc::new(RwLock::new(state_dir)),
        }
    }

    /// Backward-compatible constructor (no persistence).
    pub fn with_federation_root(federation_root: [u8; 32]) -> Self {
        Self::new(federation_root, None)
    }

    /// Enable persistence by setting the state directory after construction.
    pub async fn set_state_dir(&self, dir: PathBuf) {
        *self.state_dir.write().await = Some(dir);
    }

    /// Persist state to disk if a state_dir is configured.
    async fn persist(&self) {
        let dir = self.state_dir.read().await.clone();
        if let Some(ref dir) = dir {
            persistence::save_state(self, dir).await;
        }
    }

    /// Create a snapshot of all state for serialization.
    pub async fn snapshot(&self) -> StateSnapshot {
        let scalar = {
            let s = self.inner.read().await;
            PersistedScalarState {
                current_height: s.current_height,
                federation_root: s.federation_root,
            }
        };

        let offerings = self
            .offerings
            .list()
            .await
            .into_iter()
            .map(|(id, value)| StoreEntry { id, value })
            .collect();

        let orders = self
            .orders
            .list()
            .await
            .into_iter()
            .map(|(id, value)| StoreEntry { id, value })
            .collect();

        let settlements = self
            .settlements
            .list()
            .await
            .into_iter()
            .map(|(id, value)| StoreEntry { id, value })
            .collect();

        let disputes = self
            .disputes
            .list()
            .await
            .into_iter()
            .map(|(id, value)| StoreEntry { id, value })
            .collect();

        let escrows = self
            .escrows
            .list()
            .await
            .into_iter()
            .map(|(id, value)| StoreEntry { id, value })
            .collect();

        StateSnapshot {
            scalar,
            offerings,
            orders,
            settlements,
            disputes,
            escrows,
        }
    }

    // =========================================================================
    // Block height
    // =========================================================================

    pub async fn current_height(&self) -> u64 {
        self.inner.read().await.current_height
    }

    pub async fn advance_height(&self, delta: u64) {
        let mut state = self.inner.write().await;
        state.current_height += delta;
        drop(state);
        self.persist().await;
    }

    pub async fn federation_root(&self) -> [u8; 32] {
        self.inner.read().await.federation_root
    }

    pub async fn set_federation_root(&self, root: [u8; 32]) {
        self.inner.write().await.federation_root = root;
        self.persist().await;
    }

    // =========================================================================
    // Offerings
    // =========================================================================

    pub async fn insert_offering(&self, offering: Offering) {
        self.offerings.insert(offering.id, offering).await;
        self.persist().await;
    }

    pub async fn get_offering(&self, id: &[u8; 32]) -> Option<Offering> {
        self.offerings.get(id).await
    }

    pub async fn list_offerings(&self) -> Vec<Offering> {
        self.offerings
            .find(|o| o.available)
            .await
            .into_iter()
            .map(|(_, o)| o)
            .collect()
    }

    // =========================================================================
    // Orders
    // =========================================================================

    pub async fn insert_order(&self, order: Order) {
        self.orders.insert(order.id, order).await;
        self.persist().await;
    }

    pub async fn get_order(&self, id: &OrderId) -> Option<Order> {
        self.orders.get(id).await
    }

    pub async fn update_order_status(&self, id: &OrderId, status: OrderStatus) -> bool {
        let updated = self.orders.update(id, |order| order.status = status).await;
        if updated {
            self.persist().await;
        }
        updated
    }

    pub async fn set_order_settlement(&self, order_id: &OrderId, settlement_id: SettlementId) {
        self.orders
            .update(order_id, |order| order.settlement_id = Some(settlement_id))
            .await;
        self.persist().await;
    }

    // =========================================================================
    // Commit-reveal registry
    // =========================================================================

    pub async fn register_order_commitment(
        &self,
        order_id: [u8; 32],
        secret: &[u8; 32],
        now: u64,
    ) -> Result<OrderCommitment, String> {
        let mut state = self.inner.write().await;
        state
            .fulfillment_registry
            .register_commitment(order_id, secret, now)
            .map(|c| OrderCommitment {
                order_id: c.intent_id,
                commitment_hash: c.commitment_hash,
                committed_at: c.committed_at,
            })
            .map_err(|e| e.to_string())
    }

    pub async fn validate_reveal(
        &self,
        order_id: &[u8; 32],
        secret: &[u8; 32],
        now: u64,
    ) -> Result<(), String> {
        let state = self.inner.read().await;
        state
            .fulfillment_registry
            .validate_reveal(order_id, secret, now)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    pub async fn mark_order_fulfilled(&self, order_id: [u8; 32]) {
        let mut state = self.inner.write().await;
        state.fulfillment_registry.mark_fulfilled(order_id);
    }

    // =========================================================================
    // Settlements
    // =========================================================================

    pub async fn insert_settlement(&self, settlement: Settlement) {
        self.settlements.insert(settlement.id, settlement).await;
        self.persist().await;
    }

    pub async fn get_settlement(&self, id: &SettlementId) -> Option<Settlement> {
        self.settlements.get(id).await
    }

    pub async fn update_settlement_status(
        &self,
        id: &SettlementId,
        status: SettlementStatus,
    ) -> bool {
        let updated = self.settlements.update(id, |s| s.status = status).await;
        if updated {
            self.persist().await;
        }
        updated
    }

    // =========================================================================
    // Escrows
    // =========================================================================

    pub async fn insert_escrow(&self, id: [u8; 32], record: EscrowRecord) {
        self.escrows.insert(id, record).await;
        self.persist().await;
    }

    pub async fn get_escrow(&self, id: &[u8; 32]) -> Option<EscrowRecord> {
        self.escrows.get(id).await
    }

    /// Release an escrow by submitting a turn to the engine via EscrowManager,
    /// then marking it resolved in the local store.
    ///
    /// Only marks the escrow resolved if the engine operation succeeds.
    pub async fn release_escrow(&self, id: &[u8; 32], proof: &[u8]) -> bool {
        // Submit a real ReleaseEscrow turn via the engine.
        let mut engine = self.engine.lock().await;
        let mut mgr = EscrowManager::new(&mut engine, make_escrow_authorizer());
        let result = mgr.release_with_proof(*id, proof);
        drop(engine);

        // Only mark resolved if the engine operation succeeded.
        if result.is_err() {
            return false;
        }

        // Update the local record to reflect resolution.
        let updated = self
            .escrows
            .update(id, |escrow| escrow.resolved = true)
            .await;
        if updated {
            self.persist().await;
        }
        updated
    }

    /// Refund an expired escrow by submitting a turn to the engine via EscrowManager,
    /// then marking it resolved in the local store.
    ///
    /// Only marks the escrow resolved if the engine operation succeeds.
    pub async fn refund_escrow(&self, id: &[u8; 32], current_height: u64) -> bool {
        // Submit a real RefundEscrow turn via the engine.
        let mut engine = self.engine.lock().await;
        let mut mgr = EscrowManager::new(&mut engine, make_escrow_authorizer());
        let result = mgr.refund_expired(*id, current_height);
        drop(engine);

        // Only mark resolved if the engine operation succeeded.
        if result.is_err() {
            return false;
        }

        // Update the local record to reflect resolution.
        let updated = self
            .escrows
            .update(id, |escrow| escrow.resolved = true)
            .await;
        if updated {
            self.persist().await;
        }
        updated
    }

    // =========================================================================
    // Disputes
    // =========================================================================

    pub async fn insert_dispute(&self, dispute: Dispute) {
        self.disputes.insert(dispute.settlement_id, dispute).await;
        self.persist().await;
    }

    pub async fn get_dispute(&self, settlement_id: &SettlementId) -> Option<Dispute> {
        self.disputes.get(settlement_id).await
    }

    pub async fn update_dispute_status(
        &self,
        settlement_id: &SettlementId,
        status: DisputeStatus,
    ) -> bool {
        let updated = self
            .disputes
            .update(settlement_id, |d| d.status = status)
            .await;
        if updated {
            self.persist().await;
        }
        updated
    }

    // =========================================================================
    // Engine access (for proof verification)
    // =========================================================================

    /// Get a lock on the engine (for proof verification).
    pub async fn engine_read(&self) -> tokio::sync::MutexGuard<'_, PyanaEngine> {
        self.engine.lock().await
    }
}

/// Build the default `Authorizer` used by the compute-exchange's escrow turns.
///
/// Reads `PYANA_COMPUTE_ESCROW_KEY` (32-byte hex) from the environment when set;
/// otherwise falls back to a deterministic dev-only key and emits a warning.
/// Production deployments MUST set `PYANA_COMPUTE_ESCROW_KEY`.
fn make_escrow_authorizer() -> Box<dyn Authorizer> {
    let secret = match std::env::var("PYANA_COMPUTE_ESCROW_KEY") {
        Ok(hex) => parse_hex_32(&hex).unwrap_or_else(|| {
            eprintln!(
                "WARNING: PYANA_COMPUTE_ESCROW_KEY is not valid 32-byte hex; using dev key"
            );
            dev_key_bytes()
        }),
        Err(_) => {
            eprintln!(
                "WARNING: PYANA_COMPUTE_ESCROW_KEY not set; using deterministic dev key. \
                 DO NOT use this in production."
            );
            dev_key_bytes()
        }
    };
    Box::new(SignedAuthorizer::from_secret_bytes(secret))
}

fn dev_key_bytes() -> [u8; 32] {
    *blake3::hash(b"pyana-compute-exchange-dev-escrow-key-v1").as_bytes()
}

fn parse_hex_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim().trim_start_matches("0x");
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}
