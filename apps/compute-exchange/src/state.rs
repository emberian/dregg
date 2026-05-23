//! In-memory application state for the compute exchange.
//!
//! Tracks offerings, orders, settlements, disputes, and the commit-reveal registry.
//! Uses `ContentStore<T>` from the app-framework for concurrent storage.

use std::sync::Arc;

use tokio::sync::RwLock;

use pyana_app_framework::escrow::EscrowManager;
use pyana_app_framework::store::ContentStore;
use pyana_app_framework::{EngineConfig, EscrowRecord, FulfillmentRegistry, PyanaEngine};

use crate::auction::OrderCommitment;
use crate::orderbook::{Offering, Order, OrderId, OrderStatus};
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
    engine: Arc<RwLock<PyanaEngine>>,
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
    /// Create a new empty state with the given federation root.
    pub fn with_federation_root(federation_root: [u8; 32]) -> Self {
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
            engine: Arc::new(RwLock::new(PyanaEngine::new(EngineConfig::default()))),
        }
    }

    /// Create a new empty state (dev mode: zeroed federation root).
    pub fn new() -> Self {
        Self::with_federation_root([0u8; 32])
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
    }

    pub async fn federation_root(&self) -> [u8; 32] {
        self.inner.read().await.federation_root
    }

    pub async fn set_federation_root(&self, root: [u8; 32]) {
        self.inner.write().await.federation_root = root;
    }

    // =========================================================================
    // Offerings
    // =========================================================================

    pub async fn insert_offering(&self, offering: Offering) {
        self.offerings.insert(offering.id, offering).await;
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
    }

    pub async fn get_order(&self, id: &OrderId) -> Option<Order> {
        self.orders.get(id).await
    }

    pub async fn update_order_status(&self, id: &OrderId, status: OrderStatus) -> bool {
        self.orders.update(id, |order| order.status = status).await
    }

    pub async fn set_order_settlement(&self, order_id: &OrderId, settlement_id: SettlementId) {
        self.orders
            .update(order_id, |order| order.settlement_id = Some(settlement_id))
            .await;
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
    }

    pub async fn get_settlement(&self, id: &SettlementId) -> Option<Settlement> {
        self.settlements.get(id).await
    }

    pub async fn update_settlement_status(
        &self,
        id: &SettlementId,
        status: SettlementStatus,
    ) -> bool {
        self.settlements.update(id, |s| s.status = status).await
    }

    // =========================================================================
    // Escrows
    // =========================================================================

    pub async fn insert_escrow(&self, id: [u8; 32], record: EscrowRecord) {
        self.escrows.insert(id, record).await;
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
        let mut engine = self.engine.write().await;
        let mut mgr = EscrowManager::new(&mut engine);
        let result = mgr.release_with_proof(*id, proof);
        drop(engine);

        // Only mark resolved if the engine operation succeeded.
        if result.is_err() {
            return false;
        }

        // Update the local record to reflect resolution.
        self.escrows
            .update(id, |escrow| escrow.resolved = true)
            .await
    }

    /// Refund an expired escrow by submitting a turn to the engine via EscrowManager,
    /// then marking it resolved in the local store.
    ///
    /// Only marks the escrow resolved if the engine operation succeeds.
    pub async fn refund_escrow(&self, id: &[u8; 32], current_height: u64) -> bool {
        // Submit a real RefundEscrow turn via the engine.
        let mut engine = self.engine.write().await;
        let mut mgr = EscrowManager::new(&mut engine);
        let result = mgr.refund_expired(*id, current_height);
        drop(engine);

        // Only mark resolved if the engine operation succeeded.
        if result.is_err() {
            return false;
        }

        // Update the local record to reflect resolution.
        self.escrows
            .update(id, |escrow| escrow.resolved = true)
            .await
    }

    // =========================================================================
    // Disputes
    // =========================================================================

    pub async fn insert_dispute(&self, dispute: Dispute) {
        self.disputes.insert(dispute.settlement_id, dispute).await;
    }

    pub async fn get_dispute(&self, settlement_id: &SettlementId) -> Option<Dispute> {
        self.disputes.get(settlement_id).await
    }

    pub async fn update_dispute_status(
        &self,
        settlement_id: &SettlementId,
        status: DisputeStatus,
    ) -> bool {
        self.disputes
            .update(settlement_id, |d| d.status = status)
            .await
    }

    // =========================================================================
    // Engine access (for proof verification)
    // =========================================================================

    /// Get a read lock on the engine (for proof verification).
    pub async fn engine_read(&self) -> tokio::sync::RwLockReadGuard<'_, PyanaEngine> {
        self.engine.read().await
    }
}
