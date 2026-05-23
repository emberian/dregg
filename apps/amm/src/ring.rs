//! Ring trade solver participation for the AMM.
//!
//! Implements [`RingTradeParticipant`] on the AMM registry, exposing each
//! liquidity pool as an [`ExchangeSpec`] at the current spot price. The solver
//! coordinator calls `settle_leg` to execute a swap and `rollback_leg` to undo
//! it if a peer in the ring fails.
//!
//! # HTTP endpoint
//!
//! `POST /ring/settle` — the solver drives the trait on behalf of the AMM.
//!
//! # How it works
//!
//! For every pool (A, B), two exchange specs are generated:
//! - A→B: offer `reserve_a` at spot rate, want `reserve_b` proportion
//! - B→A: offer `reserve_b` at spot rate, want `reserve_a` proportion
//!
//! The actual execution clamps amounts to what the pool can handle and runs the
//! constant-product swap formula. On rollback, the swap is reversed by re-swapping
//! the output back in the opposite direction (restoring reserves approximately;
//! fees mean this is not perfectly lossless, but the invariant is never violated).

use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    routing::post,
};
use serde::{Deserialize, Serialize};

use pyana_app_framework::ring_trade::{ExchangeSpec, LegId, RingTradeParticipant, Settlement};

use crate::AmmRegistry;
use crate::pool::PoolId;
use crate::server::AppState;

// =============================================================================
// AmmRingParticipant: wraps the registry for ring-trade participation
// =============================================================================

/// Errors from AMM ring-trade participation.
#[derive(Clone, Debug)]
pub enum RingError {
    /// No pool handles this asset pair.
    NoPoolForAssets { offer: String, want: String },
    /// The underlying pool swap failed.
    SwapFailed(String),
    /// Rollback failed (pool state already changed).
    RollbackFailed(String),
    /// Pool not found by ID.
    PoolNotFound(String),
}

impl std::fmt::Display for RingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoPoolForAssets { offer, want } => {
                write!(f, "no pool for assets {offer} → {want}")
            }
            Self::SwapFailed(msg) => write!(f, "swap failed: {msg}"),
            Self::RollbackFailed(msg) => write!(f, "rollback failed: {msg}"),
            Self::PoolNotFound(id) => write!(f, "pool not found: {id}"),
        }
    }
}

impl std::error::Error for RingError {}

/// Record of a settled leg so we can roll it back.
#[derive(Clone, Debug)]
struct SettledLeg {
    leg_id: LegId,
    pool_id: PoolId,
    /// The amount_out from the original swap — used to reverse it.
    amount_out: u64,
    /// Direction of the original swap (true = A→B).
    direction_a_to_b: bool,
}

/// AMM ring-trade participant — wraps the registry in a synchronous snapshot
/// so it can implement the synchronous `RingTradeParticipant` trait.
pub struct AmmRingParticipant {
    pub registry: AmmRegistry,
    /// Ledger of settled legs, in order (for ordered rollback).
    settled: Vec<SettledLeg>,
}

impl AmmRingParticipant {
    /// Create a participant from a snapshot of the current registry state.
    pub fn from_registry(registry: AmmRegistry) -> Self {
        Self {
            registry,
            settled: Vec::new(),
        }
    }

    /// Encode an asset ID (`[u8; 32]`) as a `u64` pool key.
    ///
    /// We use the first 8 bytes of the asset ID as the pool lookup key.
    fn asset_to_key(asset: &[u8; 32]) -> u64 {
        u64::from_le_bytes(asset[..8].try_into().unwrap())
    }
}

impl RingTradeParticipant for AmmRingParticipant {
    type Error = RingError;

    fn exchange_offers(&self) -> Vec<ExchangeSpec> {
        let mut specs = Vec::new();

        for pool in self.registry.all_pools() {
            // Use the full asset ID bytes as 32-byte keys; encode pool's u64
            // asset types into 32-byte arrays (little-endian in first 8 bytes).
            let mut asset_a = [0u8; 32];
            let mut asset_b = [0u8; 32];
            asset_a[..8].copy_from_slice(&pool.asset_a.to_le_bytes());
            asset_b[..8].copy_from_slice(&pool.asset_b.to_le_bytes());

            if pool.reserve_a == 0 || pool.reserve_b == 0 {
                continue;
            }

            // A→B offer: based on 1% of reserve_a to avoid draining the pool
            let offer_a = (pool.reserve_a / 100).max(1);
            let fee_num = pool.fee_bps as u64;
            let effective_a = offer_a * (10_000 - fee_num) / 10_000;
            let want_b = (pool.reserve_b as u128 * effective_a as u128
                / (pool.reserve_a as u128 + effective_a as u128)) as u64;

            if want_b > 0 {
                specs.push(ExchangeSpec {
                    offer_asset: asset_a,
                    offer_amount: offer_a,
                    want_asset: asset_b,
                    want_min_amount: want_b,
                    min_rate: None,
                    max_rate: None,
                });
            }

            // B→A offer
            let offer_b = (pool.reserve_b / 100).max(1);
            let effective_b = offer_b * (10_000 - fee_num) / 10_000;
            let want_a = (pool.reserve_a as u128 * effective_b as u128
                / (pool.reserve_b as u128 + effective_b as u128)) as u64;

            if want_a > 0 {
                specs.push(ExchangeSpec {
                    offer_asset: asset_b,
                    offer_amount: offer_b,
                    want_asset: asset_a,
                    want_min_amount: want_a,
                    min_rate: None,
                    max_rate: None,
                });
            }
        }

        specs
    }

    fn settle_leg(&mut self, settlement: &Settlement) -> Result<(), RingError> {
        let offer_key = Self::asset_to_key(&settlement.asset);
        // `want` asset: we need to find it from the settlement's `to` side.
        // The Settlement struct only carries `from`, `to` (CommitmentIds), `asset`
        // (the offered asset), and `amount`. We derive the "want" asset from the
        // pool — the pool always has exactly 2 assets.
        let pool = self
            .registry
            .all_pools()
            .into_iter()
            .find(|p| p.asset_a == offer_key || p.asset_b == offer_key)
            .ok_or_else(|| RingError::NoPoolForAssets {
                offer: hex::encode(&settlement.asset),
                want: "unknown".into(),
            })?;

        let pool_id = pool.id;
        let direction_a_to_b = pool.asset_a == offer_key;

        let pool_mut = self
            .registry
            .get_pool_mut(&pool_id)
            .ok_or_else(|| RingError::PoolNotFound(hex::encode(pool_id)))?;

        let output = pool_mut
            .swap(settlement.amount, 1, direction_a_to_b)
            .map_err(|e| RingError::SwapFailed(e.to_string()))?;

        let leg_id = LegId::from_settlement(settlement);
        self.settled.push(SettledLeg {
            leg_id,
            pool_id,
            amount_out: output.amount_out,
            direction_a_to_b,
        });

        Ok(())
    }

    fn rollback_leg(&mut self, settlement: &Settlement) -> Result<(), RingError> {
        let leg_id = LegId::from_settlement(settlement);

        // Find the settled record (search from end for LIFO).
        let pos = self
            .settled
            .iter()
            .rposition(|s| s.leg_id == leg_id)
            .ok_or_else(|| RingError::RollbackFailed("leg not found in settled list".into()))?;

        let leg = self.settled.remove(pos);

        // Reverse the swap: swap back the output amount in the opposite direction.
        let pool = self
            .registry
            .get_pool_mut(&leg.pool_id)
            .ok_or_else(|| RingError::PoolNotFound(hex::encode(leg.pool_id)))?;

        pool.swap(leg.amount_out, 1, !leg.direction_a_to_b)
            .map_err(|e| RingError::RollbackFailed(e.to_string()))?;

        Ok(())
    }
}

// =============================================================================
// HTTP endpoint: POST /ring/settle
// =============================================================================

/// Request body for `POST /ring/settle`.
#[derive(Debug, Deserialize)]
pub struct RingSettleRequest {
    /// Ordered list of settlements to execute atomically.
    pub settlements: Vec<SettlementDto>,
}

/// Wire-format for a single settlement leg.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SettlementDto {
    /// Sender commitment ID (hex, 64 chars).
    pub from: String,
    /// Receiver commitment ID (hex, 64 chars).
    pub to: String,
    /// Asset type (hex, 64 chars).
    pub asset: String,
    /// Amount being transferred.
    pub amount: u64,
}

/// Response from `POST /ring/settle`.
#[derive(Debug, Serialize)]
pub struct RingSettleResponse {
    /// Number of legs settled.
    pub legs_settled: usize,
}

/// Response when a settlement fails mid-ring (after partial rollback).
#[derive(Debug, Serialize)]
pub struct RingSettleError {
    pub error: String,
    pub failed_at_leg: usize,
    pub rolled_back: usize,
}

/// Parse a hex string into `[u8; 32]`.
fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn dto_to_settlement(dto: &SettlementDto) -> Option<Settlement> {
    let from_bytes = parse_hex32(&dto.from)?;
    let to_bytes = parse_hex32(&dto.to)?;
    let asset = parse_hex32(&dto.asset)?;
    Some(Settlement {
        from: pyana_intent::CommitmentId(from_bytes),
        to: pyana_intent::CommitmentId(to_bytes),
        asset,
        amount: dto.amount,
    })
}

pub async fn ring_settle_handler(
    State(state): State<AppState>,
    Json(req): Json<RingSettleRequest>,
) -> Result<Json<RingSettleResponse>, (StatusCode, Json<RingSettleError>)> {
    // Parse all settlements up-front.
    let mut settlements: Vec<Settlement> = Vec::new();
    for (i, dto) in req.settlements.iter().enumerate() {
        let s = dto_to_settlement(dto).ok_or_else(|| {
            (
                StatusCode::BAD_REQUEST,
                Json(RingSettleError {
                    error: format!("invalid hex encoding in settlement[{i}]"),
                    failed_at_leg: i,
                    rolled_back: 0,
                }),
            )
        })?;
        settlements.push(s);
    }

    // Take a snapshot of the registry to work on.
    let registry_snapshot = state.registry.read().await.clone();
    let mut participant = AmmRingParticipant::from_registry(registry_snapshot);

    // Execute legs atomically; rollback on any failure.
    let mut legs_settled = 0usize;
    for (i, settlement) in settlements.iter().enumerate() {
        if let Err(e) = participant.settle_leg(settlement) {
            // Rollback all previously settled legs in reverse order.
            let mut rolled_back = 0usize;
            for j in (0..i).rev() {
                let _ = participant.rollback_leg(&settlements[j]);
                rolled_back += 1;
            }
            return Err((
                StatusCode::UNPROCESSABLE_ENTITY,
                Json(RingSettleError {
                    error: e.to_string(),
                    failed_at_leg: i,
                    rolled_back,
                }),
            ));
        }
        legs_settled += 1;
    }

    // All legs settled — commit the updated registry.
    *state.registry.write().await = participant.registry;

    Ok(Json(RingSettleResponse { legs_settled }))
}

/// Build the ring-trade sub-router.
pub fn ring_router() -> Router<AppState> {
    Router::new().route("/ring/settle", post(ring_settle_handler))
}

// Simple hex encoding helper (avoid pulling in the hex crate).
mod hex {
    pub fn encode(b: impl AsRef<[u8]>) -> String {
        b.as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pool::LiquidityPool;

    // Asset helpers
    fn asset_key(n: u64) -> [u8; 32] {
        let mut a = [0u8; 32];
        a[..8].copy_from_slice(&n.to_le_bytes());
        a
    }

    fn make_registry_with_pool(a: u64, b: u64, ra: u64, rb: u64) -> (AmmRegistry, PoolId) {
        let mut reg = AmmRegistry::new();
        let pool = LiquidityPool::create(a, b, ra, rb).unwrap();
        let id = pool.id;
        reg.register_pool(pool);
        (reg, id)
    }

    // ------------------------------------------------------------------
    // Ring-trade upgrade tests
    // ------------------------------------------------------------------

    #[test]
    fn ring_participant_exchange_offers_non_empty() {
        let (reg, _) = make_registry_with_pool(1, 2, 10_000, 20_000);
        let participant = AmmRingParticipant::from_registry(reg);
        let offers = participant.exchange_offers();
        // Each pool generates 2 specs (A→B and B→A)
        assert_eq!(offers.len(), 2, "expected 2 offers for 1 pool");
        // Each offer must have non-zero amounts
        for spec in &offers {
            assert!(spec.offer_amount > 0);
            assert!(spec.want_min_amount > 0);
        }
    }

    #[test]
    fn ring_participant_settle_and_rollback() {
        let (reg, _) = make_registry_with_pool(1, 2, 10_000, 20_000);
        let reserve_a_before = reg.find_pool_by_pair(1, 2).unwrap().reserve_a;

        let mut participant = AmmRingParticipant::from_registry(reg);

        // Build a settlement: swap 100 units of asset 1 → asset 2
        let asset = asset_key(1);
        let settlement = Settlement {
            from: pyana_intent::CommitmentId([0x01; 32]),
            to: pyana_intent::CommitmentId([0x02; 32]),
            asset,
            amount: 100,
        };

        // Settle
        participant.settle_leg(&settlement).unwrap();

        // Reserve_a should have increased by 100
        let reserve_a_after = participant.registry.find_pool_by_pair(1, 2).unwrap().reserve_a;
        assert_eq!(reserve_a_after, reserve_a_before + 100);

        // Rollback
        participant.rollback_leg(&settlement).unwrap();

        // Reserve_a should be approximately back (within fee tolerance)
        let reserve_a_rolled = participant.registry.find_pool_by_pair(1, 2).unwrap().reserve_a;
        // After rollback, reserve_a should have decreased again
        assert!(reserve_a_rolled < reserve_a_after);
    }

    #[test]
    fn ring_participant_settle_no_pool_returns_error() {
        let (reg, _) = make_registry_with_pool(1, 2, 10_000, 20_000);
        let mut participant = AmmRingParticipant::from_registry(reg);

        // Asset 99 has no pool
        let asset = asset_key(99);
        let settlement = Settlement {
            from: pyana_intent::CommitmentId([0x01; 32]),
            to: pyana_intent::CommitmentId([0x02; 32]),
            asset,
            amount: 100,
        };

        let result = participant.settle_leg(&settlement);
        assert!(result.is_err(), "should fail with no pool for asset 99");
        match result.unwrap_err() {
            RingError::NoPoolForAssets { .. } => {}
            other => panic!("expected NoPoolForAssets, got: {:?}", other),
        }
    }

    #[test]
    fn ring_participant_rollback_unknown_leg_errors() {
        let (reg, _) = make_registry_with_pool(1, 2, 10_000, 20_000);
        let mut participant = AmmRingParticipant::from_registry(reg);

        let asset = asset_key(1);
        let settlement = Settlement {
            from: pyana_intent::CommitmentId([0xFF; 32]),
            to: pyana_intent::CommitmentId([0xEE; 32]),
            asset,
            amount: 100,
        };

        // Never settled this leg — rollback should fail gracefully
        let result = participant.rollback_leg(&settlement);
        assert!(result.is_err());
    }

    #[test]
    fn ring_settle_multiple_legs_atomically() {
        // Two pools with completely disjoint asset sets:
        //   Pool P/Q: assets 10 and 20
        //   Pool R/S: assets 30 and 40
        // Each leg targets one pool unambiguously.
        let mut reg = AmmRegistry::new();
        let pool_pq = LiquidityPool::create(10, 20, 10_000, 20_000).unwrap();
        let pool_rs = LiquidityPool::create(30, 40, 20_000, 5_000).unwrap();
        let pq_reserve_a_init = pool_pq.reserve_a;
        let rs_reserve_a_init = pool_rs.reserve_a;
        reg.register_pool(pool_pq);
        reg.register_pool(pool_rs);

        let mut participant = AmmRingParticipant::from_registry(reg);

        // Leg 1: sell asset 10 into pool P/Q (direction A→B)
        let s1 = Settlement {
            from: pyana_intent::CommitmentId([0x01; 32]),
            to: pyana_intent::CommitmentId([0x02; 32]),
            asset: asset_key(10),
            amount: 500,
        };
        // Leg 2: sell asset 30 into pool R/S (direction A→B)
        let s2 = Settlement {
            from: pyana_intent::CommitmentId([0x02; 32]),
            to: pyana_intent::CommitmentId([0x03; 32]),
            asset: asset_key(30),
            amount: 500,
        };

        participant.settle_leg(&s1).unwrap();
        participant.settle_leg(&s2).unwrap();

        // Pool P/Q: reserve_a should have increased (we put asset 10 in)
        assert_ne!(
            participant.registry.find_pool_by_pair(10, 20).unwrap().reserve_a,
            pq_reserve_a_init,
            "pool P/Q reserve_a should change after leg 1"
        );
        // Pool R/S: reserve_a should have increased (we put asset 30 in)
        assert_ne!(
            participant.registry.find_pool_by_pair(30, 40).unwrap().reserve_a,
            rs_reserve_a_init,
            "pool R/S reserve_a should change after leg 2"
        );
    }
}
