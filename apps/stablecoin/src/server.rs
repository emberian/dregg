//! HTTP API server for the stablecoin CDP system.
//!
//! Uses `pyana-app-framework` for shared infrastructure (error responses, admin auth,
//! persistence pattern). App-specific routes and state live here.

use std::sync::Arc;

use axum::{
    Extension, Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use pyana_app_framework::fee_policy::FeePolicy;
use pyana_app_framework::server::ErrorResponse;

use crate::cdp::{CollateralPosition, ETH_ASSET_TYPE, PositionStatus, StablecoinRegistry};
use crate::circuit::MIN_RATIO_BPS;
use crate::fee_endpoints::{compute_fee_or_reject, default_fee_policy, resolve_paying_asset};
use crate::liquidation::LiquidationEngine;
use crate::liquidation_queue::{LIQUIDATION_QUEUE_MIN_DEPOSIT, LiquidationQueue};
use crate::oracle::{PriceOracle, test_attestation, test_oracle_pubkey};

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub registry: Arc<RwLock<StablecoinRegistry>>,
    pub oracle: Arc<RwLock<PriceOracle>>,
    pub liquidation_engine: Arc<LiquidationEngine>,
    /// Programmable liquidation queue (Upgrade 1).
    pub liquidation_queue: Arc<LiquidationQueue>,
    pub current_height: Arc<RwLock<u64>>,
    pub admin_token: AdminToken,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

impl AppState {
    pub fn new() -> Self {
        // The signing key used by test_attestation to produce valid signatures.
        let signing_key = [0x01u8; 32];
        // Derive the Ed25519 public key for the trusted_keys list.
        let oracle_pubkey = test_oracle_pubkey(&signing_key);
        Self {
            registry: Arc::new(RwLock::new(StablecoinRegistry::new())),
            oracle: Arc::new(RwLock::new(PriceOracle::new(vec![oracle_pubkey], 1000))),
            liquidation_engine: Arc::new(LiquidationEngine::default_config()),
            liquidation_queue: Arc::new(LiquidationQueue::new()),
            current_height: Arc::new(RwLock::new(1)),
            admin_token: AdminToken::from_env(),
        }
    }
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
pub struct OpenCdpRequest {
    pub collateral_amount: u64,
    pub debt_amount: Option<u64>,
    pub oracle_price: u64,
}

#[derive(Serialize)]
pub struct CdpResponse {
    pub id: String,
    pub collateral_amount: u64,
    pub debt_amount: u64,
    pub status: String,
    pub health_factor: Option<f64>,
}

#[derive(Deserialize)]
pub struct MintRequest {
    pub amount: u64,
    pub oracle_price: u64,
    /// Optional hex-encoded 32-byte asset ID for fee payment.
    /// Defaults to native computrons if omitted.
    /// Returns 400 if the asset is not in the accepted fee policy.
    pub paying_asset: Option<String>,
}

#[derive(Serialize)]
pub struct MintResponse {
    #[serde(flatten)]
    pub cdp: CdpResponse,
    /// The fee amount charged, denominated in `fee_asset`.
    pub fee_charged: u64,
    /// Hex-encoded asset ID used for fee payment.
    pub fee_asset: String,
}

#[derive(Deserialize)]
pub struct RepayRequest {
    pub amount: u64,
    pub oracle_price: u64,
}

/// Request to submit a liquidation candidate to the programmable queue.
#[derive(Deserialize)]
pub struct QueueLiquidationRequest {
    /// CDP position ID (hex-encoded 32 bytes).
    pub position_id: String,
    /// Oracle price to use for health-factor assessment.
    pub oracle_price: u64,
    /// Sender identity (hex-encoded 32 bytes).
    pub sender: Option<String>,
}

#[derive(Serialize)]
pub struct QueueLiquidationResponse {
    pub queued: bool,
    pub position_id: String,
    pub health_factor_bps: u64,
    pub queue_length: usize,
}

/// Request to pay a stability fee in a chosen asset.
#[derive(Deserialize)]
pub struct StabilityFeeRequest {
    /// Base stability fee amount in computrons.
    pub base_amount: u64,
    /// Optional hex-encoded 32-byte asset ID for fee payment.
    /// Defaults to native computrons if omitted.
    pub paying_asset: Option<String>,
}

#[derive(Serialize)]
pub struct StabilityFeeResponse {
    /// The fee amount charged in the chosen asset.
    pub fee_charged: u64,
    /// Hex-encoded asset ID used for fee payment.
    pub fee_asset: String,
}

#[derive(Deserialize)]
pub struct LiquidateRequest {
    pub oracle_price: u64,
}

#[derive(Deserialize)]
pub struct OracleUpdateRequest {
    pub asset_pair: String,
    pub price: u64,
    pub timestamp: u64,
    pub oracle_pubkey: Option<String>,
}

#[derive(Serialize)]
pub struct OraclePriceResponse {
    pub asset_pair: String,
    pub price: u64,
    pub timestamp: u64,
}

// ErrorResponse is imported from pyana_app_framework::server::ErrorResponse

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/cdp/open", post(open_cdp))
        .route("/cdp/{id}", get(get_cdp))
        .route("/cdp/{id}/mint", post(mint_cdp))
        .route("/cdp/{id}/repay", post(repay_cdp))
        .route("/cdp/{id}/liquidate", post(liquidate_cdp))
        .route("/oracle/update", post(oracle_update))
        .route("/oracle/price", get(oracle_price))
        .route("/admin/height", post(admin_advance_height))
        // Upgrade 1: programmable liquidation queue
        .route("/queue/liquidations/submit", post(queue_liquidation_submit))
        .route("/queue/liquidations/drain", get(queue_liquidation_drain))
        // Upgrade 2: multi-asset fees
        .route("/fees", get(crate::fee_endpoints::get_fees))
        .route("/stability-fee", post(stability_fee))
}

// =============================================================================
// Handlers
// =============================================================================

fn hex_id(id: &[u8; 32]) -> String {
    pyana_app_framework::hex::bytes32_to_hex(id)
}

fn parse_hex_id(s: &str) -> Option<[u8; 32]> {
    pyana_app_framework::hex::hex_to_bytes32(s).ok()
}

fn position_to_response(pos: &CollateralPosition, price: Option<u64>) -> CdpResponse {
    let health_factor = price.and_then(|p| {
        pos.collateral_ratio_bps(p)
            .map(|ratio| ratio as f64 / MIN_RATIO_BPS as f64)
    });
    CdpResponse {
        id: hex_id(&pos.id),
        collateral_amount: pos.collateral_amount,
        debt_amount: pos.debt_amount,
        status: match &pos.status {
            PositionStatus::Active => "active".to_string(),
            PositionStatus::Closed => "closed".to_string(),
            PositionStatus::Liquidated { .. } => "liquidated".to_string(),
        },
        health_factor,
    }
}

async fn open_cdp(
    State(state): State<AppState>,
    Json(req): Json<OpenCdpRequest>,
) -> Result<(StatusCode, Json<CdpResponse>), (StatusCode, Json<ErrorResponse>)> {
    let owner = pyana_cell::CellId([0xAA; 32]); // placeholder owner
    let height = *state.current_height.read().await;

    let mut position = CollateralPosition::open(
        owner,
        req.collateral_amount,
        ETH_ASSET_TYPE,
        MIN_RATIO_BPS,
        height,
    )
    .map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    // If the caller wants to mint immediately on open:
    if let Some(debt) = req.debt_amount {
        if debt > 0 {
            let attestation = test_attestation("ETH/USD", req.oracle_price, height, [0x01; 32]);
            position
                .mint(debt, &attestation, height, 1000)
                .map_err(|e| {
                    (
                        StatusCode::BAD_REQUEST,
                        Json(ErrorResponse {
                            error: e.to_string(),
                        }),
                    )
                })?;
        }
    }

    let resp = position_to_response(&position, Some(req.oracle_price));
    state.registry.write().await.register(position);
    Ok((StatusCode::CREATED, Json(resp)))
}

async fn get_cdp(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<CdpResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let registry = state.registry.read().await;
    let position = registry.get(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "CDP not found".to_string(),
            }),
        )
    })?;

    // Try to get latest oracle price for health factor.
    let oracle = state.oracle.read().await;
    let height = *state.current_height.read().await;
    let price = oracle.get_price("ETH/USD", height).ok().map(|a| a.price);

    Ok(Json(position_to_response(position, price)))
}

async fn mint_cdp(
    State(state): State<AppState>,
    Extension(policy): Extension<FeePolicy>,
    Path(id): Path<String>,
    Json(req): Json<MintRequest>,
) -> Result<Json<MintResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    // Upgrade 2: resolve paying asset and compute fee.
    let paying_asset = resolve_paying_asset(req.paying_asset.as_deref(), &policy)
        .map_err(|e| (StatusCode::BAD_REQUEST, Json(ErrorResponse { error: e })))?;

    // Base fee = 1% of mint amount (100 bps).
    let base_fee = req.amount / 100;
    let fee_charged = compute_fee_or_reject(&policy, &paying_asset, base_fee)?;

    let height = *state.current_height.read().await;
    let attestation = test_attestation("ETH/USD", req.oracle_price, height, [0x01; 32]);

    let mut registry = state.registry.write().await;
    let position = registry.get_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "CDP not found".to_string(),
            }),
        )
    })?;

    position
        .mint(req.amount, &attestation, height, 1000)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    Ok(Json(MintResponse {
        cdp: position_to_response(position, Some(req.oracle_price)),
        fee_charged,
        fee_asset: hex_id(&paying_asset),
    }))
}

async fn repay_cdp(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<RepayRequest>,
) -> Result<Json<CdpResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let height = *state.current_height.read().await;
    let attestation = test_attestation("ETH/USD", req.oracle_price, height, [0x01; 32]);

    let mut registry = state.registry.write().await;
    let position = registry.get_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "CDP not found".to_string(),
            }),
        )
    })?;

    position
        .repay(req.amount, &attestation, 1000)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    Ok(Json(position_to_response(position, Some(req.oracle_price))))
}

async fn liquidate_cdp(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<LiquidateRequest>,
) -> Result<Json<CdpResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut registry = state.registry.write().await;
    let position = registry.get_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "CDP not found".to_string(),
            }),
        )
    })?;

    if !position.is_liquidatable(req.oracle_price) {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "position is not liquidatable at this price".to_string(),
            }),
        ));
    }

    let height = *state.current_height.read().await;
    position.status = PositionStatus::Liquidated {
        liquidated_at: height,
        liquidator: pyana_cell::CellId([0xBB; 32]),
    };

    Ok(Json(position_to_response(position, Some(req.oracle_price))))
}

async fn oracle_update(
    State(state): State<AppState>,
    Json(req): Json<OracleUpdateRequest>,
) -> Result<StatusCode, (StatusCode, Json<ErrorResponse>)> {
    let height = *state.current_height.read().await;
    let oracle_key = [0x01u8; 32];
    let attestation = test_attestation(&req.asset_pair, req.price, req.timestamp, oracle_key);

    state
        .oracle
        .write()
        .await
        .submit_attestation(attestation, height)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    Ok(StatusCode::OK)
}

async fn oracle_price(
    State(state): State<AppState>,
) -> Result<Json<OraclePriceResponse>, (StatusCode, Json<ErrorResponse>)> {
    let height = *state.current_height.read().await;
    let oracle = state.oracle.read().await;
    let attestation = oracle.get_price("ETH/USD", height).map_err(|e| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    Ok(Json(OraclePriceResponse {
        asset_pair: attestation.asset_pair.clone(),
        price: attestation.price,
        timestamp: attestation.timestamp,
    }))
}

// =============================================================================
// Upgrade 1: Liquidation Queue Handlers
// =============================================================================

/// `POST /queue/liquidations/submit` — submit a CDP position as a liquidation candidate.
///
/// The request must include the position_id, oracle_price, and optionally sender.
/// Returns 400 if the position is not liquidatable or is already queued.
async fn queue_liquidation_submit(
    State(state): State<AppState>,
    Json(req): Json<QueueLiquidationRequest>,
) -> Result<Json<QueueLiquidationResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&req.position_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid position_id format".to_string(),
            }),
        )
    })?;

    let sender = if let Some(s) = &req.sender {
        parse_hex_id(s).ok_or_else(|| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: "invalid sender format".to_string(),
                }),
            )
        })?
    } else {
        [0u8; 32]
    };

    let registry = state.registry.read().await;
    let position = registry.get(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "CDP not found".to_string(),
            }),
        )
    })?;

    let health_factor_bps = position
        .collateral_ratio_bps(req.oracle_price)
        .unwrap_or(u64::MAX);

    state
        .liquidation_queue
        .submit(position, req.oracle_price, sender, LIQUIDATION_QUEUE_MIN_DEPOSIT)
        .await
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    let queue_length = state.liquidation_queue.len().await;

    Ok(Json(QueueLiquidationResponse {
        queued: true,
        position_id: req.position_id,
        health_factor_bps,
        queue_length,
    }))
}

/// `GET /queue/liquidations/drain` — return all pending liquidation candidates in priority order.
///
/// Returns candidates sorted lowest-health-factor-first (most-at-risk first).
async fn queue_liquidation_drain(
    State(state): State<AppState>,
) -> Json<serde_json::Value> {
    let candidates = state.liquidation_queue.drain_priority().await;
    Json(serde_json::json!({
        "candidates": candidates.iter().map(|c| serde_json::json!({
            "position_id": hex::encode(c.position_id),
            "oracle_price": c.oracle_price,
            "health_factor_bps": c.health_factor_bps,
        })).collect::<Vec<_>>(),
        "count": candidates.len(),
    }))
}

// =============================================================================
// Upgrade 2: Stability Fee with Multi-Asset Payment
// =============================================================================

/// `POST /stability-fee` — compute and record a stability fee in the caller's chosen asset.
///
/// The request specifies a base amount and optionally a paying_asset (hex-encoded 32-byte
/// asset ID). Returns 400 if the asset is not in the accepted fee policy.
async fn stability_fee(
    Extension(policy): Extension<FeePolicy>,
    Json(req): Json<StabilityFeeRequest>,
) -> Result<Json<StabilityFeeResponse>, (StatusCode, Json<ErrorResponse>)> {
    let paying_asset = resolve_paying_asset(req.paying_asset.as_deref(), &policy)
        .map_err(|e| (StatusCode::BAD_REQUEST, Json(ErrorResponse { error: e })))?;

    let fee_charged = compute_fee_or_reject(&policy, &paying_asset, req.base_amount)?;

    Ok(Json(StabilityFeeResponse {
        fee_charged,
        fee_asset: hex_id(&paying_asset),
    }))
}

mod hex {
    pub fn encode(b: impl AsRef<[u8]>) -> String {
        b.as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
    }
}

// =============================================================================
// Admin Handlers (protected by AdminAuth extractor)
// =============================================================================

#[derive(Deserialize)]
pub struct AdvanceHeightRequest {
    pub delta: Option<u64>,
}

async fn admin_advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(req): Json<AdvanceHeightRequest>,
) -> Json<serde_json::Value> {
    let delta = req.delta.unwrap_or(1);
    let mut height = state.current_height.write().await;
    *height += delta;
    Json(serde_json::json!({"height": *height}))
}
