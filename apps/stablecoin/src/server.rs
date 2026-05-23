//! Minimal HTTP API server for the stablecoin CDP system.

use std::collections::HashMap;
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::cdp::{CollateralPosition, PositionStatus, StablecoinRegistry, ETH_ASSET_TYPE};
use crate::circuit::MIN_RATIO_BPS;
use crate::liquidation::LiquidationEngine;
use crate::oracle::{PriceAttestation, PriceOracle, test_attestation};

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub registry: Arc<RwLock<StablecoinRegistry>>,
    pub oracle: Arc<RwLock<PriceOracle>>,
    pub liquidation_engine: Arc<LiquidationEngine>,
    pub current_height: Arc<RwLock<u64>>,
}

impl AppState {
    pub fn new() -> Self {
        let oracle_key = [0x01u8; 32];
        Self {
            registry: Arc::new(RwLock::new(StablecoinRegistry::new())),
            oracle: Arc::new(RwLock::new(PriceOracle::new(vec![oracle_key], 1000))),
            liquidation_engine: Arc::new(LiquidationEngine::default()),
            current_height: Arc::new(RwLock::new(1)),
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
}

#[derive(Deserialize)]
pub struct RepayRequest {
    pub amount: u64,
    pub oracle_price: u64,
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

#[derive(Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

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
        .route("/health", get(health_check))
}

// =============================================================================
// Handlers
// =============================================================================

fn hex_id(id: &[u8; 32]) -> String {
    id.iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_hex_id(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
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

    let mut position =
        CollateralPosition::open(owner, req.collateral_amount, ETH_ASSET_TYPE, MIN_RATIO_BPS, height)
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
    Path(id): Path<String>,
    Json(req): Json<MintRequest>,
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

    position.mint(req.amount, &attestation, height, 1000).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    Ok(Json(position_to_response(position, Some(req.oracle_price))))
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

    position.repay(req.amount, &attestation, 1000).map_err(|e| {
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

async fn health_check() -> &'static str {
    "ok"
}
