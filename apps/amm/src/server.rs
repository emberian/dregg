//! Minimal HTTP API server for the AMM.

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::AmmRegistry;
use crate::pool::LiquidityPool;
use crate::ring::ring_router;
use crate::twap_queue::{SharedTwapState, TwapBatchState, twap_queue_router};

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub registry: Arc<RwLock<AmmRegistry>>,
    /// Staged swap intents for TWAP batch execution.
    pub twap_state: SharedTwapState,
}

impl AppState {
    pub fn new() -> Self {
        Self {
            registry: Arc::new(RwLock::new(AmmRegistry::new())),
            twap_state: Arc::new(RwLock::new(TwapBatchState::default())),
        }
    }
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
pub struct CreatePoolRequest {
    pub token_a: u64,
    pub token_b: u64,
    pub initial_a: u64,
    pub initial_b: u64,
}

#[derive(Serialize)]
pub struct PoolResponse {
    pub id: String,
    pub token_a: u64,
    pub token_b: u64,
    pub reserve_a: u64,
    pub reserve_b: u64,
    pub k: String,
    pub lp_total_supply: u64,
    pub fee_bps: u32,
}

#[derive(Deserialize)]
pub struct SwapRequest {
    pub amount_in: u64,
    pub direction_a_to_b: bool,
    pub min_out: u64,
}

#[derive(Serialize)]
pub struct SwapResponse {
    pub amount_out: u64,
    pub fee_amount: u64,
    pub reserve_a_new: u64,
    pub reserve_b_new: u64,
}

#[derive(Deserialize)]
pub struct AddLiquidityRequest {
    pub amount_a: u64,
    pub amount_b: u64,
}

#[derive(Serialize)]
pub struct AddLiquidityResponse {
    pub lp_minted: u64,
    pub amount_a_used: u64,
    pub amount_b_used: u64,
}

#[derive(Deserialize)]
pub struct RemoveLiquidityRequest {
    pub lp_amount: u64,
}

#[derive(Serialize)]
pub struct RemoveLiquidityResponse {
    pub amount_a: u64,
    pub amount_b: u64,
}

#[derive(Serialize)]
pub struct QuoteResponse {
    pub estimated_out: u64,
    pub price_impact_bps: u64,
}

#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/pools", post(create_pool))
        .route("/pools/{id}", get(get_pool))
        .route("/pools/{id}/swap", post(swap))
        .route("/pools/{id}/add-liquidity", post(add_liquidity))
        .route("/pools/{id}/remove-liquidity", post(remove_liquidity))
        .route("/pools/{id}/quote", get(get_quote))
        .route("/health", get(health_check))
        // Upgrade 1: Ring trade solver participation
        .merge(ring_router())
}

/// Build the full AMM router including the TWAP queue endpoint.
///
/// The queue is nested under `/queue/swaps` and uses the `AppServer::with_queue_endpoint`
/// pattern. Call this from `main` to get the complete server.
pub fn full_router(state: AppState) -> Router {
    let twap_state = state.twap_state.clone();
    // Upgrade 2: TWAP batch queue mounted at /queue/swaps
    let queue_router = twap_queue_router(twap_state, state.clone());
    Router::new()
        .merge(router().with_state(state))
        .nest("/queue/swaps", queue_router)
}

// =============================================================================
// Helpers
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

fn pool_to_response(pool: &LiquidityPool) -> PoolResponse {
    PoolResponse {
        id: hex_id(&pool.id),
        token_a: pool.asset_a,
        token_b: pool.asset_b,
        reserve_a: pool.reserve_a,
        reserve_b: pool.reserve_b,
        k: pool.k().to_string(),
        lp_total_supply: pool.lp_total_supply,
        fee_bps: pool.fee_bps,
    }
}

// =============================================================================
// Handlers
// =============================================================================

async fn create_pool(
    State(state): State<AppState>,
    Json(req): Json<CreatePoolRequest>,
) -> Result<(StatusCode, Json<PoolResponse>), (StatusCode, Json<ErrorResponse>)> {
    let pool = LiquidityPool::create(req.token_a, req.token_b, req.initial_a, req.initial_b)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    let resp = pool_to_response(&pool);
    state.registry.write().await.register_pool(pool);
    Ok((StatusCode::CREATED, Json(resp)))
}

async fn get_pool(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<PoolResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let registry = state.registry.read().await;
    let pool = registry.get_pool(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "pool not found".to_string(),
            }),
        )
    })?;

    Ok(Json(pool_to_response(pool)))
}

async fn swap(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<SwapRequest>,
) -> Result<Json<SwapResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut registry = state.registry.write().await;
    let pool = registry.get_pool_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "pool not found".to_string(),
            }),
        )
    })?;

    let output = pool
        .swap(req.amount_in, req.min_out, req.direction_a_to_b)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    Ok(Json(SwapResponse {
        amount_out: output.amount_out,
        fee_amount: output.fee_amount,
        reserve_a_new: output.reserve_a_new,
        reserve_b_new: output.reserve_b_new,
    }))
}

async fn add_liquidity(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<AddLiquidityRequest>,
) -> Result<Json<AddLiquidityResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut registry = state.registry.write().await;
    let pool = registry.get_pool_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "pool not found".to_string(),
            }),
        )
    })?;

    let output = pool
        .add_liquidity(req.amount_a, req.amount_b)
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    Ok(Json(AddLiquidityResponse {
        lp_minted: output.lp_minted,
        amount_a_used: output.amount_a_used,
        amount_b_used: output.amount_b_used,
    }))
}

async fn remove_liquidity(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<RemoveLiquidityRequest>,
) -> Result<Json<RemoveLiquidityResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut registry = state.registry.write().await;
    let pool = registry.get_pool_mut(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "pool not found".to_string(),
            }),
        )
    })?;

    let output = pool.remove_liquidity(req.lp_amount).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    Ok(Json(RemoveLiquidityResponse {
        amount_a: output.amount_a,
        amount_b: output.amount_b,
    }))
}

async fn get_quote(
    State(state): State<AppState>,
    Path(id): Path<String>,
    axum::extract::Query(params): axum::extract::Query<QuoteParams>,
) -> Result<Json<QuoteResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let registry = state.registry.read().await;
    let pool = registry.get_pool(&id_bytes).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "pool not found".to_string(),
            }),
        )
    })?;

    let amount_in = params.amount_in;
    let direction_a_to_b = params.direction_a_to_b.unwrap_or(true);

    // Compute quote without mutating state (simulate the swap math).
    let (reserve_in, reserve_out) = if direction_a_to_b {
        (pool.reserve_a, pool.reserve_b)
    } else {
        (pool.reserve_b, pool.reserve_a)
    };

    if reserve_in == 0 || reserve_out == 0 || amount_in == 0 {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid quote parameters".to_string(),
            }),
        ));
    }

    let fee = amount_in * pool.fee_bps as u64 / 10_000;
    let effective_in = amount_in - fee;
    let estimated_out = (reserve_out as u128 * effective_in as u128
        / (reserve_in as u128 + effective_in as u128)) as u64;

    // price_impact = 1 - (estimated_out / reserve_out) / (amount_in / reserve_in)
    // Simplified: in bps
    let spot_out = (reserve_out as u128 * amount_in as u128 / reserve_in as u128) as u64;
    let impact_bps = if spot_out > 0 {
        ((spot_out - estimated_out) as u128 * 10_000 / spot_out as u128) as u64
    } else {
        0
    };

    Ok(Json(QuoteResponse {
        estimated_out,
        price_impact_bps: impact_bps,
    }))
}

#[derive(Deserialize)]
pub struct QuoteParams {
    pub amount_in: u64,
    pub direction_a_to_b: Option<bool>,
}

async fn health_check() -> &'static str {
    "ok"
}
