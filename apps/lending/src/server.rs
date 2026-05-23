//! HTTP API server for the lending protocol.
//!
//! Uses `pyana-app-framework` for shared infrastructure (error responses, admin auth,
//! persistence pattern). App-specific routes and state live here.

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::{Mutex, RwLock};

use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use pyana_app_framework::server::ErrorResponse;
use pyana_storage::inbox::CapInbox;

use crate::borrow::{BorrowPosition, CollateralEntry};
use crate::circuit::{HealthFactorWitness, prove_health_factor, verify_health_factor_proof};
use crate::executor::{BorrowerDelegation, LendingBatchExecutor};
use crate::interest::BPS_SCALE;
use crate::liquidation::LiquidationResult;
use crate::warnings::{HealthWarning, new_warnings_cap_inbox, push_health_warning};
use crate::{LendingPool, Market};

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub pool: Arc<RwLock<LendingPool>>,
    pub admin_token: AdminToken,
    /// Batch executor for delegated health monitoring + emergency repayment.
    pub executor: Arc<Mutex<LendingBatchExecutor>>,
    /// Shared warnings inbox — borrowers poll this when they reconnect.
    pub warnings_inbox: Arc<Mutex<CapInbox>>,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

impl AppState {
    pub fn new() -> Self {
        let mut pool = LendingPool::new();
        pool.add_market(Market::new(1)); // Stablecoin
        pool.add_market(Market::new(2)); // Volatile asset (ETH-like)
        Self {
            pool: Arc::new(RwLock::new(pool)),
            admin_token: AdminToken::from_env(),
            executor: Arc::new(Mutex::new(LendingBatchExecutor::new())),
            warnings_inbox: Arc::new(Mutex::new(new_warnings_cap_inbox())),
        }
    }
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
pub struct SupplyRequest {
    pub asset_id: u64,
    pub amount: u64,
}

#[derive(Serialize)]
pub struct SupplyResponse {
    pub position_id: String,
    pub principal: u64,
    pub asset_id: u64,
}

#[derive(Deserialize)]
pub struct BorrowRequest {
    pub borrow_asset_id: u64,
    pub amount: u64,
    pub collateral: Vec<CollateralInput>,
}

#[derive(Deserialize)]
pub struct CollateralInput {
    pub asset_id: u64,
    pub amount: u64,
    pub price: u64,
}

#[derive(Serialize)]
pub struct BorrowResponse {
    pub position_id: String,
    pub principal: u64,
    pub health_factor: f64,
    pub proof_bytes: Option<usize>,
}

#[derive(Deserialize)]
pub struct RepayRequest {
    pub amount: u64,
}

#[derive(Serialize)]
pub struct RepayResponse {
    pub repaid: u64,
    pub remaining_debt: u64,
    pub fully_repaid: bool,
}

#[derive(Deserialize)]
pub struct LiquidateRequest {
    pub repay_amount: u64,
    pub collateral_asset_id: u64,
}

#[derive(Serialize)]
pub struct PositionResponse {
    pub id: String,
    pub principal: u64,
    pub total_debt: u64,
    pub collateral_value: u64,
    pub health_factor: f64,
    pub is_healthy: bool,
    pub repaid: bool,
    pub liquidated: bool,
}

#[derive(Serialize)]
pub struct MarketResponse {
    pub asset_id: u64,
    pub total_supply: u64,
    pub total_borrows: u64,
    pub utilization_pct: f64,
    pub supply_apy_pct: f64,
    pub borrow_apy_pct: f64,
}

#[derive(Serialize)]
pub struct ProofResponse {
    pub healthy: bool,
    pub proof_size_bytes: usize,
    pub verified: bool,
}

// =============================================================================
// Executor request / response types
// =============================================================================

#[derive(Deserialize)]
pub struct DelegateRequest {
    /// Hex-encoded borrower cell ID (64 chars).
    pub borrower_hex: String,
    /// Hex-encoded borrow position ID (64 chars).
    pub position_id_hex: String,
    /// Maximum repayment from reserve (in base units).
    pub reserve_amount: u64,
}

#[derive(Serialize)]
pub struct DelegateResponse {
    pub registered: bool,
    pub position_id: String,
}

#[derive(Deserialize)]
pub struct ExecutorRunRequest {
    /// Maximum batch size for this run.
    pub max_batch_size: Option<usize>,
}

#[derive(Serialize)]
pub struct ExecutorRunResponse {
    /// Number of turns collected from at-risk scan.
    pub scanned: usize,
    /// Number of turns in the collected batch.
    pub batch_size: usize,
    /// Position IDs that were repaid.
    pub repaid_positions: Vec<String>,
    /// Batch ID (hex).
    pub batch_id: String,
    /// Number of warnings pushed to inbox.
    pub warnings_pushed: usize,
}

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/markets", get(list_markets))
        .route("/supply", post(supply))
        .route("/borrow", post(borrow))
        .route("/position/{id}", get(get_position))
        .route("/position/{id}/repay", post(repay))
        .route("/position/{id}/liquidate", post(liquidate))
        .route("/position/{id}/prove_health", post(prove_health))
        .route("/executor/delegate", post(executor_delegate))
        .route("/executor/run", post(executor_run))
        .route("/admin/advance", post(admin_advance_height))
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

fn position_to_response(pos: &BorrowPosition) -> PositionResponse {
    PositionResponse {
        id: hex_id(&pos.id),
        principal: pos.principal,
        total_debt: pos.total_debt(),
        collateral_value: pos.collateral_value(),
        health_factor: pos.health_factor_bps() as f64 / BPS_SCALE as f64,
        is_healthy: pos.is_healthy(),
        repaid: pos.repaid,
        liquidated: pos.liquidated,
    }
}

async fn list_markets(State(state): State<AppState>) -> Json<Vec<MarketResponse>> {
    let pool = state.pool.read().await;
    let markets: Vec<MarketResponse> = pool
        .markets
        .iter()
        .map(|m| MarketResponse {
            asset_id: m.asset_id,
            total_supply: m.total_supply,
            total_borrows: m.total_borrows,
            utilization_pct: m.utilization_bps() as f64 / 100.0,
            supply_apy_pct: m.supply_apy_bps() as f64 / 100.0,
            borrow_apy_pct: m.borrow_apy_bps() as f64 / 100.0,
        })
        .collect();
    Json(markets)
}

async fn supply(
    State(state): State<AppState>,
    Json(req): Json<SupplyRequest>,
) -> Result<(StatusCode, Json<SupplyResponse>), (StatusCode, Json<ErrorResponse>)> {
    let owner = pyana_types::CellId([0xAA; 32]); // placeholder
    let mut pool = state.pool.write().await;

    let receipt = pool.supply(owner, req.asset_id, req.amount).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    Ok((
        StatusCode::CREATED,
        Json(SupplyResponse {
            position_id: hex_id(&receipt.position_id),
            principal: receipt.principal,
            asset_id: receipt.asset_id,
        }),
    ))
}

async fn borrow(
    State(state): State<AppState>,
    Json(req): Json<BorrowRequest>,
) -> Result<(StatusCode, Json<BorrowResponse>), (StatusCode, Json<ErrorResponse>)> {
    let borrower = pyana_types::CellId([0xBB; 32]); // placeholder
    let mut pool = state.pool.write().await;

    let collateral: Vec<CollateralEntry> = req
        .collateral
        .iter()
        .map(|c| CollateralEntry {
            asset_id: c.asset_id,
            amount: c.amount,
            price: c.price,
        })
        .collect();

    let pos_id = pool
        .borrow(
            borrower,
            req.borrow_asset_id,
            req.amount,
            collateral.clone(),
        )
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    // Generate a STARK proof of health for the new position
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == pos_id)
        .unwrap();

    let witness = HealthFactorWitness {
        collateral_amounts: pos.collateral.iter().map(|c| c.amount).collect(),
        collateral_prices: pos.collateral.iter().map(|c| c.price).collect(),
        debt_amount: pos.total_debt(),
        threshold_bps: pos.liquidation_threshold_bps,
    };

    let proof_size = prove_health_factor(&witness).ok().map(|p| p.len());

    Ok((
        StatusCode::CREATED,
        Json(BorrowResponse {
            position_id: hex_id(&pos_id),
            principal: req.amount,
            health_factor: pos.health_factor_bps() as f64 / BPS_SCALE as f64,
            proof_bytes: proof_size,
        }),
    ))
}

async fn get_position(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<PositionResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let pool = state.pool.read().await;
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == id_bytes)
        .ok_or_else(|| {
            (
                StatusCode::NOT_FOUND,
                Json(ErrorResponse {
                    error: "position not found".to_string(),
                }),
            )
        })?;

    Ok(Json(position_to_response(pos)))
}

async fn repay(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<RepayRequest>,
) -> Result<Json<RepayResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut pool = state.pool.write().await;
    let repaid = pool.repay(&id_bytes, req.amount).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: e.to_string(),
            }),
        )
    })?;

    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == id_bytes)
        .unwrap();

    Ok(Json(RepayResponse {
        repaid,
        remaining_debt: pos.total_debt(),
        fully_repaid: pos.repaid,
    }))
}

async fn liquidate(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<LiquidateRequest>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let liquidator = pyana_types::CellId([0xCC; 32]); // placeholder
    let mut pool = state.pool.write().await;

    let result = pool
        .liquidate(
            &id_bytes,
            liquidator,
            req.repay_amount,
            req.collateral_asset_id,
        )
        .map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: e.to_string(),
                }),
            )
        })?;

    match result {
        LiquidationResult::Success(receipt) => Ok(Json(serde_json::json!({
            "status": "liquidated",
            "debt_repaid": receipt.debt_repaid,
            "collateral_seized": receipt.collateral_seized,
            "bonus_amount": receipt.bonus_amount,
        }))),
        LiquidationResult::PositionHealthy { health_factor_bps } => Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: format!(
                    "position is healthy (health factor: {:.2})",
                    health_factor_bps as f64 / BPS_SCALE as f64
                ),
            }),
        )),
        LiquidationResult::PositionClosed => Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "position already closed".to_string(),
            }),
        )),
        LiquidationResult::ExceedsCloseFactor {
            max_repayable,
            requested,
        } => Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: format!(
                    "exceeds close factor: max {} but requested {}",
                    max_repayable, requested
                ),
            }),
        )),
    }
}

/// Generate and verify a STARK proof of health for a position.
async fn prove_health(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<ProofResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let pool = state.pool.read().await;
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == id_bytes)
        .ok_or_else(|| {
            (
                StatusCode::NOT_FOUND,
                Json(ErrorResponse {
                    error: "position not found".to_string(),
                }),
            )
        })?;

    let witness = HealthFactorWitness {
        collateral_amounts: pos.collateral.iter().map(|c| c.amount).collect(),
        collateral_prices: pos.collateral.iter().map(|c| c.price).collect(),
        debt_amount: pos.total_debt(),
        threshold_bps: pos.liquidation_threshold_bps,
    };

    let healthy = witness.is_healthy();
    let proof_bytes = prove_health_factor(&witness).map_err(|e| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: format!("proof generation failed: {}", e),
            }),
        )
    })?;

    let verified = verify_health_factor_proof(&proof_bytes, &witness).is_ok();

    Ok(Json(ProofResponse {
        healthy,
        proof_size_bytes: proof_bytes.len(),
        verified,
    }))
}

// =============================================================================
// Executor Handlers
// =============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    pyana_app_framework::hex::hex_to_bytes32(s).ok()
}

/// Register a borrower delegation so the executor can monitor their position.
async fn executor_delegate(
    State(state): State<AppState>,
    Json(req): Json<DelegateRequest>,
) -> Result<(StatusCode, Json<DelegateResponse>), (StatusCode, Json<ErrorResponse>)> {
    let borrower_bytes = parse_hex32(&req.borrower_hex).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid borrower_hex".to_string(),
            }),
        )
    })?;
    let position_id = parse_hex32(&req.position_id_hex).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid position_id_hex".to_string(),
            }),
        )
    })?;

    let borrower = pyana_types::CellId(borrower_bytes);
    let mut exec = state.executor.lock().await;
    exec.register_delegation(BorrowerDelegation {
        borrower,
        position_id,
        reserve_amount: req.reserve_amount,
        active: true,
    });

    Ok((
        StatusCode::CREATED,
        Json(DelegateResponse {
            registered: true,
            position_id: req.position_id_hex,
        }),
    ))
}

/// Drive the executor: scan at-risk positions, collect batch, apply repayments,
/// and push inbox warnings for any position that crossed the health threshold.
async fn executor_run(
    State(state): State<AppState>,
    Json(req): Json<ExecutorRunRequest>,
) -> Json<ExecutorRunResponse> {
    use pyana_app_framework::batch_executor::BatchExecutor;

    let max_batch_size = req.max_batch_size.unwrap_or(64);

    // Step 1: collect pool snapshot info and scan for at-risk positions
    let mut exec = state.executor.lock().await;
    let pool_read = state.pool.read().await;
    let scanned = exec.scan_at_risk(&pool_read);
    drop(pool_read);

    // Step 2: collect the batch
    let batch = exec.collect_batch(max_batch_size);
    let batch_size = batch.len();

    // Step 3: compute batch_id
    let execution = exec.execute_batch(batch.clone()).unwrap_or(pyana_app_framework::batch_executor::BatchExecution {
        batch_id: [0u8; 32],
        turn_count: 0,
        proof: None,
    });

    // Step 4: apply repayments to the pool
    let mut pool_write = state.pool.write().await;
    let repaid = exec.apply_batch(&batch, &mut pool_write);
    let repaid_positions: Vec<String> = repaid.iter().map(hex_id).collect();

    // Step 5: push inbox warnings for positions that crossed the threshold
    let mut warnings_count = 0;
    {
        let mut inbox = state.warnings_inbox.lock().await;
        for pos in &pool_write.borrow_positions {
            if pos.repaid || pos.liquidated {
                continue;
            }
            let health = pos.health_factor_bps();
            if health < crate::executor::EXECUTOR_HEALTH_THRESHOLD_BPS {
                let warning = HealthWarning {
                    position_id_hex: hex_id(&pos.id),
                    health_factor_bps: health,
                    threshold_bps: crate::executor::EXECUTOR_HEALTH_THRESHOLD_BPS,
                    block: pool_write.current_block,
                };
                if push_health_warning(&mut inbox, pos.borrower, warning, 0).is_ok() {
                    warnings_count += 1;
                }
            }
        }
    }

    let batch_id_hex: String = execution.batch_id.iter().map(|b| format!("{b:02x}")).collect();

    Json(ExecutorRunResponse {
        scanned,
        batch_size,
        repaid_positions,
        batch_id: batch_id_hex,
        warnings_pushed: warnings_count,
    })
}

// =============================================================================
// Admin Handlers
// =============================================================================

#[derive(Deserialize)]
pub struct AdvanceHeightRequest {
    pub blocks: Option<u64>,
}

async fn admin_advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(req): Json<AdvanceHeightRequest>,
) -> Json<serde_json::Value> {
    let blocks = req.blocks.unwrap_or(1);
    let mut pool = state.pool.write().await;
    let new_block = pool.current_block + blocks;
    pool.advance_to_block(new_block);
    Json(serde_json::json!({
        "current_block": pool.current_block,
        "advanced_by": blocks,
    }))
}
