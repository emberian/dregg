//! In-process bounty board server for embedding in examples and tests.
//!
//! This module provides a way to start the bounty board HTTP server within the
//! same process (as a background tokio task), avoiding the need for a separate
//! binary or a live devnet node.
//!
//! Uses the shared `AppServer` from `pyana-app-framework` for consistent
//! infrastructure (health endpoint, CORS) across all pyana apps.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
};
use serde_json::json;
use tokio::sync::{Mutex, RwLock};
use tracing::{info, warn};

use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_app_framework::{CellId, EngineConfig, PyanaEngine};

use crate::qualification::{FederationRootHistory, verify_qualification};
use crate::state::BoardState;
use crate::{
    ApproveRequest, Bounty, BountyFilter, BountyStatus, BountyStatusResponse, ClaimRequest,
    CreateBountyRequest, SubmitRequest, bounty_id_from_hex, bounty_id_hex, compute_bounty_id,
};

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the in-process bounty board server.
pub struct ServerConfig {
    /// Initial federation root (can be updated via admin endpoint).
    pub federation_root: [u8; 32],
    /// Listen address.
    pub listen: SocketAddr,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            federation_root: [0u8; 32],
            listen: "127.0.0.1:3030".parse().unwrap(),
        }
    }
}

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
struct AppState {
    board: BoardState,
    root_history: Arc<RwLock<FederationRootHistory>>,
    root_last_updated: Arc<RwLock<Option<Instant>>>,
    engine: Arc<Mutex<PyanaEngine>>,
    node_url: Arc<String>,
    node_connected: Arc<RwLock<bool>>,
    admin_token: AdminToken,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

// =============================================================================
// Public API
// =============================================================================

/// Start the bounty board server in the background as a tokio task.
///
/// Returns the actual `SocketAddr` the server is listening on (useful when
/// the port is 0 for random assignment).
///
/// Uses the framework's `AppServer` for consistent infrastructure. The server
/// runs until the tokio runtime is shut down.
pub async fn start_server(config: ServerConfig) -> SocketAddr {
    let now_ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let state = AppState {
        board: BoardState::new(),
        root_history: Arc::new(RwLock::new(FederationRootHistory::with_initial_root(
            config.federation_root,
        ))),
        root_last_updated: Arc::new(RwLock::new(Some(Instant::now()))),
        engine: Arc::new(Mutex::new(PyanaEngine::new(EngineConfig::new(now_ts)))),
        node_url: Arc::new("none".to_string()),
        node_connected: Arc::new(RwLock::new(false)),
        // In-process server uses open admin mode (no token needed for tests/examples).
        admin_token: AdminToken::open(),
    };

    let app_routes = app_router().with_state(state);

    let app_config = AppConfig::default().with_listen(config.listen.to_string());

    let addr = AppServer::new(app_config)
        .service_name("pyana-bounty-board")
        .with_health()
        .with_cors()
        .routes(app_routes)
        .serve_background()
        .await
        .expect("failed to start bounty board server");

    addr
}

/// Build the application router for the in-process server.
fn app_router() -> Router<AppState> {
    Router::new()
        .route("/bounties", post(create_bounty))
        .route("/bounties", get(list_bounties))
        .route("/bounties/{id}/claim", post(claim_bounty))
        .route("/bounties/{id}/submit", post(submit_work))
        .route("/bounties/{id}/approve", post(approve_bounty))
        .route("/bounties/{id}/status", get(bounty_status))
        .route("/worker/bounties", get(worker_bounties))
        .route("/admin/height", post(advance_height))
        .route("/admin/expire", post(expire_bounties))
        .route("/admin/federation-root", post(set_federation_root))
}

// =============================================================================
// Handlers
// =============================================================================

async fn create_bounty(
    State(state): State<AppState>,
    Json(req): Json<CreateBountyRequest>,
) -> impl IntoResponse {
    let current_height = state.board.current_height().await;

    let issuer_cell = match bounty_id_from_hex(&req.issuer_cell) {
        Some(bytes) => CellId::from_bytes(bytes),
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid issuer_cell hex"})),
            );
        }
    };

    if req.deadline_height <= current_height {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "deadline must be in the future"})),
        );
    }

    let bounty_id = compute_bounty_id(&issuer_cell, &req.title, req.reward_amount, current_height);

    let bounty = Bounty {
        id: bounty_id,
        issuer_cell,
        title: req.title,
        description: req.description,
        reward_amount: req.reward_amount,
        reward_asset: req.reward_asset,
        deadline_height: req.deadline_height,
        qualification: req.qualification,
        status: BountyStatus::Open,
        reward_token: req.reward_token,
        created_at: current_height,
        tags: req.tags,
    };

    let id_hex = bounty_id_hex(&bounty_id);
    state.board.insert_bounty(bounty).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "open"
        })),
    )
}

async fn list_bounties(
    State(state): State<AppState>,
    Query(filter): Query<BountyFilter>,
) -> impl IntoResponse {
    let bounties = state.board.list_bounties(&filter).await;
    Json(json!({
        "bounties": bounties,
        "count": bounties.len()
    }))
}

async fn claim_bounty(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<ClaimRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    if !matches!(bounty.status, BountyStatus::Open) {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "bounty is not open for claims"})),
        );
    }

    let current_height = state.board.current_height().await;
    if bounty.deadline_height <= current_height {
        return (
            StatusCode::GONE,
            Json(json!({"error": "bounty has expired"})),
        );
    }

    let proof_bytes = req.qualification_proof.as_deref().unwrap_or(&[]);
    let engine = state.engine.lock().await;
    let root_history = state.root_history.read().await;
    match verify_qualification(&engine, &bounty.qualification, proof_bytes, &*root_history) {
        Ok(true) => {}
        Ok(false) => {
            return (
                StatusCode::FORBIDDEN,
                Json(json!({"error": "qualification proof does not meet threshold"})),
            );
        }
        Err(e) => {
            warn!(bounty_id = %id, error = %e, "qualification verification failed");
            return (
                StatusCode::FORBIDDEN,
                Json(json!({"error": format!("qualification rejected: {e}")})),
            );
        }
    }

    let new_status = BountyStatus::Claimed {
        worker_commitment: req.worker_commitment,
        claimed_at: current_height,
    };
    state.board.update_status(&bounty_id, new_status).await;

    info!(bounty_id = %id, "bounty claimed");

    (
        StatusCode::OK,
        Json(json!({
            "status": "claimed",
            "bounty_id": id
        })),
    )
}

async fn submit_work(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<SubmitRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    match &bounty.status {
        BountyStatus::Claimed {
            worker_commitment, ..
        } => {
            if *worker_commitment != req.worker_commitment {
                return (
                    StatusCode::FORBIDDEN,
                    Json(json!({"error": "worker commitment does not match claim"})),
                );
            }
        }
        _ => {
            return (
                StatusCode::CONFLICT,
                Json(json!({"error": "bounty is not in claimed state"})),
            );
        }
    }

    if req.completion_proof.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "completion proof must not be empty"})),
        );
    }

    let completion_proof_hash = *blake3::hash(&req.completion_proof).as_bytes();

    let new_status = BountyStatus::Submitted {
        worker_commitment: req.worker_commitment,
        completion_proof_hash,
    };
    state.board.update_status(&bounty_id, new_status).await;

    (
        StatusCode::OK,
        Json(json!({
            "status": "submitted",
            "bounty_id": id,
            "completion_proof_hash": bounty_id_hex(&completion_proof_hash)
        })),
    )
}

async fn approve_bounty(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<ApproveRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    let issuer_cell_hex = bounty_id_hex(bounty.issuer_cell.as_bytes());
    if req.issuer_cell != issuer_cell_hex {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the issuer can approve"})),
        );
    }

    let worker_commitment = match &bounty.status {
        BountyStatus::Submitted {
            worker_commitment, ..
        } => *worker_commitment,
        _ => {
            return (
                StatusCode::CONFLICT,
                Json(json!({"error": "bounty is not in submitted state"})),
            );
        }
    };

    state
        .board
        .update_status(&bounty_id, BountyStatus::Approved)
        .await;

    state
        .board
        .record_completion(worker_commitment, bounty_id)
        .await;

    let receipt_hash = *blake3::hash(&bounty_id).as_bytes();
    state
        .board
        .update_status(&bounty_id, BountyStatus::Paid { receipt_hash })
        .await;

    (
        StatusCode::OK,
        Json(json!({
            "status": "paid",
            "bounty_id": id,
            "receipt_hash": bounty_id_hex(&receipt_hash)
        })),
    )
}

async fn bounty_status(State(state): State<AppState>, Path(id): Path<String>) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            )
                .into_response();
        }
    };

    match state.board.get_bounty(&bounty_id).await {
        Some(bounty) => {
            let response = BountyStatusResponse {
                id: bounty_id_hex(&bounty.id),
                title: bounty.title,
                description: bounty.description,
                reward_amount: bounty.reward_amount,
                reward_asset: bounty.reward_asset,
                deadline_height: bounty.deadline_height,
                status: bounty.status,
                tags: bounty.tags,
                qualification: bounty.qualification,
                created_at: bounty.created_at,
            };
            (
                StatusCode::OK,
                Json(serde_json::to_value(&response).unwrap()),
            )
                .into_response()
        }
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "bounty not found"})),
        )
            .into_response(),
    }
}

async fn worker_bounties(
    State(state): State<AppState>,
    Query(params): Query<WorkerQuery>,
) -> impl IntoResponse {
    let commitment = match bounty_id_from_hex(&params.commitment) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid worker commitment hex"})),
            )
                .into_response();
        }
    };

    let active = state.board.worker_active_bounties(&commitment).await;
    let completed_count = state.board.worker_completed_count(&commitment).await;
    let completed_ids: Vec<String> = state
        .board
        .worker_bounty_ids(&commitment)
        .await
        .iter()
        .map(bounty_id_hex)
        .collect();

    Json(json!({
        "active": active,
        "completed_count": completed_count,
        "completed_ids": completed_ids
    }))
    .into_response()
}

#[derive(serde::Deserialize)]
struct WorkerQuery {
    commitment: String,
}

// =============================================================================
// Admin Endpoints (protected by framework AdminAuth extractor)
// =============================================================================

async fn advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.board.advance_height(delta).await;
    let new_height = state.board.current_height().await;
    Json(json!({"height": new_height}))
}

async fn expire_bounties(_auth: AdminAuth, State(state): State<AppState>) -> impl IntoResponse {
    let count = state.board.expire_stale_bounties().await;
    Json(json!({"expired": count}))
}

async fn set_federation_root(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let root_hex = match body["root"].as_str() {
        Some(s) => s,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "missing 'root' field (64 hex chars)"})),
            );
        }
    };

    let root_hex = root_hex.strip_prefix("0x").unwrap_or(root_hex);
    match hex_to_bytes32(root_hex) {
        Ok(root) => {
            if root == [0u8; 32] {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "refusing to set all-zeroes federation root"})),
                );
            }
            let mut history = state.root_history.write().await;
            history.push(root);
            drop(history);
            *state.root_last_updated.write().await = Some(Instant::now());
            (StatusCode::OK, Json(json!({"root": bytes32_to_hex(&root)})))
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        ),
    }
}
