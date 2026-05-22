//! Pyana Bounty Board — federated work marketplace with privacy-preserving qualifications.
//!
//! A standalone HTTP server (axum) providing a bounty board where:
//! - Issuers post bounties with rewards and qualification requirements.
//! - Workers claim bounties by proving qualifications anonymously.
//! - Payment is released atomically via conditional turns on completion.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
};
use serde_json::json;
use tracing::{info, warn};

use pyana_bounty_board::qualification::verify_qualification;
use pyana_bounty_board::state::BoardState;
use pyana_bounty_board::{
    ApproveRequest, Bounty, BountyFilter, BountyStatus, BountyStatusResponse, BountySummary,
    ClaimRequest, CompletionEvidence, CreateBountyRequest, QualificationRequirement,
    SerializedToken, SubmitRequest, bounty_id_from_hex, bounty_id_hex, compute_bounty_id,
    qualification_label, status_label,
};
use pyana_types::CellId;

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
struct AppState {
    board: BoardState,
    /// The federation root used for membership/qualification checks.
    /// In production this would be fetched from the federation periodically.
    federation_root: [u8; 32],
}

// =============================================================================
// Main
// =============================================================================

#[tokio::main]
async fn main() {
    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_target(false)
        .with_level(true)
        .init();

    let state = AppState {
        board: BoardState::new(),
        federation_root: [0u8; 32], // placeholder; would come from federation attestation
    };

    let app = Router::new()
        // Bounty lifecycle
        .route("/bounties", post(create_bounty))
        .route("/bounties", get(list_bounties))
        .route("/bounties/{id}/claim", post(claim_bounty))
        .route("/bounties/{id}/submit", post(submit_work))
        .route("/bounties/{id}/approve", post(approve_bounty))
        .route("/bounties/{id}/status", get(bounty_status))
        // Worker endpoints
        .route("/worker/bounties", get(worker_bounties))
        // Admin / utility
        .route("/admin/height", post(advance_height))
        .route("/admin/expire", post(expire_bounties))
        .route("/health", get(health_check))
        .with_state(state);

    let addr = SocketAddr::from(([127, 0, 0, 1], 3030));
    info!("pyana bounty board listening on {addr}");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind");

    axum::serve(listener, app).await.expect("server error");
}

// =============================================================================
// Handlers
// =============================================================================

/// POST /bounties — create a new bounty.
async fn create_bounty(
    State(state): State<AppState>,
    Json(req): Json<CreateBountyRequest>,
) -> impl IntoResponse {
    let current_height = state.board.current_height().await;

    // Parse the issuer cell ID from hex.
    let issuer_cell = match bounty_id_from_hex(&req.issuer_cell) {
        Some(bytes) => CellId::from_bytes(bytes),
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid issuer_cell hex"})),
            );
        }
    };

    // Validate deadline is in the future.
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
    info!(bounty_id = %id_hex, title = %bounty.title, reward = bounty.reward_amount, "bounty created");

    state.board.insert_bounty(bounty).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "open"
        })),
    )
}

/// GET /bounties — list open bounties with optional filters.
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

/// POST /bounties/:id/claim — worker claims a bounty with qualification proof.
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

    // Must be open.
    if !matches!(bounty.status, BountyStatus::Open) {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "bounty is not open for claims"})),
        );
    }

    // Check deadline.
    let current_height = state.board.current_height().await;
    if bounty.deadline_height <= current_height {
        return (
            StatusCode::GONE,
            Json(json!({"error": "bounty has expired"})),
        );
    }

    // Verify qualification proof.
    let proof_bytes = req.qualification_proof.as_deref().unwrap_or(&[]);
    match verify_qualification(&bounty.qualification, proof_bytes, state.federation_root) {
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

    // Claim the bounty.
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

/// POST /bounties/:id/submit — worker submits completed work.
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

    // Must be claimed by this worker.
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

    // Validate completion proof is non-empty.
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

    info!(bounty_id = %id, "work submitted");

    (
        StatusCode::OK,
        Json(json!({
            "status": "submitted",
            "bounty_id": id,
            "completion_proof_hash": bounty_id_hex(&completion_proof_hash)
        })),
    )
}

/// POST /bounties/:id/approve — issuer approves completion and triggers payment.
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

    // Verify the approver is the issuer.
    let issuer_cell_hex = bounty_id_hex(bounty.issuer_cell.as_bytes());
    if req.issuer_cell != issuer_cell_hex {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the issuer can approve"})),
        );
    }

    // Must be in submitted state.
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

    // Mark as approved.
    state
        .board
        .update_status(&bounty_id, BountyStatus::Approved)
        .await;

    // Record completion for the worker's standing.
    state
        .board
        .record_completion(worker_commitment, bounty_id)
        .await;

    info!(bounty_id = %id, "bounty approved, payment released");

    // In a full implementation, this would resolve the conditional turn and produce
    // a TurnReceipt. For now we mark as paid with a deterministic receipt hash.
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

/// GET /bounties/:id/status — check bounty status.
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

/// GET /worker/bounties — worker's active and completed bounties.
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

/// Query parameters for worker bounty listing.
#[derive(serde::Deserialize)]
struct WorkerQuery {
    commitment: String,
}

// =============================================================================
// Admin / Utility Endpoints
// =============================================================================

/// POST /admin/height — advance the simulated block height.
async fn advance_height(
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.board.advance_height(delta).await;
    let new_height = state.board.current_height().await;
    Json(json!({"height": new_height}))
}

/// POST /admin/expire — expire all bounties past their deadline.
async fn expire_bounties(State(state): State<AppState>) -> impl IntoResponse {
    let count = state.board.expire_stale_bounties().await;
    Json(json!({"expired": count}))
}

/// GET /health — health check.
async fn health_check() -> impl IntoResponse {
    Json(json!({"status": "ok", "service": "pyana-bounty-board"}))
}
