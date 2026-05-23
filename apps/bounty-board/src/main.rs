//! Pyana Bounty Board — federated work marketplace with privacy-preserving qualifications.
//!
//! A standalone HTTP server (axum) providing a bounty board where:
//! - Issuers post bounties with rewards and qualification requirements.
//! - Workers claim bounties by proving qualifications anonymously.
//! - Payment is released atomically via conditional turns on completion.

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
use clap::Parser;
use serde_json::json;
use tokio::sync::RwLock;
use tracing::{error, info, warn};

use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use pyana_app_framework::{CellId, EngineConfig, PyanaEngine};
use pyana_bounty_board::qualification::verify_qualification;
use pyana_bounty_board::state::BoardState;
use pyana_bounty_board::{
    ApproveRequest, Bounty, BountyFilter, BountyStatus, BountyStatusResponse, ClaimRequest,
    CreateBountyRequest, SubmitRequest, bounty_id_from_hex, bounty_id_hex, compute_bounty_id,
};

// =============================================================================
// CLI Arguments
// =============================================================================

/// Pyana Bounty Board — federated work marketplace with privacy-preserving qualifications.
#[derive(Parser, Debug)]
#[command(name = "bounty-board")]
struct Args {
    /// Federation root hash (64 hex chars). If not provided, fetches from the node.
    #[arg(long, env = "PYANA_FEDERATION_ROOT")]
    federation_root: Option<String>,

    /// URL of a running pyana-node to fetch the federation root from.
    /// The app will query /status and /federation/roots on startup and
    /// periodically sync the latest attested root.
    #[arg(long, default_value = "http://127.0.0.1:8420", env = "PYANA_NODE_URL")]
    node_url: String,

    /// Listen address.
    #[arg(long, default_value = "127.0.0.1:3030", env = "PYANA_LISTEN")]
    listen: SocketAddr,

    /// Root sync interval in seconds (how often to poll the node for new roots).
    #[arg(long, default_value = "30", env = "PYANA_SYNC_INTERVAL")]
    sync_interval: u64,
}

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
struct AppState {
    board: BoardState,
    /// The federation root used for membership/qualification checks.
    federation_root: Arc<RwLock<[u8; 32]>>,
    /// When the federation root was last updated.
    root_last_updated: Arc<RwLock<Option<Instant>>>,
    /// The pyana engine for cryptographic proof verification.
    engine: Arc<RwLock<PyanaEngine>>,
    /// The node URL used for root syncing.
    node_url: Arc<String>,
    /// Whether the node is currently reachable.
    node_connected: Arc<RwLock<bool>>,
}

// =============================================================================
// Node Client
// =============================================================================

/// Response shape from the node's GET /status endpoint.
#[derive(serde::Deserialize)]
struct NodeStatusResponse {
    healthy: bool,
    latest_height: u64,
    #[allow(dead_code)]
    peer_count: usize,
}

/// Response shape from the node's GET /federation/roots endpoint.
#[derive(serde::Deserialize)]
struct AttestedRootInfo {
    #[allow(dead_code)]
    height: u64,
    merkle_root: String,
    #[allow(dead_code)]
    timestamp: i64,
    #[allow(dead_code)]
    signatures: usize,
}

/// Fetch the latest federation root from a running node.
///
/// Queries `/federation/roots` and returns the merkle_root of the highest-height
/// attested root. Falls back to `/status` to verify the node is reachable.
async fn fetch_federation_root(node_url: &str) -> Result<[u8; 32], String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(5))
        .build()
        .map_err(|e| format!("failed to build HTTP client: {e}"))?;

    // First verify the node is healthy.
    let status_url = format!("{node_url}/status");
    let status: NodeStatusResponse = client
        .get(&status_url)
        .send()
        .await
        .map_err(|e| format!("node unreachable at {status_url}: {e}"))?
        .json()
        .await
        .map_err(|e| format!("invalid status response: {e}"))?;

    if !status.healthy {
        return Err("node reports unhealthy status".to_string());
    }

    // Fetch attested roots.
    let roots_url = format!("{node_url}/federation/roots");
    let roots: Vec<AttestedRootInfo> = client
        .get(&roots_url)
        .send()
        .await
        .map_err(|e| format!("failed to fetch federation roots: {e}"))?
        .json()
        .await
        .map_err(|e| format!("invalid federation roots response: {e}"))?;

    if roots.is_empty() {
        return Err(format!(
            "node at height {} has no attested roots yet",
            status.latest_height
        ));
    }

    // Use the last root (highest height, the list is ordered).
    let latest = roots.last().unwrap();
    let root = hex_to_bytes32(&latest.merkle_root)
        .map_err(|e| format!("invalid merkle_root hex from node: {e}"))?;

    if root == [0u8; 32] {
        return Err("node returned zeroed federation root".to_string());
    }

    Ok(root)
}

/// Background task that periodically syncs the federation root from the node.
async fn root_sync_task(state: AppState, interval_secs: u64) {
    let mut interval = tokio::time::interval(std::time::Duration::from_secs(interval_secs));
    // Skip the first immediate tick (we already fetched on startup).
    interval.tick().await;

    loop {
        interval.tick().await;

        match fetch_federation_root(&state.node_url).await {
            Ok(new_root) => {
                let old_root = *state.federation_root.read().await;
                *state.federation_root.write().await = new_root;
                *state.root_last_updated.write().await = Some(Instant::now());
                *state.node_connected.write().await = true;

                if new_root != old_root {
                    info!(
                        root = %bytes32_to_hex(&new_root),
                        "federation root updated from node"
                    );
                }
            }
            Err(e) => {
                *state.node_connected.write().await = false;
                warn!(error = %e, "failed to sync federation root from node");
            }
        }
    }
}

// =============================================================================
// Main
// =============================================================================

/// Parse a 64-char hex string into a [u8; 32] federation root.
fn parse_federation_root(hex: &str) -> Result<[u8; 32], String> {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    hex_to_bytes32(hex).map_err(|e| format!("invalid federation root hex: {e}"))
}

#[tokio::main]
async fn main() {
    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_target(false)
        .with_level(true)
        .init();

    let args = Args::parse();

    // Resolve federation root: explicit > node fetch > refuse to start.
    let (federation_root, root_updated) = match &args.federation_root {
        Some(hex) => match parse_federation_root(hex) {
            Ok(root) => {
                info!(
                    root = %bytes32_to_hex(&root),
                    "federation root configured (explicit)"
                );
                (root, Some(Instant::now()))
            }
            Err(e) => {
                error!("{e}");
                std::process::exit(1);
            }
        },
        None => {
            // Fetch from the node (required).
            info!(node_url = %args.node_url, "fetching federation root from node...");
            match fetch_federation_root(&args.node_url).await {
                Ok(root) => {
                    info!(
                        root = %bytes32_to_hex(&root),
                        node_url = %args.node_url,
                        "federation root fetched from node"
                    );
                    (root, Some(Instant::now()))
                }
                Err(e) => {
                    error!(
                        "cannot reach node at {}: {e}\n\
                         A federation root is required for verification. Either:\n\
                         - Start a devnet node (pyana-node) at the default address, or\n\
                         - Pass --node-url pointing to a running node, or\n\
                         - Pass --federation-root explicitly.",
                        args.node_url
                    );
                    std::process::exit(1);
                }
            }
        }
    };

    let node_connected = federation_root != [0u8; 32];

    let state = AppState {
        board: BoardState::new(),
        federation_root: Arc::new(RwLock::new(federation_root)),
        root_last_updated: Arc::new(RwLock::new(root_updated)),
        engine: Arc::new(RwLock::new(PyanaEngine::new(EngineConfig::new(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0),
        )))),
        node_url: Arc::new(args.node_url.clone()),
        node_connected: Arc::new(RwLock::new(node_connected)),
    };

    // Spawn background root sync task.
    tokio::spawn(root_sync_task(state.clone(), args.sync_interval));

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
        .route("/admin/federation-root", post(set_federation_root))
        .route("/health", get(health_check))
        .with_state(state);

    let addr = args.listen;
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

    // Verify qualification proof (real cryptographic verification).
    let proof_bytes = req.qualification_proof.as_deref().unwrap_or(&[]);
    let engine = state.engine.read().await;
    let federation_root = *state.federation_root.read().await;
    match verify_qualification(&engine, &bounty.qualification, proof_bytes, federation_root) {
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

/// POST /admin/federation-root — set the federation root at runtime.
///
/// Accepts JSON: `{"root": "abcd...1234"}` (64 hex chars).
async fn set_federation_root(
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
            *state.federation_root.write().await = root;
            *state.root_last_updated.write().await = Some(Instant::now());
            info!(root = %bytes32_to_hex(&root), "federation root updated via admin endpoint");
            (StatusCode::OK, Json(json!({"root": bytes32_to_hex(&root)})))
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        ),
    }
}

/// GET /health — comprehensive health check.
///
/// Returns app status, federation root info, bounty counts, and node connection status.
async fn health_check(State(state): State<AppState>) -> impl IntoResponse {
    let federation_root = *state.federation_root.read().await;
    let root_last_updated = *state.root_last_updated.read().await;
    let node_connected = *state.node_connected.read().await;

    let root_age_secs = root_last_updated.map(|t| t.elapsed().as_secs());

    // Count bounties by status.
    let all_bounties = state
        .board
        .list_bounties(&BountyFilter::default())
        .await;
    let open = all_bounties.iter().filter(|b| b.status == "open").count();
    let claimed = all_bounties.iter().filter(|b| b.status == "claimed").count();
    let submitted = all_bounties
        .iter()
        .filter(|b| b.status == "submitted")
        .count();
    let paid = all_bounties.iter().filter(|b| b.status == "paid").count();
    let expired = all_bounties
        .iter()
        .filter(|b| b.status == "expired")
        .count();

    let root_is_live = federation_root != [0u8; 32];

    Json(json!({
        "status": "running",
        "service": "pyana-bounty-board",
        "federation_root": {
            "value": bytes32_to_hex(&federation_root),
            "live": root_is_live,
            "last_updated_secs_ago": root_age_secs,
        },
        "bounties": {
            "total": all_bounties.len(),
            "open": open,
            "claimed": claimed,
            "submitted": submitted,
            "paid": paid,
            "expired": expired,
        },
        "node": {
            "url": state.node_url.as_str(),
            "connected": node_connected,
        }
    }))
}
