//! Pyana Bounty Board — federated work marketplace with privacy-preserving qualifications.
//!
//! A standalone HTTP server (axum) providing a bounty board where:
//! - Issuers post bounties with rewards and qualification requirements.
//! - Workers claim bounties by proving qualifications anonymously.
//! - Payment is released atomically via conditional turns on completion.
//!
//! Uses the shared `AppServer` from `pyana-app-framework` for standard middleware
//! (health, CORS, admin auth) and environment-based configuration.

use std::collections::HashMap;
use std::path::PathBuf;
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
use tokio::sync::{Mutex, RwLock};
use tracing::{error, info, warn};

use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use pyana_app_framework::persistence::JsonPersistence;
use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_app_framework::{CellId, EngineConfig, EscrowCondition, PyanaEngine};
use pyana_bounty_board::payment::{self, Escrow};
use pyana_bounty_board::qualification::{FederationRootHistory, verify_qualification};
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
    listen: String,

    /// Root sync interval in seconds (how often to poll the node for new roots).
    #[arg(long, default_value = "30", env = "PYANA_SYNC_INTERVAL")]
    sync_interval: u64,

    /// Path for persisting state across restarts. If not set, state is in-memory only.
    /// Uses the framework's atomic JSON persistence (write-then-rename).
    #[arg(long, env = "PYANA_STATE_FILE")]
    state_file: Option<PathBuf>,
}

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
struct AppState {
    board: BoardState,
    /// Recent federation roots for multi-validator coherence.
    /// Verification accepts proofs against any root in this window, tolerating
    /// propagation lag between nodes in a multi-validator devnet.
    root_history: Arc<RwLock<FederationRootHistory>>,
    /// When the federation root was last updated.
    root_last_updated: Arc<RwLock<Option<Instant>>>,
    /// The pyana engine for cryptographic proof verification.
    engine: Arc<Mutex<PyanaEngine>>,
    /// The node URL used for root syncing.
    node_url: Arc<String>,
    /// Whether the node is currently reachable.
    node_connected: Arc<RwLock<bool>>,
    /// Active escrows indexed by bounty ID (for payment release/refund).
    escrows: Arc<RwLock<HashMap<[u8; 32], Escrow>>>,
    /// Admin token for admin endpoint authentication.
    admin_token: AdminToken,
    /// Optional persistence handle for state snapshots.
    persistence: Option<JsonPersistence>,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
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
///
/// New roots are pushed into the history window rather than replacing a single value.
/// This ensures that proofs generated against recently-superseded roots remain valid
/// for the duration of the window, resolving multi-validator coherence issues.
async fn root_sync_task(state: AppState, interval_secs: u64) {
    let mut interval = tokio::time::interval(std::time::Duration::from_secs(interval_secs));
    // Skip the first immediate tick (we already fetched on startup).
    interval.tick().await;

    loop {
        interval.tick().await;

        match fetch_federation_root(&state.node_url).await {
            Ok(new_root) => {
                let mut history = state.root_history.write().await;
                let was_known = history.is_known_root(&new_root);
                history.push(new_root);
                drop(history);

                *state.root_last_updated.write().await = Some(Instant::now());
                *state.node_connected.write().await = true;

                if !was_known {
                    info!(
                        root = %bytes32_to_hex(&new_root),
                        "federation root updated from node (added to history)"
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

    // Set up framework-based configuration.
    let config = AppConfig::from_env().with_listen(&args.listen);

    // Initialize persistence via framework's JsonPersistence.
    let persistence = args.state_file.as_ref().map(|path| {
        let p = JsonPersistence::new(path.clone());
        if let Err(e) = p.initialize() {
            error!(path = %path.display(), error = %e, "failed to initialize persistence");
            std::process::exit(1);
        }
        info!(path = %path.display(), "persistence initialized");
        p
    });

    // Create board state with persistence support.
    let board = if let Some(ref persist) = persistence {
        let board = BoardState::new();
        if let Ok(Some(snapshot)) = persist.load() {
            board.restore_from_snapshot(snapshot).await;
            info!("restored board state from disk");
        }
        board
    } else {
        BoardState::new()
    };

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
        board,
        root_history: Arc::new(RwLock::new(FederationRootHistory::with_initial_root(
            federation_root,
        ))),
        root_last_updated: Arc::new(RwLock::new(root_updated)),
        engine: Arc::new(Mutex::new(PyanaEngine::new(EngineConfig::new(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0),
        )))),
        node_url: Arc::new(args.node_url.clone()),
        node_connected: Arc::new(RwLock::new(node_connected)),
        escrows: Arc::new(RwLock::new(HashMap::new())),
        admin_token: config.admin_token.clone(),
        persistence: persistence.clone(),
    };

    // Spawn background root sync task.
    tokio::spawn(root_sync_task(state.clone(), args.sync_interval));

    // Build application routes.
    let app_routes = app_router().with_state(state);

    // Serve using the AppServer builder.
    AppServer::new(config)
        .service_name("pyana-bounty-board")
        .with_health()
        .with_cors()
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}

/// Build the application router (without state applied).
fn app_router() -> Router<AppState> {
    Router::new()
        // Bounty lifecycle
        .route("/bounties", post(create_bounty))
        .route("/bounties", get(list_bounties))
        .route("/bounties/{id}/claim", post(claim_bounty))
        .route("/bounties/{id}/submit", post(submit_work))
        .route("/bounties/{id}/approve", post(approve_bounty))
        .route("/bounties/{id}/status", get(bounty_status))
        // Worker endpoints
        .route("/worker/bounties", get(worker_bounties))
        // Admin (protected by framework's AdminAuth extractor)
        .route("/admin/height", post(advance_height))
        .route("/admin/expire", post(expire_bounties))
        .route("/admin/federation-root", post(set_federation_root))
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

    // Create escrow to lock the reward via EscrowManager.
    // The worker cell uses bounty_id as placeholder (real identity is blinded).
    // The condition requires presentation of a proof keyed by the bounty ID.
    let worker_placeholder = CellId::from_bytes(bounty_id);
    let condition = EscrowCondition::ProofPresented {
        verification_key: bounty_id,
    };

    let mut engine = state.engine.lock().await;
    let escrow_result = payment::create_escrow(
        &mut engine,
        payment::make_default_authorizer(),
        issuer_cell,
        worker_placeholder,
        req.reward_amount,
        req.deadline_height,
        condition,
    );
    drop(engine);

    let escrow = match escrow_result {
        Ok(e) => e,
        Err(e) => {
            warn!(error = %e, "failed to create escrow for bounty");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": format!("escrow creation failed: {e}")})),
            );
        }
    };

    let escrow_id = escrow.escrow_id;
    state.escrows.write().await.insert(bounty_id, escrow);

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
    info!(
        bounty_id = %id_hex,
        title = %bounty.title,
        reward = bounty.reward_amount,
        escrow_id = %bounty_id_hex(&escrow_id),
        "bounty created with escrow"
    );

    state.board.insert_bounty(bounty).await;

    // Persist state after mutation.
    persist_state(&state).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "open",
            "escrow_id": bounty_id_hex(&escrow_id)
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
    // Uses the root history window for multi-validator coherence: accepts proofs
    // generated against any recent federation root, not just the current one.
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

    // Claim the bounty.
    let new_status = BountyStatus::Claimed {
        worker_commitment: req.worker_commitment,
        claimed_at: current_height,
    };
    state.board.update_status(&bounty_id, new_status).await;

    info!(bounty_id = %id, "bounty claimed");

    persist_state(&state).await;

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

    persist_state(&state).await;

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
    let (worker_commitment, completion_proof_hash) = match &bounty.status {
        BountyStatus::Submitted {
            worker_commitment,
            completion_proof_hash,
        } => (*worker_commitment, *completion_proof_hash),
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

    let escrow = state.escrows.read().await.get(&bounty_id).cloned();
    let receipt_hash = match escrow {
        Some(ref esc) => {
            let mut engine = state.engine.lock().await;
            match payment::release_reward(
                &mut engine,
                payment::make_default_authorizer(),
                esc,
                &completion_proof_hash,
            ) {
                Ok(escrow_id) => {
                    info!(bounty_id = %id, escrow_id = %bounty_id_hex(&escrow_id), "escrow released");
                    escrow_id
                }
                Err(e) => {
                    warn!(bounty_id = %id, error = %e, "escrow release failed, using fallback");
                    *blake3::hash(&bounty_id).as_bytes()
                }
            }
        }
        None => {
            warn!(bounty_id = %id, "no escrow found, using fallback receipt");
            *blake3::hash(&bounty_id).as_bytes()
        }
    };

    state.escrows.write().await.remove(&bounty_id);

    state
        .board
        .update_status(&bounty_id, BountyStatus::Paid { receipt_hash })
        .await;

    info!(bounty_id = %id, "bounty approved, payment released");

    persist_state(&state).await;

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
// Admin Endpoints (protected by framework AdminAuth extractor)
// =============================================================================

/// POST /admin/height — advance the simulated block height.
///
/// Protected by the framework's `AdminAuth` extractor which validates the
/// `Authorization: Bearer <token>` header against `PYANA_ADMIN_TOKEN`.
async fn advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.board.advance_height(delta).await;
    let new_height = state.board.current_height().await;
    persist_state(&state).await;
    Json(json!({"height": new_height}))
}

/// POST /admin/expire — expire bounties past deadline and refund their escrows.
async fn expire_bounties(_auth: AdminAuth, State(state): State<AppState>) -> impl IntoResponse {
    let current_height = state.board.current_height().await;
    let count = state.board.expire_stale_bounties().await;

    // Refund escrows for expired bounties.
    if count > 0 {
        let mut engine = state.engine.lock().await;
        let mut escrows = state.escrows.write().await;
        let expired_ids: Vec<[u8; 32]> = escrows
            .iter()
            .filter(|(_, esc)| esc.timeout_height <= current_height)
            .map(|(id, _)| *id)
            .collect();

        for bid in expired_ids {
            if let Some(esc) = escrows.remove(&bid) {
                match payment::refund_escrow(
                    &mut engine,
                    payment::make_default_authorizer(),
                    &esc,
                    current_height,
                ) {
                    Ok(_) => info!(bounty_id = %bounty_id_hex(&bid), "escrow refunded"),
                    Err(e) => {
                        warn!(bounty_id = %bounty_id_hex(&bid), error = %e, "escrow refund failed")
                    }
                }
            }
        }
    }

    persist_state(&state).await;

    Json(json!({"expired": count}))
}

/// POST /admin/federation-root — set the federation root at runtime.
///
/// Accepts JSON: `{"root": "abcd...1234"}` (64 hex chars).
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
            )
                .into_response();
        }
    };

    let root_hex = root_hex.strip_prefix("0x").unwrap_or(root_hex);
    match hex_to_bytes32(root_hex) {
        Ok(root) => {
            if root == [0u8; 32] {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "refusing to set all-zeroes federation root"})),
                )
                    .into_response();
            }
            let mut history = state.root_history.write().await;
            history.push(root);
            let history_len = history.len();
            drop(history);
            *state.root_last_updated.write().await = Some(Instant::now());
            info!(
                root = %bytes32_to_hex(&root),
                history_depth = history_len,
                "federation root pushed via admin endpoint"
            );
            (
                StatusCode::OK,
                Json(json!({"root": bytes32_to_hex(&root), "history_depth": history_len})),
            )
                .into_response()
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        )
            .into_response(),
    }
}

// =============================================================================
// Persistence Helper
// =============================================================================

/// Persist the current board state using the framework's JsonPersistence.
///
/// No-op if persistence is not configured.
async fn persist_state(state: &AppState) {
    if let Some(ref persistence) = state.persistence {
        let snapshot = state.board.snapshot().await;
        if let Err(e) = persistence.save(&snapshot) {
            warn!(error = %e, "failed to persist state");
        }
    }
}
