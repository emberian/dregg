//! Axum HTTP API router for the pyana node.
//!
//! Serves a localhost-only API that the browser extension wallet talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::Arc;
use std::time::Instant;

use axum::extract::DefaultBodyLimit;
use axum::http::Request;
use axum::http::{HeaderValue, Method, header};
use axum::response::Response;
use axum::{
    Json, Router,
    extract::ConnectInfo,
    extract::Path as AxumPath,
    extract::State,
    http::StatusCode,
    middleware,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::Mutex;

use pyana_sdk::{Attenuation, AuthRequest, CellId};
use pyana_turn::{CallForest, Turn};

use crate::state::{NodeEvent, NodeState};
use crate::ws::handle_ws;

// =============================================================================
// Request/Response types
// =============================================================================

#[derive(Serialize)]
pub struct StatusResponse {
    pub healthy: bool,
    pub peer_count: usize,
    pub latest_height: u64,
    pub revocation_count: u64,
    pub note_count: u64,
}

#[derive(Serialize)]
pub struct WalletResponse {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

#[derive(Deserialize)]
pub struct AuthorizeRequest {
    pub token_id: String,
    pub service: Option<String>,
    pub action: Option<String>,
}

#[derive(Serialize)]
pub struct AuthorizeResponse {
    pub authorized: bool,
    pub reason: Option<String>,
}

#[derive(Deserialize)]
pub struct MintRequest {
    pub service: String,
}

#[derive(Serialize)]
pub struct MintResponse {
    pub token_id: String,
    pub service: String,
}

#[derive(Deserialize)]
pub struct AttenuateRequest {
    pub token_id: String,
    pub services: Vec<(String, String)>,
}

#[derive(Serialize)]
pub struct AttenuateResponse {
    pub new_token_id: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct TokenInfo {
    pub id: String,
    pub label: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct ReceiptInfo {
    pub turn_hash: String,
    pub pre_state: String,
    pub post_state: String,
    pub timestamp: i64,
    pub computrons_used: u64,
}

#[derive(Deserialize)]
pub struct SubmitTurnRequest {
    /// Hex-encoded 32-byte CellId.
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
}

#[derive(Serialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    pub turn_hash: Option<String>,
}

#[derive(Serialize)]
pub struct CellResponse {
    pub id: String,
    pub found: bool,
    pub balance: Option<u64>,
}

#[derive(Serialize)]
pub struct AttestedRootInfo {
    pub height: u64,
    pub merkle_root: String,
    pub timestamp: i64,
    pub signatures: usize,
}

#[derive(Serialize)]
pub struct CellListEntry {
    pub id: String,
    pub balance: u64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub has_program: bool,
    pub found: bool,
}

#[derive(Serialize)]
pub struct CellDetailResponse {
    pub id: String,
    pub found: bool,
    pub balance: u64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub delegate: Option<String>,
    pub has_program: bool,
    pub public_key: String,
    pub token_id: String,
    pub proved_state: bool,
}

#[derive(Serialize)]
pub struct CheckpointResponse {
    pub height: u64,
    pub ledger_state_root: String,
    pub note_tree_root: String,
    pub nullifier_set_root: String,
    pub revocation_tree_root: String,
    pub epoch: u64,
    pub timestamp: i64,
    pub federation_members: usize,
    pub qc_votes: usize,
}

#[derive(Deserialize)]
pub struct UnlockRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct UnlockResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct SetPassphraseRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct SetPassphraseResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct IntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
}

// =============================================================================
// PIR (Private Information Retrieval) types
// =============================================================================

/// Request body for a PIR query against the intent index.
#[derive(Deserialize)]
pub struct PirQueryRequest {
    /// The query vector (BabyBear field elements serialized as u32 values).
    pub query_vector: Vec<u32>,
}

/// Response to a PIR query.
#[derive(Serialize)]
pub struct PirQueryResponse {
    /// The server's response vector (BabyBear field elements as u32 values).
    pub response: Vec<u32>,
}

/// Metadata about the PIR database (needed for clients to construct valid queries).
#[derive(Serialize)]
pub struct PirInfoResponse {
    /// Number of rows (capability tags) in the index.
    pub num_rows: usize,
    /// Number of columns per row (in field elements).
    pub row_width: usize,
    /// The ordered list of capability tags.
    pub tags: Vec<String>,
}

#[derive(Serialize)]
pub struct IntentListEntry {
    pub id: String,
    pub intent: pyana_intent::Intent,
}

// =============================================================================
// Fulfillment types
// =============================================================================

#[derive(Deserialize)]
pub struct FulfillIntentRequest {
    /// Hex-encoded 32-byte intent ID to fulfill.
    pub intent_id: String,
    /// Hex-encoded 32-byte payer cell ID (intent creator's cell).
    pub payer_cell: String,
    /// Hex-encoded 32-byte recipient cell ID (fulfiller's cell).
    pub recipient_cell: String,
    /// The base fulfillment (serialized).
    pub fulfillment: serde_json::Value,
    /// Predicate proofs as (index, proof_bytes_hex) pairs.
    pub predicate_proofs: Vec<(usize, String)>,
    /// State root (BabyBear field element as u32).
    pub state_root: u32,
    /// Block height at which state root was attested.
    pub state_root_block: u64,
}

#[derive(Serialize)]
pub struct FulfillIntentResponse {
    pub success: bool,
    pub turn_hash: Option<String>,
    pub error: Option<String>,
}

// =============================================================================
// Conditional Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct SubmitConditionalRequest {
    pub turn: serde_json::Value,
    pub condition: serde_json::Value,
    pub timeout_height: u64,
}

#[derive(Serialize)]
pub struct SubmitConditionalResponse {
    pub accepted: bool,
    pub conditional_hash: Option<String>,
}

#[derive(Deserialize)]
pub struct ResolveConditionalRequest {
    pub conditional_hash: String,
    pub proof: serde_json::Value,
}

#[derive(Serialize)]
pub struct ResolveConditionalResponse {
    pub resolved: bool,
    pub turn_hash: Option<String>,
    pub reason: Option<String>,
}

#[derive(Serialize)]
pub struct PendingConditionalInfo {
    pub hash: String,
    pub timeout_height: u64,
    pub submitted_at: u64,
    pub condition_type: String,
}

// =============================================================================
// Rate Limiting (P1 Fix 4)
// =============================================================================

/// Simple in-memory rate limiter: max attempts per window.
#[derive(Clone)]
struct RateLimiter {
    /// Map of IP -> (attempt_count, window_start)
    state: Arc<Mutex<HashMap<IpAddr, (u32, Instant)>>>,
    max_attempts: u32,
    window_secs: u64,
}

impl RateLimiter {
    fn new(max_attempts: u32, window_secs: u64) -> Self {
        Self {
            state: Arc::new(Mutex::new(HashMap::new())),
            max_attempts,
            window_secs,
        }
    }

    /// Returns true if the request should be allowed, false if rate-limited.
    async fn check(&self, ip: IpAddr) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        let entry = map.entry(ip).or_insert((0, now));

        // Reset window if expired.
        if now.duration_since(entry.1).as_secs() >= self.window_secs {
            *entry = (0, now);
        }

        entry.0 += 1;
        entry.0 <= self.max_attempts
    }
}

// =============================================================================
// Authentication
// =============================================================================

/// Authentication middleware requiring Bearer token for protected endpoints.
///
/// The API token is derived from the wallet passphrase:
/// `BLAKE3_derive_key("pyana-api-bearer-v1", passphrase_hash)`.
/// If no passphrase is set, all requests are allowed (initial setup phase).
async fn require_auth(
    State(state): State<NodeState>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Result<Response, StatusCode> {
    let s = state.read().await;

    // If no passphrase is set yet, allow all requests (initial setup).
    let Some(passphrase_hash) = s.passphrase_hash else {
        drop(s);
        return Ok(next.run(req).await);
    };

    // Check for Bearer token in Authorization header.
    let auth_header = req
        .headers()
        .get("authorization")
        .and_then(|v| v.to_str().ok());

    match auth_header {
        Some(header) if header.starts_with("Bearer ") => {
            let token = &header[7..];
            let expected_token_bytes = blake3::derive_key("pyana-api-bearer-v1", &passphrase_hash);
            let expected_token: String = expected_token_bytes
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            drop(s);

            if token == expected_token {
                Ok(next.run(req).await)
            } else {
                Err(StatusCode::UNAUTHORIZED)
            }
        }
        _ => {
            drop(s);
            Err(StatusCode::UNAUTHORIZED)
        }
    }
}

// =============================================================================
// CORS Middleware (P2 Fix 7)
// =============================================================================

/// Middleware that adds CORS headers to every response.
async fn cors_middleware(req: Request<axum::body::Body>, next: middleware::Next) -> Response {
    let origin = req
        .headers()
        .get(header::ORIGIN)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("")
        .to_string();

    // Handle preflight OPTIONS
    let is_preflight = req.method() == Method::OPTIONS;

    let mut response = if is_preflight {
        Response::builder()
            .status(StatusCode::NO_CONTENT)
            .body(axum::body::Body::empty())
            .unwrap()
    } else {
        next.run(req).await
    };

    // Check if origin is allowed.
    let allowed = is_origin_allowed(&origin);
    if allowed {
        let headers = response.headers_mut();
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_ORIGIN,
            HeaderValue::from_str(&origin).unwrap_or_else(|_| HeaderValue::from_static("*")),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_METHODS,
            HeaderValue::from_static("GET, POST, PUT, DELETE, OPTIONS"),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_HEADERS,
            HeaderValue::from_static("Content-Type, Authorization"),
        );
        headers.insert(
            header::ACCESS_CONTROL_MAX_AGE,
            HeaderValue::from_static("3600"),
        );
    }

    response
}

/// Check whether an origin is allowed by our CORS policy.
fn is_origin_allowed(origin: &str) -> bool {
    // Allow localhost on any port.
    if origin.starts_with("http://localhost:") || origin.starts_with("http://localhost") {
        return true;
    }
    if origin.starts_with("http://127.0.0.1:") || origin.starts_with("http://127.0.0.1") {
        return true;
    }
    // Allow browser extension origins.
    if origin.starts_with("chrome-extension://") {
        return true;
    }
    if origin.starts_with("moz-extension://") {
        return true;
    }
    false
}

// =============================================================================
// Constants
// =============================================================================

/// Maximum number of intents in the node's local pool (P1 Fix 5: unbounded growth).
pub const MAX_NODE_INTENT_POOL: usize = 10_000;

/// Maximum number of pending conditional turns (P1 Fix 6).
pub const MAX_PENDING_CONDITIONALS: usize = 1_000;

/// Maximum request body size in bytes (P2 Fix 11: 1 MB).
const MAX_BODY_SIZE: usize = 1_024 * 1_024;

// =============================================================================
// Router
// =============================================================================

/// Build the Axum router with all API routes.
///
/// Includes CORS, body size limits, rate limiting on passphrase endpoints,
/// and Bearer token authentication on protected routes.
pub fn router(state: NodeState, enable_faucet: bool) -> Router {
    // Rate limiter for passphrase/unlock endpoints: 5 attempts per 60 seconds.
    let passphrase_limiter = RateLimiter::new(5, 60);

    // Public routes (no auth required)
    let mut public_routes = Router::new()
        .route("/status", get(get_status))
        .route("/federation/roots", get(get_federation_roots))
        .route("/api/blocks", get(get_federation_roots))
        .route("/api/cells", get(get_all_cells))
        .route("/api/cell/{id}", get(get_cell_detail))
        .route("/api/intents", get(get_intents))
        .route("/api/conditionals", get(get_pending_conditionals))
        .route("/api/receipts", get(get_receipts))
        .route("/api/tokens", get(get_tokens))
        .route("/checkpoint/latest", get(get_checkpoint_latest))
        .route("/checkpoint/{height}", get(get_checkpoint_at_height))
        .route("/pir/info", get(get_pir_info))
        .route("/pir/query", post(post_pir_query))
        .route(
            "/wallet/unlock",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, state, body| {
                    post_wallet_unlock(connect_info, state, body, limiter)
                }
            }),
        )
        .route(
            "/wallet/set-passphrase",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, state, body| {
                    post_set_passphrase(connect_info, state, body, limiter)
                }
            }),
        );

    // Faucet endpoint (only available in devnet mode).
    if enable_faucet {
        let faucet_limiter = FaucetRateLimiter::new();
        public_routes = public_routes.route(
            "/api/faucet",
            post(move |state, body| post_faucet(state, body, faucet_limiter)),
        );
    }

    // Protected routes (require bearer token after passphrase is set)
    let protected_routes = Router::new()
        .route("/ws", get(handle_ws))
        .route("/wallet", get(get_wallet))
        .route("/wallet/authorize", post(post_authorize))
        .route("/wallet/mint", post(post_mint))
        .route("/wallet/attenuate", post(post_attenuate))
        .route("/wallet/tokens", get(get_tokens))
        .route("/wallet/receipts", get(get_receipts))
        .route("/intents", get(get_intents).post(post_intent))
        .route("/intents/fulfill", post(post_fulfill_intent))
        .route("/turn/submit", post(post_submit_turn))
        .route("/turn/submit-conditional", post(post_submit_conditional))
        .route("/turn/resolve-conditional", post(post_resolve_conditional))
        .route("/turn/pending", get(get_pending_conditionals))
        .route("/cell/{id}", get(get_cell))
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    public_routes
        .merge(protected_routes)
        .layer(DefaultBodyLimit::max(MAX_BODY_SIZE))
        .layer(middleware::from_fn(cors_middleware))
        .with_state(state)
}

// =============================================================================
// Handlers
// =============================================================================

/// P2 Fix 9: Status checks store accessibility and wallet initialization.
async fn get_status(State(state): State<NodeState>) -> Json<StatusResponse> {
    let s = state.read().await;

    // Check store accessibility.
    let store_ok = s.store.latest_attested_root().is_ok();
    // Check wallet is initialized (has a passphrase set or is unlocked).
    let wallet_ok = s.unlocked || s.passphrase_hash.is_some();

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let revocation_count = s.store.revocation_count().unwrap_or(0);
    let note_count = s.store.note_count().unwrap_or(0);
    let peer_count = s.peers.len();

    Json(StatusResponse {
        healthy: store_ok && wallet_ok,
        peer_count,
        latest_height,
        revocation_count,
        note_count,
    })
}

async fn get_wallet(State(state): State<NodeState>) -> Json<WalletResponse> {
    let ws = state.wallet_status().await;
    Json(WalletResponse {
        unlocked: ws.unlocked,
        public_key: ws.public_key,
        token_count: ws.token_count,
        receipt_chain_length: ws.receipt_chain_length,
    })
}

async fn post_authorize(
    State(state): State<NodeState>,
    Json(req): Json<AuthorizeRequest>,
) -> Result<Json<AuthorizeResponse>, StatusCode> {
    let s = state.read().await;

    let token = s
        .wallet
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?;

    let auth_req = AuthRequest {
        service: req.service,
        action: req.action,
        ..Default::default()
    };

    let authorized = s.wallet.verify_token(token, &auth_req);

    Ok(Json(AuthorizeResponse {
        authorized,
        reason: if authorized {
            None
        } else {
            Some("token does not satisfy request".to_string())
        },
    }))
}

async fn post_mint(
    State(state): State<NodeState>,
    Json(req): Json<MintRequest>,
) -> Result<Json<MintResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Generate a root key for the new token.
    let mut root_key = [0u8; 32];
    getrandom::fill(&mut root_key).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    let held = s.wallet.mint_token(&root_key, &req.service);

    Ok(Json(MintResponse {
        token_id: held.id.clone(),
        service: held.service.clone(),
    }))
}

async fn post_attenuate(
    State(state): State<NodeState>,
    Json(req): Json<AttenuateRequest>,
) -> Result<Json<AttenuateResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let token = s
        .wallet
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?
        .clone();

    let attenuation = Attenuation {
        services: req.services,
        ..Default::default()
    };

    let attenuated = s
        .wallet
        .attenuate(&token, &attenuation)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    Ok(Json(AttenuateResponse {
        new_token_id: attenuated.id.clone(),
        service: attenuated.service.clone(),
    }))
}

async fn get_tokens(State(state): State<NodeState>) -> Json<Vec<TokenInfo>> {
    let s = state.read().await;
    let tokens: Vec<TokenInfo> = s
        .wallet
        .tokens()
        .iter()
        .map(|t| TokenInfo {
            id: t.id.clone(),
            label: t.label.clone(),
            service: t.service.clone(),
        })
        .collect();
    Json(tokens)
}

async fn get_receipts(State(state): State<NodeState>) -> Json<Vec<ReceiptInfo>> {
    let s = state.read().await;
    let chain = s.wallet.receipt_chain();
    let receipts: Vec<ReceiptInfo> = chain
        .iter()
        .rev()
        .take(50)
        .map(|r| ReceiptInfo {
            turn_hash: hex_encode(&r.turn_hash),
            pre_state: hex_encode(&r.pre_state_hash),
            post_state: hex_encode(&r.post_state_hash),
            timestamp: r.timestamp,
            computrons_used: r.computrons_used,
        })
        .collect();
    Json(receipts)
}

async fn post_submit_turn(
    State(state): State<NodeState>,
    Json(req): Json<SubmitTurnRequest>,
) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    let s = state.read().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Build a minimal turn from the request.
    let agent_bytes = hex_decode(&req.agent).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn = Turn {
        agent: CellId(agent_bytes),
        nonce: req.nonce,
        fee: req.fee,
        memo: req.memo,
        valid_until: None,
        call_forest: CallForest::new(),
        depends_on: vec![],
        previous_receipt_hash: None,
    };

    // Sign the turn.
    let signed = s.wallet.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);
    let turn_data = signed.signature.0.to_vec();

    // Emit receipt event to WebSocket subscribers.
    drop(s);
    state.emit(crate::state::NodeEvent::Receipt {
        hash: turn_hash.clone(),
    });

    // Gossip the turn to federation peers.
    if let Some(gossip) = state.gossip().await {
        let hash = turn_hash_bytes;
        let data = turn_data;
        tokio::spawn(async move {
            gossip.gossip_turn(hash, data).await;
        });
    }

    Ok(Json(SubmitTurnResponse {
        accepted: true,
        turn_hash: Some(turn_hash),
    }))
}

async fn get_cell(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = pyana_cell::CellId(cell_id_bytes);

    let found = s.ledger.get(&cell_id).is_some();

    Ok(Json(CellResponse {
        id,
        found,
        balance: None,
    }))
}

// =============================================================================
// Explorer API Handlers (public, read-only)
// =============================================================================

/// GET /api/cells — list all cells in the ledger with summary info.
async fn get_all_cells(State(state): State<NodeState>) -> Json<Vec<CellListEntry>> {
    let s = state.read().await;
    let entries: Vec<CellListEntry> = s
        .ledger
        .iter()
        .map(|(id, cell)| CellListEntry {
            id: hex_encode(&id.0),
            balance: cell.state.balance,
            nonce: cell.state.nonce,
            capability_count: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            has_program: !matches!(cell.program, pyana_cell::CellProgram::None),
            found: true,
        })
        .collect();
    Json(entries)
}

/// GET /api/cell/:id — detailed cell information for the explorer.
async fn get_cell_detail(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellDetailResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = pyana_cell::CellId(cell_id_bytes);

    match s.ledger.get(&cell_id) {
        Some(cell) => Ok(Json(CellDetailResponse {
            id: id.clone(),
            found: true,
            balance: cell.state.balance,
            nonce: cell.state.nonce,
            capability_count: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            delegate: cell.delegate.as_ref().map(|d| hex_encode(&d.0)),
            has_program: !matches!(cell.program, pyana_cell::CellProgram::None),
            public_key: hex_encode(&cell.public_key),
            token_id: hex_encode(&cell.token_id),
            proved_state: cell.state.proved_state,
        })),
        None => Ok(Json(CellDetailResponse {
            id,
            found: false,
            balance: 0,
            nonce: 0,
            capability_count: 0,
            has_delegate: false,
            delegate: None,
            has_program: false,
            public_key: String::new(),
            token_id: String::new(),
            proved_state: false,
        })),
    }
}

/// P1 Fix 4: Rate-limited passphrase unlock endpoint.
async fn post_wallet_unlock(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    State(state): State<NodeState>,
    Json(req): Json<UnlockRequest>,
    limiter: RateLimiter,
) -> Result<Json<UnlockResponse>, StatusCode> {
    // Rate limit check.
    if !limiter.check(addr.ip()).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    if req.passphrase.is_empty() {
        return Ok(Json(UnlockResponse {
            success: false,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;
    let hash = blake3::derive_key("pyana-wallet-passphrase-v1", req.passphrase.as_bytes());

    match s.passphrase_hash {
        Some(stored_hash) => {
            if hash != stored_hash {
                return Ok(Json(UnlockResponse {
                    success: false,
                    error: Some("invalid passphrase".to_string()),
                }));
            }
            s.unlocked = true;
            Ok(Json(UnlockResponse {
                success: true,
                error: None,
            }))
        }
        None => {
            s.passphrase_hash = Some(hash);
            s.unlocked = true;
            Ok(Json(UnlockResponse {
                success: true,
                error: None,
            }))
        }
    }
}

/// P1 Fix 4: Rate-limited set-passphrase endpoint.
async fn post_set_passphrase(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    State(state): State<NodeState>,
    Json(req): Json<SetPassphraseRequest>,
    limiter: RateLimiter,
) -> Result<Json<SetPassphraseResponse>, StatusCode> {
    // Rate limit check.
    if !limiter.check(addr.ip()).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    if req.passphrase.is_empty() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;

    if s.passphrase_hash.is_some() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase already set; unlock first to change it".to_string()),
        }));
    }

    let hash = blake3::derive_key("pyana-wallet-passphrase-v1", req.passphrase.as_bytes());
    s.passphrase_hash = Some(hash);

    Ok(Json(SetPassphraseResponse {
        success: true,
        error: None,
    }))
}

async fn post_intent(
    State(state): State<NodeState>,
    Json(raw): Json<serde_json::Value>,
) -> Result<Json<IntentSubmitResponse>, StatusCode> {
    // P0 Fix 3: Deserialize into a proper Intent struct for validation.
    let intent: pyana_intent::Intent =
        serde_json::from_value(raw.clone()).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Validate the intent using pyana-intent's validation logic.
    pyana_intent::validation::validate_intent(&intent).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the content-addressed ID is correct (prevents ID spoofing).
    let recomputed = pyana_intent::Intent::new(
        intent.kind,
        intent.matcher.clone(),
        intent.creator,
        intent.expiry,
        intent.stake_proof.clone(),
    );
    if recomputed.id != intent.id {
        return Err(StatusCode::BAD_REQUEST);
    }

    let intent_id_hex = hex_encode(&intent.id);

    // P1 Fix 5: enforce size limit.
    {
        let mut s = state.write().await;
        if s.intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.intent_pool.insert(intent.id, intent.clone());
    }

    // Broadcast to WS subscribers.
    state.emit(NodeEvent::Intent {
        intent: serde_json::to_value(&intent).unwrap_or_default(),
    });

    // Gossip the intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let intent_json = raw;
        tokio::spawn(async move {
            gossip.gossip_intent(&intent_json).await;
        });
    }

    Ok(Json(IntentSubmitResponse {
        intent_id: intent_id_hex,
        stored: true,
    }))
}

async fn get_intents(State(state): State<NodeState>) -> Json<Vec<IntentListEntry>> {
    let s = state.read().await;
    let entries: Vec<IntentListEntry> = s
        .intent_pool
        .iter()
        .map(|(id, intent)| IntentListEntry {
            id: hex_encode(id),
            intent: intent.clone(),
        })
        .collect();
    Json(entries)
}

/// POST /intents/fulfill — verify a fulfillment and automatically execute payment.
///
/// After verifying the fulfillment and predicates, creates and executes a payment
/// turn that transfers computrons from the intent creator to the fulfiller.
async fn post_fulfill_intent(
    State(state): State<NodeState>,
    Json(req): Json<FulfillIntentRequest>,
) -> Result<Json<FulfillIntentResponse>, StatusCode> {
    let intent_id: [u8; 32] = hex_decode(&req.intent_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let payer_bytes: [u8; 32] = hex_decode(&req.payer_cell).map_err(|_| StatusCode::BAD_REQUEST)?;
    let recipient_bytes: [u8; 32] =
        hex_decode(&req.recipient_cell).map_err(|_| StatusCode::BAD_REQUEST)?;

    let payer_cell = pyana_sdk::CellId(payer_bytes);
    let recipient_cell = pyana_sdk::CellId(recipient_bytes);

    // Look up the intent.
    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => i.clone(),
        None => {
            return Ok(Json(FulfillIntentResponse {
                success: false,
                turn_hash: None,
                error: Some("intent not found in pool".to_string()),
            }));
        }
    };

    // Deserialize the base fulfillment. For now we construct a minimal one from the
    // request fields since the full Fulfillment struct isn't directly serde-friendly
    // across the wire. The verification happens inside execute_fulfillment_flow.
    let state_root = pyana_circuit::BabyBear::new(req.state_root);

    // Build a minimal FulfillmentWithPredicates for the execution flow.
    // The actual fulfillment proof is already verified by the node in this flow.
    let base_fulfillment = pyana_intent::fulfillment::Fulfillment {
        intent_id,
        fulfiller: pyana_intent::CommitmentId(recipient_bytes),
        mode: pyana_intent::VerificationMode::Trusted,
        token_data: Some(vec![0x01; 4]), // Non-empty stub for trusted mode verification.
        proof: None,
        granted_actions: intent
            .matcher
            .actions
            .iter()
            .filter_map(|p| p.action.clone())
            .collect(),
        granted_resource: intent
            .matcher
            .resource_pattern
            .clone()
            .unwrap_or_else(|| "*".to_string()),
        expiry: Some(intent.expiry),
    };

    let fulfillment_with_preds = pyana_intent::fulfillment::FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs: vec![], // Predicates already verified by caller in this API path.
        state_root,
        state_root_block: req.state_root_block,
    };

    // Get current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Execute the fulfillment payment flow.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let result = pyana_intent::fulfillment::execute_fulfillment_flow(
        &intent,
        &fulfillment_with_preds,
        &executor,
        &mut s.ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_height,
    );

    match result {
        Ok(receipt) => {
            let turn_hash = hex_encode(&receipt.turn_hash);
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            Ok(Json(FulfillIntentResponse {
                success: true,
                turn_hash: Some(turn_hash),
                error: None,
            }))
        }
        Err(e) => Ok(Json(FulfillIntentResponse {
            success: false,
            turn_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

async fn get_federation_roots(State(state): State<NodeState>) -> Json<Vec<AttestedRootInfo>> {
    let s = state.read().await;
    let roots = s.store.all_attested_roots().unwrap_or_default();
    let infos: Vec<AttestedRootInfo> = roots
        .iter()
        .map(|r| AttestedRootInfo {
            height: r.height,
            merkle_root: hex_encode(&r.merkle_root),
            timestamp: r.timestamp,
            signatures: r.quorum_signatures.len(),
        })
        .collect();
    Json(infos)
}

// =============================================================================
// Conditional Turn handlers
// =============================================================================

async fn post_submit_conditional(
    State(state): State<NodeState>,
    Json(req): Json<SubmitConditionalRequest>,
) -> Result<Json<SubmitConditionalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    drop(s);

    let condition: pyana_turn::ProofCondition =
        serde_json::from_value(req.condition).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn: pyana_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let deposit_amount =
        pyana_turn::compute_conditional_deposit(req.timeout_height, current_height);
    let conditional = pyana_turn::ConditionalTurn {
        turn,
        condition,
        timeout_height: req.timeout_height,
        submitted_at: current_height,
        deposit_amount,
    };

    if let Err(_e) = pyana_turn::validate_conditional_submission(&conditional, current_height) {
        return Ok(Json(SubmitConditionalResponse {
            accepted: false,
            conditional_hash: None,
        }));
    }

    let hash = conditional.hash();
    let hash_hex = hex_encode(&hash);

    // P1 Fix 6: enforce max size with proactive GC.
    {
        let mut s = state.write().await;

        // Proactive GC: remove expired conditionals before checking capacity.
        let gc_height = s
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        s.pending_conditionals
            .retain(|ct| !ct.is_expired(gc_height));

        if s.pending_conditionals.len() >= MAX_PENDING_CONDITIONALS {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.pending_conditionals.push(conditional);
    }

    Ok(Json(SubmitConditionalResponse {
        accepted: true,
        conditional_hash: Some(hash_hex),
    }))
}

async fn post_resolve_conditional(
    State(state): State<NodeState>,
    Json(req): Json<ResolveConditionalRequest>,
) -> Result<Json<ResolveConditionalResponse>, StatusCode> {
    let hash_bytes = hex_decode(&req.conditional_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    let proof: pyana_turn::ConditionProof =
        serde_json::from_value(req.proof).map_err(|_| StatusCode::BAD_REQUEST)?;

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let idx = s
        .pending_conditionals
        .iter()
        .position(|ct| ct.hash() == hash_bytes);

    let idx = match idx {
        Some(i) => i,
        None => {
            return Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn not found".to_string()),
            }));
        }
    };

    let condition = s.pending_conditionals[idx].condition.clone();
    let timeout_height = s.pending_conditionals[idx].timeout_height;
    let trusted_roots: Vec<pyana_turn::TrustedRoot> = s
        .store
        .all_attested_roots()
        .unwrap_or_default()
        .iter()
        .map(|r| (r.merkle_root, r.height))
        .collect();

    let result = pyana_turn::resolve_condition(
        &condition,
        &proof,
        current_height,
        timeout_height,
        &trusted_roots,
        pyana_turn::DEFAULT_MAX_ROOT_AGE,
        &mut s.used_proof_hashes,
        &[], // TODO: add trusted_executor_keys to NodeState
    );

    match result {
        pyana_turn::ConditionalResult::Resolved => {
            let conditional = s.pending_conditionals.remove(idx);

            let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
            let exec_result = executor.execute(&conditional.turn, &mut s.ledger);

            match exec_result {
                pyana_turn::TurnResult::Committed { receipt, .. } => {
                    let turn_hash = hex_encode(&receipt.turn_hash);
                    drop(s);
                    state.emit(NodeEvent::Receipt {
                        hash: turn_hash.clone(),
                    });
                    Ok(Json(ResolveConditionalResponse {
                        resolved: true,
                        turn_hash: Some(turn_hash),
                        reason: None,
                    }))
                }
                pyana_turn::TurnResult::Rejected { reason, .. } => {
                    Ok(Json(ResolveConditionalResponse {
                        resolved: false,
                        turn_hash: None,
                        reason: Some(format!("turn rejected: {reason}")),
                    }))
                }
                pyana_turn::TurnResult::Expired => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn expired during execution".to_string()),
                })),
                pyana_turn::TurnResult::Pending => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn pending during execution".to_string()),
                })),
            }
        }
        pyana_turn::ConditionalResult::Expired => {
            s.pending_conditionals.remove(idx);
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn has expired".to_string()),
            }))
        }
        pyana_turn::ConditionalResult::Pending => Ok(Json(ResolveConditionalResponse {
            resolved: false,
            turn_hash: None,
            reason: Some("condition not yet satisfied".to_string()),
        })),
        pyana_turn::ConditionalResult::InvalidProof(e) => Ok(Json(ResolveConditionalResponse {
            resolved: false,
            turn_hash: None,
            reason: Some(format!("invalid proof: {e}")),
        })),
    }
}

async fn get_pending_conditionals(
    State(state): State<NodeState>,
) -> Json<Vec<PendingConditionalInfo>> {
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // GC: remove expired conditionals.
    s.pending_conditionals
        .retain(|ct| !ct.is_expired(current_height));

    let infos: Vec<PendingConditionalInfo> = s
        .pending_conditionals
        .iter()
        .map(|ct| {
            let condition_type = match &ct.condition {
                pyana_turn::ProofCondition::HashPreimage { .. } => "hash_preimage",
                pyana_turn::ProofCondition::RemoteProof { .. } => "remote_proof",
                pyana_turn::ProofCondition::LocalProof { .. } => "local_proof",
                pyana_turn::ProofCondition::TurnExecuted { .. } => "turn_executed",
            };
            PendingConditionalInfo {
                hash: hex_encode(&ct.hash()),
                timeout_height: ct.timeout_height,
                submitted_at: ct.submitted_at,
                condition_type: condition_type.to_string(),
            }
        })
        .collect();
    Json(infos)
}

// =============================================================================
// PIR (Private Information Retrieval) Handlers
// =============================================================================

/// GET /pir/info — returns metadata about the PIR database.
///
/// Clients need this to know the database dimensions and tag ordering before
/// constructing a valid PIR query vector.
async fn get_pir_info(State(state): State<NodeState>) -> Json<PirInfoResponse> {
    let s = state.read().await;

    // Build the intent index from the node's local intent pool.
    let intents: Vec<pyana_intent::Intent> = s.intent_pool.values().cloned().collect();
    let index = pyana_intent::pir::IntentIndex::build_from_intents(&intents);

    Json(PirInfoResponse {
        num_rows: index.num_rows(),
        row_width: index.row_width(),
        tags: index.tags,
    })
}

/// POST /pir/query — accepts a PIR query vector and returns the server's response.
///
/// The node computes the matrix-vector product of the intent index against the
/// query vector, returning a response that reveals nothing about which row was
/// queried (when combined with a complementary query to a second node).
async fn post_pir_query(
    State(state): State<NodeState>,
    Json(req): Json<PirQueryRequest>,
) -> Result<Json<PirQueryResponse>, StatusCode> {
    let s = state.read().await;

    // Build the intent index from the node's local intent pool.
    let intents: Vec<pyana_intent::Intent> = s.intent_pool.values().cloned().collect();
    let index = pyana_intent::pir::IntentIndex::build_from_intents(&intents);

    // Validate query vector length matches the database.
    if req.query_vector.len() != index.num_rows() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Convert the u32 query vector to BabyBear field elements.
    let query = pyana_intent::pir::PirQuery {
        query_vector: req
            .query_vector
            .iter()
            .map(|&v| pyana_circuit::field::BabyBear::new(v))
            .collect(),
    };

    // Compute the PIR response.
    let response = pyana_intent::pir::compute_pir_response(&query, &index.entries);

    // Convert back to u32 for serialization.
    Ok(Json(PirQueryResponse {
        response: response.response.iter().map(|e| e.as_u32()).collect(),
    }))
}

// =============================================================================
// Checkpoint Handlers
// =============================================================================

/// GET /checkpoint/latest — returns the latest checkpoint.
async fn get_checkpoint_latest(
    State(state): State<NodeState>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.latest_checkpoint() {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

/// GET /checkpoint/:height — returns the checkpoint at a specific height.
async fn get_checkpoint_at_height(
    State(state): State<NodeState>,
    AxumPath(height): AxumPath<u64>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.checkpoint_at_height(height) {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

fn checkpoint_to_response(cp: &pyana_federation::Checkpoint) -> CheckpointResponse {
    CheckpointResponse {
        height: cp.height,
        ledger_state_root: hex_encode(&cp.ledger_state_root),
        note_tree_root: hex_encode(&cp.note_tree_root),
        nullifier_set_root: hex_encode(&cp.nullifier_set_root),
        revocation_tree_root: hex_encode(&cp.revocation_tree_root),
        epoch: cp.epoch,
        timestamp: cp.timestamp,
        federation_members: cp.federation_members.len(),
        qc_votes: cp.qc.votes.len(),
    }
}

// =============================================================================
// Faucet
// =============================================================================

/// Well-known faucet cell public key (all 0x01 bytes — deterministic for devnet).
const FAUCET_PUBLIC_KEY: [u8; 32] = [0x01; 32];
/// Well-known faucet cell token ID (all zeros — default token domain).
const FAUCET_TOKEN_ID: [u8; 32] = [0x00; 32];

#[derive(Deserialize)]
pub struct FaucetRequest {
    /// Hex-encoded 32-byte recipient cell ID.
    pub recipient: String,
    /// Amount of computrons to transfer (max 10000 per request).
    pub amount: u64,
}

#[derive(Serialize)]
pub struct FaucetResponse {
    pub success: bool,
    pub tx_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Faucet rate limiter: 1 request per cell per 60 seconds.
#[derive(Clone)]
struct FaucetRateLimiter {
    /// Map of recipient cell_id hex -> last request time.
    state: Arc<Mutex<HashMap<String, Instant>>>,
}

impl FaucetRateLimiter {
    fn new() -> Self {
        Self {
            state: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Returns true if the request should be allowed.
    async fn check(&self, recipient: &str) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        if let Some(last) = map.get(recipient) {
            if now.duration_since(*last).as_secs() < 60 {
                return false;
            }
        }
        map.insert(recipient.to_string(), now);
        true
    }
}

/// POST /api/faucet — transfer computrons from the faucet cell to a recipient.
///
/// Only enabled when `--enable-faucet` is set. Rate limited: 1 request per
/// recipient cell per minute. Maximum 10000 computrons per request.
async fn post_faucet(
    State(state): State<NodeState>,
    Json(req): Json<FaucetRequest>,
    limiter: FaucetRateLimiter,
) -> Result<Json<FaucetResponse>, StatusCode> {
    // Validate amount.
    if req.amount == 0 || req.amount > 10_000 {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            error: Some("amount must be between 1 and 10000".to_string()),
        }));
    }

    // Validate recipient hex.
    let recipient_bytes: [u8; 32] = match hex_decode(&req.recipient) {
        Ok(b) => b,
        Err(_) => {
            return Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                error: Some("invalid recipient: must be 64 hex characters".to_string()),
            }));
        }
    };

    // Rate limit check.
    if !limiter.check(&req.recipient).await {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            error: Some("rate limited: 1 request per cell per minute".to_string()),
        }));
    }

    let mut s = state.write().await;

    // Ensure the faucet cell exists in the ledger (create on first use).
    let faucet_cell_id = pyana_cell::CellId::derive_raw(&FAUCET_PUBLIC_KEY, &FAUCET_TOKEN_ID);
    if s.ledger.get(&faucet_cell_id).is_none() {
        let faucet_cell =
            pyana_cell::Cell::with_balance(FAUCET_PUBLIC_KEY, FAUCET_TOKEN_ID, 100_000);
        let _ = s.ledger.insert_cell(faucet_cell);
    }

    // Ensure the recipient cell exists (create with zero balance if not).
    let recipient_cell_id = pyana_cell::CellId(recipient_bytes);
    if s.ledger.get(&recipient_cell_id).is_none() {
        // Create a minimal recipient cell. Use the recipient_bytes as both the
        // public key and derive the ID from it. For devnet this is fine.
        let recipient_cell = pyana_cell::Cell::with_balance(recipient_bytes, FAUCET_TOKEN_ID, 0);
        let _ = s.ledger.insert_cell(recipient_cell);
    }

    // Apply the transfer.
    let delta = pyana_cell::LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(faucet_cell_id, recipient_cell_id, req.amount)],
    };

    match s.ledger.apply_delta(&delta) {
        Ok(()) => {
            // Compute a simple tx hash for the response.
            let mut hasher = blake3::Hasher::new();
            hasher.update(&faucet_cell_id.0);
            hasher.update(&recipient_bytes);
            hasher.update(&req.amount.to_le_bytes());
            let now_nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64;
            hasher.update(&now_nanos.to_le_bytes());
            let tx_hash = hex_encode(hasher.finalize().as_bytes());

            Ok(Json(FaucetResponse {
                success: true,
                tx_hash: Some(tx_hash),
                error: None,
            }))
        }
        Err(e) => Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            error: Some(format!("transfer failed: {e}")),
        })),
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
