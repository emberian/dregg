//! Axum HTTP API router for the pyana node.
//!
//! Serves a localhost-only API that the browser extension wallet talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::Arc;
use std::time::Instant;

use axum::{
    Json, Router,
    extract::Path as AxumPath,
    extract::State,
    extract::ConnectInfo,
    http::StatusCode,
    middleware,
    routing::{get, post},
};
use axum::extract::DefaultBodyLimit;
use axum::http::Request;
use axum::http::{HeaderValue, Method, header};
use axum::response::Response;
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

#[derive(Serialize)]
pub struct IntentListEntry {
    pub id: String,
    pub intent: pyana_intent::Intent,
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
            let expected_token_bytes =
                blake3::derive_key("pyana-api-bearer-v1", &passphrase_hash);
            let expected_token: String =
                expected_token_bytes.iter().map(|b| format!("{b:02x}")).collect();
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
async fn cors_middleware(
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Response {
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
pub fn router(state: NodeState) -> Router {
    // Rate limiter for passphrase/unlock endpoints: 5 attempts per 60 seconds.
    let passphrase_limiter = RateLimiter::new(5, 60);

    // Public routes (no auth required)
    let public_routes = Router::new()
        .route("/status", get(get_status))
        .route("/federation/roots", get(get_federation_roots))
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

    let conditional = pyana_turn::ConditionalTurn {
        turn,
        condition,
        timeout_height: req.timeout_height,
        submitted_at: current_height,
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
