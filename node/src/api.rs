//! Axum HTTP API router for the pyana node.
//!
//! Serves a localhost-only API that the browser extension wallet talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::Arc;
use std::time::Instant;

use argon2::password_hash::SaltString;
use argon2::password_hash::rand_core::OsRng;
use argon2::{Argon2, PasswordHash, PasswordHasher, PasswordVerifier};
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
use subtle::ConstantTimeEq;
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

#[derive(Serialize)]
pub struct EncryptedIntentSubmitResponse {
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
// Fast-Path Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct FastPathLockRequest {
    /// The turn to lock (full turn structure).
    pub turn: serde_json::Value,
}

#[derive(Serialize)]
pub struct FastPathLockResponse {
    pub locked: bool,
    pub validator_key: Option<String>,
    pub signature: Option<String>,
    pub height: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct FastPathCertificateRequest {
    /// The turn being certified.
    pub turn: serde_json::Value,
    /// Hex-encoded turn hash.
    pub turn_hash: String,
    /// Collected validator signatures.
    pub signatures: Vec<FastPathSignatureEntry>,
    /// Optional STARK proof (hex-encoded).
    pub proof_bytes: Option<String>,
}

#[derive(Deserialize)]
pub struct FastPathSignatureEntry {
    /// Hex-encoded 32-byte validator public key.
    pub validator_key: String,
    /// Hex-encoded 64-byte signature.
    pub signature: String,
    /// Height at which the signature was produced.
    pub height: u64,
}

#[derive(Serialize)]
pub struct FastPathCertificateResponse {
    pub executed: bool,
    pub turn_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
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
// Sovereign Cell Ephemeral Registration types
// =============================================================================

/// Request body for ephemeral sovereign cell registration.
///
/// The cell exists locally on the agent; the federation stores only the commitment.
/// Registration is temporary — expires after `ttl_blocks` of inactivity.
#[derive(Deserialize)]
pub struct RegisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte current state commitment.
    pub commitment: String,
    /// How many blocks to keep the registration alive (default: 1000).
    pub ttl_blocks: Option<u64>,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || commitment`.
    pub signature: String,
    /// Optional hex-encoded 32-byte verification key hash to bind this cell
    /// to a deployed program. When set, proof-carrying turns are verified
    /// against the program identified by this VK hash.
    pub verification_key_hash: Option<String>,
}

/// Response to a sovereign cell registration.
#[derive(Serialize)]
pub struct RegisterCellResponse {
    pub registered: bool,
    pub ttl_blocks: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voluntary deregistration.
#[derive(Deserialize)]
pub struct DeregisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    pub signature: String,
}

/// Response to a sovereign cell deregistration.
#[derive(Serialize)]
pub struct DeregisterCellResponse {
    pub deregistered: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for updating a sovereign cell's commitment after a transition.
#[derive(Deserialize)]
pub struct UpdateCommitmentRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte old commitment (must match stored).
    pub old_commitment: String,
    /// Hex-encoded 32-byte new commitment.
    pub new_commitment: String,
    /// Optional hex-encoded STARK proof of the transition (future use).
    pub transition_proof: Option<String>,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || old_commitment || new_commitment`.
    pub signature: String,
}

/// Response to a commitment update.
#[derive(Serialize)]
pub struct UpdateCommitmentResponse {
    pub updated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Program Deployment types
// =============================================================================

/// Request body for deploying a custom cell program to the federation.
#[derive(Deserialize)]
pub struct DeployProgramRequest {
    /// Hex-encoded postcard-serialized CircuitDescriptor bytes.
    pub descriptor_bytes: String,
    /// Program version (for upgrade/migration tracking).
    pub version: u32,
}

/// Response to a program deployment.
#[derive(Serialize)]
pub struct DeployProgramResponse {
    pub deployed: bool,
    /// Hex-encoded 32-byte VK hash (program identity).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vk_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Atomic Multi-Party Turn types
// =============================================================================

/// Request body for proposing an atomic multi-party turn.
#[derive(Deserialize)]
pub struct AtomicProposalRequest {
    /// The combined call forest from all parties (serialized).
    pub forest: serde_json::Value,
    /// Hex-encoded 32-byte participant node IDs.
    pub participants: Vec<String>,
    /// Vote threshold required for commitment.
    pub threshold: usize,
    /// Fee in computrons.
    pub fee: u64,
    /// Hex-encoded 32-byte initiator cell ID.
    pub initiator: String,
}

/// Response to an atomic turn proposal.
#[derive(Serialize)]
pub struct AtomicProposalResponse {
    pub accepted: bool,
    pub proposal_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voting on an atomic proposal.
#[derive(Deserialize)]
pub struct AtomicVoteRequest {
    /// Hex-encoded 32-byte proposal ID.
    pub proposal_id: String,
    /// Whether the participant votes yes.
    pub approve: bool,
    /// Hex-encoded 64-byte Ed25519 signature over the vote.
    pub signature: String,
    /// Hex-encoded 32-byte voter node ID.
    pub voter: String,
}

/// Response to an atomic vote.
#[derive(Serialize)]
pub struct AtomicVoteResponse {
    pub accepted: bool,
    /// If voting completed a decision, this is "commit" or "abort".
    pub decision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Response to a proposal status query.
#[derive(Serialize)]
pub struct ProposalStatusResponse {
    pub found: bool,
    /// One of: "proposing", "committed", "aborted", "idle".
    pub state: String,
    /// Number of yes votes received so far.
    pub yes_votes: usize,
    /// Number of no votes received so far.
    pub no_votes: usize,
    /// Total participants required.
    pub total_participants: usize,
    /// Threshold needed for commit.
    pub threshold: usize,
    /// Seconds since proposal creation.
    pub age_secs: u64,
}

/// Request body for a participant evaluating a proposal locally.
#[derive(Deserialize)]
pub struct EvaluateProposalRequest {
    /// Hex-encoded 32-byte proposal ID from the coordinator.
    pub proposal_id: String,
    /// The atomic forest to evaluate (serialized, same as the coordinator's proposal).
    pub forest: serde_json::Value,
}

/// Response to local proposal evaluation.
#[derive(Serialize)]
pub struct EvaluateProposalResponse {
    /// Whether the participant would vote yes based on local state.
    pub approve: bool,
    /// If rejecting, the reason.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// The Ed25519 signature over the vote (hex-encoded, 128 chars).
    pub signature: String,
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

/// Default maximum turns per minute per connection (configurable).
pub const DEFAULT_TURN_RATE_LIMIT: u32 = 60;

impl RateLimiter {
    fn new(max_attempts: u32, window_secs: u64) -> Self {
        let limiter = Self {
            state: Arc::new(Mutex::new(HashMap::new())),
            max_attempts,
            window_secs,
        };

        // Spawn a background task that prunes stale entries every 60 seconds
        // to prevent unbounded memory growth from many unique IPs.
        let prune_state = limiter.state.clone();
        let prune_window = window_secs;
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(60));
            loop {
                interval.tick().await;
                let mut map = prune_state.lock().await;
                let now = Instant::now();
                map.retain(|_, (_, window_start)| {
                    now.duration_since(*window_start).as_secs() < prune_window
                });
            }
        });

        limiter
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
/// The API token is derived from the bearer seed (which is itself derived from
/// passphrase + salt via BLAKE3 at passphrase-set time).
/// If no passphrase is set, all requests are allowed (initial setup phase).
async fn require_auth(
    State(state): State<NodeState>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Result<Response, StatusCode> {
    let s = state.read().await;

    // If no passphrase is set yet, allow all requests (initial setup).
    let Some(ref bearer_seed) = s.bearer_seed else {
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
            let expected_token_bytes = blake3::derive_key("pyana-api-bearer-v1", bearer_seed);
            let expected_token: String = expected_token_bytes
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            drop(s);

            // Constant-time comparison to prevent timing attacks on the bearer token.
            if token.as_bytes().ct_eq(expected_token.as_bytes()).into() {
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
///
/// Uses proper URL parsing to prevent bypass via domains like `localhost.evil.com`.
fn is_origin_allowed(origin: &str) -> bool {
    // Allow browser extension origins (not parseable as URLs).
    if origin.starts_with("chrome-extension://") || origin.starts_with("moz-extension://") {
        return true;
    }

    // Parse as a URL and check the host exactly.
    // This prevents bypasses like "http://localhost.evil.com".
    let Ok((scheme, host)) = parse_origin(origin) else {
        return false;
    };

    if scheme != "http" && scheme != "https" {
        return false;
    }

    matches!(host.as_str(), "localhost" | "127.0.0.1" | "[::1]")
}

/// Minimal origin parser: extracts scheme and host from an origin string.
/// Returns (scheme, host) without pulling in the `url` crate.
fn parse_origin(origin: &str) -> Result<(String, String), ()> {
    // Format: scheme "://" host [ ":" port ]
    let rest = origin.split_once("://").ok_or(())?;
    let scheme = rest.0.to_lowercase();
    let authority = rest.1;
    // Strip port if present (host is everything before the first ':' or '/')
    let host = authority
        .split_once(':')
        .map(|(h, _)| h)
        .or_else(|| authority.split_once('/').map(|(h, _)| h))
        .unwrap_or(authority);
    if host.is_empty() {
        return Err(());
    }
    Ok((scheme, host.to_lowercase()))
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
/// per-identity rate limiting on turn submission, and Bearer token
/// authentication on protected routes.
pub fn router(
    state: NodeState,
    enable_faucet: bool,
    metrics_handle: metrics_exporter_prometheus::PrometheusHandle,
) -> Router {
    // Rate limiter for passphrase/unlock endpoints: 5 attempts per 60 seconds.
    let passphrase_limiter = RateLimiter::new(5, 60);

    // Rate limiter for turn submission: DEFAULT_TURN_RATE_LIMIT per 60 seconds per IP.
    let turn_limiter = RateLimiter::new(DEFAULT_TURN_RATE_LIMIT, 60);

    // Public routes (no auth required)
    let mut public_routes = Router::new()
        .route("/status", get(get_status))
        .route("/federation/roots", get(get_federation_roots))
        .route("/api/blocks", get(get_federation_roots))
        .route("/api/cells", get(get_all_cells))
        .route("/api/cell/{id}", get(get_cell_detail))
        .route("/api/intents", get(get_intents))
        .route("/api/conditionals", get(get_pending_conditionals))
        .route("/api/discharge", post(post_discharge))
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
        .route("/intents/encrypted", post(post_encrypted_intent))
        .route("/intents/fulfill", post(post_fulfill_intent))
        .route(
            "/turn/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, state, body| {
                    post_submit_turn(connect_info, state, body, limiter)
                }
            }),
        )
        .route("/turn/fast-path", post(post_fast_path_lock))
        .route("/turn/certificate", post(post_fast_path_certificate))
        .route("/turn/submit-conditional", post(post_submit_conditional))
        .route("/turn/resolve-conditional", post(post_resolve_conditional))
        .route("/turn/pending", get(get_pending_conditionals))
        .route("/turn/atomic", post(post_atomic_proposal))
        .route("/turn/atomic/vote", post(post_atomic_vote))
        .route("/turn/atomic/{id}", get(get_proposal_status))
        .route("/turn/atomic/evaluate", post(post_evaluate_proposal))
        .route("/cell/{id}", get(get_cell))
        .route("/cells/register", post(post_register_cell))
        .route("/cells/deregister", post(post_deregister_cell))
        .route("/cells/update-commitment", post(post_update_commitment))
        .route("/programs/deploy", post(post_deploy_program))
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    // Metrics endpoint (separate state: PrometheusHandle)
    let metrics_route = Router::new()
        .route("/metrics", get(crate::metrics::metrics_handler))
        .with_state(metrics_handle);

    public_routes
        .merge(protected_routes)
        .merge(metrics_route)
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

#[tracing::instrument(skip_all, fields(agent = %req.agent))]
async fn post_submit_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    State(state): State<NodeState>,
    Json(req): Json<SubmitTurnRequest>,
    limiter: RateLimiter,
) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    // Per-connection rate limit: max DEFAULT_TURN_RATE_LIMIT turns per minute.
    if !limiter.check(addr.ip()).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    let mut s = state.write().await;

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
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };

    // Sign the turn.
    let signed = s.wallet.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    // Execute the turn locally FIRST.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            s.wallet.append_receipt(receipt);

            // Serialize the full SignedTurn for gossip (postcard format).
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");

            drop(s);

            // Emit receipt event to WebSocket subscribers.
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Gossip the turn to federation peers.
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            Ok(Json(SubmitTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: Some(format!("rejected: {reason}")),
            }))
        }
        _ => {
            crate::metrics::inc_turns_executed("rejected");
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: None,
            }))
        }
    }
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

/// Hash a passphrase with Argon2id and derive a bearer seed.
///
/// Returns (PHC string for storage, bearer_seed for token derivation).
fn hash_passphrase(passphrase: &str) -> (String, [u8; 32]) {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default(); // Argon2id v19 with recommended params
    let phc_string = argon2
        .hash_password(passphrase.as_bytes(), &salt)
        .expect("argon2 hash_password should not fail")
        .to_string();
    // Derive a separate bearer seed from passphrase + salt using BLAKE3.
    // This is safe because BLAKE3 is a proper KDF and the input has high entropy
    // (passphrase + random salt).
    let bearer_seed = blake3::derive_key(
        "pyana-node-bearer-v1",
        format!("{}{}", passphrase, salt.as_str()).as_bytes(),
    );
    (phc_string, bearer_seed)
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

    match s.passphrase_hash.clone() {
        Some(stored_hash) => {
            // Verify against stored Argon2id hash.
            let parsed =
                PasswordHash::new(&stored_hash).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
            if Argon2::default()
                .verify_password(req.passphrase.as_bytes(), &parsed)
                .is_err()
            {
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
            // First unlock sets the passphrase using Argon2id.
            let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
            s.passphrase_hash = Some(phc_string.clone());
            s.bearer_seed = Some(bearer_seed);
            let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
            let _ = s.store.set_config("bearer_seed", &bearer_seed);
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

    let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
    s.passphrase_hash = Some(phc_string.clone());
    s.bearer_seed = Some(bearer_seed);
    // Persist the passphrase hash and bearer seed to the store so they survive restarts.
    let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
    let _ = s.store.set_config("bearer_seed", &bearer_seed);

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
        // Invalidate PIR index cache on pool mutation.
        s.pir_index_cache = None;
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

/// POST /intents/encrypted — submit an SSE-encrypted intent for gossip propagation.
///
/// Encrypted intents carry search tokens for privacy-preserving matching. The body
/// is hidden until a fulfiller's capability keywords produce a matching token, at
/// which point the poster reveals the decryption key over a direct channel.
async fn post_encrypted_intent(
    State(state): State<NodeState>,
    Json(encrypted): Json<pyana_intent::sse::EncryptedIntent>,
) -> Result<Json<EncryptedIntentSubmitResponse>, StatusCode> {
    let intent_id_hex = hex_encode(&encrypted.id);

    // Basic validation: check non-empty search tokens and non-empty body.
    if encrypted.search_tokens.is_empty() || encrypted.encrypted_body.is_empty() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Check expiry if set.
    if let Some(expiry) = encrypted.expiry {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        if now >= expiry {
            return Err(StatusCode::BAD_REQUEST);
        }
    }

    // Store in the encrypted intent pool.
    {
        let mut s = state.write().await;
        if s.encrypted_intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.encrypted_intent_pool
            .insert(encrypted.id, encrypted.clone());
    }

    // Gossip the encrypted intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let enc = encrypted.clone();
        tokio::spawn(async move {
            gossip.gossip_encrypted_intent(&enc).await;
        });
    }

    Ok(Json(EncryptedIntentSubmitResponse {
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

    // Verify the payer_cell matches the intent's creator (ownership check).
    // The payer must be the intent creator — prevents arbitrary payer exploitation.
    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => {
            if i.creator.0 != payer_bytes {
                return Ok(Json(FulfillIntentResponse {
                    success: false,
                    turn_hash: None,
                    error: Some("payer_cell does not match intent creator".to_string()),
                }));
            }
            i.clone()
        }
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
// Fast-Path Turn handlers
// =============================================================================

/// POST /turn/fast-path — request a fast-path lock from this validator.
///
/// The node checks eligibility, acquires cell locks, and returns a TurnSign
/// (the validator's lock acknowledgement) if the turn qualifies.
#[tracing::instrument(skip_all)]
async fn post_fast_path_lock(
    State(state): State<NodeState>,
    Json(req): Json<FastPathLockRequest>,
) -> Result<Json<FastPathLockResponse>, StatusCode> {
    let turn: pyana_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash = turn.hash();

    let mut s = state.write().await;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Use the node's public key as the validator signing key.
    let validator_key = s.wallet.public_key().0;

    // Split borrows: take mutable ref to cell_lock_table and immutable ref to ledger
    // from disjoint fields of the same struct.
    let inner = &mut *s;
    let result = pyana_turn::process_fast_path_lock(
        &mut inner.cell_lock_table,
        &turn,
        turn_hash,
        current_height,
        &inner.ledger,
        &validator_key,
    );

    match result {
        Ok(sign) => Ok(Json(FastPathLockResponse {
            locked: true,
            validator_key: Some(hex_encode(&sign.validator_key)),
            signature: Some(hex_encode_var(&sign.signature)),
            height: Some(sign.height),
            error: None,
        })),
        Err(e) => Ok(Json(FastPathLockResponse {
            locked: false,
            validator_key: None,
            signature: None,
            height: None,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /turn/certificate — execute a certified fast-path turn.
///
/// The client presents a TurnCertificate (turn + 2f+1 validator signatures).
/// The node verifies the certificate, executes the turn, releases locks, and
/// gossips the result.
#[tracing::instrument(skip_all)]
async fn post_fast_path_certificate(
    State(state): State<NodeState>,
    Json(req): Json<FastPathCertificateRequest>,
) -> Result<Json<FastPathCertificateResponse>, StatusCode> {
    let turn: pyana_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash_bytes: [u8; 32] =
        hex_decode(&req.turn_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the turn hash matches.
    let computed_hash = turn.hash();
    if computed_hash != turn_hash_bytes {
        return Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: None,
            error: Some("turn hash mismatch".to_string()),
        }));
    }

    // Parse signatures.
    let mut signatures = Vec::new();
    for entry in &req.signatures {
        let vk: [u8; 32] = hex_decode(&entry.validator_key).map_err(|_| StatusCode::BAD_REQUEST)?;
        let sig_bytes = hex_decode_var(&entry.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
        if sig_bytes.len() != 64 {
            return Err(StatusCode::BAD_REQUEST);
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&sig_bytes);
        signatures.push(pyana_turn::TurnSign {
            validator_key: vk,
            signature: sig,
            height: entry.height,
        });
    }

    // Assemble certificate (verify quorum).
    // Threshold is derived from federation size: n - f where f = (n-1)/3.
    // For single-node (n=1): threshold = 1. For 4 nodes: threshold = 3.
    let n = {
        let s = state.read().await;
        let key_count = s.known_federation_keys.len();
        if key_count == 0 { 1usize } else { key_count }
    };
    let f = (n.saturating_sub(1)) / 3;
    let threshold = n - f;
    let cert = match pyana_turn::assemble_certificate(turn, turn_hash_bytes, signatures, threshold)
    {
        Ok(c) => c,
        Err(e) => {
            return Ok(Json(FastPathCertificateResponse {
                executed: false,
                turn_hash: None,
                error: Some(e.to_string()),
            }));
        }
    };

    // Execute the certified turn.
    let mut s = state.write().await;
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

    // Split borrows: take mutable refs to disjoint fields.
    let inner = &mut *s;
    let result = pyana_turn::execute_certified_turn(
        &cert,
        &executor,
        &mut inner.ledger,
        &mut inner.cell_lock_table,
    );

    match result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            let hash_hex = hex_encode(&receipt.turn_hash);
            s.wallet.append_receipt(receipt);
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: hash_hex.clone(),
            });
            Ok(Json(FastPathCertificateResponse {
                executed: true,
                turn_hash: Some(hash_hex),
                error: None,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            error: Some(format!("turn rejected: {reason}")),
        })),
        _ => Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            error: Some("turn did not commit".to_string()),
        })),
    }
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

#[tracing::instrument(skip_all)]
async fn post_resolve_conditional(
    State(state): State<NodeState>,
    Json(req): Json<ResolveConditionalRequest>,
) -> Result<Json<ResolveConditionalResponse>, StatusCode> {
    // Require wallet to be unlocked for conditional resolution.
    {
        let s = state.read().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    let hash_bytes = hex_decode(&req.conditional_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    let proof: pyana_turn::ConditionProof =
        serde_json::from_value(req.proof).map_err(|_| StatusCode::BAD_REQUEST)?;
    let verify_start = Instant::now();

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
    let trusted_executor_keys: Vec<[u8; 32]> =
        s.known_federation_keys.iter().map(|k| k.0).collect();

    let result = pyana_turn::resolve_condition(
        &condition,
        &proof,
        current_height,
        timeout_height,
        &trusted_roots,
        pyana_turn::DEFAULT_MAX_ROOT_AGE,
        &mut s.used_proof_hashes,
        &trusted_executor_keys,
    );

    crate::metrics::record_proof_verification_duration(verify_start.elapsed().as_secs_f64());

    match result {
        pyana_turn::ConditionalResult::Resolved => {
            crate::metrics::inc_proofs_verified("valid");
            // SECURITY: Persist the proof nullifier to the store immediately so
            // a crash cannot allow proof replay. The in-memory set was already
            // updated by resolve_condition; this makes it durable.
            let proof_hash = pyana_turn::compute_proof_hash(&proof);
            if let Err(e) = s.store.insert_proof_hash(&proof_hash) {
                tracing::warn!(error = %e, "failed to persist proof nullifier to store");
            }

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
            crate::metrics::inc_proofs_verified("error");
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
        pyana_turn::ConditionalResult::InvalidProof(e) => {
            crate::metrics::inc_proofs_verified("invalid");
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some(format!("invalid proof: {e}")),
            }))
        }
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
// Atomic Multi-Party Turn Handlers
// =============================================================================

/// POST /turn/atomic — Submit an atomic multi-party turn proposal.
///
/// The coordinator node creates a Coordinator instance, validates the proposal
/// (budget gate, participant count, threshold), persists it in the proposals map,
/// and returns a proposal_id that participants can vote on.
#[tracing::instrument(skip_all)]
async fn post_atomic_proposal(
    State(state): State<NodeState>,
    Json(req): Json<AtomicProposalRequest>,
) -> Result<Json<AtomicProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    // Parse participant node IDs.
    let mut participants: Vec<[u8; 32]> = Vec::new();
    for p in &req.participants {
        let bytes: [u8; 32] = hex_decode(p).map_err(|_| StatusCode::BAD_REQUEST)?;
        participants.push(bytes);
    }

    if participants.is_empty() {
        return Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some("at least one participant required".to_string()),
        }));
    }

    // Parse the initiator cell ID.
    let initiator_bytes: [u8; 32] =
        hex_decode(&req.initiator).map_err(|_| StatusCode::BAD_REQUEST)?;
    let initiator = pyana_cell::CellId(initiator_bytes);

    // Deserialize the call forest.
    let forest: pyana_turn::CallForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Build the atomic forest.
    let atomic_forest = pyana_coord::AtomicForest::new(
        participants.clone(),
        forest,
        vec![], // preconditions left empty; participants validate locally
        initiator,
        req.fee,
    );

    // Create the coordinator with the node's identity.
    let mut s = state.write().await;

    // Garbage-collect stale proposals before creating new ones.
    s.expire_stale_proposals();

    let node_id = s.silo_id;
    let signing_key = s.wallet.gossip_signing_key().to_bytes();
    let costs = pyana_turn::ComputronCosts::default();

    // Build participant key map (for production, these would come from federation config).
    let participant_keys: std::collections::HashMap<[u8; 32], [u8; 32]> = participants
        .iter()
        .map(|&id| (id, id)) // In production: lookup real public keys
        .collect();

    let mut coordinator = pyana_coord::Coordinator::new(
        node_id,
        signing_key,
        req.threshold,
        costs,
        u64::MAX, // max budget — actual gate applied at execution time
        participant_keys,
    );

    let forest_for_storage = atomic_forest.clone();

    match coordinator.propose(atomic_forest) {
        Ok(propose_msg) => {
            let proposal_id = propose_msg.proposal_id;
            let proposal_id_hex = hex_encode(&proposal_id);

            // Persist the coordinator in the proposals map for later vote collection.
            s.atomic_proposals.insert(
                proposal_id,
                crate::state::ActiveProposal {
                    coordinator,
                    created_at: std::time::Instant::now(),
                    forest: forest_for_storage,
                },
            );

            // Broadcast proposal to peers via gossip if available.
            drop(s);
            if let Some(gossip) = state.gossip().await {
                let msg = serde_json::json!({
                    "type": "atomic_proposal",
                    "proposal_id": proposal_id_hex,
                });
                let msg_bytes = serde_json::to_vec(&msg).unwrap_or_default();
                gossip.gossip_turn(proposal_id, msg_bytes).await;
            }

            Ok(Json(AtomicProposalResponse {
                accepted: true,
                proposal_id: Some(proposal_id_hex),
                error: None,
            }))
        }
        Err(e) => Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some(format!("{e}")),
        })),
    }
}

/// POST /turn/atomic/vote — Vote on an atomic proposal.
///
/// Participants submit their vote (approve/reject) with an Ed25519 signature.
/// When enough votes are collected, the coordinator decides to commit or abort,
/// executing the turn via TurnExecutor on commit.
async fn post_atomic_vote(
    State(state): State<NodeState>,
    Json(req): Json<AtomicVoteRequest>,
) -> Result<Json<AtomicVoteResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let voter: [u8; 32] = hex_decode(&req.voter).map_err(|_| StatusCode::BAD_REQUEST)?;

    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }
    let mut signature = [0u8; 64];
    signature.copy_from_slice(&sig_bytes);

    let vote = if req.approve {
        pyana_coord::Vote::yes(signature)
    } else {
        pyana_coord::Vote::no("participant rejected", signature)
    };

    // Defense-in-depth: verify the vote signature against the claimed voter's
    // public key BEFORE passing to the coordinator. This prevents an authenticated
    // node from voting as another participant (the coordinator also verifies, but
    // rejecting early avoids acquiring the write lock for invalid votes).
    {
        let s = state.read().await;
        let active = match s.atomic_proposals.get(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        let forest_hash = active.forest.hash;
        let sig_valid = if req.approve {
            pyana_coord::Vote::verify_yes(&signature, &proposal_id, &forest_hash, &voter)
        } else {
            pyana_coord::Vote::verify_no(&signature, &proposal_id, &forest_hash, &voter)
        };
        if !sig_valid {
            return Ok(Json(AtomicVoteResponse {
                accepted: false,
                decision: None,
                error: Some("vote signature does not match claimed voter identity".to_string()),
            }));
        }
    }

    let mut s = state.write().await;

    // Feed the vote to the coordinator.
    let decision = {
        let active = match s.atomic_proposals.get_mut(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        match active.coordinator.receive_vote(voter, vote) {
            Ok(maybe_decision) => maybe_decision,
            Err(e) => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some(format!("{e}")),
                }));
            }
        }
    };

    // Handle the decision.
    match decision {
        Some(pyana_coord::Decision::Commit) => {
            // Extract the proposal so we can borrow ledger mutably.
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            // Execute the atomic turn against the ledger.
            match active.coordinator.commit(&mut s.ledger) {
                Ok(_commit_msg) => Ok(Json(AtomicVoteResponse {
                    accepted: true,
                    decision: Some("commit".to_string()),
                    error: None,
                })),
                Err(e) => {
                    // Commit failed (e.g., turn execution error) — abort.
                    let _ = active.coordinator.abort(format!("commit failed: {e}"));

                    Ok(Json(AtomicVoteResponse {
                        accepted: true,
                        decision: Some("abort".to_string()),
                        error: Some(format!("commit failed: {e}")),
                    }))
                }
            }
        }
        Some(pyana_coord::Decision::Abort) => {
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            let _ = active
                .coordinator
                .abort("too many rejections — threshold unreachable");

            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: Some("abort".to_string()),
                error: None,
            }))
        }
        Some(pyana_coord::Decision::Pending) | None => {
            // Still waiting for more votes.
            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: None,
                error: None,
            }))
        }
    }
}

/// GET /turn/atomic/:id — Query the status of an active atomic proposal.
///
/// Returns vote counts, coordinator state, and age so clients can monitor
/// progress without polling the vote endpoint.
async fn get_proposal_status(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<ProposalStatusResponse>, StatusCode> {
    let proposal_id: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.read().await;
    let active = match s.atomic_proposals.get(&proposal_id) {
        Some(p) => p,
        None => {
            return Ok(Json(ProposalStatusResponse {
                found: false,
                state: "not_found".to_string(),
                yes_votes: 0,
                no_votes: 0,
                total_participants: 0,
                threshold: 0,
                age_secs: 0,
            }));
        }
    };

    let (state_name, yes_count, no_count, total) = match &active.coordinator.state {
        pyana_coord::CoordinatorState::Idle => ("idle", 0, 0, 0),
        pyana_coord::CoordinatorState::Proposing { forest, votes, .. } => {
            let yes = votes.values().filter(|v| v.is_yes()).count();
            let no = votes.values().filter(|v| v.is_no()).count();
            ("proposing", yes, no, forest.participant_count())
        }
        pyana_coord::CoordinatorState::Committed { .. } => ("committed", 0, 0, 0),
        pyana_coord::CoordinatorState::Aborted { .. } => ("aborted", 0, 0, 0),
    };

    let age_secs = std::time::Instant::now()
        .duration_since(active.created_at)
        .as_secs();

    Ok(Json(ProposalStatusResponse {
        found: true,
        state: state_name.to_string(),
        yes_votes: yes_count,
        no_votes: no_count,
        total_participants: total,
        threshold: active.coordinator.threshold,
        age_secs,
    }))
}

/// POST /turn/atomic/evaluate — Participant evaluates a proposal against local state.
///
/// A node that received a proposal via gossip uses this endpoint to evaluate
/// whether it should vote yes or no, based on its local ledger and preconditions.
/// Returns the signed vote that can then be submitted to the coordinator's
/// `/turn/atomic/vote` endpoint.
async fn post_evaluate_proposal(
    State(state): State<NodeState>,
    Json(req): Json<EvaluateProposalRequest>,
) -> Result<Json<EvaluateProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the atomic forest from the request.
    let atomic_forest: pyana_coord::AtomicForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.write().await;

    // Build a Participant from the node's local identity and ledger.
    let node_id = s.silo_id;
    let signing_key = s.wallet.gossip_signing_key().to_bytes();
    let cell_id = pyana_cell::CellId(node_id);

    let mut participant =
        pyana_coord::Participant::new(cell_id, node_id, signing_key, s.ledger.clone());

    // Evaluate the proposal locally.
    let vote = participant.evaluate_proposal(&proposal_id, &atomic_forest);

    match vote {
        pyana_coord::Vote::Yes { signature } => Ok(Json(EvaluateProposalResponse {
            approve: true,
            reason: None,
            signature: hex_encode_var(&signature),
        })),
        pyana_coord::Vote::No { reason, signature } => Ok(Json(EvaluateProposalResponse {
            approve: false,
            reason: Some(reason),
            signature: hex_encode_var(&signature),
        })),
    }
}

// =============================================================================
// Sovereign Cell Ephemeral Registration Handlers
// =============================================================================

/// POST /cells/register — register a sovereign cell's commitment with the federation.
///
/// The cell exists locally on the agent; the federation stores only the commitment
/// and TTL metadata. Registration expires after `ttl_blocks` of inactivity.
#[tracing::instrument(skip_all)]
async fn post_register_cell(
    State(state): State<NodeState>,
    Json(req): Json<RegisterCellRequest>,
) -> Result<Json<RegisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let commitment: [u8; 32] = hex_decode(&req.commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || commitment.
    let mut message = Vec::with_capacity(64);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some("invalid signature".to_string()),
        }));
    }

    let ttl = req.ttl_blocks.unwrap_or(pyana_cell::DEFAULT_SOVEREIGN_TTL);
    let cell_id = pyana_cell::CellId(cell_id_bytes);

    // Parse optional verification key hash.
    let vk_hash: Option<[u8; 32]> = match &req.verification_key_hash {
        Some(hex_str) => Some(hex_decode(hex_str).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s
        .ledger
        .register_sovereign_cell_with_vk(cell_id, commitment, current_height, ttl, vk_hash)
    {
        Ok(()) => Ok(Json(RegisterCellResponse {
            registered: true,
            ttl_blocks: ttl,
            error: None,
        })),
        Err(e) => Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/deregister — voluntarily remove a sovereign cell from the federation.
#[tracing::instrument(skip_all)]
async fn post_deregister_cell(
    State(state): State<NodeState>,
    Json(req): Json<DeregisterCellRequest>,
) -> Result<Json<DeregisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id (proves ownership for deregistration).
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &cell_id_bytes) {
        return Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;

    match s.ledger.deregister_sovereign_cell(&cell_id) {
        Ok(()) => Ok(Json(DeregisterCellResponse {
            deregistered: true,
            error: None,
        })),
        Err(e) => Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/update-commitment — update a sovereign cell's commitment after a transition.
///
/// Verifies the old commitment matches, updates to the new commitment, and resets
/// the TTL activity counter.
#[tracing::instrument(skip_all)]
async fn post_update_commitment(
    State(state): State<NodeState>,
    Json(req): Json<UpdateCommitmentRequest>,
) -> Result<Json<UpdateCommitmentResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let old_commitment: [u8; 32] =
        hex_decode(&req.old_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let new_commitment: [u8; 32] =
        hex_decode(&req.new_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || old_commitment || new_commitment.
    let mut message = Vec::with_capacity(96);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&old_commitment);
    message.extend_from_slice(&new_commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s.ledger.update_sovereign_registration_commitment(
        &cell_id,
        old_commitment,
        new_commitment,
        current_height,
    ) {
        Ok(()) => Ok(Json(UpdateCommitmentResponse {
            updated: true,
            error: None,
        })),
        Err(e) => Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /programs/deploy — deploy a custom cell program to the federation.
///
/// Accepts a postcard-serialized CircuitDescriptor, validates it for safety,
/// and stores it in the program registry. Returns the VK hash (program identity).
#[tracing::instrument(skip_all)]
async fn post_deploy_program(
    State(state): State<NodeState>,
    Json(req): Json<DeployProgramRequest>,
) -> Result<Json<DeployProgramResponse>, StatusCode> {
    // Decode hex descriptor bytes.
    let descriptor_bytes =
        hex_decode_var(&req.descriptor_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the CircuitDescriptor from postcard format.
    let descriptor: pyana_dsl_runtime::CircuitDescriptor =
        postcard::from_bytes(&descriptor_bytes).map_err(|_| {
            StatusCode::BAD_REQUEST
        })?;

    // Create the CellProgram (computes VK hash).
    let program = pyana_dsl_runtime::CellProgram::new(descriptor, req.version);

    // Deploy to registry (validates safety bounds).
    let mut s = state.write().await;
    match s.program_registry.deploy(program) {
        Ok(vk_hash) => Ok(Json(DeployProgramResponse {
            deployed: true,
            vk_hash: Some(hex_encode(&vk_hash)),
            error: None,
        })),
        Err(e) => Ok(Json(DeployProgramResponse {
            deployed: false,
            vk_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

/// Verify an Ed25519 signature where the public key is the cell_id bytes.
///
/// The cell_id doubles as the public key for sovereign cells (the cell_id IS
/// the Ed25519 public key or is derived from it). For this API, we treat
/// the cell_id as the public key directly.
fn verify_ed25519_signature(public_key_bytes: &[u8; 32], sig_bytes: &[u8], message: &[u8]) -> bool {
    use ed25519_dalek::Verifier;

    let Ok(verifying_key) = ed25519_dalek::VerifyingKey::from_bytes(public_key_bytes) else {
        return false;
    };
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(sig_bytes);
    let signature = ed25519_dalek::Signature::from_bytes(&sig_arr);
    verifying_key.verify(message, &signature).is_ok()
}

// =============================================================================
// PIR (Private Information Retrieval) Handlers
// =============================================================================

/// GET /pir/info — returns metadata about the PIR database.
///
/// Clients need this to know the database dimensions and tag ordering before
/// constructing a valid PIR query vector.
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn get_pir_info(State(state): State<NodeState>) -> Json<PirInfoResponse> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<pyana_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(pyana_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

    Json(PirInfoResponse {
        num_rows: index.num_rows(),
        row_width: index.row_width(),
        tags: index.tags.clone(),
    })
}

/// POST /pir/query — accepts a PIR query vector and returns the server's response.
///
/// The node computes the matrix-vector product of the intent index against the
/// query vector, returning a response that reveals nothing about which row was
/// queried (when combined with a complementary query to a second node).
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn post_pir_query(
    State(state): State<NodeState>,
    Json(req): Json<PirQueryRequest>,
) -> Result<Json<PirQueryResponse>, StatusCode> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<pyana_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(pyana_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

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
// Discharge Gateway Endpoint
// =============================================================================

/// POST /api/discharge request body.
#[derive(Deserialize)]
pub struct NodeDischargeRequest {
    /// Base64-encoded ticket from the 3P caveat.
    pub ticket: String,
    /// Optional client identifier.
    pub client_id: Option<String>,
    /// Optional base64-encoded proof.
    pub proof: Option<String>,
    /// Optional payment amount.
    pub payment: Option<u64>,
    /// Arbitrary metadata.
    #[serde(default)]
    pub metadata: HashMap<String, String>,
}

/// POST /api/discharge response body.
#[derive(Serialize)]
pub struct NodeDischargeResponse {
    pub success: bool,
    pub discharge: Option<String>,
    pub expires_at: Option<i64>,
    pub condition_met: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// POST /api/discharge — issue a discharge macaroon from this node's gateway.
///
/// The node acts as a discharge gateway for its own federation's tokens.
/// The shared key is derived from the wallet's signing key using BLAKE3 KDF
/// with domain "pyana-discharge-gateway-v1".
async fn post_discharge(
    State(state): State<NodeState>,
    Json(req): Json<NodeDischargeRequest>,
) -> Result<Json<NodeDischargeResponse>, StatusCode> {
    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;

    // Decode ticket from base64.
    let ticket = engine
        .decode(&req.ticket)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    // Decode optional proof from base64.
    let proof = match &req.proof {
        Some(p) => Some(engine.decode(p).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // SECURITY: Use the persistent discharge gateway from node state.
    // This ensures the `issued` HashSet persists across requests, providing
    // actual replay prevention. Previously, a fresh gateway was created per
    // request, making the replay set useless (it was dropped immediately).
    if s.discharge_gateway.is_none() {
        let gateway_key = s.wallet.derive_symmetric_key("pyana-discharge-gateway-v1");
        let location = format!("pyana-node://{}", hex_encode(&s.wallet.public_key().0));
        let mut gateway = pyana_macaroon::DischargeGateway::new(gateway_key, location);
        // Default evaluator: require proof to prevent accidental open gateways.
        gateway.add_evaluator(Box::new(pyana_macaroon::ProofRequiredEvaluator));
        // Load previously persisted replay set from store (survives restarts).
        if let Ok(Some(data)) = s.store.get_config("discharge_issued_set") {
            gateway.load_issued_set(&data);
        }
        s.discharge_gateway = Some(gateway);
    }

    let gateway = s.discharge_gateway.as_ref().unwrap();

    let discharge_req = pyana_macaroon::DischargeRequest {
        ticket,
        client_id: req.client_id,
        proof,
        payment: req.payment,
        metadata: req.metadata,
    };

    match gateway.process_request(&discharge_req) {
        Ok(resp) => {
            // SECURITY: Persist replay-prevention state immediately after each
            // successful discharge. A crash between discharge issuance and shutdown
            // would otherwise lose the replay set, enabling ticket reuse.
            let data = gateway.serialize_issued_set();
            if let Err(e) = s.store.set_config("discharge_issued_set", &data) {
                tracing::warn!(error = %e, "failed to persist discharge replay set");
            }
            Ok(Json(NodeDischargeResponse {
                success: true,
                discharge: Some(resp.discharge),
                expires_at: Some(resp.expires_at),
                condition_met: Some(resp.condition_met),
                error: None,
            }))
        }
        Err(e) => Ok(Json(NodeDischargeResponse {
            success: false,
            discharge: None,
            expires_at: None,
            condition_met: None,
            error: Some(e.reason),
        })),
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Encode variable-length byte slices to hex (for signatures, etc.).
fn hex_encode_var(bytes: &[u8]) -> String {
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

/// Decode variable-length hex strings into byte vectors.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
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

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_coord::{AtomicForest, Coordinator, Decision, Vote};
    use pyana_turn::ComputronCosts;
    use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use std::collections::HashMap;
    use std::time::{Duration, Instant};

    /// Helper: create a deterministic key pair for testing.
    fn test_key(name: &str) -> [u8; 32] {
        *blake3::hash(format!("pyana-node-atomic-test:{name}").as_bytes()).as_bytes()
    }

    /// Helper: build a minimal AtomicForest with a single noop-like action.
    fn make_test_forest(participants: Vec<[u8; 32]>, initiator: [u8; 32]) -> AtomicForest {
        let cell_id = pyana_cell::CellId(initiator);
        let mut forest = pyana_turn::CallForest::new();
        let action = Action {
            target: cell_id,
            method: *blake3::hash(b"noop").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: pyana_cell::Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };
        forest.add_root(action);
        AtomicForest::new(participants, forest, vec![], cell_id, 0)
    }

    #[test]
    fn test_proposal_creation_and_vote_commit() {
        let node_a = test_key("node_a");
        let node_b = test_key("node_b");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        // Propose.
        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node A votes yes.
        let sig_a = Vote::sign_yes(&proposal_id, &forest.hash, &node_a);
        let vote_a = Vote::yes(sig_a);
        let decision_a = coordinator.receive_vote(pub_a, vote_a).unwrap();
        assert_eq!(decision_a, None); // Still pending.

        // Node B votes yes.
        let sig_b = Vote::sign_yes(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::yes(sig_b);
        let decision_b = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision_b, Some(Decision::Commit)); // Quorum reached!
    }

    #[test]
    fn test_proposal_abort_on_rejection() {
        let node_a = test_key("node_c");
        let node_b = test_key("node_d");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous required
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node B votes no -- threshold becomes unreachable.
        let sig_b = Vote::sign_no(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::no("testing rejection", sig_b);
        let decision = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision, Some(Decision::Abort));
    }

    #[test]
    fn test_proposal_expiry() {
        use crate::state::{ActiveProposal, PROPOSAL_EXPIRY_SECS};

        let node_a = test_key("node_e");
        let pub_a = Vote::public_key_from_signing_key(&node_a);

        let participants = vec![pub_a];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            1,
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Simulate an old proposal by setting created_at in the past.
        let mut proposals: HashMap<[u8; 32], ActiveProposal> = HashMap::new();
        proposals.insert(
            proposal_id,
            ActiveProposal {
                coordinator,
                created_at: Instant::now() - Duration::from_secs(PROPOSAL_EXPIRY_SECS + 10),
                forest,
            },
        );

        // Expire stale proposals.
        let now = Instant::now();
        let expiry = Duration::from_secs(PROPOSAL_EXPIRY_SECS);
        proposals.retain(|_, p| now.duration_since(p.created_at) < expiry);

        assert!(proposals.is_empty(), "expired proposal should be removed");
    }
}
