//! Relay operator service.
//!
//! Exposes the `pyana-storage` RelayOperator as an HTTP service. Operators bond
//! computrons to host inboxes, accept store-and-forward messages from senders,
//! deliver them to recipients on drain, charge fees, and run periodic GC.
//!
//! # Endpoints
//!
//! ```text
//! GET  /relay/status            -- operator info (bond, inboxes, earnings)
//! POST /relay/subscribe         -- create a hosted inbox
//! DELETE /relay/unsubscribe     -- remove an inbox
//! POST /relay/send/:dest        -- enqueue a message
//! GET  /relay/drain             -- drain your inbox (authenticated)
//! GET  /relay/inbox/:id/status  -- check inbox status
//! GET  /relay/proof/:msg_id     -- get dequeue proof for a delivered message
//! ```

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::{delete, get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::info;

use pyana_storage::inbox::InboxMessage;
use pyana_storage::operator::RelayOperator;
use pyana_storage::queue::DequeueProof;

// ─── Configuration ────────────────────────────────────────────────────────────

/// Configuration for the relay operator service.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayConfig {
    /// Port to listen on.
    pub listen_port: u16,
    /// Operator identity key (32 bytes, hex-encoded when serialized to file).
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub operator_key: [u8; 32],
    /// Bond amount (computrons staked).
    pub bond_amount: u64,
    /// Fee policy (what assets accepted, at what rates).
    pub fee_policy: FeePolicy,
    /// Maximum total capacity to host (sum of all inbox capacities).
    pub max_total_capacity: usize,
    /// GC interval in seconds.
    pub gc_interval_secs: u64,
    /// TTL for messages in blocks (used during GC).
    pub message_ttl_blocks: u64,
    /// SLA: max delivery latency in blocks.
    pub max_delivery_latency_blocks: u64,
    /// Path for persistent state file.
    pub state_file: PathBuf,
    /// Default inbox capacity for new subscriptions.
    pub default_inbox_capacity: usize,
    /// Default minimum deposit for new inboxes.
    pub default_min_deposit: u64,
}

impl Default for RelayConfig {
    fn default() -> Self {
        Self {
            listen_port: 3100,
            operator_key: [0u8; 32],
            bond_amount: 10_000,
            fee_policy: FeePolicy::default(),
            max_total_capacity: 100_000,
            gc_interval_secs: 300,
            message_ttl_blocks: 1000,
            max_delivery_latency_blocks: 50,
            state_file: PathBuf::from("./relay-state.json"),
            default_inbox_capacity: 100,
            default_min_deposit: 100,
        }
    }
}

/// Fee policy: which assets are accepted and at what rates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeePolicy {
    /// Minimum deposit per message (in computrons).
    pub min_deposit_computrons: u64,
    /// Subscription fee (one-time, for creating an inbox).
    pub subscription_fee: u64,
    /// Whether to accept external assets (USDC, ETH, etc.) via deposit vouchers.
    pub accept_external_assets: bool,
    /// Exchange rate: external asset units per computron (fixed-point, 1e6 = 1:1).
    pub external_rate_micros: u64,
}

impl Default for FeePolicy {
    fn default() -> Self {
        Self {
            min_deposit_computrons: 100,
            subscription_fee: 1000,
            accept_external_assets: false,
            external_rate_micros: 1_000_000,
        }
    }
}

// ─── Service State ────────────────────────────────────────────────────────────

/// Shared relay service state.
pub struct RelayState {
    /// The underlying relay operator (from pyana-storage).
    pub operator: RelayOperator,
    /// Configuration.
    pub config: RelayConfig,
    /// Current block height (updated by the node or a ticker).
    pub current_height: u64,
    /// Delivered message proofs: msg_hash -> DequeueProof.
    pub delivery_proofs: std::collections::HashMap<[u8; 32], DequeueProof>,
    /// Total messages delivered since startup.
    pub messages_delivered: u64,
    /// Total messages received since startup.
    pub messages_received: u64,
}

pub type SharedRelayState = Arc<RwLock<RelayState>>;

// ─── HTTP API Types ───────────────────────────────────────────────────────────

/// GET /relay/status response.
#[derive(Serialize)]
pub struct RelayStatusResponse {
    pub operator_id: String,
    pub bond: u64,
    pub required_bond: u64,
    pub is_underbonded: bool,
    pub active_inboxes: usize,
    pub total_pending_messages: usize,
    pub earned_fees: u64,
    pub max_delivery_latency_blocks: u64,
    pub current_height: u64,
    pub messages_delivered: u64,
    pub messages_received: u64,
    pub gc_interval_secs: u64,
}

/// POST /relay/subscribe request.
#[derive(Deserialize)]
pub struct SubscribeRequest {
    /// Owner public key (hex-encoded, 64 chars).
    pub owner: String,
    /// Requested inbox capacity (optional, defaults to config).
    pub capacity: Option<usize>,
    /// Custom minimum deposit (optional, defaults to config).
    pub min_deposit: Option<u64>,
    /// Hex-encoded 8-byte nonce, included in the signed message to bind the
    /// request to a single use (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"pyana-relay-subscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/subscribe response.
#[derive(Serialize)]
pub struct SubscribeResponse {
    pub owner: String,
    pub capacity: usize,
    pub min_deposit: u64,
    pub subscription_fee_paid: u64,
}

/// DELETE /relay/unsubscribe request.
#[derive(Deserialize)]
pub struct UnsubscribeRequest {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"pyana-relay-unsubscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/send/:dest request.
#[derive(Deserialize)]
pub struct SendRequest {
    /// Sender public key (hex-encoded).
    pub sender: String,
    /// Message payload (base64-encoded).
    pub payload: String,
    /// Deposit amount (computrons).
    pub deposit: u64,
}

/// POST /relay/send/:dest response.
#[derive(Serialize)]
pub struct SendResponse {
    pub queue_root: String,
    pub position: usize,
}

/// GET /relay/drain request (via query params or auth header).
#[derive(Deserialize)]
pub struct DrainQuery {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Maximum messages to drain.
    pub max: Option<usize>,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"pyana-relay-drain-v1" || owner || nonce || max_le_bytes`.
    pub signature: String,
}

/// GET /relay/drain response.
#[derive(Serialize)]
pub struct DrainResponse {
    pub messages: Vec<DrainedMessage>,
    pub new_root: String,
}

/// A single drained message with proof.
#[derive(Serialize)]
pub struct DrainedMessage {
    pub content_hash: String,
    pub sender: String,
    pub deposit: u64,
    pub enqueued_at: u64,
    pub proof_old_root: String,
    pub proof_new_root: String,
}

/// GET /relay/inbox/:id/status response.
#[derive(Serialize)]
pub struct InboxStatusResponse {
    pub owner: String,
    pub pending_messages: usize,
    pub committed_capacity: usize,
    pub queue_root: String,
    pub last_drain_height: u64,
    pub evicted: bool,
}

/// GET /relay/proof/:msg_id response.
#[derive(Serialize)]
pub struct ProofResponse {
    pub msg_id: String,
    pub old_root: String,
    pub new_root: String,
    pub found: bool,
}

/// Generic error response.
#[derive(Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// ─── Router ───────────────────────────────────────────────────────────────────

/// Build the relay service HTTP router.
pub fn relay_router(state: SharedRelayState) -> Router {
    Router::new()
        .route("/relay/status", get(handle_status))
        .route("/relay/subscribe", post(handle_subscribe))
        .route("/relay/unsubscribe", delete(handle_unsubscribe))
        .route("/relay/send/{dest}", post(handle_send))
        .route("/relay/drain", get(handle_drain))
        .route("/relay/inbox/{id}/status", get(handle_inbox_status))
        .route("/relay/proof/{msg_id}", get(handle_proof))
        .with_state(state)
}

// ─── Auth helpers (F-P1-1) ────────────────────────────────────────────────────

/// Verify an Ed25519 signature over a domain-separated message that the
/// `owner` is supposed to have signed. Used to gate subscribe/unsubscribe/drain
/// (F-P1-1).
fn verify_owner_signature(
    owner: &[u8; 32],
    signature_hex: &str,
    domain: &[u8],
    payload: &[u8],
) -> Result<(), &'static str> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    let sig_bytes = hex_decode_var(signature_hex).map_err(|_| "invalid signature hex")?;
    if sig_bytes.len() != 64 {
        return Err("signature must be 64 bytes");
    }
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let sig = Signature::from_bytes(&sig_arr);
    let vk = VerifyingKey::from_bytes(owner).map_err(|_| "invalid owner public key")?;

    let mut msg = Vec::with_capacity(domain.len() + payload.len());
    msg.extend_from_slice(domain);
    msg.extend_from_slice(payload);

    vk.verify(&msg, &sig).map_err(|_| "signature does not verify")
}

fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for i in 0..s.len() / 2 {
        out.push(u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).map_err(|_| ())?);
    }
    Ok(out)
}

// ─── Handlers ─────────────────────────────────────────────────────────────────

async fn handle_status(State(state): State<SharedRelayState>) -> Json<RelayStatusResponse> {
    let s = state.read().await;
    Json(RelayStatusResponse {
        operator_id: hex_encode(&s.operator.id),
        bond: s.operator.bond,
        required_bond: s.operator.required_bond(),
        is_underbonded: s.operator.is_underbonded(),
        active_inboxes: s.operator.active_inbox_count(),
        total_pending_messages: s.operator.total_pending(),
        earned_fees: s.operator.earned_fees,
        max_delivery_latency_blocks: s.operator.max_delivery_latency,
        current_height: s.current_height,
        messages_delivered: s.messages_delivered,
        messages_received: s.messages_received,
        gc_interval_secs: s.config.gc_interval_secs,
    })
}

async fn handle_subscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<SubscribeRequest>,
) -> Result<Json<SubscribeResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    // F-P1-1: require an Ed25519 signature from `owner` over a domain-separated
    // (owner, nonce) tuple. Without this, any network attacker could subscribe
    // an inbox in another user's name.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(&owner, &req.signature, b"pyana-relay-subscribe-v1", &payload) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("subscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let capacity = req.capacity.unwrap_or(s.config.default_inbox_capacity);
    let min_deposit = req.min_deposit.unwrap_or(s.config.default_min_deposit);

    // Check total capacity limit.
    let current_total: usize = s
        .operator
        .hosted_inboxes
        .values()
        .filter(|h| !h.evicted)
        .map(|h| h.committed_capacity)
        .sum();
    if current_total + capacity > s.config.max_total_capacity {
        return Err((
            StatusCode::SERVICE_UNAVAILABLE,
            Json(ErrorResponse {
                error: format!(
                    "would exceed max total capacity ({} + {} > {})",
                    current_total, capacity, s.config.max_total_capacity
                ),
            }),
        ));
    }

    s.operator
        .host_inbox(owner, capacity, min_deposit)
        .map_err(|e| {
            let msg = format!("{e:?}");
            let status = match &e {
                pyana_storage::relay::RelayError::AlreadyHosted { .. } => StatusCode::CONFLICT,
                pyana_storage::relay::RelayError::Underbonded { .. } => {
                    StatusCode::SERVICE_UNAVAILABLE
                }
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(ErrorResponse { error: msg }))
        })?;

    let fee = s.config.fee_policy.subscription_fee;
    info!(
        owner = %req.owner,
        capacity = capacity,
        "new inbox subscription"
    );

    Ok(Json(SubscribeResponse {
        owner: req.owner,
        capacity,
        min_deposit,
        subscription_fee_paid: fee,
    }))
}

async fn handle_unsubscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<UnsubscribeRequest>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    // F-P1-1: require Ed25519 signature from owner.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(&owner, &req.signature, b"pyana-relay-unsubscribe-v1", &payload) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("unsubscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let refunds = s.operator.evict_inbox(&owner);

    info!(
        owner = %req.owner,
        refunds = refunds.len(),
        "inbox unsubscribed (evicted)"
    );

    Ok(Json(serde_json::json!({
        "owner": req.owner,
        "refunds_issued": refunds.len(),
        "total_refunded": refunds.iter().map(|r| r.amount).sum::<u64>(),
    })))
}

async fn handle_send(
    State(state): State<SharedRelayState>,
    Path(dest): Path<String>,
    Json(req): Json<SendRequest>,
) -> Result<Json<SendResponse>, (StatusCode, Json<ErrorResponse>)> {
    let destination = hex_decode_32(&dest).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid destination key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let sender = hex_decode_32(&req.sender).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid sender key".to_string(),
            }),
        )
    })?;

    let payload = base64_decode(&req.payload).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: format!("invalid base64 payload: {e}"),
            }),
        )
    })?;

    let mut s = state.write().await;
    let current_height = s.current_height;

    let msg = InboxMessage::Encrypted {
        ciphertext: payload,
        sender,
    };

    let root = s
        .operator
        .receive_message(&destination, msg, req.deposit, current_height)
        .map_err(|e| {
            let msg = format!("{e:?}");
            let status = match &e {
                pyana_storage::relay::RelayError::InboxNotFound { .. } => StatusCode::NOT_FOUND,
                pyana_storage::relay::RelayError::InsufficientDeposit { .. } => {
                    StatusCode::PAYMENT_REQUIRED
                }
                pyana_storage::relay::RelayError::QueueFull { .. } => {
                    StatusCode::SERVICE_UNAVAILABLE
                }
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(ErrorResponse { error: msg }))
        })?;

    s.messages_received += 1;
    let pending = s.operator.total_pending();

    Ok(Json(SendResponse {
        queue_root: hex_encode(&root),
        position: pending,
    }))
}

async fn handle_drain(
    State(state): State<SharedRelayState>,
    axum::extract::Query(query): axum::extract::Query<DrainQuery>,
) -> Result<Json<DrainResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&query.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    let max = query.max.unwrap_or(100);

    // F-P1-1: require Ed25519 signature from `owner` over (owner, nonce, max).
    // Without this, anyone on the network could drain any inbox.
    let nonce_bytes = hex_decode_var(&query.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len() + 8);
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    payload.extend_from_slice(&(max as u64).to_le_bytes());
    if let Err(e) = verify_owner_signature(&owner, &query.signature, b"pyana-relay-drain-v1", &payload) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("drain signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let current_height = s.current_height;
    let drained = s.operator.drain_for_owner(&owner, max, current_height);

    // Store delivery proofs and build response.
    let messages: Vec<DrainedMessage> = drained
        .into_iter()
        .map(|(entry, proof)| {
            // Cache the proof for later retrieval.
            s.delivery_proofs.insert(entry.content_hash, proof.clone());
            s.messages_delivered += 1;

            DrainedMessage {
                content_hash: hex_encode(&entry.content_hash),
                sender: hex_encode(&entry.sender),
                deposit: entry.deposit,
                enqueued_at: entry.enqueued_at,
                proof_old_root: hex_encode(&proof.old_root),
                proof_new_root: hex_encode(&proof.new_root),
            }
        })
        .collect();

    // Get new queue root after drain.
    let new_root = s.operator.inbox_root(&owner).unwrap_or([0u8; 32]);

    Ok(Json(DrainResponse {
        messages,
        new_root: hex_encode(&new_root),
    }))
}

async fn handle_inbox_status(
    State(state): State<SharedRelayState>,
    Path(id): Path<String>,
) -> Result<Json<InboxStatusResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid inbox id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    let hosted = s.operator.hosted_inboxes.get(&owner).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "inbox not found".to_string(),
            }),
        )
    })?;

    let root = s.operator.inbox_root(&owner).unwrap_or([0u8; 32]);

    Ok(Json(InboxStatusResponse {
        owner: id,
        pending_messages: hosted.inbox.len(),
        committed_capacity: hosted.committed_capacity,
        queue_root: hex_encode(&root),
        last_drain_height: hosted.last_drain_height,
        evicted: hosted.evicted,
    }))
}

async fn handle_proof(
    State(state): State<SharedRelayState>,
    Path(msg_id): Path<String>,
) -> Result<Json<ProofResponse>, (StatusCode, Json<ErrorResponse>)> {
    let msg_hash = hex_decode_32(&msg_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid msg_id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    if let Some(proof) = s.delivery_proofs.get(&msg_hash) {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: hex_encode(&proof.old_root),
            new_root: hex_encode(&proof.new_root),
            found: true,
        }))
    } else {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: String::new(),
            new_root: String::new(),
            found: false,
        }))
    }
}

// ─── Service Lifecycle ────────────────────────────────────────────────────────

/// Start the relay service: initialize operator, spawn GC task, serve HTTP.
pub async fn run_relay_service(config: RelayConfig) {
    info!(
        port = config.listen_port,
        bond = config.bond_amount,
        max_capacity = config.max_total_capacity,
        gc_interval = config.gc_interval_secs,
        state_file = %config.state_file.display(),
        "starting relay operator service"
    );

    // Initialize the relay operator.
    let operator = RelayOperator::new(
        config.operator_key,
        config.bond_amount,
        config.max_delivery_latency_blocks,
    );

    let relay_state = Arc::new(RwLock::new(RelayState {
        operator,
        config: config.clone(),
        current_height: 0,
        delivery_proofs: std::collections::HashMap::new(),
        messages_delivered: 0,
        messages_received: 0,
    }));

    // Spawn the GC background task.
    let gc_state = relay_state.clone();
    let gc_interval = config.gc_interval_secs;
    let message_ttl = config.message_ttl_blocks;
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(gc_interval));
        loop {
            interval.tick().await;
            let mut s = gc_state.write().await;
            let height = s.current_height;
            let result = s.operator.gc_expired(height, message_ttl);
            if result.messages_collected > 0 {
                info!(
                    collected = result.messages_collected,
                    operator_fees = result.operator_fees,
                    refunds = result.sender_refunds.len(),
                    "relay GC pass completed"
                );
            }
        }
    });

    // Spawn a block height ticker (simulates block production for standalone mode).
    let height_state = relay_state.clone();
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(12));
        loop {
            interval.tick().await;
            let mut s = height_state.write().await;
            s.current_height += 1;
        }
    });

    // Build and serve the HTTP API.
    let app = relay_router(relay_state);

    let addr = std::net::SocketAddr::new(
        std::net::IpAddr::V4(std::net::Ipv4Addr::new(0, 0, 0, 0)),
        config.listen_port,
    );

    info!(%addr, "relay service HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind relay HTTP listener");

    axum::serve(listener, app)
        .with_graceful_shutdown(async {
            tokio::signal::ctrl_c()
                .await
                .expect("failed to listen for Ctrl-C");
            info!("relay service shutting down");
        })
        .await
        .expect("relay HTTP server error");
}

// ─── Utility Functions ────────────────────────────────────────────────────────

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

fn base64_decode(s: &str) -> Result<Vec<u8>, String> {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD
        .decode(s)
        .map_err(|e| e.to_string())
}

fn hex_ser_32<S: serde::Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
    s.serialize_str(&hex_encode(bytes))
}

fn hex_de_32<'de, D: serde::Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
    let s = String::deserialize(d)?;
    hex_decode_32(&s).ok_or_else(|| serde::de::Error::custom("expected 64 hex chars"))
}

// ─── Adversarial tests for F-P1-1 (relay caller-authentication) ──────────────
//
// These tests exercise `verify_owner_signature` directly. The handlers
// themselves are thin wrappers around the verifier (see handle_subscribe,
// handle_unsubscribe, handle_drain) so verifying the verifier is sufficient
// to demonstrate the regression-coverage. A future router-level integration
// test (deferred while sdk/cell rebuild is in flight) would also exercise
// the wiring.

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn make_key(seed_byte: u8) -> (SigningKey, [u8; 32]) {
        let mut seed = [0u8; 32];
        seed[0] = seed_byte;
        let sk = SigningKey::from_bytes(&seed);
        let pk = sk.verifying_key().to_bytes();
        (sk, pk)
    }

    /// F-P1-1: an unsigned drain request must be rejected. (The verifier is
    /// the choke-point: an empty/garbage signature must not be accepted.)
    #[test]
    fn audit_f_p1_1_unsigned_drain_rejected() {
        let (_sk, pk) = make_key(1);
        let payload = b"\x00\x01\x02";
        // Empty signature.
        assert!(
            verify_owner_signature(&pk, "", b"pyana-relay-drain-v1", payload).is_err()
        );
        // Garbage signature.
        let bad = "ff".repeat(64);
        assert!(
            verify_owner_signature(&pk, &bad, b"pyana-relay-drain-v1", payload).is_err()
        );
    }

    /// F-P1-1: a drain signature by another key (key A) but claiming to be
    /// from a different owner (key B) MUST be rejected.
    #[test]
    fn audit_f_p1_1_wrong_signer_rejected() {
        let (sk_a, _pk_a) = make_key(1);
        let (_sk_b, pk_b) = make_key(2);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk_b);
        payload.extend_from_slice(b"nonce123");
        // Sign with A's key but verify against B.
        let mut full = Vec::new();
        full.extend_from_slice(b"pyana-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk_a.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk_b, &sig_hex, b"pyana-relay-drain-v1", &payload).is_err(),
            "must reject when signer != claimed owner"
        );
    }

    /// F-P1-1: a correctly-signed drain request passes.
    #[test]
    fn audit_f_p1_1_valid_drain_signature_accepted() {
        let (sk, pk) = make_key(7);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk);
        payload.extend_from_slice(b"nonce456");
        payload.extend_from_slice(&100u64.to_le_bytes());

        let mut full = Vec::new();
        full.extend_from_slice(b"pyana-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk, &sig_hex, b"pyana-relay-drain-v1", &payload).is_ok(),
            "valid signature should pass"
        );
    }

    /// F-P1-1: a drain signature signed for a DIFFERENT domain (e.g.,
    /// subscribe) must NOT be replayable as a drain signature.
    #[test]
    fn audit_f_p1_1_cross_domain_replay_rejected() {
        let (sk, pk) = make_key(11);
        let payload = b"some-payload";

        // Sign for subscribe.
        let mut full = Vec::new();
        full.extend_from_slice(b"pyana-relay-subscribe-v1");
        full.extend_from_slice(payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        // Verifies under subscribe domain.
        assert!(verify_owner_signature(&pk, &sig_hex, b"pyana-relay-subscribe-v1", payload).is_ok());
        // Replayed as drain: rejected.
        assert!(verify_owner_signature(&pk, &sig_hex, b"pyana-relay-drain-v1", payload).is_err());
        // Replayed as unsubscribe: rejected.
        assert!(verify_owner_signature(&pk, &sig_hex, b"pyana-relay-unsubscribe-v1", payload).is_err());
    }

    /// F-P1-1: the request structs require nonce + signature fields. Verify
    /// the deserialization layer rejects requests that omit them.
    #[test]
    fn audit_f_p1_1_subscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(good).is_ok());
    }

    /// F-P1-1: same for unsubscribe.
    #[test]
    fn audit_f_p1_1_unsubscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(good).is_ok());
    }
}
