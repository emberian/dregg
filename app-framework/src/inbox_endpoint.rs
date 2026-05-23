//! HTTP wrapper around [`CapInbox`].
//!
//! `InboxEndpoint` exposes three routes:
//!
//! - `POST /send` — deliver a message to the inbox with a deposit.
//! - `GET /next` — owner reads the next queued entry.
//! - `GET /status` — inbox status JSON.
//!
//! All spam-prevention and Merkle accounting lives in `pyana_storage::inbox::CapInbox`.
//! This module is a thin HTTP skin.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::inbox_endpoint::InboxEndpoint;
//!
//! let endpoint = InboxEndpoint::new(256, 100).ttl_blocks(1000);
//! let app = AppServer::new(config)
//!     .with_inbox("/inbox", endpoint)
//!     .serve();
//! ```

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::Mutex;

use pyana_storage::{
    QuotaId,
    inbox::{CapInbox, InboxMessage},
};

use crate::server::api_error;

// =============================================================================
// Request / response types
// =============================================================================

/// Request body for `POST /send` — delivers a message.
///
/// The message type is determined by which optional field is populated:
/// - `cert_bytes_hex` → `InboxMessage::Capability`
/// - `uri` → `InboxMessage::SturdyRef`
/// - `ciphertext_hex` → `InboxMessage::Encrypted`
#[derive(Debug, Deserialize)]
pub struct SendRequest {
    /// Sender identity (hex-encoded 32 bytes).
    pub sender_hex: String,
    /// Deposit paid by sender (must meet `min_deposit`).
    pub deposit: u64,
    /// Capability certificate bytes (hex-encoded). Mutually exclusive with the others.
    pub cert_bytes_hex: Option<String>,
    /// Sturdy-ref URI string. Mutually exclusive with the others.
    pub uri: Option<String>,
    /// Encrypted ciphertext (hex-encoded). Mutually exclusive with the others.
    pub ciphertext_hex: Option<String>,
}

/// Response from `POST /send`.
#[derive(Debug, Serialize)]
pub struct SendResponse {
    /// New inbox root hash (hex).
    pub root_hex: String,
}

/// Response from `GET /next`.
#[derive(Debug, Serialize)]
pub struct NextResponse {
    /// Content hash of the entry (hex).
    pub content_hash_hex: String,
    /// Sender of the entry (hex).
    pub sender_hex: String,
    /// Deposit paid.
    pub deposit: u64,
    /// Block height when enqueued.
    pub enqueued_at: u64,
    /// Dequeue proof: old root before this dequeue (hex).
    pub old_root_hex: String,
    /// Dequeue proof: new root after this dequeue (hex).
    pub new_root_hex: String,
    /// Position in the queue.
    pub position: usize,
}

/// Response from `GET /status`.
#[derive(Debug, Serialize)]
pub struct InboxStatusResponse {
    pub pending_messages: usize,
    pub is_full: bool,
    pub min_deposit: u64,
    pub max_message_size: usize,
    pub root_hex: String,
}

// =============================================================================
// Endpoint state
// =============================================================================

#[derive(Clone)]
struct EndpointState {
    inbox: Arc<Mutex<CapInbox>>,
    #[allow(dead_code)]
    ttl_blocks: Option<u64>,
}

/// HTTP endpoint wrapping a [`CapInbox`].
pub struct InboxEndpoint {
    inbox: Arc<Mutex<CapInbox>>,
    ttl_blocks: Option<u64>,
}

impl InboxEndpoint {
    /// Create a new inbox endpoint.
    ///
    /// * `capacity_per_user` — maximum number of messages that can be queued.
    /// * `min_deposit` — minimum deposit required from senders (anti-spam).
    ///
    /// Uses `QuotaId(0)` as the owner quota. Apps that need real quota accounting
    /// should construct `CapInbox` directly and use `InboxEndpoint::from_inbox`.
    pub fn new(capacity_per_user: usize, min_deposit: u64) -> Self {
        let inbox = CapInbox::new(QuotaId(0), capacity_per_user, min_deposit);
        Self {
            inbox: Arc::new(Mutex::new(inbox)),
            ttl_blocks: None,
        }
    }

    /// Create an endpoint from an existing `Arc<Mutex<CapInbox>>`.
    ///
    /// Use this when the app needs to share the inbox with other handlers
    /// (e.g., to push notifications from a submission handler).
    pub fn from_inbox(inbox: Arc<Mutex<CapInbox>>) -> Self {
        Self {
            inbox,
            ttl_blocks: None,
        }
    }

    /// Get a clone of the inner `Arc<Mutex<CapInbox>>` for sharing with handlers.
    pub fn inbox_arc(&self) -> Arc<Mutex<CapInbox>> {
        Arc::clone(&self.inbox)
    }

    /// Set a time-to-live (in blocks). Expired messages are evicted on GC.
    ///
    /// NOTE: Automatic GC is NOT called by the HTTP handlers — apps must call
    /// `gc_expired` on the inner `CapInbox` from their own background task.
    pub fn ttl_blocks(mut self, ttl: u64) -> Self {
        self.ttl_blocks = Some(ttl);
        self
    }

    /// Build the axum router.
    pub fn router(self) -> Router {
        let state = EndpointState {
            inbox: self.inbox,
            ttl_blocks: self.ttl_blocks,
        };
        Router::new()
            .route("/send", post(handle_send))
            .route("/next", get(handle_next))
            .route("/status", get(handle_status))
            .with_state(state)
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let bytes: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect::<Result<_, _>>()
        .ok()?;
    bytes.try_into().ok()
}

fn hex_encode(b: &[u8; 32]) -> String {
    b.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn parse_hex_bytes(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

// =============================================================================
// Handlers
// =============================================================================

async fn handle_send(
    State(state): State<EndpointState>,
    Json(req): Json<SendRequest>,
) -> Result<Json<SendResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let sender = parse_hex32(&req.sender_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid sender_hex"))?;

    // Determine message type from request.
    let msg = if let Some(cert_hex) = &req.cert_bytes_hex {
        let cert_bytes = parse_hex_bytes(cert_hex)
            .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid cert_bytes_hex"))?;
        InboxMessage::Capability { cert_bytes, sender }
    } else if let Some(uri) = &req.uri {
        InboxMessage::SturdyRef {
            uri: uri.clone(),
            sender,
        }
    } else if let Some(ct_hex) = &req.ciphertext_hex {
        let ciphertext = parse_hex_bytes(ct_hex)
            .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid ciphertext_hex"))?;
        InboxMessage::Encrypted { ciphertext, sender }
    } else {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "one of cert_bytes_hex, uri, or ciphertext_hex must be provided",
        ));
    };

    let mut inbox = state.inbox.lock().await;
    match inbox.receive(msg, req.deposit) {
        Ok(root) => Ok(Json(SendResponse {
            root_hex: hex_encode(&root),
        })),
        Err(e) => Err(api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            format!("inbox rejected: {e:?}"),
        )),
    }
}

async fn handle_next(
    State(state): State<EndpointState>,
) -> Result<Json<NextResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let mut inbox = state.inbox.lock().await;
    match inbox.read_next() {
        Ok((entry, proof)) => Ok(Json(NextResponse {
            content_hash_hex: hex_encode(&entry.content_hash),
            sender_hex: hex_encode(&entry.sender),
            deposit: entry.deposit,
            enqueued_at: entry.enqueued_at,
            old_root_hex: hex_encode(&proof.old_root),
            new_root_hex: hex_encode(&proof.new_root),
            position: proof.position,
        })),
        Err(e) => Err(api_error(
            StatusCode::NOT_FOUND,
            format!("inbox error: {e:?}"),
        )),
    }
}

async fn handle_status(State(state): State<EndpointState>) -> Json<InboxStatusResponse> {
    let inbox = state.inbox.lock().await;
    let status = inbox.status();
    Json(InboxStatusResponse {
        pending_messages: status.pending_messages,
        is_full: status.is_full,
        min_deposit: status.min_deposit,
        max_message_size: status.max_message_size,
        root_hex: hex_encode(&status.root),
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::{Method, Request};
    use tower::ServiceExt;

    fn make_sender_hex() -> String {
        format!("{:064x}", 1u64)
    }

    #[tokio::test]
    async fn send_and_read_next_roundtrip() {
        let endpoint = InboxEndpoint::new(16, 0);
        let app = endpoint.router();

        // Send a sturdy-ref message.
        let body = serde_json::json!({
            "sender_hex": make_sender_hex(),
            "deposit": 0u64,
            "uri": "pyana://test/ref"
        });
        let req = Request::builder()
            .method(Method::POST)
            .uri("/send")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(&body).unwrap()))
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);

        // Read next.
        let req = Request::builder()
            .method(Method::GET)
            .uri("/next")
            .body(Body::empty())
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        let entry: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(entry["deposit"], 0);
    }

    #[tokio::test]
    async fn status_initially_empty() {
        let endpoint = InboxEndpoint::new(8, 100);
        let app = endpoint.router();

        let req = Request::builder()
            .method(Method::GET)
            .uri("/status")
            .body(Body::empty())
            .unwrap();
        let resp = app.oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        let status: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(status["pending_messages"], 0);
        assert_eq!(status["min_deposit"], 100);
    }
}
