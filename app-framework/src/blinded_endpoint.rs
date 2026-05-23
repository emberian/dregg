//! HTTP wrapper around [`BlindedQueue`] and [`FairDistribution`].
//!
//! `FairDistributionEndpoint` exposes four routes:
//!
//! - `POST /commit` — submit a commitment to the blinded queue.
//! - `POST /consume` — consume with a public proof (reveals which commitment).
//! - `POST /consume-private` — consume with a ZK spending proof (hides which commitment).
//! - `GET /status` — queue status JSON.
//!
//! All privacy-preserving mechanics (nullifier uniqueness, Merkle membership) live in
//! `pyana_storage::blinded`. This module is a thin HTTP skin.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::blinded_endpoint::FairDistributionEndpoint;
//!
//! let endpoint = FairDistributionEndpoint::new(64)
//!     .with_distribution(32, current_height + 1000);
//! let app = AppServer::new(config)
//!     .with_blinded_endpoint("/airdrop", endpoint)
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

use pyana_storage::blinded::{
    BlindedQueue, ConsumptionProof, ConsumeResult, FairDistribution, PrivateConsumptionProof,
};

use crate::server::api_error;

// =============================================================================
// Request / response types
// =============================================================================

/// Request body for `POST /commit`.
#[derive(Debug, Deserialize)]
pub struct CommitRequest {
    /// Commitment hash (hex-encoded 32 bytes).
    pub commitment_hex: String,
}

/// Response from `POST /commit`.
#[derive(Debug, Serialize)]
pub struct CommitResponse {
    /// New commitment tree root (hex).
    pub root_hex: String,
}

/// Request body for `POST /consume` (public proof, reveals commitment).
#[derive(Debug, Deserialize)]
pub struct ConsumePublicRequest {
    /// Nullifier (hex-encoded 32 bytes).
    pub nullifier_hex: String,
    /// Commitment being consumed (hex-encoded 32 bytes).
    pub commitment_hex: String,
    /// Position in the tree.
    pub position: usize,
    /// Merkle sibling hashes (hex-encoded 32 bytes each).
    pub membership_proof: Vec<String>,
}

/// Request body for `POST /consume-private` (ZK proof, hides commitment).
#[derive(Debug, Deserialize)]
pub struct ConsumePrivateRequest {
    /// Nullifier (hex-encoded 32 bytes).
    pub nullifier_hex: String,
    /// Commitment tree root at time of consumption (hex-encoded 32 bytes).
    pub tree_root_hex: String,
    /// STARK spending proof bytes (hex-encoded).
    pub spending_proof_hex: String,
}

/// Response from consume operations.
#[derive(Debug, Serialize)]
pub struct ConsumeResponse {
    pub result: String,
    pub nullifier_hex: Option<String>,
}

/// Response from `GET /status`.
#[derive(Debug, Serialize)]
pub struct BlindedStatusResponse {
    pub commitment_root: String,
    pub consumed_count: usize,
    pub remaining: usize,
}

// =============================================================================
// Endpoint state
// =============================================================================

#[derive(Clone)]
struct EndpointState {
    queue: Arc<Mutex<BlindedQueue>>,
    distribution: Option<Arc<Mutex<FairDistribution>>>,
}

/// HTTP endpoint wrapping a [`BlindedQueue`] with optional [`FairDistribution`].
pub struct FairDistributionEndpoint {
    queue: Arc<Mutex<BlindedQueue>>,
    distribution: Option<Arc<Mutex<FairDistribution>>>,
}

impl FairDistributionEndpoint {
    /// Create an endpoint backed by a fresh `BlindedQueue` with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: Arc::new(Mutex::new(BlindedQueue::new(capacity))),
            distribution: None,
        }
    }

    /// Attach a `FairDistribution` layer (initializes it from the current queue).
    ///
    /// `expected_participants` is the number of parties that must claim before the
    /// distribution is considered complete. `deadline` is the block height by which
    /// all claims must be made.
    ///
    /// NOTE: This creates a NEW `FairDistribution` with no pre-committed items.
    /// To use an existing commitment set, call `FairDistribution::new` directly and
    /// wrap it yourself.
    pub fn with_distribution(mut self, expected_participants: usize, deadline: u64) -> Self {
        // Create an empty distribution (items committed later via /commit).
        let dist = FairDistribution::new(vec![], expected_participants, deadline);
        self.distribution = Some(Arc::new(Mutex::new(dist)));
        self
    }

    /// Get a clone of the inner `Arc<Mutex<BlindedQueue>>` for sharing with handlers.
    pub fn queue_arc(&self) -> Arc<Mutex<BlindedQueue>> {
        Arc::clone(&self.queue)
    }

    /// Build the axum router.
    pub fn router(self) -> Router {
        let state = EndpointState {
            queue: self.queue,
            distribution: self.distribution,
        };
        Router::new()
            .route("/commit", post(handle_commit))
            .route("/consume", post(handle_consume_public))
            .route("/consume-private", post(handle_consume_private))
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

fn consume_result_to_response(result: ConsumeResult) -> ConsumeResponse {
    match result {
        ConsumeResult::Consumed { nullifier } => ConsumeResponse {
            result: "consumed".into(),
            nullifier_hex: Some(hex_encode(&nullifier)),
        },
        ConsumeResult::AlreadyConsumed => ConsumeResponse {
            result: "already_consumed".into(),
            nullifier_hex: None,
        },
        ConsumeResult::InvalidProof => ConsumeResponse {
            result: "invalid_proof".into(),
            nullifier_hex: None,
        },
    }
}

// =============================================================================
// Handlers
// =============================================================================

async fn handle_commit(
    State(state): State<EndpointState>,
    Json(req): Json<CommitRequest>,
) -> Result<Json<CommitResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let commitment = parse_hex32(&req.commitment_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid commitment_hex"))?;

    let mut q = state.queue.lock().await;
    q.commit(commitment)
        .map_err(|e| api_error(StatusCode::UNPROCESSABLE_ENTITY, format!("commit failed: {e:?}")))?;

    Ok(Json(CommitResponse {
        root_hex: hex_encode(&q.commitment_root()),
    }))
}

async fn handle_consume_public(
    State(state): State<EndpointState>,
    Json(req): Json<ConsumePublicRequest>,
) -> Result<Json<ConsumeResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let nullifier = parse_hex32(&req.nullifier_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid nullifier_hex"))?;
    let commitment = parse_hex32(&req.commitment_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid commitment_hex"))?;

    let mut membership_proof = Vec::with_capacity(req.membership_proof.len());
    for s in &req.membership_proof {
        let h = parse_hex32(s)
            .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid membership_proof entry"))?;
        membership_proof.push(h);
    }

    let proof = ConsumptionProof {
        nullifier,
        commitment,
        position: req.position,
        membership_proof,
    };

    let mut q = state.queue.lock().await;
    let result = q.consume(&proof);
    Ok(Json(consume_result_to_response(result)))
}

async fn handle_consume_private(
    State(state): State<EndpointState>,
    Json(req): Json<ConsumePrivateRequest>,
) -> Result<Json<ConsumeResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let nullifier = parse_hex32(&req.nullifier_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid nullifier_hex"))?;
    let tree_root = parse_hex32(&req.tree_root_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid tree_root_hex"))?;

    // Decode the spending proof from hex.
    let spending_proof: Vec<u8> = if req.spending_proof_hex.len() % 2 != 0 {
        return Err(api_error(StatusCode::BAD_REQUEST, "spending_proof_hex must have even length"));
    } else {
        (0..req.spending_proof_hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&req.spending_proof_hex[i..i + 2], 16))
            .collect::<Result<_, _>>()
            .map_err(|_| api_error(StatusCode::BAD_REQUEST, "invalid spending_proof_hex"))?
    };

    let proof = PrivateConsumptionProof {
        nullifier,
        tree_root,
        spending_proof,
    };

    let mut q = state.queue.lock().await;
    let result = q.consume_private(&proof);
    Ok(Json(consume_result_to_response(result)))
}

async fn handle_status(State(state): State<EndpointState>) -> Json<BlindedStatusResponse> {
    let q = state.queue.lock().await;
    Json(BlindedStatusResponse {
        commitment_root: hex_encode(&q.commitment_root()),
        consumed_count: q.consumed_count(),
        remaining: q.remaining(),
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

    #[tokio::test]
    async fn commit_and_status_roundtrip() {
        let endpoint = FairDistributionEndpoint::new(16);
        let app = endpoint.router();

        // Commit a dummy commitment.
        let commitment_hex = format!("{:064x}", 42u64);
        let body = serde_json::json!({ "commitment_hex": commitment_hex });
        let req = Request::builder()
            .method(Method::POST)
            .uri("/commit")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(&body).unwrap()))
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);

        // Check status.
        let req = Request::builder()
            .method(Method::GET)
            .uri("/status")
            .body(Body::empty())
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        let status: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(status["consumed_count"], 0);
        assert_eq!(status["remaining"], 1);
    }
}
