//! Axum extractors for verifying pyana presentation proofs from request headers.
//!
//! Extracts and verifies the `X-Pyana-Proof` header using
//! `PyanaEngine::verify_presentation_bytes()`.
//!
//! Two extractors are provided:
//!
//! - [`StrictPresentation`]: Rejects the request with 403 **before the handler runs**
//!   if verification fails. This is the correct default for almost all handlers.
//!
//! - [`OptionalPresentation`]: Succeeds even if verification fails. Useful for
//!   diagnostics endpoints or partial-auth flows where the handler wants to inspect
//!   an unverified proof.
//!
//! # Usage
//!
//! ```ignore
//! use axum::{Router, routing::get};
//! use pyana_app_framework::middleware::StrictPresentation;
//!
//! async fn protected(proof: StrictPresentation) -> &'static str {
//!     // If we got here, verification already passed.
//!     "access granted"
//! }
//!
//! let app = Router::new()
//!     .route("/protected", get(protected))
//!     .with_state(engine_state);
//! ```

use std::sync::Arc;

use axum::extract::FromRequestParts;
use axum::http::StatusCode;
use axum::http::request::Parts;
use tokio::sync::RwLock;

use pyana_sdk::embed::PyanaEngine;

// =============================================================================
// StrictPresentation
// =============================================================================

/// Strict extractor: rejects unverified presentations with 403 before the handler runs.
///
/// If the proof header is missing, returns 401. If decoding fails, returns 400.
/// If STARK verification fails, returns 403. The handler never sees unverified proofs.
#[derive(Clone, Debug)]
pub struct StrictPresentation {
    /// The action field from the proof (BLAKE3 hash of action string).
    pub action: [u8; 32],
    /// The resource field from the proof (BLAKE3 hash of resource string).
    pub resource: [u8; 32],
    /// The federation root the proof was verified against.
    pub federation_root: [u8; 32],
}

impl FromRequestParts<EngineState> for StrictPresentation {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &EngineState,
    ) -> Result<Self, Self::Rejection> {
        // Extract the proof header.
        let proof_header = parts
            .headers
            .get(PROOF_HEADER)
            .ok_or((StatusCode::UNAUTHORIZED, "missing X-Pyana-Proof header"))?;

        let proof_b64 = proof_header.to_str().map_err(|_| {
            (
                StatusCode::BAD_REQUEST,
                "X-Pyana-Proof header is not valid UTF-8",
            )
        })?;

        // Decode base64.
        use base64::Engine as _;
        let proof_bytes = base64::engine::general_purpose::STANDARD
            .decode(proof_b64)
            .map_err(|_| (StatusCode::BAD_REQUEST, "X-Pyana-Proof is not valid base64"))?;

        // Extract action/resource from headers (hashed for binding).
        let action = extract_hash_header(&parts.headers, ACTION_HEADER);
        let resource = extract_hash_header(&parts.headers, RESOURCE_HEADER);

        // Verify against the engine.
        let engine = state.0.read().await;
        let federation_root = engine.federation_root();
        let verified = engine.verify_presentation_bytes(&proof_bytes);

        if !verified {
            return Err((
                StatusCode::FORBIDDEN,
                "presentation proof verification failed",
            ));
        }

        Ok(StrictPresentation {
            action,
            resource,
            federation_root,
        })
    }
}

// =============================================================================
// OptionalPresentation
// =============================================================================

/// Optional extractor: succeeds even if verification fails (for diagnostics).
///
/// Use this only when the handler needs to inspect an unverified proof — for example,
/// a diagnostics endpoint that reports *why* verification failed.
///
/// For normal auth-gated endpoints, use [`StrictPresentation`] instead.
#[derive(Clone, Debug)]
pub struct OptionalPresentation {
    /// Whether the proof cryptographically verified.
    pub verified: bool,
    /// The action field from the proof (BLAKE3 hash of action string), or None on failure.
    pub action: Option<[u8; 32]>,
    /// The resource field from the proof (BLAKE3 hash of resource string), or None on failure.
    pub resource: Option<[u8; 32]>,
    /// The federation root the proof was verified against, or None on failure.
    pub federation_root: Option<[u8; 32]>,
    /// If verification or decoding failed, the error message.
    pub error: Option<String>,
}

impl FromRequestParts<EngineState> for OptionalPresentation {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &EngineState,
    ) -> Result<Self, Self::Rejection> {
        // Extract the proof header. If missing, return an "unverified" result rather
        // than rejecting — that's the whole point of OptionalPresentation.
        let proof_header = match parts.headers.get(PROOF_HEADER) {
            Some(h) => h,
            None => {
                return Ok(OptionalPresentation {
                    verified: false,
                    action: None,
                    resource: None,
                    federation_root: None,
                    error: Some("missing X-Pyana-Proof header".into()),
                });
            }
        };

        let proof_b64 = match proof_header.to_str() {
            Ok(s) => s,
            Err(_) => {
                return Ok(OptionalPresentation {
                    verified: false,
                    action: None,
                    resource: None,
                    federation_root: None,
                    error: Some("X-Pyana-Proof header is not valid UTF-8".into()),
                });
            }
        };

        // Decode base64.
        use base64::Engine as _;
        let proof_bytes = match base64::engine::general_purpose::STANDARD.decode(proof_b64) {
            Ok(b) => b,
            Err(e) => {
                return Ok(OptionalPresentation {
                    verified: false,
                    action: None,
                    resource: None,
                    federation_root: None,
                    error: Some(format!("X-Pyana-Proof is not valid base64: {e}")),
                });
            }
        };

        // Extract action/resource from headers (hashed for binding).
        let action = extract_hash_header(&parts.headers, ACTION_HEADER);
        let resource = extract_hash_header(&parts.headers, RESOURCE_HEADER);

        // Verify against the engine.
        let engine = state.0.read().await;
        let federation_root = engine.federation_root();
        let verified = engine.verify_presentation_bytes(&proof_bytes);

        if verified {
            Ok(OptionalPresentation {
                verified: true,
                action: Some(action),
                resource: Some(resource),
                federation_root: Some(federation_root),
                error: None,
            })
        } else {
            Ok(OptionalPresentation {
                verified: false,
                action: Some(action),
                resource: Some(resource),
                federation_root: Some(federation_root),
                error: Some("presentation proof verification failed".into()),
            })
        }
    }
}

// =============================================================================
// Shared types and helpers
// =============================================================================

/// Shared engine state that the extractors read from.
///
/// Wrap your `PyanaEngine` in this type and pass it as axum state:
///
/// ```ignore
/// let state = EngineState(Arc::new(RwLock::new(engine)));
/// Router::new().with_state(state);
/// ```
#[derive(Clone)]
pub struct EngineState(pub Arc<RwLock<PyanaEngine>>);

/// Header name for the base64-encoded presentation proof.
pub const PROOF_HEADER: &str = "x-pyana-proof";

/// Header name for the action being authorized (optional, for binding check).
pub const ACTION_HEADER: &str = "x-pyana-action";

/// Header name for the resource being accessed (optional, for binding check).
pub const RESOURCE_HEADER: &str = "x-pyana-resource";

/// Extract a header value and hash it to 32 bytes, or return zeroes if absent.
fn extract_hash_header(headers: &axum::http::HeaderMap, name: &str) -> [u8; 32] {
    headers
        .get(name)
        .and_then(|v| v.to_str().ok())
        .map(|s| *blake3::hash(s.as_bytes()).as_bytes())
        .unwrap_or([0u8; 32])
}
