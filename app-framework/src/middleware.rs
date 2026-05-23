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
use tokio::sync::{Mutex, RwLock};

use pyana_sdk::embed::PyanaEngine;

// =============================================================================
// StrictPresentation
// =============================================================================

/// Strict extractor: rejects unverified presentations with 403 before the handler runs.
///
/// If the proof header is missing, returns 401. If decoding fails, returns 400.
/// If STARK verification fails, or the proof is not bound to the claimed action/resource,
/// or the proof timestamp is stale, returns 403.
/// The handler never sees unverified proofs.
///
/// The `X-Pyana-Action` and `X-Pyana-Resource` headers MUST be present. These are
/// compared against the proof's cryptographic action binding commitment — a proof
/// generated for action A will be rejected when presented claiming action B.
#[derive(Clone, Debug)]
pub struct StrictPresentation {
    /// The action string from the request header that was verified against the proof.
    pub action: String,
    /// The resource string from the request header that was verified against the proof.
    pub resource: String,
    /// The federation root the proof was verified against.
    pub federation_root: [u8; 32],
    /// The verified proof with tier information. Always Production tier.
    pub verified_proof: pyana_circuit::VerifiedProof,
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

        // Extract action/resource strings from headers.
        // These are compared against the proof's action binding commitment.
        let action = extract_str_header(&parts.headers, ACTION_HEADER)
            .ok_or((StatusCode::BAD_REQUEST, "missing X-Pyana-Action header"))?;
        let resource = extract_str_header(&parts.headers, RESOURCE_HEADER)
            .ok_or((StatusCode::BAD_REQUEST, "missing X-Pyana-Resource header"))?;

        // Verify against the engine with full action binding + freshness checks.
        let engine = state.0.lock().await;
        let federation_root = engine.federation_root();
        let verified = engine
            .verify_presentation_bytes(&proof_bytes, &action, &resource)
            .map_err(|_| (StatusCode::BAD_REQUEST, "proof decode failed"))?;

        if !verified {
            return Err((
                StatusCode::FORBIDDEN,
                "presentation proof verification failed",
            ));
        }

        // Tier enforcement removed per verification-policy-design.md:
        // If verify_presentation_bytes() passes (which delegates to verify_proof_complete),
        // the proof is cryptographically valid. The tier is a prover-side concern, not
        // a verifier-side concern. Structural stubs cannot produce valid STARK proofs,
        // so they are rejected by the cryptographic check above.
        let verified_proof = pyana_circuit::VerifiedProof::with_federation_root(
            pyana_circuit::proof_tier::stark_tier(),
            pyana_circuit::proof_tier::STARK_BACKEND,
            federation_root,
        );

        Ok(StrictPresentation {
            action,
            resource,
            federation_root,
            verified_proof,
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
    /// Whether the proof cryptographically verified (including action binding + freshness).
    pub verified: bool,
    /// The action string from the request header, or None if absent.
    pub action: Option<String>,
    /// The resource string from the request header, or None if absent.
    pub resource: Option<String>,
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

        // Extract action/resource strings from headers.
        let action = extract_str_header(&parts.headers, ACTION_HEADER);
        let resource = extract_str_header(&parts.headers, RESOURCE_HEADER);

        // Both action and resource are required for binding verification.
        let (action_str, resource_str) = match (action.as_deref(), resource.as_deref()) {
            (Some(a), Some(r)) => (a, r),
            _ => {
                return Ok(OptionalPresentation {
                    verified: false,
                    action,
                    resource,
                    federation_root: None,
                    error: Some(
                        "missing X-Pyana-Action or X-Pyana-Resource header for binding check"
                            .into(),
                    ),
                });
            }
        };

        // Verify against the engine with full action binding + freshness checks.
        let engine = state.0.lock().await;
        let federation_root = engine.federation_root();
        let result = engine.verify_presentation_bytes(&proof_bytes, action_str, resource_str);

        match result {
            Ok(true) => Ok(OptionalPresentation {
                verified: true,
                action,
                resource,
                federation_root: Some(federation_root),
                error: None,
            }),
            Ok(false) => Ok(OptionalPresentation {
                verified: false,
                action,
                resource,
                federation_root: Some(federation_root),
                error: Some("presentation proof verification failed".into()),
            }),
            Err(e) => Ok(OptionalPresentation {
                verified: false,
                action,
                resource,
                federation_root: Some(federation_root),
                error: Some(format!("proof decode error: {e}")),
            }),
        }
    }
}

// =============================================================================
// Shared types and helpers
// =============================================================================

/// Shared engine state that the extractors read from (Mutex variant).
///
/// Wrap your `PyanaEngine` in this type and pass it as axum state:
///
/// ```ignore
/// let state = EngineState(Arc::new(Mutex::new(engine)));
/// Router::new().with_state(state);
/// ```
///
/// Note: `PyanaEngine` is `Send` but not `Sync` (contains `RefCell` internally).
/// `tokio::sync::Mutex<T>` only requires `T: Send`, so this compiles correctly.
#[derive(Clone)]
pub struct EngineState(pub Arc<Mutex<PyanaEngine>>);

/// Shared engine state using `tokio::sync::Mutex` (single-accessor variant).
///
/// Use this when your app also needs mutable access to the engine (e.g., executing
/// turns). The bounty-board pattern uses this variant.
///
/// ```ignore
/// let state = MutexEngineState(Arc::new(Mutex::new(engine)));
/// ```
#[derive(Clone)]
pub struct MutexEngineState(pub Arc<tokio::sync::Mutex<PyanaEngine>>);

/// Header name for the base64-encoded presentation proof.
pub const PROOF_HEADER: &str = "x-pyana-proof";

/// Header name for the action being authorized (REQUIRED for binding check).
pub const ACTION_HEADER: &str = "x-pyana-action";

/// Header name for the resource being accessed (REQUIRED for binding check).
pub const RESOURCE_HEADER: &str = "x-pyana-resource";

/// Extract a header value as a string, or return None if absent.
fn extract_str_header(headers: &axum::http::HeaderMap, name: &str) -> Option<String> {
    headers
        .get(name)
        .and_then(|v| v.to_str().ok())
        .map(|s| s.to_string())
}

// =============================================================================
// MutexEngineState impls (for apps that need mutable engine access)
// =============================================================================

impl FromRequestParts<MutexEngineState> for StrictPresentation {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &MutexEngineState,
    ) -> Result<Self, Self::Rejection> {
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

        use base64::Engine as _;
        let proof_bytes = base64::engine::general_purpose::STANDARD
            .decode(proof_b64)
            .map_err(|_| (StatusCode::BAD_REQUEST, "X-Pyana-Proof is not valid base64"))?;

        let action = extract_str_header(&parts.headers, ACTION_HEADER)
            .ok_or((StatusCode::BAD_REQUEST, "missing X-Pyana-Action header"))?;
        let resource = extract_str_header(&parts.headers, RESOURCE_HEADER)
            .ok_or((StatusCode::BAD_REQUEST, "missing X-Pyana-Resource header"))?;

        let engine = state.0.lock().await;
        let federation_root = engine.federation_root();
        let verified = engine
            .verify_presentation_bytes(&proof_bytes, &action, &resource)
            .map_err(|_| (StatusCode::BAD_REQUEST, "proof decode failed"))?;

        if !verified {
            return Err((
                StatusCode::FORBIDDEN,
                "presentation proof verification failed",
            ));
        }

        let verified_proof = pyana_circuit::VerifiedProof::with_federation_root(
            pyana_circuit::proof_tier::stark_tier(),
            pyana_circuit::proof_tier::STARK_BACKEND,
            federation_root,
        );

        Ok(StrictPresentation {
            action,
            resource,
            federation_root,
            verified_proof,
        })
    }
}

impl FromRequestParts<MutexEngineState> for OptionalPresentation {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &MutexEngineState,
    ) -> Result<Self, Self::Rejection> {
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

        let action = extract_str_header(&parts.headers, ACTION_HEADER);
        let resource = extract_str_header(&parts.headers, RESOURCE_HEADER);

        let (action_str, resource_str) = match (action.as_deref(), resource.as_deref()) {
            (Some(a), Some(r)) => (a, r),
            _ => {
                return Ok(OptionalPresentation {
                    verified: false,
                    action,
                    resource,
                    federation_root: None,
                    error: Some(
                        "missing X-Pyana-Action or X-Pyana-Resource header for binding check"
                            .into(),
                    ),
                });
            }
        };

        let engine = state.0.lock().await;
        let federation_root = engine.federation_root();
        let result = engine.verify_presentation_bytes(&proof_bytes, action_str, resource_str);

        match result {
            Ok(true) => Ok(OptionalPresentation {
                verified: true,
                action,
                resource,
                federation_root: Some(federation_root),
                error: None,
            }),
            Ok(false) => Ok(OptionalPresentation {
                verified: false,
                action,
                resource,
                federation_root: Some(federation_root),
                error: Some("presentation proof verification failed".into()),
            }),
            Err(e) => Ok(OptionalPresentation {
                verified: false,
                action,
                resource,
                federation_root: Some(federation_root),
                error: Some(format!("proof decode error: {e}")),
            }),
        }
    }
}

// =============================================================================
// Dev/test: any-tier verification helper
// =============================================================================

/// Verify a proof accepting any tier (dev/test only).
///
/// This function is only available when the `dev` feature is enabled.
/// It allows structural and experimental proofs to pass verification,
/// which is useful for integration testing without real cryptographic backends.
#[cfg(feature = "dev")]
pub fn verify_any_tier_presentation(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<pyana_circuit::VerifiedProof, pyana_sdk::SdkError> {
    pyana_sdk::verify_any_tier(
        proof_bytes,
        federation_root,
        expected_action,
        expected_resource,
    )
}
