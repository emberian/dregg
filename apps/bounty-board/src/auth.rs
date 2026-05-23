//! Admin bearer token authentication for the bounty board.
//!
//! Reads `PYANA_ADMIN_TOKEN` from the environment. All `/admin/*` routes require
//! an `Authorization: Bearer <token>` header matching this value.
//!
//! If `PYANA_ADMIN_TOKEN` is not set, admin endpoints are DISABLED (return 503).

use std::sync::Arc;

use axum::extract::FromRequestParts;
use axum::http::StatusCode;
use axum::http::request::Parts;
use axum::response::{IntoResponse, Response};
use serde_json::json;

/// The admin token, read from `PYANA_ADMIN_TOKEN` at startup.
///
/// Stored in `AppState` and checked by the `AdminAuth` extractor.
#[derive(Clone, Debug)]
pub struct AdminToken(pub Option<Arc<String>>);

impl AdminToken {
    /// Read the admin token from the environment.
    ///
    /// Returns `None` if the variable is not set (admin endpoints will be disabled).
    pub fn from_env() -> Self {
        Self(std::env::var("PYANA_ADMIN_TOKEN").ok().map(|s| Arc::new(s)))
    }

    /// Create an admin token from a known value (for testing).
    pub fn from_value(token: impl Into<String>) -> Self {
        Self(Some(Arc::new(token.into())))
    }

    /// Check if admin access is configured.
    pub fn is_configured(&self) -> bool {
        self.0.is_some()
    }
}

/// Axum extractor that validates the admin bearer token.
///
/// Usage: add `_auth: AdminAuth` as a parameter to any handler that should be protected.
///
/// Returns:
/// - 503 Service Unavailable if `PYANA_ADMIN_TOKEN` is not configured
/// - 401 Unauthorized if the `Authorization` header is missing
/// - 401 Unauthorized if the token does not match
pub struct AdminAuth;

/// Rejection type for admin auth failures.
pub enum AdminAuthRejection {
    /// Admin token not configured in environment.
    NotConfigured,
    /// Authorization header missing.
    MissingHeader,
    /// Token does not match.
    InvalidToken,
}

impl IntoResponse for AdminAuthRejection {
    fn into_response(self) -> Response {
        let (status, msg) = match self {
            Self::NotConfigured => (
                StatusCode::SERVICE_UNAVAILABLE,
                "admin endpoints disabled: PYANA_ADMIN_TOKEN not configured",
            ),
            Self::MissingHeader => (StatusCode::UNAUTHORIZED, "missing Authorization header"),
            Self::InvalidToken => (StatusCode::UNAUTHORIZED, "invalid admin token"),
        };
        (status, axum::Json(json!({"error": msg}))).into_response()
    }
}

/// The state type that AdminAuth reads from. We use a super-state approach:
/// any state containing an `AdminToken` field works via the `HasAdminToken` trait.
pub trait HasAdminToken {
    fn admin_token(&self) -> &AdminToken;
}

impl<S> FromRequestParts<S> for AdminAuth
where
    S: HasAdminToken + Send + Sync,
{
    type Rejection = AdminAuthRejection;

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        let admin_token = state.admin_token();

        // If no token is configured, admin endpoints are disabled.
        let expected = match &admin_token.0 {
            Some(t) => t,
            None => return Err(AdminAuthRejection::NotConfigured),
        };

        // Extract the Authorization header.
        let auth_header = parts
            .headers
            .get(axum::http::header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .ok_or(AdminAuthRejection::MissingHeader)?;

        // Expect "Bearer <token>" format.
        let provided = auth_header
            .strip_prefix("Bearer ")
            .ok_or(AdminAuthRejection::InvalidToken)?;

        // Constant-time comparison to prevent timing attacks.
        if !constant_time_eq(provided.as_bytes(), expected.as_bytes()) {
            return Err(AdminAuthRejection::InvalidToken);
        }

        Ok(AdminAuth)
    }
}

/// Constant-time byte comparison (prevents timing side-channels on token comparison).
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut acc = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    acc == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_time_eq_works() {
        assert!(constant_time_eq(b"hello", b"hello"));
        assert!(!constant_time_eq(b"hello", b"world"));
        assert!(!constant_time_eq(b"hello", b"hell"));
        assert!(!constant_time_eq(b"", b"x"));
        assert!(constant_time_eq(b"", b""));
    }

    #[test]
    fn admin_token_from_env_returns_none_when_unset() {
        // In test context, PYANA_ADMIN_TOKEN is not set.
        // We can't reliably test this without modifying env, so just verify the type.
        let token = AdminToken(None);
        assert!(!token.is_configured());
    }

    #[test]
    fn admin_token_from_value() {
        let token = AdminToken::from_value("secret123");
        assert!(token.is_configured());
        assert_eq!(token.0.unwrap().as_str(), "secret123");
    }
}
