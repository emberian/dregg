//! Discharge Gateway HTTP service.
//!
//! This crate provides an axum-based HTTP server that wraps the core
//! [`pyana_macaroon::DischargeGateway`] logic. It exposes:
//!
//! - `POST /discharge` — request a discharge macaroon
//! - `GET /conditions` — list supported condition types
//! - `GET /health` — health check with metrics

use std::collections::HashSet;
use std::sync::Arc;

use axum::{Json, Router, extract::State, http::StatusCode, routing::{get, post}};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use pyana_macaroon::{
    AlwaysAllow, AllowlistEvaluator, DischargeGateway, PaymentEvaluator, RateLimitEvaluator,
};

// =============================================================================
// Configuration
// =============================================================================

/// Top-level gateway configuration (parsed from TOML).
#[derive(Clone, Debug, Deserialize)]
pub struct GatewayConfig {
    pub gateway: GatewaySettings,
    #[serde(default)]
    pub conditions: Vec<ConditionConfig>,
}

/// Core gateway settings.
#[derive(Clone, Debug, Deserialize)]
pub struct GatewaySettings {
    /// Bind address (e.g., "0.0.0.0:8421").
    pub bind: String,
    /// Path to the 32-byte signing/shared key file (hex-encoded).
    pub signing_key_file: Option<String>,
    /// Inline hex-encoded signing key (alternative to file).
    pub signing_key_hex: Option<String>,
    /// The gateway's public location URL.
    pub location: String,
    /// Discharge TTL in seconds (default: 300).
    #[serde(default = "default_ttl")]
    pub discharge_ttl_secs: i64,
}

fn default_ttl() -> i64 {
    300
}

/// Configuration for a single condition evaluator.
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type")]
pub enum ConditionConfig {
    #[serde(rename = "always_allow")]
    AlwaysAllow,
    #[serde(rename = "rate_limit")]
    RateLimit {
        max_per_hour: u32,
    },
    #[serde(rename = "payment")]
    Payment {
        min_amount: u64,
    },
    #[serde(rename = "allowlist")]
    Allowlist {
        clients: Vec<String>,
    },
    #[serde(rename = "proof_required")]
    ProofRequired,
}

// =============================================================================
// HTTP types
// =============================================================================

/// POST /discharge request body.
#[derive(Deserialize)]
pub struct HttpDischargeRequest {
    /// Base64-encoded ticket bytes from the 3P caveat.
    pub ticket: String,
    /// Optional client identifier.
    pub client_id: Option<String>,
    /// Optional base64-encoded proof bytes.
    pub proof: Option<String>,
    /// Optional payment amount.
    pub payment: Option<u64>,
    /// Arbitrary metadata.
    #[serde(default)]
    pub metadata: std::collections::HashMap<String, String>,
}

/// POST /discharge response body.
#[derive(Serialize)]
pub struct HttpDischargeResponse {
    /// The discharge macaroon (em2_ prefixed).
    pub discharge: String,
    /// Unix timestamp when the discharge expires.
    pub expires_at: i64,
    /// Which condition was satisfied.
    pub condition_met: String,
}

/// Error response body.
#[derive(Serialize)]
pub struct HttpErrorResponse {
    pub error: String,
    pub condition: String,
}

/// GET /conditions response.
#[derive(Serialize)]
pub struct ConditionsResponse {
    pub supported: Vec<String>,
}

/// GET /health response.
#[derive(Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub issued_total: u64,
}

// =============================================================================
// Application state
// =============================================================================

/// Shared application state.
pub struct AppState {
    pub gateway: DischargeGateway,
}

pub type SharedState = Arc<RwLock<AppState>>;

// =============================================================================
// Router builder
// =============================================================================

/// Build the gateway from a config, returning the shared state and router.
pub fn build_gateway(config: &GatewayConfig) -> Result<(SharedState, Router), String> {
    let key = resolve_key(config)?;
    let mut gateway = DischargeGateway::new(key, config.gateway.location.clone());
    gateway.set_discharge_ttl(config.gateway.discharge_ttl_secs);

    // Register evaluators from config.
    for cond in &config.conditions {
        match cond {
            ConditionConfig::AlwaysAllow => {
                gateway.add_evaluator(Box::new(AlwaysAllow));
            }
            ConditionConfig::RateLimit { max_per_hour } => {
                gateway.add_evaluator(Box::new(RateLimitEvaluator::new(*max_per_hour, 3600)));
            }
            ConditionConfig::Payment { min_amount } => {
                gateway.add_evaluator(Box::new(PaymentEvaluator {
                    min_amount: *min_amount,
                }));
            }
            ConditionConfig::Allowlist { clients } => {
                let allowed: HashSet<String> = clients.iter().cloned().collect();
                gateway.add_evaluator(Box::new(AllowlistEvaluator { allowed }));
            }
            ConditionConfig::ProofRequired => {
                gateway.add_evaluator(Box::new(pyana_macaroon::ProofRequiredEvaluator));
            }
        }
    }

    let state: SharedState = Arc::new(RwLock::new(AppState { gateway }));

    let router = Router::new()
        .route("/discharge", post(post_discharge))
        .route("/conditions", get(get_conditions))
        .route("/health", get(get_health))
        .with_state(state.clone());

    Ok((state, router))
}

/// Resolve the 32-byte shared key from config.
fn resolve_key(config: &GatewayConfig) -> Result<[u8; 32], String> {
    if let Some(hex) = &config.gateway.signing_key_hex {
        hex_to_key(hex)
    } else if let Some(path) = &config.gateway.signing_key_file {
        let contents = std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read key file '{}': {}", path, e))?;
        hex_to_key(contents.trim())
    } else {
        Err("no signing key configured (set signing_key_hex or signing_key_file)".into())
    }
}

fn hex_to_key(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!(
            "signing key hex must be 64 characters, got {}",
            hex.len()
        ));
    }
    let mut key = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or_else(|| format!("invalid hex char at position {}", i * 2))?;
        let low = nibble(chunk[1]).ok_or_else(|| format!("invalid hex char at position {}", i * 2 + 1))?;
        key[i] = (high << 4) | low;
    }
    Ok(key)
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
// Handlers
// =============================================================================

async fn post_discharge(
    State(state): State<SharedState>,
    Json(req): Json<HttpDischargeRequest>,
) -> Result<Json<HttpDischargeResponse>, (StatusCode, Json<HttpErrorResponse>)> {
    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;

    // Decode the ticket from base64.
    let ticket = engine.decode(&req.ticket).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(HttpErrorResponse {
                error: format!("invalid ticket base64: {e}"),
                condition: "request_parse".to_string(),
            }),
        )
    })?;

    // Decode optional proof from base64.
    let proof = match &req.proof {
        Some(p) => Some(engine.decode(p).map_err(|e| {
            (
                StatusCode::BAD_REQUEST,
                Json(HttpErrorResponse {
                    error: format!("invalid proof base64: {e}"),
                    condition: "request_parse".to_string(),
                }),
            )
        })?),
        None => None,
    };

    let discharge_req = pyana_macaroon::DischargeRequest {
        ticket,
        client_id: req.client_id,
        proof,
        payment: req.payment,
        metadata: req.metadata,
    };

    let s = state.read().await;
    match s.gateway.process_request(&discharge_req) {
        Ok(resp) => Ok(Json(HttpDischargeResponse {
            discharge: resp.discharge,
            expires_at: resp.expires_at,
            condition_met: resp.condition_met,
        })),
        Err(e) => Err((
            StatusCode::FORBIDDEN,
            Json(HttpErrorResponse {
                error: e.reason,
                condition: e.condition,
            }),
        )),
    }
}

async fn get_conditions(
    State(_state): State<SharedState>,
) -> Json<ConditionsResponse> {
    Json(ConditionsResponse {
        supported: vec![
            "always_allow".into(),
            "time_window".into(),
            "rate_limit".into(),
            "payment".into(),
            "proof_required".into(),
            "allowlist".into(),
            "all_of".into(),
            "any_of".into(),
        ],
    })
}

async fn get_health(
    State(state): State<SharedState>,
) -> Json<HealthResponse> {
    let s = state.read().await;
    Json(HealthResponse {
        status: "ok".to_string(),
        issued_total: s.gateway.issued_count(),
    })
}
