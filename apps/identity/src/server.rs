//! Minimal HTTP API server for the identity/credential system.

use std::collections::BTreeMap;
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::credential::Credential;
use crate::issuer::IssuerRegistry;
use crate::presentation::PresentationBuilder;
use crate::verifier::{VerificationPolicy, VerificationResult as VResult};
use crate::{AttributeValue, IssuerId};
use pyana_circuit::dsl::predicates::PredicateType;
use pyana_circuit::field::BabyBear;

// =============================================================================
// Application State
// =============================================================================

#[derive(Clone)]
pub struct AppState {
    pub issuers: Arc<RwLock<Vec<IssuerState>>>,
    pub credentials: Arc<RwLock<BTreeMap<String, Credential>>>,
}

/// Per-issuer state.
pub struct IssuerState {
    pub registry: IssuerRegistry,
    pub name: String,
}

impl AppState {
    pub fn new() -> Self {
        // Create a default issuer for testing.
        let issuer_id: IssuerId = [0x01; 32];
        let registry = IssuerRegistry::new(issuer_id);
        let issuer_state = IssuerState {
            registry,
            name: "default".to_string(),
        };
        Self {
            issuers: Arc::new(RwLock::new(vec![issuer_state])),
            credentials: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
pub struct IssueCredentialRequest {
    pub schema_name: String,
    pub holder_id: String,
    pub attributes: BTreeMap<String, serde_json::Value>,
    pub issued_at: Option<u32>,
    pub expires_at: Option<u32>,
}

#[derive(Serialize)]
pub struct CredentialResponse {
    pub id: String,
    pub schema_name: String,
    pub issuer_id: String,
    pub holder_id: String,
    pub attributes: BTreeMap<String, serde_json::Value>,
    pub issued_at: u32,
    pub expires_at: u32,
}

#[derive(Deserialize)]
pub struct CreatePresentationRequest {
    pub credential_id: String,
    pub reveal_attributes: Vec<String>,
    pub predicates: Vec<PredicateSpec>,
}

#[derive(Deserialize)]
pub struct PredicateSpec {
    pub attribute: String,
    pub predicate: String,
    pub threshold: u32,
}

#[derive(Serialize)]
pub struct PresentationResponse {
    pub revealed_attributes: BTreeMap<String, serde_json::Value>,
    pub predicate_results: Vec<PredicateResultResponse>,
    pub non_revocation_valid: bool,
}

#[derive(Serialize)]
pub struct PredicateResultResponse {
    pub attribute: String,
    pub predicate: String,
    pub threshold: u32,
    pub verified: bool,
}

#[derive(Deserialize)]
pub struct VerifyPresentationRequest {
    pub credential_id: String,
    pub require_non_revocation: bool,
    pub requirements: Vec<PredicateSpec>,
}

#[derive(Serialize)]
pub struct VerifyResponse {
    pub accepted: bool,
    pub reason: Option<String>,
}

#[derive(Serialize)]
pub struct IssuerResponse {
    pub id: String,
    pub name: String,
    pub num_issued: usize,
    pub num_revoked: usize,
}

#[derive(Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/credentials/issue", post(issue_credential))
        .route("/credentials/{id}", get(get_credential))
        .route("/presentations/create", post(create_presentation))
        .route("/presentations/verify", post(verify_presentation))
        .route("/revocations/{id}", post(revoke_credential))
        .route("/issuers", get(list_issuers))
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_id(id: &[u8; 32]) -> String {
    id.iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_hex_id(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn json_to_attribute_value(v: &serde_json::Value) -> AttributeValue {
    match v {
        serde_json::Value::Number(n) => AttributeValue::Integer(n.as_u64().unwrap_or(0) as u32),
        serde_json::Value::String(s) => AttributeValue::Text(s.clone()),
        serde_json::Value::Bool(b) => AttributeValue::Bool(*b),
        _ => AttributeValue::Text(v.to_string()),
    }
}

fn attribute_value_to_json(v: &AttributeValue) -> serde_json::Value {
    match v {
        AttributeValue::Integer(n) => serde_json::Value::Number((*n).into()),
        AttributeValue::Text(s) => serde_json::Value::String(s.clone()),
        AttributeValue::Date(d) => serde_json::Value::Number((*d).into()),
        AttributeValue::Bool(b) => serde_json::Value::Bool(*b),
        AttributeValue::Field(f) => serde_json::Value::Number((*f).into()),
    }
}

fn credential_to_response(cred: &Credential) -> CredentialResponse {
    let attrs = cred
        .attributes
        .iter()
        .map(|(k, v)| (k.clone(), attribute_value_to_json(v)))
        .collect();
    CredentialResponse {
        id: hex_id(&cred.id),
        schema_name: cred.schema_name.clone(),
        issuer_id: hex_id(&cred.issuer_id),
        holder_id: hex_id(&cred.holder_id),
        attributes: attrs,
        issued_at: cred.issued_at,
        expires_at: cred.expires_at,
    }
}

fn parse_predicate_type(s: &str) -> Option<PredicateType> {
    match s {
        "gte" | ">=" => Some(PredicateType::Gte),
        "gt" | ">" => Some(PredicateType::Gt),
        "lte" | "<=" => Some(PredicateType::Lte),
        "lt" | "<" => Some(PredicateType::Lt),
        "neq" | "!=" => Some(PredicateType::Neq),
        _ => None,
    }
}

// =============================================================================
// Handlers
// =============================================================================

async fn issue_credential(
    State(state): State<AppState>,
    Json(req): Json<IssueCredentialRequest>,
) -> Result<(StatusCode, Json<CredentialResponse>), (StatusCode, Json<ErrorResponse>)> {
    let holder_id = parse_hex_id(&req.holder_id).unwrap_or([0xAA; 32]);

    let attributes: BTreeMap<String, AttributeValue> = req
        .attributes
        .iter()
        .map(|(k, v)| (k.clone(), json_to_attribute_value(v)))
        .collect();

    let mut issuers = state.issuers.write().await;
    let issuer = issuers.first_mut().ok_or_else(|| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: "no issuer configured".to_string(),
            }),
        )
    })?;

    let credential = issuer
        .registry
        .issue(
            &req.schema_name,
            holder_id,
            attributes,
            req.issued_at.unwrap_or(0),
            req.expires_at.unwrap_or(0),
        )
        .ok_or_else(|| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: "failed to issue credential".to_string(),
                }),
            )
        })?;

    let resp = credential_to_response(&credential);
    let id_hex = hex_id(&credential.id);
    state.credentials.write().await.insert(id_hex, credential);
    Ok((StatusCode::CREATED, Json(resp)))
}

async fn get_credential(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<CredentialResponse>, (StatusCode, Json<ErrorResponse>)> {
    let creds = state.credentials.read().await;
    let credential = creds.get(&id).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "credential not found".to_string(),
            }),
        )
    })?;

    Ok(Json(credential_to_response(credential)))
}

async fn create_presentation(
    State(state): State<AppState>,
    Json(req): Json<CreatePresentationRequest>,
) -> Result<Json<PresentationResponse>, (StatusCode, Json<ErrorResponse>)> {
    let creds = state.credentials.read().await;
    let credential = creds.get(&req.credential_id).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "credential not found".to_string(),
            }),
        )
    })?;

    let mut builder = PresentationBuilder::new();
    let cred_idx = builder.add_credential(credential.clone());

    for attr in &req.reveal_attributes {
        builder.reveal_attribute(cred_idx, attr);
    }

    for pred in &req.predicates {
        let pred_type = parse_predicate_type(&pred.predicate).ok_or_else(|| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: format!("unknown predicate type: {}", pred.predicate),
                }),
            )
        })?;
        builder.add_predicate(cred_idx, &pred.attribute, pred_type, pred.threshold);
    }

    let presentation = builder.build().ok_or_else(|| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: "failed to build presentation".to_string(),
            }),
        )
    })?;

    let predicate_results = presentation
        .predicate_results
        .iter()
        .map(|r| PredicateResultResponse {
            attribute: r.attribute_name.clone(),
            predicate: format!("{:?}", r.predicate_type),
            threshold: r.threshold,
            verified: r.verified,
        })
        .collect();

    let revealed = presentation
        .revealed_attributes
        .iter()
        .map(|(k, v)| (k.clone(), attribute_value_to_json(v)))
        .collect();

    Ok(Json(PresentationResponse {
        revealed_attributes: revealed,
        predicate_results,
        non_revocation_valid: presentation.non_revocation_valid,
    }))
}

async fn verify_presentation(
    State(state): State<AppState>,
    Json(req): Json<VerifyPresentationRequest>,
) -> Result<Json<VerifyResponse>, (StatusCode, Json<ErrorResponse>)> {
    let creds = state.credentials.read().await;
    let credential = creds.get(&req.credential_id).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "credential not found".to_string(),
            }),
        )
    })?;

    // Build a presentation and verify it against a policy.
    let mut builder = PresentationBuilder::new();
    let cred_idx = builder.add_credential(credential.clone());

    for pred in &req.requirements {
        let pred_type = parse_predicate_type(&pred.predicate).ok_or_else(|| {
            (
                StatusCode::BAD_REQUEST,
                Json(ErrorResponse {
                    error: format!("unknown predicate type: {}", pred.predicate),
                }),
            )
        })?;
        builder.add_predicate(cred_idx, &pred.attribute, pred_type, pred.threshold);
    }

    let presentation = builder.build().ok_or_else(|| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: "failed to build presentation".to_string(),
            }),
        )
    })?;

    // Build verification policy.
    let mut policy = VerificationPolicy::new("api-verify", BabyBear::ZERO, BabyBear::ZERO)
        .with_non_revocation(req.require_non_revocation);

    for pred in &req.requirements {
        if let Some(pt) = parse_predicate_type(&pred.predicate) {
            policy = policy.require_predicate(&pred.attribute, pt, pred.threshold);
        }
    }

    let result = policy.verify_presentation(&presentation);
    match result {
        VResult::Accepted => Ok(Json(VerifyResponse {
            accepted: true,
            reason: None,
        })),
        VResult::Rejected { reason } => Ok(Json(VerifyResponse {
            accepted: false,
            reason: Some(reason),
        })),
    }
}

async fn revoke_credential(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<StatusCode, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex_id(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid id format".to_string(),
            }),
        )
    })?;

    let mut issuers = state.issuers.write().await;
    let issuer = issuers.first_mut().ok_or_else(|| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse {
                error: "no issuer configured".to_string(),
            }),
        )
    })?;

    let revoked = issuer.registry.revoke(&id_bytes);
    if revoked {
        Ok(StatusCode::OK)
    } else {
        Err((
            StatusCode::CONFLICT,
            Json(ErrorResponse {
                error: "credential already revoked or not found".to_string(),
            }),
        ))
    }
}

async fn list_issuers(State(state): State<AppState>) -> Json<Vec<IssuerResponse>> {
    let issuers = state.issuers.read().await;
    let results = issuers
        .iter()
        .map(|i| IssuerResponse {
            id: hex_id(&i.registry.issuer_id),
            name: i.name.clone(),
            num_issued: i.registry.num_issued(),
            num_revoked: i.registry.num_revoked(),
        })
        .collect();
    Json(results)
}
