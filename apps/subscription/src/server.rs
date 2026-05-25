//! HTTP API server for the subscription app.
//!
//! Wires together the registry, the payment executor, the creator catalog,
//! and the shared subscriber inbox. Routes:
//!
//! * `POST /subscribers/register` — publish a recv pubkey.
//! * `POST /creators/{creator_pk_hex}/tiers` — add a tier (admin).
//! * `POST /subscribers/subscribe` — subscribe to a tier (optionally with
//!   a credential envelope).
//! * `POST /subscribers/{subscriber_pk_hex}/delegate-debit` — submit an
//!   auto-debit delegation envelope.
//! * `POST /creators/{creator_pk_hex}/publish` — publish content (admin).
//! * `POST /executor/run-epoch` — execute one batch of debits.
//! * `GET  /content/{subscriber_hex}/{content_hash_hex}` — fetch a delivered
//!   ciphertext (workaround for `CapInbox::read_next` returning only metadata).
//! * `/inbox/subscribers/*` — the framework's standard inbox routes
//!   (`POST /send`, `GET /next`, `GET /status`).

use std::collections::HashMap;
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use pyana_app_framework::BatchExecutor;
use pyana_app_framework::server::api_error;
use pyana_sdk::AgentCipherclerk;
use pyana_sdk::cipherclerk::DelegatedToken;
use pyana_storage::inbox::CapInbox;
use pyana_types::PublicKey;
use serde::{Deserialize, Serialize};
use tokio::sync::{Mutex, RwLock};

use crate::creator::{Creator, Tier};
use crate::delivery::{self, DeliveryLog, new_subscriber_inbox};
use crate::payments::PaymentExecutor;
use crate::subscriber::{DebitAuthorization, SubscriberRegistry};

// ============================================================================
// AppState
// ============================================================================

#[derive(Clone)]
pub struct AppState {
    /// Subscriber registry (recv keys, subscriptions, auto-debit auths).
    pub registry: Arc<RwLock<SubscriberRegistry>>,
    /// Per-creator catalog, keyed by creator pubkey.
    pub creators: Arc<RwLock<HashMap<PublicKey, Creator>>>,
    /// Payment batch executor.
    pub executor: Arc<Mutex<PaymentExecutor>>,
    /// The payment executor's own cipherclerk — its public key is what subscribers
    /// address auto-debit envelopes to.
    pub executor_cipherclerk: Arc<Mutex<AgentCipherclerk>>,
    /// Shared inbox into which delivered content lands.
    pub inbox: Arc<Mutex<CapInbox>>,
    /// Side-log of delivered ciphertexts (see `delivery.rs` REVIEW[P1]).
    pub delivery_log: Arc<Mutex<DeliveryLog>>,
}

impl AppState {
    /// Construct fresh state with a freshly-generated executor cipherclerk.
    pub fn new() -> Self {
        Self {
            registry: Arc::new(RwLock::new(SubscriberRegistry::new())),
            creators: Arc::new(RwLock::new(HashMap::new())),
            executor: Arc::new(Mutex::new(PaymentExecutor::new())),
            executor_cipherclerk: Arc::new(Mutex::new(AgentCipherclerk::new())),
            inbox: Arc::new(Mutex::new(new_subscriber_inbox(1024))),
            delivery_log: Arc::new(Mutex::new(DeliveryLog::new())),
        }
    }

    /// Construct state from a fixed executor cipherclerk (used by tests for
    /// determinism).
    pub fn with_executor_cipherclerk(cipherclerk: AgentCipherclerk) -> Self {
        let mut s = Self::new();
        s.executor_cipherclerk = Arc::new(Mutex::new(cipherclerk));
        s
    }
}

impl Default for AppState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Request/response types
// ============================================================================

#[derive(Deserialize)]
pub struct RegisterSubscriberRequest {
    pub subscriber_pk_hex: String,
    pub recv_pubkey_hex: String,
}

#[derive(Serialize)]
pub struct RegisterSubscriberResponse {
    pub ok: bool,
}

#[derive(Deserialize)]
pub struct AddTierRequest {
    pub id: String,
    pub label: String,
    pub price_per_epoch: u64,
    pub asset_id: u64,
    /// If `Some(hex)`, the tier is credential-gated. Otherwise free.
    pub credential_issuer_hex: Option<String>,
}

#[derive(Deserialize)]
pub struct SubscribeRequest {
    pub subscriber_pk_hex: String,
    pub creator_pk_hex: String,
    pub tier_id: String,
    /// JSON-encoded `DelegatedToken` if the tier is gated.
    pub credential: Option<DelegatedToken>,
}

#[derive(Deserialize)]
pub struct DelegateDebitRequest {
    pub envelope: DelegatedToken,
}

#[derive(Serialize)]
pub struct DelegateDebitResponse {
    pub authorization: DebitAuthorization,
}

#[derive(Deserialize)]
pub struct PublishRequest {
    pub tier_id: String,
    pub body_hex: String,
    pub epoch: u64,
}

#[derive(Serialize)]
pub struct PublishResponse {
    pub content_hash_hex: String,
    pub pushed: Vec<PushedSummary>,
}

#[derive(Serialize)]
pub struct PushedSummary {
    pub subscriber_pk_hex: String,
    pub ciphertext_len: usize,
}

#[derive(Deserialize)]
pub struct RunEpochRequest {
    pub epoch: u64,
    pub max_batch_size: usize,
}

#[derive(Serialize)]
pub struct RunEpochResponse {
    pub batch_id_hex: String,
    pub turn_count: usize,
    pub applied_count: usize,
}

// ============================================================================
// Router
// ============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/subscribers/register", post(handle_register_subscriber))
        .route("/creators/{creator_pk_hex}/tiers", post(handle_add_tier))
        .route("/subscribers/subscribe", post(handle_subscribe))
        .route(
            "/subscribers/{subscriber_pk_hex}/delegate-debit",
            post(handle_delegate_debit),
        )
        .route("/creators/{creator_pk_hex}/publish", post(handle_publish))
        .route("/executor/run-epoch", post(handle_run_epoch))
        .route(
            "/content/{subscriber_pk_hex}/{content_hash_hex}",
            get(handle_fetch_content),
        )
}

// ============================================================================
// Helpers
// ============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect::<Option<Vec<u8>>>()
        .and_then(|v| v.try_into().ok())
}

fn parse_pk_hex(s: &str) -> Option<PublicKey> {
    parse_hex32(s).map(PublicKey)
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

fn hex_encode_32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// ============================================================================
// Handlers
// ============================================================================

async fn handle_register_subscriber(
    State(state): State<AppState>,
    Json(req): Json<RegisterSubscriberRequest>,
) -> Result<Json<RegisterSubscriberResponse>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)>
{
    let pk = parse_pk_hex(&req.subscriber_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid subscriber_pk_hex"))?;
    let recv = parse_hex32(&req.recv_pubkey_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid recv_pubkey_hex"))?;
    let mut reg = state.registry.write().await;
    reg.register_subscriber(pk, recv);
    Ok(Json(RegisterSubscriberResponse { ok: true }))
}

async fn handle_add_tier(
    State(state): State<AppState>,
    Path(creator_pk_hex): Path<String>,
    Json(req): Json<AddTierRequest>,
) -> Result<Json<()>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let creator_pk = parse_pk_hex(&creator_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid creator_pk_hex"))?;
    let issuer =
        match req.credential_issuer_hex.as_ref() {
            Some(s) => Some(parse_pk_hex(s).ok_or_else(|| {
                api_error(StatusCode::BAD_REQUEST, "invalid credential_issuer_hex")
            })?),
            None => None,
        };
    let tier = Tier {
        id: req.id,
        label: req.label,
        price_per_epoch: req.price_per_epoch,
        asset_id: req.asset_id,
        credential_issuer: issuer,
    };
    let mut catalog = state.creators.write().await;
    catalog
        .entry(creator_pk)
        .or_insert_with(|| Creator::new(creator_pk))
        .add_tier(tier);
    Ok(Json(()))
}

async fn handle_subscribe(
    State(state): State<AppState>,
    Json(req): Json<SubscribeRequest>,
) -> Result<Json<()>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let sub_pk = parse_pk_hex(&req.subscriber_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid subscriber_pk_hex"))?;
    let creator_pk = parse_pk_hex(&req.creator_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid creator_pk_hex"))?;

    let catalog = state.creators.read().await;
    let creator = catalog
        .get(&creator_pk)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "creator not found"))?;
    let tier = creator
        .tier(&req.tier_id)
        .cloned()
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "tier not found"))?;
    drop(catalog);

    let mut reg = state.registry.write().await;
    reg.subscribe(sub_pk, creator_pk, &tier, req.credential)
        .map_err(|e| api_error(StatusCode::UNPROCESSABLE_ENTITY, format!("{e}")))?;
    Ok(Json(()))
}

async fn handle_delegate_debit(
    State(state): State<AppState>,
    Path(subscriber_pk_hex): Path<String>,
    Json(req): Json<DelegateDebitRequest>,
) -> Result<Json<DelegateDebitResponse>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let sub_pk = parse_pk_hex(&subscriber_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid subscriber_pk_hex"))?;
    let mut reg = state.registry.write().await;
    let mut cipherclerk = state.executor_cipherclerk.lock().await;
    let auth = reg
        .receive_debit_delegation(&mut cipherclerk, sub_pk, req.envelope)
        .map_err(|e| api_error(StatusCode::UNPROCESSABLE_ENTITY, format!("{e}")))?
        .clone();
    Ok(Json(DelegateDebitResponse {
        authorization: auth,
    }))
}

async fn handle_publish(
    State(state): State<AppState>,
    Path(creator_pk_hex): Path<String>,
    Json(req): Json<PublishRequest>,
) -> Result<Json<PublishResponse>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let creator_pk = parse_pk_hex(&creator_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid creator_pk_hex"))?;
    let body = parse_hex_bytes(&req.body_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid body_hex"))?;

    let mut catalog = state.creators.write().await;
    let creator = catalog
        .get_mut(&creator_pk)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "creator not found"))?;
    let hash = creator.publish(req.tier_id.clone(), body, req.epoch);
    let item = creator
        .published
        .iter()
        .find(|i| i.content_hash == hash)
        .cloned()
        .ok_or_else(|| {
            api_error(
                StatusCode::INTERNAL_SERVER_ERROR,
                "publish list out of sync",
            )
        })?;
    // creator_snapshot for the call (don't hold catalog lock across delivery)
    let creator_snapshot = creator.clone();
    drop(catalog);

    let reg = state.registry.read().await;
    let pushed = delivery::publish_to_subscribers(
        &creator_snapshot,
        &item,
        &reg,
        &state.inbox,
        &state.delivery_log,
    )
    .await
    .map_err(|e| api_error(StatusCode::UNPROCESSABLE_ENTITY, format!("{e}")))?;

    Ok(Json(PublishResponse {
        content_hash_hex: hex_encode_32(&hash),
        pushed: pushed
            .into_iter()
            .map(|p| PushedSummary {
                subscriber_pk_hex: hex_encode_32(&p.subscriber.0),
                ciphertext_len: p.ciphertext.len(),
            })
            .collect(),
    }))
}

async fn handle_run_epoch(
    State(state): State<AppState>,
    Json(req): Json<RunEpochRequest>,
) -> Result<Json<RunEpochResponse>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let catalog = state.creators.read().await;
    let creators_vec: Vec<(PublicKey, Creator)> =
        catalog.iter().map(|(k, v)| (*k, v.clone())).collect();
    drop(catalog);
    let creators_refs: Vec<(PublicKey, &Creator)> =
        creators_vec.iter().map(|(k, v)| (*k, v)).collect();

    let reg = state.registry.read().await;
    let mut exec = state.executor.lock().await;
    exec.schedule_epoch(&reg, &creators_refs, req.epoch);
    let batch = exec.collect_batch(req.max_batch_size);

    let execution = pyana_app_framework::batch_executor::BatchExecutor::execute_batch(
        &mut *exec,
        batch.clone(),
    )
    .map_err(|e| api_error(StatusCode::INTERNAL_SERVER_ERROR, format!("{:?}", e.0)))?;

    let applied = exec.apply_batch(&reg, &batch);

    Ok(Json(RunEpochResponse {
        batch_id_hex: hex_encode_32(&execution.batch_id),
        turn_count: execution.turn_count,
        applied_count: applied.len(),
    }))
}

#[derive(Serialize)]
pub struct ContentResponse {
    pub ciphertext_hex: String,
    pub epoch: u64,
}

async fn handle_fetch_content(
    State(state): State<AppState>,
    Path((subscriber_pk_hex, content_hash_hex)): Path<(String, String)>,
) -> Result<Json<ContentResponse>, (StatusCode, Json<pyana_app_framework::ErrorResponse>)> {
    let sub_pk = parse_pk_hex(&subscriber_pk_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid subscriber_pk_hex"))?;
    let hash = parse_hex32(&content_hash_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid content_hash_hex"))?;
    let log = state.delivery_log.lock().await;
    let item = log
        .get(sub_pk, &hash)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "not delivered to this subscriber"))?;
    Ok(Json(ContentResponse {
        ciphertext_hex: item.ciphertext.iter().map(|b| format!("{b:02x}")).collect(),
        epoch: item.epoch,
    }))
}
