//! Axum HTTP API router for the pyana node.
//!
//! Serves a localhost-only API that the browser extension wallet talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use axum::{
    Json, Router,
    extract::Path as AxumPath,
    extract::State,
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};

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

#[derive(Serialize)]
pub struct IntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
}

#[derive(Serialize)]
pub struct IntentListEntry {
    pub id: String,
    pub intent: serde_json::Value,
}

// =============================================================================
// Router
// =============================================================================

/// Build the Axum router with all API routes.
pub fn router(state: NodeState) -> Router {
    Router::new()
        .route("/status", get(get_status))
        .route("/ws", get(handle_ws))
        .route("/wallet", get(get_wallet))
        .route("/wallet/unlock", post(post_wallet_unlock))
        .route("/wallet/authorize", post(post_authorize))
        .route("/wallet/mint", post(post_mint))
        .route("/wallet/attenuate", post(post_attenuate))
        .route("/wallet/tokens", get(get_tokens))
        .route("/wallet/receipts", get(get_receipts))
        .route("/intents", get(get_intents).post(post_intent))
        .route("/turn/submit", post(post_submit_turn))
        .route("/cell/{id}", get(get_cell))
        .route("/federation/roots", get(get_federation_roots))
        .with_state(state)
}

// =============================================================================
// Handlers
// =============================================================================

async fn get_status(State(state): State<NodeState>) -> Json<StatusResponse> {
    let sync = state.sync_status().await;
    Json(StatusResponse {
        healthy: true,
        peer_count: sync.peer_count,
        latest_height: sync.latest_height,
        revocation_count: sync.revocation_count,
        note_count: sync.note_count,
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
        token_id: held.id,
        service: held.service,
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
        new_token_id: attenuated.id,
        service: attenuated.service,
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

async fn post_submit_turn(
    State(state): State<NodeState>,
    Json(req): Json<SubmitTurnRequest>,
) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    let s = state.read().await;

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
    };

    // Sign the turn.
    let signed = s.wallet.sign_turn(&turn);
    let turn_hash_bytes: [u8; 32] = signed.signature.0[..32]
        .try_into()
        .unwrap_or([0u8; 32]);
    let turn_hash = hex_encode(&turn_hash_bytes);
    let turn_data = signed.signature.0.to_vec();

    // Emit receipt event to WebSocket subscribers.
    drop(s);
    state.emit(crate::state::NodeEvent::Receipt {
        hash: turn_hash.clone(),
    });

    // Gossip the turn to federation peers.
    if let Some(gossip) = state.gossip().await {
        let hash = turn_hash_bytes;
        let data = turn_data;
        tokio::spawn(async move {
            gossip.gossip_turn(hash, data).await;
        });
    }

    Ok(Json(SubmitTurnResponse {
        accepted: true,
        turn_hash: Some(turn_hash),
    }))
}

async fn get_cell(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellResponse>, StatusCode> {
    let s = state.read().await;

    // Try to find the cell in the ledger by parsing the ID.
    // For now, return a simple not-found if not present.
    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = pyana_cell::CellId(cell_id_bytes);

    let found = s.ledger.get(&cell_id).is_some();

    Ok(Json(CellResponse {
        id,
        found,
        balance: None, // Cell balance requires domain-specific lookup.
    }))
}

async fn post_wallet_unlock(
    State(state): State<NodeState>,
    Json(req): Json<UnlockRequest>,
) -> Result<Json<UnlockResponse>, StatusCode> {
    if req.passphrase.is_empty() {
        return Ok(Json(UnlockResponse {
            success: false,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    // For now, accept any non-empty passphrase (real auth comes later).
    let mut s = state.write().await;
    s.unlocked = true;

    Ok(Json(UnlockResponse {
        success: true,
        error: None,
    }))
}

async fn post_intent(
    State(state): State<NodeState>,
    Json(intent): Json<serde_json::Value>,
) -> Result<Json<IntentSubmitResponse>, StatusCode> {
    // Extract or generate an intent ID.
    let intent_id = intent
        .get("id")
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| uuid::Uuid::new_v4().to_string());

    // Store in the intent pool.
    {
        let mut s = state.write().await;
        s.intent_pool.insert(intent_id.clone(), intent.clone());
    }

    // Broadcast to WS subscribers.
    state.emit(NodeEvent::Intent {
        intent: intent.clone(),
    });

    // Gossip the intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let intent_clone = intent.clone();
        tokio::spawn(async move {
            gossip.gossip_intent(&intent_clone).await;
        });
    }

    Ok(Json(IntentSubmitResponse {
        intent_id,
        stored: true,
    }))
}

async fn get_intents(State(state): State<NodeState>) -> Json<Vec<IntentListEntry>> {
    let s = state.read().await;
    let entries: Vec<IntentListEntry> = s
        .intent_pool
        .iter()
        .map(|(id, intent)| IntentListEntry {
            id: id.clone(),
            intent: intent.clone(),
        })
        .collect();
    Json(entries)
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
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
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

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
