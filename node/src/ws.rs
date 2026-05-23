//! WebSocket handler for real-time extension sync.
//!
//! Connected clients subscribe to event topics and receive push notifications
//! when node state changes (new roots, revocations, receipts). Clients can also
//! send commands (subscribe, authorize) over the WebSocket.

use std::net::SocketAddr;
use std::sync::LazyLock;
use std::time::Instant;

use axum::{
    extract::{
        ConnectInfo, State,
        ws::{Message, WebSocket, WebSocketUpgrade},
    },
    response::IntoResponse,
};
use argon2::password_hash::rand_core::OsRng;
use argon2::password_hash::SaltString;
use argon2::{Argon2, PasswordHash, PasswordHasher, PasswordVerifier};
use futures_util::{SinkExt, StreamExt};
use serde::{Deserialize, Serialize};
use tokio::sync::{Semaphore, broadcast};
use tracing::{debug, warn};

use crate::state::{NodeEvent, NodeState};

/// Maximum WebSocket message size (1 MiB). Prevents OOM from oversized frames.
const WS_MAX_MESSAGE_SIZE: usize = 1 * 1024 * 1024;
/// Maximum WebSocket frame size (256 KiB).
const WS_MAX_FRAME_SIZE: usize = 256 * 1024;

/// Concurrency limit for detached gossip tasks spawned from intent broadcasts.
static GOSSIP_SEMAPHORE: LazyLock<Semaphore> = LazyLock::new(|| Semaphore::new(16));

/// Per-connection rate limiter for WS unlock attempts.
/// Limits to 5 attempts per 60-second window per connection.
const WS_UNLOCK_MAX_ATTEMPTS: u32 = 5;
const WS_UNLOCK_WINDOW_SECS: u64 = 60;

// =============================================================================
// Client message types
// =============================================================================

/// Messages the client can send over the WebSocket.
#[derive(Deserialize, Debug)]
#[serde(tag = "type", rename_all = "snake_case")]
enum ClientMessage {
    /// Subscribe to specific event topics.
    Subscribe { topics: Vec<Topic> },
    /// Authorize a token (same semantics as POST /wallet/authorize).
    Authorize { request: AuthorizeWsRequest },
    /// Broadcast an intent to other connected clients.
    BroadcastIntent { intent: serde_json::Value },
    /// Unlock the wallet (accepts any non-empty passphrase for now).
    Unlock { passphrase: String },
}

/// Topics the client can subscribe to.
///
/// Unknown topics deserialize to `Unknown` instead of failing, making the
/// subscription mechanism forward-compatible.
#[derive(Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum Topic {
    Roots,
    Revocations,
    Receipts,
    Intents,
    /// Catch-all for unrecognized topics. Prevents deserialization failures
    /// when clients send topics this node version doesn't know about.
    #[serde(other)]
    Unknown,
}

/// Authorization request sent over WebSocket.
#[derive(Deserialize, Debug)]
struct AuthorizeWsRequest {
    token_id: String,
    service: Option<String>,
    action: Option<String>,
}

/// Messages the server sends to the client.
#[derive(Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum ServerMessage {
    /// A new attested root.
    Root {
        height: u64,
        merkle_root: String,
        timestamp: i64,
    },
    /// A token revocation.
    Revocation { token_id: String },
    /// A new receipt hash.
    Receipt { hash: String },
    /// An intent broadcast to subscribers.
    Intent { intent: serde_json::Value },
    /// Response to an authorize request.
    AuthorizeResult {
        authorized: bool,
        reason: Option<String>,
    },
    /// Response to an unlock request.
    UnlockResult {
        success: bool,
        error: Option<String>,
    },
    /// Acknowledgement of subscription.
    Subscribed { topics: Vec<String> },
    /// Error response.
    Error { message: String },
}

// =============================================================================
// Handler
// =============================================================================

/// Axum handler that upgrades an HTTP request to a WebSocket connection.
///
/// Security: During initial setup (passphrase not yet set), only loopback
/// connections are allowed to prevent remote passphrase hijacking.
pub async fn handle_ws(
    ws: WebSocketUpgrade,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    State(state): State<NodeState>,
) -> impl IntoResponse {
    // Issue 1 (CRITICAL): During initial setup, reject non-loopback connections
    // to prevent remote passphrase hijacking.
    {
        let s = state.read().await;
        if s.passphrase_hash.is_none() && !addr.ip().is_loopback() {
            drop(s);
            // Return a 403 Forbidden — cannot upgrade to WS from non-local during setup.
            return axum::http::StatusCode::FORBIDDEN.into_response();
        }
    }

    // Issue 2 (HIGH): Apply max message/frame size to prevent OOM.
    ws.max_message_size(WS_MAX_MESSAGE_SIZE)
        .max_frame_size(WS_MAX_FRAME_SIZE)
        .on_upgrade(move |socket| handle_socket(socket, state))
        .into_response()
}

/// Process a single WebSocket connection.
async fn handle_socket(socket: WebSocket, state: NodeState) {
    let (mut sender, mut receiver) = socket.split();

    // Subscribe to the broadcast channel for node events.
    let mut events_rx = state.subscribe_events();

    // Track which topics this client is subscribed to.
    // Default: subscribe to everything.
    let mut subscribed_topics: Vec<Topic> = vec![Topic::Roots, Topic::Revocations, Topic::Receipts];

    // Per-connection rate limiter for unlock attempts (brute-force protection).
    let mut unlock_attempts: u32 = 0;
    let mut unlock_window_start = Instant::now();

    debug!("WebSocket client connected");

    loop {
        tokio::select! {
            // Forward broadcast events to the client (filtered by subscription).
            event = events_rx.recv() => {
                match event {
                    Ok(node_event) => {
                        if should_forward(&node_event, &subscribed_topics) {
                            let msg = node_event_to_server_message(&node_event);
                            let json = match serde_json::to_string(&msg) {
                                Ok(j) => j,
                                Err(_) => continue,
                            };
                            if sender.send(Message::Text(json.into())).await.is_err() {
                                break; // Client disconnected.
                            }
                        }
                    }
                    Err(broadcast::error::RecvError::Lagged(n)) => {
                        warn!(missed = n, "WebSocket client lagged, some events dropped");
                    }
                    Err(broadcast::error::RecvError::Closed) => {
                        break; // Channel closed, node shutting down.
                    }
                }
            }

            // Handle messages from the client.
            msg = receiver.next() => {
                match msg {
                    Some(Ok(Message::Text(text))) => {
                        match serde_json::from_str::<ClientMessage>(&text) {
                            Ok(ClientMessage::Subscribe { topics }) => {
                                // Filter out unknown topics with a warning.
                                let mut known = Vec::new();
                                for t in &topics {
                                    if *t == Topic::Unknown {
                                        warn!("client subscribed to unknown topic, ignoring");
                                    } else {
                                        known.push(*t);
                                    }
                                }
                                subscribed_topics = known.clone();
                                let topic_names: Vec<String> = known
                                    .iter()
                                    .map(|t| format!("{t:?}").to_lowercase())
                                    .collect();
                                let resp = ServerMessage::Subscribed { topics: topic_names };
                                let json = serde_json::to_string(&resp).unwrap();
                                if sender.send(Message::Text(json.into())).await.is_err() {
                                    break;
                                }
                            }
                            Ok(ClientMessage::Authorize { request }) => {
                                let resp = handle_authorize(&state, request).await;
                                let json = serde_json::to_string(&resp).unwrap();
                                if sender.send(Message::Text(json.into())).await.is_err() {
                                    break;
                                }
                            }
                            Ok(ClientMessage::BroadcastIntent { intent }) => {
                                // Issue 8 (MEDIUM): Reject intent broadcasts when wallet is locked.
                                {
                                    let s = state.read().await;
                                    if !s.unlocked {
                                        let resp = ServerMessage::Error {
                                            message: "wallet is locked".to_string(),
                                        };
                                        let json = serde_json::to_string(&resp).unwrap();
                                        if sender.send(Message::Text(json.into())).await.is_err() {
                                            break;
                                        }
                                        continue;
                                    }
                                }

                                // Validate and store in local intent pool.
                                // Apply same checks as the HTTP path: validation,
                                // content-addressed ID verification, and pool size limit.
                                if let Ok(typed_intent) =
                                    serde_json::from_value::<pyana_intent::Intent>(intent.clone())
                                {
                                    if pyana_intent::validation::validate_intent(&typed_intent)
                                        .is_ok()
                                    {
                                        // Verify content-addressed ID (prevents ID spoofing).
                                        let recomputed = pyana_intent::Intent::new(
                                            typed_intent.kind,
                                            typed_intent.matcher.clone(),
                                            typed_intent.creator,
                                            typed_intent.expiry,
                                            typed_intent.stake_proof.clone(),
                                        );
                                        if recomputed.id != typed_intent.id {
                                            let resp = ServerMessage::Error {
                                                message: "intent ID mismatch (content-addressed)".to_string(),
                                            };
                                            let json = serde_json::to_string(&resp).unwrap();
                                            if sender.send(Message::Text(json.into())).await.is_err() {
                                                break;
                                            }
                                            continue;
                                        }

                                        let mut s = state.write().await;
                                        // Enforce pool size limit (same as HTTP path).
                                        if s.intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
                                            drop(s);
                                            let resp = ServerMessage::Error {
                                                message: "intent pool full".to_string(),
                                            };
                                            let json = serde_json::to_string(&resp).unwrap();
                                            if sender.send(Message::Text(json.into())).await.is_err() {
                                                break;
                                            }
                                            continue;
                                        }
                                        s.intent_pool
                                            .insert(typed_intent.id, typed_intent.clone());
                                        // Invalidate PIR index cache.
                                        s.pir_index_cache = None;
                                        drop(s);

                                        // Broadcast to all WS subscribers as a NodeEvent.
                                        state.emit(NodeEvent::Intent {
                                            intent: serde_json::to_value(&typed_intent)
                                                .unwrap_or_default(),
                                        });
                                        // Also gossip to federation peers.
                                        // Issue 3 (HIGH): Use semaphore to bound concurrent
                                        // gossip tasks and apply backpressure.
                                        if let Some(gossip) = state.gossip().await {
                                            let intent_clone = intent.clone();
                                            match GOSSIP_SEMAPHORE.try_acquire() {
                                                Ok(permit) => {
                                                    tokio::spawn(async move {
                                                        gossip
                                                            .gossip_intent(&intent_clone)
                                                            .await;
                                                        drop(permit);
                                                    });
                                                }
                                                Err(_) => {
                                                    // Backpressure: drop this gossip round.
                                                    debug!("gossip semaphore full, dropping gossip for intent");
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Ok(ClientMessage::Unlock { passphrase }) => {
                                // Rate limit unlock attempts per connection.
                                let now = Instant::now();
                                if now.duration_since(unlock_window_start).as_secs() >= WS_UNLOCK_WINDOW_SECS {
                                    unlock_attempts = 0;
                                    unlock_window_start = now;
                                }
                                unlock_attempts += 1;

                                let resp = if unlock_attempts > WS_UNLOCK_MAX_ATTEMPTS {
                                    ServerMessage::Error {
                                        message: "rate limited: too many unlock attempts".to_string(),
                                    }
                                } else if passphrase.is_empty() {
                                    ServerMessage::UnlockResult {
                                        success: false,
                                        error: Some("passphrase must not be empty".to_string()),
                                    }
                                } else {
                                    let mut s = state.write().await;
                                    match s.passphrase_hash.clone() {
                                        Some(stored_hash) => {
                                            // Verify against stored Argon2id hash.
                                            let valid = PasswordHash::new(&stored_hash)
                                                .ok()
                                                .map(|parsed| {
                                                    Argon2::default()
                                                        .verify_password(
                                                            passphrase.as_bytes(),
                                                            &parsed,
                                                        )
                                                        .is_ok()
                                                })
                                                .unwrap_or(false);
                                            if !valid {
                                                ServerMessage::UnlockResult {
                                                    success: false,
                                                    error: Some("invalid passphrase".to_string()),
                                                }
                                            } else {
                                                s.unlocked = true;
                                                ServerMessage::UnlockResult {
                                                    success: true,
                                                    error: None,
                                                }
                                            }
                                        }
                                        None => {
                                            // First unlock sets the passphrase with Argon2id.
                                            let salt = SaltString::generate(&mut OsRng);
                                            let argon2 = Argon2::default();
                                            let phc_string = argon2
                                                .hash_password(passphrase.as_bytes(), &salt)
                                                .expect("argon2 hash")
                                                .to_string();
                                            let bearer_seed = blake3::derive_key(
                                                "pyana-node-bearer-v1",
                                                format!("{}{}", passphrase, salt.as_str())
                                                    .as_bytes(),
                                            );
                                            s.passphrase_hash = Some(phc_string.clone());
                                            s.bearer_seed = Some(bearer_seed);
                                            let _ = s.store.set_config(
                                                "passphrase_hash",
                                                phc_string.as_bytes(),
                                            );
                                            let _ =
                                                s.store.set_config("bearer_seed", &bearer_seed);
                                            s.unlocked = true;
                                            ServerMessage::UnlockResult {
                                                success: true,
                                                error: None,
                                            }
                                        }
                                    }
                                };
                                let json = serde_json::to_string(&resp).unwrap();
                                if sender.send(Message::Text(json.into())).await.is_err() {
                                    break;
                                }
                            }
                            Err(e) => {
                                let resp = ServerMessage::Error {
                                    message: format!("invalid message: {e}"),
                                };
                                let json = serde_json::to_string(&resp).unwrap();
                                if sender.send(Message::Text(json.into())).await.is_err() {
                                    break;
                                }
                            }
                        }
                    }
                    Some(Ok(Message::Close(_))) | None => {
                        break; // Client disconnected.
                    }
                    Some(Ok(_)) => {
                        // Ignore binary/ping/pong frames.
                    }
                    Some(Err(_)) => {
                        break; // Connection error.
                    }
                }
            }
        }
    }

    debug!("WebSocket client disconnected");
}

// =============================================================================
// Helpers
// =============================================================================

/// Check if an event matches the client's subscribed topics.
fn should_forward(event: &NodeEvent, topics: &[Topic]) -> bool {
    match event {
        NodeEvent::Root { .. } => topics.contains(&Topic::Roots),
        NodeEvent::Revocation { .. } => topics.contains(&Topic::Revocations),
        NodeEvent::Receipt { .. } => topics.contains(&Topic::Receipts),
        NodeEvent::Intent { .. } => topics.contains(&Topic::Intents),
    }
}

/// Convert a NodeEvent to a ServerMessage for serialization.
fn node_event_to_server_message(event: &NodeEvent) -> ServerMessage {
    match event {
        NodeEvent::Root {
            height,
            merkle_root,
            timestamp,
        } => ServerMessage::Root {
            height: *height,
            merkle_root: merkle_root.clone(),
            timestamp: *timestamp,
        },
        NodeEvent::Revocation { token_id } => ServerMessage::Revocation {
            token_id: token_id.clone(),
        },
        NodeEvent::Receipt { hash } => ServerMessage::Receipt { hash: hash.clone() },
        NodeEvent::Intent { intent } => ServerMessage::Intent {
            intent: intent.clone(),
        },
    }
}

/// Handle an authorize request received over WebSocket.
async fn handle_authorize(state: &NodeState, request: AuthorizeWsRequest) -> ServerMessage {
    use pyana_sdk::AuthRequest;

    let s = state.read().await;
    let token = match s.wallet.find_token_by_id(&request.token_id) {
        Some(t) => t,
        None => {
            return ServerMessage::Error {
                message: "token not found".to_string(),
            };
        }
    };

    let auth_req = AuthRequest {
        service: request.service,
        action: request.action,
        ..Default::default()
    };

    let authorized = s.wallet.verify_token(token, &auth_req);

    ServerMessage::AuthorizeResult {
        authorized,
        reason: if authorized {
            None
        } else {
            Some("token does not satisfy request".to_string())
        },
    }
}
