//! WebSocket handler for real-time extension sync.
//!
//! Connected clients subscribe to event topics and receive push notifications
//! when node state changes (new roots, revocations, receipts). Clients can also
//! send commands (subscribe, authorize) over the WebSocket.

use axum::{
    extract::{
        State,
        ws::{Message, WebSocket, WebSocketUpgrade},
    },
    response::IntoResponse,
};
use futures_util::{SinkExt, StreamExt};
use serde::{Deserialize, Serialize};
use tokio::sync::broadcast;
use tracing::{debug, warn};

use crate::state::{NodeEvent, NodeState};

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
pub async fn handle_ws(ws: WebSocketUpgrade, State(state): State<NodeState>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

/// Process a single WebSocket connection.
async fn handle_socket(socket: WebSocket, state: NodeState) {
    let (mut sender, mut receiver) = socket.split();

    // Subscribe to the broadcast channel for node events.
    let mut events_rx = state.subscribe_events();

    // Track which topics this client is subscribed to.
    // Default: subscribe to everything.
    let mut subscribed_topics: Vec<Topic> = vec![Topic::Roots, Topic::Revocations, Topic::Receipts];

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
                                // Store in local intent pool.
                                let intent_id = intent
                                    .get("id")
                                    .and_then(|v| v.as_str())
                                    .unwrap_or("")
                                    .to_string();
                                if !intent_id.is_empty() {
                                    let mut s = state.write().await;
                                    s.intent_pool.insert(intent_id, intent.clone());
                                }
                                // Broadcast to all WS subscribers as a NodeEvent.
                                state.emit(NodeEvent::Intent {
                                    intent: intent.clone(),
                                });
                                // Also gossip to federation peers.
                                if let Some(gossip) = state.gossip().await {
                                    let intent_clone = intent.clone();
                                    tokio::spawn(async move {
                                        gossip.gossip_intent(&intent_clone).await;
                                    });
                                }
                            }
                            Ok(ClientMessage::Unlock { passphrase }) => {
                                let resp = if passphrase.is_empty() {
                                    ServerMessage::UnlockResult {
                                        success: false,
                                        error: Some("passphrase must not be empty".to_string()),
                                    }
                                } else {
                                    let mut s = state.write().await;
                                    s.unlocked = true;
                                    ServerMessage::UnlockResult {
                                        success: true,
                                        error: None,
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
