//! Federation sync via the pyana-net gossip layer.
//!
//! When `--federation-peers` are configured, this module initializes a
//! GossipNetwork backed by QUIC, joins the canonical federation topics
//! (turns, revocations, intents, roots), and spawns a receiver task that
//! processes incoming gossip messages and updates local node state.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use pyana_net::gossip::{GossipEvent, GossipNetwork, TopicHandle};
use pyana_net::message::PeerMessage;
use pyana_net::node::{NodeId, PeerNode, PeerNodeConfig};
use tracing::{error, info, warn};

use crate::state::{NodeEvent, NodeState};

/// Canonical gossip topic names for the federation.
pub const TOPIC_TURNS: &str = "pyana/turns";
pub const TOPIC_REVOCATIONS: &str = "pyana/revocations";
pub const TOPIC_INTENTS: &str = "pyana/intents";
pub const TOPIC_ROOTS: &str = "pyana/roots";

/// Handle to the gossip layer, stored in NodeState for use by API handlers.
#[derive(Clone)]
pub struct GossipHandle {
    pub network: Arc<GossipNetwork>,
    pub topic_turns: TopicHandle,
    pub topic_revocations: TopicHandle,
    pub topic_intents: TopicHandle,
    pub topic_roots: TopicHandle,
}

impl GossipHandle {
    /// Publish a turn to the gossip network.
    pub async fn gossip_turn(&self, turn_hash: [u8; 32], turn_data: Vec<u8>) {
        let msg = PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            causal_deps: vec![],
        };
        if let Err(e) = self.network.publish(&self.topic_turns, &msg).await {
            warn!(error = %e, "failed to gossip turn");
        }
    }

    /// Publish a revocation to the gossip network.
    pub async fn gossip_revocation(&self, token_id: String, signature: Vec<u8>) {
        let msg = PeerMessage::RevocationGossip {
            token_id,
            signature,
        };
        if let Err(e) = self.network.publish(&self.topic_revocations, &msg).await {
            warn!(error = %e, "failed to gossip revocation");
        }
    }

    /// Publish an intent to the gossip network.
    pub async fn gossip_intent(&self, intent_json: &serde_json::Value) {
        // Encode the intent as a turn-like message with the JSON as turn_data.
        let intent_bytes = serde_json::to_vec(intent_json).unwrap_or_default();
        let intent_hash = *blake3::hash(&intent_bytes).as_bytes();
        let msg = PeerMessage::PublishTurn {
            turn_hash: intent_hash,
            turn_data: intent_bytes,
            causal_deps: vec![],
        };
        if let Err(e) = self.network.publish(&self.topic_intents, &msg).await {
            warn!(error = %e, "failed to gossip intent");
        }
    }

    /// Publish a new attested root to the gossip network.
    pub async fn gossip_root(&self, root_data: Vec<u8>) {
        let msg = PeerMessage::AttestedRootUpdate { root: root_data };
        if let Err(e) = self.network.publish(&self.topic_roots, &msg).await {
            warn!(error = %e, "failed to gossip attested root");
        }
    }
}

/// Run the federation gossip layer as a background task.
///
/// Initializes a PeerNode and GossipNetwork, connects to configured peers,
/// subscribes to all federation topics, and processes incoming messages.
pub async fn run_federation_sync(state: NodeState) {
    let peers = {
        let s = state.read().await;
        s.peers.clone()
    };

    if peers.is_empty() {
        info!("no federation peers configured, gossip sync disabled");
        return;
    }

    info!(peer_count = peers.len(), "starting federation gossip sync");

    // Parse peer addresses.
    let peer_addrs: Vec<SocketAddr> = peers
        .iter()
        .filter_map(|p| match p.parse::<SocketAddr>() {
            Ok(addr) => Some(addr),
            Err(e) => {
                warn!(peer = %p, error = %e, "invalid peer address, skipping");
                None
            }
        })
        .collect();

    if peer_addrs.is_empty() {
        warn!("no valid peer addresses, gossip sync disabled");
        return;
    }

    // Create the PeerNode (QUIC endpoint).
    let peer_node = match PeerNode::new(PeerNodeConfig {
        bind_addr: "0.0.0.0:0".parse().unwrap(),
    })
    .await
    {
        Ok(node) => node,
        Err(e) => {
            error!(error = %e, "failed to create PeerNode for gossip");
            return;
        }
    };

    let node_id: NodeId = peer_node.node_id();
    let endpoint = peer_node.endpoint().clone();

    info!(
        node_id = %pyana_net::node::fmt_node_id(&node_id),
        local_addr = %peer_node.local_addr(),
        "gossip PeerNode ready"
    );

    // Create the GossipNetwork.
    let gossip = Arc::new(GossipNetwork::new(endpoint, node_id));

    // Join all federation topics with bootstrap peers.
    let topic_turns = match gossip.join_topic(TOPIC_TURNS, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join turns topic");
            return;
        }
    };
    let topic_revocations = match gossip.join_topic(TOPIC_REVOCATIONS, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join revocations topic");
            return;
        }
    };
    let topic_intents = match gossip.join_topic(TOPIC_INTENTS, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join intents topic");
            return;
        }
    };
    let topic_roots = match gossip.join_topic(TOPIC_ROOTS, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join roots topic");
            return;
        }
    };

    // Subscribe to each topic.
    let mut turns_stream = match gossip.subscribe(&topic_turns).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to turns");
            return;
        }
    };
    let mut revocations_stream = match gossip.subscribe(&topic_revocations).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to revocations");
            return;
        }
    };
    let mut intents_stream = match gossip.subscribe(&topic_intents).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to intents");
            return;
        }
    };
    let mut roots_stream = match gossip.subscribe(&topic_roots).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to roots");
            return;
        }
    };

    // Build the GossipHandle and store it in NodeState.
    let handle = GossipHandle {
        network: gossip.clone(),
        topic_turns: topic_turns.clone(),
        topic_revocations: topic_revocations.clone(),
        topic_intents: topic_intents.clone(),
        topic_roots: topic_roots.clone(),
    };
    state.set_gossip(handle).await;

    info!("gossip layer initialized, processing messages");

    // Spawn receiver tasks for each topic.
    let state_turns = state.clone();
    tokio::spawn(async move {
        loop {
            match turns_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_turn_message(&state_turns, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined turns topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left turns topic");
                }
                None => break,
            }
        }
    });

    let state_revocations = state.clone();
    tokio::spawn(async move {
        loop {
            match revocations_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_revocation_message(&state_revocations, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined revocations topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left revocations topic");
                }
                None => break,
            }
        }
    });

    let state_intents = state.clone();
    tokio::spawn(async move {
        loop {
            match intents_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_intent_message(&state_intents, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined intents topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left intents topic");
                }
                None => break,
            }
        }
    });

    let state_roots = state.clone();
    tokio::spawn(async move {
        loop {
            match roots_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_root_message(&state_roots, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined roots topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left roots topic");
                }
                None => break,
            }
        }
    });

    // Keep this task alive (the spawned tasks do the work).
    // We just sleep forever; if all streams close, those tasks will exit.
    loop {
        tokio::time::sleep(Duration::from_secs(3600)).await;
    }
}

/// Process an incoming turn from the gossip network.
async fn handle_turn_message(
    state: &NodeState,
    from: SocketAddr,
    message: PeerMessage,
) {
    match message {
        PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            ..
        } => {
            let hash_hex: String = turn_hash.iter().map(|b| format!("{b:02x}")).collect();
            info!(from = %from, turn_hash = %hash_hex, "received turn via gossip");

            // Emit to local WS subscribers.
            state.emit(NodeEvent::Receipt { hash: hash_hex });
        }
        _ => {
            // Unexpected message type on turns topic — ignore.
        }
    }
}

/// Process an incoming revocation from the gossip network.
async fn handle_revocation_message(
    state: &NodeState,
    from: SocketAddr,
    message: PeerMessage,
) {
    match message {
        PeerMessage::RevocationGossip {
            token_id,
            signature: _,
        } => {
            info!(from = %from, token_id = %token_id, "received revocation via gossip");

            // Emit to WS subscribers.
            state.emit(NodeEvent::Revocation { token_id });
        }
        _ => {}
    }
}

/// Process an incoming intent from the gossip network.
async fn handle_intent_message(
    state: &NodeState,
    from: SocketAddr,
    message: PeerMessage,
) {
    match message {
        PeerMessage::PublishTurn {
            turn_data,
            ..
        } => {
            // Decode the intent JSON from turn_data.
            if let Ok(intent) = serde_json::from_slice::<serde_json::Value>(&turn_data) {
                let intent_id = intent
                    .get("id")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();

                info!(from = %from, intent_id = %intent_id, "received intent via gossip");

                // Add to local intent pool.
                if !intent_id.is_empty() {
                    let mut s = state.write().await;
                    s.intent_pool.insert(intent_id, intent.clone());
                }

                // Broadcast to local WS clients.
                state.emit(NodeEvent::Intent { intent });
            }
        }
        _ => {}
    }
}

/// Process an incoming attested root from the gossip network.
async fn handle_root_message(
    state: &NodeState,
    from: SocketAddr,
    message: PeerMessage,
) {
    match message {
        PeerMessage::AttestedRootUpdate { root } => {
            info!(from = %from, root_len = root.len(), "received attested root via gossip");

            // Attempt to deserialize and store the root.
            // The root is postcard-encoded AttestedRoot from pyana-store.
            if let Ok(attested_root) =
                postcard::from_bytes::<pyana_store::AttestedRoot>(&root)
            {
                let height = attested_root.height;
                let merkle_hex: String = attested_root
                    .merkle_root
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect();

                // Persist to local store.
                {
                    let s = state.read().await;
                    if let Err(e) = s.store.put_attested_root(&attested_root) {
                        warn!(error = %e, "failed to persist attested root from gossip");
                    }
                }

                // Emit to WS subscribers.
                state.emit(NodeEvent::Root {
                    height,
                    merkle_root: merkle_hex,
                    timestamp: attested_root.timestamp,
                });
            } else {
                warn!(from = %from, "failed to decode attested root from gossip");
            }
        }
        _ => {}
    }
}
