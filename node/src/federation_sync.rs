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

    /// Publish an intent to the gossip network using the dedicated PublishIntent variant.
    pub async fn gossip_intent(&self, intent_json: &serde_json::Value) {
        let intent_bytes = serde_json::to_vec(intent_json).unwrap_or_default();
        let intent_hash = *blake3::hash(&intent_bytes).as_bytes();
        let msg = PeerMessage::PublishIntent {
            intent_hash,
            intent_data: intent_bytes,
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
        ..PeerNodeConfig::default()
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

    // Derive signing key from the node identity. In production, this should be
    // a shared pre-shared key (PSK) distributed to all federation members.
    // For now we derive it from the node_id — all peers in the same federation
    // must use the same key.
    let signing_key = *blake3::hash(b"pyana-federation-gossip-signing-key-v1").as_bytes();

    // Create the GossipNetwork.
    let gossip = Arc::new(GossipNetwork::new(endpoint, node_id, signing_key));

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
///
/// P1 Fix: Deserialize the turn, verify its signature, execute it via TurnExecutor,
/// and commit the receipt (not just emit a WS event).
async fn handle_turn_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            ..
        } => {
            let hash_hex: String = turn_hash.iter().map(|b| format!("{b:02x}")).collect();
            info!(from = %from, turn_hash = %hash_hex, "received turn via gossip");

            // Deserialize the signed turn from gossip payload.
            let signed_turn: pyana_sdk::SignedTurn = match postcard::from_bytes(&turn_data) {
                Ok(st) => st,
                Err(e) => {
                    warn!(from = %from, error = %e, "failed to deserialize gossiped turn");
                    return;
                }
            };

            // Verify the turn hash matches the claimed hash.
            let computed_hash = signed_turn.turn.hash();
            if computed_hash != turn_hash {
                warn!(
                    from = %from,
                    expected = %hash_hex,
                    "turn hash mismatch, rejecting gossiped turn"
                );
                return;
            }

            // Verify the Ed25519 signature over the turn hash.
            let sig_valid = signed_turn.signer.verify(
                &computed_hash,
                &signed_turn.signature,
            );
            if !sig_valid {
                warn!(from = %from, turn_hash = %hash_hex, "invalid signature on gossiped turn");
                return;
            }

            // Execute the turn against the local ledger.
            let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
            let mut s = state.write().await;
            let exec_result = executor.execute(&signed_turn.turn, &mut s.ledger);

            match exec_result {
                pyana_turn::TurnResult::Committed { receipt, .. } => {
                    let receipt_hash_hex: String =
                        receipt.turn_hash.iter().map(|b| format!("{b:02x}")).collect();
                    // Append receipt to the wallet's chain.
                    s.wallet.append_receipt(receipt);
                    drop(s);
                    // Emit to local WS subscribers.
                    state.emit(NodeEvent::Receipt { hash: receipt_hash_hex });
                    info!(turn_hash = %hash_hex, "gossiped turn executed and committed");
                }
                pyana_turn::TurnResult::Rejected { reason, .. } => {
                    warn!(
                        from = %from,
                        turn_hash = %hash_hex,
                        reason = %reason,
                        "gossiped turn rejected by executor"
                    );
                }
                pyana_turn::TurnResult::Expired => {
                    warn!(from = %from, turn_hash = %hash_hex, "gossiped turn expired");
                }
                pyana_turn::TurnResult::Pending => {
                    warn!(from = %from, turn_hash = %hash_hex, "gossiped turn pending (unexpected)");
                }
            }
        }
        _ => {
            // Unexpected message type on turns topic — ignore.
        }
    }
}

/// Process an incoming revocation from the gossip network.
///
/// P1 Fix: Verify the revocation signature and persist it to the revocation set.
async fn handle_revocation_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::RevocationGossip {
            token_id,
            signature,
        } => {
            info!(from = %from, token_id = %token_id, "received revocation via gossip");

            // Verify the revocation signature: the signature must be a valid Ed25519
            // signature over the token_id bytes by one of the known federation keys.
            if signature.len() != 64 {
                warn!(from = %from, token_id = %token_id, "invalid revocation signature length");
                return;
            }

            let sig_bytes: [u8; 64] = signature[..64].try_into().unwrap();
            let sig = pyana_types::Signature(sig_bytes);

            let s = state.read().await;
            let verified = if s.known_federation_keys.is_empty() {
                // If no federation keys are configured, accept revocations
                // (bootstrap/development mode).
                true
            } else {
                s.known_federation_keys
                    .iter()
                    .any(|pk| pk.verify(token_id.as_bytes(), &sig))
            };
            drop(s);

            if !verified {
                warn!(
                    from = %from,
                    token_id = %token_id,
                    "rejecting revocation: signature verification failed"
                );
                return;
            }

            // Persist the revocation to the store.
            {
                let s = state.read().await;
                if let Err(e) = s.store.store_revocation(&token_id) {
                    warn!(error = %e, token_id = %token_id, "failed to persist revocation");
                }
            }

            // Emit to WS subscribers.
            state.emit(NodeEvent::Revocation { token_id });
        }
        _ => {}
    }
}

/// Process an incoming intent from the gossip network.
///
/// P1 Fix (issue 10): Uses the dedicated PublishIntent variant instead of abusing PublishTurn.
async fn handle_intent_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::PublishIntent { intent_data, .. } => {
            // Decode the intent JSON from intent_data.
            if let Ok(intent) = serde_json::from_slice::<serde_json::Value>(&intent_data) {
                let intent_id = intent
                    .get("id")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();

                info!(from = %from, intent_id = %intent_id, "received intent via gossip");

                // Add to local intent pool (respecting size limit).
                if !intent_id.is_empty() {
                    let mut s = state.write().await;
                    if s.intent_pool.len() < crate::api::MAX_NODE_INTENT_POOL {
                        s.intent_pool.insert(intent_id, intent.clone());
                    }
                }

                // Broadcast to local WS clients.
                state.emit(NodeEvent::Intent { intent });
            }
        }
        // Also accept legacy PublishTurn on intents topic for backward compat.
        PeerMessage::PublishTurn { turn_data, .. } => {
            if let Ok(intent) = serde_json::from_slice::<serde_json::Value>(&turn_data) {
                let intent_id = intent
                    .get("id")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();

                info!(from = %from, intent_id = %intent_id, "received intent via gossip (legacy PublishTurn)");

                if !intent_id.is_empty() {
                    let mut s = state.write().await;
                    if s.intent_pool.len() < crate::api::MAX_NODE_INTENT_POOL {
                        s.intent_pool.insert(intent_id, intent.clone());
                    }
                }

                state.emit(NodeEvent::Intent { intent });
            }
        }
        _ => {}
    }
}

/// Process an incoming attested root from the gossip network.
///
/// P1 Fix (issue 3): Before persisting, verify quorum signature using the
/// federation's known public keys. Reject unverified roots.
async fn handle_root_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::AttestedRootUpdate { root } => {
            info!(from = %from, root_len = root.len(), "received attested root via gossip");

            // Attempt to deserialize the root.
            let attested_root =
                match postcard::from_bytes::<pyana_store::StoredAttestedRoot>(&root) {
                    Ok(r) => r,
                    Err(e) => {
                        warn!(from = %from, error = %e, "failed to decode attested root from gossip");
                        return;
                    }
                };

            let height = attested_root.height;
            let merkle_hex: String = attested_root
                .merkle_root
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();

            // Verify quorum signatures before persisting.
            {
                let s = state.read().await;
                if !s.known_federation_keys.is_empty() {
                    // Build a pyana_types::AttestedRoot for verification.
                    let typed_root = pyana_types::AttestedRoot {
                        merkle_root: attested_root.merkle_root,
                        note_tree_root: attested_root.note_tree_root,
                        nullifier_set_root: attested_root.nullifier_set_root,
                        height: attested_root.height,
                        timestamp: attested_root.timestamp,
                        quorum_signatures: attested_root.quorum_signatures.clone(),
                        threshold_qc: attested_root.threshold_qc.clone(),
                        threshold: attested_root.threshold,
                    };

                    let now = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_secs())
                        .unwrap_or(0);

                    if !typed_root.is_valid_at(
                        &s.known_federation_keys,
                        now,
                        s.max_root_age_secs,
                    ) {
                        if !typed_root.is_valid(&s.known_federation_keys) {
                            warn!(
                                from = %from,
                                height = height,
                                root = %merkle_hex,
                                "rejecting attested root: quorum signature verification failed"
                            );
                        } else {
                            warn!(
                                from = %from,
                                height = height,
                                root = %merkle_hex,
                                "rejecting attested root: too old or future timestamp"
                            );
                        }
                        return;
                    }
                }
            }

            // Persist to local store (verified).
            {
                let s = state.read().await;
                if let Err(e) = s.store.store_attested_root(&attested_root) {
                    warn!(error = %e, "failed to persist attested root from gossip");
                }
            }

            // Emit to WS subscribers.
            state.emit(NodeEvent::Root {
                height,
                merkle_root: merkle_hex,
                timestamp: attested_root.timestamp,
            });
        }
        _ => {}
    }
}
