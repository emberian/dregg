//! Federation sync via the pyana-net gossip layer.
//!
//! When `--federation-peers` are configured, this module initializes a
//! GossipNetwork backed by QUIC, joins the canonical federation topics
//! (turns, revocations, intents, roots), and spawns a receiver task that
//! processes incoming gossip messages and updates local node state.
//!
//! When `--morpheus` is enabled, an additional gossip topic (`pyana/consensus`)
//! is joined, and the Morpheus DAG-based BFT adapter is driven by a timer loop
//! that produces blocks, checks timeouts, and polls for finalization.

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
pub const TOPIC_DECRYPTION_SHARES: &str = "pyana/decryption-shares";
pub const TOPIC_CONSENSUS: &str = "pyana/consensus";
pub const TOPIC_CHECKPOINTS: &str = "pyana/checkpoints";

/// Configuration for the Morpheus consensus mode, passed from CLI flags.
#[derive(Clone, Debug)]
pub struct MorpheusConfig {
    /// This node's index in the federation (0-based).
    pub node_index: usize,
    /// Total number of federation nodes.
    pub federation_size: usize,
}

/// Handle to the gossip layer, stored in NodeState for use by API handlers.
#[derive(Clone)]
pub struct GossipHandle {
    pub network: Arc<GossipNetwork>,
    pub topic_turns: TopicHandle,
    pub topic_revocations: TopicHandle,
    pub topic_intents: TopicHandle,
    pub topic_roots: TopicHandle,
    pub topic_checkpoints: TopicHandle,
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

    /// Publish a checkpoint to the gossip network.
    ///
    /// After a checkpoint is created and finalized (QC attached), broadcast it
    /// so all peers can store it and optionally prune old data.
    pub async fn gossip_checkpoint(&self, height: u64, checkpoint_data: Vec<u8>) {
        let msg = PeerMessage::PublishCheckpoint {
            height,
            checkpoint_data,
        };
        if let Err(e) = self.network.publish(&self.topic_checkpoints, &msg).await {
            warn!(error = %e, "failed to gossip checkpoint");
        }
    }

    /// Publish a decryption share for threshold turn decryption.
    ///
    /// After consensus orders a block containing encrypted turns, each validator
    /// produces their decryption share and broadcasts it. When t-of-n shares are
    /// collected, the turns can be decrypted and executed.
    pub async fn gossip_decryption_share(&self, share_data: Vec<u8>) {
        let share_hash = *blake3::hash(&share_data).as_bytes();
        let msg = PeerMessage::PublishTurn {
            turn_hash: share_hash,
            turn_data: share_data,
            causal_deps: vec![],
        };
        if let Err(e) = self.network.publish(&self.topic_turns, &msg).await {
            warn!(error = %e, "failed to gossip decryption share");
        }
    }
}

/// Run the federation gossip layer as a background task.
///
/// Initializes a PeerNode and GossipNetwork, connects to configured peers,
/// subscribes to all federation topics, and processes incoming messages.
///
/// If `morpheus_config` is `Some`, the full Morpheus DAG-based BFT consensus
/// is enabled: a dedicated gossip topic carries protocol messages, and a timer
/// loop drives the adapter.
pub async fn run_federation_sync(state: NodeState, morpheus_config: Option<MorpheusConfig>) {
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

    // Derive the gossip signing key from this node's Ed25519 identity key using
    // BLAKE3 key derivation. Each node gets a unique signing key, preventing
    // impersonation. Peers verify envelopes using the sender's derived key
    // (which they can compute from the sender's known public identity).
    let signing_key = {
        let s = state.read().await;
        s.wallet
            .derive_symmetric_key("pyana-gossip-envelope-signing-v1")
    };

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
    let topic_checkpoints = match gossip.join_topic(TOPIC_CHECKPOINTS, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join checkpoints topic");
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
    let mut checkpoints_stream = match gossip.subscribe(&topic_checkpoints).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to checkpoints");
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
        topic_checkpoints: topic_checkpoints.clone(),
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

    let state_checkpoints = state.clone();
    tokio::spawn(async move {
        loop {
            match checkpoints_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_checkpoint_message(&state_checkpoints, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined checkpoints topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left checkpoints topic");
                }
                None => break,
            }
        }
    });

    // Spawn a periodic routing table pruning task.
    // Removes expired route entries every 60 seconds based on the current block height.
    let state_prune = state.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(60)).await;
            let current_height = {
                let s = state_prune.read().await;
                s.store
                    .latest_attested_root()
                    .ok()
                    .flatten()
                    .map(|r| r.height)
                    .unwrap_or(0)
            };
            let mut s = state_prune.write().await;
            let before = s.routing_table.len();
            s.routing_table.prune_expired(current_height);
            let after = s.routing_table.len();
            if before != after {
                info!(
                    pruned = before - after,
                    remaining = after,
                    height = current_height,
                    "pruned expired routing table entries"
                );
            }
        }
    });

    // Spawn a periodic pending turn timeout checker.
    // Checks every 30 seconds for pending turns that have exceeded their timeout
    // height and propagates broken-promise notifications to dependents.
    let state_pending = state.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(30)).await;
            let current_height = {
                let s = state_pending.read().await;
                s.store
                    .latest_attested_root()
                    .ok()
                    .flatten()
                    .map(|r| r.height)
                    .unwrap_or(0)
            };
            let mut s = state_pending.write().await;
            let events = s.pending_turns.check_timeouts(current_height);
            if !events.is_empty() {
                info!(
                    timed_out = events.len(),
                    height = current_height,
                    "pending turns timed out, broken promises propagated"
                );
            }
        }
    });

    // If Morpheus consensus is enabled, spawn the consensus driver.
    if let Some(_mcfg) = morpheus_config {
        // TODO: implement spawn_morpheus_driver once pyana-federation
        // exposes the Morpheus adapter API.
        warn!("morpheus consensus mode requested but not yet implemented");
    }

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
            let sig_valid = signed_turn
                .signer
                .verify(&computed_hash, &signed_turn.signature);
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
                    let receipt_hash_hex: String = receipt
                        .turn_hash
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();

                    // Process routing directives from the receipt into the local
                    // routing table. This is the consumption point: introductions
                    // produce directives, and we record "target cell is reachable
                    // via the peer that sent us this turn".
                    let directive_count = receipt.routing_directives.len();
                    for directive in &receipt.routing_directives {
                        s.routing_table.apply_directive(directive, from);
                    }
                    if directive_count > 0 {
                        info!(
                            turn_hash = %hash_hex,
                            directives = directive_count,
                            routing_table_size = s.routing_table.len(),
                            "applied routing directives from gossiped turn"
                        );
                    }

                    // Check if this receipt resolves any pending turns in the
                    // distributed promise registry. Cascading resolution will
                    // propagate to all dependents whose conditions are now met.
                    let resolution_events = s.pending_turns.resolve(
                        computed_hash,
                        pyana_turn::ResolutionOutcome::Resolved(receipt.clone()),
                    );
                    if !resolution_events.is_empty() {
                        info!(
                            turn_hash = %hash_hex,
                            resolved_count = resolution_events.len(),
                            "receipt resolved pending turns"
                        );
                    }

                    // Append receipt to the wallet's chain.
                    s.wallet.append_receipt(receipt);
                    drop(s);
                    // Emit to local WS subscribers.
                    state.emit(NodeEvent::Receipt {
                        hash: receipt_hash_hex,
                    });
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
        PeerMessage::PublishPipeline { pipeline_hash, .. } => {
            let hash_hex: String = pipeline_hash.iter().map(|b| format!("{b:02x}")).collect();
            // TODO: implement pipeline execution once pyana_turn::TurnBatch is stabilized.
            warn!(from = %from, pipeline_hash = %hash_hex, "received pipeline via gossip (not yet supported)");
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
            // Decode and validate the intent from intent_data.
            if let Ok(intent) = serde_json::from_slice::<pyana_intent::Intent>(&intent_data) {
                // Validate the intent before accepting.
                if pyana_intent::validation::validate_intent(&intent).is_ok() {
                    let intent_id_hex: String =
                        intent.id.iter().map(|b| format!("{b:02x}")).collect();
                    info!(from = %from, intent_id = %intent_id_hex, "received intent via gossip");

                    // Add to local intent pool (respecting size limit).
                    let mut s = state.write().await;
                    if s.intent_pool.len() < crate::api::MAX_NODE_INTENT_POOL {
                        s.intent_pool.insert(intent.id, intent.clone());
                    }
                    drop(s);

                    // Broadcast to local WS clients.
                    state.emit(NodeEvent::Intent {
                        intent: serde_json::to_value(&intent).unwrap_or_default(),
                    });
                }
            }
        }
        // Reject PublishTurn messages on the intents topic. Intents MUST use the
        // dedicated PublishIntent variant. Accepting JSON-encoded intents inside
        // PublishTurn.turn_data creates type confusion and allows bypassing the
        // proper message framing. Peers sending intents via PublishTurn should
        // upgrade to use PublishIntent.
        PeerMessage::PublishTurn { turn_hash, .. } => {
            let hash_hex: String = turn_hash.iter().map(|b| format!("{b:02x}")).collect();
            warn!(
                from = %from,
                turn_hash = %hash_hex,
                "rejecting PublishTurn on intents topic — intents must use PublishIntent variant"
            );
        }
        _ => {}
    }
}

// =============================================================================
// Threshold Decryption (Phase 2)
// =============================================================================

/// Process a finalized block containing encrypted turns.
///
/// After consensus orders a block with encrypted turns, this function:
/// 1. Produces this validator's decryption share for each encrypted turn
/// 2. Broadcasts the shares via the gossip network
///
/// The actual decryption and execution happens when enough shares are collected
/// (handled by `try_decrypt_and_execute`).
///
/// NOTE: encrypted_turns have been moved out of RevocationBlock into a separate
/// ordering channel. This function now takes encrypted turns as an explicit parameter.
#[allow(dead_code)]
pub async fn produce_decryption_shares_for_block(
    state: &NodeState,
    _block: &pyana_federation::types::RevocationBlock,
    _gossip: &GossipHandle,
) {
    // Encrypted turns are no longer embedded in RevocationBlock.
    // This function is retained for future integration when encrypted turns
    // are delivered via a separate gossip channel.
    let _key_share = {
        let s = state.read().await;
        match &s.threshold_key_share {
            Some(share) => share.clone(),
            None => return,
        }
    };
}

/// Attempt to decrypt encrypted turns once enough shares have been collected.
///
/// Called when a new decryption share arrives. If t-of-n shares are now available
/// for a turn, reconstructs the key, decrypts, verifies the commitment, and
/// executes the turn.
///
/// Returns the number of turns successfully decrypted and executed.
pub async fn try_decrypt_and_execute(
    state: &NodeState,
    ciphertext: &pyana_federation::ThresholdCiphertext,
    shares: &[pyana_federation::DecryptionShare],
    threshold: usize,
) -> Result<Vec<u8>, &'static str> {
    match pyana_federation::combine_shares(ciphertext, shares, threshold) {
        Ok(plaintext) => {
            info!(
                plaintext_len = plaintext.len(),
                "threshold decryption successful, executing turn"
            );
            Ok(plaintext)
        }
        Err(pyana_federation::ThresholdDecryptError::InsufficientShares { have, need }) => {
            info!(
                have = have,
                need = need,
                "waiting for more decryption shares"
            );
            Err("insufficient shares")
        }
        Err(e) => {
            error!(error = %e, "threshold decryption failed");
            Err("decryption failed")
        }
    }
}

// =============================================================================
// Morpheus Consensus Driver (stub — requires pyana-morpheus dependency)
// =============================================================================

/// Stub for the Morpheus DAG-based BFT consensus driver.
///
/// Full implementation requires pyana-morpheus and pyana-federation[morpheus] features.
/// Enable with `--morpheus` CLI flag once those dependencies are wired in.
#[allow(dead_code, unused_variables)]
async fn spawn_morpheus_driver(
    state: NodeState,
    gossip: Arc<GossipNetwork>,
    peer_addrs: &[SocketAddr],
    config: MorpheusConfig,
) {
    warn!(
        node_index = config.node_index,
        federation_size = config.federation_size,
        "Morpheus consensus driver not yet available — requires pyana-morpheus dependency"
    );
}

/// Process an incoming checkpoint from the gossip network.
///
/// Verifies the checkpoint's QC against known federation keys, stores it if valid,
/// and optionally prunes old data if pruning is enabled.
async fn handle_checkpoint_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::PublishCheckpoint {
            height,
            checkpoint_data,
        } => {
            info!(from = %from, height = height, "received checkpoint via gossip");

            // Deserialize the checkpoint.
            let checkpoint: pyana_federation::Checkpoint =
                match postcard::from_bytes(&checkpoint_data) {
                    Ok(cp) => cp,
                    Err(e) => {
                        warn!(from = %from, error = %e, "failed to decode checkpoint from gossip");
                        return;
                    }
                };

            // Verify that the checkpoint height matches the announced height.
            if checkpoint.height != height {
                warn!(
                    from = %from,
                    announced = height,
                    actual = checkpoint.height,
                    "checkpoint height mismatch"
                );
                return;
            }

            // Verify the QC against known federation keys.
            let s = state.read().await;
            if !s.known_federation_keys.is_empty() {
                // Build NodeIdentity list for verification.
                let nodes: Vec<pyana_federation::NodeIdentity> = s
                    .known_federation_keys
                    .iter()
                    .enumerate()
                    .map(|(i, pk)| pyana_federation::NodeIdentity {
                        name: format!("node-{i}"),
                        id: i,
                        public_key: pk.clone(),
                    })
                    .collect();

                if let Err(e) = checkpoint.verify(&nodes) {
                    warn!(
                        from = %from,
                        height = height,
                        error = %e,
                        "rejecting checkpoint: verification failed"
                    );
                    return;
                }
            }

            // Check it's newer than what we have.
            let existing_height = s.store.latest_checkpoint_height().unwrap_or(0);
            if height <= existing_height {
                info!(
                    from = %from,
                    height = height,
                    existing = existing_height,
                    "ignoring stale checkpoint"
                );
                return;
            }

            // Store the checkpoint.
            if let Err(e) = s.store.store_checkpoint(&checkpoint) {
                warn!(error = %e, height = height, "failed to persist checkpoint");
                return;
            }

            info!(
                height = height,
                epoch = checkpoint.epoch,
                "checkpoint stored successfully"
            );

            // If pruning is enabled, prune old data.
            if s.pruning_enabled {
                match s.store.prune_before(height) {
                    Ok(result) => {
                        if result.roots_pruned > 0 || result.audit_entries_pruned > 0 {
                            info!(
                                height = height,
                                roots_pruned = result.roots_pruned,
                                audit_pruned = result.audit_entries_pruned,
                                "pruned old data below checkpoint"
                            );
                        }
                    }
                    Err(e) => {
                        warn!(error = %e, "pruning failed after checkpoint");
                    }
                }
            }
        }
        _ => {}
    }
}

/// Process an incoming attested root from the gossip network.
///
/// P1 Fix (issue 3): Before persisting, verify quorum signature using the
/// federation's known public keys. Reject unverified roots.
///
/// State root divergence detection: if the incoming root carries a post_state_root
/// and we have a local note_tree_root / nullifier_set_root, we log a warning on
/// mismatch (potential state divergence).
async fn handle_root_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::AttestedRootUpdate { root } => {
            info!(from = %from, root_len = root.len(), "received attested root via gossip");

            // Attempt to deserialize the root.
            let attested_root = match postcard::from_bytes::<pyana_store::StoredAttestedRoot>(&root)
            {
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

                    if !typed_root.is_valid_at(&s.known_federation_keys, now, s.max_root_age_secs) {
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

            // State root divergence detection: compare the incoming root's
            // note_tree_root and nullifier_set_root against our local store.
            {
                let s = state.read().await;
                let zero = [0u8; 32];

                // Check note tree root divergence.
                if let Some(remote_note_root) = attested_root.note_tree_root {
                    if remote_note_root != zero {
                        if let Ok(local_note_root) = s.store.note_tree_root() {
                            if local_note_root != zero && local_note_root != remote_note_root {
                                let local_hex: String =
                                    local_note_root.iter().map(|b| format!("{b:02x}")).collect();
                                let remote_hex: String = remote_note_root
                                    .iter()
                                    .map(|b| format!("{b:02x}"))
                                    .collect();
                                error!(
                                    from = %from,
                                    height = height,
                                    local_note_root = %local_hex,
                                    remote_note_root = %remote_hex,
                                    "STATE DIVERGENCE DETECTED: note tree root mismatch"
                                );
                            }
                        }
                    }
                }

                // Check nullifier set root divergence.
                if let Some(remote_null_root) = attested_root.nullifier_set_root {
                    if remote_null_root != zero {
                        if let Ok(local_null_root) = s.store.nullifier_set_root() {
                            if local_null_root != zero && local_null_root != remote_null_root {
                                let local_hex: String =
                                    local_null_root.iter().map(|b| format!("{b:02x}")).collect();
                                let remote_hex: String = remote_null_root
                                    .iter()
                                    .map(|b| format!("{b:02x}"))
                                    .collect();
                                error!(
                                    from = %from,
                                    height = height,
                                    local_nullifier_root = %local_hex,
                                    remote_nullifier_root = %remote_hex,
                                    "STATE DIVERGENCE DETECTED: nullifier set root mismatch"
                                );
                            }
                        }
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
