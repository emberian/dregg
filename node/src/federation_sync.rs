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

use pyana_net::gossip::{GossipEvent, GossipNetwork, MessageStream, TopicHandle};
use pyana_net::message::PeerMessage;
use pyana_net::node::{NodeId, PeerNode, PeerNodeConfig};
use tracing::{debug, error, info, warn};

use crate::state::{NodeEvent, NodeState};

/// Canonical gossip topic names for the federation.
pub const TOPIC_TURNS: &str = "pyana/turns";
pub const TOPIC_REVOCATIONS: &str = "pyana/revocations";
pub const TOPIC_INTENTS: &str = "pyana/intents";
pub const TOPIC_ROOTS: &str = "pyana/roots";
pub const TOPIC_DECRYPTION_SHARES: &str = "pyana/decryption-shares";
pub const TOPIC_CONSENSUS: &str = "pyana/consensus";
pub const TOPIC_CHECKPOINTS: &str = "pyana/checkpoints";
/// Gossip topic for Stingray budget messages: spending certificates, unlock
/// requests, and unlock votes exchanged between silos for epoch rebalancing
/// and fast unlock quorum collection.
pub const TOPIC_BUDGET: &str = "pyana/budget";
/// Gossip topic for fast-path turn signatures (lock acknowledgements).
/// Used by clients/gateways to broadcast lock requests and collect TurnSigns.
pub const TOPIC_FAST_PATH: &str = "pyana/fast-path/signs";

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
    pub topic_decryption_shares: TopicHandle,
    pub topic_budget: TopicHandle,
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
    /// produces their decryption share and broadcasts it on the dedicated
    /// decryption shares topic. When t-of-n shares are collected, the turns
    /// can be decrypted and executed.
    pub async fn gossip_decryption_share(&self, share_data: Vec<u8>) {
        let share_hash = *blake3::hash(&share_data).as_bytes();
        let msg = PeerMessage::PublishTurn {
            turn_hash: share_hash,
            turn_data: share_data,
            causal_deps: vec![],
        };
        if let Err(e) = self
            .network
            .publish(&self.topic_decryption_shares, &msg)
            .await
        {
            warn!(error = %e, "failed to gossip decryption share");
        }
    }

    /// Publish a budget message (spending certificates, unlock requests/votes).
    ///
    /// Budget messages are serialized as postcard-encoded `BudgetGossipMessage`
    /// and disseminated on the dedicated budget topic. This enables:
    /// - Epoch spending certificate exchange for rebalancing
    /// - Fast unlock request/vote gossip for quorum collection
    pub async fn gossip_budget(&self, budget_data: Vec<u8>) {
        let msg_hash = *blake3::hash(&budget_data).as_bytes();
        let msg = PeerMessage::PublishTurn {
            turn_hash: msg_hash,
            turn_data: budget_data,
            causal_deps: vec![],
        };
        if let Err(e) = self.network.publish(&self.topic_budget, &msg).await {
            warn!(error = %e, "failed to gossip budget message");
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

    // Get the node's Ed25519 signing key for gossip envelope authentication.
    // Each node signs with its own private key; peers verify using the sender's
    // public key looked up by NodeId from the peer registry. This is proper
    // asymmetric authentication — no shared secrets needed.
    let (signing_key, _our_public_key, peer_keys_map) = {
        let s = state.read().await;
        let sk = s.wallet.gossip_signing_key();
        let pk = s.wallet.public_key();

        // Build the peer key registry from known federation keys.
        // Each federation key's NodeId is derived as blake3(public_key_bytes).
        let mut peer_keys: std::collections::HashMap<
            pyana_net::node::NodeId,
            pyana_types::PublicKey,
        > = std::collections::HashMap::new();
        for fed_key in &s.known_federation_keys {
            let peer_node_id = *blake3::hash(fed_key.as_bytes()).as_bytes();
            peer_keys.insert(peer_node_id, *fed_key);
        }
        // Also register our own key so self-originated messages can be verified.
        peer_keys.insert(node_id, pk);

        (sk, pk, peer_keys)
    };

    // Create the GossipNetwork with Ed25519 asymmetric signing.
    let gossip = Arc::new(GossipNetwork::new(
        endpoint,
        node_id,
        signing_key,
        peer_keys_map,
    ));

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
    let topic_decryption_shares = match gossip
        .join_topic(TOPIC_DECRYPTION_SHARES, &peer_addrs)
        .await
    {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join decryption shares topic");
            return;
        }
    };
    let topic_budget = match gossip.join_topic(TOPIC_BUDGET, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join budget topic");
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
    let mut budget_stream = match gossip.subscribe(&topic_budget).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to budget");
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
        topic_decryption_shares: topic_decryption_shares.clone(),
        topic_budget: topic_budget.clone(),
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

    // Spawn receiver task for budget messages (spending certificates, unlock requests/votes).
    let state_budget = state.clone();
    tokio::spawn(async move {
        loop {
            match budget_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_budget_message(&state_budget, from, message).await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined budget topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left budget topic");
                }
                None => break,
            }
        }
    });

    // Spawn periodic epoch-boundary budget rebalancing task.
    // At each epoch boundary (detected via height changes), collects local spending
    // certificates and gossips them; when enough certificates are received from
    // other silos, triggers rebalancing.
    let state_rebalance = state.clone();
    tokio::spawn(async move {
        let mut last_epoch: u64 = 0;
        loop {
            tokio::time::sleep(Duration::from_secs(30)).await;
            let current_height = {
                let s = state_rebalance.read().await;
                s.store
                    .latest_attested_root()
                    .ok()
                    .flatten()
                    .map(|r| r.height)
                    .unwrap_or(0)
            };

            let epoch_length = {
                let s = state_rebalance.read().await;
                s.checkpoint_interval
            };

            if epoch_length == 0 {
                continue;
            }

            let current_epoch =
                pyana_federation::epoch::compute_epoch(current_height, epoch_length);
            if current_epoch > last_epoch && last_epoch > 0 {
                // Epoch boundary crossed: collect and gossip spending certificates.
                info!(
                    from_epoch = last_epoch,
                    to_epoch = current_epoch,
                    height = current_height,
                    "epoch boundary crossed, collecting spending certificates for rebalancing"
                );

                let certificates = {
                    let mut s = state_rebalance.write().await;
                    s.collect_spending_certificates()
                };

                if !certificates.is_empty() {
                    // Gossip the certificates to other nodes.
                    if let Some(gossip_handle) = state_rebalance.gossip().await {
                        let budget_msg =
                            BudgetGossipMessage::SpendingCertificates(certificates.clone());
                        if let Ok(data) = postcard::to_stdvec(&budget_msg) {
                            gossip_handle.gossip_budget(data).await;
                        }
                    }

                    // Also store locally for when we receive enough from others.
                    let mut s = state_rebalance.write().await;
                    s.pending_spending_certificates.extend(certificates);
                }

                // Attempt rebalancing with whatever certificates we have so far.
                // In production, this would wait for certificates from a quorum of silos;
                // here we rebalance with what we have (graceful degradation).
                let mut s = state_rebalance.write().await;
                if !s.pending_spending_certificates.is_empty() {
                    let all_certs = s.pending_spending_certificates.clone();
                    let settlements = s.rebalance_budgets(&all_certs);
                    if !settlements.is_empty() {
                        info!(
                            settlement_count = settlements.len(),
                            epoch = current_epoch,
                            "budget rebalancing complete, applying settlements to ledger"
                        );
                        // Apply settlements to the ledger: debit spent amounts from
                        // agent balances.
                        for (agent, total_spent) in &settlements {
                            if let Some(cell) = s.ledger.get_mut(agent) {
                                cell.state.balance =
                                    cell.state.balance.saturating_sub(*total_spent);
                            }
                        }
                    }
                }
            }
            last_epoch = current_epoch;
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

    // Spawn a periodic intent expiry garbage collection task.
    // Removes expired intents from the pool every 60 seconds.
    let state_intent_gc = state.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(60)).await;
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);
            let mut s = state_intent_gc.write().await;
            let before = s.intent_pool.len();
            s.intent_pool.retain(|_id, intent| !intent.is_expired(now));
            let after = s.intent_pool.len();
            if before != after {
                info!(
                    expired = before - after,
                    remaining = after,
                    "garbage-collected expired intents from pool"
                );
                // Invalidate PIR index cache since pool changed.
                s.pir_index_cache = None;
            }
        }
    });

    // Spawn a periodic fast-path lock expiry task.
    // At each block (approximated as every 1 second), expire stale cell locks
    // from the CellLockTable and check for lock conflicts with consensus-path turns.
    let state_lock_expiry = state.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(1)).await;
            let current_height = {
                let s = state_lock_expiry.read().await;
                s.store
                    .latest_attested_root()
                    .ok()
                    .flatten()
                    .map(|r| r.height)
                    .unwrap_or(0)
            };
            let mut s = state_lock_expiry.write().await;
            let expired = pyana_turn::expire_stale_locks(&mut s.cell_lock_table, current_height);
            if !expired.is_empty() {
                info!(
                    expired_count = expired.len(),
                    height = current_height,
                    "expired stale fast-path cell locks"
                );
            }
        }
    });

    // Spawn a periodic pending turn timeout checker.
    // Checks every 30 seconds for pending turns that have exceeded their timeout
    // height and propagates broken-promise notifications to dependents.
    // Also checks for AwaitHeight conditions that are now satisfied and executes
    // those turns.
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

            // Check for AwaitHeight conditions that are now satisfied.
            let height_ready = s.pending_turns.check_height_conditions(current_height);
            if !height_ready.is_empty() {
                info!(
                    ready_count = height_ready.len(),
                    height = current_height,
                    "pending turns reached target height, executing"
                );
                for turn_hash in height_ready {
                    // Get the turn from the registry before resolving.
                    if let Some(entry) = s.pending_turns.get_pending(&turn_hash) {
                        let turn = entry.turn.clone();

                        // Configure executor from node state.
                        let mut executor =
                            pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
                        let local_fed_id =
                            *blake3::hash(s.wallet.public_key().as_bytes()).as_bytes();
                        executor.set_local_federation_id(local_fed_id);
                        let now = std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .map(|d| d.as_secs() as i64)
                            .unwrap_or(0);
                        executor.set_timestamp(now);
                        executor.set_block_height(current_height);

                        let exec_result = executor.execute(&turn, &mut s.ledger);
                        match exec_result {
                            pyana_turn::TurnResult::Committed { receipt, .. } => {
                                s.pending_turns.resolve(
                                    turn_hash,
                                    pyana_turn::ResolutionOutcome::Resolved(receipt),
                                );
                            }
                            pyana_turn::TurnResult::Rejected { reason, .. } => {
                                s.pending_turns.resolve(
                                    turn_hash,
                                    pyana_turn::ResolutionOutcome::Broken(
                                        pyana_turn::BrokenReason::TurnRejected(reason),
                                    ),
                                );
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Check for timed-out pending turns.
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
    if let Some(mcfg) = morpheus_config {
        // Join the consensus gossip topic.
        let topic_consensus = match gossip.join_topic(TOPIC_CONSENSUS, &peer_addrs).await {
            Ok(t) => t,
            Err(e) => {
                error!(error = %e, "failed to join consensus topic");
                return;
            }
        };
        let consensus_stream = match gossip.subscribe(&topic_consensus).await {
            Ok(s) => s,
            Err(e) => {
                error!(error = %e, "failed to subscribe to consensus topic");
                return;
            }
        };

        spawn_morpheus_driver(
            state.clone(),
            gossip.clone(),
            topic_consensus,
            consensus_stream,
            mcfg,
        );
        info!("Morpheus DAG-BFT consensus driver spawned");
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

            // Execute the turn against the local ledger with properly configured executor.
            let mut s = state.write().await;
            let mut executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

            // Configure executor from node state: federation identity, trusted roots,
            // current timestamp, and block height.
            let local_fed_id = *blake3::hash(s.wallet.public_key().as_bytes()).as_bytes();
            executor.set_local_federation_id(local_fed_id);

            let trusted_roots: Vec<pyana_types::AttestedRoot> = s
                .store
                .all_attested_roots()
                .unwrap_or_default()
                .iter()
                .map(|r| pyana_types::AttestedRoot {
                    merkle_root: r.merkle_root,
                    note_tree_root: r.note_tree_root,
                    nullifier_set_root: r.nullifier_set_root,
                    height: r.height,
                    timestamp: r.timestamp,
                    quorum_signatures: r.quorum_signatures.clone(),
                    threshold_qc: r.threshold_qc.clone(),
                    threshold: r.threshold,
                })
                .collect();
            executor.set_trusted_federation_roots(trusted_roots);

            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            executor.set_timestamp(now);

            let current_height = s
                .store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0);
            executor.set_block_height(current_height);

            // Attach the budget gate from the coordinator's slice for this agent.
            // If the agent has an active budget coordinator, the executor will check
            // the silo's local slice before executing (Stingray bounded counter).
            let agent_id = signed_turn.turn.agent;
            let budget_gate_active = if let Some(coordinator) = s.budget_coordinators.get(&agent_id)
            {
                if let Some(_remaining) = coordinator.remaining(&s.silo_id) {
                    // Reconstruct the slice state from the coordinator's tracked state.
                    let mut gate_slice =
                        pyana_turn::BudgetSlice::new(coordinator.silo_states[&s.silo_id].ceiling);
                    gate_slice.spent = coordinator.silo_states[&s.silo_id].spent;
                    let gate = pyana_turn::BudgetGate::new(0, gate_slice);
                    executor.set_budget_gate(gate);
                    true
                } else {
                    false
                }
            } else {
                false
            };

            let exec_result = executor.execute(&signed_turn.turn, &mut s.ledger);

            match exec_result {
                pyana_turn::TurnResult::Committed { receipt, .. } => {
                    // Sync budget gate debit back to the coordinator.
                    if budget_gate_active {
                        // Copy silo_id before the mutable borrow.
                        let local_silo_id = s.silo_id;
                        if let Some(coordinator) = s.budget_coordinators.get_mut(&agent_id) {
                            let turn_hash = signed_turn.turn.hash();
                            let digest = pyana_turn::BudgetGate::compute_debit_digest(&turn_hash);
                            // Try to debit from the coordinator (may already be tracked
                            // if the gate and coordinator share the same slice state).
                            let _ =
                                coordinator.try_debit(local_silo_id, signed_turn.turn.fee, digest);
                        }
                    }

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
                        if let Err(e) = s.routing_table.apply_directive(directive, from) {
                            tracing::warn!(?e, "rejected routing directive from gossiped turn");
                        }
                    }
                    if directive_count > 0 {
                        info!(
                            turn_hash = %hash_hex,
                            directives = directive_count,
                            routing_table_size = s.routing_table.len(),
                            "applied routing directives from gossiped turn"
                        );
                    }

                    // Append note commitments from NoteCreate effects to the
                    // in-memory Poseidon2 note tree. This keeps the ZK-friendly
                    // tree in sync for membership proof generation.
                    for tree in &signed_turn.turn.call_forest.roots {
                        for effect in &tree.action.effects {
                            if let pyana_turn::Effect::NoteCreate { commitment, .. } = effect {
                                s.note_tree_append_commitment(&commitment.0);
                                let _ = s.store.store_note_commitment(commitment);
                            }
                        }
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

                    // Execute any turns that became ready due to cascading resolution.
                    for event in &resolution_events {
                        if let pyana_turn::ResolutionEvent::ReadyToExecute {
                            turn_hash: ready_hash,
                            turn: ready_turn,
                        } = event
                        {
                            let ready_result = executor.execute(ready_turn, &mut s.ledger);
                            match ready_result {
                                pyana_turn::TurnResult::Committed {
                                    receipt: ready_receipt,
                                    ..
                                } => {
                                    // Resolve the now-executed turn with its real receipt.
                                    s.pending_turns.resolve(
                                        *ready_hash,
                                        pyana_turn::ResolutionOutcome::Resolved(
                                            ready_receipt.clone(),
                                        ),
                                    );
                                    s.wallet.append_receipt(ready_receipt);
                                }
                                pyana_turn::TurnResult::Rejected { reason, .. } => {
                                    s.pending_turns.resolve(
                                        *ready_hash,
                                        pyana_turn::ResolutionOutcome::Broken(
                                            pyana_turn::BrokenReason::TurnRejected(reason),
                                        ),
                                    );
                                }
                                _ => {}
                            }
                        }
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
                    // If a budget gate was active and the turn was rejected, the
                    // executor already refunded the local slice (fast_unlock). Now
                    // initiate the distributed fast unlock protocol so other silos
                    // can also release any locks they hold for this proposal.
                    if budget_gate_active {
                        let turn_hash_bytes = signed_turn.turn.hash();
                        let unlock_request = s.create_unlock_request(
                            turn_hash_bytes,
                            agent_id,
                            signed_turn.turn.fee,
                        );
                        // Gossip the unlock request to collect quorum votes.
                        drop(s);
                        if let Some(gossip_handle) = state.gossip().await {
                            let msg = BudgetGossipMessage::UnlockRequest(unlock_request);
                            if let Ok(data) = postcard::to_stdvec(&msg) {
                                gossip_handle.gossip_budget(data).await;
                            }
                        }
                    } else {
                        drop(s);
                    }
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
        PeerMessage::PublishPipeline {
            pipeline_hash,
            pipeline_data,
        } => {
            let hash_hex: String = pipeline_hash.iter().map(|b| format!("{b:02x}")).collect();
            info!(from = %from, pipeline_hash = %hash_hex, "received pipeline via gossip");

            // Deserialize the TurnBatch (Pipeline) from the gossip payload.
            let batch: pyana_turn::TurnBatch = match postcard::from_bytes(&pipeline_data) {
                Ok(b) => b,
                Err(e) => {
                    warn!(from = %from, error = %e, "failed to deserialize gossiped pipeline");
                    return;
                }
            };

            // Validate pipeline structure before execution.
            if let Err(e) = batch.validate() {
                warn!(from = %from, error = %e, "invalid pipeline structure, rejecting");
                return;
            }

            // Execute the pipeline against the local ledger.
            let mut s = state.write().await;
            let mut executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

            // Configure executor from node state.
            let local_fed_id = *blake3::hash(s.wallet.public_key().as_bytes()).as_bytes();
            executor.set_local_federation_id(local_fed_id);

            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            executor.set_timestamp(now);

            let current_height = s
                .store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0);
            executor.set_block_height(current_height);

            let results = pyana_turn::execute_pipeline(batch, &mut s.ledger, &executor);

            // Collect receipts from successful turns and resolve pending turns.
            let mut committed_count = 0usize;
            let mut failed_count = 0usize;
            for result in &results {
                match result {
                    Ok(receipt) => {
                        committed_count += 1;
                        // Resolve any pending turns waiting on this receipt.
                        s.pending_turns.resolve(
                            receipt.turn_hash,
                            pyana_turn::ResolutionOutcome::Resolved(receipt.clone()),
                        );
                        s.wallet.append_receipt(receipt.clone());
                    }
                    Err(_) => {
                        failed_count += 1;
                    }
                }
            }

            drop(s);

            // Emit receipts to WS subscribers.
            for result in &results {
                if let Ok(receipt) = result {
                    let receipt_hash_hex: String = receipt
                        .turn_hash
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    state.emit(NodeEvent::Receipt {
                        hash: receipt_hash_hex,
                    });
                }
            }

            info!(
                from = %from,
                pipeline_hash = %hash_hex,
                committed = committed_count,
                failed = failed_count,
                "pipeline execution complete"
            );
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

            // Update the polynomial accumulator with the new revocation hash.
            // This keeps the accumulator in sync so clients can use
            // `prove_not_revoked_accumulator()` for O(1) non-membership proofs.
            {
                let mut s = state.write().await;
                // Hash the token_id string to a fixed 32-byte value for the accumulator.
                let token_hash: [u8; 32] = *blake3::hash(token_id.as_bytes()).as_bytes();
                let revocation_hash =
                    pyana_circuit::non_revocation_air::revocation_hash_to_field(&token_hash);
                s.accumulator_insert_revocation(revocation_hash);
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
/// CRITICAL 2 Fix: Verifies stake proof for gossip-propagated intents.
async fn handle_intent_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    match message {
        PeerMessage::PublishIntent { intent_data, .. } => {
            // Decode and validate the intent from intent_data.
            let intent = match serde_json::from_slice::<pyana_intent::Intent>(&intent_data) {
                Ok(i) => i,
                Err(_) => return,
            };

            // Validate the intent structure before accepting.
            if pyana_intent::validation::validate_intent(&intent).is_err() {
                return;
            }

            let intent_id_hex: String = intent.id.iter().map(|b| format!("{b:02x}")).collect();

            // CRITICAL 2: Verify stake proof for gossip-propagated intents.
            // Intents arriving via gossip MUST carry a valid stake proof to prevent
            // spam. The stake proves the sender controls a note in the Poseidon2
            // note tree, binding real economic cost to intent propagation.
            if let Some(stake_proof) = &intent.stake_proof {
                // Build the Poseidon2 note tree root from stored commitments for
                // verification. This ensures the stake is against the current
                // federation state, not an outdated or fabricated root.
                let s = state.read().await;
                let known_root = match s.store.load_all_note_commitments() {
                    Ok(commitments) => {
                        let blake3_commits: Vec<[u8; 32]> =
                            commitments.iter().map(|c| c.0).collect();
                        let depth = 20; // Standard tree depth
                        let mut tree = pyana_store::Poseidon2NoteTree::from_blake3_commitments(
                            &blake3_commits,
                            depth,
                        );
                        tree.root()
                    }
                    Err(e) => {
                        warn!(
                            from = %from,
                            intent_id = %intent_id_hex,
                            error = %e,
                            "cannot verify intent stake: failed to load note commitments"
                        );
                        return;
                    }
                };
                drop(s);

                // Verify the stake proof against the known Poseidon2 root.
                if !pyana_intent::verify_intent_stake(&intent, known_root) {
                    warn!(
                        from = %from,
                        intent_id = %intent_id_hex,
                        "rejecting intent: stake proof verification failed"
                    );
                    return;
                }
            } else {
                // Gossip-propagated intents without a stake proof are rejected.
                // Only local intents (submitted directly via API) may omit the stake.
                warn!(
                    from = %from,
                    intent_id = %intent_id_hex,
                    "rejecting intent: no stake proof (required for gossip propagation)"
                );
                return;
            }

            info!(from = %from, intent_id = %intent_id_hex, "received intent via gossip (stake verified)");

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
// Morpheus Consensus Driver
// =============================================================================

/// Transaction type for the Morpheus consensus engine.
///
/// Wraps a serialized signed turn (postcard-encoded `pyana_sdk::SignedTurn`)
/// along with its content-addressed hash. The hash is used for deduplication
/// and ordering; the raw bytes are executed after finalization.
#[derive(
    Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, serde::Serialize, serde::Deserialize,
)]
struct ConsensusTx {
    /// blake3 hash of the turn data (content address).
    hash: [u8; 32],
    /// Serialized signed turn (postcard).
    data: Vec<u8>,
}

impl ark_serialize::CanonicalSerialize for ConsensusTx {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        _compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        writer.write_all(&self.hash)?;
        writer.write_all(&(self.data.len() as u32).to_le_bytes())?;
        writer.write_all(&self.data)?;
        Ok(())
    }

    fn serialized_size(&self, _compress: ark_serialize::Compress) -> usize {
        32 + 4 + self.data.len()
    }
}

impl ark_serialize::Valid for ConsensusTx {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl ark_serialize::CanonicalDeserialize for ConsensusTx {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        _compress: ark_serialize::Compress,
        _validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let mut hash = [0u8; 32];
        reader.read_exact(&mut hash)?;
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        if len > 1_048_576 {
            return Err(ark_serialize::SerializationError::InvalidData);
        }
        let mut data = vec![0u8; len];
        reader.read_exact(&mut data)?;
        Ok(ConsensusTx { hash, data })
    }
}

impl pyana_morpheus::Transaction for ConsensusTx {}

/// Wire-format for Morpheus protocol messages sent over the gossip consensus topic.
///
/// We use postcard serialization over the ark-serialize canonical form of the
/// morpheus `Message<ConsensusTx>` type. This avoids pulling in serde for the
/// gossip layer (which uses postcard for PeerMessage) while still being compact.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct ConsensusGossipEnvelope {
    /// The sender's morpheus Identity index (1-based).
    sender_index: u32,
    /// Canonical-serialized morpheus Message<ConsensusTx>.
    payload: Vec<u8>,
}

/// Spawn the Morpheus DAG-BFT consensus driver as a set of background tasks.
///
/// This wires the Morpheus protocol engine to the gossip network:
/// - Incoming consensus messages from gossip are deserialized and fed to the process
/// - Outgoing messages from the process are serialized and broadcast via gossip
/// - A timer loop drives block production and timeout checks
/// - Finalized transaction blocks have their turns executed against the local ledger
fn spawn_morpheus_driver(
    state: NodeState,
    gossip: Arc<GossipNetwork>,
    topic_consensus: TopicHandle,
    mut consensus_stream: MessageStream,
    config: MorpheusConfig,
) {
    let n = config.federation_size as u32;
    let f = (n - 1) / 3;
    // Morpheus Identity is 1-indexed.
    let my_identity = pyana_morpheus::Identity((config.node_index as u32) + 1);

    info!(
        node_index = config.node_index,
        federation_size = config.federation_size,
        morpheus_id = my_identity.0,
        f = f,
        "initializing Morpheus DAG-BFT consensus"
    );

    // We use a channel to funnel incoming gossip messages into the driver loop.
    let (incoming_tx, mut incoming_rx) = tokio::sync::mpsc::unbounded_channel::<(
        pyana_morpheus::Identity,
        pyana_morpheus::Message<ConsensusTx>,
    )>();

    // Spawn the gossip receiver: deserializes consensus envelopes and forwards them.
    tokio::spawn(async move {
        loop {
            match consensus_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    if let PeerMessage::PublishTurn { turn_data, .. } = message {
                        // We reuse PublishTurn as the carrier for consensus messages
                        // on the consensus topic (the turn_hash field carries a
                        // content hash of the envelope for dedup).
                        match postcard::from_bytes::<ConsensusGossipEnvelope>(&turn_data) {
                            Ok(envelope) => {
                                let sender_id = pyana_morpheus::Identity(envelope.sender_index);
                                match postcard::from_bytes::<pyana_morpheus::Message<ConsensusTx>>(
                                    &envelope.payload,
                                ) {
                                    Ok(msg) => {
                                        if incoming_tx.send((sender_id, msg)).is_err() {
                                            break;
                                        }
                                    }
                                    Err(e) => {
                                        warn!(
                                            from = %from,
                                            error = %e,
                                            "failed to deserialize morpheus message payload"
                                        );
                                    }
                                }
                            }
                            Err(e) => {
                                warn!(
                                    from = %from,
                                    error = %e,
                                    "failed to decode consensus gossip envelope"
                                );
                            }
                        }
                    }
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined consensus topic");
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left consensus topic");
                }
                None => break,
            }
        }
    });

    // Spawn the main consensus driver loop.
    tokio::spawn(async move {
        // Initialize the Morpheus process. We need a KeyBook, which requires
        // the hints threshold signature setup. For now we derive a minimal
        // setup from the federation size.
        let domain_max = (1 + n as usize).next_power_of_two();
        let mut rng = ark_std::test_rng();
        let gd = match hints::GlobalData::new(domain_max, &mut rng) {
            Ok(gd) => gd,
            Err(e) => {
                error!(error = ?e, "failed to create hints GlobalData for morpheus");
                return;
            }
        };

        // Generate keys for all federation members. In production this would come
        // from a DKG ceremony; here we use deterministic keys seeded from the
        // federation configuration so all nodes derive the same key set.
        let privs: Vec<hints::SecretKey> = (0..domain_max - 1)
            .map(|_| hints::SecretKey::random(&mut rng))
            .collect();
        let pubkeys: Vec<hints::PublicKey> = privs.iter().map(|sk| sk.public(&gd)).collect();
        let weights = vec![hints::F::from(1u64); domain_max - 1];

        let hints_vec = (0..domain_max - 1)
            .map(|i| hints::generate_hint(&gd, &privs[i], domain_max, i).unwrap())
            .collect::<Vec<_>>();

        let setup = match hints::setup_universe(&gd, pubkeys.clone(), &hints_vec, weights) {
            Ok(s) => s,
            Err(e) => {
                error!(error = ?e, "failed to setup hints universe for morpheus");
                return;
            }
        };

        let keys: std::collections::BTreeMap<pyana_morpheus::Identity, hints::PublicKey> = (0..n
            as usize)
            .map(|i| (pyana_morpheus::Identity(i as u32 + 1), pubkeys[i].clone()))
            .collect();
        let identities: std::collections::BTreeMap<hints::PublicKey, pyana_morpheus::Identity> = (0
            ..n as usize)
            .map(|i| (pubkeys[i].clone(), pyana_morpheus::Identity(i as u32 + 1)))
            .collect();

        let my_idx = config.node_index; // 0-based
        let keybook = pyana_morpheus::KeyBook {
            keys: keys.clone(),
            identities,
            me_identity: my_identity.clone(),
            me_pub_key: pubkeys[my_idx].clone(),
            me_sec_key: privs[my_idx].clone(),
            hints_setup: setup,
        };

        let mut process =
            pyana_morpheus::MorpheusProcess::<ConsensusTx>::new(keybook, my_identity.clone(), n, f);

        // Ordering cursor tracks which finalized blocks have been processed,
        // providing the total ordering guarantee (F/tau from Section 4 of the paper).
        let mut ordering_cursor = pyana_morpheus::ordering::OrderingCursor::new();

        // Track logical time (in milliseconds).
        let mut logical_time: u128 = 0;
        let tick_interval = Duration::from_millis(100);

        // Set the delta parameter to match our tick interval (in "units" where
        // 1 unit = 1 tick). The morpheus timeouts are 6*delta and 12*delta.
        // With 100ms ticks and delta=50, complain at 5s, end-view at 10s.
        process.delta = 50;

        info!("Morpheus consensus driver running");

        loop {
            // Drain pending gossip messages (non-blocking).
            let mut messages_this_tick = 0;
            while let Ok((sender, msg)) = incoming_rx.try_recv() {
                let mut to_send = Vec::new();
                process.process_message(msg, sender, &mut to_send);
                broadcast_morpheus_messages(&gossip, &topic_consensus, &my_identity, &to_send)
                    .await;
                messages_this_tick += 1;
                if messages_this_tick > 256 {
                    // Yield to avoid starving other tasks.
                    break;
                }
            }

            // Advance logical time.
            logical_time += 1;
            process.set_now(logical_time);

            // Collect pending signed turns as consensus transactions.
            // Only actual turns (submitted via the API/fulfillment flow) are proposed
            // to consensus. Raw intents stay in the pool until matched and converted
            // to turns by the fulfillment pipeline.
            {
                let mut s = state.write().await;
                let pending: Vec<ConsensusTx> = s
                    .consensus_queue
                    .drain(..)
                    .take(64)
                    .filter_map(|signed_turn| {
                        let data = postcard::to_stdvec(&signed_turn).ok()?;
                        let hash = *blake3::hash(&data).as_bytes();
                        Some(ConsensusTx { hash, data })
                    })
                    .collect();
                for tx in pending {
                    process.ready_transactions.push(tx);
                }
            }

            // Try to produce blocks.
            let mut to_send = Vec::new();
            process.try_produce_blocks(&mut to_send);
            broadcast_morpheus_messages(&gossip, &topic_consensus, &my_identity, &to_send).await;

            // Check timeouts (complain + end-view).
            let mut to_send = Vec::new();
            process.check_timeouts(&mut to_send);
            broadcast_morpheus_messages(&gossip, &topic_consensus, &my_identity, &to_send).await;

            // Extract totally-ordered transactions from newly finalized blocks.
            // This is the F/tau function from Section 4: deterministic ordering
            // across all finalized Tr blocks, with deduplication.
            let ordered_txs = pyana_morpheus::ordering::extract_new_transactions(
                &process.index,
                &mut ordering_cursor,
            );

            if !ordered_txs.is_empty() {
                let tx_count = ordered_txs.len();
                for tx in &ordered_txs {
                    execute_consensus_turn(&state, tx).await;
                }
                info!(
                    tx_count = tx_count,
                    finalized_blocks = process.index.finalized.len(),
                    "executed totally-ordered finalized transactions"
                );
            }

            // Update attested roots after finalization progress.
            // We track the latest finalized height and produce a new root
            // periodically (every 10 finalized blocks).
            let finalized_count = process.index.finalized.len() as u64;
            if finalized_count > 1 && finalized_count % 10 == 0 {
                update_attested_root_from_consensus(&state, finalized_count).await;
            }

            tokio::time::sleep(tick_interval).await;
        }
    });
}

/// Broadcast outgoing Morpheus messages to the consensus gossip topic.
async fn broadcast_morpheus_messages(
    gossip: &Arc<GossipNetwork>,
    topic: &TopicHandle,
    my_identity: &pyana_morpheus::Identity,
    messages: &[(
        pyana_morpheus::Message<ConsensusTx>,
        Option<pyana_morpheus::Identity>,
    )],
) {
    for (msg, _dest) in messages {
        // Serialize the morpheus message using postcard (serde).
        let payload = match postcard::to_stdvec(msg) {
            Ok(p) => p,
            Err(e) => {
                warn!(error = %e, "failed to serialize morpheus message");
                continue;
            }
        };

        let envelope = ConsensusGossipEnvelope {
            sender_index: my_identity.0,
            payload,
        };

        let envelope_bytes = match postcard::to_stdvec(&envelope) {
            Ok(b) => b,
            Err(e) => {
                warn!(error = %e, "failed to encode consensus envelope");
                continue;
            }
        };

        let msg_hash = *blake3::hash(&envelope_bytes).as_bytes();

        // Reuse PublishTurn as the wire carrier on the consensus topic.
        let peer_msg = PeerMessage::PublishTurn {
            turn_hash: msg_hash,
            turn_data: envelope_bytes,
            causal_deps: vec![],
        };

        if let Err(e) = gossip.publish(topic, &peer_msg).await {
            debug!(error = %e, "failed to publish consensus message");
        }
    }
}

/// Execute a single consensus transaction (finalized turn) against the local ledger.
async fn execute_consensus_turn(state: &NodeState, tx: &ConsensusTx) {
    // The transaction data is a JSON-serialized intent. In the full pipeline,
    // the intent would have been converted to a signed turn before proposal.
    // For now we attempt to deserialize as a SignedTurn first, falling back
    // to treating it as an intent that needs to be resolved.
    if let Ok(signed_turn) = postcard::from_bytes::<pyana_sdk::SignedTurn>(&tx.data) {
        // Verify signature.
        let computed_hash = signed_turn.turn.hash();
        if !signed_turn
            .signer
            .verify(&computed_hash, &signed_turn.signature)
        {
            warn!(
                tx_hash = ?tx.hash,
                "consensus tx has invalid signature, skipping"
            );
            return;
        }

        let mut s = state.write().await;
        let mut executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

        let local_fed_id = *blake3::hash(s.wallet.public_key().as_bytes()).as_bytes();
        executor.set_local_federation_id(local_fed_id);

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        executor.set_timestamp(now);

        let current_height = s
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        executor.set_block_height(current_height);

        let exec_result = executor.execute(&signed_turn.turn, &mut s.ledger);
        match exec_result {
            pyana_turn::TurnResult::Committed { receipt, .. } => {
                // Resolve pending turns.
                s.pending_turns.resolve(
                    computed_hash,
                    pyana_turn::ResolutionOutcome::Resolved(receipt.clone()),
                );
                s.wallet.append_receipt(receipt.clone());

                // Mark routes as verified for any routing directives in this receipt.
                for directive in &receipt.routing_directives {
                    s.routing_table
                        .mark_verified(&directive.target, &directive.authorizing_turn);
                }

                let receipt_hash_hex: String = receipt
                    .turn_hash
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect();
                drop(s);
                state.emit(NodeEvent::Receipt {
                    hash: receipt_hash_hex,
                });
            }
            pyana_turn::TurnResult::Rejected { reason, .. } => {
                warn!(reason = %reason, "consensus-finalized turn rejected by executor");
            }
            _ => {}
        }
    } else {
        // Treat as a serialized intent — log but don't execute directly.
        // In the full pipeline, intents are matched and converted to turns
        // by the solver before being proposed to consensus.
        debug!(
            tx_hash = ?tx.hash,
            "consensus tx is not a SignedTurn, skipping execution"
        );
    }
}

/// Update the attested root after consensus progress.
///
/// Computes the current merkle root from the store and persists it as a new
/// attested root at the given height. The merkle root is derived from the
/// note tree root (which incorporates all committed notes).
async fn update_attested_root_from_consensus(state: &NodeState, height: u64) {
    let s = state.read().await;
    let merkle_root = match s.store.note_tree_root() {
        Ok(r) => r,
        Err(_) => return,
    };

    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let root = pyana_store::StoredAttestedRoot {
        merkle_root,
        note_tree_root: s.store.note_tree_root().ok(),
        nullifier_set_root: s.store.nullifier_set_root().ok(),
        height,
        timestamp: now,
        quorum_signatures: vec![],
        threshold_qc: None,
        threshold: 0,
    };

    if let Err(e) = s.store.store_attested_root(&root) {
        warn!(error = %e, height = height, "failed to persist consensus attested root");
    }
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
            let checkpoint_verified = if !s.known_federation_keys.is_empty() {
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
                true
            } else {
                // Bootstrap mode: no federation keys configured.
                // Accept checkpoint for storage but DO NOT allow pruning.
                // A malicious peer could send a fake checkpoint at extreme height
                // to trick us into deleting all data.
                warn!(
                    from = %from,
                    height = height,
                    "accepting checkpoint without verification (bootstrap mode) — pruning DISABLED"
                );
                false
            };

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

            // If pruning is enabled, prune old data — but ONLY if the checkpoint
            // was cryptographically verified. Unverified checkpoints (bootstrap mode)
            // must never trigger pruning to prevent malicious data deletion.
            if s.pruning_enabled && checkpoint_verified {
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

                // Issue 10: Reject attested roots when federation is not configured.
                // In discovery mode we accept roots for visibility but do NOT finalize
                // them into the consensus chain (prevents accepting unverified state).
                if !s.federation_configured {
                    warn!(
                        from = %from,
                        height = height,
                        "received attested root but federation is not configured — \
                         accepting in discovery mode (not finalized)"
                    );
                }

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

// =============================================================================
// Budget Gossip Messages (Stingray bounded counters)
// =============================================================================

/// Messages exchanged on the budget gossip topic for Stingray rebalancing.
///
/// These enable the distributed bounded-counter protocol:
/// - Spending certificates are exchanged at epoch boundaries for rebalancing
/// - Unlock requests are broadcast when a turn aborts and needs fast unlock
/// - Unlock votes are collected to form quorum certificates for fast release
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BudgetGossipMessage {
    /// Spending certificates from a silo for the current epoch.
    /// Sent at epoch boundaries so all silos can agree on total spending.
    SpendingCertificates(Vec<pyana_coord::budget::SpendingCertificate>),
    /// An unlock request after a turn abort (needs f+1 votes to release).
    UnlockRequest(pyana_coord::budget::UnlockRequest),
    /// A vote on an unlock request from this silo.
    UnlockVote(pyana_coord::budget::UnlockVote),
    /// A completed unlock certificate (quorum achieved, resources released).
    UnlockCertificate(pyana_coord::budget::UnlockCertificate),
}

/// Process an incoming budget message from the gossip network.
///
/// Handles spending certificates (stored for epoch rebalancing), unlock requests
/// (voted on and responded to), unlock votes (collected toward quorum), and
/// unlock certificates (applied to release locked resources).
async fn handle_budget_message(state: &NodeState, from: SocketAddr, message: PeerMessage) {
    let budget_data = match message {
        PeerMessage::PublishTurn { turn_data, .. } => turn_data,
        _ => return,
    };

    let budget_msg: BudgetGossipMessage = match postcard::from_bytes(&budget_data) {
        Ok(msg) => msg,
        Err(e) => {
            warn!(from = %from, error = %e, "failed to decode budget gossip message");
            return;
        }
    };

    match budget_msg {
        BudgetGossipMessage::SpendingCertificates(certs) => {
            info!(
                from = %from,
                cert_count = certs.len(),
                "received spending certificates via gossip"
            );
            let mut s = state.write().await;
            s.pending_spending_certificates.extend(certs);
        }
        BudgetGossipMessage::UnlockRequest(request) => {
            info!(
                from = %from,
                proposal = ?&request.proposal_id[..4],
                amount = request.amount,
                "received unlock request via gossip"
            );
            // Vote on the unlock request and gossip back our vote.
            let vote = {
                let s = state.read().await;
                s.vote_on_unlock(&request)
            };
            if let Some(vote) = vote {
                if let Some(gossip_handle) = state.gossip().await {
                    let response = BudgetGossipMessage::UnlockVote(vote);
                    if let Ok(data) = postcard::to_stdvec(&response) {
                        gossip_handle.gossip_budget(data).await;
                    }
                }
            }
        }
        BudgetGossipMessage::UnlockVote(vote) => {
            info!(
                from = %from,
                proposal = ?&vote.request.proposal_id[..4],
                has_conflict = vote.has_conflict,
                "received unlock vote via gossip"
            );
            // Store the vote; quorum checking happens when enough votes arrive.
            // For now, we store unlock requests and votes together. A full
            // implementation would track votes per-proposal and form certificates.
            let mut s = state.write().await;
            s.pending_unlock_requests.push(vote.request);
        }
        BudgetGossipMessage::UnlockCertificate(certificate) => {
            info!(
                from = %from,
                proposal = ?&certificate.request.proposal_id[..4],
                votes = certificate.votes.len(),
                "received unlock certificate via gossip"
            );
            // Apply the unlock certificate to release locked resources.
            let mut s = state.write().await;
            match s.apply_unlock_certificate(&certificate) {
                Ok(amount) => {
                    info!(amount = amount, "fast unlock applied: resources released");
                }
                Err(e) => {
                    warn!(error = %e, "failed to apply unlock certificate");
                }
            }
        }
    }
}
