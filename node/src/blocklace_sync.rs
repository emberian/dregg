//! Federation sync via the blocklace (Cordial Miners) consensus layer.
//!
//! Replaces the Morpheus BFT consensus with the blocklace DAG structure from the
//! Cordial Miners paper. The blocklace provides:
//! - Quiescent operation (no messages when idle)
//! - Efficient cordial dissemination (send peers blocks you think they need)
//! - Leaderless total ordering via the tau function
//! - Equivocation detection built into the data structure
//!
//! The node participates in consensus by:
//! 1. Creating blocks when turns are submitted
//! 2. Disseminating blocks to peers via the existing QUIC gossip transport
//! 3. Processing finalized blocks in tau order via the TurnExecutor

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;

use ed25519_dalek::SigningKey;
use pyana_blocklace::dissemination::{DeltaGroup, DisseminationMessage, Disseminator, Frontier};
use pyana_blocklace::finality::{
    Block, BlockId, Blocklace, FinalityLevel, FinalityTracker, Payload,
};
use pyana_blocklace::ordering;
use pyana_blocklace::pyana_bridge::{CodManager, ExecutionTier, PyanaBlocklaceBridge};
use pyana_net::gossip::{GossipEvent, GossipNetwork, TopicHandle};
use pyana_net::message::PeerMessage;
use pyana_net::node::{NodeId, PeerNode, PeerNodeConfig};
use tokio::sync::{Mutex, RwLock};
use tracing::{debug, error, info, warn};

use crate::state::{NodeEvent, NodeState};

// ─── Constants ──────────────────────────────────────────────────────────────

/// Gossip topic for blocklace dissemination messages.
pub const TOPIC_BLOCKLACE: &str = "pyana/blocklace";

/// Default COD budget for optimistic execution (number of outstanding turns).
const DEFAULT_COD_BUDGET: usize = 8;

// ─── Gossip Message Types ───────────────────────────────────────────────────

/// Wire-format message for blocklace gossip.
///
/// These replace the Morpheus consensus messages on the gossip network.
/// The protocol is quiescent: messages are only sent when a turn is submitted
/// or a new block arrives from a peer.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BlocklaceGossipMessage {
    /// Push blocks I think you need (causally-closed delta).
    Push(DeltaGroup),
    /// Request blocks I'm missing.
    Pull(Vec<BlockId>),
    /// Response to a pull request.
    PullResponse(DeltaGroup),
    /// Lightweight frontier for efficient sync negotiation.
    Frontier(HashMap<[u8; 32], BlockId>),
}

// ─── Shared Blocklace State ─────────────────────────────────────────────────

/// Thread-safe handle to the blocklace consensus state.
///
/// Shared between the gossip receiver task and the HTTP API (for turn submission).
#[derive(Clone)]
pub struct BlocklaceHandle {
    /// The local blocklace (finality module's Blocklace with signing key).
    pub lace: Arc<RwLock<Blocklace>>,
    /// The disseminator for efficient block propagation.
    pub disseminator: Arc<Mutex<Disseminator>>,
    /// The finality tracker for monitoring block finality levels.
    pub finality_tracker: Arc<RwLock<FinalityTracker>>,
    /// The bridge for classifying turns and producing receipts.
    pub bridge: Arc<Mutex<PyanaBlocklaceBridge>>,
    /// Participants in the consensus (public keys of all federation members).
    pub participants: Arc<RwLock<Vec<[u8; 32]>>>,
    /// The gossip network for broadcasting messages.
    pub gossip: Arc<GossipNetwork>,
    /// The blocklace gossip topic handle.
    pub topic: TopicHandle,
    /// Our own public key (node identity for the blocklace).
    pub self_key: [u8; 32],
    /// Index tracking which blocks in the tau order have already been executed.
    pub executed_up_to: Arc<RwLock<usize>>,
}

impl BlocklaceHandle {
    /// Submit a turn to the blocklace.
    ///
    /// Creates a new block with the turn payload, adds it to the local blocklace,
    /// and pushes it to all known peers.
    ///
    /// Returns the block ID (used as a receipt handle) and the initial finality level.
    pub async fn submit_turn(&self, turn_data: Vec<u8>) -> (BlockId, FinalityLevel) {
        // Create the block in our local blocklace.
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(Payload::Turn(turn_data))
        };
        let block_id = block.id();

        // Determine initial finality based on participant count.
        let participants = self.participants.read().await;
        let initial_finality = if participants.len() <= 1 {
            // Solo mode: immediately ordered (we're the only participant).
            let mut tracker = self.finality_tracker.write().await;
            tracker.mark_ordered(block_id);
            FinalityLevel::Ordered
        } else {
            FinalityLevel::Local
        };

        // Disseminate to all peers.
        self.push_to_all_peers().await;

        (block_id, initial_finality)
    }

    /// Push new blocks to all known peers.
    ///
    /// Computes the delta each peer needs and sends it via the gossip topic.
    /// This is the core "cordial" behavior: send peers what they need.
    async fn push_to_all_peers(&self) {
        let participants = self.participants.read().await;
        let disseminator = self.disseminator.lock().await;

        for participant in participants.iter() {
            if participant == &self.self_key {
                continue;
            }
            let delta = disseminator.blocks_to_send(participant);
            if delta.is_empty() {
                continue;
            }

            let msg = BlocklaceGossipMessage::Push(delta.clone());
            self.broadcast_gossip_message(&msg).await;

            // Note: We don't call record_sent_to here because we broadcast to the
            // topic (all peers see it). The peer knowledge update happens when we
            // receive their ack/response.
        }
    }

    /// Broadcast a blocklace gossip message to the topic.
    async fn broadcast_gossip_message(&self, msg: &BlocklaceGossipMessage) {
        let encoded = match postcard::to_stdvec(msg) {
            Ok(bytes) => bytes,
            Err(e) => {
                warn!(error = %e, "failed to encode blocklace gossip message");
                return;
            }
        };

        let msg_hash = *blake3::hash(&encoded).as_bytes();
        let peer_msg = PeerMessage::PublishTurn {
            turn_hash: msg_hash,
            turn_data: encoded,
            causal_deps: vec![],
        };

        if let Err(e) = self.gossip.publish(&self.topic, &peer_msg).await {
            debug!(error = %e, "failed to publish blocklace message");
        }
    }

    /// Check for newly finalized blocks and return their turn payloads in order.
    ///
    /// This is the integration point with the tau ordering function.
    /// Returns turn payloads for blocks that have reached `Ordered` finality
    /// and have not been executed yet.
    pub async fn poll_finalized_turns(&self) -> Vec<(BlockId, Vec<u8>)> {
        let lace = self.lace.read().await;
        let participants = self.participants.read().await;
        let mut executed_up_to = self.executed_up_to.write().await;

        if participants.is_empty() {
            return vec![];
        }

        // Compute the total order via tau.
        let ordered = ordering::tau(&lace, &participants);

        // Skip already-executed blocks.
        let new_blocks = &ordered[*executed_up_to..];
        if new_blocks.is_empty() {
            return vec![];
        }

        let mut turns = Vec::new();
        for block_id in new_blocks {
            if let Some(block) = lace.get(block_id) {
                if let Payload::Turn(ref data) = block.payload {
                    turns.push((*block_id, data.clone()));
                }
            }
            // Mark as ordered in the finality tracker.
            let mut tracker = self.finality_tracker.write().await;
            tracker.mark_ordered(*block_id);
        }

        *executed_up_to = ordered.len();
        turns
    }
}

// ─── Main Entry Point ───────────────────────────────────────────────────────

/// Run the blocklace-based federation sync as a background task.
///
/// This is the replacement for `federation_sync::run_federation_sync` when
/// `--consensus blocklace` is specified.
///
/// Key difference from Morpheus: QUIESCENT operation. No periodic timers for
/// consensus. Activity only when a turn is submitted or blocks arrive from peers.
pub async fn run_blocklace_sync(state: NodeState, gossip_port: u16) -> Option<BlocklaceHandle> {
    let peers = {
        let s = state.read().await;
        s.peers.clone()
    };

    // Get our signing key and derive the blocklace identity.
    let (signing_key_bytes, our_public_key) = {
        let s = state.read().await;
        let sk = s.wallet.gossip_signing_key();
        let pk = s.wallet.public_key();
        (sk.to_bytes(), pk)
    };

    let signing_key = SigningKey::from_bytes(&signing_key_bytes);
    let self_key: [u8; 32] = signing_key.verifying_key().to_bytes();

    // Determine participants: in solo mode, just ourselves.
    // In full mode, all known federation keys.
    let participants: Vec<[u8; 32]> = {
        let s = state.read().await;
        if s.known_federation_keys.is_empty() {
            // Solo mode or unconfigured: just ourselves.
            vec![self_key]
        } else {
            s.known_federation_keys.iter().map(|k| k.0).collect()
        }
    };

    let quorum_threshold = if participants.len() <= 1 {
        1
    } else {
        ordering::supermajority_threshold(participants.len())
    };

    info!(
        participants = participants.len(),
        quorum_threshold = quorum_threshold,
        solo = (participants.len() <= 1),
        "initializing blocklace consensus"
    );

    // Initialize the blocklace with our signing key.
    let blocklace = Blocklace::new(signing_key.clone(), quorum_threshold);
    let finality_tracker = FinalityTracker::new(quorum_threshold);
    let bridge = PyanaBlocklaceBridge::new(DEFAULT_COD_BUDGET);

    // If no peers are configured and we're solo, set up the handle without gossip.
    if peers.is_empty() {
        info!("blocklace sync: solo mode, no peers — operating locally");

        // Create a minimal gossip setup for the handle (won't actually connect).
        // In solo mode we skip gossip entirely but still need the handle for
        // turn submission.
        let lace = Arc::new(RwLock::new(blocklace));
        let disseminator = Arc::new(Mutex::new(Disseminator::new(self_key)));
        let ft = Arc::new(RwLock::new(finality_tracker));
        let bridge_handle = Arc::new(Mutex::new(bridge));
        let participants_handle = Arc::new(RwLock::new(participants));
        let executed_up_to = Arc::new(RwLock::new(0usize));

        // We still need a gossip network for the handle struct, but in solo mode
        // we won't actually connect to anything. Create a PeerNode on the gossip port.
        let bind_addr_str = format!("0.0.0.0:{gossip_port}");
        let peer_node = match PeerNode::new(PeerNodeConfig {
            bind_addr: bind_addr_str.parse().unwrap(),
            ..PeerNodeConfig::default()
        })
        .await
        {
            Ok(node) => node,
            Err(e) => {
                error!(error = %e, "failed to create PeerNode for blocklace gossip");
                return None;
            }
        };

        let node_id: NodeId = peer_node.node_id();
        let endpoint = peer_node.endpoint().clone();

        // Build the signing key registry (just ourselves in solo mode).
        let mut peer_keys = std::collections::HashMap::new();
        peer_keys.insert(node_id, our_public_key);

        let gossip = Arc::new(GossipNetwork::new(
            endpoint,
            node_id,
            signing_key.clone(),
            peer_keys,
        ));

        // Join the blocklace topic (no peers to connect to).
        let topic = match gossip.join_topic(TOPIC_BLOCKLACE, &[]).await {
            Ok(t) => t,
            Err(e) => {
                error!(error = %e, "failed to create blocklace topic");
                return None;
            }
        };

        let handle = BlocklaceHandle {
            lace,
            disseminator,
            finality_tracker: ft,
            bridge: bridge_handle,
            participants: participants_handle,
            gossip,
            topic,
            self_key,
            executed_up_to,
        };

        // Spawn the finalized turn executor task.
        spawn_finality_executor(state.clone(), handle.clone());

        return Some(handle);
    }

    // ─── Full Mode: Connect to Peers via QUIC Gossip ────────────────────────

    info!(peer_count = peers.len(), "starting blocklace gossip sync");

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
        warn!("no valid peer addresses, blocklace sync running in solo mode");
    }

    // Create the PeerNode (QUIC endpoint).
    let bind_addr_str = format!("0.0.0.0:{gossip_port}");
    let peer_node = match PeerNode::new(PeerNodeConfig {
        bind_addr: bind_addr_str.parse().unwrap(),
        ..PeerNodeConfig::default()
    })
    .await
    {
        Ok(node) => node,
        Err(e) => {
            error!(error = %e, "failed to create PeerNode for blocklace gossip");
            return None;
        }
    };

    let node_id: NodeId = peer_node.node_id();
    let endpoint = peer_node.endpoint().clone();

    info!(
        node_id = %pyana_net::node::fmt_node_id(&node_id),
        local_addr = %peer_node.local_addr(),
        "blocklace PeerNode ready"
    );

    // Build the signing key registry from known federation keys.
    let peer_keys_map = {
        let s = state.read().await;
        let mut peer_keys: std::collections::HashMap<NodeId, pyana_types::PublicKey> =
            std::collections::HashMap::new();
        for fed_key in &s.known_federation_keys {
            let peer_node_id = *blake3::hash(fed_key.as_bytes()).as_bytes();
            peer_keys.insert(peer_node_id, *fed_key);
        }
        peer_keys.insert(node_id, our_public_key);
        peer_keys
    };

    // Create the GossipNetwork.
    let gossip = Arc::new(GossipNetwork::new(
        endpoint,
        node_id,
        signing_key.clone(),
        peer_keys_map,
    ));

    // Join the blocklace gossip topic.
    let topic = match gossip.join_topic(TOPIC_BLOCKLACE, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join blocklace topic");
            return None;
        }
    };

    // Subscribe to the topic.
    let mut blocklace_stream = match gossip.subscribe(&topic).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to blocklace topic");
            return None;
        }
    };

    // Initialize the disseminator with our blocklace.
    let disseminator = Disseminator::new(self_key);

    // Build the shared handle.
    let lace = Arc::new(RwLock::new(blocklace));
    let disseminator_handle = Arc::new(Mutex::new(disseminator));
    let ft = Arc::new(RwLock::new(finality_tracker));
    let bridge_handle = Arc::new(Mutex::new(bridge));
    let participants_handle = Arc::new(RwLock::new(participants));
    let executed_up_to = Arc::new(RwLock::new(0usize));

    let handle = BlocklaceHandle {
        lace: lace.clone(),
        disseminator: disseminator_handle.clone(),
        finality_tracker: ft.clone(),
        bridge: bridge_handle.clone(),
        participants: participants_handle.clone(),
        gossip: gossip.clone(),
        topic: topic.clone(),
        self_key,
        executed_up_to: executed_up_to.clone(),
    };

    // Also join the existing gossip topics so the node still participates in
    // turn/revocation/intent gossip (the blocklace handles ordering, but the
    // existing topics handle data propagation for non-consensus messages).
    // We re-use the existing federation_sync GossipHandle for those.
    {
        let topic_turns = gossip
            .join_topic(crate::federation_sync::TOPIC_TURNS, &peer_addrs)
            .await;
        let topic_revocations = gossip
            .join_topic(crate::federation_sync::TOPIC_REVOCATIONS, &peer_addrs)
            .await;
        let topic_intents = gossip
            .join_topic(crate::federation_sync::TOPIC_INTENTS, &peer_addrs)
            .await;
        let topic_roots = gossip
            .join_topic(crate::federation_sync::TOPIC_ROOTS, &peer_addrs)
            .await;
        let topic_checkpoints = gossip
            .join_topic(crate::federation_sync::TOPIC_CHECKPOINTS, &peer_addrs)
            .await;
        let topic_decryption_shares = gossip
            .join_topic(crate::federation_sync::TOPIC_DECRYPTION_SHARES, &peer_addrs)
            .await;
        let topic_budget = gossip
            .join_topic(crate::federation_sync::TOPIC_BUDGET, &peer_addrs)
            .await;

        // If all topics joined successfully, build and store the GossipHandle.
        if let (Ok(tt), Ok(tr), Ok(ti), Ok(tro), Ok(tc), Ok(td), Ok(tb)) = (
            topic_turns,
            topic_revocations,
            topic_intents,
            topic_roots,
            topic_checkpoints,
            topic_decryption_shares,
            topic_budget,
        ) {
            let gossip_handle = crate::federation_sync::GossipHandle {
                network: gossip.clone(),
                topic_turns: tt,
                topic_revocations: tr,
                topic_intents: ti,
                topic_roots: tro,
                topic_checkpoints: tc,
                topic_decryption_shares: td,
                topic_budget: tb,
            };
            state.set_gossip(gossip_handle).await;
        }
    }

    // Record initial peer count metric.
    crate::metrics::set_federation_peers_connected(peer_addrs.len() as f64);

    info!("blocklace gossip layer initialized, processing messages");

    // ─── Spawn the Gossip Receiver Task ─────────────────────────────────────

    let handle_for_receiver = handle.clone();
    let state_for_receiver = state.clone();
    tokio::spawn(async move {
        loop {
            match blocklace_stream.recv().await {
                Some(GossipEvent::Message { from, message }) => {
                    handle_blocklace_message(
                        &handle_for_receiver,
                        &state_for_receiver,
                        from,
                        message,
                    )
                    .await;
                }
                Some(GossipEvent::PeerJoined(addr)) => {
                    info!(peer = %addr, "peer joined blocklace topic");
                    // When a new peer joins, send them our frontier so they know
                    // what we have (enables efficient catch-up).
                    let lace = handle_for_receiver.lace.read().await;
                    let frontier_tips = lace.tips().clone();
                    drop(lace);

                    let msg = BlocklaceGossipMessage::Frontier(frontier_tips);
                    handle_for_receiver.broadcast_gossip_message(&msg).await;
                }
                Some(GossipEvent::PeerLeft(addr)) => {
                    info!(peer = %addr, "peer left blocklace topic");
                }
                None => {
                    warn!("blocklace gossip stream ended");
                    break;
                }
            }
        }
    });

    // ─── Spawn the Finalized Turn Executor Task ─────────────────────────────

    spawn_finality_executor(state.clone(), handle.clone());

    Some(handle)
}

// ─── Message Handling ───────────────────────────────────────────────────────

/// Process an incoming blocklace gossip message.
async fn handle_blocklace_message(
    handle: &BlocklaceHandle,
    state: &NodeState,
    from: SocketAddr,
    message: PeerMessage,
) {
    let turn_data = match message {
        PeerMessage::PublishTurn { turn_data, .. } => turn_data,
        _ => return,
    };

    let gossip_msg: BlocklaceGossipMessage = match postcard::from_bytes(&turn_data) {
        Ok(msg) => msg,
        Err(e) => {
            debug!(from = %from, error = %e, "failed to decode blocklace gossip message");
            return;
        }
    };

    match gossip_msg {
        BlocklaceGossipMessage::Push(delta) => {
            handle_push(handle, state, from, delta).await;
        }
        BlocklaceGossipMessage::Pull(missing_ids) => {
            handle_pull(handle, from, missing_ids).await;
        }
        BlocklaceGossipMessage::PullResponse(delta) => {
            handle_push(handle, state, from, delta).await;
        }
        BlocklaceGossipMessage::Frontier(their_tips) => {
            handle_frontier(handle, from, their_tips).await;
        }
    }
}

/// Handle a Push (or PullResponse) message: receive blocks into our blocklace.
async fn handle_push(
    handle: &BlocklaceHandle,
    _state: &NodeState,
    from: SocketAddr,
    delta: DeltaGroup,
) {
    if delta.is_empty() {
        return;
    }

    let block_count = delta.len();
    let mut lace = handle.lace.write().await;

    // Merge the delta into our local blocklace.
    match lace.merge(delta.blocks) {
        Ok(()) => {
            info!(
                from = %from,
                blocks = block_count,
                total = lace.len(),
                "merged blocklace delta from peer"
            );
        }
        Err(e) => {
            warn!(
                from = %from,
                error = %e,
                "failed to merge blocklace delta"
            );
            // If merge failed due to missing predecessors, we could send a Pull
            // request. For now, log and let the next push/frontier exchange fix it.
        }
    }
}

/// Handle a Pull request: respond with requested blocks.
async fn handle_pull(handle: &BlocklaceHandle, from: SocketAddr, missing_ids: Vec<BlockId>) {
    if missing_ids.is_empty() {
        return;
    }

    let lace = handle.lace.read().await;

    // Collect the requested blocks and their causal predecessors.
    let mut to_send: Vec<pyana_blocklace::finality::Block> = Vec::new();
    let mut sent_ids = std::collections::HashSet::new();

    for block_id in &missing_ids {
        if let Some(block) = lace.get(block_id) {
            // Add predecessors first (causal closure).
            let past = lace.causal_past(block_id);
            // Sort so predecessors come before dependents.
            for past_id in &past {
                if !sent_ids.contains(past_id) {
                    if let Some(past_block) = lace.get(past_id) {
                        to_send.push(past_block.clone());
                        sent_ids.insert(*past_id);
                    }
                }
            }
            if !sent_ids.contains(block_id) {
                to_send.push(block.clone());
                sent_ids.insert(*block_id);
            }
        }
    }

    drop(lace);

    if !to_send.is_empty() {
        let response = BlocklaceGossipMessage::PullResponse(DeltaGroup::from_blocks(to_send));
        handle.broadcast_gossip_message(&response).await;
        debug!(from = %from, blocks = sent_ids.len(), "sent pull response");
    }
}

/// Handle a Frontier announcement: determine what the peer needs and push it.
async fn handle_frontier(
    handle: &BlocklaceHandle,
    from: SocketAddr,
    their_tips: HashMap<[u8; 32], BlockId>,
) {
    let lace = handle.lace.read().await;

    // Convert their tips to a Frontier for the disseminator.
    let their_frontier = Frontier { tips: their_tips };

    // Compute what they're missing based on our local state.
    let mut disseminator = handle.disseminator.lock().await;
    let delta = disseminator.compute_delta_from_frontier(&their_frontier);
    drop(disseminator);
    drop(lace);

    if !delta.is_empty() {
        let msg = BlocklaceGossipMessage::Push(delta.clone());
        handle.broadcast_gossip_message(&msg).await;
        debug!(from = %from, blocks = delta.len(), "pushed delta after frontier exchange");
    }
}

// ─── Finalized Turn Executor ────────────────────────────────────────────────

/// Spawn a background task that polls for finalized blocks and executes their turns.
///
/// This task is QUIESCENT-aware: it only wakes up when there are new blocks to process.
/// In practice it polls on a short interval, but does no work when idle.
fn spawn_finality_executor(state: NodeState, handle: BlocklaceHandle) {
    tokio::spawn(async move {
        // Use a notify-driven approach: poll for new finalized blocks.
        // The interval is short (100ms) but the task does nothing when there's
        // no new work (quiescent-friendly).
        let mut poll_interval = tokio::time::interval(std::time::Duration::from_millis(100));

        loop {
            poll_interval.tick().await;

            // Check for newly finalized turns.
            let finalized_turns = handle.poll_finalized_turns().await;

            if finalized_turns.is_empty() {
                continue;
            }

            info!(
                turns = finalized_turns.len(),
                "executing finalized blocklace turns"
            );

            for (block_id, turn_data) in &finalized_turns {
                execute_finalized_turn(&state, *block_id, turn_data).await;
            }
        }
    });
}

/// Execute a single finalized turn against the node's ledger.
///
/// The turn has been totally ordered by the tau function and is ready for
/// deterministic execution.
async fn execute_finalized_turn(state: &NodeState, block_id: BlockId, turn_data: &[u8]) {
    // Deserialize the signed turn.
    let signed_turn: pyana_sdk::SignedTurn = match postcard::from_bytes(turn_data) {
        Ok(st) => st,
        Err(e) => {
            warn!(
                block_id = %block_id,
                error = %e,
                "failed to deserialize turn from finalized block"
            );
            return;
        }
    };

    // Verify the turn signature.
    let computed_hash = signed_turn.turn.hash();
    if !signed_turn
        .signer
        .verify(&computed_hash, &signed_turn.signature)
    {
        warn!(
            block_id = %block_id,
            "invalid signature on finalized turn, skipping"
        );
        return;
    }

    let turn_hash_hex: String = computed_hash.iter().map(|b| format!("{b:02x}")).collect();

    // Execute the turn against the local ledger.
    let mut s = state.write().await;
    let mut executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

    // Configure the executor with current node state.
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
            let receipt_hash_hex: String = receipt
                .turn_hash
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();

            // Resolve any pending turns waiting on this receipt.
            s.pending_turns.resolve(
                computed_hash,
                pyana_turn::ResolutionOutcome::Resolved(receipt.clone()),
            );

            // Process note commitments from NoteCreate effects.
            for tree in &signed_turn.turn.call_forest.roots {
                for effect in &tree.action.effects {
                    if let pyana_turn::Effect::NoteCreate { commitment, .. } = effect {
                        s.note_tree_append_commitment(&commitment.0);
                        let _ = s.store.store_note_commitment(commitment);
                    }
                }
            }

            // Append receipt to wallet.
            s.wallet.append_receipt(receipt.clone());
            drop(s);

            // Emit to WS subscribers.
            state.emit(NodeEvent::Receipt {
                hash: receipt_hash_hex,
            });

            info!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn executed (blocklace consensus)"
            );
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                reason = %reason,
                "finalized turn rejected"
            );
        }
        pyana_turn::TurnResult::Expired => {
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn expired"
            );
        }
        pyana_turn::TurnResult::Pending => {
            debug!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn pending"
            );
        }
    }
}
