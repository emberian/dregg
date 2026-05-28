//! Federation sync via the blocklace (Cordial Miners) consensus layer.
//!
//! Implements the live BFT consensus using the blocklace DAG structure from the
//! Cordial Miners paper (this superseded an earlier propose/vote/finalize BFT
//! simulation in `dregg_federation::node`). The blocklace provides:
//! - Quiescent operation (no messages when idle)
//! - Efficient cordial dissemination (send peers blocks you think they need)
//! - Leaderless total ordering via the tau function
//! - Equivocation detection built into the data structure
//! - Constitutional membership amendments via voting
//!
//! The node participates in consensus by:
//! 1. Creating blocks when turns are submitted
//! 2. Disseminating blocks to peers via the existing QUIC gossip transport
//! 3. Running tau() ordering to produce the finalized total order
//! 4. Processing finalized turns through the TurnExecutor

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use dregg_blocklace::constitution::{
    Constitution, ConstitutionManager, LeaveReason, MembershipProposal, MembershipVote,
};
use dregg_blocklace::dissemination::MAX_BLOCKS_PER_PUSH;
use dregg_blocklace::finality::{
    Block, BlockError, BlockId, Blocklace, FinalityLevel, MembershipAction, Payload,
    TurnArtifactBundle,
};
use dregg_blocklace::ordering::tau;
use dregg_net::gossip::{GossipEvent, GossipNetwork, TopicHandle};
use dregg_net::message::PeerMessage;
use dregg_net::node::{NodeId, PeerNode, PeerNodeConfig};
use dregg_persist::BlocklaceMeta;
use tokio::sync::{Notify, RwLock};
use tracing::{debug, error, info, warn};

use crate::state::{NodeEvent, NodeState};

// ─── Constants ──────────────────────────────────────────────────────────────

/// Gossip topic for blocklace dissemination messages.
pub const TOPIC_BLOCKLACE: &str = "dregg/blocklace";

/// Maximum number of blocklace checkpoints to retain. Older checkpoints are pruned
/// to bound storage growth.
const MAX_RETAINED_CHECKPOINTS: usize = 5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidBlocklaceBundleEvidence {
    pub block_id: BlockId,
    pub reason: String,
}

// ─── Gossip Message Types ───────────────────────────────────────────────────

/// Wire-format message for blocklace gossip.
///
/// These are the only consensus messages on the gossip network.
/// The protocol is quiescent: messages are only sent when a turn is submitted
/// or a new block arrives from a peer.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BlocklaceGossipMessage {
    /// Push blocks I think you need (causally-closed delta).
    Push(Vec<Block>),
    /// Request blocks I'm missing.
    Pull(Vec<BlockId>),
    /// Response to a pull request.
    PullResponse(Vec<Block>),
    /// Lightweight frontier for efficient sync: creator -> tip block ID.
    Frontier(HashMap<[u8; 32], BlockId>),
    /// Announce that a checkpoint is available at the given height.
    /// Peers can then request the full checkpoint data via the HTTP API.
    /// Contains just the height and content hash (not the full checkpoint data).
    CheckpointAvailable {
        height: u64,
        checkpoint_hash: [u8; 32],
    },
}

// ─── Shared Blocklace State ─────────────────────────────────────────────────

/// Thread-safe handle to the blocklace consensus state.
///
/// Shared between the gossip receiver task and the HTTP API (for turn submission).
#[derive(Clone)]
pub struct BlocklaceHandle {
    /// The local blocklace (with signing key, equivocation detection, finality).
    pub lace: Arc<RwLock<Blocklace>>,
    /// Constitution manager tracking participants and membership amendments.
    pub constitution: Arc<RwLock<ConstitutionManager>>,
    /// The gossip network for broadcasting messages.
    pub gossip: Arc<GossipNetwork>,
    /// The blocklace gossip topic handle.
    pub topic: TopicHandle,
    /// Our own public key (node identity for the blocklace).
    pub self_key: [u8; 32],
    /// Index tracking which ordered blocks have already been executed.
    pub executed_up_to: Arc<RwLock<usize>>,
    /// Notify channel: signaled when new blocks arrive that may advance finality.
    /// This makes the executor truly quiescent -- no polling.
    pub finality_notify: Arc<Notify>,
    /// If true, automatically vote to approve all join proposals (devnet mode).
    /// In production, nodes should require governance or stake proofs before approving.
    pub auto_approve_joins: bool,
    /// Blocklace configurability field (populated from CLI or safe defaults).
    /// Allows operators to tune for devnet (low latency, small budgets) vs production
    /// (larger windows, conservative timeouts) without "wrong way" source hacks.
    pub checkpoint_interval: u64,
}

/// A read-only view of one blocklace block, shaped to mirror the wasm
/// `get_federation_block` binding so the SAME `<dregg-block-dag>` inspector
/// renders both the in-browser sim and live node data.
///
/// `height` = the block's `seq` within its creator's chain. `prev_hash` is the
/// FIRST predecessor (the block's primary parent); `predecessors` carries the
/// full DAG parent set for inspectors that render the lace structure. All hashes
/// are real: `block_hash` is `Block::id()` (blake3 over signed content), and the
/// parent hashes come from the block's actual `predecessors` field.
#[derive(Clone, Debug, serde::Serialize)]
pub struct BlockView {
    pub height: u64,
    pub view: u64,
    pub proposer: String,
    pub block_hash: String,
    pub prev_hash: String,
    pub predecessors: Vec<String>,
    pub pre_state_root: String,
    pub post_state_root: String,
    pub events: Vec<String>,
    pub num_votes: usize,
    pub qc_threshold: usize,
    /// Payload kind: "turn" | "turn_bundle" | "heartbeat" | "checkpoint" |
    /// "membership" | "data". Lets the inspector distinguish heartbeats from
    /// turn-bearing blocks.
    pub kind: String,
    /// Finality round (DAG depth) assigned by tau ordering, if ordered.
    pub finality_round: Option<u64>,
}

impl BlocklaceHandle {
    /// Snapshot every block in the local blocklace as a list of [`BlockView`]s,
    /// sorted by (seq, creator) so the result is a deterministic, height-ordered
    /// view of the DAG. Each view carries real block/parent hashes.
    pub async fn block_views(&self) -> Vec<BlockView> {
        let lace = self.lace.read().await;
        let quorum = {
            let c = self.constitution.read().await;
            c.threshold()
        };
        let mut blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
        blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));
        blocks
            .into_iter()
            .map(|(id, block)| {
                let predecessors: Vec<String> =
                    block.predecessors.iter().map(|p| hex_encode(&p.0)).collect();
                let prev_hash = block
                    .predecessors
                    .first()
                    .map(|p| hex_encode(&p.0))
                    .unwrap_or_else(|| hex_encode(&[0u8; 32]));
                let kind = match &block.payload {
                    Payload::Turn(_) => "turn",
                    Payload::TurnBundle(_) => "turn_bundle",
                    Payload::Ack => "heartbeat",
                    Payload::Checkpoint { .. } => "checkpoint",
                    Payload::MembershipVote { .. } => "membership",
                    Payload::Data(_) => "data",
                }
                .to_string();
                BlockView {
                    height: block.seq,
                    view: 0,
                    proposer: hex_encode(&block.creator),
                    block_hash: hex_encode(&id.0),
                    prev_hash,
                    predecessors,
                    pre_state_root: hex_encode(&[0u8; 32]),
                    post_state_root: hex_encode(&[0u8; 32]),
                    events: Vec::new(),
                    num_votes: 0,
                    qc_threshold: quorum,
                    kind,
                    finality_round: lace.round_of(id),
                }
            })
            .collect()
    }

    /// The real blocklace DAG tip height: the maximum block `seq` across all
    /// creators in the local lace. This is the honest "how tall is the chain"
    /// number — it advances on every block (turns AND heartbeats), unlike the
    /// attested-root height which only moves on turn-bearing finality.
    ///
    /// Returns 0 for an empty lace (e.g. genesis-only before the first block).
    pub async fn dag_height(&self) -> u64 {
        let lace = self.lace.read().await;
        lace.iter().map(|(_, block)| block.seq).max().unwrap_or(0)
    }

    /// Number of blocks in the local blocklace DAG.
    pub async fn block_count(&self) -> usize {
        let lace = self.lace.read().await;
        lace.len()
    }

    /// Find the block whose creator-seq equals `height`. When several creators
    /// produced a block at the same seq (multi-node DAG), the lexicographically
    /// smallest creator wins for determinism. Returns `None` if no such block.
    pub async fn block_view_at_height(&self, height: u64) -> Option<BlockView> {
        self.block_views()
            .await
            .into_iter()
            .find(|v| v.height == height)
    }
}

/// A finalized block's payload, ready for execution by the finality executor.
///
/// The executor dispatches on this enum to process turns (state transitions),
/// membership votes (constitution amendments), and other payload types.
#[derive(Clone, Debug)]
pub enum FinalizedBlock {
    /// A dregg turn ready for ledger execution.
    Turn {
        block_id: BlockId,
        data: Vec<u8>,
        artifacts: Option<TurnArtifactBundle>,
    },
    /// A membership vote/proposal ready for constitution processing.
    Membership {
        block_id: BlockId,
        creator: [u8; 32],
        action: MembershipAction,
    },
    /// A checkpoint (no active processing needed at consensus level).
    Checkpoint {
        block_id: BlockId,
        root: [u8; 32],
        height: u64,
    },
}

impl BlocklaceHandle {
    /// Submit a turn to the blocklace.
    ///
    /// Creates a new block with the turn payload, adds it to the local blocklace,
    /// and pushes it to all known peers.
    ///
    /// Returns the block ID (used as a receipt handle) and the initial finality level.
    pub async fn submit_turn(
        &self,
        state: &NodeState,
        turn_data: Vec<u8>,
    ) -> (BlockId, FinalityLevel) {
        self.submit_turn_payload(state, Payload::Turn(turn_data))
            .await
    }

    /// Submit a signed turn plus committed receipt/witness artifacts to the
    /// blocklace. Peers that understand bundle payloads can materialize the
    /// full devnet artifact; older raw-turn blocks remain valid.
    pub async fn submit_turn_bundle(
        &self,
        state: &NodeState,
        bundle: TurnArtifactBundle,
    ) -> (BlockId, FinalityLevel) {
        self.submit_turn_payload(state, Payload::TurnBundle(bundle))
            .await
    }

    /// Produce an empty heartbeat block (`Payload::Ack`).
    ///
    /// A heartbeat is a real, signed block linking to the current tips; it
    /// carries no turn but advances the DAG (seq + parent links) so the chain
    /// makes visible progress while idle. Returns the new block id.
    pub async fn submit_heartbeat(&self, state: &NodeState) -> BlockId {
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(Payload::Ack)
        };
        let block_id = block.id();
        Self::persist_block_to_store(state, &block).await;

        // Heartbeats still advance ordering bookkeeping (the finality executor
        // treats Ack as a no-op for execution but the seq/tip have advanced).
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        debug!(block_id = %block_id, seq = block.seq, "produced heartbeat block");
        block_id
    }

    async fn submit_turn_payload(
        &self,
        state: &NodeState,
        payload: Payload,
    ) -> (BlockId, FinalityLevel) {
        // Create the block in our local blocklace.
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(payload)
        };
        let block_id = block.id();

        // Persist the newly created block to the store.
        Self::persist_block_to_store(state, &block).await;

        // Determine initial finality based on participant count.
        let constitution = self.constitution.read().await;
        let initial_finality = if constitution.current.participant_count() <= 1 {
            // Solo mode: immediately ordered (we're the only participant).
            // tau() with n=1 trivially finalizes every block.
            FinalityLevel::Ordered
        } else {
            FinalityLevel::Local
        };
        drop(constitution);

        // Notify the finality executor that new blocks are available.
        self.finality_notify.notify_one();

        // Disseminate to all peers via gossip.
        self.push_new_blocks().await;

        (block_id, initial_finality)
    }

    /// Persist a block to the store. Logs a warning on failure but does not
    /// propagate the error (persistence failure should not block consensus progress).
    async fn persist_block_to_store(state: &NodeState, block: &Block) {
        let s = state.read().await;
        if let Err(e) = s.store.persist_block(block) {
            warn!(error = %e, "failed to persist block to store");
        }
    }

    /// Push new blocks to peers via the gossip topic.
    ///
    /// Broadcasts all blocks from our local blocklace that peers may not have.
    /// In practice, since we broadcast on a topic, all subscribed peers see it.
    /// The protocol is quiescent: this is only called when we create a new block.
    async fn push_new_blocks(&self) {
        let lace = self.lace.read().await;

        // Get our latest block (just the one we created).
        let our_tip = match lace.tips().get(&self.self_key) {
            Some(tip) => *tip,
            None => return,
        };

        // Send the block (and its immediate context) to peers.
        if let Some(block) = lace.get(&our_tip) {
            let msg = BlocklaceGossipMessage::Push(vec![block.clone()]);
            self.broadcast_gossip_message(&msg).await;
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

    /// Run the tau ordering function and return newly finalized blocks.
    ///
    /// This is the core consensus function: it computes the deterministic total
    /// order from the blocklace DAG using the Cordial Miners tau function,
    /// then returns any blocks that have been newly ordered since the last call.
    ///
    /// Returns all actionable finalized blocks (turns, membership votes, checkpoints).
    /// Ack and Data payloads are skipped as they need no consensus-level processing.
    pub async fn poll_finalized_blocks(&self) -> Vec<FinalizedBlock> {
        let lace = self.lace.read().await;
        let constitution = self.constitution.read().await;
        let participants = constitution.current.participants.clone();
        drop(constitution);

        let mut executed_up_to = self.executed_up_to.write().await;

        // For solo mode (n=1): every block is immediately finalized in topological
        // order. tau() handles this correctly because with a single participant,
        // every block trivially has supermajority.
        let ordered = if participants.len() <= 1 {
            // Solo: all actionable blocks are ordered by sequence.
            let mut all_blocks: Vec<(u64, BlockId)> = lace
                .iter()
                .filter_map(|(id, block)| match &block.payload {
                    Payload::Turn(_)
                    | Payload::TurnBundle(_)
                    | Payload::MembershipVote { .. }
                    | Payload::Checkpoint { .. } => Some((block.seq, *id)),
                    _ => None,
                })
                .collect();
            all_blocks.sort_by_key(|(seq, _)| *seq);
            all_blocks.into_iter().map(|(_, id)| id).collect::<Vec<_>>()
        } else {
            // Multi-party: run the full Cordial Miners tau ordering.
            // We build an ordering-compatible blocklace and maintain a mapping
            // between the two BlockId types (they use different hash schemes).
            let (ordering_lace, id_map) = build_ordering_blocklace(&lace);
            let raw_order = tau(&ordering_lace, &participants);
            // Map ordering BlockIds back to finality BlockIds.
            raw_order
                .into_iter()
                .filter_map(|ordering_id| id_map.get(&ordering_id).copied())
                .collect::<Vec<_>>()
        };

        // Skip already-executed blocks.
        if ordered.len() <= *executed_up_to {
            return vec![];
        }

        let new_blocks = &ordered[*executed_up_to..];
        let mut finalized = Vec::new();

        for block_id in new_blocks {
            if let Some(block) = lace.get(block_id) {
                match &block.payload {
                    Payload::Turn(data) => {
                        finalized.push(FinalizedBlock::Turn {
                            block_id: *block_id,
                            data: data.clone(),
                            artifacts: None,
                        });
                    }
                    Payload::TurnBundle(bundle) => {
                        finalized.push(FinalizedBlock::Turn {
                            block_id: *block_id,
                            data: bundle.signed_turn.clone(),
                            artifacts: Some(bundle.clone()),
                        });
                    }
                    Payload::MembershipVote { action } => {
                        finalized.push(FinalizedBlock::Membership {
                            block_id: *block_id,
                            creator: block.creator,
                            action: action.clone(),
                        });
                    }
                    Payload::Checkpoint { root, height } => {
                        finalized.push(FinalizedBlock::Checkpoint {
                            block_id: *block_id,
                            root: *root,
                            height: *height,
                        });
                    }
                    // Ack and Data payloads need no consensus-level processing.
                    Payload::Ack | Payload::Data(_) => {}
                }
            }
        }

        *executed_up_to = ordered.len();
        finalized
    }

    /// Propose joining the federation (called on first connect if not already a member).
    ///
    /// If this node's key is not in the current constitution, it creates a
    /// `MembershipVote` block proposing its own Join and disseminates it.
    /// Existing participants will vote on the proposal according to their policy
    /// (auto-approve in devnet mode, governance-gated in production).
    pub async fn propose_join_if_needed(&self, state: &NodeState) {
        let constitution = self.constitution.read().await;
        if constitution.current.is_participant(&self.self_key) {
            return; // Already a member
        }
        drop(constitution);

        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(Payload::MembershipVote {
                action: MembershipAction::Join {
                    node_id: self.self_key,
                },
            })
        };

        // Persist the membership vote block.
        Self::persist_block_to_store(state, &block).await;

        info!(
            block_id = %block.id(),
            "proposed join to federation (awaiting threshold approvals)"
        );

        // Disseminate to peers via gossip.
        self.push_new_blocks().await;
    }

    /// Cast an approval vote for a membership proposal.
    ///
    /// Creates a `MembershipVote` block with an `Approve` action referencing
    /// the proposal block, and disseminates it to peers.
    async fn cast_approval_vote(&self, state: &NodeState, proposal_block: BlockId) {
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(Payload::MembershipVote {
                action: MembershipAction::Approve { proposal_block },
            })
        };

        // Persist the approval vote block.
        Self::persist_block_to_store(state, &block).await;

        debug!(
            block_id = %block.id(),
            proposal = %proposal_block,
            "cast approval vote for membership proposal"
        );

        self.push_new_blocks().await;
    }
}

/// Build a `dregg_blocklace::Blocklace` (the ordering-compatible type) from
/// the finality-layer blocklace. The ordering module's `tau()` function
/// operates on the simpler `Blocklace` from `lib.rs`.
///
/// Returns the ordering blocklace and a mapping from ordering BlockIds to
/// finality BlockIds (needed because the two types use different hash schemes).
fn build_ordering_blocklace(
    finality_lace: &Blocklace,
) -> (
    dregg_blocklace::Blocklace,
    HashMap<dregg_blocklace::BlockId, BlockId>,
) {
    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    // Mapping from finality block ID -> ordering block ID (for predecessor translation)
    let mut finality_to_ordering: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    // Reverse mapping: ordering block ID -> finality block ID (for result translation)
    let mut ordering_to_finality: HashMap<dregg_blocklace::BlockId, BlockId> = HashMap::new();

    // Insert blocks in topological order (by sequence, then by creator for ties).
    let mut blocks: Vec<(&BlockId, &Block)> = finality_lace.iter().collect();
    blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    for (finality_id, block) in blocks {
        // Translate predecessors from finality IDs to ordering IDs.
        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| finality_to_ordering.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(data) => data.clone(),
            Payload::TurnBundle(bundle) => bundle.signed_turn.clone(),
            Payload::Ack => vec![],
            Payload::Checkpoint { root, height } => {
                let mut buf = Vec::with_capacity(40);
                buf.extend_from_slice(root);
                buf.extend_from_slice(&height.to_le_bytes());
                buf
            }
            Payload::MembershipVote { .. } => vec![0x04],
            Payload::Data(data) => data.clone(),
        };
        let ordering_block =
            dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let ordering_id = ordering_block.id();
        let _ = ordering_lace.insert(ordering_block);

        // Record the bidirectional mapping.
        finality_to_ordering.insert(*finality_id, ordering_id);
        ordering_to_finality.insert(ordering_id, *finality_id);
    }
    (ordering_lace, ordering_to_finality)
}

// ─── Main Entry Point ───────────────────────────────────────────────────────

/// Run the blocklace-based federation sync as a background task.
///
/// This is the replacement for `federation_sync::run_federation_sync` when
/// `--consensus blocklace` is specified.
///
/// Key property: QUIESCENT operation. No periodic timers for consensus.
/// Activity only when a turn is submitted or blocks arrive from peers.
pub async fn run_blocklace_sync(
    state: NodeState,
    gossip_port: u16,
    auto_approve_joins: bool,
    blocklace_checkpoint_interval: u64,
    constitution_timeout_ms: u64,
    block_cadence_ms: u64,
) -> Option<BlocklaceHandle> {
    // Blocklace tuning params (from CLI --blocklace-* or safe defaults in main).
    // This is the core of making blocklace easy to configure/enable/disable/tune
    // for different envs without wrong-way const edits or forks.
    let peers = {
        let s = state.read().await;
        s.peers.clone()
    };

    // Get our signing key and derive the blocklace identity.
    let (gossip_signing_key, signing_key_bytes, our_public_key) = {
        let s = state.read().await;
        let sk = s.cclerk.gossip_signing_key();
        let pk = s.cclerk.public_key();
        (sk.clone(), sk.to_bytes(), pk)
    };

    // The finality::Blocklace uses ed25519_dalek::SigningKey directly.
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&signing_key_bytes);
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
        // 2f+1 where f = (n-1)/3
        (participants.len() * 2 / 3) + 1
    };

    info!(
        participants = participants.len(),
        quorum_threshold = quorum_threshold,
        solo = (participants.len() <= 1),
        "initializing blocklace consensus"
    );

    // Initialize the constitution with our participant set. (tunable via CLI)
    let constitution = Constitution::new(participants.clone(), constitution_timeout_ms);
    let constitution_manager = ConstitutionManager::new(constitution);

    // Attempt to restore blocklace from persistent storage.
    let (blocklace, restored_executed_up_to) = {
        let s = state.read().await;
        match s
            .store
            .load_blocklace(signing_key.clone(), quorum_threshold)
        {
            Ok(Some((restored_lace, executed_up_to))) => {
                let block_count = restored_lace.len();
                info!(
                    blocks = block_count,
                    executed_up_to = executed_up_to,
                    "restored blocklace from persistent storage"
                );
                (restored_lace, executed_up_to)
            }
            Ok(None) => {
                info!("no persisted blocklace found, starting fresh");
                (Blocklace::new(signing_key.clone(), quorum_threshold), 0)
            }
            Err(e) => {
                warn!(
                    error = %e,
                    "failed to restore blocklace from storage, starting fresh"
                );
                (Blocklace::new(signing_key.clone(), quorum_threshold), 0)
            }
        }
    };
    // Create the PeerNode (QUIC endpoint) for gossip.
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
        node_id = %dregg_net::node::fmt_node_id(&node_id),
        local_addr = %peer_node.local_addr(),
        "blocklace PeerNode ready"
    );

    // Build the signing key registry from known federation keys.
    let peer_keys_map = {
        let s = state.read().await;
        let mut peer_keys: std::collections::HashMap<NodeId, dregg_types::PublicKey> =
            std::collections::HashMap::new();
        for fed_key in &s.known_federation_keys {
            let peer_node_id = *blake3::hash(fed_key.as_bytes()).as_bytes();
            peer_keys.insert(peer_node_id, *fed_key);
        }
        peer_keys.insert(node_id, our_public_key);
        peer_keys
    };

    // Create the GossipNetwork with Ed25519 asymmetric signing.
    let gossip = Arc::new(GossipNetwork::new(
        endpoint,
        node_id,
        gossip_signing_key,
        peer_keys_map,
    ));

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

    // Join the blocklace gossip topic.
    let topic = match gossip.join_topic(TOPIC_BLOCKLACE, &peer_addrs).await {
        Ok(t) => t,
        Err(e) => {
            error!(error = %e, "failed to join blocklace topic");
            return None;
        }
    };

    // Subscribe to the blocklace topic for incoming messages.
    let mut blocklace_stream = match gossip.subscribe(&topic).await {
        Ok(s) => s,
        Err(e) => {
            error!(error = %e, "failed to subscribe to blocklace topic");
            return None;
        }
    };

    // Also join the standard gossip topics so the node participates in
    // turn/revocation/intent data propagation (the blocklace handles ordering,
    // but existing topics handle non-consensus gossip).
    if !peer_addrs.is_empty() {
        let topic_turns = gossip
            .join_topic(crate::gossip::TOPIC_TURNS, &peer_addrs)
            .await;
        let topic_revocations = gossip
            .join_topic(crate::gossip::TOPIC_REVOCATIONS, &peer_addrs)
            .await;
        let topic_intents = gossip
            .join_topic(crate::gossip::TOPIC_INTENTS, &peer_addrs)
            .await;
        let topic_roots = gossip
            .join_topic(crate::gossip::TOPIC_ROOTS, &peer_addrs)
            .await;
        let topic_checkpoints = gossip
            .join_topic(crate::gossip::TOPIC_CHECKPOINTS, &peer_addrs)
            .await;
        let topic_decryption_shares = gossip
            .join_topic(crate::gossip::TOPIC_DECRYPTION_SHARES, &peer_addrs)
            .await;
        let topic_budget = gossip
            .join_topic(crate::gossip::TOPIC_BUDGET, &peer_addrs)
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
            let gossip_handle = crate::gossip::GossipHandle {
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

    // Build the shared handle.
    let lace = Arc::new(RwLock::new(blocklace));
    let constitution_handle = Arc::new(RwLock::new(constitution_manager));
    let executed_up_to = Arc::new(RwLock::new(restored_executed_up_to));
    let finality_notify = Arc::new(Notify::new());

    let handle = BlocklaceHandle {
        lace: lace.clone(),
        constitution: constitution_handle.clone(),
        gossip: gossip.clone(),
        topic: topic.clone(),
        self_key,
        executed_up_to,
        finality_notify: finality_notify.clone(),
        auto_approve_joins, // F-CRIT-2: gated by main.rs on --auto-approve-joins CLI flag OR .devnet marker
        checkpoint_interval: blocklace_checkpoint_interval,
    };

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
                    // When a new peer joins, send our frontier for efficient catch-up.
                    let lace = handle_for_receiver.lace.read().await;
                    let frontier_tips: HashMap<[u8; 32], BlockId> =
                        lace.tips().iter().map(|(k, v)| (*k, *v)).collect();
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

    // ─── Spawn the Block Production Cadence Task ─────────────────────────────
    //
    // The pure blocklace protocol is quiescent: a block is only produced when a
    // turn is submitted. For a devnet / explorer we also want the chain to make
    // visible progress over time even when idle, so (when cadence > 0) this task
    // drains the consensus queue into real blocks and, if the queue is empty,
    // produces an empty heartbeat block. Every block links to the current tips
    // (real parent hashes) and advances the creator's seq (real height).
    if block_cadence_ms > 0 {
        spawn_block_cadence(state.clone(), handle.clone(), block_cadence_ms);
    } else {
        info!("block cadence disabled (--block-cadence-ms 0): blocks produced only on turn submission");
    }

    // If we're not already a federation participant, propose joining.
    // This enables new nodes to join at runtime via the constitutional amendment
    // protocol. Existing participants will vote (auto-approve in devnet mode).
    let join_handle = handle.clone();
    let join_state = state.clone();
    tokio::spawn(async move {
        // Brief delay to allow gossip connections to establish.
        tokio::time::sleep(Duration::from_secs(2)).await;
        join_handle.propose_join_if_needed(&join_state).await;
    });

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
        BlocklaceGossipMessage::Push(blocks) => {
            handle_push(handle, state, from, blocks).await;
        }
        BlocklaceGossipMessage::Pull(missing_ids) => {
            handle_pull(handle, from, missing_ids).await;
        }
        BlocklaceGossipMessage::PullResponse(blocks) => {
            handle_push(handle, state, from, blocks).await;
        }
        BlocklaceGossipMessage::Frontier(their_tips) => {
            handle_frontier(handle, from, their_tips).await;
        }
        BlocklaceGossipMessage::CheckpointAvailable {
            height,
            checkpoint_hash,
        } => {
            debug!(
                from = %from,
                height = height,
                "peer announced checkpoint available"
            );
            // Record that this peer has a checkpoint at the given height.
            // The actual checkpoint data is fetched via HTTP when needed (during bootstrap).
            let _ = (height, checkpoint_hash);
        }
    }
}

/// Handle a Push (or PullResponse) message: receive blocks into our blocklace.
async fn handle_push(
    handle: &BlocklaceHandle,
    state: &NodeState,
    from: SocketAddr,
    blocks: Vec<Block>,
) {
    if blocks.is_empty() {
        return;
    }

    let block_count = blocks.len();
    let mut lace = handle.lace.write().await;
    let mut inserted = 0usize;
    let mut inserted_blocks: Vec<Block> = Vec::new();
    let mut missing_deps: Vec<BlockId> = Vec::new();

    for block in blocks {
        let block_clone = block.clone();
        match lace.receive_block(block) {
            Ok(()) => {
                inserted += 1;
                inserted_blocks.push(block_clone);
            }
            Err(BlockError::MissingPredecessor { missing, .. }) => {
                missing_deps.push(missing);
            }
            Err(BlockError::Equivocation {
                creator,
                seq,
                proof,
            }) => {
                let creator_hex: String = creator[..4].iter().map(|b| format!("{b:02x}")).collect();
                warn!(
                    from = %from,
                    creator = %creator_hex,
                    seq = seq,
                    "equivocation detected from peer"
                );
                // Auto-evict equivocator from the constitution.
                drop(lace);
                let mut constitution = handle.constitution.write().await;
                constitution.auto_evict(&proof);
                drop(constitution);
                lace = handle.lace.write().await;
                inserted += 1;
                inserted_blocks.push(block_clone);
            }
            Err(BlockError::InvalidSignature { creator, seq }) => {
                let creator_hex: String = creator[..4].iter().map(|b| format!("{b:02x}")).collect();
                warn!(
                    from = %from,
                    creator = %creator_hex,
                    seq = seq,
                    "invalid signature on block from peer"
                );
            }
        }
    }
    drop(lace);

    // Persist newly inserted blocks to the store (batch write for efficiency).
    if !inserted_blocks.is_empty() {
        let s = state.read().await;
        if let Err(e) = s.store.persist_blocks(&inserted_blocks) {
            warn!(error = %e, "failed to persist received blocks to store");
        }
        drop(s);
    }

    if inserted > 0 {
        info!(
            from = %from,
            inserted = inserted,
            total_received = block_count,
            "received blocks from peer"
        );
        // Signal the finality executor that new blocks may advance ordering.
        handle.finality_notify.notify_one();
    }

    // If we have missing dependencies, request them.
    if !missing_deps.is_empty() {
        missing_deps.dedup();
        let pull_msg = BlocklaceGossipMessage::Pull(missing_deps);
        handle.broadcast_gossip_message(&pull_msg).await;
    }
}

/// Handle a Pull request: respond with requested blocks.
///
/// Uses chunked responses for large pull requests to avoid single oversized messages.
async fn handle_pull(handle: &BlocklaceHandle, from: SocketAddr, missing_ids: Vec<BlockId>) {
    if missing_ids.is_empty() {
        return;
    }

    let lace = handle.lace.read().await;

    // Collect requested blocks. For causal closure, also include their
    // predecessors that the requester may be missing.
    let mut to_send: Vec<Block> = Vec::new();
    let mut sent_ids = std::collections::HashSet::new();

    for block_id in &missing_ids {
        // Include the causal past of the requested block.
        let past = lace.causal_past(block_id);
        for past_id in &past {
            if !sent_ids.contains(past_id) {
                if let Some(block) = lace.get(past_id) {
                    to_send.push(block.clone());
                    sent_ids.insert(*past_id);
                }
            }
        }
        // Include the block itself.
        if !sent_ids.contains(block_id) {
            if let Some(block) = lace.get(block_id) {
                to_send.push(block.clone());
                sent_ids.insert(*block_id);
            }
        }
    }
    drop(lace);

    if to_send.is_empty() {
        return;
    }

    let total = to_send.len();

    // Small response: send in one shot.
    if total <= MAX_BLOCKS_PER_PUSH {
        let response = BlocklaceGossipMessage::PullResponse(to_send);
        handle.broadcast_gossip_message(&response).await;
        debug!(from = %from, blocks = total, "sent pull response");
        return;
    }

    // Large response: chunk it.
    debug!(from = %from, blocks = total, "sending chunked pull response");
    let mut sent_so_far = 0usize;
    for chunk in to_send.chunks(MAX_BLOCKS_PER_PUSH) {
        let response = BlocklaceGossipMessage::PullResponse(chunk.to_vec());
        handle.broadcast_gossip_message(&response).await;
        sent_so_far += chunk.len();

        if sent_so_far < total {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
    debug!(from = %from, blocks = total, "completed chunked pull response");
}

/// Handle a Frontier announcement: determine what the peer needs and push it.
///
/// Uses chunked sending to avoid creating a single massive message when the
/// peer is far behind. Blocks are sent in causally-ordered chunks of at most
/// `MAX_BLOCKS_PER_PUSH` blocks, with a small delay between chunks to avoid
/// overwhelming the receiver.
async fn handle_frontier(
    handle: &BlocklaceHandle,
    from: SocketAddr,
    their_tips: HashMap<[u8; 32], BlockId>,
) {
    let to_send = {
        let lace = handle.lace.read().await;

        // Determine which blocks we have that the peer doesn't.
        // A peer with a given tip has all blocks in that tip's causal past.
        let mut their_known: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
        for (_, tip_id) in &their_tips {
            if lace.contains(tip_id) {
                let past = lace.causal_past(tip_id);
                their_known.extend(past);
                their_known.insert(*tip_id);
            }
        }

        // Collect blocks they don't have, sorted in causal order.
        let mut candidates: Vec<(&BlockId, &Block)> = lace
            .iter()
            .filter(|(id, _)| !their_known.contains(id))
            .collect();
        candidates
            .sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

        // Filter to causally-closed subset (predecessors before dependents).
        let mut peer_will_know = their_known;
        let mut result: Vec<Block> = Vec::new();
        for (id, block) in &candidates {
            if block
                .predecessors
                .iter()
                .all(|p| peer_will_know.contains(p))
            {
                result.push((*block).clone());
                peer_will_know.insert(**id);
            }
        }
        result
    };

    if to_send.is_empty() {
        return;
    }

    let total_missing = to_send.len();

    // If the delta fits in one message, send it directly (common case for
    // incremental updates after initial sync).
    if total_missing <= MAX_BLOCKS_PER_PUSH {
        let msg = BlocklaceGossipMessage::Push(to_send);
        handle.broadcast_gossip_message(&msg).await;
        debug!(from = %from, blocks = total_missing, "pushed delta after frontier exchange");
        return;
    }

    // Large delta: send in chunks to avoid OOM / timeout on either side.
    let num_chunks = (total_missing + MAX_BLOCKS_PER_PUSH - 1) / MAX_BLOCKS_PER_PUSH;
    info!(
        from = %from,
        total_blocks = total_missing,
        chunk_size = MAX_BLOCKS_PER_PUSH,
        chunks = num_chunks,
        "syncing blocklace: sending chunked delta to peer"
    );

    let mut sent_so_far = 0usize;
    for chunk in to_send.chunks(MAX_BLOCKS_PER_PUSH) {
        let msg = BlocklaceGossipMessage::Push(chunk.to_vec());
        handle.broadcast_gossip_message(&msg).await;

        sent_so_far += chunk.len();
        info!(
            "syncing blocklace: sent {}/{} blocks to peer {}",
            sent_so_far, total_missing, from
        );

        // Small delay between chunks to avoid overwhelming the receiver's
        // inbound buffer. The receiver's `pending` mechanism handles any
        // transient ordering issues between chunks.
        if sent_so_far < total_missing {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    debug!(
        from = %from,
        blocks = total_missing,
        "completed chunked frontier sync"
    );
}

// ─── Block Production Cadence ────────────────────────────────────────────────

/// Spawn a background task that produces blocks on a fixed cadence.
///
/// On each tick:
///   1. Drain any signed turns queued in `consensus_queue` and submit them as
///      real turn blocks (these flow through the finality executor and update
///      the ledger + attested roots).
///   2. If the queue was empty, produce a single empty *heartbeat* block
///      (`Payload::Ack`). A heartbeat carries no turn but is still a real,
///      Ed25519-signed block that links to the current tips — so the DAG keeps
///      advancing (real seq, real block id, real parent links) even when the
///      node is idle.
///
/// This is what makes a solo node "produce blocks over time" rather than only
/// when a turn happens to arrive. Disabled when `cadence_ms == 0`.
fn spawn_block_cadence(state: NodeState, handle: BlocklaceHandle, cadence_ms: u64) {
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_millis(cadence_ms));
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        // Skip the immediate first tick so we don't emit a block at t=0 before
        // genesis/state has settled.
        ticker.tick().await;
        info!(cadence_ms, "block production cadence active");
        loop {
            ticker.tick().await;

            // Drain queued turns (if any) into real turn blocks.
            let queued: Vec<dregg_sdk::SignedTurn> = {
                let mut s = state.write().await;
                std::mem::take(&mut s.consensus_queue)
            };

            if !queued.is_empty() {
                let n = queued.len();
                for signed in queued {
                    match postcard::to_stdvec(&signed) {
                        Ok(turn_data) => {
                            handle.submit_turn(&state, turn_data).await;
                        }
                        Err(e) => {
                            warn!(error = %e, "failed to encode queued turn for block production");
                        }
                    }
                }
                debug!(turns = n, "cadence: produced turn block(s) from consensus queue");
                continue;
            }

            // Idle: produce an empty heartbeat block so height keeps advancing.
            handle.submit_heartbeat(&state).await;
        }
    });
}

// ─── Finalized Turn Executor ────────────────────────────────────────────────

/// Spawn a background task that waits for finalized blocks and executes their turns.
///
/// This task is QUIESCENT: it uses `Notify` to sleep until new blocks arrive.
/// No polling interval. Zero CPU when idle.
fn spawn_finality_executor(state: NodeState, handle: BlocklaceHandle) {
    tokio::spawn(async move {
        loop {
            // QUIESCENT: sleep until signaled that new blocks have arrived.
            handle.finality_notify.notified().await;

            // Process all newly finalized blocks (turns, membership, checkpoints).
            let finalized_blocks = handle.poll_finalized_blocks().await;

            if finalized_blocks.is_empty() {
                continue;
            }

            let turn_count = finalized_blocks
                .iter()
                .filter(|b| matches!(b, FinalizedBlock::Turn { .. }))
                .count();
            let membership_count = finalized_blocks
                .iter()
                .filter(|b| matches!(b, FinalizedBlock::Membership { .. }))
                .count();

            if turn_count > 0 || membership_count > 0 {
                info!(
                    turns = turn_count,
                    membership_votes = membership_count,
                    total = finalized_blocks.len(),
                    "executing finalized blocklace blocks"
                );
            }

            for block in &finalized_blocks {
                match block {
                    FinalizedBlock::Turn {
                        block_id,
                        data,
                        artifacts,
                    } => {
                        execute_finalized_turn(
                            &state,
                            &handle,
                            *block_id,
                            data,
                            artifacts.as_ref(),
                        )
                        .await;
                    }
                    FinalizedBlock::Membership {
                        block_id,
                        creator,
                        action,
                    } => {
                        execute_finalized_membership(&state, &handle, *block_id, *creator, action)
                            .await;
                    }
                    FinalizedBlock::Checkpoint {
                        block_id,
                        root,
                        height,
                    } => {
                        debug!(
                            block_id = %block_id,
                            height = height,
                            "finalized checkpoint block (stored)"
                        );
                        let _ = (root, height); // Checkpoint storage handled elsewhere
                    }
                }
            }

            // ── Record Participant Activity ──────────────────────────────────
            // Track which participants produced blocks in this batch so that
            // the timeout mechanism knows they are still alive.
            {
                // Collect all block creators from this batch.
                let lace = handle.lace.read().await;
                let mut active_creators: Vec<[u8; 32]> = Vec::new();
                for block in &finalized_blocks {
                    match block {
                        FinalizedBlock::Membership { creator, .. } => {
                            active_creators.push(*creator);
                        }
                        FinalizedBlock::Turn { block_id, .. } => {
                            if let Some(b) = lace.get(block_id) {
                                active_creators.push(b.creator);
                            }
                        }
                        FinalizedBlock::Checkpoint { block_id, .. } => {
                            if let Some(b) = lace.get(block_id) {
                                active_creators.push(b.creator);
                            }
                        }
                    }
                }
                drop(lace);

                // Record activity for each creator.
                let mut constitution = handle.constitution.write().await;
                let wave = constitution.current_wave;
                for creator in &active_creators {
                    constitution.record_activity(creator, wave);
                }
            }

            // ── Wave Advancement & Timeout Detection ───────────────────────
            // Advance the constitution's wave counter. Any participants that
            // have been silent for too long are proposed for auto-leave.
            advance_constitution_wave(&state, &handle).await;

            // ── Periodic Checkpoint Production ──────────────────────────────
            // After executing finalized turns, check if we've crossed a
            // checkpoint interval boundary. If so, produce and store a
            // checkpoint and announce it to the gossip network.
            maybe_produce_checkpoint(&state, &handle).await;

            // ── Periodic Ledger Checkpoint ───────────────────────────────────
            // Every 100 finalized blocks, persist the ledger state so restarts
            // don't require replaying the full blocklace history.
            maybe_checkpoint_ledger(&state).await;

            // ── Persist Blocklace Metadata ───────────────────────────────────
            // Save the executed_up_to index and blocklace metadata (tips,
            // equivocators, ordering state) so restarts don't re-execute turns.
            persist_blocklace_state(&state, &handle).await;
        }
    });
}

/// Execute a single finalized turn against the node's ledger.
///
/// The turn has been totally ordered by the blocklace consensus (tau function)
/// and is ready for deterministic execution.
///
/// On successful commit this function ALSO:
/// 1. Produces a [`dregg_federation::FederationReceipt`] (audit F7) signed by
///    the local cipherclerk (Ed25519 vote-signature flavor; the BLS aggregate path
///    requires a multi-node ceremony we don't run inline). The receipt is
///    emitted via [`crate::state::NodeEvent::FederationReceipt`].
/// 2. Writes a fresh [`dregg_types::AttestedRoot`] anchored to the blocklace
///    `block_id` + finality round (audit F3 / gap D), so the executor on the
///    next turn no longer sees `block_height = 0`.
async fn execute_finalized_turn(
    state: &NodeState,
    handle: &BlocklaceHandle,
    block_id: BlockId,
    turn_data: &[u8],
    artifacts: Option<&TurnArtifactBundle>,
) {
    // Deserialize the signed turn.
    let signed_turn: dregg_sdk::SignedTurn = match postcard::from_bytes(turn_data) {
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

    // Resolve the Cordial Miners "round" (DAG depth) of this finalized block
    // BEFORE we take the state lock — the lace read lock is held briefly.
    let finality_round = {
        let lace = handle.lace.read().await;
        lace.round_of(&block_id)
    };

    // Execute the turn against the local ledger.
    let mut s = state.write().await;
    let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());

    // Configure the executor with the canonical federation_id (audit F1).
    // Falls back to discovery-mode (cipherclerk-hash) only if no committee has
    // been loaded yet — solo devnet pre-genesis.
    let local_fed_id = if s.federation_configured {
        s.federation_id
    } else {
        *blake3::hash(s.cclerk.public_key().as_bytes()).as_bytes()
    };
    executor.set_local_federation_id(local_fed_id);

    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    executor.set_timestamp(now);

    let prior_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    // Block height advances per finalized turn so downstream verifiers see a
    // monotone sequence (audit gap D: was always 0).
    let new_height = prior_height.saturating_add(1);
    executor.set_block_height(new_height);

    let exec_result = executor.execute(&signed_turn.turn, &mut s.ledger);

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let receipt_hash_hex: String = receipt
                .turn_hash
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            let invalid_bundle_evidence = if let Some(bundle) = artifacts {
                materialize_blocklace_artifacts(&mut s, block_id, &receipt, bundle)
            } else {
                Vec::new()
            };

            // Resolve any pending turns waiting on this receipt.
            s.pending_turns.resolve(
                computed_hash,
                dregg_turn::ResolutionOutcome::Resolved(receipt.clone()),
            );

            // Process note commitments from NoteCreate effects.
            for tree in &signed_turn.turn.call_forest.roots {
                for effect in &tree.action.effects {
                    if let dregg_turn::Effect::NoteCreate { commitment, .. } = effect {
                        s.note_tree_append_commitment(&commitment.0);
                        let _ = s.store.store_note_commitment(commitment);
                    }
                }
            }

            // Append receipt to cipherclerk. Strict mode: divergence between
            // the local executor and the cipherclerk's chain is a serious
            // bug (the receipt came from our own executor), so we expect.
            s.cclerk
                .append_receipt(receipt.clone())
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            // ── Lift TurnReceipt → FederationReceipt (audit F7) ──────────
            // We carry the committed turn into a federation-shaped receipt
            // by hashing its post-state into the body and signing with the
            // local validator's Ed25519 key. In solo mode the local node is
            // the entire committee so a single signature suffices; in full
            // mode this becomes one vote of many that an aggregator collects.
            let fed_receipt_opt =
                build_federation_receipt(&s, &signed_turn.turn, &receipt, new_height, block_id);

            // ── Write a fresh AttestedRoot anchored to (block_id, round)
            // (audit F3 / gap D). The merkle_root is the BLAKE3 of the
            // ledger's canonical bytes — fine as a soundness commitment for
            // now; the Poseidon2 note-tree root is threaded as a BabyBear
            // serialized to bytes (best-effort; full STARK root binding is a
            // separate workitem).
            let merkle_root = canonical_ledger_root(&s.ledger);
            let note_tree_root: Option<[u8; 32]> = None;
            let timestamp_for_root = now;
            let federation_keys = s.known_federation_keys.clone();
            let federation_threshold = s.decryption_threshold.max(1);
            let signing_key_bytes = s.cclerk.gossip_signing_key().to_bytes();

            // v4 (#80): bind the receipt stream this attestation covers.
            // Each finalized blocklace block carries exactly one turn (the
            // signed_turn we just executed), so the receipt stream for this
            // attestation period is the singleton `[receipt.receipt_hash()]`.
            // Two federations with the same `merkle_root` but a different
            // turn would produce a different `receipt_stream_root`, making
            // the "WitnessedReceipt chain IS the persistence layer" property
            // enforceable at signature-check time.
            let receipt_stream_root = Some(dregg_types::merkle_root_of_receipt_hashes(&[
                receipt.receipt_hash()
            ]));

            // Build the attested root struct, then sign its canonical message.
            let mut attested = dregg_types::AttestedRoot {
                merkle_root,
                note_tree_root,
                nullifier_set_root: None,
                height: new_height,
                timestamp: timestamp_for_root,
                blocklace_block_id: Some(block_id.0),
                finality_round,
                quorum_signatures: Vec::new(),
                threshold_qc: None,
                threshold: federation_threshold,
                federation_id: dregg_types::FederationId(s.federation_id),
                receipt_stream_root,
            };
            let signing_msg = attested.signing_message();
            let local_pk = s.cclerk.public_key().clone();
            let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
            let sig = dregg_types::sign(&signing_key, &signing_msg);
            // In solo / single-validator mode our signature alone meets the
            // threshold (threshold defaults to 1 if the genesis-declared
            // value is zero). In full mode this is one signature; peer
            // aggregation occurs in a follow-up commit.
            if federation_keys.is_empty() || federation_keys.contains(&local_pk) {
                attested.quorum_signatures.push((local_pk, sig));
            }

            // Persist the attested root so the next turn's executor sees
            // its height (closes audit gap D — was never written).
            let stored = dregg_persist::StoredAttestedRoot {
                merkle_root: attested.merkle_root,
                note_tree_root: attested.note_tree_root,
                nullifier_set_root: attested.nullifier_set_root,
                height: attested.height,
                timestamp: attested.timestamp,
                blocklace_block_id: attested.blocklace_block_id,
                finality_round: attested.finality_round,
                quorum_signatures: attested.quorum_signatures.clone(),
                threshold_qc: attested.threshold_qc.clone(),
                threshold: attested.threshold,
                federation_id: attested.federation_id,
                receipt_stream_root: attested.receipt_stream_root,
            };
            if let Err(e) = s.store.store_attested_root(&stored) {
                warn!(error = %e, height = new_height, "failed to persist attested root");
            }

            // Emit root event to WebSocket subscribers.
            state.emit(NodeEvent::Root {
                height: new_height,
                merkle_root: dregg_types::hex_encode(&stored.merkle_root),
                timestamp: stored.timestamp,
            });

            // Emit revocation events for any RevokeCapability effects.
            for effect in signed_turn.turn.call_forest.total_effects() {
                if let dregg_turn::Effect::RevokeCapability { cell, .. } = effect {
                    state.emit(NodeEvent::Revocation {
                        token_id: dregg_types::hex_encode(&cell.0),
                    });
                }
            }

            drop(s);

            for evidence in invalid_bundle_evidence {
                warn!(
                    block_id = %evidence.block_id,
                    reason = %evidence.reason,
                    "invalid blocklace turn bundle artifacts"
                );
                state.emit(NodeEvent::InvalidBlocklaceBundle {
                    block_id: evidence.block_id.to_string(),
                    reason: evidence.reason,
                });
            }

            // Emit to WS subscribers.
            state.emit(NodeEvent::Receipt {
                hash: receipt_hash_hex,
            });

            if let Some(fed_receipt) = fed_receipt_opt {
                tracing::debug!(
                    federation_id = %dregg_types::hex_encode(&fed_receipt.federation_id),
                    height = fed_receipt.body.block_height,
                    "federation receipt produced",
                );
            }

            info!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                height = new_height,
                round = ?finality_round,
                "finalized turn executed (blocklace consensus)"
            );
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                reason = %reason,
                "finalized turn rejected"
            );
        }
        dregg_turn::TurnResult::Expired => {
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn expired"
            );
        }
        dregg_turn::TurnResult::Pending => {
            debug!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn pending"
            );
        }
    }
}

fn materialize_blocklace_artifacts(
    state: &mut crate::state::NodeStateInner,
    block_id: BlockId,
    local_receipt: &dregg_turn::TurnReceipt,
    bundle: &TurnArtifactBundle,
) -> Vec<InvalidBlocklaceBundleEvidence> {
    let local_receipt_hash = local_receipt.receipt_hash();
    let mut evidence = Vec::new();

    if let Some(receipt_bytes) = &bundle.receipt {
        match decode_blocklace_artifact::<dregg_turn::TurnReceipt>(receipt_bytes) {
            Ok(bundle_receipt) => {
                if bundle_receipt.turn_hash != local_receipt.turn_hash {
                    evidence.push(invalid_bundle(block_id, "receipt turn_hash mismatch"));
                    return evidence;
                }
                if bundle_receipt.previous_receipt_hash != local_receipt.previous_receipt_hash {
                    evidence.push(invalid_bundle(
                        block_id,
                        "receipt previous_receipt_hash mismatch",
                    ));
                    return evidence;
                }
                if bundle_receipt.receipt_hash() != local_receipt_hash {
                    evidence.push(invalid_bundle(
                        block_id,
                        "receipt hash does not match local execution",
                    ));
                    return evidence;
                }
            }
            Err(e) => {
                evidence.push(invalid_bundle(
                    block_id,
                    format!("malformed bundled receipt: {e}"),
                ));
                return evidence;
            }
        }
    }

    for (idx, witnessed_bytes) in bundle.witnessed_receipts.iter().enumerate() {
        match decode_blocklace_witnessed_receipt_artifact(witnessed_bytes) {
            Ok(witnessed) if witnessed.receipt.receipt_hash() == local_receipt_hash => {
                match witnessed.require_scope2_witness() {
                    Ok(()) => state.push_witnessed_receipt(local_receipt_hash, witnessed),
                    Err(e) => evidence.push(invalid_bundle(
                        block_id,
                        format!("witnessed_receipts[{idx}] missing scope-2 material: {e}"),
                    )),
                }
            }
            Ok(witnessed) => {
                let reason = if witnessed.receipt.turn_hash != local_receipt.turn_hash {
                    format!("witnessed_receipts[{idx}] receipt turn_hash mismatch")
                } else if witnessed.receipt.previous_receipt_hash
                    != local_receipt.previous_receipt_hash
                {
                    format!("witnessed_receipts[{idx}] receipt previous_receipt_hash mismatch")
                } else {
                    format!("witnessed_receipts[{idx}] receipt hash does not match local execution")
                };
                evidence.push(invalid_bundle(block_id, reason));
            }
            Err(e) => {
                evidence.push(invalid_bundle(
                    block_id,
                    format!("malformed witnessed_receipts[{idx}]: {e}"),
                ));
            }
        }
    }

    evidence
}

fn invalid_bundle(block_id: BlockId, reason: impl Into<String>) -> InvalidBlocklaceBundleEvidence {
    InvalidBlocklaceBundleEvidence {
        block_id,
        reason: reason.into(),
    }
}

fn decode_blocklace_artifact<T>(bytes: &[u8]) -> Result<T, String>
where
    T: for<'de> serde::Deserialize<'de>,
{
    postcard::from_bytes(bytes)
        .map_err(|e| e.to_string())
        .or_else(|_| serde_json::from_slice(bytes).map_err(|e| e.to_string()))
}

fn decode_blocklace_witnessed_receipt_artifact(
    bytes: &[u8],
) -> Result<dregg_turn::WitnessedReceipt, String> {
    dregg_turn::WitnessedReceipt::from_artifact_bytes(bytes).or_else(|dwr1_err| {
        decode_blocklace_artifact::<dregg_turn::WitnessedReceipt>(bytes).map_err(|legacy_err| {
            format!("DWR1 decode failed ({dwr1_err}); legacy decode failed ({legacy_err})")
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_types::CellId;

    fn sample_receipt(tag: u8) -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: [tag; 32],
            forest_hash: [tag.wrapping_add(1); 32],
            pre_state_hash: [tag.wrapping_add(2); 32],
            post_state_hash: [tag.wrapping_add(3); 32],
            timestamp: 42,
            effects_hash: [tag.wrapping_add(4); 32],
            computrons_used: 7,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId([tag.wrapping_add(5); 32]),
            federation_id: [tag.wrapping_add(6); 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: dregg_turn::Finality::Final,
            was_encrypted: false,
            was_burn: false,
        }
    }

    fn scope2_witnessed(receipt: dregg_turn::TurnReceipt) -> dregg_turn::WitnessedReceipt {
        let trace = vec![vec![BabyBear::new_canonical(1)]];
        dregg_turn::WitnessedReceipt::from_components(
            receipt,
            b"proof".to_vec(),
            vec![1, 2, 3],
            Some(&trace),
        )
    }

    #[tokio::test]
    async fn blocklace_turn_bundle_materializes_matching_witnesses_only() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let receipt = sample_receipt(9);
        let receipt_hash = receipt.receipt_hash();
        let witnessed = scope2_witnessed(receipt.clone());
        let mismatched_witnessed = scope2_witnessed(sample_receipt(10));
        let bundle = TurnArtifactBundle {
            signed_turn: b"signed-turn".to_vec(),
            receipt: Some(serde_json::to_vec(&receipt).expect("receipt encodes")),
            witnessed_receipts: vec![
                witnessed.to_artifact_bytes().expect("DWR1 witness encodes"),
                mismatched_witnessed
                    .to_artifact_bytes()
                    .expect("DWR1 witness encodes"),
            ],
        };
        let decoded_receipt: dregg_turn::TurnReceipt =
            decode_blocklace_artifact(bundle.receipt.as_ref().unwrap()).expect("receipt decodes");
        assert_eq!(decoded_receipt.receipt_hash(), receipt_hash);
        let decoded_witnessed: dregg_turn::WitnessedReceipt =
            decode_blocklace_witnessed_receipt_artifact(&bundle.witnessed_receipts[0])
                .expect("witness decodes");
        assert_eq!(decoded_witnessed.receipt.receipt_hash(), receipt_hash);

        let mut guard = state.write().await;
        let evidence =
            materialize_blocklace_artifacts(&mut guard, BlockId([7u8; 32]), &receipt, &bundle);

        assert_eq!(guard.witnessed_receipt_count(&receipt_hash), 1);
        assert_eq!(evidence.len(), 1);
        assert!(
            evidence[0].reason.contains("receipt turn_hash mismatch"),
            "unexpected evidence: {evidence:?}"
        );
        let stored = guard
            .witnessed_receipts
            .get(&receipt_hash)
            .expect("matching witness is materialized");
        assert_eq!(stored[0].witness_hash, witnessed.witness_hash);
    }

    #[tokio::test]
    async fn blocklace_turn_bundle_reports_invalid_artifacts() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let receipt = sample_receipt(20);
        let mut wrong_previous = receipt.clone();
        wrong_previous.previous_receipt_hash = Some([99u8; 32]);
        let no_scope2 = dregg_turn::WitnessedReceipt::from_components(
            receipt.clone(),
            b"proof".to_vec(),
            vec![1, 2, 3],
            None,
        );
        let bundle = TurnArtifactBundle {
            signed_turn: b"signed-turn".to_vec(),
            receipt: Some(serde_json::to_vec(&wrong_previous).expect("receipt encodes")),
            witnessed_receipts: vec![
                b"not-a-witness".to_vec(),
                no_scope2.to_artifact_bytes().expect("DWR1 witness encodes"),
            ],
        };

        let mut guard = state.write().await;
        let evidence =
            materialize_blocklace_artifacts(&mut guard, BlockId([8u8; 32]), &receipt, &bundle);

        assert!(guard.witnessed_receipts.is_empty());
        assert_eq!(evidence.len(), 1);
        assert!(
            evidence[0]
                .reason
                .contains("receipt previous_receipt_hash mismatch"),
            "unexpected evidence: {evidence:?}"
        );

        let bundle = TurnArtifactBundle {
            signed_turn: b"signed-turn".to_vec(),
            receipt: None,
            witnessed_receipts: vec![
                b"not-a-witness".to_vec(),
                no_scope2.to_artifact_bytes().expect("DWR1 witness encodes"),
            ],
        };
        let evidence =
            materialize_blocklace_artifacts(&mut guard, BlockId([9u8; 32]), &receipt, &bundle);

        assert!(guard.witnessed_receipts.is_empty());
        assert_eq!(evidence.len(), 2);
        assert!(
            evidence
                .iter()
                .any(|e| e.reason.contains("malformed witnessed_receipts[0]")),
            "unexpected evidence: {evidence:?}"
        );
        assert!(
            evidence
                .iter()
                .any(|e| e.reason.contains("missing scope-2 material")),
            "unexpected evidence: {evidence:?}"
        );
    }

    #[test]
    fn blocklace_bundle_payload_preserves_signed_turn_for_ordering() {
        let bundle = TurnArtifactBundle {
            signed_turn: b"signed-turn".to_vec(),
            receipt: None,
            witnessed_receipts: Vec::new(),
        };
        let key = ed25519_dalek::SigningKey::from_bytes(&[3u8; 32]);
        let mut finality_lace = Blocklace::new_simple(key);
        let block = finality_lace.add_block(Payload::TurnBundle(bundle.clone()));

        let (ordering_lace, id_map) = build_ordering_blocklace(&finality_lace);
        let ordering_id = id_map
            .iter()
            .find_map(|(ordering, finality)| (*finality == block.id()).then_some(*ordering))
            .expect("bundle block is mapped into ordering lace");
        let ordering_block = ordering_lace
            .get(&ordering_id)
            .expect("ordering block exists");

        assert_eq!(ordering_block.payload, bundle.signed_turn);
    }
}

// ─── Periodic Ledger Checkpointing ─────────────────────────────────────────

/// Checkpoint interval for ledger persistence (in finalized blocks).
const LEDGER_CHECKPOINT_INTERVAL: u64 = 100;

/// Periodically checkpoint the ledger to persistent storage.
///
/// Checks the current block height against the last checkpoint height. If the
/// difference exceeds `LEDGER_CHECKPOINT_INTERVAL`, writes a new checkpoint.
/// Also prunes old checkpoints to bound storage (keeps last 3).
async fn maybe_checkpoint_ledger(state: &NodeState) {
    let s = state.read().await;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let last_checkpoint_height = s.store.latest_ledger_checkpoint_height().unwrap_or(0);

    if current_height.saturating_sub(last_checkpoint_height) < LEDGER_CHECKPOINT_INTERVAL {
        return;
    }

    match s.store.checkpoint_ledger(&s.ledger, current_height) {
        Ok(()) => {
            info!(
                height = current_height,
                cells = s.ledger.len(),
                "periodic ledger checkpoint saved"
            );
            // Prune old checkpoints: keep only the last 3.
            if let Err(e) = s.store.prune_ledger_checkpoints(3) {
                warn!(error = %e, "failed to prune old ledger checkpoints");
            }
        }
        Err(e) => {
            warn!(error = %e, "failed to save periodic ledger checkpoint");
        }
    }
}

// ─── Blocklace State Persistence ────────────────────────────────────────────

/// Persist the current blocklace metadata and executed_up_to index.
///
/// Called after each batch of finalized turns is executed. This ensures that on
/// restart, the node resumes from the correct position without re-executing
/// already-processed turns.
async fn persist_blocklace_state(state: &NodeState, handle: &BlocklaceHandle) {
    let executed_up_to = {
        let idx = handle.executed_up_to.read().await;
        *idx
    };

    // Gather metadata from the blocklace.
    let meta = {
        let lace = handle.lace.read().await;
        BlocklaceMeta {
            tips: lace.tips().clone(),
            equivocators: lace.equivocators().iter().copied().collect(),
            ordered_block_ids: lace.finality.ordering.ordered.clone(),
            attested_block_ids: lace.finality.ordering.attested.iter().copied().collect(),
        }
    };

    let s = state.read().await;
    if let Err(e) = s.store.persist_executed_up_to(executed_up_to as u64) {
        warn!(error = %e, "failed to persist executed_up_to index");
    }
    if let Err(e) = s.store.persist_blocklace_meta(&meta) {
        warn!(error = %e, "failed to persist blocklace metadata");
    }
}

// ─── Blocklace Checkpoint Production & Serving ──────────────────────────────

/// Produce a full blocklace checkpoint (DAG state + ledger snapshot) at the
/// current finalized height, store it locally, prune old ones, and announce
/// availability via gossip.
///
/// Called from the finality executor after each batch of finalized turns.
async fn maybe_produce_checkpoint(state: &NodeState, handle: &BlocklaceHandle) {
    let executed_count = {
        let e = handle.executed_up_to.read().await;
        *e as u64
    };

    // Only produce checkpoints at interval boundaries. (uses the configured value for this run)
    if executed_count == 0 || executed_count % handle.checkpoint_interval != 0 {
        return;
    }

    let finalized_height = executed_count;

    info!(height = finalized_height, "producing blocklace checkpoint");

    // Snapshot the blocklace DAG state.
    let blocklace_checkpoint = {
        let lace = handle.lace.read().await;
        lace.checkpoint()
    };

    // Serialize the blocklace checkpoint (postcard format).
    let blocklace_data = match postcard::to_stdvec(&blocklace_checkpoint) {
        Ok(data) => data,
        Err(e) => {
            warn!(error = %e, "failed to serialize blocklace checkpoint");
            return;
        }
    };

    // Snapshot the ledger state (cell contents).
    let ledger_data = {
        let s = state.read().await;
        let cells: Vec<(&dregg_cell::CellId, &dregg_cell::Cell)> = s.ledger.iter().collect();
        match postcard::to_stdvec(&cells) {
            Ok(data) => data,
            Err(e) => {
                warn!(error = %e, "failed to serialize ledger snapshot for checkpoint");
                return;
            }
        }
    };

    // Compute content hashes before compression (used for verification).
    let blocklace_hash = *blake3::hash(&blocklace_data).as_bytes();
    let ledger_hash = *blake3::hash(&ledger_data).as_bytes();

    // Apply compression wrapper (magic byte prefix for future zstd support).
    let blocklace_stored = compress_checkpoint_data(&blocklace_data);
    let ledger_stored = compress_checkpoint_data(&ledger_data);

    // Store the checkpoint locally.
    {
        let s = state.read().await;
        let checkpoint_key = format!("blocklace_checkpoint_{}", finalized_height);
        let ledger_key = format!("blocklace_ledger_snapshot_{}", finalized_height);
        if let Err(e) = s.store.set_config(&checkpoint_key, &blocklace_stored) {
            warn!(error = %e, height = finalized_height, "failed to store blocklace checkpoint");
            return;
        }
        if let Err(e) = s.store.set_config(&ledger_key, &ledger_stored) {
            warn!(error = %e, height = finalized_height, "failed to store ledger snapshot");
            return;
        }
        let height_bytes = finalized_height.to_le_bytes();
        let _ = s
            .store
            .set_config("blocklace_checkpoint_latest_height", &height_bytes);

        let list_key = "blocklace_checkpoint_heights";
        let mut heights: Vec<u64> = s
            .store
            .get_config(list_key)
            .ok()
            .flatten()
            .and_then(|data| postcard::from_bytes(&data).ok())
            .unwrap_or_default();
        heights.push(finalized_height);

        while heights.len() > MAX_RETAINED_CHECKPOINTS {
            let old_height = heights.remove(0);
            let old_cp_key = format!("blocklace_checkpoint_{}", old_height);
            let old_ledger_key = format!("blocklace_ledger_snapshot_{}", old_height);
            let _ = s.store.set_config(&old_cp_key, &[]);
            let _ = s.store.set_config(&old_ledger_key, &[]);
            debug!(height = old_height, "pruned old blocklace checkpoint");
        }

        if let Ok(heights_data) = postcard::to_stdvec(&heights) {
            let _ = s.store.set_config(list_key, &heights_data);
        }
    }

    info!(
        height = finalized_height,
        blocklace_bytes = blocklace_stored.len(),
        ledger_bytes = ledger_stored.len(),
        "blocklace checkpoint stored"
    );

    let announcement = BlocklaceGossipMessage::CheckpointAvailable {
        height: finalized_height,
        checkpoint_hash: blocklace_hash,
    };
    handle.broadcast_gossip_message(&announcement).await;

    debug!(
        height = finalized_height,
        blocklace_hash = %hex_encode(&blocklace_hash[..8]),
        ledger_hash = %hex_encode(&ledger_hash[..8]),
        "checkpoint announcement gossiped"
    );
}

fn compress_checkpoint_data(data: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(1 + data.len());
    result.push(0x00);
    result.extend_from_slice(data);
    result
}

pub fn decompress_checkpoint_data(data: &[u8]) -> Option<Vec<u8>> {
    if data.is_empty() {
        return None;
    }
    match data[0] {
        0x00 => Some(data[1..].to_vec()),
        _ => None,
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BlocklaceCheckpointResponse {
    pub height: u64,
    pub blocklace: String,
    pub ledger: String,
    pub blocklace_hash: String,
    pub ledger_hash: String,
}

#[derive(Clone, Debug, serde::Deserialize)]
pub struct BlocklaceCheckpointQuery {
    pub height: Option<u64>,
}

pub fn load_blocklace_checkpoint(
    store: &dregg_persist::PersistentStore,
    height: u64,
) -> Option<BlocklaceCheckpointResponse> {
    let checkpoint_key = format!("blocklace_checkpoint_{}", height);
    let ledger_key = format!("blocklace_ledger_snapshot_{}", height);

    let blocklace_data = store.get_config(&checkpoint_key).ok()??;
    let ledger_data = store.get_config(&ledger_key).ok()??;

    if blocklace_data.is_empty() || ledger_data.is_empty() {
        return None;
    }

    let blocklace_raw = decompress_checkpoint_data(&blocklace_data)?;
    let ledger_raw = decompress_checkpoint_data(&ledger_data)?;
    let blocklace_hash = *blake3::hash(&blocklace_raw).as_bytes();
    let ledger_hash = *blake3::hash(&ledger_raw).as_bytes();

    Some(BlocklaceCheckpointResponse {
        height,
        blocklace: hex_encode(&blocklace_data),
        ledger: hex_encode(&ledger_data),
        blocklace_hash: hex_encode(&blocklace_hash),
        ledger_hash: hex_encode(&ledger_hash),
    })
}

pub fn latest_blocklace_checkpoint_height(store: &dregg_persist::PersistentStore) -> u64 {
    store
        .get_config("blocklace_checkpoint_latest_height")
        .ok()
        .flatten()
        .and_then(|data| {
            if data.len() == 8 {
                Some(u64::from_le_bytes(data.try_into().ok()?))
            } else {
                None
            }
        })
        .unwrap_or(0)
}

#[allow(dead_code)]
pub async fn bootstrap_from_checkpoint(
    peer_url: &str,
    self_key: ed25519_dalek::SigningKey,
    quorum_threshold: usize,
) -> Option<(
    dregg_blocklace::finality::Blocklace,
    Vec<(dregg_cell::CellId, dregg_cell::Cell)>,
)> {
    use dregg_blocklace::finality::CheckpointData;

    info!(peer = %peer_url, "attempting checkpoint-based bootstrap");

    let url = format!("{}/api/blocklace/checkpoint", peer_url);
    let resp_bytes = fetch_checkpoint_http(&url).await?;
    let checkpoint_resp: BlocklaceCheckpointResponse = serde_json::from_slice(&resp_bytes).ok()?;

    let blocklace_compressed = hex_decode_var(&checkpoint_resp.blocklace)?;
    let blocklace_bytes = decompress_checkpoint_data(&blocklace_compressed)?;

    let actual_hash = *blake3::hash(&blocklace_bytes).as_bytes();
    let expected_hash = hex_decode_var(&checkpoint_resp.blocklace_hash)?;
    if actual_hash.as_slice() != expected_hash.as_slice() {
        warn!(peer = %peer_url, "blocklace checkpoint hash mismatch");
        return None;
    }

    let checkpoint_data: CheckpointData = match postcard::from_bytes(&blocklace_bytes) {
        Ok(data) => data,
        Err(e) => {
            warn!(peer = %peer_url, error = %e, "failed to deserialize blocklace checkpoint");
            return None;
        }
    };

    let blocklace = match dregg_blocklace::finality::Blocklace::from_checkpoint(
        &checkpoint_data,
        self_key,
        quorum_threshold,
    ) {
        Ok(lace) => lace,
        Err(e) => {
            warn!(peer = %peer_url, error = %e, "failed to restore blocklace from checkpoint");
            return None;
        }
    };

    let ledger_compressed = hex_decode_var(&checkpoint_resp.ledger)?;
    let ledger_bytes = decompress_checkpoint_data(&ledger_compressed)?;

    let actual_ledger_hash = *blake3::hash(&ledger_bytes).as_bytes();
    let expected_ledger_hash = hex_decode_var(&checkpoint_resp.ledger_hash)?;
    if actual_ledger_hash.as_slice() != expected_ledger_hash.as_slice() {
        warn!(peer = %peer_url, "ledger snapshot hash mismatch");
        return None;
    }

    let cells: Vec<(dregg_cell::CellId, dregg_cell::Cell)> =
        match postcard::from_bytes(&ledger_bytes) {
            Ok(cells) => cells,
            Err(e) => {
                warn!(peer = %peer_url, error = %e, "failed to deserialize ledger snapshot");
                return None;
            }
        };

    info!(
        peer = %peer_url,
        height = checkpoint_resp.height,
        blocks = checkpoint_data.blocks.len(),
        cells = cells.len(),
        "checkpoint bootstrap complete"
    );

    Some((blocklace, cells))
}

async fn fetch_checkpoint_http(url: &str) -> Option<Vec<u8>> {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpStream;

    let rest = url.strip_prefix("http://")?;
    let (authority, path) = rest.split_once('/').unwrap_or((rest, ""));
    let path = format!("/{}", path);

    let stream = TcpStream::connect(authority).await.ok()?;
    let (mut reader, mut writer) = tokio::io::split(stream);

    let host = authority.split(':').next().unwrap_or(authority);
    let request = format!(
        "GET {} HTTP/1.1\r\nHost: {}\r\nConnection: close\r\nAccept: application/json\r\n\r\n",
        path, host
    );
    writer.write_all(request.as_bytes()).await.ok()?;

    let mut response = Vec::new();
    reader.read_to_end(&mut response).await.ok()?;

    let header_end = response.windows(4).position(|w| w == b"\r\n\r\n")?;
    let body = &response[header_end + 4..];

    let first_line_end = response.iter().position(|&b| b == b'\r')?;
    let first_line = std::str::from_utf8(&response[..first_line_end]).ok()?;
    if !first_line.contains("200") {
        warn!(status_line = %first_line, "checkpoint fetch failed");
        return None;
    }

    Some(body.to_vec())
}

fn hex_decode_var(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = hex_nibble(chunk[0])?;
        let low = hex_nibble(chunk[1])?;
        out.push((high << 4) | low);
    }
    Some(out)
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ─── Membership Vote Processing ─────────────────────────────────────────────

/// Execute a finalized membership action (join proposal, leave proposal, or vote).
///
/// When a block with a `MembershipVote` payload reaches finality (appears in tau
/// output), we process it against the ConstitutionManager:
/// - Join/Leave proposals are registered as new proposals
/// - Approve/Reject actions are recorded as votes
/// - If a proposal reaches threshold, the constitution is amended
///
/// In devnet mode (`auto_approve_joins`), existing nodes automatically cast
/// approval votes for incoming Join proposals.
async fn execute_finalized_membership(
    state: &NodeState,
    handle: &BlocklaceHandle,
    block_id: BlockId,
    creator: [u8; 32],
    action: &MembershipAction,
) {
    match action {
        MembershipAction::Join { node_id } => {
            // A node is proposing to join the federation.
            let proposal = MembershipProposal::Join {
                node_key: *node_id,
                justification: vec![],
            };

            let mut constitution = handle.constitution.write().await;
            constitution.submit_proposal(block_id, proposal);

            // The proposer implicitly votes for their own join.
            let self_vote = MembershipVote {
                proposal_block: block_id,
                approve: true,
            };
            let passed = constitution.submit_vote(&self_vote, creator);
            drop(constitution);

            let creator_hex: String = creator[..4].iter().map(|b| format!("{b:02x}")).collect();
            info!(
                block_id = %block_id,
                proposer = %creator_hex,
                "membership join proposal registered"
            );

            // In devnet mode, auto-approve join proposals from other nodes.
            if handle.auto_approve_joins && *node_id != handle.self_key {
                // Check that we are a current participant (only participants can vote).
                let constitution = handle.constitution.read().await;
                let we_are_participant = constitution.current.is_participant(&handle.self_key);
                drop(constitution);

                if we_are_participant {
                    handle.cast_approval_vote(state, block_id).await;
                    info!(
                        proposal = %block_id,
                        "auto-approved join proposal (devnet mode)"
                    );
                }
            }

            // Check if the proposal already passed (e.g., n=1 solo mode).
            if let Some(proposal_block) = passed {
                apply_passed_proposal(handle, &proposal_block).await;
            }
        }

        MembershipAction::Leave { node_id } => {
            // A proposal to remove a node from the federation.
            let proposal = MembershipProposal::Leave {
                node_key: *node_id,
                reason: LeaveReason::Voluntary,
            };

            let mut constitution = handle.constitution.write().await;
            constitution.submit_proposal(block_id, proposal);

            // The proposer implicitly votes for the leave.
            let self_vote = MembershipVote {
                proposal_block: block_id,
                approve: true,
            };
            let passed = constitution.submit_vote(&self_vote, creator);
            drop(constitution);

            let node_hex: String = node_id[..4].iter().map(|b| format!("{b:02x}")).collect();
            info!(
                block_id = %block_id,
                leaving_node = %node_hex,
                "membership leave proposal registered"
            );

            if let Some(proposal_block) = passed {
                apply_passed_proposal(handle, &proposal_block).await;
            }
        }

        MembershipAction::Approve { proposal_block } => {
            // A participant is voting to approve an existing proposal.
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: true,
            };

            let mut constitution = handle.constitution.write().await;
            let passed = constitution.submit_vote(&vote, creator);
            drop(constitution);

            let creator_hex: String = creator[..4].iter().map(|b| format!("{b:02x}")).collect();
            debug!(
                block_id = %block_id,
                voter = %creator_hex,
                proposal = %proposal_block,
                "membership approval vote recorded"
            );

            if let Some(proposal_block) = passed {
                apply_passed_proposal(handle, &proposal_block).await;
            }
        }

        MembershipAction::Reject { proposal_block } => {
            // A participant is voting to reject an existing proposal.
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: false,
            };

            let mut constitution = handle.constitution.write().await;
            constitution.submit_vote(&vote, creator);
            drop(constitution);

            let creator_hex: String = creator[..4].iter().map(|b| format!("{b:02x}")).collect();
            debug!(
                block_id = %block_id,
                voter = %creator_hex,
                proposal = %proposal_block,
                "membership rejection vote recorded"
            );
        }
    }
}

/// Apply a membership proposal that has reached threshold.
///
/// Amends the constitution and logs the change. The new participant list takes
/// effect at the NEXT wave boundary (the current wave's ordering uses the old set).
async fn apply_passed_proposal(handle: &BlocklaceHandle, proposal_block: &BlockId) {
    let mut constitution = handle.constitution.write().await;
    if constitution.apply_if_passed(proposal_block) {
        let new_count = constitution.current.participant_count();
        let new_version = constitution.version();
        let new_threshold = constitution.threshold();
        info!(
            proposal_block = %proposal_block,
            new_participant_count = new_count,
            new_threshold = new_threshold,
            constitution_version = new_version,
            "constitution amended: membership change applied"
        );
    }
}

/// Advance the constitution's wave counter and handle timeout-based auto-leave.
///
/// Called after each batch of finalized blocks is processed. Checks if any
/// participants have been silent for too long and proposes their removal.
///
/// Timeout-based leave ensures the federation can continue making progress
/// even if participants go offline permanently. The timed-out participant can
/// rejoin later by submitting a new Join proposal.
async fn advance_constitution_wave(state: &NodeState, handle: &BlocklaceHandle) {
    let mut constitution = handle.constitution.write().await;
    let current_wave = constitution.current_wave + 1;
    let timeout_proposals = constitution.advance_wave(current_wave);
    drop(constitution);

    if timeout_proposals.is_empty() {
        return;
    }

    // For each timed-out participant, create a Leave proposal block.
    for proposal in &timeout_proposals {
        if let MembershipProposal::Leave { node_key, reason } = proposal {
            let node_hex: String = node_key[..4].iter().map(|b| format!("{b:02x}")).collect();
            let (last_wave, detected_wave) = match reason {
                LeaveReason::Timeout {
                    last_active_wave,
                    detected_at_wave,
                } => (*last_active_wave, *detected_at_wave),
                _ => (0, current_wave),
            };

            info!(
                node = %node_hex,
                last_active_wave = last_wave,
                detected_at_wave = detected_wave,
                "proposing auto-leave for timed-out participant"
            );

            // Create the leave proposal block.
            let block = {
                let mut lace = handle.lace.write().await;
                lace.add_block(Payload::MembershipVote {
                    action: MembershipAction::Leave { node_id: *node_key },
                })
            };

            // Persist the leave proposal block.
            BlocklaceHandle::persist_block_to_store(state, &block).await;

            // Register the proposal in the constitution manager.
            let mut constitution = handle.constitution.write().await;
            constitution.submit_proposal(block.id(), proposal.clone());
            // Self-vote for the timeout leave.
            let vote = MembershipVote {
                proposal_block: block.id(),
                approve: true,
            };
            let passed = constitution.submit_vote(&vote, handle.self_key);
            drop(constitution);

            // Disseminate the proposal.
            handle.push_new_blocks().await;

            // If we're the only participant (solo mode), it passes immediately.
            if let Some(proposal_block) = passed {
                apply_passed_proposal(handle, &proposal_block).await;
            }
        }
    }
}

// ─── Federation Receipt + Attested Root Helpers ─────────────────────────────

/// Build a [`dregg_federation::FederationReceipt`] for a committed turn.
///
/// Closes audit finding F7 (`AUDIT-federation.md`): the production path now
/// emits a federation-shaped receipt after every successful turn execution,
/// not just from tests. The receipt body commits to the turn hash, the
/// pre/post state, the effects hash, and the block height; the QC is the
/// local validator's Ed25519 vote signature.
///
/// In **solo mode** (single validator) this single signature satisfies the
/// threshold of 1 and the receipt is fully self-contained.
///
/// In **full mode** (multi-validator BFT) this returns a partially-signed
/// receipt — one of `threshold` vote signatures the aggregator collects.
/// The aggregator runs out-of-band (see `node/src/blocklace_sync.rs::execute_finalized_turn`
/// for the per-turn vote-collection scaffold).
fn build_federation_receipt(
    state_guard: &crate::state::NodeStateInner,
    turn: &dregg_turn::Turn,
    receipt: &dregg_turn::TurnReceipt,
    block_height: u64,
    block_id: BlockId,
) -> Option<dregg_federation::FederationReceipt> {
    use dregg_federation::FederationReceiptBody;
    use dregg_federation::receipt::FederationReceipt;

    // Federation id MUST come from state (audit F1). In discovery mode we
    // skip producing a federation receipt — there is no committee to attest.
    if !state_guard.federation_configured {
        return None;
    }

    let federation_id = state_guard.federation_id;
    let committee_epoch = state_guard.committee_epoch;

    let body = FederationReceiptBody {
        turn_hash: receipt.turn_hash,
        block_height,
        block_hash: block_id.0,
        agent: receipt.agent,
        nonce: turn.nonce,
        pre_state_hash: receipt.pre_state_hash,
        post_state_hash: receipt.post_state_hash,
        effects_hash: receipt.effects_hash,
        previous_receipt_hash: receipt.previous_receipt_hash,
    };

    let body_hash = body.body_hash();
    let signing_key_bytes = state_guard.cclerk.gossip_signing_key().to_bytes();
    let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
    let sig = dregg_types::sign(&signing_key, &body_hash);
    let local_pk = state_guard.cclerk.public_key().clone();

    Some(FederationReceipt::with_vote_signatures(
        federation_id,
        committee_epoch,
        body,
        vec![(local_pk, sig)],
    ))
}

/// Compute a canonical 32-byte root over the ledger's current state.
///
/// Folds each cell's id + state-hash into a domain-separated BLAKE3 hash,
/// sorted lexicographically by cell id for determinism. This is the
/// `merkle_root` field carried in [`dregg_types::AttestedRoot`].
fn canonical_ledger_root(ledger: &dregg_cell::Ledger) -> [u8; 32] {
    let mut entries: Vec<(dregg_types::CellId, [u8; 32])> = ledger
        .iter()
        .map(|(id, cell)| {
            // Hash the cell's state via postcard serialization. Postcard is
            // canonical for our types (deterministic field order, fixed
            // encoding), so this is a stable commitment.
            let bytes = postcard::to_stdvec(&cell.state).unwrap_or_default();
            let h = *blake3::hash(&bytes).as_bytes();
            (*id, h)
        })
        .collect();
    entries.sort_by(|a, b| a.0.0.cmp(&b.0.0));
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ledger-root-v1");
    hasher.update(&(entries.len() as u64).to_le_bytes());
    for (id, h) in &entries {
        hasher.update(id.as_bytes());
        hasher.update(h);
    }
    *hasher.finalize().as_bytes()
}
