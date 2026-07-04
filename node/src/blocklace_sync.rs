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
    Block, BlockId, Blocklace, FinalityLevel, MembershipAction, Payload, TurnArtifactBundle,
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

/// How many cadence ticks a cast finalization vote is re-emitted before it is
/// dropped from the pending set (the vote-layer anti-entropy budget). Re-emission
/// runs on the FREQUENT cadence tick (default 2s), so this is ~60s of re-delivery.
/// The eager push over a lossy-but-live QUIC link drops a fraction of single
/// messages (blocks survive only because they are pushed repeatedly every tick);
/// a vote is one message, so it needs its own repeated re-delivery to reliably
/// reach a peer that needs it for quorum — and the holder cannot observe the
/// peer's quorum, so it re-emits for a generous fixed window regardless of its
/// OWN quorum. Each re-emit carries a fresh nonce so the gossip `seen`-dedup
/// never collapses it. Bounded + self-draining: the set empties after the window.
const VOTE_REEMIT_SWEEPS: u32 = 30;

/// A strictly-monotonic per-process counter stamped into each `Frontier` message
/// so repeated frontiers are byte-unique and never collapse under the gossip
/// layer's hash-dedup (see `BlocklaceGossipMessage::Frontier`).
fn frontier_nonce() -> u64 {
    static FRONTIER_NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    FRONTIER_NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

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
    ///
    /// `nonce` is a per-send liveness counter that makes every frontier message
    /// BYTE-UNIQUE. A frontier is a catch-up PING, not content to deduplicate:
    /// without the nonce, a node STALLED at a fixed tip-set (e.g. waiting for the
    /// last missing block of its current round under `supermajority == n`) re-emits
    /// an IDENTICAL frontier every tick, which the gossip layer's hash-dedup drops
    /// after the first — so the peer's `handle_frontier` never re-fires and the
    /// missing block is never re-pushed (a permanent bootstrap deadlock). The
    /// nonce defeats that dedup so a stuck node's repeated frontier always reaches
    /// the peer and pulls the gap, every tick, until it advances.
    Frontier {
        tips: HashMap<[u8; 32], BlockId>,
        nonce: u64,
        /// Finalization votes the sender currently holds (its own + any it has
        /// collected), piggybacked onto the frontier. The Frontier is the
        /// PROVEN-bidirectional anti-entropy channel — it is sent every cadence
        /// tick and reaches both directions even when the Plumtree eager tree has
        /// pruned a peer to lazy at small N (which is exactly why the block DAG
        /// converges while a one-shot eager vote push can be dropped). Carrying
        /// votes here gives them the SAME anti-entropy guarantee blocks have:
        /// `handle_frontier` records each, so a vote dropped on the eager path is
        /// re-delivered on the next frontier and the peer crosses quorum.
        /// Defaults empty (older peers omit it).
        #[serde(default)]
        votes: Vec<crate::finalization_votes::FinalizationVote>,
    },
    /// Announce that a checkpoint is available at the given height.
    /// Peers can then request the full checkpoint data via the HTTP API.
    /// Contains just the height and content hash (not the full checkpoint data).
    CheckpointAvailable {
        height: u64,
        checkpoint_hash: [u8; 32],
    },
    /// AUTHENTICATED GOSSIP-OF-PEERS: the sender shares dialable listen addresses
    /// it has CRYPTOGRAPHICALLY VERIFIED for committee members, so a node booted
    /// with only a partial peer list (a single seed) learns the rest of the mesh
    /// transitively instead of every node having to enumerate every peer.
    ///
    /// Each entry is `(committee_public_key, listen_addr)`. The whole gossip
    /// envelope carrying this message is already Ed25519-signed by the sender's
    /// federation key (so an unauthenticated wire peer cannot inject it at all),
    /// AND each individual address is one the sender verified by dialing that
    /// identity and validating its signature ([`GossipNetwork::verified_peer_bindings`]).
    ///
    /// THE TRUST ANCHOR IS THE COMMITTEE KEY SET, NOT THE WIRE SENDER: the
    /// receiver ([`handle_peer_addrs`]) accepts an address ONLY when
    /// `committee_public_key` is one of its OWN `known_federation_keys` — a member
    /// it already trusts from genesis. A claimed address for a non-committee key
    /// (a stranger an introducer tries to smuggle in) is rejected outright. So
    /// discovery learns ADDRESSES for already-trusted identities; it never admits
    /// new identities.
    PeerAddrs(Vec<([u8; 32], SocketAddr)>),
    /// A signed QUORUM FINALIZATION VOTE: the emitting member asserts it has
    /// locally finalized `vote.block_id` to `vote.level`. Carried ON the
    /// blocklace topic (the proven-bidirectional dissemination channel) rather
    /// than a separate gossip topic: a vote is a small consensus-agreement
    /// message and rides the exact path blocks already converge over. The
    /// receiver verifies + collects distinct signers; a block becomes
    /// consensus-wide Attested at 2f+1. See [`crate::finalization_votes`].
    FinalizationVote(crate::finalization_votes::FinalizationVote),
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
    /// Identity-tracking execution cursor over the finalized order: which
    /// blocks have already been served to the executor, BY BLOCK ID — not an
    /// index. An index cursor assumes tau's finalized prefix is stable across
    /// lace growth, which `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`
    /// REFUTES (an honest catch-up block can sort mid-prefix); identity
    /// tracking executes each finalized block exactly once regardless.
    pub cursor: Arc<RwLock<crate::execution_cursor::ExecutionCursor>>,
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
    /// Causal staging area for blocks that arrived before their predecessors.
    ///
    /// The A1-fixed insert (`finality.rs::receive_block`) rejects a block whose
    /// predecessors are unknown. Rather than drop such an orphan (forcing a
    /// re-gossip), we buffer it here keyed by the predecessors it waits on; when a
    /// predecessor lands the orphan is re-applied in causal order. This is what
    /// makes catch-up over lossy/out-of-order gossip reconstruct the
    /// causally-closed finalized set. See `crate::catchup`.
    pub orphans: Arc<RwLock<crate::catchup::OrphanBuffer>>,
    /// Capped exponential backoff for re-requesting missing predecessors. The
    /// reactive `handle_push` pull always fires on a fresh gap (first miss is
    /// immediate), but the PERIODIC `catchup_tick` re-request is gated through
    /// this so a still-missing block is not hammered every sweep — the per-block
    /// re-request window doubles (capped) until the block arrives, at which point
    /// the entry is cleared. Bounds request bandwidth against a slow/withholding
    /// peer while preserving eventual re-request (liveness). See
    /// `dregg_net::peer_score::RequestBackoff`.
    pub pull_backoff: Arc<RwLock<dregg_net::peer_score::RequestBackoff<BlockId>>>,
    /// TIGHT, NON-ESCALATING backoff for the cohort-completion pull (a peer's
    /// announced FRONTIER tip we lack — see `handle_frontier`). This pull is
    /// LIVENESS-CRITICAL: the round-synchronous rule cannot advance until a node
    /// holds a supermajority of distinct creators' blocks at its round, so a single
    /// missing tip wedges the whole committee. The general `pull_backoff` escalates
    /// to a 30s cap (correct for a possibly-withholding peer on a deep history gap),
    /// but under load — where the eager push AND the pull response are both lossier —
    /// that let a missing cohort tip go un-retried for tens of seconds, stalling the
    /// chain for minutes. A committee member's current tip is neither withholding nor
    /// a deep gap, so retry it briskly (base 500ms, cap 1500ms): recovery within a
    /// couple seconds even under sustained loss, still bounded (≤ n−1 tips, ≤ one
    /// frontier/peer/tick).
    pub tip_pull_backoff: Arc<RwLock<dregg_net::peer_score::RequestBackoff<BlockId>>>,
    /// Instant of the last block WE produced (turn, ack, or heartbeat). The
    /// cadence task measures idleness against this so the low-frequency idle
    /// heartbeat fires only when the node has genuinely produced nothing for a
    /// full idle window (mutation-driven production resets it).
    pub last_produced: Arc<RwLock<std::time::Instant>>,
    /// Set when a peer's non-Ack block (turn / membership / checkpoint) lands in
    /// our lace and is consumed by the cadence task, which answers with one
    /// `Payload::Ack` block linking the current tips. This is the REACTIVE,
    /// mutation-driven half of Cordial-Miners attestation (blocks answer
    /// blocks): peers' turns accumulate our acknowledgment within one cadence
    /// check tick instead of waiting for the idle heartbeat. Naturally
    /// debounced — any number of pushes between ticks collapse into one ack.
    pub ack_pending: Arc<std::sync::atomic::AtomicBool>,
    /// Our federation Ed25519 signing key, used to sign [`FinalizationVote`]s.
    /// The same key derives `self_key`.
    ///
    /// [`FinalizationVote`]: crate::finalization_votes::FinalizationVote
    pub signing_key: ed25519_dalek::SigningKey,
    /// Collector that gates CONSENSUS-WIDE Attested finality on a quorum (2f+1)
    /// of distinct, verified committee signers. The DAG-derived `tau` order is
    /// computed per-node; this is the explicit cross-node AGREEMENT layer: a
    /// block is only consensus-attested once a supermajority of members have
    /// SIGNED that they finalized it. See [`crate::finalization_votes`].
    pub votes: Arc<RwLock<crate::finalization_votes::VoteCollector>>,
    /// Signed finalization votes WE have cast (for blocks we locally finalized),
    /// each with a remaining-broadcast budget. PIGGYBACKED onto every `Frontier`
    /// (`send_frontier`) so a vote dropped by the lossy/pruned Plumtree eager
    /// path is re-delivered on the proven-bidirectional anti-entropy channel —
    /// the same guarantee that converges the block DAG. We keep the SIGNED vote
    /// (the signature is stable; only the transport nonce changes per emit) so it
    /// can be re-broadcast without re-signing. Bounded + self-draining: the entry
    /// is dropped after [`VOTE_REEMIT_SWEEPS`] frontier rounds. Kept regardless of
    /// OUR quorum — a node that already has its own quorum must still help a
    /// lagging peer reach theirs (the holder cannot observe the peer's count).
    pub my_pending_votes:
        Arc<RwLock<HashMap<BlockId, (crate::finalization_votes::FinalizationVote, u32)>>>,
    /// Turn/membership payloads awaiting inclusion in a ROUND-DISCIPLINED block
    /// (the n>1 path). The naive `submit_turn` produced a block IMMEDIATELY,
    /// linking all current tips — which at n>1 lands the turn at `max_round+1`
    /// and degenerates the DAG into a single zig-zag CHAIN (one creator per
    /// round), so `tau` never super-ratifies. Instead, at n>1 a submitted turn is
    /// STAGED here and the round-driven cadence (`cadence_tick_round_driven`)
    /// carries it as the payload of its next round block, keeping the DAG
    /// round-synchronous so waves finalize cross-node. FIFO; drained one payload
    /// per round. (Solo n=1 bypasses this and produces the turn block directly.)
    pub pending_payloads: Arc<RwLock<std::collections::VecDeque<Payload>>>,
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
                let predecessors: Vec<String> = block
                    .predecessors
                    .iter()
                    .map(|p| hex_encode(&p.0))
                    .collect();
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
        *self.last_produced.write().await = std::time::Instant::now();

        // Heartbeats still advance ordering bookkeeping (the finality executor
        // treats Ack as a no-op for execution but the seq/tip have advanced).
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        debug!(block_id = %block_id, seq = block.seq, "produced heartbeat block");
        block_id
    }

    /// ROUND-DISCIPLINED block production (the Stage-5 finality mechanism).
    ///
    /// The Cordial-Miners ordering rule (`ordering::tau`) only super-ratifies a
    /// wave leader once a SUPERMAJORITY of DISTINCT creators have blocks at the
    /// wave's last round whose causal past cross-links the leader — i.e. the DAG
    /// must approach the ROUND-SYNCHRONOUS shape (`blocklace/tests/multi_node_convergence.rs`
    /// `build_rounds`: round-r blocks point at the round-(r−1) cohort). The naive
    /// producer (`add_block` linking ALL current tips, one block per cadence tick)
    /// does NOT build that shape: once gossip delivers a peer's block, that tip is
    /// at a strictly higher round, so each new block sits at `max+1` and the DAG
    /// degenerates into a single zig-zag CHAIN with exactly ONE creator per round
    /// — `is_super_ratified` can then never reach a supermajority of creators at
    /// any round, and `latest_height` stays 0 at n≥2 forever (the observed S5-1
    /// failure, even with full dissemination).
    ///
    /// This producer instead advances the local creator ONE round at a time, in
    /// lock-step with the committee:
    ///
    ///  * If we have authored nothing yet (`my_max_round == 0`), author a GENESIS
    ///    block (round 1, no predecessors) — the round-1 cohort seed.
    ///  * Otherwise we want to author round `my_max_round + 1`, and we may do so
    ///    ONLY once a supermajority of DISTINCT creators have blocks at our current
    ///    round `my_max_round` (`plan_round_block`). The new block links the WHOLE
    ///    round-`my_max_round` cohort as predecessors, so it lands at exactly
    ///    `my_max_round + 1`. Every honest node paces identically, so the round-r
    ///    cohort fills with a supermajority of creators and waves super-ratify.
    ///
    /// `payload` is carried by the produced block (a queued `Turn`/`TurnBundle`,
    /// else `Payload::Ack` for a heartbeat/reactive-ack). Returns the new block id,
    /// or `None` when the round cannot yet advance (we lack a supermajority of the
    /// current round — the caller leaves the work pending and retries next tick).
    pub async fn produce_round_block(
        &self,
        state: &NodeState,
        payload: Payload,
    ) -> Option<BlockId> {
        let supermajority = {
            let c = self.constitution.read().await;
            dregg_blocklace::ordering::supermajority_threshold(c.current.participant_count())
        };
        let block = {
            let mut lace = self.lace.write().await;
            let plan = plan_round_block(&lace, lace.self_creator(), supermajority);
            match plan {
                RoundPlan::Wait => return None,
                RoundPlan::Genesis => lace.add_block_with_predecessors(payload, Vec::new()),
                RoundPlan::Advance { predecessors, .. } => {
                    lace.add_block_with_predecessors(payload, predecessors)
                }
            }
        };

        let block_id = block.id();
        Self::persist_block_to_store(state, &block).await;
        *self.last_produced.write().await = std::time::Instant::now();
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        debug!(
            block_id = %block_id,
            seq = block.seq,
            npreds = block.predecessors.len(),
            "produced round-disciplined block"
        );
        Some(block_id)
    }

    async fn submit_turn_payload(
        &self,
        state: &NodeState,
        payload: Payload,
    ) -> (BlockId, FinalityLevel) {
        let n_participants = {
            let c = self.constitution.read().await;
            c.current.participant_count()
        };

        if n_participants > 1 {
            // MULTI-PARTY: stage the turn for ROUND-DISCIPLINED production. Emitting
            // the block right here (linking all current tips) would land it at
            // `max_round+1` and break the round-synchronous shape `tau` finalizes
            // over (the DAG would zig-zag into a one-creator-per-round chain that
            // never super-ratifies). The round-driven cadence
            // (`cadence_tick_round_driven`) instead carries this payload in its next
            // round block. We return the payload's CONTENT id as the receipt handle
            // (the eventual block id differs; all live callers ignore the return),
            // and `Local` finality (not yet ordered — it orders when its round
            // block is produced and a wave super-ratifies it cross-node).
            let receipt = Self::payload_receipt_id(&payload);
            self.pending_payloads.write().await.push_back(payload);
            // Nudge the cadence/executor so the staged turn is picked up promptly.
            self.finality_notify.notify_one();
            return (receipt, FinalityLevel::Local);
        }

        // SOLO (n=1): tau finalizes every block trivially in sequence, so produce
        // the turn block immediately (linking current tips) — no round discipline.
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(payload)
        };
        let block_id = block.id();

        // Persist the newly created block to the store.
        Self::persist_block_to_store(state, &block).await;
        *self.last_produced.write().await = std::time::Instant::now();

        // Notify the finality executor that new blocks are available.
        self.finality_notify.notify_one();

        // Disseminate to all peers via gossip.
        self.push_new_blocks().await;

        (block_id, FinalityLevel::Ordered)
    }

    /// A stable receipt handle for a staged payload (a `BlockId`-shaped digest of
    /// its content). Used only as the synchronous return of `submit_turn` at n>1,
    /// where the real round-block id is not yet known; the live call sites discard
    /// it, and the turn's actual finality is observed via the attested root.
    fn payload_receipt_id(payload: &Payload) -> BlockId {
        let bytes = postcard::to_stdvec(payload).unwrap_or_default();
        BlockId(*blake3::hash(&bytes).as_bytes())
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

    /// Gossip our current frontier (per-creator tips) so peers compute the delta
    /// we are missing and push it. This is the PROACTIVE half of catch-up: a node
    /// already connected to the topic that has fallen behind announces what it has,
    /// and `handle_frontier` on the peer side replies with the causally-ordered
    /// blocks we lack. Cheap (one map of tip ids) and quiescent-friendly (only sent
    /// on join, on a slow timer, or when a gap is detected).
    pub async fn send_frontier(&self) {
        let frontier_tips: HashMap<[u8; 32], BlockId> = {
            let lace = self.lace.read().await;
            let tips = lace.tips();
            // DAG structure gauges (emitted under the lace lock, so they reflect a
            // single consistent view): frontier width = number of per-creator tips;
            // depth = the maximum round across those tips.
            crate::metrics::set_blocklace_frontier(tips.len() as f64);
            let depth = tips
                .values()
                .filter_map(|t| lace.round_of(t))
                .max()
                .unwrap_or(0);
            crate::metrics::set_blocklace_depth(depth as f64);
            tips.iter().map(|(k, v)| (*k, *v)).collect()
        };
        let msg = BlocklaceGossipMessage::Frontier {
            tips: frontier_tips,
            nonce: frontier_nonce(),
            votes: self.frontier_votes().await,
        };
        self.broadcast_gossip_message(&msg).await;
    }

    /// One catch-up sweep: re-request any predecessors that buffered orphans are
    /// still waiting on, and (if we are staging orphans or were asked to) announce
    /// our frontier so peers push the rest of their lace. Returns the number of
    /// orphans still buffered after the sweep (0 ⇒ no detected gap).
    ///
    /// This is the driver that lets a node which fell behind (or whose gossip
    /// dropped intermediate blocks) make forward progress without waiting for a
    /// fresh `PeerJoined` event: the buffered-orphan roots are exactly the missing
    /// finalized predecessors, and pulling them (with their causal past) drains the
    /// buffer toward the finalized prefix.
    pub async fn catchup_tick(&self) -> usize {
        let (buffered, roots) = {
            let buf = self.orphans.read().await;
            (buf.len(), buf.unmet_roots())
        };
        // Re-request still-missing predecessors of buffered orphans.
        if !roots.is_empty() {
            // Filter out any roots that have since landed.
            let lace = self.lace.read().await;
            let still_missing: Vec<BlockId> =
                roots.into_iter().filter(|r| !lace.contains(r)).collect();
            drop(lace);
            // BACKOFF GATE: only (re-)request roots whose backoff window has
            // elapsed. A freshly-missing root requests immediately; a root that
            // keeps not arriving is requested with a doubling (capped) window so
            // we do not hammer a slow/withholding peer every sweep. Roots that
            // arrive get their backoff cleared in `handle_push`.
            let due: Vec<BlockId> = {
                let mut bo = self.pull_backoff.write().await;
                still_missing
                    .into_iter()
                    .filter(|r| bo.should_request(*r))
                    .collect()
            };
            if !due.is_empty() {
                debug!(
                    roots = due.len(),
                    buffered, "catch-up: re-requesting missing predecessors (backoff-gated)"
                );
                self.broadcast_gossip_message(&BlocklaceGossipMessage::Pull(due))
                    .await;
            }
        }
        // If we have an open gap, also announce our frontier so a peer pushes the
        // delta proactively (covers blocks lost before they ever reached our
        // orphan buffer — a pure tip-delta with peers).
        if buffered > 0 {
            self.send_frontier().await;
        }
        buffered
    }

    /// Sign and gossip a [`FinalizationVote`] for a block we have locally
    /// finalized, then record our OWN vote in the collector.
    ///
    /// This is the emit half of the quorum-agreement layer: when this node's
    /// `tau` order finalizes a turn-bearing block (it reaches `Ordered`, which
    /// subsumes local `Attested`), we broadcast a signed assertion of that fact
    /// so every other member can collect a quorum of distinct signers. Recording
    /// our own vote means a node counts toward its own quorum (a member's local
    /// finalization IS one of the 2f+1 signatures).
    ///
    /// Idempotent at the collector: a block already consensus-attested is not
    /// re-broadcast (the caller gates on the per-block already-voted set), so an
    /// n-member committee produces exactly n votes per finalized block, not a
    /// storm.
    async fn emit_finalization_vote(
        &self,
        block_id: BlockId,
        level: dregg_blocklace::finality::FinalityLevel,
    ) {
        use crate::finalization_votes::FinalizationVote;
        let vote = FinalizationVote::sign(&self.signing_key, block_id, level);

        // Record our own vote (a member's local finality is one signature toward
        // its own quorum) through the SAME funnel as a received vote, so that if
        // OUR vote is the one that crosses quorum (the peer's vote already landed
        // — a routine self-emit/gossip race at n=2) the consensus-wide Attested
        // transition still fires exactly once. See `record_finalization_vote`.
        record_finalization_vote(self, &vote).await;

        // Track this signed vote for RE-DELIVERY over a bounded budget. It is
        // piggybacked onto every `Frontier` (the proven-bidirectional anti-
        // entropy channel) and also eager-re-broadcast — so a vote dropped on
        // the lossy/pruned Plumtree eager path still reaches a peer that needs
        // it for quorum, REGARDLESS of OUR quorum.
        self.my_pending_votes
            .write()
            .await
            .insert(block_id, (vote.clone(), VOTE_REEMIT_SWEEPS));

        self.broadcast_gossip_message(&BlocklaceGossipMessage::FinalizationVote(vote))
            .await;
    }

    /// Re-broadcast every vote we have cast whose budget is non-zero,
    /// decrementing each and dropping those that hit zero. Called on each cadence
    /// tick (alongside the frontier piggyback). Belt-and-suspenders to the
    /// frontier carry: a fresh transport nonce per re-emit defeats the gossip
    /// `seen`-dedup, so a peer that missed the vote on the eager path records it
    /// here too. Bounded + self-draining.
    pub async fn reemit_pending_votes(&self) {
        let to_emit: Vec<crate::finalization_votes::FinalizationVote> = {
            let mut pending = self.my_pending_votes.write().await;
            let mut out = Vec::new();
            pending.retain(|_block_id, (vote, budget)| {
                // Fresh transport nonce so the re-emit is byte-unique.
                let mut v = vote.clone();
                v.nonce = crate::finalization_votes::fresh_nonce();
                out.push(v);
                *budget -= 1;
                *budget > 0
            });
            out
        };
        for vote in to_emit {
            self.broadcast_gossip_message(&BlocklaceGossipMessage::FinalizationVote(vote))
                .await;
        }
    }

    /// The finalization votes to piggyback onto an outgoing `Frontier` — the
    /// signed votes we currently hold for not-yet-drained blocks (a fresh
    /// transport nonce each so the carrying frontier is byte-unique). Cheap:
    /// at small N this is a handful of votes.
    async fn frontier_votes(&self) -> Vec<crate::finalization_votes::FinalizationVote> {
        let pending = self.my_pending_votes.read().await;
        pending
            .values()
            .map(|(vote, _)| {
                let mut v = vote.clone();
                v.nonce = crate::finalization_votes::fresh_nonce();
                v
            })
            .collect()
    }

    /// AUTHENTICATED GOSSIP-OF-PEERS: share the dialable committee-member
    /// addresses we have personally VERIFIED so peers booted with only a partial
    /// peer list learn the rest of the mesh transitively.
    ///
    /// The gossip layer hands back its cryptographically-verified bindings
    /// (`peer NodeId -> dialable listen address`, where the NodeId is
    /// `blake3(committee_public_key)` proven by an Ed25519-verified envelope over a
    /// link WE dialed). We map each verified `NodeId` back to its committee PUBLIC
    /// KEY using `known_federation_keys` (the genesis-trusted set) — dropping any
    /// binding whose identity is NOT a current committee member — and broadcast the
    /// surviving `(committee_pubkey, addr)` pairs. The carrying envelope is signed
    /// by our federation key, and the receiver re-checks each pubkey against ITS
    /// OWN committee set before dialing, so the trust anchor is the committee on
    /// both ends, never the wire path.
    ///
    /// Quiet when we hold no verified bindings (a brand-new solo node) — nothing
    /// to share.
    pub async fn share_peer_addrs(&self, state: &NodeState) {
        // Reverse map: gossip NodeId (blake3(pubkey)) -> committee public key.
        let id_to_pubkey: HashMap<[u8; 32], [u8; 32]> = {
            let s = state.read().await;
            s.known_federation_keys
                .iter()
                .map(|k| (*blake3::hash(k.as_bytes()).as_bytes(), k.0))
                .collect()
        };
        let bindings = self.gossip.verified_peer_bindings().await;
        let to_share: Vec<([u8; 32], SocketAddr)> = bindings
            .into_iter()
            .filter_map(|(node_id, addr)| {
                // Only share bindings whose identity is a CURRENT committee member
                // (the receiver enforces the same, but filtering here keeps the
                // message tight and never leaks a rotated-out identity).
                let pubkey = id_to_pubkey.get(&node_id)?;
                // Never advertise an un-dialable address.
                if addr.ip().is_unspecified() || addr.port() == 0 {
                    return None;
                }
                Some((*pubkey, addr))
            })
            .collect();
        if to_share.is_empty() {
            return;
        }
        debug!(
            count = to_share.len(),
            "gossip-of-peers: sharing verified committee addresses"
        );
        self.broadcast_gossip_message(&BlocklaceGossipMessage::PeerAddrs(to_share))
            .await;
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

        // Intra-committee block sync uses the DIRECT eager broadcast, NOT the
        // Dandelion++ stem. The stem hides a public transaction's ORIGIN; a
        // validator's blocklace blocks have no origin to hide (every committee
        // member is public), and the BFT ordering rule (`ordering::tau`) only
        // super-ratifies once a supermajority of creators' round-blocks have
        // cross-linked — which needs every creator's block to reach every node
        // PROMPTLY. Routing each block through one random stem relay delivers
        // blocks asymmetrically at small N (the Stage-5 dissemination gap,
        // `docs/STAGE5-CONSENSUS-DEVAC.md`); `publish_eager` reaches every
        // committee peer in one hop so the round-synchronous shape `tau`
        // finalizes over actually forms on the running node.
        if let Err(e) = self.gossip.publish_eager(&self.topic, &peer_msg).await {
            debug!(error = %e, "failed to publish blocklace message");
        }
    }

    /// Broadcast a co-turn `ProposeAtomicTurn` on the blocklace topic so every
    /// participant's funnel (`handle_blocklace_message`) lifts it into the
    /// in-process `dregg_coord` engine and votes.
    ///
    /// THE SEND WELD: this replaces the old JSON-stub `atomic_proposal` that went
    /// out as a `PublishTurn` and could not be reconstructed. The dedicated variant
    /// carries the full forest (`AtomicForest::encode_for_wire`) PLUS the
    /// coordinator's real `proposal_id` and identity, so a participant binds its
    /// vote to the id the coordinator will tally against. Published on `self.topic`
    /// (the blocklace topic) — the topic the funnel is subscribed to — via the
    /// direct eager broadcast, reaching every committee peer in one hop.
    pub async fn gossip_atomic_propose(
        &self,
        forest_hash: [u8; 32],
        proposal_id: [u8; 32],
        coordinator: [u8; 32],
        participants: Vec<[u8; 32]>,
        forest_data: Vec<u8>,
    ) {
        let peer_msg = PeerMessage::propose_atomic_turn(
            forest_hash,
            proposal_id,
            coordinator,
            participants,
            forest_data,
        );
        if let Err(e) = self.gossip.publish_eager(&self.topic, &peer_msg).await {
            warn!(error = %e, "co-turn: failed to broadcast atomic proposal");
        }
    }

    /// Return a participant's signed `VoteAtomicTurn` to the coordinator on the
    /// blocklace topic. The coordinator's funnel arm tallies it into the
    /// `Coordinator` persisted in `state::atomic_proposals` and fires the commit
    /// when the quorum agrees. Published on the same direct eager channel.
    pub async fn gossip_atomic_vote(
        &self,
        proposal_id: [u8; 32],
        forest_hash: [u8; 32],
        voter: [u8; 32],
        vote: bool,
        signature: Vec<u8>,
    ) {
        let peer_msg =
            PeerMessage::vote_atomic_turn(proposal_id, forest_hash, voter, vote, signature);
        if let Err(e) = self.gossip.publish_eager(&self.topic, &peer_msg).await {
            warn!(error = %e, "co-turn: failed to return atomic vote");
        }
    }

    /// Run the tau ordering function and return newly finalized blocks.
    ///
    /// This is the core consensus function: it computes the deterministic total
    /// order from the blocklace DAG using the Cordial Miners tau function
    /// (`dregg_blocklace::ordering::tau`), then returns any blocks that have been
    /// newly ordered since the last call.
    ///
    /// CONSENSUS PILLAR — VERIFIED MODEL.
    /// `ordering::tau` (the finalization rule this slices to feed `execute_finalized_turn`)
    /// is modeled faithfully and executably in Lean at
    /// `metatheory/Dregg2/Distributed/BlocklaceFinality.lean` (`computeRounds` /
    /// `findAllFinalLeaders` / `tauOrder` over `Lace`). That module proves the safety
    /// properties THIS path relies on — a wave anchors AT MOST ONE final leader
    /// (`finalLeaders_one_per_wave`), an equivocating leader anchors nothing
    /// (`finalLeaderAt_needs_unique_candidate`), and the order is a deterministic function of
    /// `(lace, participants, wavelength)` (`tauOrder_deterministic`) — and WIRES the computed
    /// order into the verified executor (`executeTau` folds `tauOrder` through
    /// `Exec.ConsensusExec.executeFinalized` = `recCexec`; `tau_drives_verified_run`,
    /// `tau_execution_agreement`: same lace ⇒ same executed state). The Rust↔Lean agreement on a
    /// real trace is checked by `ordering::tests::test_tau_differential_against_lean_model` (the
    /// finalized `(creator, seq)` order reproduces the Lean `tauGolden` golden vector) and
    /// `test_tau_differential_equivocator_excluded`.
    ///
    /// Returns all actionable finalized blocks (turns, membership votes, checkpoints).
    /// Ack and Data payloads are skipped as they need no consensus-level processing.
    pub async fn poll_finalized_blocks(&self) -> Vec<FinalizedBlock> {
        // SNAPSHOT the lace and RELEASE the read lock immediately. The verified-Lean
        // tau-order FFI (`VerifiedFinality::compute_order`) and the finality-gate FFI
        // (`VerifiedFinality::compute`) below are O(history) and run on EVERY finality
        // notification; holding `lace.read()` across them STARVED the block producer's
        // `lace.write()` as the chain grew — round production halted under sustained
        // load and `dag_height` froze (the live n=4 stall). Cloning is the same
        // O(history) cost as the `build_ordering_blocklace` the poll already does, and a
        // block produced after the snapshot is simply finalized on the NEXT poll
        // (finality is monotone) — so the producer advances concurrently and the chain
        // keeps climbing. The `cursor` write lock is likewise deferred (below) until
        // after the FFI so it does not block the cadence's `wave_open` read.
        let lace = {
            let guard = self.lace.read().await;
            (*guard).clone()
        };
        let constitution = self.constitution.read().await;
        let raw_participants = constitution.current.participants.clone();
        drop(constitution);

        // ── VERIFIED FEDERATION-ADMISSION GATE (F-4) ──────────────────────────────────────────────
        // Filter the participant set through the VERIFIED Lean strand-admission rule
        // (`Dregg2.Distributed.StrandAdmission.admitted`, the `@[export] dregg_strand_admit` the node
        // CALLS via `dregg_lean_ffi::verified_admits`): the constitution members are the bootstrap
        // SEEDS (the trust root, admitted by construction), so a fresh free Sybil keypair that is NOT
        // a constitutional member and has no vouch/bond standing is DROPPED before it can be a
        // leader candidate for `tau` — closing F-4 (unlimited free strands) on the live path. The
        // Lean theorem `strand_admit_eq_admitted` proves the export's verdict IS the verified
        // `admitted` predicate, so the participant set the node finalizes over is the one the
        // VERIFIED rule admits. Default ON (`DREGG_STRAND_ADMISSION_GATE`); fail-safe (the gate is
        // the identity on the constitutional members, and `admitted` falls back to its Rust sibling
        // when the Lean archive is absent).
        let participants = crate::strand_admission_gate::admitted_participants(
            &raw_participants,
            &raw_participants,
        );
        if participants.len() != raw_participants.len() {
            warn!(
                admitted = participants.len(),
                proposed = raw_participants.len(),
                "verified strand-admission gate (F-4) filtered un-admitted strands out of the \
                 finality participant set"
            );
        }

        // For solo mode (n=1): every block is immediately finalized in topological
        // order. tau() handles this correctly because with a single participant,
        // every block trivially has supermajority.
        // `ordered_from_lean` records whether the multi-party order below came from the
        // verified Lean export (the authoritative path) rather than the Rust fallback. It
        // lets us SKIP the redundant secondary finality-gate FFI in the common case (the
        // gate only ever admits the whole Lean order back) — halving the executor's
        // O(history) Lean work per poll, which is the dominant cost as the chain grows.
        let mut ordered_from_lean = false;
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
            // Multi-party: produce the finalized total order from the VERIFIED LEAN RULE.
            //
            // STRONG BAR (the node IMPLEMENTS consensus via the verified kernel, not a model+gate):
            // the AUTHORITATIVE order is `BlocklaceFinality.tauOrder` itself, computed by the
            // `@[export] dregg_tau_order` the node CALLS through
            // `crate::finality_gate::VerifiedFinality::compute_order` (FFI →
            // `dregg_lean_ffi::verified_tau_order`). The Lean theorem `tau_order_export_eq` proves the
            // export's output decodes back to `tauOrder` EXACTLY (order-faithful), so the order the
            // node finalizes over IS the verified rule's, by construction — not a Rust order the Lean
            // model merely vetoes.
            //
            // DIFFERENTIAL: the Rust `dregg_blocklace::ordering::tau` (dreggrs) is still run, but as a
            // DIFFERENTIAL SIBLING — we assert agreement with the Lean order and log LOUDLY on any
            // divergence (the verified Lean order WINS; the Rust order is never authoritative when the
            // export is live). This is the Lean==Rust differential ON THE LIVE PATH, the same posture
            // the executor uses (verified producer + Rust differential), not a beside-the-node test.
            //
            // FAIL-SAFE: when the verified archive lacks `dregg_tau_order` (stale/marshal-only build)
            // or the wire returns ERR, `compute_order` is `None` and we fall back to the Rust `tau`
            // order with a loud warning — the live path is never broken, only un-verified for that poll.
            let (ordering_lace, id_map) = build_ordering_blocklace(&lace);
            let rust_order: Vec<BlockId> = tau(&ordering_lace, &participants)
                .into_iter()
                .filter_map(|ordering_id| id_map.get(&ordering_id).copied())
                .collect();

            let order_gate_armed = crate::finality_gate::finality_gate_enabled();
            // Run the verified-Lean tau-order FFI on a BLOCKING thread (`spawn_blocking`), never inline
            // on this tokio worker. The verified ordering is O(history) and — even with the memoized
            // Lean causal-past (`BlocklaceFinality.tauOrderFast`, the parallel of the Rust `PastCache`)
            // — a large lace can still take real CPU time; running it inline PINNED the async worker and
            // STARVED the runtime (gossip/QUIC/`/status` froze) on a cross-linked DAG (the finality
            // wedge). On a blocking thread the async runtime stays responsive regardless of how long the
            // ordering takes. The lace snapshot + participants are moved into the closure (owned).
            let lean_order_opt = if order_gate_armed {
                let lace_ffi = lace.clone();
                let participants_ffi = participants.clone();
                match tokio::task::spawn_blocking(move || {
                    crate::finality_gate::VerifiedFinality::compute_order(
                        &lace_ffi,
                        &participants_ffi,
                    )
                })
                .await
                {
                    Ok(v) => v,
                    Err(e) => {
                        warn!(
                            error = %e,
                            "verified tau-order FFI blocking task panicked/cancelled — falling back \
                             to the Rust `ordering::tau` order for this poll"
                        );
                        None
                    }
                }
            } else {
                None
            };
            match lean_order_opt {
                Some(lean_order) => {
                    // DIFFERENTIAL: assert the verified Lean order and the Rust `tau` order AGREE.
                    // The two id schemes differ (blake3 vs interned `Nat`), so we compare on the
                    // content-identical `(creator, seq)` coordinate — the level at which the Rust↔Lean
                    // differential is sound (the named OPEN-CM-XSORT residual only reorders within a
                    // round-cohort, so we compare the finalized MULTISET of `(creator, seq)` and the
                    // length, the exact differential the Lean `tauGolden` `#guard`s pin).
                    let coord = |ids: &[BlockId]| -> Vec<(u64, [u8; 32])> {
                        let mut v: Vec<(u64, [u8; 32])> = ids
                            .iter()
                            .filter_map(|id| lace.get(id).map(|b| (b.seq, b.creator)))
                            .collect();
                        v.sort_unstable();
                        v
                    };
                    if coord(&lean_order) != coord(&rust_order) {
                        // MIXED-NETWORK DIFFERENTIAL (intentional): a Lean-shadowed node
                        // cross-checks every finalization against the Rust `ordering::tau` that
                        // rust-only consensus members run. A divergence here means the two finality
                        // implementations DISAGREE — surface it LOUDLY (a warn line) AND to
                        // monitoring (a Prometheus counter), never a silent drop. The verified Lean
                        // order wins for this poll; the counter lets operators of a mixed federation
                        // SEE a real rust↔lean divergence accumulate.
                        crate::metrics::inc_consensus_differential_divergence();
                        warn!(
                            lean_len = lean_order.len(),
                            rust_len = rust_order.len(),
                            "consensus DIFFERENTIAL DIVERGENCE: the verified Lean `dregg_tau_order` \
                             and the Rust `ordering::tau` finalized DIFFERENT (creator, seq) sets — \
                             the VERIFIED Lean order is AUTHORITATIVE (Rust is the differential \
                             sibling). This is a Rust-side bug or a stale archive; investigate. \
                             (dregg_consensus_differential_divergence_total incremented.)"
                        );
                    } else {
                        debug!(
                            finalized = lean_order.len(),
                            "consensus order: verified Lean `dregg_tau_order` is authoritative; \
                             Rust `ordering::tau` differential AGREES"
                        );
                    }
                    // The VERIFIED Lean order is the one we finalize over.
                    ordered_from_lean = true;
                    lean_order
                }
                None => {
                    if order_gate_armed {
                        warn!(
                            "verified consensus order UNAVAILABLE (Lean archive missing \
                             `dregg_tau_order` or wire returned ERR) — FALLING BACK to the Rust \
                             `ordering::tau` order for this poll. Rebuild the node with the verified \
                             archive (it splices Dregg2.Distributed.FinalityGate) to make the verified \
                             rule authoritative."
                        );
                    }
                    rust_order
                }
            }
        };

        // ── VERIFIED FINALITY GATE (multi-party only) — SECONDARY CONSISTENCY BELT ──────────────────
        // With `ordered` now PRODUCED by the verified Lean `dregg_tau_order` (above; the authoritative
        // path), this projection gate is a belt-and-suspenders consistency check: it independently
        // re-runs the verified `dregg_blocklace_finalize` export (the `(creator, seq)` projection of the
        // SAME `BlocklaceFinality.tauOrder`) and admits a block to the executor ONLY when that
        // projection also finalizes it. Because the order is already Lean-authoritative, every block in
        // `ordered` IS in the verified `tauGolden` order, so the gate admits them all — it now defends
        // against a corrupted `ordered` (e.g. a future fail-open Rust fallback that diverged) by
        // STOPPING the committed prefix at any block the verified projection does not finalize. The
        // Lean theorem `gate_admits_iff_verified_finalizes` proves admission ⟺ membership in `tauGolden`.
        //
        // FLAG: default ON (`DREGG_FINALITY_GATE`); solo (n=1) does not run `tau` and is
        // scales-to-zero, so the gate applies to the n>1 path that matters.
        //
        // FAIL-OPEN: when the verified archive lacks the export (stale build) or the wire returns
        // ERR, `compute` is `None` and the gate is a no-op with a loud warning — the live path is
        // never broken. When it IS armed and the verified projection excludes a block, we STOP the
        // committed batch BEFORE that block (it is NOT marked executed), so it is re-evaluated on a
        // later poll once the lace has grown enough — preserving liveness (a finalized block stays
        // pending until served; identity tracking makes the retry order-shift-proof).
        //
        // PERF: when `ordered` ALREADY came from the verified Lean export (`ordered_from_lean`,
        // the common path), the gate is provably a no-op — it re-runs the SAME verified projection
        // and admits the whole Lean order back (`gate_admits_iff_verified_finalizes`). So skip the
        // second O(history) FFI there and keep the belt ONLY for the Rust fallback (the case it
        // actually defends, where `ordered` is NOT Lean-verified). Equivalent to the prior behaviour
        // (verified=None ⇒ fail-open ⇒ admit all) on the Lean path, at half the per-poll Lean cost.
        let gate_armed = participants.len() > 1
            && !ordered_from_lean
            && crate::finality_gate::finality_gate_enabled();
        // Belt-and-suspenders consistency gate FFI — also on a BLOCKING thread (see the tau-order FFI
        // above) so it can never starve the async runtime, regardless of lace size.
        let verified = if gate_armed {
            let lace_ffi = lace.clone();
            let participants_ffi = participants.clone();
            match tokio::task::spawn_blocking(move || {
                crate::finality_gate::VerifiedFinality::compute(&lace_ffi, &participants_ffi)
            })
            .await
            {
                Ok(v) => v,
                Err(e) => {
                    warn!(
                        error = %e,
                        "verified finality-gate FFI blocking task panicked/cancelled — failing open \
                         (un-gated) for this poll"
                    );
                    None
                }
            }
        } else {
            None
        };
        if gate_armed && verified.is_none() {
            warn!(
                "verified finality gate UNAVAILABLE (Lean archive missing `dregg_blocklace_finalize` \
                 or wire returned ERR) — FAILING OPEN to the un-gated tau order. Rebuild the node \
                 with the verified archive (it splices Dregg2.Distributed.FinalityGate) to arm the gate."
            );
        }

        // ── TAU-PREFIX-MONOTONE CLOSURE (identity cursor, not an index) ─────────────────────────
        // `TauPrefixMonotone.lean` proves tau's finalized prefix is stable only CONDITIONALLY
        // (`FinalizedRegionStable`) and refutes the unconditional claim with an honest catch-up
        // trace (`lagBase → lagGrown`): a lagging validator's late wave-end block ratifies an
        // already-final leader, grows the wave's coverage, and sorts MID-PREFIX — so a bare index
        // cursor both RE-EXECUTES a block past the cursor and PERMANENTLY SKIPS the honest
        // finalized block that fell behind it. The node cannot discharge the stability hypothesis
        // locally, so the cursor does not assume it: executed blocks are tracked BY IDENTITY and
        // each poll serves exactly the finalized blocks not yet executed, in the CURRENT tau order
        // (execution = set difference, order = current tau — the corrected theorem's shape). A
        // prefix shift is then absorbed correctly and surfaced as OBSERVABILITY: `observe_order`
        // diffs the previously computed order against the new one (the conclusion-level mirror of
        // the Lean `stableCheck`) so operators SEE reorgs-by-catchup happen.
        //
        // Acquire the cursor write lock HERE — AFTER the O(history) verified-Lean FFI above —
        // so it is never held across that work (it would otherwise block the cadence's
        // `wave_open` cursor read, the second half of the producer starvation). Only the
        // single finality-executor task calls this function, so deferring the acquisition
        // cannot race a concurrent poll.
        let mut cursor = self.cursor.write().await;
        let prefix_stable = cursor.observe_order(&ordered);
        if !prefix_stable {
            crate::metrics::inc_tau_prefix_shift();
            warn!(
                total_shifts = cursor.prefix_shifts(),
                finalized = ordered.len(),
                "tau finalized order PREFIX SHIFTED (reorg-by-catchup: an honest late block sorted \
                 into the already-executed region — the TauPrefixMonotone counterexample, live). \
                 The identity cursor absorbs this correctly: every finalized block still executes \
                 exactly once, late blocks execute on this poll."
            );
        }

        let pending = cursor.pending(&ordered);
        if pending.is_empty() {
            return vec![];
        }

        let mut finalized = Vec::new();

        for block_id in pending {
            let Some(block) = lace.get(&block_id) else {
                // A finalized id missing from the lace is an invariant breach (tau orders only
                // lace members); mark it so it cannot wedge the cursor in a hot retry loop.
                warn!(
                    block_id = %block_id,
                    "finalized block id not present in the lace — marking served and skipping"
                );
                cursor.mark_executed(block_id);
                continue;
            };
            // GATE: REFUSE any actionable block the verified rule did not finalize. Ack/Data are
            // not consensus-actionable (skipped below regardless), so a heartbeat the rule does
            // not "finalize" never trips the gate. The refused block and everything after it are
            // NOT marked executed, so they are re-evaluated on a later poll once the lace has
            // grown enough (verified rule wins; liveness preserved).
            if let Some(vf) = verified.as_ref() {
                let actionable = matches!(
                    &block.payload,
                    Payload::Turn(_)
                        | Payload::TurnBundle(_)
                        | Payload::MembershipVote { .. }
                        | Payload::Checkpoint { .. }
                );
                if actionable && !vf.admits(&block.creator, block.seq) {
                    warn!(
                        block_id = %block_id,
                        seq = block.seq,
                        "verified finality gate REFUSED a block the Rust tau ordered but the \
                         verified rule did NOT finalize — STOPPING the committed batch here \
                         (will re-evaluate on a later poll; verified rule wins)"
                    );
                    break;
                }
            }
            match &block.payload {
                Payload::Turn(data) => {
                    finalized.push(FinalizedBlock::Turn {
                        block_id,
                        data: data.clone(),
                        artifacts: None,
                    });
                }
                Payload::TurnBundle(bundle) => {
                    finalized.push(FinalizedBlock::Turn {
                        block_id,
                        data: bundle.signed_turn.clone(),
                        artifacts: Some(bundle.clone()),
                    });
                }
                Payload::MembershipVote { action } => {
                    finalized.push(FinalizedBlock::Membership {
                        block_id,
                        creator: block.creator,
                        action: action.clone(),
                    });
                }
                Payload::Checkpoint { root, height } => {
                    finalized.push(FinalizedBlock::Checkpoint {
                        block_id,
                        root: *root,
                        height: *height,
                    });
                }
                // Ack and Data payloads need no consensus-level processing.
                Payload::Ack | Payload::Data(_) => {}
            }
            // Served (or consensus-inert): never serve this identity again.
            cursor.mark_executed(block_id);
        }

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

    /// LIVE EPOCH TRANSITION — advance the running consensus committee to a
    /// newly-finalized validator set.
    ///
    /// Called from [`apply_passed_proposal`] once a membership change has been
    /// ratified by a quorum of the CURRENT committee (the constitution
    /// `apply_if_passed` gate) AND confirmed by tau finality. Two live pieces
    /// advance, atomically with respect to consensus:
    ///
    /// 1. **The finalization-vote committee** — `self.votes` is reconfigured to
    ///    the new participant set and the new supermajority threshold, so the
    ///    added validator's signed finalization votes COUNT from this point and
    ///    a removed validator's no longer do. Already-attested blocks stay
    ///    attested (monotone), so the boundary introduces no safety gap.
    /// 2. **The gossip mesh admission** — each current participant's federation
    ///    key is (re-)registered in the gossip network's authenticated peer set
    ///    (keyed by `blake3(public_key)`, the SAME derivation the mesh uses), so
    ///    a newly-added validator's signed envelopes are accepted live without
    ///    recreating the transport. (Authentication is by public key, not by
    ///    `federation_id`, so this survives a committee change.)
    ///
    /// The constitution's participant set (which `tau` ordering reads live) was
    /// already advanced by the caller. What is deliberately NOT touched here is
    /// the federation/chain identity — see [`apply_passed_proposal`].
    ///
    /// A removed validator's gossip key is left registered (harmless: it is no
    /// longer a `tau` participant and its finalization votes are now rejected by
    /// the reconfigured collector). HORIZONLOG: optional deregistration on
    /// removal.
    pub async fn apply_committee_change(&self, participants: &[[u8; 32]], threshold: usize) {
        // 1. Advance the finalization-vote committee + quorum threshold.
        {
            let mut votes = self.votes.write().await;
            votes.reconfigure(participants.iter().copied(), threshold);
        }
        // 2. Admit every current participant to the authenticated gossip mesh.
        for pk in participants {
            let node_id = *blake3::hash(pk).as_bytes();
            self.gossip
                .register_peer_key(node_id, dregg_types::PublicKey(*pk))
                .await;
        }
        info!(
            participants = participants.len(),
            quorum_threshold = threshold,
            "live consensus committee advanced (epoch transition applied)"
        );
    }

    /// OPERATOR-DRIVEN epoch transition: propose adding or removing a validator
    /// on a RUNNING node (the live, chain-continuing path — distinct from the
    /// offline `add-validator` genesis re-roll).
    ///
    /// Creates a `MembershipVote` proposal block (`Join` for an add, `Leave` for
    /// a remove), self-votes it (the proposing validator's authority), persists
    /// it, and disseminates it. The change only APPLIES once a quorum of the
    /// CURRENT committee ratifies it through finality — proposing is not
    /// authority, the current committee's votes are. Returns the proposal block
    /// id so the caller can report / poll it.
    ///
    /// `add = true` proposes `Join(node_id)`; `add = false` proposes
    /// `Leave(node_id)`. A rotation is two calls: `Leave(old)` then `Join(new)`.
    pub async fn propose_membership(
        &self,
        state: &NodeState,
        node_id: [u8; 32],
        add: bool,
    ) -> BlockId {
        let action = if add {
            MembershipAction::Join { node_id }
        } else {
            MembershipAction::Leave { node_id }
        };
        let block = {
            let mut lace = self.lace.write().await;
            lace.add_block(Payload::MembershipVote {
                action: action.clone(),
            })
        };
        let block_id = block.id();
        Self::persist_block_to_store(state, &block).await;
        info!(
            block_id = %block_id,
            add,
            "operator proposed epoch transition (membership change) on running node"
        );
        self.push_new_blocks().await;
        block_id
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
        // These are unsigned mirror skeletons of already-authenticated finality
        // blocks, rebuilt purely to run `ordering::tau` — the unsigned ORDERING
        // PROJECTION path (`insert_unverified`), which enforces only causal
        // closure. Feed-integrity (signatures/seq/equivocation) was already
        // discharged on the source `finality_lace`; verified `insert` would
        // (correctly) reject these unsigned skeletons.
        let ordering_block =
            dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let ordering_id = ordering_block.id();
        let _ = ordering_lace.insert_unverified(ordering_block);

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
/// Resolve a list of `host:port` peer specs to dialable socket addresses.
///
/// Each spec may be an `IP:PORT` literal (e.g. `127.0.0.1:9420`) OR a
/// `hostname:port` (e.g. a genesis-emitted overlay hostname like `edge:9420`).
/// Hostnames are resolved via DNS at dial time (`tokio::net::lookup_host`), not
/// parsed as IP literals — the previous `p.parse::<SocketAddr>()` SILENTLY
/// DROPPED every hostname peer, so overlay-named nodes never federated at the
/// blocklace layer (the federation blocker). A spec that does not resolve (or
/// resolves to zero addresses) is logged LOUDLY at `error` — never silently
/// dropped — so a misconfigured overlay hostname / DNS failure is visible.
///
/// All resolved addresses are returned (a hostname may yield both an IPv4 and an
/// IPv6 record); the gossip layer dials each, and the one reachable from our
/// bound endpoint connects.
async fn resolve_peer_addrs(peers: &[String]) -> Vec<SocketAddr> {
    let mut resolved: Vec<SocketAddr> = Vec::new();
    for p in peers {
        match tokio::net::lookup_host(p.as_str()).await {
            Ok(addrs) => {
                let before = resolved.len();
                for addr in addrs {
                    resolved.push(addr);
                }
                let got = resolved.len() - before;
                if got == 0 {
                    error!(
                        peer = %p,
                        "peer address resolved to ZERO socket addresses — peer DROPPED; it will \
                         NOT federate at the blocklace layer. Check the overlay hostname / DNS."
                    );
                } else {
                    debug!(peer = %p, resolved = got, "resolved peer address for blocklace dial");
                }
            }
            Err(e) => {
                error!(
                    peer = %p,
                    error = %e,
                    "failed to RESOLVE peer address (hostname lookup failed) — peer DROPPED; it \
                     will NOT federate at the blocklace layer. A `host:port` spec needs a \
                     resolvable host (an IP literal or an overlay hostname that resolves)."
                );
            }
        }
    }
    resolved
}

/// Activity only when a turn is submitted or blocks arrive from peers.
#[allow(clippy::too_many_arguments)]
pub async fn run_blocklace_sync(
    state: NodeState,
    gossip_port: u16,
    auto_approve_joins: bool,
    blocklace_checkpoint_interval: u64,
    constitution_timeout_ms: u64,
    block_cadence_ms: u64,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
    // Our OWN externally-reachable gossip endpoint (`--bind <ip>:<gossip-port>`),
    // if the operator supplied a routable bind IP. Fed to the gossip layer so the
    // node advertises itself in the authenticated peer exchange and the committee
    // meshes transitively from a single bootstrap. `None` (e.g. `--bind 0.0.0.0`)
    // disables self-advertisement and falls back to manual `--federation-peers`.
    advertise_addr: Option<SocketAddr>,
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

    // THE one quorum formula (#170 unification): the blocklace strict supermajority
    // ⌊2n/3⌋ + 1 = n − ⌊(n−1)/3⌋, same function the federation layer consumes.
    // (n=1 solo gives 1 — the solo-finality semantics — with no special case.)
    let quorum_threshold = dregg_blocklace::supermajority_threshold(participants.len());

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
    let (blocklace, restored_cursor) = {
        let s = state.read().await;
        match s
            .store
            .load_blocklace(signing_key.clone(), quorum_threshold)
        {
            Ok(Some((restored_lace, legacy_executed_up_to))) => {
                let block_count = restored_lace.len();
                // CRASH-CONSISTENT resume point, BY IDENTITY (TauPrefixMonotone
                // closure). Two durable sources compose the executed set:
                //
                //  * TURN-carrying blocks — recovered EXACTLY from the durable
                //    commit log: each `CommitRecord.block_id` was written in the
                //    same atomic transaction as the applied turn, so a turn is in
                //    this set iff its effects are durably in the ledger (no lost
                //    turn, no double-apply). A persisted id whose turn is NOT in
                //    the commit log (torn crash between serve and commit) is
                //    DROPPED so the turn is re-served and re-applied idempotently
                //    — the same contract the old min(legacy, durable-cursor)
                //    resume relied on, now per-block instead of per-prefix.
                //  * NON-TURN blocks (membership/checkpoint/ack) — restored from
                //    the batch-cadence persisted id set; if that lags a crash,
                //    re-processing is idempotent (the commit-log contract).
                //
                // Pre-upgrade DBs have no persisted id set: turns still restore
                // exactly from the commit log; non-turn blocks re-process once.
                // The legacy index count is logged for visibility only — an
                // INDEX cannot be trusted as a resume point, because the order it
                // indexes into can shift under honest catch-up growth.
                let durable_turn_ids: std::collections::HashSet<BlockId> = s
                    .store
                    .commit_log_block_ids()
                    .unwrap_or_default()
                    .into_iter()
                    .map(BlockId)
                    .collect();
                let persisted_ids = s.store.load_executed_block_ids().unwrap_or_default();
                let persisted_count = persisted_ids.len();
                let mut executed_ids: Vec<BlockId> = Vec::new();
                let mut seen: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
                for id in persisted_ids {
                    let keep = match restored_lace.get(&id).map(|b| &b.payload) {
                        Some(Payload::Turn(_)) | Some(Payload::TurnBundle(_)) => {
                            durable_turn_ids.contains(&id)
                        }
                        Some(_) => true,
                        // Not in the restored lace: tau can never order it, so it
                        // can never be served; carrying it would only grow the set.
                        None => false,
                    };
                    if keep && seen.insert(id) {
                        executed_ids.push(id);
                    }
                }
                for id in &durable_turn_ids {
                    if seen.insert(*id) {
                        executed_ids.push(*id);
                    }
                }
                info!(
                    blocks = block_count,
                    executed_restored = executed_ids.len(),
                    persisted_ids = persisted_count,
                    durable_turns = durable_turn_ids.len(),
                    legacy_executed_up_to,
                    "restored blocklace from persistent storage (crash-consistent \
                     identity-cursor resume)"
                );
                (
                    restored_lace,
                    crate::execution_cursor::ExecutionCursor::restore(executed_ids),
                )
            }
            Ok(None) => {
                info!("no persisted blocklace found, starting fresh");
                (
                    Blocklace::new(signing_key.clone(), quorum_threshold),
                    crate::execution_cursor::ExecutionCursor::new(),
                )
            }
            Err(e) => {
                warn!(
                    error = %e,
                    "failed to restore blocklace from storage, starting fresh"
                );
                (
                    Blocklace::new(signing_key.clone(), quorum_threshold),
                    crate::execution_cursor::ExecutionCursor::new(),
                )
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

    // The QUIC transport identity (blake3 of the TLS cert) is randomized per
    // boot and is NOT the federation identity. Gossip envelopes are
    // authenticated against the FEDERATION signing key, so the gossip-layer
    // NodeId (the `sender` field stamped into every signed envelope) must be
    // derived deterministically from our federation public key — otherwise
    // peers look up `blake3(cert_der)` in a registry keyed by
    // `blake3(federation_pubkey)`, miss, and reject every envelope as
    // "unknown sender". See the peer_keys_map below: both ends must agree on
    // `node_id = blake3(public_key)`.
    let transport_node_id: NodeId = peer_node.node_id();
    let node_id: NodeId = *blake3::hash(our_public_key.as_bytes()).as_bytes();
    let endpoint = peer_node.endpoint().clone();

    info!(
        gossip_node_id = %dregg_net::node::fmt_node_id(&node_id),
        transport_node_id = %dregg_net::node::fmt_node_id(&transport_node_id),
        local_addr = %peer_node.local_addr(),
        "blocklace PeerNode ready"
    );

    // Build the signing key registry from known federation keys.
    //
    // Every entry is keyed by `blake3(public_key)` — the same derivation we use
    // for our own gossip `node_id` above — so a signed envelope's `sender`
    // resolves to the signer's federation public key on the receiving side.
    let peer_keys_map = {
        let s = state.read().await;
        let mut peer_keys: std::collections::HashMap<NodeId, dregg_types::PublicKey> =
            std::collections::HashMap::new();
        for fed_key in &s.known_federation_keys {
            let peer_node_id = *blake3::hash(fed_key.as_bytes()).as_bytes();
            peer_keys.insert(peer_node_id, *fed_key);
        }
        // Self-register under the federation-derived id (matches `node_id`).
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

    // SELF-FORMING MESH: advertise our own reachable listen endpoint in the
    // authenticated peer exchange. A node booted with only `--bootstrap <one-peer>`
    // signs and broadcasts this address to every peer it connects to; the peer
    // records the authenticated `identity -> addr` binding and re-shares it via
    // gossip-of-peers, so the whole committee learns every member's endpoint from a
    // single seed (manual `--federation-peers` becomes an optional override). A
    // non-routable bind (e.g. `0.0.0.0`) yields `None` and self-advertisement stays
    // off — the address would not be dialable anyway.
    if let Some(adv) = advertise_addr {
        gossip.set_advertise_addr(adv).await;
        info!(advertise = %adv, "gossip self-advertisement enabled (self-forming mesh)");
    }

    // Resolve peer addresses. A spec is `host:port` where `host` may be a
    // HOSTNAME (e.g. a genesis-emitted overlay hostname like `edge:9420`), not
    // only an `IP:PORT` literal — resolve via DNS at dial time. An unresolvable
    // peer is logged LOUDLY (an `error`), never silently dropped.
    let peer_addrs: Vec<SocketAddr> = resolve_peer_addrs(&peers).await;

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

    // QUORUM FINALIZATION VOTES ride ON the blocklace topic (the
    // proven-bidirectional dissemination channel) as a
    // `BlocklaceGossipMessage::FinalizationVote` variant — no separate topic.
    // A node emits one signed vote per turn-bearing block it locally finalizes;
    // `handle_finalization_vote` collects 2f+1 distinct-signer votes before
    // declaring a block consensus-wide Attested. See `crate::finalization_votes`.

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
    let cursor = Arc::new(RwLock::new(restored_cursor));
    let finality_notify = Arc::new(Notify::new());

    // Quorum finalization-vote collector: the committee = the consensus
    // participants, the threshold = the same 2f+1 supermajority that gates
    // block production. A turn-bearing block is consensus-attested only once a
    // supermajority of distinct members have SIGNED a vote for it.
    let votes = Arc::new(RwLock::new(crate::finalization_votes::VoteCollector::new(
        participants.iter().copied(),
        quorum_threshold,
    )));

    let handle = BlocklaceHandle {
        lace: lace.clone(),
        constitution: constitution_handle.clone(),
        gossip: gossip.clone(),
        topic: topic.clone(),
        self_key,
        signing_key: signing_key.clone(),
        votes: votes.clone(),
        my_pending_votes: Arc::new(RwLock::new(HashMap::new())),
        cursor,
        finality_notify: finality_notify.clone(),
        auto_approve_joins, // F-CRIT-2: gated by main.rs on --auto-approve-joins CLI flag OR .devnet marker
        checkpoint_interval: blocklace_checkpoint_interval,
        orphans: Arc::new(RwLock::new(crate::catchup::OrphanBuffer::new())),
        // Missing-block re-request backoff: base 1s, capped at 30s. A fresh gap
        // re-requests promptly; a persistently-missing predecessor backs off to
        // a 30s ceiling rather than being hammered every catch-up sweep.
        pull_backoff: Arc::new(RwLock::new(dregg_net::peer_score::RequestBackoff::new(
            Duration::from_secs(1),
            Duration::from_secs(30),
        ))),
        tip_pull_backoff: Arc::new(RwLock::new(dregg_net::peer_score::RequestBackoff::new(
            Duration::from_millis(500),
            Duration::from_millis(1500),
        ))),
        last_produced: Arc::new(RwLock::new(std::time::Instant::now())),
        ack_pending: Arc::new(std::sync::atomic::AtomicBool::new(false)),
        pending_payloads: Arc::new(RwLock::new(std::collections::VecDeque::new())),
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
                    // When a new peer joins, send our frontier (with any held
                    // votes piggybacked) for efficient catch-up.
                    handle_for_receiver.send_frontier().await;
                    // …and share the committee addresses we have verified, so a
                    // peer that connected to us with only a partial peer list
                    // immediately learns the rest of the mesh (gossip-of-peers).
                    handle_for_receiver
                        .share_peer_addrs(&state_for_receiver)
                        .await;
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
    // turn is submitted. Block production here is MUTATION-DRIVEN: each check
    // tick produces a block only for pending queued turns, a pending reactive
    // ack of received peer blocks, or — when the node has produced nothing for
    // `idle_heartbeat_ms` — one low-frequency idle heartbeat so liveness /
    // finality probes (and post-GST attestation exchange) still advance. Every
    // produced block links the current tips (real parent hashes) and advances
    // the creator's seq (real height). An idle node no longer grows the DAG by
    // an empty block every tick.
    if block_cadence_ms > 0 {
        spawn_block_cadence(
            state.clone(),
            handle.clone(),
            block_cadence_ms,
            idle_heartbeat_ms,
            min_block_interval_ms,
        );
    } else {
        info!(
            "block cadence disabled (--block-cadence-ms 0): blocks produced only on turn submission"
        );
    }

    // ─── Spawn the Catch-up Driver ──────────────────────────────────────────
    //
    // Reactive catch-up lives in `handle_push` (orphan buffer + pull). This timer
    // is the safety net for gaps whose triggering gossip was lost. The interval is
    // intentionally slow relative to block cadence; if cadence is disabled we still
    // run a modest 5s sweep so a connected-but-behind node converges.
    let catchup_interval_ms = if block_cadence_ms > 0 {
        (block_cadence_ms * 4).max(2_000)
    } else {
        5_000
    };
    spawn_catchup_driver(handle.clone(), catchup_interval_ms);

    // ─── Spawn the Peer Reconnect Prober ────────────────────────────────────
    //
    // Robust federation beyond the one-shot startup dial: re-dial any known
    // peer that is currently unconnected (down at boot, or dropped) on a
    // RequestBackoff schedule, so a late-joining or returning peer rejoins the
    // mesh and converges WITHOUT an operator restart. Only meaningful when we
    // have configured peers; a solo node has nothing to re-dial.
    if !peer_addrs.is_empty() {
        // Probe cadence: tied to catch-up cadence (a peer-down gap is the same
        // class of liveness problem), floored at 2s so it is polite.
        let prober_interval_ms = catchup_interval_ms.max(2_000);
        spawn_peer_prober(handle.clone(), state.clone(), prober_interval_ms);
    }

    // A fresh/restarted node proactively announces its frontier once gossip is up,
    // so peers push whatever it is missing (initial catch-up without waiting for a
    // peer to notice us first).
    let frontier_handle = handle.clone();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(3)).await;
        frontier_handle.send_frontier().await;
    });

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

        // ─── Co-turn flow: a proposed atomic turn from a peer ───────────────
        //
        // WIRE 2 OF THE LIQUID FRONTIER. Previously every non-`PublishTurn`
        // variant hit `_ => return` and was dropped — the dedicated co-turn
        // vocabulary (`ProposeAtomicTurn`/…) was defined but DEAD on receive. We
        // now lift a received proposal back into the in-process `dregg_coord`
        // engine: the node acts as a 2PC *participant*, reconstructs the full
        // forest, and evaluates it against its OWN local ledger via
        // `Participant::evaluate_proposal` — the SAME engine the local
        // `/turn/atomic/vote` path drives. A co-turn proposed on node A now
        // genuinely flows into node B's engine instead of being dropped.
        PeerMessage::ProposeAtomicTurn {
            forest_hash,
            proposal_id,
            coordinator,
            forest_data,
            ..
        } => {
            let local_ledger = {
                let s = state.read().await;
                s.ledger.clone()
            };
            let (node_id, signing_key) = {
                let s = state.read().await;
                (s.silo_id, s.cclerk.gossip_signing_key().to_bytes())
            };
            match dispatch_atomic_proposal(
                &forest_data,
                forest_hash,
                proposal_id,
                coordinator,
                node_id,
                signing_key,
                local_ledger,
            ) {
                Ok(vote) => {
                    let approve = vote.is_yes();
                    debug!(
                        from = %from,
                        forest = ?&forest_hash[..4],
                        vote = if approve { "yes" } else { "no" },
                        "co-turn: evaluated received atomic proposal as participant"
                    );
                    // VOTE-RETURN (the send half of the loop): gossip the signed
                    // verdict back as `PeerMessage::VoteAtomicTurn`, bound to the
                    // coordinator's real `proposal_id` so it tallies in
                    // `Coordinator::receive_vote` on the proposer. The signature
                    // travels as the raw 64-byte vote sig.
                    let sig: Vec<u8> = match &vote {
                        dregg_coord::Vote::Yes { signature } => signature.to_vec(),
                        dregg_coord::Vote::No { signature, .. } => signature.to_vec(),
                    };
                    handle
                        .gossip_atomic_vote(proposal_id, forest_hash, node_id, approve, sig)
                        .await;
                }
                Err(e) => {
                    debug!(from = %from, error = %e, "co-turn: dropped malformed atomic proposal");
                }
            }
            return;
        }

        // ─── Co-turn flow: a participant's vote returns to the coordinator ──────
        //
        // WIRE 3 OF THE LIQUID FRONTIER (the vote-return + tally). The coordinator
        // that broadcast the `ProposeAtomicTurn` receives each participant's signed
        // `VoteAtomicTurn` and feeds it into the SAME `Coordinator::receive_vote`
        // the local `/turn/atomic/vote` HTTP path drives — the coordinator persisted
        // in `state::atomic_proposals` IS the vote tally. When the quorum of Yes
        // votes lands, `receive_vote` returns `Decision::Commit` and we drive the
        // existing commit path (`Coordinator::commit` against the local ledger), so
        // the co-turn SETTLES across the participants. A No-quorum aborts.
        PeerMessage::VoteAtomicTurn {
            proposal_id,
            forest_hash,
            voter,
            vote,
            signature,
        } => {
            tally_returned_vote(
                state,
                from,
                proposal_id,
                forest_hash,
                voter,
                vote,
                signature,
            )
            .await;
            return;
        }

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
        BlocklaceGossipMessage::Frontier { tips, votes, .. } => {
            // Record any piggybacked finalization votes (the anti-entropy carry:
            // a vote dropped on the eager path arrives here on the next frontier).
            for vote in votes {
                handle_finalization_vote(handle, from, vote).await;
            }
            handle_frontier(handle, from, tips).await;
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
        BlocklaceGossipMessage::PeerAddrs(addrs) => {
            handle_peer_addrs(handle, state, from, addrs).await;
        }
        BlocklaceGossipMessage::FinalizationVote(vote) => {
            handle_finalization_vote(handle, from, vote).await;
        }
    }
}

/// Dispatch a received `ProposeAtomicTurn` into the in-process `dregg_coord`
/// engine — the receive-side weld that makes a co-turn FLOW between nodes.
///
/// The node receiving a proposal acts as a 2PC **participant**: it reconstructs
/// the full `AtomicForest` from the gossiped `forest_data`, then evaluates it
/// against its OWN local ledger via [`dregg_coord::Participant::evaluate_proposal`]
/// — the same engine the local `/turn/atomic/vote` path drives. The result is a
/// real, signed `Vote` (Yes if our preconditions hold, No with a reason
/// otherwise), NOT a no-op: the variable that previously hit `_ => return` now
/// reaches the engine and produces a vote.
///
/// The participant's `cell_id` is the node's own sovereign cell (`CellId(node_id)`),
/// so the preconditions keyed to our cell are checked against our local view.
///
/// Returns the produced `Vote`, or a `CoordError` if the `forest_data` does not
/// decode into a well-formed forest (the only "drop" left — a malformed payload,
/// logged at the call site).
fn dispatch_atomic_proposal(
    forest_data: &[u8],
    forest_hash: [u8; 32],
    proposal_id: [u8; 32],
    coordinator: [u8; 32],
    node_id: [u8; 32],
    signing_key: [u8; 32],
    ledger: dregg_cell::Ledger,
) -> Result<dregg_coord::Vote, dregg_coord::CoordError> {
    // Reconstruct the full forest from the richer wire payload.
    let forest = dregg_coord::AtomicForest::decode_from_wire(forest_data)?;

    // Anti-tamper #1: the decoded forest's hash must match the announced
    // `forest_hash` (rejects a payload whose body was swapped under a stale hash).
    if forest.hash != forest_hash {
        return Err(dregg_coord::CoordError::HashMismatch {
            claimed: forest_hash,
            computed: forest.hash,
        });
    }

    // Anti-tamper #2 (THE PROPOSAL-ID FIX): recompute the coordinator's proposal
    // id from `(forest.hash, coordinator)` and verify it equals the claimed
    // `proposal_id` on the wire. This binds our vote to the coordinator's REAL
    // proposal id — the same id `Coordinator::receive_vote` verifies the returning
    // vote's signature against — instead of binding to the bare `forest_hash`. A
    // forged `proposal_id` (not derivable from this forest + coordinator) is
    // rejected here rather than producing an unverifiable vote.
    let expected_pid = dregg_coord::Coordinator::proposal_id_for(&forest.hash, &coordinator);
    if expected_pid != proposal_id {
        return Err(dregg_coord::CoordError::HashMismatch {
            claimed: proposal_id,
            computed: expected_pid,
        });
    }

    // Build the participant over our local ledger view and evaluate. This is the
    // in-process coord engine reached: real precondition checks against our cells.
    // The vote is SIGNED over the coordinator's proposal_id so it verifies on return.
    let cell_id = dregg_cell::CellId(node_id);
    let mut participant = dregg_coord::Participant::new(cell_id, node_id, signing_key, ledger);
    Ok(participant.evaluate_proposal(&proposal_id, &forest))
}

/// Tally a returned `VoteAtomicTurn` into the coordinator that proposed it, and
/// drive the commit when the quorum agrees — the COORDINATOR-SIDE close of the
/// co-turn loop.
///
/// The coordinator persisted in `state::atomic_proposals` under `proposal_id` is
/// the live vote tally (the same `Coordinator` the local `/turn/atomic/vote` HTTP
/// path feeds). This funnel arm:
///   1. reconstructs the `Vote` (Yes/No) from the wire,
///   2. feeds it into `Coordinator::receive_vote` (which verifies the Ed25519
///      signature against `(proposal_id, forest.hash)` and the voter's registered
///      key — a forged vote is rejected here),
///   3. on `Decision::Commit`, drives the existing `Coordinator::commit` against
///      the local ledger so the atomic forest SETTLES; on `Decision::Abort`,
///      aborts; otherwise leaves the proposal Proposing for more votes.
///
/// A vote for an unknown `proposal_id` (we are not the coordinator, or it expired)
/// is dropped — only the proposing node holds the coordinator.
async fn tally_returned_vote(
    state: &NodeState,
    from: SocketAddr,
    proposal_id: [u8; 32],
    forest_hash: [u8; 32],
    voter: [u8; 32],
    approve: bool,
    signature: Vec<u8>,
) {
    if signature.len() != 64 {
        debug!(from = %from, "co-turn: dropped returned vote with malformed signature length");
        return;
    }
    let mut sig = [0u8; 64];
    sig.copy_from_slice(&signature);
    let vote = if approve {
        dregg_coord::Vote::yes(sig)
    } else {
        dregg_coord::Vote::no("participant rejected", sig)
    };

    let mut s = state.write().await;

    // We must be the COORDINATOR holding this proposal; otherwise drop.
    let decision = {
        let active = match s.atomic_proposals.get_mut(&proposal_id) {
            Some(p) => p,
            None => {
                debug!(
                    from = %from,
                    proposal = ?&proposal_id[..4],
                    "co-turn: returned vote for unknown/expired proposal — dropped"
                );
                return;
            }
        };
        // Sanity: the announced forest hash must match the proposal we hold.
        if active.forest.hash != forest_hash {
            debug!(from = %from, "co-turn: returned vote forest-hash mismatch — dropped");
            return;
        }
        match active.coordinator.receive_vote(voter, vote) {
            Ok(maybe_decision) => maybe_decision,
            Err(e) => {
                debug!(from = %from, error = %e, "co-turn: returned vote rejected by coordinator");
                return;
            }
        }
    };

    match decision {
        Some(dregg_coord::Decision::Commit) => {
            // Quorum of Yes votes reached: drive the existing commit path against
            // the local ledger so the atomic forest settles.
            let mut active = match s.atomic_proposals.remove(&proposal_id) {
                Some(a) => a,
                None => return,
            };
            match active.coordinator.commit(&mut s.ledger) {
                Ok(_commit_msg) => {
                    info!(
                        from = %from,
                        proposal = ?&proposal_id[..4],
                        "co-turn: quorum reached — atomic forest committed across participants"
                    );
                }
                Err(e) => {
                    let _ = active.coordinator.abort(format!("commit failed: {e}"));
                    warn!(from = %from, error = %e, "co-turn: commit failed after quorum — aborted");
                }
            }
        }
        Some(dregg_coord::Decision::Abort) => {
            if let Some(mut active) = s.atomic_proposals.remove(&proposal_id) {
                let _ = active
                    .coordinator
                    .abort("too many rejections — threshold unreachable");
                debug!(from = %from, proposal = ?&proposal_id[..4], "co-turn: proposal aborted");
            }
        }
        Some(dregg_coord::Decision::Pending) | None => {
            // Still collecting votes; the coordinator stays Proposing.
        }
    }
}

/// Record ONE finalization vote into the collector and fire the consensus-wide
/// Attested transition (metric + log) EXACTLY ONCE, on whichever recorded vote
/// crosses the quorum threshold.
///
/// This is the single funnel for BOTH the node's OWN vote (`emit_finalization_vote`)
/// and a peer's vote (`handle_finalization_vote`). Routing both through here is
/// load-bearing: at n=2 the quorum is crossed by the SECOND distinct vote, and
/// either party's vote can be the second one to land in this node's collector.
/// If the peer's vote arrives BEFORE this node has recorded its own (a routine
/// gossip/self-emit race — the peer can finalize and gossip its vote before our
/// local finalizer emits ours), then it is the SELF-vote record that crosses the
/// threshold. A self-record path that discarded its `RecordOutcome` (the old
/// `let _ = col.record(..)`) therefore swallowed the `ReachedQuorum` transition,
/// leaving the node permanently at `AlreadyQuorum` with the metric never
/// incremented and the log never emitted — the per-boot "one direction reaches
/// consensus-wide Attested, the other never does" symptom (purely a counting
/// race in the node, independent of transport). Funnelling both records here
/// fires the transition once regardless of which vote is the threshold-crosser.
async fn record_finalization_vote(
    handle: &BlocklaceHandle,
    vote: &crate::finalization_votes::FinalizationVote,
) {
    use crate::finalization_votes::RecordOutcome;
    let block_id = vote.block_id;
    let outcome = {
        let mut col = handle.votes.write().await;
        col.record(vote)
    };
    // Per-validator liveness: every recorded (well-formed, member-signed) vote is
    // a freshness heartbeat from its signer. Bounded label cardinality (one per
    // committee member).
    let voter_tag = hex_encode(&vote.voter[..4]);
    match outcome {
        RecordOutcome::ReachedQuorum { distinct_votes } => {
            crate::metrics::inc_consensus_attested();
            crate::metrics::set_validator_last_seen(&voter_tag);
            crate::metrics::inc_validator_votes(&voter_tag);
            // Finality latency: first local vote for this block → quorum reached.
            crate::metrics::record_finality_latency(&block_id.0);
            info!(
                block_id = %block_id,
                votes = distinct_votes,
                "block reached CONSENSUS-WIDE Attested finality (quorum of distinct signed \
                 finalization votes) — agreement, not a per-node guess"
            );
        }
        RecordOutcome::Counted { distinct_votes } => {
            crate::metrics::set_validator_last_seen(&voter_tag);
            crate::metrics::inc_validator_votes(&voter_tag);
            // The first recorded vote opens this node's quorum-gathering window.
            if distinct_votes == 1 {
                crate::metrics::mark_block_voting_started(block_id.0);
            }
            debug!(
                block_id = %block_id,
                votes = distinct_votes,
                "recorded finalization vote (below quorum)"
            );
        }
        RecordOutcome::AlreadyQuorum { .. } => {
            crate::metrics::set_validator_last_seen(&voter_tag);
            crate::metrics::inc_validator_votes(&voter_tag);
        }
        RecordOutcome::Rejected => {
            debug!(
                block_id = %block_id,
                "rejected finalization vote (bad signature or non-member signer)"
            );
        }
    }
}

/// Process a received finalization vote: verify + collect by distinct signer,
/// firing the consensus-wide Attested transition if THIS vote crosses quorum.
async fn handle_finalization_vote(
    handle: &BlocklaceHandle,
    _from: SocketAddr,
    vote: crate::finalization_votes::FinalizationVote,
) {
    record_finalization_vote(handle, &vote).await;
}

/// Process a received `PeerAddrs` gossip-of-peers announcement: learn dialable
/// listen addresses for committee members from a connected peer, so the mesh
/// forms transitively from a single seed.
///
/// SECURITY — the committee key set is the trust anchor:
///   * The whole envelope was already Ed25519-verified by the gossip layer
///     against the sending NODE's federation key, so a non-committee wire peer
///     cannot deliver this message at all (it would be dropped as "unknown
///     sender" / bad signature before reaching here).
///   * EACH advertised `(committee_pubkey, addr)` is accepted ONLY when
///     `committee_pubkey` is one of OUR `known_federation_keys` — a genesis-known
///     member we already trust. A claimed address for any other key (a stranger
///     an introducer tries to smuggle in) is REJECTED. Discovery learns
///     ADDRESSES for trusted identities; it never admits new identities, and the
///     wire SENDER is never the trust anchor.
///   * We never learn an address for OURSELVES (`self_key`) and the address must
///     be a well-formed, routable socket (non-unspecified host, non-zero port).
///
/// An accepted address is fed to the gossip layer's topic peer set
/// ([`GossipNetwork::learn_peer`]) WITHOUT a synchronous dial; the existing
/// reconnect prober dials it on its backoff schedule. Returns the number of
/// newly-learned committee addresses (for tests / diagnostics).
async fn handle_peer_addrs(
    handle: &BlocklaceHandle,
    state: &NodeState,
    from: SocketAddr,
    addrs: Vec<([u8; 32], SocketAddr)>,
) -> usize {
    // The committee key set: the genesis-trusted identities. Discovery may learn
    // an address ONLY for a key in this set (never an introducer-supplied stranger).
    let committee: std::collections::HashSet<[u8; 32]> = {
        let s = state.read().await;
        s.known_federation_keys.iter().map(|k| k.0).collect()
    };

    let mut learned = 0usize;
    for (pubkey, addr) in addrs {
        // TRUST GATE: the address is only acceptable if it is claimed FOR a known
        // committee member. A non-committee key is a stranger — reject it.
        if !committee.contains(&pubkey) {
            debug!(
                from = %from,
                "gossip-of-peers: rejecting address for non-committee key (untrusted introducer claim)"
            );
            continue;
        }
        // Never learn our own address (we don't dial ourselves).
        if pubkey == handle.self_key {
            continue;
        }
        // Validate the address shape: a routable host + non-zero port. Drops
        // 0.0.0.0/::/port-0 hints that nothing can dial.
        if addr.ip().is_unspecified() || addr.port() == 0 {
            debug!(from = %from, %addr, "gossip-of-peers: rejecting un-dialable address");
            continue;
        }
        if handle.gossip.learn_peer(&handle.topic, addr).await {
            info!(
                from = %from,
                %addr,
                member = %hex_encode(&pubkey[..4]),
                "gossip-of-peers: learned committee peer address (prober will dial)"
            );
            learned += 1;
        }
    }
    if learned > 0 {
        // A freshly-learned peer is an open gap: nudge a frontier so once the
        // prober dials it, catch-up flows promptly.
        crate::metrics::set_federation_peers_connected(
            handle.gossip.connected_peer_count().await as f64,
        );
    }
    learned
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

    // Apply the batch through the orphan-buffering catch-up path. Blocks that
    // arrive before their predecessors are STAGED (not dropped) and re-applied in
    // causal order once the gap closes; the A1-fixed `receive_block` re-verifies
    // sig/seq/equivocation on every (re-)application. Out-of-order or partial
    // delivery from gossip therefore still converges to the causally-closed set.
    let outcome = {
        let mut lace = handle.lace.write().await;
        let mut buffer = handle.orphans.write().await;
        crate::catchup::apply_with_buffering(&mut lace, &mut buffer, blocks)
    };

    // Auto-evict any equivocators surfaced during application (keeps the block as
    // evidence, mirrors the previous behaviour).
    if !outcome.equivocations.is_empty() {
        let mut constitution = handle.constitution.write().await;
        for proof in &outcome.equivocations {
            let creator_hex: String = proof.creator[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            warn!(
                from = %from,
                creator = %creator_hex,
                "equivocation detected from peer"
            );
            constitution.auto_evict(proof);
        }
        drop(constitution);

        // GOSSIP-LAYER PENALTY: the transport peer that relayed the equivocation
        // is graylisted in the gossip reputation scoreboard — it is evicted from
        // every topic's eclipse-resistant eager set so a Byzantine relay stops
        // carrying full messages. This is distinct from the CONSENSUS-layer
        // auto-evict above (which removes the *equivocating creator* from
        // membership): here we penalize the *relay* at the network layer.
        // (The block itself is still retained as slashable evidence and continues
        // to propagate — only this peer's relay privilege is demoted.)
        handle.gossip.penalize_equivocation_relay(from).await;

        // ADJUDICATION WELD (ORGANS §5 / CONSENSUS-FLEX §7): propagated fork
        // evidence reaches the SLASH path, not just membership auto-evict.
        // Each retained proof is reduced to the self-contained wire value
        // (`EvidenceOfEquivocation`); if the equivocator posted a bond on
        // this node, the exhibit slashes it as one conserved executor move
        // from the bonded cell — no operator in the loop, no-double-resolve
        // via the burned evidence digest. Unbonded / already-resolved /
        // different-seq proofs are logged no-ops.
        for proof in &outcome.equivocations {
            crate::equivocation_court_service::slash_from_proof(state, proof).await;
        }
    }

    let inserted = outcome.inserted.len();

    // REACTIVE ATTESTATION: a peer's freshly-inserted non-Ack block (turn /
    // membership / checkpoint) is a mutation that wants our acknowledgment —
    // flag the cadence task to answer with one `Payload::Ack` block on its next
    // check tick. Acking only NON-Ack foreign blocks terminates the exchange
    // (acks do not beget acks), so n nodes acking one turn produce exactly the
    // n attestation blocks the 2f+1 quorum needs, not a storm.
    if outcome
        .inserted
        .iter()
        .any(|b| b.creator != handle.self_key && b.payload != Payload::Ack)
    {
        handle
            .ack_pending
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // Clear pull-backoff for every block that just landed: a later miss of the
    // same id (after a re-org / GC) should start fresh, not deep in backoff.
    if !outcome.inserted.is_empty() {
        let mut bo = handle.pull_backoff.write().await;
        let mut tbo = handle.tip_pull_backoff.write().await;
        for b in &outcome.inserted {
            let id = b.id();
            bo.clear(&id);
            tbo.clear(&id);
        }
    }

    // Persist newly inserted blocks to the store (batch write for efficiency).
    if !outcome.inserted.is_empty() {
        let s = state.read().await;
        if let Err(e) = s.store.persist_blocks(&outcome.inserted) {
            warn!(error = %e, "failed to persist received blocks to store");
        }
        drop(s);
    }

    if inserted > 0 {
        let buffered = handle.orphans.read().await.len();
        info!(
            from = %from,
            inserted = inserted,
            total_received = block_count,
            buffered_orphans = buffered,
            "received blocks from peer"
        );
        // Signal the finality executor that new blocks may advance ordering.
        handle.finality_notify.notify_one();
    }

    // If a gap remains (missing predecessors of buffered orphans), request the
    // catch-up roots so a peer pushes them; their causal past comes along
    // (handle_pull includes `causal_past`), draining the buffer.
    if !outcome.pull_roots.is_empty() {
        let pull_msg = BlocklaceGossipMessage::Pull(outcome.pull_roots);
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
            if !sent_ids.contains(past_id)
                && let Some(block) = lace.get(past_id)
            {
                to_send.push(block.clone());
                sent_ids.insert(*past_id);
            }
        }
        // Include the block itself.
        if !sent_ids.contains(block_id)
            && let Some(block) = lace.get(block_id)
        {
            to_send.push(block.clone());
            sent_ids.insert(*block_id);
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
    // SELF-HEALING PULL (the other half of reconciliation): a Frontier is push-only
    // on its own — the receiver computes what the SENDER lacks and pushes it. That
    // converges a peer that is strictly BEHIND, but NOT the concurrent case where
    // both sides hold blocks the other is missing. At n>1 the round-synchronous
    // rule needs a SUPERMAJORITY of distinct creators at a round before any node may
    // advance (n=3 ⇒ all three), so when the committee advances rounds concurrently
    // every node ends a round holding its OWN newest block but missing its peers'
    // newest blocks. The only holder of a peer's tip is that peer; if its one-shot
    // eager push was lost, nothing ever re-requests it — the orphan-pull path never
    // fires (the missing tip never arrives to reveal the gap), so the cluster wedges
    // one block short of the round cohort FOREVER and `dag_height` freezes. Pulling
    // every announced per-creator tip we do NOT hold closes that gap deterministically:
    // a Pull response carries the block's full causal past (`handle_pull`), so any
    // predecessor gap heals atomically. Backoff-gated (shared with the catch-up
    // pull limiter), so a tip we already requested is not re-hammered and steady
    // state — every announced tip known — stays quiet.
    let tips_to_pull: Vec<BlockId> = {
        let lace = handle.lace.read().await;
        their_tips
            .values()
            .filter(|tip_id| !lace.contains(tip_id))
            .copied()
            .collect()
    };
    if !tips_to_pull.is_empty() {
        let due: Vec<BlockId> = {
            let mut bo = handle.tip_pull_backoff.write().await;
            tips_to_pull
                .into_iter()
                .filter(|id| bo.should_request(*id))
                .collect()
        };
        if !due.is_empty() {
            debug!(from = %from, tips = due.len(), "frontier: pulling announced tips we lack");
            handle
                .broadcast_gossip_message(&BlocklaceGossipMessage::Pull(due))
                .await;
        }
    }

    let to_send = {
        let lace = handle.lace.read().await;

        // Determine which blocks we have that the peer doesn't.
        // A peer with a given tip has all blocks in that tip's causal past.
        // Take the union of all (locally-known) tips' causal pasts in ONE
        // shared-visited traversal instead of re-walking the overlapping
        // history once per tip. Only tips we actually hold seed the union,
        // matching the prior `if lace.contains(tip_id)` guard; the union is
        // inclusive of each seed, so the tips themselves are covered.
        let known_tips: Vec<&BlockId> = their_tips
            .values()
            .filter(|tip_id| lace.contains(tip_id))
            .collect();
        let their_known: std::collections::HashSet<BlockId> = lace.causal_past_union(known_tips);

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

    // NOTE: a received Frontier must NOT be answered with another (votes-carrying)
    // Frontier. Doing so was an UNBOUNDED AMPLIFICATION LOOP: every node that holds
    // a re-emittable finalization vote (which is every member for the whole
    // re-emit window after each finalization) replied to each inbound Frontier with
    // an outbound one, which the peer in turn replied to — a frontier storm
    // (thousands/sec at n=3) that saturated the gossip receive path and STARVED the
    // very block/Pull deliveries the round-synchronous rule needs to advance, so the
    // committee stalled after the first wave even though the transport was healthy.
    // Vote anti-entropy already has TWO bounded channels that do not self-amplify:
    // `reemit_pending_votes` (once per cadence tick, budget-capped) and the vote
    // piggyback on each node's OWN periodic announcement Frontier (`send_frontier` →
    // `frontier_votes`). A catching-up peer therefore still learns our votes within
    // a tick — without the reply that turned reconciliation into a storm.

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
    let num_chunks = total_missing.div_ceil(MAX_BLOCKS_PER_PUSH);
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

// ─── Round-Disciplined Production Plan ───────────────────────────────────────

/// The predecessor-selection decision for one round-disciplined block, computed
/// from the local lace and the committee supermajority. Pure so the
/// round-synchrony property is unit-testable without a running node. See
/// [`BlocklaceHandle::produce_round_block`] for the rationale.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RoundPlan {
    /// Author a genesis block (round 1, no predecessors): we have authored
    /// nothing yet and seed the round-1 cohort.
    Genesis,
    /// Author round `next_round` linking the WHOLE round-(`next_round`−1) cohort
    /// (`predecessors`): a supermajority of distinct creators are present at our
    /// current round, so we may advance.
    Advance {
        predecessors: Vec<BlockId>,
        next_round: u64,
    },
    /// Do not produce: we lack a supermajority of distinct creators at our
    /// current round, so advancing would link too few of the previous round for
    /// `tau` to super-ratify. The caller retries on a later tick.
    Wait,
}

/// Decide how the local creator advances the DAG by ONE round (Cordial-Miners
/// round discipline). `my_creator` is this node's public key; `supermajority`
/// is `supermajority_threshold(participants)`.
///
/// Rule:
///  * No own block yet ⇒ [`RoundPlan::Genesis`].
///  * Otherwise let `r = my_max_round`. We want round `r+1`. If a supermajority
///    of DISTINCT creators have a block at round `r`, return [`RoundPlan::Advance`]
///    linking every round-`r` block; else [`RoundPlan::Wait`].
///
/// Linking the full round-`r` cohort makes the new block land at exactly `r+1`,
/// and — because every honest node paces identically — fills each round with a
/// supermajority of creators, which is the precondition `is_super_ratified` needs.
pub(crate) fn plan_round_block(
    lace: &Blocklace,
    my_creator: [u8; 32],
    supermajority: usize,
) -> RoundPlan {
    // Round of every block in the lace (DAG depth; genesis = 1).
    let mut round_of: HashMap<BlockId, u64> = HashMap::new();
    let mut my_max_round: u64 = 0;
    for (id, block) in lace.iter() {
        let r = lace.round_of(id).unwrap_or(0);
        round_of.insert(*id, r);
        if block.creator == my_creator {
            my_max_round = my_max_round.max(r);
        }
    }

    if my_max_round == 0 {
        // We have authored nothing yet: seed round 1.
        return RoundPlan::Genesis;
    }

    // The cohort at our current round: distinct creators + the block ids.
    let mut cohort_creators: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
    let mut cohort_blocks: Vec<BlockId> = Vec::new();
    for (id, block) in lace.iter() {
        if round_of.get(id).copied() == Some(my_max_round) {
            cohort_creators.insert(block.creator);
            cohort_blocks.push(*id);
        }
    }

    if cohort_creators.len() >= supermajority {
        // Deterministic predecessor order (independent of HashMap iteration).
        cohort_blocks.sort_unstable_by_key(|a| a.0);
        RoundPlan::Advance {
            predecessors: cohort_blocks,
            next_round: my_max_round + 1,
        }
    } else {
        RoundPlan::Wait
    }
}

// ─── Block Production Cadence ────────────────────────────────────────────────

/// What the cadence task does on one check tick. Pure decision so the
/// no-empty-block-spam property is unit-testable without a running node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CadenceAction {
    /// Queued turns are pending: submit them as real turn blocks.
    DrainTurns,
    /// A peer's non-Ack block landed since the last tick: answer with one
    /// `Payload::Ack` block (Cordial-Miners reactive attestation).
    ReactiveAck,
    /// An unclosed wave carries a turn this node still has to help finalize:
    /// advance one round (a minimal `Payload::Ack` attestation) to drive the
    /// wave toward super-ratification. The WAKE/CLOSE step on the round-driven
    /// (n>1) path: a turn entered the DAG at some round, and the cluster must
    /// advance through the wave boundary for `tau` to super-ratify it, even
    /// after the one-shot reactive-ack has been spent.
    AdvanceWave,
    /// Nothing pending and the node produced no block for a full idle window:
    /// one low-frequency heartbeat block so liveness/finality probes advance.
    IdleHeartbeat,
    /// Nothing to do — produce NO block.
    Nothing,
}

/// Decide the cadence action for one check tick. Block production is
/// MUTATION-DRIVEN: a block is produced only for pending turns, a pending
/// reactive ack, or an expired idle-heartbeat window (`idle_heartbeat_ms == 0`
/// disables the idle heartbeat entirely).
///
/// This is the SOLO (n=1) decision (no rounds, no waves: `tau` finalizes every
/// block trivially in sequence). The round-driven (n>1) path uses
/// [`round_cadence_decision`], which adds the wave-open WAKE/CLOSE step and the
/// min-block-interval rate cap.
pub(crate) fn cadence_decision(
    queued_turns: usize,
    ack_pending: bool,
    idle_for: Duration,
    idle_heartbeat_ms: u64,
) -> CadenceAction {
    if queued_turns > 0 {
        CadenceAction::DrainTurns
    } else if ack_pending {
        CadenceAction::ReactiveAck
    } else if idle_heartbeat_ms > 0 && idle_for >= Duration::from_millis(idle_heartbeat_ms) {
        CadenceAction::IdleHeartbeat
    } else {
        CadenceAction::Nothing
    }
}

/// Decide the cadence action for ONE round-driven (n>1) check tick.
///
/// This is the QUIESCENT-ON-DEMAND core of the n>1 finality path. The old
/// round-driven tick advanced a round EVERY tick (carrying a queued turn or an
/// empty `Payload::Ack`), so `--block-cadence-ms` was effectively the BLOCK
/// rate: 1000ms → one block/s of empty-DAG spam; 5000ms → the cluster never
/// woke and a faucet turn never finalized (the observed live deadlock). This
/// decision instead advances a round ONLY when there is genuinely something to
/// finalize, and never faster than `min_block_interval`:
///
///  * `queued_turns > 0` ⇒ [`CadenceAction::DrainTurns`] — carry a real turn.
///  * a peer's fresh non-Ack block landed (`ack_pending`) ⇒
///    [`CadenceAction::ReactiveAck`] — the WAKE: a peer's turn means a wave
///    needs closing, so advance the round to attest it.
///  * an unclosed wave carries an unfinalized turn (`wave_open`) ⇒
///    [`CadenceAction::AdvanceWave`] — keep advancing rounds across the wave
///    boundary until `tau` super-ratifies (one reactive-ack is not enough: a
///    turn at round `r` needs the cluster to reach the wave's last round).
///  * otherwise, only the idle-heartbeat liveness floor remains (the DAG is
///    fully finalized: nothing to block about).
///
/// RATE CAP: if this node produced a block less than `min_block_interval` ago,
/// every advance-producing action is held to [`CadenceAction::Nothing`] for
/// this tick — so even under sustained load the node emits ≤ one block per
/// `min_block_interval`. The cap CANNOT deadlock finality: the wake conditions
/// (`queued_turns` / `ack_pending` / `wave_open`) are DAG/queue STATE, not
/// edge-triggered events, so they persist across the hold; once the interval
/// elapses the held round is produced and the wave closes — just over a few
/// `min_block_interval`-spaced rounds (slower finality is the accepted
/// tradeoff). The idle heartbeat is exempt from the cap (it is already a
/// low-frequency floor governed by `idle_heartbeat_ms ≫ min_block_interval`).
pub(crate) fn round_cadence_decision(
    queued_turns: usize,
    ack_pending: bool,
    wave_open: bool,
    since_last_block: Duration,
    min_block_interval: Duration,
    idle_for: Duration,
    idle_heartbeat_ms: u64,
) -> CadenceAction {
    // The work this tick WANTS to do, ignoring the rate cap. Priority: drain a
    // real turn, else attest a freshly-arrived peer turn, else keep closing an
    // already-open wave.
    let wants_advance = if queued_turns > 0 {
        Some(CadenceAction::DrainTurns)
    } else if ack_pending {
        Some(CadenceAction::ReactiveAck)
    } else if wave_open {
        Some(CadenceAction::AdvanceWave)
    } else {
        None
    };

    if let Some(action) = wants_advance {
        // RATE CAP: hold the advance if we produced a block too recently. The
        // wake condition persists (DAG/queue state), so the very next tick after
        // the interval elapses will advance — no lost liveness, just paced.
        if since_last_block < min_block_interval {
            CadenceAction::Nothing
        } else {
            action
        }
    } else if idle_heartbeat_ms > 0 && idle_for >= Duration::from_millis(idle_heartbeat_ms) {
        // Fully finalized DAG: only the low-frequency liveness floor remains.
        CadenceAction::IdleHeartbeat
    } else {
        // Nothing to finalize and the DAG is quiet → produce NO block.
        CadenceAction::Nothing
    }
}

/// Whether the DAG carries an UNCLOSED wave that this node should help finalize:
/// is there any turn-bearing (non-`Ack`) block in the lace whose id `tau` has
/// NOT yet finalized+executed (it is not in the identity `cursor`)?
///
/// This is the quiescence boundary for the round-driven path. A turn block lands
/// at some round `r` (wave `(r-1)/wavelength`); for `tau` to super-ratify and
/// finalize it, the cluster must advance through the wave's last round and a
/// later wave-leader must be ratified — several rounds of (possibly `Ack`-only)
/// wave-closing blocks after the turn arrives. While such a turn sits
/// unfinalized, the node must keep advancing rounds (`AdvanceWave`); once every
/// non-`Ack` block in the lace has executed, the DAG has nothing left to block
/// about and goes quiet (`Ack` heartbeats alone never reopen a wave: acking an
/// ack is the terminating case).
///
/// Cheap (one pass over the in-RAM lace, an O(1) cursor membership test per
/// block — both already O(history)-resident) and PURE in its inputs, so the
/// no-empty-block-spam + wake-on-pending properties are exercised by
/// [`round_cadence_decision`] without a running node; this only supplies the
/// `wave_open` boolean it consumes.
async fn wave_open(handle: &BlocklaceHandle) -> bool {
    let cursor = handle.cursor.read().await;
    let lace = handle.lace.read().await;

    // The DAG depth (max round). A turn-bearing block needs the cluster to advance
    // through its wave's last round and a later wave-leader to super-ratify it — a
    // bounded number of rounds past where the turn LANDED. Once the tip is that far
    // ahead, the turn is tau-FINALIZED; whether it has been EXECUTED yet is a
    // separate, purely-local step the finality executor performs on its own.
    //
    // LIVELOCK GUARD: keying "wave open" off `!is_executed` ALONE means that when the
    // finality executor lags the producer (e.g. under load, its O(history) verified
    // tau poll falls behind), a turn stays "open" long after it is finalized, so the
    // cadence keeps advancing EMPTY wave-closing rounds for it — which grows the DAG,
    // makes the executor's next poll even slower, and drives a runaway (the DAG raced
    // to dozens of rounds while finality stuck). Bounding "open" to turns within
    // `2*wavelength` rounds of the tip stops that: a turn the chain has already moved
    // well past is finalized-pending-execution (NOT a reason to mint more rounds), so
    // production goes quiescent and lets the executor catch up — no runaway, and the
    // turn still commits the moment its poll lands.
    let tip_round = lace.tips().values().filter_map(|t| lace.round_of(t)).max();
    const FINALITY_DEPTH_ROUNDS: u64 = 2 * 3; // 2 × wavelength (ordering default = 3)

    lace.iter().any(|(id, block)| {
        if block.payload == Payload::Ack || cursor.is_executed(id) {
            return false;
        }
        // Still needs ROUNDS to super-ratify (within the finality depth of the tip) ⇒
        // genuinely open. Already finalized-but-unexecuted (the chain is far past it) ⇒
        // not open: the executor will serve it without more rounds.
        match (tip_round, lace.round_of(id)) {
            (Some(tip), Some(r)) => tip.saturating_sub(r) <= FINALITY_DEPTH_ROUNDS,
            _ => true,
        }
    })
}

/// Spawn the block-production cadence task.
///
/// `check_ms` is a CHECK interval, not a production interval: most ticks
/// produce nothing. On each tick the task either
///   1. drains signed turns queued in `consensus_queue` into real turn blocks
///      (these flow through the finality executor and update the ledger +
///      attested roots),
///   2. answers freshly-received peer turn blocks with one `Payload::Ack`
///      block (reactive attestation, see `BlocklaceHandle::ack_pending`), or
///   3. produces one idle *heartbeat* block (`Payload::Ack`) — but only when
///      the node has produced no block at all for `idle_heartbeat_ms`. A
///      heartbeat is a real, Ed25519-signed block linking the current tips
///      (real seq, real parents), so the DAG provably advances while idle and
///      post-GST peers keep exchanging attestations — at heartbeat frequency,
///      not at check frequency.
///
/// This replaces the old unconditional block-per-tick cadence (which grew the
/// DAG by an empty block every `check_ms` forever). Turn submission itself is
/// NOT gated on this task: the API submits turn blocks directly
/// (`BlocklaceHandle::submit_turn`), so turns commit promptly regardless of
/// the check interval. Disabled when `check_ms == 0` (purely quiescent:
/// blocks only on turn submission).
///
/// `min_block_interval_ms` is the QUIESCENT-ON-DEMAND rate cap on the n>1
/// round-driven path: this node emits at most one block per `min_block_interval_ms`
/// (default 5000), batching turns within the window and closing each wave across
/// a few interval-spaced rounds. It does not gate the solo (n=1) path (which is
/// already mutation-driven) nor turn submission.
fn spawn_block_cadence(
    state: NodeState,
    handle: BlocklaceHandle,
    check_ms: u64,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
) {
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_millis(check_ms));
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        // Skip the immediate first tick so we don't emit a block at t=0 before
        // genesis/state has settled.
        ticker.tick().await;
        info!(
            check_ms,
            idle_heartbeat_ms,
            min_block_interval_ms,
            "block production cadence active (quiescent-on-demand round-disciplined at n>1; \
             mutation-driven at n=1)"
        );

        // CONNECTIVITY GATE (multi-party bootstrap): before producing the FIRST
        // round block, wait until the committee mesh is established (every other
        // member's QUIC link is up) — or a bounded timeout. The round-1 genesis
        // block is eager-pushed ONCE; if a peer's connection is not yet up when we
        // emit it, that peer never receives it (the one-shot push goes to the void)
        // and — under `supermajority == n`, where ALL members' round-1 blocks are
        // required to advance — the cluster deadlocks a round apart at the smallest
        // N, exactly when links are slowest to form. Holding the first block until
        // the mesh is up makes the genesis cohort reliably cross-propagate, so the
        // round-synchronous DAG `tau` finalizes over forms deterministically. After
        // genesis, frontier reconciliation + connection-agnostic fan-out keep it
        // live; this gate only governs the first block.
        {
            let n_participants = {
                let c = handle.constitution.read().await;
                c.current.participant_count()
            };
            if n_participants > 1 {
                let want = n_participants - 1; // links to every other committee member
                let deadline = std::time::Instant::now() + Duration::from_secs(15);
                loop {
                    let connected = handle.gossip.connected_peer_count().await;
                    if connected >= want || std::time::Instant::now() >= deadline {
                        info!(
                            connected,
                            want, "consensus mesh ready (or timed out) — starting round production"
                        );
                        // Announce our frontier so any peer that came up first pulls
                        // whatever it is missing right as we begin producing.
                        handle.send_frontier().await;
                        break;
                    }
                    tokio::time::sleep(Duration::from_millis(200)).await;
                }
            }
        }

        loop {
            ticker.tick().await;

            // VOTE-LAYER ANTI-ENTROPY (every tick): re-emit our finalization
            // votes for blocks still inside their re-emit window. Runs on the
            // frequent cadence tick (not the slow catch-up sweep) so a vote a
            // lossy QUIC link dropped is re-delivered quickly enough for a peer
            // to cross quorum. Quiescent once every pending vote's budget drains.
            handle.reemit_pending_votes().await;

            // The committee size decides the production discipline. At n>1 the
            // Cordial-Miners ordering rule needs the ROUND-SYNCHRONOUS DAG shape,
            // so production is ROUND-DRIVEN — but QUIESCENT-ON-DEMAND: advance a
            // round only when there is something to finalize (a queued turn, a
            // peer's fresh turn, or an open wave still closing), never an empty
            // round per tick, and never faster than `min_block_interval_ms`. At
            // n=1 (solo, scales-to-zero) tau trivially finalizes every block in
            // sequence, so we keep the MUTATION-DRIVEN cadence (no empty-block
            // spam while idle). See `cadence_tick_round_driven` / `produce_round_block`.
            let n_participants = {
                let c = handle.constitution.read().await;
                c.current.participant_count()
            };

            if n_participants > 1 {
                cadence_tick_round_driven(
                    &state,
                    &handle,
                    idle_heartbeat_ms,
                    min_block_interval_ms,
                )
                .await;
            } else {
                cadence_tick_solo(&state, &handle, idle_heartbeat_ms).await;
            }
        }
    });
}

/// ROUND-DRIVEN production tick (the n>1 finality path), QUIESCENT-ON-DEMAND.
///
/// The old tick advanced the local creator by one round EVERY check tick (carrying
/// a queued turn or an empty `Payload::Ack`), so `--block-cadence-ms` was in
/// effect the BLOCK rate: 1000ms spammed one empty block/s, and 5000ms DEADLOCKED
/// (rounds stalled so a faucet turn never finalized). The fix: advance a round
/// ONLY when [`round_cadence_decision`] says there is something to finalize, and
/// never faster than `min_block_interval`:
///
///  * `DrainTurns` — a turn is staged: carry it (genesis or one round forward).
///  * `ReactiveAck` — a peer's fresh non-`Ack` block arrived (the WAKE): advance
///    a round to attest it, which is how a faucet turn wakes the cluster
///    (submitter makes the turn block → peers see it → they advance → the wave
///    fills at supermajority → `tau` finalizes → all go quiet).
///  * `AdvanceWave` — a turn already in the DAG is not yet finalized
///    ([`wave_open`]): keep advancing rounds across the wave boundary until `tau`
///    super-ratifies it (one reactive-ack is not enough — a turn at round `r`
///    needs the cluster to reach the wave's last round).
///  * `IdleHeartbeat` — the DAG is fully finalized but the idle window expired:
///    one low-frequency liveness-floor block (genesis/attestation) so probes and
///    post-GST attestation exchange still advance, then quiet again.
///  * `Nothing` — nothing to finalize (or the rate cap is holding an advance):
///    produce NO block. The DAG goes quiet; rounds stop advancing.
///
/// `produce_round_block` is still supermajority-gated ([`plan_round_block`]), so a
/// node can never outrun the slowest honest member by more than one round; the
/// cluster paces together and fills each round with a supermajority of creators,
/// so waves super-ratify and `tau` finalizes cross-node — now only while there is
/// a turn in flight.
async fn cadence_tick_round_driven(
    state: &NodeState,
    handle: &BlocklaceHandle,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
) {
    // Quiescence inputs (all DAG/queue STATE, so they persist across a held tick —
    // the rate cap can pace an advance but never lose it).
    let queued_turns = handle.pending_payloads.read().await.len();
    // Mempool depth: turns/payloads queued but not yet drained into a block.
    crate::metrics::set_mempool_pending(queued_turns as f64);
    let ack_pending = handle
        .ack_pending
        .load(std::sync::atomic::Ordering::Relaxed);
    let wave_is_open = wave_open(handle).await;
    let since_last_block = handle.last_produced.read().await.elapsed();
    let idle_for = since_last_block;

    // EXECUTION BACKPRESSURE: is there a non-`Ack` block tau has finalized but the
    // finality executor has NOT yet executed? (`wave_open` already covers turns still
    // needing ROUNDS to super-ratify; this is the leftover set — finalized, awaiting
    // local execution.) When the executor lags the producer under load, minting more
    // (idle-heartbeat) rounds only grows the DAG, which makes the executor's
    // O(history) verified poll EVEN slower — a runaway where the chain races dozens of
    // rounds ahead while a finalized turn never commits. So when finalized work is
    // pending execution we STOP producing and instead NUDGE the executor to re-poll:
    // the DAG stops growing, the executor catches up on a now-stable lace, the turn
    // commits, and only then does normal idle production resume. (Notifying is safe —
    // the executor recomputes the full finalized set each poll, so it cannot miss the
    // pending turn, and we do not depend on a fresh block to wake it.)
    let exec_pending = {
        let cursor = handle.cursor.read().await;
        let lace = handle.lace.read().await;
        lace.iter()
            .any(|(id, b)| b.payload != Payload::Ack && !cursor.is_executed(id))
    };

    let mut action = round_cadence_decision(
        queued_turns,
        ack_pending,
        wave_is_open,
        since_last_block,
        Duration::from_millis(min_block_interval_ms),
        idle_for,
        idle_heartbeat_ms,
    );

    // EXECUTION BACKPRESSURE (see `exec_pending` above): if the only thing this tick
    // would do is mint an idle-heartbeat round while a FINALIZED turn is still waiting
    // to execute, hold off — growing the DAG would only slow the executor's catch-up.
    // Nudge it to re-poll and produce nothing. (`DrainTurns`/`ReactiveAck`/`AdvanceWave`
    // are real finalization work and are NOT held — they keep the committee live.)
    if action == CadenceAction::IdleHeartbeat && exec_pending {
        handle.finality_notify.notify_one();
        action = CadenceAction::Nothing;
    }

    // QUIESCENCE: nothing to finalize (or the rate cap is holding) → produce NO
    // block this tick. Rounds stop advancing; the DAG goes quiet. We still
    // announce our frontier below so a lagging peer can catch up cheaply.
    if action == CadenceAction::Nothing {
        handle.send_frontier().await;
        return;
    }

    // We are advancing this round. For `DrainTurns` carry the next staged
    // turn/membership payload; for every other advancing action carry a minimal
    // `Payload::Ack` attestation (the wave-closing/wake step). One payload per
    // round keeps the DAG round-synchronous and drains the backlog at the round
    // cadence.
    let (payload, carried_turn) = if action == CadenceAction::DrainTurns {
        match handle.pending_payloads.write().await.pop_front() {
            Some(p) => (p, true),
            // Raced empty (a concurrent drain): fall back to an attestation so
            // the wake/close still advances the round.
            None => (Payload::Ack, false),
        }
    } else {
        (Payload::Ack, false)
    };

    let advanced = handle.produce_round_block(state, payload.clone()).await;
    match advanced {
        Some(_) => {
            // A peer's freshly-received non-Ack block has now been attested by our
            // round advance — clear the reactive-ack flag (the round block IS the
            // attestation; acks no longer beget separate ack blocks). The open
            // wave (if any) is what carries finalization forward from here, via
            // `wave_open` on the next ticks.
            handle
                .ack_pending
                .store(false, std::sync::atomic::Ordering::Relaxed);
        }
        None => {
            // The round cannot advance yet (we lack a supermajority of DISTINCT
            // creators at our current round). Re-stage any pulled payload so it is
            // carried by the next produced round block.
            if carried_turn {
                handle.pending_payloads.write().await.push_front(payload);
            }
        }
    }

    // Announce our FRONTIER every tick (cheap: one map of tip ids), so peers PUSH
    // any round blocks we are missing (`handle_frontier`) — and so peers missing
    // OUR latest block pull it. At the genesis-strength threshold
    // (`supermajority_threshold(n) == n` for small n: n=3 needs ALL three), round
    // advancement requires gap-free per-round delivery; the one-shot eager push
    // can miss a peer whose QUIC link was not yet up when a block was produced
    // (a bootstrap delivery race), which deadlocks every node a round apart until
    // the slow anti-entropy sweep. Continuous frontier reconciliation drains any
    // such gap within ONE tick, keeping the cluster paced together and live —
    // independent of bootstrap timing.
    handle.send_frontier().await;
}

/// MUTATION-DRIVEN production tick (the n=1 solo path): drain queued turns, answer
/// received peer blocks with one reactive ack, or emit one idle heartbeat per
/// `idle_heartbeat_ms` — never an empty block per check tick. Preserved verbatim
/// from the pre-round-discipline cadence (solo finalizes trivially, no rounds).
async fn cadence_tick_solo(state: &NodeState, handle: &BlocklaceHandle, idle_heartbeat_ms: u64) {
    let queued: Vec<dregg_sdk::SignedTurn> = {
        let mut s = state.write().await;
        std::mem::take(&mut s.consensus_queue)
    };
    let ack_pending = handle
        .ack_pending
        .load(std::sync::atomic::Ordering::Relaxed);
    let idle_for = handle.last_produced.read().await.elapsed();

    match cadence_decision(queued.len(), ack_pending, idle_for, idle_heartbeat_ms) {
        CadenceAction::DrainTurns => {
            let n = queued.len();
            for signed in queued {
                match postcard::to_stdvec(&signed) {
                    Ok(turn_data) => {
                        handle.submit_turn(state, turn_data).await;
                    }
                    Err(e) => {
                        warn!(error = %e, "failed to encode queued turn for block production");
                    }
                }
            }
            debug!(
                turns = n,
                "cadence: produced turn block(s) from consensus queue"
            );
        }
        CadenceAction::ReactiveAck => {
            handle
                .ack_pending
                .store(false, std::sync::atomic::Ordering::Relaxed);
            handle.submit_heartbeat(state).await;
            debug!("cadence: produced reactive ack block for received peer blocks");
        }
        CadenceAction::IdleHeartbeat => {
            handle.submit_heartbeat(state).await;
            debug!(
                idle_heartbeat_ms,
                "cadence: produced idle heartbeat block (no mutations for a full idle window)"
            );
        }
        // The solo decision (`cadence_decision`) never opens a wave (n=1 has no
        // rounds; `tau` finalizes every block in sequence), so `AdvanceWave` is
        // unreachable here — treat it as the closest solo equivalent (a heartbeat
        // attestation) rather than panicking, so the type stays total.
        CadenceAction::AdvanceWave => {
            handle.submit_heartbeat(state).await;
        }
        CadenceAction::Nothing => {}
    }
}

// ─── Catch-up Driver ─────────────────────────────────────────────────────────

/// Spawn the periodic catch-up driver.
///
/// The block-reception path (`handle_push`) already drives catch-up REACTIVELY:
/// out-of-order blocks are buffered and their missing predecessors pulled the
/// moment a gap is seen. This driver is the SAFETY NET for the case where the
/// triggering gossip was itself lost — a node that fell behind while a peer's
/// `Push` never arrived has nothing in its orphan buffer to react to. On a slow
/// timer it (a) re-requests any still-unmet predecessors of buffered orphans (in
/// case the earlier `Pull` was dropped), and (b) when a gap is open, re-announces
/// its frontier so peers recompute and push the delta. Quiescent when fully synced
/// (empty buffer ⇒ a frontier ping at most, and only if `interval_ms > 0`).
/// Spawn the **peer reconnect prober**.
///
/// Federation peer join was ONE-SHOT at startup: `join_topic` dialed each
/// `--federation-peers` address exactly once. A peer that was down at boot was
/// never retried, and a peer whose link dropped never re-dialed — the node
/// silently ran degraded (or solo) until an operator restart. This task closes
/// that gap.
///
/// On a slow tick it asks the gossip layer which known topic peers currently
/// have NO live link ([`GossipNetwork::unconnected_topic_peers`], which already
/// excludes graylisted/Byzantine peers), and re-dials each on a per-peer
/// [`RequestBackoff`] schedule: the first miss re-dials promptly, then the
/// window doubles (capped) so a persistently-down peer is probed politely
/// rather than hammered every tick. When the peer comes up the dial succeeds,
/// the link is registered + the eager/lazy split recomputed
/// ([`GossipNetwork::reconnect_peer`]), and the node converges WITHOUT a
/// restart. A successful (re)connect clears that peer's backoff so a later drop
/// of the same peer starts fresh.
///
/// Re-dialing the blocklace topic's peer set is sufficient to recover the
/// transport link for ALL topics: a QUIC connection is shared across the
/// logical gossip topics, so one restored link carries blocklace + turns +
/// revocations + … again.
fn spawn_peer_prober(handle: BlocklaceHandle, state: NodeState, interval_ms: u64) {
    if interval_ms == 0 {
        info!("peer reconnect prober disabled (interval 0)");
        return;
    }
    tokio::spawn(async move {
        // Per-peer capped exponential backoff: first re-dial after `base`, then
        // doubling to `max`. Wired from `dregg_net::peer_score::RequestBackoff`
        // (the same limiter the missing-block pull path uses).
        let mut backoff: dregg_net::peer_score::RequestBackoff<SocketAddr> =
            dregg_net::peer_score::RequestBackoff::new(
                Duration::from_millis(interval_ms.max(1)),
                Duration::from_secs(30),
            );
        let mut ticker = tokio::time::interval(Duration::from_millis(interval_ms));
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        ticker.tick().await; // skip the immediate tick
        info!(interval_ms, "peer reconnect prober active");
        loop {
            ticker.tick().await;
            // AUTHENTICATED GOSSIP-OF-PEERS: each tick, share the committee
            // addresses we have personally verified so a peer booted with only a
            // partial peer list learns the rest of the mesh transitively. This is
            // the discovery half that pairs with the reconnect half below: the
            // shared addresses become unconnected topic peers on the receiver,
            // which ITS prober then dials — so the mesh forms from a single seed
            // without every node enumerating every peer.
            handle.share_peer_addrs(&state).await;

            let unconnected = handle.gossip.unconnected_topic_peers(&handle.topic).await;
            // Drop backoff state for peers that are no longer candidates (they
            // reconnected, or were graylisted) so memory stays bounded and a
            // later re-drop starts fresh.
            for addr in &unconnected {
                if backoff.should_request(*addr) && handle.gossip.reconnect_peer(*addr).await {
                    info!(peer = %addr, "peer reconnect prober: (re)established link");
                    backoff.clear(addr);
                    crate::metrics::set_federation_peers_connected(
                        handle.gossip.connected_peer_count().await as f64,
                    );
                    // A freshly (re)connected peer wants our frontier so it
                    // pushes whatever we are missing (and vice-versa) — the
                    // same catch-up nudge a fresh boot does.
                    handle.send_frontier().await;
                }
            }
            // Bound the backoff map: forget entries for peers no longer in the
            // unconnected set (now connected) after a generous idle window.
            backoff.gc(Duration::from_secs(120));
        }
    });
}

fn spawn_catchup_driver(handle: BlocklaceHandle, interval_ms: u64) {
    if interval_ms == 0 {
        info!("catch-up driver disabled (interval 0): catch-up is purely reactive");
        return;
    }
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_millis(interval_ms));
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        ticker.tick().await; // skip immediate tick
        info!(interval_ms, "catch-up driver active");
        loop {
            ticker.tick().await;
            let buffered = handle.catchup_tick().await;
            if buffered > 0 {
                debug!(buffered, "catch-up driver: gap still open, requested sync");
            }
            // (Vote re-emission runs on the frequent block-cadence tick — see
            // `spawn_block_cadence` — so a vote dropped by a lossy link is
            // re-delivered promptly enough for a peer to reach quorum.)
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

            // DEBOUNCE/COALESCE: one finality recompute is O(history) — it clones the
            // lace and runs the verified-Lean tau-order FFI twice — and a notification
            // fires on EVERY block this node produces OR receives. Under sustained load
            // that drove back-to-back recomputes that pinned a worker on the FFI and
            // starved everything else (the round-production crawl). A finalization is
            // never time-critical to the millisecond (the rate cap is seconds), so wait
            // a short window and let any notifications that land during it collapse into
            // THIS single poll — `poll_finalized_blocks` already recomputes the whole
            // finalized set, so nothing is missed. Cuts recompute frequency by ~an order
            // of magnitude under load while keeping finality latency well under a round.
            tokio::time::sleep(Duration::from_millis(150)).await;

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

            // Block-level executed COUNT for the durable commit record. Recovery
            // resumes BY IDENTITY (the commit log's `block_id`s ∪ the persisted
            // executed-id set), not from this count — it is carried in each
            // turn's atomic commit as a diagnostic/compat field only (an index
            // into the tau order cannot be a sound resume point: the order can
            // shift under honest catch-up growth, see TauPrefixMonotone).
            let block_executed_up_to = { handle.cursor.read().await.executed_count() as u64 };

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
                            block_executed_up_to,
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

                // ── QUORUM AGREEMENT: emit our signed finalization vote ──────
                // This block is now in our local `tau` order (Ordered, which
                // subsumes Attested). Broadcast a signed vote so the committee
                // can collect 2f+1 distinct signers and declare it
                // consensus-wide Attested. Gate on "have we voted yet" so we
                // emit exactly once per block (n members ⇒ n votes, no storm).
                // Solo (n=1) is a committee of one: quorum=1, so a single self
                // vote is already consensus-attested — correct and inert.
                {
                    let block_id = match block {
                        FinalizedBlock::Turn { block_id, .. }
                        | FinalizedBlock::Membership { block_id, .. }
                        | FinalizedBlock::Checkpoint { block_id, .. } => *block_id,
                    };
                    let already = {
                        let col = handle.votes.read().await;
                        col.has_voted(&block_id, &handle.self_key)
                    };
                    if !already {
                        handle
                            .emit_finalization_vote(
                                block_id,
                                dregg_blocklace::finality::FinalityLevel::Ordered,
                            )
                            .await;
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
            // Save the executed block-id set and blocklace metadata (tips,
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
    block_executed_up_to: u64,
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

    crate::executor_setup::configure_turn_executor(
        &mut executor,
        &s,
        crate::executor_setup::BlockHeightMode::Next,
    );

    // boundary-P1 (bug 1): plumb the NODE-fed admission context onto the per-turn executor so the
    // verified Lean shadow's clock / chain-head / budget legs are decided by THIS node's own state
    // (not the turn). `TurnExecutor::execute` reads these (`get_last_receipt_hash` / `budget_gate`
    // / `cell_migrations`) to build the `ShadowHostCtx`; without seeding they default to genesis /
    // no-gate (the diagnostic stub). Production overrides:
    //   * stored receipt-chain HEAD — the node's authoritative head for the agent. For this node's
    //     own agent it is the cipherclerk receipt chain's last receipt; the verified ChainHead leg
    //     then checks the turn's claimed `prev` against it (a forked turn whose `prev` ≠ the node's
    //     stored head is rejected). (Federated turns from OTHER agents carry their head in the
    //     bundle the node already validated upstream; we seed the local-agent head here, the case
    //     the node maintains independently.)
    //   * silo BUDGET slice — the agent's Stingray bounded-counter remaining slice for this silo;
    //     the verified Budget leg rejects `fee > budget`.
    {
        let agent = signed_turn.turn.agent;
        if let Some(head) = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()) {
            // The local node's authoritative chain head (independent of the turn's claim).
            if agent == crate::executor_setup::local_agent_cell(&s) {
                executor.set_last_receipt_hash(agent, head);
            }
        }
        if let Some(remaining) = s
            .budget_coordinators
            .get(&agent)
            .and_then(|c| c.remaining(&s.silo_id))
        {
            // A gate whose remaining slice = the agent's bounded-counter remaining for THIS silo.
            // The gate's numeric silo tag is a stable u32 fingerprint of the node's SiloId (only an
            // identifier; the load-bearing value is the slice ceiling the verified Budget leg reads).
            let silo_tag =
                u32::from_le_bytes([s.silo_id[0], s.silo_id[1], s.silo_id[2], s.silo_id[3]]);
            let slice = dregg_turn::BudgetSlice::new(remaining);
            executor.set_budget_gate(dregg_turn::BudgetGate::new(silo_tag, slice));
        }
    }

    let new_height = executor.block_height;
    let now = executor.current_timestamp;

    // Full-turn proving (commit-path): capture the actor cell's pre-execution
    // state BEFORE the executor mutates the ledger. The full-turn proof binds
    // `old_commit` to this pre-state; capturing it after execution would let a
    // forged transition pass. Only collected when proving is enabled (devnet).
    let full_turn_pre_state: Option<(u64, u64)> = if s.full_turn_proving_enabled {
        // THE EPOCH: balances are SIGNED (i64); the full-turn VM pre-state is
        // u64. The actor is an ORDINARY cell (non-negative) on the proving
        // path — checked conversion, never an `as` cast that wraps negatives.
        s.ledger
            .get(&signed_turn.turn.agent)
            .map(|cell| {
                (
                    u64::try_from(cell.state.balance()).unwrap_or(0),
                    cell.state.nonce(),
                )
            })
            .or(Some((0, 0)))
    } else {
        None
    };

    // FLOW-B ROTATION: capture the actor cell's FULL pre-execution `Cell` (the real
    // RecordKernelState the rotation producer reads — balance/nonce/fields/c-list/lifecycle/
    // heap_root/authority), so the live node turn can prove ROTATED. Cloned BEFORE
    // `execute_via_producer` mutates the ledger; the post-state cell is read after execution.
    let full_turn_pre_cell: Option<dregg_cell::Cell> = if s.full_turn_proving_enabled {
        s.ledger.get(&signed_turn.turn.agent).cloned()
    } else {
        None
    };

    // AUTHORITY path (cap Phase D): capture the actor cell's CANONICAL
    // pre-execution `capability_root` — the sorted-Poseidon2 root over its
    // c-list (cap Phase A's openable scheme) — in the TWO forms the two legs
    // consume. `full_turn_pre_cap_root` (SCALAR lane-0, `_felt`) seeds the
    // Effect-VM row's `cap_root` column (`CellState::capability_root: BabyBear`,
    // the historical scalar column, with the wide lanes 1..7 carried separately
    // at the rotated extras). `full_turn_pre_cap_root_8` (FULL native 8-felt,
    // `_8`) is the openable membership root the cap-membership leg /
    // `CapMembershipExpectation.cap_root` binds — the ~124-bit faithful root, NOT
    // a lane-0 squeeze. A capability-gated turn's cap-membership leg is bound
    // against THIS root, never one from the receipt/prover. Captured BEFORE
    // execution (effects may mutate the c-list). A missing cell has the canonical
    // EMPTY root.
    let (full_turn_pre_cap_root, full_turn_pre_cap_root_8): (
        dregg_circuit::field::BabyBear,
        [dregg_circuit::field::BabyBear; 8],
    ) = if s.full_turn_proving_enabled {
        s.ledger
            .get(&signed_turn.turn.agent)
            .map(|cell| {
                (
                    dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities),
                    dregg_cell::compute_canonical_capability_root_8(&cell.capabilities).limbs(),
                )
            })
            .unwrap_or_else(|| {
                (
                    dregg_cell::compute_canonical_capability_root_felt(
                        &dregg_cell::CapabilitySet::new(),
                    ),
                    dregg_circuit::cap_root::empty_capability_root().limbs(),
                )
            })
    } else {
        (
            dregg_cell::compute_canonical_capability_root_felt(&dregg_cell::CapabilitySet::new()),
            dregg_circuit::cap_root::empty_capability_root().limbs(),
        )
    };

    // FRESHNESS path: capture the node's CANONICAL spent-nullifier set BEFORE this
    // turn's spend is recorded. A `NoteSpend` turn is proven against THIS set
    // (freshness = "not yet spent"); recording this turn's nullifier first would
    // make its own freshness proof impossible. Empty/Err is fine — a turn with no
    // spend never enters the freshness path.
    let full_turn_previously_spent: Vec<[u8; 32]> = if s.full_turn_proving_enabled {
        s.store
            .load_all_nullifiers()
            .map(|ns| ns.into_iter().map(|n| n.0).collect())
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    // BEARER AUTHORITY path: capture the CANONICAL pre-execution `capability_root`
    // of every cell a bearer (`SignedDelegation`) authorization in this turn names
    // as its DELEGATOR, keyed by the delegator's `CellId`. A bearer-delegated turn
    // (the consumed cap's `holder` is the delegator, not the actor) binds its
    // AUTHORITY leg against THIS root — the delegator's real pre-state c-list — so
    // the leg proves the delegated cap was actually held (not merely that the
    // receipt witness is internally consistent). Captured BEFORE execution: an
    // earlier effect in the same forest could grant/revoke on the delegator, and
    // the authority the bearer exercised was the pre-execution authority. A turn
    // with no bearer authorization yields an empty map (zero cost on the hot path).
    let full_turn_delegator_cap_roots: HashMap<
        dregg_types::CellId,
        [dregg_circuit::field::BabyBear; 8],
    > = if s.full_turn_proving_enabled {
        crate::turn_proving::delegator_pre_state_cap_roots(&signed_turn.turn.call_forest, &s.ledger)
    } else {
        HashMap::new()
    };

    // UNIFORM CROSS-NODE APPLICATION: a finalized Transfer must execute the SAME on
    // every node so each emits the same attested root AND the same ledger content.
    // No node has the destination's pre-image (the recipient's public key is not
    // carried over consensus), so provisioning is driven SOLELY by the finalized
    // turn's data via `provision_transfer_destinations`, which is byte-deterministic:
    // every node inserts the IDENTICAL zero-balance stub for each missing Transfer
    // destination. This is what makes the finalized application provably uniform —
    // not "the submitter created it out of band and peers approximate it" (which
    // would leave divergent cell content the attested root cannot see, since
    // `canonical_ledger_root` commits only `cell.state`). The submitter no longer
    // provisions authoritatively at faucet-submission time in multi-party mode
    // (see `api.rs`), so it reaches this same path and provisions identically.
    // THE SWAP — producer mode (authority inversion), now the DEFAULT — through the ONE
    // shared producer gate every ingress uses (`executor_setup::execute_via_producer`,
    // #171): finalized turns, thin-HTTP turns, and remote signed envelopes all execute
    // on the same authoritative state producer.
    let lean_producer_enabled = s.lean_producer_enabled;

    // ─── A1 FIX — the confirmed n=5 finalization-stall root cause ─────────────
    // The EXECUTION FFI (`dregg_exec_full_forest_auth`, reached through
    // `execute_via_producer`) used to run INLINE on the tokio async worker while
    // this function held the GLOBAL `state.write()` lock (acquired above) for the
    // FFI's ENTIRE duration. At n=5 that pinned the worker AND held the write lock
    // across the whole (slow) FFI, starving the producer / round / super-ratify
    // loop — so `execute_finalized_turn` never completed the promotion and turns
    // never finalized. (The `24dcd0474` wedge fix moved the ORDERING FFI off the
    // worker but left THIS execution FFI inline-under-lock.)
    //
    // Fix: run the FFI on a `spawn_blocking` thread against a CLONE of the
    // pre-state (CLONE-IN), releasing the global write lock for the FFI's whole
    // duration, then re-apply the committed post-state under a BRIEF re-acquired
    // lock as a per-cell OVERLAY of exactly the cells this turn touched. We do NOT
    // wholesale-replace `s.ledger` (that would clobber concurrent writers on OTHER
    // cells — the service inserts / the atomic-coordinator commit). This changes
    // only WHERE/HOW the verified executor runs; the Lean executor stays
    // authoritative and its post-state is installed verbatim.
    let pre_ledger = s.ledger.clone();
    let mut exec_ledger = s.ledger.clone();
    // Every value the remainder of this function needs from the pre-state has
    // already been captured into owned locals above (new_height, now, and the
    // full_turn_* proving snapshots), so releasing the guard here is sound.
    drop(s);

    let turn_for_exec = signed_turn.turn.clone();
    let exec_join = tokio::task::spawn_blocking(move || {
        // Provision Transfer destinations on the CLONE the FFI executes against
        // (byte-deterministic — the identical zero-stub every node inserts). The
        // pre→post diff below classifies each provisioned+credited destination as
        // a created cell, so the overlay installs it on the authoritative ledger.
        provision_transfer_destinations(&mut exec_ledger, &turn_for_exec.call_forest);
        let result = crate::executor_setup::execute_via_producer(
            &executor,
            &turn_for_exec,
            &mut exec_ledger,
            lean_producer_enabled,
        );
        (result, exec_ledger)
    });
    let (exec_result, exec_ledger) = match exec_join.await {
        Ok(v) => v,
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "finalized-turn EXECUTION task panicked/cancelled; turn NOT applied"
            );
            return;
        }
    };

    // The COMPLETE set of cells this turn changed — the full pre→post cell diff.
    // Unlike the executor's `LedgerDelta` (which omits the heap_root / lifecycle /
    // program / vk / delegation dimensions — see `compute_delta_from_journal`), a
    // whole-`Cell` diff captures EVERY committed change, so overlaying it
    // reproduces the exact post-state a re-executing validator computes. `Cell`'s
    // `PartialEq` compares content only (the leaf cache is excluded), so there are
    // no false positives.
    let touched_ids = ledger_touched_diff(&pre_ledger, &exec_ledger);

    // Re-acquire the global write lock BRIEFLY to install the result.
    let mut s = state.write().await;

    // CONCURRENCY GUARD (validate-or-reject, never overwrite). The FFI executed
    // against a snapshot taken while the lock was released. In multi-party mode
    // the other ingress paths only STAGE during this window (the faucet executes
    // against a scratch clone — see `api.rs`; `/turn/atomic` stages a proposal;
    // consensus is the sole authoritative writer), so the touched set is normally
    // untouched by anyone else. If a concurrent path DID write a cell this turn
    // also changed, the snapshot is stale and overlaying it would silently clobber
    // that write — so we DECLINE to install and surface it loudly. The durable
    // commit is then NOT written, so identity-recovery re-applies this turn
    // against fresh state (idempotently) rather than corrupting the live root now.
    let concurrent_conflict = touched_ids
        .iter()
        .any(|id| pre_ledger.get(id) != s.ledger.get(id));
    if concurrent_conflict {
        error!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            "A1 concurrency guard: a concurrent ledger write landed on a cell this \
             finalized turn touched during the off-lock exec window — the execution \
             snapshot is STALE. DECLINING to install (validate-or-reject); the turn \
             re-applies from the durable cursor on restart"
        );
        return;
    }

    // Install the COMPLETE post-state for exactly the touched cells (overlay, not
    // replace): remove+insert so an updated cell's full new content lands verbatim,
    // a created cell is inserted, and a destroyed cell (present pre, absent post)
    // is removed. Concurrent inserts on OTHER cells are left intact.
    for id in &touched_ids {
        match exec_ledger.get(id) {
            Some(cell) => {
                let _ = s.ledger.remove(id);
                let _ = s.ledger.insert_cell(cell.clone());
            }
            None => {
                let _ = s.ledger.remove(id);
            }
        }
    }

    match exec_result {
        dregg_turn::TurnResult::Committed {
            receipt,
            ref ledger_delta,
            ..
        } => {
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

            // FRESHNESS: record this turn's spent note nullifiers into the node's
            // CANONICAL persisted nullifier set, so subsequent turns' freshness
            // proofs are bound against an up-to-date set (and double-spends are
            // rejected). This is the authoritative set
            // `turn_proving::prove_and_verify_finalized_turn_freshness` derives its
            // sorted-Merkle canonical revocation root from. Done AFTER capturing
            // `full_turn_previously_spent` above (this turn's own freshness is
            // proven against the pre-this-turn set).
            {
                let spent: Vec<dregg_turn::Effect> = signed_turn
                    .turn
                    .call_forest
                    .total_effects()
                    .into_iter()
                    .cloned()
                    .collect();
                for nf in crate::turn_proving::spent_nullifiers(&spent) {
                    if let Err(e) = s.store.store_nullifier(&dregg_cell::note::Nullifier(nf)) {
                        warn!(error = %e, "failed to persist spent note nullifier");
                    }
                }
            }

            // Append receipt to cipherclerk. Strict mode: divergence between
            // the local executor and the cipherclerk's chain is a serious
            // bug (the receipt came from our own executor), so we expect.
            s.cclerk
                .append_receipt(receipt.clone())
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");

            // ── Full-turn proving (commit path) ──────────────────────────
            // When enabled (devnet), prove EVERY committed turn and gate
            // acceptance on the proof verifying. This is what makes the public
            // "every state transition is proven" claim TRUE for the running
            // node: the finalized turn produces a real composed STARK proof
            // (Effect-VM AIR over the actor cell's transition), which is then
            // re-verified against the actor cell's pre-state commitment and the
            // proven post-state commitment (verify→accept leg). A turn whose
            // proof does not verify is logged as a serious soundness event and
            // its proof is NOT attached. The proof bytes are persisted keyed by
            // turn hash so any peer / operator can fetch the attached proof.
            //
            // ROUTING BY TRUST MODEL:
            //  - A CAPABILITY-GATED turn (receipt carries an actor-held
            //    `consumed_capabilities` witness, cap Phase C) routes through the
            //    AUTHORITY path (`prove_and_verify_finalized_turn_capability`, cap
            //    Phase D): the consumed cap's leaf is proven a sorted-Merkle member
            //    of the actor's CANONICAL pre-state `capability_root`, and
            //    acceptance is gated on `verify_full_turn_bound` with the cap
            //    expectation pinned (root + leaf teeth). A cap-gated spend keeps
            //    its freshness leg (the nullifier is threaded through).
            //  - A turn that SPENDS a note (carries a `NoteSpend`) routes through
            //    the FRESHNESS path (`prove_and_verify_finalized_turn_freshness`):
            //    non-revocation sub-proof + canonical revocation root pinned, so
            //    the no-double-spend bindings (a)+(b) FIRE.
            //  - Everything else stays on the self-sovereign Effect-VM path (the
            //    correct trust model for an owner-authorized turn).
            //  - A BEARER-delegation turn (a consumed witness whose `holder` is
            //    the DELEGATOR, not the actor) routes through the AUTHORITY path
            //    binding the DELEGATOR's pre-state cap root
            //    (`prove_and_verify_finalized_turn_capability_holder` with
            //    `holder_cap_root = full_turn_delegator_cap_roots[holder]`), so
            //    the authority leg PROVES the delegated cap was really held — the
            //    former soundness residual (proving WITHOUT the authority leg) is
            //    CLOSED.
            // A1 item 4 — the full-turn PROVING FFI below still runs inline under
            // the (now briefly re-acquired) write lock. It is gated on
            // `full_turn_proving_enabled`, which is OFF by default and only ON with
            // `--prove-turns` / `DREGG_PROVE_TURNS=1` (see `main.rs`), so it is OFF
            // the n=5 finalization hot path this fix targets. When proving IS
            // enabled it should get the same `spawn_blocking` + off-lock treatment
            // as the execution FFI above (the named follow-up); a proving validator
            // otherwise re-introduces a per-turn lock hold for the prover's duration.
            let full_turn_proof_attached: Option<Vec<u8>> =
                if let Some((pre_balance, pre_nonce)) = full_turn_pre_state {
                    let effects: Vec<dregg_turn::Effect> = signed_turn
                        .turn
                        .call_forest
                        .total_effects()
                        .into_iter()
                        .cloned()
                        .collect();
                    let spent_nullifiers = crate::turn_proving::spent_nullifiers(&effects);
                    let actor_cap_witness = crate::turn_proving::actor_consumed_cap(
                        &receipt.consumed_capabilities,
                        &signed_turn.turn.agent,
                    );
                    // The bearer witness (holder != actor) + the node-derived
                    // pre-state cap root of its delegator. The actor path takes
                    // precedence (a turn holding its own cap proves over its own
                    // root); only when there is NO actor-held witness do we route
                    // a bearer witness through the delegator-bound authority leg.
                    let bearer_cap = if actor_cap_witness.is_none() {
                        crate::turn_proving::bearer_consumed_cap(
                            &receipt.consumed_capabilities,
                            &signed_turn.turn.agent,
                        )
                    } else {
                        None
                    };
                    let bearer_cap_witness: Option<(
                        &dregg_turn::ConsumedCapWitness,
                        [dregg_circuit::field::BabyBear; 8],
                    )> = bearer_cap.and_then(|w| {
                        match full_turn_delegator_cap_roots.get(&w.holder) {
                            Some(root) => Some((w, *root)),
                            None => {
                                // The delegator was not resolvable in the node's
                                // pre-state ledger (e.g. an anonymous STARK
                                // delegation, which records no concrete holder, or
                                // a delegator absent at pre-state). We cannot bind
                                // a real authority leg, so we keep the v1 fallback
                                // and surface it loudly rather than mint a proof
                                // missing the authority binding.
                                warn!(
                                    turn_hash = %turn_hash_hex,
                                    holder = %w.holder,
                                    "bearer-delegated turn: delegator pre-state cap root \
                                     unavailable (no resolvable delegator cell) — proving \
                                     WITHOUT the AUTHORITY leg (v1 fallback)"
                                );
                                None
                            }
                        }
                    });
                    let proving_result = match (
                        actor_cap_witness,
                        bearer_cap_witness,
                        spent_nullifiers.first(),
                    ) {
                        (Some(consumed), _, spent_nullifier) => {
                            // CAPABILITY-GATED turn → AUTHORITY path (cap Phase D),
                            // freshness leg included when it also spends. FLOW-B (C7 close): build
                            // the per-turn ROTATION producer witnesses from the REAL before/after
                            // cells + the canonical pre-state cap root, so the live capability turn
                            // proves ROTATED and the rotated commit pins fold the REAL authority
                            // digest r23 (NOT a zero-pk stub). The builder's self-validating gate
                            // returns None — graceful v1 fallback — for any turn it cannot faithfully
                            // rotate (e.g. a cap-gated turn that also spends, or a cell whose welded
                            // scalars diverge from the v1 cap pre-state).
                            let rotation = match (
                                full_turn_pre_cell.as_ref(),
                                s.ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_capability(
                                        pre_balance,
                                        pre_nonce,
                                        full_turn_pre_cap_root,
                                        before_cell,
                                        after_cell,
                                        &receipt_hashes,
                                        &effects,
                                    )
                                }
                                _ => None,
                            };
                            // cap-WRITE light-client axis: thread the actor's FULL pre-state cap-tree
                            // write witness bundle (the arity-2 leaf-set + the 7-field c-list +
                            // tombstones) so a write-bearing cap effect (RevokeDelegation REMOVE /
                            // delegate-family INSERT) proves the post-cap-root on the wire. Empty when
                            // the before-cell is unavailable (the authority-only route still proves).
                            let cap_trees = full_turn_pre_cell
                                .as_ref()
                                .map(crate::turn_proving::cap_write_tree_witness)
                                .unwrap_or_default();
                            crate::turn_proving::prove_and_verify_finalized_turn_capability(
                                &signed_turn.turn.agent,
                                pre_balance,
                                pre_nonce,
                                full_turn_pre_cap_root,
                                full_turn_pre_cap_root_8,
                                &effects,
                                computed_hash,
                                consumed,
                                spent_nullifier,
                                &full_turn_previously_spent,
                                rotation,
                                cap_trees,
                                // VK EPOCH (umem flip): the DOMAIN-2 welded producer is ARMED. When the
                                // actor's GENUINE before→after record-kernel projection diff is a
                                // NON-EMPTY single-domain CAPS change, mint the WIDE+UMEM welded cap-open
                                // form (the universal-memory leg BESIDE the 8-felt commit, accepted
                                // ADDITIVELY). An empty / heap-domain / multi-domain diff (incl. the 12
                                // live-only members) yields `None` ⇒ the byte-identical BARE wide leg.
                                match (
                                    full_turn_pre_cell.as_ref(),
                                    s.ledger.get(&signed_turn.turn.agent),
                                ) {
                                    (Some(before_cell), Some(after_cell)) => {
                                        crate::turn_proving::caps_umem_weld_witness(
                                            before_cell,
                                            after_cell,
                                        )
                                    }
                                    _ => None,
                                },
                            )
                        }
                        (None, Some((consumed, holder_cap_root)), spent_nullifier) => {
                            // BEARER-DELEGATION turn → AUTHORITY path bound to the DELEGATOR's
                            // pre-state cap root (the soundness fix). The actor's EffectVm
                            // state-transition leg is seeded from the ACTOR's pre-state cap root
                            // (`full_turn_pre_cap_root`), while the cap-membership leg opens against
                            // the DELEGATOR's pre-state cap root (`holder_cap_root`, node-derived).
                            // So the proof attests "the actor's state evolved correctly AND the
                            // delegated authority it exercised was a real member of the delegator's
                            // c-list." The actor's rotation witness is built from its REAL
                            // before/after cells (same as the self-sovereign / actor-cap arms); when
                            // the gate refuses it, the byte-identical v1 actor leg runs ALONGSIDE the
                            // delegator-bound cap leg. A bearer turn that ALSO spends keeps its
                            // freshness leg (the nullifier is threaded through).
                            let rotation = match (
                                full_turn_pre_cell.as_ref(),
                                s.ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_self_sovereign(
                                        pre_balance,
                                        pre_nonce,
                                        before_cell,
                                        after_cell,
                                        &receipt_hashes,
                                        &effects,
                                    )
                                }
                                _ => None,
                            };
                            crate::turn_proving::prove_and_verify_finalized_turn_capability_holder(
                                &signed_turn.turn.agent,
                                pre_balance,
                                pre_nonce,
                                full_turn_pre_cap_root,
                                holder_cap_root,
                                &effects,
                                computed_hash,
                                consumed,
                                spent_nullifier,
                                &full_turn_previously_spent,
                                rotation,
                                // BEARER path: the cap-tree write witness is the DELEGATOR's c-list
                                // (not the actor's) — the bearer write wrapper is the named fan-out
                                // residual; the authority-only route proves until it lands.
                                Default::default(),
                                // VK EPOCH (umem flip): DOMAIN-2 welded producer ARMED on the bearer arm
                                // too — built from the ACTOR's genuine before→after projection diff (the
                                // producer fails closed to `None` ⇒ bare for any non-single-caps diff).
                                match (
                                    full_turn_pre_cell.as_ref(),
                                    s.ledger.get(&signed_turn.turn.agent),
                                ) {
                                    (Some(before_cell), Some(after_cell)) => {
                                        crate::turn_proving::caps_umem_weld_witness(
                                            before_cell,
                                            after_cell,
                                        )
                                    }
                                    _ => None,
                                },
                            )
                        }
                        (None, None, Some(spent_nullifier)) => {
                            // SPEND turn → freshness path (bound verify). FLOW-B (C4 close): unlike
                            // the sibling arms, this path builds the per-turn ROTATION producer
                            // witnesses INTERNALLY (from the cap-less synthetic actor cell — the
                            // SAME pre-state the v1 leg proves over), so a single-spend NoteSpend
                            // turn proves ROTATED through `noteSpendVmDescriptor2R24`, which pins the
                            // spent nullifier at PI[38] (`EffectVmEmitRotationV3.noteSpendV3`). The
                            // no-double-spend binding survives the rotation (`verify_full_turn` step
                            // 8 reads PI[38]); a multi-spend turn keeps the v1 leg (the rotated
                            // generator's single-spend gate refuses it, where a 2nd distinct
                            // nullifier is UNSAT). Under `not(recursion)` the byte-identical v1 leg
                            // runs (the present rotation witness is ignored).
                            crate::turn_proving::prove_and_verify_finalized_turn_freshness(
                                &signed_turn.turn.agent,
                                pre_balance,
                                pre_nonce,
                                &effects,
                                computed_hash,
                                spent_nullifier,
                                &full_turn_previously_spent,
                            )
                        }
                        (None, None, None) => {
                            // Non-spend turn → self-sovereign Effect-VM path. FLOW-B: build the
                            // per-turn ROTATION producer witnesses from the REAL before/after
                            // cells so the live node turn proves ROTATED (the builder's
                            // self-validating gate returns None for cells the synthetic
                            // cap-less pre-state cannot represent, falling back to v1).
                            let rotation = match (
                                full_turn_pre_cell.as_ref(),
                                s.ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_self_sovereign(
                                        pre_balance,
                                        pre_nonce,
                                        before_cell,
                                        after_cell,
                                        &receipt_hashes,
                                        &effects,
                                    )
                                }
                                _ => None,
                            };
                            crate::turn_proving::prove_and_verify_finalized_turn(
                                &signed_turn.turn.agent,
                                pre_balance,
                                pre_nonce,
                                &effects,
                                computed_hash,
                                rotation,
                            )
                        }
                    };
                    let is_spend = !spent_nullifiers.is_empty();
                    match proving_result {
                        Ok(proven) => {
                            let proof_bytes = proven.proof_bytes().to_vec();
                            let key = crate::turn_proving::turn_proof_config_key(&turn_hash_hex);
                            if let Err(e) = s.store.set_config(&key, &proof_bytes) {
                                warn!(error = %e, turn_hash = %turn_hash_hex,
                                    "failed to persist full-turn proof");
                            }
                            info!(
                                turn_hash = %turn_hash_hex,
                                block_id = %block_id,
                                proof_bytes = proof_bytes.len(),
                                old_commit = ?proven.old_commit,
                                new_commit = ?proven.new_commit,
                                spend = is_spend,
                                freshness_bound = is_spend,
                                "full-turn proof generated and verified (commit path); \
                                 spend turns are FRESHNESS-bound to the canonical revocation root"
                            );
                            Some(proof_bytes)
                        }
                        Err(
                            crate::turn_proving::FullTurnProvingError::RevocationCapacityExceeded {
                                have,
                                max,
                            },
                        ) => {
                            // KNOWN LIMITATION (not a soundness failure): the canonical
                            // nullifier set outgrew the fixed-depth non-revocation circuit.
                            // We do not silently truncate the set (that could hide a
                            // double-spend), so the spend turn carries no freshness-bound
                            // proof until a depth-parameterized non-revocation AIR lands.
                            warn!(
                                turn_hash = %turn_hash_hex,
                                block_id = %block_id,
                                have,
                                max,
                                "spend turn NOT freshness-proven: canonical nullifier set exceeds \
                                 the non-revocation circuit capacity (needs a deeper AIR); turn \
                                 committed without a freshness-bound proof"
                            );
                            None
                        }
                        Err(e) => {
                            // SOUNDNESS: a committed turn whose full-turn proof
                            // does not verify is a serious event. We surface it
                            // loudly and refuse to attach an unverified proof.
                            error!(
                                turn_hash = %turn_hash_hex,
                                block_id = %block_id,
                                error = %e,
                                spend = is_spend,
                                "full-turn proof generation/verification FAILED; \
                                 turn committed but carries NO verified proof"
                            );
                            None
                        }
                    }
                } else {
                    None
                };

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
            // ledger's canonical bytes. When full-turn proving is enabled
            // (devnet) the committed turn ALSO carries a real, re-verified
            // full-turn STARK proof (see `full_turn_proof_attached` above);
            // the note-tree Poseidon2 root binding remains threaded separately.
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
            let local_pk = s.cclerk.public_key();
            let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
            let sig = dregg_types::sign(&signing_key, &signing_msg);
            // In solo / single-validator mode our signature alone meets the
            // threshold (threshold defaults to 1 if the genesis-declared value
            // is zero), so the persisted root is a genuine quorum and the node
            // restarts cleanly.
            //
            // ⚠ FULL-MODE COMMITTEE RESTART HOLE (caught by the N3 live run).
            // In full mode this pushes ONLY the local signature (1 < threshold),
            // so the persisted `quorum_signatures` do NOT carry a committee
            // quorum. On restart `verify_signed_anchor_and_rollback` (state.rs)
            // calls `StoredAttestedRoot::verify_signatures`, which requires
            // `quorum_signatures.len() >= threshold` valid committee signatures
            // over THIS root's `signing_message()`. A full-mode committee node
            // therefore fail-closes after finalizing >=1 height. The recovery
            // anchor is CORRECT hardening; the persistence under-feeds it.
            //
            // This is NOT a plumbing gap (the earlier "peer aggregation occurs
            // in a follow-up commit" note was wrong). The only cross-node
            // committee quorum that forms is the `FinalizationVote` set
            // (finalization_votes.rs), which:
            //   (a) signs `VOTE_DOMAIN || block_id || level` — NOT this root's
            //       merkle_root-binding `signing_message()`;
            //   (b) is collected ASYNC, AFTER this synchronous persist (peer
            //       votes arrive later over gossip; the local node has not even
            //       emitted its own vote yet at this point — see the
            //       `emit_finalization_vote` call after `execute_finalized_turn`);
            //   (c) is retained by `VoteCollector` as distinct-signer KEY sets
            //       only — the signature bytes are discarded after counting.
            // And `signing_message()` binds a wall-clock `timestamp`
            // (executor_setup sets it via `wall_clock_secs()`), so committee
            // peers cannot even produce matching signatures over this root.
            //
            // Closing this SOUNDLY (without weakening the anchor) requires a
            // protocol addition: a DETERMINISTIC attested root (drop the
            // wall-clock timestamp from the signed preimage / derive it from
            // the finalized block) plus a signed-gossip exchange of committee
            // signatures over the root, aggregated to >=threshold and threaded
            // here — OR extending `FinalizationVote` to bind the finalized
            // merkle_root, retaining those sigs, and persisting the root once
            // its quorum assembles. Both are consensus-visible and carry an
            // async-window liveness decision (this synchronous commit cannot
            // block on network gossip). Diagnosis pinned by
            // `dregg_persist::tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`.
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

            // ── DURABLE, CRASH-CONSISTENT COMMIT (single atomic boundary) ────
            // Record this finalized turn in the durable commit log + index in ONE
            // redb transaction (one fsync boundary): the per-turn record, the
            // commit-cursor advance, the block-level resume cursor, and every
            // secondary index entry (receipt-by-hash, turn-by-hash,
            // turn-by-(height,creator), cell-by-id) all land together or not at
            // all. This is what makes recovery converge to a CONSISTENT
            // checkpoint with no torn state, no lost finalized turn, and no
            // double-apply: the cursor is advanced only here, atomically with the
            // record it counts. See `dregg_persist::commit_log`.
            //
            // The touched-cell post-states are read from the just-committed
            // ledger for exactly the cell ids the executor reported in
            // `ledger_delta` (created ∪ updated ∪ computron_transfer endpoints) —
            // the authoritative, complete, bounded set of cells this turn
            // mutated. The cell-by-id index is therefore the durable
            // last-writer-wins overlay on top of the periodic full ledger
            // checkpoint, and recovery reconstructs the finalized ledger from
            // (checkpoint ⊕ overlay) without re-executing.
            {
                let touched_ids = touched_cell_ids(ledger_delta);
                let mut touched_cells: Vec<dregg_cell::Cell> =
                    Vec::with_capacity(touched_ids.len());
                for id in &touched_ids {
                    if let Some(cell) = s.ledger.get(id) {
                        touched_cells.push(cell.clone());
                    }
                    // A touched id absent post-commit means the cell was
                    // destroyed this turn; its removal is reflected by the
                    // checkpoint, and the overlay carries no stale entry.
                }
                let commit_record = dregg_persist::CommitRecord {
                    ordinal: 0, // assigned by the store at the durable cursor
                    height: new_height,
                    block_id: block_id.0,
                    turn_hash: computed_hash,
                    creator: *signed_turn.turn.agent.as_bytes(),
                    receipt_hash: receipt.receipt_hash(),
                    ledger_root: merkle_root,
                    block_executed_up_to,
                    touched_cells,
                };
                let expected_ordinal = s.store.commit_cursor().unwrap_or(0);
                match s
                    .store
                    .commit_finalized_turn(expected_ordinal, &commit_record)
                {
                    Ok(assigned) => {
                        debug!(
                            turn_hash = %turn_hash_hex,
                            ordinal = assigned,
                            block_executed_up_to,
                            "durable commit-log record written (atomic; index updated)"
                        );
                        // pg-dregg M2: ship this verified turn to the postgres
                        // mirror (opt-in; no-op unless DREGG_PG_MIRROR_URL is set).
                        // The record carries its durable ordinal now.
                        let mirrored = dregg_persist::CommitRecord {
                            ordinal: assigned,
                            ..commit_record.clone()
                        };
                        s.mirror_committed_record(&mirrored);
                    }
                    Err(e) => {
                        // A failed durable commit is a serious crash-consistency
                        // event: the ledger was mutated in RAM but the durable
                        // record/cursor did not advance. We surface it loudly; the
                        // in-RAM cursor has this block marked executed, but its
                        // `block_id` is NOT in the durable commit log, so identity
                        // recovery drops it from the restored executed set and
                        // re-applies this turn idempotently after a restart.
                        error!(
                            turn_hash = %turn_hash_hex,
                            error = %e,
                            "DURABLE commit-log write FAILED; turn applied in RAM but not durably \
                             recorded — recovery will re-apply from the durable cursor"
                        );
                    }
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
                full_turn_proven = full_turn_proof_attached.is_some(),
                "finalized turn executed (blocklace consensus)"
            );
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // boundary-P1 (bug 2): a turn whose ADMISSION PROLOGUE committed (fee debited + nonce
            // ticked, anti-DoS, never rolled back) but whose BODY then FAILED lands HERE — it is
            // `Rejected`, NOT `Committed`. Only the `Committed` arm above appends the receipt,
            // resolves pending turns, and proves; this arm does none of those, so a
            // prologue-committed-body-failed turn is NEVER treated as an accepted/committed turn
            // (the fee was charged purely as anti-spam). This mirrors the Lean export's three-way
            // status: `PrologueCommittedBodyFailed` (status:1, ok:0) maps to this rejection, while
            // `BodyCommitted` (status:2, ok:1) maps to the `Committed` arm. The verified Lean
            // shadow (`decode_shadow_verdict`) reports `committed` ONLY for `BodyCommitted`, so the
            // RUST↔LEAN divergence check agrees with this acceptance gate.
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                reason = %reason,
                "finalized turn rejected (prologue fee may have been charged as anti-spam; turn NOT accepted)"
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
            consumed_capabilities: vec![],
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

    /// Regression: the gossip-layer node identity and EVERY `peer_keys`
    /// registry entry must be derived as `blake3(public_key)`. If the local
    /// gossip `node_id` were the QUIC transport id (`blake3(tls_cert)`, random
    /// per boot) while the registry is keyed by `blake3(public_key)`, peers
    /// reject all of our envelopes as "unknown sender" and a multi-node devnet
    /// never finalizes (`latest_height` stuck at 0). This pins the derivation
    /// that `run_blocklace_sync` uses for both `node_id` and `peer_keys_map`.
    #[test]
    fn gossip_node_id_and_peer_registry_agree_on_federation_derivation() {
        // Three federation validator keys (as they arrive from genesis).
        let validator_keys: Vec<dregg_types::PublicKey> = (0u8..3)
            .map(|i| {
                let sk = ed25519_dalek::SigningKey::from_bytes(&[i + 1; 32]);
                dregg_types::PublicKey(sk.verifying_key().to_bytes())
            })
            .collect();

        // Pick one as "ours".
        let our_public_key = validator_keys[0];

        // Local gossip identity — exactly as run_blocklace_sync computes it.
        let node_id: [u8; 32] = *blake3::hash(our_public_key.as_bytes()).as_bytes();

        // Build the registry exactly as `peer_keys_map` does.
        let mut peer_keys: std::collections::HashMap<[u8; 32], dregg_types::PublicKey> =
            std::collections::HashMap::new();
        for fed_key in &validator_keys {
            peer_keys.insert(*blake3::hash(fed_key.as_bytes()).as_bytes(), *fed_key);
        }
        peer_keys.insert(node_id, our_public_key);

        // Our own gossip id resolves to our key (self-loop / anti-entropy).
        assert_eq!(peer_keys.get(&node_id), Some(&our_public_key));

        // Every peer's gossip id (= blake3(their pubkey), the sender they stamp)
        // resolves to that peer's verifying key — so signature checks pass
        // instead of being dropped as "unknown sender".
        for fed_key in &validator_keys {
            let peer_gossip_id: [u8; 32] = *blake3::hash(fed_key.as_bytes()).as_bytes();
            assert_eq!(
                peer_keys.get(&peer_gossip_id),
                Some(fed_key),
                "every federation member's gossip sender id must resolve in the registry"
            );
        }

        // A QUIC-transport-style id (random TLS-cert hash) is correctly unknown.
        let transport_style_id: [u8; 32] = [0x7c; 32];
        assert!(!peer_keys.contains_key(&transport_style_id));
    }

    // ── Block-production cadence: mutation-driven, no empty-block spam ──────

    /// THE idle pin: an idle node (no queued turns, no acks owed) produces at
    /// most ⌊elapsed / idle_heartbeat⌋ blocks — NOT one per check tick. This is
    /// the regression test for the 2s-empty-block-spam behavior (which grew the
    /// DAG 25→59 overnight with one real turn: ~one block per tick, i.e. 300
    /// blocks over the 10 virtual minutes simulated here instead of 5).
    #[test]
    fn idle_interval_produces_at_most_heartbeat_blocks() {
        let check_ms: u64 = 2_000;
        let idle_heartbeat_ms: u64 = 120_000;
        let total_ms: u64 = 600_000; // 10 idle minutes
        let ticks = total_ms / check_ms;

        let mut idle_for_ms: u64 = 0;
        let mut blocks_produced = 0u64;
        for _ in 0..ticks {
            idle_for_ms += check_ms;
            match cadence_decision(
                0,
                false,
                Duration::from_millis(idle_for_ms),
                idle_heartbeat_ms,
            ) {
                CadenceAction::IdleHeartbeat => {
                    blocks_produced += 1;
                    idle_for_ms = 0; // producing a block resets last_produced
                }
                CadenceAction::Nothing => {}
                other => panic!("idle tick must never produce {other:?}"),
            }
        }

        assert_eq!(
            blocks_produced,
            total_ms / idle_heartbeat_ms,
            "idle production = exactly one heartbeat per idle window"
        );
        assert!(
            blocks_produced <= total_ms / idle_heartbeat_ms,
            "no-empty-block-spam: idle interval ⇒ ≤ ⌊elapsed/heartbeat⌋ blocks"
        );
    }

    /// Queued turns drain on the very next check tick — and take priority over
    /// both the reactive ack and the idle heartbeat (turns commit promptly).
    #[test]
    fn queued_turns_drain_on_next_tick() {
        // Fresh mutation, nothing else pending.
        assert_eq!(
            cadence_decision(3, false, Duration::from_millis(0), 120_000),
            CadenceAction::DrainTurns
        );
        // Turns win even when an ack is owed and the idle window expired.
        assert_eq!(
            cadence_decision(1, true, Duration::from_secs(3_600), 120_000),
            CadenceAction::DrainTurns
        );
        // Turns drain even when the idle heartbeat is disabled.
        assert_eq!(
            cadence_decision(1, false, Duration::from_millis(0), 0),
            CadenceAction::DrainTurns
        );
    }

    /// A received peer turn block is a mutation: it is answered with one
    /// reactive ack block promptly (next tick), not deferred to the heartbeat.
    #[test]
    fn received_peer_blocks_get_prompt_reactive_ack() {
        assert_eq!(
            cadence_decision(0, true, Duration::from_millis(0), 120_000),
            CadenceAction::ReactiveAck
        );
        // Reactive ack also fires when idle heartbeats are disabled —
        // attestation is mutation-driven, not heartbeat-driven.
        assert_eq!(
            cadence_decision(0, true, Duration::from_millis(0), 0),
            CadenceAction::ReactiveAck
        );
    }

    /// Nothing pending + window not expired ⇒ NO block. (The old cadence
    /// produced a heartbeat here unconditionally.)
    #[test]
    fn quiet_tick_produces_no_block() {
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(2_000), 120_000),
            CadenceAction::Nothing
        );
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(119_999), 120_000),
            CadenceAction::Nothing
        );
        // idle_heartbeat_ms == 0 disables the idle heartbeat entirely.
        assert_eq!(
            cadence_decision(0, false, Duration::from_secs(86_400), 0),
            CadenceAction::Nothing
        );
    }

    /// The idle heartbeat fires exactly at window expiry (liveness floor: the
    /// DAG still provably advances while idle, for finality probes + post-GST
    /// attestation exchange).
    #[test]
    fn idle_heartbeat_fires_at_window_expiry() {
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(120_000), 120_000),
            CadenceAction::IdleHeartbeat
        );
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(500_000), 120_000),
            CadenceAction::IdleHeartbeat
        );
    }

    // ── Round-driven (n>1) cadence: QUIESCENT-ON-DEMAND + the ≥5s rate cap ──
    //
    // These pin the consensus-liveness properties of `round_cadence_decision`
    // WITHOUT a running node: (1) an idle, fully-finalized DAG produces no block
    // (no empty-round spam — the 1000ms→1block/s failure); (2) a queued turn, a
    // peer's fresh turn, or an open wave each WAKE the round (the 5000ms→deadlock
    // failure, where a faucet turn never finalized); (3) the min-block-interval
    // caps THIS node to ≤ one block per window but NEVER drops an advance (the
    // wake condition persists, so the held round fires the next eligible tick and
    // the wave still closes — slower, not never).

    const MIN_IVL: Duration = Duration::from_millis(5_000);
    const RECENT: Duration = Duration::from_millis(1_000); // < MIN_IVL: cap holds
    const ELAPSED: Duration = Duration::from_millis(6_000); // ≥ MIN_IVL: cap clear

    /// THE quiescence pin: idle (no queued turn, no ack owed, NO open wave) and
    /// inside the idle window ⇒ NO block. Rounds stop advancing; the DAG goes
    /// quiet. This is the fix for the round-driven path emitting an empty round
    /// every check tick (1000ms → 1 block/s of empty-DAG spam at n>1).
    #[test]
    fn round_idle_with_no_open_wave_produces_no_block() {
        assert_eq!(
            round_cadence_decision(
                0,
                false,
                false,
                ELAPSED,
                MIN_IVL,
                Duration::from_millis(2_000),
                120_000,
            ),
            CadenceAction::Nothing,
            "idle + finalized DAG must produce NO round (quiescence)"
        );
        // Even with the rate cap clear, an empty DAG stays quiet.
        assert_eq!(
            round_cadence_decision(0, false, false, ELAPSED, MIN_IVL, ELAPSED, 0),
            CadenceAction::Nothing
        );
    }

    /// A queued turn WAKES the round (DrainTurns) — and takes priority over the
    /// reactive ack and the wave-close, as long as the rate cap is clear.
    #[test]
    fn round_queued_turn_drains_when_cap_clear() {
        assert_eq!(
            round_cadence_decision(2, false, false, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::DrainTurns
        );
        assert_eq!(
            round_cadence_decision(1, true, true, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::DrainTurns,
            "a queued turn outranks both ack_pending and wave_open"
        );
    }

    /// A peer's fresh non-Ack block (ack_pending) WAKES the round with a reactive
    /// ack — this is how a faucet turn wakes the cluster (submitter posts the turn
    /// block, peers see it, peers advance their rounds to attest it).
    #[test]
    fn round_peer_turn_wakes_reactive_ack() {
        assert_eq!(
            round_cadence_decision(0, true, false, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::ReactiveAck
        );
        // ack_pending outranks a still-open wave (attest the fresh block first).
        assert_eq!(
            round_cadence_decision(0, true, true, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::ReactiveAck
        );
    }

    /// An open wave (a turn in the DAG that `tau` has not yet finalized) keeps the
    /// round advancing across the wave boundary until super-ratification — even
    /// after the one-shot reactive-ack is spent. This is the anti-deadlock tooth:
    /// the cluster must keep closing the wave, not stall after a single attestation.
    #[test]
    fn round_open_wave_keeps_advancing() {
        assert_eq!(
            round_cadence_decision(0, false, true, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::AdvanceWave
        );
        // Open wave wins even when the idle window has expired (finalization
        // beats the idle heartbeat — close the live turn, do not just heartbeat).
        assert_eq!(
            round_cadence_decision(
                0,
                false,
                true,
                ELAPSED,
                MIN_IVL,
                Duration::from_secs(86_400),
                120_000,
            ),
            CadenceAction::AdvanceWave
        );
    }

    /// THE rate-cap pin: while the node produced a block < min_block_interval ago,
    /// every advance-producing decision is HELD to Nothing — so even under
    /// sustained turn load the node emits ≤ one block per window (ember's ≤1
    /// block/5s bound). Applies uniformly to DrainTurns / ReactiveAck / AdvanceWave.
    #[test]
    fn round_rate_cap_holds_advance_within_min_interval() {
        for (q, ack, wave) in [(3, false, false), (0, true, false), (0, false, true)] {
            assert_eq!(
                round_cadence_decision(q, ack, wave, RECENT, MIN_IVL, RECENT, 120_000),
                CadenceAction::Nothing,
                "advance (q={q} ack={ack} wave={wave}) must be HELD within the rate cap"
            );
        }
    }

    /// The cap holds but NEVER drops the advance: the wake condition is DAG/queue
    /// state, so as soon as the interval elapses the held advance fires. (This is
    /// why the cap cannot deadlock finality — it paces, it does not lose work.)
    #[test]
    fn round_rate_cap_releases_held_advance_after_interval() {
        // A queued turn HELD at t=1s since the last block (cap not yet cleared)…
        assert_eq!(
            round_cadence_decision(1, false, true, RECENT, MIN_IVL, RECENT, 120_000),
            CadenceAction::Nothing,
            "advance held while inside the rate-cap window"
        );
        // …released at exactly the interval boundary, SAME persisted wake state
        // (the queued turn never went away — the cap paces, it does not drop work).
        assert_eq!(
            round_cadence_decision(1, false, true, MIN_IVL, MIN_IVL, MIN_IVL, 120_000),
            CadenceAction::DrainTurns
        );
        // And an open wave that was held closes once the interval clears.
        assert_eq!(
            round_cadence_decision(0, false, true, RECENT, MIN_IVL, RECENT, 120_000),
            CadenceAction::Nothing
        );
        assert_eq!(
            round_cadence_decision(0, false, true, ELAPSED, MIN_IVL, ELAPSED, 120_000),
            CadenceAction::AdvanceWave
        );
    }

    /// The idle heartbeat is EXEMPT from the min-interval cap (it is already a
    /// low-frequency floor, idle_heartbeat_ms ≫ min_block_interval): a fully
    /// finalized DAG past the idle window heartbeats even if the last block was
    /// recent. Disabling the heartbeat (0) keeps it quiet.
    #[test]
    fn round_idle_heartbeat_is_exempt_from_rate_cap() {
        assert_eq!(
            round_cadence_decision(
                0,
                false,
                false,
                RECENT,
                MIN_IVL,
                Duration::from_secs(200),
                120_000
            ),
            CadenceAction::IdleHeartbeat
        );
        assert_eq!(
            round_cadence_decision(
                0,
                false,
                false,
                RECENT,
                MIN_IVL,
                Duration::from_secs(200),
                0
            ),
            CadenceAction::Nothing,
            "idle_heartbeat_ms == 0 disables the liveness floor"
        );
    }

    /// END-TO-END (pure model): a turn enters the DAG, and under the ≥5s rate cap
    /// the round-driven decision keeps advancing — one block per window — until
    /// the wave closes, THEN goes quiet. This is the finality-preserved property
    /// at the decision layer: the rate cap slows finality but the turn DOES
    /// finalize (no deadlock), and after closure the DAG produces NO further block.
    #[test]
    fn round_turn_finalizes_under_rate_cap_then_quiesces() {
        // Model: a turn lands at round r; the cluster must advance K wave-closing
        // rounds for `tau` to super-ratify it. Each produced block resets the
        // "since last block" clock; the check tick is faster than the cap, so most
        // ticks are HELD and exactly one block is produced per min-interval window.
        let check = Duration::from_millis(1_000);
        let rounds_to_close: u32 = 5; // r → wave boundary + ratifying wave
        let mut rounds_done: u32 = 0;
        let mut since_last = MIN_IVL; // first tick is eligible
        let mut ticks = 0u32;
        let mut produced_total = 0u32;

        // The wave is open until we have produced `rounds_to_close` advancing
        // blocks; one queued turn carried by the first, attestations after.
        while rounds_done < rounds_to_close {
            ticks += 1;
            assert!(
                ticks < 1_000,
                "must finalize in bounded ticks (no deadlock)"
            );
            let queued = if rounds_done == 0 { 1 } else { 0 };
            let wave_open = true; // turn not yet finalized
            let action = round_cadence_decision(
                queued, false, wave_open, since_last, MIN_IVL, since_last, 120_000,
            );
            match action {
                CadenceAction::Nothing => {
                    since_last += check; // cap holding; clock advances toward release
                }
                CadenceAction::DrainTurns | CadenceAction::AdvanceWave => {
                    // RATE-CAP INVARIANT: never produce within the cap window.
                    assert!(
                        since_last >= MIN_IVL,
                        "produced a block within the rate cap (since_last={since_last:?})"
                    );
                    rounds_done += 1;
                    produced_total += 1;
                    since_last = check; // just produced; clock restarts
                }
                other => panic!("unexpected wave-closing action {other:?}"),
            }
        }

        // The turn FINALIZED: every wave-closing round was produced…
        assert_eq!(produced_total, rounds_to_close, "the wave closed");
        // …across at least (rounds-1) full rate-cap windows of holding ticks
        // (slower finality, the accepted tradeoff — not a deadlock).
        assert!(
            ticks > rounds_to_close,
            "the rate cap spaced the wave-closing rounds out over time"
        );

        // QUIESCENCE AFTER CLOSURE: with the wave now closed (wave_open=false) and
        // nothing queued, the next ticks produce NO block — the DAG is quiet.
        for _ in 0..10 {
            assert_eq!(
                round_cadence_decision(
                    0,
                    false,
                    false,
                    ELAPSED,
                    MIN_IVL,
                    Duration::from_millis(0),
                    120_000
                ),
                CadenceAction::Nothing,
                "after the wave closed the DAG must go quiet (no empty-round spam)"
            );
        }
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

    // ── Distributed witness path: gossip → materialize → aggregate + verify ──

    /// Build a real two-cell transfer Turn (alice → bob).
    fn aggregate_test_turn(
        alice: dregg_types::CellId,
        bob: dregg_types::CellId,
        amount: u64,
        nonce: u64,
    ) -> dregg_turn::Turn {
        let mut builder = dregg_turn::TurnBuilder::new(alice, nonce);
        let action = dregg_turn::ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, amount)
            .build();
        builder.add_action(action);
        builder.fee(0).build()
    }

    /// Fabricate a per-cell scope-2 WitnessedReceipt whose PI is projected from
    /// the canonical Turn's bilateral schedule, bound to a SHARED committed
    /// receipt (so `materialize_blocklace_artifacts` accepts it via
    /// receipt-hash binding). Mirrors the executor's `populate_pi` discipline
    /// and the aggregate prover's own `fabricate_wr` test helper.
    fn aggregate_test_wr(
        turn: &dregg_turn::Turn,
        cell_id: &dregg_types::CellId,
        receipt: &dregg_turn::TurnReceipt,
    ) -> dregg_turn::WitnessedReceipt {
        use dregg_circuit::effect_vm::pi as p;
        use dregg_turn::bilateral_schedule::{ExpectedBilateral, project_into_pi};

        let sched = ExpectedBilateral::from_turn(turn);
        let counts = sched.counts_for(cell_id);
        let roots = sched.roots_for(cell_id, turn.nonce);

        // ACTIVE_BASE_COUNT (PI v3): the verifier refuses < 204; the v3 tail
        // (committed_height + caveat tags) rides as zeros in this synthetic WR.
        let mut pi_bb = vec![BabyBear::ZERO; p::ACTIVE_BASE_COUNT];
        let (th, eg, _, prev) = dregg_turn::TurnExecutor::compute_turn_identity_pi(turn);
        pi_bb[p::TURN_HASH_BASE..p::TURN_HASH_BASE + p::TURN_HASH_LEN]
            .copy_from_slice(&th[..p::TURN_HASH_LEN]);
        pi_bb
            [p::EFFECTS_HASH_GLOBAL_BASE..p::EFFECTS_HASH_GLOBAL_BASE + p::EFFECTS_HASH_GLOBAL_LEN]
            .copy_from_slice(&eg[..p::EFFECTS_HASH_GLOBAL_LEN]);
        pi_bb[p::PREVIOUS_RECEIPT_HASH_BASE
            ..p::PREVIOUS_RECEIPT_HASH_BASE + p::PREVIOUS_RECEIPT_HASH_LEN]
            .copy_from_slice(&prev[..p::PREVIOUS_RECEIPT_HASH_LEN]);
        pi_bb[p::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
        project_into_pi(&mut pi_bb, &counts, &roots);
        pi_bb[p::IS_AGENT_CELL] = if cell_id == &turn.agent {
            BabyBear::new(1)
        } else {
            BabyBear::ZERO
        };
        let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();
        let trace = vec![vec![
            BabyBear::ZERO;
            dregg_circuit::effect_vm::EFFECT_VM_WIDTH
        ]];
        dregg_turn::WitnessedReceipt::from_components(
            receipt.clone(),
            Vec::new(),
            pi_u32,
            Some(&trace),
        )
    }

    /// End-to-end distributed witness path:
    ///   1. Two per-cell WitnessedReceipts are produced INDEPENDENTLY (one per
    ///      cell), each encoded to wire artifact bytes and wrapped in a
    ///      `TurnArtifactBundle` — the exact shape the production submit path
    ///      now gossips via `submit_turn_bundle`.
    ///   2. Each bundle is fed through `materialize_blocklace_artifacts` — the
    ///      gossip-RECEIVE path — which validates receipt-hash binding +
    ///      scope-2 witness requirement and stores the WR. Decoding from
    ///      artifact bytes is what makes these genuinely cross-sourced (not the
    ///      single-call self-prove the MCP tool does).
    ///   3. The two materialized WRs are pulled back out of node state and run
    ///      through the REAL aggregate (`prove_aggregated_bundle` +
    ///      `verify_aggregated_bundle`).
    ///
    /// Honest residual: a true multi-node gossip exchange needs >= 2 live
    /// nodes, which this single-process test cannot spin up; per the brief we
    /// exercise the materialize + aggregate steps directly with two
    /// independently-built, artifact-byte-roundtripped WitnessedReceipts.
    #[tokio::test]
    async fn distributed_witness_path_gossip_materialize_aggregate_verify() {
        use dregg_types::CellId;

        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);
        let turn = aggregate_test_turn(alice, bob, 100, 1);

        // Shared committed receipt: both per-cell WRs cover the SAME receipt,
        // and the receiving node re-executes to this same receipt locally.
        let receipt = sample_receipt(42);
        let receipt_hash = receipt.receipt_hash();

        // ── Source A: alice-side WR, independently produced + serialized. ──
        let alice_wr = aggregate_test_wr(&turn, &alice, &receipt);
        let alice_artifact = alice_wr
            .to_artifact_bytes()
            .expect("alice WR artifact encodes");
        let bundle_a = TurnArtifactBundle::with_committed(
            b"signed-turn".to_vec(),
            Some(serde_json::to_vec(&receipt).expect("receipt encodes")),
            vec![alice_artifact.clone()],
        );

        // ── Source B: bob-side WR, INDEPENDENTLY produced + serialized. ──
        let bob_wr = aggregate_test_wr(&turn, &bob, &receipt);
        let bob_artifact = bob_wr.to_artifact_bytes().expect("bob WR artifact encodes");
        let bundle_b = TurnArtifactBundle::with_committed(
            b"signed-turn".to_vec(),
            Some(serde_json::to_vec(&receipt).expect("receipt encodes")),
            vec![bob_artifact.clone()],
        );

        // Confirm the two sources are genuinely distinct artifacts (different
        // cells → different bilateral-schedule PI) — NOT the same object reused
        // (which is what the MCP single-call self-prove would produce). The
        // witness_hash binds only the trace bundle (identical empty trace here),
        // so cross-sourcing is established by the per-cell public_inputs, which
        // carry the distinct IS_AGENT_CELL flag and bilateral root projection.
        assert_ne!(
            alice_artifact, bob_artifact,
            "the two per-cell WR artifacts must be independently sourced"
        );
        assert_ne!(
            alice_wr.public_inputs, bob_wr.public_inputs,
            "the two per-cell WRs must carry distinct bilateral PI (cross-sourced)"
        );
        let is_agent_idx = dregg_circuit::effect_vm::pi::IS_AGENT_CELL;
        assert_eq!(
            alice_wr.public_inputs.get(is_agent_idx).copied(),
            Some(1),
            "alice is the agent side"
        );
        assert_eq!(
            bob_wr.public_inputs.get(is_agent_idx).copied(),
            Some(0),
            "bob is the counterparty side"
        );

        // ── Receive path: materialize each gossiped bundle on the node. ──
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let mut guard = state.write().await;

        let ev_a =
            materialize_blocklace_artifacts(&mut guard, BlockId([1u8; 32]), &receipt, &bundle_a);
        assert!(
            ev_a.is_empty(),
            "alice bundle must materialize cleanly: {ev_a:?}"
        );
        let ev_b =
            materialize_blocklace_artifacts(&mut guard, BlockId([2u8; 32]), &receipt, &bundle_b);
        assert!(
            ev_b.is_empty(),
            "bob bundle must materialize cleanly: {ev_b:?}"
        );

        // Both independently-gossiped WRs are now stored under the receipt.
        let stored = guard
            .witnessed_receipts
            .get(&receipt_hash)
            .expect("witnesses materialized")
            .clone();
        assert_eq!(stored.len(), 2, "both cross-sourced WRs materialized");
        drop(guard);

        // The materialized WRs round-tripped through artifact-byte decode: the
        // stored per-cell public_inputs must equal the original per-source PIs
        // (i.e. the gossip-receive path faithfully reconstructed both
        // independently-sourced witnesses, not one duplicated).
        let mut stored_pis: Vec<Vec<u32>> =
            stored.iter().map(|w| w.public_inputs.clone()).collect();
        stored_pis.sort();
        let mut source_pis = vec![alice_wr.public_inputs.clone(), bob_wr.public_inputs.clone()];
        source_pis.sort();
        assert_eq!(
            stored_pis, source_pis,
            "materialized WRs are exactly the two independently-sourced ones"
        );

        // ── Aggregate: REAL cross-node aggregate over the gossiped WRs. ──
        // Recover each materialized WR by cell (IS_AGENT_CELL slot distinguishes
        // the agent/alice side from bob).
        let materialized_alice = stored
            .iter()
            .find(|w| w.public_inputs.get(is_agent_idx).copied() == Some(1))
            .expect("agent-side WR present")
            .clone();
        let materialized_bob = stored
            .iter()
            .find(|w| w.public_inputs.get(is_agent_idx).copied() == Some(0))
            .expect("counterparty WR present")
            .clone();

        let entries = vec![(alice, materialized_alice), (bob, materialized_bob)];
        let bundle =
            dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle(&turn, &entries)
                .expect("cross-sourced WRs must aggregate");
        assert_eq!(bundle.participating_cells.len(), 2);
        dregg_turn::aggregate_bilateral_prover::verify_aggregated_bundle(&bundle)
            .expect("aggregated bundle of gossiped WRs must verify");
    }

    // ── Finalized-execution cross-node UNIFORMITY (S5-1 hardening) ──────────
    //
    // The production property: once a turn is finalized, applying it must yield
    // the IDENTICAL post-state on every node — same ledger content, same
    // attested root — with no local-only state and no double-apply. These tests
    // drive the exact production functions the live commit path
    // (`execute_finalized_turn`) uses: `provision_transfer_destinations` for
    // deterministic cross-node cell provisioning, the real `TurnExecutor`, and
    // `canonical_ledger_root` for the attested commitment. A simulated committee
    // of independent ledgers (one per node) stands in for separate processes —
    // the load-bearing fact is that each node sees ONLY the finalized turn's
    // bytes, never the submitter's out-of-band local state.

    /// Build a real ed25519-signed Transfer turn from `sender` to `to`.
    fn signed_transfer_turn(
        cclerk: &dregg_sdk::AgentCipherclerk,
        sender: dregg_cell::CellId,
        to: dregg_cell::CellId,
        amount: u64,
        nonce: u64,
        federation_id: &[u8; 32],
    ) -> dregg_sdk::SignedTurn {
        let transfer = dregg_turn::Effect::Transfer {
            from: sender,
            to,
            amount,
        };
        let action = cclerk.make_action(sender, "transfer", vec![transfer], federation_id);
        let mut call_forest = dregg_turn::CallForest::new();
        call_forest.add_root(action);
        let mut turn = dregg_turn::Turn {
            agent: sender,
            nonce,
            fee: 0,
            memo: None,
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: vec![],
            cross_effect_dependencies: vec![],
            effect_witness_index_map: vec![],
        };
        // Size the fee (= the executor's computron budget cap) to the estimated
        // cost so the budget gate passes — exactly as the real faucet does in
        // `api.rs` (`faucet_turn.fee = executor.estimate_cost(&faucet_turn)`).
        // A `fee: 0` made every amount>0 Transfer reject as BudgetExceeded
        // (limit=0, used=100). The estimator and the applying executor both use
        // `ComputronCosts::default()`, so estimate == charged cost.
        let est = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
        turn.fee = est.estimate_cost(&turn);
        cclerk.sign_turn(&turn)
    }

    /// Seed an independent per-node ledger exactly as genesis would: the sender
    /// (faucet) cell funded; the destination ABSENT (no node has seen it).
    fn node_genesis_ledger(sender_pk: [u8; 32], balance: i64) -> dregg_cell::Ledger {
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(
                sender_pk, [0u8; 32], balance,
            ))
            .expect("genesis sender cell");
        ledger
    }

    /// Apply a finalized turn to one node's ledger via the PRODUCTION path:
    /// verify the signature (the `execute_finalized_turn` gate), provision any
    /// missing Transfer destination deterministically, then execute. Returns the
    /// post-state root.
    fn apply_finalized_on_node(
        signed: &dregg_sdk::SignedTurn,
        ledger: &mut dregg_cell::Ledger,
    ) -> [u8; 32] {
        // Signature gate — exactly what `execute_finalized_turn` checks first.
        let h = signed.turn.hash();
        assert!(
            signed.signer.verify(&h, &signed.signature),
            "finalized turn signature must verify"
        );
        // Deterministic cross-node provisioning (the function under test).
        provision_transfer_destinations(ledger, &signed.turn.call_forest);
        let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
        match executor.execute(&signed.turn, ledger) {
            dregg_turn::TurnResult::Committed { .. } => {}
            other => panic!("finalized turn must commit on every node, got: {other:?}"),
        }
        canonical_ledger_root(ledger)
    }

    /// A finalized cross-node Transfer to a FRESH destination applies identically
    /// on every node: same attested root, byte-identical provisioned cell, exact
    /// value moved, and a re-apply is rejected (no double-apply).
    #[test]
    fn finalized_transfer_to_fresh_dest_is_uniform_across_nodes() {
        const N: usize = 3;
        let sender_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"finalized-uniform:sender").as_bytes(),
        ));
        let sender_pk = sender_cclerk.public_key().0;
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &[0u8; 32]);
        // A fresh destination NO node has seen (not derived from any local cell).
        let dest = dregg_cell::CellId([0x5Du8; 32]);
        // Sign for the BARE executor each node runs: `apply_finalized_on_node`
        // builds `TurnExecutor::new(..)` without `set_local_federation_id`, so its
        // `local_federation_id` is `[0u8; 32]` (see node/src/mcp.rs:154). The
        // per-action signature binds the federation id (authorize.rs
        // `compute_signing_message`), so it must match what the executor
        // reconstructs — i.e. `[0u8; 32]` here, the same convention production
        // uses when no non-zero federation is configured.
        let federation_id = [0u8; 32];

        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);

        // N independent node ledgers, each seeded identically from "genesis"
        // (sender funded, dest absent). Each applies ONLY the finalized bytes.
        let mut roots: Vec<[u8; 32]> = Vec::new();
        let mut dest_cells: Vec<dregg_cell::Cell> = Vec::new();
        let mut ledgers: Vec<dregg_cell::Ledger> = Vec::new();
        for _ in 0..N {
            let mut ledger = node_genesis_ledger(sender_pk, 1_000_000);
            let root = apply_finalized_on_node(&signed, &mut ledger);
            roots.push(root);
            dest_cells.push(
                ledger
                    .get(&dest)
                    .expect("destination provisioned on this node")
                    .clone(),
            );
            ledgers.push(ledger);
        }

        // (1) UNIFORM ROOT: every node's attested ledger root is identical.
        for r in &roots {
            assert_eq!(
                r, &roots[0],
                "finalized application must yield an identical attested root on every node"
            );
        }

        // (2) BYTE-IDENTICAL PROVISIONED CELL: the anti-divergence property the
        // attested root (now over the whole cell) actually witnesses. A
        // submitter that minted a canonical pk-cell while peers stubbed would
        // fail HERE even though balances matched.
        let dest_bytes0 = postcard::to_stdvec(&dest_cells[0]).expect("dest cell encodes");
        for c in &dest_cells {
            assert_eq!(
                postcard::to_stdvec(c).expect("dest cell encodes"),
                dest_bytes0,
                "the provisioned destination cell must be byte-identical on every node"
            );
        }

        // (3) EXACT VALUE moved into the (provisioned) destination.
        assert_eq!(
            dest_cells[0].state.balance(),
            4_200,
            "destination must hold exactly the transferred amount"
        );
        // Sender debited by the transfer amount AND the turn fee on every node.
        // The fee is debited in-place (execute.rs:419) and — since the test sets
        // no fee-well/proposer/treasury cell on the executor — credited nowhere,
        // i.e. BURNED. That burn is byte-identical on all N nodes, so debiting it
        // leaves the attested root uniform (the property under test still holds).
        for ledger in &ledgers {
            assert_eq!(
                ledger.get(&sender).expect("sender present").state.balance(),
                1_000_000 - 4_200 - signed.turn.fee as i64,
                "sender must be debited (amount + burned fee) identically on every node"
            );
        }

        // (4) NO DOUBLE-APPLY: re-applying the SAME finalized turn is rejected on
        // every node (the nonce already advanced), so a duplicate finalized
        // delivery cannot move value twice or diverge the ledger.
        for ledger in &mut ledgers {
            let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
            // The destination already exists now; provisioning is a no-op.
            provision_transfer_destinations(ledger, &signed.turn.call_forest);
            match executor.execute(&signed.turn, ledger) {
                dregg_turn::TurnResult::Committed { .. } => {
                    panic!("a finalized turn must not commit twice (double-apply)")
                }
                _ => {}
            }
            // Value unchanged after the rejected re-apply.
            assert_eq!(
                ledger.get(&dest).expect("dest present").state.balance(),
                4_200,
                "a rejected re-apply must not move value"
            );
        }
    }

    // ─── A1 FIX — off-lock finalized execution + concurrency safety ──────────
    //
    // The confirmed n=5 finalization-stall root cause: the EXECUTION FFI ran
    // inline on the tokio worker while `execute_finalized_turn` held the global
    // write lock for the FFI's whole duration, starving the producer/round loop.
    // The fix runs the FFI on `spawn_blocking` against a CLONE of the pre-state
    // (lock released), then re-applies the committed post-state under a brief
    // re-acquired lock as a per-cell OVERLAY of exactly the cells the turn touched
    // (never a wholesale ledger replace). These two tests cover the make-or-break
    // (a real finalized turn advances height 0 -> 1 through `execute_finalized_turn`
    // with A1) and the install mechanism + concurrency guard in isolation.

    /// THE MAKE-OR-BREAK: a finalized Transfer turn executes through the REAL
    /// `execute_finalized_turn` (the live commit path, now off-lock) and advances
    /// the attested height 0 -> 1 — the local confirmation that A1 unblocks
    /// finalization (the execution completes + promotes, no wedge), and the ledger
    /// reflects the committed transfer. Forces the deterministic Rust producer path
    /// so the test does not depend on a Lean-linked archive; the A1 change (WHERE
    /// the FFI runs + HOW its result is installed) is identical either way.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn a1_finalized_turn_advances_height_zero_to_one_off_lock() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        // Deterministic Rust producer (no Lean-archive dependence).
        {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
        }

        // The federation id the node's executor binds (fresh state, not
        // federation-configured): blake3(node cclerk pubkey). The turn's per-action
        // signature MUST bind the SAME id or admission rejects.
        let federation_id = {
            let s = state.read().await;
            *blake3::hash(s.cclerk.public_key().as_bytes()).as_bytes()
        };

        // Fund a sender cell; the destination is fresh (materialized by the path).
        let sender_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"a1-finalize:sender").as_bytes(),
        ));
        let sender_pk = sender_cclerk.public_key().0;
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &[0u8; 32]);
        let dest = dregg_cell::CellId([0x3Cu8; 32]);
        {
            let mut s = state.write().await;
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    sender_pk, [0u8; 32], 1_000_000,
                ))
                .expect("fund sender");
        }

        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);
        let turn_data = postcard::to_stdvec(&signed).expect("encode signed turn");

        // A minimal real handle; `execute_finalized_turn` reads only `handle.lace`
        // for the OPTIONAL finality round (an empty lace yields round None — fine).
        let self_key = [0x9Au8; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let block_id = BlockId([0x11u8; 32]);

        let height_before = {
            let s = state.read().await;
            s.store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0)
        };
        assert_eq!(height_before, 0, "fresh node starts at attested height 0");

        // With A1 the execution FFI runs off the worker + off the lock, so this
        // COMPLETES (does not wedge) and promotes.
        execute_finalized_turn(&state, &handle, block_id, &turn_data, None, 0).await;

        let height_after = {
            let s = state.read().await;
            s.store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0)
        };
        assert_eq!(
            height_after, 1,
            "a finalized turn MUST advance attested height 0 -> 1 with A1 — the unlock"
        );

        // The ledger reflects the committed transfer.
        let s = state.read().await;
        assert_eq!(
            s.ledger
                .get(&dest)
                .expect("destination materialized by the finalized path")
                .state
                .balance(),
            4_200,
            "destination holds exactly the transferred amount"
        );
        assert_eq!(
            s.ledger
                .get(&sender)
                .expect("sender present")
                .state
                .balance(),
            1_000_000 - 4_200 - signed.turn.fee as i64,
            "sender debited by amount + burned fee"
        );
    }

    /// A1 install mechanism + concurrency guard, in isolation and deterministic.
    /// Mirrors `execute_finalized_turn`'s new flow: execute the finalized turn
    /// against a CLONE of the pre-state (the off-lock `spawn_blocking` step), diff
    /// pre->post for the COMPLETE touched set (`ledger_touched_diff`), then overlay
    /// exactly those cells onto the authoritative ledger. Proves (a) the overlay
    /// reproduces the transfer's post-state, (b) a concurrent write to a DISJOINT
    /// cell during the window is PRESERVED (a wholesale replace would drop it), and
    /// (c) the guard DETECTS a concurrent SAME-cell write (validate-or-reject,
    /// never a silent overwrite).
    #[test]
    fn a1_overlay_installs_poststate_and_guards_concurrent_writes() {
        let federation_id = [0u8; 32]; // bare-executor convention (Rust producer path)
        let sender_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"a1-overlay:sender").as_bytes(),
        ));
        let sender_pk = sender_cclerk.public_key().0;
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &[0u8; 32]);
        let dest = dregg_cell::CellId([0x7Eu8; 32]);
        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);

        // The authoritative ledger (sender funded, dest absent).
        let mut authoritative = node_genesis_ledger(sender_pk, 1_000_000);

        // === off-lock exec against a CLONE of the pre-state (spawn_blocking step) ===
        let pre_ledger = authoritative.clone();
        let mut exec_ledger = authoritative.clone();
        provision_transfer_destinations(&mut exec_ledger, &signed.turn.call_forest);
        let executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
        match crate::executor_setup::execute_via_producer(
            &executor,
            &signed.turn,
            &mut exec_ledger,
            false,
        ) {
            dregg_turn::TurnResult::Committed { .. } => {}
            other => panic!("finalized transfer must commit, got {other:?}"),
        }
        let touched = ledger_touched_diff(&pre_ledger, &exec_ledger);
        assert!(
            touched.contains(&sender) && touched.contains(&dest),
            "the touched set must include the debited sender and the credited destination"
        );

        // === a CONCURRENT writer touches a DISJOINT cell during the window ===
        let bystander = dregg_cell::Cell::with_balance([0xABu8; 32], [0u8; 32], 777);
        let bystander_id = bystander.id();
        authoritative
            .insert_cell(bystander)
            .expect("concurrent disjoint insert");

        // Guard: a DISJOINT concurrent write is NOT a conflict.
        let conflict = touched
            .iter()
            .any(|id| pre_ledger.get(id) != authoritative.get(id));
        assert!(
            !conflict,
            "a concurrent write to a DISJOINT cell must not register as a conflict"
        );

        // === overlay install (the per-cell, non-replace apply) ===
        for id in &touched {
            match exec_ledger.get(id) {
                Some(cell) => {
                    let _ = authoritative.remove(id);
                    authoritative
                        .insert_cell(cell.clone())
                        .expect("overlay insert");
                }
                None => {
                    let _ = authoritative.remove(id);
                }
            }
        }

        // (a) the transfer landed.
        assert_eq!(
            authoritative.get(&dest).expect("dest").state.balance(),
            4_200,
            "destination credited by the overlay"
        );
        assert_eq!(
            authoritative.get(&sender).expect("sender").state.balance(),
            1_000_000 - 4_200 - signed.turn.fee as i64,
            "sender debited by amount + burned fee"
        );
        // (b) the concurrent disjoint cell is PRESERVED (a wholesale replace drops it).
        assert_eq!(
            authoritative
                .get(&bystander_id)
                .expect("bystander preserved")
                .state
                .balance(),
            777,
            "a concurrent write to ANOTHER cell survives the overlay (no wholesale replace)"
        );

        // === (c) the guard DETECTS a concurrent SAME-cell write ===
        let mut authoritative2 = node_genesis_ledger(sender_pk, 1_000_000);
        let pre_ledger2 = authoritative2.clone();
        // A concurrent path mutates the SENDER (a cell this turn also touches).
        let mut moved = authoritative2.get(&sender).expect("sender present").clone();
        moved.state.set_balance(500_000);
        let _ = authoritative2.remove(&sender);
        authoritative2
            .insert_cell(moved)
            .expect("concurrent same-cell write");
        let conflict2 = touched
            .iter()
            .any(|id| pre_ledger2.get(id) != authoritative2.get(id));
        assert!(
            conflict2,
            "a concurrent SAME-cell write MUST be detected as a conflict (validate-or-reject)"
        );
    }

    /// `provision_transfer_destinations` is deterministic and idempotent: the
    /// stub it inserts is byte-identical regardless of node, and a second call
    /// (or a destination that already exists) leaves the cell untouched.
    #[test]
    fn provision_transfer_destinations_is_deterministic_and_idempotent() {
        let sender = dregg_cell::CellId([1u8; 32]);
        let dest = dregg_cell::CellId([0xEEu8; 32]);
        let mut forest = dregg_turn::CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(sender, "t", sender)
                .effect_transfer(sender, dest, 7)
                .build(),
        );

        // Two independent nodes provision from the same forest → identical cell.
        let mut a = dregg_cell::Ledger::new();
        let mut b = dregg_cell::Ledger::new();
        provision_transfer_destinations(&mut a, &forest);
        provision_transfer_destinations(&mut b, &forest);
        let ca = a.get(&dest).expect("a provisioned").clone();
        let cb = b.get(&dest).expect("b provisioned").clone();
        assert_eq!(
            postcard::to_stdvec(&ca).unwrap(),
            postcard::to_stdvec(&cb).unwrap(),
            "provisioned stub must be byte-identical across nodes"
        );
        assert_eq!(ca.state.balance(), 0, "stub starts at zero balance");

        // Idempotent: a second provisioning does not overwrite / duplicate.
        let before = postcard::to_stdvec(&ca).unwrap();
        provision_transfer_destinations(&mut a, &forest);
        let after = postcard::to_stdvec(a.get(&dest).expect("still present")).unwrap();
        assert_eq!(before, after, "re-provisioning must be a no-op");

        // A destination that already exists (e.g. a real canonical cell) is left
        // untouched — provisioning only fills genuine absences.
        let mut c = dregg_cell::Ledger::new();
        let real = dregg_cell::Cell::with_balance([9u8; 32], [0u8; 32], 500);
        let real_id = real.id();
        c.insert_cell(real).expect("insert real");
        let mut forest2 = dregg_turn::CallForest::new();
        forest2.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(sender, "t", sender)
                .effect_transfer(sender, real_id, 1)
                .build(),
        );
        provision_transfer_destinations(&mut c, &forest2);
        assert_eq!(
            c.get(&real_id).expect("real still present").state.balance(),
            500,
            "an existing destination must not be overwritten by provisioning"
        );
    }

    /// The attested root now commits the WHOLE cell, so a divergence in
    /// non-state fields (e.g. a stub vs a canonical pk-cell at the same id, the
    /// exact pre-hardening faucet bug) produces DIFFERENT roots — the divergence
    /// is loud, not silent.
    #[test]
    fn ledger_root_witnesses_full_cell_divergence() {
        let id = dregg_cell::CellId([0x7Au8; 32]);

        // Node A: a zero-pk stub at `id` (what peers materialize).
        let mut a = dregg_cell::Ledger::new();
        a.insert_cell(dregg_cell::Cell::remote_stub_with_id_and_balance(id, 0))
            .expect("stub");

        // Node B: a canonical pk-cell whose id ALSO happens to be `id` — same
        // balance/nonce (state), different public_key. Constructed via the stub
        // constructor that lets us pin a non-zero pk at the chosen id.
        let mut b = dregg_cell::Ledger::new();
        b.insert_cell(dregg_cell::Cell::remote_stub_with_id_pk_balance(
            id,
            [0x11u8; 32],
            0,
        ))
        .expect("pk-cell");

        // States are equal (balance 0, nonce 0) — the OLD state-only root would
        // have called these identical. The whole-cell root does not.
        assert_ne!(
            canonical_ledger_root(&a),
            canonical_ledger_root(&b),
            "the attested root must witness a public_key divergence at the same id"
        );
    }

    // ─── Gossip-of-peers: committee-gated address acceptance ────────────────

    /// Build a minimal real [`BlocklaceHandle`] over a live gossip network for a
    /// committee of `participants`, so `handle_peer_addrs` can be exercised
    /// end-to-end (it learns into the REAL gossip topic peer set).
    async fn test_handle_with_committee(
        self_key: [u8; 32],
        participants: Vec<[u8; 32]>,
    ) -> BlocklaceHandle {
        use dregg_blocklace::constitution::{Constitution, ConstitutionManager};
        let (sk, _pk) = dregg_types::generate_keypair();
        let node_id: NodeId = *blake3::hash(&self_key).as_bytes();
        let peer_node = PeerNode::new(PeerNodeConfig::default()).await.unwrap();
        let gossip = Arc::new(GossipNetwork::new(
            peer_node.endpoint().clone(),
            node_id,
            sk,
            HashMap::new(),
        ));
        let topic = gossip.join_topic(TOPIC_BLOCKLACE, &[]).await.unwrap();
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]);
        let quorum = dregg_blocklace::supermajority_threshold(participants.len());
        let blocklace = dregg_blocklace::finality::Blocklace::new(signing_key.clone(), quorum);
        let constitution =
            ConstitutionManager::new(Constitution::new(participants.clone(), 60_000));
        let votes =
            crate::finalization_votes::VoteCollector::new(participants.iter().copied(), quorum);
        BlocklaceHandle {
            lace: Arc::new(RwLock::new(blocklace)),
            constitution: Arc::new(RwLock::new(constitution)),
            gossip,
            topic,
            self_key,
            signing_key,
            votes: Arc::new(RwLock::new(votes)),
            my_pending_votes: Arc::new(RwLock::new(HashMap::new())),
            cursor: Arc::new(RwLock::new(crate::execution_cursor::ExecutionCursor::new())),
            finality_notify: Arc::new(Notify::new()),
            auto_approve_joins: false,
            checkpoint_interval: 100,
            orphans: Arc::new(RwLock::new(crate::catchup::OrphanBuffer::new())),
            pull_backoff: Arc::new(RwLock::new(dregg_net::peer_score::RequestBackoff::new(
                Duration::from_secs(1),
                Duration::from_secs(30),
            ))),
            tip_pull_backoff: Arc::new(RwLock::new(dregg_net::peer_score::RequestBackoff::new(
                Duration::from_millis(500),
                Duration::from_millis(1500),
            ))),
            last_produced: Arc::new(RwLock::new(std::time::Instant::now())),
            ack_pending: Arc::new(std::sync::atomic::AtomicBool::new(false)),
            pending_payloads: Arc::new(RwLock::new(std::collections::VecDeque::new())),
        }
    }

    // ─── BUG 1: hostname peer resolution (overlay hostnames federate) ───────────

    /// A `hostname:port` peer (not an `IP:PORT` literal) RESOLVES via DNS and is
    /// returned for dialing — the case the old `parse::<SocketAddr>()` silently
    /// dropped, so genesis-emitted overlay hostnames never federated. `localhost`
    /// is a hostname every host resolves; an IP literal still works too.
    #[tokio::test]
    async fn hostname_peer_resolves_and_is_dialed() {
        // A hostname spec — the previously-dropped case.
        let resolved = resolve_peer_addrs(&["localhost:9420".to_string()]).await;
        assert!(
            !resolved.is_empty(),
            "a hostname peer (localhost:9420) must RESOLVE and be returned for dialing — the \
             overlay-hostname federation case the IP-literal parser silently dropped"
        );
        assert!(
            resolved.iter().all(|a| a.port() == 9420),
            "resolved addresses must carry the spec's port"
        );

        // An IP literal still resolves (lookup_host accepts it verbatim).
        let lit = resolve_peer_addrs(&["127.0.0.1:9420".to_string()]).await;
        assert_eq!(lit, vec!["127.0.0.1:9420".parse::<SocketAddr>().unwrap()]);
    }

    /// An UNRESOLVABLE peer is dropped VISIBLY (logged loud, returns nothing) —
    /// never a silent drop. `.invalid` is the RFC-2606 guaranteed-non-resolvable
    /// TLD, so this is deterministic offline.
    #[tokio::test]
    async fn unresolvable_peer_errors_visibly_and_is_omitted() {
        let resolved = resolve_peer_addrs(&["no-such-host.invalid:9420".to_string()]).await;
        assert!(
            resolved.is_empty(),
            "an unresolvable peer must be omitted (and logged loudly at error), not crash or be \
             treated as dialable"
        );

        // A mix: the good hostname survives, the bad one is dropped (visibly).
        let mixed = resolve_peer_addrs(&[
            "localhost:9420".to_string(),
            "no-such-host.invalid:9420".to_string(),
        ])
        .await;
        assert!(
            !mixed.is_empty() && mixed.iter().all(|a| a.port() == 9420),
            "a resolvable peer in a mixed list must still be dialed even when a sibling fails"
        );
    }

    /// THE DISCOVERY TRUST GATE: a `PeerAddrs` announcement learns an address ONLY
    /// for a key already in the committee (`known_federation_keys`), and REJECTS a
    /// forged address claimed for a non-committee key. The committee — not the wire
    /// sender — is the trust anchor: discovery learns addresses for trusted
    /// identities, never admits strangers.
    #[tokio::test]
    async fn gossip_of_peers_accepts_committee_rejects_forged() {
        // The gossip/QUIC transport needs a rustls CryptoProvider (idempotent).
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        // Committee = three genesis-trusted members (self + B + C).
        let (_sk_self, pk_self) = dregg_types::generate_keypair();
        let (_sk_b, pk_b) = dregg_types::generate_keypair();
        let (_sk_c, pk_c) = dregg_types::generate_keypair();
        // A STRANGER: a free Sybil keypair NOT in the committee.
        let (_sk_x, pk_x) = dregg_types::generate_keypair();

        state
            .write()
            .await
            .set_federation_keys(vec![pk_self, pk_b, pk_c]);

        let handle = test_handle_with_committee(pk_self.0, vec![pk_self.0, pk_b.0, pk_c.0]).await;

        let from: SocketAddr = "127.0.0.1:40000".parse().unwrap();
        let addr_c: SocketAddr = "127.0.0.1:41000".parse().unwrap();
        let addr_x: SocketAddr = "127.0.0.1:42000".parse().unwrap();
        let addr_self: SocketAddr = "127.0.0.1:43000".parse().unwrap();

        // One message carrying: a VALID committee binding for C, a FORGED binding
        // for the non-committee stranger X, and a (self) binding we must ignore.
        let learned = handle_peer_addrs(
            &handle,
            &state,
            from,
            vec![(pk_c.0, addr_c), (pk_x.0, addr_x), (pk_self.0, addr_self)],
        )
        .await;

        // Exactly ONE address was learned: C's. X (stranger) and self were dropped.
        assert_eq!(
            learned, 1,
            "only the committee member C's address may be learned"
        );

        let topic_peers = handle.gossip.topic_peers(&handle.topic).await;
        assert!(
            topic_peers.contains(&addr_c),
            "C's authenticated committee address must be learned into the topic peer set"
        );
        assert!(
            !topic_peers.contains(&addr_x),
            "a FORGED address for a non-committee key must be REJECTED (stranger not admitted)"
        );
        assert!(
            !topic_peers.contains(&addr_self),
            "we must never learn an address for ourselves"
        );

        // Idempotent: re-announcing C's address learns nothing new.
        let again = handle_peer_addrs(&handle, &state, from, vec![(pk_c.0, addr_c)]).await;
        assert_eq!(again, 0, "re-announcing a known address learns nothing new");
    }

    // ─── Co-turn flow: a ProposeAtomicTurn reaches the engine, not the drop ──
    //
    // THE BAR for Wire 2: a co-turn variant gossiped from one node is RECEIVED +
    // dispatched into the in-process coord engine on another — not dropped at the
    // funnel's `_ => return`. These tests drive `dispatch_atomic_proposal` (the
    // exact function the receive funnel calls for `PeerMessage::ProposeAtomicTurn`)
    // and prove the variant produces a REAL vote from `Participant::evaluate_proposal`
    // against a local ledger, rather than no-op'ing.

    /// Build a 2-participant atomic forest moving value from `a` to `b`, as a
    /// coordinator on node A would.
    fn make_atomic_forest(a: [u8; 32], b: [u8; 32]) -> dregg_coord::AtomicForest {
        let from = dregg_cell::CellId(a);
        let to = dregg_cell::CellId(b);
        // A minimal action carrying the transfer (atomic forests are bound by the
        // QC, not the action signature, on commit — mirrors coord's own test helpers).
        let action = dregg_turn::Action {
            target: from,
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: dregg_turn::Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![dregg_turn::Effect::Transfer {
                from,
                to,
                amount: 10,
            }],
            may_delegate: dregg_turn::DelegationMode::None,
            commitment_mode: dregg_turn::CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = dregg_turn::CallForest::new();
        forest.add_root(action);
        dregg_coord::AtomicForest::new(
            vec![a, b],
            forest,
            vec![], // no explicit preconditions: the participant validates locally
            from,
            0,
        )
    }

    #[test]
    fn co_turn_propose_reaches_engine_not_dropped() {
        // Node B's identity + its local ledger (B holds its own funded cell).
        let node_b = [0x0b; 32];
        let node_a = [0x0a; 32];
        let signing_key = [0x42; 32];
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(node_b, [0u8; 32], 1_000))
            .expect("B's cell");
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(node_a, [0u8; 32], 1_000))
            .expect("A's cell");

        // A proposes an atomic turn; the richer wire payload (the broadcast fix).
        let forest = make_atomic_forest(node_a, node_b);
        let forest_hash = forest.hash;
        let wire = forest.encode_for_wire();
        assert!(!wire.is_empty(), "the richer payload is non-empty");

        // The coordinator's REAL proposal id (bound to forest + coordinator = A).
        let proposal_id = dregg_coord::Coordinator::proposal_id_for(&forest_hash, &node_a);

        // B receives it: the funnel dispatches into the in-process coord engine
        // instead of `_ => return`. This produces a REAL vote, not a no-op.
        let vote = dispatch_atomic_proposal(
            &wire,
            forest_hash,
            proposal_id,
            node_a,
            node_b,
            signing_key,
            ledger,
        )
        .expect("a well-formed proposal must reach the engine and produce a vote");

        // With no failing precondition keyed to B's cell, B's participant votes Yes
        // — and the signature is bound to the coordinator's REAL proposal_id, so the
        // coordinator can verify it in `receive_vote`. The variant FLOWED in.
        assert!(
            vote.is_yes(),
            "B's participant should approve (preconditions hold on its local ledger)"
        );
        let sig = match vote {
            dregg_coord::Vote::Yes { signature } => signature,
            dregg_coord::Vote::No { .. } => unreachable!(),
        };
        let pubkey = dregg_coord::Vote::public_key_from_signing_key(&signing_key);
        assert!(
            dregg_coord::Vote::verify_yes(&sig, &proposal_id, &forest_hash, &pubkey),
            "the vote must be a genuine engine-signed vote bound to the coordinator's proposal_id"
        );
    }

    #[test]
    fn co_turn_propose_rejects_malformed_payload() {
        // The ONLY drop left: a payload that does not decode into a forest. This is
        // a genuine decode failure, not the old blanket `_ => return`.
        let err = dispatch_atomic_proposal(
            &[0xff, 0x00, 0x13, 0x37],
            [0u8; 32],
            [0u8; 32],
            [0x0a; 32],
            [0x0b; 32],
            [0x42; 32],
            dregg_cell::Ledger::new(),
        )
        .unwrap_err();
        assert!(
            matches!(err, dregg_coord::CoordError::WireDecode(_)),
            "a malformed forest payload is reported, not silently dropped: {err}"
        );
    }

    #[test]
    fn co_turn_propose_rejects_hash_mismatch() {
        // A payload whose body was swapped under a stale announced hash is rejected
        // (anti-tamper): the decoded forest hash must match the wire `forest_hash`.
        let node_a = [0x0a; 32];
        let node_b = [0x0b; 32];
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(node_b, [0u8; 32], 1_000))
            .expect("B's cell");
        let forest = make_atomic_forest(node_a, node_b);
        let wire = forest.encode_for_wire();
        let wrong_hash = [0x99; 32];
        let pid = dregg_coord::Coordinator::proposal_id_for(&wrong_hash, &node_a);
        let err =
            dispatch_atomic_proposal(&wire, wrong_hash, pid, node_a, node_b, [0x42; 32], ledger)
                .unwrap_err();
        assert!(
            matches!(err, dregg_coord::CoordError::HashMismatch { .. }),
            "a forest whose hash disagrees with the announced hash is rejected: {err}"
        );
    }

    #[test]
    fn co_turn_propose_rejects_forged_proposal_id() {
        // THE PROPOSAL-ID FIX, negatively: a proposal_id NOT derivable from
        // (forest.hash, coordinator) is rejected before producing a vote — so a
        // participant never signs a vote bound to a forged id.
        let node_a = [0x0a; 32];
        let node_b = [0x0b; 32];
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(node_b, [0u8; 32], 1_000))
            .expect("B's cell");
        let forest = make_atomic_forest(node_a, node_b);
        let forest_hash = forest.hash;
        let wire = forest.encode_for_wire();
        let forged_pid = [0x55; 32]; // not H(.. || forest_hash || node_a)
        let err = dispatch_atomic_proposal(
            &wire,
            forest_hash,
            forged_pid,
            node_a,
            node_b,
            [0x42; 32],
            ledger,
        )
        .unwrap_err();
        assert!(
            matches!(err, dregg_coord::CoordError::HashMismatch { .. }),
            "a forged proposal_id (not bound to forest+coordinator) is rejected: {err}"
        );
    }

    // ─── Co-turn 2PC ROUND-TRIP: propose → vote → commit, end to end ───────────
    //
    // WIRE 3's BAR: a co-turn proposed by node A flows to B, B votes, the vote
    // RETURNS to A, and A COMMITS the atomic forest when the quorum agrees. This
    // drives the exact functions the receive funnels call — `dispatch_atomic_proposal`
    // (B's vote) and `tally_returned_vote` (A's tally + commit) — against a real
    // `NodeState`, proving the loop SETTLES (the ledger transitions), not a no-op.
    #[tokio::test]
    async fn co_turn_round_trip_propose_vote_commit_settles() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        // Sovereign identities (cell_id == pubkey == node_id): A is the coordinator
        // + initiator, B is the other participant. Their signing keys ARE their ids.
        let sk_a = [0x0a; 32];
        let sk_b = [0x0b; 32];
        let node_a = dregg_coord::Vote::public_key_from_signing_key(&sk_a);
        let node_b = dregg_coord::Vote::public_key_from_signing_key(&sk_b);

        // Fund both cells permissively so the transfer executes on commit (mirrors
        // coord's own `permissive_cell` commit fixtures). `with_balance` derives the
        // cell id from (pubkey, token); `insert_cell` returns that real id, which we
        // then use as the forest's from/to/initiator so the commit finds the cells.
        let permissive_cell = |key: [u8; 32], balance: i64| -> dregg_cell::Cell {
            let mut cell = dregg_cell::Cell::with_balance(key, [0u8; 32], balance);
            cell.permissions = dregg_cell::Permissions {
                send: dregg_cell::AuthRequired::None,
                receive: dregg_cell::AuthRequired::None,
                set_state: dregg_cell::AuthRequired::None,
                set_permissions: dregg_cell::AuthRequired::None,
                set_verification_key: dregg_cell::AuthRequired::None,
                increment_nonce: dregg_cell::AuthRequired::None,
                delegate: dregg_cell::AuthRequired::None,
                access: dregg_cell::AuthRequired::None,
            };
            cell
        };
        let (cell_a, cell_b) = {
            let mut s = state.write().await;
            let cell_a = s
                .ledger
                .insert_cell(permissive_cell(node_a, 1_000))
                .expect("A's cell");
            let cell_b = s
                .ledger
                .insert_cell(permissive_cell(node_b, 1_000))
                .expect("B's cell");
            (cell_a, cell_b)
        };

        // A builds the atomic forest (transfer 10 from cell_a to cell_b, initiator
        // = cell_a) over the REAL inserted cell ids. Participants are the node ids
        // (node_a / node_b) — the protocol identities the 2PC quorum is keyed by.
        let transfer = dregg_turn::Action {
            target: cell_a,
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: dregg_turn::Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![dregg_turn::Effect::Transfer {
                from: cell_a,
                to: cell_b,
                amount: 10,
            }],
            may_delegate: dregg_turn::DelegationMode::None,
            commitment_mode: dregg_turn::CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut call_forest = dregg_turn::CallForest::new();
        call_forest.add_root(transfer);
        let forest =
            dregg_coord::AtomicForest::new(vec![node_a, node_b], call_forest, vec![], cell_a, 0);
        let forest_hash = forest.hash;
        let mut participant_keys = HashMap::new();
        participant_keys.insert(node_a, node_a);
        participant_keys.insert(node_b, node_b);
        let mut coordinator = dregg_coord::Coordinator::new(
            node_a,
            sk_a,
            2, // unanimous: A + B both required
            dregg_turn::ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );
        let propose_msg = coordinator.propose(forest.clone()).expect("A proposes");
        let proposal_id = propose_msg.proposal_id;

        // A casts ITS OWN Yes vote into its coordinator (mirrors the local path where
        // the initiator is also a participant). Now the only missing vote is B's.
        let sig_a = dregg_coord::Vote::sign_yes(&proposal_id, &forest_hash, &sk_a);
        let pending = coordinator
            .receive_vote(node_a, dregg_coord::Vote::yes(sig_a))
            .expect("A's self-vote accepted");
        assert_eq!(pending, None, "one of two votes in — still pending");

        // Persist the coordinator as the live tally (exactly as `post_atomic_proposal`).
        {
            let mut s = state.write().await;
            s.atomic_proposals.insert(
                proposal_id,
                crate::state::ActiveProposal {
                    coordinator,
                    created_at: std::time::Instant::now(),
                    forest: forest.clone(),
                },
            );
        }

        // ─ B's side: receive the broadcast proposal, evaluate, produce a real vote ─
        let wire = forest.encode_for_wire();
        let b_ledger = {
            let s = state.read().await;
            s.ledger.clone()
        };
        let b_vote = dispatch_atomic_proposal(
            &wire,
            forest_hash,
            proposal_id,
            node_a,
            node_b,
            sk_b,
            b_ledger,
        )
        .expect("B reaches the engine and votes");
        assert!(b_vote.is_yes(), "B approves on its local ledger");
        let b_sig = match &b_vote {
            dregg_coord::Vote::Yes { signature } => signature.to_vec(),
            dregg_coord::Vote::No { signature, .. } => signature.to_vec(),
        };

        // ─ The vote RETURNS to A: tally it. This is the 2nd Yes of threshold-2, so
        //   the coordinator decides Commit and `tally_returned_vote` drives the
        //   commit against A's ledger — the co-turn SETTLES.
        let nonce_before = {
            let s = state.read().await;
            s.ledger.get(&cell_a).unwrap().state.nonce()
        };
        let from: SocketAddr = "127.0.0.1:50000".parse().unwrap();
        tally_returned_vote(&state, from, proposal_id, forest_hash, node_b, true, b_sig).await;

        // SETTLEMENT EVIDENCE: the proposal was consumed (committed, not left
        // pending) AND the ledger transitioned (initiator nonce bumped by the
        // executed turn).
        {
            let s = state.read().await;
            assert!(
                !s.atomic_proposals.contains_key(&proposal_id),
                "a committed proposal is removed from the active map — the loop settled"
            );
            let nonce_after = s.ledger.get(&cell_a).unwrap().state.nonce();
            assert_eq!(
                nonce_after,
                nonce_before + 1,
                "the committed atomic turn advanced the initiator's nonce — real settlement, not a no-op"
            );
        }
    }

    #[tokio::test]
    async fn co_turn_returned_vote_for_unknown_proposal_is_dropped() {
        // A vote for a proposal this node does not coordinate is harmlessly dropped
        // (we are not the coordinator / it expired) — no panic, no state change.
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let from: SocketAddr = "127.0.0.1:50001".parse().unwrap();
        tally_returned_vote(
            &state,
            from,
            [0x77; 32],
            [0x88; 32],
            [0x0b; 32],
            true,
            vec![0u8; 64],
        )
        .await;
        let s = state.read().await;
        assert!(
            s.atomic_proposals.is_empty(),
            "a vote for an unknown proposal changes nothing"
        );
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

/// Persist the current blocklace metadata and the executed-block identity set.
///
/// Called after each batch of finalized turns is executed. On restart the node
/// resumes BY IDENTITY: turn-carrying blocks from the durable commit log, the
/// rest from this batch-cadence set (idempotent on re-process if it lags a
/// crash). The legacy `executed_up_to` COUNT is still written for
/// diagnostics/compat, but is never used as a resume index (TauPrefixMonotone:
/// the order it would index into can shift under honest catch-up growth).
async fn persist_blocklace_state(state: &NodeState, handle: &BlocklaceHandle) {
    let (executed_up_to, executed_ids) = {
        let cursor = handle.cursor.read().await;
        (cursor.executed_count(), cursor.executed_ids().to_vec())
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
        warn!(error = %e, "failed to persist executed_up_to count");
    }
    if let Err(e) = s.store.persist_executed_block_ids(&executed_ids) {
        warn!(error = %e, "failed to persist executed block-id set");
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
    let executed_count = { handle.cursor.read().await.executed_count() as u64 };

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

    // Peer-supplied checkpoint: the only integrity check above is a self-asserted
    // blake3 hash the SAME peer also provided, so it authenticates nothing about
    // the blocks' provenance. We therefore restore via the AUTHENTICATING loader
    // (`from_checkpoint`), which re-verifies every block's Ed25519 signature,
    // enforces causal closure (rejecting dangling predecessors), and detects
    // equivocation — exactly the hardened `receive_block` checks, on the recovery
    // path. A forged/unsigned block in a malicious peer's checkpoint is rejected
    // here rather than sailing into the restored DAG (the A1-class bug this closes).
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
    if !s.len().is_multiple_of(2) {
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
/// Amends the constitution AND advances the LIVE consensus committee so the
/// validator-set reconfiguration is an on-chain, chain-continuing operation
/// rather than a disruptive genesis re-roll. The new participant list takes
/// effect at the NEXT wave boundary (the current wave's ordering uses the old
/// set); the finalization-vote committee and the gossip mesh are advanced here.
async fn apply_passed_proposal(handle: &BlocklaceHandle, proposal_block: &BlockId) {
    let mut constitution = handle.constitution.write().await;
    if constitution.apply_if_passed(proposal_block) {
        let new_participants: Vec<[u8; 32]> = constitution.current.participants.clone();
        let new_count = constitution.current.participant_count();
        let new_version = constitution.version();
        let new_threshold = constitution.threshold();
        drop(constitution);
        info!(
            proposal_block = %proposal_block,
            new_participant_count = new_count,
            new_threshold = new_threshold,
            constitution_version = new_version,
            "constitution amended: membership change applied"
        );
        // LIVE EPOCH TRANSITION: advance the running consensus committee to the
        // newly-finalized validator set. The chain (blocklace + cell state) is
        // carried across; only the committee that gates finality + the gossip
        // mesh admission advance. The federation/chain identity
        // (`federation_id` / `committee_epoch` / `known_federation_keys`) is
        // INTENTIONALLY left unchanged — it is the STABLE chain root the bot /
        // bridge / light client pin, so a committee change never forces a
        // re-point (inflexibility #3). See `apply_committee_change`.
        handle
            .apply_committee_change(&new_participants, new_threshold)
            .await;
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
    let local_pk = state_guard.cclerk.public_key();

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
/// The complete, bounded set of cell ids a committed turn mutated, taken
/// directly from the executor's authoritative [`dregg_cell::LedgerDelta`]:
/// every created cell, every updated cell, and both endpoints of every
/// computron transfer. This is the set whose post-states the durable commit log
/// snapshots into the cell-by-id index, so recovery reconstructs the finalized
/// ledger from (checkpoint ⊕ overlay) without re-execution. Deduplicated and
/// order-stable.
fn touched_cell_ids(delta: &dregg_cell::LedgerDelta) -> Vec<dregg_cell::CellId> {
    let mut ids: Vec<dregg_cell::CellId> = Vec::new();
    fn push(ids: &mut Vec<dregg_cell::CellId>, id: dregg_cell::CellId) {
        if !ids.contains(&id) {
            ids.push(id);
        }
    }
    for cell in &delta.created {
        push(&mut ids, cell.id());
    }
    for (id, _) in &delta.updated {
        push(&mut ids, *id);
    }
    for (from, to, _) in &delta.computron_transfers {
        push(&mut ids, *from);
        push(&mut ids, *to);
    }
    ids
}

/// The COMPLETE set of cell ids whose CONTENT differs between two ledgers — the
/// A1 off-lock execution path's authoritative touched set.
///
/// A finalized turn is executed against a CLONE of the pre-state on a
/// `spawn_blocking` thread (so the FFI holds neither the async worker nor the
/// global write lock); this diff of the resulting post-state against the pre-state
/// is exactly the set the caller overlays onto the authoritative ledger. It is a
/// whole-`Cell` comparison, so — unlike [`touched_cell_ids`] over the executor's
/// `LedgerDelta`, which omits the heap_root / lifecycle / program / vk /
/// delegation dimensions — it captures EVERY committed change and reproduces the
/// exact post-state a re-executing validator computes. `Cell`'s `PartialEq`
/// compares content only (the leaf-digest cache is excluded from `PartialEq`), so
/// two byte-equal cells never register as a spurious change. Order-stable,
/// deduplicated (a created/updated cell appears once; a removed cell — present
/// pre, absent post — is included so the overlay can delete it).
fn ledger_touched_diff(
    pre: &dregg_cell::Ledger,
    post: &dregg_cell::Ledger,
) -> Vec<dregg_cell::CellId> {
    let mut touched: Vec<dregg_cell::CellId> = Vec::new();
    // Created or updated: present in post with content differing from pre.
    for (id, cell) in post.iter() {
        match pre.get(id) {
            Some(prev) if prev == cell => {}
            _ => touched.push(*id),
        }
    }
    // Removed: present in pre, absent in post.
    for (id, _) in pre.iter() {
        if post.get(id).is_none() {
            touched.push(*id);
        }
    }
    touched
}

/// Provision any missing Transfer destination as a deterministic zero-balance
/// remote stub BEFORE a finalized turn executes, so the application is identical
/// on every node.
///
/// SOUNDNESS / UNIFORMITY. A finalized Transfer must execute the SAME on every
/// node, both in its attested root AND in resulting ledger content. The executor
/// rejects a Transfer whose destination cell is absent (`TransferDestNotFound`),
/// so a destination not yet seen locally must be materialized first. The recipient's
/// pre-image (its public key / token id) is NOT carried over consensus, so NO node
/// can reconstruct the canonical cell — instead every node provisions the IDENTICAL
/// landing site purely from the turn's data: a zero-balance, zero-pk stub at the
/// destination id (`Cell::remote_stub_with_id_and_balance`). Because the input
/// (the call forest) and the constructor are byte-deterministic, the provisioned
/// cell is byte-identical on every node — the submitter (which no longer provisions
/// authoritatively at faucet-submission in multi-party mode) and every peer.
///
/// This is destination PROVISIONING, not the turn's value semantics: the
/// conservation-checked Transfer still moves the exact amount into the (now-present)
/// stub. The whole forest is walked (`total_effects`), so a Transfer nested inside a
/// child action is provisioned too, not only root-level effects.
///
/// Idempotent: a destination already present (genesis cell, a prior turn, or a
/// peer that legitimately holds the canonical cell) is left untouched.
pub(crate) fn provision_transfer_destinations(
    ledger: &mut dregg_cell::Ledger,
    call_forest: &dregg_turn::CallForest,
) {
    for effect in call_forest.total_effects() {
        if let dregg_turn::Effect::Transfer { to, .. } = effect
            && ledger.get(to).is_none()
        {
            let stub = dregg_cell::Cell::remote_stub_with_id_and_balance(*to, 0);
            let _ = ledger.insert_cell(stub);
        }
    }
}

// The canonical full-ledger convergence root now lives ONCE in dregg-persist (the
// M4 "shared pub fn lift" — was duplicated here as `pub(crate)` + a byte-for-byte
// replica in starbridge-v2). Re-exported so node's callers
// (`crate::blocklace_sync::canonical_ledger_root`) are unchanged.
//
// BYTE-IDENTICAL to the prior in-module impl (verified by inspection — load-bearing
// for attested-root quorum convergence): the prior impl built `Vec<(CellId,[u8;32])>`,
// sorted by `CellId.0`, hashed `id.as_bytes()`; the shared fn builds
// `Vec<([u8;32],[u8;32])>` sorting/hashing `*id.as_bytes()`. Since
// `CellId(pub [u8;32])` derives `Ord` (sorts by `.0`) and `as_bytes()` returns
// `&self.0`, the sort order and the hashed id bytes are identical — same domain
// (`dregg-ledger-root-v2`), same length prefix, same whole-cell postcard leaves.
pub(crate) use dregg_persist::canonical_ledger_root;
