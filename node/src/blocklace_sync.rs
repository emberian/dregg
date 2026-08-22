//! Federation sync via the blocklace (Cordial Miners) consensus layer.
//!
//! Implements the live BFT consensus using the blocklace DAG structure from the
//! Cordial Miners paper (this superseded an earlier propose/vote/finalize BFT
//! simulation in `dregg_federation::node`). The blocklace provides:
//! - Quiescent operation (no messages when idle)
//! - Efficient cordial dissemination (send peers blocks you think they need)
//! - Leaderless total ordering via the tau function
//! - Equivocation detection AND exclusion in the data structure: detection pins
//!   the incomparable pair into the tips (`CreatorTips::Pair`, the CM Alg. 1:5
//!   two-tips floor) so the fork is carried into later closures, where tau's
//!   per-closure predicate excludes the equivocator (`node(b) ∉ byz(⌊b⌋)`,
//!   arXiv:2402.08068 §4.3; Lean `Dregg2.Distributed.ExclusionByPast`). The
//!   participant set NEVER changes on detection (flag day 2026-08-08 — the old
//!   gossip-arrival `auto_evict` was the F-CO-1 fork through a second door and
//!   reverted on restart)
//! - Constitutional membership amendments via voting — the ONLY membership door
//!
//! The node participates in consensus by:
//! 1. Creating blocks when turns are submitted
//! 2. Disseminating blocks to peers via the existing QUIC gossip transport
//! 3. Running tau() ordering to produce the finalized total order
//! 4. Processing finalized turns through the TurnExecutor

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use dregg_blocklace::constitution::{
    Constitution, ConstitutionManager, LeaveReason, MembershipProposal, MembershipVote,
};
use dregg_blocklace::dissemination::MAX_BLOCKS_PER_PUSH;
use dregg_blocklace::finality::{
    Block, BlockError, BlockId, Blocklace, ConsensusTimePolicyV1, ConsensusTimedTurnPayloadV1,
    CreatorTips, FinalityLevel, MembershipAction, Payload, TurnArtifactBundle,
};
use dregg_blocklace::ordering::tau;
use dregg_net::gossip::{GossipEvent, GossipNetwork, TopicHandle};
use dregg_net::message::PeerMessage;
use dregg_net::node::{NodeId, PeerNode, PeerNodeConfig};
use dregg_persist::BlocklaceMeta;
use tokio::sync::{Notify, RwLock};
use tracing::{debug, error, info, warn};

use crate::execution_cursor::FinalizedExecutionOutcome;
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

fn consensus_time_policy_v1_from_config(
    configured: Option<&str>,
    mode: Option<&str>,
) -> Result<ConsensusTimePolicyV1, String> {
    match mode {
        Some(crate::genesis::CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE) => {}
        Some(other) => {
            return Err(format!(
                "unsupported {}={other:?}; CTM1 currently supports only explicit devnet causal replay time, not federation-grade fair wall time",
                crate::genesis::CONSENSUS_TIME_V1_MODE_ENV
            ));
        }
        None => {
            return Err(format!(
                "missing required {}={} scope acknowledgement",
                crate::genesis::CONSENSUS_TIME_V1_MODE_ENV,
                crate::genesis::CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE
            ));
        }
    }
    let raw = configured.ok_or_else(|| {
        format!(
            "missing required deployment coordinate {} (re-run genesis or provide the persisted federation anchor)",
            crate::genesis::CONSENSUS_GENESIS_UNIX_SECONDS_ENV
        )
    })?;
    let anchor = raw.parse::<i64>().map_err(|error| {
        format!(
            "invalid {}={raw:?}: expected canonical signed Unix seconds ({error})",
            crate::genesis::CONSENSUS_GENESIS_UNIX_SECONDS_ENV
        )
    })?;
    Ok(ConsensusTimePolicyV1::new(anchor))
}

pub(crate) fn consensus_time_policy_v1_from_genesis(
    genesis: &serde_json::Value,
) -> Result<ConsensusTimePolicyV1, String> {
    let anchor = genesis["consensus_genesis_unix_seconds"]
        .as_i64()
        .ok_or_else(|| {
            "genesis.json is missing signed-integer consensus_genesis_unix_seconds".to_string()
        })?;
    let mode = genesis["consensus_time_mode"].as_str();
    consensus_time_policy_v1_from_config(Some(&anchor.to_string()), mode)
}

fn consensus_time_policy_v1_from_env() -> Result<ConsensusTimePolicyV1, String> {
    let configured =
        std::env::var(crate::genesis::CONSENSUS_GENESIS_UNIX_SECONDS_ENV).map_err(|error| {
            format!(
                "could not load {}: {error}",
                crate::genesis::CONSENSUS_GENESIS_UNIX_SECONDS_ENV
            )
        })?;
    let mode = std::env::var(crate::genesis::CONSENSUS_TIME_V1_MODE_ENV).map_err(|error| {
        format!(
            "could not load {}: {error}",
            crate::genesis::CONSENSUS_TIME_V1_MODE_ENV
        )
    })?;
    consensus_time_policy_v1_from_config(Some(&configured), Some(&mode))
}

/// Local wall time is only a proposal heuristic. The selected value is causally clamped, signed,
/// and thereafter replayed as immutable block content by every validator.
fn producer_wall_unix_seconds() -> Result<i64, String> {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("producer clock predates Unix epoch: {error}"))?
        .as_secs();
    i64::try_from(seconds).map_err(|_| "producer clock does not fit signed Unix seconds".into())
}

fn payload_for_consensus_time_v1(
    lace: &Blocklace,
    payload: Payload,
    predecessors: &[BlockId],
    producer_wall_unix_seconds: i64,
) -> Result<Payload, BlockError> {
    match payload {
        Payload::Turn(signed_turn) => {
            let consensus_time =
                lace.suggest_consensus_time_v1(predecessors, producer_wall_unix_seconds)?;
            Ok(Payload::ConsensusTimedTurnV1(
                ConsensusTimedTurnPayloadV1::new(consensus_time, signed_turn),
            ))
        }
        Payload::TurnBundle(bundle) => {
            let consensus_time =
                lace.suggest_consensus_time_v1(predecessors, producer_wall_unix_seconds)?;
            Ok(Payload::ConsensusTimedTurnV1(
                ConsensusTimedTurnPayloadV1::with_artifacts(
                    consensus_time,
                    bundle.signed_turn,
                    bundle.receipt,
                    bundle.witnessed_receipts,
                ),
            ))
        }
        already_timed @ Payload::ConsensusTimedTurnV1(_) => Ok(already_timed),
        non_turn => Ok(non_turn),
    }
}

/// The F2 durable-landing step shared by every LOCAL producer: persist a
/// just-authored block while its authoring write lock is STILL held; on a
/// persist I/O failure, roll it back out of `lace` and report `false` so the
/// caller does NOT broadcast an un-persisted authored block. Persisting inside
/// the lock is what makes the rollback exact — no concurrently-authored
/// successor can be stranded (the block is always our current self-tip). Returns
/// `true` when the block durably landed. See
/// [`dregg_blocklace::finality::Blocklace::rollback_local_authored`].
fn land_authored_or_rollback(
    store: &dregg_persist::PersistentStore,
    lace: &mut Blocklace,
    block: &Block,
) -> bool {
    if let Err(e) = store.persist_block(block) {
        warn!(
            error = %e,
            block_id = %block.id(),
            "authored block failed to persist durably — rolling it back out of the live \
             lace and NOT broadcasting (self-equivocation window closed)"
        );
        let rolled = lace.rollback_local_authored(block.id());
        debug_assert!(
            rolled,
            "the just-authored block must be the rollback-able self tip"
        );
        return false;
    }
    true
}

fn produce_payload_with_consensus_time_v1(
    lace: &mut Blocklace,
    payload: Payload,
    predecessors: Vec<BlockId>,
    producer_wall_unix_seconds: i64,
) -> Result<Block, BlockError> {
    let payload =
        payload_for_consensus_time_v1(lace, payload, &predecessors, producer_wall_unix_seconds)?;
    match payload {
        Payload::ConsensusTimedTurnV1(payload) => {
            lace.add_consensus_timed_turn_v1_with_predecessors(payload, predecessors)
        }
        non_turn => lace.try_add_block_with_predecessors(non_turn, predecessors),
    }
}

/// Test-only one-shot fault injection at the generic finalized durable barrier.
/// It exercises the real execute/prepare path while proving a store failure
/// publishes none of the isolated candidate into node RAM or subscriber state.
#[cfg(test)]
static FAIL_GENERIC_FINALIZED_COMMIT_FOR_BLOCK: std::sync::Mutex<Option<[u8; 32]>> =
    std::sync::Mutex::new(None);

/// Test-only idempotent-outcome injection. This pins that even a successful
/// store response does not republish RAM/events when the record was not fresh.
#[cfg(test)]
static REPLAY_GENERIC_FINALIZED_COMMIT_FOR_BLOCK: std::sync::Mutex<Option<[u8; 32]>> =
    std::sync::Mutex::new(None);

/// Test-only failure at the deterministic-rejection write. A rejection is a
/// terminal outcome only after its authenticated row is durable; before that,
/// the finalized block identity must remain retryable and unacknowledged.
#[cfg(test)]
static FAIL_FINALIZED_REJECTION_WRITE_FOR_BLOCK: std::sync::Mutex<Option<[u8; 32]>> =
    std::sync::Mutex::new(None);

/// A strictly-monotonic per-process counter stamped into every ANTI-ENTROPY
/// message so each SEND is byte-unique and cannot collapse under the gossip
/// layer's hash-dedup.
///
/// ⚑ WHY EVERY REPAIR MESSAGE NEEDS THIS, not just `Frontier`.
///
/// `GossipNetwork` dedups on `blake3(PeerMessage::encode_raw())` and the `seen`
/// set is the Plumtree flood terminator: a receiver that has the hash `return`s
/// before the subscriber ever sees the payload (`net/src/gossip.rs`, the
/// `s.seen.contains(&msg_hash)` arm). That is correct for FORWARDING — a
/// re-forward carries the originator's identical bytes, so the flood still
/// terminates — but it is wrong for a RETRANSMISSION, which is a new send of the
/// same content and must be delivered.
///
/// `Frontier` was given a nonce for exactly this reason and its doc names the
/// failure ("a permanent bootstrap deadlock"). `Push` / `Pull` / `PullResponse`
/// were left as pure content, and they are the messages that actually CARRY the
/// round cohort. The consequence, measured on hbox at n=4 on 2026-07-30:
///
///   * every node authored its round-8 block and eager-pushed it;
///   * one copy per peer was lost, so each node's lace held its OWN round-8
///     block and none of its peers' (`creator_max_rounds=[7,7,7,8]`,
///     `tip_seq_round=[(7,7),(7,7),(7,7),(8,8)]`, on ALL FOUR nodes);
///   * `plan_round_block` then needs 3 distinct creators at round 8 and sees 1,
///     so every node returned `RoundPlan::Wait` — forever;
///   * and the repair path could not help, because a WEDGED DAG produces a
///     FROZEN delta: `handle_frontier` recomputed the identical `Push(4 blocks)`
///     every tick, the identical `Pull([tip])` every backoff window, and every
///     one of them was byte-identical to the first and dropped at the receiver.
///
/// So the anti-entropy channel died at exactly the moment it was needed: the
/// instant the state stops changing, every retry is a duplicate. A client turn
/// submitted into that committee returned `accepted: true` and was re-staged by
/// the cadence ~90 times without ever entering a block.
fn gossip_send_nonce() -> u64 {
    static GOSSIP_SEND_NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    GOSSIP_SEND_NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
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
    ///
    /// `nonce` makes each SEND byte-unique — see [`gossip_send_nonce`]. Without
    /// it a wedged committee re-derives an identical delta every tick and the
    /// receiver's hash-dedup drops every copy after the first, so the round
    /// cohort can never be repaired.
    Push { blocks: Vec<Block>, nonce: u64 },
    /// Request blocks I'm missing. `nonce` per [`gossip_send_nonce`]: a re-request
    /// for the SAME missing ids is the whole point of the backoff loop, and is
    /// byte-identical without it.
    Pull { ids: Vec<BlockId>, nonce: u64 },
    /// Response to a pull request. `nonce` per [`gossip_send_nonce`]: answering
    /// two identical pulls must deliver twice, not once.
    PullResponse { blocks: Vec<Block>, nonce: u64 },
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
        /// Per-creator tips: the chain head, or — for a detected equivocator —
        /// the pinned evidence PAIR (CM Alg. 1:5 two-tips floor). ⚑ wire flag
        /// day 2026-08-08: the value type changed from a bare `BlockId`; mixed
        /// committees cannot parse each other's frontiers — redeploy together.
        tips: HashMap<[u8; 32], CreatorTips>,
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

/// One local round-production queue item. Private dependent turns retain their
/// durable reservation id until the cadence atomically persists the produced
/// block and consumes that reservation; ordinary ingress carries no id.
#[derive(Clone, Debug)]
pub struct PendingBlocklacePayload {
    payload: Payload,
    private_reservation_id: Option<[u8; 32]>,
}

impl PendingBlocklacePayload {
    fn ordinary(payload: Payload) -> Self {
        Self {
            payload,
            private_reservation_id: None,
        }
    }

    fn private(payload: Payload, reservation_id: [u8; 32]) -> Self {
        Self {
            payload,
            private_reservation_id: Some(reservation_id),
        }
    }
}

// ─── Federation liveness: what `/status` needs in order to say "I CANNOT finalize" ──
//
// ⚑ Measured on a real 4-node federation, threshold 3 (2026-08-08): with two
// members SIGSTOPped, the surviving 2-of-4 minority reported `healthy: true` and
// `consensus_live: true` for the full 210 s of the partition, while
// `latest_height` sat frozen at 1 and `dag_height` climbed 13 → 15 on its own
// heartbeat blocks. `peer_count` read 3 the whole time, because it counts
// CONFIGURED peers — a value read out of the launch flags, which cannot change no
// matter what the network does.
//
// (The sibling failure — a joiner permanently stuck outside the committee, also
// reporting an unqualified `healthy: true` — is covered by `JoinProgress`, not
// by this.)
//
// Neither reading was wrong about the fact it named. `consensus_live` means "the
// consensus task is attached"; `block_count > 0` means "this node has ever
// produced a block". Both stay true while the node talks only to itself. What
// was missing was any fact about the OTHER members: whether their votes are
// still arriving, and whether a quorum of them is still assemblable. That is
// what this records.

/// How recently a committee member's finalization vote must have been RECORDED
/// here for its link to count as LIVE.
///
/// Sized against vote CADENCE, not against a guess: every finalized block draws
/// one vote from every honest member, and the devnet's idle heartbeat alone
/// produces blocks every 2 s (`--idle-heartbeat-ms 2000`), with production
/// cadence faster still under load. 60 s is therefore tens of missed
/// opportunities — long enough that a GC pause, a slow round or a brief gossip
/// reconnect never flaps the signal, short enough that the 210 s partition above
/// is reported as unreachable for its last ~150 s.
pub const COMMITTEE_LIVENESS_WINDOW: Duration = Duration::from_secs(60);

/// How long this node may go without any block crossing consensus-wide quorum
/// before `/status` stops calling it healthy.
///
/// This is the "I have proposed and heard nothing" leg. It is deliberately
/// LONGER than [`COMMITTEE_LIVENESS_WINDOW`]: losing sight of a peer is a
/// warning, failing to finalize is the injury, and the injury should be reported
/// only once it is real rather than on a slow round.
pub const FINALITY_STALL_THRESHOLD: Duration = Duration::from_secs(90);

/// Upper bound on remembered in-flight turns. Reaching it means turns are being
/// submitted far faster than they finalize; the map is cleared wholesale rather
/// than grown (the same bounded-memory posture as `metrics::FINALITY_T0`). A
/// dropped entry costs a `pending` answer that degrades to `unknown`, never a
/// wrong one — `accepted` and `rejected` come from DURABLE rows, not from here.
const MAX_IN_FLIGHT_TURNS: usize = 8192;

/// Per-node record of who is still talking to us and when we last finalized.
///
/// Deliberately process-LOCAL and in-memory: it is an observation about this
/// node's own recent experience, not consensus state, and must never be
/// persisted or gossiped (a peer's claim about its own liveness is worth
/// nothing). Uses `std` locks, not tokio's — every critical section is a couple
/// of map operations with no await inside.
#[derive(Debug)]
pub struct FederationLiveness {
    /// Last instant a verified finalization vote from each committee identity
    /// was recorded here. Bounded by committee size.
    voter_last_seen: std::sync::Mutex<HashMap<[u8; 32], std::time::Instant>>,
    /// Last instant any block crossed the consensus-wide quorum threshold here.
    /// `None` until the first one does — which is itself the signal that a
    /// freshly started or permanently stuck node has never reached agreement.
    last_quorum: std::sync::Mutex<Option<std::time::Instant>>,
    /// When this handle was built. The baseline the stall clock runs from before
    /// any quorum exists, so "never finalized anything" reports as a stall
    /// instead of as an absence of evidence.
    started: std::time::Instant,
}

impl Default for FederationLiveness {
    fn default() -> Self {
        Self {
            voter_last_seen: std::sync::Mutex::new(HashMap::new()),
            last_quorum: std::sync::Mutex::new(None),
            started: std::time::Instant::now(),
        }
    }
}

impl FederationLiveness {
    /// A verified, member-signed finalization vote from `voter` was recorded.
    pub fn note_vote(&self, voter: &[u8; 32]) {
        self.voter_last_seen
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(*voter, std::time::Instant::now());
    }

    /// A block crossed the consensus-wide quorum threshold.
    pub fn note_quorum(&self) {
        *self.last_quorum.lock().unwrap_or_else(|p| p.into_inner()) =
            Some(std::time::Instant::now());
    }

    /// Distinct committee identities OTHER than `self_key` whose vote landed
    /// within [`COMMITTEE_LIVENESS_WINDOW`].
    fn live_remote_voters(&self, self_key: &[u8; 32]) -> usize {
        let now = std::time::Instant::now();
        self.voter_last_seen
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .iter()
            .filter(|(voter, seen)| {
                *voter != self_key && now.duration_since(**seen) <= COMMITTEE_LIVENESS_WINDOW
            })
            .count()
    }

    fn since_quorum(&self) -> Duration {
        let last = *self.last_quorum.lock().unwrap_or_else(|p| p.into_inner());
        std::time::Instant::now().duration_since(last.unwrap_or(self.started))
    }

    fn ever_reached_quorum(&self) -> bool {
        self.last_quorum
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .is_some()
    }

    /// The federation-health facts `/status` reports, derived at read time.
    ///
    /// `quorum_threshold` is the collector's live 2f+1 (it tracks committee
    /// reconfiguration), `connected_peers` the gossip layer's count of peers
    /// with an OPEN transport right now.
    pub fn snapshot(
        &self,
        self_key: &[u8; 32],
        quorum_threshold: usize,
        connected_peers: usize,
    ) -> FederationLivenessSnapshot {
        let live_committee_voters = self.live_remote_voters(self_key);
        // This node counts toward its own quorum: it signs its own finalization
        // votes. A threshold of 1 is therefore always reachable alone, which is
        // exactly right for a solo/collapsed deployment.
        let quorum_reachable = live_committee_voters + 1 >= quorum_threshold;
        let since_quorum = self.since_quorum();
        // With no cross-node quorum to lose there is no stall to detect: a
        // threshold-1 node finalizes on its own signature, and some solo paths
        // never route a vote through the collector at all. Reporting a stall
        // there would be a false alarm, not a stricter check.
        let finality_stalled = quorum_threshold > 1 && since_quorum > FINALITY_STALL_THRESHOLD;
        FederationLivenessSnapshot {
            live_committee_voters,
            quorum_threshold,
            quorum_reachable,
            connected_peers,
            ever_reached_quorum: self.ever_reached_quorum(),
            seconds_since_quorum: since_quorum.as_secs(),
            finality_stalled,
        }
    }
}

/// What this node can honestly say about its own ability to finalize.
#[derive(Clone, Copy, Debug)]
pub struct FederationLivenessSnapshot {
    /// Distinct OTHER committee members whose finalization vote landed here
    /// within [`COMMITTEE_LIVENESS_WINDOW`]. A LINK that carried consensus
    /// traffic — not a configured address.
    pub live_committee_voters: usize,
    /// The live 2f+1 the vote collector enforces.
    pub quorum_threshold: usize,
    /// `live_committee_voters + 1 >= quorum_threshold`: could a quorum be
    /// assembled from the members currently reaching us?
    pub quorum_reachable: bool,
    /// Peers with an open gossip transport right now (`GossipNetwork`).
    pub connected_peers: usize,
    /// Has any block EVER crossed consensus-wide quorum on this node? `false` on
    /// a joiner that never got in.
    pub ever_reached_quorum: bool,
    /// Seconds since the last consensus-wide quorum — or since this handle
    /// started, if there has never been one.
    pub seconds_since_quorum: u64,
    /// `seconds_since_quorum` past [`FINALITY_STALL_THRESHOLD`] on a federation
    /// with a real (>1) threshold.
    pub finality_stalled: bool,
}

/// Turn hashes this node has accepted for consensus and not yet seen a durable
/// verdict for.
///
/// ⚑ THE STATE A CLIENT COULD NOT NAME. A submitted turn's two terminal outcomes
/// are both durable — the commit log for accepted, the finalized-rejection row
/// for rejected — but between "the node answered `success: true`" and either of
/// those lies the finality lag (~30–60 s on the measured federation), and during
/// it every durable store is silent. A client polling by turn hash could not
/// tell that window from "dropped forever", which is the whole complaint.
///
/// This is the missing middle, and only that: it is in-memory (a restart forgets
/// it, and the answer honestly degrades to `unknown`), process-local, and it is
/// NEVER consulted for a terminal verdict. It answers exactly one question:
/// *did this node take this turn on, and has it not resolved it yet?*
#[derive(Debug, Default)]
pub struct InFlightTurns {
    submitted: std::sync::Mutex<HashMap<[u8; 32], std::time::Instant>>,
}

impl InFlightTurns {
    /// This node accepted `turn_hash` for consensus.
    pub fn note_submitted(&self, turn_hash: [u8; 32]) {
        let mut map = self.submitted.lock().unwrap_or_else(|p| p.into_inner());
        if map.len() >= MAX_IN_FLIGHT_TURNS {
            map.clear();
        }
        map.entry(turn_hash).or_insert_with(std::time::Instant::now);
    }

    /// A durable verdict landed for `turn_hash`; it is no longer in flight.
    pub fn resolve(&self, turn_hash: &[u8; 32]) {
        self.submitted
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .remove(turn_hash);
    }

    /// Seconds this node has been carrying `turn_hash` unresolved, if it is.
    pub fn pending_for_seconds(&self, turn_hash: &[u8; 32]) -> Option<u64> {
        self.submitted
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .get(turn_hash)
            .map(|since| std::time::Instant::now().duration_since(*since).as_secs())
    }

    /// How many turns this node is carrying unresolved.
    pub fn len(&self) -> usize {
        self.submitted
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ─── The narrow join channel, application half ──────────────────────────────
//
// ⚑ THE DEADLOCK THIS BREAKS, AT SOURCE. The federation could not grow, by
// three interlocking rings — each of which independently made a join
// impossible, and only the first was visible in the logs:
//
//  1. THE MESH. `dregg_net::gossip` resolves an envelope's `sender` in the
//     `peer_keys` registry and refuses what it cannot find. That registry is
//     seeded from the genesis committee (`peer_keys_map`, below) and extended in
//     exactly ONE place — `apply_committee_change` step 3 — which runs AFTER the
//     committee advanced. A candidate's key entered the mesh only once it was a
//     member; it could become a member only via a block the mesh refused.
//
//  2. THE ROSTER. Suppose the envelope got through. `catchup::apply_with_
//     buffering` → `Blocklace::receive_block_pinned` refuses any block whose
//     creator has no ENROLLED ML-DSA key (`BlockError::UnenrolledCreator`, and
//     correctly so — it must never trust a self-carried key). `enroll_pq` is
//     called at boot for the genesis committee and, again, in
//     `apply_committee_change`. Same shape, one layer down.
//
//  3. THE ORDER. Suppose the proposal were somehow ratified. A member's ML-DSA
//     half comes from the genesis-published, index-aligned roster, and NOTHING
//     on the wire carried a non-genesis candidate's. `project_committed_
//     participants` drops an admitted member with no committed ML-DSA key and
//     `poll_finalized_blocks` then FAILS CLOSED — so a SUCCESSFUL join would
//     have halted finality on every node. The residual was named in that
//     function's own comment and is now closed by `MembershipAction::Join`
//     carrying `ml_dsa_pubkey`.
//
// The repair does NOT open the mesh. A non-member may send exactly one envelope
// kind — a self-certifying [`JoinRequestBody`], size-capped and rate-limited —
// and it is not a block, never enters the lace, and registers nothing. A
// committee MEMBER validates it and authors the `Join` proposal under its OWN
// key, so rings 2 and 3 are never even approached by an unenrolled creator.

/// Domain separator for the ML-DSA proof of possession inside a join request.
const JOIN_REQUEST_PQ_BINDING_V1: &[u8] = b"dregg-join-request-pq-binding-v1";

/// The only accepted join-request version. Fail-closed on anything else.
const JOIN_REQUEST_VERSION: u8 = 1;

/// How often a non-member re-sends its join request while it waits.
const JOIN_REQUEST_RESEND: Duration = Duration::from_secs(15);

/// The application payload of a narrow-channel join request.
///
/// The gossip layer has already proven the sender holds the ed25519 key whose
/// hash is the envelope's `sender` id. This body adds the PQ half and PROVES
/// possession of it too, so the pair — and therefore the hybrid consensus id
/// `H(ed25519 ‖ ml_dsa)` the roster and tau schedule are keyed by — is genuinely
/// the candidate's and not a key it copied off the wire.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct JoinRequestBody {
    /// Format version. Refused unless [`JOIN_REQUEST_VERSION`].
    pub version: u8,
    /// The federation this request is for. A request minted against one chain
    /// must not be replayable into another.
    pub federation_id: [u8; 32],
    /// The candidate's ML-DSA-65 public key (FIPS 204 serialized, 1952 B).
    pub ml_dsa_pubkey: Vec<u8>,
    /// ML-DSA-65 signature over [`join_request_binding`], proving the candidate
    /// holds the PQ secret. Without it a candidate could name someone else's PQ
    /// key and mint a hybrid id it cannot sign blocks under — a member the
    /// committee would admit and then never hear from, which under the
    /// fail-closed projection is a permanent finality halt.
    pub pq_proof: Vec<u8>,
}

/// The bytes both halves of a join request are bound to.
fn join_request_binding(
    federation_id: &[u8; 32],
    ed25519: &[u8; 32],
    ml_dsa_pubkey: &[u8],
) -> Vec<u8> {
    let mut m = Vec::with_capacity(JOIN_REQUEST_PQ_BINDING_V1.len() + 64 + ml_dsa_pubkey.len());
    m.extend_from_slice(JOIN_REQUEST_PQ_BINDING_V1);
    m.extend_from_slice(federation_id);
    m.extend_from_slice(ed25519);
    m.extend_from_slice(ml_dsa_pubkey);
    m
}

/// A join request this node has validated and is holding for a sponsorship
/// decision (automatic under `auto_approve_joins`, otherwise an operator's).
#[derive(Clone)]
pub struct PendingJoinRequest {
    /// The candidate's ed25519 strand key — PROVEN, not claimed.
    pub node_id: [u8; 32],
    /// The candidate's ML-DSA-65 key — PROVEN by the request's `pq_proof`.
    pub ml_dsa_pubkey: dregg_federation::frost::MlDsaPublicKey,
    /// Where it reached us from (diagnostic only; never an authorization input).
    pub from: SocketAddr,
    /// When we first accepted a request from this candidate.
    pub first_seen: std::time::Instant,
    /// The proposal block, once some node's sponsorship of this candidate has
    /// been observed — so a re-sent request does not open a second proposal.
    pub proposed: Option<BlockId>,
}

/// Upper bound on candidates held awaiting sponsorship. A join is an
/// operator-scale event; this only has to be larger than any real committee.
const MAX_PENDING_JOIN_REQUESTS: usize = 64;

/// Depth of the queue between join ADMISSION (the narrow-channel receiver) and
/// join SPONSORSHIP (the task that authors the `Join` proposal).
///
/// One slot per admissible candidate: a candidate that cannot be held in
/// `pending_joins` at all can never be queued here, so a deeper queue would only
/// buffer duplicates of candidates already waiting. Bounded on purpose — the
/// receiver `try_send`s and moves on, so a full queue delays a sponsorship by
/// one 15 s candidate retry and delays no validation at all.
const SPONSOR_QUEUE_CAPACITY: usize = MAX_PENDING_JOIN_REQUESTS;

/// What this node's OWN join attempt has achieved, for `/status`.
///
/// ⚑ THIS EXISTS BECAUSE A WEDGED JOINER REPORTED `"healthy": true`. `/status`'s
/// `healthy` is `store_ok && consensus_live && block_count > 0`, all three of
/// which a permanently-stuck non-member satisfies: its store is fine, its
/// consensus task is running, and it authored its own genesis block. It sat at
/// `dag_height=1, latest_height=0` for the life of the process, having reached
/// no one, and said it was healthy. A node that has asked to join and heard
/// nothing must SAY so.
#[derive(Clone, Debug, Default)]
pub struct JoinProgress {
    /// True once our own key is a constitutional participant.
    pub member: bool,
    /// How many join requests we have sent, and to how many live peers.
    pub requests_sent: u64,
    pub last_request_peers: usize,
    /// Seconds since we first asked to join, while still not a member.
    pub waiting_secs: u64,
    /// True once we have observed a Join proposal for OUR key in the
    /// constitution — i.e. the request demonstrably reached a member.
    pub proposal_seen: bool,
}

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
    /// Candidates that reached us over the narrow join channel and passed
    /// validation, keyed by their ed25519 strand key. This is the ONLY source of
    /// a non-genesis candidate's ML-DSA key — `ML-DSA.KeyGen` needs the seed, so
    /// no peer can derive it — which is why `propose_membership` refuses an add
    /// for a candidate with no entry here and no committed key rather than
    /// authoring a Join that would halt finality on ratification.
    pub pending_joins: Arc<RwLock<HashMap<[u8; 32], PendingJoinRequest>>>,
    /// This node's own join progress, surfaced by `/status` so a stuck joiner
    /// stops reporting an unqualified `"healthy": true`.
    pub join_progress: Arc<RwLock<JoinProgress>>,
    /// Our OWN ML-DSA-65 public key. Needed as a VALUE (not just the signing
    /// key) because a join request must publish the PQ half no peer can derive.
    pub pq_public_key: dregg_federation::frost::MlDsaPublicKey,
    /// The configured gossip peer addresses. The narrow join channel sends to
    /// these directly: a non-member has no topic and therefore no publish path.
    pub peer_addrs: Vec<SocketAddr>,
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
    /// CM Alg. 4:75's clock for the ES ROUND-ADVANCE GATE: *"timeout is measured from when round
    /// r is cordial."* Armed at the first production attempt where the current round planned an
    /// `Advance` (= the first local observation of cordiality at that round); consulted by
    /// [`Self::es_advance_hold`] to derive the `timeoutFired` bit the verified Lean gate
    /// (`Dregg2.Distributed.RoundAdvanceGate.advanceGate`, `@[export] dregg_round_advance`)
    /// takes as input. The RULE lives in Lean; this is only the clock (time is I/O).
    /// ⚠ NOT `blocklace_wave_timeout_ms` — that is governance proposal expiry.
    pub round_advance_timer: Arc<std::sync::Mutex<crate::round_advance_gate::RoundAdvanceTimer>>,
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
    /// HYBRID-PQ: this node's ML-DSA-65 signing key, derived deterministically
    /// from the same `node.key` seed as `signing_key` (so it needs no separate
    /// key file). Signs the post-quantum half of every finalization vote.
    pub pq_signing_key: dregg_federation::frost::MlDsaSigningKey,
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
    pub pending_payloads: Arc<RwLock<std::collections::VecDeque<PendingBlocklacePayload>>>,
    /// CROSS-POLL VERIFIED-ORDER CACHE (fingerprint half). A cheap `u64` hashed
    /// over the SORTED block-id set of the lace at the last poll whose verified
    /// Lean tau-order FFI succeeded. Block ids are blake3 content hashes, so an
    /// identical sorted id-set ⇒ an identical lace ⇒ an identical deterministic
    /// `tauOrder`; a fingerprint MATCH lets `poll_finalized_blocks` reuse
    /// `last_lean_order` and SKIP the O(history) FFI, a MISMATCH forces a
    /// recompute (never a stale order for a changed lace). See
    /// `docs/VERIFIED-GATE-PERF.md`.
    pub last_order_fingerprint: Arc<RwLock<Option<u64>>>,
    /// CROSS-POLL VERIFIED-ORDER CACHE (order half). The finalized tau-order computed at the
    /// poll recorded by `last_order_fingerprint`, PAIRED WITH ITS PROVENANCE: `true` when the
    /// verified Lean `dregg_tau_order` FFI produced it, `false` when it is the un-verified Rust
    /// `ordering::tau` order a budget-missing / export-missing poll fell back to. Reused verbatim
    /// on a fingerprint hit; overwritten on every recompute.
    ///
    /// ⚑ THE FLAG IS THE POINT. This was a bare `Vec<BlockId>`, so a fallback poll stored an
    /// UN-VERIFIED order indistinguishably from a verified one — and since the cache is keyed on
    /// the finalized ORDER (stable while finality is not advancing), every later poll served that
    /// un-verified order under a `debug!("verified-order cache HIT")` line. One WARN at the
    /// timeout, then an unbounded silent run. Provenance now rides the cache, so a hit is counted
    /// and logged as what it actually is and `ordered_from_lean` cannot be laundered by it.
    pub last_lean_order: Arc<RwLock<Option<(Vec<BlockId>, bool)>>>,
    /// Who is still voting at us, and when we last reached quorum — the facts
    /// `/status` needs to say "I cannot finalize". See [`FederationLiveness`].
    pub liveness: Arc<FederationLiveness>,
    /// Turns this node took on and has not yet resolved, so a client polling by
    /// turn hash can be told "pending" instead of nothing. See [`InFlightTurns`].
    pub in_flight_turns: Arc<InFlightTurns>,
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
        self.block_views_page(0, usize::MAX).await
    }

    /// ANON-DoS #2 — a BOUNDED window of the height-ordered block views:
    /// `limit` views starting at `offset` in (seq, creator) order. The full-scan
    /// [`Self::block_views`] delegates here with an unbounded window; the public
    /// `GET /api/blocklace/blocks` handler passes a capped `limit` so an anon
    /// caller cannot force materialization + serialization of the ENTIRE lace.
    /// Only the requested window is turned into `BlockView`s (the per-block hex
    /// allocation), so the work is bounded by `limit`, not the lace size.
    pub async fn block_views_page(&self, offset: usize, limit: usize) -> Vec<BlockView> {
        let lace = self.lace.read().await;
        let quorum = {
            let c = self.constitution.read().await;
            c.threshold()
        };
        let mut blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
        blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));
        blocks
            .into_iter()
            .skip(offset)
            .take(limit)
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
                    Payload::ConsensusTimedTurnV1(_) => "consensus_timed_turn_v1",
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

    /// What this node can honestly say about its own ability to finalize:
    /// which committee members are still voting at us, over an OPEN transport,
    /// against the collector's live 2f+1.
    ///
    /// Every input is a measurement, not a configuration: the threshold comes
    /// from the vote collector (so it tracks committee reconfiguration), the
    /// connected count from the gossip layer's open-transport set, and the voter
    /// set from votes this node actually admitted.
    pub async fn federation_liveness(&self) -> FederationLivenessSnapshot {
        let quorum_threshold = self.votes.read().await.quorum_threshold();
        let connected_peers = self.gossip.connected_peer_count().await;
        self.liveness
            .snapshot(&self.self_key, quorum_threshold, connected_peers)
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

impl FinalizedBlock {
    const fn block_id(&self) -> BlockId {
        match self {
            Self::Turn { block_id, .. }
            | Self::Membership { block_id, .. }
            | Self::Checkpoint { block_id, .. }
            | Self::Inert { block_id } => *block_id,
        }
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
        consensus_time: Option<i64>,
    },
    /// A membership vote/proposal ready for constitution processing.
    Membership {
        block_id: BlockId,
        /// The proposer/voter's **ed25519 strand key** (`Block::ed25519`) — the
        /// identity space `Constitution::participants` is keyed by, and the ONLY
        /// one `ConstitutionManager::submit_vote`'s `is_participant` gate can
        /// accept. Deliberately NOT `Block::creator`: that is the HYBRID
        /// consensus id `H(ed25519 ‖ ml_dsa)`, which is never equal to any
        /// constitution member, so handing it over refuses every vote silently.
        /// Named for its space so the two can never be swapped by a reader
        /// reaching for the nearest `creator` field.
        creator_ed25519: [u8; 32],
        action: MembershipAction,
    },
    /// A checkpoint (no active processing needed at consensus level).
    Checkpoint {
        block_id: BlockId,
        root: [u8; 32],
        height: u64,
    },
    /// Consensus-inert payload. It has no application-side durable outcome and
    /// may be acknowledged immediately after planning.
    Inert { block_id: BlockId },
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

    /// Submit an already-admitted private dependent turn under its durable
    /// ingress reservation.
    ///
    /// Solo production constructs on an isolated lace clone, atomically stores
    /// the exact block plus `Submitted(block_id)`, then installs/broadcasts the
    /// clone. Multi-party production stages the reservation id beside the
    /// payload; the round cadence performs that same atomic cut when a legal
    /// round is available. `None` therefore means safely queued, not accepted.
    /// A restart never calls this method for an old `Claimed` row: recovery
    /// reconciles finalized identity only and does not blind-resend.
    pub async fn submit_private_dependent_turn(
        &self,
        state: &NodeState,
        reservation_id: [u8; 32],
        turn_data: Vec<u8>,
    ) -> Result<Option<BlockId>, String> {
        let payload = Payload::Turn(turn_data);
        let n_participants = {
            let c = self.constitution.read().await;
            c.current.participant_count()
        };
        if n_participants > 1 {
            self.pending_payloads
                .write()
                .await
                .push_back(PendingBlocklacePayload::private(payload, reservation_id));
            self.finality_notify.notify_one();
            return Ok(None);
        }

        let store = { state.read().await.store.clone() };
        let block = {
            let mut live = self.lace.write().await;
            let mut candidate = live.clone();
            let predecessors: Vec<BlockId> = candidate.tip_ids();
            let producer_wall = producer_wall_unix_seconds()?;
            let block = produce_payload_with_consensus_time_v1(
                &mut candidate,
                payload,
                predecessors,
                producer_wall,
            )
            .map_err(|error| format!("private dependent block production failed: {error}"))?;
            store
                .accept_private_dependent_ingress_block_v1(reservation_id, &block)
                .map_err(|error| {
                    format!("private dependent ingress durable accept failed: {error}")
                })?;
            *live = candidate;
            block
        };
        let block_id = block.id();
        *self.last_produced.write().await = std::time::Instant::now();
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        Ok(Some(block_id))
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
    pub async fn submit_heartbeat(&self, state: &NodeState) -> Option<BlockId> {
        // Fail-closed (F2): the heartbeat advances our self strand's seq, so it
        // must durably land before it is broadcast — otherwise a persist failure
        // + crash lets restart re-author this seq with different content
        // (self-equivocation). On failure the block is rolled back and not sent.
        let block = self
            .author_add_block_or_rollback(state, Payload::Ack)
            .await?;
        let block_id = block.id();
        *self.last_produced.write().await = std::time::Instant::now();

        // Heartbeats still advance ordering bookkeeping (the finality executor
        // treats Ack as a no-op for execution but the seq/tip have advanced).
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        debug!(block_id = %block_id, seq = block.seq, "produced heartbeat block");
        Some(block_id)
    }

    /// THE ES ROUND-ADVANCE GATE (CM Alg. 4:67–75) — consulted after `plan_round_block` says
    /// `Advance` and BEFORE the block is authored. Returns `None` when the round may advance,
    /// `Some(reason)` when this producer must HOLD the round this tick.
    ///
    /// The RULE is the verified Lean `Dregg2.Distributed.RoundAdvanceGate.advanceGate`
    /// (`@[export] dregg_round_advance`; `round_advance_eq_gate` proves the wire verdict IS the
    /// predicate): advance a cordial round only when the wave leader's block is present (wave
    /// start) / ratified (mid-wave) / super-ratified (wave end) — or the timeout fired. CM §6.2:
    /// the clauses exist because with a prospective (round-robin, genesis-published) leader the
    /// adversary knows the schedule in advance; `plan_round_block` alone is the ASYNCHRONY
    /// instance's advance rule (Alg. 4:59) and enforced no leader clause at all. Prop. 38's
    /// liveness needs `timeout > ∆` — the timeout and its stated ∆ assumption live in
    /// `crate::round_advance_gate::round_advance_timeout_ms` (⚠ NOT `blocklace_wave_timeout_ms`,
    /// which is governance proposal expiry).
    ///
    /// The participant set is the SAME admission-filtered, committed-hybrid-id projection the
    /// finalizer uses (`poll_finalized_blocks`'s pipeline): the gate picks the wave leader by
    /// matching `participants[wave % n]` against block creators, so feeding it any other set
    /// would gate against a different schedule than the one τ anchors.
    ///
    /// Fail-safety: a linked-but-erroring gate HOLDS unconditionally (an `ERR` is our encoder
    /// bug); an ABSENT export takes the declared bypasses of `es_gate_bypass_allowed`
    /// (archive-less build / `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, both revoked by
    /// `DREGG_REQUIRE_LEAN=1`) back to the pre-gate cordiality-only advance, loudly.
    async fn es_advance_hold(
        &self,
        state: &NodeState,
        lace: &Blocklace,
        completing_round: u64,
    ) -> Option<String> {
        let raw_participants = {
            let c = self.constitution.read().await;
            c.current.participants.clone()
        };
        let admitted = crate::strand_admission_gate::admitted_participants(
            &raw_participants,
            &raw_participants,
        );
        let participants: Vec<[u8; 32]> = project_committed_participants(state, &admitted).await;
        let timeout_ms = crate::round_advance_gate::round_advance_timeout_ms();
        let timeout_fired = self
            .round_advance_timer
            .lock()
            .expect("round-advance timer poisoned")
            .timeout_fired(completing_round, timeout_ms);
        use crate::round_advance_gate::EsAdvanceConsult;
        match crate::round_advance_gate::consult(
            lace,
            &participants,
            completing_round,
            timeout_fired,
        ) {
            EsAdvanceConsult::Advance => None,
            EsAdvanceConsult::Hold => {
                let waiting_ms = self
                    .round_advance_timer
                    .lock()
                    .expect("round-advance timer poisoned")
                    .waiting_ms(completing_round);
                Some(format!(
                    "ES round-advance HOLD: round {completing_round} is cordial but the wave \
                     leader's block is not yet present/ratified/super-ratified (waited \
                     {waiting_ms} ms of the {timeout_ms} ms timeout)"
                ))
            }
            EsAdvanceConsult::GateError(e) => Some(format!(
                "ES round-advance gate ERROR at round {completing_round} (HOLDING, fail-closed): {e}"
            )),
            EsAdvanceConsult::ExportUnavailable(e) => {
                if crate::round_advance_gate::es_gate_bypass_allowed(
                    dregg_lean_ffi::round_advance_available(),
                    allow_unverified_consensus(),
                    require_verified_lean_gate(),
                ) {
                    warn!(
                        completing_round,
                        "ES round-advance export absent — DECLARED BYPASS taken (archive-less \
                         build or DREGG_ALLOW_UNVERIFIED_CONSENSUS=1): advancing on cordiality \
                         alone, the pre-gate asynchrony rule"
                    );
                    None
                } else {
                    Some(format!(
                        "ES round-advance export missing at round {completing_round} and no \
                         declared bypass (DREGG_REQUIRE_LEAN revokes them): {e}"
                    ))
                }
            }
        }
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
        let producer_wall = match producer_wall_unix_seconds() {
            Ok(seconds) => seconds,
            Err(error) => {
                warn!(
                    error,
                    "producer clock unavailable; proposing the causal minimum for this round"
                );
                i64::MIN
            }
        };
        let supermajority = {
            let c = self.constitution.read().await;
            dregg_blocklace::ordering::supermajority_threshold(c.current.participant_count())
        };
        // Fail-closed (F2): the round block advances our self strand, so it must
        // durably land BEFORE broadcast. `RoundPlan::Wait` (no supermajority yet)
        // is normal backpressure, not an error — surface it as `None` without a
        // wasted persist by short-circuiting before authoring.
        let store = { state.read().await.store.clone() };
        let mut lace = self.lace.write().await;
        let plan = plan_round_block(&lace, lace.self_creator(), supermajority);
        let produced = match plan {
            RoundPlan::Wait {
                my_max_round,
                cohort_creators,
                creator_max_rounds,
            } => {
                let mut tip_seq_round: Vec<(u64, u64)> = lace
                    .tips()
                    .values()
                    .flat_map(CreatorTips::iter)
                    .map(|t| {
                        (
                            lace.get(&t).map(|b| b.seq).unwrap_or(0),
                            lace.round_of(&t).unwrap_or(0),
                        )
                    })
                    .collect();
                tip_seq_round.sort_unstable();
                debug!(
                    my_max_round,
                    cohort_creators,
                    supermajority,
                    lace_size = lace.len(),
                    ?creator_max_rounds,
                    ?tip_seq_round,
                    "round production WAITING: too few distinct creators at our current round"
                );
                return None;
            }
            RoundPlan::Genesis => produce_payload_with_consensus_time_v1(
                &mut lace,
                payload,
                Vec::new(),
                producer_wall,
            ),
            RoundPlan::Advance {
                predecessors,
                next_round,
            } => {
                // ── THE ES ROUND-ADVANCE GATE (CM Alg. 4:67–75, Lean-decided) ────────────
                // `plan_round_block` is only line 68's cordiality; lines 69–75 (leader
                // present/ratified/super-ratified ∨ timeout) are the verified gate. See
                // `es_advance_hold`'s docstring for the rule, the ∆ assumption, and the
                // fail-safety ladder.
                let completing_round = next_round.saturating_sub(1);
                if let Some(hold) = self.es_advance_hold(state, &lace, completing_round).await {
                    debug!(
                        completing_round,
                        %hold,
                        "round production HOLDING: cordial, but the ES advance gate refused"
                    );
                    return None;
                }
                produce_payload_with_consensus_time_v1(
                    &mut lace,
                    payload,
                    predecessors,
                    producer_wall,
                )
            }
        };
        let block = match produced {
            Ok(block) => block,
            Err(error) => {
                error!(%error, "consensus-time-v1 refused round block production");
                return None;
            }
        };
        if !land_authored_or_rollback(&store, &mut lace, &block) {
            return None;
        }
        drop(lace);

        let block_id = block.id();
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

    /// Round-disciplined counterpart of [`Self::submit_private_dependent_turn`].
    /// The live lace remains untouched unless the exact produced block and the
    /// reservation's Submitted transition commit together.
    async fn produce_private_dependent_round_block(
        &self,
        state: &NodeState,
        payload: Payload,
        reservation_id: [u8; 32],
    ) -> Result<Option<BlockId>, String> {
        let producer_wall = producer_wall_unix_seconds()?;
        let supermajority = {
            let c = self.constitution.read().await;
            dregg_blocklace::ordering::supermajority_threshold(c.current.participant_count())
        };
        let store = { state.read().await.store.clone() };
        let block = {
            let mut live = self.lace.write().await;
            let mut candidate = live.clone();
            let plan = plan_round_block(&candidate, candidate.self_creator(), supermajority);
            let produced = match plan {
                RoundPlan::Wait { .. } => return Ok(None),
                RoundPlan::Genesis => produce_payload_with_consensus_time_v1(
                    &mut candidate,
                    payload,
                    Vec::new(),
                    producer_wall,
                ),
                RoundPlan::Advance {
                    predecessors,
                    next_round,
                } => {
                    // ── THE ES ROUND-ADVANCE GATE — same gate as `produce_round_block`'s
                    // Advance arm (one rule, both producers; a private-dependent turn must not
                    // advance a round the public producer would hold).
                    let completing_round = next_round.saturating_sub(1);
                    if let Some(hold) = self
                        .es_advance_hold(state, &candidate, completing_round)
                        .await
                    {
                        debug!(
                            completing_round,
                            %hold,
                            "private-dependent round production HOLDING: cordial, but the ES \
                             advance gate refused"
                        );
                        return Ok(None);
                    }
                    produce_payload_with_consensus_time_v1(
                        &mut candidate,
                        payload,
                        predecessors,
                        producer_wall,
                    )
                }
            }
            .map_err(|error| format!("private dependent round block production failed: {error}"))?;
            store
                .accept_private_dependent_ingress_block_v1(reservation_id, &produced)
                .map_err(|error| {
                    format!("private dependent round durable accept failed: {error}")
                })?;
            *live = candidate;
            produced
        };

        let block_id = block.id();
        *self.last_produced.write().await = std::time::Instant::now();
        self.finality_notify.notify_one();
        self.push_new_blocks().await;
        debug!(
            block_id = %block_id,
            seq = block.seq,
            npreds = block.predecessors.len(),
            reservation_id = %dregg_types::hex_encode(&reservation_id),
            "produced atomically reserved private dependent round block"
        );
        Ok(Some(block_id))
    }

    async fn submit_turn_payload(
        &self,
        state: &NodeState,
        payload: Payload,
    ) -> (BlockId, FinalityLevel) {
        // THE MOMENT THE NODE TAKES RESPONSIBILITY. Everything after this returns
        // a `turn_hash` to the caller, so from here until a durable verdict lands
        // the honest answer to "what happened to my turn?" is `pending` — and
        // until now the node had no way to give it. Recorded for BOTH paths (the
        // n>1 staging return and the solo direct production below); resolved by
        // `persist_finalized_payload_rejection` and by the commit-log lookup that
        // `GET /api/turn/{hash}/verdict` performs.
        if let Some(turn_hash) = payload_signed_turn_hash(&payload) {
            self.in_flight_turns.note_submitted(turn_hash);
        }
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
            let depth = {
                let mut q = self.pending_payloads.write().await;
                q.push_back(PendingBlocklacePayload::ordinary(payload));
                q.len()
            };
            // SUBMISSION-PATH TRACE. The staging step is the FIRST of the four
            // places a submitted turn can be lost (never enqueued / enqueued and
            // never drained / drained and never planned / planned and never
            // finalized), and until 2026-07-30 none of the four was observable:
            // an operator watching a turn that "returned accepted:true and never
            // appeared" had no way to tell them apart without patching the node.
            // This line plus the `carried a STAGED turn payload` /
            // `RE-STAGED` pair in `cadence_tick_round_driven` separate all four.
            info!(
                receipt = %receipt,
                queue_depth = depth,
                "submission STAGED for round-driven production (n>1); the cadence carries it \
                 in its next round block"
            );
            // Nudge the cadence/executor so the staged turn is picked up promptly.
            self.finality_notify.notify_one();
            return (receipt, FinalityLevel::Local);
        }

        // SOLO (n=1): tau finalizes every block trivially in sequence, so produce
        // the turn block immediately (linking current tips) — no round discipline.
        // Fail-closed (F2): the solo turn advances our self strand, so it must
        // durably land BEFORE broadcast; a persist failure rolls it back (it is
        // not ordered/final) rather than serving an un-persisted authored turn.
        let store = { state.read().await.store.clone() };
        let mut lace = self.lace.write().await;
        let predecessors: Vec<BlockId> = lace.tip_ids();
        let producer_wall = match producer_wall_unix_seconds() {
            Ok(seconds) => seconds,
            Err(error) => {
                warn!(
                    error,
                    "producer clock unavailable; proposing the causal minimum for solo turn"
                );
                i64::MIN
            }
        };
        let block =
            produce_payload_with_consensus_time_v1(&mut lace, payload, predecessors, producer_wall)
                .expect(
                    "configured live consensus-time-v1 must admit a locally produced solo turn",
                );
        let block_id = block.id();
        if !land_authored_or_rollback(&store, &mut lace, &block) {
            // The turn did NOT durably land and was withdrawn from the live lace.
            // Report it as not-ordered (Local): no live caller reads this handle,
            // and the turn simply never finalizes (the client observes no receipt
            // and may retry). Never Ordered — that would ack a lost turn.
            error!(block_id = %block_id, "solo turn failed to persist durably — withdrawn, not broadcast");
            return (block_id, FinalityLevel::Local);
        }
        drop(lace);

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

    /// Author a local block and DURABLY LAND IT before it can be broadcast —
    /// the fail-closed producer step that closes the self-equivocation window
    /// (node durability finding F2).
    ///
    /// `author` mutates the write-locked lace and returns the new block (its
    /// `(creator, seq)` advances the self strand). The block is persisted while
    /// that write lock is STILL held, so on a persist I/O failure it is rolled
    /// back out of the live lace ([`Blocklace::rollback_local_authored`]) —
    /// keeping the live lace equal to durable state — and `None` is returned so
    /// the caller does NOT broadcast it. Boot rebuilds the self strand's next
    /// sequence from PERSISTED blocks only; without this, an authored-but-
    /// unpersisted-yet-broadcast block would be re-authored at the same
    /// `(creator, seq)` with different content after a crash (a slashable
    /// self-equivocation).
    ///
    /// The store handle is captured BEFORE the lace lock (deadlock-free order,
    /// as in `produce_private_dependent_round_block`). `Some(block)` ⇒ the block
    /// durably landed and the caller may broadcast; `None` ⇒ production was
    /// refused OR the block was withdrawn (never broadcast).
    async fn author_persist_or_rollback<F>(&self, state: &NodeState, author: F) -> Option<Block>
    where
        F: FnOnce(&mut Blocklace) -> Result<Block, BlockError>,
    {
        let store = { state.read().await.store.clone() };
        let mut lace = self.lace.write().await;
        let block = match author(&mut lace) {
            Ok(block) => block,
            Err(e) => {
                error!(%e, "local block production refused before persist");
                return None;
            }
        };
        if land_authored_or_rollback(&store, &mut lace, &block) {
            Some(block)
        } else {
            None
        }
    }

    /// Author a plain `add_block(payload)` fail-closed (see
    /// [`Self::author_persist_or_rollback`]). Used by the heartbeat + membership
    /// producers, whose payloads (`Ack` / `MembershipVote`) never trip the
    /// consensus-time admission that `add_block` asserts.
    async fn author_add_block_or_rollback(
        &self,
        state: &NodeState,
        payload: Payload,
    ) -> Option<Block> {
        self.author_persist_or_rollback(state, move |lace| Ok(lace.add_block(payload)))
            .await
    }

    /// Push new blocks to peers via the gossip topic.
    ///
    /// Broadcasts all blocks from our local blocklace that peers may not have.
    /// In practice, since we broadcast on a topic, all subscribed peers see it.
    /// The protocol is quiescent: this is only called when we create a new block.
    ///
    /// ⚑ `lace.tips()` IS KEYED BY `Block::creator`, WHICH IS THE HYBRID ID
    /// `H(ed25519 ‖ ml_dsa)` — NOT `self.self_key`, which is the ed25519 verify
    /// key (`run_blocklace_sync_with_policy` derives it as
    /// `signing_key.verifying_key()`). This function read `tips().get(&self_key)`
    /// from 2026-05-23 until 2026-07-30, and `9f5920bda` (2026-07-09) re-based
    /// `Block::creator` onto the hybrid id — after which the lookup could NEVER
    /// match and **every authored block's one-shot eager push was a silent
    /// no-op.** Block dissemination then depended entirely on the periodic
    /// frontier-reconciliation delta, which shares one serial `forward_loop`
    /// with the Plumtree prune traffic; measured on hbox at n=3, that queue ran
    /// 7.1 s behind and stalled outright, so the round cohort never completed
    /// and — with `supermajority_threshold(3) == 3` — the committee wedged
    /// permanently at the first round. Same class as the six `block.creator`
    /// consumers the finality-gate work found reading it as ed25519.
    async fn push_new_blocks(&self) {
        let lace = self.lace.read().await;

        // Get our latest block (just the one we created). Keyed by our HYBRID
        // creator id, the value `Block::new` actually stamps.
        let our_tip = match lace.creator_tip(&lace.self_creator()) {
            Some(tip) => tip,
            None => {
                debug!(
                    self_creator = %dregg_types::hex_encode(&lace.self_creator()[..4]),
                    tips = lace.tips().len(),
                    "push_new_blocks: no tip for our own creator id — nothing authored yet"
                );
                return;
            }
        };

        // Send the block (and its immediate context) to peers.
        if let Some(block) = lace.get(&our_tip) {
            debug!(
                block_id = %our_tip,
                seq = block.seq,
                round = lace.round_of(&our_tip).unwrap_or(0),
                "push_new_blocks: eager-broadcasting our own tip"
            );
            let msg = BlocklaceGossipMessage::Push {
                blocks: vec![block.clone()],
                nonce: gossip_send_nonce(),
            };
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
        let frontier_tips: HashMap<[u8; 32], CreatorTips> = {
            let lace = self.lace.read().await;
            let tips = lace.tips();
            // DAG structure gauges (emitted under the lace lock, so they reflect a
            // single consistent view): frontier width = number of per-creator tips;
            // depth = the maximum round across those tips (both halves of a
            // pinned equivocation pair count — they are announced tips too).
            crate::metrics::set_blocklace_frontier(tips.len() as f64);
            let depth = tips
                .values()
                .flat_map(CreatorTips::iter)
                .filter_map(|t| lace.round_of(&t))
                .max()
                .unwrap_or(0);
            crate::metrics::set_blocklace_depth(depth as f64);
            let mut announced: Vec<(u64, u64)> = tips
                .values()
                .flat_map(CreatorTips::iter)
                .map(|t| {
                    (
                        lace.get(&t).map(|b| b.seq).unwrap_or(0),
                        lace.round_of(&t).unwrap_or(0),
                    )
                })
                .collect();
            announced.sort_unstable();
            debug!(
                ?announced,
                "frontier: announcing our per-creator tips (seq, round)"
            );
            tips.iter().map(|(k, v)| (*k, *v)).collect()
        };
        let msg = BlocklaceGossipMessage::Frontier {
            tips: frontier_tips,
            nonce: gossip_send_nonce(),
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
    /// finalized predecessors, and pulling them (each reply a bounded ancestry
    /// window, [`MAX_PULL_RESPONSE_BLOCKS`]) drains the buffer toward the
    /// finalized prefix, one window per sweep for the deepest gaps.
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
                // ROTATING TARGET (2026-08-08, the retry half of targeted
                // fetch): the reactive pull already asked the peer that
                // REVEALED each gap (`handle_push`) — if we are here, that ask
                // was lost, refused, or the peer does not have the block after
                // all. Retry against ONE topic peer, advancing round-robin per
                // sweep, so a withholding/dead peer costs one backoff window
                // and full peer coverage arrives within n sweeps — Mysticeti's
                // likely-holder-first-then-rotate, with rotation instead of
                // random sampling for guaranteed small-n coverage. The old
                // topic-wide broadcast asked everyone and had EVERY holder
                // answer with a full history dump.
                if sync_baseline() {
                    // ⚠ TEMPORARY MEASUREMENT SCAFFOLD.
                    self.broadcast_gossip_message(&BlocklaceGossipMessage::Pull {
                        ids: due,
                        nonce: gossip_send_nonce(),
                    })
                    .await;
                } else {
                    let peers = self.gossip.topic_peers(&self.topic).await;
                    if let Some(target) = {
                        static ROTATE: std::sync::atomic::AtomicUsize =
                            std::sync::atomic::AtomicUsize::new(0);
                        let n = peers.len();
                        (n > 0).then(|| {
                            peers[ROTATE.fetch_add(1, std::sync::atomic::Ordering::Relaxed) % n]
                        })
                    } {
                        debug!(
                            roots = due.len(),
                            buffered,
                            target = %target,
                            "catch-up: re-requesting missing predecessors (backoff-gated, rotating target)"
                        );
                        self.send_gossip_direct(
                            target,
                            &BlocklaceGossipMessage::Pull {
                                ids: due,
                                nonce: gossip_send_nonce(),
                            },
                        )
                        .await;
                    }
                }
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
        merkle_root: [u8; 32],
        receipt_stream_root: Option<[u8; 32]>,
    ) {
        use crate::finalization_votes::FinalizationVote;
        // HYBRID-PQ: sign BOTH the ed25519 and the ML-DSA-65 halves. `sign`
        // returns `None` only on a transient OS-entropy failure during hedged
        // ML-DSA signing — treat as "cannot vote this instant" and skip the
        // emission (a later finalized block re-triggers a vote; liveness is
        // unaffected, and no half-signed vote is ever gossiped).
        let Some(vote) = FinalizationVote::sign(
            &self.signing_key,
            &self.pq_signing_key,
            block_id,
            level,
            merkle_root,
            receipt_stream_root,
        ) else {
            tracing::warn!(
                "ML-DSA finalization-vote signing failed (transient); skipping emission"
            );
            return;
        };

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
        // `.docs-history-noclaude/STAGE5-CONSENSUS-DEVAC.md`); `publish_eager` reaches every
        // committee peer in one hop so the round-synchronous shape `tau`
        // finalizes over actually forms on the running node.
        if let Err(e) = self.gossip.publish_eager(&self.topic, &peer_msg).await {
            debug!(error = %e, "failed to publish blocklace message");
        }
    }

    /// Send one blocklace gossip message POINT-TO-POINT to `target` — the
    /// request/response counterpart of [`broadcast_gossip_message`].
    ///
    /// ⚑ THE FAN-OUT FIX (2026-08-08, follows Mysticeti's targeted synchronizer
    /// rather than inventing): `Pull`, `PullResponse`, and the frontier delta
    /// `Push` are all computed FOR one specific peer, but every one of them
    /// used to go out via `publish_eager` — full payload to every peer over
    /// every live link, then re-forwarded by each receiver (Plumtree). One lost
    /// tip at committee size n therefore cost up to n−1 peers each broadcasting
    /// a full-causal-past dump to all peers: O(n² · |history|) frames for a
    /// one-block gap. This is our local shape of the measured uncertified-DAG
    /// pathology (SH++ §8.3: 1% egress drop on 5/100 nodes ⇒ 10× latency for
    /// Mysticeti, from replicas "scrambl[ing] to perform critical-path
    /// synchronization"; MY §VIII names "inefficient synchronization of
    /// unevenly broadcasted blocks" from production). Mysticeti's remedy is
    /// targeted fetch — the likely holder first, then rotate — and a reply
    /// addressed to its requester; `GossipEnvelope::Direct` (never
    /// re-forwarded) is that primitive on our transport.
    ///
    /// `target` may be the ephemeral `from` address of a received message: the
    /// link map registers inbound connections under exactly that address, so
    /// the reply rides the live link the request arrived on.
    async fn send_gossip_direct(&self, target: SocketAddr, msg: &BlocklaceGossipMessage) {
        let encoded = match postcard::to_stdvec(msg) {
            Ok(bytes) => bytes,
            Err(e) => {
                warn!(error = %e, "failed to encode direct blocklace gossip message");
                return;
            }
        };
        let msg_hash = *blake3::hash(&encoded).as_bytes();
        let peer_msg = PeerMessage::PublishTurn {
            turn_hash: msg_hash,
            turn_data: encoded,
            causal_deps: vec![],
        };
        if let Err(e) = self
            .gossip
            .send_direct(&self.topic, target, &peer_msg)
            .await
        {
            debug!(error = %e, target = %target, "failed to send direct blocklace message");
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
    ///
    /// `state` is the COMMITTED consensus state, read to project the tau participant
    /// set from the agreed roster (`NodeState::ml_dsa_key_for`) rather than any
    /// node-local key view — see the participant-projection block below (F-CO-1).
    pub async fn poll_finalized_blocks(&self, state: &NodeState) -> Vec<FinalizedBlock> {
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
        let admitted = crate::strand_admission_gate::admitted_participants(
            &raw_participants,
            &raw_participants,
        );
        if admitted.len() != raw_participants.len() {
            warn!(
                admitted = admitted.len(),
                proposed = raw_participants.len(),
                "verified strand-admission gate (F-4) filtered un-admitted strands out of the \
                 finality participant set"
            );
        }

        // ── HYBRID-ID PARTICIPANT PROJECTION — FROM COMMITTED STATE, NEVER NODE-LOCAL KEY VIEW ──
        // The finality `Block::creator` is the HYBRID id `H(ed25519 ‖ ml_dsa)` (committed surface-3:
        // `dregg_types::hybrid_id_commitment` / `verify_committed_ml_dsa`), and the roster, tips,
        // finalization votes, and gossip `NodeId` are all keyed by it. The verified finalizer
        // (`ordering::tau` / `VerifiedFinality::compute_order` / `compute`) picks each wave's leader
        // by MATCHING the participant set against each block's `creator` AND by the round-robin
        // `participants[wave % n]` (Lean `waveLeader`) — so the finalized order is a pure function of
        // the EXACT hybrid-id participant set and its length `n`. The set MUST therefore be keyed by
        // the same hybrid id as `creator` (NOT the raw ed25519 the constitution stores), AND it MUST
        // be BYTE-IDENTICAL on every honest node — or two honest nodes compute DIFFERENT leader
        // schedules over the SAME lace and finalize DIVERGENT orders with no detection: a silent fork.
        //
        // CONSENSUS-SAFETY (F-CO-1 — cross-node tau participant-set divergence): each member's ML-DSA
        // half is read from COMMITTED consensus state (`NodeState::ml_dsa_key_for` — the genesis-
        // published, index-aligned `known_federation_keys`/`known_federation_ml_dsa_keys` roster),
        // which is the SAME value on every node with the same genesis. It is DELIBERATELY NOT read
        // from the vote collector's `pq_committee` (`votes.pq_key`): that map is NODE-LOCAL — a node
        // self-inserts its OWN key and learns peers' keys piecemeal as they propagate — so projecting
        // through it let a node that had learned a joined validator J's key project {A,B,C,J} (n=4)
        // while a peer that had not projected {A,B,C} (n=3); both pass a bare non-degeneracy guard and
        // run tau over DIFFERENT participant sets ⇒ different leaders ⇒ different finalized order ⇒
        // fork. Sourcing the key from committed state makes this projection a deterministic function
        // of committed state alone, so every honest node with the same finalized prefix projects the
        // IDENTICAL set (and order). A member whose ML-DSA key is not in committed state is DROPPED
        // here and the poll then FAILS CLOSED below (it does NOT silently order over a subset): an
        // under-committed key stalls finality (liveness) rather than forking it (safety). Vote
        // VERIFICATION legitimately still uses `votes.pq_key` (a node must learn a peer's key to check
        // its vote) — set-MEMBERSHIP for the order is the only thing that must come from committed
        // state. (Residual: a live-JOINED validator's key is not yet committed on-chain — the Join
        // payload carries only its ed25519 key — so its key must be added to committed state, e.g.
        // via genesis roster or an on-chain-key Join, before it can lead/finalize; until then every
        // node deterministically halts rather than forking.)
        let participants: Vec<[u8; 32]> = project_committed_participants(state, &admitted).await;
        if participants.len() != admitted.len() {
            warn!(
                projected = participants.len(),
                admitted = admitted.len(),
                "hybrid-id participant projection dropped admitted current participants with no \
                 COMMITTED ML-DSA key — finality will FAIL CLOSED this poll (halts rather than \
                 ordering over a subset). Commit the missing member's ML-DSA key (genesis roster / \
                 on-chain join); never a node-local key view (that would fork)."
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
        // CONSENSUS-SAFETY (F-CO-1): the solo-vs-consensus decision keys on the RAW
        // ADMITTED participant count (`admitted.len()`), and multi-party tau runs ONLY
        // when the committed-state projection covers EVERY admitted participant
        // (`participants.len() == admitted.len()`). Three arms:
        //   * `admitted <= 1` → genuine solo: order the ENROLLED creators' blocks by `seq` (no
        //     leader schedule, so no full projection needed — but see
        //     [`solo_enrolled_creators`]: the creator filter IS needed, and the node's own
        //     hybrid id is derivable without a committed key, so it applies on a cold start too).
        //   * `admitted > 1` but the projection dropped ≥1 admitted member (a current
        //     participant with no COMMITTED ML-DSA key) → FAIL CLOSED, finalize NOTHING.
        //     A node must NEVER order over a proper subset of the committed set: because
        //     the projection is a function of committed state, every node that DOES order
        //     uses the identical full set (identical tau leader schedule ⇒ identical
        //     order), while a node missing any committed key HALTS (liveness) instead of
        //     ordering over a smaller set that would diverge from a peer holding the full
        //     set (safety). This strictly subsumes the old fail-open solo hole: an
        //     `admitted > 1` federation whose projection collapses can never enter the
        //     seq-only solo arm with the quorum belt disarmed (the `TauPrefixMonotone`
        //     hazard) — nor run tau over a subset (the divergence hazard).
        //   * projection covers all admitted → run the verified multi-party tau order.
        let ordered = if admitted.len() <= 1 {
            // Solo: the actionable blocks of an ENROLLED creator, ordered by sequence.
            //
            // ⚑ THE ENROLLMENT FILTER, SOLO ARM — the sibling `c6f00c228` named and left open, now
            // closed. The multi-party arm below finalizes only ENROLLED creators (the verified
            // `BlocklaceFinality.enrolledId` filter, mirrored in `ordering::tau`, proved by
            // `tauOrder_only_enrolled` — see `crate::finality_gate`'s module header). This arm had
            // NO creator check at all: it finalized EVERY actionable block in the lace regardless
            // of who created it. Not hypothetical on a lace that once held more creators — both
            // reachable paths are verified at source in
            // `solo_arm_refuses_an_unenrolled_creator_at_seq_zero`:
            //   * a federation SHRUNK to n=1. `blocklace/src/finality.rs::enroll_pq` (:979) only
            //     inserts and nothing in the workspace removes, so the pinned ingest roster is
            //     INSERT-ONLY, while `apply_passed_proposal` (:14217) shrinks
            //     `constitution.current.participants`, which this poll re-reads every time. A
            //     removed validator's NEW blocks keep passing `receive_block_pinned` and land in a
            //     lace this arm then finalizes whole.
            //   * a RESTART through `blocklace/src/finality.rs::from_checkpoint` (authenticating
            //     since 2026-08-08 — it was the verbatim `from_checkpoint_trusted` before that),
            //     reached from the boot `store.load_blocklace`
            //     (`persist/src/blocklace_store.rs`). Signatures, closure and equivocation are now
            //     re-checked on restore, but the lace it builds still starts with an EMPTY
            //     `pq_roster` — a formerly-enrolled creator's validly-signed blocks come back.
            //
            // ⚑ THE BOOTSTRAP TENSION IS DISSOLVED, NOT TRADED. `c6f00c228` left this open because
            // "the only sound creator key to filter against is the projected hybrid id", so a
            // filter here would make solo bootstrap depend on a COMMITTED ML-DSA key and refuse the
            // node's OWN blocks on a cold start. That premise is FALSE for the one identity that
            // matters here: the node's own hybrid id `H(ed25519 ‖ ml_dsa)` is DERIVABLE from the
            // ed25519 seed it already holds, because `ML-DSA.KeyGen` is deterministic in the seed.
            // The lace's `HybridBlockSigner` (`blocklace/src/signer.rs`) has already paid that
            // derivation once at `Blocklace::new`, so `lace.signer().creator()` is the exact value
            // `Block::new` stamps on every block this node authors — free, and available before any
            // genesis roster is committed. The boot path does the same derivation at :3100 and
            // enrolls it at :3450. So [`solo_enrolled_creators`] completes the committed-state
            // projection with the ONE member whose key we can derive: ourselves. A genuine cold
            // start (constitution `vec![self_key]`, `known_federation_ml_dsa_keys` empty) therefore
            // finalizes its own blocks with the filter fully armed.
            //
            // ⚑ SAY WHAT BROKE (flag day, node startup behaviour). A node whose own ed25519 is NOT
            // an admitted constitutional participant and whose `admitted.len() <= 1` no longer
            // finalizes its OWN blocks — previously it finalized every block in the lace, its own
            // included. That is the n=1 case of the rule the multi-party arm has enforced since
            // `c6f00c228` (a non-participant's blocks are refused by `enrolledId` there too), so
            // this makes n=1 CONSISTENT with n>1 rather than introducing a new refusal. Nothing
            // re-emits and nothing refuses to load; what changes is which blocks reach the executor.
            let self_ed25519 = lace.signer().ed25519();
            let self_hybrid = lace.signer().creator();
            let solo_enrolled =
                solo_enrolled_creators(&participants, &admitted, &self_ed25519, self_hybrid);
            if solo_enrolled.is_empty() {
                warn!(
                    admitted = admitted.len(),
                    projected = participants.len(),
                    "SOLO FAIL-CLOSED: no enrolled creator is resolvable for the n<=1 finality arm \
                     (this node is not an admitted constitutional participant, and no admitted \
                     participant has a COMMITTED ML-DSA key) — finalizing NOTHING this poll rather \
                     than finalizing every block in the lace regardless of creator. Commit the \
                     participant's ML-DSA key (genesis roster / on-chain join) to resume."
                );
            }
            // `(seq, creator, id)` — the sort was `sort_by_key(seq)` over a HashMap iteration, so
            // two blocks at the same seq came out in ARBITRARY order. At n=1 that is an
            // equivocation, but the order fed to the executor must be a function of the lace, not
            // of hash iteration. Same tiebreak `committee_replay::finalized_order` already uses.
            let mut all_blocks: Vec<(u64, [u8; 32], BlockId)> = lace
                .iter()
                .filter(|(_, block)| solo_enrolled.contains(&block.creator))
                .filter_map(|(id, block)| match &block.payload {
                    Payload::Turn(_)
                    | Payload::TurnBundle(_)
                    | Payload::ConsensusTimedTurnV1(_)
                    | Payload::MembershipVote { .. }
                    | Payload::Checkpoint { .. } => Some((block.seq, block.creator, *id)),
                    _ => None,
                })
                .collect();
            all_blocks.sort_unstable();
            all_blocks
                .into_iter()
                .map(|(_, _, id)| id)
                .collect::<Vec<_>>()
        } else if participants.len() != admitted.len() {
            // FAIL-CLOSED: at least one admitted CURRENT participant has no COMMITTED
            // ML-DSA key, so its hybrid id — and thus the exact tau participant set and
            // leader schedule — cannot be reconstructed the SAME on every node. Ordering
            // over the surviving subset would diverge from any node that holds the full
            // committed key set: a silent fork. Finalize NOTHING this poll and warn;
            // finality HALTS until the missing member's ML-DSA key is committed (genesis
            // roster / on-chain join), at which point every node's projection fills to the
            // full agreed set and finalization resumes over ONE order. This also covers
            // the degenerate `participants.len() <= 1` case (any drop below `admitted`).
            warn!(
                admitted = admitted.len(),
                projected = participants.len(),
                "FAIL-CLOSED: an admitted current participant has no COMMITTED ML-DSA key \
                 (projected < admitted) — HALTING finality this poll rather than ordering \
                 over a subset (which would fork against a node holding the full set). \
                 Commit the missing ML-DSA key (genesis roster / on-chain join) to resume."
            );
            Vec::new()
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
            //
            // ⚑ THE CLAIM ABOVE IS CONDITIONAL ON A WALL-CLOCK BUDGET. SAY IT HERE, NOT ONLY IN A
            // WARN LINE. "The order the node finalizes over IS the verified rule's" holds *on a poll
            // whose verified FFI completes within `verified_order_ffi_timeout()`* (default 2500 ms).
            // It is NOT an unconditional property of this node, and the budget is not comfortably
            // far away: the verified `dregg_tau_order` is super-quadratic in the lace size
            // (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean` — `tauOrderFastImpl` keeps
            // HashMap past/round maps but the lace itself is `List Block` with an O(n) `Lace.lookup`
            // on the hot path), a lace grows without bound on a running chain, and over-budget
            // warnings were observed on an IDLE 4-node committee at `lace_size` 773–981.
            //
            // What a missed budget does, and it is NOT the same on every node:
            //   * `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` (what `scripts/federation-local.sh` sets):
            //     the UN-VERIFIED Rust `ordering::tau` twin decides the poll. Safety rests entirely
            //     on the two orders agreeing — pinned by
            //     `node/tests/verified_order_budget.rs::the_two_orders_the_node_swaps_between_agree_exactly`,
            //     which compares the SEQUENCE (the differential below sorts, so it compares only the
            //     finalized SET and is blind to a pure reordering).
            //   * Otherwise (a Lean-linked PoA node; `scripts/poa-devnet.sh` pins the escape to `0`):
            //     the poll FINALIZES NOTHING. Repeated misses are a finality HALT, not a silent swap.
            //
            // Either way the poll's provenance is now RECORDED (`metrics::record_consensus_order_source`)
            // and served on `/status` as `consensus_order*`, because a WARN line was not enough: the
            // poll STORES its order in the cross-poll cache below, so the warning fires ONCE and every
            // later fingerprint-matching poll takes the silent "cache HIT" path.
            let (ordering_lace, id_map) = build_ordering_blocklace(&lace);
            let rust_order: Vec<BlockId> = tau(&ordering_lace, &participants)
                .into_iter()
                .filter_map(|ordering_id| id_map.get(&ordering_id).copied())
                .collect();

            // ── TWIN-DELETION (#8): the Rust `ordering::tau` twin must NEVER decide finality on a
            // live full node. It may serve as the finalized order ONLY when there is no verified
            // archive to route to at all (`!tau_order_available()` — a genuinely no-Lean build, which
            // a full node is REFUSED to start on at `lib.rs`'s hard-check unless the operator opted
            // in), OR the operator explicitly accepts unverified consensus
            // (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, the same labeled-unaudited escape). Otherwise a
            // poll whose verified `dregg_tau_order` FFI is unavailable / returns ERR / exceeds the
            // per-poll budget FAILS CLOSED (finalizes NOTHING this poll and re-attempts on a later
            // poll) rather than silently running the unverified twin — the same halt-not-fork posture
            // the F-CO-1 committed-key projection above uses.
            let allow_rust_fallback = rust_tau_fallback_allowed(
                dregg_lean_ffi::tau_order_available(),
                allow_unverified_consensus(),
            );

            let order_gate_armed = crate::finality_gate::finality_gate_enabled();
            // Run the verified-Lean tau-order FFI on a BLOCKING thread (`spawn_blocking`), never inline
            // on this tokio worker. The verified ordering is O(history) and — even with the memoized
            // Lean causal-past (`BlocklaceFinality.tauOrderFast`, the parallel of the Rust `PastCache`)
            // — a large lace can still take real CPU time; running it inline PINNED the async worker and
            // STARVED the runtime (gossip/QUIC/`/status` froze) on a cross-linked DAG (the finality
            // wedge). On a blocking thread the async runtime stays responsive regardless of how long the
            // ordering takes. The lace snapshot + participants are moved into the closure (owned).
            // ── CROSS-POLL VERIFIED-ORDER CACHE (INCREMENTAL, FINALITY-KEYED) ─────────────────
            // The verified-Lean tau-order FFI below is O(history) and, absent a cache, is
            // recomputed FROM SCRATCH on every finality poll — the Lean `tauOrderFast` memo
            // (PastCache/RoundCache) is rebuilt inside each FFI call and thrown away. As the DAG
            // grows the per-poll cost outpaces block production and the finalized prefix never
            // reaches the frontier turn in-window (docs/VERIFIED-GATE-PERF.md).
            //
            // The prior cache fingerprinted the WHOLE LACE id-set, so ANY new frontier block (an
            // ack/heartbeat/round block that is NOT yet super-ratified) busted it — and under
            // continuous cross-machine catch-up the lace grows EVERY poll, so the fingerprint MISSED
            // every poll and the full O(n²) FFI ran every poll while the finalized order barely
            // moved (docs/CROSS-MACHINE-FINALITY-FINDING.md §3). We instead key the cache on the
            // FINALIZED ORDER itself — the ordered `rust_order` id sequence (now edge-faithful after
            // the topological `build_ordering_blocklace` fix, so it equals the verified `tauOrder`).
            // Frontier-only growth leaves the finalized order UNCHANGED ⇒ cache HIT ⇒ FFI skipped;
            // the FFI runs ONLY when finality actually ADVANCES or a catch-up block SHIFTS the
            // prefix (docs/CROSS-MACHINE-FINALITY-FINDING.md §4 / TauPrefixMonotone). This is the
            // O(finality-delta) reuse of §"Fix direction 1", not O(lace-churn). Sound: identical
            // finalized order ⇒ identical `tauOrder` (a pure function of the finalized causal DAG);
            // a change always recomputes, so the cache never serves a stale order for a moved prefix.
            let order_fingerprint: u64 = {
                use std::hash::{Hash, Hasher};
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                rust_order.len().hash(&mut hasher);
                for id in &rust_order {
                    id.hash(&mut hasher);
                }
                hasher.finish()
            };
            let lean_order_opt = if order_gate_armed {
                // Cache HIT: the finalized order is byte-identical to the last poll whose verified
                // order we cached ⇒ reuse that verified order, skip the FFI.
                let cached: Option<(Vec<BlockId>, bool)> = {
                    let fp_guard = self.last_order_fingerprint.read().await;
                    if *fp_guard == Some(order_fingerprint) {
                        self.last_lean_order.read().await.clone()
                    } else {
                        None
                    }
                };
                match cached {
                    Some((order, cached_verified)) => {
                        // ⚑ PROVENANCE RIDES THE CACHE. The fallback branch below stores the
                        // UN-VERIFIED Rust order under this same fingerprint, so a bare "cache HIT"
                        // used to serve an un-verified order while logging the word "verified" —
                        // and, because the fingerprint is stable while finality is not advancing,
                        // it served it on EVERY subsequent poll with no warning at all. One WARN,
                        // then silence forever. The cached order now carries whether it was
                        // verified, and a hit is counted as what it actually is.
                        if cached_verified {
                            debug!(
                                fingerprint = order_fingerprint,
                                finalized = order.len(),
                                "verified-order cache HIT (finality unchanged), skipped FFI"
                            );
                            crate::metrics::record_consensus_order_source(
                                crate::metrics::ConsensusOrderSource::VerifiedCached,
                                false,
                            );
                        } else {
                            warn!(
                                fingerprint = order_fingerprint,
                                finalized = order.len(),
                                "consensus-order cache HIT serving an UN-VERIFIED Rust \
                                 `ordering::tau` order (stored by an earlier over-budget/ERR poll) \
                                 — this poll does NOT finalize over the verified ordering. \
                                 Verified-ness does not return on a cache hit; it returns when the \
                                 finalized order next changes and an in-budget FFI re-anchors the \
                                 cache. (dregg_consensus_order_polls_total{{source=\
                                 \"unverified_cached\"}} incremented.)"
                            );
                            crate::metrics::record_consensus_order_source(
                                crate::metrics::ConsensusOrderSource::UnverifiedCached,
                                false,
                            );
                        }
                        Some((order, cached_verified))
                    }
                    None => {
                        let lace_ffi = lace.clone();
                        let participants_ffi = participants.clone();
                        // Cache MISS: finality ADVANCED or the prefix SHIFTED — recompute the
                        // verified order. BOUNDED (Fix: un-stall the serial executor from the slow
                        // FFI). The `poll_finalized_blocks` loop awaits this before the next poll, so
                        // one slow O(n²) FFI on a large cross-linked lace would freeze ALL
                        // finalization. Cap it: on timeout we use the edge-faithful Rust `tau` order
                        // (== `tauOrder` after the topological build fix) for THIS poll, so a single
                        // slow poll can never freeze the executor. The abandoned `spawn_blocking`
                        // finishes in the background pool; a later, in-budget poll re-anchors the
                        // cache to the genuine verified order.
                        let lace_size = lace.iter().count();
                        let ffi_started = std::time::Instant::now();
                        let timeout = verified_order_ffi_timeout();
                        let ffi = tokio::task::spawn_blocking(move || {
                            crate::finality_gate::VerifiedFinality::compute_order(
                                &lace_ffi,
                                &participants_ffi,
                            )
                        });
                        let (computed, timed_out) = match tokio::time::timeout(timeout, ffi).await {
                            Ok(Ok(v)) => (v, false),
                            Ok(Err(e)) => {
                                warn!(
                                    error = %e,
                                    "verified tau-order FFI blocking task panicked/cancelled — \
                                     falling back to the Rust `ordering::tau` order for this poll"
                                );
                                (None, false)
                            }
                            Err(_elapsed) => {
                                // ⚑ THIS WARN USED TO ASSERT AN OUTCOME IT DOES NOT DECIDE. It read
                                // "using the edge-faithful Rust `ordering::tau` order for THIS poll"
                                // — but whether the Rust order is used is decided ~50 lines below by
                                // `allow_rust_fallback`, and on a Lean-linked node without
                                // `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` this poll finalizes NOTHING
                                // instead. Reading this line off a live node therefore told an
                                // operator the unverified twin had decided finality when in fact
                                // finality had HALTED — opposite failure, opposite remedy. The line
                                // now reports only what it knows: the budget was missed.
                                warn!(
                                    fingerprint = order_fingerprint,
                                    lace_size,
                                    timeout_ms = timeout.as_millis() as u64,
                                    "verified tau-order FFI EXCEEDED THE PER-POLL BUDGET — this poll \
                                     will NOT finalize over the verified ordering. What happens \
                                     instead is logged next: either the un-verified Rust \
                                     `ordering::tau` order decides it (only under \
                                     DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 / a no-Lean build) or the \
                                     poll FAILS CLOSED and finalizes nothing. The bound exists so a \
                                     slow FFI cannot freeze the serial finality executor; raising \
                                     DREGG_FINALITY_ORDER_TIMEOUT_MS moves the crossing without \
                                     changing whether the verified path runs. \
                                     (dregg_consensus_order_over_budget_total incremented.)"
                                );
                                (None, true)
                            }
                        };
                        debug!(
                            fingerprint = order_fingerprint,
                            lace_size,
                            ffi_ms = ffi_started.elapsed().as_millis() as u64,
                            finalized = computed.as_ref().map(|o| o.len()).unwrap_or(0),
                            "verified-order cache MISS, recomputed FFI"
                        );
                        match computed {
                            Some(order) => {
                                // Genuine verified order: cache under the finality fingerprint,
                                // TAGGED verified so a later hit can say so truthfully.
                                *self.last_order_fingerprint.write().await =
                                    Some(order_fingerprint);
                                *self.last_lean_order.write().await = Some((order.clone(), true));
                                crate::metrics::record_consensus_order_source(
                                    crate::metrics::ConsensusOrderSource::VerifiedFfi,
                                    false,
                                );
                                Some((order, true))
                            }
                            None => {
                                // FFI unavailable (stale archive / ERR) or over-budget.
                                if allow_rust_fallback {
                                    // LABELED-UNAUDITED (no verified archive linked, or
                                    // DREGG_ALLOW_UNVERIFIED_CONSENSUS=1): use the edge-faithful Rust
                                    // `tau` order for this poll and cache it under the finality
                                    // fingerprint so an identical next poll does not re-pay the
                                    // slow/failing FFI — SOUND because the topological
                                    // `build_ordering_blocklace` makes `rust_order ==
                                    // compute_order(lace)` on the same lace. A `timed_out` fallback
                                    // still re-attempts the FFI whenever finality next moves (the
                                    // fingerprint changes).
                                    //
                                    // ⚑ The cached entry is TAGGED UN-VERIFIED. It used to be
                                    // stored indistinguishably from a verified one, so every later
                                    // fingerprint-matching poll served it under a "verified-order
                                    // cache HIT" debug line — the single WARN above was the only
                                    // trace, and on an idle committee (stable fingerprint) it was
                                    // followed by an unbounded run of silent un-verified polls.
                                    // The "SOUND because `rust_order == compute_order(lace)`"
                                    // premise is now an ASSERTED, SEQUENCE-LEVEL property:
                                    // `node/tests/verified_order_budget.rs`. The differential below
                                    // does NOT establish it (it sorts before comparing).
                                    *self.last_order_fingerprint.write().await =
                                        Some(order_fingerprint);
                                    *self.last_lean_order.write().await =
                                        Some((rust_order.clone(), false));
                                    crate::metrics::record_consensus_order_source(
                                        if timed_out {
                                            crate::metrics::ConsensusOrderSource::UnverifiedOverBudget
                                        } else {
                                            crate::metrics::ConsensusOrderSource::UnverifiedUnavailable
                                        },
                                        timed_out,
                                    );
                                    Some((rust_order.clone(), false))
                                } else {
                                    // FAIL CLOSED (#8): the verified `dregg_tau_order` export IS
                                    // linked (this is a live full node) but this poll's FFI was
                                    // unavailable / ERR / over-budget. NEVER run the unverified Rust
                                    // twin as the live finalized order — finalize NOTHING this poll
                                    // (a later in-budget / non-ERR poll produces the verified order).
                                    // Do NOT cache: caching the Rust order would poison the cache with
                                    // an unverified order a later hit would serve as authoritative.
                                    warn!(
                                        fingerprint = order_fingerprint,
                                        "verified tau-order FFI unavailable/ERR/over-budget on a \
                                         Lean-linked full node — FAILING CLOSED (finalize nothing this \
                                         poll) rather than running the unverified Rust `ordering::tau` \
                                         twin. A later poll re-attempts the verified order. Set \
                                         DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 to deliberately accept the \
                                         Rust order, or raise DREGG_FINALITY_ORDER_TIMEOUT_MS."
                                    );
                                    crate::metrics::record_consensus_order_source(
                                        crate::metrics::ConsensusOrderSource::FailedClosed,
                                        timed_out,
                                    );
                                    None
                                }
                            }
                        }
                    }
                }
            } else {
                None
            };
            match lean_order_opt {
                Some((lean_order, order_is_verified)) => {
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
                    // ⚑ `ordered_from_lean` MUST mean what its name and its consumer say it means.
                    // It used to be set unconditionally `true` here — for the over-budget Rust
                    // fallback and for an un-verified cache hit as well as for a genuine verified
                    // order. Its ONE consumer (`gate_armed`, ~150 lines below) disarms the
                    // belt-and-suspenders finality gate on it, with the comment "keep the belt ONLY
                    // for the Rust fallback (the case it actually defends, where `ordered` is NOT
                    // Lean-verified)". So the timeout fallback disarmed the belt in precisely the
                    // case the belt exists for, and the justification ("`ordered` IS the verified
                    // rule's own output, so there is no un-verified order to gate") was false on
                    // exactly those polls. It now carries the real provenance.
                    ordered_from_lean = order_is_verified;
                    lean_order
                }
                None => {
                    if allow_rust_fallback {
                        // LABELED-UNAUDITED: no verified archive linked (a genuinely no-Lean build /
                        // guest), or the operator set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1, or the
                        // finality gate is disarmed (`DREGG_FINALITY_GATE=0`) on such a build. The
                        // Rust `ordering::tau` order decides this poll.
                        if order_gate_armed {
                            warn!(
                                "verified consensus order UNAVAILABLE (Lean archive missing \
                                 `dregg_tau_order` or wire returned ERR) — FALLING BACK to the Rust \
                                 `ordering::tau` order for this poll (labeled-unaudited: no verified \
                                 archive linked or DREGG_ALLOW_UNVERIFIED_CONSENSUS set). Rebuild the \
                                 node with the verified archive to make the verified rule authoritative."
                            );
                        }
                        crate::metrics::record_consensus_order_source(
                            crate::metrics::ConsensusOrderSource::UnverifiedUnavailable,
                            false,
                        );
                        rust_order
                    } else {
                        // FAIL CLOSED (#8): a live full node with the verified `dregg_tau_order`
                        // export linked has no verified order this poll (finality gate disarmed via
                        // DREGG_FINALITY_GATE=0, or the FFI failed). NEVER run the unverified Rust
                        // twin as the live finalized order — finalize NOTHING this poll. To run the
                        // Rust ordering on a Lean-linked node, set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1
                        // (a deliberate, labeled acceptance of unverified consensus).
                        warn!(
                            "no verified consensus order this poll on a Lean-linked full node \
                             (finality gate disarmed or verified FFI failed) — FAILING CLOSED \
                             (finalize nothing) rather than running the unverified Rust \
                             `ordering::tau` twin. Set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 to accept \
                             the Rust order deliberately."
                        );
                        crate::metrics::record_consensus_order_source(
                            crate::metrics::ConsensusOrderSource::FailedClosed,
                            false,
                        );
                        Vec::new()
                    }
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
        // ⚑ FAIL-CLOSED (this site was the SECOND confirmed member of the conservation twin's
        // fail-OPEN class). When the verified archive lacks `dregg_blocklace_finalize`, or the wire
        // returns `ERR`, or the blocking FFI thread panics, `compute` is `None`. That used to be a
        // NO-OP WITH A WARNING: the poll went on to advance finality over the UN-GATED Rust tau
        // order, with a log line as the only trace. It now REFUSES to advance finality — see
        // [`finality_belt_disposition`] below, consulted after `pending` is known, whose refusal
        // returns an EMPTY batch (finalize NOTHING this poll; a later poll re-attempts, exactly the
        // disposition the F-CO-1 projection halt and the twin#8 order gate already use).
        //
        // The refusal has TWO DECLARED BYPASSES (`belt_gate_bypass_allowed`, the shape twin#8's
        // `rust_tau_fallback_allowed` and twin#11's `quorum_rust_fallback_allowed` already use):
        // there is no `dregg_blocklace_finalize` export linked AT ALL (no verified projection to
        // route to — the state the `lib.rs` verified-consensus hard-check owns, and the state every
        // archive-less test binary and the wasm/zkVM guest are in), or the operator explicitly
        // accepted unverified consensus (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`). `DREGG_REQUIRE_LEAN=1`
        // promotes BOTH to the hard refusal. Both bypasses are DECLARED in
        // `scripts/ci-invariants/gate-dataflow.tsv`'s `allow` column, so they print in every CI log
        // instead of hiding in a match arm.
        //
        // When the gate IS armed and DOES answer, and the verified projection excludes a block, we
        // STOP the committed batch BEFORE that block (it is NOT marked executed), so it is
        // re-evaluated on a later poll once the lace has grown enough — preserving liveness (a
        // finalized block stays pending until served; identity tracking makes the retry
        // order-shift-proof).
        //
        // ⚑ HOW WIDE WAS THE HOLE — stated at its real resolution, not inflated. Reaching the belt
        // with a NON-EMPTY `ordered` requires `!ordered_from_lean`, which in the multi-party arm
        // implies `allow_rust_fallback` (`!tau_order_available() || DREGG_ALLOW_UNVERIFIED_CONSENSUS`).
        // So on a FULLY Lean-linked node with no operator escape the belt never armed with work to do,
        // and the fail-open was NOT reachable there. What the refusal actually newly closes:
        //   * a SPLIT archive (`dregg_blocklace_finalize` present, `dregg_tau_order` absent) on a node
        //     that never ran `lib.rs`'s verified-consensus hard-check — one started
        //     `--federation-mode solo` whose constitution grew to n>1 (the check keys on the FLAG, the
        //     order on the runtime roster), or any embedder/test driving this handle directly;
        //   * `DREGG_REQUIRE_LEAN=1`, which previously had NO effect on this path at all and now makes
        //     an operator who demands the verified artifact get a HARD HALT instead of a log line.
        // The durable half is that the disposition is now a REGISTERED decision site
        // (`gate-dataflow.tsv` twin#8b + `lean-twins.tsv`), so the warn-and-continue cannot regrow
        // silently — which is the same value the conservation fix delivered.
        //
        // PERF: when `ordered` ALREADY came from the verified Lean export (`ordered_from_lean`,
        // the common path), the gate is provably a no-op — it re-runs the SAME verified projection
        // and admits the whole Lean order back (`gate_admits_iff_verified_finalizes`). So skip the
        // second O(history) FFI there and keep the belt ONLY for the Rust fallback (the case it
        // actually defends, where `ordered` is NOT Lean-verified). NOT a fail-open: on the Lean path
        // `ordered` IS the verified rule's own output, so there is no un-verified order to gate.
        //
        // ⚑ THE VACUITY SHORT-CIRCUIT LIVES HERE AND BELOW, NOT IN THE REFUSAL. `ordered_from_lean`
        // is the FIRST of the three states where "no verified belt" is genuinely irrelevant (the
        // other two: a poll with an EMPTY pending set, and a pending set with no CONSENSUS-ACTIONABLE
        // block — the belt only ever gates actionable payloads, so refusing an ack/heartbeat-only
        // poll would halt the DAG on a decision that does not exist). See
        // `finality_belt_disposition`.
        let gate_armed = belt_gate_fault_injected()
            || (participants.len() > 1
                && !ordered_from_lean
                && crate::finality_gate::finality_gate_enabled());
        // Belt-and-suspenders consistency gate FFI — also on a BLOCKING thread (see the tau-order FFI
        // above) so it can never starve the async runtime, regardless of lace size.
        let verified = if gate_armed && !belt_gate_fault_injected() {
            let lace_ffi = lace.clone();
            let participants_ffi = participants.clone();
            match tokio::task::spawn_blocking(move || {
                crate::finality_gate::VerifiedFinality::compute(&lace_ffi, &participants_ffi)
            })
            .await
            {
                Ok(v) => v,
                Err(e) => {
                    // A panicked/cancelled FFI thread is a gate-UNAVAILABLE, exactly like a stale
                    // archive — it is NOT a verdict about any block. It falls through to
                    // `finality_belt_disposition` below, which REFUSES unless a bypass is declared.
                    warn!(
                        error = %e,
                        "verified finality-gate FFI blocking task panicked/cancelled — the belt gate \
                         is UNAVAILABLE for this poll (see the fail-closed disposition below)"
                    );
                    None
                }
            }
        } else {
            None
        };

        // ── TAU-PREFIX-MONOTONE CLOSURE (identity cursor, not an index) ─────────────────────────
        // `TauPrefixMonotone.lean` proves tau's finalized prefix is stable only CONDITIONALLY
        // (`ClosedExtension` + `ChainExtends`, CM Def. 19 + Prop. 3) after the tau re-authoring;
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
        drop(cursor);
        if pending.is_empty() {
            return vec![];
        }

        // ── THE BELT'S FAIL-CLOSED DISPOSITION (the fix for this site's fail-OPEN) ──────────────
        // `gate_armed` means: this poll is about to advance finality over an order the verified Lean
        // rule did NOT produce, so the belt projection is the ONLY verified check standing between the
        // un-gated Rust `ordering::tau` and the executor. If the belt could not answer, we do not
        // advance. Nothing has been marked executed at this point (`pending` is a pure set difference;
        // `observe_order` above is observability only), so an empty return is a clean "finalize
        // nothing this poll" that a later poll re-attempts — the same disposition as the F-CO-1
        // projection halt and the twin#8 order gate.
        if gate_armed {
            let actionable_pending = pending
                .iter()
                .filter_map(|id| lace.get(id))
                .filter(|b| is_consensus_actionable(&b.payload))
                .count();
            // Whether the verified PROJECTION export (`dregg_blocklace_finalize`) is linked at all.
            // This is what distinguishes "there is no verified projection in this binary" (a DECLARED
            // bypass — an archive-less build, the state the startup hard-check owns) from "the
            // projection IS here and this poll could not get an answer out of it" (wire `ERR` /
            // panicked FFI thread — the undeclared fail-open this site shipped with). Probed HERE, not
            // beside `gate_armed`: `finality_gate_available()` runs `lean_init_once()`, and the solo
            // (n=1) path must not start initialising the Lean runtime it otherwise never touches.
            let belt_export_linked =
                dregg_lean_ffi::finality_gate_available() || belt_gate_fault_injected();
            if let Err(refusal) = finality_belt_disposition(
                verified.as_ref(),
                actionable_pending,
                belt_export_linked,
                allow_unverified_consensus(),
                require_verified_lean_gate(),
            ) {
                crate::metrics::inc_finality_gate_unavailable_refusals();
                warn!(
                    refusal = %refusal,
                    actionable_pending,
                    finalized = ordered.len(),
                    belt_export_linked,
                    "verified finality gate UNAVAILABLE — FAILING CLOSED: finalizing NOTHING this \
                     poll rather than advancing finality over the UN-GATED Rust `ordering::tau` \
                     order. This is NOT a verdict about any block (no block was refused; the gate \
                     could not answer). Rebuild the node against the verified archive (it splices \
                     Dregg2.Distributed.FinalityGate), or set DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 to \
                     deliberately accept un-gated finality."
                );
                return Vec::new();
            }
        }

        let mut finalized = Vec::new();

        for block_id in pending {
            let Some(block) = lace.get(&block_id) else {
                // A finalized id missing from the lace is an invariant breach (tau orders only
                // lace members). Do not acknowledge an impossible local observation.
                error!(
                    block_id = %block_id,
                    "finalized block id not present in the lace — stopping planned prefix"
                );
                break;
            };
            // GATE: REFUSE any actionable block the verified rule did not finalize. Ack/Data are
            // not consensus-actionable (skipped below regardless), so a heartbeat the rule does
            // not "finalize" never trips the gate. The refused block and everything after it are
            // NOT marked executed, so they are re-evaluated on a later poll once the lace has
            // grown enough (verified rule wins; liveness preserved).
            if let Some(vf) = verified.as_ref() {
                let actionable = is_consensus_actionable(&block.payload);
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
                        consensus_time: None,
                    });
                }
                Payload::TurnBundle(bundle) => {
                    finalized.push(FinalizedBlock::Turn {
                        block_id,
                        data: bundle.signed_turn.clone(),
                        artifacts: Some(bundle.clone()),
                        consensus_time: None,
                    });
                }
                Payload::ConsensusTimedTurnV1(timed) => {
                    finalized.push(FinalizedBlock::Turn {
                        block_id,
                        data: timed.signed_turn().to_vec(),
                        artifacts: Some(TurnArtifactBundle {
                            signed_turn: timed.signed_turn().to_vec(),
                            receipt: timed.receipt().map(ToOwned::to_owned),
                            witnessed_receipts: timed.witnessed_receipts().to_vec(),
                        }),
                        consensus_time: Some(timed.consensus_time().unix_seconds()),
                    });
                }
                Payload::MembershipVote { action } => {
                    finalized.push(FinalizedBlock::Membership {
                        block_id,
                        // ⚑ `block.ed25519`, NOT `block.creator`. Membership is a
                        // STRAND/economic act and the constitution's participant
                        // set is keyed by the ed25519 strand key; `block.creator`
                        // is the HYBRID consensus id `H(ed25519 ‖ ml_dsa)` and is
                        // never a member, so passing it made
                        // `record_vote`'s `is_participant` gate refuse EVERY vote
                        // on the live path. `committee_replay::derive_from_lace`
                        // has always passed `block.ed25519`; this is the live half
                        // agreeing with the replay half.
                        creator_ed25519: block.ed25519,
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
                Payload::Ack | Payload::Data(_) => {
                    finalized.push(FinalizedBlock::Inert { block_id });
                }
            }
        }

        finalized
    }

    /// Ask the committee to admit us, over the narrow join channel.
    ///
    /// ⚑ THIS USED TO AUTHOR A BLOCK, AND THAT IS EXACTLY WHY IT NEVER WORKED.
    /// A non-member's block is refused twice over — as an `unknown_sender`
    /// envelope at the transport, and (had it got in) as an `UnenrolledCreator`
    /// at `receive_block_pinned`. Measured on a real 4-node federation: the
    /// candidate logged `proposed join to federation` for a block id that
    /// appeared in ZERO committee-node logs, while each committee member emitted
    /// ~7,300 `unknown sender` WARNs in three minutes and `GET /api/membership`
    /// read `participants=4, proposals=0` on all five nodes indefinitely.
    ///
    /// So we do not author a block we cannot deliver. We send a signed request —
    /// the one envelope kind a non-member can get delivered — and a MEMBER
    /// authors the proposal under its own committee key. The candidate is
    /// evidence; the sponsor is authority.
    ///
    /// Re-sent on [`JOIN_REQUEST_RESEND`] until we are a participant, because a
    /// peer may be down, the committee may not yet have quorum, or an operator
    /// may take a while to sponsor. Returns once we are a member.
    pub async fn run_join_requests_until_member(&self, state: &NodeState) {
        let (federation_id, ml_dsa_pubkey) = {
            let s = state.read().await;
            (s.federation_id, self.pq_public_key_bytes())
        };
        let binding = join_request_binding(&federation_id, &self.self_key, &ml_dsa_pubkey);
        let Some(pq_proof) = self.pq_signing_key.sign(&binding) else {
            error!(
                "could not sign the join request's ML-DSA proof of possession — this node cannot \
                 ask to join and will never become a member. Consensus continues as a follower."
            );
            return;
        };
        let body = JoinRequestBody {
            version: JOIN_REQUEST_VERSION,
            federation_id,
            ml_dsa_pubkey,
            pq_proof,
        };
        let Ok(encoded) = postcard::to_stdvec(&body) else {
            error!("join request failed to encode — not sent");
            return;
        };

        let started = std::time::Instant::now();
        loop {
            if self
                .constitution
                .read()
                .await
                .current
                .is_participant(&self.self_key)
            {
                let mut p = self.join_progress.write().await;
                p.member = true;
                p.waiting_secs = 0;
                info!("this node is now a federation participant — join requests stop");
                return;
            }

            // Did our request demonstrably REACH a member? A Join proposal for
            // our own key in the constitution is proof that it did, and is the
            // difference between "waiting for approval" and "shouting into a
            // void" — the two states the old code could not tell apart.
            let proposal_seen = self
                .constitution
                .read()
                .await
                .votes
                .proposal_tallies()
                .iter()
                .any(|(_, p, _, _, _)| {
                    matches!(p, MembershipProposal::Join { node_key, .. } if *node_key == self.self_key)
                });

            let peers = self
                .gossip
                .send_join_request(encoded.clone(), &self.peer_addrs)
                .await;

            {
                let mut p = self.join_progress.write().await;
                p.member = false;
                p.requests_sent += 1;
                p.last_request_peers = peers;
                p.waiting_secs = started.elapsed().as_secs();
                p.proposal_seen = proposal_seen;
            }
            metrics::gauge!("dregg_join_waiting_seconds").set(started.elapsed().as_secs_f64());
            metrics::counter!("dregg_join_requests_sent_total").increment(1);

            if peers == 0 {
                warn!(
                    waiting_secs = started.elapsed().as_secs(),
                    "join request NOT SENT — no live gossip link to any peer. This node is not a \
                     member and is reaching no one."
                );
            } else if proposal_seen {
                info!(
                    peers,
                    waiting_secs = started.elapsed().as_secs(),
                    "join request delivered; a Join proposal for our key is open and awaiting \
                     committee approvals"
                );
            } else {
                info!(
                    peers,
                    waiting_secs = started.elapsed().as_secs(),
                    "join request sent to the committee — no proposal for our key is open yet"
                );
            }

            tokio::time::sleep(JOIN_REQUEST_RESEND).await;
        }
    }

    /// Our own ML-DSA-65 public key bytes — the SAME key `Blocklace`'s hybrid
    /// signer stamps into every block we author, so the hybrid id the committee
    /// derives from this request is by construction the one our blocks carry.
    fn pq_public_key_bytes(&self) -> Vec<u8> {
        self.pq_public_key.0.to_vec()
    }

    /// Validate and record ONE inbound join request. Member side.
    ///
    /// Everything the gossip layer proved is carried in `candidate`: the sender
    /// holds that ed25519 key. Everything else is checked here, fail-closed.
    ///
    /// ⚑ ADMISSION ONLY — THE AUTHORING IS SOMEBODY ELSE'S TASK, AND THAT SPLIT
    /// IS THE FIX. The narrow-join-channel receiver is a SINGLE-CONSUMER loop
    /// (`while let Some(req) = join_rx.recv().await { handle_join_request(…).await }`),
    /// and this function used to `await` the whole sponsorship inline:
    /// `propose_membership` → `author_persist_or_rollback` → `lace.write()` +
    /// a durable persist + a gossip broadcast. So for as long as one
    /// sponsorship took, NOTHING ELSE ON THE JOIN CHANNEL WAS EVEN LOOKED AT.
    ///
    /// Measured on a live 4-node federation on hbox (2026-08-09, run
    /// `/tank/dregg-build/fedpole3`): node0 accepted a candidate at
    /// `11:29:46.959` and its `lace.write()` was not granted until
    /// `11:38:20.487` — **513 seconds** inside this function. During that window
    /// the gossip layer went on admitting join requests every 15 s (the
    /// candidate's own retries plus ~15 from an impostor naming a DIFFERENT
    /// federation) and not one of them was validated: the impostor's first
    /// `join request refused: it names a different federation` is stamped
    /// `11:38:22.929`, **4 m 38 s** after its first request was admitted, and
    /// they then drained in one burst. The security pole read the committee's
    /// logs during that gap and recorded `no refusal line found — THIS IS A
    /// FAILURE`, because the refusal genuinely had not happened yet.
    ///
    /// That is the property the narrow channel was built to have, inverted: an
    /// unregistered key may send exactly one kind of message and is supposed to
    /// GAIN NOTHING BY IT — but one such message, from one candidate, held the
    /// committee's entire join-admission path for eight and a half minutes.
    /// Validation is cheap and fail-closed and belongs on the receiver;
    /// authoring contends for the lace with every other writer and belongs on
    /// [`Self::sponsor_pending_join`], behind a bounded queue.
    pub async fn handle_join_request(
        &self,
        state: &NodeState,
        from: SocketAddr,
        candidate: [u8; 32],
        body: &[u8],
        sponsor: &tokio::sync::mpsc::Sender<[u8; 32]>,
    ) {
        let cand_hex: String = candidate[..4].iter().map(|b| format!("{b:02x}")).collect();
        let Ok(req) = postcard::from_bytes::<JoinRequestBody>(body) else {
            warn!(from = %from, candidate = %cand_hex, "join request refused: undecodable body");
            metrics::counter!("dregg_join_request_refused_total", "reason" => "decode")
                .increment(1);
            return;
        };
        if req.version != JOIN_REQUEST_VERSION {
            warn!(from = %from, candidate = %cand_hex, version = req.version,
                  "join request refused: unsupported version");
            metrics::counter!("dregg_join_request_refused_total", "reason" => "version")
                .increment(1);
            return;
        }
        // Chain binding: a request minted against another federation is not a
        // request to join THIS one.
        let our_federation_id = { state.read().await.federation_id };
        if req.federation_id != our_federation_id {
            warn!(from = %from, candidate = %cand_hex,
                  "join request refused: it names a different federation");
            metrics::counter!("dregg_join_request_refused_total", "reason" => "wrong_federation")
                .increment(1);
            return;
        }
        let Ok(pq_bytes): Result<[u8; dregg_pq::ML_DSA_PK_LEN], _> =
            req.ml_dsa_pubkey.clone().try_into()
        else {
            warn!(from = %from, candidate = %cand_hex,
                  "join request refused: ML-DSA public key is the wrong length");
            metrics::counter!("dregg_join_request_refused_total", "reason" => "pq_key_length")
                .increment(1);
            return;
        };
        let ml_dsa = dregg_federation::frost::MlDsaPublicKey(pq_bytes);
        // PROOF OF POSSESSION of the PQ half. Without it a candidate could name
        // a key it cannot sign under; the committee would admit a member whose
        // hybrid id never authors a block, and under the fail-closed projection
        // that is a permanent finality halt for everyone.
        let binding = join_request_binding(&our_federation_id, &candidate, &req.ml_dsa_pubkey);
        if !ml_dsa.verify(&binding, &req.pq_proof) {
            warn!(from = %from, candidate = %cand_hex,
                  "join request REFUSED: the ML-DSA proof of possession does not verify — the \
                   candidate does not hold the post-quantum key it named");
            metrics::counter!("dregg_join_request_refused_total", "reason" => "pq_proof")
                .increment(1);
            return;
        }

        {
            let c = self.constitution.read().await;
            if c.current.is_participant(&candidate) {
                debug!(candidate = %cand_hex, "join request from an existing participant — ignored");
                return;
            }
        }

        let mut pending = self.pending_joins.write().await;
        if let Some(existing) = pending.get(&candidate) {
            // A re-send is expected (the candidate retries until ratified) and
            // must not open a second proposal. What stops the second proposal is
            // `proposed`, NOT the mere presence of this entry — and that
            // distinction is what makes the retry USEFUL rather than ignored.
            //
            // ⚑ `proposed` WAS A DEAD FIELD: declared, documented as "so a
            // re-sent request does not open a second proposal", written exactly
            // once as `None` at insert, and never read or set anywhere in the
            // workspace. The dedupe it claimed to perform was actually being
            // done by this early `return`, which is a strictly WORSE rule — it
            // drops a re-send whether or not anything was ever authored. With
            // sponsorship on a bounded queue there are now real ways for the
            // first attempt to produce nothing (queue full; this node not yet a
            // participant; a durable-persist rollback), and under the old rule
            // every one of them was PERMANENT: the candidate stayed admitted,
            // kept retrying every 15 s forever, and no retry could ever reach
            // the authoring path again. The candidate's own retry is the
            // natural place to close that, so it re-enqueues while `proposed`
            // is unset and the sponsor makes it idempotent.
            let already = existing.proposed;
            let waiting = existing.first_seen.elapsed().as_secs();
            drop(pending);
            debug!(
                candidate = %cand_hex,
                waiting_secs = waiting,
                proposed = ?already,
                "join request re-sent by a candidate we are already holding"
            );
            if already.is_none() && self.auto_approve_joins {
                self.enqueue_sponsorship(sponsor, candidate);
            }
            return;
        }
        if pending.len() >= MAX_PENDING_JOIN_REQUESTS {
            warn!(
                candidate = %cand_hex,
                held = pending.len(),
                "join request refused: this node is already holding the maximum number of \
                 candidates awaiting sponsorship"
            );
            metrics::counter!("dregg_join_request_refused_total", "reason" => "pending_full")
                .increment(1);
            return;
        }
        pending.insert(
            candidate,
            PendingJoinRequest {
                node_id: candidate,
                ml_dsa_pubkey: ml_dsa,
                from,
                first_seen: std::time::Instant::now(),
                proposed: None,
            },
        );
        drop(pending);
        metrics::counter!("dregg_join_request_accepted_total").increment(1);
        info!(
            from = %from,
            candidate = %cand_hex,
            auto_approve = self.auto_approve_joins,
            "join request ACCEPTED: both key halves proven. Awaiting sponsorship by this committee \
             member (automatic under auto-approve-joins; otherwise `propose-epoch-transition --add`)"
        );

        // Sponsorship: HANDED OFF, never performed here. The authority checks
        // (are we a participant, is the candidate already one) are re-read at
        // AUTHORING time in `sponsor_pending_join`, because the constitution can
        // change while a candidate sits in the queue and the answer that matters
        // is the one true when the block is signed — not the one true when the
        // datagram arrived.
        if !self.auto_approve_joins {
            return;
        }
        self.enqueue_sponsorship(sponsor, candidate);
    }

    /// Hand a validated candidate to the serial sponsor task.
    ///
    /// `try_send` and NOT `send`: the whole value of the split is that the
    /// narrow-channel receiver never waits. A full queue costs THIS candidate a
    /// 15-second retry (which re-enqueues — see the re-send arm of
    /// [`Self::handle_join_request`]); a blocking send would cost the committee
    /// its refusals, which is the failure being repaired.
    fn enqueue_sponsorship(
        &self,
        sponsor: &tokio::sync::mpsc::Sender<[u8; 32]>,
        candidate: [u8; 32],
    ) {
        let cand_hex: String = candidate[..4].iter().map(|b| format!("{b:02x}")).collect();
        match sponsor.try_send(candidate) {
            Ok(()) => debug!(candidate = %cand_hex, "queued for sponsorship"),
            Err(tokio::sync::mpsc::error::TrySendError::Full(_)) => {
                warn!(
                    candidate = %cand_hex,
                    capacity = SPONSOR_QUEUE_CAPACITY,
                    "sponsorship queue is full — this candidate is admitted but not yet queued; \
                     its next re-send re-enqueues it. Join admission itself is UNAFFECTED."
                );
                metrics::counter!("dregg_join_sponsor_enqueue_dropped_total", "reason" => "full")
                    .increment(1);
            }
            Err(tokio::sync::mpsc::error::TrySendError::Closed(_)) => {
                warn!(
                    candidate = %cand_hex,
                    "sponsorship task is gone — no member on this node will author a Join for \
                     this candidate"
                );
                metrics::counter!("dregg_join_sponsor_enqueue_dropped_total", "reason" => "closed")
                    .increment(1);
            }
        }
    }

    /// Author the `Join` proposal for ONE already-validated candidate.
    ///
    /// Runs on the dedicated sponsor task (see `run_blocklace_sync_with_policy`),
    /// one candidate at a time, so the `lace.write()` this ultimately needs
    /// contends with the block producer and the gossip funnel WITHOUT holding
    /// the narrow join channel while it does. Nothing about the security
    /// argument moves: every fail-closed check — federation binding, ML-DSA
    /// proof of possession, already-a-participant, capacity — has already run in
    /// [`Self::handle_join_request`] before a candidate can reach this queue,
    /// and the proposal is still authored under THIS MEMBER's key by the same
    /// `propose_membership`, which still refuses an add whose PQ half it cannot
    /// resolve.
    pub async fn sponsor_pending_join(&self, state: &NodeState, candidate: [u8; 32]) {
        let cand_hex: String = candidate[..4].iter().map(|b| format!("{b:02x}")).collect();

        // AUTHORITY, RE-READ AT AUTHORING TIME.
        {
            let c = self.constitution.read().await;
            if c.current.is_participant(&candidate) {
                debug!(
                    candidate = %cand_hex,
                    "candidate became a participant while queued — nothing to sponsor"
                );
                return;
            }
            // Only a CURRENT participant can author a proposal that counts, so a
            // non-member that somehow received a request holds it and does nothing.
            if !c.current.is_participant(&self.self_key) {
                debug!(
                    candidate = %cand_hex,
                    "this node is not a current participant — its proposal would not count \
                     toward quorum; holding the candidate without sponsoring"
                );
                return;
            }
        }

        // ONE proposal per candidate. The read guard is released before
        // `propose_membership`, which takes `pending_joins.read()` itself in
        // `resolve_candidate_pq_key` — and tokio's RwLock is FAIR, so a writer
        // queued between the two would deadlock a re-entrant read.
        let held = {
            let pending = self.pending_joins.read().await;
            match pending.get(&candidate) {
                Some(p) => Some(p.proposed),
                None => None,
            }
        };
        match held {
            None => {
                warn!(
                    candidate = %cand_hex,
                    "sponsorship queued for a candidate this node is not holding — dropped \
                     (it is never this queue that decides a candidate is legitimate)"
                );
                return;
            }
            Some(Some(block)) => {
                debug!(
                    candidate = %cand_hex,
                    proposal_block = %block,
                    "already sponsored by this node — the retry is idempotent"
                );
                return;
            }
            Some(None) => {}
        }

        match self.propose_membership(state, candidate, true).await {
            Ok(block_id) => {
                // Record it BEFORE the log line: `proposed` is what makes every
                // subsequent re-send a no-op, and a crash between the two would
                // only cost a duplicate proposal, never a missing one.
                if let Some(p) = self.pending_joins.write().await.get_mut(&candidate) {
                    p.proposed = Some(block_id);
                }
                metrics::counter!("dregg_join_sponsored_total").increment(1);
                info!(
                    candidate = %cand_hex,
                    proposal_block = %block_id,
                    "SPONSORED a join request under this member's key (auto-approve-joins)"
                );
            }
            Err(reason) => warn!(
                candidate = %cand_hex,
                reason = %reason,
                "sponsorship of the join request did not land — the candidate stays admitted \
                 and its next re-send retries this"
            ),
        }
    }

    /// Cast an approval vote for a membership proposal.
    ///
    /// Creates a `MembershipVote` block with an `Approve` action referencing
    /// the proposal block, and disseminates it to peers.
    async fn cast_approval_vote(&self, state: &NodeState, proposal_block: BlockId) {
        // Fail-closed (F2): the vote advances our self strand, so land it durably
        // before broadcast; a persist failure withdraws it rather than emitting a
        // vote whose seq restart would re-author with different content.
        let Some(block) = self
            .author_add_block_or_rollback(
                state,
                Payload::MembershipVote {
                    action: MembershipAction::Approve { proposal_block },
                },
            )
            .await
        else {
            warn!(
                proposal = %proposal_block,
                "approval vote failed to persist durably — not broadcast"
            );
            return;
        };

        debug!(
            block_id = %block.id(),
            proposal = %proposal_block,
            "cast approval vote for membership proposal"
        );

        self.push_new_blocks().await;
    }

    /// Operator-facing: cast THIS node's approval vote for a pending
    /// membership proposal — the production twin of the devnet
    /// `auto_approve_joins` path (`POST /membership/approve`). An admitted
    /// proposal reaches quorum when enough CURRENT participants run this;
    /// the constitution amendment + live epoch transition then happen
    /// on-chain via `execute_finalized_membership`, no genesis re-roll.
    pub async fn approve_membership(
        &self,
        state: &NodeState,
        proposal_block: BlockId,
    ) -> Result<(), String> {
        {
            let c = self.constitution.read().await;
            if !c.current.is_participant(&self.self_key) {
                return Err(
                    "this node is not a current committee participant — its approval would \
                     not count toward quorum"
                        .to_string(),
                );
            }
            if c.votes.get_proposal(&proposal_block).is_none() {
                return Err(format!(
                    "unknown membership proposal {proposal_block} — it has not been \
                     finalized/registered on this node yet (check GET /api/membership)"
                ));
            }
            if c.votes.is_applied(&proposal_block) {
                return Err(format!(
                    "membership proposal {proposal_block} was already applied — the \
                     committee has advanced"
                ));
            }
        }
        self.cast_approval_vote(state, proposal_block).await;
        Ok(())
    }

    /// The live membership picture for the operator surface
    /// (`GET /api/membership`): current committee, threshold, constitution
    /// version, and every registered proposal with its tally.
    pub async fn membership_snapshot(&self) -> MembershipSnapshot {
        let c = self.constitution.read().await;
        let required_for = |p: &MembershipProposal| c.current.required_votes_for(p);
        let proposals = c
            .votes
            .proposal_tallies()
            .into_iter()
            .map(
                |(proposal_block, proposal, approvals, rejections, applied)| {
                    let required = required_for(&proposal);
                    MembershipProposalStatus {
                        proposal_block,
                        proposal,
                        approvals,
                        rejections,
                        required,
                        applied,
                    }
                },
            )
            .collect();
        MembershipSnapshot {
            participants: c.current.participants.clone(),
            threshold: c.threshold(),
            version: c.version(),
            frozen: c.membership_frozen,
            self_key: self.self_key,
            self_is_participant: c.current.is_participant(&self.self_key),
            proposals,
        }
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
    pub async fn apply_committee_change(
        &self,
        participants: &[[u8; 32]],
        pq_committee: HashMap<[u8; 32], dregg_federation::frost::MlDsaPublicKey>,
        threshold: usize,
    ) {
        // 1. Enroll the new committee's ML-DSA-65 keys into the finality
        //    Blocklace's PQ roster across the epoch transition, so the live wire
        //    ingest (`receive_block_pinned`) accepts a rotated-in validator's
        //    hybrid-signed blocks (and still fails closed on any creator whose PQ
        //    key the committee has not learned). `enroll_pq` is additive; a
        //    removed member's stale key is inert (it can no longer finalize).
        {
            let mut lace = self.lace.write().await;
            for (creator, pq_pk) in &pq_committee {
                // Roster keyed by the HYBRID id (== `Block::creator`), computed
                // from the rotated-in member's ed25519 + ML-DSA public keys.
                let ml_dsa = dregg_blocklace::pq::MlDsaPublicKey(pq_pk.0);
                let hybrid =
                    dregg_blocklace::finality::Block::hybrid_id_from_parts(creator, &ml_dsa);
                lace.enroll_pq(hybrid, ml_dsa);
            }
        }
        // 2. Advance the finalization-vote committee + quorum threshold — and
        //    the HYBRID-PQ key map alongside them (a participant absent from
        //    `pq_committee` cannot contribute to quorum; fail-closed). This is
        //    also the D7 DRAIN point: `reconfigure` retires every departing
        //    member's votes from the tallies that have not crossed yet, so a
        //    post-boundary quorum can never be assembled partly out of the
        //    configuration this install ended (Lean
        //    `Dregg2.Distributed.LeaveDrain.drainTally`).
        let drain = {
            let mut votes = self.votes.write().await;
            votes.reconfigure(participants.iter().copied(), pq_committee, threshold)
        };
        // 3. Admit every current participant to the authenticated gossip mesh.
        for pk in participants {
            let node_id = *blake3::hash(pk).as_bytes();
            self.gossip
                .register_peer_key(node_id, dregg_types::PublicKey(*pk))
                .await;
        }
        info!(
            participants = participants.len(),
            quorum_threshold = threshold,
            departed = drain.departed,
            votes_retired = drain.votes_retired,
            straddles_closed = drain.straddles_closed,
            "live consensus committee advanced (epoch transition applied)"
        );
        // 4. ⚑ THE LEAVER'S SIGNAL (D7 / SKM17 §3). If THIS node is the member the
        //    install removed, say so loudly, exactly once, at the install point.
        //    The protocol owes a departing member a SIGNAL, never a delivery
        //    guarantee — DBRB Thms. 81/82 prove the latter unimplementable even
        //    for one crash fault — and the signal is DERIVED, not received: the
        //    install position is a function of the committed prefix
        //    (`LeaveDrain.outAt_immutable`), so every honest node computes the
        //    same one and no message has to reach us for this to be true.
        if !participants.contains(&self.self_key) {
            let tag: String = self.self_key[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            warn!(
                self_key = %tag,
                new_participant_count = participants.len(),
                "LEAVE SIGNAL: this node is NOT in the newly installed committee. Our \
                 finalization votes are no longer admissible anywhere and our in-flight votes \
                 have been retired by every survivor's drain. Nothing further is promised to \
                 us and nothing is owed: the operator may switch this node off now. What we \
                 authored before this position is already in the committed order; what we \
                 author after it is un-includable by construction."
            );
        }
    }

    /// The ML-DSA-65 key to put in a `Join` proposal for `node_id`.
    ///
    /// Two sources, in order, and NEITHER is derivable or guessable:
    ///  * a validated narrow-channel join request from the candidate itself
    ///    (proof of possession already checked in `handle_join_request`);
    ///  * committed state, for a member the roster already knows — the re-add
    ///    case after a `Leave`.
    async fn resolve_candidate_pq_key(
        &self,
        state: &NodeState,
        node_id: &[u8; 32],
    ) -> Option<dregg_federation::frost::MlDsaPublicKey> {
        if let Some(p) = self.pending_joins.read().await.get(node_id) {
            return Some(p.ml_dsa_pubkey.clone());
        }
        state.read().await.ml_dsa_key_for(node_id).cloned()
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
    ///
    /// ⚑ AN ADD REFUSES WITHOUT THE CANDIDATE'S ML-DSA KEY, and that refusal is
    /// the point. `MembershipAction::Join` must carry the PQ half or a
    /// ratification HALTS finality on every node (see the module header, ring 3).
    /// The key cannot be derived — `ML-DSA.KeyGen` needs the seed — so it comes
    /// from the candidate's own narrow-channel join request, or from committed
    /// state for a member being re-added. With neither, authoring the proposal
    /// would be authoring a wedge, so we refuse and say why.
    pub async fn propose_membership(
        &self,
        state: &NodeState,
        node_id: [u8; 32],
        add: bool,
    ) -> Result<BlockId, String> {
        let action = if add {
            let ml_dsa = match self.resolve_candidate_pq_key(state, &node_id).await {
                Some(k) => k,
                None => {
                    let hex: String = node_id[..4].iter().map(|b| format!("{b:02x}")).collect();
                    error!(
                        candidate = %hex,
                        "REFUSING to propose this validator: no ML-DSA-65 public key is known for \
                         it. A Join without the PQ half cannot be projected into the tau \
                         participant set, so ratifying it would halt finality on every node. The \
                         candidate must first reach this committee over the narrow join channel \
                         (start it with `dregg-node join --bootstrap <member>:<gossip-port>`), \
                         which is what publishes its post-quantum key."
                    );
                    metrics::counter!("dregg_join_request_refused_total", "reason" => "operator_add_without_pq_key")
                        .increment(1);
                    // ⚑ Each refusal names ITS OWN reason: this one used to be
                    // reported upstream as "durable persist failed" (the other
                    // arm's diagnosis) with `success: true` around it.
                    return Err(
                        "no ML-DSA-65 public key is known for this candidate — the joiner must \
                         first publish it over the join channel (`dregg-node join --bootstrap \
                         <member>:<gossip-port>`); proposal not created"
                            .to_string(),
                    );
                }
            };
            MembershipAction::Join {
                node_id,
                ml_dsa_pubkey: dregg_blocklace::pq::MlDsaPublicKey(ml_dsa.0),
            }
        } else {
            MembershipAction::Leave { node_id }
        };
        // Fail-closed (F2): land the proposal durably before broadcast so a
        // persist failure cannot leave a broadcast-but-unpersisted proposal seq
        // that restart re-authors differently. `Err` ⇒ the proposal did not land.
        let block = self
            .author_add_block_or_rollback(
                state,
                Payload::MembershipVote {
                    action: action.clone(),
                },
            )
            .await
            .ok_or_else(|| {
                "durable persist failed — the proposal was rolled back and NOT broadcast \
                 (F2 fail-closed); proposal not created"
                    .to_string()
            })?;
        let block_id = block.id();
        info!(
            block_id = %block_id,
            add,
            "operator proposed epoch transition (membership change) on running node"
        );
        self.push_new_blocks().await;
        Ok(block_id)
    }
}

/// Per-poll wall-clock budget for the verified-Lean tau-order FFI
/// (`VerifiedFinality::compute_order`). The single serial finality executor
/// awaits this FFI before the next poll can start, so an O(history) recompute on
/// a large cross-linked lace that exceeds a round of block production freezes ALL
/// finalization. `poll_finalized_blocks` bounds the FFI by this budget so one slow poll cannot
/// stall the executor. Default 2500 ms; operators can tune it via
/// `DREGG_FINALITY_ORDER_TIMEOUT_MS` (a value of 0 falls back to the default rather than
/// disabling the bound).
///
/// ⚑ WHAT A MISS COSTS DEPENDS ON THE NODE, and this doc used to state only one of the two
/// outcomes ("on timeout, uses the edge-faithful Rust `ordering::tau` order for that poll"). That
/// is true ONLY where the Rust twin is permitted (`rust_tau_fallback_allowed`: no verified archive
/// at all, or `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`). On a Lean-linked node without the escape —
/// the deployed PoA posture, which `scripts/poa-devnet.sh` pins — a miss FAILS CLOSED and the poll
/// finalizes nothing. Same trigger, opposite failure mode, opposite remedy.
///
/// ⚑ RAISING THIS IS NOT A FIX. The verified `dregg_tau_order` is super-quadratic in the lace size
/// and a lace grows without bound, so any constant budget is crossed by a long-enough-lived chain;
/// a larger one only moves the crossing. The fix is to make the verified path cheaper — the
/// dominating cost is `Lace.lookup` (`metatheory/Dregg2/Authority/Blocklace.lean`), a `List.find?`
/// over the whole lace, called inside the innermost loops of `tauOrderFastImpl`
/// (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`), which already builds `Std.HashMap`
/// past/round maps but has no `BlockId → Block` index. See `docs/VERIFIED-GATE-PERF.md`.
///
/// `pub` so `/status` can report the budget alongside the provenance tally: a claim that holds
/// only under a budget has to publish the budget.
pub fn verified_order_ffi_timeout() -> Duration {
    let ms = std::env::var("DREGG_FINALITY_ORDER_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|v| *v > 0)
        .unwrap_or(2500);
    Duration::from_millis(ms)
}

/// The `DREGG_ALLOW_UNVERIFIED_CONSENSUS` labeled-unaudited escape hatch (the SAME variable the
/// startup marshal-only tripwire and the verified-consensus hard-check in `lib.rs` read). Running the
/// un-verified Rust `ordering::tau` twin as the live finalized order is a DELIBERATE opt-in — this
/// returns `true` only when the operator explicitly set the variable to a truthy value.
fn allow_unverified_consensus() -> bool {
    matches!(
        std::env::var("DREGG_ALLOW_UNVERIFIED_CONSENSUS")
            .ok()
            .as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    )
}

/// TWIN-DELETION (#8): whether the Rust `ordering::tau` twin may serve as the live finalized order.
///
/// It is allowed ONLY when there is no verified `dregg_tau_order` archive to route to at all
/// (`!tau_order_available` — a genuinely no-Lean build, on which a full node is REFUSED to start at
/// the `lib.rs` verified-consensus hard-check unless the operator opted in), OR the operator
/// explicitly accepts unverified consensus (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`). On a Lean-linked
/// full node WITHOUT the escape it is FORBIDDEN — a poll with no verified order then FAILS CLOSED
/// (finalizes nothing) instead of silently running the twin. So on the deployed verified-role node
/// the Rust twin never decides finality.
fn rust_tau_fallback_allowed(tau_order_available: bool, allow_unverified: bool) -> bool {
    !tau_order_available || allow_unverified
}

/// Whether a payload is CONSENSUS-ACTIONABLE — i.e. finalizing it changes committed state, so the
/// verified finality gate is entitled to have an opinion about it. `Ack`/`Data` are DAG plumbing:
/// they are served to the executor as `Inert` and carry no state transition.
///
/// One definition, two consumers: the per-block belt gate (which only refuses ACTIONABLE blocks the
/// verified projection did not finalize) and the belt's fail-closed vacuity count (which must not
/// refuse a poll whose pending set is heartbeats only). Inlining it twice is how the two drift.
fn is_consensus_actionable(payload: &Payload) -> bool {
    matches!(
        payload,
        Payload::Turn(_)
            | Payload::TurnBundle(_)
            | Payload::ConsensusTimedTurnV1(_)
            | Payload::MembershipVote { .. }
            | Payload::Checkpoint { .. }
    )
}

/// `DREGG_REQUIRE_LEAN=1` — "I demand the verified artifact". The tree-wide signal (the
/// `dregg-lean-ffi` build gate; `turn`'s `require_verified_conservation_gate`) that a build must not
/// take ANY declared bypass around a verified gate. It promotes both of
/// [`belt_gate_bypass_allowed`]'s bypasses to the hard refusal, which is how an archive-less build —
/// a test binary, a dev box — can drive the fail-closed pole that a deployed node reaches on its own.
fn require_verified_lean_gate() -> bool {
    std::env::var_os("DREGG_REQUIRE_LEAN")
        .is_some_and(|v| matches!(v.to_string_lossy().trim(), "1" | "true" | "on" | "yes"))
}

/// FAIL-CLOSED CLASS (the finality twin of `rust_tau_fallback_allowed` / `quorum_rust_fallback_allowed`):
/// whether the verified finality BELT gate — the `dregg_blocklace_finalize` `(creator, seq)`
/// projection of `BlocklaceFinality.tauOrder` — may be BYPASSED when it could not answer.
///
/// Two DECLARED bypasses, and nothing else:
///   * `!belt_export_linked` — the archive contains no `dregg_blocklace_finalize` at all, so there
///     is no verified projection in this binary to route to. That is the archive-less build (every
///     test binary, the wasm/zkVM guest, a marshal-only dev box), and for a full-mode node it is the
///     state the `lib.rs` verified-consensus hard-check refuses to start in.
///   * `allow_unverified` — `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, the operator's explicit acceptance
///     of un-verified consensus. They already accepted the Rust `ordering::tau` ORDER; the belt is a
///     secondary check over that same order, so its absence adds nothing they did not accept.
///
/// `require_lean` (`DREGG_REQUIRE_LEAN=1`) revokes BOTH.
///
/// What is DELIBERATELY not a bypass, and is the hole this closes: the export IS linked and this
/// poll still got no answer out of it (the wire returned `ERR`, or the blocking FFI thread
/// panicked). That state used to warn and advance finality over the un-gated order.
fn belt_gate_bypass_allowed(
    belt_export_linked: bool,
    allow_unverified: bool,
    require_lean: bool,
) -> bool {
    // ⚑ ONE BOOLEAN EXPRESSION, DELIBERATELY — DO NOT REINTRODUCE THE EARLY RETURN.
    //
    // This was `if require_lean { return false; }` followed by the disjunction, and that shape
    // BLINDED invariant 6 (`scripts/ci-invariants/gate-dataflow.py`) at this very site. The
    // checker inlines a declared discriminator's body when searching the gate-absent region for
    // a terminal verdict, and a bare `return false` reads as a REFUSAL token. So with this
    // predicate's early return present, deleting `finality_belt_disposition`'s real
    // `return Err(FinalityGateUnavailable)` still PASSED — the guard reported
    // "the non-exempt arm REFUSES (`return false`)", quoting *this function* rather than the
    // disposition it was supposed to be checking. Measured, not theorised: mutating the refusal
    // to `Ok(())` left invariant 6 green until this was flattened.
    //
    // `coord_gate_bypass_allowed` carries the same note for the same reason.
    !require_lean && (!belt_export_linked || allow_unverified)
}

/// Why a poll REFUSED to advance finality. Distinct from every "the verified rule did not finalize
/// this block" outcome on purpose: mirroring conservation's `ConservationGateUnavailable`, a
/// VERIFIER's missing archive is not a PROVER's fault. No block is invalid here and none was
/// refused — the gate could not answer, so this poll declines to advance at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FinalityAdvanceRefusal {
    /// The verified `dregg_blocklace_finalize` projection gate was ARMED (this poll is advancing over
    /// an order the verified Lean rule did not produce) and could not answer, with no declared
    /// bypass. Finality does not advance this poll.
    FinalityGateUnavailable,
}

impl std::fmt::Display for FinalityAdvanceRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FinalityGateUnavailable => write!(
                f,
                "FinalityGateUnavailable: the verified finality projection gate \
                 (dregg_blocklace_finalize) was armed and could not answer — finality does not \
                 advance (this is a MISSING GATE, not a verdict about any block)"
            ),
        }
    }
}

/// THE FAIL-CLOSED DISPOSITION for the verified finality belt gate. Called by
/// `poll_finalized_blocks` on every poll where the belt is armed — i.e. every poll about to advance
/// finality over an order the verified Lean rule did not produce.
///
/// `Ok(())` ⇒ the poll may advance. `Err(FinalityGateUnavailable)` ⇒ finalize NOTHING this poll.
///
/// ## The vacuity short-circuit, and why it is REQUIRED
///
/// A refusal that fires where it means nothing is not a gate. The belt only ever gates
/// CONSENSUS-ACTIONABLE blocks (`is_consensus_actionable`); `Ack`/`Data` are DAG plumbing served as
/// `Inert`. A poll whose pending set is heartbeats only therefore has NO decision for the belt to
/// make, and refusing it would halt DAG progress on a verdict that does not exist — the same
/// over-refusal the conservation fix hit when a `set_state` with no value delta tripped its gate.
/// So `actionable_pending == 0` short-circuits BEFORE the gate is consulted. (The other two vacuous
/// states are handled at the arming site: `ordered_from_lean` — the order IS the verified rule's
/// output, nothing un-verified to gate — and an empty `pending`, which returns earlier.)
fn finality_belt_disposition(
    belt_gate: Option<&crate::finality_gate::VerifiedFinality>,
    actionable_pending: usize,
    belt_export_linked: bool,
    allow_unverified: bool,
    require_lean: bool,
) -> Result<(), FinalityAdvanceRefusal> {
    // VACUOUS POLL — no consensus-actionable block is pending, so there is no admission decision in
    // existence for the projection to make. Short-circuited BEFORE the gate is consulted, so the
    // refusal below can never fire where it would mean nothing.
    if actionable_pending == 0 {
        return Ok(());
    }
    let Some(_admissions) = belt_gate else {
        if belt_gate_bypass_allowed(belt_export_linked, allow_unverified, require_lean) {
            return Ok(());
        }
        return Err(FinalityAdvanceRefusal::FinalityGateUnavailable);
    };
    Ok(())
}

// ─── The BEARER-AUTHORITY-LEG disposition (the fail-open class, ATTESTATION flavour) ─────────────
//
// ⚑ THE QUESTION THAT DECIDED THIS SITE'S SHAPE, ANSWERED BEFORE THE FIX (2026-07-26):
// **DOES A VERIFIER ACCEPT A v1 PROOF FOR A BEARER-DELEGATED TURN?**
//
// The answer is YES — and the reason is worse than a missing check, so state it exactly. The
// verification MODE is a CALLER-SUPPLIED ARGUMENT, not a property derived from the turn:
//
//   sdk/src/full_turn_proof.rs::verify_full_turn_bound(proof, old_commit, new_commit,
//                                                     expected_cap_membership: Option<&CapMembershipExpectation>)
//
// and the AUTHORITY demand lives entirely inside `if let Some(expected) = expected_cap_membership`
// ("capability-gated turn carries no AUTHORITY leg"). That refusal is real and it works. But
// `verify_full_turn` — the ONLY entry point anyone outside the prover calls — hardcodes `None`, the
// signature takes NO turn and NO receipt (it does not even bind `turn_hash`), and a tree-wide grep
// for `CapMembershipExpectation` finds exactly ONE non-test construction site: `turn_proving.rs`,
// INSIDE THE PROVER, one line after minting the proof. Zero in `lightclient/`, `eth-lightclient/`,
// `dreggnet-game-board/`, `verifier/`, `net/`, `blocklace/`, the node API, or the discord bot (which
// re-verifies stored proofs but reconstructs the component set from the proof's OWN labels and calls
// the `None` entry). The retained IVC input carries only the rotated effect-vm leg, so the
// light-client aggregate has no authority leg on ANY routing arm. So: the prover picks its own
// verification mode, and it is the only party that ever picks one.
//
// ⚑ AND THE SCOPE QUALIFIER THAT KEEPS THAT FROM BEING OVER-READ — IT IS **NOT** AN AUTHORIZATION
// BYPASS, AND CALLING IT A FORGERY SURFACE WOULD BE WRONG. A bearer-delegated turn cannot be
// COMMITTED without its delegation being real: `turn/src/executor/authorize.rs::verify_bearer_cap`
// checks the delegator's Ed25519 signature (`verify_strict`), resolves the delegator cell, requires
// it to ACTUALLY HOLD the capability (`BearerCapDelegatorLacksCapability`), and enforces expiry,
// the committed revocation registry, permission non-amplification and facet attenuation — and every
// node RE-EXECUTES the finalized turn before any proving happens. The missing leg is therefore an
// ATTESTATION / COMPLETENESS gap (the proof UNDER-CLAIMS what was enforced), not an authority hole.
// The durable residual is on the VERIFY side and is NOT closed here: nothing in the tree derives
// "this turn needed an authority leg" from a receipt, so a stripped leg is unnoticeable to every
// consumer. Closing that means giving verifiers the receipt, which is a protocol change, not a
// disposition. Named, not laundered.
//
// What IS closed here: the prover no longer PUBLISHES an attestation it knows to be incomplete.

/// Whether the operator accepted publishing a bearer-delegated turn's full-turn proof WITHOUT its
/// AUTHORITY leg (`DREGG_ALLOW_UNBOUND_BEARER_PROOF=1`) — a DECLARED bypass that
/// `DREGG_REQUIRE_LEAN=1` revokes. The escape is real, not decorative: on a node that genuinely
/// cannot resolve a delegator, the v1 proof still attests the STATE TRANSITION, and an operator may
/// prefer a partial attestation (and its IVC retention) to none.
fn allow_unbound_bearer_proof() -> bool {
    std::env::var_os("DREGG_ALLOW_UNBOUND_BEARER_PROOF")
        .is_some_and(|v| matches!(v.to_string_lossy().trim(), "1" | "true" | "on" | "yes"))
}

/// FAIL-CLOSED CLASS (the ATTESTATION sibling of `belt_gate_bypass_allowed` /
/// `coord_gate_bypass_allowed`): whether a bearer-delegated turn's missing AUTHORITY leg may be
/// BYPASSED, publishing the v1 proof anyway.
///
/// ONE DECLARED bypass, and nothing else: `allow_unbound` — `DREGG_ALLOW_UNBOUND_BEARER_PROOF=1`.
/// `require_lean` (`DREGG_REQUIRE_LEAN=1`) revokes it.
///
/// ⚑ ONE BOOLEAN EXPRESSION, DELIBERATELY — DO NOT REINTRODUCE AN EARLY RETURN, for the reason
/// measured at this site's two siblings and recorded in `1736835f69`: a leading
/// `if require_lean { return false; }` is a REFUSAL token that `gate-dataflow.py` finds while
/// inlining this helper, which blinds invariant 6 to the caller's real refusal arm.
fn bearer_authority_bypass_allowed(allow_unbound: bool, require_lean: bool) -> bool {
    !require_lean && allow_unbound
}

/// Why a finalized turn published NO full-turn proof. Distinct from every `Prove`/`Verify` failure
/// on purpose: mirroring twin#1's `ConservationGateUnavailable`, nothing was rejected and no proof
/// failed to verify — the AUTHORITY BINDING WAS UNBUILDABLE, so the attestation is withheld rather
/// than published in an under-claiming form. The turn itself still commits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BearerAuthorityRefusal {
    /// The turn is bearer-delegated (its receipt carries a `BearerSignedDelegation` consumed-cap
    /// witness) and the node could not resolve the delegator's canonical pre-state capability root,
    /// so no AUTHORITY leg can be bound. No proof is published for this turn.
    DelegatorCapRootUnresolvable,
}

impl std::fmt::Display for BearerAuthorityRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DelegatorCapRootUnresolvable => write!(
                f,
                "DelegatorCapRootUnresolvable: a BEARER-DELEGATED turn's delegator pre-state \
                 capability root could not be resolved, so the AUTHORITY leg is unbuildable — NO \
                 full-turn proof is published (this is a MISSING BINDING, not a verdict about the \
                 turn; the executor already enforced the delegation and the turn still commits)"
            ),
        }
    }
}

/// THE FAIL-CLOSED DISPOSITION for a bearer-delegated turn's AUTHORITY leg. Called on the finalized
/// commit path once per proven candidate.
///
/// `Ok(())` ⇒ proving proceeds normally. `Err(DelegatorCapRootUnresolvable)` ⇒ REFUSE: publish no
/// proof at all rather than a v1 proof that silently omits the authority binding.
///
/// ## The vacuity short-circuit, and why it is REQUIRED
///
/// A refusal that fires where it means nothing is not a gate. The overwhelming majority of turns are
/// not bearer-delegated at all — self-sovereign turns, note spends, and actor-held capability turns
/// all have no delegator and no authority leg to be missing. Refusing there would stop the node
/// publishing ANY proof, which is the same over-refusal conservation hit on a `set_state` with no
/// value delta and twin#8b hit on a heartbeat-only poll. So a turn that is not bearer-delegated
/// short-circuits BEFORE the delegator root is consulted.
fn bearer_authority_disposition(
    delegator_cap_root: Option<&[dregg_circuit::field::BabyBear; 8]>,
    turn_is_bearer_delegated: bool,
    allow_unbound: bool,
    require_lean: bool,
) -> Result<(), BearerAuthorityRefusal> {
    // VACUOUS TURN — no bearer delegation was exercised, so there is no authority leg in existence
    // to be missing. Short-circuited BEFORE the root is consulted, so the refusal below can never
    // fire where it would mean nothing.
    if !turn_is_bearer_delegated {
        return Ok(());
    }
    let Some(_root) = delegator_cap_root else {
        if bearer_authority_bypass_allowed(allow_unbound, require_lean) {
            return Ok(());
        }
        return Err(BearerAuthorityRefusal::DelegatorCapRootUnresolvable);
    };
    Ok(())
}

// TEST-ONLY fault injection for the belt gate's ARMED-BUT-UNANSWERABLE state — the export linked,
// the poll advancing over a non-Lean order, and no answer out of the FFI (a wire `ERR` or a panicked
// blocking thread).
//
// It exists because that state is not producible in-process on EITHER build. With the archive
// present, `compute_order` succeeds, so `ordered_from_lean` is true and the belt is never armed; with
// the archive absent, `finality_gate_available()` is false, so the miss is a DECLARED bypass.
// Reaching the armed-and-unanswerable state otherwise requires `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`,
// which is itself a declared bypass. So without this, the poll-level refusal could only be asserted
// on an archive-less box — i.e. it would pass VACUOUSLY on ember's laptop.
//
// `#[cfg(test)]`: it does not exist in any non-test build, and the checker in
// `scripts/ci-invariants/gate-dataflow.py` strips `cfg(test)` definitions before slicing.
//
// THREAD-LOCAL, not a static: several other tests in this binary call `poll_finalized_blocks`
// concurrently and would see a process-wide flag, turning them flakily red. `#[tokio::test]` polls
// its future on the calling thread (current-thread runtime), so the poll body reads the same
// thread-local the test set.
//
// (Plain `//` comments, not `///`: a doc comment on a macro invocation is an `unused_doc_comments`
// warning — the macro would have to emit the docs itself.)
#[cfg(test)]
thread_local! {
    static FORCE_BELT_GATE_UNANSWERABLE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
fn belt_gate_fault_injected() -> bool {
    FORCE_BELT_GATE_UNANSWERABLE.with(|c| c.get())
}

/// TEST-ONLY: arm/disarm the belt-gate fault injector for THIS thread. See
/// [`FORCE_BELT_GATE_UNANSWERABLE`].
#[cfg(test)]
fn set_belt_gate_fault_injected(on: bool) {
    FORCE_BELT_GATE_UNANSWERABLE.with(|c| c.set(on));
}

#[cfg(not(test))]
#[inline]
fn belt_gate_fault_injected() -> bool {
    false
}

/// Build a `dregg_blocklace::Blocklace` (the ordering-compatible type) from
/// the finality-layer blocklace. The ordering module's `tau()` function
/// operates on the simpler `Blocklace` from `lib.rs`.
///
/// Returns the ordering blocklace and a mapping from ordering BlockIds to
/// finality BlockIds (needed because the two types use different hash schemes).
/// ⚑ `pub` (was `pub(crate)`) so `node/tests/verified_order_budget.rs` can measure and
/// differentially compare the REAL projection the node runs. A test that rebuilds this
/// construction itself would be testing its own mirror, not the node's path — and the
/// topological-insertion fix documented above is precisely the part a mirror gets wrong.
pub fn build_ordering_blocklace(
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

    // ── TOPOLOGICAL (CAUSAL) INSERTION — Kahn's algorithm ───────────────────────
    // `insert_unverified` enforces causal closure: a block whose predecessors are
    // not YET inserted has those edges DROPPED (`filter_map(finality_to_ordering.get)`
    // below only keeps already-inserted preds). The prior code inserted sorted by
    // `(seq, creator)`, which equals topological order ONLY on a clean round-
    // synchronous single-machine DAG. In the CROSS-MACHINE CATCH-UP case a lagging
    // creator's late block has a LOW `seq` but cites the current tips (a HIGH
    // DAG-depth round); the `(seq, creator)` sort then places it BEFORE its
    // predecessors, dropping those edges and collapsing the projected DAG depth.
    // Rust `ordering::tau` then finds no super-ratified leader and returns
    // `rust_len = 0` while the verified Lean order — which runs on the FULL edge
    // set — returns hundreds: the 291 false `DIFFERENTIAL DIVERGENCE lean_len=180
    // rust_len=0` alarms (docs/CROSS-MACHINE-FINALITY-FINDING.md §2).
    //
    // Insert in TOPOLOGICAL order instead: every in-lace predecessor lands before
    // its dependent, so NO in-lace edge is ever dropped and the Rust projection
    // carries the SAME edge set as the Lean authority. Ties (blocks whose
    // predecessors are all satisfied at the same frontier) break by
    // `(seq, creator, id)` for a deterministic linearization. Predecessors NOT
    // present in the lace are edges NEITHER order traverses (the Lean wire-build
    // filters them identically), so they impose no ordering constraint.
    let mut indeg: HashMap<BlockId, usize> = HashMap::new();
    let mut succ: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (id, block) in finality_lace.iter() {
        let in_lace_preds = block
            .predecessors
            .iter()
            .filter(|p| finality_lace.get(p).is_some())
            .count();
        indeg.insert(*id, in_lace_preds);
        for p in &block.predecessors {
            if finality_lace.get(p).is_some() {
                succ.entry(*p).or_default().push(*id);
            }
        }
    }
    // Deterministic ready-frontier: a min-heap keyed by `(seq, creator, id)`.
    let heap_key = |id: &BlockId| -> std::cmp::Reverse<(u64, [u8; 32], BlockId)> {
        let b = finality_lace
            .get(id)
            .expect("indexed id is present in the lace");
        std::cmp::Reverse((b.seq, b.creator, *id))
    };
    let mut ready: std::collections::BinaryHeap<std::cmp::Reverse<(u64, [u8; 32], BlockId)>> =
        std::collections::BinaryHeap::new();
    for (id, d) in &indeg {
        if *d == 0 {
            ready.push(heap_key(id));
        }
    }

    while let Some(std::cmp::Reverse((_, _, finality_id))) = ready.pop() {
        let block = finality_lace
            .get(&finality_id)
            .expect("ready-frontier id is present in the lace");
        // Translate predecessors from finality IDs to ordering IDs. By topological
        // order every in-lace predecessor is ALREADY inserted, so this keeps the
        // full in-lace edge set (no dropped edge).
        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| finality_to_ordering.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(data) => data.clone(),
            Payload::TurnBundle(bundle) => bundle.signed_turn.clone(),
            Payload::ConsensusTimedTurnV1(bundle) => {
                let mut data = bundle.consensus_time().encode().to_vec();
                data.extend_from_slice(bundle.signed_turn());
                data
            }
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
        finality_to_ordering.insert(finality_id, ordering_id);
        ordering_to_finality.insert(ordering_id, finality_id);

        // Relax successors: once all of a block's in-lace predecessors are
        // inserted it joins the ready frontier (Kahn's algorithm).
        if let Some(children) = succ.get(&finality_id) {
            for child in children.clone() {
                if let Some(d) = indeg.get_mut(&child) {
                    *d -= 1;
                    if *d == 0 {
                        ready.push(heap_key(&child));
                    }
                }
            }
        }
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
/// HYBRID-PQ: assemble the ML-DSA-65 committee key map for `participants` from
/// state's genesis-published, INDEX-ALIGNED
/// `known_federation_keys` / `known_federation_ml_dsa_keys` pair.
///
/// A participant with no published ML-DSA key gets NO entry — fail-closed: the
/// [`crate::finalization_votes::VoteCollector`] will never count that member's
/// votes toward quorum (a missing PQ key is never an ed25519-only downgrade).
async fn pq_committee_for_participants(
    state: &NodeState,
    participants: &[[u8; 32]],
) -> HashMap<[u8; 32], dregg_federation::frost::MlDsaPublicKey> {
    let s = state.read().await;
    let mut map = HashMap::new();
    for pk in participants {
        if let Some(pq) = s.ml_dsa_key_for(pk) {
            map.insert(*pk, pq.clone());
        }
    }
    map
}

/// Project the canonical ed25519 participant set (`admitted`, from the committed
/// constitution) to the HYBRID-id set tau orders over, reading each member's ML-DSA
/// half from COMMITTED consensus state (`NodeState::ml_dsa_key_for`) — NEVER from
/// node-local vote-collector knowledge (`votes.pq_key`).
///
/// This is the F-CO-1 fix boundary: the result is a deterministic function of
/// `(admitted, committed roster)` alone — `votes` is not an input — so two honest
/// nodes with the same committed roster but DIFFERENT per-node ML-DSA-key knowledge
/// project the BYTE-IDENTICAL participant set (hence the identical tau leader
/// schedule and finalized order). A member with no committed ML-DSA key is DROPPED;
/// the caller MUST fail closed when the projection does not cover every admitted
/// member (never order over a subset — see `poll_finalized_blocks`).
async fn project_committed_participants(state: &NodeState, admitted: &[[u8; 32]]) -> Vec<[u8; 32]> {
    let s = state.read().await;
    admitted
        .iter()
        .filter_map(|ed25519| {
            s.ml_dsa_key_for(ed25519).map(|ml_dsa| {
                dregg_blocklace::finality::Block::hybrid_id_from_parts(
                    ed25519,
                    &dregg_blocklace::pq::MlDsaPublicKey(ml_dsa.0),
                )
            })
        })
        .collect()
}

/// The creator HYBRID ids the SOLO (`admitted.len() <= 1`) finality arm may finalize — the n=1 face
/// of the verified rule's `BlocklaceFinality.enrolledId`.
///
/// ⚑ SUBSTRATE. The finalization RULE is Lean-authored and unchanged: `enrolledId` + `tauOrder`,
/// with `tauOrder_only_enrolled` ("every finalized block's creator is a participant", no hypothesis
/// on the lace) and `tauOrder_enrolled_eq_unfiltered` ("on an all-enrolled lace the filter is the
/// identity"). Nothing in `metatheory/` needed to change for this. What was wrong was WHICH FUNCTION
/// the live path calls: the `admitted <= 1` arm of `poll_finalized_blocks` short-circuits the
/// verified rule entirely (`ordering::tau`/`tauOrder` cannot serve it — `find_all_final_leaders`
/// breaks at `wave_end > max_round`, and with wavelength 3 a fresh solo lace has `max_round == 1`,
/// so the verified rule finalizes NOTHING until three rounds exist and the mutation-driven solo
/// cadence never produces them). So the arm stays a `seq` order and gains the rule's ENROLLMENT
/// PREDICATE, keyed by the same hybrid id `enrolledId` compares.
///
/// TWO SOURCES, and the second is what makes the filter safe at cold start:
///
///  * `projected` — [`project_committed_participants`]'s output: the admitted constitutional
///    members whose ML-DSA half is in COMMITTED consensus state. This is the only sound source for
///    a PEER's hybrid id (`ML-DSA.KeyGen` needs the seed, which we do not have for a peer, so a
///    peer's `H(ed25519 ‖ ml_dsa)` genuinely cannot be derived from its ed25519 public key).
///  * `self_hybrid` — OUR OWN hybrid id, admitted only when our own ed25519 IS one of the
///    `admitted` constitutional participants. `ML-DSA.KeyGen` is deterministic in the seed and we
///    own our seed, so this is derivable with NO committed key — `blocklace/src/signer.rs`'s
///    `HybridBlockSigner` holds it already, having paid the derivation once at `Blocklace::new`,
///    and it is BY CONSTRUCTION the `creator` every block this node authors carries. This is not a
///    widening of the enrolled set: it is the LOCAL computation of a projection entry that
///    committed state would carry the identical value for. It is also the narrowly-typed case that
///    cannot be entered remotely — it names exactly one key, our signer's, and no network peer can
///    influence which key that is.
///
/// The result is EMPTY only when this node is not an admitted participant AND no admitted
/// participant has a committed ML-DSA key; the caller then finalizes nothing and warns, the same
/// halt-not-fork disposition the `participants.len() != admitted.len()` arm uses.
fn solo_enrolled_creators(
    projected: &[[u8; 32]],
    admitted: &[[u8; 32]],
    self_ed25519: &[u8; 32],
    self_hybrid: [u8; 32],
) -> std::collections::HashSet<[u8; 32]> {
    let mut enrolled: std::collections::HashSet<[u8; 32]> = projected.iter().copied().collect();
    if admitted.contains(self_ed25519) {
        enrolled.insert(self_hybrid);
    }
    enrolled
}

/// Abort the process because consensus startup failed.
///
/// Every early exit in [`run_blocklace_sync_with_policy`] leaves the same object
/// behind: a node with NO consensus. Its only deployed caller
/// (`lib.rs::run`, `if let Some(handle) = …` with no `else`) then continues to
/// bind HTTP and serve, so the node accepts every turn, applies none, reports
/// `consensus_live:false` / `block_count:0`, and answers `{"success":true}` to
/// grants that never land. That is the fail-open shape: the check that would
/// have refused instead logged and proceeded, and to every external liveness
/// probe the process looks alive.
///
/// Measured on 2026-07-26 with the gossip port held by another process:
///
/// ```text
/// ERROR …blocklace_sync: failed to create PeerNode for blocklace gossip
///       error=bind error: Address already in use (os error 48)
///  INFO dregg_node: HTTP API listening addr=127.0.0.1:8521
/// $ curl -s localhost:8521/api/faucet -d '{"recipient":"7a…7a","amount":10000}'
/// {"success":true,"turn_hash":"447e63…"}
/// $ curl -s localhost:8521/api/cell/7a…7a
/// {"found":false,"balance":0,…}
/// ```
///
/// There is no mode in this binary where that node is useful. `--federation-mode
/// solo` still runs the real committee-of-one blocklace through this same
/// function (the block production loop lives past every one of these exits);
/// there is no `--no-gossip` flag; and every in-process caller passes
/// `gossip_port = 0` (OS-assigned, cannot collide) and already `.expect()`s a
/// handle. So the refusal is unconditional: log the operator-facing reason, then
/// die before the HTTP surface exists.
fn refuse_to_start_without_consensus(reason: &str) -> ! {
    error!(
        reason,
        "REFUSING TO START: consensus did not come up, and a dregg-node without consensus \
         accepts turns and applies none — it would serve HTTP with consensus_live:false and \
         block_count:0 while answering success to grants that never land. Fix the reason above \
         and restart."
    );
    panic!("refusing to start without consensus: {reason}");
}

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
    let consensus_time_policy = match consensus_time_policy_v1_from_env() {
        Ok(policy) => policy,
        Err(error) => {
            refuse_to_start_without_consensus(&format!(
                "consensus-time-v1 deployment coordinate unavailable: {error}"
            ));
        }
    };
    run_blocklace_sync_with_policy(
        state,
        gossip_port,
        auto_approve_joins,
        blocklace_checkpoint_interval,
        constitution_timeout_ms,
        block_cadence_ms,
        idle_heartbeat_ms,
        min_block_interval_ms,
        advertise_addr,
        consensus_time_policy,
    )
    .await
}

/// Whether consensus startup may author this node's own constitutional Join
/// proposal when its key is outside the current committee.
///
/// `FollowOnly` is deliberately an enum rather than a second approval boolean:
/// receiving and verifying history is not a request for admission.  It leaves
/// the node connected and catching up but forbids the one local write that
/// would otherwise turn an observer into an applicant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MembershipProposalPolicy {
    ProposeIfNonMember,
    FollowOnly,
}

/// Dependency-injected consensus startup used by the node after it loads the shared public
/// `genesis.json`, by integrator tests, and by explicit embedders. [`run_blocklace_sync`] is the
/// environment-backed adapter for standalone callers; both routes converge here before any gossip
/// or production task starts.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn run_blocklace_sync_with_policy(
    state: NodeState,
    gossip_port: u16,
    auto_approve_joins: bool,
    blocklace_checkpoint_interval: u64,
    constitution_timeout_ms: u64,
    block_cadence_ms: u64,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
    advertise_addr: Option<SocketAddr>,
    consensus_time_policy: ConsensusTimePolicyV1,
) -> Option<BlocklaceHandle> {
    run_blocklace_sync_with_membership_policy(
        state,
        gossip_port,
        auto_approve_joins,
        MembershipProposalPolicy::ProposeIfNonMember,
        blocklace_checkpoint_interval,
        constitution_timeout_ms,
        block_cadence_ms,
        idle_heartbeat_ms,
        min_block_interval_ms,
        advertise_addr,
        consensus_time_policy,
    )
    .await
}

/// Consensus startup with an explicit local membership-proposal policy.
///
/// The legacy adapter above retains its historical auto-propose behavior for
/// existing callers. Operator entry points that promise proposal-neutral
/// observation must call this function with [`MembershipProposalPolicy::FollowOnly`].
#[allow(clippy::too_many_arguments)]
pub(crate) async fn run_blocklace_sync_with_membership_policy(
    state: NodeState,
    gossip_port: u16,
    auto_approve_joins: bool,
    membership_proposal_policy: MembershipProposalPolicy,
    blocklace_checkpoint_interval: u64,
    constitution_timeout_ms: u64,
    block_cadence_ms: u64,
    idle_heartbeat_ms: u64,
    min_block_interval_ms: u64,
    advertise_addr: Option<SocketAddr>,
    consensus_time_policy: ConsensusTimePolicyV1,
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
    // HYBRID-PQ: re-derive this node's ML-DSA-65 keypair from the SAME seed
    // (matching what `genesis.rs` published as its ML-DSA public key). No separate
    // key file — the ed25519 seed IS the PQ seed. The public half seeds our own
    // entry in the vote collector's PQ committee (authoritative for OURSELVES —
    // it is the key our own votes verify under — so a solo/bootstrap node counts
    // its own hybrid vote even before any genesis publishes a committee).
    let (pq_public_key, pq_signing_key) =
        dregg_federation::frost::MlDsaSigningKey::from_seed(&signing_key_bytes);

    // The constitution seed: prefer the REPLAYED manager main derived from the
    // persisted chain (`committee_replay` — carries every finalized membership
    // amendment AND in-flight proposal/vote state across the restart); fall
    // back to a fresh constitution over the configured committee (fresh chain,
    // solo bootstrap, or tests that never ran the boot derivation).
    let boot_cm = {
        let mut s = state.write().await;
        s.boot_constitution.take()
    };
    let (constitution_manager, participants): (ConstitutionManager, Vec<[u8; 32]>) = match boot_cm {
        Some(cm) => {
            let p = cm.participants().to_vec();
            (cm, p)
        }
        None => {
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
            // Initialize the constitution with our participant set. (tunable via CLI)
            let constitution = Constitution::new(participants.clone(), constitution_timeout_ms);
            (ConstitutionManager::new(constitution), participants)
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
        constitution_version = constitution_manager.version(),
        "initializing blocklace consensus"
    );

    // Attempt to restore blocklace from persistent storage.
    let (mut blocklace, restored_cursor) = {
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
                let durable_committed_turn_ids: std::collections::HashSet<BlockId> = s
                    .store
                    .commit_log_block_ids()
                    .unwrap_or_default()
                    .into_iter()
                    .map(BlockId)
                    .collect();
                // A deterministic rejection is the other durable terminal turn
                // outcome.  Re-derive its ids from the restored immutable lace
                // and authenticate every row against the carried payload.  This
                // closes the crash window where the row committed but RAM ACK
                // (and the best-effort served-id projection) did not.
                let mut durable_rejected_turn_ids = std::collections::HashSet::new();
                for (id, block) in restored_lace.iter() {
                    let Some(payload) = finalized_turn_bytes(&block.payload) else {
                        continue;
                    };
                    let key =
                        crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                            &id.0,
                        );
                    match s.store.get_config(&key) {
                        Ok(Some(bytes)) => match crate::signed_turn_validation::FinalizedPayloadRejectionRecord::decode_authenticated(&bytes, id.0, payload) {
                            Ok(_) => { durable_rejected_turn_ids.insert(*id); }
                            Err(reason) => error!(block_id = %id, reason, "malformed durable finalized-rejection authority; identity remains pending"),
                        },
                        Ok(None) => {}
                        Err(error) => error!(block_id = %id, error = %error, "could not read durable finalized-rejection authority; identity remains pending"),
                    }
                }
                let durable_turn_ids: std::collections::HashSet<BlockId> =
                    durable_committed_turn_ids
                        .union(&durable_rejected_turn_ids)
                        .copied()
                        .collect();
                let persisted_ids = s.store.load_executed_block_ids().unwrap_or_default();
                let persisted_count = persisted_ids.len();
                let executed_ids = reconcile_restored_execution_ids(
                    &restored_lace,
                    persisted_ids,
                    &durable_turn_ids,
                );
                info!(
                    blocks = block_count,
                    executed_restored = executed_ids.len(),
                    persisted_ids = persisted_count,
                    durable_turns = durable_turn_ids.len(),
                    durable_rejections = durable_rejected_turn_ids.len(),
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
                refuse_to_start_without_consensus(&format!(
                    "could not restore the blocklace from storage, and replacing durable history \
                     with a fresh lace is not an option: {e}"
                ));
            }
        }
    };
    if let Err(error) = blocklace.restore_consensus_time_v1(consensus_time_policy) {
        refuse_to_start_without_consensus(&format!(
            "the consensus-time-v1 flag-day migration refused durable history (genesis_unix_seconds \
             {}): an old timestamp-less turn database requires explicit migration or re-genesis: \
             {error}",
            consensus_time_policy.genesis_unix_seconds()
        ));
    }
    info!(
        genesis_unix_seconds = consensus_time_policy.genesis_unix_seconds(),
        restored_blocks = blocklace.len(),
        "consensus-time-v1 active; authenticated causal frontier rebuilt"
    );

    // ⚑ RESTORE LIVE-JOINED MEMBERS' POST-QUANTUM KEYS FROM THE CHAIN.
    //
    // `known_federation_keys` / `known_federation_ml_dsa_keys` are re-read from
    // `genesis.json` on EVERY boot, so a validator admitted by a live join has no
    // committed ML-DSA key after a restart — while `committee_replay` faithfully
    // restores it as a PARTICIPANT. That mismatch is exactly the
    // `projected < admitted` condition `poll_finalized_blocks` fails closed on:
    // the node would come back up with the right committee and HALT.
    //
    // The Join payload carries the key, in the same signed block that carries the
    // membership claim, so both halves are restorable from the same source. We
    // scan the restored lace rather than the finalized order because this only
    // LEARNS a key — it grants nothing, and `learn_committee_member_hybrid_key`
    // refuses to rebind a key that disagrees with one already committed, so a
    // stale or unratified proposal cannot displace a genesis member's key.
    {
        let mut restored_keys = 0usize;
        let mut s = state.write().await;
        for (_, block) in blocklace.iter() {
            if let Payload::MembershipVote {
                action:
                    MembershipAction::Join {
                        node_id,
                        ml_dsa_pubkey,
                    },
            } = &block.payload
                && s.learn_committee_member_hybrid_key(
                    node_id,
                    dregg_federation::frost::MlDsaPublicKey(ml_dsa_pubkey.0),
                )
            {
                restored_keys += 1;
            }
        }
        if restored_keys > 0 {
            info!(
                restored_keys,
                "restored live-joined members' ML-DSA-65 keys from the chain — the committed \
                 roster now covers every admitted participant, so finality does not fail closed \
                 on this restart"
            );
        }
    }

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
            refuse_to_start_without_consensus(&format!(
                "could not bind the gossip endpoint on {bind_addr_str}: {e}. Another process \
                 already holds that UDP port (a second dregg-node on the same box defaults to \
                 9420 too) — pass a free `--gossip-port` and restart."
            ));
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
            refuse_to_start_without_consensus(&format!("could not join the blocklace topic: {e}"));
        }
    };

    // Subscribe to the blocklace topic for incoming messages.
    let mut blocklace_stream = match gossip.subscribe(&topic).await {
        Ok(s) => s,
        Err(e) => {
            refuse_to_start_without_consensus(&format!(
                "could not subscribe to the blocklace topic: {e}"
            ));
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
    // supermajority of distinct members have SIGNED a vote for it — with BOTH
    // halves (ed25519 ∧ ML-DSA-65) verifying. The PQ committee is read from
    // state's genesis-published, index-aligned ML-DSA keys; our OWN entry is
    // the locally re-derived key (same seed), so solo/bootstrap still votes. A
    // participant with no known ML-DSA key simply cannot contribute to quorum
    // (fail-closed; never an ed25519-only downgrade).
    let mut pq_committee = pq_committee_for_participants(&state, &participants).await;
    pq_committee.insert(self_key, pq_public_key.clone());
    // HYBRID-PQ pinning (GAP #1b live-wiring): enroll every committee member's
    // ML-DSA-65 public key into the finality Blocklace's PQ roster, so the live
    // wire ingest (`catchup::apply_with_buffering` → `receive_block_pinned`) PINS
    // each incoming consensus block's post-quantum half to its creator's ENROLLED
    // key and FAILS CLOSED on an unenrolled/forged creator. This is the SAME
    // genesis-published + self-derived ML-DSA key set the finalization-vote path
    // uses; the `frost` and `blocklace` newtypes both wrap the raw
    // `ml_dsa_65::keygen_from_seed` bytes, so the key transfers directly. Enrolled
    // BEFORE the gossip receiver task is spawned, so no ingest runs unpinned.
    {
        let mut l = lace.write().await;
        for (creator, pq_pk) in &pq_committee {
            // The finality roster is keyed by the HYBRID id (== `Block::creator`):
            // `H(ed25519 ‖ ml_dsa)`. Compute it from the member's published
            // ed25519 + ML-DSA public keys — the same value `Block::new` stamps —
            // so `receive_block_pinned` finds the enrolled key for every honest
            // creator and the commitment gate binds them cryptographically.
            let ml_dsa = dregg_blocklace::pq::MlDsaPublicKey(pq_pk.0);
            let hybrid = dregg_blocklace::finality::Block::hybrid_id_from_parts(creator, &ml_dsa);
            l.enroll_pq(hybrid, ml_dsa);
        }
    }
    let votes = Arc::new(RwLock::new(crate::finalization_votes::VoteCollector::new(
        participants.iter().copied(),
        pq_committee,
        quorum_threshold,
    )));

    let handle = BlocklaceHandle {
        lace: lace.clone(),
        constitution: constitution_handle.clone(),
        gossip: gossip.clone(),
        topic: topic.clone(),
        self_key,
        signing_key: signing_key.clone(),
        pq_signing_key: pq_signing_key.clone(),
        votes: votes.clone(),
        my_pending_votes: Arc::new(RwLock::new(HashMap::new())),
        cursor,
        finality_notify: finality_notify.clone(),
        auto_approve_joins, // F-CRIT-2: gated by main.rs on --auto-approve-joins CLI flag OR .devnet marker
        pending_joins: Arc::new(RwLock::new(HashMap::new())),
        join_progress: Arc::new(RwLock::new(JoinProgress::default())),
        pq_public_key: pq_public_key.clone(),
        peer_addrs: peer_addrs.clone(),
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
        round_advance_timer: Arc::new(std::sync::Mutex::new(
            crate::round_advance_gate::RoundAdvanceTimer::default(),
        )),
        ack_pending: Arc::new(std::sync::atomic::AtomicBool::new(false)),
        pending_payloads: Arc::new(RwLock::new(std::collections::VecDeque::new())),
        last_order_fingerprint: Arc::new(RwLock::new(None)),
        last_lean_order: Arc::new(RwLock::new(None)),
        liveness: Arc::new(FederationLiveness::default()),
        in_flight_turns: Arc::new(InFlightTurns::default()),
    };

    info!("blocklace gossip layer initialized, processing messages");

    // ─── Spawn the Gossip Receiver Task ─────────────────────────────────────

    let handle_for_receiver = handle.clone();
    let state_for_receiver = state.clone();
    tokio::spawn(async move {
        loop {
            // ⚑ DRAIN-AND-SCHEDULE, NOT ONE-AT-A-TIME. See
            // `drain_and_schedule_blocklace_batch` for the measurement that forced
            // this: the old loop awaited `handle_blocklace_message` per message on a
            // SINGLE consumer of an UNBOUNDED channel, and at n=3 the arrival rate
            // exceeded the service rate — 338 messages delivered into the channel
            // against 160 ever pulled out in one 40 s run. The blocks the round
            // cohort needed were IN the queue and never reached `handle_push`.
            let first = match blocklace_stream.recv().await {
                Some(ev) => ev,
                None => {
                    warn!("blocklace gossip stream ended");
                    break;
                }
            };
            match first {
                GossipEvent::Message { .. } => {
                    let mut batch = vec![first];
                    // Take everything already queued behind it (bounded), so the
                    // scheduler below sees the whole backlog and can coalesce it.
                    while batch.len() < MAX_GOSSIP_DRAIN_BATCH {
                        match blocklace_stream.try_recv() {
                            Some(ev) => batch.push(ev),
                            None => break,
                        }
                    }
                    drain_and_schedule_blocklace_batch(
                        &handle_for_receiver,
                        &state_for_receiver,
                        batch,
                    )
                    .await;
                }
                GossipEvent::PeerJoined(addr) => {
                    info!(peer = %addr, "peer joined blocklace topic");
                    handle_for_receiver.send_frontier().await;
                    handle_for_receiver
                        .share_peer_addrs(&state_for_receiver)
                        .await;
                }
                GossipEvent::PeerLeft(addr) => {
                    info!(peer = %addr, "peer left blocklace topic");
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

    // ─── Spawn the Narrow-Join-Channel Receiver ─────────────────────────────
    //
    // THE COMMITTEE SIDE of the growth fix. Join requests arrive on their own
    // channel, NOT on a topic — an unregistered key has no topic and no
    // spanning-tree slot, which is precisely why the old design could not work.
    // Each request has already been proven self-certified by the gossip layer;
    // everything about MEANING (is this our federation, does the candidate hold
    // the PQ key it names, is it already a member, do we sponsor it) is decided
    // here, in the layer that knows what a committee is.
    if let Some(mut join_rx) = gossip.take_join_requests() {
        // TWO TASKS, AND THE SPLIT IS LOAD-BEARING. Validation is cheap,
        // fail-closed and must never be behind anything; authoring needs
        // `lace.write()` and a durable persist and can therefore be behind
        // EVERYTHING. Running both on the receiver meant one candidate's
        // sponsorship froze the committee's whole join-admission path — 513 s
        // measured, with an impostor's wrong-federation refusals sitting
        // unvalidated in the channel for 4 m 38 s of it. See
        // `BlocklaceHandle::handle_join_request`.
        let (sponsor_tx, mut sponsor_rx) =
            tokio::sync::mpsc::channel::<[u8; 32]>(SPONSOR_QUEUE_CAPACITY);
        let sp_handle = handle.clone();
        let sp_state = state.clone();
        tokio::spawn(async move {
            // Serial by construction: at most one Join proposal is authored at a
            // time, so sponsorship cannot itself become a source of lace-write
            // contention.
            while let Some(candidate) = sponsor_rx.recv().await {
                sp_handle.sponsor_pending_join(&sp_state, candidate).await;
            }
        });
        let jr_handle = handle.clone();
        let jr_state = state.clone();
        tokio::spawn(async move {
            while let Some(req) = join_rx.recv().await {
                jr_handle
                    .handle_join_request(
                        &jr_state,
                        req.from,
                        req.candidate_public_key.0,
                        &req.body,
                        &sponsor_tx,
                    )
                    .await;
            }
        });
    }

    match membership_proposal_policy {
        MembershipProposalPolicy::ProposeIfNonMember => {
            // THE CANDIDATE SIDE. Not a block — a narrow-channel request, retried
            // until a member sponsors it. See `run_join_requests_until_member`
            // for why authoring a block here could never have reached anyone.
            let join_handle = handle.clone();
            let join_state = state.clone();
            tokio::spawn(async move {
                // Brief delay to allow gossip connections to establish.
                tokio::time::sleep(Duration::from_secs(2)).await;
                join_handle
                    .run_join_requests_until_member(&join_state)
                    .await;
            });
        }
        MembershipProposalPolicy::FollowOnly => {
            info!("follow-only membership policy active — history sync will not ask to join");
        }
    }

    Some(handle)
}

// ─── Message Handling ───────────────────────────────────────────────────────

/// Upper bound on how many already-queued gossip events one scheduling pass takes
/// out of the funnel channel. Generous — the point is to see the whole backlog so it
/// can be coalesced, not to ration work — but bounded so a sustained burst cannot
/// keep the loop from ever returning to `recv().await`.
const MAX_GOSSIP_DRAIN_BATCH: usize = 512;

/// ⚑ THE ANTI-ENTROPY CHANNEL MUST NOT BE ABLE TO STARVE ITSELF.
///
/// The blocklace funnel is ONE task consuming ONE unbounded channel, and it `await`s
/// each message's handler in turn. `handle_frontier` is by far the most expensive
/// handler — it takes `lace.read()`, walks `causal_past_union` over the whole
/// history, builds a causally-closed delta, and then broadcasts that delta, which
/// takes the gossip layer's `state.write()` in contention with every inbound stream
/// handler. And Frontiers are the most FREQUENT message: every node emits one per
/// cadence tick to every peer, and each is re-forwarded.
///
/// Measured on hbox at n=3 (2026-07-30), one 40 s run, node-0: **338 messages
/// delivered into the funnel channel, 160 ever pulled out.** The arrival rate simply
/// exceeded the service rate, the unbounded channel absorbed the difference, and the
/// backlog grew monotonically. The round-5 cohort blocks were IN that queue — they
/// had been sent, accepted by the gossip layer, and handed to the subscriber — and
/// they never reached `handle_push`. With `supermajority_threshold(3) == 3` the
/// committee cannot advance a round until every creator's block for the current
/// round has landed, so a funnel that is permanently behind reads from the outside
/// as a permanent wedge: `dag_height` frozen at 5, `latest_height` 0, forever, with
/// no error anywhere. It is not a rule failure and not a transport failure; it is a
/// SCHEDULING failure inside the receiver.
///
/// The fix is scheduling, not rationing, and it rests on two facts about the
/// protocol:
///
///  * **A Frontier is a state ANNOUNCEMENT, not an event.** Its own wire doc says it
///    is "a catch-up PING, not content to deduplicate". Processing the newest
///    frontier from a peer subsumes every older one from that peer — the older one
///    describes a strictly earlier view of the same lace. So a backlog of frontiers
///    from one peer coalesces to its LAST element with **zero** information loss.
///  * **Blocks are what liveness depends on; frontiers only ask for them.** A
///    `Push`/`PullResponse` carries the round cohort. A `Pull` unblocks a peer's
///    cohort. A `FinalizationVote` carries quorum agreement. None of those are
///    reconstructible from a later message, so all of them are processed in arrival
///    order, ahead of any frontier.
///
/// So: take the whole queued backlog, run every block-, pull- and vote-bearing
/// message first in arrival order, then at most ONE frontier per peer. Under load
/// the expensive-and-redundant class collapses and the liveness-critical class
/// overtakes it; when there is no backlog this is exactly the old behaviour (a batch
/// of one).
///
/// This also cuts the OUTBOUND load, because each coalesced-away frontier would have
/// produced its own delta broadcast to every peer.
async fn drain_and_schedule_blocklace_batch(
    handle: &BlocklaceHandle,
    state: &NodeState,
    batch: Vec<GossipEvent>,
) {
    // Liveness-critical, arrival-ordered: blocks and pull requests.
    let mut urgent: Vec<(SocketAddr, BlocklaceGossipMessage)> = Vec::new();
    // Finalization votes, DEDUPED by (block_id, voter) within the batch and run
    // LAST. See the vote block below for the measurement.
    let mut votes: Vec<(SocketAddr, BlocklaceGossipMessage)> = Vec::new();
    let mut vote_keys: std::collections::HashSet<(BlockId, [u8; 32])> =
        std::collections::HashSet::new();
    let mut votes_deduped = 0usize;
    // At most one frontier per peer — the newest wins. `Vec` rather than a map so
    // the *relative* order of distinct peers stays the arrival order.
    let mut latest_frontier: Vec<(SocketAddr, BlocklaceGossipMessage)> = Vec::new();
    // Non-`PublishTurn` peer messages (the co-turn vocabulary) keep the old path.
    let mut passthrough: Vec<(SocketAddr, PeerMessage)> = Vec::new();

    let mut coalesced = 0usize;
    for event in batch {
        let GossipEvent::Message { from, message } = event else {
            // `PeerJoined`/`PeerLeft` cannot appear here: the caller only batches
            // `Message` events (it handles the others on the spot).
            continue;
        };
        let PeerMessage::PublishTurn { ref turn_data, .. } = message else {
            passthrough.push((from, message));
            continue;
        };
        let gossip_msg: BlocklaceGossipMessage = match postcard::from_bytes(turn_data) {
            Ok(m) => m,
            Err(e) => {
                debug!(from = %from, error = %e, "failed to decode blocklace gossip message");
                continue;
            }
        };
        if matches!(gossip_msg, BlocklaceGossipMessage::Frontier { .. }) {
            match latest_frontier.iter_mut().find(|(a, _)| *a == from) {
                Some(slot) => {
                    // A newer announcement from this peer supersedes the staged one.
                    // ⚠ The superseded frontier's piggybacked VOTES are not lost:
                    // `frontier_votes` re-attaches every vote still inside its
                    // re-emit budget to EVERY outgoing frontier, so the newest
                    // frontier from a peer carries a superset of the older one's
                    // votes. Coalescing therefore drops no vote that is still live.
                    slot.1 = gossip_msg;
                    coalesced += 1;
                }
                None => latest_frontier.push((from, gossip_msg)),
            }
        } else if let BlocklaceGossipMessage::FinalizationVote(ref v) = gossip_msg {
            // ⚑ THE MOST EXPENSIVE HANDLER ON THE FUNNEL, AND THE MOST REDUNDANT.
            // Verifying one vote is a HYBRID check — ed25519 AND ML-DSA-65 (FIPS
            // 204) over the same message — and it runs synchronously on this single
            // consumer. Measured on hbox at n=3 (2026-07-30): 1155-1910 ms PER VOTE,
            // 25 slow + 6 over the one-second stall threshold in a single 60 s run,
            // which is why `handle_blocklace_gossip` now times and names its
            // handlers. Every round-cohort block queued behind such a vote waited
            // that long, and at `supermajority_threshold(3) == 3` a late cohort is a
            // stalled committee.
            //
            // And the volume is almost entirely RE-EMITS: `reemit_pending_votes`
            // re-broadcasts every pending vote each cadence tick for
            // `VOTE_REEMIT_SWEEPS` (30) sweeps, AND `frontier_votes` piggybacks the
            // same set onto every outgoing frontier — each copy byte-unique via a
            // fresh transport `nonce` (deliberately, so the gossip `seen` cache
            // cannot collapse it). So the funnel sees the same (block, voter) vote
            // dozens of times and pays a full hybrid verify for every copy.
            //
            // Within one drained batch a repeat is worth NOTHING: the collector
            // counts DISTINCT signers per block, so the second copy of a
            // (block_id, voter) pair cannot change any tally. Dedupe on that key and
            // run the survivors LAST, behind every block. This drops no vote a
            // quorum needs — a vote from a different voter, or for a different block,
            // has a different key and is kept, and a genuinely new copy arriving in a
            // later batch is processed then. Nothing about VERIFICATION is relaxed:
            // every surviving vote goes through the identical hybrid check.
            if vote_keys.insert((v.block_id, v.voter)) {
                votes.push((from, gossip_msg));
            } else {
                votes_deduped += 1;
            }
        } else {
            urgent.push((from, gossip_msg));
        }
    }

    if coalesced > 0 || votes_deduped > 0 {
        debug!(
            urgent = urgent.len(),
            votes = votes.len(),
            frontiers = latest_frontier.len(),
            coalesced,
            votes_deduped,
            "blocklace funnel: backlog scheduled (blocks first, then votes, one frontier per peer)"
        );
    }

    // 1. Blocks and pull requests — arrival order, ahead of everything else. These
    //    carry the round cohort; nothing else can reconstruct them.
    for (from, msg) in urgent {
        handle_blocklace_gossip(handle, state, from, msg).await;
    }
    // 2. The co-turn vocabulary.
    for (from, message) in passthrough {
        handle_blocklace_message(handle, state, from, message).await;
    }
    // 3. One frontier per peer, newest.
    for (from, msg) in latest_frontier {
        handle_blocklace_gossip(handle, state, from, msg).await;
    }
    // 4. Votes last: a quorum that crosses one batch later still finalizes, but a
    //    cohort block that arrives one batch later stalls the round.
    for (from, msg) in votes {
        handle_blocklace_gossip(handle, state, from, msg).await;
    }
}

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

    handle_blocklace_gossip(handle, state, from, gossip_msg).await;
}

/// Dispatch one ALREADY-DECODED blocklace gossip message. Split out of
/// [`handle_blocklace_message`] so [`drain_and_schedule_blocklace_batch`] can inspect
/// the message class (frontier vs block-bearing) to schedule the backlog without
/// decoding twice.
async fn handle_blocklace_gossip(
    handle: &BlocklaceHandle,
    state: &NodeState,
    from: SocketAddr,
    gossip_msg: BlocklaceGossipMessage,
) {
    // ⚑ NAME THE HANDLER THAT STALLED THE FUNNEL. This is a SINGLE-CONSUMER queue:
    // one slow handler delays every message behind it, including the round-cohort
    // blocks that `supermajority_threshold(n) == n` makes liveness-critical. When
    // that happened there was nothing in the log to say WHICH handler, only a
    // committee that had stopped — so the stall is timed and named at source.
    let started = std::time::Instant::now();
    let kind = match &gossip_msg {
        BlocklaceGossipMessage::Push { blocks, .. } => format!("Push[{}]", blocks.len()),
        BlocklaceGossipMessage::Pull { ids, .. } => format!("Pull[{}]", ids.len()),
        BlocklaceGossipMessage::PullResponse { blocks, .. } => {
            format!("PullResponse[{}]", blocks.len())
        }
        BlocklaceGossipMessage::Frontier { tips, votes, .. } => {
            format!("Frontier[tips={} votes={}]", tips.len(), votes.len())
        }
        BlocklaceGossipMessage::CheckpointAvailable { .. } => "CheckpointAvailable".to_string(),
        BlocklaceGossipMessage::PeerAddrs(a) => format!("PeerAddrs[{}]", a.len()),
        BlocklaceGossipMessage::FinalizationVote(_) => "FinalizationVote".to_string(),
    };
    handle_blocklace_gossip_inner(handle, state, from, gossip_msg).await;
    let took = started.elapsed();
    if took >= FUNNEL_STALL_WARN {
        warn!(
            from = %from, kind = %kind, ms = took.as_millis() as u64,
            "blocklace funnel: handler STALLED the single-consumer queue — every message \
             behind it, including round-cohort blocks, waited this long"
        );
    } else if took >= FUNNEL_SLOW_DEBUG {
        debug!(from = %from, kind = %kind, ms = took.as_millis() as u64, "blocklace funnel: slow handler");
    }
}

/// How long one funnel handler may take before it is merely noted…
const FUNNEL_SLOW_DEBUG: Duration = Duration::from_millis(250);
/// …and before it is a warning. At a 1 s block cadence, a handler holding the
/// single-consumer funnel for a full second is already delaying the next round.
const FUNNEL_STALL_WARN: Duration = Duration::from_millis(1_000);

async fn handle_blocklace_gossip_inner(
    handle: &BlocklaceHandle,
    state: &NodeState,
    from: SocketAddr,
    gossip_msg: BlocklaceGossipMessage,
) {
    match gossip_msg {
        BlocklaceGossipMessage::Push { blocks, .. } => {
            handle_push(handle, state, from, blocks).await;
        }
        BlocklaceGossipMessage::Pull {
            ids: missing_ids, ..
        } => {
            handle_pull(handle, from, missing_ids).await;
        }
        BlocklaceGossipMessage::PullResponse { blocks, .. } => {
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
    // The SAME freshness fact, kept where `/status` can read it back. The
    // Prometheus gauge above is for a dashboard; the node itself had no in-process
    // notion of which members were still reaching it, which is why it kept
    // answering `healthy: true` while two of four peers were frozen. Recorded only
    // for outcomes the collector ADMITTED — a vote it rejected as unsigned or
    // non-member is not evidence that its claimed signer is alive.
    if !matches!(outcome, RecordOutcome::Rejected) {
        handle.liveness.note_vote(&vote.voter);
    }
    match outcome {
        RecordOutcome::ReachedQuorum { distinct_votes } => {
            handle.liveness.note_quorum();
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

    // EXCLUSION IS A PREDICATE OVER COMMITTED STRUCTURE, NEVER A LIVE MUTATION
    // (flag day 2026-08-08, exclusion-by-past). This path used to call
    // `constitution.auto_evict(proof)` here — retaining a participant out of the
    // τ set and recomputing the threshold ON GOSSIP ARRIVAL. That made the
    // participant set a function of local arrival order (the exact F-CO-1 fork
    // the projection docblock forbids: a node holding both fork halves ran at
    // n−1 while a peer holding one ran at n ⇒ different `wave_leader` for the
    // same wave, silently), and it reverted on restart (never a block, absent
    // from `committee_replay`'s fold). Both source papers keep Π fixed:
    // exclusion is `node(b) ∉ byz(⌊b⌋)` — evaluated per anchor closure inside τ
    // (`ordering.rs::approves` / Lean `hasEquivInPast`; spec + poles:
    // `Dregg2.Distributed.ExclusionByPast`). What makes that predicate REACHABLE
    // is the ingest itself: `insert_checked` pins the detected incomparable pair
    // as the creator's `CreatorTips::Pair`, and the next block we author points
    // at both halves (the CM Alg. 1:5 two-tips evidence floor), so the fork
    // enters every later closure. Detection here therefore DECIDES WHETHER we
    // log/slash — never WHAT any consensus verdict is.
    if !outcome.equivocations.is_empty() {
        for proof in &outcome.equivocations {
            let creator_hex: String = proof.creator[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            warn!(
                from = %from,
                creator = %creator_hex,
                "equivocation detected from peer — evidence pair pinned into tips; \
                 membership and threshold UNCHANGED (exclusion is per-closure in tau)"
            );
        }

        // NO RELAY PENALTY. The old `penalize_equivocation_relay(from)` graylisted
        // the relaying peer out of EVERY topic's eager set — on the one message
        // class the harm bound runs on. Under the blocklace paper (Prop. 5.5 /
        // Lemma A.1) forwarding fork evidence is CORRECT behaviour by a correct
        // node, and the connected-correct-graph hypothesis both propositions
        // stand on is exactly what the penalty eroded: one fork block, broadcast
        // once, demoted the mesh position of every honest node that forwarded it
        // — a cheap, one-sided DoS amplifier against our own dissemination.

        // ADJUDICATION WELD (ORGANS §5 / CONSENSUS-FLEX §7): propagated fork
        // evidence reaches the SLASH path (the one mechanism here that is
        // legitimately beyond the papers). Each retained proof is reduced to the
        // self-contained wire value (`EvidenceOfEquivocation`); if the
        // equivocator posted a bond on this node, the exhibit slashes it as one
        // conserved executor move from the bonded cell — no operator in the
        // loop, no-double-resolve via the burned evidence digest. Unbonded /
        // already-resolved / different-seq proofs are logged no-ops.
        for proof in &outcome.equivocations {
            crate::equivocation_court_service::slash_from_proof(state, proof).await;
        }
    }

    // A DETERMINISTIC INGEST REFUSAL IS A LIVENESS EVENT, NOT A FOOTNOTE. At
    // `supermajority_threshold(n) == n` (every n ≤ 3) the round cohort cannot
    // complete without this block, and the refusal path deliberately neither
    // buffers nor re-pulls it — so one refused block halts the committee for good.
    // `error!`, and it names the reason: the arm this reads from was a silent `{}`
    // until 2026-07-30, which made "we refused it" indistinguishable from "the wire
    // lost it" for the whole n=3 wedge investigation.
    if !outcome.refused.is_empty() {
        let reasons: Vec<String> = outcome
            .refused
            .iter()
            .map(|(id, why)| {
                format!(
                    "{}: {why}",
                    id.0[..4]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect::<String>()
                )
            })
            .collect();
        error!(
            from = %from,
            refused = outcome.refused.len(),
            total_received = block_count,
            reasons = ?reasons,
            "peer consensus blocks REFUSED on ingest and dropped permanently — at \
             supermajority == n this stalls round advancement until the creator re-authors"
        );
    }

    let inserted = outcome.inserted.len();

    // REACTIVE ATTESTATION: a peer's freshly-inserted non-Ack block (turn /
    // membership / checkpoint) is a mutation that wants our acknowledgment —
    // flag the cadence task to answer with one `Payload::Ack` block on its next
    // check tick. Acking only NON-Ack foreign blocks terminates the exchange
    // (acks do not beget acks), so n nodes acking one turn produce exactly the
    // n attestation blocks the 2f+1 quorum needs, not a storm.
    // `b.ed25519`, not `b.creator`: `self_key` is this node's ed25519 verify key
    // (`run_blocklace_sync_with_policy` derives it as `signing_key.verifying_key()`),
    // while `Block::creator` is the HYBRID id — so the old comparison could never be
    // false and "foreign" degenerated to "any non-Ack block", including our own
    // echoed back by a peer.
    if outcome
        .inserted
        .iter()
        .any(|b| b.ed25519 != handle.self_key && b.payload != Payload::Ack)
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
    // catch-up roots FROM THE PEER THAT REVEALED THE GAP. Targeting is sound by
    // the closure property (`insert_checked`: a lace holds a block only with
    // its whole causal past): an honest peer that pushed us a block holds every
    // predecessor that block cites, transitively — so `from` is a guaranteed
    // holder of exactly the roots we are missing. This replaces the old
    // topic-wide broadcast Pull, which asked every peer and had every holder
    // answer (the O(n²) reply amplification `send_gossip_direct` documents).
    // If `from` is Byzantine/withholding or the reply is lost, the per-root
    // backoff expires and `catchup_tick` retries against a ROTATING peer —
    // Mysticeti's likely-holder-first-then-rotate shape.
    //
    // OFF THE FUNNEL (see `spawn_gossip_send`): this send used to run inline on
    // the single serial inbound consumer — the one of the four handler-ending
    // sends that was left behind when the other three were spawned off. It is
    // idempotent anti-entropy with its own nonce like the rest; nothing orders
    // it against the funnel.
    if !outcome.pull_roots.is_empty() {
        let pull_msg = BlocklaceGossipMessage::Pull {
            ids: outcome.pull_roots,
            nonce: gossip_send_nonce(),
        };
        if sync_baseline() {
            // ⚠ TEMPORARY MEASUREMENT SCAFFOLD (see SYNC_BASELINE_FOR_MEASUREMENT).
            handle.broadcast_gossip_message(&pull_msg).await;
        } else {
            let sender = handle.clone();
            spawn_gossip_send(async move {
                sender.send_gossip_direct(from, &pull_msg).await;
            });
        }
    }
}

/// ⚠ TEMPORARY MEASUREMENT SCAFFOLD — MUST BE DELETED BEFORE COMMIT (grep
/// `SYNC_BASELINE`). When set (only ever by the loss-injection measurement
/// harness, and only in test builds), the sync paths revert to the pre-fix
/// behavior — topic-broadcast Pull/PullResponse/delta-Push and full-causal-past
/// pull replies — so the SAME binary can measure before/after without a stash,
/// a clone, or a second build. `#[cfg(test)]`: the old shape does not exist in
/// a production binary at all.
#[cfg(test)]
pub(crate) static SYNC_BASELINE_FOR_MEASUREMENT: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

#[inline]
fn sync_baseline() -> bool {
    #[cfg(test)]
    {
        SYNC_BASELINE_FOR_MEASUREMENT.load(std::sync::atomic::Ordering::Relaxed)
    }
    #[cfg(not(test))]
    {
        false
    }
}

/// Hard cap on blocks in one Pull response (requested blocks + their nearby
/// ancestry). Two `MAX_BLOCKS_PER_PUSH` chunks: enough to close a typical
/// loss-induced gap (a few rounds × committee width) in ONE round trip, small
/// enough that no reply is ever a history dump.
///
/// ⚑ WHY BOUNDED AT ALL — the old reply was `causal_past(id)`, i.e. EVERYTHING
/// from genesis below each requested block, chunked but unbounded, and the lace
/// never prunes. Under loss, every re-pull of one lost tip therefore shipped
/// the entire DAG again. The papers' shape (Mysticeti's synchronizer) is the
/// opposite: a fetch returns the requested blocks; ancestry still missing after
/// they land is discovered by the receiver's own gap tracking (our
/// `OrphanBuffer::unmet_roots`) and fetched in the NEXT targeted request —
/// iterative deepening, one bounded window per round trip. We keep a window
/// above the bare requested set so the common shallow gap closes in one RTT.
/// DEEP catch-up (a fresh joiner) is not this path's job and does not regress:
/// `handle_frontier` computes the full tip-delta for that peer and pushes it
/// chunked (now point-to-point), which is where from-genesis transfer belongs.
const MAX_PULL_RESPONSE_BLOCKS: usize = 2 * MAX_BLOCKS_PER_PUSH;

/// Collect the reply for a Pull: each requested block plus nearby ancestry,
/// nearest-first (BFS through predecessors from the requested ids), capped at
/// [`MAX_PULL_RESPONSE_BLOCKS`], in causal-friendly order (ascending per-creator
/// `seq`; the receiver's orphan buffer absorbs any cross-creator reordering).
///
/// Pure so the bound and ordering are unit-testable without a transport.
fn collect_pull_response(
    lace: &dregg_blocklace::finality::Blocklace,
    requested: &[BlockId],
) -> Vec<Block> {
    let mut collected: Vec<Block> = Vec::new();
    let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut frontier: std::collections::VecDeque<BlockId> = requested.iter().copied().collect();
    while let Some(id) = frontier.pop_front() {
        if collected.len() >= MAX_PULL_RESPONSE_BLOCKS {
            break;
        }
        if !visited.insert(id) {
            continue;
        }
        let Some(block) = lace.get(&id) else {
            // We do not hold this id (never had it, or it is beyond our own
            // view) — skip. The requester's rotating retry asks someone else.
            continue;
        };
        collected.push(block.clone());
        for pred in &block.predecessors {
            if !visited.contains(pred) {
                frontier.push_back(*pred);
            }
        }
    }
    collected.sort_by(|a, b| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));
    collected
}

/// Handle a Pull request: reply to the REQUESTER with the requested blocks plus
/// a bounded ancestry window ([`collect_pull_response`]).
///
/// Two 2026-08-08 changes, both fan-out (the message's existence and the
/// closure discipline are untouched):
/// * **Bounded reply, not `causal_past`.** See [`MAX_PULL_RESPONSE_BLOCKS`] for
///   the unit and the paper it follows. Deeper gaps converge by iterative
///   windows (the requester's orphan roots drive the next targeted pull);
///   from-genesis transfer is `handle_frontier`'s tip-delta push.
/// * **Point-to-point, not broadcast.** The reply goes to `from` — the one
///   peer that asked — via [`BlocklaceHandle::send_gossip_direct`], instead of
///   `publish_eager`ing every chunk to the whole committee.
async fn handle_pull(handle: &BlocklaceHandle, from: SocketAddr, missing_ids: Vec<BlockId>) {
    if missing_ids.is_empty() {
        return;
    }
    debug!(from = %from, requested = missing_ids.len(), "handling pull request");

    let to_send = {
        let lace = handle.lace.read().await;
        if sync_baseline() {
            // ⚠ TEMPORARY MEASUREMENT SCAFFOLD: the pre-fix reply — the FULL
            // causal past of every requested id, from genesis, unbounded.
            #[cfg(test)]
            {
                collect_pull_response_baseline_full_past(&lace, &missing_ids)
            }
            #[cfg(not(test))]
            {
                unreachable!("sync_baseline() is constant false outside test builds")
            }
        } else {
            collect_pull_response(&lace, &missing_ids)
        }
    };

    if to_send.is_empty() {
        return;
    }

    let total = to_send.len();

    // OFF THE FUNNEL (see `spawn_gossip_send`): answering a pull is an OUTBOUND
    // act, and the chunked form even sleeps between chunks. Neither belongs on
    // the single serial inbound consumer.
    let sender = handle.clone();
    spawn_gossip_send(async move {
        let baseline = sync_baseline();
        if total <= MAX_BLOCKS_PER_PUSH {
            let response = BlocklaceGossipMessage::PullResponse {
                blocks: to_send,
                nonce: gossip_send_nonce(),
            };
            if baseline {
                sender.broadcast_gossip_message(&response).await;
            } else {
                sender.send_gossip_direct(from, &response).await;
            }
            debug!(to = %from, blocks = total, "sent pull response");
            return;
        }
        debug!(to = %from, blocks = total, "sending chunked pull response");
        let mut sent_so_far = 0usize;
        for chunk in to_send.chunks(MAX_BLOCKS_PER_PUSH) {
            let response = BlocklaceGossipMessage::PullResponse {
                blocks: chunk.to_vec(),
                nonce: gossip_send_nonce(),
            };
            if baseline {
                sender.broadcast_gossip_message(&response).await;
            } else {
                sender.send_gossip_direct(from, &response).await;
            }
            sent_so_far += chunk.len();

            if sent_so_far < total {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
        debug!(to = %from, blocks = total, "completed chunked pull response");
    });
}

/// ⚠ TEMPORARY MEASUREMENT SCAFFOLD — the pre-2026-08-08 `handle_pull` reply
/// (verbatim semantics): every requested block plus its ENTIRE causal past.
/// Exists only so the measurement harness can run the baseline from the same
/// binary; deleted with `SYNC_BASELINE_FOR_MEASUREMENT`.
#[cfg(test)]
fn collect_pull_response_baseline_full_past(
    lace: &dregg_blocklace::finality::Blocklace,
    missing_ids: &[BlockId],
) -> Vec<Block> {
    let mut to_send: Vec<Block> = Vec::new();
    let mut sent_ids = std::collections::HashSet::new();
    for block_id in missing_ids {
        let past = lace.causal_past(block_id);
        for past_id in &past {
            if !sent_ids.contains(past_id)
                && let Some(block) = lace.get(past_id)
            {
                to_send.push(block.clone());
                sent_ids.insert(*past_id);
            }
        }
        if !sent_ids.contains(block_id)
            && let Some(block) = lace.get(block_id)
        {
            to_send.push(block.clone());
            sent_ids.insert(*block_id);
        }
    }
    to_send
}

/// Run one OUTBOUND gossip send off the inbound funnel task.
///
/// ⚑ WHY. The blocklace funnel is ONE task that `await`s each inbound handler in
/// turn, and three of those handlers finish by BROADCASTING — the frontier delta,
/// the self-healing pull, and the pull response. A broadcast is not cheap: it
/// takes the gossip layer's `state.write()` (contended by every inbound stream
/// handler) and then writes a QUIC frame per live connection, and the chunked
/// forms additionally SLEEP between chunks. Awaiting that on the funnel makes the
/// receive path's service rate a function of the SEND path's latency.
///
/// Measured on hbox at n=4, 2026-07-30, node-0 over one ~150 s run: `Frontier`
/// handling averaged **2372 ms** (max 9254 ms) across 31 logged-slow handlers,
/// **73.6 s of the run** on the one consumer — against 3 peers each announcing a
/// frontier every cadence tick. Every round-cohort block queued behind that
/// waited, so inter-round latency degraded 13 s → 20 s → 33 s → 60 s and a client
/// turn needing several rounds to close its wave never finalized inside 90 s.
///
/// Ordering is not load-bearing for any of the three: they are idempotent
/// anti-entropy, each send carries its own [`gossip_send_nonce`], and the
/// receiver dedups blocks by id. So the funnel computes the payload under a read
/// lock (cheap) and hands the send away.
fn spawn_gossip_send<F>(fut: F)
where
    F: std::future::Future<Output = ()> + Send + 'static,
{
    tokio::spawn(fut);
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
    their_tips: HashMap<[u8; 32], CreatorTips>,
) {
    // Flatten to the announced tip-id set (≤ 2 per creator by type): every use
    // below treats the frontier as "which blocks does the peer hold as maximal",
    // and a pinned equivocation pair announces both halves — so fork evidence
    // rides the SAME anti-entropy path as any other block.
    let their_tips: Vec<BlockId> = their_tips.values().flat_map(CreatorTips::iter).collect();
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
    // a Pull response carries the tip plus a bounded ancestry window
    // (`collect_pull_response`), which covers the wedge's whole gap in one round
    // trip — the wedge shape is by construction at most a round or two of
    // missing cohort blocks, far inside `MAX_PULL_RESPONSE_BLOCKS`; a deeper gap
    // iterates via the orphan roots. Backoff-gated (shared with the catch-up
    // pull limiter), so a tip we already requested is not re-hammered and steady
    // state — every announced tip known — stays quiet.
    let (tips_to_pull, held): (Vec<BlockId>, Vec<(u64, u64)>) = {
        let lace = handle.lace.read().await;
        let to_pull = their_tips
            .iter()
            .filter(|tip_id| !lace.contains(tip_id))
            .copied()
            .collect();
        let mut held: Vec<(u64, u64)> = their_tips
            .iter()
            .filter_map(|t| lace.get(t).map(|b| (b.seq, lace.round_of(t).unwrap_or(0))))
            .collect();
        held.sort_unstable();
        (to_pull, held)
    };
    // ANTI-ENTROPY TRACE. `announced` vs `lacking` separates "the peer told us
    // about a tip we do not hold" from "we already hold everything it announced"
    // — the two are indistinguishable from the outside and the second one looks
    // exactly like a healthy cluster while the committee is wedged.
    debug!(
        from = %from,
        announced = their_tips.len(),
        lacking = tips_to_pull.len(),
        ?held,
        "frontier: reconciling announced tips"
    );
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
            // TARGETED (2026-08-08): the ANNOUNCER is a guaranteed holder of
            // its own announced tips (a lace contains only closed blocks), so
            // the pull goes to `from` alone rather than the whole topic. A
            // lost reply retries via `catchup_tick`'s rotating pull once the
            // tip surfaces as an orphan root — or simply via the peer's next
            // per-tick Frontier re-announcement.
            // OFF THE FUNNEL (see `spawn_gossip_send`).
            let sender = handle.clone();
            spawn_gossip_send(async move {
                let msg = BlocklaceGossipMessage::Pull {
                    ids: due,
                    nonce: gossip_send_nonce(),
                };
                if sync_baseline() {
                    // ⚠ TEMPORARY MEASUREMENT SCAFFOLD.
                    sender.broadcast_gossip_message(&msg).await;
                } else {
                    sender.send_gossip_direct(from, &msg).await;
                }
            });
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
            .iter()
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

    // OFF THE FUNNEL (see `spawn_gossip_send`). THIS is the send that made the
    // receive path's service rate a function of the send path's latency: it runs
    // once per inbound frontier, i.e. `peers x cadence-ticks` times a second, and
    // it was measured at 2.4 s average on the one serial consumer.
    // TARGETED (2026-08-08): the delta below is computed FOR `from` (it is
    // "what THAT peer's announced tips say it lacks"), so it is sent to `from`
    // alone. Broadcasting it meant every member that received the same
    // Frontier pushed the same delta to every peer — the O(n²) shape
    // `send_gossip_direct` documents, here on the largest payload class
    // (deep-catch-up deltas). Any OTHER peer that lacks these blocks announces
    // its own frontier on its own tick and gets its own delta.
    let sender = handle.clone();
    spawn_gossip_send(async move {
        // If the delta fits in one message, send it directly (common case for
        // incremental updates after initial sync).
        if total_missing <= MAX_BLOCKS_PER_PUSH {
            let msg = BlocklaceGossipMessage::Push {
                blocks: to_send,
                nonce: gossip_send_nonce(),
            };
            if sync_baseline() {
                // ⚠ TEMPORARY MEASUREMENT SCAFFOLD.
                sender.broadcast_gossip_message(&msg).await;
            } else {
                sender.send_gossip_direct(from, &msg).await;
            }
            debug!(to = %from, blocks = total_missing, "pushed delta after frontier exchange");
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
            let msg = BlocklaceGossipMessage::Push {
                blocks: chunk.to_vec(),
                nonce: gossip_send_nonce(),
            };
            if sync_baseline() {
                // ⚠ TEMPORARY MEASUREMENT SCAFFOLD.
                sender.broadcast_gossip_message(&msg).await;
            } else {
                sender.send_gossip_direct(from, &msg).await;
            }

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
    });
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
    ///
    /// The two counts are carried so a stalled producer can SAY WHY. "Round could
    /// not advance" without `my_max_round` and `cohort_creators` is unactionable:
    /// it cannot distinguish a peer that has not caught up (creators short, DAG
    /// still moving) from a local creator that has run AHEAD of the cohort it
    /// needs (the wedge this whole path can enter and never leave).
    Wait {
        my_max_round: u64,
        cohort_creators: usize,
        /// Every committee creator's own max round in THIS lace, ascending. The
        /// wedge is visible only here: if the local creator sits strictly above
        /// the `supermajority`-th highest entry, no honest peer will ever join
        /// its round and the wait is permanent, not transient.
        creator_max_rounds: Vec<u64>,
    },
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
    // Round of every block in the lace (DAG depth; genesis = 1), and each
    // creator's own high-water round (the wedge diagnostic — see `Wait`).
    let mut round_of: HashMap<BlockId, u64> = HashMap::new();
    let mut creator_max: HashMap<[u8; 32], u64> = HashMap::new();
    let mut my_max_round: u64 = 0;
    for (id, block) in lace.iter() {
        let r = lace.round_of(id).unwrap_or(0);
        round_of.insert(*id, r);
        let entry = creator_max.entry(block.creator).or_insert(0);
        *entry = (*entry).max(r);
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
        // EVIDENCE FLOOR (CM Alg. 1:5, the two-tips rule in the direction that
        // matters): also link BOTH halves of every pinned equivocating pair, so
        // the fork enters this block's causal closure and the anchor-relative
        // exclusion predicate (`approves` / Lean `hasEquivInPast`,
        // `Dregg2.Distributed.ExclusionByPast`) can actually see it on the
        // round-driven path — the dominant producer at n>1, which links round
        // cohorts, not tips, and would otherwise never carry the pair. Only
        // halves at rounds ≤ our cohort round are linked (a deeper half would
        // inflate our next round; it is linked once our round catches up —
        // until then the pin persists, bounded at 2 pointers per flagged
        // creator). Authoring with both halves as predecessors clears the pin
        // (`try_add_block_with_predecessors`' evidence weld), so the pair is
        // carried once and then rides our own chain transitively.
        for (_creator, a, b) in lace.pinned_evidence_pairs() {
            for half in [a, b] {
                let hr = round_of.get(&half).copied().unwrap_or(0);
                if hr <= my_max_round && !cohort_blocks.contains(&half) {
                    cohort_blocks.push(half);
                }
            }
        }
        // Deterministic predecessor order (independent of HashMap iteration).
        cohort_blocks.sort_unstable_by_key(|a| a.0);
        RoundPlan::Advance {
            predecessors: cohort_blocks,
            next_round: my_max_round + 1,
        }
    } else {
        let mut creator_max_rounds: Vec<u64> = creator_max.into_values().collect();
        creator_max_rounds.sort_unstable();
        RoundPlan::Wait {
            my_max_round,
            cohort_creators: cohort_creators.len(),
            creator_max_rounds,
        }
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
    lace_is_empty: bool,
) -> CadenceAction {
    if queued_turns > 0 {
        CadenceAction::DrainTurns
    } else if ack_pending {
        CadenceAction::ReactiveAck
    } else if idle_heartbeat_ms > 0
        && (lace_is_empty || idle_for >= Duration::from_millis(idle_heartbeat_ms))
    {
        // BOOT ANCHOR (`lace_is_empty`): a node that has never produced a block
        // has an EMPTY DAG — nothing for a peer to sync to, no finality anchor,
        // and `/status.healthy` (which requires `block_count > 0`) false. The
        // idle timer starts at boot, so with the default 120s window a correct,
        // freshly started node reported UNHEALTHY for two minutes and served an
        // empty `/api/blocks` the whole time. "No block yet" is precisely the
        // condition the idle heartbeat exists for, so do not wait out a window
        // to establish the first one.
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
    let tip_round = lace.tip_ids().iter().filter_map(|t| lace.round_of(t)).max();
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

    // SUBMISSION-PATH TRACE (the drain half). Logged only while a turn is
    // actually staged, so a quiescent committee stays silent: this is the line
    // that distinguishes "enqueued and never drained" from "drained and never
    // planned into a block", which is exactly the pair E1 could only tell apart
    // by instrumenting a lane copy.
    if queued_turns > 0 {
        debug!(
            queued_turns,
            ack_pending,
            wave_is_open,
            exec_pending,
            since_last_block_ms = since_last_block.as_millis() as u64,
            min_block_interval_ms,
            ?action,
            "cadence tick with a STAGED turn"
        );
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
    let (staged, carried_turn) = if action == CadenceAction::DrainTurns {
        match handle.pending_payloads.write().await.pop_front() {
            Some(p) => (p, true),
            // Raced empty (a concurrent drain): fall back to an attestation so
            // the wake/close still advances the round.
            None => (PendingBlocklacePayload::ordinary(Payload::Ack), false),
        }
    } else {
        (PendingBlocklacePayload::ordinary(Payload::Ack), false)
    };

    let advanced = match staged.private_reservation_id {
        Some(reservation_id) => match handle
            .produce_private_dependent_round_block(state, staged.payload.clone(), reservation_id)
            .await
        {
            Ok(block_id) => block_id,
            Err(error) => {
                error!(
                    %error,
                    reservation_id = %dregg_types::hex_encode(&reservation_id),
                    "private dependent round production refused before live-lace publication"
                );
                None
            }
        },
        None => {
            handle
                .produce_round_block(state, staged.payload.clone())
                .await
        }
    };
    match advanced {
        Some(block_id) => {
            if carried_turn {
                info!(
                    block_id = %block_id,
                    "round block carried a STAGED turn payload into the DAG"
                );
            }
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
                debug!(
                    "round could not advance (no supermajority at our current round) — \
                     staged turn RE-STAGED for the next produced round block"
                );
                handle.pending_payloads.write().await.push_front(staged);
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
    let lace_is_empty = handle.block_count().await == 0;

    match cadence_decision(
        queued.len(),
        ack_pending,
        idle_for,
        idle_heartbeat_ms,
        lace_is_empty,
    ) {
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
            let finalized_blocks = handle.poll_finalized_blocks(&state).await;

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

            let mut acknowledged_blocks = Vec::new();
            let mut retry_prefix = false;
            for block in &finalized_blocks {
                let block_id = block.block_id();
                let outcome = match block {
                    FinalizedBlock::Turn {
                        block_id,
                        data,
                        artifacts,
                        consensus_time,
                    } => {
                        // Diagnostic compatibility coordinate only. Recovery is
                        // by terminal identity, never this count.
                        let block_executed_up_to =
                            handle.cursor.read().await.executed_count() as u64 + 1;
                        Some(
                            execute_finalized_turn(
                                &state,
                                &handle,
                                *block_id,
                                data,
                                artifacts.as_ref(),
                                *consensus_time,
                                block_executed_up_to,
                            )
                            .await,
                        )
                    }
                    FinalizedBlock::Membership {
                        block_id,
                        creator_ed25519,
                        action,
                    } => {
                        execute_finalized_membership(
                            &state,
                            &handle,
                            *block_id,
                            *creator_ed25519,
                            action,
                        )
                        .await;
                        None
                    }
                    FinalizedBlock::Checkpoint {
                        block_id,
                        root,
                        height,
                    } => {
                        // NOT stored: `PersistentStore::store_checkpoint` has zero
                        // callers repo-wide, nothing ever constructs a
                        // `Payload::Checkpoint` to propose, and `finalize_checkpoint`
                        // is only reached from tests. So `/checkpoint/latest`
                        // (`store.latest_checkpoint()`) 404s forever and every
                        // finality gate built on it is inert. The old message claimed
                        // "(stored)" — it stored nothing. See
                        // docs/FINDING-checkpoint-pipeline-unwired.md.
                        debug!(
                            block_id = %block_id,
                            height = height,
                            "finalized checkpoint block observed (NOT stored — checkpoint pipeline is unwired)"
                        );
                        let _ = (root, height);
                        None
                    }
                    FinalizedBlock::Inert { .. } => None,
                };

                // v4 THE PER-TURN VALUE THE VOTE WILL BIND. Taken from the
                // outcome of THIS block's commit — the same `receipt_stream_root`
                // the attested root published — never re-derived from the store.
                // A block that committed no turn (membership / checkpoint /
                // inert / deterministically rejected) has none, and every honest
                // member derives that same `None`.
                let block_receipt_stream_root = match outcome.as_ref() {
                    Some(FinalizedExecutionOutcome::Committed {
                        receipt_stream_root,
                        ..
                    }) => *receipt_stream_root,
                    _ => None,
                };

                if let Some(outcome) = outcome.as_ref() {
                    match outcome {
                        FinalizedExecutionOutcome::Committed { .. }
                        | FinalizedExecutionOutcome::DeterministicallyRejected { .. } => {
                            // A TERMINAL verdict exists in a durable store now,
                            // so the turn is no longer "in flight" — the verdict
                            // route answers from the commit log or the rejection
                            // row from here on. Retiring it here (rather than only
                            // when someone happens to ask) is what keeps
                            // `/status`'s `turns_in_flight` a real backlog gauge
                            // instead of a monotone count of submissions.
                            if let FinalizedBlock::Turn { data, .. } = block
                                && let Some(turn_hash) = signed_turn_hash_from_bytes(data)
                            {
                                handle.in_flight_turns.resolve(&turn_hash);
                            }
                            let advanced =
                                handle.cursor.write().await.acknowledge_terminal(outcome);
                            debug_assert!(
                                advanced || handle.cursor.read().await.is_executed(&block_id)
                            );
                        }
                        FinalizedExecutionOutcome::RetryableOperational { error, .. } => {
                            warn!(block_id = %block_id, error, "finalized execution hit a retryable operational failure; stopping tau prefix before successor");
                            retry_prefix = true;
                            break;
                        }
                        FinalizedExecutionOutcome::FatalIntegrity { error, .. } => {
                            error!(block_id = %block_id, error, "finalized execution hit a fatal integrity failure; stopping tau prefix without acknowledgement");
                            // Earlier terminal identities in this batch are
                            // already durable authority. Persist their cursor
                            // projection before permanently stopping this task;
                            // otherwise an inert/membership prefix could be
                            // needlessly replayed after the operator restarts.
                            if !acknowledged_blocks.is_empty() {
                                persist_blocklace_state(&state, &handle).await;
                            }
                            error!(
                                block_id = %block_id,
                                "finality executor permanently stopped after fatal integrity failure"
                            );
                            return;
                        }
                    }
                } else {
                    // Membership/checkpoint/data remain consensus-inert or
                    // idempotent in this turn-focused cut. They do not authorize
                    // an actionable turn ACK.
                    handle.cursor.write().await.mark_executed(block_id);
                }
                acknowledged_blocks.push(block.clone());

                // ── QUORUM AGREEMENT: emit our signed finalization vote ──────
                // This block is now in our local `tau` order (Ordered, which
                // subsumes Attested). Broadcast a signed vote so the committee
                // can collect 2f+1 distinct signers and declare it
                // consensus-wide Attested. Gate on "have we voted yet" so we
                // emit exactly once per block (n members ⇒ n votes, no storm).
                // Solo (n=1) is a committee of one: quorum=1, so a single self
                // vote is already consensus-attested — correct and inert.
                {
                    let already = {
                        let col = handle.votes.read().await;
                        col.has_voted(&block_id, &handle.self_key)
                    };
                    if !already {
                        // Bind the vote to the finalized committed state root, so
                        // this vote's signature IS a persisted `finalization_quorum`
                        // signature (N3 committee-restart fix). For a Turn block that
                        // is the post-execution `canonical_ledger_root` (execution of
                        // this block completed above); non-Turn blocks (membership /
                        // checkpoint) anchor no persisted attested root, so their
                        // vote binds the current canonical root harmlessly.
                        //
                        // v4: the vote ALSO binds this block's
                        // `receipt_stream_root` — the per-turn value. That is what
                        // makes the >=threshold quorum a committee statement about
                        // the TURN and not merely about a whole-ledger digest, and
                        // it is what `TurnAnchorV1::verify` refused for lack of on
                        // every federation with threshold > 1.
                        let merkle_root = {
                            let s = state.read().await;
                            canonical_ledger_root(&s.ledger)
                        };
                        handle
                            .emit_finalization_vote(
                                block_id,
                                dregg_blocklace::finality::FinalityLevel::Ordered,
                                merkle_root,
                                block_receipt_stream_root,
                            )
                            .await;
                    }
                }
            }

            if acknowledged_blocks.is_empty() {
                if retry_prefix {
                    tokio::time::sleep(Duration::from_millis(250)).await;
                    handle.finality_notify.notify_one();
                }
                continue;
            }

            // ── Record Participant Activity ──────────────────────────────────
            // Track which participants produced blocks in this batch so that
            // the timeout mechanism knows they are still alive.
            //
            // ⚑ ED25519, NOT `Block::creator`. `ConstitutionManager::record_activity`
            // writes `last_active_wave`, which `check_timeouts` reads back keyed by
            // `constitution.current.participants` — the ed25519 strand keys. Feeding it
            // the HYBRID id inserted rows under keys no participant ever has, so every
            // participant's `last_active_wave` stayed at its wave-0 initialisation and
            // the timeout mechanism could only ever count UP. Same mismatch as the vote
            // path, one loop away.
            {
                // Collect all block creators from this batch, in the ed25519
                // strand-key space the constitution is keyed by.
                let lace = handle.lace.read().await;
                let mut active_creators: Vec<[u8; 32]> = Vec::new();
                for block in &acknowledged_blocks {
                    match block {
                        FinalizedBlock::Membership {
                            creator_ed25519, ..
                        } => {
                            active_creators.push(*creator_ed25519);
                        }
                        FinalizedBlock::Turn { block_id, .. } => {
                            if let Some(b) = lace.get(block_id) {
                                active_creators.push(b.ed25519);
                            }
                        }
                        FinalizedBlock::Checkpoint { block_id, .. } => {
                            if let Some(b) = lace.get(block_id) {
                                active_creators.push(b.ed25519);
                            }
                        }
                        FinalizedBlock::Inert { .. } => {}
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

            // ── N3 committee-restart anchor: back-fill vote quorums ──────────
            // Committee finalization votes arrive async over gossip, AFTER a
            // root is first persisted with only the local signature. Once a
            // >=threshold quorum over a recently finalized root has assembled in
            // the collector, re-store that root carrying the quorum so a restart
            // can re-anchor it (`verify_finalization_quorum`). The persisted
            // quorum trails the finalized head by the gossip round(s) it takes
            // the votes to converge — the deliberate liveness cost of Fix B.
            backfill_finalization_quorums(&state, &handle).await;
            if retry_prefix {
                tokio::time::sleep(Duration::from_millis(250)).await;
                handle.finality_notify.notify_one();
            }
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
/// Re-persist recently finalized attested roots that now carry an assembled
/// committee finalization-vote quorum — the N3 committee-restart anchor (Fix B).
///
/// A full-mode committee node first persists each attested root synchronously
/// with only its OWN signature (`1 < threshold`); the cross-node quorum forms a
/// gossip round or two later as peers' [`FinalizationVote`]s converge in the
/// collector. This scans a bounded window of the most recent roots and, for any
/// whose `finalization_quorum` is still empty but whose block now has a genuine
/// `>= threshold` quorum over the SAME `merkle_root`, re-stores the root with
/// that quorum attached. On restart, `verify_finalization_quorum` then re-anchors
/// it — closing the fail-close WITHOUT accepting any root that lacks a real
/// committee quorum.
///
/// [`FinalizationVote`]: crate::finalization_votes::FinalizationVote
async fn backfill_finalization_quorums(state: &NodeState, handle: &BlocklaceHandle) {
    /// How many recent heights to reconcile per finality tick. The quorum trails
    /// the head by only a round or two, so a small window converges it while
    /// bounding the per-tick work.
    const WINDOW: u64 = 32;

    let s = state.read().await;
    let latest_h = match s.store.latest_attested_root() {
        Ok(Some(r)) => r.height,
        _ => return,
    };
    let start = latest_h.saturating_sub(WINDOW);
    let col = handle.votes.read().await;
    for h in start..=latest_h {
        let root = match s.store.attested_root_at_height(h) {
            Ok(Some(r)) => r,
            _ => continue,
        };
        if root.has_finalization_quorum() {
            continue;
        }
        let Some(block_id) = root.blocklace_block_id else {
            continue;
        };
        if let Some((qpair, sigs)) = col.assembled_quorum(&BlockId(block_id)) {
            // Only attach a quorum that binds THIS root's exact committed state
            // — v4: the ledger root AND the receipt stream — and meets the
            // root's own threshold. Never fabricate an anchor, and never attach
            // signatures that agreed on the ledger image while disagreeing about
            // which receipts produced it.
            if qpair == (root.merkle_root, root.receipt_stream_root) && sigs.len() >= root.threshold
            {
                let updated = dregg_persist::StoredAttestedRoot {
                    finalization_quorum: sigs,
                    ..root
                };
                match s.store.store_attested_root(&updated) {
                    Ok(()) => debug!(
                        height = h,
                        "back-filled committee finalization quorum (restart anchor assembled)"
                    ),
                    Err(e) => {
                        warn!(error = %e, height = h, "failed to back-fill finalization quorum")
                    }
                }
            }
        }
    }
}

/// A fresh store or legacy image has no faithful-history segment yet.  Derive a
/// deterministic nonzero federation context even for solo bootstrap (whose
/// historical `federation_id` placeholder is zero), so every node with the same
/// local identity starts the same exact segment rather than accepting a
/// caller-selected session.
fn faithful_history_federation_id(
    configured: [u8; 32],
    local_author: &dregg_types::PublicKey,
) -> [u8; 32] {
    if configured.iter().any(|byte| *byte != 0) {
        configured
    } else {
        *blake3::Hasher::new_derive_key("dregg-faithful-note-root-solo-federation-v1")
            .update(local_author.as_bytes())
            .finalize()
            .as_bytes()
    }
}

fn faithful_history_session_id(federation_id: [u8; 32], committee_epoch: u64) -> [u8; 32] {
    *blake3::Hasher::new_derive_key("dregg-faithful-note-root-session-v1")
        .update(&federation_id)
        .update(&committee_epoch.to_le_bytes())
        .finalize()
        .as_bytes()
}

#[derive(Debug)]
enum FinalizedSignalRouteError {
    Malformed(crate::poa_signal_adapter::SignalAdapterError),
    Multiple,
    NonCanonicalCarrier(&'static str),
}

/// Find the one reserved Signal claim and require its entire action carrier to
/// have the one shape the Lean network judge actually interprets.
///
/// Unknown events remain ordinary. Once the reserved marker appears, however,
/// the turn is no longer a generic call forest: it must be one root action,
/// without children or capability wrapping, targeting the outer actor through
/// method `poa-signal`, with one exact `EmitEvent` and no balance-change or
/// witness side channel. This prevents a judged Signal code from hitchhiking
/// beside an unrelated generic mutation that the game judge never saw.
fn finalized_signal_claim(
    turn: &dregg_turn::Turn,
) -> Result<Option<dregg_sdk::poa_signal::SignalClaimV1>, FinalizedSignalRouteError> {
    fn collect(
        effect: &dregg_turn::Effect,
        found: &mut Option<dregg_sdk::poa_signal::SignalClaimV1>,
    ) -> Result<(), FinalizedSignalRouteError> {
        match crate::poa_signal_adapter::classify_signal_effect(effect)
            .map_err(FinalizedSignalRouteError::Malformed)?
        {
            crate::poa_signal_adapter::SignalEffectRoute::Ordinary => {}
            crate::poa_signal_adapter::SignalEffectRoute::Signal(claim) => {
                if found.replace(claim).is_some() {
                    return Err(FinalizedSignalRouteError::Multiple);
                }
            }
        }
        if let dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } = effect {
            for inner in inner_effects {
                collect(inner, found)?;
            }
        }
        Ok(())
    }

    let mut found = None;
    for effect in turn.call_forest.total_effects() {
        collect(effect, &mut found)?;
    }
    let Some(claim) = found else {
        return Ok(None);
    };

    let exact = dregg_sdk::poa_signal::claim_from_exact_signal_turn(turn).map_err(|_| {
        FinalizedSignalRouteError::NonCanonicalCarrier(
            "Signal turn differs from the canonical one-action hybrid-fee carrier",
        )
    })?;
    let action = &turn.call_forest.roots[0].action;
    if !matches!(
        &action.authorization,
        dregg_turn::Authorization::Signature(..)
            | dregg_turn::Authorization::HybridSignature { .. }
    ) {
        return Err(FinalizedSignalRouteError::NonCanonicalCarrier(
            "Signal action is not directly signature-authorized",
        ));
    }
    if exact != claim {
        return Err(FinalizedSignalRouteError::NonCanonicalCarrier(
            "Signal scan and exact carrier decoder disagree",
        ));
    }
    Ok(Some(claim))
}

/// Positional NoteCreate leaves for the finalized call forest.  The call-tree
/// depth is semantically significant: nested actions execute too, so collecting
/// only root actions would produce a live tree that omits committed notes.
fn finalized_note_commitments(forest: &dregg_turn::CallForest) -> Vec<[u8; 32]> {
    fn collect(effect: &dregg_turn::Effect, out: &mut Vec<[u8; 32]>) {
        match effect {
            dregg_turn::Effect::NoteCreate { commitment, .. } => out.push(commitment.0),
            dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out);
                }
            }
            _ => {}
        }
    }

    let mut out = Vec::new();
    for effect in forest.total_effects() {
        collect(effect, &mut out);
    }
    out
}

/// The off-lock executor result may be installed only if the durable global
/// frontier it started from is still current.  Cell-level conflict detection
/// alone is insufficient: a concurrent spend by a disjoint agent changes the
/// global nullifier accumulator without touching any of this turn's cells.
fn finalized_global_snapshot_matches(
    expected_cursor: u64,
    expected_nullifier_root: [u8; 32],
    current_cursor: u64,
    current_nullifier_root: [u8; 32],
) -> bool {
    expected_cursor == current_cursor && expected_nullifier_root == current_nullifier_root
}

/// A receipt durably staged by the historical solo ingress path may differ
/// from a receipt re-executed after restart only in the executor's wall clock
/// and the solo `Tentative` finality bit (plus the signature over those bytes).
/// Every semantic transition field must otherwise be byte-identical.
fn staged_receipt_matches_reexecution(
    staged: &dregg_turn::TurnReceipt,
    reexecuted: &dregg_turn::TurnReceipt,
) -> bool {
    let mut normalized = reexecuted.clone();
    normalized.timestamp = staged.timestamp;
    normalized.finality = staged.finality;
    // `executor_signature` is not folded into `receipt_hash`; copy it only so
    // future equality implementations cannot accidentally make it relevant.
    normalized.executor_signature = staged.executor_signature.clone();
    normalized.receipt_hash() == staged.receipt_hash()
}

/// Public nullifier-accumulator inputs of every finalized NoteSpend, including
/// capability-wrapped inner effects, in deterministic DFS/effect order.
///
/// The value is already part of the note-spend statement.  Carrying it here is
/// required to reconstruct the deployed accumulator leaf after restart; a bare
/// nullifier presence bit is not the same committed state.
fn finalized_note_spends(
    forest: &dregg_turn::CallForest,
) -> Vec<dregg_persist::FinalizedNullifierRecord> {
    fn collect(
        effect: &dregg_turn::Effect,
        out: &mut Vec<dregg_persist::FinalizedNullifierRecord>,
    ) {
        match effect {
            dregg_turn::Effect::NoteSpend {
                nullifier, value, ..
            } => out.push(dregg_persist::FinalizedNullifierRecord {
                nullifier: nullifier.0,
                value: *value,
            }),
            dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out);
                }
            }
            _ => {}
        }
    }

    let mut out = Vec::new();
    for effect in forest.total_effects() {
        collect(effect, &mut out);
    }
    out
}

/// Rebuild the exact successor chain a DFS-ordered batch of spends produces.
///
/// The returned roots are *per effect*, not one repeated batch root: root `i`
/// is the accumulator after inserting spends `0..=i`.  FNSP carriers bind these
/// staged roots because the executor applies the same effects sequentially.
fn planned_ordered_nullifier_successors(
    durable: &dregg_cell::nullifier_set::NullifierSet,
    spends: &[dregg_persist::FinalizedNullifierRecord],
) -> Result<(dregg_cell::nullifier_set::NullifierSet, Vec<[u8; 32]>), [u8; 32]> {
    let mut successor = durable.clone();
    let mut roots = Vec::with_capacity(spends.len());
    for spend in spends {
        successor
            .insert(dregg_cell::note::Nullifier(spend.nullifier), spend.value)
            .map_err(|_| spend.nullifier)?;
        roots.push(successor.root8().to_bytes32());
    }
    Ok((successor, roots))
}

/// Decode every NoteSpend's strict versioned carrier and lift both root byte
/// strings into the canonical eight-felt type wall. The opaque inner proof
/// remains for the note-spend verifier; this boundary identifies the exact
/// authenticated historical frontier it opens and the exact nullifier
/// successor finalization must atomically persist.
fn finalized_faithful_spend_claims(
    forest: &dregg_turn::CallForest,
) -> Result<
    Vec<(
        u64,
        dregg_persist::CanonicalFaithfulRoot,
        dregg_persist::CanonicalFaithfulRoot,
        u64,
    )>,
    (),
> {
    fn collect(
        effect: &dregg_turn::Effect,
        out: &mut Vec<(
            u64,
            dregg_persist::CanonicalFaithfulRoot,
            dregg_persist::CanonicalFaithfulRoot,
            u64,
        )>,
    ) -> Result<(), ()> {
        match effect {
            dregg_turn::Effect::NoteSpend {
                note_tree_root,
                spending_proof,
                asset_type,
                ..
            } => {
                let carrier =
                    dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier::decode(
                        spending_proof,
                    )
                    .map_err(|_| ())?;
                let root = dregg_persist::CanonicalFaithfulRoot::from_bytes(*note_tree_root)
                    .map_err(|_| ())?;
                let successor = dregg_persist::CanonicalFaithfulRoot::from_bytes(
                    carrier.successor_nullifier_root(),
                )
                .map_err(|_| ())?;
                out.push((carrier.root_height(), root, successor, *asset_type));
            }
            dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    let mut out = Vec::new();
    for effect in forest.total_effects() {
        collect(effect, &mut out)?;
    }
    Ok(out)
}

fn faithful_history_contains_pair(
    history: &dregg_persist::FaithfulNoteRootHistoryV1,
    height: u64,
    root: dregg_persist::CanonicalFaithfulRoot,
) -> bool {
    (history.anchor().height == height && history.anchor().root == root)
        || history
            .envelopes()
            .iter()
            .any(|envelope| envelope.record.height == height && envelope.record.successor == root)
}

fn finalized_turn_bytes(payload: &Payload) -> Option<&[u8]> {
    match payload {
        Payload::Turn(bytes) => Some(bytes),
        Payload::TurnBundle(bundle) => Some(&bundle.signed_turn),
        Payload::ConsensusTimedTurnV1(bundle) => Some(bundle.signed_turn()),
        Payload::Ack
        | Payload::Checkpoint { .. }
        | Payload::MembershipVote { .. }
        | Payload::Data(_) => None,
    }
}

/// The turn hash a turn-bearing payload carries — the SAME value a submit
/// response hands the caller (`signed_turn.turn.hash()`), so a client's handle
/// and the node's bookkeeping are the same coordinate by construction rather
/// than by convention.
///
/// `None` for a non-turn payload or bytes that do not decode; a payload the node
/// cannot read as a signed turn is simply not tracked as in-flight, which costs
/// a `pending` answer and never a wrong one.
fn payload_signed_turn_hash(payload: &Payload) -> Option<[u8; 32]> {
    signed_turn_hash_from_bytes(finalized_turn_bytes(payload)?)
}

/// [`payload_signed_turn_hash`] for bytes already extracted from a payload.
fn signed_turn_hash_from_bytes(bytes: &[u8]) -> Option<[u8; 32]> {
    postcard::from_bytes::<dregg_sdk::SignedTurn>(bytes)
        .ok()
        .map(|signed| signed.turn.hash())
}

/// Reconcile the best-effort executed-id projection with terminal turn
/// authority reconstructed from the commit/rejection logs.
///
/// All three turn carriers require a durable terminal row. In particular a
/// persisted `ConsensusTimedTurnV1` id is not authority by itself: it may have
/// been flushed just before a crash while its application transaction failed.
fn reconcile_restored_execution_ids(
    restored_lace: &Blocklace,
    persisted_ids: Vec<BlockId>,
    durable_turn_ids: &std::collections::HashSet<BlockId>,
) -> Vec<BlockId> {
    let mut executed_ids = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for id in persisted_ids {
        let keep = match restored_lace.get(&id).map(|block| &block.payload) {
            Some(Payload::Turn(_))
            | Some(Payload::TurnBundle(_))
            | Some(Payload::ConsensusTimedTurnV1(_)) => durable_turn_ids.contains(&id),
            Some(_) => true,
            // Not in the restored lace: tau can never order it, so it can never
            // be served; carrying it would only grow the set.
            None => false,
        };
        if keep && seen.insert(id) {
            executed_ids.push(id);
        }
    }
    for id in durable_turn_ids {
        if seen.insert(*id) {
            executed_ids.push(*id);
        }
    }
    executed_ids
}

fn persist_finalized_payload_rejection(
    s: &crate::state::NodeStateInner,
    block_id: BlockId,
    payload: &[u8],
    turn_hash: Option<[u8; 32]>,
    reason_code: &str,
) -> FinalizedExecutionOutcome {
    let retryable =
        |error: String| FinalizedExecutionOutcome::RetryableOperational { block_id, error };
    let fatal = |error: String| FinalizedExecutionOutcome::FatalIntegrity { block_id, error };
    let record = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::new(
        block_id.0,
        payload,
        turn_hash,
        reason_code,
    );
    let key =
        crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(&block_id.0);
    let encoded = match record.encode() {
        Ok(encoded) => encoded,
        Err(error) => {
            error!(
                block_id = %block_id,
                reason_code,
                error = %error,
                "failed to encode deterministic finalized-payload rejection record"
            );
            return fatal(format!(
                "failed to encode deterministic rejection row: {error}"
            ));
        }
    };
    match s.store.get_config(&key) {
        Ok(Some(existing)) if existing == encoded => {
            // Already recorded — a crash replay or duplicate delivery of a
            // verdict this node already reached. The COUNTER deliberately does
            // NOT move here: a rejection counter that climbs on restart is a
            // counter of restarts. The by-turn index is still reconciled, so a
            // row written before the index existed becomes queryable.
            record_rejection_turn_index(s, turn_hash, block_id, reason_code);
            return FinalizedExecutionOutcome::DeterministicallyRejected {
                block_id,
                reason_code: reason_code.to_owned(),
            };
        }
        Ok(Some(_)) => {
            // A block id names one immutable consensus payload.  Never replace
            // an existing outcome with a contradictory local observation.
            error!(
                block_id = %block_id,
                reason_code,
                "refusing to overwrite a conflicting finalized-payload rejection record"
            );
            return fatal("conflicting durable rejection row for immutable block id".into());
        }
        Ok(None) => {}
        Err(error) => {
            error!(
                block_id = %block_id,
                reason_code,
                error = %error,
                "failed to read finalized-payload rejection record before idempotent write"
            );
            return retryable(format!("failed to read durable rejection row: {error}"));
        }
    }
    #[cfg(test)]
    {
        let mut target = FAIL_FINALIZED_REJECTION_WRITE_FOR_BLOCK
            .lock()
            .expect("finalized rejection failure hook mutex");
        if target.as_ref() == Some(&block_id.0) {
            target.take();
            return retryable("injected finalized rejection-store failure".into());
        }
    }
    match s.store.set_config(&key, &encoded) {
        Ok(()) => {
            // COUNT IT. This is the one place a deterministic post-finalization
            // refusal becomes durable for the first time, so it is the one place
            // that may move the counter. Before this line the path that
            // unanimously and correctly discarded a turn on four nodes left
            // `dregg_turns_rejected_total` reading 0 on all four.
            crate::metrics::note_finalized_payload_rejected(reason_code);
            record_rejection_turn_index(s, turn_hash, block_id, reason_code);
            FinalizedExecutionOutcome::DeterministicallyRejected {
                block_id,
                reason_code: reason_code.to_owned(),
            }
        }
        Err(error) => {
            error!(
                block_id = %block_id,
                reason_code,
                error = %error,
                "failed to persist deterministic finalized-payload rejection record; identity remains pending"
            );
            retryable(format!("failed to persist durable rejection row: {error}"))
        }
    }
}

/// Write the reciprocal `turn_hash → (block_id, reason)` index for a recorded
/// rejection, and retire the turn from this node's in-flight set.
///
/// SURFACE THE VERDICT. The block-keyed authority row was already durable on all
/// four nodes of the measured federation and reachable by nothing: `/api/receipts`
/// simply lacked the turn, and the only coordinate the client held was the turn
/// hash. This is the index that closes that.
///
/// Best-effort by construction, and that is the right posture: the AUTHORITY is
/// the block-keyed row, which is written first and whose failure already fails
/// the whole outcome. A missing or unwritable index makes the verdict
/// unqueryable-by-hash (it reads `unknown`, the honest answer), never wrong —
/// `GET /api/turn/{hash}/verdict` re-reads the authority row and refuses to
/// answer if the two disagree. First-write-wins: an existing index row is never
/// replaced.
fn record_rejection_turn_index(
    s: &crate::state::NodeStateInner,
    turn_hash: Option<[u8; 32]>,
    block_id: BlockId,
    reason_code: &str,
) {
    let Some(turn_hash) = turn_hash else {
        // A payload that never decoded to a signed turn has no turn hash to
        // index by. The block-keyed row still records the refusal.
        return;
    };
    if let Some(handle) = s.blocklace_handle.as_ref() {
        handle.in_flight_turns.resolve(&turn_hash);
    }
    if !crate::signed_turn_validation::canonical_rejection_reason(reason_code) {
        error!(
            block_id = %block_id,
            reason_code,
            "refusing to index a finalized rejection under a non-canonical reason code"
        );
        return;
    }
    let index = crate::signed_turn_validation::FinalizedPayloadRejectionTurnIndex::new(
        turn_hash,
        block_id.0,
        reason_code,
    );
    let index_key =
        crate::signed_turn_validation::FinalizedPayloadRejectionTurnIndex::storage_key(&turn_hash);
    match s.store.get_config(&index_key) {
        Ok(Some(_)) => return,
        Ok(None) => {}
        Err(error) => {
            warn!(
                turn_hash = %hex_encode(&turn_hash),
                error = %error,
                "could not read the finalized-rejection turn index; the verdict stays durable \
                 under its block id but is not queryable by turn hash"
            );
            return;
        }
    }
    let Ok(encoded) = index.encode() else {
        error!(
            turn_hash = %hex_encode(&turn_hash),
            "failed to encode the finalized-rejection turn index"
        );
        return;
    };
    if let Err(error) = s.store.set_config(&index_key, &encoded) {
        warn!(
            turn_hash = %hex_encode(&turn_hash),
            error = %error,
            "could not persist the finalized-rejection turn index; the verdict stays durable \
             under its block id but is not queryable by turn hash"
        );
    }
}

/// Complete locked snapshot for the disjoint exact-v3 finalized-turn path.
///
/// Every field is owned so proof verification and the real producer can run on a blocking worker
/// with no Tokio worker or node-state lock held.  The actor authority retains the complete durable
/// ledger image and its opaque revalidation key through the later CAS.
struct LiveExactFnspV3Preparation {
    signed_turn: dregg_sdk::SignedTurn,
    validated_signed_turn: crate::signed_turn_validation::ValidatedSignedTurn,
    actor_authority: crate::exact_fnsp_v3_actor_authority::DurableExactFnspV3ActorAuthority,
    prepared_transition: dregg_persist::PreparedExactFnspV3StateTransitionV1,
    signer: crate::exact_fnsp_v3_activation::ExactFnspV3ExecutorSignerAuthority,
    epoch: dregg_turn::ExactFnspV3ReceiptEpochV1,
    executor: dregg_turn::TurnExecutor,
    coordinates: crate::exact_fnsp_v3_execution_authority::FinalizedRecordCoordinates,
    block_id: BlockId,
    block_executed_up_to: u64,
    captured_executed_up_to: u64,
    timestamp: i64,
    lean_producer_enabled: bool,
    artifacts: Option<TurnArtifactBundle>,
}

/// Stable terminal disposition for failures on the disjoint exact-v3 route.
///
/// The payload class is safe to persist as ACK authority because it depends only on authenticated
/// signed bytes and code-owned proof verification.  Availability/CAS failures remain retryable;
/// contradictions between already-authenticated durable coordinates stop the finality task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExactFinalizedFailureClass {
    DeterministicPayload(&'static str),
    RetryableOperational,
    FatalIntegrity,
}

#[derive(Debug)]
struct ExactFinalizedFailure {
    class: ExactFinalizedFailureClass,
    error: String,
}

impl ExactFinalizedFailure {
    fn deterministic(reason_code: &'static str, error: impl Into<String>) -> Self {
        Self {
            class: ExactFinalizedFailureClass::DeterministicPayload(reason_code),
            error: error.into(),
        }
    }

    fn retryable(error: impl Into<String>) -> Self {
        Self {
            class: ExactFinalizedFailureClass::RetryableOperational,
            error: error.into(),
        }
    }

    fn fatal(error: impl Into<String>) -> Self {
        Self {
            class: ExactFinalizedFailureClass::FatalIntegrity,
            error: error.into(),
        }
    }
}

fn exact_store_failure_class(error: &dregg_persist::StoreError) -> ExactFinalizedFailureClass {
    match error {
        // redb I/O/transaction availability can clear without changing the finalized payload.
        dregg_persist::StoreError::Database(_) => ExactFinalizedFailureClass::RetryableOperational,
        // These say bytes or authenticated state already present in the durable image are
        // contradictory. Retrying the same image cannot repair them and must not spin tau.
        dregg_persist::StoreError::Serialization(_)
        | dregg_persist::StoreError::Crypto(_)
        | dregg_persist::StoreError::Integrity(_)
        | dregg_persist::StoreError::NotFound => ExactFinalizedFailureClass::FatalIntegrity,
    }
}

fn classify_exact_store_failure(error: dregg_persist::StoreError) -> ExactFinalizedFailure {
    ExactFinalizedFailure {
        class: exact_store_failure_class(&error),
        error: error.to_string(),
    }
}

fn classify_exact_executor_failure(
    error: crate::exact_fnsp_v3_execution_authority::ExecutorProducedFinalizationError,
) -> ExactFinalizedFailure {
    use crate::exact_fnsp_v3_execution_authority::ExecutorProducedFinalizationError as E;

    let class = match &error {
        E::ExactNoteSpendCardinality { .. }
        | E::ExactProofCarrierInvalid(_)
        | E::ExactTurnShapeUnsupported => {
            ExactFinalizedFailureClass::DeterministicPayload("exact-fnsp-v3-carrier-refused")
        }
        E::ExactProofAcceptance(_) => {
            ExactFinalizedFailureClass::DeterministicPayload("exact-fnsp-v3-proof-refused")
        }
        E::ExactChargedRoutePreflight(_) | E::ProducerDidNotCommit(_) => {
            ExactFinalizedFailureClass::DeterministicPayload("exact-fnsp-v3-execution-refused")
        }
        E::ExactAdmission(dregg_turn::executor::ExactFnspV3AdmissionError::MutexPoisoned) => {
            ExactFinalizedFailureClass::RetryableOperational
        }
        E::ValidatedTurnHashMismatch
        | E::DurableActorMismatch
        | E::ActorOrdinalMismatch
        | E::ProducerRejectedAfterMutation
        | E::ReceiptTurnMismatch
        | E::ReceiptForestMismatch
        | E::ReceiptActorMismatch
        | E::ReceiptBeforeContextMismatch
        | E::ReceiptAfterContextMismatch
        | E::ExecutorSignatureInvalid
        | E::ExactExecutorHasBudgetGate
        | E::NonDurableExecutorSideStateMutation
        | E::ExactAdmission(_)
        | E::ExactAdmissionMissingAfterCommit
        | E::ExecutorKeyChangedAtFrameJoin
        | E::ExactFrameReceiptMismatch
        | E::ExactFrameCarrierMismatch
        | E::ExactFrameStatementMismatch
        | E::ExactFrameSignatureInvalid
        | E::ReceiptEpoch(_) => ExactFinalizedFailureClass::FatalIntegrity,
    };
    ExactFinalizedFailure {
        class,
        error: error.to_string(),
    }
}

fn classify_exact_actor_failure(
    error: crate::exact_fnsp_v3_actor_authority::DurableExactFnspV3ActorAuthorityError,
) -> ExactFinalizedFailure {
    use crate::exact_fnsp_v3_actor_authority::DurableExactFnspV3ActorAuthorityError as E;

    let class = match &error {
        E::Store(store_error) => exact_store_failure_class(store_error),
        E::CanonicalCheckpointUnavailable | E::SnapshotMoved => {
            ExactFinalizedFailureClass::RetryableOperational
        }
        E::CheckpointAnchorEncoding(_)
        | E::CheckpointAnchorMissing { .. }
        | E::CheckpointAnchorBehind { .. }
        | E::CheckpointAnchorRootMismatch { .. }
        | E::CheckpointAnchorUnauthenticated { .. }
        | E::ExactStateMissing
        | E::ReceiptDecode(_)
        | E::OverlayApply(_)
        | E::CompactionFloorAhead { .. }
        | E::CommitTailMissing { .. }
        | E::RecoveredRootMismatch { .. }
        | E::LiveRootMismatch { .. }
        | E::DurableActorMissing(_)
        | E::LiveActorMismatch(_) => ExactFinalizedFailureClass::FatalIntegrity,
    };
    ExactFinalizedFailure {
        class,
        error: error.to_string(),
    }
}

fn classify_exact_activation_failure(
    error: crate::exact_fnsp_v3_activation::ExactFnspV3ActivationError,
) -> ExactFinalizedFailure {
    use crate::exact_fnsp_v3_activation::ExactFnspV3ActivationError as E;

    let class = match &error {
        E::Store(store_error) => exact_store_failure_class(store_error),
        E::ExactStateUninitialized
        | E::ExactInitialMismatch
        | E::ExactCurrentHeadMismatch
        | E::ExecutorKeyMismatch
        | E::ExecutorSignatureSelfCheckFailed
        | E::StoredActivationMismatch
        | E::StoredHeadMismatch
        | E::PlayerReceiptCoordinateMismatch => ExactFinalizedFailureClass::FatalIntegrity,
    };
    ExactFinalizedFailure {
        class,
        error: error.to_string(),
    }
}

fn classify_exact_finalization_failure(
    error: crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError,
) -> ExactFinalizedFailure {
    use crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError as E;

    let class = match &error {
        E::HistoricalRootUnauthenticated | E::FaithfulHistoryUninitialized => {
            ExactFinalizedFailureClass::DeterministicPayload(
                "exact-fnsp-v3-historical-root-refused",
            )
        }
        E::Store(store_error) => exact_store_failure_class(store_error),
        E::FrameSignatureInvalid
        | E::PersistedActivationMissing
        | E::PersistedHeadMismatch(_)
        | E::InvalidHistoryAuthority
        | E::FaithfulSpendCardinality { .. }
        | E::FaithfulStatementCardinality { .. }
        | E::CoordinateMismatch(_)
        | E::Anchor(_)
        | E::ReceiptEncoding(_)
        | E::ExecutorState(_)
        | E::PromiseResolution(_)
        | E::ReceiptHeadInstall(_) => ExactFinalizedFailureClass::FatalIntegrity,
    };
    ExactFinalizedFailure {
        class,
        error: error.to_string(),
    }
}

fn exact_failure_outcome(
    locked: &crate::state::NodeStateInner,
    block_id: BlockId,
    payload: &[u8],
    turn_hash: [u8; 32],
    failure: ExactFinalizedFailure,
) -> FinalizedExecutionOutcome {
    match failure.class {
        ExactFinalizedFailureClass::DeterministicPayload(reason_code) => {
            persist_finalized_payload_rejection(
                locked,
                block_id,
                payload,
                Some(turn_hash),
                reason_code,
            )
        }
        ExactFinalizedFailureClass::RetryableOperational => {
            FinalizedExecutionOutcome::RetryableOperational {
                block_id,
                error: failure.error,
            }
        }
        ExactFinalizedFailureClass::FatalIntegrity => FinalizedExecutionOutcome::FatalIntegrity {
            block_id,
            error: failure.error,
        },
    }
}

fn require_live_exact_epoch_supported(is_solo: bool) -> Result<(), ExactFinalizedFailure> {
    if is_solo {
        Ok(())
    } else {
        // The current exact frame has one executor signature, so a distributed epoch cannot
        // become executable merely by retrying the same finalized payload. Treat this as a
        // consensus-stable unsupported route, not an availability wait that wedges tau forever.
        Err(ExactFinalizedFailure::deterministic(
            "exact-fnsp-v3-epoch-unsupported",
            "exact FNSP-v3 live epoch currently requires one devnet executor signer; shared/threshold frame signing is not installed",
        ))
    }
}

#[allow(clippy::too_many_arguments)]
fn prepare_live_exact_fnsp_v3(
    locked: &mut crate::state::NodeStateInner,
    executor: dregg_turn::TurnExecutor,
    signed_turn: dregg_sdk::SignedTurn,
    validated_signed_turn: crate::signed_turn_validation::ValidatedSignedTurn,
    route: crate::exact_fnsp_v3_execution_authority::ExactFnspV3RouteCoordinates,
    block_id: BlockId,
    block_executed_up_to: u64,
    artifacts: Option<TurnArtifactBundle>,
) -> Result<LiveExactFnspV3Preparation, ExactFinalizedFailure> {
    require_live_exact_epoch_supported(
        locked
            .solo_consensus
            .as_ref()
            .is_some_and(|consensus| consensus.is_solo),
    )?;
    // Current admission paths do not append exact-v3 receipts: the executor refuses the carrier
    // without the proof-acceptance token minted only below.  Detect a row left by an older/foreign
    // ingress anyway.  Such a row cannot be reclassified as the epoch cutover tail and reused as
    // its own exact frame; doing so would shift the exact log coordinate by one.
    if locked
        .cclerk
        .receipt_log()
        .iter()
        .any(|receipt| receipt.turn_hash == validated_signed_turn.turn_hash())
    {
        return Err(ExactFinalizedFailure::fatal(
            "same exact-v3 turn receipt was already staged before finalization",
        ));
    }

    let live_authority = locked
        .store
        .exact_fnsp_v3_live_authority()
        .map_err(classify_exact_store_failure)?;
    let exact_head = if let Some((activation, committed_head)) = live_authority.as_ref() {
        committed_head
            .as_ref()
            .map(|head| head.exact_after())
            .unwrap_or_else(|| activation.exact_initial())
    } else {
        match locked
            .store
            .exact_fnsp_v3_state_head()
            .map_err(classify_exact_store_failure)?
        {
            Some(head) => head,
            None => locked
                .store
                .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
                .map_err(classify_exact_store_failure)?,
        }
    };

    // This is deliberately before lazy activation.  A payload cannot install the federation flag
    // day unless a complete checkpoint⊕overlay actor/ledger image is already authenticated and
    // welded to the live ledger.
    let actor_authority =
        crate::exact_fnsp_v3_actor_authority::capture_durable_exact_fnsp_v3_actor(
            locked,
            signed_turn.turn.agent,
        )
        .map_err(classify_exact_actor_failure)?;
    let actor_coordinates = actor_authority.coordinates();
    if actor_coordinates.exact_state_head() != exact_head {
        return Err(ExactFinalizedFailure::retryable(
            "exact state moved while capturing durable actor authority",
        ));
    }
    let prepared_transition = locked
        .store
        .prepare_exact_fnsp_v3_transition_or_replay(route.nullifier(), route.value())
        .map_err(classify_exact_store_failure)?;
    if prepared_transition.cas().expected() != actor_coordinates.exact_state_head() {
        return Err(ExactFinalizedFailure::retryable(
            "prepared exact transition does not start at the actor snapshot head",
        ));
    }

    let signer = crate::exact_fnsp_v3_activation::ExactFnspV3ExecutorSignerAuthority::capture(
        &locked.cclerk,
    );
    let (receipt_next_index, encoded_tail) = locked
        .store
        .receipt_chain_head()
        .map_err(classify_exact_store_failure)?;
    if receipt_next_index != actor_coordinates.receipt_log_next_index() {
        return Err(ExactFinalizedFailure::retryable(
            "durable receipt cursor moved while capturing exact transition",
        ));
    }
    let receipt_tail_hash = encoded_tail
        .as_deref()
        .map(|bytes| {
            postcard::from_bytes::<dregg_turn::TurnReceipt>(bytes)
                .map(|receipt| receipt.receipt_hash())
                .map_err(|error| {
                    ExactFinalizedFailure::fatal(format!(
                        "durable receipt tail is not canonical: {error}"
                    ))
                })
        })
        .transpose()?;
    if receipt_tail_hash != actor_coordinates.receipt_log_tail_hash() {
        return Err(ExactFinalizedFailure::retryable(
            "durable receipt tail moved while capturing exact transition",
        ));
    }

    let (epoch_number, federation_id, cutover_index, cutover_tail, exact_initial) =
        if let Some((stored_activation, _)) = live_authority {
            (
                stored_activation.epoch(),
                stored_activation.federation_id(),
                stored_activation.receipt_cutover_next_index(),
                stored_activation.receipt_cutover_tail_hash(),
                stored_activation.exact_initial(),
            )
        } else {
            (
                1,
                crate::executor_setup::federation_id_for_executor(locked),
                receipt_next_index,
                receipt_tail_hash,
                exact_head,
            )
        };
    let epoch = dregg_turn::ExactFnspV3ReceiptEpochV1::prepare(
        dregg_turn::ExactFnspV3ReceiptEpoch::new(epoch_number)
            .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?,
        federation_id,
        signer.public_key().0,
        cutover_index,
        cutover_tail,
        dregg_turn::ExactFnspV3StatePoint::new(exact_initial.root(), exact_initial.count())
            .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?,
    )
    .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?;

    let captured_executed_up_to = locked
        .store
        .load_executed_up_to()
        .map_err(classify_exact_store_failure)?;
    let coordinates = crate::exact_fnsp_v3_execution_authority::FinalizedRecordCoordinates::new(
        actor_coordinates.commit_cursor(),
        executor.block_height,
        block_id.0,
        block_executed_up_to,
    );
    let timestamp = executor.current_timestamp;
    Ok(LiveExactFnspV3Preparation {
        signed_turn,
        validated_signed_turn,
        actor_authority,
        prepared_transition,
        signer,
        epoch,
        executor,
        coordinates,
        block_id,
        block_executed_up_to,
        captured_executed_up_to,
        timestamp,
        lean_producer_enabled: locked.lean_producer_enabled,
        artifacts,
    })
}

async fn execute_live_exact_fnsp_v3(
    state: &NodeState,
    handle: &BlocklaceHandle,
    preparation: LiveExactFnspV3Preparation,
    finality_round: Option<u64>,
) -> Result<(u64, Option<[u8; 32]>), ExactFinalizedFailure> {
    let LiveExactFnspV3Preparation {
        signed_turn,
        validated_signed_turn,
        actor_authority,
        prepared_transition,
        signer,
        epoch,
        executor,
        coordinates,
        block_id,
        block_executed_up_to,
        captured_executed_up_to,
        timestamp,
        lean_producer_enabled,
        artifacts,
    } = preparation;

    // HidingFRI verification and the real Rust/Lean producer both run on the blocking pool against
    // owned state.  Rejected execution never reaches the node's RAM, cipherclerk, store, events,
    // or generic fee/nonce rejection path.
    let joined = tokio::task::spawn_blocking(move || {
        let accepted =
            crate::exact_fnsp_v3_execution_authority::verify_exact_fnsp_v3_turn_acceptance(
                &signed_turn,
                &prepared_transition,
                &actor_authority,
                &executor,
            )?;
        let executed =
            crate::exact_fnsp_v3_execution_authority::execute_and_authenticate_finalized_turn(
                executor,
                accepted,
                &signed_turn,
                validated_signed_turn,
                actor_authority,
                &signer,
                lean_producer_enabled,
                coordinates,
            )?;
        Ok::<_, crate::exact_fnsp_v3_execution_authority::ExecutorProducedFinalizationError>((
            executed,
            signer,
            epoch,
            prepared_transition,
            signed_turn,
        ))
    })
    .await
    .map_err(|error| {
        ExactFinalizedFailure::retryable(format!(
            "exact proof/executor worker unavailable: {error}"
        ))
    })?
    .map_err(classify_exact_executor_failure)?;

    let (executed, signer, epoch, prepared_transition, signed_turn) = joined;
    let mut locked = state.write().await;

    // The blocklace resume cursor is independent of the commit cursor and exact CAS.  It may move
    // while proof work is off-lock; do not attach this turn to a different finalized-block view.
    let current_executed_up_to = locked
        .store
        .load_executed_up_to()
        .map_err(classify_exact_store_failure)?;
    if current_executed_up_to != captured_executed_up_to {
        return Err(ExactFinalizedFailure::retryable(
            "exact FNSP-v3 block finalization cursor moved during proof work",
        ));
    }
    executed
        .revalidate_actor_locked(&locked)
        .map_err(classify_exact_actor_failure)?;

    // Retain the live signer material for the prepared exact-finalization authority below.  The
    // prepared authority is also the sole historical-root admission boundary: it performs one
    // full history audit on first activation, then authenticates active-epoch spends in O(1).
    let local_pk = locked.cclerk.public_key();
    let signing_key_bytes = locked.cclerk.gossip_signing_key().to_bytes();
    if signer.public_key() != local_pk {
        return Err(ExactFinalizedFailure::fatal(
            "exact FNSP-v3 executor signer changed before finalization",
        ));
    }
    let (local_ml_dsa_pk, local_ml_dsa_signing_key) =
        dregg_federation::frost::MlDsaSigningKey::from_seed(&signing_key_bytes);

    // This is the first point allowed to install a lazy epoch: the authenticated actor/checkpoint,
    // exact proof, real producer, and every captured cursor have all succeeded.  The predecessor
    // helper also rechecks the global cclerk receipt length/tail against the durable log, making the
    // post-durable in-memory append a structurally infallible projection install.
    let predecessor = crate::exact_fnsp_v3_activation::exact_fnsp_v3_current_predecessor(
        &locked.store,
        &locked.cclerk,
        epoch,
        signed_turn.turn.agent,
    )
    .map_err(classify_exact_activation_failure)?;
    let executed = executed
        .bind_exact_frame(&signer, predecessor)
        .map_err(classify_exact_executor_failure)?;
    executed
        .revalidate_actor_locked(&locked)
        .map_err(classify_exact_actor_failure)?;

    let binding = executed.frame().accepted_binding();
    let spent_nullifiers = [dregg_persist::commit_log::FinalizedNullifierRecord {
        nullifier: binding.nullifier(),
        value: binding.value(),
    }];
    // The exact AAFI root and FNS3 are intentionally distinct from the deployed legacy
    // sorted-dense nullifier root carried by faithful-spend authority and AttestedRoot.  Rebuild
    // that legacy successor independently from its durable records; never substitute either exact
    // coordinate into this seam.
    let durable_legacy_nullifiers = dregg_cell::nullifier_set::NullifierSet::from_records(
        locked
            .store
            .load_faithful_nullifier_records()
            .map_err(classify_exact_store_failure)?,
    )
    .map_err(|error| {
        ExactFinalizedFailure::fatal(format!(
            "durable legacy nullifier accumulator is malformed: {error}"
        ))
    })?;
    let (_, ordered_legacy_successors) =
        planned_ordered_nullifier_successors(&durable_legacy_nullifiers, &spent_nullifiers)
            .map_err(|nullifier| {
                ExactFinalizedFailure::deterministic(
                    "exact-fnsp-v3-nullifier-already-spent",
                    format!(
                        "exact FNSP-v3 nullifier is already present in the legacy accumulator: {}",
                        dregg_types::hex_encode(&nullifier)
                    ),
                )
            })?;
    let successor_nullifier_root =
        dregg_persist::CanonicalFaithfulRoot::from_bytes(ordered_legacy_successors[0])
            .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?;
    let finalized_spends = [dregg_persist::FinalizedFaithfulSpendInput {
        root_height: binding.historical_root_height(),
        historical_note_root: dregg_persist::CanonicalFaithfulRoot::from_bytes(
            binding.historical_note_root(),
        )
        .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?,
        nullifier: binding.nullifier(),
        value: binding.value(),
        asset_type: binding.asset_type(),
        successor_nullifier_root,
    }];
    let receipt = executed.receipt().clone();
    let record = executed.record().clone();
    let receipt_hash = receipt.receipt_hash();
    let new_height = record.height;

    let prepared_finalization =
        crate::exact_fnsp_v3_finalization::prepare_exact_fnsp_v3_finalization(
            &locked.store,
            executed,
            prepared_transition,
            crate::exact_fnsp_v3_finalization::ExactFnspV3HistoryAuthority {
                ed25519_committee: std::slice::from_ref(&local_pk),
                ml_dsa_committee: std::slice::from_ref(&local_ml_dsa_pk),
                threshold: 1,
            },
        )
        .map_err(classify_exact_finalization_failure)?;

    // A spend-only exact turn advances the note-root history by one finalized height with the
    // exact same note count/root.  There are deliberately no note leaves to append or publish.
    let faithful_federation_id = faithful_history_federation_id(locked.federation_id, &local_pk);
    let existing_faithful_head = locked
        .store
        .faithful_note_root_head()
        .map_err(classify_exact_store_failure)?;
    if existing_faithful_head.as_ref().is_some_and(|head| {
        head.federation_id != faithful_federation_id
            || head.committee_epoch != locked.committee_epoch
    }) {
        return Err(ExactFinalizedFailure::fatal(
            "faithful note-root segment belongs to another committee context",
        ));
    }
    let initial_faithful_anchor = if existing_faithful_head.is_none() {
        let previous_height = new_height.checked_sub(1).ok_or_else(|| {
            ExactFinalizedFailure::fatal("exact finalized height zero has no faithful predecessor")
        })?;
        let note_count = u64::try_from(locked.note_tree.size())
            .map_err(|_| ExactFinalizedFailure::fatal("faithful note count does not fit u64"))?;
        Some(
            dregg_persist::FaithfulNoteRootAnchorV1::new(
                faithful_history_session_id(faithful_federation_id, locked.committee_epoch),
                faithful_federation_id,
                locked.committee_epoch,
                previous_height,
                note_count,
                dregg_persist::CanonicalFaithfulRoot::from_faithful(
                    locked.note_tree.faithful_root_immutable(),
                ),
            )
            .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?,
        )
    } else {
        None
    };
    let faithful_predecessor = existing_faithful_head
        .as_ref()
        .or(initial_faithful_anchor.as_ref())
        .expect("existing or initial faithful head");
    let faithful_record = dregg_persist::plan_faithful_note_root_transition_v1(
        &locked.note_tree,
        faithful_predecessor,
        block_id.0,
        &[],
    )
    .map_err(|error| ExactFinalizedFailure::fatal(error.to_string()))?;
    let faithful_message = faithful_record.signing_message();
    let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
    let faithful_classical_signature = dregg_types::sign(&signing_key, &faithful_message);
    let faithful_pq_signature = local_ml_dsa_signing_key
        .sign(&faithful_message)
        .ok_or_else(|| ExactFinalizedFailure::fatal("ML-DSA faithful-root signing failed"))?;
    let faithful_envelope = dregg_persist::FaithfulNoteRootEnvelopeV1 {
        record: faithful_record.clone(),
        hybrid_quorum: vec![dregg_types::HybridQuorumSig {
            pubkey: local_pk,
            signature: faithful_classical_signature,
            ml_dsa_pubkey: local_ml_dsa_pk.0.to_vec(),
            pq_signature: faithful_pq_signature,
        }],
    };

    let mut attested = dregg_types::AttestedRoot {
        merkle_root: record.ledger_root,
        note_tree_root: Some(faithful_record.successor.to_bytes()),
        nullifier_set_root: Some(successor_nullifier_root.to_bytes()),
        height: new_height,
        timestamp,
        blocklace_block_id: Some(block_id.0),
        finality_round,
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 1,
        federation_id: dregg_types::FederationId(faithful_federation_id),
        receipt_stream_root: Some(dregg_types::merkle_root_of_receipt_hashes(&[receipt_hash])),
        hybrid_quorum: Vec::new(),
    };
    let attested_signature = dregg_types::sign(&signing_key, &attested.signing_message());
    attested
        .quorum_signatures
        .push((local_pk, attested_signature));
    // v4: the assembled quorum agrees on the PAIR, so a quorum is attachable to
    // THIS root only when it binds both this ledger root AND this receipt
    // stream. Filtering on the ledger root alone would attach signatures that
    // said nothing about the receipts this attestation publishes.
    let finalization_quorum = handle
        .votes
        .read()
        .await
        .assembled_quorum(&block_id)
        .filter(|(pair, _)| *pair == (attested.merkle_root, attested.receipt_stream_root))
        .map(|(_, signatures)| signatures)
        .unwrap_or_default();
    // ONE mapping, shared with the other finalized path, the anchor endpoint and
    // the exhibits — see `QuorumSignature::to_hybrid`.
    attested.hybrid_quorum =
        dregg_persist::hybrid_quorum_from_finalization_quorum(&finalization_quorum);
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
        finalization_quorum,
    };

    // The async vote lookup above deliberately happened before the last fence.  Nothing may sit
    // between this revalidation and the one atomic writer transaction.
    if locked
        .store
        .load_executed_up_to()
        .map_err(classify_exact_store_failure)?
        != captured_executed_up_to
    {
        return Err(ExactFinalizedFailure::retryable(
            "exact FNSP-v3 block cursor moved before durable commit",
        ));
    }
    let faithful_weld = dregg_persist::commit_log::FinalizedFaithfulRootWeld {
        initial_anchor: initial_faithful_anchor.as_ref(),
        envelope: &faithful_envelope,
        author_committee: std::slice::from_ref(&local_pk),
        author_ml_dsa_committee: std::slice::from_ref(&local_ml_dsa_pk),
        attested_root: &stored,
        spent_nullifiers: &spent_nullifiers,
        finalized_spends: &finalized_spends,
    };
    let durable = prepared_finalization
        .commit_appending_receipt(&locked.store, faithful_weld)
        .map_err(classify_exact_finalization_failure)?;
    let outcome = durable.outcome();
    if !outcome.freshly_committed {
        debug!(
            turn_hash = %dregg_types::hex_encode(&validated_signed_turn.turn_hash()),
            ordinal = outcome.ordinal,
            "exact FNSP-v3 commit was already durable; suppressing RAM/event replay"
        );
        return Ok((outcome.ordinal, attested.receipt_stream_root));
    }
    // Clone before taking disjoint mutable field borrows.  Fresh installation is deliberately
    // coupled to typed promise-resolution publication against the same durable store.
    let publication_store = locked.store.clone();
    let locked_inner = &mut *locked;
    durable
        .install_fresh_post_execution(
            &mut locked_inner.ledger,
            &mut locked_inner.cclerk,
            state,
            &publication_store,
        )
        .map_err(classify_exact_finalization_failure)?;
    crate::metrics::inc_turns_executed("committed");
    crate::metrics::set_ledger_cell_count(locked.ledger.len() as f64);
    crate::metrics::set_receipt_chain_length(locked.cclerk.receipt_log_length() as f64);
    state.emit(NodeEvent::Root {
        height: new_height,
        merkle_root: dregg_types::hex_encode(&stored.merkle_root),
        timestamp: stored.timestamp,
    });
    let mirrored = dregg_persist::CommitRecord {
        ordinal: outcome.ordinal,
        ..record.clone()
    };
    locked.mirror_committed_record(&mirrored);
    let activity_kinds: Vec<String> = signed_turn
        .turn
        .call_forest
        .iter_dfs()
        .flat_map(|tree| tree.action.effects.iter().map(crate::api::effect_kind))
        .collect();
    crate::api::push_committed_event_enriched(
        &mut locked,
        dregg_types::hex_encode(&receipt_hash),
        dregg_types::hex_encode(signed_turn.turn.agent.as_bytes()),
        if activity_kinds.is_empty() {
            vec!["turn_committed".to_string()]
        } else {
            activity_kinds
        },
        Vec::new(),
        crate::state::ActivityProofStatus::Proved,
    );
    let invalid_bundle_evidence = artifacts
        .as_ref()
        .map(|bundle| materialize_blocklace_artifacts(&mut locked, block_id, &receipt, bundle))
        .unwrap_or_default();
    let federation_receipt =
        build_federation_receipt(&locked, &signed_turn.turn, &receipt, new_height, block_id);
    drop(locked);

    for evidence in invalid_bundle_evidence {
        warn!(
            block_id = %evidence.block_id,
            reason = %evidence.reason,
            "invalid exact FNSP-v3 blocklace turn bundle artifacts"
        );
        state.emit(NodeEvent::InvalidBlocklaceBundle {
            block_id: evidence.block_id.to_string(),
            reason: evidence.reason,
        });
    }
    state.emit(NodeEvent::Receipt {
        hash: dregg_types::hex_encode(&receipt_hash),
    });
    if let Some(federation_receipt) = federation_receipt {
        debug!(
            federation_id = %dregg_types::hex_encode(&federation_receipt.federation_id),
            height = federation_receipt.body.block_height,
            "exact FNSP-v3 federation receipt produced"
        );
    }
    info!(
        turn_hash = %dregg_types::hex_encode(&validated_signed_turn.turn_hash()),
        block_id = %block_id,
        height = new_height,
        round = ?finality_round,
        block_executed_up_to,
        "exact FNSP-v3 finalized turn durably committed and published"
    );
    Ok((outcome.ordinal, attested.receipt_stream_root))
}

/// Apply one identity selected by [`ExecutionCursor::pending`]. The sole live
/// caller is the single finality-executor task, which acknowledges a successful
/// commit before its next poll. On restart, `run_blocklace_sync` reconstructs
/// the cursor from `PersistentStore::commit_log_block_ids` (including compacted
/// ids) before polling. Therefore an already-committed Signal turn is filtered
/// by block identity before this function can snapshot the advanced PoA head
/// and accidentally judge it as a new game action. The persistence apex's exact
/// replay checks remain defence in depth for lower-level crash/recovery callers;
/// they are not an invitation to re-enter semantic evaluation here.
async fn execute_finalized_turn(
    state: &NodeState,
    handle: &BlocklaceHandle,
    block_id: BlockId,
    turn_data: &[u8],
    artifacts: Option<&TurnArtifactBundle>,
    consensus_time: Option<i64>,
    block_executed_up_to: u64,
) -> FinalizedExecutionOutcome {
    // Deserialize the signed turn.
    let signed_turn: dregg_sdk::SignedTurn = match crate::signed_turn_validation::decode_signed_turn(
        turn_data,
    ) {
        Ok(st) => st,
        Err(e) => {
            let s = state.read().await;
            let outcome =
                persist_finalized_payload_rejection(&s, block_id, turn_data, None, e.code());
            warn!(
                block_id = %block_id,
                error = %e,
                reason_code = e.code(),
                "failed to strictly decode turn from finalized block (deterministic rejection recorded)"
            );
            return outcome;
        }
    };

    let computed_hash = signed_turn.turn.hash();
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
    if let Some(consensus_time) = consensus_time {
        executor.current_timestamp = consensus_time;
    }
    // HYBRID PERIMETER — DEPLOYED POSTURE (require_pq = ON) at the finalized-turn
    // admission boundary: a classical-only authorization is rejected on the
    // authoritative cross-node commit path, matching the HTTP submit ingress.
    crate::executor_setup::require_pq_admission(&executor);

    // THE FIRST-TURN CLAIM, computed before the predicate reads the actor cell.
    // Every input is in-block and signature-verified (`SignedTurn.signer`,
    // `SignedTurn.pq_signer`, `turn.hash()`), so every node derives the identical
    // bytes at the identical id — the same cross-node uniformity argument
    // `provision_transfer_destinations` makes, but stronger: the actor's
    // pre-image IS carried, so the claim materializes the canonical account
    // rather than a stub. Deciding it HERE rather than inside the execution clone
    // is the whole onboarding fix: with no cell the predicate answered
    // `pq-identity-not-enrolled`, and with the faucet's zero-pk stub it answered
    // `live-agent-signer-mismatch` — both BEFORE the upgrade that fixed either,
    // so a funded client's first turn could never finalize. `None` means nothing
    // to claim (already the signer's account, or the envelope does not prove it),
    // and the predicate then refuses the turn on its own terms.
    //
    // ⚑ IT IS A CANDIDATE WRITE, NOT AN AUTHORITATIVE ONE, and that distinction
    // is the whole reason this is `claimed_actor_cell` (pure) rather than
    // `claim_signer_actor_cell` (which mutates a ledger). A finalized payload can
    // clear this entire outer perimeter and still be refused afterwards — receipt
    // continuity below, a faithful-note/nullifier refusal, or the executor's own
    // phase-1 charge — and every one of those arms records a deterministic
    // rejection that writes NOTHING durable. The durable image is `checkpoint ⊕
    // touched-cell overlay` built from `ledger_touched_diff(pre_ledger,
    // exec_ledger)`, so a claim written into `s.ledger` here appears in no commit
    // record: it survives in RAM until this node restarts and then vanishes,
    // while a peer that did not restart keeps it. `canonical_ledger_root` hashes
    // the whole cell, so that is an attested-root split on the next finalized
    // turn, not merely invisible content. The claim is therefore installed on the
    // ISOLATED `exec_ledger` candidate below and reaches authoritative RAM only
    // through `install_finalized_ledger_overlay`, past the durable commit point,
    // exactly like every other cell this turn creates.
    let claimed_actor_cell: Option<dregg_cell::Cell> =
        crate::signed_turn_validation::claimed_actor_cell(
            s.ledger.get(&signed_turn.turn.agent),
            &signed_turn,
            executor.require_pq(),
        );

    // Consensus authenticated the block producer, not the enclosed user turn.
    // Re-run the exact HTTP/PG application predicate while holding the state
    // guard and before any ledger/prologue mutation.  Required PQ is pinned to
    // the host-enrolled signer identity; a substituted self-carried key is not
    // an authority.  A bad finalized payload remains a consensus fact, so store
    // a deterministic rejection record instead of silently skipping it.
    let validated_signed_turn = match crate::signed_turn_validation::validate_signed_turn(
        &signed_turn,
        &executor,
        claimed_actor_cell
            .as_ref()
            .or_else(|| s.ledger.get(&signed_turn.turn.agent)),
    ) {
        Ok(validated) => validated,
        Err(validation_error) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                validation_error.code(),
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                reason_code = validation_error.code(),
                reason = %validation_error,
                "finalized SignedTurn failed application authorization before mutation (deterministic rejection recorded)"
            );
            return outcome;
        }
    };

    // Reserved PoA Signal ingress is classified only after the complete
    // SignedTurn perimeter, but before any executor or ledger mutation. The
    // event contributes one mission id and one bounded code; every authority
    // coordinate is loaded/derived below. Malformed or multiple reserved
    // effects are terminal payload refusals and can never fall through as
    // ordinary EmitEvent traffic.
    let signal_claim = match finalized_signal_claim(&signed_turn.turn) {
        Ok(claim) => claim,
        Err(FinalizedSignalRouteError::Malformed(error)) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "poa-signal-reserved-marker-malformed",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %error,
                "malformed reserved PoA Signal effect refused before mutation"
            );
            return outcome;
        }
        Err(FinalizedSignalRouteError::Multiple) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "poa-signal-multiple-effects",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                "multiple PoA Signal effects refused before mutation"
            );
            return outcome;
        }
        Err(FinalizedSignalRouteError::NonCanonicalCarrier(reason)) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "poa-signal-noncanonical-carrier",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                reason,
                "PoA Signal carrier contains semantics outside the one-action Lean judgment"
            );
            return outcome;
        }
    };
    let galley_route = match crate::poa_galley_api::classify_finalized_galley(&signed_turn) {
        Ok(route) => route,
        Err(error) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                error.code(),
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                reason_code = error.code(),
                error = %error,
                "reserved PoA Galley carrier refused before mutation"
            );
            return outcome;
        }
    };
    let is_galley_public_perform = matches!(
        galley_route,
        crate::poa_galley_api::FinalizedGalleyRoute::PublicPerform
    );
    // Classify the disjoint exact-FNSP route before consulting any Signal
    // deployment state. A mixed carrier is intrinsically unsupported: its
    // deterministic disposition must not change merely because one replica has
    // not installed the PoA authority head yet.
    let exact_fnsp_v3_route =
        match crate::exact_fnsp_v3_execution_authority::exact_fnsp_v3_route_coordinates(
            &signed_turn,
        ) {
            Ok(route) => route,
            Err(error) => {
                let outcome = persist_finalized_payload_rejection(
                    &s,
                    block_id,
                    turn_data,
                    Some(computed_hash),
                    "exact-fnsp-v3-carrier-refused",
                );
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    error = %error,
                    "malformed exact FNSP-v3 finalized carrier refused before legacy dispatch"
                );
                return outcome;
            }
        };
    if signal_claim.is_some() && exact_fnsp_v3_route.is_some() {
        let outcome = persist_finalized_payload_rejection(
            &s,
            block_id,
            turn_data,
            Some(computed_hash),
            "poa-signal-exact-fnsp-v3-combination-unsupported",
        );
        warn!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            "PoA Signal plus exact FNSP-v3 is a disjoint unsupported route; refusing rather than omitting the Signal weld"
        );
        return outcome;
    }
    if is_galley_public_perform && signal_claim.is_some() {
        let outcome = persist_finalized_payload_rejection(
            &s,
            block_id,
            turn_data,
            Some(computed_hash),
            "poa-galley-signal-combination-unsupported",
        );
        warn!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            "PoA Galley plus Signal is a disjoint unsupported route"
        );
        return outcome;
    }
    if is_galley_public_perform && exact_fnsp_v3_route.is_some() {
        let outcome = persist_finalized_payload_rejection(
            &s,
            block_id,
            turn_data,
            Some(computed_hash),
            "poa-galley-exact-fnsp-v3-combination-unsupported",
        );
        warn!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            "PoA Galley plus exact FNSP-v3 is a disjoint unsupported route"
        );
        return outcome;
    }
    let galley_preflight = if is_galley_public_perform {
        match s
            .store
            .preflight_active_poa_galley_public_perform_v1(&signed_turn)
        {
            Ok(preflight) => Some(preflight),
            Err(
                dregg_persist::poa_galley_authority::PoaGalleyPublicPerformPreflightErrorV1::StaleAction(
                    reason,
                ),
            ) => {
                let outcome = persist_finalized_payload_rejection(
                    &s,
                    block_id,
                    turn_data,
                    Some(computed_hash),
                    "poa-galley-stale-action",
                );
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    reason,
                    "stale Galley action refused deterministically before execution"
                );
                return outcome;
            }
            Err(
                dregg_persist::poa_galley_authority::PoaGalleyPublicPerformPreflightErrorV1::AuthorityUnavailable(
                    error,
                ),
            ) => {
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    error = %error,
                    "Galley native authority unavailable; finalized identity remains pending"
                );
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("Galley preflight unavailable: {error}"),
                };
            }
        }
    } else {
        None
    };
    let signal_head_snapshot = if signal_claim.is_some() {
        match s.store.load_poa_signal_head(s.federation_id) {
            Ok(Some(head)) => Some(head),
            Ok(None) => {
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    federation_id = %dregg_types::hex_encode(&s.federation_id),
                    "PoA Signal authority head is not initialized; finalized identity remains pending"
                );
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: "PoA Signal authority head is not initialized".into(),
                };
            }
            Err(dregg_persist::StoreError::Database(error)) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("could not load PoA Signal authority head: {error}"),
                };
            }
            Err(error) => {
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("PoA Signal authority head malformed: {error}"),
                };
            }
        }
    } else {
        None
    };

    // The open slot is authority for the run's INSTANCE, exactly as the head is
    // authority for its state. A node with no open slot cannot serve a scored run:
    // the instance would be one nobody committed to in advance, which is the whole
    // property the slot commitment exists to provide. Refuse rather than draw one.
    let signal_slot_snapshot = if signal_claim.is_some() {
        match s.store.load_poa_signal_open_slot_v1(s.federation_id) {
            Ok(Some(slot)) => Some(slot),
            Ok(None) => {
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    federation_id = %dregg_types::hex_encode(&s.federation_id),
                    "no PoA Signal slot is open; scored runs refuse until the curator opens one"
                );
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: "no PoA Signal slot is open".into(),
                };
            }
            Err(dregg_persist::StoreError::Database(error)) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("could not load the open PoA Signal slot: {error}"),
                };
            }
            Err(error) => {
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("PoA Signal slot malformed: {error}"),
                };
            }
        }
    } else {
        None
    };

    // ⚑ THE TRANSCRIPT-PROVENANCE GATE — a judged settlement is evidence a game
    // was PLAYED, and this is where that becomes true.
    //
    // `SignalTriangulation.judge` scores whatever transcript it is handed and is
    // right to; provenance is the node's job. Until this gate a public claim
    // carried one code, the adapter wrapped it as a one-round game, and a blind
    // 1-in-216 guess settled a turn with no session and no feedback anywhere in its
    // causal history. Here the claim's rounds are checked against the durable
    // session THIS NODE served for this (authority, slot, signer).
    //
    // It sits BEFORE the executor and before any Lean judgment because a claim with
    // no game behind it should cost the chain nothing to refuse, and it routes to
    // `persist_finalized_payload_rejection` — a deterministic refusal with no
    // transition and no height, the same clean disposition a LOSING claim gets. It
    // is NOT a `FatalIntegrity`: a stranger submitting a code is ordinary traffic,
    // not a corrupted node.
    //
    // ⚠ The refusal reason is a function of (stored session, submitted claim) only.
    // It never reads the target, so it cannot tell a submitter how close they were
    // — `poa_signal_adapter::the_refusal_never_depends_on_whether_the_code_is_right`.
    if let (Some(slot), Some(claim)) = (signal_slot_snapshot.as_ref(), signal_claim.as_ref()) {
        let session = match s.store.load_poa_signal_session_v1(
            s.federation_id,
            slot.slot(),
            signed_turn.signer.0,
        ) {
            Ok(found) => found,
            Err(dregg_persist::StoreError::Database(error)) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("could not load the judged PoA Signal session: {error}"),
                };
            }
            Err(error) => {
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("PoA Signal session record malformed: {error}"),
                };
            }
        };
        if let Err(refusal) = crate::poa_signal_adapter::verify_claim_transcript_was_played(
            session.as_ref(),
            slot,
            claim,
        ) {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                refusal.code(),
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                reason_code = refusal.code(),
                reason = %refusal,
                "PoA Signal claim carries a transcript this node never classified; refused \
                 before any judgment or mutation"
            );
            return outcome;
        }
    }

    // EXACT FNSP-v3 is a disjoint finalized-turn route.  Classification happens after the full
    // SignedTurn perimeter but before the legacy FNSP decoder and every generic charge/mutation.
    // Once an `FNSP || version=3` carrier selects this branch, every refusal returns from here: it
    // can never fall through into v2 execution or be charged as an ordinary rejected turn.
    match exact_fnsp_v3_route {
        Some(route) => {
            let preparation = match prepare_live_exact_fnsp_v3(
                &mut s,
                executor,
                signed_turn,
                validated_signed_turn,
                route,
                block_id,
                block_executed_up_to,
                artifacts.cloned(),
            ) {
                Ok(preparation) => preparation,
                Err(failure) => {
                    warn!(
                        block_id = %block_id,
                        turn_hash = %turn_hash_hex,
                        class = ?failure.class,
                        error = %failure.error,
                        "exact FNSP-v3 finalized turn refused during typed locked snapshot preparation"
                    );
                    return exact_failure_outcome(&s, block_id, turn_data, computed_hash, failure);
                }
            };
            drop(s);
            return match execute_live_exact_fnsp_v3(state, handle, preparation, finality_round)
                .await
            {
                Ok((durable_ordinal, receipt_stream_root)) => {
                    FinalizedExecutionOutcome::Committed {
                        block_id,
                        durable_ordinal,
                        receipt_stream_root,
                    }
                }
                Err(failure) => {
                    warn!(block_id = %block_id, turn_hash = %turn_hash_hex,
                        class = ?failure.class, error = %failure.error,
                        "exact FNSP-v3 finalized turn reached a typed terminal disposition");
                    let s = state.read().await;
                    exact_failure_outcome(&s, block_id, turn_data, computed_hash, failure)
                }
            };
        }
        None => {
            // Exact activation is a one-way flag day for NoteSpend state.  A v2 spend after it
            // would advance the faithful accumulator without the exact prefix and make the next
            // exact frame detect the divergence only after it was durable.
            if !finalized_note_spends(&signed_turn.turn.call_forest).is_empty() {
                match s.store.exact_fnsp_v3_live_authority() {
                    Ok(Some(_)) => {
                        let outcome = persist_finalized_payload_rejection(
                            &s,
                            block_id,
                            turn_data,
                            Some(computed_hash),
                            "legacy-spend-after-exact-cutover",
                        );
                        warn!(
                            block_id = %block_id,
                            turn_hash = %turn_hash_hex,
                            "legacy/v2 NoteSpend refused after exact FNSP-v3 activation"
                        );
                        return outcome;
                    }
                    Ok(None) => {}
                    Err(error) => {
                        error!(
                            block_id = %block_id,
                            turn_hash = %turn_hash_hex,
                            error = %error,
                            "could not authenticate exact cutover before legacy NoteSpend dispatch"
                        );
                        return FinalizedExecutionOutcome::FatalIntegrity {
                            block_id,
                            error: format!("exact cutover authority malformed: {error}"),
                        };
                    }
                }
            }
        }
    }

    // HISTORICAL NOTE-ROOT ADMISSION: the signed effect carries a strict FNSP
    // envelope whose height selects one exact faithful-eight root. Re-authenticate
    // and replay the sealed local history before accepting that pair. A canonical
    // root with no authenticated row is not enough; wrong height, sibling root,
    // truncation, fork, bad hybrid signature, and legacy unversioned proof bytes
    // all refuse before ledger or executor state changes.
    let faithful_spend_claims = match finalized_faithful_spend_claims(&signed_turn.turn.call_forest)
    {
        Ok(claims) => claims,
        Err(()) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "faithful-note-spend-proof-required",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                "finalized NoteSpend lacks a canonical FNSP height carrier or faithful-eight root"
            );
            return outcome;
        }
    };
    if !faithful_spend_claims.is_empty() {
        let expected = match s.store.faithful_note_root_expectation() {
            Ok(Some(expected)) => expected,
            Ok(None) => {
                let outcome = persist_finalized_payload_rejection(
                    &s,
                    block_id,
                    turn_data,
                    Some(computed_hash),
                    "faithful-note-root-not-authenticated",
                );
                warn!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    "finalized NoteSpend names a root before an authenticated faithful history exists"
                );
                return outcome;
            }
            Err(e) => {
                error!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    error = %e,
                    "faithful note-root history seal is malformed; finalized NoteSpend refused"
                );
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("faithful note-root history malformed: {e}"),
                };
            }
        };
        let local_pk = s.cclerk.public_key();
        let local_seed = s.cclerk.gossip_signing_key().to_bytes();
        let (local_ml_dsa_pk, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&local_seed);
        let history = match s.store.load_faithful_note_root_history_hybrid(
            std::slice::from_ref(&local_pk),
            std::slice::from_ref(&local_ml_dsa_pk),
            1,
            expected,
        ) {
            Ok(history) => history,
            Err(e) => {
                error!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    error = %e,
                    "faithful note-root history failed exact hybrid replay; finalized NoteSpend refused"
                );
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("faithful note-root history replay failed: {e}"),
                };
            }
        };
        if let Some((height, root, _, _)) = faithful_spend_claims
            .iter()
            .copied()
            .find(|(height, root, _, _)| !faithful_history_contains_pair(&history, *height, *root))
        {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "faithful-note-root-not-authenticated",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                root_height = height,
                root = %dregg_types::hex_encode(root.as_bytes()),
                "finalized NoteSpend names a height/root pair absent from the authenticated faithful history"
            );
            return outcome;
        }
    }

    // SPENT-STATE ADMISSION: rebuild the executor's production nullifier set
    // from the durable `(nullifier, public value, append-seq)` records before
    // execution. A fresh per-turn executor must not begin from empty or a spend
    // accepted at height N becomes spendable again at N+1. The exact successor
    // root is computed now and later signed/welded with this carrying commit.
    let finalized_nullifier_spends = finalized_note_spends(&signed_turn.turn.call_forest);
    let durable_nullifier_records = match s.store.load_faithful_nullifier_records() {
        Ok(records) => records,
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "durable faithful nullifier accumulator is malformed; finalized turn refused before mutation"
            );
            return FinalizedExecutionOutcome::FatalIntegrity {
                block_id,
                error: format!("durable faithful nullifier state malformed: {e}"),
            };
        }
    };
    let durable_nullifier_set = match dregg_cell::nullifier_set::NullifierSet::from_records(
        durable_nullifier_records,
    ) {
        Ok(set) => set,
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "durable faithful nullifier accumulator reconstruction failed; finalized turn refused"
            );
            return FinalizedExecutionOutcome::FatalIntegrity {
                block_id,
                error: format!("faithful nullifier reconstruction failed: {e}"),
            };
        }
    };
    let durable_nullifier_root = durable_nullifier_set.root8().to_bytes32();
    let durable_commit_cursor = match s.store.commit_cursor() {
        Ok(cursor) => cursor,
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "could not capture the durable commit cursor before off-lock execution"
            );
            return FinalizedExecutionOutcome::RetryableOperational {
                block_id,
                error: format!("could not capture durable commit cursor: {e}"),
            };
        }
    };
    if faithful_spend_claims.len() != finalized_nullifier_spends.len() {
        let outcome = persist_finalized_payload_rejection(
            &s,
            block_id,
            turn_data,
            Some(computed_hash),
            "faithful-note-spend-claim-count-mismatch",
        );
        error!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            claims = faithful_spend_claims.len(),
            spends = finalized_nullifier_spends.len(),
            "faithful NoteSpend carrier/effect traversal produced different ordered lengths"
        );
        return outcome;
    }

    // Each carrier names the successor immediately after ITS spend in DFS/effect
    // order.  This is the same sequential pre-state the executor sees while it
    // applies a multi-input turn.  Comparing every carrier with only the final
    // batch root would make a two-spend turn impossible: the first insertion's
    // root is necessarily different from the second insertion's root.
    let (successor_nullifier_set, ordered_successors) = match planned_ordered_nullifier_successors(
        &durable_nullifier_set,
        &finalized_nullifier_spends,
    ) {
        Ok(plan) => plan,
        Err(nullifier) => {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "nullifier-already-spent",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                nullifier = %dregg_types::hex_encode(&nullifier),
                "finalized NoteSpend duplicates a durable or within-turn nullifier; refused before mutation"
            );
            return outcome;
        }
    };
    for ((spend, (height, _, claimed_successor, _)), step_successor) in finalized_nullifier_spends
        .iter()
        .zip(faithful_spend_claims.iter().copied())
        .zip(ordered_successors.iter())
    {
        if claimed_successor.to_bytes() != *step_successor {
            let outcome = persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "faithful-nullifier-successor-mismatch",
            );
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                root_height = height,
                nullifier = %dregg_types::hex_encode(&spend.nullifier),
                claimed_successor = %dregg_types::hex_encode(claimed_successor.as_bytes()),
                planned_successor = %dregg_types::hex_encode(step_successor),
                "faithful NoteSpend proof does not bind its exact ordered nullifier successor"
            );
            return outcome;
        }
    }
    let finalized_faithful_spends: Vec<dregg_persist::FinalizedFaithfulSpendInput> =
        finalized_nullifier_spends
            .iter()
            .zip(faithful_spend_claims.iter().copied())
            .map(
                |(
                    spend,
                    (root_height, historical_note_root, successor_nullifier_root, asset_type),
                )| {
                    dregg_persist::FinalizedFaithfulSpendInput {
                        root_height,
                        historical_note_root,
                        nullifier: spend.nullifier,
                        value: spend.value,
                        asset_type,
                        successor_nullifier_root,
                    }
                },
            )
            .collect();
    let planned_nullifier_root = successor_nullifier_set.root8().to_bytes32();
    *executor.note_nullifiers.lock().unwrap() = durable_nullifier_set;

    let agent = signed_turn.turn.agent;
    // Solo ingress may already have applied and logged this exact turn; retain
    // that idempotent finality-bookkeeping case. Every genuinely new finalized
    // turn must name the independently stored head for its own agent.
    let staged_solo_receipt = if s.solo_consensus.as_ref().is_some_and(|sc| sc.is_solo) {
        // The old solo ingress could durably append a receipt before the
        // finalized ledger/faithful commit.  Its global log index is required
        // for byte-exact recovery; the agent projection deliberately discards
        // that position.  Do NOT infer that the ledger was applied merely from
        // this receipt: after a crash RAM is pre-turn while the receipt survives.
        s.cclerk
            .receipt_log()
            .iter()
            .enumerate()
            .find(|(_, receipt)| receipt.agent == agent && receipt.turn_hash == computed_hash)
            .and_then(|(index, receipt)| {
                u64::try_from(index)
                    .ok()
                    .map(|index| (index, receipt.clone()))
            })
    } else {
        None
    };
    let expected_prev = staged_solo_receipt
        .as_ref()
        .map(|(_, receipt)| receipt.previous_receipt_hash)
        .unwrap_or_else(|| s.cclerk.agent_receipt_head_hash(&agent));
    if signed_turn.turn.previous_receipt_hash != expected_prev {
        let outcome = persist_finalized_payload_rejection(
            &s,
            block_id,
            turn_data,
            Some(computed_hash),
            "receipt-chain-mismatch",
        );
        warn!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            expected = ?expected_prev,
            got = ?signed_turn.turn.previous_receipt_hash,
            "finalized SignedTurn failed agent-scoped receipt continuity before mutation (deterministic rejection recorded)"
        );
        return outcome;
    }

    // ⚑ AND THE EXEMPTION ABOVE HAD NO EFFECT, BECAUSE THE EXECUTOR RE-DECIDES IT.
    //
    // `configure_turn_executor` seeds `TurnExecutor::last_receipt_hash` from the WHOLE durable
    // receipt log (`executor_state_admission::restore_executor_receipt_heads`), so when the crash
    // image this branch exists for is present — the ingress receipt for THIS turn durable, the
    // ledger mutation lost — the executor's seeded head for `agent` is the receipt we just found,
    // i.e. one link PAST the turn we are about to re-execute. `check_previous_receipt_hash` then
    // refuses with `ReceiptChainMismatch { expected: Some(<the staged receipt>), got: None }`, the
    // turn comes back `Rejected`, no attested root is written, and `latest_height` stays 0 — the
    // exact symptom `solo_finalization_recovers_receipt_durable_ledger_absent_crash` reports.
    // The `staged_solo_receipt` check above passed and then decided nothing.
    //
    // Rewind the seeded head to the staged receipt's OWN predecessor, so the re-execution sees the
    // identical chain state the original ingress saw and can reproduce the identical receipt. This
    // relaxes ONLY the chain-continuity leg, and only for a turn whose receipt is already in this
    // node's log at this exact `turn_hash`: the anti-replay authority is the actor cell's NONCE in
    // the authoritative ledger, which is untouched here. A genuine replay of an already-APPLIED
    // turn still meets a bumped nonce and is refused `NonceReplay`; only the crash image (ledger
    // pre-turn, receipt durable) proceeds, which is precisely the case this arm names.
    if let Some((_, staged)) = staged_solo_receipt.as_ref() {
        let mut heads = executor
            .last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        match staged.previous_receipt_hash {
            Some(prev) => {
                heads.insert(agent, prev);
            }
            None => {
                heads.remove(&agent);
            }
        }
    }

    // boundary-P1 (bug 1): plumb the NODE-fed admission context onto the per-turn executor so the
    // verified Lean shadow's clock / chain-head / budget legs are decided by THIS node's own state
    // (not the turn). `TurnExecutor::execute` reads these (`get_last_receipt_hash` / `budget_gate`
    // / `cell_migrations`) to build the `ShadowHostCtx`; without seeding they default to genesis /
    // no-gate (the diagnostic stub). Production overrides:
    //   * stored receipt-chain HEAD — the node's authoritative per-agent head from
    //     the immutable receipt log. The verified ChainHead leg checks the turn's
    //     claimed `prev` against that state for local and foreign agents alike;
    //     neither the wire claim nor the global observation-log tip is authority.
    //   * silo BUDGET slice — the agent's Stingray bounded-counter remaining slice for this silo;
    //     the verified Budget leg rejects `fee > budget`.
    {
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

    // Finalization is now the sole authoritative application in solo and
    // committee modes alike.  A historical durable solo receipt is recovery
    // input, never evidence that the RAM-only ledger mutation survived a crash.

    // FLOW-B ROTATION: capture the actor cell's FULL pre-execution `Cell` (the real
    // RecordKernelState the rotation producer reads — balance/nonce/fields/c-list/lifecycle/
    // heap_root/authority), so the live node turn can prove ROTATED. Cloned BEFORE
    // `execute_via_producer` mutates the ledger; the post-state cell is read after execution.
    //
    // This is the pre-state the EXECUTOR sees, which on a first turn is the
    // claimed actor cell, not the live ledger's (absent / zero-pk stub) image.
    // The proof binds `old_commit` to it, so reading the un-claimed live cell
    // here would bind a transition the executor never took.
    let full_turn_pre_cell: Option<dregg_cell::Cell> = if s.full_turn_proving_enabled {
        claimed_actor_cell
            .clone()
            .or_else(|| s.ledger.get(&signed_turn.turn.agent).cloned())
    } else {
        None
    };

    // Full-turn proving (commit-path): capture the actor cell's pre-execution
    // state BEFORE the executor mutates the ledger. The full-turn proof binds
    // `old_commit` to this pre-state; capturing it after execution would let a
    // forged transition pass. Only collected when proving is enabled (devnet).
    let full_turn_pre_state: Option<(u64, u64)> = if s.full_turn_proving_enabled {
        // THE EPOCH: balances are SIGNED (i64); the full-turn VM pre-state is
        // u64. The actor is an ORDINARY cell (non-negative) on the proving
        // path — checked conversion, never an `as` cast that wraps negatives.
        full_turn_pre_cell
            .as_ref()
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
        full_turn_pre_cell
            .as_ref()
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
    // carried over consensus), so the landing site is materialized locally by
    // `provision_transfer_destinations`.
    //
    // ⚑ THAT FUNCTION IS DETERMINISTIC IN (TURN, PRE-STATE) — NOT IN THE TURN ALONE.
    // This paragraph said "driven SOLELY by the finalized turn's data … every node
    // inserts the IDENTICAL zero-balance stub" until 2026-08-06, and the code has
    // read the SOURCE cell out of the LOCAL LEDGER since the stub gained an asset:
    // a Transfer is a single-asset move, so a landing site minted in any other
    // asset is refused by the executor's own same-asset guard. The uniformity
    // argument never needed the stronger claim — the executor consumes exactly the
    // same pair, so nodes agreeing on the pre-state provision AND execute
    // identically, while a node that disagrees was already going to compute a
    // different post-state. `provision_transfer_destinations` carries the
    // absent-source case and names the two-node test that drives it.
    //
    // This is what makes the finalized application uniform —
    // not "the submitter created it out of band and peers approximate it" (which
    // would leave divergent cell content the attested root cannot see, since
    // `dregg_persist::canonical_ledger_root` hashes `postcard(cell)` — the WHOLE
    // cell, public key and `pq_identity` included — so a divergent provisioning
    // is an attested-root split, not merely invisible content). The submitter no longer
    // provisions authoritatively at faucet-submission time in multi-party mode
    // (see `api.rs`), so it reaches this same path and provisions identically.
    // THE SWAP — producer mode (authority inversion), now the DEFAULT — through the ONE
    // shared producer gate every ingress uses (`executor_setup::execute_via_producer`,
    // #171): finalized turns, thin-HTTP turns, and remote signed envelopes all execute
    // on the same authoritative state producer.
    let lean_producer_enabled = s.lean_producer_enabled;

    // The short-lived executor owns consensus state beyond the ledger. Capture
    // every sparse-snapshot/CAS predecessor before the isolated execution so
    // the store can compare the complete successor against the exact durable
    // image. A malformed live predecessor is an integrity failure, not a state
    // that may be silently reset by constructing the next executor.
    let executor_consensus_predecessors =
        match crate::executor_side_state_persistence::capture_executor_consensus_predecessors(
            &executor,
        ) {
            Ok(predecessors) => predecessors,
            Err(error) => {
                error!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    error = %error,
                    "could not capture executor consensus-state predecessors"
                );
                return FinalizedExecutionOutcome::FatalIntegrity { block_id, error };
            }
        };
    let signal_head_revalidation = signal_head_snapshot
        .as_ref()
        .map(|head| (head.authority_id(), head.digest()));
    let signal_evaluation_plan = signal_head_snapshot
        .zip(signal_slot_snapshot)
        .zip(signal_claim)
        .map(|((head, slot), claim)| (head, slot, s.federation_id, signed_turn.signer.0, claim));

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
        // THE PRE-EXECUTION LEDGER SHAPE, on the isolated candidate — and it is
        // the SAME function every ingress's admission staging run applies
        // (`signed_turn_validation::install_pre_execution_state`), which is the
        // point: "what the ledger must look like before this turn runs" now has
        // one definition, so a staging run cannot silently predict a verdict
        // against a ledger this path will never produce. Two ingresses did
        // exactly that by omitting the provisioning half.
        //
        // [1] THE FIRST-TURN CLAIM. It was DECIDED before the admission
        // predicate (which could not have passed otherwise) and is APPLIED here,
        // so the authoritative ledger carries it only through the post-durability
        // overlay. There is still exactly one claim, computed once, by
        // `claimed_actor_cell`; what moved is where it lands. `pre_ledger` was
        // cloned before this install, so the actor is in the pre→post diff and
        // therefore in the commit record's `touched_cells` whether or not
        // execution touches it again — which is what makes the durable image and
        // live RAM agree on a first turn.
        //
        // [2] TRANSFER DESTINATIONS — the stub every node with the same pre-state
        // inserts (deterministic in (turn, pre-state), NOT in the turn alone: the
        // asset comes from the source cell). The pre→post diff below classifies
        // each provisioned+credited destination as a created cell, so the overlay
        // installs it on the authoritative ledger.
        crate::signed_turn_validation::install_pre_execution_state(
            &mut exec_ledger,
            claimed_actor_cell,
            &turn_for_exec.call_forest,
        );
        let result = crate::executor_setup::execute_via_producer(
            &executor,
            &turn_for_exec,
            &mut exec_ledger,
            lean_producer_enabled,
        );

        // Resolve this real finalized receipt on the retained executor, which
        // is the one consensus owner of pending turns. The event cascade stays
        // candidate-local until the carrying redb transaction returns Fresh.
        // Rejected/expired/pending candidates resolve nothing.
        let resolution_events = match &result {
            dregg_turn::TurnResult::Committed { receipt, .. } => {
                if receipt.turn_hash != computed_hash {
                    return Err(
                        "executor receipt turn hash differs from the finalized SignedTurn"
                            .to_string(),
                    );
                }
                executor.resolve_pending_receipt(receipt.turn_hash, receipt.clone())
            }
            _ => Vec::new(),
        };
        // Signal authority is evaluated only for a body-committed executor
        // candidate, because `actor_root` is the receipt's AIR-bound
        // `pre_state_hash`. The signer identity is the outer SignedTurn key
        // captured above, never `turn.agent`. This remains candidate-local and
        // joins the carrying turn only at the redb apex.
        let poa_signal_evaluation = match (&result, signal_evaluation_plan) {
            (
                dregg_turn::TurnResult::Committed { receipt, .. },
                Some((head, slot, federation_id, player_key, claim)),
            ) => Some(crate::poa_signal_adapter::evaluate_persisted_signal_claim(
                &head,
                &slot,
                federation_id,
                player_key,
                receipt.pre_state_hash,
                claim,
            )),
            _ => None,
        };
        // NULLIFIER-ROOT (VK-epoch ghost mirror): capture the executor's LIVE nullifier-accumulator
        // frontier AFTER execution — the native `CanonicalHeapTree8` root over its (nf, value)
        // `note_nullifiers` map. Captured HERE (the executor is consumed by this blocking task) and
        // returned so the rotated producer can bind the committed `nullifier_root` (limbs [26,67..73])
        // to the node's REAL spent-note frontier instead of a hardcoded default.
        let live_nullifier_root = executor.note_nullifiers.lock().unwrap().root8();
        // COMMITMENTS-ROOT (VK-epoch ghost mirror, CREATE dual): capture the executor's LIVE
        // commitments-accumulator frontier — the native `CanonicalHeapTree8` root over its
        // (commitment, value) `note_commitments` map — so the rotated producer binds the committed
        // `commitments_root` (limbs [27,74..80]) to the node's REAL created-note frontier.
        let live_commitments_root = executor.note_commitments.lock().unwrap().root8();
        // Capture the COMPLETE post-execution executor image only after receipt
        // resolution. This includes accumulators, sparse rate/factory images,
        // the canonical pending registry, and the dedicated React replay set.
        let executor_state =
            crate::executor_side_state_persistence::capture_finalized_executor_consensus_state(
                &executor,
                &executor_consensus_predecessors,
            )?;
        Ok::<_, String>((
            result,
            exec_ledger,
            live_nullifier_root,
            live_commitments_root,
            executor_state,
            resolution_events,
            poa_signal_evaluation,
        ))
    });
    let (
        exec_result,
        exec_ledger,
        live_nullifier_root,
        live_commitments_root,
        mut executor_state,
        resolution_events,
        poa_signal_evaluation,
    ) = match exec_join.await {
        Ok(Ok(v)) => v,
        Ok(Err(error)) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %error,
                "finalized-turn executor consensus-state capture failed closed"
            );
            return FinalizedExecutionOutcome::FatalIntegrity { block_id, error };
        }
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "finalized-turn EXECUTION task panicked/cancelled; turn NOT applied"
            );
            return FinalizedExecutionOutcome::FatalIntegrity {
                block_id,
                error: format!("durable nullifier reconstruction failed: {e}"),
            };
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

    // Re-acquire the global write lock BRIEFLY to validate the snapshot and stage
    // the durable commit.  Crucially, the candidate ledger is still isolated:
    // no cell, receipt, pending resolution, artifact, or event becomes live until
    // the finalized record has crossed the single durable commit boundary below.
    let mut s = state.write().await;

    // GLOBAL concurrency guard. The per-cell diff below cannot observe a
    // disjoint-agent turn advancing the node-wide nullifier accumulator while
    // the verified executor ran off-lock. Re-read both the commit cursor and
    // the exact durable accumulator before changing RAM; on any drift, abandon
    // this stale result so recovery/replay executes it against the new frontier.
    let current_commit_cursor = match s.store.commit_cursor() {
        Ok(cursor) => cursor,
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "could not revalidate the durable commit cursor after off-lock execution"
            );
            return FinalizedExecutionOutcome::RetryableOperational {
                block_id,
                error: format!("durable commit cursor read failed: {e}"),
            };
        }
    };
    let current_nullifier_root = match s
        .store
        .load_faithful_nullifier_records()
        .map_err(|error| error.to_string())
        .and_then(|records| {
            dregg_cell::nullifier_set::NullifierSet::from_records(records)
                .map_err(|error| error.to_string())
        }) {
        Ok(set) => set.root8().to_bytes32(),
        Err(e) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "could not reconstruct the durable exact nullifier root after off-lock execution"
            );
            return FinalizedExecutionOutcome::FatalIntegrity {
                block_id,
                error: format!("durable nullifier reconstruction failed: {e}"),
            };
        }
    };
    if !finalized_global_snapshot_matches(
        durable_commit_cursor,
        durable_nullifier_root,
        current_commit_cursor,
        current_nullifier_root,
    ) {
        warn!(
            block_id = %block_id,
            turn_hash = %turn_hash_hex,
            expected_cursor = durable_commit_cursor,
            current_cursor = current_commit_cursor,
            expected_nullifier_root = %dregg_types::hex_encode(&durable_nullifier_root),
            current_nullifier_root = %dregg_types::hex_encode(&current_nullifier_root),
            "global finalized frontier changed during off-lock execution; stale result refused before RAM overlay"
        );
        return FinalizedExecutionOutcome::RetryableOperational {
            block_id,
            error: "global finalized frontier moved during off-lock execution".into(),
        };
    }

    // Galley action tokens are head-scoped. The first native preflight made an
    // already-stale payload deterministic; this second mint closes the off-lock
    // execution window. Any world/head/token movement is retryable because the
    // action was valid at the earlier finalized snapshot, while equality lets
    // the same-writer apex perform the final authoritative check.
    if let Some(expected) = galley_preflight.as_ref() {
        match s
            .store
            .preflight_active_poa_galley_public_perform_v1(&signed_turn)
        {
            Ok(current) if &current == expected => {}
            Ok(_) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: "PoA Galley world or stream head moved during off-lock execution"
                        .into(),
                };
            }
            Err(
                dregg_persist::poa_galley_authority::PoaGalleyPublicPerformPreflightErrorV1::StaleAction(
                    _,
                ),
            ) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: "PoA Galley action expired during off-lock execution".into(),
                };
            }
            Err(
                dregg_persist::poa_galley_authority::PoaGalleyPublicPerformPreflightErrorV1::AuthorityUnavailable(
                    error,
                ),
            ) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("could not revalidate PoA Galley head: {error}"),
                };
            }
        }
    }

    // The judge ran against an owned persisted-head snapshot while the state
    // lock was released. Re-read that exact CAS token before interpreting its
    // verdict. A concurrent Signal finalization is retryable; accepting or
    // terminally rejecting against its stale predecessor would fork the game
    // history even though the generic ledger snapshot remained conflict-free.
    if let Some((authority_id, expected_head_digest)) = signal_head_revalidation {
        match s.store.load_poa_signal_head(authority_id) {
            Ok(Some(current)) if current.digest() == expected_head_digest => {}
            Ok(Some(_)) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: "PoA Signal authority head moved during off-lock evaluation".into(),
                };
            }
            Ok(None) => {
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: "PoA Signal authority head vanished during evaluation".into(),
                };
            }
            Err(dregg_persist::StoreError::Database(error)) => {
                return FinalizedExecutionOutcome::RetryableOperational {
                    block_id,
                    error: format!("could not revalidate PoA Signal head: {error}"),
                };
            }
            Err(error) => {
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: format!("PoA Signal head revalidation failed: {error}"),
                };
            }
        }
    }
    let poa_signal_transition = match poa_signal_evaluation {
        None => None,
        Some(Ok(candidate)) => Some(candidate),
        Some(Err(crate::poa_signal_adapter::SignalAdapterError::LeanTransport(error))) => {
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %error,
                "PoA Signal Lean judge unavailable; finalized identity remains pending without ACK"
            );
            return FinalizedExecutionOutcome::RetryableOperational {
                block_id,
                error: format!("PoA Signal Lean judge unavailable: {error}"),
            };
        }
        Some(Err(error))
            if matches!(
                &error,
                crate::poa_signal_adapter::SignalAdapterError::LeanRejected
                    | crate::poa_signal_adapter::SignalAdapterError::MissionMismatch { .. }
            ) =>
        {
            warn!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %error,
                "PoA Signal semantics refused the finalized claim; isolated executor candidate discarded"
            );
            return persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "poa-signal-semantic-rejected",
            );
        }
        Some(Err(error)) => {
            error!(
                block_id = %block_id,
                turn_hash = %turn_hash_hex,
                error = %error,
                "PoA Signal persisted authority or Lean output failed strict binding"
            );
            return FinalizedExecutionOutcome::FatalIntegrity {
                block_id,
                error: format!("PoA Signal authority/output integrity failure: {error}"),
            };
        }
    };

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
        return FinalizedExecutionOutcome::RetryableOperational {
            block_id,
            error: "ledger snapshot moved during off-lock execution".into(),
        };
    }

    match exec_result {
        dregg_turn::TurnResult::Committed {
            receipt: reexecuted_receipt,
            ..
        } => {
            // Crash recovery for the former solo ingress split: a receipt may
            // already be durable while its RAM-only ledger mutation was lost.
            // Re-execution above is authoritative.  Reuse the immutable staged
            // receipt only after proving it describes this exact transition and
            // is genuinely signed by this node; otherwise refuse before the
            // faithful commit can bless unrelated bytes.
            let (receipt, receipt_log_index, receipt_already_in_log) = if let Some((
                index,
                staged,
            )) =
                staged_solo_receipt.as_ref()
            {
                if !staged_receipt_matches_reexecution(staged, &reexecuted_receipt) {
                    error!(
                        block_id = %block_id,
                        turn_hash = %turn_hash_hex,
                        receipt_index = *index,
                        "durable staged solo receipt does not describe the exact re-executed transition; refusing finalization"
                    );
                    return FinalizedExecutionOutcome::FatalIntegrity {
                        block_id,
                        error: "durable staged receipt disagrees with re-execution".into(),
                    };
                }
                if let Err(error) = dregg_turn::verify_receipt_signature_with_keys(
                    staged,
                    &[s.cclerk.public_key().0],
                ) {
                    error!(
                        block_id = %block_id,
                        turn_hash = %turn_hash_hex,
                        receipt_index = *index,
                        error = ?error,
                        "durable staged solo receipt has no valid local executor signature; refusing finalization"
                    );
                    return FinalizedExecutionOutcome::FatalIntegrity {
                        block_id,
                        error: format!("durable staged receipt signature invalid: {error:?}"),
                    };
                }
                (staged.clone(), *index, true)
            } else {
                let index = s.cclerk.receipt_log_next_index();
                s.cclerk
                    .validate_receipt_append(&reexecuted_receipt)
                    .expect("finalized executor receipt must match the prechecked agent head");
                (reexecuted_receipt, index, false)
            };

            let receipt_hash_hex: String = receipt
                .turn_hash
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();

            // Collect note commitments from NoteCreate effects. Bug #58: the
            // DURABLE append is DEFERRED and WELDED into the crash-consistent
            // commit transaction below (`commit_finalized_turn_with_notes`), so
            // the note leaf and the turn record land in ONE fsync boundary —
            // exactly-once across a crash. Appending here (in its own redb txn,
            // hundreds of lines before the atomic barrier) is what let a crash
            // leave the note leaf durable without the turn record, so recovery
            // re-applied the turn and appended the SAME commitment a second time
            // (a permanent double leaf, since the boot path rebuilds the tree
            // from the durable table). The in-RAM Poseidon2 tree is advanced only
            // AFTER durable success, in the commit block below.
            let note_commitments = finalized_note_commitments(&signed_turn.turn.call_forest);

            // Reserve and validate the immutable global-log slot while the
            // node-state lock excludes every other append.  The exact encoded
            // receipt is welded into the finalized commit transaction below;
            // in-memory indices advance only after that transaction succeeds.
            // A durable replay never reaches this point: recovery restores both
            // the welded receipt and the executed-block cursor atomically, and
            // an anomalous direct re-entry is refused by the pre-mutation
            // predecessor check above (the restored head is already this turn).
            let encoded_receipt =
                postcard::to_stdvec(&receipt).expect("TurnReceipt postcard encoding is infallible");

            // TYPED EFFECT ENRICHMENT on the CONSENSUS commit path — the same
            // `transfer`/`balance`/`granted` facts the direct-submit path records
            // (`api.rs`, `push_committed_event_enriched`). Without this a turn
            // finalized through blocklace consensus lands in the receipt index with
            // NO typed effects, so every reader of `/api/receipts/index/range` — the
            // light-client verified reads that parse `Granted` facts (e.g. an
            // execution-lease grant) — sees an empty log on a FEDERATED node while
            // working on a solo one. Additive; never gates the commit.
            // Prepare the activity payload from the isolated candidate. Publishing
            // it now would expose a committed-looking event even if redb rejects
            // the finalized record, so the actual feed mutation happens only in
            // the durable-success arm below.
            let activity_summaries =
                crate::api::summarize_turn_effects(&signed_turn.turn, &pre_ledger, &exec_ledger);
            let activity_kinds: Vec<String> = signed_turn
                .turn
                .call_forest
                .iter_dfs()
                .flat_map(|t| t.action.effects.iter().map(crate::api::effect_kind))
                .collect();
            let activity_kinds = if activity_kinds.is_empty() {
                vec!["turn_committed".to_string()]
            } else {
                activity_kinds
            };
            let activity_agent_hex = dregg_types::hex_encode(signed_turn.turn.agent.as_bytes());

            // ── Full-turn proving (commit path) ──────────────────────────
            // When enabled (devnet), prove every body-committed candidate; the
            // bytes are published only after the durable barrier below. The
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
            //    the canonical spent set is threaded to the IN-CIRCUIT limb-26
            //    grow-gate and the canonical-set-derived OLD commit is pinned, so
            //    the no-double-spend binding FIRES (felt-width #11 fold-in).
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
            //
            // ⚑ THE DISPOSITION IS CARRIED, NOT JUST THE ARTIFACTS. The second
            // element is `Some(reason)` exactly when proving/verification FAILED —
            // as opposed to being disabled, not applicable, or deliberately
            // withheld. Those four were all represented as `None` and published to
            // observers as `ProofPending`, so "the proof for this finalized turn
            // did not verify" was indistinguishable from "the proof is in flight",
            // forever, on every surface except the log.
            //
            // ⚑ AND THE PROVEN 8-FELT ANCHOR PAIR RIDES WITH THEM (third element). Without it no
            // surface outside this function ever held the values `verify_full_turn_bound` takes as
            // `expected_old_commit` / `expected_new_commit`, so the only production re-verifier
            // read them out of the artifact and compared each against itself. See
            // `turn_proving::turn_proof_anchors_config_key`.
            let (full_turn_proof_artifacts, full_turn_proof_failure): (
                Option<(Vec<u8>, Option<Vec<u8>>, [u8; 64])>,
                Option<String>,
            ) = if let Some((pre_balance, pre_nonce)) = full_turn_pre_state {
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
                // The bearer witness (a `BearerSignedDelegation` consumed-cap
                // witness whose holder is the delegator, NOT merely one whose
                // holder differs from the actor — see `bearer_consumed_cap`) +
                // the node-derived pre-state cap root of its delegator. The
                // actor path takes precedence (a turn holding its own cap proves
                // over its own root); only when there is NO actor-held witness do
                // we route a bearer witness through the delegator-bound
                // authority leg.
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
                    full_turn_delegator_cap_roots
                        .get(&w.holder)
                        .map(|root| (w, *root))
                });
                // ── THE BEARER-AUTHORITY DISPOSITION (see `bearer_authority_disposition`) ──
                // This arm used to `warn!` "proving WITHOUT the AUTHORITY leg (v1 fallback)" and
                // carry on, publishing a proof that omits the binding it names. That is the
                // fail-OPEN class at its ATTESTATION flavour: nothing downstream ever demands the
                // leg back (`verify_full_turn` hardcodes `expected_cap_membership: None` and no
                // consumer in the tree constructs a `CapMembershipExpectation`), so the omission is
                // unnoticeable — the proof simply claims less than it appears to.
                //
                // It REFUSES now: no proof at all beats an attestation the prover knows is
                // incomplete. The turn still COMMITS (the executor enforced the delegation
                // independently), and `DREGG_ALLOW_UNBOUND_BEARER_PROOF=1` is the declared,
                // REQUIRE_LEAN-revocable escape for a node that wants the partial attestation.
                let bearer_authority_refusal = bearer_authority_disposition(
                    bearer_cap_witness.as_ref().map(|(_, root)| root),
                    bearer_cap.is_some(),
                    allow_unbound_bearer_proof(),
                    require_verified_lean_gate(),
                )
                .err();
                if let Some(refusal) = bearer_authority_refusal {
                    crate::metrics::inc_bearer_authority_leg_refusals();
                    warn!(
                        turn_hash = %turn_hash_hex,
                        refusal = %refusal,
                        holder = ?bearer_cap.map(|w| w.holder),
                        "bearer-delegated turn: delegator pre-state cap root unavailable (no \
                         resolvable delegator cell) — FAILING CLOSED: NO full-turn proof is \
                         published for this turn, rather than a v1 proof missing the AUTHORITY \
                         binding. The turn still commits; the executor already enforced the \
                         delegation (signature, delegator-holds-the-cap, non-amplification). Set \
                         DREGG_ALLOW_UNBOUND_BEARER_PROOF=1 to deliberately publish the partial \
                         attestation."
                    );
                }
                // `live_nullifier_root` (captured from the executor's post-execution `note_nullifiers`
                // frontier, returned by the blocking exec task above) threads the node's REAL
                // spent-note frontier into the rotated commit-path arms below.
                let proving_result = if bearer_authority_refusal.is_some() {
                    Err(crate::turn_proving::FullTurnProvingError::BearerAuthorityLegUnbindable)
                } else {
                    match (
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
                                exec_ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_capability_with_root(
                                        pre_balance,
                                        pre_nonce,
                                        full_turn_pre_cap_root,
                                        before_cell,
                                        after_cell,
                                        &receipt_hashes,
                                        &effects,
                                        &live_nullifier_root,
                                        &live_commitments_root,
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
                                    exec_ledger.get(&signed_turn.turn.agent),
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
                                exec_ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_self_sovereign_with_root(
                                    pre_balance,
                                    pre_nonce,
                                    before_cell,
                                    after_cell,
                                    &receipt_hashes,
                                    &effects,
                                    &live_nullifier_root,
                                    &live_commitments_root,
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
                                    exec_ledger.get(&signed_turn.turn.agent),
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
                                exec_ledger.get(&signed_turn.turn.agent),
                            ) {
                                (Some(before_cell), Some(after_cell)) => {
                                    let receipt_hashes = [receipt.receipt_hash()];
                                    crate::turn_proving::rotation_witness_for_self_sovereign_with_root(
                                    pre_balance,
                                    pre_nonce,
                                    before_cell,
                                    after_cell,
                                    &receipt_hashes,
                                    &effects,
                                    &live_nullifier_root,
                                    &live_commitments_root,
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
                    }
                };
                let is_spend = !spent_nullifiers.is_empty();
                match proving_result {
                    Ok(proven) => {
                        let proof_bytes = proven.proof_bytes().to_vec();
                        // ── FINALIZED-TURN RETENTION (the REAL IVC-compression input) ──
                        // Mint the wrap-input `FinalizedTurn` from the SAME execution
                        // context this proof was generated from, bound FAIL-CLOSED to the
                        // proof's proven wide anchors (`finalized_turn_from_full_turn`'s
                        // anchor tie), and persist it keyed by turn hash.
                        // `dregg_compress_history` folds EXACTLY these retained turns
                        // through `ivc_turn_chain::prove_turn_chain_recursive`. A turn
                        // that cannot be faithfully minted is NOT retained — never a
                        // fabricated stand-in — and history compression then refuses it.
                        let retained_turn = match (
                            full_turn_pre_cell.as_ref(),
                            exec_ledger.get(&signed_turn.turn.agent),
                        ) {
                            (Some(before_cell), Some(after_cell)) => {
                                let receipt_hashes = [receipt.receipt_hash()];
                                match crate::turn_proving::mint_and_encode_finalized_turn(
                                    &signed_turn.turn.agent,
                                    pre_balance,
                                    pre_nonce,
                                    &effects,
                                    before_cell,
                                    after_cell,
                                    &receipt_hashes,
                                    &live_nullifier_root,
                                    &live_commitments_root,
                                    proven.old_commit,
                                    proven.new_commit,
                                ) {
                                    Ok(turn_bytes) => Some(turn_bytes),
                                    Err(e) => {
                                        warn!(
                                            turn_hash = %turn_hash_hex,
                                            error = %e,
                                            "finalized turn NOT retained for IVC compression \
                                             (fail-closed; history compression will refuse this turn)"
                                        );
                                        None
                                    }
                                }
                            }
                            _ => {
                                warn!(
                                    turn_hash = %turn_hash_hex,
                                    "finalized turn NOT retained for IVC compression: before/after \
                                     actor cell context unavailable on this commit path (fail-closed)"
                                );
                                None
                            }
                        };
                        info!(
                            turn_hash = %turn_hash_hex,
                            block_id = %block_id,
                            proof_bytes = proof_bytes.len(),
                            old_commit = ?proven.old_commit,
                            new_commit = ?proven.new_commit,
                            spend = is_spend,
                            freshness_bound = is_spend,
                            "full-turn proof generated and verified for finalized candidate; \
                             spend turns are FRESHNESS-bound in-circuit to the canonical spent set"
                        );
                        // Proof/retention bytes are intentionally only prepared
                        // here. Their store keys are published after the finalized
                        // commit succeeds, so a rejected durable record leaves no
                        // orphan proof that looks accepted.
                        //
                        // ⚑ THE PROVEN ANCHOR PAIR, captured at the ONE place it exists. These are
                        // the felts `prove_and_verify_finalized_turn*` re-derived generate-only
                        // from the trusted pre-state + effects (`wide_commit_anchors`) and then
                        // gated the proof on via `verify_full_turn_bound` — so persisting them is
                        // persisting a check that already ran, not a new claim. `/api/turn/{h}/
                        // anchor` serves them so a stranger's `expected_old_commit` stops being a
                        // value read out of the artifact it is meant to judge.
                        let proven_anchors = dregg_circuit::commit8_wire::commit8_pair_to_bytes(
                            &proven.old_commit,
                            &proven.new_commit,
                        );
                        (Some((proof_bytes, retained_turn, proven_anchors)), None)
                    }
                    Err(
                        crate::turn_proving::FullTurnProvingError::RevocationCapacityExceeded {
                            have,
                            max,
                        },
                    ) => {
                        // KNOWN LIMITATION (not a soundness failure): the canonical
                        // nullifier set outgrew the openable heap tree
                        // (`MAX_REVOCATION_TREE_ENTRIES`, 65535 entries).
                        // We do not silently truncate the set (that could hide a
                        // double-spend), so the spend turn carries no freshness-bound
                        // proof.
                        warn!(
                            turn_hash = %turn_hash_hex,
                            block_id = %block_id,
                            have,
                            max,
                            "spend candidate NOT freshness-proven: canonical nullifier set exceeds \
                             the openable heap tree capacity"
                        );
                        // WITHHELD, not failed: nothing was proven wrong.
                        (None, None)
                    }
                    Err(
                        crate::turn_proving::FullTurnProvingError::BearerAuthorityLegUnbindable,
                    ) => {
                        // THE FAIL-CLOSED DISPOSITION FIRED (already warned + metered above, where
                        // the delegator lookup missed). Not an error!-level soundness event: no
                        // proof failed to verify and the turn is not invalid — the AUTHORITY leg was
                        // unbuildable, so the attestation is WITHHELD rather than under-claimed.
                        // Given its own arm so it can never be laundered into the `error!` below,
                        // which says "proof generation/verification FAILED" about a turn where
                        // neither happened.
                        debug!(
                            turn_hash = %turn_hash_hex,
                            block_id = %block_id,
                            "no full-turn proof published: bearer AUTHORITY leg unbindable \
                             (fail-closed disposition)"
                        );
                        // WITHHELD, not failed: the authority leg was unbuildable.
                        (None, None)
                    }
                    Err(e) => {
                        // SOUNDNESS: a body-committed candidate whose full-turn proof
                        // does not verify is a serious event. We surface it
                        // loudly and refuse to attach an unverified proof.
                        //
                        // ⚑ AND THE TURN STILL COMMITS. That is a GENUINE DESIGN
                        // FORK and it is deliberately NOT decided here:
                        //
                        //   (a) COMMIT UNPROVEN (what this code does). Consensus
                        //       already ORDERED this turn; every other node will
                        //       apply it. Refusing locally does not un-finalize it,
                        //       it only makes THIS node diverge from the committee's
                        //       state — and since the proving failure is
                        //       deterministic, the node would refuse the same turn
                        //       on every retry, i.e. HALT at this height forever.
                        //       The state transition itself was still validated by
                        //       the executor; what is missing is the succinct
                        //       attestation of it.
                        //   (b) REFUSE THE DURABLE COMMIT (return
                        //       `FinalizedExecutionOutcome::RetryableOperational`,
                        //       exactly as the malformed-note-root arm below does).
                        //       This keeps "every finalized state transition on this
                        //       node is proven" TRUE by construction, at the cost of
                        //       a wedge that an operator must clear by hand.
                        //
                        // Which one is right depends on what a dregg node is FOR —
                        // a liveness-first validator or a proof-carrying archive —
                        // and that is the operator's call, not a lane's.
                        //
                        // What is NOT a fork, and is closed here: the failure used
                        // to leave no trace but this line. The turn was published to
                        // every observer as `ProofPending`, and `full_turn_proof:{h}`
                        // was simply absent — the same shape as proving being turned
                        // off. It is now recorded durably under
                        // `full_turn_proof_failed:{h}` and reported as
                        // `ProofGenerationFailed`, so option (a) is at least an
                        // AUDITABLE choice rather than an invisible one.
                        error!(
                            turn_hash = %turn_hash_hex,
                            block_id = %block_id,
                            error = %e,
                            spend = is_spend,
                            "full-turn proof generation/verification FAILED for candidate; \
                             no verified proof will be published, and the finalized turn \
                             COMMITS UNPROVEN (recorded under full_turn_proof_failed:*)"
                        );
                        (None, Some(e.to_string()))
                    }
                }
            } else {
                (None, None)
            };

            // ── Lift TurnReceipt → FederationReceipt (audit F7) ──────────
            // We prepare the body-committed candidate's federation-shaped receipt
            // by hashing its post-state into the body and signing with the
            // local validator's Ed25519 key. In solo mode the local node is
            // the entire committee so a single signature suffices; in full
            // mode this becomes one vote of many that an aggregator collects.
            let fed_receipt_opt =
                build_federation_receipt(&s, &signed_turn.turn, &receipt, new_height, block_id);

            // ── Write a fresh AttestedRoot anchored to (block_id, round)
            // (audit F3 / gap D).
            //
            // `merkle_root` is the BLAKE3 whole-image `canonical_ledger_root`,
            // and it STAYS that ON PURPOSE: it is the RESTART ANCHOR — on boot a
            // node reconstructs its ledger from the store and checks the
            // reconstruction against this quorum-signed value (`state.rs`'s
            // `recovered_root`). No per-cell algebraic commitment fills that
            // role, and the whole-ledger 8-felt that would (`cells_root`
            // Phase-E) is deferred.
            //
            // The AIR-bound binding arrives through `receipt_stream_root` below:
            // it roots `receipt.receipt_hash()`, and a receipt's
            // `pre`/`post_state_hash` are now the chip 8-felt state commitment
            // (`dregg_turn::state_commit`), NOT the trusted-Rust
            // `Ledger::root()`. So this attestation's quorum signature DOES
            // certify the AIR-bound anchor — transitively, via the receipt
            // stream — while the BLAKE3 digest keeps doing the whole-image
            // recovery job the dual-hash ADR (`dregg_commit::hash`) reserves for
            // non-circuit paths.
            //
            // When full-turn proving is enabled (devnet) the candidate ALSO
            // carries a real, re-verified full-turn STARK proof (see
            // `full_turn_proof_artifacts` above); the note-tree Poseidon2 root
            // binding remains threaded separately.
            let merkle_root = canonical_ledger_root(&exec_ledger);
            let timestamp_for_root = now;
            let federation_keys = s.known_federation_keys.clone();
            let federation_threshold = s.decryption_threshold.max(1);
            let signing_key_bytes = s.cclerk.gossip_signing_key().to_bytes();

            // FAITHFUL NOTE ROOT: plan the exact successor from the in-memory
            // tree restored from the durable positional leaf table, then hybrid-
            // sign the complete history edge under this enrolled node identity.
            // The store independently reconstructs both roots and commits this
            // edge with the leaves/receipt/attestation/cursor in one redb txn.
            let local_pk = s.cclerk.public_key();
            let faithful_federation_id = faithful_history_federation_id(s.federation_id, &local_pk);
            let existing_faithful_head = match s.store.faithful_note_root_head() {
                Ok(head) => head,
                Err(e) => {
                    error!(
                        block_id = %block_id,
                        error = %e,
                        "faithful note-root history is malformed; refusing durable finalized commit"
                    );
                    return FinalizedExecutionOutcome::FatalIntegrity {
                        block_id,
                        error: format!("faithful note-root history malformed: {e}"),
                    };
                }
            };
            if existing_faithful_head.as_ref().is_some_and(|head| {
                head.federation_id != faithful_federation_id
                    || head.committee_epoch != s.committee_epoch
            }) {
                error!(
                    block_id = %block_id,
                    active_federation = %dregg_types::hex_encode(&faithful_federation_id),
                    active_epoch = s.committee_epoch,
                    "faithful note-root segment belongs to an earlier committee context; refusing \
                     to extend it until an authenticated segment-rollover certificate is installed"
                );
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: "faithful note-root committee context mismatch".into(),
                };
            }
            let initial_faithful_anchor = if existing_faithful_head.is_none() {
                let Some(previous_height) = new_height.checked_sub(1) else {
                    error!(
                        block_id = %block_id,
                        "finalized height zero has no faithful predecessor; refusing durable commit"
                    );
                    return FinalizedExecutionOutcome::FatalIntegrity {
                        block_id,
                        error: "finalized height zero has no faithful predecessor".into(),
                    };
                };
                let note_count = match u64::try_from(s.note_tree.size()) {
                    Ok(count) => count,
                    Err(_) => {
                        error!(
                            block_id = %block_id,
                            "faithful note count does not fit u64; refusing durable finalized commit"
                        );
                        return FinalizedExecutionOutcome::FatalIntegrity {
                            block_id,
                            error: "faithful note count does not fit u64".into(),
                        };
                    }
                };
                match dregg_persist::FaithfulNoteRootAnchorV1::new(
                    faithful_history_session_id(faithful_federation_id, s.committee_epoch),
                    faithful_federation_id,
                    s.committee_epoch,
                    previous_height,
                    note_count,
                    dregg_persist::CanonicalFaithfulRoot::from_faithful(
                        s.note_tree.faithful_root_immutable(),
                    ),
                ) {
                    Ok(anchor) => Some(anchor),
                    Err(e) => {
                        error!(
                            block_id = %block_id,
                            error = %e,
                            "could not create faithful note-root segment anchor"
                        );
                        return FinalizedExecutionOutcome::FatalIntegrity {
                            block_id,
                            error: format!("faithful note-root anchor construction failed: {e}"),
                        };
                    }
                }
            } else {
                None
            };
            let faithful_predecessor = existing_faithful_head
                .as_ref()
                .or(initial_faithful_anchor.as_ref())
                .expect("existing or initial faithful head");
            let faithful_record = match dregg_persist::plan_faithful_note_root_transition_v1(
                &s.note_tree,
                faithful_predecessor,
                block_id.0,
                &note_commitments,
            ) {
                Ok(record) => record,
                Err(e) => {
                    error!(
                        block_id = %block_id,
                        error = %e,
                        "live note tree does not extend the authenticated faithful head; refusing durable commit"
                    );
                    return FinalizedExecutionOutcome::FatalIntegrity {
                        block_id,
                        error: format!("faithful note-root transition invalid: {e}"),
                    };
                }
            };
            let faithful_message = faithful_record.signing_message();
            let signing_key = dregg_types::SigningKey::from_bytes(&signing_key_bytes);
            let faithful_classical_signature = dregg_types::sign(&signing_key, &faithful_message);
            let (local_ml_dsa_pk, local_ml_dsa_signing_key) =
                dregg_federation::frost::MlDsaSigningKey::from_seed(&signing_key_bytes);
            let Some(faithful_pq_signature) = local_ml_dsa_signing_key.sign(&faithful_message)
            else {
                error!(
                    block_id = %block_id,
                    "ML-DSA faithful-root signing failed; refusing half-authenticated durable commit"
                );
                return FinalizedExecutionOutcome::FatalIntegrity {
                    block_id,
                    error: "ML-DSA faithful-root signing failed".into(),
                };
            };
            let faithful_envelope = dregg_persist::FaithfulNoteRootEnvelopeV1 {
                record: faithful_record.clone(),
                hybrid_quorum: vec![dregg_types::HybridQuorumSig {
                    pubkey: local_pk,
                    signature: faithful_classical_signature,
                    ml_dsa_pubkey: local_ml_dsa_pk.0.to_vec(),
                    pq_signature: faithful_pq_signature,
                }],
            };
            let note_tree_root = Some(faithful_record.successor.to_bytes());

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
                nullifier_set_root: Some(planned_nullifier_root),
                height: new_height,
                timestamp: timestamp_for_root,
                blocklace_block_id: Some(block_id.0),
                finality_round,
                quorum_signatures: Vec::new(),
                threshold_qc: None,
                threshold: federation_threshold,
                federation_id: dregg_types::FederationId(faithful_federation_id),
                receipt_stream_root,
                // Classical local attestation; the wire hybrid quorum is
                // populated by the cross-fed export path, not this signer.
                hybrid_quorum: Vec::new(),
            };
            let signing_msg = attested.signing_message();
            let sig = dregg_types::sign(&signing_key, &signing_msg);
            // In solo / single-validator mode our signature alone meets the
            // threshold (threshold defaults to 1 if the genesis-declared value
            // is zero), so the persisted root is a genuine quorum and the node
            // restarts cleanly.
            //
            // FULL-MODE COMMITTEE RESTART (caught by the N3 live run; CLOSED by
            // Fix B). In full mode this pushes ONLY the local signature
            // (1 < threshold), so `quorum_signatures` alone cannot re-anchor a
            // restart — the recovery anchor (`verify_signed_anchor_and_rollback`,
            // state.rs) is CORRECT hardening and pre-Fix-B this fail-closed the
            // node after >=1 finalized height.
            //
            // Fix B (landed): `FinalizationVote` binds the finalized merkle_root
            // AND (v4) this block's `receipt_stream_root`
            // (`dregg-finalization-vote-v4 || block_id || merkle_root ||
            // framed(receipt_stream_root)`) — which is what makes the assembled
            // quorum a committee statement about the TURN and not only about a
            // whole-ledger digest. The `VoteCollector` RETAINS the signature bytes
            // (`assembled_quorum`), and the >=threshold committee quorum is
            // persisted into the root's `finalization_quorum` — captured below
            // when already assembled, otherwise back-filled a gossip round or
            // two later by `backfill_finalization_quorums` (this synchronous
            // commit never blocks on network gossip; the trailing window is the
            // deliberate liveness cost). On restart the anchor accepts
            // `verify_signatures || verify_finalization_quorum`. Pinned by
            // `dregg_persist::tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`
            // and `tests::committee_node_restarts_cleanly_with_finalization_quorum`.
            if federation_keys.is_empty() || federation_keys.contains(&local_pk) {
                attested.quorum_signatures.push((local_pk, sig));
            }

            // Persist the attested root so the next turn's executor sees
            // its height (closes audit gap D — was never written).
            // N3 committee-restart fix (Fix B): if a >=threshold committee
            // finalization-vote quorum over THIS finalized root has already
            // assembled (peer votes that arrived before this synchronous
            // persist), capture it now. Usually empty at first persist — our own
            // vote is emitted just after this returns and peer votes trail over
            // gossip — so the quorum is normally back-filled later by
            // `backfill_finalization_quorums`. Populating it here too closes the
            // case where the quorum is already complete.
            // v4: attachable only when the assembled quorum binds THIS root's
            // PAIR — ledger root and receipt stream both.
            let finalization_quorum = handle
                .votes
                .read()
                .await
                .assembled_quorum(&block_id)
                .filter(|(pair, _)| *pair == (attested.merkle_root, attested.receipt_stream_root))
                .map(|(_, sigs)| sigs)
                .unwrap_or_default();

            // CROSS-FED PRODUCER: carry the hybrid (ed25519 ∧ ML-DSA-65) quorum on
            // the WIRE AttestedRoot, mapped from the assembled finalization quorum —
            // each QuorumSignature already holds both halves + the voter's self-
            // contained ML-DSA-65 pubkey. A cross-fed receipt verifier checks THIS
            // (`verify_hybrid_quorum_sigs`), so this is what lifts cross-fed finality
            // verification from fail-closed to actually verifying the PQ half.
            // (Empty at first persist while the quorum is still assembling; the
            // backfill path below carries the completed quorum on the stored root,
            // and the same mapping applies wherever the root is exported cross-fed.)
            //
            // ⚑ AND THE PREIMAGE THIS FIELD IS OVER IS THE VOTE PREIMAGE, NOT
            // `signing_message()`. These are finalization-vote signatures; a
            // consumer that checked them against the attested-root preimage
            // refused every live root while every test signed
            // `signing_message()` directly and never saw it. Both consumers now
            // read `AttestedRoot::hybrid_quorum_message()`, and the mapping is
            // the shared `QuorumSignature::to_hybrid` so a test cannot build
            // this field differently from the node.
            attested.hybrid_quorum =
                dregg_persist::hybrid_quorum_from_finalization_quorum(&finalization_quorum);

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
                finalization_quorum,
            };

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
            // The touched-cell post-states are read from the isolated candidate
            // for the complete pre→post whole-cell diff. The cell-by-id index is
            // therefore the durable
            // last-writer-wins overlay on top of the periodic full ledger
            // checkpoint, and recovery reconstructs the finalized ledger from
            // (checkpoint ⊕ overlay) without re-executing.
            let durable_ordinal = {
                // Persist the same COMPLETE whole-cell diff that will be
                // installed after durability. `LedgerDelta` intentionally does
                // not cover every cell dimension (heap/program/lifecycle/etc.),
                // so using it here can make recovery diverge from the attested
                // candidate even when the live overlay was correct.
                let commit_touched_ids = &touched_ids;
                let mut touched_cells: Vec<dregg_cell::Cell> =
                    Vec::with_capacity(commit_touched_ids.len());
                for id in commit_touched_ids {
                    if let Some(cell) = exec_ledger.get(id) {
                        touched_cells.push(cell.clone());
                    }
                    // A touched id absent post-commit is not carried here — a
                    // genuine REMOVAL travels in `removed` (below), the authoritative
                    // tombstone the overlay deletes on recovery.
                }
                // The tombstone dimension: cells this turn REMOVED from the hosted
                // set (MakeSovereign). Post-states alone (`touched_cells`) cannot
                // represent an erasure, so without this the durable overlay
                // resurrects the removed cell as hosted on recovery and the
                // reconstructed root diverges from `ledger_root`.
                let removed: Vec<[u8; 32]> = commit_touched_ids
                    .iter()
                    .filter(|id| pre_ledger.get(id).is_some() && exec_ledger.get(id).is_none())
                    .map(|id| id.0)
                    .collect();
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
                    removed,
                };
                // This is the fail-closed cursor captured before execution and
                // revalidated byte-for-byte after reacquiring the state lock.
                // Reading it again here would add a masking fallback/race seam.
                let expected_ordinal = durable_commit_cursor;
                executor_state.promise_resolutions =
                    match crate::promise_resolutions::resolution_candidates(
                        expected_ordinal,
                        receipt.receipt_hash(),
                        &resolution_events,
                    ) {
                        Ok(candidates) => candidates,
                        Err(error) => {
                            error!(
                                block_id = %block_id,
                                turn_hash = %turn_hash_hex,
                                error = %error,
                                "could not canonicalize promise-resolution outbox before commit"
                            );
                            return FinalizedExecutionOutcome::FatalIntegrity { block_id, error };
                        }
                    };
                // Weld the NoteCreate commitments into this SAME atomic commit
                // transaction (bug #58): the note leaves and the turn record land
                // together-or-not-at-all in one fsync boundary, so a crash-retry
                // can never double-append a note leaf.
                let faithful_weld = dregg_persist::commit_log::FinalizedFaithfulRootWeld {
                    initial_anchor: initial_faithful_anchor.as_ref(),
                    envelope: &faithful_envelope,
                    author_committee: std::slice::from_ref(&local_pk),
                    author_ml_dsa_committee: std::slice::from_ref(&local_ml_dsa_pk),
                    attested_root: &stored,
                    spent_nullifiers: &finalized_nullifier_spends,
                    finalized_spends: &finalized_faithful_spends,
                };
                let commit_durable = || {
                    if is_galley_public_perform {
                        s.store.commit_finalized_poa_galley_public_perform_v1(
                            expected_ordinal,
                            &commit_record,
                            &note_commitments,
                            receipt_log_index,
                            &signed_turn,
                            &receipt,
                            faithful_weld,
                            &executor_state,
                        )
                    } else {
                        match (receipt_already_in_log, poa_signal_transition.as_ref()) {
                        (true, Some(poa_signal)) => s
                            .store
                            .commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt_and_poa_signal(
                                expected_ordinal,
                                &commit_record,
                                &note_commitments,
                                receipt_log_index,
                                &encoded_receipt,
                                faithful_weld,
                                &executor_state,
                                poa_signal,
                            ),
                        (false, Some(poa_signal)) => s.store
                            .commit_finalized_turn_with_faithful_root_and_executor_state_and_poa_signal(
                                expected_ordinal,
                                &commit_record,
                                &note_commitments,
                                receipt_log_index,
                                &encoded_receipt,
                                faithful_weld,
                                &executor_state,
                                poa_signal,
                            ),
                        (true, None) => s
                            .store
                            .commit_finalized_turn_with_faithful_root_and_executor_state_existing_receipt(
                                expected_ordinal,
                                &commit_record,
                                &note_commitments,
                                receipt_log_index,
                                &encoded_receipt,
                                faithful_weld,
                                &executor_state,
                            ),
                        (false, None) => s.store
                            .commit_finalized_turn_with_faithful_root_and_executor_state(
                                expected_ordinal,
                                &commit_record,
                                &note_commitments,
                                receipt_log_index,
                                &encoded_receipt,
                                faithful_weld,
                                &executor_state,
                            ),
                        }
                    }
                };
                #[cfg(test)]
                let injected_failure = {
                    let mut target = FAIL_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
                        .lock()
                        .expect("generic finalized failure hook mutex");
                    if target.as_ref() == Some(&block_id.0) {
                        target.take();
                        true
                    } else {
                        false
                    }
                };
                #[cfg(test)]
                let injected_replay = {
                    let mut target = REPLAY_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
                        .lock()
                        .expect("generic finalized replay hook mutex");
                    if target.as_ref() == Some(&block_id.0) {
                        target.take();
                        true
                    } else {
                        false
                    }
                };
                #[cfg(test)]
                let durable_outcome = if injected_failure {
                    Err(dregg_persist::StoreError::Database(
                        "injected generic finalized commit failure".to_string(),
                    ))
                } else if injected_replay {
                    Ok(dregg_persist::commit_log::CommitOutcome {
                        ordinal: expected_ordinal,
                        freshly_committed: false,
                    })
                } else {
                    commit_durable()
                };
                #[cfg(not(test))]
                let durable_outcome = commit_durable();
                match durable_outcome {
                    Ok(outcome) => {
                        let assigned = outcome.ordinal;
                        if !outcome.freshly_committed {
                            debug!(
                                turn_hash = %turn_hash_hex,
                                ordinal = assigned,
                                "finalized commit was already durable; suppressing duplicate RAM/event publication"
                            );
                            return FinalizedExecutionOutcome::Committed {
                                block_id,
                                durable_ordinal: assigned,
                                receipt_stream_root,
                            };
                        }

                        // COMMIT POINT CROSSED. Install the complete candidate
                        // overlay only now. A rejected/expired/pending executor
                        // result, stale CAS, or redb error can no longer leak a
                        // fee debit, nonce tick, provisioned cell, or body write
                        // into authoritative RAM.
                        install_finalized_ledger_overlay(&mut s.ledger, &exec_ledger, &touched_ids);

                        if !receipt_already_in_log {
                            s.cclerk
                                .append_receipt_already_durable(
                                    receipt_log_index,
                                    receipt.clone(),
                                )
                                .expect(
                                    "durably welded receipt must append at its reserved in-memory index",
                                );
                            crate::metrics::set_receipt_chain_length(
                                s.cclerk.receipt_log_length() as f64
                            );
                        }
                        // Advance the in-RAM Poseidon2 note tree ONLY after the
                        // durable append succeeded, and ONLY when THIS call
                        // freshly wrote the leaves. On an idempotent replay of an
                        // already-committed turn the leaves are already durable,
                        // and the boot-time rebuild from `load_all_note_commitments`
                        // already holds them — re-appending here would double the
                        // in-RAM tree.
                        for cm in &note_commitments {
                            s.note_tree_append_commitment(cm);
                        }
                        // Only a root that landed in the same atomic transaction
                        // as its exact note frontier may become externally
                        // observable.  A failed commit emits no phantom head.
                        state.emit(NodeEvent::Root {
                            height: new_height,
                            merkle_root: dregg_types::hex_encode(&stored.merkle_root),
                            timestamp: stored.timestamp,
                        });
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
                        assigned
                    }
                    Err(e) => {
                        // The candidate was never published, so the durable
                        // failure leaves authoritative RAM, receipt heads,
                        // pending state, artifacts and subscriber events exactly
                        // at the pre-turn snapshot. Recovery/retry can safely
                        // execute from the same durable cursor.
                        error!(
                            turn_hash = %turn_hash_hex,
                            error = %e,
                            "DURABLE commit-log write FAILED; isolated candidate discarded with no RAM/event publication"
                        );
                        return FinalizedExecutionOutcome::RetryableOperational {
                            block_id,
                            error: format!("durable finalized commit failed: {e}"),
                        };
                    }
                }
            };

            // Everything below is post-commit publication. None of these RAM,
            // auxiliary-store, or observer-visible effects can run for a failed
            // finalized record.
            //
            // Named crash gap: proof + retained-turn config bytes are auxiliary
            // post-commit writes, not members of the redb finalized transaction.
            // A crash here can leave an otherwise valid finalized record without
            // those served artifacts. They are never published *before* commit,
            // but complete crash recovery requires welding/rederiving them later.
            if let Some((proof_bytes, retained_turn, proven_anchors)) = &full_turn_proof_artifacts {
                let key = crate::turn_proving::turn_proof_config_key(&turn_hash_hex);
                if let Err(e) = s.store.set_config(&key, proof_bytes) {
                    warn!(error = %e, turn_hash = %turn_hash_hex,
                            "failed to persist full-turn proof after finalized commit");
                }
                // ⚑ THE PROVEN 8-FELT ANCHOR PAIR. Written on the SAME path as the proof so a
                // reader that finds a proof and no anchors is looking at a pre-cutover entry, and
                // the anchor endpoint then serves NO bindable pair rather than an unrelated one.
                // A checker with no pair REFUSES; it never falls back to reading the artifact.
                let anchors_key =
                    crate::turn_proving::turn_proof_anchors_config_key(&turn_hash_hex);
                if let Err(e) = s.store.set_config(&anchors_key, proven_anchors) {
                    warn!(error = %e, turn_hash = %turn_hash_hex,
                            "failed to persist the full-turn proof's 8-felt commit anchors; \
                             /api/turn/{{h}}/anchor will serve no bindable pair for this turn and \
                             a stranger re-verifying it gets a REFUSAL rather than a verdict");
                }
                if let Some(turn_bytes) = retained_turn {
                    let key = crate::turn_proving::finalized_turn_config_key(&turn_hash_hex);
                    match s.store.set_config(&key, turn_bytes) {
                        Ok(()) => info!(
                            turn_hash = %turn_hash_hex,
                            retained_bytes = turn_bytes.len(),
                            "finalized turn retained for IVC history compression \
                             (anchor-tied to the served proof)"
                        ),
                        Err(e) => warn!(
                            error = %e, turn_hash = %turn_hash_hex,
                            "failed to persist retained finalized turn; history compression will refuse this turn"
                        ),
                    }
                }
            }

            // A finalized turn whose proof FAILED is recorded as such, durably and
            // per-turn. Same auxiliary-write caveat as the proof bytes above (this
            // is not a member of the finalized redb transaction), but it is written
            // on the SAME path, so a reader that finds neither `full_turn_proof:{h}`
            // nor `full_turn_proof_failed:{h}` is looking at a turn that was never
            // proved rather than one that failed.
            if let Some(reason) = &full_turn_proof_failure {
                let key = crate::turn_proving::turn_proof_failure_config_key(&turn_hash_hex);
                if let Err(e) = s.store.set_config(&key, reason.as_bytes()) {
                    error!(
                        error = %e,
                        turn_hash = %turn_hash_hex,
                        reason = %reason,
                        "could not record the full-turn proving FAILURE durably; this turn's \
                         unproven status is now only in the log"
                    );
                }
            }

            crate::api::push_committed_event_enriched(
                &mut s,
                receipt_hash_hex.clone(),
                activity_agent_hex,
                activity_kinds,
                activity_summaries,
                // ⚠ NOT unconditionally `ProofPending`. A turn whose proof failed
                // is never going to be attested, and reporting it as "in flight"
                // is a claim that resolves itself in the reader's head as success.
                if full_turn_proof_failure.is_some() {
                    crate::state::ActivityProofStatus::ProofGenerationFailed
                } else {
                    crate::state::ActivityProofStatus::ProofPending
                },
            );

            // Publish only the exact cascade that shared the source commit's
            // transaction. ReadyToExecute is intentionally notification-only:
            // it contains an unsigned dependent turn and is never submitted to
            // the signed consensus queue.
            crate::executor_side_state_persistence::trace_durable_resolution_events(
                &resolution_events,
            );
            if let Err(error) = crate::promise_resolutions::publish_durable_resolution_events(
                state,
                &s.store,
                durable_ordinal,
                receipt.receipt_hash(),
                &resolution_events,
            ) {
                error!(
                    block_id = %block_id,
                    turn_hash = %turn_hash_hex,
                    durable_ordinal,
                    error = %error,
                    "durable promise-resolution outbox could not be published"
                );
            }

            let invalid_bundle_evidence = if let Some(bundle) = artifacts {
                materialize_blocklace_artifacts(&mut s, block_id, &receipt, bundle)
            } else {
                Vec::new()
            };

            // Emit revocation events only after the revocation has become part
            // of the durable finalized transition.
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
                full_turn_proven = full_turn_proof_artifacts.is_some(),
                "finalized turn executed (blocklace consensus)"
            );
            return FinalizedExecutionOutcome::Committed {
                block_id,
                durable_ordinal,
                receipt_stream_root,
            };
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // Write-ahead-before-live: the executor's candidate can contain a
            // phase-1 fee debit + nonce tick when the body fails, but a generic
            // rejection has no typed durable attempt receipt yet. Therefore the
            // entire candidate is discarded. This is the Rust boundary form of
            // `Dregg2.Exec.Durability.durableApply_reject_stays`: rejection leaves
            // the durable/live state unchanged. A future charged-rejection design
            // must first add a typed phase1-only durable record; it must never
            // resurrect this candidate overlay as a RAM-only anti-spam charge.
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                reason = %reason,
                "finalized turn rejected; isolated phase1/body candidate discarded (no typed durable attempt receipt)"
            );
            persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "executor-rejected",
            )
        }
        dregg_turn::TurnResult::Expired => {
            warn!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn expired; isolated candidate discarded without publication"
            );
            persist_finalized_payload_rejection(
                &s,
                block_id,
                turn_data,
                Some(computed_hash),
                "turn-expired",
            )
        }
        dregg_turn::TurnResult::Pending => {
            debug!(
                turn_hash = %turn_hash_hex,
                block_id = %block_id,
                "finalized turn pending; isolated candidate discarded without publication"
            );
            FinalizedExecutionOutcome::RetryableOperational {
                block_id,
                error: "finalized turn remained pending".into(),
            }
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

/// Drive the SOLE AUTHORITATIVE APPLICATION of one already-admitted `SignedTurn`, for a test in
/// another module of this crate.
///
/// ⚑ WHY THIS EXISTS. `POST /turns/submit` is ADMISSION STAGING at every committee size, n=1
/// included: `api.rs` arms an undo journal, executes to build the receipt for the HTTP response,
/// and then rolls the ledger back UNCONDITIONALLY. Consensus finalization — this function's
/// `execute_finalized_turn` — is the only thing that mutates authoritative state. A test that
/// POSTs an envelope and then reads `state.ledger` therefore observes NOTHING, no matter how
/// correct the turn is, and its failure looks like an executor or cell-program defect rather than
/// a missing half of the pipeline. `relay_slash_submit`'s weld test read exactly that way for nine
/// days. Rather than each caller reconstructing a `BlocklaceHandle`, there is ONE entry.
#[cfg(test)]
pub(crate) async fn finalize_admitted_turn_for_test(
    state: &NodeState,
    block_id: BlockId,
    turn_data: &[u8],
) -> crate::execution_cursor::FinalizedExecutionOutcome {
    let self_key = { state.read().await.cclerk.public_key().0 };
    let handle = tests::test_handle_with_committee(self_key, vec![self_key]).await;
    execute_finalized_turn(state, &handle, block_id, turn_data, None, None, 0).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_types::CellId;

    /// THE SIGNAL THAT COULD NOT GO FALSE. `/status` reported `healthy: true`
    /// through a quorum-losing 2-of-4 partition because nothing it consulted was
    /// about the other members. These are the facts it consults now, asserted as
    /// a pure value — no network, no clock beyond `now`.
    #[test]
    fn federation_liveness_reports_quorum_reachability_from_who_is_actually_voting() {
        let me = [0x01u8; 32];
        let liveness = FederationLiveness::default();

        // Nobody has voted at us. At the N=4 threshold of 3 we cannot finalize
        // even though this process is perfectly healthy in every local sense.
        let alone = liveness.snapshot(&me, 3, 0);
        assert_eq!(alone.live_committee_voters, 0);
        assert!(!alone.quorum_reachable);
        assert!(!alone.ever_reached_quorum);
        // ... and a threshold-1 (solo / collapsed) deployment is unaffected: it
        // finalizes on its own signature and must not be called unhealthy.
        let solo = liveness.snapshot(&me, 1, 0);
        assert!(solo.quorum_reachable);
        assert!(!solo.finality_stalled);

        // OUR OWN vote is not evidence that anyone else is reachable. It arrives
        // through the same funnel as a peer's, so this distinction is load-bearing.
        liveness.note_vote(&me);
        assert_eq!(liveness.snapshot(&me, 3, 0).live_committee_voters, 0);

        // One peer back: still short of 3 (2 of 3 counting ourselves).
        liveness.note_vote(&[0x02u8; 32]);
        let one_peer = liveness.snapshot(&me, 3, 1);
        assert_eq!(one_peer.live_committee_voters, 1);
        assert!(!one_peer.quorum_reachable);

        // A SECOND vote from the SAME member is not a second member.
        liveness.note_vote(&[0x02u8; 32]);
        assert_eq!(liveness.snapshot(&me, 3, 1).live_committee_voters, 1);

        // Two distinct peers + ourselves = 3 = threshold. Quorum reachable.
        liveness.note_vote(&[0x03u8; 32]);
        let quorate = liveness.snapshot(&me, 3, 2);
        assert_eq!(quorate.live_committee_voters, 2);
        assert!(quorate.quorum_reachable);
        assert_eq!(quorate.connected_peers, 2);

        // A fresh handle has not stalled yet (the clock runs from `started`), and
        // crossing quorum records that it happened.
        assert!(!quorate.finality_stalled);
        liveness.note_quorum();
        assert!(liveness.snapshot(&me, 3, 2).ever_reached_quorum);
    }

    /// A submitted turn has a name for the window between "accepted for
    /// consensus" and a durable verdict, so a client polling by hash is told
    /// `pending` rather than nothing.
    #[test]
    fn in_flight_turns_name_the_window_between_submission_and_a_verdict() {
        let in_flight = InFlightTurns::default();
        let turn = [0x19u8; 32];
        assert!(in_flight.is_empty());
        assert_eq!(in_flight.pending_for_seconds(&turn), None);

        in_flight.note_submitted(turn);
        assert_eq!(in_flight.len(), 1);
        assert!(in_flight.pending_for_seconds(&turn).is_some());

        // Re-submission of the same hash keeps ONE entry and does not reset the
        // clock to zero on every poll.
        in_flight.note_submitted(turn);
        assert_eq!(in_flight.len(), 1);

        // A durable verdict retires it; the route then answers from the store.
        in_flight.resolve(&turn);
        assert!(in_flight.is_empty());
        assert_eq!(in_flight.pending_for_seconds(&turn), None);
    }

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

    #[test]
    fn exact_live_path_never_replays_full_faithful_history() {
        let blocklace_source = include_str!("blocklace_sync.rs");
        let exact_live = blocklace_source
            .split_once("async fn execute_live_exact_fnsp_v3(")
            .expect("exact live executor remains present")
            .1
            .split_once("async fn execute_finalized_turn(")
            .expect("exact live executor remains a bounded function")
            .0;
        assert!(
            !exact_live.contains("load_faithful_note_root_history_hybrid"),
            "active exact spends must consume prepared O(1) history authority"
        );

        let finalization_source = include_str!("exact_fnsp_v3_finalization.rs");
        let history_validator = finalization_source
            .split_once("fn validate_authenticated_history(")
            .expect("history validator remains present")
            .1
            .split_once("fn validate_faithful_coordinates(")
            .expect("history validator remains a bounded function")
            .0;
        assert_eq!(
            history_validator
                .matches("load_faithful_note_root_history_hybrid")
                .count(),
            1,
            "first activation retains exactly one full-history audit"
        );
        assert!(
            history_validator.contains("exact_fnsp_v3_live_authority")
                && history_validator.contains(".is_none()"),
            "the full-history audit must remain guarded by absent live authority"
        );
    }

    #[test]
    fn exact_failure_classifier_separates_payload_availability_and_integrity() {
        use crate::exact_fnsp_v3_execution_authority::ExecutorProducedFinalizationError as E;

        assert!(require_live_exact_epoch_supported(true).is_ok());
        assert_eq!(
            require_live_exact_epoch_supported(false)
                .expect_err("distributed exact epoch is unsupported, not retryable")
                .class,
            ExactFinalizedFailureClass::DeterministicPayload("exact-fnsp-v3-epoch-unsupported"),
            "an unsupported finalized exact epoch must not wedge tau by retrying forever"
        );

        let deterministic = [
            (
                E::ExactProofCarrierInvalid("bad carrier".into()),
                "exact-fnsp-v3-carrier-refused",
            ),
            (
                E::ExactProofAcceptance("bad proof".into()),
                "exact-fnsp-v3-proof-refused",
            ),
            (
                E::ExactTurnShapeUnsupported,
                "exact-fnsp-v3-carrier-refused",
            ),
            (
                E::ExactChargedRoutePreflight("bad nonce".into()),
                "exact-fnsp-v3-execution-refused",
            ),
        ];
        for (error, reason_code) in deterministic {
            assert_eq!(
                classify_exact_executor_failure(error).class,
                ExactFinalizedFailureClass::DeterministicPayload(reason_code)
            );
        }

        let impossible = [
            E::ValidatedTurnHashMismatch,
            E::ReceiptTurnMismatch,
            E::ExactFrameSignatureInvalid,
            E::NonDurableExecutorSideStateMutation,
        ];
        for error in impossible {
            assert_eq!(
                classify_exact_executor_failure(error).class,
                ExactFinalizedFailureClass::FatalIntegrity
            );
        }
        assert_eq!(
            classify_exact_executor_failure(E::ExactAdmission(
                dregg_turn::executor::ExactFnspV3AdmissionError::MutexPoisoned,
            ))
            .class,
            ExactFinalizedFailureClass::RetryableOperational,
            "lock availability must not let adversarial payloads permanently stop finality"
        );

        assert_eq!(
            classify_exact_finalization_failure(
                crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError::Store(
                    dregg_persist::StoreError::Database("busy".into()),
                ),
            )
            .class,
            ExactFinalizedFailureClass::RetryableOperational
        );
        for corrupt in [
            dregg_persist::StoreError::Integrity("contradictory seal".into()),
            dregg_persist::StoreError::Serialization("bad durable bytes".into()),
            dregg_persist::StoreError::Crypto("bad durable signature".into()),
            dregg_persist::StoreError::NotFound,
        ] {
            assert_eq!(
                classify_exact_store_failure(corrupt).class,
                ExactFinalizedFailureClass::FatalIntegrity,
                "durable corruption/missing required authority cannot become an infinite retry"
            );
        }
        assert_eq!(
            classify_exact_finalization_failure(
                crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError::HistoricalRootUnauthenticated,
            )
            .class,
            ExactFinalizedFailureClass::DeterministicPayload(
                "exact-fnsp-v3-historical-root-refused"
            )
        );
        assert_eq!(
            classify_exact_finalization_failure(
                crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError::FaithfulHistoryUninitialized,
            )
            .class,
            ExactFinalizedFailureClass::DeterministicPayload(
                "exact-fnsp-v3-historical-root-refused"
            ),
            "missing authenticated history cannot spin a finalized exact payload forever"
        );
        assert_eq!(
            classify_exact_finalization_failure(
                crate::exact_fnsp_v3_finalization::ExactFnspV3FinalizationError::CoordinateMismatch(
                    crate::exact_fnsp_v3_finalization::ExactFnspV3Coordinate::FaithfulSpend,
                ),
            )
            .class,
            ExactFinalizedFailureClass::FatalIntegrity
        );
    }

    #[test]
    fn finalized_note_commitments_include_nested_actions_in_dfs_order() {
        fn action(tag: u8, effects: Vec<dregg_turn::Effect>) -> dregg_turn::Action {
            dregg_turn::Action {
                target: dregg_cell::CellId([tag; 32]),
                method: [tag.wrapping_add(1); 32],
                args: Vec::new(),
                authorization: dregg_turn::Authorization::Unchecked,
                preconditions: Default::default(),
                effects,
                may_delegate: dregg_turn::DelegationMode::None,
                commitment_mode: dregg_turn::CommitmentMode::Full,
                balance_change: None,
                witness_blobs: Vec::new(),
            }
        }
        fn note(tag: u8) -> dregg_turn::Effect {
            dregg_turn::Effect::NoteCreate {
                commitment: dregg_cell::NoteCommitment([tag; 32]),
                value: u64::from(tag),
                asset_type: 7,
                encrypted_note: vec![tag],
                value_commitment: None,
                range_proof: None,
            }
        }

        let mut forest = dregg_turn::CallForest::new();
        let root = forest.add_root(action(
            0x10,
            vec![
                note(0x11),
                dregg_turn::Effect::ExerciseViaCapability {
                    cap_slot: 0,
                    inner_effects: vec![
                        note(0x12),
                        dregg_turn::Effect::ExerciseViaCapability {
                            cap_slot: 1,
                            inner_effects: vec![note(0x13)],
                        },
                    ],
                },
            ],
        ));
        let child = root.add_child(action(
            0x20,
            vec![
                dregg_turn::Effect::IncrementNonce {
                    cell: dregg_cell::CellId([0x22; 32]),
                },
                note(0x21),
            ],
        ));
        child.add_child(action(0x30, vec![note(0x31)]));

        assert_eq!(
            finalized_note_commitments(&forest),
            vec![[0x11; 32], [0x12; 32], [0x13; 32], [0x21; 32], [0x31; 32]],
            "every executed NoteCreate, including capability-wrapped effects, becomes one positional faithful leaf in execution order"
        );
    }

    #[test]
    fn finalized_signal_routing_finds_nested_markers_but_refuses_noncanonical_carriers() {
        fn action(effects: Vec<dregg_turn::Effect>) -> dregg_turn::Action {
            dregg_turn::Action {
                target: dregg_cell::CellId([0x71; 32]),
                method: [0x72; 32],
                args: Vec::new(),
                authorization: dregg_turn::Authorization::Unchecked,
                preconditions: Default::default(),
                effects,
                may_delegate: dregg_turn::DelegationMode::None,
                commitment_mode: dregg_turn::CommitmentMode::Full,
                balance_change: None,
                witness_blobs: Vec::new(),
            }
        }
        fn signal(cell: u8) -> dregg_turn::Effect {
            let claim = dregg_sdk::poa_signal::SignalClaimV1::new(
                1,
                &[dregg_sdk::poa_signal::SignalCode::new(5, 0, 5).unwrap()],
            )
            .unwrap();
            dregg_turn::Effect::EmitEvent {
                cell: dregg_cell::CellId([cell; 32]),
                event: dregg_sdk::poa_signal::signal_claim_event(claim),
            }
        }
        fn turn(call_forest: dregg_turn::CallForest) -> dregg_turn::Turn {
            dregg_turn::Turn {
                agent: dregg_cell::CellId([0x71; 32]),
                nonce: 0,
                call_forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: None,
                depends_on: Vec::new(),
                conservation_proof: None,
                sovereign_witnesses: Default::default(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            }
        }

        let mut nested = dregg_turn::CallForest::new();
        nested.add_root(action(vec![dregg_turn::Effect::ExerciseViaCapability {
            cap_slot: 3,
            inner_effects: vec![dregg_turn::Effect::ExerciseViaCapability {
                cap_slot: 7,
                inner_effects: vec![signal(0x73)],
            }],
        }]));
        assert!(matches!(
            finalized_signal_claim(&turn(nested)),
            Err(FinalizedSignalRouteError::NonCanonicalCarrier(_))
        ));

        let mut duplicate = dregg_turn::CallForest::new();
        duplicate.add_root(action(vec![
            signal(0x74),
            dregg_turn::Effect::ExerciseViaCapability {
                cap_slot: 0,
                inner_effects: vec![signal(0x75)],
            },
        ]));
        assert!(matches!(
            finalized_signal_claim(&turn(duplicate)),
            Err(FinalizedSignalRouteError::Multiple)
        ));

        let malformed_event = dregg_turn::action::Event::new(
            dregg_turn::action::symbol(dregg_sdk::poa_signal::SIGNAL_CLAIM_TOPIC_V1),
            vec![dregg_cell::field_from_u64(1)],
        );
        let mut malformed = dregg_turn::CallForest::new();
        malformed.add_root(action(vec![dregg_turn::Effect::EmitEvent {
            cell: dregg_cell::CellId([0x76; 32]),
            event: malformed_event,
        }]));
        assert!(matches!(
            finalized_signal_claim(&turn(malformed)),
            Err(FinalizedSignalRouteError::Malformed(
                crate::poa_signal_adapter::SignalAdapterError::Claim(
                    dregg_sdk::poa_signal::SignalClaimError::MalformedReserved(_)
                )
            ))
        ));
    }

    #[test]
    fn off_lock_finalization_refuses_global_cursor_or_nullifier_drift() {
        let cursor = 17;
        let root = [0x42; 32];
        assert!(finalized_global_snapshot_matches(
            cursor, root, cursor, root
        ));
        assert!(!finalized_global_snapshot_matches(
            cursor,
            root,
            cursor + 1,
            root
        ));
        let mut changed_root = root;
        changed_root[31] ^= 1;
        assert!(!finalized_global_snapshot_matches(
            cursor,
            root,
            cursor,
            changed_root
        ));
    }

    #[test]
    fn ordered_faithful_nullifier_successors_match_executor_staging() {
        let durable = dregg_cell::nullifier_set::NullifierSet::new();
        let spends = [
            dregg_persist::FinalizedNullifierRecord {
                nullifier: [0x41; 32],
                value: 700,
            },
            dregg_persist::FinalizedNullifierRecord {
                nullifier: [0x51; 32],
                value: 900,
            },
        ];

        let (successor, roots) = planned_ordered_nullifier_successors(&durable, &spends)
            .expect("two fresh spends have an exact ordered successor chain");
        assert_eq!(roots.len(), 2);
        assert_ne!(
            roots[0], roots[1],
            "the first carrier must not be compared with the final batch root"
        );

        let mut first_only = durable.clone();
        first_only
            .insert(dregg_cell::Nullifier(spends[0].nullifier), spends[0].value)
            .unwrap();
        assert_eq!(roots[0], first_only.root8().to_bytes32());
        assert_eq!(roots[1], successor.root8().to_bytes32());

        let duplicate = [spends[0], spends[0]];
        assert_eq!(
            planned_ordered_nullifier_successors(&durable, &duplicate)
                .expect_err("within-turn duplicate nullifiers must refuse"),
            spends[0].nullifier,
            "within-turn duplicate nullifiers refuse before mutation"
        );
    }

    #[test]
    fn finalized_note_spend_admission_carries_height_root_and_public_nullifier_tail() {
        fn action(tag: u8, effects: Vec<dregg_turn::Effect>) -> dregg_turn::Action {
            dregg_turn::Action {
                target: dregg_cell::CellId([tag; 32]),
                method: [tag.wrapping_add(1); 32],
                args: Vec::new(),
                authorization: dregg_turn::Authorization::Unchecked,
                preconditions: Default::default(),
                effects,
                may_delegate: dregg_turn::DelegationMode::None,
                commitment_mode: dregg_turn::CommitmentMode::Full,
                balance_change: None,
                witness_blobs: Vec::new(),
            }
        }
        fn spend(tag: u8, value: u64, height: u64, root: [u8; 32]) -> dregg_turn::Effect {
            let successor = dregg_circuit::Faithful8::ZERO.to_bytes32();
            let carrier = dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier::new(
                height,
                successor,
                vec![tag, tag.wrapping_add(1)],
            )
            .unwrap();
            dregg_turn::Effect::NoteSpend {
                nullifier: dregg_cell::note::Nullifier([tag; 32]),
                note_tree_root: root,
                value,
                asset_type: 7,
                spending_proof: carrier.encode(),
                value_commitment: None,
            }
        }

        let root = dregg_persist::CanonicalFaithfulRoot::from_faithful(
            dregg_persist::Poseidon2NoteTree::with_depth(16).faithful_root_immutable(),
        );
        let mut forest = dregg_turn::CallForest::new();
        let top = forest.add_root(action(0x40, vec![spend(0x41, 700, 9, root.to_bytes())]));
        top.add_child(action(0x50, vec![spend(0x51, 900, 12, root.to_bytes())]));

        assert_eq!(
            finalized_note_spends(&forest),
            vec![
                dregg_persist::FinalizedNullifierRecord {
                    nullifier: [0x41; 32],
                    value: 700,
                },
                dregg_persist::FinalizedNullifierRecord {
                    nullifier: [0x51; 32],
                    value: 900,
                },
            ]
        );
        assert_eq!(
            finalized_faithful_spend_claims(&forest).unwrap(),
            vec![
                (
                    9,
                    root,
                    dregg_persist::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                    7,
                ),
                (
                    12,
                    root,
                    dregg_persist::CanonicalFaithfulRoot::from_bytes([0; 32]).unwrap(),
                    7,
                ),
            ]
        );

        let anchor =
            dregg_persist::FaithfulNoteRootAnchorV1::new([1; 32], [2; 32], 3, 9, 0, root).unwrap();
        let history = dregg_persist::FaithfulNoteRootHistoryV1::new(anchor);
        assert!(faithful_history_contains_pair(&history, 9, root));
        assert!(!faithful_history_contains_pair(&history, 10, root));

        if let dregg_turn::Effect::NoteSpend { spending_proof, .. } =
            &mut forest.roots[0].action.effects[0]
        {
            spending_proof.push(0);
        }
        assert!(
            finalized_faithful_spend_claims(&forest).is_err(),
            "a trailing byte must make the signed FNSP carrier noncanonical"
        );
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
                false,
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
            cadence_decision(3, false, Duration::from_millis(0), 120_000, false),
            CadenceAction::DrainTurns
        );
        // Turns win even when an ack is owed and the idle window expired.
        assert_eq!(
            cadence_decision(1, true, Duration::from_secs(3_600), 120_000, false),
            CadenceAction::DrainTurns
        );
        // Turns drain even when the idle heartbeat is disabled.
        assert_eq!(
            cadence_decision(1, false, Duration::from_millis(0), 0, false),
            CadenceAction::DrainTurns
        );
    }

    /// A received peer turn block is a mutation: it is answered with one
    /// reactive ack block promptly (next tick), not deferred to the heartbeat.
    #[test]
    fn received_peer_blocks_get_prompt_reactive_ack() {
        assert_eq!(
            cadence_decision(0, true, Duration::from_millis(0), 120_000, false),
            CadenceAction::ReactiveAck
        );
        // Reactive ack also fires when idle heartbeats are disabled —
        // attestation is mutation-driven, not heartbeat-driven.
        assert_eq!(
            cadence_decision(0, true, Duration::from_millis(0), 0, false),
            CadenceAction::ReactiveAck
        );
    }

    /// A node whose lace is EMPTY anchors it on the first tick instead of
    /// waiting out a full idle window.
    ///
    /// The idle timer starts at boot, so with the default 120s heartbeat a
    /// freshly started, perfectly correct node spent two minutes with an empty
    /// DAG: `/status.healthy` false (it requires `block_count > 0`),
    /// `/api/blocks` empty, and nothing for a peer to sync to. "Never produced a
    /// block" is exactly the condition the heartbeat exists for.
    #[test]
    fn an_empty_lace_is_anchored_on_the_first_tick() {
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(0), 120_000, true),
            CadenceAction::IdleHeartbeat,
            "a node with no blocks must produce its anchor block immediately"
        );
        // Once anchored, the ordinary idle discipline applies again.
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(0), 120_000, false),
            CadenceAction::Nothing
        );
        // A real mutation still wins over the anchor.
        assert_eq!(
            cadence_decision(2, false, Duration::from_millis(0), 120_000, true),
            CadenceAction::DrainTurns
        );
        // And an operator who disabled heartbeats entirely still gets none.
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(0), 0, true),
            CadenceAction::Nothing
        );
    }

    /// Nothing pending + window not expired ⇒ NO block. (The old cadence
    /// produced a heartbeat here unconditionally.)
    #[test]
    fn quiet_tick_produces_no_block() {
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(2_000), 120_000, false),
            CadenceAction::Nothing
        );
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(119_999), 120_000, false),
            CadenceAction::Nothing
        );
        // idle_heartbeat_ms == 0 disables the idle heartbeat entirely.
        assert_eq!(
            cadence_decision(0, false, Duration::from_secs(86_400), 0, false),
            CadenceAction::Nothing
        );
    }

    /// The idle heartbeat fires exactly at window expiry (liveness floor: the
    /// DAG still provably advances while idle, for finality probes + post-GST
    /// attestation exchange).
    #[test]
    fn idle_heartbeat_fires_at_window_expiry() {
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(120_000), 120_000, false),
            CadenceAction::IdleHeartbeat
        );
        assert_eq!(
            cadence_decision(0, false, Duration::from_millis(500_000), 120_000, false),
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
    fn consensus_time_flag_day_config_is_required_and_strict() {
        let mode = Some(crate::genesis::CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE);
        assert!(consensus_time_policy_v1_from_config(None, mode).is_err());
        assert!(consensus_time_policy_v1_from_config(Some(""), mode).is_err());
        assert!(consensus_time_policy_v1_from_config(Some("1.5"), mode).is_err());
        assert!(
            consensus_time_policy_v1_from_config(Some("1700000000"), None).is_err(),
            "causal replay time must never be presented as fair federation wall time"
        );
        assert!(
            consensus_time_policy_v1_from_config(Some("1700000000"), Some("federation-fair"))
                .is_err()
        );
        let policy = consensus_time_policy_v1_from_config(Some("1700000000"), mode)
            .expect("canonical explicitly-scoped deployment coordinate");
        assert_eq!(policy.genesis_unix_seconds(), 1_700_000_000);

        let genesis = serde_json::json!({
            "consensus_genesis_unix_seconds": 1_700_000_000_i64,
            "consensus_time_mode": crate::genesis::CONSENSUS_TIME_V1_DEVNET_CAUSAL_MODE,
        });
        assert_eq!(
            consensus_time_policy_v1_from_genesis(&genesis)
                .unwrap()
                .genesis_unix_seconds(),
            1_700_000_000
        );
        assert!(consensus_time_policy_v1_from_genesis(&serde_json::json!({})).is_err());
    }

    #[test]
    fn production_upgrades_raw_and_bundle_turns_to_signed_consensus_time() {
        let anchor = 1_700_000_000;
        let key = ed25519_dalek::SigningKey::from_bytes(&[0x61; 32]);
        let mut raw_lace = Blocklace::new_simple(key.clone());
        let mut bundle_lace = Blocklace::new_simple(key);
        raw_lace
            .enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
            .unwrap();
        bundle_lace
            .enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
            .unwrap();

        let raw = produce_payload_with_consensus_time_v1(
            &mut raw_lace,
            Payload::Turn(b"signed-turn".to_vec()),
            Vec::new(),
            i64::MAX,
        )
        .unwrap();
        let Payload::ConsensusTimedTurnV1(raw_payload) = raw.payload else {
            panic!("production must not sign a legacy turn carrier");
        };
        assert_eq!(raw_payload.consensus_time().unix_seconds(), anchor);
        assert_eq!(raw_payload.signed_turn(), b"signed-turn");

        let artifacts = TurnArtifactBundle {
            signed_turn: b"signed-turn".to_vec(),
            receipt: Some(b"receipt".to_vec()),
            witnessed_receipts: vec![b"witness-a".to_vec(), b"witness-b".to_vec()],
        };
        let bundled = produce_payload_with_consensus_time_v1(
            &mut bundle_lace,
            Payload::TurnBundle(artifacts.clone()),
            Vec::new(),
            i64::MIN,
        )
        .unwrap();
        let Payload::ConsensusTimedTurnV1(bundle_payload) = bundled.payload else {
            panic!("production must not sign a legacy bundle carrier");
        };
        assert_eq!(bundle_payload.consensus_time().unix_seconds(), anchor);
        assert_eq!(bundle_payload.signed_turn(), artifacts.signed_turn);
        assert_eq!(bundle_payload.receipt(), artifacts.receipt.as_deref());
        assert_eq!(
            bundle_payload.witnessed_receipts(),
            artifacts.witnessed_receipts
        );
    }

    #[test]
    fn opposite_genesis_clocks_produce_the_same_timed_block_identity() {
        let anchor = 1_700_000_000;
        let key = ed25519_dalek::SigningKey::from_bytes(&[0x62; 32]);
        let mut slow = Blocklace::new_simple(key.clone());
        let mut fast = Blocklace::new_simple(key);
        slow.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
            .unwrap();
        fast.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
            .unwrap();

        let slow_block = produce_payload_with_consensus_time_v1(
            &mut slow,
            Payload::Turn(b"same-turn".to_vec()),
            Vec::new(),
            i64::MIN,
        )
        .unwrap();
        let fast_block = produce_payload_with_consensus_time_v1(
            &mut fast,
            Payload::Turn(b"same-turn".to_vec()),
            Vec::new(),
            i64::MAX,
        )
        .unwrap();
        assert_eq!(slow_block.id(), fast_block.id());
        assert_eq!(slow_block.payload, fast_block.payload);
    }

    /// Live-handle composition tooth for private dependent execution:
    /// durable Ready claim/reservation → isolated CTM1 block production → one
    /// atomic block+Submitted transaction → ordinary finalized execution → the
    /// exact wake receipt removes the retained promise and appends Resolved.
    #[test]
    fn private_dependent_live_handle_atomically_submits_and_finalizes_exact_wake() {
        // The extracted ML-DSA cores are intentionally allocation-free and use
        // large fixed stack frames.  libtest/Tokio's default worker stack is too
        // small for the verified keygen+sign crossing exercised below, so keep
        // the requirement local to this live composition tooth rather than
        // making the whole test process depend on RUST_MIN_STACK.
        std::thread::Builder::new()
            .name("private-dependent-live-tooth".into())
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                tokio::runtime::Builder::new_multi_thread()
                    .worker_threads(2)
                    .thread_stack_size(64 * 1024 * 1024)
                    .enable_all()
                    .build()
                    .expect("private dependent test runtime")
                    .block_on(private_dependent_live_handle_tooth_inner());
            })
            .expect("spawn private dependent live tooth")
            .join()
            .expect("private dependent live tooth thread");
    }

    async fn private_dependent_live_handle_tooth_inner() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let _ = crate::install_mldsa_verified_keygen_core_real();
        let _ = crate::install_mldsa_verified_sign_core_real();
        let _ = crate::install_mldsa_verified_verify_core();
        assert!(
            dregg_pq::lean_keygen_core_real_installed()
                && dregg_pq::lean_sign_core_real_installed()
                && dregg_pq::lean_verify_core_real_installed(),
            "live private-ingress tooth requires the verified ML-DSA cores"
        );

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let actor_seed = [0xA6; 32];
        let actor_clerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(actor_seed));
        let actor_pk = actor_clerk.public_key().0;
        let token = *blake3::hash(b"default").as_bytes();
        let actor_cell = dregg_cell::Cell::with_balance(actor_pk, token, 1_000_000);
        let actor = actor_cell.id();
        let destination = dregg_cell::CellId([0xA7; 32]);

        let federation_id = {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
            s.ledger.insert_cell(actor_cell).expect("fund wake actor");
            let local_pk = s.cclerk.public_key();
            let local_seed = s.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("local PQ key");
            let actor_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&actor_seed)
                    .public_bytes()
                    .try_into()
                    .expect("actor PQ key");
            s.set_federation_keys_hybrid(
                vec![local_pk, actor_clerk.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(actor_pq),
                ],
            );
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let signed =
            signed_transfer_turn(&actor_clerk, actor, destination, 4_200, 0, &federation_id);
        let wake = signed.turn.clone();
        let wake_hash = wake.hash();
        let payload = postcard::to_stdvec(&signed).expect("canonical signed wake");
        {
            let s = state.read().await;
            let executor = crate::executor_setup::new_submit_executor(&s);
            crate::signed_turn_validation::validate_signed_turn(
                &signed,
                &executor,
                s.ledger.get(&actor),
            )
            .expect("wake passes canonical ingress before custody release");
        }

        // Build the exact durable Published predecessor and Ready observer row
        // that a finalized React carrier would leave behind.
        let condition = dregg_turn::ProofCondition::HashPreimage { hash: [0xA8; 32] };
        let mut registry = dregg_turn::PendingTurnRegistry::new();
        let empty = registry.to_canonical_bytes().expect("empty registry");
        registry
            .try_submit_pending_at(
                wake.clone(),
                dregg_turn::ResolutionCondition::AwaitCondition(condition.clone()),
                100,
                0,
            )
            .expect("register wake");
        registry
            .mark_react_ready(&wake_hash, &actor, &condition, &wake, 1)
            .expect("release wake");
        let carrier_receipt = sample_receipt(0xA9);
        let ready_events = registry.resolve(
            carrier_receipt.turn_hash,
            dregg_turn::ResolutionOutcome::Resolved(carrier_receipt.clone()),
        );
        assert!(matches!(
            ready_events.as_slice(),
            [dregg_turn::ResolutionEvent::ReadyToExecute { turn_hash, turn }]
                if *turn_hash == wake_hash && turn.hash() == wake_hash
        ));
        let published = registry.to_canonical_bytes().expect("published registry");
        let ready_candidates = crate::promise_resolutions::resolution_candidates(
            0,
            carrier_receipt.receipt_hash(),
            &ready_events,
        )
        .expect("Ready candidates");
        let (store, ledger_root, local_creator) = {
            let s = state.read().await;
            (
                s.store.clone(),
                canonical_ledger_root(&s.ledger),
                s.cclerk.public_key().0,
            )
        };
        store
            .commit_finalized_turn_with_executor_state(
                0,
                &dregg_persist::CommitRecord {
                    ordinal: 0,
                    height: 1,
                    block_id: [0xAA; 32],
                    block_executed_up_to: 0,
                    turn_hash: carrier_receipt.turn_hash,
                    creator: local_creator,
                    receipt_hash: carrier_receipt.receipt_hash(),
                    ledger_root,
                    touched_cells: Vec::new(),
                    removed: Vec::new(),
                },
                &[],
                &dregg_persist::FinalizedExecutorConsensusState {
                    reactive_registry: dregg_persist::ReactiveRegistryCasV1::new(
                        dregg_persist::reactive_registry_commitment(&empty),
                        published,
                    ),
                    promise_resolutions: ready_candidates,
                    ..Default::default()
                },
            )
            .expect("persist finalized Ready carrier");
        store
            .arm_private_dependent_turn_v1(wake_hash, wake_hash, vec![0xAB; 80], 100)
            .expect("arm private wake");
        let ready = store
            .promise_resolution_batch_for_commit_v1(0)
            .expect("read Ready batch")
            .expect("Ready batch exists");
        let claim = store
            .claim_private_dependent_turn_v1(wake_hash, ready[0].sequence)
            .expect("claim Ready")
            .expect("unique claim");
        let reservation_id = dregg_persist::private_dependent_ingress_reservation_id_v1(
            claim.promise_id,
            claim.signed_turn_hash,
            claim.ready_sequence,
            claim.event_id,
        );

        let self_key = local_creator;
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        handle
            .lace
            .write()
            .await
            .enable_consensus_time_v1(ConsensusTimePolicyV1::new(1_700_000_000))
            .expect("enable CTM1");
        let block_id = handle
            .submit_private_dependent_turn(&state, reservation_id, payload.clone())
            .await
            .expect("live private handle accepts")
            .expect("solo handle produces immediately");

        // The block and Submitted row are already one crash-consistent image,
        // before ordinary finalization is invoked.
        assert!(matches!(
            store
                .private_dependent_turn_status_v1(wake_hash)
                .expect("custody status")
                .expect("custody row")
                .status,
            dregg_persist::PrivateDependentTurnStatusV1::Submitted {
                ingress_id,
                ..
            } if ingress_id == block_id.0
        ));
        let produced = handle
            .lace
            .read()
            .await
            .get(&block_id)
            .expect("block installed only after durable accept")
            .clone();
        assert!(
            store
                .load_all_blocks()
                .expect("durable blocks")
                .iter()
                .any(|stored| stored == &produced),
            "the exact live block must be durable before publication"
        );
        let Payload::ConsensusTimedTurnV1(timed) = &produced.payload else {
            panic!("private live handle must produce CTM1");
        };
        assert_eq!(timed.signed_turn(), payload);

        let outcome = execute_finalized_turn(
            &state,
            &handle,
            block_id,
            timed.signed_turn(),
            None,
            Some(timed.consensus_time().unix_seconds()),
            1,
        )
        .await;
        assert!(matches!(
            outcome,
            FinalizedExecutionOutcome::Committed {
                block_id: committed,
                ..
            } if committed == block_id
        ));
        assert!(
            dregg_turn::PendingTurnRegistry::from_canonical_bytes(
                &store
                    .load_latest_reactive_registry_snapshot_bytes()
                    .expect("terminal registry"),
            )
            .expect("decode terminal registry")
            .is_empty(),
            "only the exact finalized wake receipt removes the retained promise"
        );
        let rows = store
            .promise_resolutions_after_v1(None, 10)
            .expect("resolution history");
        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows[0].outcome,
            dregg_persist::PromiseResolutionKindV1::ReadyToExecute
        );
        assert!(matches!(
            rows[1].outcome,
            dregg_persist::PromiseResolutionKindV1::Resolved { .. }
        ));
        assert_eq!(
            store
                .lookup_turn(&wake_hash)
                .expect("turn index")
                .expect("wake finalized")
                .block_id,
            block_id.0
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

    /// A best-effort executed-id flush is not terminal authority for any turn
    /// carrier. This is the timed-turn crash image: the id reached the cursor
    /// projection, but neither a commit row nor authenticated rejection did.
    /// Restart must re-serve it; conversely a durable terminal row restores it
    /// even when the cursor flush itself was lost.
    #[test]
    fn timed_turn_restart_requires_durable_terminal_authority() {
        let key = ed25519_dalek::SigningKey::from_bytes(&[0x73; 32]);
        let mut lace = Blocklace::new_simple(key);
        let anchor = 1_700_000_000;
        lace.enable_consensus_time_v1(dregg_blocklace::finality::ConsensusTimePolicyV1::new(
            anchor,
        ))
        .expect("install consensus-time policy");
        let block = lace
            .add_consensus_timed_turn_v1(
                dregg_blocklace::finality::ConsensusTimedTurnPayloadV1::new(
                    anchor,
                    b"signed-turn".to_vec(),
                ),
            )
            .expect("add timed turn");
        let id = block.id();

        let stale =
            reconcile_restored_execution_ids(&lace, vec![id], &std::collections::HashSet::new());
        assert!(
            stale.is_empty(),
            "persisted timed-turn id without commit/rejection authority must be retried"
        );

        let durable = std::collections::HashSet::from([id]);
        let restored = reconcile_restored_execution_ids(&lace, Vec::new(), &durable);
        assert_eq!(
            restored,
            vec![id],
            "durable terminal authority restores an id across a lost cursor flush"
        );
    }

    /// A deterministic rejection is terminal only if its authenticated row was
    /// actually written. A store failure must remain retryable, leave no row,
    /// and therefore cannot authorize finality-cursor acknowledgement.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn rejection_store_failure_remains_retryable_and_unrecorded() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let block_id = BlockId([0x74; 32]);
        *FAIL_FINALIZED_REJECTION_WRITE_FOR_BLOCK
            .lock()
            .expect("rejection failure hook mutex") = Some(block_id.0);
        let handle = test_handle_with_committee([0x75; 32], vec![[0x75; 32]]).await;

        let malformed_payload = b"not-a-canonical-signed-turn";
        let outcome =
            execute_finalized_turn(&state, &handle, block_id, malformed_payload, None, None, 0)
                .await;
        assert!(matches!(
            outcome,
            FinalizedExecutionOutcome::RetryableOperational { block_id: id, .. } if id == block_id
        ));
        assert!(
            FAIL_FINALIZED_REJECTION_WRITE_FOR_BLOCK
                .lock()
                .expect("rejection failure hook mutex")
                .is_none(),
            "one-shot fault must fire at the real rejection write"
        );
        let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &block_id.0,
        );
        assert!(
            state
                .read()
                .await
                .store
                .get_config(&key)
                .expect("read rejection row")
                .is_none(),
            "failed rejection write must not leave terminal authority"
        );
    }

    /// A well-formed exact-v3 carrier with attacker-chosen invalid proof bytes is a terminal
    /// payload refusal, not a node-integrity failure.  Its authenticated rejection row must both
    /// authorize the live ACK and reconstruct that terminal identity after a crash which lost the
    /// best-effort executed-id projection.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn live_exact_invalid_proof_is_durable_ack_authority_after_restart() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let _ = crate::install_mldsa_verified_keygen_core_real();
        let _ = crate::install_mldsa_verified_sign_core_real();
        let _ = crate::install_mldsa_verified_verify_core();
        let verified_pq = dregg_pq::lean_keygen_core_real_installed()
            && dregg_pq::lean_sign_core_real_installed()
            && dregg_pq::lean_verify_core_real_installed();
        if !verified_pq {
            assert_ne!(
                std::env::var("DREGG_REQUIRE_PQ_CORES").as_deref(),
                Ok("1"),
                "live exact-proof falsifier requires the three verified ML-DSA cores"
            );
            assert_eq!(
                std::env::var("DREGG_ALLOW_UNAUDITED_PQ").as_deref(),
                Ok("1"),
                "an explicit test-only fallback is required when verified ML-DSA cores are absent"
            );
            eprintln!("TEST-ONLY: exact ACK control-flow runs with explicit unaudited PQ fallback");
        }
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let actor_seed = [0x76; 32];
        let actor_clerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(actor_seed));
        let default_token = *blake3::hash(b"default").as_bytes();
        let actor_cell =
            dregg_cell::Cell::with_balance(actor_clerk.public_key().0, default_token, 100_000);
        let actor = actor_cell.id();

        let local_pk = {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
            let solo_seed = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(solo_seed));
            s.ledger
                .insert_cell(actor_cell)
                .expect("insert exact actor");

            let local_pk = s.cclerk.public_key();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&solo_seed)
                    .public_bytes()
                    .try_into()
                    .expect("fixed-size local PQ key");
            let actor_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&actor_seed)
                    .public_bytes()
                    .try_into()
                    .expect("fixed-size actor PQ key");
            s.set_federation_keys_hybrid(
                vec![local_pk, actor_clerk.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(actor_pq),
                ],
            );
            s.federation_configured = true;
            s.store
                .checkpoint_ledger(&s.ledger, 0)
                .expect("canonical actor checkpoint");
            // Keep a real durable tail above the compacted floor so actor authority is rooted in
            // the finalized overlay chain (the invalid proof fails before this unrelated row can
            // otherwise matter to exact execution).
            s.store
                .commit_finalized_turn(
                    0,
                    &dregg_persist::CommitRecord {
                        ordinal: 0,
                        height: 0,
                        block_id: [0x70; 32],
                        block_executed_up_to: 0,
                        turn_hash: [0x71; 32],
                        creator: local_pk.0,
                        receipt_hash: [0x72; 32],
                        ledger_root: canonical_ledger_root(&s.ledger),
                        touched_cells: Vec::new(),
                        removed: Vec::new(),
                    },
                )
                .expect("durable actor-root tail");
            local_pk
        };

        let invalid_carrier =
            dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier::new(
                0,
                vec![0xA5, 0x5A],
            )
            .expect("bounded exact carrier")
            .encode();
        let unsigned = dregg_turn::Action {
            target: actor,
            method: [0x77; 32],
            args: Vec::new(),
            authorization: dregg_turn::Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![dregg_turn::Effect::NoteSpend {
                nullifier: dregg_cell::Nullifier([0x78; 32]),
                note_tree_root: [0x79; 32],
                value: 0,
                asset_type: 23,
                spending_proof: invalid_carrier,
                value_commitment: None,
            }],
            may_delegate: dregg_turn::DelegationMode::None,
            commitment_mode: dregg_turn::CommitmentMode::Full,
            balance_change: None,
            witness_blobs: Vec::new(),
        };
        let mut forest = dregg_turn::CallForest::new();
        // Exact-v3's currently characterized envelope deliberately uses an unchecked action; the
        // hybrid-authenticated outer SignedTurn is the application perimeter.
        forest.add_root(unsigned);
        let signed = actor_clerk.sign_turn(&dregg_turn::Turn {
            agent: actor,
            nonce: 0,
            fee: 0,
            memo: Some("invalid exact proof must ACK".into()),
            valid_until: Some(i64::MAX / 2),
            call_forest: forest,
            depends_on: Vec::new(),
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        });
        let payload = postcard::to_stdvec(&signed).expect("exact payload");
        let mut restored_lace =
            Blocklace::new_simple(ed25519_dalek::SigningKey::from_bytes(&[0x7A; 32]));
        let block_id = restored_lace.add_block(Payload::Turn(payload.clone())).id();
        let handle = test_handle_with_committee(local_pk.0, vec![local_pk.0]).await;

        let outcome =
            execute_finalized_turn(&state, &handle, block_id, &payload, None, None, 1).await;
        assert!(
            matches!(
                &outcome,
                FinalizedExecutionOutcome::DeterministicallyRejected {
                    block_id: rejected,
                    reason_code,
                } if *rejected == block_id && reason_code == "exact-fnsp-v3-proof-refused"
            ),
            "unexpected invalid-proof outcome: {outcome:?}"
        );

        drop(state);
        let restarted = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("restart node");
        let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &block_id.0,
        );
        let row = restarted
            .read()
            .await
            .store
            .get_config(&key)
            .expect("read exact rejection")
            .expect("exact rejection is durable");
        let rejection =
            crate::signed_turn_validation::FinalizedPayloadRejectionRecord::decode_authenticated(
                &row, block_id.0, &payload,
            )
            .expect("restart authenticates exact rejection");
        assert_eq!(rejection.reason_code, "exact-fnsp-v3-proof-refused");

        let durable_terminal = std::collections::HashSet::from([block_id]);
        assert_eq!(
            reconcile_restored_execution_ids(&restored_lace, Vec::new(), &durable_terminal),
            vec![block_id],
            "lost cursor flush must be reconstructed from authenticated exact-proof rejection"
        );
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
            dregg_turn_prover::aggregate_bilateral_prover::prove_aggregated_bundle(&turn, &entries)
                .expect("cross-sourced WRs must aggregate");
        assert_eq!(bundle.participating_cells.len(), 2);
        dregg_turn_prover::aggregate_bilateral_prover::verify_aggregated_bundle(&bundle)
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

    /// Build an ordinary finalized event turn carrying one public PoA Signal
    /// claim (or a deliberately malformed reserved event). Authority still
    /// comes from the outer hybrid SignedTurn, never from event fields.
    fn signed_signal_event_turn(
        cclerk: &dregg_sdk::AgentCipherclerk,
        actor: dregg_cell::CellId,
        event: dregg_turn::action::Event,
        nonce: u64,
        federation_id: &[u8; 32],
    ) -> dregg_sdk::SignedTurn {
        let effect = dregg_turn::Effect::EmitEvent { cell: actor, event };
        signed_signal_effects_turn(cclerk, actor, vec![effect], nonce, federation_id)
    }

    fn signed_signal_effects_turn(
        cclerk: &dregg_sdk::AgentCipherclerk,
        actor: dregg_cell::CellId,
        effects: Vec<dregg_turn::Effect>,
        nonce: u64,
        federation_id: &[u8; 32],
    ) -> dregg_sdk::SignedTurn {
        let action = cclerk.make_action(actor, "poa-signal", effects, federation_id);
        let mut call_forest = dregg_turn::CallForest::new();
        call_forest.add_root(action);
        let mut turn = dregg_turn::Turn {
            agent: actor,
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
        let estimator = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
        turn.fee = estimator.estimate_cost(&turn);
        cclerk.sign_turn(&turn)
    }

    fn signed_signal_turn(
        cclerk: &dregg_sdk::AgentCipherclerk,
        actor: dregg_cell::CellId,
        mission_id: u64,
        nonce: u64,
        federation_id: &[u8; 32],
    ) -> dregg_sdk::SignedTurn {
        // ⚠ The solving code cannot be written down: the instance is drawn per
        // (slot, mission, PLAYER), so it differs for every fixture signer. Ask Lean
        // for this player's answer exactly as the node does.
        // `mission_id` is preserved because callers use a WRONG one (2, against an
        // activated mission 1) to exercise the adapter's semantic refusal. Only the
        // CODE is derived.
        let solving = crate::poa_signal_adapter::solving_claim_for_finality_test(
            &crate::poa_signal_adapter::fixture_signal_head_for_finality_test(*federation_id),
            &crate::poa_signal_adapter::fixture_signal_slot_for_finality_test(*federation_id),
            *federation_id,
            cclerk.public_key().0,
            [0u8; 32],
        );
        let claim =
            dregg_sdk::poa_signal::SignalClaimV1::new(mission_id, solving.transcript()).unwrap();
        let mut turn =
            dregg_sdk::poa_signal::signal_claim_turn(&cclerk.public_key().0, nonce, None, claim);
        assert_eq!(turn.agent, actor, "fixture actor is the signing identity");
        let unsigned = turn.call_forest.roots[0].action.clone();
        turn.call_forest.roots[0].action = cclerk.sign_action(unsigned, federation_id);
        turn.call_forest.roots[0].hash = [0; 32];
        turn.call_forest.forest_hash = [0; 32];
        cclerk.sign_turn(&turn)
    }

    /// Signal is a dedicated judged transition, not an annotation that may be
    /// attached to an otherwise arbitrary Dregg turn. These cases exercise the
    /// classifier before executor/finality state exists, so every extra
    /// semantic surface is refused by construction rather than by a later
    /// rollback.
    #[test]
    fn poa_signal_carrier_is_one_exact_root_action_and_nothing_else() {
        let seed = *blake3::hash(b"poa-signal-carrier-shape:actor").as_bytes();
        let cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        let actor = dregg_cell::CellId::derive_raw(
            &cclerk.public_key().0,
            blake3::hash(b"default").as_bytes(),
        );
        let federation_id = [0x41; 32];
        let exact = signed_signal_turn(&cclerk, actor, 1, 0, &federation_id);
        assert!(matches!(
            finalized_signal_claim(&exact.turn),
            Ok(Some(claim)) if claim.mission_id() == 1
        ));

        let ordinary = signed_transfer_turn(&cclerk, actor, actor, 0, 0, &federation_id);
        assert!(matches!(finalized_signal_claim(&ordinary.turn), Ok(None)));

        let assert_noncanonical = |turn: &dregg_turn::Turn, case: &str| {
            assert!(
                matches!(
                    finalized_signal_claim(turn),
                    Err(FinalizedSignalRouteError::NonCanonicalCarrier(_))
                ),
                "{case} must not share the Signal judge"
            );
        };

        let mut extra_effect = exact.turn.clone();
        extra_effect.call_forest.roots[0]
            .action
            .effects
            .push(dregg_turn::Effect::IncrementNonce { cell: actor });
        assert_noncanonical(&extra_effect, "ordinary co-effect");

        let mut extra_root = exact.turn.clone();
        let second = cclerk.make_action(
            actor,
            "ordinary",
            vec![dregg_turn::Effect::IncrementNonce { cell: actor }],
            &federation_id,
        );
        extra_root.call_forest.add_root(second.clone());
        assert_noncanonical(&extra_root, "second root action");

        let mut child = exact.turn.clone();
        child.call_forest.roots[0].add_child(second);
        assert_noncanonical(&child, "child action");

        let mut wrong_method = exact.turn.clone();
        wrong_method.call_forest.roots[0].action.method = dregg_turn::action::symbol("ordinary");
        assert_noncanonical(&wrong_method, "wrong method");

        let other = dregg_cell::CellId::derive_raw(&[0x52; 32], &[0x53; 32]);
        let mut wrong_target = exact.turn.clone();
        wrong_target.call_forest.roots[0].action.target = other;
        assert_noncanonical(&wrong_target, "wrong action target");

        let mut wrong_event_cell = exact.turn.clone();
        let dregg_turn::Effect::EmitEvent { cell, .. } =
            &mut wrong_event_cell.call_forest.roots[0].action.effects[0]
        else {
            panic!("fixture Signal carrier must be EmitEvent")
        };
        *cell = other;
        assert_noncanonical(&wrong_event_cell, "wrong event cell");

        let mut balance_side_channel = exact.turn.clone();
        balance_side_channel.call_forest.roots[0]
            .action
            .balance_change = Some(0);
        assert_noncanonical(&balance_side_channel, "balance-change side channel");

        let mut unchecked_auth = exact.turn.clone();
        unchecked_auth.call_forest.roots[0].action.authorization =
            dregg_turn::Authorization::Unchecked;
        assert_noncanonical(&unchecked_auth, "unsigned action authorization");

        let mut witness_sidecar = exact.turn.clone();
        witness_sidecar.call_forest.roots[0]
            .action
            .witness_blobs
            .push(dregg_turn::action::WitnessBlob::preimage([0x60; 32]));
        assert_noncanonical(&witness_sidecar, "action witness sidecar");

        let mut execution_sidecar = exact.turn.clone();
        execution_sidecar.execution_proof = Some(vec![1, 2, 3]);
        execution_sidecar.execution_proof_cell = Some(actor);
        execution_sidecar.execution_proof_new_commitment = Some([0x61; 32]);
        assert_noncanonical(&execution_sidecar, "sovereign execution-proof sidecar");

        let mut custom_sidecar = exact.turn.clone();
        custom_sidecar.custom_program_proofs = Some(Vec::new());
        assert_noncanonical(&custom_sidecar, "custom-proof presence sidecar");

        let mut dependency_sidecar = exact.turn.clone();
        dependency_sidecar.depends_on.push([0x62; 32]);
        assert_noncanonical(&dependency_sidecar, "turn dependency sidecar");

        let mut overfee = exact.turn.clone();
        overfee.fee = overfee
            .fee
            .checked_add(1)
            .expect("fixture fee below u64 max");
        assert_noncanonical(&overfee, "caller-selected fee mutation");

        let mut multiple = exact.turn.clone();
        let duplicate_claim = multiple.call_forest.roots[0].action.effects[0].clone();
        multiple.call_forest.roots[0]
            .action
            .effects
            .push(duplicate_claim);
        assert!(matches!(
            finalized_signal_claim(&multiple),
            Err(FinalizedSignalRouteError::Multiple)
        ));
    }

    /// Stand up the exact hybrid perimeter used by the finalized executor and,
    /// when requested, install the authenticated test deployment head before
    /// any commit. Production deliberately has no browser-driven auto-genesis.
    async fn poa_finality_test_state(
        path: &std::path::Path,
        initialize_head: bool,
    ) -> (
        crate::state::NodeState,
        dregg_sdk::AgentCipherclerk,
        dregg_cell::CellId,
        [u8; 32],
    ) {
        let state = crate::state::NodeState::new(path, Vec::new()).expect("node state");
        let actor_seed = *blake3::hash(b"poa-signal-finality:actor").as_bytes();
        let actor_cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(actor_seed));
        let default_token = *blake3::hash(b"default").as_bytes();
        let actor = dregg_cell::CellId::derive_raw(&actor_cclerk.public_key().0, &default_token);
        let federation_id;
        {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
            let local_pk = s.cclerk.public_key();
            let local_seed = s.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("local ML-DSA key");
            let actor_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&actor_seed)
                    .public_bytes()
                    .try_into()
                    .expect("actor ML-DSA key");
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    actor_cclerk.public_key().0,
                    default_token,
                    1_000_000,
                ))
                .expect("fund Signal actor");
            s.set_federation_keys_hybrid(
                vec![local_pk, actor_cclerk.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(actor_pq),
                ],
            );
            federation_id = crate::executor_setup::federation_id_for_executor(&s);
            if initialize_head {
                let head =
                    crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id);
                s.store
                    .initialize_poa_signal_head(&head)
                    .expect("install authenticated PoA Signal test deployment");
                // A finalized Signal claim now requires an OPEN SLOT: without one
                // the node refuses rather than drawing an uncommitted instance.
                s.store
                    .install_poa_signal_slot_for_test(
                        &crate::poa_signal_adapter::fixture_signal_slot_for_finality_test(
                            federation_id,
                        ),
                    )
                    .expect("open a PoA Signal slot for the test deployment");
                // …AND A PLAYED SESSION. Since the transcript-provenance gate landed
                // (`poa_signal_adapter::verify_claim_transcript_was_played`), a
                // finalized claim must name rounds THIS NODE classified, so a
                // finality fixture that only installs a head and a slot is a fixture
                // whose claim can never be judged: it dies at the gate as
                // `poa-signal-transcript-no-session` and every downstream assertion
                // about the weld measures nothing.
                //
                // The rounds are played through the REAL Lean oracle
                // (`play_session_for_test`), not written by hand, so this fixture
                // cannot pass the gate while disagreeing with the rule.
                let head =
                    crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id);
                let slot =
                    crate::poa_signal_adapter::fixture_signal_slot_for_finality_test(federation_id);
                if dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available()
                    && dregg_lean_ffi::poa_signal_feedback_ffi::poa_signal_feedback_available()
                {
                    let solving = crate::poa_signal_adapter::solving_claim_for_finality_test(
                        &head,
                        &slot,
                        federation_id,
                        actor_cclerk.public_key().0,
                        [0u8; 32],
                    );
                    crate::poa_signal_adapter::play_session_for_test(
                        &s.store,
                        &head,
                        &slot,
                        federation_id,
                        actor_cclerk.public_key().0,
                        solving.transcript(),
                    );
                }
            }
        }
        (state, actor_cclerk, actor, federation_id)
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

    /// The complete content image of a ledger: every cell's canonical `postcard`
    /// encoding, keyed and ordered by id. Stronger than comparing
    /// `canonical_ledger_root` (which is a hash) and stronger than comparing
    /// balances (which misses pk / asset / c-list drift) — two ledgers with equal
    /// images are equal in every consensus-observable byte.
    fn ledger_content_image(ledger: &dregg_cell::Ledger) -> Vec<(dregg_cell::CellId, Vec<u8>)> {
        let mut image: Vec<(dregg_cell::CellId, Vec<u8>)> = ledger
            .iter()
            .map(|(id, cell)| (*id, postcard::to_stdvec(cell).expect("cell encodes")))
            .collect();
        image.sort_by(|a, b| a.0.0.cmp(&b.0.0));
        image
    }

    /// ⚑ THE PROVISIONING SKIP, DRIVEN ON TWO REAL NODES — what it can carry is a
    /// LOUD refusal, never a silent state fork.
    ///
    /// `provision_transfer_destinations` reads the Transfer's SOURCE cell out of
    /// the LOCAL ledger to learn which asset to mint the landing site in, and
    /// `continue`s when the source is absent. That read is a dependence on local
    /// state inside a function whose docblock used to claim it provisioned "purely
    /// from the turn's data", so the question this test settles is whether the skip
    /// can produce a SILENT fork: two nodes both COMMITTING the same finalized turn
    /// to different content, each believing it applied consensus faithfully.
    ///
    /// Two independent `NodeState`s — separate data dirs, stores, ledgers, receipt
    /// chains and attested-root histories — are seeded IDENTICALLY except for ONE
    /// cell: the Transfer's source, which node A holds and node B does not. Both
    /// are handed the SAME finalized `SignedTurn` bytes through the production
    /// `execute_finalized_turn`. They share a validator key so both derive the same
    /// `federation_id` and the one action signature is admissible on both, which
    /// leaves the missing source cell as the ONLY independent variable.
    ///
    /// The source is deliberately NOT the turn's agent, because for `from == agent`
    /// the skip is UNREACHABLE: `claimed_actor_cell` installs the signer's canonical
    /// account on the execution candidate BEFORE provisioning runs, and
    /// `validate_signed_turn` refuses the payload outright when there is no actor to
    /// claim. Reaching the skip needs a cross-cell Send, which is what the agent's
    /// c-list grant below sets up — granted identically on both nodes, so what
    /// differs is only whether the cap's TARGET exists locally.
    ///
    /// What the two nodes produce:
    ///   A — COMMITS: the landing site is provisioned in the source's asset, the
    ///       value moves, the attested height advances 0 -> 1.
    ///   B — REFUSES, and its authoritative state is byte-identical before and
    ///       after: the executor cannot find the source (`apply.rs`'s
    ///       `CellNotFound`), `TurnResult::Rejected` discards the whole isolated
    ///       candidate without an overlay, and the refusal is recorded durably
    ///       against the block. Height stays 0.
    ///
    /// So the skip is OUTCOME-NEUTRAL: on the node where it fires, provisioning or
    /// not provisioning cannot change the post-state, because that node writes NO
    /// post-state at all. That — not "byte-determinism from the turn alone" — is
    /// the property carrying the cross-node uniformity argument, and it is the
    /// property `provision_transfer_destinations`'s docblock now states.
    ///
    /// ⚑ MEASURED, 2026-08-06, by running this test against three deliberately
    /// broken copies of the production path (on a build lane, never the shared
    /// tree). The 2×2 isolates which mechanism is actually load-bearing:
    ///
    /// | provisioning on absent source | `TurnResult::Rejected` arm | result |
    /// |---|---|---|
    /// | SKIPS (HEAD)                  | discards the candidate     | PASS   |
    /// | mints a GUESSED-asset stub    | discards the candidate     | PASS   |
    /// | SKIPS                         | installs the overlay       | FAIL   |
    /// | mints a GUESSED-asset stub    | installs the overlay       | FAIL   |
    ///
    /// The skip's column does not move the result: replacing it with the
    /// invent-a-landing-site "fix" leaves B byte-identical either way. The
    /// REJECTION ARM's discard is the entire guard — and note the third row, which
    /// reds on the AGENT's cell, not the destination: a rejected candidate still
    /// carries the executor's phase-1 fee debit and nonce tick (the arm's own
    /// comment says so), so `touched_ids` is NON-EMPTY on a refused turn and an
    /// overlay there would publish a charge for a turn the node refused. This test
    /// is therefore also the live guard on "a refused finalized turn writes
    /// nothing", which is the broader property and the one that can go red.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn finalized_transfer_source_absent_refuses_it_does_not_fork_state() {
        let _ = tracing_subscriber::fmt::try_init();
        let _ = rustls::crypto::ring::default_provider().install_default();

        let default_token = *blake3::hash(b"default").as_bytes();

        // The acting identity: present, funded and hybrid-enrolled on BOTH nodes.
        let agent_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"provision-skip:agent").as_bytes(),
        ));
        let agent_pk = agent_cclerk.public_key().0;
        let agent = dregg_cell::CellId::derive_raw(&agent_pk, &default_token);

        // The Transfer SOURCE — a cell the agent reaches through its c-list, held
        // by node A only. The DESTINATION is absent everywhere, so provisioning is
        // the only thing that can mint it.
        let source_pk = *blake3::hash(b"provision-skip:source").as_bytes();
        let source = dregg_cell::CellId::derive_raw(&source_pk, &default_token);
        let dest = dregg_cell::CellId([0xD5u8; 32]);
        const SOURCE_FUNDING: i64 = 500_000;
        const MOVED: u64 = 4_200;

        // ONE validator key, TWO data dirs. `set_federation_keys_hybrid` re-derives
        // `federation_id` from the committee, so a shared key is what makes ONE
        // signed turn admissible on both nodes; the stores and ledgers stay fully
        // independent.
        let node_key = *blake3::hash(b"provision-skip:validator").as_bytes();
        let tmp_a = tempfile::tempdir().expect("tempdir A");
        let tmp_b = tempfile::tempdir().expect("tempdir B");
        let node_a = crate::state::NodeState::with_cclerk(tmp_a.path(), vec![], node_key)
            .expect("node A state");
        let node_b = crate::state::NodeState::with_cclerk(tmp_b.path(), vec![], node_key)
            .expect("node B state");

        for (node, holds_source) in [(&node_a, true), (&node_b, false)] {
            let mut s = node.write().await;
            s.lean_producer_enabled = false;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
            s.federation_configured = true;
            let mut agent_cell = dregg_cell::Cell::with_hybrid_balance(
                agent_pk,
                &agent_cclerk.ml_dsa_public_bytes(),
                default_token,
                1_000_000,
            )
            .expect("canonical ML-DSA-65 agent identity");
            agent_cell
                .capabilities
                .grant(source, dregg_cell::AuthRequired::None)
                .expect("cross-cell Send slot");
            s.ledger.insert_cell(agent_cell).expect("seed agent");
            if holds_source {
                let mut source_cell =
                    dregg_cell::Cell::with_balance(source_pk, default_token, SOURCE_FUNDING);
                // The other half of a cross-cell Send: `check_cross_cell_permission`
                // wants BOTH a c-list path from the actor AND `Send: None` on the
                // target itself (the default is `Signature`, and a zero-pk-adjacent
                // vessel cannot produce one). This is the ordinary open-perms world
                // cell — the shape `deos_host::open_permissions` and
                // `starbridge_seed::grant_operator_reach` mint in production.
                source_cell.permissions.send = dregg_cell::AuthRequired::None;
                s.ledger.insert_cell(source_cell).expect("seed source");
            }
            // A solo node's committee IS its own key (see the fixture note on
            // `solo_finalization_recovers_receipt_durable_ledger_absent_crash`: a
            // committee the node is not a member of leaves the attested root
            // unsigned and the durable commit correctly refuses).
            let self_pk = s.cclerk.public_key();
            let (self_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(
                &s.cclerk.gossip_signing_key().to_bytes(),
            );
            s.set_federation_keys_hybrid(vec![self_pk], vec![self_ml_dsa]);
        }

        let federation_id = {
            let s = node_a.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        assert_eq!(
            federation_id,
            {
                let s = node_b.read().await;
                crate::executor_setup::federation_id_for_executor(&s)
            },
            "the two nodes must agree on the federation id, or they are not applying the SAME turn"
        );

        // ONE finalized SignedTurn: the agent moves value OUT OF `source` (not out
        // of its own cell) into an unseen destination.
        let signed = {
            let action = agent_cclerk.make_action(
                agent,
                "cross-cell-transfer",
                vec![dregg_turn::Effect::Transfer {
                    from: source,
                    to: dest,
                    amount: MOVED,
                }],
                &federation_id,
            );
            let mut call_forest = dregg_turn::CallForest::new();
            call_forest.add_root(action);
            let mut turn = dregg_turn::Turn {
                agent,
                nonce: 0,
                fee: 0,
                memo: None,
                valid_until: Some(i64::MAX / 2),
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
            turn.fee = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default())
                .estimate_cost(&turn);
            agent_cclerk.sign_turn(&turn)
        };
        let payload = postcard::to_stdvec(&signed).expect("encode signed turn");

        // ── BEFORE ────────────────────────────────────────────────────────────
        async fn attested_height(node: &NodeState) -> u64 {
            node.read()
                .await
                .store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0)
        }
        let root_a_before = {
            let s = node_a.read().await;
            canonical_ledger_root(&s.ledger)
        };
        let (root_b_before, image_b_before, ledger_b_before) = {
            let s = node_b.read().await;
            (
                canonical_ledger_root(&s.ledger),
                ledger_content_image(&s.ledger),
                s.ledger.clone(),
            )
        };
        assert_eq!(attested_height(&node_a).await, 0, "A starts at genesis");
        assert_eq!(attested_height(&node_b).await, 0, "B starts at genesis");
        assert_ne!(
            root_a_before, root_b_before,
            "the two nodes must START divergent on exactly the source cell — that is the \
             independent variable under test"
        );

        // THE SKIP FIRES ON B, and only on B. Probed against B's REAL authoritative
        // pre-state (a clone, so nothing is written), because the durable refusal
        // record's reason code is the coarse `executor-rejected` and would pass this
        // test for an unrelated refusal.
        {
            let mut probe = ledger_b_before.clone();
            provision_transfer_destinations(&mut probe, &signed.turn.call_forest);
            assert!(
                probe.get(&dest).is_none(),
                "B lacks the source, so provisioning must SKIP — this test is vacuous otherwise"
            );
        }

        // ⚑ THE DIAGNOSIS, COMPUTED UP FRONT. `execute_finalized_turn` collapses
        // EVERY executor refusal to the one durable code `executor-rejected` and
        // leaves the actual reason in a `warn!` a lib-test binary never shows, so
        // a red here would otherwise arrive naming no cause at all. Run the same
        // turn against a CLONE of each node's authoritative pre-state, through the
        // node's OWN configured executor (a bare one carries `federation_id =
        // [0; 32]` and would report a signature failure that production does not
        // have), and carry the verdicts into the assertion messages below.
        let verdict_a = {
            let s = node_a.read().await;
            let executor = crate::executor_setup::new_submit_executor(&s);
            let mut probe = s.ledger.clone();
            provision_transfer_destinations(&mut probe, &signed.turn.call_forest);
            format!(
                "{:?}",
                crate::executor_setup::execute_via_producer(
                    &executor,
                    &signed.turn,
                    &mut probe,
                    false
                )
            )
        };
        let verdict_b = {
            let s = node_b.read().await;
            let executor = crate::executor_setup::new_submit_executor(&s);
            let mut probe = s.ledger.clone();
            provision_transfer_destinations(&mut probe, &signed.turn.call_forest);
            format!(
                "{:?}",
                crate::executor_setup::execute_via_producer(
                    &executor,
                    &signed.turn,
                    &mut probe,
                    false
                )
            )
        };

        // ── THE SAME FINALIZED BLOCK, TO BOTH NODES ───────────────────────────
        let handle = test_handle_with_committee([0x5Fu8; 32], vec![[0x5Fu8; 32]]).await;
        let block_id = BlockId([0x51u8; 32]);
        let outcome_a =
            execute_finalized_turn(&node_a, &handle, block_id, &payload, None, None, 0).await;
        let outcome_b =
            execute_finalized_turn(&node_b, &handle, block_id, &payload, None, None, 0).await;

        // ── A: COMPLETENESS. Honest provisioning still works where the cell is. ──
        assert!(
            matches!(outcome_a, FinalizedExecutionOutcome::Committed { .. }),
            "the node HOLDING the source must commit the finalized transfer; got \
             {outcome_a:?}\n  executor verdict on A's pre-state: {verdict_a}"
        );
        // B refused for the RIGHT reason: its executor cannot find the source. The
        // durable code cannot say this, so it is pinned here.
        assert!(
            verdict_b.contains("CellNotFound"),
            "B must refuse because the Transfer SOURCE is absent (that is what makes the \
             provisioning skip outcome-neutral), got: {verdict_b}"
        );
        let root_a_after = {
            let s = node_a.read().await;
            let landed = s
                .ledger
                .get(&dest)
                .expect("A provisioned AND credited the destination");
            assert_eq!(
                landed.state.balance(),
                MOVED as i64,
                "the provisioned landing site holds exactly the moved amount"
            );
            assert_eq!(
                landed.asset(),
                dregg_cell::CellId::from_bytes(default_token),
                "the landing site is minted in the SOURCE's asset — a stub in any other asset \
                 is refused by the executor's same-asset guard as a cross-asset teleport"
            );
            assert_eq!(
                s.ledger
                    .get(&source)
                    .expect("source present")
                    .state
                    .balance(),
                SOURCE_FUNDING - MOVED as i64,
                "the source is debited exactly once"
            );
            canonical_ledger_root(&s.ledger)
        };
        assert_ne!(root_a_after, root_a_before, "A's attested root moved");
        assert_eq!(attested_height(&node_a).await, 1, "A advanced 0 -> 1");

        // ── B: THE WHOLE POINT. Refused, and NOTHING was written. ──────────────
        assert!(
            matches!(
                &outcome_b,
                FinalizedExecutionOutcome::DeterministicallyRejected { reason_code, .. }
                    if reason_code == "executor-rejected"
            ),
            "the node LACKING the source must REFUSE the finalized turn — not apply a \
             divergent one, and not silently skip it; got {outcome_b:?}"
        );
        let root_b_after = {
            let s = node_b.read().await;
            assert!(
                s.ledger.get(&dest).is_none(),
                "the SKIPPED provisioning must leave no landing site behind on B"
            );
            assert_eq!(
                ledger_content_image(&s.ledger),
                image_b_before,
                "a refused finalized turn must leave B's ledger byte-identical — every cell, \
                 not merely every balance"
            );
            // The refusal is DURABLE and names this exact block, so B's divergence
            // from A is a recorded fact rather than a quiet no-op.
            let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                &block_id.0,
            );
            let bytes = s
                .store
                .get_config(&key)
                .expect("read rejection record")
                .expect("B's refusal of a finalized block is durable");
            let record: crate::signed_turn_validation::FinalizedPayloadRejectionRecord =
                postcard::from_bytes(&bytes).expect("decode rejection record");
            assert_eq!(record.block_id, block_id.0);
            assert_eq!(record.turn_hash, Some(signed.turn.hash()));
            canonical_ledger_root(&s.ledger)
        };
        assert_eq!(
            root_b_after, root_b_before,
            "B's attested ledger root must be byte-identical before and after a refused \
             finalized turn"
        );
        assert_eq!(attested_height(&node_b).await, 0, "B did not advance");

        // ── THE DIVERGENCE, EXHIBITED ─────────────────────────────────────────
        // Same finalized bytes, different post-state — and it is the LOUD kind:
        // one node committed, the other recorded a refusal against the block. What
        // does NOT happen is two commits at different roots, which is what a
        // provisioning skip would have to cause to be a consensus fault of its own.
        assert_ne!(
            root_a_after, root_b_after,
            "the two nodes end divergent (that is the exhibit) — but by one commit and one \
             RECORDED REFUSAL, never by two disagreeing commits"
        );
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

    /// A Byzantine proposer may finalize arbitrary payload bytes, so the live
    /// application path must not rely on HTTP having derived the agent.  Give a
    /// fully hybrid-signed attacker envelope the victim's current nonce and a
    /// non-zero fee; finalization must refuse it before the executor prologue can
    /// debit value or consume that nonce, and must durably name the refusal.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn finalized_attacker_turn_cannot_charge_or_advance_victim() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        let victim_clerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0x44; 32]));
        let default_token = *blake3::hash(b"default").as_bytes();
        let victim_cell =
            dregg_cell::Cell::with_balance(victim_clerk.public_key().0, default_token, 900_000);
        let victim = victim_cell.id();
        let (before_balance, before_nonce, signed) = {
            let mut s = state.write().await;
            s.ledger.insert_cell(victim_cell).expect("insert victim");
            let attacker = crate::executor_setup::local_agent_cell(&s);
            if s.ledger.get(&attacker).is_none() {
                let attacker_pk = s.cclerk.public_key().0;
                s.ledger
                    .insert_cell(dregg_cell::Cell::with_balance(
                        attacker_pk,
                        default_token,
                        100_000,
                    ))
                    .expect("insert attacker cell");
            }
            let before = s.ledger.get(&victim).expect("victim present");
            let before_balance = before.state.balance();
            let before_nonce = before.state.nonce();
            let federation_id = crate::executor_setup::federation_id_for_executor(&s);
            let attacker_action =
                s.cclerk
                    .make_action(attacker, "attacker_noop", vec![], &federation_id);
            let mut forest = dregg_turn::CallForest::new();
            forest.add_root(attacker_action);
            let mut hostile = dregg_turn::Turn {
                agent: victim,
                nonce: before_nonce,
                fee: 0,
                memo: Some("byzantine proposer victim-fee attempt".to_string()),
                valid_until: Some(i64::MAX / 2),
                call_forest: forest,
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
            hostile.fee = crate::executor_setup::new_submit_executor(&s).estimate_cost(&hostile);
            assert!(hostile.fee > 0, "hostile turn exercises a real fee debit");
            // The attacker is the node operator here and therefore has an
            // independently enrolled, valid ML-DSA identity.  Both signature
            // halves are honest; only its authority over `victim` is false.
            let signed = s.cclerk.sign_turn(&hostile);
            (before_balance, before_nonce, signed)
        };

        let payload = postcard::to_stdvec(&signed).expect("encode hostile SignedTurn");
        let self_key = [0xB7; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let block_id = BlockId([0xD3; 32]);
        execute_finalized_turn(&state, &handle, block_id, &payload, None, None, 0).await;

        let s = state.read().await;
        let after = s.ledger.get(&victim).expect("victim remains present");
        assert_eq!(
            after.state.balance(),
            before_balance,
            "rejected finalized payload must not debit the victim fee"
        );
        assert_eq!(
            after.state.nonce(),
            before_nonce,
            "rejected finalized payload must not consume the victim nonce"
        );

        let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &block_id.0,
        );
        let bytes = s
            .store
            .get_config(&key)
            .expect("read rejection record")
            .expect("finalized rejection is durable");
        let record: crate::signed_turn_validation::FinalizedPayloadRejectionRecord =
            postcard::from_bytes(&bytes).expect("decode rejection record");
        assert_eq!(record.block_id, block_id.0);
        assert_eq!(record.payload_hash, *blake3::hash(&payload).as_bytes());
        assert_eq!(record.turn_hash, Some(signed.turn.hash()));
        assert_eq!(record.reason_code, "agent-signer-mismatch");
    }

    /// Finalization enforces the full enrolled outer PQ identity, not merely
    /// the block's committee signature.  Each hostile envelope remains a
    /// finalized consensus artifact with its own deterministic refusal record,
    /// while the operator cell is untouched.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn finalized_turn_rejects_stripped_invalid_and_substituted_outer_pq() {
        assert!(
            std::env::var("DREGG_REQUIRE_PQ")
                .map(|v| v != "0" && !v.eq_ignore_ascii_case("false"))
                .unwrap_or(true),
            "hostile native-PQ gate must run with required PQ enabled"
        );
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let (operator, before_balance, before_nonce, honest) = {
            let mut s = state.write().await;
            let operator_pk = s.cclerk.public_key().0;
            let operator = crate::executor_setup::local_agent_cell(&s);
            let token = *blake3::hash(b"default").as_bytes();
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(operator_pk, token, 800_000))
                .expect("insert operator cell");
            let before = s.ledger.get(&operator).expect("operator present");
            let before_balance = before.state.balance();
            let before_nonce = before.state.nonce();
            let turn = dregg_turn::Turn {
                agent: operator,
                nonce: before_nonce,
                fee: 60_000,
                memo: None,
                valid_until: Some(i64::MAX / 2),
                call_forest: dregg_turn::CallForest::new(),
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
            (
                operator,
                before_balance,
                before_nonce,
                s.cclerk.sign_turn(&turn),
            )
        };

        let mut stripped = honest.clone();
        stripped.pq_signature.clear();
        stripped.pq_signer.clear();

        let mut invalid = honest.clone();
        invalid.pq_signature[0] ^= 0x20;

        let attacker = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[0xE1; 32]);
        let mut substituted = honest.clone();
        substituted.pq_signer = attacker.public_bytes();
        substituted.pq_signature = attacker
            .sign(&honest.turn.hash())
            .expect("attacker signature");

        let cases = [
            (stripped, BlockId([0xC1; 32]), "pq-signature-required"),
            (invalid, BlockId([0xC2; 32]), "invalid-pq-signature"),
            (
                substituted,
                BlockId([0xC3; 32]),
                "substituted-pq-public-key",
            ),
        ];
        let self_key = [0xB8; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        for (hostile, block_id, expected_code) in cases {
            let payload = postcard::to_stdvec(&hostile).expect("encode hostile SignedTurn");
            execute_finalized_turn(&state, &handle, block_id, &payload, None, None, 0).await;
            let s = state.read().await;
            let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                &block_id.0,
            );
            let bytes = s
                .store
                .get_config(&key)
                .expect("read rejection record")
                .expect("rejection record exists");
            let record: crate::signed_turn_validation::FinalizedPayloadRejectionRecord =
                postcard::from_bytes(&bytes).expect("decode rejection record");
            assert_eq!(record.reason_code, expected_code);
            let live = s.ledger.get(&operator).expect("operator remains present");
            assert_eq!(live.state.balance(), before_balance);
            assert_eq!(live.state.nonce(), before_nonce);
        }

        let trailing_block = BlockId([0xC4; 32]);
        let mut trailing_payload =
            postcard::to_stdvec(&honest).expect("encode canonical SignedTurn");
        trailing_payload.extend_from_slice(&[0x00, 0x7F]);
        execute_finalized_turn(
            &state,
            &handle,
            trailing_block,
            &trailing_payload,
            None,
            None,
            0,
        )
        .await;
        let s = state.read().await;
        let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &trailing_block.0,
        );
        let bytes = s
            .store
            .get_config(&key)
            .expect("read trailing-byte rejection")
            .expect("trailing-byte rejection is durable");
        let record: crate::signed_turn_validation::FinalizedPayloadRejectionRecord =
            postcard::from_bytes(&bytes).expect("decode rejection record");
        assert_eq!(record.reason_code, "trailing-signed-turn-bytes");
        let live = s.ledger.get(&operator).expect("operator remains present");
        assert_eq!(live.state.balance(), before_balance);
        assert_eq!(live.state.nonce(), before_nonce);
    }

    /// Finalization keeps one immutable observation log but independent causal
    /// heads per foreign agent.  A/B/A interleaving must not cross-link the
    /// chains, and an A turn that omits A's now-required predecessor must be
    /// refused before nonce/state mutation with a durable reason.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn finalized_foreign_receipts_are_agent_scoped_and_omitted_link_is_refused() {
        assert!(
            std::env::var("DREGG_REQUIRE_PQ")
                .map(|v| v != "0" && !v.eq_ignore_ascii_case("false"))
                .unwrap_or(true),
            "foreign-chain gate must run with native PQ required"
        );
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let seed_a = [0x31; 32];
        let seed_b = [0x52; 32];
        let clerk_a = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed_a));
        let clerk_b = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed_b));
        let agent_a = clerk_a.cell_id("default");
        let agent_b = clerk_b.cell_id("default");
        let pq_a: [u8; dregg_pq::ML_DSA_PK_LEN] =
            dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed_a)
                .public_bytes()
                .try_into()
                .expect("fixed-size ML-DSA public key");
        let pq_b: [u8; dregg_pq::ML_DSA_PK_LEN] =
            dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed_b)
                .public_bytes()
                .try_into()
                .expect("fixed-size ML-DSA public key");
        {
            let mut s = state.write().await;
            let local_pk = s.cclerk.public_key();
            let local_seed = s.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("fixed-size local ML-DSA public key");
            let token = *blake3::hash(b"default").as_bytes();
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    clerk_a.public_key().0,
                    token,
                    700_000,
                ))
                .expect("insert foreign A");
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    clerk_b.public_key().0,
                    token,
                    700_000,
                ))
                .expect("insert foreign B");
            s.set_federation_keys_hybrid(
                // The foreign agents are enrolled application authors; the
                // node itself is the enrolled validator that authenticates the
                // faithful-root edge and live attestation.
                vec![local_pk, clerk_a.public_key(), clerk_b.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(pq_a),
                    dregg_federation::frost::MlDsaPublicKey(pq_b),
                ],
            );
        }

        fn signed_noop(
            clerk: &dregg_sdk::AgentCipherclerk,
            agent: dregg_cell::CellId,
            nonce: u64,
            previous_receipt_hash: Option<[u8; 32]>,
            federation_id: &[u8; 32],
        ) -> dregg_sdk::SignedTurn {
            let unsigned = dregg_turn::Action {
                target: agent,
                method: *blake3::hash(b"foreign-chain-noop").as_bytes(),
                args: vec![],
                authorization: dregg_turn::Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![],
                may_delegate: dregg_turn::DelegationMode::None,
                commitment_mode: dregg_turn::CommitmentMode::Full,
                balance_change: None,
                witness_blobs: vec![],
            };
            let action = clerk.sign_action_hybrid(unsigned, federation_id, nonce);
            let mut call_forest = dregg_turn::CallForest::new();
            call_forest.add_root(action);
            let mut turn = dregg_turn::Turn {
                agent,
                nonce,
                fee: 0,
                memo: None,
                valid_until: Some(i64::MAX / 2),
                call_forest,
                depends_on: vec![],
                previous_receipt_hash,
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
            let estimator = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default());
            turn.fee = estimator.estimate_cost(&turn);
            clerk.sign_turn(&turn)
        }

        let self_key = [0xB9; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let signed_a1 = signed_noop(&clerk_a, agent_a, 0, None, &federation_id);
        let payload_a1 = postcard::to_stdvec(&signed_a1).expect("encode A1");
        execute_finalized_turn(
            &state,
            &handle,
            BlockId([0xA1; 32]),
            &payload_a1,
            None,
            None,
            0,
        )
        .await;
        let head_a1 = state
            .read()
            .await
            .cclerk
            .agent_receipt_head_hash(&agent_a)
            .expect("A1 appended");

        let signed_b1 = signed_noop(&clerk_b, agent_b, 0, None, &federation_id);
        let payload_b1 = postcard::to_stdvec(&signed_b1).expect("encode B1");
        execute_finalized_turn(
            &state,
            &handle,
            BlockId([0xB1; 32]),
            &payload_b1,
            None,
            None,
            1,
        )
        .await;

        let signed_a2 = signed_noop(&clerk_a, agent_a, 1, Some(head_a1), &federation_id);
        let payload_a2 = postcard::to_stdvec(&signed_a2).expect("encode A2");
        execute_finalized_turn(
            &state,
            &handle,
            BlockId([0xA2; 32]),
            &payload_a2,
            None,
            None,
            2,
        )
        .await;

        let before_omitted = state
            .read()
            .await
            .ledger
            .get(&agent_a)
            .expect("A live")
            .state
            .nonce();
        assert_eq!(before_omitted, 2);
        let omitted = signed_noop(&clerk_a, agent_a, before_omitted, None, &federation_id);
        let omitted_payload = postcard::to_stdvec(&omitted).expect("encode omitted-link A3");
        let omitted_block = BlockId([0xA3; 32]);
        execute_finalized_turn(
            &state,
            &handle,
            omitted_block,
            &omitted_payload,
            None,
            None,
            3,
        )
        .await;

        let s = state.read().await;
        assert_eq!(s.cclerk.receipt_log_length(), 3);
        assert_eq!(s.cclerk.agent_receipt_count(&agent_a), 2);
        assert_eq!(s.cclerk.agent_receipt_count(&agent_b), 1);
        let observed_agents: Vec<_> = s.cclerk.receipt_log().iter().map(|r| r.agent).collect();
        assert_eq!(observed_agents, vec![agent_a, agent_b, agent_a]);
        let a_receipts: Vec<_> = s.cclerk.agent_receipts(&agent_a).collect();
        assert_eq!(a_receipts[0].previous_receipt_hash, None);
        assert_eq!(a_receipts[1].previous_receipt_hash, Some(head_a1));
        assert_eq!(
            s.ledger.get(&agent_a).expect("A live").state.nonce(),
            before_omitted,
            "omitted predecessor must be rejected before nonce mutation"
        );
        let key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &omitted_block.0,
        );
        let bytes = s
            .store
            .get_config(&key)
            .expect("read rejection record")
            .expect("omitted-link rejection recorded");
        let record: crate::signed_turn_validation::FinalizedPayloadRejectionRecord =
            postcard::from_bytes(&bytes).expect("decode rejection record");
        assert_eq!(record.reason_code, "receipt-chain-mismatch");
    }

    /// THE MAKE-OR-BREAK: a finalized Transfer turn executes through the REAL
    /// `execute_finalized_turn` (the live commit path, now off-lock) and advances
    /// the attested height 0 -> 1 — the local confirmation that A1 unblocks
    /// finalization (the execution completes + promotes, no wedge), and the ledger
    /// reflects the committed transfer. Forces the deterministic Rust producer path
    /// so the test does not depend on a Lean-linked archive; the A1 change (WHERE
    /// the FFI runs + HOW its result is installed) is identical either way.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn a1_finalized_turn_advances_height_zero_to_one_off_lock() {
        let _ = tracing_subscriber::fmt()
            .with_env_filter("dregg_node=debug")
            .with_test_writer()
            .try_init();
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        // Deterministic Rust producer (no Lean-archive dependence).
        {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
        }

        // Fund a sender cell; the destination is fresh (materialized by the path).
        let sender_seed = *blake3::hash(b"a1-finalize:sender").as_bytes();
        let sender_cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(sender_seed));
        let sender_pk = sender_cclerk.public_key().0;
        let default_token = *blake3::hash(b"default").as_bytes();
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &default_token);
        let dest = dregg_cell::CellId([0x3Cu8; 32]);
        {
            let mut s = state.write().await;
            let local_pk = s.cclerk.public_key();
            let local_seed = s.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("fixed-size local ML-DSA public key");
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    sender_pk,
                    default_token,
                    1_000_000,
                ))
                .expect("fund sender");
            let pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&sender_seed)
                    .public_bytes()
                    .try_into()
                    .expect("fixed-size ML-DSA public key");
            s.set_federation_keys_hybrid(
                // Sender is an enrolled application author; this node is the
                // enrolled validator that signs the faithful-root attestation.
                vec![local_pk, sender_cclerk.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(pq),
                ],
            );
        }

        // The per-action signature binds the same hybrid federation id the
        // configured finalized executor will use.
        let federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };

        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);
        let turn_data = postcard::to_stdvec(&signed).expect("encode signed turn");

        // A minimal real handle; `execute_finalized_turn` reads only `handle.lace`
        // for the OPTIONAL finality round (an empty lace yields round None — fine).
        let self_key = [0x9Au8; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let block_id = BlockId([0x11u8; 32]);
        let mut publication_events = state.subscribe_events();

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
        execute_finalized_turn(&state, &handle, block_id, &turn_data, None, None, 0).await;

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
        let stored_root = s
            .store
            .latest_attested_root()
            .expect("read attested root")
            .expect("faithful attested root persisted");
        let faithful = s
            .store
            .faithful_note_root_expectation()
            .expect("read faithful history seal")
            .expect("faithful history installed");
        assert_eq!(faithful.records, 1);
        assert_eq!(faithful.height, 1);
        assert_eq!(faithful.note_count, 0);
        assert_eq!(stored_root.note_tree_root, Some(faithful.root.to_bytes()));
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
        assert_eq!(s.store.commit_cursor().expect("commit cursor"), 1);
        assert_eq!(s.cclerk.receipt_chain_length(), 1);
        assert_eq!(s.event_log.len(), 1, "activity publishes exactly once");
        drop(s);

        let mut roots = 0;
        let mut receipts = 0;
        while let Ok(event) = publication_events.try_recv() {
            match event {
                NodeEvent::Root { .. } => roots += 1,
                NodeEvent::Receipt { .. } => receipts += 1,
                _ => {}
            }
        }
        assert_eq!(roots, 1, "fresh durable commit emits one root event");
        assert_eq!(receipts, 1, "fresh durable commit emits one receipt event");
    }

    /// The deployment ceremony is an explicit prerequisite. A malformed
    /// reserved marker is terminal even without a head, while an exact Signal
    /// with no authenticated head stays retryable and receives no finalization
    /// ACK. Neither path is allowed to leak the executor candidate into live or
    /// durable state. The malformed payload-rejection record is the sole
    /// durable diagnostic change and is not a finalized commit.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn poa_signal_missing_ceremony_and_malformed_marker_never_mutate_game_or_executor() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let (state, actor_cclerk, actor, federation_id) =
            poa_finality_test_state(tmp.path(), false).await;
        let handle = test_handle_with_committee([0x81; 32], vec![[0x81; 32]]).await;

        let before = {
            let s = state.read().await;
            (
                canonical_ledger_root(&s.ledger),
                s.store
                    .load_executor_accumulator_snapshot()
                    .expect("executor snapshot"),
                s.store.commit_cursor().expect("commit cursor"),
                s.store.receipt_chain_len().expect("receipt chain len"),
                s.cclerk.receipt_chain_length(),
                s.event_log.len(),
            )
        };

        let malformed_event = dregg_turn::action::Event::new(
            dregg_turn::action::symbol(dregg_sdk::poa_signal::SIGNAL_CLAIM_TOPIC_V1),
            vec![dregg_cell::field_from_u64(1)],
        );
        let malformed =
            signed_signal_event_turn(&actor_cclerk, actor, malformed_event, 0, &federation_id);
        let malformed_payload = postcard::to_stdvec(&malformed).expect("encode malformed turn");
        let malformed_block = BlockId([0x82; 32]);
        let malformed_outcome = execute_finalized_turn(
            &state,
            &handle,
            malformed_block,
            &malformed_payload,
            None,
            None,
            0,
        )
        .await;
        assert!(matches!(
            malformed_outcome,
            FinalizedExecutionOutcome::DeterministicallyRejected { ref reason_code, .. }
                if reason_code == "poa-signal-reserved-marker-malformed"
        ));

        let mixed_claim = dregg_sdk::poa_signal::SignalClaimV1::new(
            1,
            &[dregg_sdk::poa_signal::SignalCode::new(5, 0, 5).expect("bounded Signal code")],
        )
        .expect("bounded mission");
        let mixed = signed_signal_effects_turn(
            &actor_cclerk,
            actor,
            vec![
                dregg_turn::Effect::EmitEvent {
                    cell: actor,
                    event: dregg_sdk::poa_signal::signal_claim_event(mixed_claim),
                },
                dregg_turn::Effect::IncrementNonce { cell: actor },
            ],
            0,
            &federation_id,
        );
        let mixed_payload = postcard::to_stdvec(&mixed).expect("encode mixed carrier");
        let mixed_block = BlockId([0x88; 32]);
        let mixed_outcome =
            execute_finalized_turn(&state, &handle, mixed_block, &mixed_payload, None, None, 0)
                .await;
        assert!(matches!(
            mixed_outcome,
            FinalizedExecutionOutcome::DeterministicallyRejected { ref reason_code, .. }
                if reason_code == "poa-signal-noncanonical-carrier"
        ));

        let exact = signed_signal_turn(&actor_cclerk, actor, 1, 0, &federation_id);
        let exact_payload = postcard::to_stdvec(&exact).expect("encode exact Signal turn");
        let retry_block = BlockId([0x83; 32]);
        let retry_outcome =
            execute_finalized_turn(&state, &handle, retry_block, &exact_payload, None, None, 0)
                .await;
        assert!(matches!(
            retry_outcome,
            FinalizedExecutionOutcome::RetryableOperational { ref error, .. }
                if error.contains("head is not initialized")
        ));

        let s = state.read().await;
        assert_eq!(canonical_ledger_root(&s.ledger), before.0);
        assert_eq!(
            s.store
                .load_executor_accumulator_snapshot()
                .expect("executor snapshot after refusals"),
            before.1
        );
        assert_eq!(s.store.commit_cursor().expect("commit cursor"), before.2);
        assert_eq!(
            s.store.receipt_chain_len().expect("receipt chain len"),
            before.3
        );
        assert_eq!(s.cclerk.receipt_chain_length(), before.4);
        assert_eq!(s.event_log.len(), before.5);
        assert!(
            s.store
                .load_poa_signal_head(federation_id)
                .expect("PoA head lookup")
                .is_none()
        );
        assert!(
            s.store
                .load_poa_signal_transition(federation_id, 1)
                .expect("PoA transition lookup")
                .is_none()
        );
        let malformed_key =
            crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                &malformed_block.0,
            );
        assert!(
            s.store
                .get_config(&malformed_key)
                .expect("malformed rejection read")
                .is_some(),
            "the diagnostic rejection index may advance without mutating execution state"
        );
        let mixed_key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &mixed_block.0,
        );
        assert!(
            s.store
                .get_config(&mixed_key)
                .expect("mixed-carrier rejection read")
                .is_some(),
            "mixed carrier must terminate before either executor state can commit"
        );
        let retry_key = crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
            &retry_block.0,
        );
        assert!(
            s.store
                .get_config(&retry_key)
                .expect("retryable rejection read")
                .is_none(),
            "retryable missing-deployment state must not manufacture a terminal ACK record"
        );
    }

    /// A semantic refusal happens only after ordinary execution has produced a
    /// candidate receipt/root for Lean. The candidate remains isolated: fee,
    /// nonce, receipt, executor accumulators, and PoA head are unchanged. Only
    /// the finalized-payload rejection index records the terminal disposition.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn poa_signal_semantic_rejection_discards_the_entire_executor_candidate() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let (state, actor_cclerk, actor, federation_id) =
            poa_finality_test_state(tmp.path(), true).await;
        let handle = test_handle_with_committee([0x84; 32], vec![[0x84; 32]]).await;
        let before = {
            let s = state.read().await;
            (
                canonical_ledger_root(&s.ledger),
                s.store
                    .load_executor_accumulator_snapshot()
                    .expect("executor snapshot"),
                s.store
                    .load_poa_signal_head(federation_id)
                    .expect("PoA head")
                    .expect("initialized PoA head"),
                s.store.commit_cursor().expect("commit cursor"),
                s.store.receipt_chain_len().expect("receipt chain len"),
                s.cclerk.receipt_chain_length(),
                s.event_log.len(),
            )
        };

        // Mission 2 is a well-formed public claim, but the persisted deployment
        // activates mission 1. This is an adapter-level semantic refusal before
        // FFI; the armed accepted-path test below separately proves real Lean
        // execution and exact output binding.
        let signed = signed_signal_turn(&actor_cclerk, actor, 2, 0, &federation_id);
        let payload = postcard::to_stdvec(&signed).expect("encode rejected Signal turn");
        let block_id = BlockId([0x85; 32]);
        let outcome =
            execute_finalized_turn(&state, &handle, block_id, &payload, None, None, 0).await;
        assert!(matches!(
            outcome,
            FinalizedExecutionOutcome::DeterministicallyRejected { ref reason_code, .. }
                if reason_code == "poa-signal-semantic-rejected"
        ));

        let s = state.read().await;
        assert_eq!(canonical_ledger_root(&s.ledger), before.0);
        assert_eq!(
            s.store
                .load_executor_accumulator_snapshot()
                .expect("executor snapshot after refusal"),
            before.1
        );
        assert_eq!(
            s.store
                .load_poa_signal_head(federation_id)
                .expect("PoA head after refusal")
                .expect("PoA head remains initialized"),
            before.2
        );
        assert!(
            s.store
                .load_poa_signal_transition(federation_id, 1)
                .expect("PoA transition lookup")
                .is_none()
        );
        assert_eq!(s.store.commit_cursor().expect("commit cursor"), before.3);
        assert_eq!(
            s.store.receipt_chain_len().expect("receipt chain len"),
            before.4
        );
        assert_eq!(s.cclerk.receipt_chain_length(), before.5);
        assert_eq!(s.event_log.len(), before.6);
        assert_eq!(
            s.ledger
                .get(&actor)
                .expect("actor remains present")
                .state
                .nonce(),
            0
        );
        assert_eq!(
            s.ledger
                .get(&actor)
                .expect("actor remains present")
                .state
                .balance(),
            1_000_000
        );
        let rejection_key =
            crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                &block_id.0,
            );
        assert!(
            s.store
                .get_config(&rejection_key)
                .expect("semantic rejection read")
                .is_some(),
            "terminal semantic refusal is indexed without becoming a commit"
        );
    }

    /// The complete authoritative weld: ordinary execution produces the exact
    /// receipt pre-root, the outer signer becomes the player identity, Lean
    /// judges the persisted Canon/config, and the successor lands atomically
    /// with the carrying finalized turn. A cold reopen must reproduce every
    /// byte and chain coordinate.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn poa_signal_finality_weld_survives_restart_with_exact_signer_and_actor_root() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "the authoritative PoA Signal finalized-turn integration",
        ) {
            return;
        }
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let (state, actor_cclerk, actor, federation_id) =
            poa_finality_test_state(tmp.path(), true).await;
        let signed = signed_signal_turn(&actor_cclerk, actor, 1, 0, &federation_id);
        let payload = postcard::to_stdvec(&signed).expect("encode accepted Signal turn");
        let block_id = BlockId([0x86; 32]);
        let handle = test_handle_with_committee([0x87; 32], vec![[0x87; 32]]).await;
        let outcome =
            execute_finalized_turn(&state, &handle, block_id, &payload, None, None, 0).await;
        assert!(matches!(
            outcome,
            FinalizedExecutionOutcome::Committed {
                durable_ordinal: 0,
                ..
            }
        ));

        let (committed_head, committed_transition, committed_root, committed_executor) = {
            let s = state.read().await;
            let head = s
                .store
                .load_poa_signal_head(federation_id)
                .expect("PoA head")
                .expect("advanced PoA head");
            assert_eq!(head.transition_count(), 1);
            assert_eq!(head.world_sequence(), 1);
            assert_eq!(head.canon_revision(), 1);
            let transition = s
                .store
                .load_poa_signal_transition(federation_id, 1)
                .expect("PoA transition")
                .expect("first PoA transition");
            assert_eq!(transition.sequence(), 1);
            assert_eq!(transition.commit_ordinal(), 0);
            assert_eq!(transition.turn_hash(), signed.turn.hash());
            let receipt = s.cclerk.receipt_log().last().expect("committed receipt");
            assert_eq!(transition.receipt_hash(), receipt.receipt_hash());

            let judge_input: serde_json::Value =
                serde_json::from_slice(transition.judge_input()).expect("exact judge input JSON");
            let request = judge_input
                .get("request")
                .and_then(serde_json::Value::as_object)
                .expect("judge request object");
            let signer_hex = dregg_types::hex_encode(&signed.signer.0);
            let agent_hex = dregg_types::hex_encode(signed.turn.agent.as_bytes());
            let actor_root_hex = dregg_types::hex_encode(&receipt.pre_state_hash);
            assert_eq!(
                request
                    .get("player_key")
                    .and_then(serde_json::Value::as_str),
                Some(signer_hex.as_str()),
                "player identity comes from SignedTurn.signer"
            );
            assert_ne!(
                request
                    .get("player_key")
                    .and_then(serde_json::Value::as_str),
                Some(agent_hex.as_str()),
                "a CellId may never be substituted for the outer signer key"
            );
            assert_eq!(
                request
                    .get("actor_root")
                    .and_then(serde_json::Value::as_str),
                Some(actor_root_hex.as_str()),
                "actor root comes from the executor-produced committed receipt"
            );
            s.store.audit_poa_signal_state().expect("PoA state audit");
            assert_eq!(s.store.commit_cursor().expect("commit cursor"), 1);
            (
                head,
                transition,
                canonical_ledger_root(&s.ledger),
                s.store
                    .load_executor_accumulator_snapshot()
                    .expect("executor snapshot"),
            )
        };

        drop(state);
        let reopened = crate::state::NodeState::new(tmp.path(), Vec::new())
            .expect("cold reopen after PoA Signal commit");
        let s = reopened.read().await;
        assert_eq!(
            s.store
                .load_poa_signal_head(federation_id)
                .expect("reopened PoA head")
                .expect("reopened authority"),
            committed_head
        );
        assert_eq!(
            s.store
                .load_poa_signal_transition(federation_id, 1)
                .expect("reopened PoA transition")
                .expect("reopened first transition"),
            committed_transition
        );
        assert_eq!(canonical_ledger_root(&s.ledger), committed_root);
        assert_eq!(
            s.store
                .load_executor_accumulator_snapshot()
                .expect("reopened executor snapshot"),
            committed_executor
        );
        assert_eq!(s.store.commit_cursor().expect("reopened commit cursor"), 1);
        assert_eq!(s.store.receipt_chain_len().expect("receipt chain len"), 1);
        let durable_ids = s
            .store
            .commit_log_block_ids()
            .expect("reopened durable turn identities");
        assert_eq!(durable_ids, vec![block_id.0]);
        let restored_cursor = crate::execution_cursor::ExecutionCursor::restore(
            durable_ids.into_iter().map(BlockId).collect(),
        );
        assert!(
            restored_cursor.is_executed(&block_id),
            "restart filters the carrying block by durable identity before the advanced PoA head can be judged again"
        );
        s.store
            .audit_poa_signal_state()
            .expect("reopened PoA state audit");
    }

    /// F2 (self-equivocation window): a locally-authored block must land DURABLY
    /// before it is broadcast. Both directions through the REAL producer
    /// (`submit_heartbeat`), driven by the `persist_block` fault seam:
    ///
    ///  * a SIMULATED persist failure returns `None` (so `push_new_blocks` is
    ///    never reached — not broadcast), leaves the DURABLE block count
    ///    unchanged (the authored seq does not advance durably, so restart —
    ///    which rebuilds the self strand from persisted blocks — cannot re-author
    ///    it), and rolls the block back out of the live lace (tip unchanged);
    ///  * a SUCCESSFUL persist advances both the durable store and the live tip.
    #[tokio::test]
    async fn authored_block_persist_failure_is_fail_closed_no_broadcast_no_durable_advance() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let self_key = [0x5Au8; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let store = { state.read().await.store.clone() };
        let self_creator = handle.lace.read().await.self_creator();

        // Helper: (durable block count, live tip id, live tip seq).
        async fn snapshot(
            store: &dregg_persist::PersistentStore,
            handle: &BlocklaceHandle,
            self_creator: &[u8; 32],
        ) -> (u64, Option<BlockId>, Option<u64>) {
            let count = store.blocklace_block_count().expect("durable block count");
            let lace = handle.lace.read().await;
            let tip = lace.creator_tip(self_creator);
            let seq = tip.and_then(|id| lace.get(&id).map(|b| b.seq));
            (count, tip, seq)
        }

        // ── SUCCESS: heartbeat lands durably and advances the live tip. ──
        let id1 = handle
            .submit_heartbeat(&state)
            .await
            .expect("heartbeat with a working store lands durably");
        let (count1, tip1, seq1) = snapshot(&store, &handle, &self_creator).await;
        assert_eq!(count1, 1, "the authored heartbeat is durable");
        assert_eq!(tip1, Some(id1), "live tip is the authored block");
        assert_eq!(seq1, Some(1), "first authored block is seq 1");

        // ── FAILURE: arm the persist fault; the next heartbeat must fail closed. ──
        store.set_fail_persist_block(true);
        let outcome = handle.submit_heartbeat(&state).await;
        assert!(
            outcome.is_none(),
            "a persist failure returns None (never reaches push_new_blocks — not broadcast)"
        );
        let (count2, tip2, seq2) = snapshot(&store, &handle, &self_creator).await;
        assert_eq!(
            count2, 1,
            "durable authored-seq did NOT advance on persist failure (restart cannot re-author)"
        );
        assert_eq!(
            tip2,
            Some(id1),
            "the un-persisted block was rolled back — tip unchanged"
        );
        assert_eq!(
            seq2,
            Some(1),
            "self seq did NOT advance past the last durable block"
        );

        // ── RECOVERY: clear the fault; production resumes at the un-reused seq. ──
        store.set_fail_persist_block(false);
        let id3 = handle
            .submit_heartbeat(&state)
            .await
            .expect("heartbeat lands durably again once the store recovers");
        assert_ne!(
            id3, id1,
            "a fresh block, not a re-emit of the rolled-back one"
        );
        let (count3, tip3, seq3) = snapshot(&store, &handle, &self_creator).await;
        assert_eq!(count3, 2, "the recovered heartbeat is durable");
        assert_eq!(tip3, Some(id3));
        assert_eq!(
            seq3,
            Some(2),
            "seq advances 1 -> 2 (the failed attempt consumed no durable seq)"
        );
    }

    /// Write-ahead-before-live falsifier: drive a valid body-committed transfer
    /// all the way to the real durable barrier, inject a store error there, and
    /// prove that every live/publication surface remains at its pre-turn image.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn generic_finalized_store_error_discards_every_candidate_surface() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        {
            state.write().await.lean_producer_enabled = false;
        }

        let sender_seed = *blake3::hash(b"generic-atomicity:store-error").as_bytes();
        let sender_cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(sender_seed));
        let sender_pk = sender_cclerk.public_key().0;
        let default_token = *blake3::hash(b"default").as_bytes();
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &default_token);
        let dest = dregg_cell::CellId([0xE4; 32]);
        {
            let mut s = state.write().await;
            let local_pk = s.cclerk.public_key();
            let local_seed = s.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("local ML-DSA key");
            let sender_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&sender_seed)
                    .public_bytes()
                    .try_into()
                    .expect("sender ML-DSA key");
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    sender_pk,
                    default_token,
                    1_000_000,
                ))
                .expect("fund sender");
            s.set_federation_keys_hybrid(
                vec![local_pk, sender_cclerk.public_key()],
                vec![
                    dregg_federation::frost::MlDsaPublicKey(local_pq),
                    dregg_federation::frost::MlDsaPublicKey(sender_pq),
                ],
            );
        }
        let federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);
        let payload = postcard::to_stdvec(&signed).expect("encode signed turn");
        let bundle = TurnArtifactBundle {
            signed_turn: payload.clone(),
            receipt: Some(vec![0xFF]),
            witnessed_receipts: vec![vec![0xFE]],
        };

        let mut events = state.subscribe_events();
        let before = {
            let s = state.read().await;
            let pending_len = dregg_turn::PendingTurnRegistry::from_canonical_bytes(
                &s.store
                    .load_latest_reactive_registry_snapshot_bytes()
                    .expect("read durable pending registry"),
            )
            .expect("decode durable pending registry")
            .len();
            (
                canonical_ledger_root(&s.ledger),
                s.cclerk.receipt_chain_length(),
                pending_len,
                s.event_log.len(),
                s.witnessed_receipts.len(),
                s.store.commit_cursor().expect("commit cursor"),
                s.store.latest_attested_root().expect("root read"),
            )
        };

        let failed_block = BlockId([0xE6; 32]);
        *FAIL_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
            .lock()
            .expect("failure hook mutex") = Some(failed_block.0);
        let self_key = [0xE5; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        execute_finalized_turn(
            &state,
            &handle,
            failed_block,
            &payload,
            Some(&bundle),
            None,
            0,
        )
        .await;
        assert!(
            FAIL_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
                .lock()
                .expect("failure hook mutex")
                .is_none(),
            "fault hook must be consumed at the real durable barrier"
        );

        let s = state.read().await;
        assert_eq!(canonical_ledger_root(&s.ledger), before.0);
        assert_eq!(s.cclerk.receipt_chain_length(), before.1);
        assert_eq!(
            dregg_turn::PendingTurnRegistry::from_canonical_bytes(
                &s.store
                    .load_latest_reactive_registry_snapshot_bytes()
                    .expect("read durable pending registry"),
            )
            .expect("decode durable pending registry")
            .len(),
            before.2
        );
        assert_eq!(s.event_log.len(), before.3);
        assert_eq!(s.witnessed_receipts.len(), before.4);
        assert_eq!(s.store.commit_cursor().expect("commit cursor"), before.5);
        assert_eq!(s.store.latest_attested_root().expect("root read"), before.6);
        assert!(
            s.ledger.get(&dest).is_none(),
            "provisioned candidate leaked"
        );
        assert_eq!(
            s.ledger.get(&sender).expect("sender").state.balance(),
            1_000_000,
            "fee/body candidate leaked"
        );
        assert!(matches!(
            events.try_recv(),
            Err(tokio::sync::broadcast::error::TryRecvError::Empty)
        ));
        drop(s);

        // A successful-but-idempotent store response is also non-publishing:
        // only `freshly_committed` may cross the live boundary.
        let replay_block = BlockId([0xE7; 32]);
        *REPLAY_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
            .lock()
            .expect("replay hook mutex") = Some(replay_block.0);
        execute_finalized_turn(
            &state,
            &handle,
            replay_block,
            &payload,
            Some(&bundle),
            None,
            0,
        )
        .await;
        assert!(
            REPLAY_GENERIC_FINALIZED_COMMIT_FOR_BLOCK
                .lock()
                .expect("replay hook mutex")
                .is_none(),
            "replay hook must be consumed at the real durable barrier"
        );
        {
            let s = state.read().await;
            assert_eq!(canonical_ledger_root(&s.ledger), before.0);
            assert_eq!(s.cclerk.receipt_chain_length(), before.1);
            assert_eq!(
                dregg_turn::PendingTurnRegistry::from_canonical_bytes(
                    &s.store
                        .load_latest_reactive_registry_snapshot_bytes()
                        .expect("read durable pending registry"),
                )
                .expect("decode durable pending registry")
                .len(),
                before.2
            );
            assert_eq!(s.event_log.len(), before.3);
            assert_eq!(s.witnessed_receipts.len(), before.4);
            assert_eq!(s.store.commit_cursor().expect("commit cursor"), before.5);
            assert!(s.ledger.get(&dest).is_none());
        }
        assert!(matches!(
            events.try_recv(),
            Err(tokio::sync::broadcast::error::TryRecvError::Empty)
        ));

        // A semantically valid envelope whose body fails after the executor's
        // phase-1 fee/nonce charge must discard that charged candidate too. No
        // typed durable phase1-only attempt record exists yet, so publishing the
        // charge would violate durableApply_reject_stays.
        let rejected_dest = dregg_cell::CellId([0xE8; 32]);
        let rejected = signed_transfer_turn(
            &sender_cclerk,
            sender,
            rejected_dest,
            2_000_000,
            0,
            &federation_id,
        );
        let rejected_payload = postcard::to_stdvec(&rejected).expect("encode rejected turn");
        execute_finalized_turn(
            &state,
            &handle,
            BlockId([0xE9; 32]),
            &rejected_payload,
            None,
            None,
            0,
        )
        .await;
        let s = state.read().await;
        assert_eq!(canonical_ledger_root(&s.ledger), before.0);
        assert_eq!(s.cclerk.receipt_chain_length(), before.1);
        assert_eq!(
            dregg_turn::PendingTurnRegistry::from_canonical_bytes(
                &s.store
                    .load_latest_reactive_registry_snapshot_bytes()
                    .expect("read durable pending registry"),
            )
            .expect("decode durable pending registry")
            .len(),
            before.2
        );
        assert_eq!(s.event_log.len(), before.3);
        assert_eq!(s.witnessed_receipts.len(), before.4);
        assert_eq!(s.store.commit_cursor().expect("commit cursor"), before.5);
        assert!(s.ledger.get(&rejected_dest).is_none());
        assert_eq!(
            s.ledger.get(&sender).expect("sender").state.balance(),
            1_000_000,
            "rejected phase1 fee candidate leaked"
        );
        assert_eq!(
            s.ledger.get(&sender).expect("sender").state.nonce(),
            0,
            "rejected phase1 nonce candidate leaked"
        );
        assert!(matches!(
            events.try_recv(),
            Err(tokio::sync::broadcast::error::TryRecvError::Empty)
        ));
    }

    /// FALSIFIER for the old solo receipt/ledger split: a crash could leave the
    /// ingress receipt durable while the authoritative ledger mutation existed
    /// only in RAM and was lost.  Receipt presence must therefore NEVER make
    /// finalization skip execution.
    ///
    /// This drives the crash image exactly: build and durably append the admission
    /// receipt against a scratch ledger, leave the node ledger untouched, then
    /// finalize.  The finalized path must re-execute once, byte-verify/reuse the
    /// old receipt without appending, and atomically advance every ordinary commit
    /// coordinate.  A receipt-as-applied shortcut leaves the balances unchanged
    /// and reds this test.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn solo_finalization_recovers_receipt_durable_ledger_absent_crash() {
        // The finalized executor reports WHY it refused only through `warn!`
        // ("finalized turn rejected; …  reason = …"); the returned outcome keeps
        // the coarse durable code. A lib-test binary installs no subscriber, so
        // that reason was unreachable without re-running the whole node. nextest
        // captures this and prints it only on failure.
        let _ = tracing_subscriber::fmt::try_init();
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        // Solo (n=1) mode + deterministic Rust producer (no Lean-archive dependence).
        {
            let mut s = state.write().await;
            s.lean_producer_enabled = false;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
            s.federation_configured = true;
            s.federation_id = [0u8; 32];
        }

        let sender_seed = *blake3::hash(b"solo-idem:sender").as_bytes();
        let sender_cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(sender_seed));
        let sender_pk = sender_cclerk.public_key().0;
        let default_token = *blake3::hash(b"default").as_bytes();
        let sender = dregg_cell::CellId::derive_raw(&sender_pk, &default_token);
        // A PRE-EXISTING destination (so ingress needs no destination provisioning).
        let dest_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"solo-idem:dest").as_bytes(),
        ));
        let dest_pk = dest_cclerk.public_key().0;
        let dest = dregg_cell::CellId::derive_raw(&dest_pk, &default_token);
        {
            let mut s = state.write().await;
            // ⚑ A USER'S PQ IDENTITY LIVES IN ITS OWN CELL. The hybrid admission predicate anchors
            // the ML-DSA key an envelope carries in the ACTING CELL's own identity commitment
            // (`with_hybrid_balance`), which is the only place a spender's PQ half is authoritative.
            // While this fixture had the sender enrolled as the sole VALIDATOR, the roster stood in
            // for that commitment; with the committee corrected to the node, a bare
            // `with_balance` sender is refused "required post-quantum target-cell identity is not
            // committed in the live cell" — correctly, and at ingress rather than at finalization.
            s.ledger
                .insert_cell(
                    dregg_cell::Cell::with_hybrid_balance(
                        sender_pk,
                        &sender_cclerk.ml_dsa_public_bytes(),
                        default_token,
                        1_000_000,
                    )
                    .expect("canonical ML-DSA-65 sender identity"),
                )
                .expect("fund sender");
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(dest_pk, default_token, 0))
                .expect("seed destination");
            // ⚑ THE COMMITTEE IS THIS NODE, NOT THE SENDER. This fixture used to install the
            // SENDER's keypair as the sole validator — a committee the node itself is not a member
            // of. The node then signs its own faithful note-root envelope and attested root with
            // `cclerk.gossip_signing_key()`, and `execute_finalized_turn` only stamps that
            // signature when `federation_keys.contains(&local_pk)`; with a foreign committee the
            // root went out with EMPTY `quorum_signatures` and `PersistentStore` correctly refused
            // the durable commit — `Integrity("faithful note-root attestation has no valid author
            // signature")` — so nothing was ever written and `latest_height` stayed 0. That is the
            // class `node/src/init.rs`'s header already names: "the key and the committee have to
            // be minted together or they do not match". A SOLO node's committee IS its own key;
            // the sender is a USER, and a user has never needed to be a validator to spend.
            let self_pk = s.cclerk.public_key();
            let (self_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(
                &s.cclerk.gossip_signing_key().to_bytes(),
            );
            s.set_federation_keys_hybrid(vec![self_pk], vec![self_ml_dsa]);
        }

        // The federation id the EXECUTOR verifies action signatures against, read after the
        // committee is installed. `set_federation_keys_hybrid` RE-DERIVES `federation_id` from the
        // hybrid committee, so the `[0u8; 32]` this fixture used to sign its actions with stopped
        // being the executor's id the moment the keys were loaded — and the action's Ed25519 half
        // (whose message binds the federation id) then failed to verify, which is precisely the
        // `hybrid: Ed25519 (classical) signature half failed` this test was reporting.
        let federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };

        let signed = signed_transfer_turn(&sender_cclerk, sender, dest, 4_200, 0, &federation_id);
        let fee = signed.turn.fee as i64;
        let turn_data = postcard::to_stdvec(&signed).expect("encode signed turn");

        // ── SIMULATE THE CRASH IMAGE: receipt durable, ledger absent. ──
        {
            let mut s = state.write().await;
            let executor = crate::executor_setup::new_submit_executor(&s);
            let mut scratch = s.ledger.clone();
            match crate::executor_setup::execute_via_producer(
                &executor,
                &signed.turn,
                &mut scratch,
                false,
            ) {
                dregg_turn::TurnResult::Committed { receipt, .. } => {
                    s.cclerk.append_receipt(receipt).expect("ingress append");
                }
                other => panic!("solo ingress must commit the transfer, got {other:?}"),
            }
        }

        // The durable receipt survived, but the authoritative ledger did not.
        {
            let s = state.read().await;
            assert_eq!(
                s.ledger.get(&sender).expect("sender").state.balance(),
                1_000_000,
                "crash-restored ledger is still pre-turn"
            );
            assert_eq!(
                s.ledger.get(&dest).expect("dest").state.balance(),
                0,
                "receipt presence alone must not imply ledger application"
            );
            assert_eq!(
                s.cclerk.receipt_chain_length(),
                1,
                "ingress appended exactly one receipt"
            );
        }
        // ...but the ATTESTED ROOT (which drives `latest_height`) is NOT written by
        // ingress — only finalization writes it.
        let height_before = {
            let s = state.read().await;
            s.store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0)
        };
        assert_eq!(
            height_before, 0,
            "solo ingress alone does NOT advance the attested height (the finalization pass must)"
        );

        // ── FINALIZATION of the ALREADY-APPLIED turn. Before the fix this re-executed
        // → NonceReplay → Rejected → attested root never written (height stuck at 0).
        let self_key = [0x9Au8; 32];
        let handle = test_handle_with_committee(self_key, vec![self_key]).await;
        let block_id = BlockId([0x22u8; 32]);
        let outcome =
            execute_finalized_turn(&state, &handle, block_id, &turn_data, None, None, 0).await;
        // ⚑ ASSERT THE OUTCOME, NOT ONLY ITS SHADOW. This return value — the one thing that
        // NAMES why a finalized turn did not commit (`DeterministicallyRejected { reason_code }`,
        // `FatalIntegrity { error }`) — was discarded, so every failure of this test arrived as a
        // bare `attested height 0 != 1` and the reason was reachable only by re-running the node
        // under a tracing subscriber. Demanding `Committed` here makes the diagnosis the failure
        // message.
        assert!(
            matches!(outcome, FinalizedExecutionOutcome::Committed { .. }),
            "the crash-image finalization must COMMIT the already-receipted turn; got {outcome:?}"
        );

        // (a) THE FIX: the turn genuinely finalizes — attested height advances 0 -> 1.
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
            "an already-applied solo turn MUST still finalize (attested height 0 -> 1), \
             not be rejected as a nonce replay"
        );

        // (b) EXACTLY ONCE: finalization applied the missing ledger transition,
        // while reusing (not re-appending) the durable receipt.
        {
            let s = state.read().await;
            assert_eq!(
                s.ledger.get(&sender).expect("sender").state.balance(),
                1_000_000 - 4_200 - fee,
                "sender is debited EXACTLY once by finalization"
            );
            assert_eq!(
                s.ledger.get(&dest).expect("dest").state.balance(),
                4_200,
                "destination is credited exactly once by finalization"
            );
            assert_eq!(
                s.cclerk.receipt_chain_length(),
                1,
                "the receipt is NOT re-appended by finalization"
            );
            // Sanity: the persisted attested root's merkle_root matches the live ledger.
            let stored = s
                .store
                .latest_attested_root()
                .ok()
                .flatten()
                .expect("attested root persisted");
            assert_eq!(
                stored.merkle_root,
                canonical_ledger_root(&s.ledger),
                "the attested root commits the already-applied ledger state"
            );
        }

        // (c) MONOTONIC: `latest_height` TRACKS turns — a second solo turn advances
        // it 1 -> 2 (not stuck, not a hardcoded 1). This is the `/status` symptom.
        // A FRESH sender (its own first turn) so the manual harness needs no
        // per-cell authority-rotation bookkeeping — orthogonal to the height logic.
        let sender2_seed = *blake3::hash(b"solo-idem:sender2").as_bytes();
        let sender2_cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(sender2_seed));
        let sender2_pk = sender2_cclerk.public_key().0;
        let sender2 = dregg_cell::CellId::derive_raw(&sender2_pk, &default_token);
        {
            let mut s = state.write().await;
            s.ledger
                .insert_cell(
                    dregg_cell::Cell::with_hybrid_balance(
                        sender2_pk,
                        &sender2_cclerk.ml_dsa_public_bytes(),
                        default_token,
                        1_000_000,
                    )
                    .expect("canonical ML-DSA-65 sender2 identity"),
                )
                .expect("fund sender2");
        }
        // The committee is UNCHANGED (this node, alone) — funding a second USER does not enroll a
        // validator. This block used to widen the committee to {sender, sender2}, which is the same
        // "the node is not in its own committee" defect as the first install and would have failed
        // the second durable commit for the same reason. Re-read the id anyway so the fixture keeps
        // signing against whatever `federation_id_for_executor` reports rather than a cached value.
        let federation_id2 = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        assert_eq!(
            federation_id2, federation_id,
            "funding a user must not rotate the solo committee's federation id"
        );
        let signed2 =
            signed_transfer_turn(&sender2_cclerk, sender2, dest, 1_000, 0, &federation_id2);
        let turn_data2 = postcard::to_stdvec(&signed2).expect("encode signed turn 2");
        {
            let mut s = state.write().await;
            let executor = crate::executor_setup::new_submit_executor(&s);
            let mut scratch = s.ledger.clone();
            match crate::executor_setup::execute_via_producer(
                &executor,
                &signed2.turn,
                &mut scratch,
                false,
            ) {
                dregg_turn::TurnResult::Committed { receipt, .. } => {
                    s.cclerk.append_receipt(receipt).expect("ingress append 2");
                }
                other => panic!("second solo ingress must commit, got {other:?}"),
            }
        }
        let block_id2 = BlockId([0x23u8; 32]);
        execute_finalized_turn(&state, &handle, block_id2, &turn_data2, None, None, 0).await;
        let height_after_2 = {
            let s = state.read().await;
            s.store
                .latest_attested_root()
                .ok()
                .flatten()
                .map(|r| r.height)
                .unwrap_or(0)
        };
        assert_eq!(
            height_after_2, 2,
            "a second solo turn MUST advance the attested height 1 -> 2 (latest_height tracks turns)"
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
        let removed_cell = dregg_cell::Cell::with_balance([0xD0; 32], [0xD1; 32], 99);
        let removed_id = removed_cell.id();
        authoritative
            .insert_cell(removed_cell)
            .expect("seed cell removed by candidate");

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
        let _ = exec_ledger.remove(&removed_id);
        let touched = ledger_touched_diff(&pre_ledger, &exec_ledger);
        assert!(
            touched.contains(&sender) && touched.contains(&dest) && touched.contains(&removed_id),
            "the whole-cell diff must include update, create, and remove"
        );

        // PRE-COMMIT NONPUBLICATION: executing and diffing the isolated
        // candidate does not change the authoritative ledger at all.
        assert_eq!(
            authoritative.get(&sender).expect("sender").state.balance(),
            1_000_000
        );
        assert!(authoritative.get(&dest).is_none());
        assert!(authoritative.get(&removed_id).is_some());

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

        // === post-durable overlay install (the per-cell, non-replace apply) ===
        install_finalized_ledger_overlay(&mut authoritative, &exec_ledger, &touched);

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
        assert!(
            authoritative.get(&removed_id).is_none(),
            "a candidate tombstone removes the live cell after commit"
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
    /// (or a destination that already exists) leaves the cell untouched. The
    /// stub is minted in the SOURCE's asset — a Transfer is a single-asset move,
    /// so a landing site in any other asset refuses the very transfer it was
    /// created for — and a transfer whose SOURCE is absent provisions nothing.
    #[test]
    fn provision_transfer_destinations_is_deterministic_and_idempotent() {
        let sender_token = *blake3::hash(b"provisioning-asset").as_bytes();
        let sender_cell = dregg_cell::Cell::with_balance([1u8; 32], sender_token, 1_000);
        let sender = sender_cell.id();
        let dest = dregg_cell::CellId([0xEEu8; 32]);
        let mut forest = dregg_turn::CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(sender, "t", sender)
                .effect_transfer(sender, dest, 7)
                .build(),
        );

        // A transfer whose SOURCE this node has never seen provisions NOTHING:
        // the asset to land in is unknown and the transfer cannot execute anyway.
        let mut absent_source = dregg_cell::Ledger::new();
        provision_transfer_destinations(&mut absent_source, &forest);
        assert!(
            absent_source.get(&dest).is_none(),
            "no source cell ⇒ no landing site invented"
        );

        // Two independent nodes provision from the same forest → identical cell.
        let mut a = dregg_cell::Ledger::new();
        let mut b = dregg_cell::Ledger::new();
        a.insert_cell(sender_cell.clone()).expect("seed source (a)");
        b.insert_cell(sender_cell.clone()).expect("seed source (b)");
        provision_transfer_destinations(&mut a, &forest);
        provision_transfer_destinations(&mut b, &forest);
        let ca = a.get(&dest).expect("a provisioned").clone();
        let cb = b.get(&dest).expect("b provisioned").clone();
        assert_eq!(
            *ca.token_id(),
            sender_token,
            "the landing site must hold the asset being moved, or the executor refuses the \
             transfer as cross-asset"
        );
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
        c.insert_cell(sender_cell).expect("seed source (c)");
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
    pub(crate) async fn test_handle_with_committee(
        self_key: [u8; 32],
        participants: Vec<[u8; 32]>,
    ) -> BlocklaceHandle {
        test_handle_inner(
            self_key,
            ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]),
            participants,
        )
        .await
    }

    /// Like [`test_handle_with_committee`], but the handle's `self_key` AND the lace's
    /// `HybridBlockSigner` are the SAME identity — which is what the production boot builds
    /// (`run_blocklace_sync_with_policy` derives `self_key` from `signing_key` and hands the SAME
    /// `signing_key` to `Blocklace::new` / `store.load_blocklace`).
    ///
    /// ⚑ This distinction is load-bearing for the solo enrollment filter and NOT a convenience:
    /// [`solo_enrolled_creators`] admits the node's own hybrid id only when the node's own ed25519
    /// is an admitted constitutional participant, so a fixture whose lace is signed by an unrelated
    /// key (the `[7u8; 32]` above) models an OBSERVER, not a solo validator. Any test that means
    /// "a genuine solo node finalizing its own blocks" must use this constructor.
    async fn test_handle_for_signer(
        signing_key: ed25519_dalek::SigningKey,
        participants: Vec<[u8; 32]>,
    ) -> BlocklaceHandle {
        let self_key = signing_key.verifying_key().to_bytes();
        test_handle_inner(self_key, signing_key, participants).await
    }

    async fn test_handle_inner(
        self_key: [u8; 32],
        signing_key: ed25519_dalek::SigningKey,
        participants: Vec<[u8; 32]>,
    ) -> BlocklaceHandle {
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
        test_handle_with_transport(self_key, signing_key, participants, gossip, topic).await
    }

    /// Like [`test_handle_inner`] but over a CALLER-SUPPLIED transport (an
    /// already-meshed [`GossipNetwork`] + joined topic), so a multi-node test
    /// can build a real federation of handles without duplicating this literal.
    async fn test_handle_with_transport(
        self_key: [u8; 32],
        signing_key: ed25519_dalek::SigningKey,
        participants: Vec<[u8; 32]>,
        gossip: Arc<GossipNetwork>,
        topic: TopicHandle,
    ) -> BlocklaceHandle {
        use dregg_blocklace::constitution::{Constitution, ConstitutionManager};
        let quorum = dregg_blocklace::supermajority_threshold(participants.len());
        let blocklace = dregg_blocklace::finality::Blocklace::new(signing_key.clone(), quorum);
        let constitution =
            ConstitutionManager::new(Constitution::new(participants.clone(), 60_000));
        // No ML-DSA committee in this fixture (it exercises peer-address
        // learning, not vote quorum): an EMPTY pq map is the fail-closed
        // "hybrid unconfigured" state — the collector counts no votes.
        let votes = crate::finalization_votes::VoteCollector::new(
            participants.iter().copied(),
            HashMap::new(),
            quorum,
        );
        BlocklaceHandle {
            lace: Arc::new(RwLock::new(blocklace)),
            constitution: Arc::new(RwLock::new(constitution)),
            gossip,
            topic,
            self_key,
            pq_public_key: dregg_federation::frost::MlDsaSigningKey::from_seed(
                &signing_key.to_bytes(),
            )
            .0,
            pq_signing_key: dregg_federation::frost::MlDsaSigningKey::from_seed(
                &signing_key.to_bytes(),
            )
            .1,
            signing_key,
            votes: Arc::new(RwLock::new(votes)),
            my_pending_votes: Arc::new(RwLock::new(HashMap::new())),
            cursor: Arc::new(RwLock::new(crate::execution_cursor::ExecutionCursor::new())),
            finality_notify: Arc::new(Notify::new()),
            auto_approve_joins: false,
            // The narrow join channel is not exercised by the in-process test
            // handle: no candidate reaches it and it dials nobody.
            pending_joins: Arc::new(RwLock::new(HashMap::new())),
            join_progress: Arc::new(RwLock::new(JoinProgress::default())),
            peer_addrs: Vec::new(),
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
            round_advance_timer: Arc::new(std::sync::Mutex::new(
                crate::round_advance_gate::RoundAdvanceTimer::default(),
            )),
            ack_pending: Arc::new(std::sync::atomic::AtomicBool::new(false)),
            pending_payloads: Arc::new(RwLock::new(std::collections::VecDeque::new())),
            last_order_fingerprint: Arc::new(RwLock::new(None)),
            last_lean_order: Arc::new(RwLock::new(None)),
            liveness: Arc::new(FederationLiveness::default()),
            in_flight_turns: Arc::new(InFlightTurns::default()),
        }
    }

    // ─── CONSENSUS-SAFETY (F-CO-1): tau participant set from COMMITTED state ──────

    /// Build a committed-roster `NodeState` for `members` (ed25519 signing keys), with
    /// each member's ML-DSA half = `from_seed(member_ed_seed)` — the SAME value
    /// `Block::new` stamps into `creator`, so the projected hybrid ids match the lace.
    /// The returned `TempDir` must be kept alive for the state's lifetime.
    async fn committed_state_for(
        members: &[ed25519_dalek::SigningKey],
    ) -> (tempfile::TempDir, crate::state::NodeState) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let eds: Vec<dregg_types::PublicKey> = members
            .iter()
            .map(|k| dregg_types::PublicKey(k.verifying_key().to_bytes()))
            .collect();
        let mls: Vec<dregg_federation::frost::MlDsaPublicKey> = members
            .iter()
            .map(|k| dregg_federation::frost::MlDsaSigningKey::from_seed(&k.to_bytes()).0)
            .collect();
        {
            let mut s = state.write().await;
            s.set_federation_keys_hybrid(eds, mls);
        }
        (tmp, state)
    }

    /// A 3-round, fully cross-linked finality lace over `members` (the `trace3` shape):
    /// each round references ALL of the previous round; every block carries a Turn.
    /// Finalizes under `ordering::tau` with the members' hybrid ids as participants.
    fn cross_linked_finality_lace(
        members: &[ed25519_dalek::SigningKey],
        quorum: usize,
    ) -> Blocklace {
        let mut lace = Blocklace::new(members[0].clone(), quorum);
        let mut round_prev: Vec<BlockId> = Vec::new();
        for round in 0u64..=2 {
            let mut this_round = Vec::new();
            for (i, k) in members.iter().enumerate() {
                let b = Block::new(
                    k,
                    round,
                    Payload::Turn(vec![(round * 10) as u8 + i as u8]),
                    round_prev.clone(),
                );
                this_round.push(b.id());
                lace.receive_block(b).expect("block insert");
            }
            round_prev = this_round;
        }
        lace
    }

    fn finalized_order_ids(blocks: &[FinalizedBlock]) -> Vec<BlockId> {
        blocks
            .iter()
            .map(|b| match b {
                FinalizedBlock::Turn { block_id, .. }
                | FinalizedBlock::Membership { block_id, .. }
                | FinalizedBlock::Checkpoint { block_id, .. }
                | FinalizedBlock::Inert { block_id } => *block_id,
            })
            .collect()
    }

    /// F-CO-1 UNIT: the tau participant projection is a function of COMMITTED state
    /// alone — `project_committed_participants` takes NO node-local `votes` — so two
    /// honest nodes with the SAME committed roster project the BYTE-IDENTICAL set, and
    /// a live-joined validator absent from committed state is dropped identically on
    /// every node (deterministic, never a per-node divergence).
    #[tokio::test]
    async fn committed_participant_projection_ignores_node_local_key_view() {
        let members: Vec<ed25519_dalek::SigningKey> = [[0x21u8; 32], [0x22u8; 32], [0x23u8; 32]]
            .iter()
            .map(ed25519_dalek::SigningKey::from_bytes)
            .collect();
        let eds: Vec<[u8; 32]> = members
            .iter()
            .map(|k| k.verifying_key().to_bytes())
            .collect();
        let (_tmp, state) = committed_state_for(&members).await;

        // Expected hybrid ids, derived independently from the committed keys.
        let expected: Vec<[u8; 32]> = members.iter().map(Block::hybrid_id).collect();

        let projected = project_committed_participants(&state, &eds).await;
        assert_eq!(
            projected, expected,
            "the tau participant projection must be exactly the committed-roster hybrid ids \
             (a pure function of committed state, independent of any node's vote-collector view)"
        );

        // A joined validator with no committed ML-DSA key is dropped — the SAME drop on
        // every node (no fork), leaving exactly the committed set.
        let joined = ed25519_dalek::SigningKey::from_bytes(&[0x9Fu8; 32]);
        let mut admitted_with_j = eds.clone();
        admitted_with_j.push(joined.verifying_key().to_bytes());
        let projected_j = project_committed_participants(&state, &admitted_with_j).await;
        assert_eq!(
            projected_j, expected,
            "a joined validator with no COMMITTED ML-DSA key must be dropped deterministically \
             (every node drops it identically) — leaving exactly the committed set"
        );
    }

    /// TWIN-DELETION (#8) FAIL-CLOSED: on a Lean-linked full node the Rust `ordering::tau` twin is
    /// FORBIDDEN as the live finalized order — a poll with no verified order fails closed instead of
    /// running it. The twin is allowed ONLY on a genuinely no-Lean build (no `dregg_tau_order` export,
    /// which a full node is refused to start on) or under the explicit
    /// `DREGG_ALLOW_UNVERIFIED_CONSENSUS` escape. This pins the exact gate `poll_finalized_blocks`
    /// uses (`allow_rust_fallback`).
    #[test]
    fn rust_tau_twin_forbidden_on_verified_full_node() {
        // Live verified-role node: the verified `dregg_tau_order` export IS linked, no escape.
        assert!(
            !rust_tau_fallback_allowed(true, false),
            "the Rust ordering::tau twin must NEVER decide finality on a Lean-linked full node \
             without the escape — the poll must fail closed"
        );
        // Deliberate opt-in to unverified consensus: the twin is a labeled fallback.
        assert!(
            rust_tau_fallback_allowed(true, true),
            "DREGG_ALLOW_UNVERIFIED_CONSENSUS deliberately permits the Rust order as a labeled fallback"
        );
        // Genuinely no-Lean build (no verified order to route to): the Rust order is the honest
        // decider (a full node is refused to start in this state unless it opted in).
        assert!(
            rust_tau_fallback_allowed(false, false),
            "with no verified archive linked the Rust ordering::tau is the only decider available"
        );
        assert!(rust_tau_fallback_allowed(false, true));
    }

    /// ⚑ POLE A (the DISPOSITION, exhaustively): the verified finality BELT gate is UNAVAILABLE and
    /// finality REFUSES TO ADVANCE. This is the second confirmed member of the conservation twin's
    /// fail-OPEN class — `blocklace_sync` used to warn that the gate was unavailable, declare itself
    /// to be failing open to the un-gated tau order, and then execute turns off the un-gated Rust
    /// `ordering::tau`. (`lean-twins.tsv`'s `forbid` row keeps that exact warn text from returning, so
    /// it is deliberately not reproduced verbatim here.)
    ///
    /// The test asserts THE NEGATIVE the way conservation's Pole A does: an `Ok(())` in the
    /// no-bypass quadrant PANICS with a FAIL-OPEN message, because `Ok(())` there means the poll went
    /// on to advance finality with no verified gate — the exact defect.
    ///
    /// It also pins the two DECLARED bypasses (and that `DREGG_REQUIRE_LEAN=1` revokes both), and the
    /// VACUITY short-circuit (a heartbeat-only poll is not refused — a refusal that fires where it
    /// means nothing is a bust nobody can land).
    #[test]
    fn finality_fails_closed_when_the_verified_gate_is_unavailable() {
        // ── THE HOLE, CLOSED. Export linked, no operator escape, actionable work pending, and the
        //    gate could not answer (wire ERR / panicked FFI thread) ⇒ REFUSE.
        match finality_belt_disposition(None, 3, true, false, false) {
            Err(FinalityAdvanceRefusal::FinalityGateUnavailable) => { /* fail-closed */ }
            Ok(()) => panic!(
                "FAIL-OPEN: the verified `dregg_blocklace_finalize` projection gate IS linked, the \
                 operator did NOT accept unverified consensus, 3 consensus-actionable blocks are \
                 pending, and the gate returned NO ANSWER — yet the disposition permits the poll to \
                 ADVANCE FINALITY over the un-gated Rust `ordering::tau` order. That is the defect \
                 this gate exists to prevent: state transitions reach the executor with no verified \
                 finality rule having finalized them."
            ),
        }

        // The refusal is TOTAL over actionable work — one pending turn is enough, it is not a
        // threshold effect.
        assert!(
            finality_belt_disposition(None, 1, true, false, false).is_err(),
            "a single pending consensus-actionable block with no verified gate must refuse"
        );

        // ── VACUITY SHORT-CIRCUIT: NO consensus-actionable block is pending (an ack/heartbeat-only
        //    poll). There is no admission decision in existence, so refusing would halt the DAG on a
        //    verdict that does not exist — the over-refusal the conservation fix had to fix.
        assert!(
            finality_belt_disposition(None, 0, true, false, false).is_ok(),
            "a poll with no consensus-actionable pending block must NOT be refused — the belt only \
             ever gates actionable payloads, so there is nothing for a missing gate to have decided. \
             A refusal here would halt heartbeat processing on every poll."
        );

        // ── DECLARED BYPASS 1: no `dregg_blocklace_finalize` export in this binary at all. Nothing
        //    to route to (an archive-less build / the guest; for a full node, the state `lib.rs`'s
        //    verified-consensus hard-check refuses to start in).
        assert!(
            finality_belt_disposition(None, 3, false, false, false).is_ok(),
            "with NO verified projection export linked there is no gate to be unavailable — this is \
             the DECLARED bypass (gate-dataflow.tsv), not a silent fall-open"
        );
        // ── DECLARED BYPASS 2: the operator explicitly accepted unverified consensus.
        assert!(
            finality_belt_disposition(None, 3, true, true, false).is_ok(),
            "DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 is the operator's declared acceptance of un-gated \
             finality (the same escape twin#8 and twin#11 use)"
        );
        // ── `DREGG_REQUIRE_LEAN=1` REVOKES BOTH — this is what lets an archive-less build drive the
        //    same hard refusal a deployed node reaches on its own.
        assert!(
            finality_belt_disposition(None, 3, false, false, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the no-export bypass"
        );
        assert!(
            finality_belt_disposition(None, 3, true, true, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the operator-escape bypass too"
        );

        // The bypass predicate itself, so a future widening is a visible diff and not a quiet
        // boolean flip.
        assert!(!belt_gate_bypass_allowed(true, false, false));
        assert!(belt_gate_bypass_allowed(false, false, false));
        assert!(belt_gate_bypass_allowed(true, true, false));
        assert!(!belt_gate_bypass_allowed(false, true, true));
    }

    /// ⚑ POLE A (twin#12, the ATTESTATION flavour of the fail-open class): a bearer-delegated turn
    /// whose delegator pre-state cap root cannot be resolved publishes NO full-turn proof, instead of
    /// a v1 proof that silently omits the AUTHORITY leg it needs.
    ///
    /// ⚑ THE ANSWER THIS TEST ENCODES, established before the fix and stated so nobody re-litigates
    /// it from the comment alone: a verifier DOES accept a v1 proof for a bearer-delegated turn.
    /// `verify_full_turn_bound`'s authority demand is inside `if let Some(expected) =
    /// expected_cap_membership`, and the only entry point anyone outside the prover calls
    /// (`verify_full_turn`) hardcodes `None` — the verification MODE is a caller-supplied argument
    /// and the prover is the only party that ever supplies one. AND the scope qualifier that keeps
    /// that from being over-read: this is NOT an authorization bypass. The executor enforces the
    /// delegation independently on every node (`verify_bearer_cap`: signature, delegator-holds-the-cap,
    /// expiry, committed revocation, non-amplification) and every node re-executes the finalized turn,
    /// so the gap is in what is ATTESTED, not in what is authorized.
    ///
    /// The test asserts THE NEGATIVE the way its four siblings do: an `Ok(())` in the no-bypass
    /// quadrant PANICS with a FAIL-OPEN message, because `Ok(())` there means the node went on to
    /// publish an attestation it knows to be incomplete. It also pins the VACUITY short-circuit (the
    /// overwhelming majority of turns are not bearer-delegated and must never be refused) and the
    /// bypass predicate's own quadrants — invariant 6 does NOT evaluate the discriminator, so a
    /// mutation of `bearer_authority_bypass_allowed` to a bare `true` stays GREEN there and must
    /// redden HERE. Invariants 2 and 6 are COMPLEMENTS at this site, not alternatives.
    #[test]
    fn bearer_authority_leg_fails_closed_when_the_delegator_root_is_unresolvable() {
        let root = [dregg_circuit::field::BabyBear::new(7); 8];

        // ── THE HOLE, CLOSED. The turn IS bearer-delegated, the delegator root is unresolvable, and
        //    no bypass is declared ⇒ REFUSE to publish.
        match bearer_authority_disposition(None, true, false, false) {
            Err(BearerAuthorityRefusal::DelegatorCapRootUnresolvable) => { /* fail-closed */ }
            Ok(()) => panic!(
                "FAIL-OPEN: this turn carries a BearerSignedDelegation consumed-cap witness, the \
                 node could NOT resolve the delegator's pre-state capability root, and no bypass is \
                 declared — yet the disposition permits the commit path to publish a v1 full-turn \
                 proof anyway. That proof omits the AUTHORITY leg, and NOTHING downstream ever asks \
                 for it back: `verify_full_turn` hardcodes `expected_cap_membership: None` and no \
                 consumer in the tree builds a CapMembershipExpectation. So the node would publish, \
                 under `full_turn_proof:{{hash}}` and a `has_proof` flag, an attestation that claims \
                 less than the turn's authorization and says so nowhere."
            ),
        }

        // ── VACUITY SHORT-CIRCUIT: not a bearer-delegated turn at all. Self-sovereign turns, note
        //    spends and actor-held capability turns have no delegator and no leg to be missing —
        //    refusing there would stop the node publishing ANY proof.
        assert!(
            bearer_authority_disposition(None, false, false, false).is_ok(),
            "a turn with NO bearer delegation must NEVER be refused — there is no authority leg in \
             existence for a missing delegator root to have broken. A refusal here would withhold \
             the proof of every ordinary turn on the node."
        );

        // ── THE ROOT RESOLVED: there is no missing binding to dispose of.
        assert!(
            bearer_authority_disposition(Some(&root), true, false, false).is_ok(),
            "a bearer turn whose delegator root RESOLVED routes through the holder-bound authority \
             leg — that is the success path, not a refusal"
        );

        // ── THE ONE DECLARED BYPASS: the operator accepted the partial attestation.
        assert!(
            bearer_authority_disposition(None, true, true, false).is_ok(),
            "DREGG_ALLOW_UNBOUND_BEARER_PROOF=1 is the operator's declared acceptance of a v1 proof \
             without the authority leg (the same shape twin#8b, twin#3b and twin#13 use)"
        );
        // ── `DREGG_REQUIRE_LEAN=1` REVOKES it.
        assert!(
            bearer_authority_disposition(None, true, true, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the unbound-bearer-proof opt-in"
        );

        // The bypass predicate itself, so a future widening is a visible diff and not a quiet
        // boolean flip. Invariant 6 CANNOT see this — these four lines are the complement that
        // catches a `bearer_authority_bypass_allowed -> true` mutant.
        assert!(!bearer_authority_bypass_allowed(false, false));
        assert!(bearer_authority_bypass_allowed(true, false));
        assert!(!bearer_authority_bypass_allowed(true, true));
        assert!(!bearer_authority_bypass_allowed(false, true));
    }

    /// ⚑ POLE A AT THE POLL, and POLE B beside it: the SAME handle, the SAME lace, the SAME committed
    /// roster — the ONLY thing that changes is whether the belt gate can answer.
    ///
    /// * BELT ANSWERS (or is not armed) ⇒ honest finality ADVANCES (a non-empty batch). Without this
    ///   half, "refuses when the gate is missing" is satisfied by a node that finalizes nothing ever.
    /// * BELT ARMED AND CANNOT ANSWER ⇒ the poll returns an EMPTY batch and NOTHING reaches the
    ///   executor. A non-empty batch here PANICS with a FAIL-OPEN message: it would mean turns were
    ///   sliced to the executor off the un-gated Rust `ordering::tau` order.
    ///
    /// The fault injector is needed because the armed-and-unanswerable state is not producible
    /// in-process on either build (see `FORCE_BELT_GATE_UNANSWERABLE`) — without it this pole would
    /// pass VACUOUSLY wherever the Lean archive is present.
    #[tokio::test]
    async fn poll_refuses_to_advance_finality_when_the_belt_gate_cannot_answer() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        let members: Vec<ed25519_dalek::SigningKey> = [[0x51u8; 32], [0x52u8; 32], [0x53u8; 32]]
            .iter()
            .map(ed25519_dalek::SigningKey::from_bytes)
            .collect();
        let eds: Vec<[u8; 32]> = members
            .iter()
            .map(|k| k.verifying_key().to_bytes())
            .collect();
        let quorum = dregg_blocklace::supermajority_threshold(members.len());

        let (_tmp, state) = committed_state_for(&members).await;
        let handle = test_handle_with_committee(eds[0], eds.clone()).await;
        *handle.lace.write().await = cross_linked_finality_lace(&members, quorum);
        {
            let mut pq = HashMap::new();
            for k in &members {
                pq.insert(
                    k.verifying_key().to_bytes(),
                    dregg_federation::frost::MlDsaSigningKey::from_seed(&k.to_bytes()).0,
                );
            }
            handle.votes.write().await.set_committee(eds.clone(), pq);
        }

        // ── POLE B: the honest baseline. No fault injected ⇒ finality advances.
        set_belt_gate_fault_injected(false);
        let honest = handle.poll_finalized_blocks(&state).await;
        assert!(
            !honest.is_empty(),
            "the 3-node cross-linked lace must finalize a non-empty batch with the gate in its \
             normal state — otherwise the refusal pole below asserts nothing (a node that never \
             finalizes trivially 'fails closed')"
        );
        let honest_actionable = honest
            .iter()
            .filter(|b| !matches!(b, FinalizedBlock::Inert { .. }))
            .count();
        assert!(
            honest_actionable > 0,
            "the honest baseline must include at least one CONSENSUS-ACTIONABLE finalized block — a \
             heartbeat-only batch would hit the vacuity short-circuit and make the refusal pole \
             vacuous too"
        );

        // ── POLE A: hold EVERYTHING fixed and change ONLY the gate's ability to answer. Reset the
        //    cursor so the same order is re-served (otherwise `pending` is empty and the vacuity
        //    short-circuit — not the refusal — would produce the empty batch).
        *handle.cursor.write().await = crate::execution_cursor::ExecutionCursor::new();
        set_belt_gate_fault_injected(true);
        let refused = handle.poll_finalized_blocks(&state).await;
        set_belt_gate_fault_injected(false);

        if !refused.is_empty() {
            panic!(
                "FAIL-OPEN: the verified finality belt gate was ARMED and could NOT answer, and the \
                 poll STILL sliced {} finalized block(s) ({} consensus-actionable) to the executor \
                 off the UN-GATED Rust `ordering::tau` order. Nothing verified finalized them. This \
                 is exactly the fail-OPEN-to-the-un-gated-tau-order defect this gate closes.",
                refused.len(),
                refused
                    .iter()
                    .filter(|b| !matches!(b, FinalizedBlock::Inert { .. }))
                    .count()
            );
        }

        // And it is a REFUSAL, not a stuck cursor: with the gate answering again the same lace
        // finalizes the same honest batch. A fail-closed path that never recovers is not a fix.
        *handle.cursor.write().await = crate::execution_cursor::ExecutionCursor::new();
        let recovered = handle.poll_finalized_blocks(&state).await;
        assert_eq!(
            finalized_order_ids(&recovered),
            finalized_order_ids(&honest),
            "once the belt gate can answer again the SAME lace must finalize the SAME order — the \
             refusal halts the poll, it does not poison the cursor or drop blocks"
        );
    }

    /// F-CO-1 FALSIFIER (the fork the fix closes): two poll passes over the SAME lace
    /// and the SAME committed roster but with DIFFERENT node-local vote-collector key
    /// knowledge compute the IDENTICAL finalized order — no cross-node divergence.
    ///
    /// Pass 1 has the full ML-DSA committee in `votes`; pass 2 has an EMPTY `votes`
    /// committee (modelling a peer that has learned NO keys yet). Before the fix the
    /// projection read `votes.pq_key`, so pass 2 would project the empty set → HALT,
    /// diverging from pass 1's full order — a silent fork between two honest nodes.
    /// After the fix the projection reads committed state, so both passes project the
    /// full {A,B,C} set and finalize the identical order.
    ///
    /// Mutation canary: revert the projection to read `votes.pq_key` and pass 2 returns
    /// EMPTY while pass 1 is non-empty ⇒ this asserts RED.
    #[tokio::test]
    async fn divergent_vote_key_knowledge_yields_identical_finalized_order() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        let members: Vec<ed25519_dalek::SigningKey> = [[0x31u8; 32], [0x32u8; 32], [0x33u8; 32]]
            .iter()
            .map(ed25519_dalek::SigningKey::from_bytes)
            .collect();
        let eds: Vec<[u8; 32]> = members
            .iter()
            .map(|k| k.verifying_key().to_bytes())
            .collect();
        let quorum = dregg_blocklace::supermajority_threshold(members.len());

        let (_tmp, state) = committed_state_for(&members).await;
        let handle = test_handle_with_committee(eds[0], eds.clone()).await;
        *handle.lace.write().await = cross_linked_finality_lace(&members, quorum);

        // PASS 1 — full node-local key knowledge in the vote collector.
        {
            let mut pq = HashMap::new();
            for k in &members {
                pq.insert(
                    k.verifying_key().to_bytes(),
                    dregg_federation::frost::MlDsaSigningKey::from_seed(&k.to_bytes()).0,
                );
            }
            handle.votes.write().await.set_committee(eds.clone(), pq);
        }
        let order1 = finalized_order_ids(&handle.poll_finalized_blocks(&state).await);
        assert!(
            !order1.is_empty(),
            "the 3-node cross-linked lace must finalize a non-empty order (else the falsifier is \
             vacuous)"
        );

        // PASS 2 — DIFFERENT node's view: an EMPTY vote-collector committee (no keys
        // learned). Reset the execution cursor so the poll re-serves the whole order.
        *handle.cursor.write().await = crate::execution_cursor::ExecutionCursor::new();
        handle
            .votes
            .write()
            .await
            .set_committee(eds.clone(), HashMap::new());
        let order2 = finalized_order_ids(&handle.poll_finalized_blocks(&state).await);

        assert_eq!(
            order1, order2,
            "two honest nodes with the SAME committed roster but DIFFERENT vote-collector key \
             knowledge must finalize the IDENTICAL order — the participant set (hence the tau \
             leader schedule) is a function of committed state, never node-local key knowledge. \
             A divergence here is the silent consensus fork F-CO-1."
        );
    }

    /// F-CO-1 GUARD: a live-JOINED validator whose ML-DSA key is NOT in committed state
    /// makes the committed projection cover fewer than all admitted participants, so the
    /// poll FAILS CLOSED (halts) rather than ordering over the surviving subset — which
    /// would fork against a node holding the full committed set.
    ///
    /// Mutation canary: revert the guard to `participants.len() <= 1` and this reddens —
    /// the projection {A,B} (2 > 1) would fall through to tau over the subset and finalize.
    #[tokio::test]
    async fn joined_validator_without_committed_key_halts_finality() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        // Committed genesis roster {A, B}; J joins the constitution but its ML-DSA key
        // is never committed (the Join payload carries only ed25519).
        let ab: Vec<ed25519_dalek::SigningKey> = [[0x41u8; 32], [0x42u8; 32]]
            .iter()
            .map(ed25519_dalek::SigningKey::from_bytes)
            .collect();
        let ed_a = ab[0].verifying_key().to_bytes();
        let ed_b = ab[1].verifying_key().to_bytes();
        let ed_j = ed25519_dalek::SigningKey::from_bytes(&[0x4Au8; 32])
            .verifying_key()
            .to_bytes();

        let (_tmp, state) = committed_state_for(&ab).await;
        // Constitution {A, B, J}; the lace finalizes under tau over {A, B}.
        let handle = test_handle_with_committee(ed_a, vec![ed_a, ed_b, ed_j]).await;
        let quorum = dregg_blocklace::supermajority_threshold(2);
        *handle.lace.write().await = cross_linked_finality_lace(&ab, quorum);

        let finalized = handle.poll_finalized_blocks(&state).await;
        assert!(
            finalized.is_empty(),
            "admitted = {{A,B,J}} but J has no COMMITTED ML-DSA key ⇒ the projection covers only \
             {{A,B}} ⇒ finality must FAIL CLOSED (halt), never order over the subset (which would \
             fork against a node holding J's key) — got {} finalized block(s)",
            finalized.len()
        );
    }

    /// LIVENESS COMPANION: a GENUINE solo node (`admitted == 1`) still finalizes its
    /// actionable blocks in `seq` order. Guards the fail-closed fix above against an
    /// over-aggressive mutation (e.g. "always halt") — the fail-closed arm must fire
    /// ONLY when a genuine n>1 federation's projection is incomplete, never for real solo.
    ///
    /// ⚑ FIXTURE CORRECTED (solo enrollment filter). This used to build the handle with
    /// `test_handle_with_committee(pk_self, vec![pk_self])`, where `pk_self` is a random keypair
    /// and the LACE is signed by an unrelated `[7u8; 32]` — so the node authoring the block was
    /// NOT the constitutional participant. That models an observer, not a solo validator, and
    /// under the enrollment filter it is (correctly) refused. The constructor now ties the two,
    /// exactly as the production boot does, so the test asserts what its name says.
    #[tokio::test]
    async fn genuine_solo_node_still_finalizes() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        let sk_self = ed25519_dalek::SigningKey::from_bytes(&[0x5Au8; 32]);
        let pk_self = sk_self.verifying_key().to_bytes();
        let handle = test_handle_for_signer(sk_self, vec![pk_self]).await;
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");

        {
            let mut lace = handle.lace.write().await;
            lace.add_block(Payload::Turn(vec![9, 9, 9]));
        }

        let finalized = handle.poll_finalized_blocks(&state).await;
        assert_eq!(
            finalized.len(),
            1,
            "a genuine solo node (admitted == 1) must still finalize its actionable Turn — \
             the fail-closed fix must not halt real solo finality"
        );
    }

    // ─── THE SOLO ENROLLMENT FILTER (the `c6f00c228` residual, closed) ────────────

    /// Build a solo-shaped finality lace: the solo node's own genesis Turn at **seq 0**, and an
    /// UNENROLLED creator's genuinely well-formed, correctly hybrid-signed Turn at **seq 0** which
    /// the node's own later block ACKNOWLEDGES (so it is load-bearing in the causal past, not an
    /// unreferenced island). Inserted with `receive_block` (ed25519-only) on purpose: that is the
    /// ingest both reachable production paths produce — see the falsifier's HONEST SCOPE.
    fn solo_lace_with_an_unenrolled_creator(
        solo: &ed25519_dalek::SigningKey,
        stranger: &ed25519_dalek::SigningKey,
    ) -> Blocklace {
        let mut lace = Blocklace::new(solo.clone(), 1);
        let mine0 = Block::new(solo, 0, Payload::Turn(vec![0xA0]), vec![]);
        let mine0_id = mine0.id();
        lace.receive_block(mine0).expect("own seq-0 block inserts");
        let theirs0 = Block::new(stranger, 0, Payload::Turn(vec![0xB0]), vec![]);
        let theirs0_id = theirs0.id();
        lace.receive_block(theirs0)
            .expect("stranger seq-0 block inserts (receive_block is ed25519-only)");
        // Our seq-1 block ACKS both — the stranger's genesis is now in our causal past.
        let mine1 = Block::new(
            solo,
            1,
            Payload::Turn(vec![0xA1]),
            vec![mine0_id, theirs0_id],
        );
        lace.receive_block(mine1).expect("own seq-1 block inserts");
        lace
    }

    /// ⚑ **THE SOLO TOOTH, AT SEQ 0 — the arm a bootstrap runs in.**
    ///
    /// `poll_finalized_blocks`' `admitted.len() <= 1` arm had NO creator check at all: it
    /// finalized every actionable block in the lace by `seq`, whoever made it. The sibling
    /// falsifier `finality_gate::tests::attacker_block_from_unenrolled_creator_is_refused_by_the_
    /// verified_rule` fires at seq 1 on the MULTI-PARTY arm and cannot see this one — the solo arm
    /// never calls `tau`, `tauOrder`, or the belt gate, so no verified export is consulted anywhere
    /// on this path. And seq 0 is where a bootstrap lives: this asserts the filter at the exact
    /// coordinate a cold-started node's first block occupies.
    ///
    /// HONEST SCOPE — two ORDINARY production paths produce this lace with no attack on the ingest:
    ///   * a federation SHRUNK to n=1. `finality.rs::enroll_pq` only inserts (nothing in the
    ///     workspace removes), so the pinned ingest roster is INSERT-ONLY, while
    ///     `apply_passed_proposal` shrinks `constitution.current.participants` and this poll
    ///     re-reads it every time. A removed validator's NEW blocks keep passing
    ///     `receive_block_pinned` into the lace this arm then finalizes whole.
    ///   * a RESTART through the authenticating `finality.rs::from_checkpoint` (see the companion
    ///     test below, which drives the verbatim `from_checkpoint_trusted` shape to keep the
    ///     hazard constructible): signatures/closure/equivocation are re-checked on restore since
    ///     2026-08-08, but the restored lace still has an EMPTY `pq_roster` — no roster check.
    ///
    /// ⚑ **THE COMMITTED ROSTER IS EMPTY** — `NodeState::new(tmp, vec![])`, no
    /// `set_federation_keys_hybrid`. This is the GENUINE COLD START, and it is the guard that makes
    /// the test about the fix rather than about a committed key: `project_committed_participants`
    /// returns EMPTY here (asserted below), so the only thing that can admit the solo node's own
    /// blocks is the LOCAL derivation of its own hybrid id from its own ed25519 seed. If that
    /// derivation were not sound, this test would fail on the HONEST pole, not the refusal — which
    /// is exactly the "a filter one key short refuses the node's own blocks and the chain never
    /// starts" failure `c6f00c228` declined to risk.
    ///
    /// BOTH HALVES, because either alone is satisfied by a broken gate:
    ///   * the unenrolled creator's seq-0 block is REFUSED, and
    ///   * the solo node's OWN seq-0 and seq-1 blocks still finalize.
    #[tokio::test]
    async fn solo_arm_refuses_an_unenrolled_creator_at_seq_zero() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        let solo = ed25519_dalek::SigningKey::from_bytes(&[0x60u8; 32]);
        let stranger = ed25519_dalek::SigningKey::from_bytes(&[0x61u8; 32]);
        let solo_ed = solo.verifying_key().to_bytes();
        let solo_hybrid = Block::hybrid_id(&solo);
        let stranger_hybrid = Block::hybrid_id(&stranger);
        assert_ne!(
            solo_hybrid, stranger_hybrid,
            "the stranger must be a DIFFERENT identity — else this test has no adversary"
        );

        // GENUINE COLD START: a fresh store with NO committed federation roster at all.
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let handle = test_handle_for_signer(solo.clone(), vec![solo_ed]).await;
        *handle.lace.write().await = solo_lace_with_an_unenrolled_creator(&solo, &stranger);

        // ── ANTI-VACUITY 1: the projection this arm was told it needed is EMPTY. Nothing the
        //    committed roster carries can be what admits the solo node's blocks below.
        let projected = project_committed_participants(&state, &[solo_ed]).await;
        assert!(
            projected.is_empty(),
            "a cold-started node has NO committed ML-DSA key for itself — if the projection is \
             non-empty this fixture is not a cold start and the derivation half is untested"
        );

        // ── ANTI-VACUITY 2: the stranger really is in the lace, at seq 0, with an ACTIONABLE
        //    payload the arm's payload filter admits — so there is something to refuse.
        let stranger_seqs: Vec<u64> = {
            let lace = handle.lace.read().await;
            lace.iter()
                .filter(|(_, b)| b.creator == stranger_hybrid)
                .map(|(_, b)| b.seq)
                .collect()
        };
        assert_eq!(
            stranger_seqs,
            vec![0],
            "the unenrolled creator must have exactly its seq-0 block in the lace — else there is \
             nothing for the solo arm to refuse at the bootstrap coordinate"
        );

        // ── ANTI-VACUITY 3 (THE WOUND, EXECUTED — no mutation required). The arm's payload filter
        //    and `seq` sort WITHOUT the enrollment filter finalize the stranger's block. This is
        //    the permanent in-tree witness that the filter is load-bearing rather than a no-op.
        let unfiltered: Vec<[u8; 32]> = {
            let lace = handle.lace.read().await;
            let mut v: Vec<(u64, [u8; 32])> = lace
                .iter()
                .filter_map(|(_, block)| match &block.payload {
                    Payload::Turn(_)
                    | Payload::TurnBundle(_)
                    | Payload::ConsensusTimedTurnV1(_)
                    | Payload::MembershipVote { .. }
                    | Payload::Checkpoint { .. } => Some((block.seq, block.creator)),
                    _ => None,
                })
                .collect();
            v.sort_unstable();
            v.into_iter().map(|(_, c)| c).collect()
        };
        assert!(
            unfiltered.contains(&stranger_hybrid),
            "the UNFILTERED solo arm (the shape this code shipped with) must finalize the \
             unenrolled creator's block — if it does not, this fixture cannot witness the wound \
             and the refusal below asserts nothing"
        );

        // ── THE REAL POLL, over the REAL handle.
        let finalized = handle.poll_finalized_blocks(&state).await;
        let finalized_creators: Vec<[u8; 32]> = {
            let lace = handle.lace.read().await;
            finalized_order_ids(&finalized)
                .iter()
                .filter_map(|id| lace.get(id).map(|b| (b.creator, b.seq)))
                .map(|(c, _)| c)
                .collect()
        };
        let finalized_coords: Vec<(u64, [u8; 32])> = {
            let lace = handle.lace.read().await;
            finalized_order_ids(&finalized)
                .iter()
                .filter_map(|id| lace.get(id).map(|b| (b.seq, b.creator)))
                .collect()
        };

        // ── HALF 1, THE HONEST POLE FIRST. A gate that refuses everyone is exactly as broken as
        //    one that refuses no one, and it is what a wrong self-derivation would produce.
        assert!(
            finalized_coords.contains(&(0, solo_hybrid)),
            "the solo node's OWN seq-0 block was NOT finalized on a genuine cold start (committed \
             roster EMPTY) — the enrollment filter is refusing the node's own blocks and the chain \
             never starts. That is a WORSE bug than the one it closes. Finalized: {finalized_coords:?}"
        );
        assert!(
            finalized_coords.contains(&(1, solo_hybrid)),
            "the solo node's own seq-1 block must finalize too — the filter is a SUBTRACTION on an \
             all-enrolled prefix, not a stall. Finalized: {finalized_coords:?}"
        );

        // ── HALF 2, THE REFUSAL.
        assert!(
            !finalized_creators.contains(&stranger_hybrid),
            "the SOLO finality arm FINALIZED a block created by an UNENROLLED identity — an \
             unenrolled node can inject state transitions into this node's executor. The gate is \
             OPEN. Finalized: {finalized_coords:?}"
        );
    }

    /// ⚑ **THE RESTART SHAPE, DRIVEN — a restored lace is where unenrolled blocks
    /// come back, and the solo arm is what used to finalize them.**
    ///
    /// Since 2026-08-08 the boot path (`store.load_blocklace`,
    /// `persist/src/blocklace_store.rs`) routes through the AUTHENTICATING
    /// `finality.rs::from_checkpoint` — signature, closure and equivocation are re-checked on
    /// restore. What NO restore does is a roster check, and the restored lace's `pq_roster` is
    /// EMPTY either way (a fresh `Blocklace::new`): a creator that was rotated out — or never
    /// enrolled, if its blocks are validly signed — comes back. This test drives the verbatim
    /// `from_checkpoint_trusted` deliberately, because it CONSTRUCTS the worst restored shape
    /// (the stranger's block re-admitted with no checks at all) and proves the FINALITY arm
    /// refuses it even then; the authenticating restore only shrinks what reaches this gate.
    ///
    /// THE ANSWER TO "does closing the solo arm without closing the restart accomplish anything":
    /// YES, and this test is the measurement. The restart is the SUPPLIER of unenrolled blocks; the
    /// solo arm was the CONSUMER that fed them to the executor. With the restore at its weakest —
    /// every block re-admitted, `pq_roster` empty, asserted below — the poll refuses the
    /// stranger and still finalizes the node's own restored blocks.
    #[tokio::test]
    async fn restored_trusted_checkpoint_does_not_resurrect_an_unenrolled_creator() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        let solo = ed25519_dalek::SigningKey::from_bytes(&[0x62u8; 32]);
        let stranger = ed25519_dalek::SigningKey::from_bytes(&[0x63u8; 32]);
        let solo_ed = solo.verifying_key().to_bytes();
        let solo_hybrid = Block::hybrid_id(&solo);
        let stranger_hybrid = Block::hybrid_id(&stranger);

        // The lace as it stood before the restart, then the checkpoint, then THE RESTART.
        let before = solo_lace_with_an_unenrolled_creator(&solo, &stranger);
        let checkpoint = before.checkpoint();
        let restored = Blocklace::from_checkpoint_trusted(&checkpoint, solo.clone(), 1)
            .expect("the trusted restore accepts the checkpoint verbatim");

        // ── ANTI-VACUITY: the restore really did re-admit the stranger, and really did come back
        //    with an EMPTY PQ roster — i.e. the supplier path is intact and is not what refuses.
        assert!(
            restored.pq_roster().is_empty(),
            "from_checkpoint_trusted builds a fresh Blocklace, so the restored PQ roster is EMPTY \
             — if this ever becomes non-empty the restore has grown a check and this test is \
             measuring something else"
        );
        assert_eq!(
            restored.len(),
            before.len(),
            "the trusted restore re-inserts EVERY persisted block with no roster check — that is \
             the path under test"
        );
        assert!(
            restored
                .iter()
                .any(|(_, b)| b.creator == stranger_hybrid && b.seq == 0),
            "the unenrolled creator's block must survive the restore — else there is nothing for \
             the finality arm to refuse"
        );

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), Vec::new()).expect("node state");
        let handle = test_handle_for_signer(solo.clone(), vec![solo_ed]).await;
        *handle.lace.write().await = restored;

        let finalized = handle.poll_finalized_blocks(&state).await;
        let coords: Vec<(u64, [u8; 32])> = {
            let lace = handle.lace.read().await;
            finalized_order_ids(&finalized)
                .iter()
                .filter_map(|id| lace.get(id).map(|b| (b.seq, b.creator)))
                .collect()
        };

        assert!(
            coords.contains(&(0, solo_hybrid)) && coords.contains(&(1, solo_hybrid)),
            "a node that RESTARTED must still finalize its own restored blocks — a restart that \
             comes back unable to finalize anything is a worse outage than the hole. Got {coords:?}"
        );
        assert!(
            !coords.iter().any(|(_, c)| *c == stranger_hybrid),
            "a RESTART through `from_checkpoint_trusted` resurrected an UNENROLLED creator's block \
             and the solo finality arm fed it to the executor. Got {coords:?}"
        );
    }

    // ─── GOVERNANCE: the voter identity the live path hands the constitution ──────

    /// A cross-linked finality lace over `members` where round `r`'s block from member
    /// `i` carries `payloads[r][i]` if present, else `Payload::Ack`. Every round
    /// references ALL of the previous round (the shape `tau` super-ratifies).
    fn cross_linked_lace_with(
        members: &[ed25519_dalek::SigningKey],
        quorum: usize,
        rounds: u64,
        payloads: &[(u64, usize, Payload)],
    ) -> (Blocklace, HashMap<(u64, usize), BlockId>) {
        let mut lace = Blocklace::new(members[0].clone(), quorum);
        let mut ids: HashMap<(u64, usize), BlockId> = HashMap::new();
        let mut round_prev: Vec<BlockId> = Vec::new();
        for round in 0..rounds {
            let mut this_round = Vec::new();
            for (i, k) in members.iter().enumerate() {
                let payload = payloads
                    .iter()
                    .find(|(r, m, _)| *r == round && *m == i)
                    .map(|(_, _, p)| p.clone())
                    .unwrap_or(Payload::Ack);
                let b = Block::new(k, round, payload, round_prev.clone());
                let id = b.id();
                ids.insert((round, i), id);
                this_round.push(id);
                lace.receive_block(b).expect("block insert");
            }
            round_prev = this_round;
        }
        (lace, ids)
    }

    /// ⚑ **THE GOVERNANCE TOOTH: a membership vote that actually COUNTS, through the
    /// live poll — and a stranger's that does not, in the same process.**
    ///
    /// THE WOUND. `poll_finalized_blocks` built `FinalizedBlock::Membership` with
    /// `creator: block.creator` — the HYBRID consensus id `H(ed25519 ‖ ml_dsa)` — and
    /// `execute_finalized_membership` handed that straight to
    /// `ConstitutionManager::submit_vote`, whose `VoteTracker::record_vote` opens with
    /// `if !constitution.is_participant(&voter) { return … }` over a participant set
    /// keyed by **ed25519**. A hybrid id is a BLAKE3 commitment and is never equal to a
    /// member's ed25519 key, so the gate refused unconditionally: **no membership vote
    /// submitted through the live path had ever counted.** Every join, leave, threshold
    /// amendment and route amendment was silently inert. The pure twin
    /// `committee_replay::fold_membership_block` was fed `block.ed25519` and was right.
    ///
    /// WHY ED25519 IS THE RIGHT KEYING and not the convenient one. The hybrid id is a
    /// ONE-WAY commitment. `project_committed_participants` maps ed25519 → hybrid using
    /// committed state, and that is the direction consensus needs; the inverse does not
    /// exist. A hybrid-keyed constitution could not produce the ed25519 keys
    /// `apply_committee_change` requires — it re-derives each member's hybrid id for
    /// `enroll_pq` from `(ed25519, ml_dsa)`, hands the ed25519 set to
    /// `VoteCollector::reconfigure`, and hashes each ed25519 for the gossip `NodeId`.
    /// `MembershipAction::Join` likewise carries an ed25519 `node_id`. Governance is
    /// keyed by the strand; finality is keyed by a projection OF the strand, and the two
    /// keyings are correct precisely because they differ.
    ///
    /// BOTH POLES, IN ONE PROCESS, because a path that has never worked grows tests
    /// shaped around it not working:
    ///   * PHASE 1 — A proposes Join(D) and B approves. Two CURRENT participants' votes
    ///     must COUNT (approvals == 2) while the proposal correctly does NOT yet apply
    ///     (quorum for n=3 is 3). This is the pole the wound erased: pre-fix, approvals
    ///     was 0 and D would never be admitted no matter how many honest validators voted.
    ///   * PHASE 2 — a STRANGER (not a participant) casts Approve on the same proposal.
    ///     Approvals must stay 2 and the proposal must stay unapplied.
    ///   * PHASE 3 — C, the third CURRENT participant, approves. Quorum is reached, the
    ///     proposal APPLIES, and it TAKES EFFECT: D is a participant, the constitution
    ///     version advances, the threshold recomputes, and the LIVE committee advances
    ///     (`VoteCollector::is_committee_member(D)`) — not merely "submit_vote returned Ok".
    #[tokio::test]
    async fn membership_vote_counts_through_the_live_poll_and_a_strangers_is_refused() {
        let _ = rustls::crypto::ring::default_provider().install_default();

        // A, B, C = the genesis committee. D = the validator being admitted.
        // The stranger is not in the committee and never becomes one.
        let members: Vec<ed25519_dalek::SigningKey> = [[0x71u8; 32], [0x72u8; 32], [0x73u8; 32]]
            .iter()
            .map(ed25519_dalek::SigningKey::from_bytes)
            .collect();
        let d = ed25519_dalek::SigningKey::from_bytes(&[0x74u8; 32]);
        let stranger = ed25519_dalek::SigningKey::from_bytes(&[0x7Fu8; 32]);
        let eds: Vec<[u8; 32]> = members
            .iter()
            .map(|k| k.verifying_key().to_bytes())
            .collect();
        let ed_d = d.verifying_key().to_bytes();
        let ed_stranger = stranger.verifying_key().to_bytes();

        // D's ML-DSA half IS committed, so the post-join projection covers the whole
        // amended committee and the "took effect" pole is about governance rather than
        // about a missing key.
        let mut roster = members.clone();
        roster.push(d.clone());
        let (_tmp, state) = committed_state_for(&roster).await;

        let handle = test_handle_with_committee(eds[0], eds.clone()).await;
        let quorum = dregg_blocklace::supermajority_threshold(members.len());
        assert_eq!(
            quorum, 3,
            "n=3 supermajority is 3 — the fixture's quorum arithmetic"
        );

        // Round 1: A proposes Join(D). Round 2: B approves. Later rounds are Acks that
        // super-ratify the wave carrying them. C's approval is cast in PHASE 3.
        let (lace, ids) = {
            // Two passes: the Approve payload must name the Join block's id, which is
            // only known after the Join block exists. Build the Join-only lace first to
            // learn the id, then rebuild the whole lace with both payloads.
            let (probe, probe_ids) = cross_linked_lace_with(
                &members,
                quorum,
                2,
                &[(
                    1,
                    0,
                    Payload::MembershipVote {
                        action: MembershipAction::Join {
                            node_id: ed_d,
                            ml_dsa_pubkey: dregg_blocklace::pq::MlDsaPublicKey(
                                [0u8; dregg_blocklace::pq::PK_LEN],
                            ),
                        },
                    },
                )],
            );
            let _ = probe;
            let join_id = probe_ids[&(1, 0)];
            cross_linked_lace_with(
                &members,
                quorum,
                6,
                &[
                    (
                        1,
                        0,
                        Payload::MembershipVote {
                            action: MembershipAction::Join {
                                node_id: ed_d,
                                ml_dsa_pubkey: dregg_blocklace::pq::MlDsaPublicKey(
                                    [0u8; dregg_blocklace::pq::PK_LEN],
                                ),
                            },
                        },
                    ),
                    (
                        2,
                        1,
                        Payload::MembershipVote {
                            action: MembershipAction::Approve {
                                proposal_block: join_id,
                            },
                        },
                    ),
                ],
            )
        };
        let join_block = ids[&(1, 0)];
        *handle.lace.write().await = lace;

        // ── ANTI-VACUITY 1: D is NOT a member, and the stranger is NOT a member.
        {
            let c = handle.constitution.read().await;
            assert!(
                !c.current.is_participant(&ed_d),
                "D must start outside the committee"
            );
            assert!(
                !c.current.is_participant(&ed_stranger),
                "the stranger must start outside the committee — else PHASE 2 refuses nothing"
            );
            assert_eq!(c.current.participant_count(), 3);
            assert_eq!(c.threshold(), 3);
            assert_eq!(c.version(), 0);
        }

        // ── ANTI-VACUITY 2 (THE WOUND, EXECUTED — no mutation required). Replay the
        //    SAME two votes into a scratch manager over the SAME committee using the
        //    HYBRID ids the shipped code passed. Zero approvals. This is the permanent
        //    in-tree witness that the identity space is load-bearing: if the two spaces
        //    ever coincided, this assertion would fail and the test below would be
        //    asserting nothing.
        {
            use dregg_blocklace::constitution::{
                Constitution, ConstitutionManager, MembershipProposal, MembershipVote,
            };
            let mut scratch = ConstitutionManager::new(Constitution::new(eds.clone(), 60_000));
            scratch.submit_proposal(
                join_block,
                MembershipProposal::Join {
                    node_key: ed_d,
                    justification: vec![],
                },
            );
            let v = MembershipVote {
                proposal_block: join_block,
                approve: true,
            };
            scratch.submit_vote(&v, Block::hybrid_id(&members[0]));
            scratch.submit_vote(&v, Block::hybrid_id(&members[1]));
            assert_eq!(
                scratch.votes.approval_count(&join_block),
                0,
                "the HYBRID id must be refused by `is_participant` over an ed25519-keyed \
                 committee — this is the wound the live path shipped. A non-zero count here \
                 means the two identity spaces coincide in this fixture and the test below \
                 proves nothing."
            );
        }

        // ── PHASE 1: THE REAL POLL, over the REAL handle, then the executor's own
        //    dispatch loop — the exact call `poll_finalized_blocks` feeds the executor.
        let finalized = handle.poll_finalized_blocks(&state).await;
        let membership: Vec<(BlockId, [u8; 32], MembershipAction)> = finalized
            .iter()
            .filter_map(|b| match b {
                FinalizedBlock::Membership {
                    block_id,
                    creator_ed25519,
                    action,
                } => Some((*block_id, *creator_ed25519, action.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(
            membership.len(),
            2,
            "both the Join proposal and B's Approve must reach finality — else there is no \
             vote for the constitution to count. Finalized {} block(s) total.",
            finalized.len()
        );
        assert!(
            matches!(membership[0].2, MembershipAction::Join { .. }),
            "the proposal must be ordered BEFORE the vote that references it — got {:?}",
            membership[0].2
        );
        for (block_id, creator_ed25519, action) in &membership {
            execute_finalized_membership(&state, &handle, *block_id, *creator_ed25519, action)
                .await;
        }

        let snap = handle.membership_snapshot().await;
        let status = snap
            .proposals
            .iter()
            .find(|p| p.proposal_block == join_block)
            .expect("the Join proposal is registered on the live node");
        assert_eq!(
            status.approvals, 2,
            "TWO CURRENT PARTICIPANTS' VOTES MUST COUNT (A's implicit proposer self-vote and \
             B's Approve). This is the assertion the dead path could never satisfy: with the \
             hybrid id the count was 0 and no quorum was reachable at any committee size."
        );
        assert!(
            !status.applied,
            "2 of a required 3 must NOT apply — a vote counting is not a vote passing"
        );
        assert_eq!(status.required, 3);
        assert!(
            !handle
                .constitution
                .read()
                .await
                .current
                .is_participant(&ed_d),
            "D must not be admitted under quorum"
        );

        // ── PHASE 2: THE REFUSAL POLE. A stranger casts the identical Approve through
        //    the identical entry point. The tally must not move.
        execute_finalized_membership(
            &state,
            &handle,
            BlockId([0xEE; 32]),
            ed_stranger,
            &MembershipAction::Approve {
                proposal_block: join_block,
            },
        )
        .await;
        let snap = handle.membership_snapshot().await;
        let status = snap
            .proposals
            .iter()
            .find(|p| p.proposal_block == join_block)
            .expect("the proposal is still registered");
        assert_eq!(
            status.approvals, 2,
            "a NON-PARTICIPANT's approval must be refused by `Constitution::is_participant` — \
             the tally must be unchanged at 2"
        );
        assert!(
            !status.applied,
            "a stranger's vote must not carry a proposal to quorum"
        );
        assert!(
            !handle
                .constitution
                .read()
                .await
                .current
                .is_participant(&ed_d),
            "D must still not be admitted after a stranger's vote"
        );

        // ── PHASE 3: C, the third CURRENT participant, approves. Quorum → the proposal
        //    APPLIES and TAKES EFFECT.
        execute_finalized_membership(
            &state,
            &handle,
            BlockId([0xCC; 32]),
            eds[2],
            &MembershipAction::Approve {
                proposal_block: join_block,
            },
        )
        .await;

        {
            let c = handle.constitution.read().await;
            assert!(
                c.current.is_participant(&ed_d),
                "QUORUM REACHED AND THE PROPOSAL MUST TAKE EFFECT: D is not in the committee. \
                 Participants: {}",
                c.current.participant_count()
            );
            assert_eq!(c.current.participant_count(), 4, "the committee grew to 4");
            assert_eq!(c.version(), 1, "the constitution version advanced");
            assert_eq!(
                c.threshold(),
                dregg_blocklace::supermajority_threshold(4),
                "the threshold recomputed for the amended committee"
            );
            assert!(
                !c.current.is_participant(&ed_stranger),
                "the stranger must STILL not be a member — nothing about quorum admits them"
            );
        }
        // THE LIVE EFFECT, not just the record: `apply_passed_proposal` →
        // `apply_committee_change` advanced the finalization-vote committee, so D's
        // signed finalization votes count from here.
        {
            let votes = handle.votes.read().await;
            assert!(
                votes.is_committee_member(&ed_d),
                "the LIVE consensus committee must have advanced — D's finalization votes \
                 must count. A constitution that amends without advancing the committee is a \
                 record, not an effect."
            );
            assert!(
                !votes.is_committee_member(&ed_stranger),
                "the stranger must not have been admitted to the live committee"
            );
            assert_eq!(
                votes.quorum_threshold(),
                dregg_blocklace::supermajority_threshold(4),
                "the live quorum threshold followed the amended committee"
            );
        }
    }

    /// The solo enrolled-creator set, in quadrants — so a future widening is a visible diff and not
    /// a quiet boolean flip. Invariant/gate sweeps cannot evaluate this predicate; these four lines
    /// are the complement that catches a `solo_enrolled_creators -> everything` mutant.
    #[test]
    fn solo_enrolled_creators_quadrants() {
        let self_ed = [0x01u8; 32];
        let self_hybrid = [0x11u8; 32];
        let peer_ed = [0x02u8; 32];
        let peer_hybrid = [0x22u8; 32];

        // COLD START: we are the sole admitted participant and NOTHING is committed. The derived
        // self hybrid is the whole enrolled set — this is the case that keeps bootstrap alive.
        let cold = solo_enrolled_creators(&[], &[self_ed], &self_ed, self_hybrid);
        assert_eq!(cold.len(), 1);
        assert!(cold.contains(&self_hybrid));

        // COMMITTED: the projection carries us; the derived id is the SAME value, so the set does
        // not grow. (The local derivation completes the projection, it does not widen it.)
        let committed = solo_enrolled_creators(&[self_hybrid], &[self_ed], &self_ed, self_hybrid);
        assert_eq!(committed, cold);

        // OBSERVER: the sole admitted participant is someone else and we are not a member. Our own
        // hybrid id is NOT admitted — this is the n=1 face of the rule `tauOrder`'s `enrolledId`
        // has enforced at n>1 since `c6f00c228`.
        let observer = solo_enrolled_creators(&[peer_hybrid], &[peer_ed], &self_ed, self_hybrid);
        assert_eq!(observer.len(), 1);
        assert!(observer.contains(&peer_hybrid));
        assert!(!observer.contains(&self_hybrid));

        // NOTHING RESOLVABLE: not a member, and the sole admitted member has no committed key.
        // Empty ⇒ the caller finalizes nothing and warns (halt, never finalize-everything).
        assert!(solo_enrolled_creators(&[], &[peer_ed], &self_ed, self_hybrid).is_empty());
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
            None,
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
        let forest = dregg_coord::AtomicForest::new(
            vec![node_a, node_b],
            call_forest,
            vec![],
            cell_a,
            0,
            None,
        );
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

    // ── THE GOSSIP BIND IS FAIL-CLOSED ────────────────────────────────────────
    //
    // Until 2026-07-26 a node whose gossip port was taken logged
    //
    //   ERROR failed to create PeerNode for blocklace gossip
    //         error=bind error: Address already in use (os error 48)
    //
    // and kept going: `lib.rs::run` matches `if let Some(handle) = …` with no
    // `else`, so it bound HTTP anyway and served forever with
    // `consensus_live:false`, `block_count:0` — accepting every turn, applying
    // none, and answering `{"success":true}` to faucet grants that never landed.
    // Two nodes from the same binary, one of which had grabbed 9420 first, behaved
    // oppositely with nothing surfaced to the operator.
    //
    // These two tests are the pair: the first proves the refusal FIRES on a taken
    // port, the second proves it does not fire when the port is free (a gate that
    // always refuses is as useless as one that never does).

    /// A `NodeState` on a throwaway data dir, unlocked, with nothing else running.
    async fn bare_node_state() -> (crate::state::NodeState, tempfile::TempDir) {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::new(tmp.path(), vec![]).expect("build NodeState");
        state.write().await.unlocked = true;
        (state, tmp)
    }

    /// Bind a UDP socket to an OS-chosen port and keep it. The returned port is
    /// therefore guaranteed occupied for as long as the socket lives — no
    /// hardcoded port number, no flake if something else owns 9420.
    fn hold_a_udp_port() -> (std::net::UdpSocket, u16) {
        let sock = std::net::UdpSocket::bind("0.0.0.0:0").expect("bind an ephemeral UDP port");
        let port = sock.local_addr().expect("local_addr").port();
        (sock, port)
    }

    /// Proposal-neutral observation and ordinary joining share every startup
    /// path except this explicit policy.  Exercise both poles against real
    /// blocklaces: the observer must author no Join block after the normal
    /// proposal delay, while the legacy/default policy must still author one.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn follow_only_never_emits_join_while_normal_policy_still_does() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let committee = [ed25519_dalek::SigningKey::from_bytes(&[0x91; 32])];
        let (follow_tmp, follow_state) = committed_state_for(&committee).await;
        let (normal_tmp, normal_state) = committed_state_for(&committee).await;

        let (follow, normal) = tokio::join!(
            run_blocklace_sync_with_membership_policy(
                follow_state,
                0,
                false,
                MembershipProposalPolicy::FollowOnly,
                100,
                10_000,
                0,
                0,
                0,
                None,
                dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
            ),
            run_blocklace_sync_with_membership_policy(
                normal_state,
                0,
                false,
                MembershipProposalPolicy::ProposeIfNonMember,
                100,
                10_000,
                0,
                0,
                0,
                None,
                dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
            )
        );
        let follow = follow.expect("follow-only blocklace starts");
        let normal = normal.expect("normal blocklace starts");

        // The production proposal task waits two seconds for gossip. Wait past
        // that same boundary so a scheduler delay cannot make the positive pole
        // vacuous.
        tokio::time::sleep(Duration::from_millis(2_500)).await;
        let join_count = |blocks: Vec<Block>| {
            blocks
                .iter()
                .filter(|block| {
                    matches!(
                        block.payload,
                        Payload::MembershipVote {
                            action: MembershipAction::Join { .. }
                        }
                    )
                })
                .count()
        };
        assert_eq!(
            join_count(follow.lace.read().await.all_blocks()),
            0,
            "follow-only history sync authored a Join proposal"
        );
        assert_eq!(
            join_count(normal.lace.read().await.all_blocks()),
            1,
            "the ordinary join policy no longer auto-proposes membership"
        );

        drop((follow_tmp, normal_tmp));
    }

    // The expected message names the BIND specifically, not just "refusing to
    // start": every other early exit in this function now panics too, so a bare
    // "refusing to start" match would pass on a fixture that never reached the bind
    // at all. The companion test below is the other half of that guard — it proves
    // this fixture DOES reach the bind and get past it when the port is free.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    #[should_panic(expected = "could not bind the gossip endpoint")]
    async fn a_node_that_cannot_bind_its_gossip_port_refuses_to_start() {
        let (_held, taken_port) = hold_a_udp_port();
        let (state, _tmp) = bare_node_state().await;

        // The bind MUST fail (the socket above still holds `taken_port`), and the
        // failure must be terminal. If this ever returns instead of panicking, the
        // fail-open is back: the caller would go on to serve HTTP with no consensus.
        let _ = run_blocklace_sync_with_policy(
            state,
            taken_port,
            true,
            100,
            10_000,
            50,
            2_000,
            0,
            None,
            dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
        )
        .await;
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_node_whose_gossip_port_is_free_still_starts() {
        // Take a port and immediately release it, so we hand the node a port that is
        // free but was chosen the same way as the test above — the ONLY difference
        // between the two tests is whether the holder is still alive.
        let taken_port = {
            let (sock, port) = hold_a_udp_port();
            drop(sock);
            port
        };
        let (state, _tmp) = bare_node_state().await;

        let handle = run_blocklace_sync_with_policy(
            state,
            taken_port,
            true,
            100,
            10_000,
            50,
            2_000,
            0,
            None,
            dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
        )
        .await;
        assert!(
            handle.is_some(),
            "a free gossip port must still bring consensus up — otherwise the refusal \
             above is unconditional and proves nothing"
        );
    }

    // ─── Bounded pull responses (the fan-out fix, 2026-08-08) ────────────────

    /// A lace with one enrolled creator and a `depth`-block chain; returns
    /// (holder lace, creator key, blocks in causal order).
    fn deep_chain_lace(depth: usize) -> (Blocklace, ed25519_dalek::SigningKey, Vec<Block>) {
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x51u8; 32]);
        let mut lace = dregg_blocklace::finality::Blocklace::new_simple(sk.clone());
        let mut blocks = Vec::with_capacity(depth);
        for _ in 0..depth {
            blocks.push(lace.add_block(Payload::Ack));
        }
        (lace, sk, blocks)
    }

    /// The reply to a Pull is BOUNDED and NEAREST-FIRST: requesting the tip of a
    /// chain much deeper than the cap returns exactly
    /// [`MAX_PULL_RESPONSE_BLOCKS`] blocks — the tip plus its nearest ancestry —
    /// never the from-genesis dump the pre-fix reply shipped.
    #[test]
    fn pull_response_is_bounded_and_nearest_first() {
        let depth = MAX_PULL_RESPONSE_BLOCKS + 300;
        let (lace, _sk, blocks) = deep_chain_lace(depth);
        let tip = blocks.last().unwrap().id();

        let reply = collect_pull_response(&lace, &[tip]);
        assert_eq!(
            reply.len(),
            MAX_PULL_RESPONSE_BLOCKS,
            "a deep-history pull reply must be exactly the cap, not the whole DAG"
        );
        assert!(
            reply.iter().any(|b| b.id() == tip),
            "the requested block itself is always in the reply"
        );
        // Nearest-first: the window is the TOP of the chain (highest seqs).
        let min_seq = reply.iter().map(|b| b.seq).min().unwrap();
        let max_seq = reply.iter().map(|b| b.seq).max().unwrap();
        let tip_seq = blocks.last().unwrap().seq;
        assert_eq!(max_seq, tip_seq, "window ends at the requested tip");
        assert_eq!(
            (max_seq - min_seq) as usize + 1,
            MAX_PULL_RESPONSE_BLOCKS,
            "window is contiguous nearest ancestry of the requested tip"
        );
        // Causal-friendly order (ascending seq for a single creator).
        assert!(
            reply.windows(2).all(|w| w[0].seq <= w[1].seq),
            "reply is sorted parents-before-children"
        );

        // An id we do not hold yields nothing (the requester's rotating retry
        // asks someone else) — never an error, never a stall.
        let unknown = BlockId([0xEE; 32]);
        assert!(collect_pull_response(&lace, &[unknown]).is_empty());
    }

    /// LIVENESS FALSIFIER for the bound: a joiner that is ARBITRARILY far behind
    /// still converges through repeated bounded windows — each reply advances the
    /// orphan buffer's unmet roots strictly downward, and ceil(depth/window)
    /// round trips reconstruct the whole chain. This is the property that makes
    /// bounding the reply safe (Mysticeti-style iterative fetch), and it is the
    /// test that would go red if the window could strand a deep gap.
    #[test]
    fn bounded_pull_windows_converge_a_deep_joiner() {
        let depth = 3 * MAX_PULL_RESPONSE_BLOCKS + 57; // several windows + remainder
        let (holder, sk, blocks) = deep_chain_lace(depth);
        let tip = blocks.last().unwrap().id();

        let mut joiner = dregg_blocklace::finality::Blocklace::new_simple(
            ed25519_dalek::SigningKey::from_bytes(&[0x52u8; 32]),
        );
        joiner.enroll_pq(Block::hybrid_id(&sk), Block::pq_public_key(&sk));
        let mut buf = crate::catchup::OrphanBuffer::new();

        // Round 1 requests the tip (as the reactive path would); every later
        // round requests exactly the still-unmet roots (as `catchup_tick` does).
        let mut request: Vec<BlockId> = vec![tip];
        let mut rounds = 0usize;
        loop {
            rounds += 1;
            assert!(
                rounds <= depth / MAX_PULL_RESPONSE_BLOCKS + 2,
                "iterative windows must converge in ~depth/window round trips"
            );
            let reply = collect_pull_response(&holder, &request);
            assert!(
                reply.len() <= MAX_PULL_RESPONSE_BLOCKS,
                "every reply respects the bound"
            );
            let outcome = crate::catchup::apply_with_buffering(&mut joiner, &mut buf, reply);
            if outcome.pull_roots.is_empty() {
                break;
            }
            request = outcome.pull_roots;
        }
        assert!(buf.is_empty(), "no orphan remains once the gap closes");
        let holder_ids: std::collections::HashSet<BlockId> =
            holder.iter().map(|(id, _)| *id).collect();
        let joiner_ids: std::collections::HashSet<BlockId> =
            joiner.iter().map(|(id, _)| *id).collect();
        assert_eq!(
            holder_ids, joiner_ids,
            "the joiner reconstructs the holder's exact keyset through bounded windows"
        );
    }

    // ─── Loss-injection measurement harness (SH++ §8.3 scenario, ours) ───────
    //
    // The measurement that had never existed: OUR dissemination + catch-up
    // stack, over real QUIC loopback gossip, with egress message drops injected
    // on one committee member (`GossipNetwork::set_egress_drop_permille`) — the
    // Shoal++ §8.3 shape (they drop 1% of egress on 5/100 nodes at the network
    // layer; we drop whole gossip frames on 1/4 nodes, because QUIC retransmits
    // packet-level loss, so the frame is our smallest droppable egress unit).
    //
    // Everything on the receive path is the PRODUCTION code: the real
    // `drain_and_schedule_blocklace_batch` funnel scheduler, the real
    // `handle_push`/`handle_pull`/`handle_frontier`, the real orphan buffer and
    // backoffs, and the real periodic drivers (`send_frontier`, `catchup_tick`)
    // at production-shaped cadences. The harness supplies only what sits ABOVE
    // the layer under test: block production (one `Payload::Ack` block per node
    // per tick, exactly the `Push` shape `push_new_blocks` broadcasts) and the
    // metric samplers.
    //
    // Run explicitly (ignored by default; ~90 s per scenario):
    //   DREGG_MEASURE_BASELINE=1 cargo test -p dregg-node --release \
    //     loss_sync_measurement -- --ignored --nocapture   # pre-fix behavior
    //   cargo test -p dregg-node --release \
    //     loss_sync_measurement -- --ignored --nocapture   # fixed behavior
    // Optional: DREGG_MEASURE_DROP_PERMILLE (default 100 = 10%),
    //           DREGG_MEASURE_PRODUCE_SECS (default 45).

    struct WireCounts {
        push_msgs: std::sync::atomic::AtomicUsize,
        pull_msgs: std::sync::atomic::AtomicUsize,
        pullresp_msgs: std::sync::atomic::AtomicUsize,
        frontier_msgs: std::sync::atomic::AtomicUsize,
        blocks_rx: std::sync::atomic::AtomicUsize,
        dup_blocks_rx: std::sync::atomic::AtomicUsize,
    }

    impl WireCounts {
        fn new() -> Self {
            use std::sync::atomic::AtomicUsize;
            Self {
                push_msgs: AtomicUsize::new(0),
                pull_msgs: AtomicUsize::new(0),
                pullresp_msgs: AtomicUsize::new(0),
                frontier_msgs: AtomicUsize::new(0),
                blocks_rx: AtomicUsize::new(0),
                dup_blocks_rx: AtomicUsize::new(0),
            }
        }
    }

    struct MeasuredNode {
        handle: BlocklaceHandle,
        state: NodeState,
        counts: Arc<WireCounts>,
        _tmp: tempfile::TempDir,
    }

    /// Boot an n-node federation over real QUIC loopback: meshed gossip with
    /// registered envelope keys, enrolled hybrid rosters, production funnel +
    /// periodic drivers. Returns the nodes; every spawned task lives until the
    /// test process ends (tests are one process per #[tokio::test]).
    async fn boot_measurement_committee(
        n: usize,
        member_keys: &[ed25519_dalek::SigningKey],
    ) -> Vec<MeasuredNode> {
        use std::sync::atomic::Ordering;

        // Gossip transport identities (envelope signing) — one per node, all
        // registered in every node's peer_keys, as the production boot builds
        // from `known_federation_keys`.
        let mut gossip_keys = Vec::new();
        let mut peer_keys: HashMap<NodeId, dregg_types::PublicKey> = HashMap::new();
        for _ in 0..n {
            let (sk, pk) = dregg_types::generate_keypair();
            peer_keys.insert(*blake3::hash(pk.as_bytes()).as_bytes(), pk);
            gossip_keys.push((sk, pk));
        }

        // Endpoints first (all addresses known before any join dials).
        let mut peer_nodes = Vec::new();
        for _ in 0..n {
            peer_nodes.push(PeerNode::new(PeerNodeConfig::default()).await.unwrap());
        }
        let addrs: Vec<SocketAddr> = peer_nodes.iter().map(|p| p.local_addr()).collect();

        let participants: Vec<[u8; 32]> = member_keys.iter().map(Block::hybrid_id).collect();

        let mut out = Vec::new();
        for i in 0..n {
            let (gsk, gpk) = &gossip_keys[i];
            let node_id: NodeId = *blake3::hash(gpk.as_bytes()).as_bytes();
            let gossip = Arc::new(GossipNetwork::new(
                peer_nodes[i].endpoint().clone(),
                node_id,
                gsk.clone(),
                peer_keys.clone(),
            ));
            let others: Vec<SocketAddr> = addrs
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, a)| *a)
                .collect();
            let topic = gossip.join_topic(TOPIC_BLOCKLACE, &others).await.unwrap();
            let mut stream = gossip.subscribe(&topic).await.unwrap();

            let handle = test_handle_with_transport(
                member_keys[i].verifying_key().to_bytes(),
                member_keys[i].clone(),
                participants.clone(),
                gossip,
                topic,
            )
            .await;
            // Enroll the whole committee's ML-DSA keys so the pinned wire
            // ingest accepts every member's hybrid-signed blocks.
            {
                let mut lace = handle.lace.write().await;
                for k in member_keys {
                    lace.enroll_pq(Block::hybrid_id(k), Block::pq_public_key(k));
                }
            }
            let (tmp, state) = committed_state_for(member_keys).await;
            let counts = Arc::new(WireCounts::new());

            // The funnel: the production drain-and-schedule loop, verbatim in
            // shape (recv → drain backlog → schedule), with a metrics pass over
            // the borrowed batch before dispatch.
            {
                let h = handle.clone();
                let st = state.clone();
                let c = counts.clone();
                tokio::spawn(async move {
                    loop {
                        let Some(first) = stream.recv().await else {
                            break;
                        };
                        match first {
                            GossipEvent::Message { .. } => {
                                let mut batch = vec![first];
                                while batch.len() < MAX_GOSSIP_DRAIN_BATCH {
                                    match stream.try_recv() {
                                        Some(ev) => batch.push(ev),
                                        None => break,
                                    }
                                }
                                for ev in &batch {
                                    let GossipEvent::Message { message, .. } = ev else {
                                        continue;
                                    };
                                    let PeerMessage::PublishTurn { turn_data, .. } = message else {
                                        continue;
                                    };
                                    let Ok(m) =
                                        postcard::from_bytes::<BlocklaceGossipMessage>(turn_data)
                                    else {
                                        continue;
                                    };
                                    let counted_blocks = match &m {
                                        BlocklaceGossipMessage::Push { blocks, .. } => {
                                            c.push_msgs.fetch_add(1, Ordering::Relaxed);
                                            Some(blocks)
                                        }
                                        BlocklaceGossipMessage::PullResponse { blocks, .. } => {
                                            c.pullresp_msgs.fetch_add(1, Ordering::Relaxed);
                                            Some(blocks)
                                        }
                                        BlocklaceGossipMessage::Pull { .. } => {
                                            c.pull_msgs.fetch_add(1, Ordering::Relaxed);
                                            None
                                        }
                                        BlocklaceGossipMessage::Frontier { .. } => {
                                            c.frontier_msgs.fetch_add(1, Ordering::Relaxed);
                                            None
                                        }
                                        _ => None,
                                    };
                                    if let Some(blocks) = counted_blocks {
                                        c.blocks_rx.fetch_add(blocks.len(), Ordering::Relaxed);
                                        let lace = h.lace.read().await;
                                        let dups = blocks
                                            .iter()
                                            .filter(|b| lace.contains(&b.id()))
                                            .count();
                                        c.dup_blocks_rx.fetch_add(dups, Ordering::Relaxed);
                                    }
                                }
                                drain_and_schedule_blocklace_batch(&h, &st, batch).await;
                            }
                            GossipEvent::PeerJoined(_) => {
                                h.send_frontier().await;
                            }
                            GossipEvent::PeerLeft(_) => {}
                        }
                    }
                });
            }
            // Periodic drivers at production-shaped cadences: a frontier per
            // second (the cadence tick announces one per tick in production)
            // and a catch-up sweep every 2 s (the production floor).
            {
                let h = handle.clone();
                tokio::spawn(async move {
                    let mut t = tokio::time::interval(Duration::from_millis(1_000));
                    t.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                    loop {
                        t.tick().await;
                        h.send_frontier().await;
                    }
                });
                let h = handle.clone();
                tokio::spawn(async move {
                    let mut t = tokio::time::interval(Duration::from_millis(2_000));
                    t.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                    loop {
                        t.tick().await;
                        h.catchup_tick().await;
                    }
                });
            }

            out.push(MeasuredNode {
                handle,
                state,
                counts,
                _tmp: tmp,
            });
        }
        out
    }

    fn percentile(sorted_ms: &[u128], p: f64) -> u128 {
        if sorted_ms.is_empty() {
            return 0;
        }
        let idx = ((sorted_ms.len() as f64 - 1.0) * p).round() as usize;
        sorted_ms[idx]
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 8)]
    #[ignore = "measurement harness — run explicitly with --ignored --nocapture (~90 s)"]
    async fn loss_sync_measurement() {
        use std::sync::atomic::Ordering;
        // ⚠ `0eccd772d` left this harness naming `Instant` with no `Instant` in
        // scope, so `dregg-node`'s ENTIRE lib-test binary failed to compile —
        // every unit test in the crate, for every lane, not just this one.
        use std::time::Instant;

        let baseline = std::env::var_os("DREGG_MEASURE_BASELINE").is_some();
        SYNC_BASELINE_FOR_MEASUREMENT.store(baseline, Ordering::Relaxed);
        let drop_permille: u16 = std::env::var("DREGG_MEASURE_DROP_PERMILLE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(100);
        let produce_secs: u64 = std::env::var("DREGG_MEASURE_PRODUCE_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(45);

        const N: usize = 4;
        const PRODUCE_EVERY: Duration = Duration::from_millis(400);
        let member_keys: Vec<ed25519_dalek::SigningKey> = (0..N as u8)
            .map(|i| ed25519_dalek::SigningKey::from_bytes(&[0x40 + i; 32]))
            .collect();
        let nodes = boot_measurement_committee(N, &member_keys).await;

        // produced block id -> (produced_at, seen_at per node)
        type SeenMap = HashMap<BlockId, (Instant, [Option<Instant>; N])>;
        let produced: Arc<std::sync::Mutex<SeenMap>> =
            Arc::new(std::sync::Mutex::new(HashMap::new()));

        // Sampler: 25 ms resolution on "node j holds block b".
        {
            let produced = produced.clone();
            let laces: Vec<_> = nodes.iter().map(|n| n.handle.lace.clone()).collect();
            tokio::spawn(async move {
                let mut t = tokio::time::interval(Duration::from_millis(25));
                t.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                loop {
                    t.tick().await;
                    let pending: Vec<(BlockId, [bool; N])> = {
                        let m = produced.lock().unwrap();
                        m.iter()
                            .filter(|(_, (_, seen))| seen.iter().any(Option::is_none))
                            .map(|(id, (_, seen))| {
                                let mut mask = [false; N];
                                for (j, s) in seen.iter().enumerate() {
                                    mask[j] = s.is_none();
                                }
                                (*id, mask)
                            })
                            .collect()
                    };
                    if pending.is_empty() {
                        continue;
                    }
                    let now = Instant::now();
                    for j in 0..N {
                        let ids: Vec<BlockId> = pending
                            .iter()
                            .filter(|(_, mask)| mask[j])
                            .map(|(id, _)| *id)
                            .collect();
                        if ids.is_empty() {
                            continue;
                        }
                        let lace = laces[j].read().await;
                        let held: Vec<BlockId> =
                            ids.into_iter().filter(|id| lace.contains(id)).collect();
                        drop(lace);
                        if held.is_empty() {
                            continue;
                        }
                        let mut m = produced.lock().unwrap();
                        for id in held {
                            if let Some((_, seen)) = m.get_mut(&id) {
                                seen[j] = Some(now);
                            }
                        }
                    }
                }
            });
        }

        // ─── Phase 1: 5 s warmup, no loss (mesh + first blocks) ──────────────
        let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
        for (i, node) in nodes.iter().enumerate() {
            let h = node.handle.clone();
            let produced = produced.clone();
            let stop = stop.clone();
            tokio::spawn(async move {
                let mut t = tokio::time::interval(PRODUCE_EVERY);
                t.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                loop {
                    t.tick().await;
                    if stop.load(Ordering::Relaxed) {
                        break;
                    }
                    let block = {
                        let mut lace = h.lace.write().await;
                        lace.add_block(Payload::Ack)
                    };
                    {
                        let mut m = produced.lock().unwrap();
                        let mut seen = [None; N];
                        seen[i] = Some(Instant::now());
                        m.insert(block.id(), (Instant::now(), seen));
                    }
                    // Exactly the eager one-hop Push `push_new_blocks` sends.
                    h.broadcast_gossip_message(&BlocklaceGossipMessage::Push {
                        blocks: vec![block],
                        nonce: gossip_send_nonce(),
                    })
                    .await;
                }
            });
        }
        tokio::time::sleep(Duration::from_secs(5)).await;

        // ─── Phase 2: loss on node 0's egress; produce under loss ────────────
        nodes[0]
            .handle
            .gossip
            .set_egress_drop_permille(drop_permille)
            .await;
        let loss_started = Instant::now();

        // POLE PROBE at +10 s: a signed block from an enrolled creator citing a
        // predecessor NOBODY holds — the "peer that cannot supply a block"
        // case. It must be staged (not admitted), must trigger no stall, and
        // its fetches must fail quietly against every rotating target.
        let fabricated = Block::new(
            &member_keys[2],
            9_999,
            Payload::Data(b"unresolvable-orphan".to_vec()),
            vec![BlockId([0xFA; 32])],
        );
        let fabricated_id = fabricated.id();
        {
            let h = nodes[1].handle.clone();
            let st = nodes[1].state.clone();
            let fab = fabricated.clone();
            tokio::spawn(async move {
                tokio::time::sleep(Duration::from_secs(10)).await;
                let from: SocketAddr = "127.0.0.1:9".parse().unwrap();
                handle_push(&h, &st, from, vec![fab]).await;
            });
        }

        tokio::time::sleep(Duration::from_secs(produce_secs)).await;
        stop.store(true, Ordering::Relaxed);

        // ─── Phase 3: drain (loss still on — recovery must work under it) ────
        tokio::time::sleep(Duration::from_secs(25)).await;

        // ─── Verdicts ────────────────────────────────────────────────────────
        let produced_final = produced.lock().unwrap().clone();
        let mut all_ms: Vec<u128> = Vec::new(); // produced -> held by ALL nodes
        let mut node0_ms: Vec<u128> = Vec::new(); // produced -> held by the LOSSY node
        let mut unconverged = 0usize;
        for (_, (t0, seen)) in produced_final.iter() {
            match seen.iter().copied().collect::<Option<Vec<Instant>>>() {
                Some(times) => {
                    let last = times.iter().max().unwrap();
                    all_ms.push(last.duration_since(*t0).as_millis());
                }
                None => unconverged += 1,
            }
            if let Some(t) = seen[0] {
                node0_ms.push(t.duration_since(*t0).as_millis());
            }
        }
        all_ms.sort_unstable();
        node0_ms.sort_unstable();

        println!("\n══ loss_sync_measurement ══");
        println!(
            "config: mode={} n={} drop=node0 egress {}‰ produce={}s cadence={}ms loss_phase={}s",
            if baseline {
                "BASELINE(pre-fix)"
            } else {
                "FIXED"
            },
            N,
            drop_permille,
            produce_secs,
            PRODUCE_EVERY.as_millis(),
            loss_started.elapsed().as_secs(),
        );
        println!(
            "blocks produced: {} | unconverged after {}s drain: {}",
            produced_final.len(),
            25,
            unconverged
        );
        println!(
            "dissemination latency ms (all 4 hold): p50={} p95={} max={}",
            percentile(&all_ms, 0.50),
            percentile(&all_ms, 0.95),
            percentile(&all_ms, 1.0),
        );
        println!(
            "lossy-node catch-up latency ms (node0 holds): p50={} p95={} max={}",
            percentile(&node0_ms, 0.50),
            percentile(&node0_ms, 0.95),
            percentile(&node0_ms, 1.0),
        );
        for (j, node) in nodes.iter().enumerate() {
            let c = &node.counts;
            println!(
                "node{j} rx: push={} pull={} pullresp={} frontier={} blocks={} dup_blocks={}",
                c.push_msgs.load(Ordering::Relaxed),
                c.pull_msgs.load(Ordering::Relaxed),
                c.pullresp_msgs.load(Ordering::Relaxed),
                c.frontier_msgs.load(Ordering::Relaxed),
                c.blocks_rx.load(Ordering::Relaxed),
                c.dup_blocks_rx.load(Ordering::Relaxed),
            );
        }

        // POLE 2 (no unclosed admission, no stall): the fabricated orphan is in
        // NO lace, node 1 stayed live (its blocks converged), and the orphan is
        // still merely staged.
        for (j, node) in nodes.iter().enumerate() {
            let lace = node.handle.lace.read().await;
            assert!(
                !lace.contains(&fabricated_id),
                "node{j} must never admit a block whose predecessor nobody can supply"
            );
        }
        assert!(
            nodes[1]
                .handle
                .orphans
                .read()
                .await
                .contains(&fabricated_id),
            "the unresolvable orphan is STAGED at its receiver (bounded, TTL-swept later) — \
             not admitted, not dropped-silently"
        );

        // CONVERGENCE: every produced block reached every node despite the loss.
        assert_eq!(
            unconverged, 0,
            "all produced blocks must converge to all nodes within the drain window"
        );
        let key0: std::collections::HashSet<BlockId> = {
            let lace = nodes[0].handle.lace.read().await;
            lace.iter().map(|(id, _)| *id).collect()
        };
        for (j, node) in nodes.iter().enumerate().skip(1) {
            let keys: std::collections::HashSet<BlockId> = {
                let lace = node.handle.lace.read().await;
                lace.iter().map(|(id, _)| *id).collect()
            };
            assert_eq!(
                key0, keys,
                "node0 and node{j} keysets must be identical after drain"
            );
        }
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
    let mut blocklace = match dregg_blocklace::finality::Blocklace::from_checkpoint(
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
    let consensus_time_policy = match consensus_time_policy_v1_from_env() {
        Ok(policy) => policy,
        Err(error) => {
            warn!(peer = %peer_url, error = %error, "checkpoint bootstrap lacks consensus-time-v1 deployment coordinate");
            return None;
        }
    };
    if let Err(error) = blocklace.restore_consensus_time_v1(consensus_time_policy) {
        warn!(
            peer = %peer_url,
            error = %error,
            "peer checkpoint is incompatible with the local consensus-time-v1 flag day"
        );
        return None;
    }

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

/// One registered membership proposal with its live tally, for the operator
/// surface. `applied` = the proposal already amended the constitution.
#[derive(Debug, Clone)]
pub struct MembershipProposalStatus {
    pub proposal_block: BlockId,
    pub proposal: MembershipProposal,
    pub approvals: usize,
    pub rejections: usize,
    pub required: usize,
    pub applied: bool,
}

/// The live membership picture (`BlocklaceHandle::membership_snapshot`).
#[derive(Debug, Clone)]
pub struct MembershipSnapshot {
    pub participants: Vec<[u8; 32]>,
    pub threshold: usize,
    pub version: u64,
    pub frozen: bool,
    pub self_key: [u8; 32],
    pub self_is_participant: bool,
    pub proposals: Vec<MembershipProposalStatus>,
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
///
/// ⚑ `creator_ed25519` IS THE ED25519 STRAND KEY, and that is load-bearing, not a
/// naming preference. `Constitution::participants` holds ed25519 keys —
/// `run_blocklace_sync_with_policy` seeds it from `signing_key.verifying_key()` /
/// `known_federation_keys`, `MembershipAction::Join` carries an ed25519 `node_id`,
/// and `apply_committee_change` consumes the amended set as ed25519 (it re-derives
/// each member's hybrid id for `enroll_pq` and hashes each key for the gossip
/// `NodeId`). `VoteTracker::record_vote` therefore gates on
/// `Constitution::is_participant(&voter)` in the ed25519 space.
///
/// This function used to be handed `Block::creator`, the HYBRID consensus id
/// `H(ed25519 ‖ ml_dsa)`. A hybrid id is a BLAKE3 commitment and is never equal to
/// any ed25519 member key, so `is_participant` refused unconditionally: **no
/// membership vote submitted through the live path had ever counted.** Joins,
/// leaves, threshold amendments and route amendments were all silently inert; the
/// pure twin `committee_replay::derive_from_lace` passed `block.ed25519` and was
/// right all along.
///
/// The two keyings do NOT need to agree, and unifying them on the hybrid id would
/// be WRONG: the projection is one-way. `project_committed_participants` maps
/// ed25519 → hybrid using committed state, but a hybrid id is a hash and cannot be
/// inverted, so a hybrid-keyed constitution could not produce the ed25519 keys
/// `apply_committee_change`, `pq_committee_for_participants` and the gossip mesh
/// all require. Governance is keyed by the strand; finality is keyed by the
/// projection of the strand.
async fn execute_finalized_membership(
    state: &NodeState,
    handle: &BlocklaceHandle,
    block_id: BlockId,
    creator_ed25519: [u8; 32],
    action: &MembershipAction,
) {
    match action {
        MembershipAction::Join {
            node_id,
            ml_dsa_pubkey,
        } => {
            // ⚑ COMMIT THE CANDIDATE'S POST-QUANTUM HALF, HERE, BEFORE ANYTHING
            // ELSE. This is ring 3 of the growth deadlock (module header): the
            // genesis roster was the only writer of the index-aligned
            // `known_federation_keys` / `known_federation_ml_dsa_keys` pair, so a
            // live-joined validator had no committed ML-DSA key,
            // `project_committed_participants` DROPPED it, and
            // `poll_finalized_blocks` FAILED CLOSED — a successful join would
            // have stopped finality on every node in the federation.
            //
            // The write is deterministic on every node because its input is the
            // RATIFIED block payload, seen identically at the same point in the
            // finalized order — never a node-local key view, which is what the
            // F-CO-1 projection comment forbids and would fork on.
            //
            // Done at proposal-registration time (not at apply time) so the key
            // is committed BEFORE `apply_passed_proposal` reads it back through
            // `pq_committee_for_participants`, including the n=1 case where the
            // proposal passes in the very next statement.
            {
                let mut s = state.write().await;
                let learned = s.learn_committee_member_hybrid_key(
                    node_id,
                    dregg_federation::frost::MlDsaPublicKey(ml_dsa_pubkey.0),
                );
                if !learned {
                    let hex: String = node_id[..4].iter().map(|b| format!("{b:02x}")).collect();
                    warn!(
                        candidate = %hex,
                        "the Join payload's ML-DSA key was NOT committed (hybrid unconfigured, or \
                         it disagrees with the key already committed for this member). If this \
                         proposal passes, the projection will drop the member and finality will \
                         halt."
                    );
                }
            }
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
            let passed = constitution.submit_vote(&self_vote, creator_ed25519);
            drop(constitution);

            let creator_hex: String = creator_ed25519[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
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
                apply_passed_proposal(state, handle, &proposal_block).await;
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
            let passed = constitution.submit_vote(&self_vote, creator_ed25519);
            drop(constitution);

            let node_hex: String = node_id[..4].iter().map(|b| format!("{b:02x}")).collect();
            info!(
                block_id = %block_id,
                leaving_node = %node_hex,
                "membership leave proposal registered"
            );

            if let Some(proposal_block) = passed {
                apply_passed_proposal(state, handle, &proposal_block).await;
            }
        }

        MembershipAction::Approve { proposal_block } => {
            // A participant is voting to approve an existing proposal.
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: true,
            };

            let mut constitution = handle.constitution.write().await;
            let passed = constitution.submit_vote(&vote, creator_ed25519);
            drop(constitution);

            let creator_hex: String = creator_ed25519[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            debug!(
                block_id = %block_id,
                voter = %creator_hex,
                proposal = %proposal_block,
                "membership approval vote recorded"
            );

            if let Some(proposal_block) = passed {
                apply_passed_proposal(state, handle, &proposal_block).await;
            }
        }

        MembershipAction::Reject { proposal_block } => {
            // A participant is voting to reject an existing proposal.
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: false,
            };

            let mut constitution = handle.constitution.write().await;
            constitution.submit_vote(&vote, creator_ed25519);
            drop(constitution);

            let creator_hex: String = creator_ed25519[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
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
/// rather than a disruptive genesis re-roll.
///
/// ⚑ THE INSTALL POINT, stated at its real resolution (the old docstring
/// claimed "takes effect at the NEXT wave boundary", which was aspiration, not
/// code). The install happens HERE, at the RATIFYING BLOCK'S POSITION in the
/// committed order: this function is only reached from the sequential
/// finalized-execution walk (`execute_finalized_membership`), so the ratifying
/// vote block is already in the causal past of a SUPER-RATIFIED final leader —
/// that super-ratification is the OLD configuration's certificate over the
/// install (Rondo §IV's `2t+1`-of-old rule, discharged by an object τ already
/// computes) — and every honest node executes the same committed order, so
/// every honest node installs at the same committed position (the Lean
/// `ConfigBoundary.install_position_immutable` shape). The vote collector's
/// `reconfigure` advances its `config_seq` at exactly this point and pins
/// already-crossed quorums to their configuration.
///
/// ⚠ NAMED RESIDUAL (not closed here): τ itself still reads the LIVE roster
/// for every wave's leader schedule (`ordering.rs::wave_leader` over
/// `constitution.current`), not the roster-as-of-each-wave — the τ
/// re-anchoring prerequisite (CONSENSUS-FROM-SOURCE §0). Until that lands, the
/// wave-boundary refinement of this install point (D6 Answer 1's "the next
/// wave runs under c+1") cannot be expressed, because no per-wave roster
/// exists to express it against.
async fn apply_passed_proposal(
    state: &NodeState,
    handle: &BlocklaceHandle,
    proposal_block: &BlockId,
) {
    let mut constitution = handle.constitution.write().await;
    // `Err` = the configuration step bound REFUSED the change BY NAME (the
    // Lean-authored `ConfigBoundary.classifyStep`; logged at the constitution
    // choke point). A refused step installs nothing — distinct from Ok(false),
    // a proposal that has not (yet) passed.
    if constitution
        .apply_if_passed(proposal_block)
        .unwrap_or(false)
    {
        let new_participants: Vec<[u8; 32]> = constitution.current.participants.clone();
        let new_count = constitution.current.participant_count();
        let new_version = constitution.version();
        let new_threshold = constitution.threshold();
        drop(constitution);
        // HYBRID-PQ committee for the NEW participant set: genesis-published
        // keys from state, plus any continuing member's key the collector
        // already holds (e.g. our OWN locally-derived key on a bootstrap node
        // not present in a genesis committee). A live-JOINED validator whose
        // ML-DSA key was never published gets NO entry — its votes cannot
        // count toward quorum until the committee learns its PQ key
        // (fail-closed; the continuing members still finalize).
        let mut pq_committee = pq_committee_for_participants(state, &new_participants).await;
        {
            let votes = handle.votes.read().await;
            for pk in &new_participants {
                if !pq_committee.contains_key(pk)
                    && let Some(k) = votes.pq_key(pk)
                {
                    pq_committee.insert(*pk, k.clone());
                }
            }
        }
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
            .apply_committee_change(&new_participants, pq_committee, new_threshold)
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

            // Create the leave proposal block and land it durably BEFORE it is
            // registered/voted/broadcast (F2 fail-closed): registering a proposal
            // whose block did not persist would bind constitution state to a seq
            // that restart re-authors differently. On failure, skip this proposal.
            let Some(block) = handle
                .author_add_block_or_rollback(
                    state,
                    Payload::MembershipVote {
                        action: MembershipAction::Leave { node_id: *node_key },
                    },
                )
                .await
            else {
                warn!(
                    node = %node_hex,
                    "auto-leave proposal failed to persist durably — not registered or broadcast"
                );
                continue;
            };

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
                apply_passed_proposal(state, handle, &proposal_block).await;
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
/// The COMPLETE set of cell ids whose CONTENT differs between two ledgers — the
/// A1 off-lock execution path's authoritative touched set.
///
/// A finalized turn is executed against a CLONE of the pre-state on a
/// `spawn_blocking` thread (so the FFI holds neither the async worker nor the
/// global write lock); this diff of the resulting post-state against the pre-state
/// is exactly the set the caller overlays onto the authoritative ledger. It is a
/// whole-`Cell` comparison, so — unlike the executor's `LedgerDelta`, which
/// omits the heap_root / lifecycle / program / vk /
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

/// Publish an already-durable finalized candidate as a whole-cell overlay.
///
/// The caller owns the ordering invariant: this helper must only run after the
/// commit-log transaction succeeds freshly and while the node write guard still
/// excludes another authoritative writer. Keeping the mutation in one tiny
/// helper makes that commit point visible in review and lets tests pin complete
/// create/update/remove behavior independently of the store.
fn install_finalized_ledger_overlay(
    live: &mut dregg_cell::Ledger,
    candidate: &dregg_cell::Ledger,
    touched: &[dregg_cell::CellId],
) {
    for id in touched {
        match candidate.get(id) {
            Some(cell) => {
                let _ = live.remove(id);
                let _ = live.insert_cell(cell.clone());
            }
            None => {
                let _ = live.remove(id);
            }
        }
    }
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
/// can reconstruct the canonical cell — instead every node mints a zero-balance,
/// zero-pk stub at the destination id.
///
/// ⚑ THE INPUT IS (TURN, PRE-STATE), NOT THE TURN ALONE. This docblock claimed
/// the landing site was provisioned "purely from the turn's data" until
/// 2026-08-06, and it was not: the destination ID comes from the turn, but the
/// ASSET is read out of the LOCAL LEDGER, from the Transfer's SOURCE cell (see
/// the loop body). A `Transfer` is a single-asset move, so a stub minted in any
/// other asset is refused by the executor's own same-asset guard — the asset has
/// to come from somewhere, and the turn does not carry it.
///
/// The uniformity argument never needed the stronger claim, and stating it that
/// way hid a real dependence behind a load-bearing word ("purely"). What actually
/// carries the argument: `provision ∘ execute` is a pure function of exactly the
/// pair (finalized turn, pre-state), and provisioning consumes no input the
/// executor does not already consume. So two nodes with equal pre-state provision
/// AND execute identically, and a node with a different pre-state was going to
/// compute a different post-state whatever provisioning did.
///
/// ⚠ THE ABSENT-SOURCE SKIP is the one case where that needs saying out loud,
/// because a silent `continue` in a loop this path depends on is exactly the
/// fail-open shape this tree has been full of. It is OUTCOME-NEUTRAL, not merely
/// harmless-looking: a node that lacks the source cell cannot execute the
/// Transfer either (`apply.rs` raises `CellNotFound` on the source before any
/// mutation), `TurnResult::Rejected` discards the whole isolated candidate
/// without an overlay, and the refusal is recorded durably against the block. So
/// on the node where the skip fires, provisioning-or-not cannot change the
/// post-state — that node writes no post-state at all. Provisioning a stub in a
/// GUESSED asset would change only which error the same rejection carries, while
/// making the un-derivable asset look derivable.
/// `finalized_transfer_source_absent_refuses_it_does_not_fork_state` drives both
/// nodes end to end and pins it: one commits, the other's ledger image is
/// byte-identical before and after.
///
/// This is destination PROVISIONING, not the turn's value semantics: the
/// conservation-checked Transfer still moves the exact amount into the (now-present)
/// stub. The whole forest is walked (`total_effects`), so a Transfer nested inside a
/// child action is provisioned too, not only root-level effects.
///
/// Idempotent: a destination already present (genesis cell, a prior turn, or a
/// peer that legitimately holds the canonical cell) is left untouched.
///
/// ⚠ ORDER-DEPENDENT, and not repaired here: the walk is single-pass over
/// `total_effects()`, so a forest whose Transfer INTO a cell is ordered after a
/// Transfer OUT OF it leaves the second destination unprovisioned and the turn
/// deterministically rejected. Uniform across nodes (same order everywhere), so
/// it is a completeness gap in what a forest may express, not a divergence — a
/// fixpoint walk would close it.
pub(crate) fn provision_transfer_destinations(
    ledger: &mut dregg_cell::Ledger,
    call_forest: &dregg_turn::CallForest,
) {
    for effect in call_forest.total_effects() {
        if let dregg_turn::Effect::Transfer { from, to, .. } = effect
            && ledger.get(to).is_none()
        {
            // THE STUB'S ASSET IS THE MOVED ASSET, AND IT COMES FROM THE LOCAL
            // LEDGER — the turn does not carry it. A Transfer is a single-asset
            // move: the executor refuses `from.asset() != to.asset()` as a
            // cross-asset teleport. A landing site minted in the all-zero asset
            // therefore REFUSED every transfer out of a cell in any other asset —
            // which, once genesis and the faucet moved to the canonical
            // `blake3("default")` domain, is every real grant.
            // The stub's id is pinned to `*to`, so its name salt is free — set it
            // to the source's ASSET so `stub.asset()` is the moved currency.
            //
            // ⚠ THE SKIP IS DELIBERATE AND OUTCOME-NEUTRAL, not a shrug (full
            // argument + the two-node test in this function's docblock): a node
            // without the source cannot execute this Transfer either — `apply.rs`
            // raises `CellNotFound` on the source before any mutation, the
            // rejected candidate is discarded without an overlay, and the refusal
            // is durably recorded. Nothing this loop does or declines to do can
            // change that node's post-state. Minting a landing site in a GUESSED
            // asset would change only which error the same rejection carries.
            let Some(token_id) = ledger.get(from).map(|cell| *cell.asset().as_bytes()) else {
                continue;
            };
            let stub =
                dregg_cell::Cell::remote_stub_with_id_pk_token_balance(*to, [0u8; 32], token_id, 0);
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
// (`dregg-ledger-root-v3`), same length prefix, same whole-cell postcard leaves.
pub(crate) use dregg_persist::canonical_ledger_root;
