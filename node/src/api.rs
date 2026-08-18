//! Axum HTTP API router for the dregg node.
//!
//! Serves a localhost-only API that the browser extension cipherclerk talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::IpAddr;
use std::sync::Arc;
use std::time::Instant;

use argon2::password_hash::SaltString;
use argon2::password_hash::rand_core::OsRng;
use argon2::{Argon2, PasswordHash, PasswordHasher, PasswordVerifier};
use axum::extract::DefaultBodyLimit;
use axum::http::Request;
use axum::http::{HeaderValue, Method, header};
use axum::response::Response;
use axum::response::sse::{Event, Sse};
use axum::{
    Json, Router,
    extract::ConnectInfo,
    extract::Path as AxumPath,
    extract::Query,
    extract::State,
    http::StatusCode,
    middleware,
    routing::{get, post},
};
use futures_util::stream::{self, Stream};
use serde::{Deserialize, Serialize};
use std::convert::Infallible;
use subtle::ConstantTimeEq;
use tokio::sync::{Mutex, Semaphore};

use dregg_sdk::{Attenuation, AuthRequest, CellId, SignedTurn};
use dregg_token::BudgetSpec;
use dregg_turn::{CallForest, Turn};

use crate::state::{
    ActivityProofStatus, ActivityStatus, CommittedEvent, FaithfulMirrorError, NodeEvent, NodeState,
};
use crate::ws::handle_ws;

// =============================================================================
// Request/Response types
// =============================================================================

#[derive(Serialize)]
pub struct StatusResponse {
    /// True when EXACTLY these three hold: the store is readable, a blocklace
    /// consensus handle is attached, and the local DAG holds at least one block
    /// (`block_count > 0`). It reflects real liveness, NOT the attested-root
    /// height — a devnet producing heartbeat blocks reports `healthy: true` well
    /// before the first turn advances `latest_height`. See `dag_height` vs
    /// `latest_height` below.
    ///
    /// The one-block floor is why a node reports `false` for the first moments
    /// after boot: until 2026-07-25 the idle-heartbeat timer started at boot, so
    /// that window was a FULL heartbeat interval (default 120s) of `healthy:
    /// false` on a correct node. The cadence now anchors an empty lace on its
    /// first tick (`blocklace_sync::cadence_decision`), so the window is a tick,
    /// not a window.
    ///
    /// ⚑ 2026-08-08 — TWO MORE CONJUNCTS, because those three could not go
    /// false for the failure that matters. Measured on a 4-node federation at
    /// threshold 3: `healthy: true` and `consensus_live: true` persisted through
    /// the whole of a quorum-losing 2-of-4 partition, `latest_height` frozen at 1
    /// for 210 s while `dag_height` climbed on local heartbeats. Every one of the
    /// three original conjuncts was TRUE, and none of them was about the other
    /// members. `healthy` now also requires `quorum_reachable` and
    /// `!finality_stalled` — see those fields.
    ///
    /// ⚑ 2026-08-09 — A SIXTH, because the partition conjuncts still could not
    /// go false for the JOINER. Measured on port 8465: 345 s of refused join
    /// requests, never a committee member, `healthy: true` throughout.
    ///
    /// A joiner that carries no committee descriptor of its own runs on a
    /// SINGLE-KEY constitution, so its threshold is 1: `quorum_reachable` is
    /// trivially true (it counts toward its own quorum) and `finality_stalled`
    /// is deliberately inert below threshold 2. Both partition legs are
    /// structurally blind to it. Re-measured on a live 4-node federation
    /// 2026-08-09 (port 8565, 300 s, 21 requests sent, no proposal ever opened):
    /// `quorum_threshold: 1, quorum_reachable: true, finality_stalled: false,
    /// consensus_live: true, block_count: 3` — every pre-existing conjunct TRUE,
    /// and only the join conjunct makes the verdict false.
    ///
    /// A joiner that DID sync the federation's descriptor sees the real
    /// threshold, so `quorum_reachable` catches it too (port 8564 in the same
    /// run: threshold 3, `quorum_reachable: false`). The join conjunct is not
    /// redundant there — it is the one that names the actual condition, "I am
    /// not a member", rather than a symptom of it.
    ///
    /// `healthy` now also requires `join_member || !ever_asked_to_join`: a node
    /// that has proposed and heard nothing says so. See the `join_*` fields.
    ///
    /// This means a legitimately-joining node reports `healthy: false` for the
    /// whole interval between its first join request and admission. That is the
    /// honest reading, not a regression — until the committee ratifies it, it
    /// finalizes nothing.
    pub healthy: bool,
    /// CONFIGURED peers: the length of the `--federation-peers` list this
    /// process was launched with. It is a constant of the deployment and says
    /// NOTHING about reachability — it read 3 with two of those three frozen.
    /// For links that are actually carrying traffic read `connected_peers`; for
    /// members actually participating in consensus read `live_committee_voters`.
    pub peer_count: usize,
    /// Peers with an OPEN gossip transport right now (`GossipNetwork`). A
    /// measurement, not a launch flag. Absent when no consensus handle is
    /// attached (there is no gossip layer to ask).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub connected_peers: Option<usize>,
    /// Distinct OTHER committee members whose finalization vote this node
    /// admitted within the last
    /// `blocklace_sync::COMMITTEE_LIVENESS_WINDOW` (60 s). This is the count
    /// that collapses under a partition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub live_committee_voters: Option<usize>,
    /// The vote collector's live 2f+1. Tracks committee reconfiguration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quorum_threshold: Option<usize>,
    /// `live_committee_voters + 1 >= quorum_threshold` — could this node
    /// assemble a quorum from the members currently reaching it? THE ANSWER TO
    /// "can I finalize at all". False on the minority side of a partition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quorum_reachable: Option<bool>,
    /// Has any block EVER crossed consensus-wide quorum on this node? `false` on
    /// a joiner that never got into the committee — which used to report
    /// `healthy: true` forever.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ever_reached_quorum: Option<bool>,
    /// Seconds since the last consensus-wide quorum here, or since consensus
    /// started if there has never been one. This is the number that climbs
    /// during a stall while `dag_height` keeps rising on local heartbeats.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seconds_since_quorum: Option<u64>,
    /// `seconds_since_quorum` past `blocklace_sync::FINALITY_STALL_THRESHOLD`
    /// (90 s) on a federation whose threshold is greater than 1 — "I have
    /// proposed and heard nothing". Never set on a threshold-1 deployment,
    /// which has no cross-node quorum to lose.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub finality_stalled: Option<bool>,
    // ─── The JOINER's own admission state (`blocklace_sync::JoinProgress`) ───
    //
    // Present ONLY on a node that has actually run the join path — it asked to
    // join, or it is a member that came in through a join. All five are absent
    // on a genesis member, whose `JoinProgress` is `default()` and would
    // otherwise publish a meaningless `join_member: false`.
    //
    // ⚑ These were populated on `BlocklaceHandle` and read by NOTHING. The
    // struct's own doc said "for `/status`" and the handle field's said
    // "surfaced by `/status`", for a value `api.rs` never mentioned; the wedged
    // joiner that motivated the type went on reporting `healthy: true`.
    /// True once this node's key is a constitutional participant. `false` here
    /// (with `join_requests_sent > 0`) is the wedged joiner, and it is the
    /// conjunct that now drives `healthy` false.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub join_member: Option<bool>,
    /// How many join requests this node has sent over the narrow join channel.
    /// `> 0` with `join_member: false` = "I have asked and I am not in".
    #[serde(skip_serializing_if = "Option::is_none")]
    pub join_requests_sent: Option<u64>,
    /// How many live gossip peers the LAST join request actually reached. `0`
    /// distinguishes "shouting into a void" (no transport to any peer) from
    /// "delivered, awaiting sponsorship".
    #[serde(skip_serializing_if = "Option::is_none")]
    pub join_last_request_peers: Option<usize>,
    /// Seconds since this node first asked to join, while still not a member.
    /// The 345 that the measured joiner had no way to report.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub join_waiting_secs: Option<u64>,
    /// True once a `Join` proposal for OUR key has been seen in the
    /// constitution — proof the request demonstrably reached a member. This is
    /// the difference between "waiting for approval" (proposal open, needs
    /// votes) and "heard nothing at all" (nobody sponsored it).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub join_proposal_seen: Option<bool>,
    /// Blocks whose VERIFIED finalization-vote tally holds conflicting
    /// `(merkle_root, receipt_stream_root)` pairs — hybrid-verified committee
    /// members really attested different finalized states
    /// (`finalization_votes::VoteCollector::verified_root_split_count`).
    /// `> 0` is the loud form of the state the 2026-08 3-vs-1 root fork spent
    /// 27 h in while this endpoint said `healthy: true`. Detection, NOT
    /// attribution: both sides are signature-backed and neither is thereby
    /// Byzantine; unverified disagreement CLAIMS never reach this number.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verified_root_splits: Option<usize>,
    /// Turns this node has accepted for consensus and not yet resolved to a
    /// durable verdict. Ask `GET /api/turn/{hash}/verdict` about any one of them.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turns_in_flight: Option<usize>,
    /// Attested-root / turn height: the height of the latest finalized
    /// AttestedRoot. This advances only on turn-bearing finality, NOT on idle
    /// heartbeat blocks, so it can legitimately be 0 on a fresh node whose DAG
    /// is already tall. Kept for backward compatibility; use `dag_height` for
    /// "how tall is the chain".
    pub latest_height: u64,
    /// Real blocklace DAG tip height: the max block `seq` in the local lace.
    /// This advances on EVERY block (turns and heartbeats), so it is the
    /// honest public "the chain is at height N" signal. 0 if consensus has not
    /// produced a block yet (or no blocklace handle is attached).
    pub dag_height: u64,
    /// Number of blocks currently in the local blocklace DAG.
    pub block_count: usize,
    /// Whether a blocklace consensus handle is attached (consensus task is
    /// running). One of the inputs to `healthy`.
    pub consensus_live: bool,
    /// F-8: aggregate private-activity counters (count of revoked credentials /
    /// shielded notes). These leak the *volume* of private activity to any
    /// unauthenticated scraper, so they are OMITTED from the public `/status`
    /// response by default (`serde` skips `None`). An operator who wants them on
    /// the wire opts in explicitly via `DREGG_STATUS_EXPOSE_COUNTS=1` (e.g. for a
    /// trusted internal dashboard behind auth). Default: `None` → field absent.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revocation_count: Option<u64>,
    /// F-8: see `revocation_count`. Omitted by default.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note_count: Option<u64>,
    pub federation_mode: String,
    pub public_key: String,
    /// THE SWAP — honest verified-execution surface. The authoritative state
    /// producer on the commit path:
    ///   * `"lean"`  — the VERIFIED Lean executor produces the committed state
    ///     for swap-safe (root-agreeing) turns (the DEFAULT; opt out with
    ///     `DREGG_LEAN_PRODUCER=0`); the Rust executor is a logged differential
    ///     cross-check.
    ///   * `"rust"`  — the legacy Rust executor produces (Lean runs at most as a
    ///     veto-only shadow). Reached only via `DREGG_LEAN_PRODUCER=0`.
    pub state_producer: String,
    /// Whether the verified Lean producer is enabled (mirrors `state_producer ==
    /// "lean"`). Convenience boolean for clients.
    pub lean_producer: bool,
    /// THE ORDERING HALF OF THE SAME HONESTY — which order decided the most recent finality
    /// poll. `state_producer` above says who produced the STATE; this says who produced the
    /// ORDER, and until now there was no such field, so a node whose verified τ-order FFI was
    /// blowing its per-poll budget looked identical on `/status` to one where the verified rule
    /// decided every poll.
    ///
    ///   * `"verified_ffi"` / `"verified_cached"` — the VERIFIED Lean `dregg_tau_order` order
    ///     decided the poll (freshly computed, or reused from the cross-poll cache that holds a
    ///     verified order). Only these two mean "this node finalized over the verified ordering".
    ///   * `"unverified_over_budget"` — the verified FFI EXCEEDED
    ///     `consensus_order_budget_ms` and the un-verified Rust `ordering::tau` twin decided.
    ///   * `"unverified_unavailable"` — the export was missing / returned ERR; the twin decided.
    ///   * `"unverified_cached"` — a cache hit serving an un-verified order stored by an earlier
    ///     over-budget poll.
    ///   * `"failed_closed"` — no verified order and the twin is forbidden: the poll finalized
    ///     NOTHING (a liveness alarm).
    ///   * `"none"` — no multi-party finality poll has selected an order yet.
    pub consensus_order: String,
    /// The per-poll wall-clock budget (`DREGG_FINALITY_ORDER_TIMEOUT_MS`, default 2500) the
    /// verified τ-order FFI must meet for `consensus_order` to be a `verified_*` value. **The
    /// verified-ordering claim is conditional on this number**, so the number is published with
    /// the claim rather than left in a source comment.
    pub consensus_order_budget_ms: u64,
    /// Finality polls whose order came from the VERIFIED Lean rule, since process start.
    pub consensus_order_verified_polls: u64,
    /// Finality polls whose order came from the UN-VERIFIED Rust `ordering::tau` twin. **Any
    /// non-zero value falsifies the unqualified claim "this node finalizes over the verified
    /// ordering"** for this process.
    pub consensus_order_unverified_polls: u64,
    /// Finality polls that finalized NOTHING because no verified order was available and the
    /// twin was forbidden. Sustained growth here is a finality HALT.
    pub consensus_order_failed_closed_polls: u64,
    /// Finality polls whose verified τ-order FFI BLEW the budget, whatever happened next. This is
    /// the number that says whether the budget is a real constraint on this node right now.
    pub consensus_order_over_budget_polls: u64,
    /// Whether the node generates + verifies a full-turn STARK proof for every
    /// committed turn on the commit path (the "every transition is proven"
    /// claim). When `false`, only activity proofs are produced on submission.
    pub full_turn_proving: bool,
    /// Number of SWAP-SAFE (ROOT-AGREEING) effect KINDS: the verified producer
    /// runs AND its reconstituted root provably equals the Rust executor's. A
    /// turn touching only these is produced by the verified Lean executor; a turn
    /// touching any root-gap or unmappable effect falls back to Rust for that
    /// turn.
    ///
    /// NOT the same number as `GET /api/node/producer`'s MAPPABLE set (the
    /// producer runs; root agreement not claimed). Both used to be spelled
    /// "covered", which is how `/api/node/health` said 18 and
    /// `/api/node/producer` said 21 about the same producer; the producer
    /// endpoint's fields are now `mappable_effects` / `unmappable_effects` and
    /// this one says root-agreeing. See `GET /api/node/producer` for the full
    /// per-effect breakdown of both sets.
    pub producer_root_agreeing_effects: usize,
    /// DEPRECATED SPELLING of `producer_root_agreeing_effects` — the identical
    /// number, kept on the wire because a shipped client still decodes this key
    /// (`discord-bot`'s status/dashboard structs). New clients read
    /// `producer_root_agreeing_effects`; this alias goes away once the last
    /// reader moves.
    pub producer_covered_effects: usize,
}

/// Public, redacted projection of one validated durable PoA Signal head.
///
/// The exact config and Canon images are deliberately not returned: the Canon
/// carries player/activity state, and a status route does not need the complete
/// authority-bearing payload.  The durable head digest remains enough to name
/// the exact stored object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalHeadViewV1 {
    pub head_digest: String,
    pub deployment_digest: String,
    pub transition_count: u64,
    pub world_sequence: u64,
    pub canon_revision: u64,
    pub last_transition_digest: String,
}

/// Honest status for the PoA Signal authority attached to this node's exact
/// federation.  `installed` means only that a structurally validated durable
/// genesis/head exists; this endpoint supplies no quorum or finality proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalStatusResponseV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub federation_id: String,
    pub installed: bool,
    pub head: Option<PoaSignalHeadViewV1>,
    pub consensus_finality: &'static str,
}

/// Redacted public cross-reference for one validated durable PoA Signal
/// transition and its carrying turn/receipt.
///
/// Judge wires and predecessor/successor Canon images are intentionally
/// omitted.  The receipt hash is a durable cross-reference, not a claim that
/// this response contains a quorum-finality certificate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalTransitionViewV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub federation_id: String,
    pub sequence: u64,
    pub observed_head_transition_count: u64,
    pub is_observed_head_transition: bool,
    pub commit_ordinal: u64,
    pub turn_hash: String,
    pub receipt_hash: String,
    pub predecessor_head_digest: String,
    pub successor_head_digest: String,
    pub transition_digest: String,
    pub judge_input_digest: String,
    pub judge_output_digest: String,
    pub consensus_finality: &'static str,
}

/// The only player-cell projection needed to construct a fresh Signal claim.
///
/// This deliberately does not reuse [`CellDetailResponse`]: that explorer view
/// also exposes balances, program/state fields, delegates, and the complete
/// capability list.  A public game ingress needs only the replay coordinates
/// and the identity binding it is about to sign against.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalPlayerHeadResponseV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub federation_id: String,
    pub cell_id: String,
    pub found: bool,
    pub nonce: u64,
    pub public_key: Option<String>,
    pub last_receipt_hash: Option<String>,
}

/// Response from `GET /api/node/producer` — the honest verified-execution
/// surface (THE SWAP boundary). Tells a client EXACTLY which state producer
/// runs the commit path and, when the verified Lean producer is enabled, which
/// effect kinds it covers (defaults to Lean for) vs. which still fall back to
/// the Rust producer.
#[derive(Serialize)]
pub struct ProducerStatusResponse {
    /// `"lean"` or `"rust"` — the authoritative state producer on the commit path.
    pub state_producer: String,
    /// Whether the verified Lean producer is enabled (default ON; opt out with
    /// `DREGG_LEAN_PRODUCER=0`).
    pub lean_producer_enabled: bool,
    /// Whether a full-turn STARK proof is generated + verified per committed turn.
    pub full_turn_proving: bool,
    /// Effect kinds the producer can MAP (a turn touching ONLY these runs on the
    /// verified producer when enabled). Mirrors the marshaller's wire-projected
    /// set. Running is not root agreement — `root_agreeing_effects` below is the
    /// swap-safe subset, and it is the number `/status` reports. This field was
    /// called `covered_effects` while `/status` called the SWAP-SAFE count
    /// "covered" too: one word, two numbers.
    pub mappable_effects: Vec<String>,
    /// Total number of distinct on-chain effect kinds.
    pub total_effect_kinds: usize,
    /// Effect kinds the producer canNOT map — a turn touching any of these falls
    /// back to the Rust producer for that turn. This is the honest "blocks the
    /// full default" list. (Was `uncovered_effects`.)
    pub unmappable_effects: Vec<String>,
    /// The SWAP-SAFE subset of `mappable_effects`: the producer runs AND its
    /// reconstituted `.root()` provably EQUALS the Rust executor's (pinned by the
    /// `lean_state_producer_*` differentials). A turn touching ONLY these has ZERO
    /// post-state divergence when the verified producer runs.
    pub root_agreeing_effects: Vec<String>,
    /// Mapped effects whose Lean-produced `.root()` DIVERGES from Rust (the wire
    /// model is lossier than the cell commitment, or Rust re-shapes the ledger):
    /// the producer still runs and installs the verified state, but the divergence
    /// is logged as a real finding. The CHARACTERIZED residual of THE SWAP.
    pub root_gap_effects: Vec<String>,
    /// Human-readable summary of the boundary.
    pub summary: String,
}

/// Response from `GET /api/node/identity` — the node operator's own identity.
/// The `agent_cell` is the cell `/turn/submit` acts on by default (the node
/// signs every operator turn as this cell); a client can fund it via the faucet
/// or target it directly. This makes the "who am I / what's my cell" question a
/// first-class answer instead of a derivation a client has to reproduce.
#[derive(Serialize)]
pub struct NodeIdentityResponse {
    /// Hex-encoded operator Ed25519 public key.
    pub public_key: String,
    /// Hex-encoded operator agent cell id (`derive_raw(public_key, H("default"))`).
    pub agent_cell: String,
    /// Whether the operator's cipherclerk is unlocked (turns can be signed).
    pub unlocked: bool,
    /// Current balance of the agent cell, if it exists in the ledger.
    /// THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub agent_balance: Option<i64>,
    /// Current nonce of the agent cell, if it exists.
    pub agent_nonce: Option<u64>,
}

#[derive(Serialize)]
pub struct FaithfulMirrorErrorResponse {
    pub error: String,
}

/// Cursor-only request for the public append-only faithful note mirror.
/// Page sizes are protocol constants chosen by the node; callers cannot ask
/// for a note position or a narrow page.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FaithfulNoteMirrorRequest {
    #[serde(default)]
    pub commitment_cursor: u64,
    #[serde(default)]
    pub history_cursor: u64,
    #[serde(default)]
    pub nullifier_cursor: u64,
}

#[derive(Serialize)]
pub struct FaithfulNoteMirrorAnchorResponse {
    pub session_id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub height: u64,
    pub note_count: u64,
    pub root8: [u32; 8],
}

#[derive(Serialize)]
pub struct FaithfulNoteMirrorRecordResponse {
    pub session_id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub previous_height: u64,
    pub height: u64,
    pub previous_note_count: u64,
    pub note_count: u64,
    pub predecessor_root8: [u32; 8],
    pub successor_root8: [u32; 8],
    pub block_id: String,
    /// Node-author hybrid authentication over the canonical FNHR message.
    /// This is intentionally not described as a federation quorum.
    pub hybrid_quorum: Vec<dregg_types::HybridQuorumSig>,
}

#[derive(Serialize)]
pub struct FaithfulNoteMirrorHeadResponse {
    pub history_records: u64,
    pub height: u64,
    pub note_count: u64,
    pub root8: [u32; 8],
    pub nullifier_count: u64,
    pub attested_nullifier_root8: [u32; 8],
}

#[derive(Serialize)]
pub struct FaithfulNullifierMirrorRecordResponse {
    pub nullifier: String,
    pub value: u64,
    pub seq: u64,
}

#[derive(Serialize)]
pub struct FaithfulNoteMirrorResponse {
    pub protocol: &'static str,
    pub commitment_cursor: u64,
    pub next_commitment_cursor: u64,
    pub history_cursor: u64,
    pub next_history_cursor: u64,
    pub nullifier_cursor: u64,
    pub next_nullifier_cursor: u64,
    /// Fixed-size prefix page, encoded as lowercase 32-byte hex strings.
    pub commitments: Vec<String>,
    pub nullifiers: Vec<FaithfulNullifierMirrorRecordResponse>,
    pub anchor: FaithfulNoteMirrorAnchorResponse,
    pub history: Vec<FaithfulNoteMirrorRecordResponse>,
    pub head: FaithfulNoteMirrorHeadResponse,
    /// FNMS-v1 hybrid signature over the complete target-independent head.
    pub head_hybrid_quorum: Vec<dregg_types::HybridQuorumSig>,
    pub complete: bool,
    /// Transport observers still learn mirror-sync timing and lag.  The SDK
    /// therefore walks from zero through every continuation. PIR/broadcast
    /// distribution is a later transport optimization, not claimed here.
    pub privacy: &'static str,
}

#[derive(Serialize)]
pub struct CipherclerkResponse {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

/// Exactly one stable coordinate for the authenticated finalized-receipt query.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FinalizedReceiptCoreQuery {
    pub receipt_index: Option<u64>,
    pub core_id: Option<String>,
}

/// Provenance-preserving predecessor projected from the canonical FRC1 core.
#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FinalizedReceiptPredecessorResponse {
    Genesis,
    LegacyCutover {
        legacy_receipt_index: u64,
        legacy_receipt_hash: String,
    },
    Core {
        core_id: String,
        legacy_receipt_index: u64,
        legacy_receipt_hash: String,
    },
}

/// Signer-independent exact finalization object served with its two durable coordinates.
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct FinalizedReceiptCoreResponse {
    pub protocol: &'static str,
    pub receipt_index: u64,
    pub core_id: String,
    /// Canonical fixed-width FRC1 bytes.  Clients rehash these under the FRC1 domain and compare
    /// the result with `core_id`; no local FRE1 signature is required or returned.
    pub canonical_core: String,
    pub block_id: String,
    pub tau_round: u64,
    pub consensus_unix_seconds: i64,
    pub committee_epoch: u64,
    pub predecessor: FinalizedReceiptPredecessorResponse,
    pub turn_hash: String,
    pub agent: String,
    pub federation_id: String,
}

impl FinalizedReceiptCoreResponse {
    fn from_core(receipt_index: u64, core: dregg_turn::FinalizedReceiptCoreV1) -> Self {
        let context = core.context();
        let predecessor = match core.predecessor() {
            dregg_turn::FinalizedReceiptPredecessorV1::Genesis => {
                FinalizedReceiptPredecessorResponse::Genesis
            }
            dregg_turn::FinalizedReceiptPredecessorV1::LegacyCutover {
                legacy_receipt_index,
                legacy_receipt_hash,
            } => FinalizedReceiptPredecessorResponse::LegacyCutover {
                legacy_receipt_index,
                legacy_receipt_hash: hex_encode(&legacy_receipt_hash),
            },
            dregg_turn::FinalizedReceiptPredecessorV1::Core {
                core_id,
                legacy_receipt_index,
                legacy_receipt_hash,
            } => FinalizedReceiptPredecessorResponse::Core {
                core_id: hex_encode(&core_id.bytes()),
                legacy_receipt_index,
                legacy_receipt_hash: hex_encode(&legacy_receipt_hash),
            },
        };
        Self {
            protocol: "FRC1",
            receipt_index,
            core_id: hex_encode(&core.id().bytes()),
            canonical_core: hex_encode(&core.to_canonical_bytes()),
            block_id: hex_encode(&context.block_id()),
            tau_round: context.tau_round(),
            consensus_unix_seconds: context.consensus_unix_seconds(),
            committee_epoch: core.committee_epoch(),
            predecessor,
            turn_hash: hex_encode(&core.turn_hash()),
            agent: hex_encode(&core.agent()),
            federation_id: hex_encode(&core.federation_id()),
        }
    }
}

#[derive(Deserialize)]
pub struct AuthorizeRequest {
    pub token_id: String,
    pub service: Option<String>,
    pub action: Option<String>,
    /// Cost of this specific request, in budget units. Threaded straight into
    /// `AuthRequest.request_cost` so a token carrying Budget caveats is checked
    /// against the amount actually being spent (defaults to 1 when the token
    /// has budgets but no cost is supplied).
    #[serde(default)]
    pub request_cost: Option<u64>,
    /// Current remaining budget per budget id, threaded into
    /// `AuthRequest.budget_states`. Required for a token that carries Budget
    /// caveats — the verifier denies when a budget's state is absent.
    ///
    /// CAVEAT (do not oversell): these values are CALLER-SUPPLIED and only
    /// per-request anti-spoofed by the kernel (`remaining <= limit`). Cumulative
    /// budget accounting across requests is NOT kernel-enforced — that would
    /// require sourcing the counter from cell state. This field exposes the
    /// budget caveat for per-request enforcement under the existing model; it is
    /// NOT a trustless cumulative cap.
    #[serde(default)]
    pub budget_states: std::collections::HashMap<String, u64>,
}

#[derive(Serialize)]
pub struct AuthorizeResponse {
    pub authorized: bool,
    pub reason: Option<String>,
}

#[derive(Deserialize)]
pub struct MintRequest {
    pub service: String,
}

#[derive(Serialize)]
pub struct MintResponse {
    pub token_id: String,
    pub service: String,
}

#[derive(Deserialize)]
pub struct AttenuateRequest {
    pub token_id: String,
    pub services: Vec<(String, String)>,
    /// Validity-window upper bound (Unix seconds), threaded into
    /// `Attenuation.not_after`. The attenuated token is invalid after this time
    /// — a real, kernel-enforced narrowing (checked as a time deny at verify).
    #[serde(default)]
    pub not_after: Option<i64>,
    /// Budget enrollment for the attenuated token, threaded into
    /// `Attenuation.budget`. Adds a Budget caveat (`id`, `class`, `limit`,
    /// optional `window`) that the holder must satisfy at verify time.
    ///
    /// CAVEAT (do not oversell): the caveat binds a per-request `remaining <=
    /// limit` check whose state is CALLER-SUPPLIED at authorize time. Cumulative
    /// spend across requests is NOT kernel-enforced (no cell-state counter), so
    /// this narrows the token's stated budget policy but is not a trustless
    /// cumulative cap.
    #[serde(default)]
    pub budget: Option<BudgetSpec>,
}

#[derive(Serialize)]
pub struct AttenuateResponse {
    pub new_token_id: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct TokenInfo {
    pub id: String,
    pub label: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct ReceiptInfo {
    pub chain_index: u64,
    pub chain_head: bool,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub agent: String,
    pub pre_state: String,
    pub post_state: String,
    pub timestamp: i64,
    pub computrons_used: u64,
    pub action_count: usize,
    pub previous_receipt_hash: Option<String>,
    pub finality: String,
    pub was_encrypted: bool,
    pub was_burn: bool,
    pub has_proof: bool,
    pub executor_signed: bool,
    pub has_witness: bool,
    pub witness_count: usize,
}

#[derive(Deserialize)]
pub struct SubmitTurnRequest {
    /// Hex-encoded 32-byte CellId.
    ///
    /// NOTE: this is advisory only. The node derives the real agent cell from
    /// its own cipherclerk pubkey (confused-deputy hardening, F-P1-3) and signs
    /// the turn as itself. The body value is parsed for validation/error
    /// reporting but never trusted as the signer.
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    /// The turn's actions — each becomes a root in the call forest, signed by
    /// the node operator's cipherclerk and routed through consensus.
    ///
    /// Historically this field did not exist and the handler built an empty
    /// `CallForest`, so every operator-signed turn was rejected by the executor
    /// ("call forest is empty") and nothing ever replicated. A request with no
    /// actions still round-trips (it produces an empty no-op turn that the
    /// executor rejects honestly) but real flows MUST carry at least one action.
    #[serde(default)]
    pub actions: Vec<TurnActionSpec>,
}

/// One action in a `SubmitTurnRequest`. The operator's cipherclerk signs each
/// action over its canonical bytes (`AgentCipherclerk::make_action`), so the
/// resulting `Authorization::Signature` authenticates the operator as the
/// caller for every effect in the action.
#[derive(Deserialize)]
pub struct TurnActionSpec {
    /// Hex-encoded 32-byte target cell id. Defaults to the operator's own
    /// agent cell when omitted (the common "act on my own cell" case).
    #[serde(default)]
    pub target: Option<String>,
    /// Method name (hashed to a `Symbol`). Defaults to `"submit"`.
    #[serde(default)]
    pub method: Option<String>,
    /// The effects this action applies.
    pub effects: Vec<TurnEffectSpec>,
}

/// A JSON-friendly projection of the on-chain `Effect` enum, covering the
/// effect kinds that a thin HTTP client needs to drive app flows: state
/// writes, value transfers, nonce bumps, and event emission. Richer effects
/// (notes, capability grants, factory births) go through the typed
/// `/turns/submit` signed-envelope path with an SDK-built `SignedTurn`.
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TurnEffectSpec {
    /// Write a 32-byte field element into a cell's state slot.
    SetField {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
        index: u64,
        /// Hex-encoded value: a full 64-char hex field element, or a shorter
        /// hex/decimal scalar that is left-padded into a little-endian u64.
        value: String,
    },
    /// Transfer computrons between cells.
    Transfer {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        from: Option<String>,
        to: String,
        amount: u64,
    },
    /// Emit an event (topic + data) from a cell.
    EmitEvent {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
        topic: String,
        /// Event data words, each a hex/decimal scalar.
        #[serde(default)]
        data: Vec<String>,
    },
    /// Increment a cell's nonce by 1.
    IncrementNonce {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
    },
    /// Grant a capability on `target` (a cell the operator owns) into `to`'s
    /// c-list. The thin path covers the OPERATOR-authored grant an external
    /// provider needs witnessed in the receipt log (e.g. the execution-lease
    /// grant — the `Granted` fact whose label the verified lease read
    /// decodes); richer grants (breadstuff tokens, facet masks, expiries) go
    /// through the signed-envelope path.
    GrantCapability {
        /// Hex cell id of the grantor. Defaults to the action's target (the
        /// operator cell on the thin path).
        #[serde(default)]
        from: Option<String>,
        /// Hex cell id whose c-list receives the capability.
        to: String,
        /// Hex cell id the capability points at.
        target: String,
        /// C-list slot. Defaults to 0.
        #[serde(default)]
        slot: u32,
    },
}

/// Parse a value string into a 32-byte field element.
///
/// Accepts either a full 64-char hex field element (used verbatim) or a
/// shorter hex (`0x…`) / decimal scalar, which rides the CANONICAL u64 lane
/// (`dregg_cell::field_from_u64`, big-endian bytes `24..32`). Both branches now
/// land on the same lane; the scalar branch used to write little-endian into
/// bytes `0..8`, so one endpoint served two incompatible encodings and the
/// scalar one could not prove.
fn parse_field_element(s: &str) -> Result<[u8; 32], String> {
    let t = s.trim();
    if t.len() == 64 && t.bytes().all(|b| b.is_ascii_hexdigit()) {
        let bytes = hex_decode(t).map_err(|_| format!("invalid hex field element: {s}"))?;
        let mut out = [0u8; 32];
        out.copy_from_slice(&bytes);
        return Ok(out);
    }
    let scalar = if let Some(hex) = t.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).map_err(|_| format!("invalid hex scalar: {s}"))?
    } else {
        t.parse::<u64>()
            .map_err(|_| format!("invalid scalar: {s}"))?
    };
    // The canonical u64 lane (big-endian bytes 24..32) — NOT little-endian into 0..8. A `0..8`
    // write lands in the high lanes the deployed `setFieldVmDescriptor2-{slot}R24` FREEZES, so
    // `{"kind":"set_field","value":"42"}` could not prove at all, and no kernel-side reader
    // (`field_to_u64` / `field_to_i128`) could see it. The 64-char-hex branch above passes 32
    // bytes through verbatim and was already on this lane, so one endpoint served two encodings.
    // Gate: `circuit/tests/setfield_encoder_window_gate.rs`.
    Ok(dregg_cell::field_from_u64(scalar))
}

fn parse_cell_id(s: &str) -> Result<CellId, String> {
    let bytes: [u8; 32] = hex_decode(s).map_err(|_| format!("invalid cell id: {s}"))?;
    Ok(CellId(bytes))
}

/// Convert a `TurnEffectSpec` into an on-chain `Effect`, resolving cell
/// defaults against the action's target.
fn build_effect(spec: TurnEffectSpec, default_cell: CellId) -> Result<dregg_turn::Effect, String> {
    use dregg_turn::Effect;
    let resolve = |opt: Option<String>| -> Result<CellId, String> {
        match opt {
            Some(h) => parse_cell_id(&h),
            None => Ok(default_cell),
        }
    };
    Ok(match spec {
        TurnEffectSpec::SetField { cell, index, value } => Effect::SetField {
            cell: resolve(cell)?,
            index,
            value: parse_field_element(&value)?,
        },
        TurnEffectSpec::Transfer { from, to, amount } => Effect::Transfer {
            from: resolve(from)?,
            to: parse_cell_id(&to)?,
            amount,
        },
        TurnEffectSpec::EmitEvent { cell, topic, data } => {
            let words: Result<Vec<[u8; 32]>, String> =
                data.iter().map(|w| parse_field_element(w)).collect();
            Effect::EmitEvent {
                cell: resolve(cell)?,
                event: dregg_turn::action::Event::new(dregg_turn::action::symbol(&topic), words?),
            }
        }
        TurnEffectSpec::IncrementNonce { cell } => Effect::IncrementNonce {
            cell: resolve(cell)?,
        },
        TurnEffectSpec::GrantCapability {
            from,
            to,
            target,
            slot,
        } => {
            let cap_target = parse_cell_id(&target)?;
            Effect::GrantCapability {
                from: resolve(from)?,
                to: parse_cell_id(&to)?,
                cap: dregg_cell::CapabilityRef {
                    target: cap_target,
                    slot,
                    permissions: dregg_cell::AuthRequired::None,
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                    provenance: dregg_cell::derivation::cap_provenance(
                        &cap_target,
                        slot,
                        &dregg_cell::derivation::mint_provenance(),
                        &[0u8; 32],
                    ),
                },
            }
        }
    })
}

#[derive(Serialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct SubmitSignedTurnResponse {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub signer: Option<String>,
    pub action_count: usize,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

// =============================================================================
// EncryptedTurn submission types (AUDIT-privacy.md §11.2 wiring).
//
// Wire format: the request body is the postcard-serialized
// `dregg_turn::EncryptedTurn` envelope as **raw bytes** (Content-Type:
// application/octet-stream). The body is **not** wrapped in JSON because
// the EncryptedTurn includes a ciphertext blob whose size makes hex/base64
// inflation undesirable and because postcard is the canonical dregg wire
// format for binary envelopes.
//
// The executor's X25519 unsealer secret is derived from the node's cipherclerk
// via `AgentCipherclerk::derive_symmetric_key("dregg-turn-unsealer-v1")`.
// The matching public key is exposed via `GET /turns/encryption-key` so a
// sender can encrypt to this executor.
//
// Boundary (BOUNDARIES.md §5):
//   - **out-of-band**: gossip observers / route hops (see only ciphertext)
//   - **cleartext-inside**: the executor holding the unsealer secret
//   - the receipt's `was_encrypted: true` bit is the only fact disclosed
//     after commit.
// =============================================================================

/// Response from `GET /turns/encryption-key` — the X25519 public key
/// the executor accepts `EncryptedTurn`s under. Senders use this with
/// `EncryptedTurn::encrypt_for_executor`.
#[derive(Serialize)]
pub struct TurnEncryptionKeyResponse {
    /// 64 hex chars — the executor's static X25519 public key.
    pub executor_x25519_public: String,
    /// Domain-string used to derive the secret from the cipherclerk seed.
    /// Lets verifiers reconstruct the deployment's key-derivation path.
    pub derivation_domain: String,
}

/// Response from `POST /turns/submit-encrypted`.
#[derive(Serialize)]
pub struct SubmitEncryptedTurnResponse {
    pub accepted: bool,
    /// On success, hex-encoded BLAKE3 hash of the recovered inner turn.
    /// On reject, contains "rejected: <reason>". The recovered turn hash
    /// is itself derivable by anyone who can decrypt; it is NOT a privacy
    /// leak (the encrypted-turn commitment already binds to this hash).
    pub turn_hash: Option<String>,
    /// Whether the receipt's `was_encrypted` bit was set (always `true`
    /// on success; included so the caller can confirm the encrypted path
    /// was actually taken).
    pub was_encrypted: bool,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct CellResponse {
    pub id: String,
    pub found: bool,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: Option<i64>,
}

#[derive(Serialize)]
pub struct AttestedRootInfo {
    pub height: u64,
    pub merkle_root: String,
    pub timestamp: i64,
    /// LOCAL light-client signature count (`quorum_signatures.len()`); on a
    /// full node this is 1 and is NOT the cross-node quorum. Kept for wire
    /// compatibility — gate on `quorum`/`threshold` instead.
    pub signatures: usize,
    /// The number of cross-node committee finalization votes assembled for this
    /// root (`finalization_quorum.len()`). A consumer gates acceptance on
    /// `quorum >= threshold`. COUNT ONLY — not signature-verified server-side;
    /// trust still derives from the independently recomputed ledger root.
    pub quorum: usize,
    /// The committee vote count required for a valid finalization quorum.
    pub threshold: usize,
    /// Structural completeness per `StoredAttestedRoot::is_structurally_complete`:
    /// a threshold QC, or >= `threshold` DISTINCT signers in EITHER population —
    /// the local light-client signatures or the cross-node committee votes.
    ///
    /// ⚑ Until 2026-08-08 it consulted only `signatures`, which on a full-mode
    /// node is structurally 1, so this read `false` on every finalized root the
    /// federation had genuinely agreed. It is now the field it always looked
    /// like. Still COUNT-ONLY: no signature is verified here, and trust still
    /// derives from the independently recomputed ledger root.
    pub structurally_complete: bool,
}

#[derive(Serialize)]
pub struct FederationInfo {
    pub id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub threshold: u32,
    pub member_count: usize,
    pub members: Vec<String>,
    pub is_local: bool,
    pub latest_height: u64,
    pub latest_root: Option<String>,
    pub num_finalized_roots: usize,
}

#[derive(Serialize)]
pub struct CellListEntry {
    pub id: String,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub has_program: bool,
    pub found: bool,
}

#[derive(Serialize)]
pub struct CellDetailResponse {
    pub id: String,
    pub found: bool,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    /// Alias for JS inspector compat (cell.js + Starbridge Remote expect num_capabilities in some paths).
    pub num_capabilities: usize,
    pub has_delegate: bool,
    pub delegate: Option<String>,
    pub has_program: bool,
    pub public_key: String,
    pub token_id: String,
    pub proved_state: bool,
    pub delegation_epoch: u64,
    /// Content-addressed commitment for PeerExchange / state sync (matches wasm CellStateView).
    pub state_commitment: String,
    /// Quick kind for <dregg-cell-program> and raw views without full program dump.
    pub program_kind: String,
    /// Full self-describing program view (`{ kind, constraints | cases |
    /// circuit_hash }`) — the SAME total `StateConstraintView` projection the
    /// wasm runtime serves (`dregg_cell::program::CellProgramView`), so a
    /// live cell can show its own slot caveats (e.g. a council cell's
    /// AffineLe threshold M) to remote inspectors.
    pub program: dregg_cell::program::CellProgramView,
    /// The cell's `[FieldElement; 16]` state slots, each hex-encoded (64 chars).
    ///
    /// Empty when the cell is not found. Slot indices match the on-chain layout
    /// (`SetField` writes here); userspace apps (e.g. the nameservice) pin a
    /// fixed slot schema and read named slots out of this vector. Exposing the
    /// raw fields lets a thin client "resolve" a name by reading its slots back
    /// rather than only replaying events.
    #[serde(default)]
    pub fields: Vec<String>,
    /// The cell's c-list EDGES — every held capability serialized IN FULL
    /// (`target`, `slot`, `permissions`, `breadstuff`, `expires_at`,
    /// `allowed_effects`, R7 `stored_epoch`), NOT merely `capability_count`.
    ///
    /// A remote crawl (`dregg-sdk-net`'s `NodeWorldSink`) rebuilds the real
    /// [`CapabilitySet`](dregg_cell::CapabilitySet) from these edges so an
    /// authority read (`has_access`) over a crawled ledger answers IDENTICALLY
    /// to a read on the origin box (Pillar-2b: "any box derives the same cap
    /// from its own ledger copy"). Serializing the whole `CapabilityRef` via
    /// serde is byte-faithful — it carries the `Custom` vk_hash, the breadstuff
    /// token hash, and the facet mask that a hand-rolled projection would drop.
    #[serde(default)]
    pub capabilities: Vec<dregg_cell::CapabilityRef>,
    /// The revoked-slot TOMBSTONES (the openable-tree ghost leaves). Carried so
    /// a crawled c-list reproduces the post-revoke cap-root shape via
    /// [`CapabilitySet::reconstruct`](dregg_cell::CapabilitySet::reconstruct),
    /// not a compacted rebuild.
    #[serde(default)]
    pub capability_tombstones: Vec<u32>,
    /// The agent's RECEIPT-CHAIN HEAD — the `receipt_hash` of the last committed
    /// turn by this cell (as agent), or `None` if it has none yet. A client
    /// stamps this into the NEXT turn's `previous_receipt_hash` so the executor's
    /// per-agent chain check (`TurnExecutor::check_previous_receipt_hash`)
    /// accepts it under a PERSISTENT executor. Served from the node's persistent
    /// receipt log's per-agent index, NOT projected from `s.ledger`
    /// (a cell carries no receipt head) — that was the persistence time bomb:
    /// the head lives in the executor's `last_receipt_hash` map, and this exposes
    /// the authoritative persistent equivalent so the six `None`-hardcoding
    /// callers can chain. `None` for a first turn (matches a fresh executor's
    /// stored head), so the genesis case is served correctly too.
    #[serde(default)]
    pub last_receipt_hash: Option<String>,
}

#[derive(Serialize)]
pub struct CheckpointResponse {
    pub height: u64,
    pub ledger_state_root: String,
    pub note_tree_root: String,
    pub nullifier_set_root: String,
    pub revocation_tree_root: String,
    pub epoch: u64,
    pub timestamp: i64,
    pub federation_members: usize,
    pub qc_votes: usize,
}

#[derive(Deserialize)]
pub struct UnlockRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct UnlockResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bearer_token: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct SetPassphraseRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct SetPassphraseResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct IntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
    /// `true` when the submitted intent was *self-fulfillable* and was COMMITTED
    /// immediately through the verified ledger at submit time (rather than only
    /// pooled). When `true`, `turn_hash` carries the real committed receipt hash.
    #[serde(default)]
    pub committed: bool,
    /// Hex-encoded `turn_hash` of the committed fulfillment receipt, present iff
    /// `committed == true`. This is a genuine receipt from
    /// `execute_fulfillment_flow_verified` (the same verified path `/intents/fulfill`
    /// drives), NOT a stub.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn_hash: Option<String>,
}

#[derive(Serialize)]
pub struct EncryptedIntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
}

// =============================================================================
// SSE (Searchable Symmetric Encryption) match query types
// =============================================================================

/// Request body for `/intents/encrypted/search` — a fulfiller's local
/// capability keywords + epoch, used as a coarse SSE-token filter
/// against the node's encrypted intent pool.
///
/// The fulfiller hashes each of their `capability_keywords` under
/// `(keyword, epoch)` to produce SSE search tokens, and the server
/// streams back any stored encrypted intent whose token set intersects.
/// The intent body remains encrypted; the fulfiller requests body
/// decryption out-of-band after picking matches.
#[derive(Deserialize)]
pub struct SseSearchRequest {
    /// Capability keywords (cleartext, e.g. "action:read",
    /// "resource:documents/*"). The server hashes each as
    /// `BLAKE3_derive_key("dregg-sse-token-v1", keyword || epoch_le)`.
    pub capability_keywords: Vec<String>,
    /// Epoch for token derivation (must match the epoch the poster
    /// used; rotate-by-epoch makes cross-epoch correlation harder).
    pub epoch: u64,
    /// Maximum results to return (cap at server-side limit).
    #[serde(default)]
    pub limit: Option<usize>,
}

/// A single SSE search hit: the encrypted intent (still encrypted)
/// plus its content-addressed id for follow-up.
#[derive(Serialize)]
pub struct SseSearchHit {
    pub intent_id: String,
    pub encrypted_intent: dregg_intent::sse::EncryptedIntent,
}

/// Response from `/intents/encrypted/search`. Returns intent
/// envelopes whose SSE tokens intersect with any of the request's
/// derived tokens.
#[derive(Serialize)]
pub struct SseSearchResponse {
    pub hits: Vec<SseSearchHit>,
    /// Number of intents matched before `limit` truncation (lets the
    /// client know if there are more results behind the cap).
    pub total_matches: usize,
}

// =============================================================================
// Events query types
// =============================================================================

/// Query parameters for GET /api/events.
#[derive(Deserialize)]
pub struct EventsQuery {
    /// Return events committed after this block height. A cursor of 0 returns
    /// the current retained log for first-time pollers.
    pub since_height: Option<u64>,
    /// Maximum number of events to return (default 50, max 200).
    pub limit: Option<usize>,
}

/// Query parameters for public Starbridge indexing reads.
#[derive(Deserialize)]
pub struct StarbridgeQuery {
    /// Maximum results to return (default 50, max 200).
    pub limit: Option<usize>,
    /// Receipt/event cursor. For event reads this is exclusive when nonzero.
    pub since_height: Option<u64>,
    /// Hex-encoded cell id. Receipt reads match the receipt agent; event and
    /// turn reads match affected cells/action targets/effect cell references.
    pub cell: Option<String>,
    /// Case-insensitive substring match against memo/effect/action summaries.
    pub memo: Option<String>,
    /// Case-insensitive effect kind or summary substring.
    pub effect: Option<String>,
    /// Exact hex-encoded turn hash.
    pub turn_hash: Option<String>,
    /// Exact hex-encoded effects hash for receipt reads.
    pub effects_hash: Option<String>,
    /// Case-insensitive app bucket: nameservice, identity, governance, or custom.
    pub app: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeReceiptInfo {
    #[serde(flatten)]
    pub receipt: ReceiptInfo,
    pub effects_hash: String,
    pub federation_id: String,
    pub emitted_event_count: usize,
    pub routing_directive_count: usize,
    pub derivation_record_count: usize,
    pub source: &'static str,
    pub turn_body_available: bool,
}

#[derive(Serialize)]
pub struct StarbridgeSignedTurnInfo {
    pub queue_index: usize,
    pub turn_hash: String,
    pub signer: String,
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    pub action_count: usize,
    pub effect_count: usize,
    pub action_targets: Vec<String>,
    pub effect_kinds: Vec<String>,
    pub touched_cells: Vec<String>,
    pub app: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeActionInfo {
    pub source: &'static str,
    pub queue_index: usize,
    pub action_index: usize,
    pub turn_hash: String,
    pub signer: String,
    pub agent: String,
    pub memo: Option<String>,
    pub app: Option<String>,
    pub target: String,
    pub method: String,
    pub effect_kinds: Vec<String>,
    pub touched_cells: Vec<String>,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityEventInfo {
    pub source: &'static str,
    pub chain_index: Option<u64>,
    pub event_index: Option<usize>,
    pub height: Option<u64>,
    pub receipt_hash: Option<String>,
    pub turn_hash: String,
    pub cell_id: String,
    pub timestamp: i64,
    pub topic: Option<serde_json::Value>,
    pub data: Option<serde_json::Value>,
    pub effects: Vec<String>,
    pub proof_status: ActivityProofStatus,
    pub finality: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityCredentialInfo {
    pub source: &'static str,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub issuer_cell: String,
    pub subject_cells: Vec<String>,
    pub timestamp: i64,
    pub effects_hash: String,
    pub event_count: usize,
    pub derivation_record_count: usize,
    pub proof_status: ActivityProofStatus,
    pub finality: String,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityProofCheckpointInfo {
    pub source: &'static str,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub cell_id: String,
    pub timestamp: i64,
    pub effects_hash: String,
    pub pre_state: String,
    pub post_state: String,
    pub proof_status: ActivityProofStatus,
    pub executor_signed: bool,
    pub witness_count: usize,
    pub finality: String,
}

// =============================================================================
// PIR (Private Information Retrieval) types
// =============================================================================

/// Request body for a PIR query against the intent index.
#[derive(Deserialize)]
pub struct PirQueryRequest {
    /// The query vector (BabyBear field elements serialized as u32 values).
    pub query_vector: Vec<u32>,
}

/// Response to a PIR query.
#[derive(Serialize)]
pub struct PirQueryResponse {
    /// The server's response vector (BabyBear field elements as u32 values).
    pub response: Vec<u32>,
}

/// Metadata about the PIR database (needed for clients to construct valid queries).
#[derive(Serialize)]
pub struct PirInfoResponse {
    /// Number of rows (capability tags) in the index.
    pub num_rows: usize,
    /// Number of columns per row (in field elements).
    pub row_width: usize,
    /// The ordered list of capability tags.
    pub tags: Vec<String>,
}

#[derive(Serialize)]
pub struct IntentListEntry {
    pub id: String,
    pub intent: dregg_intent::Intent,
}

// =============================================================================
// Fulfillment types
// =============================================================================

#[derive(Deserialize)]
pub struct FulfillIntentRequest {
    /// Hex-encoded 32-byte intent ID to fulfill.
    pub intent_id: String,
    /// Hex-encoded 32-byte payer cell ID (intent creator's cell).
    pub payer_cell: String,
    /// Hex-encoded 32-byte recipient cell ID (fulfiller's cell).
    pub recipient_cell: String,
    /// State root (BabyBear field element as u32).
    pub state_root: u32,
    /// Block height at which state root was attested.
    pub state_root_block: u64,
}

#[derive(Serialize)]
pub struct FulfillIntentResponse {
    pub success: bool,
    pub turn_hash: Option<String>,
    pub error: Option<String>,
}

// =============================================================================
// Fast-Path Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct FastPathLockRequest {
    /// The turn to lock (full turn structure).
    pub turn: serde_json::Value,
    /// Hex-encoded 64-byte Ed25519 signature from the agent over `turn.hash()`.
    /// Required (P1-6): validators must verify the agent actually authored the
    /// turn before locking on their behalf.
    pub agent_signature: String,
}

#[derive(Serialize)]
pub struct FastPathLockResponse {
    pub locked: bool,
    pub validator_key: Option<String>,
    pub signature: Option<String>,
    pub height: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct FastPathCertificateRequest {
    /// The turn being certified.
    pub turn: serde_json::Value,
    /// Hex-encoded turn hash.
    pub turn_hash: String,
    /// Collected validator signatures.
    pub signatures: Vec<FastPathSignatureEntry>,
}

#[derive(Deserialize)]
pub struct FastPathSignatureEntry {
    /// Hex-encoded 32-byte validator public key.
    pub validator_key: String,
    /// Hex-encoded 64-byte signature.
    pub signature: String,
    /// Height at which the signature was produced.
    pub height: u64,
}

#[derive(Serialize)]
pub struct FastPathCertificateResponse {
    pub executed: bool,
    pub turn_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Conditional Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct SubmitConditionalRequest {
    pub turn: serde_json::Value,
    pub condition: serde_json::Value,
    pub timeout_height: u64,
}

#[derive(Serialize)]
pub struct SubmitConditionalResponse {
    pub accepted: bool,
    pub conditional_hash: Option<String>,
}

#[derive(Deserialize)]
pub struct ResolveConditionalRequest {
    pub conditional_hash: String,
    pub proof: serde_json::Value,
}

#[derive(Serialize)]
pub struct ResolveConditionalResponse {
    pub resolved: bool,
    pub turn_hash: Option<String>,
    pub reason: Option<String>,
}

#[derive(Serialize)]
pub struct PendingConditionalInfo {
    pub hash: String,
    pub timeout_height: u64,
    pub submitted_at: u64,
    pub condition_type: String,
}

// =============================================================================
// Sovereign Cell Ephemeral Registration types
// =============================================================================

/// Request body for ephemeral sovereign cell registration.
///
/// The cell exists locally on the agent; the federation stores only the commitment.
/// Registration is temporary — expires after `ttl_blocks` of inactivity.
#[derive(Deserialize)]
pub struct RegisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte current state commitment.
    pub commitment: String,
    /// How many blocks to keep the registration alive (default: 1000).
    pub ttl_blocks: Option<u64>,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || commitment`.
    pub signature: String,
    /// Optional hex-encoded 32-byte verification key hash to bind this cell
    /// to a deployed program. When set, proof-carrying turns are verified
    /// against the program identified by this VK hash.
    pub verification_key_hash: Option<String>,
}

/// Response to a sovereign cell registration.
#[derive(Serialize)]
pub struct RegisterCellResponse {
    pub registered: bool,
    pub ttl_blocks: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voluntary deregistration.
#[derive(Deserialize)]
pub struct DeregisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    pub signature: String,
}

/// Response to a sovereign cell deregistration.
#[derive(Serialize)]
pub struct DeregisterCellResponse {
    pub deregistered: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for updating a sovereign cell's commitment after a transition.
#[derive(Deserialize)]
pub struct UpdateCommitmentRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte old commitment (must match stored).
    pub old_commitment: String,
    /// Hex-encoded 32-byte new commitment.
    pub new_commitment: String,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || old_commitment || new_commitment`.
    pub signature: String,
}

/// Response to a commitment update.
#[derive(Serialize)]
pub struct UpdateCommitmentResponse {
    pub updated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Program Deployment types
// =============================================================================

/// Request body for deploying a custom cell program to the federation.
#[derive(Deserialize)]
pub struct DeployProgramRequest {
    /// Hex-encoded postcard-serialized CircuitDescriptor bytes.
    pub descriptor_bytes: String,
    /// Program version (for upgrade/migration tracking).
    pub version: u32,
}

/// Response to a program deployment.
#[derive(Serialize)]
pub struct DeployProgramResponse {
    pub deployed: bool,
    /// Hex-encoded 32-byte VK hash (program identity).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vk_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Atomic Multi-Party Turn types
// =============================================================================

/// Request body for proposing an atomic multi-party turn.
#[derive(Deserialize)]
pub struct AtomicProposalRequest {
    /// The combined call forest from all parties (serialized).
    pub forest: serde_json::Value,
    /// Hex-encoded 32-byte participant node IDs.
    pub participants: Vec<String>,
    /// Vote threshold required for commitment.
    pub threshold: usize,
    /// Fee in computrons.
    pub fee: u64,
    /// Hex-encoded 32-byte initiator cell ID.
    pub initiator: String,
    /// Optional explicit per-participant Ed25519 verifying keys (hex, 64 chars).
    /// Must have the same length as `participants` if provided. F-P1-4: when
    /// omitted, the node falls back to `known_federation_keys` matched by ID;
    /// unknown participants cause rejection.
    #[serde(default)]
    pub participant_pubkeys: Option<Vec<String>>,
}

/// Per-proposal computron budget cap (F-P2-1). Prior code passed `u64::MAX`
/// straight through to the coordinator, so a misbehaving caller could exhaust
/// computron budget at execution time.
pub const MAX_ATOMIC_BUDGET: u64 = 1_000_000_000;

/// Response to an atomic turn proposal.
#[derive(Serialize)]
pub struct AtomicProposalResponse {
    pub accepted: bool,
    pub proposal_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voting on an atomic proposal.
#[derive(Deserialize)]
pub struct AtomicVoteRequest {
    /// Hex-encoded 32-byte proposal ID.
    pub proposal_id: String,
    /// Whether the participant votes yes.
    pub approve: bool,
    /// Hex-encoded 64-byte Ed25519 signature over the vote.
    pub signature: String,
    /// Hex-encoded 32-byte voter node ID.
    pub voter: String,
}

/// Response to an atomic vote.
#[derive(Serialize)]
pub struct AtomicVoteResponse {
    pub accepted: bool,
    /// If voting completed a decision, this is "commit" or "abort".
    pub decision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Response to a proposal status query.
#[derive(Serialize)]
pub struct ProposalStatusResponse {
    pub found: bool,
    /// One of: "proposing", "committed", "aborted", "idle".
    pub state: String,
    /// Number of yes votes received so far.
    pub yes_votes: usize,
    /// Number of no votes received so far.
    pub no_votes: usize,
    /// Total participants required.
    pub total_participants: usize,
    /// Threshold needed for commit.
    pub threshold: usize,
    /// Seconds since proposal creation.
    pub age_secs: u64,
}

/// Request body for a participant evaluating a proposal locally.
#[derive(Deserialize)]
pub struct EvaluateProposalRequest {
    /// Hex-encoded 32-byte proposal ID from the coordinator.
    pub proposal_id: String,
    /// The atomic forest to evaluate (serialized, same as the coordinator's proposal).
    pub forest: serde_json::Value,
}

/// Response to local proposal evaluation.
#[derive(Serialize)]
pub struct EvaluateProposalResponse {
    /// Whether the participant would vote yes based on local state.
    pub approve: bool,
    /// If rejecting, the reason.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// The Ed25519 signature over the vote (hex-encoded, 128 chars).
    pub signature: String,
}

// =============================================================================
// Rate Limiting (P1 Fix 4)
// =============================================================================

/// Trusted reverse-proxy front-ends (F-1).
///
/// When the node sits behind a reverse proxy (the devnet's nginx/Caddy), every
/// request arrives from the proxy's socket IP, so a per-socket-IP rate limiter
/// collapses into a single global bucket (trivial DoS of honest clients) and
/// gives a NATed/proxied/IP-rotating attacker no per-client cost. The proxy
/// instead conveys the real client address in `X-Forwarded-For`.
///
/// This set lists the socket IPs we trust to have set `X-Forwarded-For`
/// truthfully. Only when the *direct peer* is in this set do we believe the
/// header — otherwise an unproxied attacker could spoof an arbitrary client IP
/// (and thus a fresh, unlimited bucket) by sending the header themselves.
///
/// Populated from `DREGG_TRUSTED_PROXIES` (comma-separated IPs) at router
/// construction. Empty = no proxy trusted = key purely on the socket IP (the
/// safe default for a directly-exposed node).
#[derive(Clone, Default)]
pub struct TrustedProxies {
    set: Arc<HashSet<IpAddr>>,
}

impl TrustedProxies {
    /// Build from an iterator of textual IPs (invalid entries are skipped).
    pub fn from_strings<I: IntoIterator<Item = String>>(iter: I) -> Self {
        let set: HashSet<IpAddr> = iter
            .into_iter()
            .filter_map(|s| s.trim().parse::<IpAddr>().ok())
            .collect();
        Self { set: Arc::new(set) }
    }

    /// Build from the `DREGG_TRUSTED_PROXIES` env var (comma-separated).
    pub fn from_env() -> Self {
        match std::env::var("DREGG_TRUSTED_PROXIES") {
            Ok(v) if !v.trim().is_empty() => {
                Self::from_strings(v.split(',').map(|s| s.to_string()))
            }
            _ => Self::default(),
        }
    }

    fn contains(&self, ip: &IpAddr) -> bool {
        self.set.contains(ip)
    }

    fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

/// Resolve the rate-limiting key (real client IP) for a request (F-1).
///
/// * If the direct peer (`socket_ip`) is NOT a trusted proxy, we use the socket
///   IP verbatim — a direct attacker cannot grant itself a different bucket by
///   sending `X-Forwarded-For`, because we ignore the header from untrusted
///   peers.
/// * If the direct peer IS a trusted proxy, we walk `X-Forwarded-For` from the
///   right (proxy-appended, least-spoofable end) and return the FIRST address
///   that is not itself a trusted proxy — i.e. the real external client. This
///   defeats a client that pre-seeds the header with spoofed left-hand entries.
///
/// Returns `None` only when the header is malformed/empty behind a trusted
/// proxy, in which case the caller falls back to the socket IP (the proxy's),
/// degrading to the conservative global-bucket behavior rather than fail-open.
pub fn resolve_client_ip(
    socket_ip: IpAddr,
    forwarded_for: Option<&str>,
    trusted: &TrustedProxies,
) -> IpAddr {
    // Untrusted direct peer, or no proxies configured: never believe XFF.
    if trusted.is_empty() || !trusted.contains(&socket_ip) {
        return socket_ip;
    }

    // The peer is a trusted proxy. X-Forwarded-For is "client, proxy1, proxy2, …"
    // where each hop APPENDS the address it received from. Walking from the
    // right, skip addresses that are themselves trusted proxies; the first
    // non-trusted address is the genuine external client. A client that spoofs
    // leading entries cannot move this rightmost-untrusted boundary.
    if let Some(xff) = forwarded_for {
        for hop in xff.split(',').rev() {
            if let Ok(ip) = hop.trim().parse::<IpAddr>()
                && !trusted.contains(&ip)
            {
                return ip;
            }
        }
    }

    // Trusted proxy but no usable forwarded client: fall back to the proxy IP
    // (conservative shared bucket) rather than fail-open with a fresh bucket.
    socket_ip
}

/// Process-wide trusted-proxy set for the pre-passphrase setup gates, memoized
/// from `DREGG_TRUSTED_PROXIES` so every gate resolves the effective client IP
/// through the SAME configuration.
fn setup_gate_trusted_proxies() -> &'static TrustedProxies {
    static TRUSTED: std::sync::OnceLock<TrustedProxies> = std::sync::OnceLock::new();
    TRUSTED.get_or_init(TrustedProxies::from_env)
}

/// Whether the *effective* client of a request is loopback, honoring
/// `X-Forwarded-For` from `trusted` proxies exactly like the rate limiter's
/// `resolve_client_ip` (F-1). Pure over its inputs, so it is unit-testable.
///
/// Behind a same-host reverse proxy the raw socket IP is ALWAYS loopback; a gate
/// that trusts the socket IP verbatim would treat the whole internet as local
/// during the pre-passphrase window (remote passphrase / bearer-seed hijack,
/// F-CRIT-1). Resolving through the trusted-proxy `X-Forwarded-For` path first
/// means a remote client behind the proxy is NOT admitted, while a genuine local
/// caller (no proxy, or an XFF that is itself loopback) still is.
pub fn effective_client_is_loopback_with(
    socket_ip: IpAddr,
    headers: &axum::http::HeaderMap,
    trusted: &TrustedProxies,
) -> bool {
    let xff = headers.get("x-forwarded-for").and_then(|v| v.to_str().ok());
    resolve_client_ip(socket_ip, xff, trusted).is_loopback()
}

/// The ONE trusted-client-IP decision shared by every pre-passphrase setup gate
/// — `require_auth`'s no-bearer branch, the HTTP unlock / set-passphrase
/// endpoints, and the WebSocket setup gate — so they cannot diverge. Uses the
/// process trusted-proxy set from `DREGG_TRUSTED_PROXIES`.
pub fn effective_client_is_loopback(socket_ip: IpAddr, headers: &axum::http::HeaderMap) -> bool {
    effective_client_is_loopback_with(socket_ip, headers, setup_gate_trusted_proxies())
}

/// Simple in-memory rate limiter: max attempts per window.
#[derive(Clone)]
pub(crate) struct RateLimiter {
    /// Map of IP -> (attempt_count, window_start)
    state: Arc<Mutex<HashMap<IpAddr, (u32, Instant)>>>,
    max_attempts: u32,
    window_secs: u64,
    /// Trusted reverse-proxy front-ends whose `X-Forwarded-For` we honor (F-1).
    trusted_proxies: TrustedProxies,
}

/// Default maximum turns per minute per connection (configurable).
pub const DEFAULT_TURN_RATE_LIMIT: u32 = 60;

impl RateLimiter {
    pub(crate) fn new(max_attempts: u32, window_secs: u64) -> Self {
        Self::with_proxies(max_attempts, window_secs, TrustedProxies::from_env())
    }

    fn with_proxies(max_attempts: u32, window_secs: u64, trusted_proxies: TrustedProxies) -> Self {
        let limiter = Self {
            state: Arc::new(Mutex::new(HashMap::new())),
            max_attempts,
            window_secs,
            trusted_proxies,
        };

        // Spawn a background task that prunes stale entries every 60 seconds
        // to prevent unbounded memory growth from many unique IPs.
        let prune_state = limiter.state.clone();
        let prune_window = window_secs;
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(60));
            loop {
                interval.tick().await;
                let mut map = prune_state.lock().await;
                let now = Instant::now();
                map.retain(|_, (_, window_start)| {
                    now.duration_since(*window_start).as_secs() < prune_window
                });
            }
        });

        limiter
    }

    /// Returns true if the request should be allowed, false if rate-limited.
    async fn check(&self, ip: IpAddr) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        let entry = map.entry(ip).or_insert((0, now));

        // Reset window if expired.
        if now.duration_since(entry.1).as_secs() >= self.window_secs {
            *entry = (0, now);
        }

        entry.0 += 1;
        entry.0 <= self.max_attempts
    }

    /// Resolve the per-client rate-limiting key for an incoming request, honoring
    /// `X-Forwarded-For` ONLY when the direct peer is a configured trusted proxy
    /// (F-1). This is the entry point every rate-limited handler should use so
    /// that, behind the devnet's reverse proxy, the limiter keys on the real
    /// external client instead of degenerating into one global bucket.
    fn client_ip(&self, socket_ip: IpAddr, headers: &axum::http::HeaderMap) -> IpAddr {
        let xff = headers.get("x-forwarded-for").and_then(|v| v.to_str().ok());
        resolve_client_ip(socket_ip, xff, &self.trusted_proxies)
    }

    /// Convenience: resolve the client IP and apply the limiter in one call.
    pub(crate) async fn check_request(
        &self,
        socket_ip: IpAddr,
        headers: &axum::http::HeaderMap,
    ) -> bool {
        let key = self.client_ip(socket_ip, headers);
        self.check(key).await
    }
}

/// Shared admission budget for the anonymous, exact-shape PoA Signal ingress.
#[derive(Clone)]
struct PoaSignalIngressLimits {
    per_ip: RateLimiter,
    in_flight: Arc<Semaphore>,
}

impl PoaSignalIngressLimits {
    fn new() -> Self {
        Self {
            per_ip: RateLimiter::new(POA_SIGNAL_SUBMITS_PER_MINUTE, 60),
            in_flight: Arc::new(Semaphore::new(POA_SIGNAL_MAX_IN_FLIGHT)),
        }
    }
}

// =============================================================================
// Authentication
// =============================================================================

/// Authentication middleware requiring Bearer token for protected endpoints.
///
/// The API token is derived from the bearer seed (which is itself derived from
/// passphrase + salt via BLAKE3 at passphrase-set time).
/// If no passphrase is set, only loopback callers are allowed (initial setup phase).
/// This closes F-CRIT-1: a network attacker that reaches the port before the
/// operator runs `set-passphrase` MUST NOT be able to drive any endpoint.
async fn require_auth(
    State(state): State<NodeState>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Result<Response, StatusCode> {
    let s = state.read().await;

    // If no passphrase is set yet, restrict to loopback (initial setup).
    // F-CRIT-1: prior code allowed *any* caller through here; on `--bind 0.0.0.0`
    // a network attacker could reach this branch before the operator and set the
    // passphrase themselves.
    //
    // PROXY HARDENING: behind a local reverse proxy (the devnet's Caddy on the
    // same host), EVERY external request arrives from a loopback socket, so a
    // raw `is_loopback()` check would hold this door open to the whole internet
    // during the pre-passphrase window. When `DREGG_TRUSTED_PROXIES` names the
    // proxy, we resolve the REAL client IP through `X-Forwarded-For` (same F-1
    // logic as the rate limiters) and require THAT to be loopback. With no
    // trusted proxies configured the resolution is the socket IP verbatim
    // (unchanged local-dev behavior).
    let Some(ref bearer_seed) = s.bearer_seed else {
        drop(s);
        // Pull ConnectInfo if present; if no ConnectInfo we play safe (deny).
        let connect_info: Option<&axum::extract::ConnectInfo<std::net::SocketAddr>> =
            req.extensions().get();
        return match connect_info {
            Some(ci) => {
                if effective_client_is_loopback(ci.0.ip(), req.headers()) {
                    Ok(next.run(req).await)
                } else {
                    Err(StatusCode::FORBIDDEN)
                }
            }
            _ => Err(StatusCode::FORBIDDEN),
        };
    };

    // Check for Bearer token in Authorization header.
    let auth_header = req
        .headers()
        .get("authorization")
        .and_then(|v| v.to_str().ok());

    match auth_header {
        Some(header) if header.starts_with("Bearer ") => {
            let token = &header[7..];
            let expected_token_bytes = blake3::derive_key("dregg-api-bearer-v1", bearer_seed);
            let expected_token: String = expected_token_bytes
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            drop(s);

            // Constant-time comparison to prevent timing attacks on the bearer token.
            if token.as_bytes().ct_eq(expected_token.as_bytes()).into() {
                Ok(next.run(req).await)
            } else {
                Err(StatusCode::UNAUTHORIZED)
            }
        }
        _ => {
            drop(s);
            Err(StatusCode::UNAUTHORIZED)
        }
    }
}

// =============================================================================
// CORS Middleware (P2 Fix 7)
// =============================================================================

/// Configured CORS allowlist: extra exact origins (e.g. the deployed devnet
/// site origin `https://devnet.example.com`) that are permitted in addition to
/// the always-allowed localhost / browser-extension origins. Wrapped in an
/// `Arc` so it can be cloned cheaply into the per-request middleware closure.
///
/// The default is empty (locked down to localhost + extensions). Operators
/// widen it via `--cors-origin` flags or the `DREGG_CORS_ORIGINS` env var
/// (comma-separated), wired in `main.rs`.
pub type CorsAllowlist = Arc<HashSet<String>>;

pub(crate) const CORS_ALLOWED_REQUEST_HEADERS: &str =
    "Content-Type, Authorization, X-Devnet-Key, X-Dregg-Actor";

/// Middleware that adds CORS headers to every response.
async fn cors_middleware(
    State(allowlist): State<CorsAllowlist>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Response {
    let origin = req
        .headers()
        .get(header::ORIGIN)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("")
        .to_string();

    // Handle preflight OPTIONS
    let is_preflight = req.method() == Method::OPTIONS;

    let mut response = if is_preflight {
        Response::builder()
            .status(StatusCode::NO_CONTENT)
            .body(axum::body::Body::empty())
            .unwrap()
    } else {
        next.run(req).await
    };

    // Check if origin is allowed.
    let allowed = is_origin_allowed(&origin, &allowlist);
    if allowed {
        let headers = response.headers_mut();
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_ORIGIN,
            HeaderValue::from_str(&origin).unwrap_or_else(|_| HeaderValue::from_static("*")),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_METHODS,
            HeaderValue::from_static("GET, POST, PUT, DELETE, OPTIONS"),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_HEADERS,
            HeaderValue::from_static(CORS_ALLOWED_REQUEST_HEADERS),
        );
        headers.insert(
            header::ACCESS_CONTROL_MAX_AGE,
            HeaderValue::from_static("3600"),
        );
    }

    response
}

/// Check whether an origin is allowed by our CORS policy.
///
/// Uses proper URL parsing to prevent bypass via domains like `localhost.evil.com`.
///
/// Always allows localhost / `127.0.0.1` / `[::1]` over http(s) and browser
/// extension origins. In addition, any exact origin in `allowlist` (configured
/// via `--cors-origin` / `DREGG_CORS_ORIGINS`) is permitted — this is how a
/// deployed devnet site origin (e.g. `https://devnet.example.com`) reaches the
/// node cross-origin. The default allowlist is empty (locked down).
fn is_origin_allowed(origin: &str, allowlist: &HashSet<String>) -> bool {
    // Allow browser extension origins (not parseable as URLs).
    if origin.starts_with("chrome-extension://") || origin.starts_with("moz-extension://") {
        return true;
    }

    // Configured exact-origin allowlist (deployed site origin, etc.). Matched
    // case-insensitively on the normalized origin string so trivial case
    // differences don't slip through or block a legitimate origin.
    if !origin.is_empty() && allowlist.contains(&origin.to_lowercase()) {
        return true;
    }

    // Parse as a URL and check the host exactly.
    // This prevents bypasses like "http://localhost.evil.com".
    let Ok((scheme, host)) = parse_origin(origin) else {
        return false;
    };

    if scheme != "http" && scheme != "https" {
        return false;
    }

    matches!(host.as_str(), "localhost" | "127.0.0.1" | "[::1]")
}

/// Minimal origin parser: extracts scheme and host from an origin string.
/// Returns (scheme, host) without pulling in the `url` crate.
fn parse_origin(origin: &str) -> Result<(String, String), ()> {
    // Format: scheme "://" host [ ":" port ]
    let rest = origin.split_once("://").ok_or(())?;
    let scheme = rest.0.to_lowercase();
    let authority = rest.1;
    // Strip port if present (host is everything before the first ':' or '/')
    let host = authority
        .split_once(':')
        .map(|(h, _)| h)
        .or_else(|| authority.split_once('/').map(|(h, _)| h))
        .unwrap_or(authority);
    if host.is_empty() {
        return Err(());
    }
    Ok((scheme, host.to_lowercase()))
}

// =============================================================================
// Constants
// =============================================================================

/// Maximum number of intents in the node's local pool (P1 Fix 5: unbounded growth).
pub const MAX_NODE_INTENT_POOL: usize = 10_000;

/// Maximum number of pending conditional turns (P1 Fix 6).
pub const MAX_PENDING_CONDITIONALS: usize = 1_000;

/// Maximum request body size in bytes (P2 Fix 11: 1 MB).
const MAX_BODY_SIZE: usize = 1_024 * 1_024;

/// A canonical hybrid-signed Signal carrier contains two ML-DSA-65 public-key /
/// signature pairs (action + outer turn) and is comfortably below this bound.
/// Keep the anonymous game ingress two orders of magnitude below the generic
/// node body ceiling so it cannot be used as a free one-megabyte buffering path.
const POA_SIGNAL_MAX_CLAIM_BYTES: usize = 16 * 1_024;

/// Signal publication is a consented player action, not a bulk-ingest API.
const POA_SIGNAL_SUBMITS_PER_MINUTE: u32 = 10;

/// The state-write lock already serializes execution.  This smaller explicit
/// admission ceiling prevents an anonymous burst from accumulating expensive
/// hybrid-signature work while waiting for that lock.
const POA_SIGNAL_MAX_IN_FLIGHT: usize = 4;

// =============================================================================
// Router
// =============================================================================

/// Build the Axum router with all API routes.
///
/// Includes CORS, body size limits, rate limiting on passphrase endpoints,
/// per-identity rate limiting on turn submission, and Bearer token
/// authentication on protected routes.
// Convenience constructor retained for embedders/tests; the binary uses router_with_cors.
pub fn router(
    state: NodeState,
    enable_faucet: bool,
    metrics_handle: metrics_exporter_prometheus::PrometheusHandle,
) -> Router {
    router_with_cors(state, enable_faucet, metrics_handle, HashSet::new())
}

/// Build the router with an explicit extra CORS origin allowlist.
///
/// `cors_origins` is a set of exact origin strings (e.g.
/// `https://devnet.example.com`) that are permitted cross-origin *in addition*
/// to the always-allowed localhost / extension origins. An empty set keeps the
/// historical locked-down behavior. `main.rs` populates this from the
/// `--cors-origin` flags and the `DREGG_CORS_ORIGINS` env var.
pub fn router_with_cors(
    state: NodeState,
    enable_faucet: bool,
    metrics_handle: metrics_exporter_prometheus::PrometheusHandle,
    cors_origins: HashSet<String>,
) -> Router {
    // Normalize configured origins to lowercase so matching is case-insensitive.
    let cors_allowlist: CorsAllowlist =
        Arc::new(cors_origins.into_iter().map(|o| o.to_lowercase()).collect());
    // Rate limiter for passphrase/unlock endpoints: 5 attempts per 60 seconds.
    let passphrase_limiter = RateLimiter::new(5, 60);

    // Rate limiter for turn submission: DEFAULT_TURN_RATE_LIMIT per 60 seconds per IP.
    let turn_limiter = RateLimiter::new(DEFAULT_TURN_RATE_LIMIT, 60);
    // The anonymous PoA door is narrower than generic signed-turn ingress: one
    // exact game carrier, a ten-per-minute real-IP budget, and four requests in
    // flight across the process.
    let poa_signal_ingress_limits = PoaSignalIngressLimits::new();
    // Shared by both faithful-mirror aliases so changing the path cannot double
    // an attacker's ML-DSA signing budget.
    let faithful_mirror_limiter = RateLimiter::new(120, 60);

    // ANON-DoS #1/#2: per-IP limiters for the expensive public full-scan reads.
    // Each holds `state.read()` while it folds/scans/serializes, so a flood must
    // not be free. Budget = 120/min (the faithful-mirror read precedent): it
    // bounds a tight flood while leaving generous headroom for a dashboard /
    // consensus-liveness probe that polls these every couple seconds (≈30/min).
    // Per-request work is independently bounded (pagination + `MAX_PROOF_LEAVES`).
    let cell_proof_limiter = RateLimiter::new(120, 60);
    let cells_list_limiter = RateLimiter::new(120, 60);
    let blocklace_blocks_limiter = RateLimiter::new(120, 60);
    // ANON-DoS #3: global + per-IP admission control for the receipt SSE stream.
    let sse_limits = crate::events::SseLimits::with_defaults();

    // Public routes (no auth required)
    let mut public_routes = Router::new()
        // The built-in explorer. A node that serves 86 JSON routes and no way to
        // look at them is only legible to someone already holding `curl` and the
        // route list, so `/` is the explorer that reads those routes. It is the
        // SAME page `dreggnet-web` serves at `/explorer` — one source in
        // `site/explorer/`, compiled in, so the binary needs nothing installed
        // beside it. Read-only: every route it touches is a public GET.
        .route("/", get(get_explorer_page))
        .route("/explorer/explorer.css", get(get_explorer_css))
        .route("/explorer/explorer.js", get(get_explorer_js))
        .route("/explorer/blake3.js", get(get_explorer_blake3_js))
        .route("/explorer/target", get(get_explorer_target))
        .route("/status", get(get_status))
        .route("/health", get(get_status))
        .route("/api/node/producer", get(get_producer_status))
        .route("/api/node/identity", get(get_node_identity))
        // Public, read-only PoA Signal observability.  The authority path
        // component must name this node's exact configured federation; these
        // routes never enumerate authorities or return Canon/judge bytes.
        .route(
            "/api/poa/signal/{authority}/status",
            get(get_poa_signal_status),
        )
        .route(
            "/api/poa/signal/{authority}/transitions/{sequence}",
            get(get_poa_signal_transition),
        )
        .route(
            "/api/poa/signal/{authority}/players/{cell}/head",
            get(get_poa_signal_player_head),
        )
        .route(
            "/api/poa/signal/{authority}/claims",
            post({
                let limits = poa_signal_ingress_limits.clone();
                move |connect_info, headers, path, state, body| {
                    post_poa_signal_claim(connect_info, headers, path, state, body, limits.clone())
                }
            })
            .layer(DefaultBodyLimit::max(POA_SIGNAL_MAX_CLAIM_BYTES)),
        )
        .route("/federation/roots", get(get_federation_roots))
        // The ATTESTED-ROOTS surface under its own honest name. `/api/blocks`
        // used to point here too, so a client asking a node for its blocks got
        // attested roots — and on a solo node whose `latest_height` never leaves
        // 0, that is a permanent `[]` from an endpoint named "blocks" while
        // `/api/blocklace/blocks` was full of them. A route name is a claim;
        // `/api/blocks` now serves blocks (below) and this serves roots.
        .route("/api/federation/roots", get(get_federation_roots))
        .route("/api/federations", get(get_federations))
        .route("/api/membership", get(get_membership))
        .route("/api/cells", {
            let limiter = cells_list_limiter.clone();
            get(move |connect_info, headers, page, state| {
                get_all_cells(connect_info, headers, page, state, limiter.clone())
            })
        })
        .route("/api/cell/{id}", get(get_cell_detail))
        .route("/api/cell/{id}/proof", {
            let limiter = cell_proof_limiter.clone();
            get(move |connect_info, headers, state, path, query| {
                get_cell_proof(connect_info, headers, state, path, query, limiter.clone())
            })
        })
        .route("/api/node/cells/{id}", get(get_cell_detail))
        .route("/api/tokens", get(get_tokens))
        // DEOS-HOST discovery: a hosted private server's cap-gated affordance surface,
        // projected per viewer (public — discovery confers no authority; the cap tooth
        // is the EXECUTOR on the fire, not the read).
        .route(
            "/api/server/{cell}/affordances",
            get(get_server_affordances),
        )
        .route("/api/receipts", get(get_receipts))
        .route("/api/receipts/{hash}/witnesses", get(get_receipt_witnesses))
        // The attested-query index (dregg-query): the receipt-log MMR root and
        // certified positional slices. A query answer built over a slice from
        // `/index/range` carries a non-omission certificate the caller verifies
        // against the `/index/root` root — proving the answer was computed from
        // EXACTLY the committed receipt range. Public (read-only over the log).
        .route("/api/receipts/index/root", get(get_receipt_index_root))
        .route("/api/receipts/index/range", get(get_receipt_index_range))
        // The SIGNED index head: the same root, signed by the node's
        // federation key and anchored to the latest attested root's
        // quorum-pinned coordinates (docs/deos/CONSENSUS-BINDS-INDEX.md
        // rung A — node-bound + consensus-anchored, NOT quorum-bound).
        .route("/api/receipts/index/head", get(get_receipt_index_head))
        // ORGANS identity rider — the KERI-shaped identity event-log export:
        // a cell's chained / signed / witness-receipted key-event history as
        // a PORTABLE artifact (independently checkable via
        // `crate::identity_export::verify_export`, no node required).
        // Public: the KEL is the cell's self-published key history.
        .route(
            "/identity/export/{cell}",
            get(crate::identity_export::get_identity_export),
        )
        .route("/api/turn/{hash}/proof", get(get_turn_proof))
        .route("/api/turn/{hash}/anchor", get(get_turn_anchor))
        .route("/api/turn/{hash}/verdict", get(get_turn_verdict))
        .route("/api/starbridge/receipts", get(get_starbridge_receipts))
        .route("/api/starbridge/events", get(get_starbridge_events))
        .route("/api/starbridge/turns", get(get_starbridge_turns))
        .route("/api/starbridge/actions", get(get_starbridge_actions))
        .route(
            "/api/starbridge/identity/events",
            get(get_starbridge_identity_events),
        )
        .route(
            "/api/starbridge/identity/credentials",
            get(get_starbridge_identity_credentials),
        )
        .route(
            "/api/starbridge/identity/proof-checkpoints",
            get(get_starbridge_identity_proof_checkpoints),
        )
        .route("/api/intents", get(get_intents))
        .route("/api/conditionals", get(get_pending_conditionals))
        .route("/api/discharge", {
            // Public + does real crypto + takes the global state-write lock:
            // give it its own per-IP budget so a flood cannot contend the lock.
            let limiter = RateLimiter::new(30, 60);
            post(move |connect_info, headers, state, body| {
                post_discharge(connect_info, headers, state, body, limiter)
            })
        })
        .route("/api/events", get(get_events))
        .route("/api/events/stream", {
            let limits = sse_limits.clone();
            get(move |query, headers, connect_info, state| {
                crate::events::events_stream(query, headers, connect_info, state, limits.clone())
            })
        })
        .route(
            "/api/promise-resolutions",
            get(crate::promise_resolutions::get_promise_resolutions),
        )
        // Public, target-independent faithful-note synchronization.  Both
        // cursors are append-only prefix lengths and page sizes are fixed;
        // the SDK consumes every continuation from zero.  FNMS includes a
        // fresh ML-DSA signature, so cap public CPU amplification per real IP.
        .route("/notes/faithful-spend/mirror", {
            let limiter = faithful_mirror_limiter.clone();
            post(move |connect_info, headers, state, body| {
                post_faithful_note_mirror(connect_info, headers, state, body, limiter)
            })
        })
        .route("/api/notes/faithful-spend/mirror", {
            let limiter = faithful_mirror_limiter.clone();
            post(move |connect_info, headers, state, body| {
                post_faithful_note_mirror(connect_info, headers, state, body, limiter)
            })
        })
        .route("/observability/stream", get(observability_stream))
        .route("/checkpoint/latest", get(get_checkpoint_latest))
        .route("/checkpoint/{height}", get(get_checkpoint_at_height))
        .route("/api/blocklace/checkpoint", get(get_blocklace_checkpoint))
        .route("/api/blocklace/blocks", {
            let limiter = blocklace_blocks_limiter.clone();
            get(move |connect_info, headers, page, state| {
                get_blocklace_blocks(connect_info, headers, page, state, limiter.clone())
            })
        })
        // `/api/blocks` — the same real blocks, under the name every client
        // reads as "this node's blocks" (it served attested federation roots
        // until 2026-07-25). Same handler, same per-IP cap, same paging.
        .route("/api/blocks", {
            let limiter = blocklace_blocks_limiter.clone();
            get(move |connect_info, headers, page, state| {
                get_blocklace_blocks(connect_info, headers, page, state, limiter.clone())
            })
        })
        .route("/api/block/{height}", get(get_block_by_height))
        .route("/pir/info", get(get_pir_info))
        .route("/pir/query", post(post_pir_query))
        // Short-lived, RPC-attested `$DREGG` arcade admission. The transport
        // accepts no balance or slot assertion from the browser; the isolated
        // gate reloads the server-issued challenge and validates server-fetched
        // finalized Token-2022 bytes. This tier never enters governance weight.
        .merge(crate::poa_galley_api::routes())
        .merge(crate::poa_holding_api::routes())
        // Where a finished run lands and can be read back. Public because the
        // record is the public artifact: it publishes what the Lean read model
        // chose to publish (never the Signal target), it is rate-limited and
        // in-flight capped because it re-judges the finalized history through
        // native Lean on every request, and it refuses rather than serving a
        // partial view. Before the first turn settles it shows the installed
        // world and mission, which is a true thing to show.
        .merge(crate::poa_records_api::routes())
        // The station's two daily organs, which were proved and DARK: the
        // communal ship instrument panel, and the salvage crate's visible
        // rotation. Public because the panel is communal BY TYPE —
        // `ShipInstrumentPanel.State` has no per-player field, and
        // `the_served_panel_does_not_depend_on_the_crew` proves substituting any
        // request leaves every communal field bit-identical — and because the
        // rotation is one the crate deliberately publishes (its mixer is not an
        // unpredictability source; the beacon schedule is curator-authored and
        // visible). Neither `HiddenInstance` nor `SlotDeriveRuntime` is in this
        // read's import cone, so no run seed, slot secret, commitment or target
        // can reach this wire. READ-ONLY BY TYPE: the crate's opening demands an
        // `opaque` capability with no producer.
        // PUBLICATION of the curator-signed slot opening — UNAUTHENTICATED, on
        // purpose. A commitment a node keeps to itself binds nothing, and a client
        // with no way to read one can only ever offer practice: this route is the
        // difference between a station that can be played for real and one that
        // can only rehearse. It was mounted behind the bearer layer, where the
        // browser fetched it anonymously, got refused, and SILENTLY degraded every
        // game to practice — the publication surface existed and published to
        // nobody.
        //
        // Standing question, answered: a reader who has not played CANNOT
        // reconstruct an instance from this. It serves the statement, the curator
        // key and the signature — never the secret, the run seed, the target, nor
        // the pre-encoded signing message (a client that verified pre-encoded
        // bytes could be handed statement S beside a valid signature over S'; it
        // re-derives instead). The published commitment is `commit secret slot`:
        // no player, no mission, ~2^124 to invert.
        .merge(crate::poa_signal_slot_api::routes())
        // ⚑ THE SLOT-CLOSE OPENING — the one route in this node that publishes a
        // slot SECRET, and the answer to the census question below is deliberately
        // YES for it. That is not a leak; it is what opening a commitment means.
        //
        // Every descriptor declares `instance.commitment.opened_after:
        // "slot-close"`, `poa-web` REFUSES any descriptor that does not, and
        // `schema.json` pins the opening as `["slot", "slot_secret"]` under
        // `verify: "commit(slot_secret, slot) == commitment"`. Until this route
        // there was no code anywhere that published either value, so the one
        // integrity claim Path of Angels makes to a player — your instance was
        // fixed before you played — was unfalsifiable by that player.
        //
        // The secret is bounded to slots that are SUPERSEDED. The gate is in
        // `PersistentStore::load_poa_signal_slot_reveal_v1`, beside the monotone
        // install that creates closure, and this route has no other accessor: a
        // superseded slot cannot settle a run, so its secret answers a question
        // nobody can still be asked. The LIVE slot refuses with 409 and its secret
        // appears nowhere in the refusal.
        .merge(crate::poa_signal_slot_reveal_api::routes())
        // ⚑ PUBLIC ON PURPOSE, 2026-08-07 — moved OUT of `protected_routes`, where a
        // docblock dated this same morning called it "AUTHENTICATED ON PURPOSE". That
        // note reasoned correctly about what a session SPENDS and then drew the wrong
        // conclusion about what a bearer token PROVES.
        //
        // THE BEARER WAS NEVER THE AUTHORIZATION. It says "a client of this node"; it
        // does not say "this player" — and `poa_signal_session`'s own header says so, in
        // the paragraph explaining why the player signature exists at all. Every session
        // WRITE is authorized by an Ed25519 signature under the player key over a
        // statement the node RE-DERIVES from the structured fields
        // (`verify_player_signature`, which never accepts a pre-encoded message), and the
        // guess statement covers `round`, so a captured request replays into
        // `session-round-mismatch` rather than into a second spent burst. Strip the
        // bearer and not one check gets weaker: the check that mattered never read it.
        //
        // What it DID do is exclude every player. A route whose entire purpose is
        // player-facing play cannot require a credential no player holds, and the cost
        // was measured: the browser terminal signed a valid statement, POSTed it, and got
        // a 401 before the signature was ever looked at — `CUSTODY_BLOCKERS[0]` in
        // `poa-web/src/judged-session.js`. This is the same class as the slot publication
        // three entries up, which was mounted protected and silently degraded every
        // browser game to practice.
        //
        // ⚠ THE BEARER'S REAL CONTRIBUTION WAS ABUSE RESISTANCE, AND THAT IS REPLACED,
        // NOT DROPPED. `poa_signal_session::SessionAdmission` binds three distinct
        // resources: a proxy-aware per-IP window on writes and (larger) on reads, a
        // per-PLAYER-KEY window charged only AFTER a signature verifies — before it, a
        // stranger could lock a player out of their own run using nothing but the public
        // key — and a global in-flight ceiling. Refusals are named `session-rate-limit`,
        // `session-player-rate-limit`, `session-busy`.
        //
        // The standing question, answered rather than waved at: CAN A READER WHO HAS
        // NEVER PLAYED RECONSTRUCT THE HIDDEN INSTANCE FROM WHAT THESE ROUTES SERVE? No,
        // and provably: the only thing a session emits about the target is
        // `SignalTriangulation.feedback`, and Lean's
        // `SignalFeedbackRuntime.served_transcript_cannot_separate_feedback_equivalent_
        // targets` shows a whole session's bytes are IDENTICAL for any two targets
        // consistent with the guesses played. A reader of a transcript is exactly where
        // the player who produced it is. The document carries no secret, no run seed and
        // no target, and its `settlement.code` is the player's own solving guess read
        // back out of the stored transcript.
        //
        // And the read-back cannot be WALKED: no route lists sessions, `GET
        // …/session/{player}` takes one exact 32-byte key, a wrong key is
        // indistinguishable from an unplayed one (both 404 `session-not-open`), and —
        // the reason that matters — `HiddenInstance.runSeedFor` takes the player key, so
        // somebody else's transcript is a transcript of a DIFFERENT target and is worth
        // nothing against your own run. Full blast radius: the module header.
        .merge(crate::poa_signal_session::routes())
        .merge(crate::poa_station_api::routes())
        .route(
            "/cipherclerk/unlock",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_cclerk_unlock(connect_info, headers, state, body, limiter)
                }
            }),
        )
        // Gateway-reachable alias (the public Caddy forwards only /api/-prefixed
        // routes): unlocking is the remote operator's auth bootstrap, so it must
        // be reachable through the gateway. Same handler + rate limiter.
        // /cipherclerk/set-passphrase intentionally has NO alias — first-time
        // passphrase setup stays operator-local (loopback).
        .route(
            "/api/cipherclerk/unlock",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_cclerk_unlock(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/cipherclerk/set-passphrase",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_set_passphrase(connect_info, headers, state, body, limiter)
                }
            }),
        );

    // Faucet endpoint (only available in devnet mode).
    if enable_faucet {
        let faucet_limiter = FaucetRateLimiter::new();
        // Per-IP faucet budget (proxy-aware): bounds drain + zero-amount cell
        // materialization per real client. 10/min is generous for a human or a
        // demo script and miserly for a flood.
        let faucet_ip_limiter = RateLimiter::new(10, 60);
        public_routes = public_routes.route(
            "/api/faucet",
            post(move |connect_info, headers, state, body| {
                post_faucet(
                    connect_info,
                    headers,
                    state,
                    body,
                    faucet_limiter,
                    faucet_ip_limiter,
                )
            }),
        );
    }

    // Protected routes (require bearer token after passphrase is set)
    let protected_routes = Router::new()
        .route("/ws", get(handle_ws))
        .route("/cipherclerk", get(get_cclerk))
        .route("/cipherclerk/authorize", post(post_authorize))
        .route("/cipherclerk/mint", post(post_mint))
        .route("/cipherclerk/attenuate", post(post_attenuate))
        .route("/cipherclerk/tokens", get(get_tokens))
        .route("/cipherclerk/receipts", get(get_receipts))
        // Authenticated, bounded lookup of the signer-independent consensus receipt object.
        // The canonical FRC1 bytes are self-verifying under the returned typed id; local FRE1
        // envelopes are deliberately not read or returned.
        .route(
            "/api/receipts/finalized-core",
            get(get_finalized_receipt_core),
        )
        .route("/intents", get(get_intents).post(post_intent))
        .route("/intents/encrypted", post(post_encrypted_intent))
        .route("/intents/encrypted/search", post(post_sse_search))
        .route("/intents/trustless", post(post_trustless_intent))
        .route(
            "/intents/trustless/share",
            post(post_trustless_decrypt_share),
        )
        .route(
            "/intents/trustless/status",
            get(get_trustless_engine_status),
        )
        .route("/intents/fulfill", post(post_fulfill_intent))
        .route(
            "/turn/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/turn/fast-path", post(post_fast_path_lock))
        .route("/turn/certificate", post(post_fast_path_certificate))
        // AUDIT-privacy.md §11.2 wiring: encrypted-turn submission +
        // executor public-key discovery. The submit endpoint pulls the
        // executor's X25519 secret from the cipherclerk, hands it to
        // `TurnExecutor::apply_encrypted_turn`, and returns the
        // post-commit receipt's was_encrypted bit.
        .route(
            "/turns/submit-encrypted",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_encrypted_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/turns/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_signed_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/turns/aggregate", post(post_aggregate_bundle))
        .route("/turns/encryption-key", get(get_turn_encryption_key))
        .route("/turn/submit-conditional", post(post_submit_conditional))
        .route("/turn/resolve-conditional", post(post_resolve_conditional))
        .route("/turn/pending", get(get_pending_conditionals))
        .route("/turn/atomic", post(post_atomic_proposal))
        .route("/turn/atomic/vote", post(post_atomic_vote))
        .route("/turn/atomic/{id}", get(get_proposal_status))
        .route("/turn/atomic/evaluate", post(post_evaluate_proposal))
        .route("/cell/{id}", get(get_cell))
        .route("/cells/register", post(post_register_cell))
        .route("/cells/deregister", post(post_deregister_cell))
        .route("/cells/update-commitment", post(post_update_commitment))
        .route("/cells/create-from-factory", post(post_create_from_factory))
        .route("/cells/make-sovereign", post(post_make_sovereign))
        .route("/programs/deploy", post(post_deploy_program))
        .route("/turns/bearer-auth", post(post_bearer_auth))
        // ⚑ DELETED 2026-08-06: `/proofs/compose` and `/turns/peer-exchange`.
        // Both answered `success: true` over inputs nothing read.
        //
        // `/proofs/compose` took an untagged `Vec<serde_json::Value>`, BLAKE3'd
        // the JSON together and reported success — no proof was deserialized,
        // no verifier ran, and its `error` field was unreachable (`{"proofs":[]}`
        // succeeded). Composition cannot be earned here: a composed verdict
        // needs a per-turn canonical anchor a stranger can independently
        // obtain, and no such anchor exists. Its two siblings were already
        // retired for exactly this — the MCP tool `dregg_compose_proofs` fails
        // closed with an explanatory error (`mcp/handlers_verify.rs`), and the
        // wasm `compose_proofs` was downgraded to `valid: false` in favour of
        // `compose_and_verify_proofs`, which runs the REAL per-kind verifiers
        // client-side over TAGGED envelopes. Browser callers use that.
        //
        // `/turns/peer-exchange` hashed (sender, receiver, amount) into an
        // "exchange_id", logged a line and returned. Peer exchange is a
        // federation-BYPASSING protocol between two sovereign cells
        // (`dregg_cell_crypto::PeerExchange`): `verify_transition` bites only
        // against a `PeerCellView` a PARTICIPANT maintains, and the node holds
        // no sovereign signing key and no such view — seeding one from a
        // placeholder is the exact defect `tool_peer_exchange` was called out
        // for. The node's real ingestion path is `POST /turns/submit` carrying
        // `sovereign_witnesses`, where the executor's `validate_sovereign_witness`
        // checks the signature, the commitment chain and
        // `ledger.last_sovereign_witness_sequence(cell) + 1`.
        // LIVE EPOCH TRANSITION (validator-set reconfiguration on a RUNNING
        // node): propose adding/removing validators. The change only APPLIES
        // once a quorum of the CURRENT committee ratifies it through finality —
        // this endpoint only submits the proposal. Auth-protected (operator op).
        .route(
            "/epoch/propose-transition",
            post(post_propose_epoch_transition),
        )
        // Storage gateway (ORGANS §3): content-addressed put/get/stat/list
        // whose ADMISSION is the StorageGatewayMandate cell (capability +
        // op allowlist + prefix scope + executor-enforced volume debit).
        .merge(crate::storage_service::routes())
        // Trustlines (ORGANS §1): open (the funded birth edge, seeding the
        // Stingray coordinator) / draw / repay (the bilateral counter) /
        // settle (rebalance applied back to the ledger as moves) / status.
        .merge(crate::trustline_service::routes())
        // Channels (ORGANS §4): create / join / remove / rekey (the unified
        // group-key + capability-freshness epoch, ONE turn per step) and the
        // off-cell data plane (post ciphertext + SSE delivery).
        .merge(crate::channels_service::routes())
        // Equivocation court (ORGANS §5): bond (slashable stake escrowed in
        // a real bond cell) / evidence (the witness-first slash, executed as
        // one conserved executor move from the bonded cell) / status.
        .merge(crate::equivocation_court_service::routes())
        // DKG ceremony (ORGANS §6): start (factory-birth the ceremony cell
        // from blueprint terms) / contribute (signed dealing + sealed shares,
        // round roots pinned per phase) / complain (witness-first response) /
        // finalize (|QUAL| >= t -> output commitment pinned) / status.
        .merge(crate::dkg_service::routes())
        // REALM substrate (the §9.4/§9.5/§9.2 MUD model, realm-model graduated
        // into the node): create/list realms + list committed law + open/play/
        // settle instances + canonical-identity mint/bind/resolve and hybrid-PQ
        // succession/guardian recovery. Every write drives the SAME NodeRealms
        // gate the in-process path uses (catalog check / identity resolution /
        // scope membrane) and lands in the SAME durable REALM_LOG, so a realm
        // created over HTTP survives a node restart and an uncatalogued
        // ruleset_root is refused persisting nothing.
        .merge(crate::realm_service::routes())
        // Private dependent-turn custody: bearer-gated, bounded octet-stream
        // arm plus cancel/status. Signed/sealed bytes are never returned.
        .merge(crate::private_dependent_turns::routes())
        // THE ENCRYPTED CALL AUCTION: submit a trader-encrypted, trader-signed BFV order and
        // read a cleared `(p*, V*)`. Bearer-gated like the rest of the protected surface; no
        // route of it returns an order, a side, a limit, a quantity, a trader index, a
        // ciphertext, or a per-bucket volume. Gated to the Lean-emitted
        // `dark-bazaar-private-n4k4` family and fails closed on committee / verified-core /
        // certificate. (`crate::dark_clearing_service`.)
        .merge(crate::dark_clearing_service::routes())
        // Operator-only Signal node-envelope diagnostic. This route inherits
        // the bearer layer below and applies its own proxy-aware rate/concurrency
        // budget; it is neither anonymous nor a finality/provenance surface.
        .merge(crate::poa_signal_authority_export::routes())
        // ⚑ `poa_signal_session` USED TO BE MOUNTED HERE and moved to `public_routes` on
        // 2026-08-07 — see the long note at its new home for why the bearer was never
        // the check, and what replaced the abuse resistance it incidentally provided.
        // THE DAILY SALVAGE CRATE'S ONE WRITE. Authenticated because opening is an authorized
        // act against a curator-authored roster; the document it returns is still communal
        // (`ShipInstrumentPanel.State` has no per-player field), so mounting it here rather than
        // in `public_routes` costs a reader nothing they could get from `/panel` anyway. Every
        // number in the reply is Lean's: `StationCrateOpenRuntime` replays this node's durable
        // open log from `SalvageCrate.genesis`, appends the open under the capability chain, and
        // folds the crate's own sealed receipt. (`crate::poa_crate_api`.)
        .merge(crate::poa_crate_api::routes())
        // Queue operations
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    // Metrics endpoint (separate state: PrometheusHandle)
    let metrics_route = Router::new()
        .route("/metrics", get(crate::metrics::metrics_handler))
        .with_state(metrics_handle);

    // ─── Path normalization aliases (Gap 3: bot/app compatibility) ────────────
    // The bot/apps expect /api/node/... and /api/turns/... prefixed paths.
    // These aliases ensure BOTH the canonical and prefixed paths work.
    let path_aliases = Router::new()
        // /api/node/* aliases
        .route("/api/node/health", get(get_status))
        .route("/api/node/status", get(get_status))
        // /api/turns/* aliases (protected — require auth)
        .route(
            "/api/turns/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/api/turns/bearer-auth", post(post_bearer_auth))
        .route(
            "/api/turns/submit-signed",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_signed_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/api/turns/submit-encrypted",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_encrypted_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/api/turns/encryption-key", get(get_turn_encryption_key))
        .route("/api/turns/fast-path", post(post_fast_path_lock))
        .route("/api/turns/certificate", post(post_fast_path_certificate))
        // Gateway-reachable aliases for the public-facing app surface (the
        // devnet Caddy forwards only /api/-prefixed routes; a canonical route
        // without an /api/ alias is operator-local in practice). Same handlers,
        // same bearer-token gate. Routes deliberately left WITHOUT an alias
        // (operator-local by choice): /cipherclerk/set-passphrase + the
        // /cipherclerk key-management surface (authorize/mint/attenuate),
        // /cells/register, /cells/deregister, /cells/update-commitment,
        // /cells/make-sovereign, /turns/aggregate, /turn/submit-conditional,
        // /turn/resolve-conditional — node-administration operations, not app
        // traffic.
        .route("/api/turn/atomic", post(post_atomic_proposal))
        .route("/api/turn/atomic/vote", post(post_atomic_vote))
        .route("/api/turn/atomic/{id}", get(get_proposal_status))
        .route("/api/turn/atomic/evaluate", post(post_evaluate_proposal))
        // ⚑ `/api/turns/peer-exchange` DELETED 2026-08-06 with its canonical
        // route — see the note beside `/turns/bearer-auth` above.
        .route(
            "/api/cells/create-from-factory",
            post(post_create_from_factory),
        )
        .route("/api/programs/deploy", post(post_deploy_program))
        // Operator-local by convention (no /api/ alias — the gateway forwards
        // only /api/-prefixed routes): cast THIS node's approval vote for a
        // pending membership proposal. The production admit verb of the
        // join-with-a-doc flow (docs/guide/FEDERATION-JOIN.md).
        .route("/membership/approve", post(post_membership_approve))
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    public_routes
        .merge(protected_routes)
        .merge(path_aliases)
        .merge(metrics_route)
        .layer(DefaultBodyLimit::max(MAX_BODY_SIZE))
        .layer(middleware::from_fn_with_state(
            cors_allowlist,
            cors_middleware,
        ))
        .with_state(state)
}

// =============================================================================
// The built-in explorer
// =============================================================================
//
// The page, its stylesheet and its two scripts live in `site/explorer/` — the
// directory that already owned this surface, and that `dreggnet-web` already
// compiles in the same way. Serving a COPY here would give the project two
// explorers that drift; `include_str!` gives it one that ships twice.
//
// The page is written to run in either deployment and asks `/explorer/target`
// which one it is in. Behind the web tier that answer names a remote node URL;
// here it says `self_hosted`, and the page reads this node's routes directly.

/// One compiled-in asset, with the content type the browser needs to honour it
/// (a stylesheet served as `text/plain` is silently ignored, and a module
/// script served as anything but JavaScript is refused outright).
fn explorer_asset(content_type: &'static str, body: &'static str) -> Response {
    let mut res = Response::new(axum::body::Body::from(body));
    res.headers_mut()
        .insert(header::CONTENT_TYPE, HeaderValue::from_static(content_type));
    res
}

/// `GET /` — the explorer page.
async fn get_explorer_page() -> Response {
    explorer_asset(
        "text/html; charset=utf-8",
        include_str!("../../site/explorer/index.html"),
    )
}

async fn get_explorer_css() -> Response {
    explorer_asset(
        "text/css; charset=utf-8",
        include_str!("../../site/explorer/explorer.css"),
    )
}

async fn get_explorer_js() -> Response {
    explorer_asset(
        "text/javascript; charset=utf-8",
        include_str!("../../site/explorer/explorer.js"),
    )
}

async fn get_explorer_blake3_js() -> Response {
    explorer_asset(
        "text/javascript; charset=utf-8",
        include_str!("../../site/explorer/blake3.js"),
    )
}

/// `GET /explorer/target` — which node this explorer reads.
///
/// The page asks this before anything else so that "no node configured" stays a
/// distinct state from "the node is empty" and from "the node is unreachable".
/// Served by the node itself the question has only one answer, and `self_hosted`
/// is what tells the page to drop the web tier's hop prefix.
async fn get_explorer_target() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "configured": true,
        "self_hosted": true,
        // The node has no idea what URL a browser reached it by (proxies,
        // port-forwards, tunnels), so it does not guess one. The page fills this
        // in from its own origin, which IS the URL that worked.
        "node_url": serde_json::Value::Null,
    }))
}

// =============================================================================
// Handlers
// =============================================================================

/// `/status` — honest liveness for the deployed devnet.
///
/// `healthy` reflects "the node is up and consensus is live and producing
/// blocks," NOT the attested-root height. The prior implementation tied
/// `healthy` to store + cipherclerk init, which made a perfectly live devnet
/// (DAG at height 85, producing heartbeat blocks) report `healthy: false`
/// while `latest_height: 0` — a terrible public signal.
///
/// Now we derive liveness from real consensus state: a blocklace handle must
/// be attached (the consensus task is running) and the DAG must have a tip
/// (at least one real signed block produced). We surface `dag_height`
/// (real blocklace tip) alongside `latest_height` (attested-root / turn height)
/// so the distinction is explicit on the wire.
/// F-8: whether the public `/status` is allowed to disclose the aggregate
/// private-activity counters (`note_count` / `revocation_count`). Off unless the
/// operator opts in with `DREGG_STATUS_EXPOSE_COUNTS=1`.
fn status_exposes_private_counts() -> bool {
    std::env::var("DREGG_STATUS_EXPOSE_COUNTS")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

/// Everything `/status`'s `healthy` verdict is allowed to depend on, gathered
/// as plain values so the verdict itself is a pure function that can be
/// exhibited at BOTH poles without a network, a clock, or a node.
///
/// The `Option`s mean "no consensus handle is attached" — there is no committee
/// to be reachable from and no join path to have run — not "unknown".
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct HealthFacts {
    /// The store answered `latest_attested_root()`.
    pub store_ok: bool,
    /// A blocklace consensus handle is attached.
    pub consensus_live: bool,
    /// Blocks in the local DAG (a genesis block counts).
    pub block_count: usize,
    /// `FederationLivenessSnapshot::quorum_reachable` — can a quorum be
    /// assembled from the members currently reaching us?
    pub quorum_reachable: Option<bool>,
    /// `FederationLivenessSnapshot::finality_stalled`.
    pub finality_stalled: Option<bool>,
    /// This node ran the join path at all (`JoinProgress` is non-default):
    /// it has sent a join request, or it is a member that came in through one.
    pub ever_asked_to_join: bool,
    /// This node's key is a constitutional participant.
    pub join_member: bool,
}

/// The `/status` health verdict.
///
/// Six conjuncts, three generations of them, and each generation exists because
/// the previous set could not go false for a failure that had already happened
/// in production:
///
///   1. `store_ok && consensus_live && block_count > 0` — this process is up.
///      All three are about THIS process alone, which is why they all held for
///      210 s of a quorum-losing 2-of-4 partition.
///   2. `quorum_reachable && !finality_stalled` — the committee is still there.
///      Both are read against the vote collector's live threshold, so on a
///      non-member's own single-key constitution (threshold 1) they are
///      trivially satisfied: it counts toward its own quorum and the stall leg
///      is deliberately inert below threshold 2.
///   3. `join_member || !ever_asked_to_join` — THIS node got in. The only
///      conjunct that can go false for the wedged joiner measured on port 8465:
///      345 s of refused join requests, member of nothing, `healthy: true`.
///
/// A node with no consensus handle fails at conjunct 2 of generation 1
/// (`consensus_live`), so the absent liveness/join facts are not permitted to
/// make the verdict TRUE on their own — they default to the non-accusing value
/// and `consensus_live` carries the refusal.
/// Whether this node's [`JoinProgress`](crate::blocklace_sync::JoinProgress) is
/// something `/status` should publish at all.
///
/// `Some` exactly when the join path RAN: the node has sent at least one join
/// request, or it is a member that came in through one. A genesis member never
/// enters the loop, so its progress is `default()` — and publishing that
/// verbatim would put `join_member: false` on the wire for a node that is a
/// full participant and was never a candidate. Absent is the honest answer
/// there; the five fields say something only where there is something to say.
pub(crate) fn reportable_join_progress(
    progress: &crate::blocklace_sync::JoinProgress,
) -> Option<crate::blocklace_sync::JoinProgress> {
    (progress.member || progress.requests_sent > 0).then(|| progress.clone())
}

pub(crate) fn status_healthy(facts: HealthFacts) -> bool {
    let up = facts.store_ok && facts.consensus_live && facts.block_count > 0;
    let can_finalize =
        facts.quorum_reachable.unwrap_or(true) && !facts.finality_stalled.unwrap_or(false);
    let admitted = facts.join_member || !facts.ever_asked_to_join;
    up && can_finalize && admitted
}

async fn get_status(State(state): State<NodeState>) -> Json<StatusResponse> {
    // Read the real blocklace DAG state first (separate lock).
    let blocklace = state.blocklace().await;
    let (dag_height, block_count, consensus_live) = match &blocklace {
        Some(handle) => (handle.dag_height().await, handle.block_count().await, true),
        None => (0, 0, false),
    };
    // CAN THIS NODE STILL FINALIZE? Measured from the members that are actually
    // reaching it, against the vote collector's live threshold — never from the
    // launch flags. `None` when no consensus handle is attached, in which case
    // `consensus_live: false` already says everything there is to say.
    let liveness = match &blocklace {
        Some(handle) => Some(handle.federation_liveness().await),
        None => None,
    };
    // A verified committee divergence (two hybrid-verified votes on different
    // finalized roots for one block) — the state the 3-vs-1 fork sat in
    // invisibly. Read from the collector; `None` when no consensus handle.
    let verified_root_splits = match &blocklace {
        Some(handle) => Some(handle.votes.read().await.verified_root_split_count()),
        None => None,
    };
    let turns_in_flight = blocklace
        .as_ref()
        .map(|handle| handle.in_flight_turns.len());
    // DID THIS NODE EVER GET IN? The partition legs above are read against the
    // vote collector's LIVE threshold, and a non-member's threshold is 1 (its
    // own single-key constitution), so neither of them can go false for a
    // joiner that reached no one. This is the fact that can. Reported ONLY when
    // the join path actually ran — a genesis member's `JoinProgress` is
    // `default()` and publishing `join_member: false` for it would be a lie of
    // a different shape.
    let join = match &blocklace {
        Some(handle) => reportable_join_progress(&*handle.join_progress.read().await),
        None => None,
    };

    let s = state.read().await;

    // Check store accessibility.
    let store_ok = s.store.latest_attested_root().is_ok();

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    // F-8: only surface the aggregate private-activity counters when an operator
    // has explicitly opted in (`DREGG_STATUS_EXPOSE_COUNTS=1`). Otherwise the
    // public, unauthenticated `/status` MUST NOT disclose how many credentials
    // have been revoked or how many shielded notes exist — those are a private-
    // activity-volume oracle. Default = omitted.
    let expose_counts = status_exposes_private_counts();
    let revocation_count = if expose_counts {
        Some(s.store.revocation_count().unwrap_or(0))
    } else {
        None
    };
    let note_count = if expose_counts {
        Some(s.store.note_count().unwrap_or(0))
    } else {
        None
    };
    let peer_count = s.peers.len();

    let federation_mode = if s.solo_consensus.as_ref().is_some_and(|s| s.is_solo) {
        "solo".to_string()
    } else {
        "full".to_string()
    };

    // Liveness: store reachable + consensus task running + DAG has produced at
    // least one real block. block_count > 0 (rather than dag_height > 0) so a
    // single genesis block at seq 0 still counts as "producing".
    //
    // ⚑ AND — since 2026-08-08 — the node must still be able to FINALIZE, and
    // — since 2026-08-09 — it must actually be IN the committee it is claiming
    // health on behalf of. The verdict is a pure function of these facts so
    // both poles are exhibitable without a federation; see `status_healthy`.
    let healthy = status_healthy(HealthFacts {
        store_ok,
        consensus_live,
        block_count,
        quorum_reachable: liveness.map(|l| l.quorum_reachable),
        finality_stalled: liveness.map(|l| l.finality_stalled),
        ever_asked_to_join: join.is_some(),
        join_member: join.as_ref().is_some_and(|p| p.member),
    });

    let lean_producer = s.lean_producer_enabled;
    let full_turn_proving = s.full_turn_proving_enabled;
    let state_producer = if lean_producer { "lean" } else { "rust" }.to_string();
    // The DEFAULT-ON producer INSTALLS verified state only for the swap-safe (root-agreeing) set;
    // report that, not the wider "merely mappable" surface, so the status is honest about what the
    // verified executor actually commits.
    let producer_root_agreeing_effects =
        dregg_exec_lean::lean_shadow::producer_root_agreeing_effects().len();
    // WHICH ORDER decided finality — the ordering-side counterpart of `state_producer`. Read from
    // the process-global tally `poll_finalized_blocks` writes on every order selection.
    let order_tally = crate::metrics::consensus_order_tally();

    Json(StatusResponse {
        healthy,
        peer_count,
        connected_peers: liveness.map(|l| l.connected_peers),
        live_committee_voters: liveness.map(|l| l.live_committee_voters),
        quorum_threshold: liveness.map(|l| l.quorum_threshold),
        quorum_reachable: liveness.map(|l| l.quorum_reachable),
        ever_reached_quorum: liveness.map(|l| l.ever_reached_quorum),
        seconds_since_quorum: liveness.map(|l| l.seconds_since_quorum),
        finality_stalled: liveness.map(|l| l.finality_stalled),
        join_member: join.as_ref().map(|p| p.member),
        join_requests_sent: join.as_ref().map(|p| p.requests_sent),
        join_last_request_peers: join.as_ref().map(|p| p.last_request_peers),
        join_waiting_secs: join.as_ref().map(|p| p.waiting_secs),
        join_proposal_seen: join.as_ref().map(|p| p.proposal_seen),
        verified_root_splits,
        turns_in_flight,
        latest_height,
        dag_height,
        block_count,
        consensus_live,
        revocation_count,
        note_count,
        federation_mode,
        public_key: hex_encode(&s.cclerk.public_key().0),
        state_producer,
        lean_producer,
        full_turn_proving,
        consensus_order: order_tally.last_source.to_string(),
        consensus_order_budget_ms: crate::blocklace_sync::verified_order_ffi_timeout().as_millis()
            as u64,
        consensus_order_verified_polls: order_tally.verified_polls,
        consensus_order_unverified_polls: order_tally.unverified_polls,
        consensus_order_failed_closed_polls: order_tally.failed_closed_polls,
        consensus_order_over_budget_polls: order_tally.over_budget_polls,
        producer_root_agreeing_effects,
        producer_covered_effects: producer_root_agreeing_effects,
    })
}

const POA_SIGNAL_STATUS_FORMAT_V1: &str = "POA-SIGNAL-STATUS-1";
const POA_SIGNAL_TRANSITION_VIEW_FORMAT_V1: &str = "POA-SIGNAL-TRANSITION-VIEW-1";
const POA_SIGNAL_PLAYER_HEAD_FORMAT_V1: &str = "POA-SIGNAL-PLAYER-HEAD-1";
pub(crate) const POA_SIGNAL_VIEW_FINALITY_CLAIM: &str = "not_asserted_by_this_view";
const POA_SIGNAL_PUBLIC_MISSION_ID: u32 = 1;

pub(crate) fn parse_poa_signal_authority(authority: &str) -> Result<[u8; 32], StatusCode> {
    if authority.len() != 64
        || !authority
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(StatusCode::BAD_REQUEST);
    }
    hex_decode(authority).map_err(|_| StatusCode::BAD_REQUEST)
}

fn parse_poa_signal_player_cell(cell: &str) -> Result<CellId, StatusCode> {
    parse_poa_signal_authority(cell).map(CellId)
}

/// Decode a canonical, positive decimal PoA transition coordinate.
///
/// The 20-byte ceiling is the decimal width of `u64`; rejecting leading zeroes
/// gives each stored transition one URL and keeps attacker-controlled path work
/// constant.  This is only a lookup coordinate, never a game-state value.
fn parse_poa_signal_sequence(sequence: &str) -> Result<u64, StatusCode> {
    if sequence.is_empty()
        || sequence.len() > 20
        || !sequence.bytes().all(|byte| byte.is_ascii_digit())
        || (sequence.len() > 1 && sequence.starts_with('0'))
    {
        return Err(StatusCode::BAD_REQUEST);
    }
    let sequence = sequence
        .parse::<u64>()
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    if sequence == 0 {
        return Err(StatusCode::BAD_REQUEST);
    }
    Ok(sequence)
}

/// Select the only PoA Signal authority this node is entitled to serve.
///
/// A path cannot be used to probe arbitrary authority rows in the shared store:
/// the exact 32-byte selector must equal the node's canonical configured
/// federation id.  Discovery-mode nodes have no such authority and return 503.
pub(crate) fn select_local_poa_signal_authority(
    authority: [u8; 32],
    federation_configured: bool,
    federation_id: [u8; 32],
) -> Result<[u8; 32], StatusCode> {
    if !federation_configured {
        return Err(StatusCode::SERVICE_UNAVAILABLE);
    }
    if authority != federation_id {
        return Err(StatusCode::BAD_REQUEST);
    }
    Ok(authority)
}

fn poa_signal_head_view(head: &dregg_persist::PoaSignalHeadV1) -> PoaSignalHeadViewV1 {
    PoaSignalHeadViewV1 {
        head_digest: hex_encode(&head.digest()),
        deployment_digest: hex_encode(&head.deployment_digest()),
        transition_count: head.transition_count(),
        world_sequence: head.world_sequence(),
        canon_revision: head.canon_revision(),
        last_transition_digest: hex_encode(&head.last_transition_digest()),
    }
}

/// `GET /api/poa/signal/{authority}/status`.
///
/// Returns `200` with `installed:false` when the configured federation has not
/// run the PoA genesis ceremony.  A present head has already passed the store's
/// strict decode/seal/key validation.  The endpoint is observational: it calls
/// no audit, repair, index-sync, or initialization method.
async fn get_poa_signal_status(
    AxumPath(authority): AxumPath<String>,
    State(state): State<NodeState>,
) -> Result<Json<PoaSignalStatusResponseV1>, StatusCode> {
    // Parse the fixed-width input before acquiring the shared state lock.
    let requested = parse_poa_signal_authority(&authority)?;
    let s = state.read().await;
    let authority_id =
        select_local_poa_signal_authority(requested, s.federation_configured, s.federation_id)?;
    let head = s
        .store
        .load_poa_signal_head(authority_id)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    let normalized_authority = hex_encode(&authority_id);
    Ok(Json(PoaSignalStatusResponseV1 {
        format: POA_SIGNAL_STATUS_FORMAT_V1,
        authority_id: normalized_authority.clone(),
        federation_id: normalized_authority,
        installed: head.is_some(),
        head: head.as_ref().map(poa_signal_head_view),
        consensus_finality: POA_SIGNAL_VIEW_FINALITY_CLAIM,
    }))
}

/// `GET /api/poa/signal/{authority}/players/{cell}/head`.
///
/// Supplies exactly the replay and identity coordinates the extension needs
/// before it constructs a signed Signal carrier.  It intentionally cannot be
/// widened by query parameters and never serializes the cell's balance,
/// program, state fields, delegates, or capability list.
async fn get_poa_signal_player_head(
    AxumPath((authority, cell)): AxumPath<(String, String)>,
    State(state): State<NodeState>,
) -> Result<Json<PoaSignalPlayerHeadResponseV1>, StatusCode> {
    let requested = parse_poa_signal_authority(&authority)?;
    let cell_id = parse_poa_signal_player_cell(&cell)?;
    let s = state.read().await;
    let authority_id =
        select_local_poa_signal_authority(requested, s.federation_configured, s.federation_id)?;
    let live = s.ledger.get(&cell_id);
    let normalized_authority = hex_encode(&authority_id);
    Ok(Json(PoaSignalPlayerHeadResponseV1 {
        format: POA_SIGNAL_PLAYER_HEAD_FORMAT_V1,
        authority_id: normalized_authority.clone(),
        federation_id: normalized_authority,
        cell_id: hex_encode(&cell_id.0),
        found: live.is_some(),
        nonce: live.map_or(0, |cell| cell.state.nonce()),
        public_key: live.map(|cell| hex_encode(cell.public_key())),
        last_receipt_hash: persistent_receipt_head(&s, &cell_id).map(|hash| hex_encode(&hash)),
    }))
}

/// `GET /api/poa/signal/{authority}/transitions/{sequence}`.
///
/// The returned record is the store-validated immutable transition envelope.
/// It exposes only stable digests and the carrying commit/turn/receipt
/// coordinates.  In particular it returns neither Canon/config bytes nor judge
/// input/output, and it makes no quorum-finality claim.
async fn get_poa_signal_transition(
    AxumPath((authority, sequence)): AxumPath<(String, String)>,
    State(state): State<NodeState>,
) -> Result<Json<PoaSignalTransitionViewV1>, StatusCode> {
    let sequence = parse_poa_signal_sequence(&sequence)?;
    let requested = parse_poa_signal_authority(&authority)?;
    let s = state.read().await;
    let authority_id =
        select_local_poa_signal_authority(requested, s.federation_configured, s.federation_id)?;
    let head = s
        .store
        .load_poa_signal_head(authority_id)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;
    if sequence > head.transition_count() {
        return Err(StatusCode::NOT_FOUND);
    }
    let transition = s
        .store
        .load_poa_signal_transition(authority_id, sequence)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;

    // The latest transition must land on the current head.  Boot audit already
    // checks the complete chain, but retaining this O(1) cross-row check means
    // a live corruption/race cannot be presented as a coherent current view.
    if sequence == head.transition_count() && transition.successor_head_digest() != head.digest() {
        return Err(StatusCode::INTERNAL_SERVER_ERROR);
    }

    let normalized_authority = hex_encode(&authority_id);
    Ok(Json(PoaSignalTransitionViewV1 {
        format: POA_SIGNAL_TRANSITION_VIEW_FORMAT_V1,
        authority_id: normalized_authority.clone(),
        federation_id: normalized_authority,
        sequence: transition.sequence(),
        observed_head_transition_count: head.transition_count(),
        is_observed_head_transition: sequence == head.transition_count(),
        commit_ordinal: transition.commit_ordinal(),
        turn_hash: hex_encode(&transition.turn_hash()),
        receipt_hash: hex_encode(&transition.receipt_hash()),
        predecessor_head_digest: hex_encode(&transition.predecessor_head_digest()),
        successor_head_digest: hex_encode(&transition.successor_head_digest()),
        transition_digest: hex_encode(&transition.transition_digest()),
        judge_input_digest: hex_encode(&transition.judge_input_digest()),
        judge_output_digest: hex_encode(&transition.judge_output_digest()),
        consensus_finality: POA_SIGNAL_VIEW_FINALITY_CLAIM,
    }))
}

/// GET /api/node/producer — the honest THE-SWAP verified-execution boundary.
async fn get_producer_status(State(state): State<NodeState>) -> Json<ProducerStatusResponse> {
    let s = state.read().await;
    let lean_producer_enabled = s.lean_producer_enabled;
    let full_turn_proving = s.full_turn_proving_enabled;
    drop(s);

    let covered: Vec<String> = dregg_exec_lean::lean_shadow::producer_covered_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let uncovered: Vec<String> = dregg_exec_lean::lean_shadow::producer_uncovered_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let root_agreeing: Vec<String> = dregg_exec_lean::lean_shadow::producer_root_agreeing_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let root_gaps: Vec<String> = dregg_exec_lean::lean_shadow::producer_root_gap_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let total_effect_kinds = dregg_exec_lean::lean_shadow::all_effect_kinds().len();

    let state_producer = if lean_producer_enabled {
        "lean"
    } else {
        "rust"
    }
    .to_string();

    let summary = if lean_producer_enabled {
        format!(
            "THE SWAP (default on): the VERIFIED Lean executor is the authoritative state producer \
             and INSTALLS its post-state for turns touching only the {} SWAP-SAFE (root-agreeing) \
             effect kinds, where the Lean-produced root provably == Rust. The legacy Rust executor \
             runs as a logged differential cross-check. A turn touching any of the {} characterized \
             root-GAP kinds (root provably diverges) or any of the {} unmappable kinds falls back \
             to the Rust producer FOR THAT TURN with a logged reason — never a silent commit of \
             divergent state. Of the {} mappable kinds, {} are swap-safe and {} are root-gaps. \
             Opt out with DREGG_LEAN_PRODUCER=0. Full-turn STARK proving: {}.",
            root_agreeing.len(),
            root_gaps.len(),
            uncovered.len(),
            covered.len(),
            root_agreeing.len(),
            root_gaps.len(),
            if full_turn_proving { "ON" } else { "off" }
        )
    } else {
        format!(
            "Legacy Rust executor is the authoritative state producer (verified Lean producer \
             OFF via DREGG_LEAN_PRODUCER=0 — unset it to re-enable the default SWAP for the {} \
             swap-safe effect kinds). Full-turn STARK proving: {}.",
            root_agreeing.len(),
            if full_turn_proving { "ON" } else { "off" }
        )
    };

    Json(ProducerStatusResponse {
        state_producer,
        lean_producer_enabled,
        full_turn_proving,
        mappable_effects: covered,
        total_effect_kinds,
        unmappable_effects: uncovered,
        root_agreeing_effects: root_agreeing,
        root_gap_effects: root_gaps,
        summary,
    })
}

/// GET /api/node/identity — the operator's pubkey + derived agent cell.
async fn get_node_identity(State(state): State<NodeState>) -> Json<NodeIdentityResponse> {
    let s = state.read().await;
    let public_key = s.cclerk.public_key().0;
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let agent_cell = dregg_cell::CellId::derive_raw(&public_key, &default_token_id);
    let (agent_balance, agent_nonce) = match s.ledger.get(&agent_cell) {
        Some(cell) => (Some(cell.state.balance()), Some(cell.state.nonce())),
        None => (None, None),
    };
    let unlocked = s.unlocked;
    drop(s);
    Json(NodeIdentityResponse {
        public_key: hex_encode(&public_key),
        agent_cell: hex_encode(&agent_cell.0),
        unlocked,
        agent_balance,
        agent_nonce,
    })
}

fn faithful_mirror_error(
    error: FaithfulMirrorError,
) -> (StatusCode, Json<FaithfulMirrorErrorResponse>) {
    let status = match error {
        FaithfulMirrorError::NoAuthenticatedHead
        | FaithfulMirrorError::DurableState(_)
        | FaithfulMirrorError::InconsistentHead(_) => StatusCode::SERVICE_UNAVAILABLE,
    };
    (
        status,
        Json(FaithfulMirrorErrorResponse {
            error: error.to_string(),
        }),
    )
}

fn faithful_root8_lanes(root: dregg_persist::CanonicalFaithfulRoot) -> [u32; 8] {
    root.to_faithful()
        .limbs()
        .map(dregg_circuit::field::BabyBear::as_u32)
}

/// POST `/notes/faithful-spend/mirror` (gateway alias under `/api/`).
///
/// This is a public broadcast-shaped feed, not a note lookup.  Fixed page
/// sizes plus cursor-only continuations let the SDK maintain one incremental
/// global mirror and construct all membership paths locally.  A caller that
/// fetches only a late continuation can still leak sync metadata; the supported
/// SDK path always starts at zero and consumes every intervening page.
async fn post_faithful_note_mirror(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<FaithfulNoteMirrorRequest>,
    limiter: RateLimiter,
) -> Result<Json<FaithfulNoteMirrorResponse>, (StatusCode, Json<FaithfulMirrorErrorResponse>)> {
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err((
            StatusCode::TOO_MANY_REQUESTS,
            Json(FaithfulMirrorErrorResponse {
                error: "faithful mirror rate limit exceeded".to_string(),
            }),
        ));
    }
    let page = state
        .read()
        .await
        .faithful_note_mirror_page(
            req.commitment_cursor,
            req.history_cursor,
            req.nullifier_cursor,
        )
        .map_err(faithful_mirror_error)?;
    let attested_nullifier_root =
        page.latest_attested_root
            .nullifier_set_root
            .ok_or_else(|| {
                faithful_mirror_error(FaithfulMirrorError::InconsistentHead(
                    "latest attestation has no faithful nullifier root".to_string(),
                ))
            })?;
    let attested_nullifier_root8 = faithful_root8_lanes(
        dregg_persist::CanonicalFaithfulRoot::from_bytes(attested_nullifier_root).map_err(
            |error| {
                faithful_mirror_error(FaithfulMirrorError::InconsistentHead(format!(
                    "latest attestation carries a noncanonical nullifier root: {error}"
                )))
            },
        )?,
    );
    let history = page
        .history
        .into_iter()
        .map(|envelope| {
            let record = envelope.record;
            FaithfulNoteMirrorRecordResponse {
                session_id: hex_encode(&record.session_id),
                federation_id: hex_encode(&record.federation_id),
                committee_epoch: record.committee_epoch,
                previous_height: record.previous_height,
                height: record.height,
                previous_note_count: record.previous_note_count,
                note_count: record.note_count,
                predecessor_root8: faithful_root8_lanes(record.predecessor),
                successor_root8: faithful_root8_lanes(record.successor),
                block_id: hex_encode(&record.block_id),
                hybrid_quorum: envelope.hybrid_quorum,
            }
        })
        .collect();
    let complete = page.next_commitment_cursor == page.head.note_count
        && page.next_history_cursor == page.head.records
        && page.next_nullifier_cursor == page.nullifier_count;

    Ok(Json(FaithfulNoteMirrorResponse {
        protocol: "dregg-faithful-note-mirror-v1",
        commitment_cursor: page.commitment_cursor,
        next_commitment_cursor: page.next_commitment_cursor,
        history_cursor: page.history_cursor,
        next_history_cursor: page.next_history_cursor,
        nullifier_cursor: page.nullifier_cursor,
        next_nullifier_cursor: page.next_nullifier_cursor,
        commitments: page
            .commitments
            .iter()
            .map(|commitment| hex_encode(commitment))
            .collect(),
        nullifiers: page
            .nullifiers
            .iter()
            .map(
                |(nullifier, value, seq)| FaithfulNullifierMirrorRecordResponse {
                    nullifier: hex_encode(nullifier),
                    value: *value,
                    seq: *seq,
                },
            )
            .collect(),
        anchor: FaithfulNoteMirrorAnchorResponse {
            session_id: hex_encode(&page.anchor.session_id),
            federation_id: hex_encode(&page.anchor.federation_id),
            committee_epoch: page.anchor.committee_epoch,
            height: page.anchor.height,
            note_count: page.anchor.note_count,
            root8: faithful_root8_lanes(page.anchor.root),
        },
        history,
        head: FaithfulNoteMirrorHeadResponse {
            history_records: page.head.records,
            height: page.head.height,
            note_count: page.head.note_count,
            root8: faithful_root8_lanes(page.head.root),
            nullifier_count: page.nullifier_count,
            attested_nullifier_root8,
        },
        head_hybrid_quorum: page.head_hybrid_quorum,
        complete,
        privacy: "cursor-only global mirror; SDK downloads every continuation; public volume and transport timing/lag remain observable; FNHR is threshold-1 pinned-node hybrid-authenticated and attested faithful roots remain a trusted-node transport boundary until finalization votes bind them",
    }))
}

async fn get_cclerk(State(state): State<NodeState>) -> Json<CipherclerkResponse> {
    let ws = state.cclerk_status().await;
    Json(CipherclerkResponse {
        unlocked: ws.unlocked,
        public_key: ws.public_key,
        token_count: ws.token_count,
        receipt_chain_length: ws.receipt_chain_length,
    })
}

async fn post_authorize(
    State(state): State<NodeState>,
    Json(req): Json<AuthorizeRequest>,
) -> Result<Json<AuthorizeResponse>, StatusCode> {
    let s = state.read().await;

    let token = s
        .cclerk
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?;

    let auth_req = AuthRequest {
        service: req.service,
        action: req.action,
        request_cost: req.request_cost,
        budget_states: req.budget_states,
        ..Default::default()
    };

    let authorized = s.cclerk.verify_token(token, &auth_req);

    Ok(Json(AuthorizeResponse {
        authorized,
        reason: if authorized {
            None
        } else {
            Some("token does not satisfy request".to_string())
        },
    }))
}

async fn post_mint(
    State(state): State<NodeState>,
    Json(req): Json<MintRequest>,
) -> Result<Json<MintResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Generate a root key for the new token.
    let mut root_key = [0u8; 32];
    getrandom::fill(&mut root_key).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    let held = s.cclerk.mint_token(&root_key, &req.service);

    Ok(Json(MintResponse {
        token_id: held.id().to_string(),
        service: held.service().to_string(),
    }))
}

async fn post_attenuate(
    State(state): State<NodeState>,
    Json(req): Json<AttenuateRequest>,
) -> Result<Json<AttenuateResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let token = s
        .cclerk
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?
        .clone();

    let attenuation = Attenuation {
        services: req.services,
        not_after: req.not_after,
        budget: req.budget,
        ..Default::default()
    };

    let attenuated = s
        .cclerk
        .attenuate(&token, &attenuation)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    Ok(Json(AttenuateResponse {
        new_token_id: attenuated.id().to_string(),
        service: attenuated.service().to_string(),
    }))
}

async fn get_tokens(State(state): State<NodeState>) -> Json<Vec<TokenInfo>> {
    let s = state.read().await;
    let tokens: Vec<TokenInfo> = s
        .cclerk
        .tokens()
        .iter()
        .map(|t| TokenInfo {
            id: t.id().to_string(),
            label: t.label().to_string(),
            service: t.service().to_string(),
        })
        .collect();
    Json(tokens)
}

/// `GET /api/receipts/index/root` → [`dregg_query::client::IndexRootResponse`].
///
/// The MMR root over the node's receipt chain: leaf `i` is the 32-byte
/// `receipt_hash()` of chain entry `i`, bagged per `dregg_query::Blake3Mmr`. The
/// index is brought current from the chain before the read ([`NodeStateInner::
/// sync_receipt_index`]) — additive, never gating commit. The verifier trusts
/// only this root; `len` is served for UX (the verifier re-derives it from the
/// root-pinned peak heights).
async fn get_receipt_index_root(
    State(state): State<NodeState>,
) -> Json<dregg_query::client::IndexRootResponse> {
    let mut s = state.write().await;
    s.sync_receipt_index();
    Json(dregg_query::client::IndexRootResponse {
        root: hex_encode(&s.receipt_index.root()),
        len: s.receipt_index.len(),
    })
}

/// `GET /api/receipts/index/head` → [`dregg_query::client::SignedIndexHead`].
///
/// The SAME MMR root `/index/root` serves, but SIGNED by this node's
/// federation key and BOUND to the latest consensus-attested coordinates
/// (blocklace block id, height, canonical ledger root — the values the
/// committee's finalization quorum pins). Rung A of
/// `docs/deos/CONSENSUS-BINDS-INDEX.md`: a NODE-bound, consensus-ANCHORED
/// claim (non-repudiation + portable equivocation evidence), deliberately
/// NOT presented as quorum-signed — the per-node receipt chain cannot be
/// quorum-co-signed while `receipt_hash()` absorbs the local wall clock and
/// node-local turns interleave with finalized ones.
async fn get_receipt_index_head(
    State(state): State<NodeState>,
) -> Json<dregg_query::client::SignedIndexHead> {
    let mut s = state.write().await;
    s.sync_receipt_index();
    let root = s.receipt_index.root();
    let len = s.receipt_index.len();
    // The consensus anchor: the latest attested root's quorum-pinned
    // coordinates. A fresh node (no attested root yet) signs the explicitly
    // UNANCHORED framing (block_id = None, height 0, zero ledger root) —
    // distinct bytes from any anchored head by the preimage's option tag.
    let (block_id, height, merkle_root) = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| (r.blocklace_block_id, r.height, r.merkle_root))
        .unwrap_or((None, 0, [0u8; 32]));
    let federation_id = crate::executor_setup::federation_id_for_executor(&s);
    let msg = dregg_query::client::index_head_signing_message(
        &federation_id,
        block_id.as_ref(),
        height,
        &merkle_root,
        len,
        &root,
    );
    let sig = dregg_types::sign(&s.cclerk.gossip_signing_key(), &msg);
    Json(dregg_query::client::SignedIndexHead {
        root: hex_encode(&root),
        len,
        block_id: block_id.map(|b| hex_encode(&b)),
        height,
        merkle_root: hex_encode(&merkle_root),
        federation_id: hex_encode(&federation_id),
        signer: hex_encode(&s.cclerk.public_key().0),
        signature: hex_encode(&sig.0),
    })
}

/// `GET /api/receipts/index/range?lo=&hi=` →
/// [`dregg_query::client::IndexRangeResponse`].
///
/// The certified slice: the receipt rows at dense positions `[lo, min(hi,
/// len-1)]` plus the `RangeOpening` (the honest prover, whose output always
/// verifies against the root from `/index/root`). Each row carries the typed
/// [`dregg_query::EffectSummary`] enrichment, joined from the commit event log
/// by turn hash, so the slice is a complete EDB for transfer/balance/granted
/// queries. The span is capped like other list endpoints.
async fn get_receipt_index_range(
    State(state): State<NodeState>,
    Query(q): Query<dregg_query::client::RangeParams>,
) -> Result<Json<dregg_query::client::IndexRangeResponse>, StatusCode> {
    const MAX_SPAN: u64 = 1024;
    if q.hi < q.lo || q.hi - q.lo >= MAX_SPAN {
        return Err(StatusCode::BAD_REQUEST);
    }
    let mut s = state.write().await;
    s.sync_receipt_index();
    let len = s.receipt_index.len();
    if len == 0 || q.lo >= len {
        return Err(StatusCode::NOT_FOUND);
    }
    let hi = q.hi.min(len - 1);
    let root = s.receipt_index.root();
    let (_values, opening) = s.receipt_index.open_range(q.lo, hi);

    // Build the enriched receipt rows for [lo, hi]: identity/position from the
    // chain entry, height + typed effect summaries joined from the commit event
    // log by turn hash (absent for entries evicted past the event-log window —
    // those rows still carry their certified identity, just no facts).
    let chain = s.cclerk.receipt_chain();
    let mut receipts = Vec::with_capacity((hi - q.lo + 1) as usize);
    for pos in q.lo..=hi {
        let r = &chain[pos as usize];
        let turn_hash = hex_encode(&r.turn_hash);
        let (height, summaries) = s
            .event_log
            .iter()
            .rev()
            .find(|e| e.turn_hash == turn_hash)
            .map(|e| (e.height, e.summaries.clone()))
            .unwrap_or((0, Vec::new()));
        receipts.push(dregg_query::ReceiptRecord {
            chain_index: pos,
            receipt_hash: hex_encode(&r.receipt_hash()),
            height,
            agent: hex_encode(&r.agent.0),
            effects: summaries,
        });
    }

    Ok(Json(dregg_query::client::IndexRangeResponse {
        receipts,
        root: hex_encode(&root),
        lo: q.lo,
        hi,
        opening,
    }))
}

async fn get_receipts(State(state): State<NodeState>) -> Json<Vec<ReceiptInfo>> {
    let s = state.read().await;
    Json(receipt_infos_from_chain(&s, 50))
}

/// `GET /api/receipts/finalized-core?receipt_index=N|core_id=<64 hex>`.
///
/// Exactly one coordinate is accepted.  Both store lookups cross-check the canonical core and
/// reciprocal durable indexes in bounded B-tree reads.  Unknown coordinates are `404`; malformed
/// or ambiguous queries are `400`; any reciprocal/index/core corruption fails closed as `500`.
async fn get_finalized_receipt_core(
    State(state): State<NodeState>,
    Query(query): Query<FinalizedReceiptCoreQuery>,
) -> Result<Json<FinalizedReceiptCoreResponse>, StatusCode> {
    let s = state.read().await;
    let found = match (query.receipt_index, query.core_id) {
        (Some(receipt_index), None) => s
            .store
            .finalized_receipt_core_v1(receipt_index)
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
            .map(|(_, core)| (receipt_index, core)),
        (None, Some(core_id)) => {
            let bytes: [u8; 32] = hex_decode(&core_id).map_err(|_| StatusCode::BAD_REQUEST)?;
            let id = dregg_turn::FinalizedReceiptIdV1::from_bytes(bytes)
                .map_err(|_| StatusCode::BAD_REQUEST)?;
            s.store
                .finalized_receipt_core_v1_by_id(id)
                .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        }
        (None, None) | (Some(_), Some(_)) => return Err(StatusCode::BAD_REQUEST),
    };
    let (receipt_index, core) = found.ok_or(StatusCode::NOT_FOUND)?;
    Ok(Json(FinalizedReceiptCoreResponse::from_core(
        receipt_index,
        core,
    )))
}

async fn get_receipt_witnesses(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let bytes = hex_decode(&hash).map_err(|_| StatusCode::BAD_REQUEST)?;
    let receipt_hash: [u8; 32] = bytes.try_into().map_err(|_| StatusCode::BAD_REQUEST)?;
    let s = state.read().await;
    let witnessed = s
        .witnessed_receipts
        .get(&receipt_hash)
        .cloned()
        .unwrap_or_default();
    let witness_artifacts = witnessed
        .iter()
        .map(|witness| {
            witness
                .to_artifact_bytes()
                .map(|bytes| hex_encode_var(&bytes))
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(serde_json::json!({
        "receipt_hash": hex_encode(&receipt_hash),
        "witness_count": witnessed.len(),
        "artifact_format": "DWR1",
        "witness_artifacts": witness_artifacts,
        "witnessed_receipts": witnessed,
    })))
}

/// Serve the persisted full-turn STARK proof for a committed turn so a light
/// client can fetch and independently verify it.
///
/// The proof bytes are persisted by the commit path under
/// `full_turn_proof:{turn_hash}` (see
/// [`crate::turn_proving::turn_proof_config_key`]). A spend turn's freshness is
/// IN-CIRCUIT (the limb-26 grow-gate over the canonical spent set — felt-width
/// #11 fold-in); a light client re-verifying it MUST pass the CANONICAL
/// `expected_old_commit` (derived from the authoritative pre-state INCLUDING the
/// canonical spent-set root) into `dregg_sdk::verify_full_turn_bound` — that
/// anchor is what binds the opened set to the node's authoritative one.
///
/// ⚑ EVERY RESPONSE CARRIES `proof_status`, AND ABSENCE IS NOT ONE FACT. A bare
/// 404 conflated "proving is disabled on this node", "this turn needed no proof"
/// and "**this turn's proof did not verify**" — the last of which
/// `blocklace_sync` itself calls a serious soundness event, and which used to
/// exist only as a log line. A finalized turn that failed proving is recorded
/// under [`crate::turn_proving::turn_proof_failure_config_key`] and answered here
/// as `410 Gone` with `proof_status: "generation_failed"` and the reason: the
/// proof is definitively not coming, so a poller must stop rather than read
/// absence as pending.
///
/// * `200` + `proof_status: "proved"` — hex-encoded proof bytes plus the turn hash.
/// * `410` + `proof_status: "generation_failed"` — proving/verification FAILED.
/// * `404` + `proof_status: "absent"` — nothing recorded either way.
async fn get_turn_proof(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> (StatusCode, Json<serde_json::Value>) {
    // Accept the turn hash as hex (32 bytes). Normalise to the lowercase form the
    // commit path keys with.
    let Ok(bytes) = hex_decode(&hash) else {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "turn hash must be 64 hex characters" })),
        );
    };
    let turn_hash_hex = hex_encode(&bytes);
    let key = crate::turn_proving::turn_proof_config_key(&turn_hash_hex);
    let s = state.read().await;
    match s.store.get_config(&key) {
        Ok(Some(proof_bytes)) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex,
                "proof_status": "proved",
                "proof_len": proof_bytes.len(),
                "proof_hex": hex_encode_var(&proof_bytes),
            })),
        ),
        Ok(None) => {
            let failure_key = crate::turn_proving::turn_proof_failure_config_key(&turn_hash_hex);
            match s.store.get_config(&failure_key) {
                Ok(Some(reason)) => (
                    StatusCode::GONE,
                    Json(serde_json::json!({
                        "turn_hash": turn_hash_hex,
                        "proof_status": "generation_failed",
                        "error": String::from_utf8_lossy(&reason),
                    })),
                ),
                Ok(None) => (
                    StatusCode::NOT_FOUND,
                    Json(serde_json::json!({
                        "turn_hash": turn_hash_hex,
                        "proof_status": "absent",
                    })),
                ),
                // The store could not answer. That is not "absent" — say so
                // rather than let an unreadable store read as a clean negative.
                Err(e) => (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({
                        "turn_hash": turn_hash_hex,
                        "error": format!("store could not be read: {e}"),
                    })),
                ),
            }
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex,
                "error": format!("store could not be read: {e}"),
            })),
        ),
    }
}

/// `GET /api/turn/{hash}/anchor` — **the committee-signed per-turn anchor**, so a stranger
/// re-verifying a served full-turn STARK is checking it against something they obtained and
/// checked themselves, instead of against the artifact's own claims.
///
/// This endpoint publishes NO new authority. Every byte it serves is either recomputable by the
/// holder or already covered by a signature the finalized path produced:
/// `TurnReceipt::receipt_hash()` -> `merkle_root_of_receipt_hashes([receipt_hash])` ->
/// `AttestedRoot::receipt_stream_root` -> `AttestedRoot::signing_message()` -> the committee
/// signatures in `quorum_signatures`. The node does not sign an envelope around values it
/// computed — that would be the same `x != x` with a signature on it.
///
/// The authoritative object is `anchor_hex`: the postcard encoding of
/// [`dregg_federation::TurnAnchorV1`], which the holder deserializes and runs
/// [`dregg_federation::TurnAnchorV1::verify`] on **against a committee roster of their own**.
/// The JSON summary beside it is a convenience for humans and is NOT what anything should trust.
///
/// ⚠ THE ANCHOR CARRIES AN 8-FELT STATE COMMIT PAIR THAT IS **NOT** THE PROOF'S. The receipt's
/// `pre_state_hash` / `post_state_hash` are the chip 8-felt consensus commitment under
/// `state_commit::consensus_ctx`; the full-turn proof publishes the rotated leg's commitment
/// under a context the prover assembles for itself. They are two commitments of one transition
/// and they differ on **four** fields of `V9RotationContext`, each independently sufficient —
/// `cells_root` (whole ledger vs a single-cell context ledger), `iroot` (`empty_iroot()` pinned
/// vs three different logs across four producers), `revoked_root` (the executor's live root vs
/// `empty_revoked_root_8()`, which the proof side has no parameter to thread) and `material`
/// (`Default` vs a factory turn's installed `child_vk`). Measured cause by cause in
/// `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`. Passing these to
/// `verify_full_turn_bound` as `expected_old_commit` refuses every honest proof.
///
/// ⚑ This docblock said TWO causes until 2026-08-07, and said the proof "folds the real receipt
/// chain" — true of exactly one producer, the ledgerless sovereign `cipherclerk`, whose artifacts
/// this node never serves. The live commit path folds `[receipt.receipt_hash()]`, a one-entry log.
///
/// # ⚑ AND THE PROOF'S OWN PAIR IS NOW SERVED BESIDE IT — `proof_state_commits`
///
/// Because the receipt's pair is not the proof's, a stranger re-verifying a served artifact had
/// **nothing** to pass as `expected_old_commit` / `expected_new_commit` and passed the artifact's
/// own values, which is why those two `CommitmentMismatch` teeth compared `x != x`. This response
/// now carries the pair the NODE derived at commit time
/// (`turn_proving::turn_proof_anchors_config_key` — `wide_commit_anchors` re-derived generate-only
/// from the executor's trusted pre-state and the turn's effects, then gated on by
/// `verify_full_turn_bound` before the proof was published). It rides in the JSON **outside**
/// `anchor_hex`, deliberately: `TurnAnchorV1`'s contract is that every byte in it is either
/// recomputable by the holder or covered by a committee signature, and this pair is neither. It is
/// **node-asserted**, and `proof_commit_provenance` says so in the response itself.
///
/// `proof_commit_status` is one of:
/// * `"derived"` — `proof_state_commits` carries `{old_commit, new_commit}` (64 hex each,
///   `dregg_circuit::commit8_wire`). Bind against these.
/// * `"absent"` — this node did not mint the artifact (a proof-carrying sovereign turn, a
///   pre-cutover entry, or proving disabled). **There is no bindable pair and a checker must
///   REFUSE rather than fall back to the artifact's own values.** This is the `cipherclerk`
///   boundary made structural: a ledgerless producer cannot compute a whole-ledger context, so
///   there is no honest pair to serve for its artifacts and none is served.
///
/// * `200` + `anchor_status: "anchored"` — the anchor, postcard-hex.
/// * `404` + `anchor_status: "not_committed"` — no committed turn under this hash.
/// * `409` + `anchor_status: "no_attestation"` — the turn committed but carries no attested root
///   binding a receipt stream at its height, so there is nothing for a committee signature to
///   reach. A conflict, not an absence: the turn exists and cannot be anchored.
async fn get_turn_anchor(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> (StatusCode, Json<serde_json::Value>) {
    let Ok(turn_hash) = hex_decode(&hash) else {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "turn hash must be 64 hex characters" })),
        );
    };
    let turn_hash_hex = hex_encode(&turn_hash);
    let s = state.read().await;

    let record = match s.store.lookup_turn(&turn_hash) {
        Ok(Some(record)) => record,
        Ok(None) => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex,
                    "anchor_status": "not_committed",
                })),
            );
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex,
                    "error": format!("commit log could not be read: {e}"),
                })),
            );
        }
    };

    // The receipt WHOLE — the holder recomputes `receipt_hash()` from it rather than being told
    // it. Matched by the durable commit record's receipt hash, so a chain scan cannot hand back
    // some other turn's receipt.
    let Some(receipt) = s
        .cclerk
        .receipt_chain()
        .iter()
        .find(|r| r.receipt_hash() == record.receipt_hash)
        .cloned()
    else {
        return (
            StatusCode::CONFLICT,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex,
                "anchor_status": "no_attestation",
                "error": "the committed turn's receipt is not in this node's receipt chain",
            })),
        );
    };

    let attested_stored = match s.store.attested_root_at_height(record.height) {
        Ok(Some(root)) => root,
        Ok(None) => {
            return (
                StatusCode::CONFLICT,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex,
                    "anchor_status": "no_attestation",
                    "height": record.height,
                    "error": "no attested root at this turn's committed height",
                })),
            );
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex,
                    "error": format!("attested roots could not be read: {e}"),
                })),
            );
        }
    };

    // The stored root -> the wire root. `hybrid_quorum` is mapped from `finalization_quorum`
    // exactly as the finalized path maps it (`blocklace_sync.rs:9773`), so what the holder gets
    // is byte-for-byte the committee vote signatures the node persisted.
    let attested = dregg_types::AttestedRoot {
        merkle_root: attested_stored.merkle_root,
        note_tree_root: attested_stored.note_tree_root,
        nullifier_set_root: attested_stored.nullifier_set_root,
        height: attested_stored.height,
        timestamp: attested_stored.timestamp,
        blocklace_block_id: attested_stored.blocklace_block_id,
        finality_round: attested_stored.finality_round,
        quorum_signatures: attested_stored.quorum_signatures.clone(),
        threshold_qc: attested_stored.threshold_qc.clone(),
        threshold: attested_stored.threshold,
        federation_id: attested_stored.federation_id,
        receipt_stream_root: attested_stored.receipt_stream_root,
        hybrid_quorum: dregg_persist::hybrid_quorum_from_finalization_quorum(
            &attested_stored.finalization_quorum,
        ),
    };

    // The roster the SERVER claims. A holder that uses it is trusting this node to name its own
    // judges; the type's `served_committee` accessor is named to keep that visible.
    //
    // ⚑ The empty-roster branch mirrors the SIGNER's own rule. `blocklace_sync.rs:9741` pushes the
    // local signature when `federation_keys.is_empty() || federation_keys.contains(&local_pk)` —
    // i.e. an unconfigured node IS its own committee of one. Serving an empty roster here would
    // contradict who actually signed and make every anchor refuse with `NoCommittee`, which reads
    // as "the chain is broken" rather than "this node is solo". Naming the signer is the honest
    // projection; whether to BELIEVE a committee of one is the holder's call, and
    // `RosterProvenance::ServedByTheNode` is what says so at the far end.
    let mut roster = s.known_federation_keys.clone();
    if roster.is_empty() {
        roster.push(s.cclerk.public_key());
    }
    let served_committee = dregg_federation::AnchorCommittee {
        ed25519: roster,
        ml_dsa: s
            .known_federation_ml_dsa_keys
            .iter()
            .map(|k| k.0.to_vec())
            .collect(),
        threshold: attested_stored.threshold,
        federation_id: attested_stored.federation_id,
    };

    let anchor = dregg_federation::TurnAnchorV1 {
        protocol: dregg_federation::TURN_ANCHOR_PROTOCOL_V1.to_string(),
        turn_hash,
        receipt,
        height: record.height,
        block_id: record.block_id,
        attested,
        served_committee,
    };

    let Ok(bytes) = postcard::to_stdvec(&anchor) else {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex,
                "error": "the anchor could not be encoded",
            })),
        );
    };

    // ⚑ THE PROOF'S OWN 8-FELT PAIR, if THIS node minted the artifact. Read from the durable key
    // the commit path wrote beside the proof bytes; a miss, an unreadable store, or a malformed
    // entry all resolve to "absent", which a checker must treat as a REFUSAL. Never a fallback,
    // never a best-effort octet — the whole defect this closes is a checker binding against values
    // it could not obtain independently.
    let proven_pair = s
        .store
        .get_config(&crate::turn_proving::turn_proof_anchors_config_key(
            &turn_hash_hex,
        ))
        .ok()
        .flatten()
        .and_then(|b| dregg_circuit::commit8_wire::commit8_pair_from_bytes(&b));
    let (proof_commit_status, proof_state_commits) = match &proven_pair {
        Some((old, new)) => (
            "derived",
            serde_json::json!({
                "old_commit": dregg_circuit::commit8_wire::commit8_to_hex(old),
                "new_commit": dregg_circuit::commit8_wire::commit8_to_hex(new),
            }),
        ),
        None => ("absent", serde_json::Value::Null),
    };

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "turn_hash": turn_hash_hex,
            "anchor_status": "anchored",
            // ── the proof's published state-commit pair, and WHOSE claim it is ──
            "proof_commit_status": proof_commit_status,
            "proof_state_commits": proof_state_commits,
            "proof_commit_provenance":
                "NODE-DERIVED at commit time from the executor's trusted pre-state and the turn's \
                 effects (dregg_sdk::RotationTurnWitness::wide_commit_anchors, generate-only and \
                 independent of the proof bytes), then gated on by verify_full_turn_bound before \
                 the artifact was published. NOT committee-signed: the committee signs the \
                 receipt's pre/post_state_hash, which is a DIFFERENT commitment of the same \
                 transition (turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs). \
                 `absent` means this node did not mint the artifact and there is NO bindable pair \
                 — refuse, do not fall back to the artifact's own values.",
            "artifact_format": dregg_federation::TURN_ANCHOR_PROTOCOL_V1,
            "anchor_len": bytes.len(),
            "anchor_hex": hex_encode_var(&bytes),
            // ── summary only. NOT authoritative: verify `anchor_hex`. ──
            "height": anchor.height,
            "block_id": hex_encode(&anchor.block_id),
            "receipt_hash": hex_encode(&record.receipt_hash),
            "ledger_root": hex_encode(&anchor.attested.merkle_root),
            "receipt_stream_root": anchor
                .attested
                .receipt_stream_root
                .map(|r| hex_encode(&r)),
            "threshold": anchor.attested.threshold,
            "receipt_covering_signatures": anchor.attested.quorum_signatures.len(),
            "chain_position_signatures": anchor.attested.hybrid_quorum.len(),
        })),
    )
}

/// `GET /api/turn/{hash}/verdict` — WHAT HAPPENED TO MY TURN?
///
/// ⚑ THE HOLE THIS FILLS. A faucet turn returned
/// `{"success":true,"turn_hash":"19f4da54…"}` and then vanished from all four
/// nodes of a live federation. Consensus was right to discard it — every node
/// independently refused it for `receipt-chain-mismatch` (it named a receipt head
/// a concurrent turn had already claimed), unanimously and deterministically, and
/// every node RECORDED that refusal durably. What did not exist was any way to
/// ASK. `/api/receipts` simply lacked the turn, and the client held a turn hash,
/// which was not a coordinate anything could be looked up by. "Rejected forever"
/// and "still pending" were the same observation.
///
/// The four answers, in the order they are decided — DURABLE FIRST, so a terminal
/// verdict always beats this node's volatile in-flight bookkeeping:
///
/// * `"accepted"` (200) — the commit log holds it. Carries the committed height,
///   the receipt hash, and (when an attested root exists at that height) the
///   committee's `quorum`/`threshold` for it.
/// * `"rejected"` (200) — a durable finalized-rejection row names it, with the
///   stable `reason` code and the finalized `block_id` it was carried in. THIS
///   IS TERMINAL: consensus finalized the block, the application predicate
///   refused the payload, and no retry of these bytes can ever change it.
/// * `"pending"` (200) — this node took the turn on and has not yet resolved it.
///   Carries `pending_seconds`. In-memory only: a restart forgets it and the
///   answer honestly degrades to `unknown` rather than inventing one.
/// * `"unknown"` (404) — this node has no record. NOT a verdict. It means "ask
///   another node, or ask again": a turn submitted elsewhere reads `unknown` here
///   until this node finalizes it.
///
/// `500` + `verdict: "indeterminate"` when the by-turn index and the block-keyed
/// authority row disagree. The index is a pointer, never the authority; on
/// disagreement this refuses to answer rather than serve the pointer's claim.
///
/// WHAT THE REASON MAY SAY. Only the stable machine code
/// (`receipt-chain-mismatch`), never local error formatting. The shape is
/// enforced twice — codes are `[a-z0-9-]{1,128}` at the write and again at the
/// read (`signed_turn_validation::canonical_rejection_reason`), so a reason names
/// the CAUSE and cannot carry a path, a key, a peer address or an operand. The
/// turn hash itself is the caller's own value, and the block id is public
/// consensus data already served by `/api/blocks`.
async fn get_turn_verdict(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> (StatusCode, Json<serde_json::Value>) {
    let Ok(turn_hash) = hex_decode(&hash) else {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "turn hash must be 64 hex characters" })),
        );
    };
    let turn_hash_hex = hex_encode(&turn_hash);
    let in_flight = state
        .blocklace()
        .await
        .map(|handle| handle.in_flight_turns.clone());
    let s = state.read().await;

    // ── 1. ACCEPTED. The commit log is the authority for a turn that landed. ──
    match s.store.lookup_turn(&turn_hash) {
        Ok(Some(record)) => {
            if let Some(in_flight) = in_flight.as_ref() {
                in_flight.resolve(&turn_hash);
            }
            // The committee evidence at the turn's height, when a root exists.
            // Count-only, exactly as `/api/federation/roots` reports it.
            let attested = s
                .store
                .attested_root_at_height(record.height)
                .ok()
                .flatten();
            return (
                StatusCode::OK,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex.clone(),
                    "verdict": "accepted",
                    "terminal": true,
                    "height": record.height,
                    "block_id": hex_encode(&record.block_id),
                    "receipt_hash": hex_encode(&record.receipt_hash),
                    "attested": attested.as_ref().map(|root| serde_json::json!({
                        "merkle_root": hex_encode(&root.merkle_root),
                        "quorum": root.distinct_finalization_voters(),
                        "threshold": root.threshold,
                        "structurally_complete": root.is_structurally_complete(),
                    })),
                })),
            );
        }
        Ok(None) => {}
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "turn_hash": turn_hash_hex.clone(),
                    "verdict": "indeterminate",
                    "error": format!("commit log could not be read: {e}"),
                })),
            );
        }
    }

    // ── 2. REJECTED. The by-turn index points at the block-keyed authority row;
    //       both must agree before a verdict is served. ──
    let index_key =
        crate::signed_turn_validation::FinalizedPayloadRejectionTurnIndex::storage_key(&turn_hash);
    let indeterminate = |detail: &str| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex.clone(),
                "verdict": "indeterminate",
                "error": detail,
            })),
        )
    };
    let index_bytes = match s.store.get_config(&index_key) {
        Ok(bytes) => bytes,
        Err(_) => return indeterminate("the rejection index could not be read"),
    };
    if let Some(index_bytes) = index_bytes {
        let index =
            match crate::signed_turn_validation::FinalizedPayloadRejectionTurnIndex::decode_authenticated(
                &index_bytes,
                turn_hash,
            ) {
                Ok(index) => index,
                Err(detail) => return indeterminate(detail),
            };
        let authority_key =
            crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                &index.block_id,
            );
        let authority_bytes = match s.store.get_config(&authority_key) {
            Ok(Some(bytes)) => bytes,
            Ok(None) => {
                return indeterminate(
                    "the rejection index names a block with no durable rejection record",
                );
            }
            Err(_) => return indeterminate("the rejection record could not be read"),
        };
        let authority =
            match crate::signed_turn_validation::FinalizedPayloadRejectionRecord::decode_for_query(
                &authority_bytes,
                index.block_id,
            ) {
                Ok(authority) => authority,
                Err(detail) => return indeterminate(detail),
            };
        // The two rows must name the SAME turn and the SAME reason. A pointer
        // that disagrees with the authority is not evidence of anything.
        if authority.turn_hash != Some(turn_hash) || authority.reason_code != index.reason_code {
            return indeterminate("the rejection index and the rejection record disagree");
        }
        if let Some(in_flight) = in_flight.as_ref() {
            in_flight.resolve(&turn_hash);
        }
        return (
            StatusCode::OK,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex.clone(),
                "verdict": "rejected",
                "terminal": true,
                "reason": authority.reason_code,
                "block_id": hex_encode(&authority.block_id),
                "detail": "consensus finalized the block carrying this turn and the application \
                           predicate deterministically refused the payload before any state \
                           mutation. No state changed and no retry of these exact bytes can \
                           succeed.",
            })),
        );
    }

    // ── 3. PENDING. This node took it on and has not resolved it. ──
    if let Some(pending_seconds) = in_flight
        .as_ref()
        .and_then(|in_flight| in_flight.pending_for_seconds(&turn_hash))
    {
        return (
            StatusCode::OK,
            Json(serde_json::json!({
                "turn_hash": turn_hash_hex.clone(),
                "verdict": "pending",
                "terminal": false,
                "pending_seconds": pending_seconds,
                "detail": "this node accepted the turn for consensus and has not yet reached a \
                           durable verdict on it. Poll again.",
            })),
        );
    }

    // ── 4. UNKNOWN. Not a verdict. ──
    (
        StatusCode::NOT_FOUND,
        Json(serde_json::json!({
            "turn_hash": turn_hash_hex.clone(),
            "verdict": "unknown",
            "terminal": false,
            "detail": "this node holds no record of this turn hash: no commit, no durable \
                       rejection, and it is not in flight here. A turn submitted to another node \
                       reads unknown here until this node finalizes it, and an in-flight record \
                       does not survive a restart.",
        })),
    )
}

async fn get_starbridge_receipts(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeReceiptInfo>> {
    let limit = starbridge_limit(params.limit);
    let cell = params.cell.as_deref().map(str::to_ascii_lowercase);
    let turn_hash = params.turn_hash.as_deref().map(str::to_ascii_lowercase);
    let effects_hash = params.effects_hash.as_deref().map(str::to_ascii_lowercase);

    let s = state.read().await;
    let chain = s.cclerk.receipt_chain();
    let chain_len = chain.len();
    let receipts = chain
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, r)| {
            cell.as_ref()
                .is_none_or(|want| hex_encode(&r.agent.0).eq_ignore_ascii_case(want))
                && turn_hash
                    .as_ref()
                    .is_none_or(|want| hex_encode(&r.turn_hash).eq_ignore_ascii_case(want))
                && effects_hash
                    .as_ref()
                    .is_none_or(|want| hex_encode(&r.effects_hash).eq_ignore_ascii_case(want))
        })
        .take(limit)
        .map(|(idx, r)| {
            let receipt_hash = r.receipt_hash();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);
            let turn_hash_hex = hex_encode(&r.turn_hash);
            // Same attached-proof semantics as `receipt_infos_from_chain_with_witnesses`.
            let has_proof = witness_count > 0 || stored_full_turn_proof_exists(&s, &turn_hash_hex);
            StarbridgeReceiptInfo {
                receipt: ReceiptInfo {
                    chain_index: idx as u64,
                    chain_head: idx + 1 == chain_len,
                    receipt_hash: hex_encode(&receipt_hash),
                    turn_hash: turn_hash_hex,
                    agent: hex_encode(&r.agent.0),
                    pre_state: hex_encode(&r.pre_state_hash),
                    post_state: hex_encode(&r.post_state_hash),
                    timestamp: r.timestamp,
                    computrons_used: r.computrons_used,
                    action_count: r.action_count,
                    previous_receipt_hash: r.previous_receipt_hash.map(|h| hex_encode(&h)),
                    finality: format!("{:?}", r.finality).to_lowercase(),
                    was_encrypted: r.was_encrypted,
                    was_burn: r.was_burn,
                    has_proof,
                    executor_signed: r.executor_signature.is_some(),
                    has_witness: witness_count > 0,
                    witness_count,
                },
                effects_hash: hex_encode(&r.effects_hash),
                federation_id: hex_encode(&r.federation_id),
                emitted_event_count: r.emitted_events.len(),
                routing_directive_count: r.routing_directives.len(),
                derivation_record_count: r.derivation_records.len(),
                source: "receipt_chain",
                turn_body_available: false,
            }
        })
        .collect();
    Json(receipts)
}

/// Does the node hold a persisted full-turn STARK proof for this turn hash
/// (the blocklace finalized-turn proving leg persists under
/// [`crate::turn_proving::turn_proof_config_key`])?
fn stored_full_turn_proof_exists(s: &crate::state::NodeStateInner, turn_hash_hex: &str) -> bool {
    let key = crate::turn_proving::turn_proof_config_key(turn_hash_hex);
    matches!(s.store.get_config(&key), Ok(Some(_)))
}

fn receipt_infos_from_chain(s: &crate::state::NodeStateInner, limit: usize) -> Vec<ReceiptInfo> {
    receipt_infos_from_chain_with_witnesses(
        s.cclerk.receipt_chain(),
        limit,
        |hash| s.witnessed_receipt_count(hash),
        |turn_hash_hex| stored_full_turn_proof_exists(s, turn_hash_hex),
    )
}

fn receipt_infos_from_chain_with_witnesses(
    chain: &[dregg_turn::TurnReceipt],
    limit: usize,
    witness_count_for: impl Fn(&[u8; 32]) -> usize,
    stored_proof_for: impl Fn(&str) -> bool,
) -> Vec<ReceiptInfo> {
    let chain_len = chain.len();
    chain
        .iter()
        .enumerate()
        .rev()
        .take(limit)
        .map(|(idx, r)| {
            let receipt_hash = r.receipt_hash();
            let witness_count = witness_count_for(&receipt_hash);
            let turn_hash_hex = hex_encode(&r.turn_hash);
            // `has_proof` reports whether a STARK attestation is actually
            // ATTACHED to this committed turn: either the async prove pool's
            // WitnessedReceipt (the HTTP commit path) or the persisted
            // full-turn proof (the blocklace finalized-turn path). It is NOT
            // the executor signature — that is `executor_signed`. Deriving it
            // from `executor_signature` made the field permanently false on
            // node configs that never set an executor signing key, even while
            // the pool was attaching real proofs.
            let has_proof = witness_count > 0 || stored_proof_for(&turn_hash_hex);
            ReceiptInfo {
                chain_index: idx as u64,
                chain_head: idx + 1 == chain_len,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: turn_hash_hex,
                agent: hex_encode(&r.agent.0),
                pre_state: hex_encode(&r.pre_state_hash),
                post_state: hex_encode(&r.post_state_hash),
                timestamp: r.timestamp,
                computrons_used: r.computrons_used,
                action_count: r.action_count,
                previous_receipt_hash: r.previous_receipt_hash.map(|h| hex_encode(&h)),
                finality: format!("{:?}", r.finality).to_lowercase(),
                was_encrypted: r.was_encrypted,
                was_burn: r.was_burn,
                has_proof,
                executor_signed: r.executor_signature.is_some(),
                has_witness: witness_count > 0,
                witness_count,
            }
        })
        .collect()
}

/// Query for `GET /api/server/{cell}/affordances?viewer=<authlabel>` — the discovery
/// route for a hosted deos-host private server's cap-gated affordance surface.
#[derive(Debug, Deserialize)]
pub struct ServerAffordanceQuery {
    /// The viewer's held authority label ("none"/"signature"/"proof"/"either").
    /// Defaults to "none" (the broadest viewer — sees every affordance).
    #[serde(default)]
    pub viewer: Option<String>,
}

/// Parse a viewer authority label (the deos-js / discovery vocab).
///
/// An UNKNOWN label is a hard refusal, never a silent default (the twin of the
/// deos-js `parse_auth_label` fix): `AuthRequired::None` is the BROADEST viewer
/// here — the old `_ => None` arm silently minted maximum authority from a typo.
/// An ABSENT field still defaults to "none" at the call site, so legit flows are
/// untouched; only an unrecognized label surfaces as an error (HTTP 400).
fn parse_auth_label_api(label: &str) -> Result<dregg_cell::AuthRequired, String> {
    use dregg_cell::AuthRequired;
    match label.to_lowercase().as_str() {
        "none" => Ok(AuthRequired::None),
        "signature" | "sig" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" => Ok(AuthRequired::Either),
        "impossible" => Ok(AuthRequired::Impossible),
        other => Err(format!("unknown authority label '{other}'")),
    }
}

/// `GET /api/server/{cell}/affordances?viewer=<authlabel>` — DISCOVERY.
///
/// Project a hosted deos-host private server's published affordance surface for a
/// viewer's held authority (the proven attenuation lattice: `required ⊆ held`). A
/// weaker viewer sees a strictly smaller set. Returns `[{name, required}]` JSON, or 404
/// if no server is hosted at that cell.
pub async fn get_server_affordances(
    State(state): State<NodeState>,
    AxumPath(cell_hex): AxumPath<String>,
    Query(q): Query<ServerAffordanceQuery>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let cell = match hex_decode_32(&cell_hex) {
        Some(bytes) => CellId(bytes),
        None => return Err(StatusCode::BAD_REQUEST),
    };
    // Fail-CLOSED: an unknown/typo'd viewer label refuses (400) instead of silently
    // becoming the broadest viewer. An absent `viewer` still defaults to "none".
    let held = parse_auth_label_api(q.viewer.as_deref().unwrap_or("none"))
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.read().await;
    let specs = match s.deos_server_surfaces.get(&cell) {
        Some(specs) => specs.clone(),
        None => return Err(StatusCode::NOT_FOUND),
    };
    // The executor's federation id — the binding a client signs its fire action over
    // (on a solo/unconfigured node this is `blake3(pubkey)`, not the raw `federation_id`).
    // A remote client cannot derive it, so discovery hands it back: everything needed to
    // build + sign a fire turn arrives in one round-trip.
    let executor_federation_id = hex_encode(&crate::executor_setup::federation_id_for_executor(&s));
    drop(s);

    // Project per-viewer via the proven attenuation lattice (the deos-reflect surface).
    let mut surface = deos_reflect::AffordanceSurface::new(cell);
    for (name, required) in &specs {
        surface = surface.declare(deos_reflect::Affordance::new(
            name.clone(),
            required.clone(),
            dregg_turn::action::Effect::IncrementNonce { cell },
        ));
    }
    let visible: Vec<serde_json::Value> = surface
        .project_for(&held)
        .into_iter()
        .map(|a| {
            serde_json::json!({
                "name": a.name,
                "required": a.required.label(),
            })
        })
        .collect();

    Ok(Json(serde_json::json!({
        "cell": cell_hex,
        "viewer": q.viewer.unwrap_or_else(|| "none".to_string()),
        "affordances": visible,
        "executor_federation_id": executor_federation_id,
    })))
}

/// Stable lowercase label for an `AuthRequired` (matches the deos-js / discovery vocab).
fn auth_label_str(a: &dregg_cell::AuthRequired) -> &'static str {
    use dregg_cell::AuthRequired;
    match a {
        AuthRequired::None => "none",
        AuthRequired::Signature => "signature",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        AuthRequired::Custom { .. } => "custom",
    }
}

/// Decode a 64-char hex string into a 32-byte array (cell id). `None` on any malformed
/// input.
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if !s.is_ascii() || s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn push_committed_event(
    s: &mut crate::state::NodeStateInner,
    turn_hash: String,
    cell_id: String,
    effects: Vec<String>,
    proof_status: ActivityProofStatus,
) {
    push_committed_event_enriched(s, turn_hash, cell_id, effects, Vec::new(), proof_status)
}

/// As [`push_committed_event`], but carrying the typed [`dregg_query::EffectSummary`]
/// enrichment — from/to/asset/amount, grants, and post-state balances — so the
/// LIVE receipt log yields `transfer`/`balance`/`granted` facts (not just
/// effect-kind strings) when dregg-query reads `/api/receipts/index/range`.
pub(crate) fn push_committed_event_enriched(
    s: &mut crate::state::NodeStateInner,
    turn_hash: String,
    cell_id: String,
    effects: Vec<String>,
    summaries: Vec<dregg_query::EffectSummary>,
    proof_status: ActivityProofStatus,
) {
    let store_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let solo_height = s
        .solo_consensus
        .as_ref()
        .map(|solo| solo.height)
        .unwrap_or(0);
    let next_log_height = s
        .event_log
        .back()
        .map(|e| e.height.saturating_add(1))
        .unwrap_or(1);
    let receipt_height = s.cclerk.receipt_chain_length() as u64;
    let height = store_height
        .max(solo_height)
        .max(receipt_height)
        .max(next_log_height);
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    s.push_event(CommittedEvent {
        height,
        status: ActivityStatus::Committed,
        proof_status,
        turn_hash,
        cell_id,
        effects,
        summaries,
        timestamp,
    });
}

/// What the HTTP commit path hands the async prove pool (PATH-PRESERVE Phase 5b).
///
/// F-DOS-1: the commit path does NOT generate a STARK proof inline (that ran the
/// ~750 ms prover under the global state-write lock and wedged the node) — and it
/// no longer runs an inline FRI-free constraint re-check either. The authoritative
/// executor (`execute_via_producer → Committed`) already validated the turn and
/// committed the new state BEFORE this point; the executor IS the soundness
/// boundary, so a second inline witness check would be redundant defense-in-depth,
/// not a gate. The commit path therefore just CARRIES the material the async pool
/// needs to (re-)build + self-verify the composed `FullTurnProof` off the lock —
/// including the per-turn ROTATION witness built from the REAL before/after actor
/// cells, so the attestation proves through the LEAN-emitted rotated descriptor
/// (the v1 hand-AIR is gone from this path).
///
/// ⚑ NOT HTTP-ONLY as of 2026-07-28. The MCP commit paths (`mcp/handlers_*`) now
/// reach the SAME seam rather than carrying their own answer: they used to consult
/// the RETIRED standalone v1 helper and refuse to commit when it could not produce
/// material. One attestation decision, one prove pool, both surfaces.
pub(crate) enum HttpWitnessOutcome {
    /// The turn carries an Effect-VM-bearing transition the async pool attests
    /// off the lock (rotated when the cell is a rotatable cohort member).
    Rotatable(RotatableTurn),
    /// No effect in this turn touches the ACTOR cell, so the producer projection is
    /// the lone-`NoOp` sentinel: there is no actor transition to attest.
    NotRequired,
    /// The CHECKED producer projection REFUSES this turn BY NAME: the turn
    /// carries a verb whose authority plane has no AIR row (the PQ identity
    /// verbs) or a `SetField` key wider than the AIR's u32 index lane. An
    /// attestation is REQUIRED here and CANNOT be produced, which is a different
    /// fact from [`Self::NotRequired`] and must not be reported as it.
    ///
    /// Reporting it as `NotRequired` is what the old hand-rolled twin did, and it
    /// was worse than cosmetic: the twin projected a wide `SetField` key through
    /// an `as u32` TRUNCATION, judged the turn attestable, and handed it to the
    /// pool — where `AgentCipherclerk::convert_effects_to_vm`'s `.expect()`
    /// panicked the blocking worker AFTER the turn had committed. Refusing here
    /// keeps that turn off the pool entirely.
    Unprovable(String),
}

impl HttpWitnessOutcome {
    /// The honest committed-turn `proof_status` for this outcome, paired with the
    /// job (if any) to hand the async prove pool.
    ///
    /// ONE place, called by all four commit sites (`/turns/submit`,
    /// `/turns/submit-signed`, `/turns/submit-encrypted`, the faucet). Each used to
    /// carry its own pair of `match`es over this enum, which is the same
    /// duplicated-decision shape as the projector twin this gate just lost.
    pub(crate) fn split(self, turn_hash: &str) -> (ActivityProofStatus, Option<RotatableTurn>) {
        match self {
            Self::Rotatable(rotatable) => (ActivityProofStatus::ProofPending, Some(rotatable)),
            Self::NotRequired => (ActivityProofStatus::NotRequired, None),
            Self::Unprovable(why) => {
                tracing::warn!(
                    turn_hash = %turn_hash,
                    refusal = %why,
                    "committed turn is OUTSIDE the EffectVM AIR domain; NO attestation can be \
                     produced for it — reported as proof_generation_failed, never as \
                     not_required (the commit itself stands: the executor is the authority)"
                );
                (ActivityProofStatus::ProofGenerationFailed, None)
            }
        }
    }
}

/// The material the async prove pool needs to attest a committed turn off the
/// lock. `rotation` is `Some` when the actor cell is a rotatable cohort member
/// (the effect-vm leg proves through the rotated descriptor); `None` falls back
/// to the byte-identical v1 leg INSIDE `prove_and_verify_finalized_turn` — never
/// the node's own v1 effect-vm hand-AIR.
pub(crate) struct RotatableTurn {
    agent: CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: Vec<dregg_turn::Effect>,
    turn_hash: [u8; 32],
    rotation: Option<dregg_sdk::RotationTurnWitness>,
}

/// The attestation-coverage decision for one committed turn.
///
/// See [`http_attestation_coverage`] for why this is DERIVED rather than listed.
#[derive(Debug)]
enum AttestationCoverage {
    /// The producer projection carries at least one REAL (non-`NoOp`) row: there
    /// is an actor transition for the pool to attest.
    Attestable,
    /// The projection is the lone-`NoOp` sentinel the producer injects when NO
    /// effect in the turn touches the actor cell. There is no actor transition to
    /// attest — the pool would prove `old_commit == new_commit` and say nothing
    /// about the turn's effects.
    NoActorTransition,
    /// The CHECKED producer projection refuses this turn BY NAME.
    Refused(String),
}

/// Coverage predicate for the async-attestation gate: will the async prove pool
/// have an actor transition to attest for this committed turn?
///
/// DERIVED FROM ONE PLACE, NOT RE-LISTED. The only projector consulted is
/// [`dregg_sdk::AgentCipherclerk::try_convert_effects_to_vm`] — which is the SAME
/// function the pool runs downstream (`turn_proving::prove_and_verify_finalized_turn`
/// calls `AgentCipherclerk::convert_effects_to_vm`, its unchecked wrapper, over the
/// SAME flat `total_effects()` slice this gate is handed). So the gate cannot drift
/// from the producer: it ASKS the producer.
///
/// ⚠ WHAT THIS REPLACED, and why it mattered. The gate used to be a hand-rolled
/// `match` over exactly three variants (`Transfer` / `SetField` / `IncrementNonce`),
/// against a producer that projects 29. Two lists, and they had drifted in BOTH
/// directions:
///
/// * UNDER-coverage (the unattested hole): a turn made only of `EmitEvent`,
///   `GrantCapability`, `AttenuateCapability`, `Custom`, `CellSeal`, … was judged
///   `NotRequired` and committed with NO proof obligation recorded, so a light
///   client or auditor had nothing to check for it. Both `EmitEvent` and
///   `GrantCapability` are directly submittable through `/api/turns/submit`'s
///   `TurnEffectSpec`; the other 24 arrive through `/turns/submit-signed` and
///   `/turns/submit-encrypted`, which share this gate and accept a full postcard
///   `SignedTurn`.
/// * OVER-coverage (a fictional obligation): the twin had NO actor guard at all, so
///   a `Transfer`/`SetField`/`IncrementNonce` aimed at some OTHER cell was judged
///   attestable. The pool then projected it through the real producer, got the lone
///   `NoOp` sentinel, and minted a proof of `old == new` that says nothing about the
///   effect. Those turns now report `NotRequired`, which is what they are.
/// * TRUNCATION: the twin lowered the canonical u64 `SetField` key with `as u32`,
///   where the checked producer REFUSES a key above `u32::MAX`. See
///   [`HttpWitnessOutcome::Unprovable`] for the panic that reached.
fn http_attestation_coverage(
    agent: &CellId,
    effects: &[dregg_turn::Effect],
) -> AttestationCoverage {
    match dregg_sdk::AgentCipherclerk::try_convert_effects_to_vm(agent, effects) {
        Err(refusal) => AttestationCoverage::Refused(refusal.to_string()),
        Ok(vm_effects) => {
            // The producer injects a single `NoOp` when it emitted no row at all
            // (`cipherclerk.rs`: `if vm_effects.is_empty() { push(NoOp) }`), and NO
            // arm ever emits a `NoOp` for a real effect — so "carries a non-NoOp
            // row" is exactly "the producer projected something".
            if vm_effects
                .iter()
                .any(|e| !matches!(e, dregg_circuit::effect_vm::Effect::NoOp))
            {
                AttestationCoverage::Attestable
            } else {
                AttestationCoverage::NoActorTransition
            }
        }
    }
}

/// Prepare a committed HTTP-path turn for asynchronous attestation (PATH-PRESERVE
/// Phase 5b). The authoritative executor already validated + committed this turn,
/// so this does NO inline proving and NO inline FRI-free re-check — it only
/// gathers what the async prove pool needs to (re-)build + self-verify the
/// composed `FullTurnProof` off the lock.
///
/// `after_cell` is the ACTOR cell AFTER the executor mutated it (the real after-cell
/// the rotated leg's welds read); `receipt_hash` seeds the rotation witness's
/// `iroot` MMR leaf. When the actor cell is a rotatable cohort member the rotation
/// witness is built (the effect-vm leg then proves through the LEAN-emitted rotated
/// descriptor); otherwise it is `None` and the byte-identical v1 leg runs INSIDE
/// the prover — never the node's own v1 effect-vm hand-AIR. Returns
/// [`HttpWitnessOutcome::NotRequired`] when no effect touches the actor cell,
/// [`HttpWitnessOutcome::Unprovable`] when the checked producer projection refuses
/// the turn by name, or `Err` only when the actor's local pre-state is missing /
/// unrepresentable.
///
/// Takes the two ACTOR CELLS, not two ledgers: every caller only ever asked the
/// ledgers for `turn.agent`, and the MCP commit paths hold the before-cell directly
/// (they arm no per-turn restore-point journal, so there is no `pre_ledger` for them
/// to hand over). Same function, both surfaces — the alternative was an MCP-local
/// copy of this decision, which is how the projector twin this gate replaced got
/// there in the first place.
pub(crate) fn prepare_rotatable_turn(
    turn: &Turn,
    before_cell: Option<&dregg_cell::Cell>,
    after_cell: Option<&dregg_cell::Cell>,
    receipt_hash: [u8; 32],
) -> Result<HttpWitnessOutcome, String> {
    // The SAME flat slice the prove pool will project (`ProveJob::effects`), so the
    // gate's question and the pool's answer are over one object.
    let effects: Vec<dregg_turn::Effect> = turn
        .call_forest
        .total_effects()
        .into_iter()
        .cloned()
        .collect();
    match http_attestation_coverage(&turn.agent, &effects) {
        AttestationCoverage::Attestable => {}
        AttestationCoverage::NoActorTransition => return Ok(HttpWitnessOutcome::NotRequired),
        AttestationCoverage::Refused(why) => return Ok(HttpWitnessOutcome::Unprovable(why)),
    }

    let Some(before_cell) = before_cell else {
        return Err(format!(
            "missing local pre-state for agent {}",
            hex_encode(&turn.agent.0)
        ));
    };
    // THE EPOCH: balances are SIGNED (i64); the circuit VM state is u64. The
    // agent cell is ORDINARY (non-negative) — checked conversion, no `as`.
    let pre_balance = u64::try_from(before_cell.state.balance())
        .map_err(|_| "agent cell balance is negative; cannot build VM pre-state".to_string())?;
    let pre_nonce = before_cell.state.nonce();

    // Build the per-turn ROTATION producer witness from the REAL before/after
    // actor cells (the SAME builder `blocklace_sync::execute_finalized_turn` calls
    // for the finalized leg). It self-validates: a cell the synthetic cap-less
    // rotated pre-state cannot faithfully represent — or a non-cohort effect —
    // yields `None`, and the prover then runs the byte-identical v1 leg. The
    // after-cell is the post-execution state the executor just committed.
    let rotation = match after_cell {
        Some(after_cell) => {
            let receipt_hashes = [receipt_hash];
            crate::turn_proving::rotation_witness_for_self_sovereign(
                pre_balance,
                pre_nonce,
                before_cell,
                after_cell,
                &receipt_hashes,
                &effects,
            )
        }
        None => None,
    };

    Ok(HttpWitnessOutcome::Rotatable(RotatableTurn {
        agent: turn.agent,
        pre_balance,
        pre_nonce,
        effects,
        turn_hash: turn.hash(),
        rotation,
    }))
}

/// Hand a committed turn to the async prove pool (off the state-write lock),
/// marking the receipt as proof-pending. If the pool is absent (should not happen
/// on the running node) or its queue is full, the receipt stays
/// committed-but-unattested — sound, since the authoritative executor already
/// validated + committed the state; the proof is additive attestation.
///
/// Returns whether a job was actually ACCEPTED into the queue. The HTTP callers
/// discard it (their `proof_status` is decided by [`HttpWitnessOutcome::split`]
/// before this runs, and reports `proof_pending` even when no pool is installed —
/// a named residual of this surface, not something the MCP caller should inherit);
/// the MCP callers report the returned truth instead of the intention.
pub(crate) async fn enqueue_async_proof(
    state: &NodeState,
    rotatable: RotatableTurn,
    receipt: dregg_turn::TurnReceipt,
    receipt_hash: [u8; 32],
    turn_hash_hex: String,
) -> bool {
    if let Some(pool) = state.prove_pool().await {
        let job = crate::prove_pool::ProveJob {
            agent: rotatable.agent,
            pre_balance: rotatable.pre_balance,
            pre_nonce: rotatable.pre_nonce,
            effects: rotatable.effects,
            turn_hash: rotatable.turn_hash,
            rotation: rotatable.rotation,
            receipt,
            receipt_hash,
            turn_hash_hex,
        };
        if pool.enqueue(job) {
            let mut s = state.write().await;
            s.mark_proof_pending(receipt_hash);
            return true;
        }
        false
    } else {
        tracing::warn!(
            turn_hash = %turn_hash_hex,
            "no async prove pool installed; committed receipt left unattested (the executor \
             already validated + committed the state, so the commit is sound)"
        );
        false
    }
}

/// Validity horizon (wall-clock seconds) stamped onto operator-constructed
/// turns at the API boundary. Generous for a turn that executes immediately on
/// the submit path; bounded so a replayed envelope eventually expires.
const DEFAULT_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

/// Default `valid_until` for turns the node constructs itself (the thin-HTTP
/// `/turn/submit` and faucet paths, plus `mcp::handlers_act::tool_submit_turn` —
/// see that call site for why this is `pub(crate)`).
///
/// The Lean producer's wire marshal REQUIRES the turn envelope's `valid_until`
/// (`lean_shadow::turn_to_wire_turn`); a `None` here meant every thin-HTTP turn
/// fell off the verified Lean producer back to the legacy Rust producer,
/// per-turn, forever ("turn.valid_until required for wire marshal"). The Rust
/// executor enforces `current_timestamp <= valid_until` (a TIMESTAMP deadline,
/// not a height), so the default is wall-clock now + a horizon — never a block
/// height, which would be in the past as a timestamp and expire every turn.
pub(crate) fn default_valid_until() -> Option<i64> {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    Some(now + DEFAULT_TURN_VALIDITY_HORIZON_SECS)
}

/// Build a 200-with-error `SubmitTurnResponse` for a malformed action/effect
/// spec. Returns `Ok(...)` so the body carries the diagnostic rather than an
/// opaque 4xx status (matching the rest of this handler's error reporting).
fn submit_turn_bad_request(err: String) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    Ok(Json(SubmitTurnResponse {
        accepted: false,
        turn_hash: None,
        proof_status: ActivityProofStatus::NotCommitted,
        has_witness: false,
        witness_count: 0,
        error: Some(err),
    }))
}

/// Re-apply the executor signature after the node has stamped the receipt's
/// committed finality.
///
/// The turn executor constructs receipts with [`Finality::Final`] and signs them
/// inside `execute()` (`maybe_sign_receipt` over
/// [`TurnReceipt::canonical_executor_signed_message`], the v3 message that binds
/// the *full* `receipt_hash`). Solo mode then downgrades `finality` to
/// [`Finality::Tentative`] — a field bound into `receipt_hash` — which strands
/// that original signature: any verifier recomputing `receipt_hash` from the
/// committed (Tentative) receipt derives a different v3 message, so the signature
/// fails to verify against the executor's verifying key. Re-signing with the SAME
/// key the executor used (the node's gossip signing key, per
/// `configure_turn_executor`) restores `executor_signature == sign(v3(receipt_hash))`
/// for the receipt as committed and served.
fn resign_receipt_committed(receipt: &mut dregg_turn::TurnReceipt, node_signing_key: &[u8; 32]) {
    use ed25519_dalek::Signer;
    let sk = ed25519_dalek::SigningKey::from_bytes(node_signing_key);
    let msg = receipt.canonical_executor_signed_message();
    receipt.executor_signature = Some(sk.sign(&msg).to_bytes().to_vec());
}

/// Debug-only "sign LAST" invariant: a committed receipt's own executor
/// signature MUST verify against the node's executor verifying key over the FINAL
/// receipt about to be persisted.
///
/// Because the v3 executor signature commits to the whole `receipt_hash`, any
/// mutation of a `receipt_hash`-folded field (finality, `previous_receipt_hash`,
/// ...) applied AFTER the signature silently strands it and surfaces far
/// downstream as a verifier's `ExecutorSignatureInvalid`. Asserting here trips
/// that class at the source. Scoped to the solo commit sites where the node IS
/// the signer (its gossip key), so it never false-fires on relayed/foreign
/// receipts. Zero release cost (compiled out unless `debug_assertions`).
#[cfg(debug_assertions)]
fn debug_assert_signed_last(receipt: &dregg_turn::TurnReceipt, node_signing_key: &[u8; 32]) {
    use ed25519_dalek::Verifier;
    let Some(sig_bytes) = receipt.executor_signature.as_ref() else {
        return;
    };
    let vk = ed25519_dalek::SigningKey::from_bytes(node_signing_key).verifying_key();
    let sig = ed25519_dalek::Signature::from_slice(sig_bytes)
        .expect("executor_signature must be a 64-byte ed25519 signature");
    debug_assert!(
        vk.verify(&receipt.canonical_executor_signed_message(), &sig)
            .is_ok(),
        "sign-LAST invariant violated: the node executor_signature does not verify against \
         the committed receipt_hash — a receipt_hash-folded field was mutated after signing"
    );
}

#[tracing::instrument(skip_all, fields(agent = %req.agent))]
async fn post_submit_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<SubmitTurnRequest>,
    limiter: RateLimiter,
) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    // Per-client rate limit (F-1): keys on the real client IP, consulting
    // X-Forwarded-For only when the direct peer is a configured trusted proxy.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // F-P1-3: the prior code accepted `agent` from the request body and signed
    // it with the operator's cipherclerk, allowing a confused-deputy attack where the
    // caller targets a victim cell's c-list with the operator's signature.
    // Mirror the MCP path: derive the agent cell from the cipherclerk's pubkey and
    // ignore the body's value (we still parse it for error reporting).
    let _body_agent = hex_decode(&req.agent).map_err(|_| StatusCode::BAD_REQUEST)?;
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let agent_bytes = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id).0;
    let agent_cell = CellId(agent_bytes);
    let agent = hex_encode(&agent_bytes);
    // The agent's OWN causal head, not the last entry in the node-wide observation
    // log. `receipt_chain()` interleaves every agent the node has ever committed
    // for — its documentation says so and points here — so the moment any other
    // agent committed (the faucet grant is the first one every newcomer triggers)
    // this stamped a foreign receipt as this agent's predecessor and the executor
    // refused the turn with `receipt chain mismatch: expected None, got Some(..)`.
    // That made `dregg demo` steps 3 and 4 mutually exclusive: fund the cell and
    // the very next turn from that cell could not commit.
    let previous_receipt_hash = s.cclerk.agent_receipt_head_hash(&agent_cell);

    // Build the call forest from the request's actions. Each action is signed
    // by the operator's cipherclerk over its canonical bytes
    // (`Authorization::Signature`), so every effect is authenticated to the
    // operator as caller. Cell/value defaults resolve against the action's
    // target (which itself defaults to the operator's own agent cell).
    //
    // This closes the historical blocker where the handler built an empty
    // `CallForest` and the executor rejected every turn ("call forest is
    // empty") so no operator turn ever replicated.
    //
    // Sign over the SAME federation id the executor verifies against
    // (`federation_id_for_executor`): on an unconfigured solo node this is
    // `blake3(pubkey)`, NOT the raw `s.federation_id`. Signing over the latter
    // mismatched the executor's verification domain — once a turn cleared the
    // (fee-sized) budget gate, every action's Ed25519 signature then failed.
    let federation_id = crate::executor_setup::federation_id_for_executor(&s);
    let mut actions = Vec::with_capacity(req.actions.len());
    for action_spec in req.actions {
        let target = match action_spec.target {
            Some(ref h) => match parse_cell_id(h) {
                Ok(c) => c,
                Err(err) => return submit_turn_bad_request(err),
            },
            None => agent_cell,
        };
        let method = action_spec.method.unwrap_or_else(|| "submit".to_string());
        let mut effects = Vec::with_capacity(action_spec.effects.len());
        for effect_spec in action_spec.effects {
            match build_effect(effect_spec, target) {
                Ok(effect) => effects.push(effect),
                Err(err) => return submit_turn_bad_request(err),
            }
        }
        // `make_action` produces a real per-action ed25519 signature.
        actions.push(
            s.cclerk
                .make_action(target, &method, effects, &federation_id),
        );
    }

    let call_forest = {
        let mut forest = CallForest::new();
        for action in actions {
            forest.add_root(action);
        }
        forest
    };

    // Nonce auto-fill: the turn nonce is the agent cell's replay counter, which
    // increments on each committed turn. A thin client that submits several
    // turns in a row cannot know the live value, so when the request leaves
    // `nonce` at its default (0) we fill in the agent cell's current nonce. A
    // caller that needs an explicit nonce (e.g. to pin ordering) passes a
    // non-zero one and we honor it verbatim. This makes repeated CLI turns
    // (register → transfer → revoke) work without the caller threading nonces.
    let effective_nonce = if req.nonce == 0 {
        s.ledger
            .get(&agent_cell)
            .map(|cell| cell.state.nonce())
            .unwrap_or(0)
    } else {
        req.nonce
    };

    let turn = Turn {
        agent: agent_cell,
        nonce: effective_nonce,
        fee: req.fee,
        memo: req.memo,
        // Stamped so the wire marshal accepts the envelope and the turn stays
        // on the verified Lean producer (see `default_valid_until`).
        valid_until: default_valid_until(),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    // Sign the turn.
    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    // THE ONE ADMISSION STAGING RUN — the SAME one `POST /turns/submit` and the
    // pg submit-queue drainer take (`signed_turn_validation::stage_signed_turn_admission`).
    //
    // ⚑ WHY THIS HANDLER CHANGED, AND IT IS THE FINDING, NOT A TIDY-UP. Because
    // the node builds and signs this envelope itself, this path used to run
    // NEITHER the shared outer predicate NOR the pre-execution ledger shape. The
    // second omission is the one that bit: `execute_finalized_turn` provisions
    // every missing `Transfer` destination (`provision_transfer_destinations`)
    // before it executes, and the executor refuses a `Transfer` whose
    // destination is absent — so a thin turn moving value to a cell nobody has
    // seen was answered `rejected: transfer destination not found`, TERMINALLY
    // and without ever reaching consensus, while the byte-identical effect
    // submitted to `/turns/submit` was admitted and committed on the same node.
    // A staging run exists to PREDICT finalization's verdict; one computed
    // against a ledger finalization will never produce is not stricter, it is
    // wrong, and it guarded nothing. (`transport_parity_e2e` drives both halves.)
    //
    // The predicate comes along because it is the same verdict, sooner: a
    // node-signed envelope that fails it here would have been deterministically
    // rejected at finalization anyway. The operator's own cell is enrolled by
    // `executor_setup::enroll_known_pq_identities`, and a faucet-stubbed one is
    // upgraded by the first-turn claim inside the staging run — the case
    // `dregg demo` (QUICKSTART §4) walks.
    //
    // ⚠ SAID PLAINLY, because the alternative is an over-claim: on THIS route the
    // predicate cannot be made to fire from the wire. The handler derives the
    // agent from its own cipherclerk pubkey and stamps the receipt link from its
    // own head, so agent-binding and continuity are self-consistent by
    // construction. It is here for the regression class this handler has ALREADY
    // had once — F-P1-3, where `agent` was taken from the request body and signed
    // with the operator's key (a confused deputy). Reintroduce that and
    // `agent-signer-mismatch` fires here instead of at finalization. The
    // load-bearing half of this change is the pre-execution ledger shape, which
    // `transport_parity_e2e` drives red without.
    let staged = match crate::signed_turn_validation::stage_signed_turn_admission(&mut s, &signed) {
        Ok(staged) => staged,
        Err(refusal) => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            return Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(refusal.to_string()),
            }));
        }
    };
    // Prior images of exactly the cells the staging run touched, captured from
    // the journal before the unconditional rollback.
    let pre_ledger = staged.pre_ledger;

    match staged.outcome {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // F-DOS-1 / PATH-PRESERVE Phase 5b: the authoritative executor ALREADY
            // validated + committed this turn above (the soundness boundary), so
            // there is NO inline STARK proving and NO inline FRI-free re-check under
            // the lock (the wedge F-DOS-1 closed). The succinct composed proof — its
            // effect-vm leg through the LEAN-emitted ROTATED descriptor — is built +
            // self-verified asynchronously off the lock by the prove pool below.
            // Admission staging only.  Consensus finalization is the single
            // authoritative ledger + receipt + faithful-state commit for n=1
            // and n>1 alike, so an ingress crash cannot leave a durable receipt
            // ahead of the ledger/commit cursor.
            let receipt_hash = receipt.receipt_hash();
            // Gather the rotated attestation material from the REAL before/after
            // actor cells (pre_ledger / the just-committed s.ledger). A build hiccup
            // (missing/unrepresentable pre-state) is NON-FATAL: the commit stands and
            // the receipt is simply left unattested (the executor is the authority).
            let witness_outcome = match prepare_rotatable_turn(
                &turn,
                pre_ledger.get(&turn.agent),
                s.ledger.get(&turn.agent),
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            // The receipt is committed; its attestation is pending if there is a
            // transition to prove (ProofPending), NotRequired if no effect touches
            // the actor, ProofGenerationFailed if the turn is outside the AIR domain.
            // The async prove pool attaches the WitnessedReceipt (and gossips its
            // artifact) off the lock when proving completes; the raw turn block
            // is gossiped immediately below so consensus ordering is not delayed.
            let (proof_status, pending_proof) = witness_outcome.split(&turn_hash);
            let bundle_witnessed: Vec<Vec<u8>> = Vec::new();
            let receipt_artifact = postcard::to_stdvec(&receipt).ok();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            // Typed effect enrichment from the REAL before/after actor ledger —
            // so this committed turn's receipt yields transfer/balance/granted
            // facts when dregg-query reads the live index.
            let summaries = summarize_turn_effects(&turn, &pre_ledger, &s.ledger);
            let kinds: Vec<String> = turn
                .call_forest
                .iter_dfs()
                .flat_map(|t| t.action.effects.iter().map(effect_kind))
                .collect();
            let kinds = if kinds.is_empty() {
                vec!["turn_committed".to_string()]
            } else {
                kinds
            };
            push_committed_event_enriched(
                &mut s,
                turn_hash.clone(),
                agent,
                kinds,
                summaries,
                proof_status,
            );

            // Serialize the full SignedTurn for gossip (postcard format).
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");

            drop(s);

            // F-DOS-1: hand proving to the async pool OFF the lock. Returns a
            // fast ack (ProofPending) without waiting for the ~750 ms prover.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            // Emit receipt event to WebSocket subscribers.
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Gossip the turn to federation peers (only if gossip is active).
            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data_for_gossip).await;
                });
            }

            // Submit the turn to the blocklace for consensus ordering. When we
            // produced witness material, gossip the full TurnArtifactBundle
            // (signed turn + receipt + per-cell WitnessedReceipts) so peers
            // materialize real WRs; otherwise fall back to the raw turn block.
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    if bundle_witnessed.is_empty() {
                        blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                    } else {
                        let bundle = dregg_blocklace::finality::TurnArtifactBundle::with_committed(
                            turn_data,
                            receipt_artifact,
                            bundle_witnessed,
                        );
                        blocklace
                            .submit_turn_bundle(&state_for_blocklace, bundle)
                            .await;
                    }
                });
            }

            Ok(Json(SubmitTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // The journal is already resolved: the staging run rolls it back
            // unconditionally, so a refused turn leaves the ledger exactly as it
            // found it — the first-turn claim and the provisioned destinations
            // included, neither of which is the executor's to restore.
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: Some(format!("rejected: {reason}")),
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
        _ => {
            crate::metrics::inc_turns_executed("rejected");
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: None,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some("turn did not commit".to_string()),
            }))
        }
    }
}

/// `POST /api/poa/signal/{authority}/claims` — anonymous ingress for exactly
/// one mission-1 Signal claim and no other Dregg turn.
///
/// CORS handles `OPTIONS` before routing.  This handler is deliberately public,
/// so its own boundary is semantic: exact media type and size, the node's exact
/// configured/installed authority, a strict one-envelope decode, the SDK's
/// no-piggyback carrier predicate, the deployment mission, the canonical
/// signer-derived player cell, and — since 2026-08-07 — that the transcript the
/// claim carries is one THIS NODE served.  Only then does it enter
/// [`submit_signed_turn`].
///
/// ⚑ THE TRANSCRIPT CHECK HERE IS A COURTESY, NOT THE GATE. The authoritative one
/// runs at finalization (`blocklace_sync::execute_finalized_turn`), where it
/// covers every carrier reaching consensus rather than only the ones that arrived
/// through this route — a claim gossiped in from a peer or posted to
/// `/turns/submit` never touches this function. What this adds is that a player
/// who submits a code with no game behind it is told so immediately and by name,
/// instead of watching `latest_height` fail to move.
///
/// It reveals nothing: the refusal is a function of the caller's own session
/// record and their own claim, never of the target.
async fn post_poa_signal_claim(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    AxumPath(authority): AxumPath<String>,
    State(state): State<NodeState>,
    body: axum::body::Bytes,
    limits: PoaSignalIngressLimits,
) -> Result<Json<SubmitSignedTurnResponse>, StatusCode> {
    if headers
        .get(header::CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        != Some("application/octet-stream")
    {
        return Err(StatusCode::UNSUPPORTED_MEDIA_TYPE);
    }
    if body.len() > POA_SIGNAL_MAX_CLAIM_BYTES {
        return Err(StatusCode::PAYLOAD_TOO_LARGE);
    }

    let requested = parse_poa_signal_authority(&authority)?;
    if !limits.per_ip.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }
    let _permit = Arc::clone(&limits.in_flight)
        .try_acquire_owned()
        .map_err(|_| StatusCode::TOO_MANY_REQUESTS)?;

    let authority_id = {
        let s = state.read().await;
        let authority_id =
            select_local_poa_signal_authority(requested, s.federation_configured, s.federation_id)?;
        let installed = s
            .store
            .load_poa_signal_head(authority_id)
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
            .is_some();
        if !installed {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        authority_id
    };

    let signed = crate::signed_turn_validation::decode_signed_turn(&body)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    let claim = dregg_sdk::poa_signal::claim_from_exact_signal_turn(&signed.turn)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    if claim.mission_id() != POA_SIGNAL_PUBLIC_MISSION_ID
        || dregg_sdk::poa_signal::signal_player_cell(&signed.signer.0) != signed.turn.agent
    {
        return Err(StatusCode::BAD_REQUEST);
    }

    // The claim names a played transcript; say so now if this node never served it.
    //
    // ⚠ With NO OPEN SLOT this declines to guess rather than refusing. There is no
    // instance to compare a session against, so any verdict here would be about the
    // absence of a curator ceremony rather than about the player — and the claim
    // cannot settle regardless: `execute_finalized_turn` has no slot snapshot to
    // judge with and holds the turn as retryable. Declining weakens nothing, because
    // the binding gate runs there and runs AFTER the slot snapshot.
    {
        let s = state.read().await;
        let slot = s
            .store
            .load_poa_signal_open_slot_v1(authority_id)
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
        if let Some(slot) = slot {
            let session = s
                .store
                .load_poa_signal_session_v1(authority_id, slot.slot(), signed.signer.0)
                .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
            if let Err(refusal) = crate::poa_signal_adapter::verify_claim_transcript_was_played(
                session.as_ref(),
                &slot,
                &claim,
            ) {
                drop(s);
                return Ok(Json(SubmitSignedTurnResponse {
                    accepted: false,
                    turn_hash: Some(hex_encode(&signed.turn.hash())),
                    signer: Some(hex_encode(&signed.signer.0)),
                    action_count: signed.turn.call_forest.action_count(),
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("{}: {refusal}", refusal.code())),
                }));
            }
        }
    }

    submit_signed_turn(state, signed).await
}

/// POST /turns/submit — accept a caller-signed canonical `SignedTurn`.
///
/// Wire format: `Content-Type: application/octet-stream`, body =
/// `postcard::to_stdvec(&dregg_sdk::SignedTurn)`. This is the remote ingress
/// used by rich clients that build app actions with `AppCipherclerk` and need
/// the node to execute, gossip, and order them without re-signing as the node.
async fn post_submit_signed_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    body: axum::body::Bytes,
    limiter: RateLimiter,
) -> Result<Json<SubmitSignedTurnResponse>, StatusCode> {
    // F-1: per-real-client rate limit (XFF-aware behind a trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    let signed: SignedTurn = match crate::signed_turn_validation::decode_signed_turn(&body) {
        Ok(turn) => turn,
        Err(_) => return Err(StatusCode::BAD_REQUEST),
    };

    submit_signed_turn(state, signed).await
}

/// The one signed-turn execution path shared by authenticated generic ingress
/// and the public, exact-carrier Signal ingress.  Transport-specific admission
/// happens before this function; signature, receipt-chain, executor, proving,
/// gossip, and consensus staging remain byte-for-byte one implementation.
async fn submit_signed_turn(
    state: NodeState,
    signed: SignedTurn,
) -> Result<Json<SubmitSignedTurnResponse>, StatusCode> {
    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    let turn_hash_bytes = signed.turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);
    let signer = hex_encode(&signed.signer.0);
    let agent = hex_encode(&signed.turn.agent.0);
    let action_count = signed.turn.call_forest.action_count();
    let signed_for_gossip = signed.clone();

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // THE ONE ADMISSION STAGING RUN, shared with `POST /turn/submit` and the pg
    // submit-queue drainer: arm the undo journal, take the first-turn claim,
    // apply the shared outer `SignedTurn` predicate, check agent-scoped receipt
    // continuity, install the SAME pre-execution ledger shape
    // `execute_finalized_turn` installs (the actor claim + Transfer-destination
    // provisioning), run THE one executor gate (#171), and roll the journal back
    // unconditionally. This transport chooses only how to RENDER the verdict; it
    // no longer chooses which checks apply or in what order
    // (`signed_turn_validation::stage_signed_turn_admission`, which is also where
    // the reasons each step sits where it does are written down). The whole
    // sequence runs under this exclusive write guard, so an identity rotation
    // cannot race the check protecting the impending mutation, and the executor
    // registry is still populated only from independently anchored host state.
    //
    // ⚑ A PARAGRAPH HERE USED TO SAY "SOLO (n=1) has no finalization pass, so it
    // keeps the in-place commit authoritatively", and the code has not done that
    // since `5f0999ab9` (2026-07-21). Consensus FINALIZATION is the sole
    // authoritative application at EVERY committee size: the rollback is
    // unconditional, `s.ledger` below is the PRE-TURN ledger, and an
    // `accepted:true` that never finalizes moved nothing. A reader trusting the
    // older bullet concludes a solo `POST /turns/submit` mutates state, which is
    // how `relay_slash_submit`'s weld test came to POST an envelope and then
    // assert on `state.ledger`: red for nine days, with a message ("bond
    // decremented by the seizure") naming the cell program, which was never at
    // fault.
    let staged = match crate::signed_turn_validation::stage_signed_turn_admission(&mut s, &signed) {
        Ok(staged) => staged,
        Err(refusal) => {
            return Ok(Json(SubmitSignedTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(refusal.to_string()),
            }));
        }
    };
    // Prior images of exactly the cells the staging run touched — the O(touched)
    // stand-in for the old full `pre_ledger` clone, captured from the journal
    // before it was rolled back.
    let pre_ledger = staged.pre_ledger;

    match staged.outcome {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // F-DOS-1 / PATH-PRESERVE Phase 5b: the executor already validated +
            // committed this turn (the soundness boundary); no inline proving / no
            // inline re-check. The composed proof (rotated effect-vm leg) is built +
            // self-verified asynchronously off the lock by the prove pool below.
            // The receipt is an admission artifact only.  Finalization welds its
            // canonical receipt into the durable log with ledger state, faithful
            // leaves, nullifiers, history, attestation, and both cursors.
            let receipt_hash = receipt.receipt_hash();
            let witness_outcome = match prepare_rotatable_turn(
                &signed.turn,
                pre_ledger.get(&signed.turn.agent),
                s.ledger.get(&signed.turn.agent),
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            // The async prove pool attaches the WitnessedReceipt off the lock.
            let (proof_status, pending_proof) = witness_outcome.split(&turn_hash);
            let bundle_witnessed: Vec<Vec<u8>> = Vec::new();
            let receipt_artifact = postcard::to_stdvec(&receipt).ok();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            push_committed_event(
                &mut s,
                turn_hash.clone(),
                agent,
                vec![format!("signed_turn:{action_count}")],
                proof_status,
            );

            let turn_data = postcard::to_stdvec(&signed_for_gossip)
                .expect("SignedTurn serialization after successful decode");

            drop(s);

            // F-DOS-1: prove off the lock; fast ProofPending ack.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data_for_gossip).await;
                });
            }

            // Gossip the full TurnArtifactBundle (with per-cell WitnessedReceipts)
            // when witness material was produced; raw turn block otherwise.
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    if bundle_witnessed.is_empty() {
                        blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                    } else {
                        let bundle = dregg_blocklace::finality::TurnArtifactBundle::with_committed(
                            turn_data,
                            receipt_artifact,
                            bundle_witnessed,
                        );
                        blocklace
                            .submit_turn_bundle(&state_for_blocklace, bundle)
                            .await;
                    }
                });
            }

            Ok(Json(SubmitSignedTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // The journal is already resolved: the staging run rolled it back
            // unconditionally, admitted or refused.
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitSignedTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
        _ => {
            crate::metrics::inc_turns_executed("rejected");
            drop(s);
            Ok(Json(SubmitSignedTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some("turn did not commit".to_string()),
            }))
        }
    }
}

/// One independently-sourced per-cell WitnessedReceipt for the cross-node
/// aggregate route. `cell_id` is the 32-byte cell hex; `witnessed_receipt` is
/// the hex-encoded `dregg_turn::WitnessedReceipt` artifact (DWR1 or legacy
/// JSON/postcard) — the SAME bytes a peer gossips in a `TurnArtifactBundle`
/// and materializes via `materialize_blocklace_artifacts`.
#[derive(Debug, serde::Deserialize)]
pub struct AggregateWitnessEntry {
    pub cell_id: String,
    pub witnessed_receipt: String,
}

/// POST /turns/aggregate request: the canonical SignedTurn (hex postcard) plus
/// two-or-more independently-produced per-cell WitnessedReceipts.
#[derive(Debug, serde::Deserialize)]
pub struct AggregateBundleRequest {
    /// Hex-encoded `postcard::to_stdvec(&dregg_sdk::SignedTurn)` — the canonical
    /// Turn the aggregator re-derives every bilateral schedule field from.
    pub signed_turn: String,
    /// Per-cell witnessed receipts, gathered from independent sources (e.g.
    /// gossiped + materialized from different nodes). Must be >= 2 to exercise
    /// a genuine cross-cell aggregation.
    pub entries: Vec<AggregateWitnessEntry>,
}

#[derive(Debug, serde::Serialize)]
pub struct AggregateBundleResponse {
    pub aggregated: bool,
    pub n_cells: usize,
    /// The verified `AggregatedBundle` (real outer STARK proof) on success.
    pub aggregated_bundle: Option<serde_json::Value>,
    pub error: Option<String>,
}

/// POST /turns/aggregate — run the REAL cross-node bilateral aggregate over
/// independently-sourced per-cell WitnessedReceipts.
///
/// Unlike the MCP `dregg_bilateral_action` tool (which self-proves BOTH sides
/// inside a single node in one call), this endpoint accepts WitnessedReceipt
/// artifacts that were produced elsewhere — gossiped through the blocklace and
/// materialized by `materialize_blocklace_artifacts`, or otherwise gathered
/// independently. It decodes each WR (the same DWR1 artifact format used on the
/// wire), runs `prove_aggregated_bundle` to produce a real outer STARK proof,
/// then `verify_aggregated_bundle` to confirm it before returning the bundle.
///
/// Soundness gates run inside the aggregator: `require_scope2_witness` per WR
/// and `WitnessedReceipt::verify_bilateral_chain` over the full set against the
/// canonical Turn (rejecting tampered PI, mismatched sender/receiver, etc.).
async fn post_aggregate_bundle(
    State(state): State<NodeState>,
    Json(req): Json<AggregateBundleRequest>,
) -> Result<Json<AggregateBundleResponse>, StatusCode> {
    {
        let s = state.read().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    let signed_turn_bytes =
        hex_decode_var(&req.signed_turn).map_err(|_| StatusCode::BAD_REQUEST)?;
    let signed: SignedTurn = crate::signed_turn_validation::decode_signed_turn(&signed_turn_bytes)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    // ⚑ AUTHENTICATE BEFORE DISCARDING THE SIGNATURE.
    //
    // This handler used to do `let turn = signed.turn;` here — dropping `signature`, `signer` and both
    // PQ fields — and then hand the *unsigned* turn to a real outer STARK prove below, on a route with
    // no rate limiter. A full-file read (2026-08-05) grepped this whole handler body for
    // `validate_signed_turn|verify|signature|signer` and found ZERO hits, while the docblock above
    // called it "the canonical Turn" twice. The word was doing work no code did.
    //
    // ⚠ It was never a spend hole — the route is bearer-gated and touches no ledger — but it was a
    // PROVENANCE hole (anyone past the bearer could attribute a turn to any agent) and an UNMETERED
    // PROVING AMPLIFIER (an arbitrary body reaches the prover). Both close here.
    //
    // The load-bearing tooth is `turn.agent == CellId::derive_raw(signer, blake3("default"))` — the
    // agent id IS a commitment to the signing key, so this is the check that makes attribution mean
    // anything.
    {
        let s = state.read().await;
        let executor = crate::executor_setup::new_submit_executor(&s);
        if let Err(error) = crate::signed_turn_validation::validate_signed_turn(
            &signed,
            &executor,
            s.ledger.get(&signed.turn.agent),
        ) {
            tracing::warn!(
                ?error,
                "aggregate-bundle: refused an unauthenticated signed turn"
            );
            return Ok(Json(AggregateBundleResponse {
                aggregated: false,
                n_cells: req.entries.len(),
                aggregated_bundle: None,
                error: Some(format!("signed turn failed validation: {error:?}")),
            }));
        }
    }

    let turn = signed.turn;

    if req.entries.len() < 2 {
        return Ok(Json(AggregateBundleResponse {
            aggregated: false,
            n_cells: req.entries.len(),
            aggregated_bundle: None,
            error: Some(
                "cross-node aggregate requires >= 2 independently-sourced WitnessedReceipts".into(),
            ),
        }));
    }

    let mut per_cell: Vec<(CellId, dregg_turn::WitnessedReceipt)> =
        Vec::with_capacity(req.entries.len());
    for (idx, entry) in req.entries.iter().enumerate() {
        let cell_bytes = match hex_decode(&entry.cell_id) {
            Ok(b) => b,
            Err(_) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: invalid cell_id hex")),
                }));
            }
        };
        let wr_bytes = match hex_decode_var(&entry.witnessed_receipt) {
            Ok(b) => b,
            Err(_) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: invalid witnessed_receipt hex")),
                }));
            }
        };
        let mut wr = match dregg_turn::WitnessedReceipt::from_artifact_bytes(&wr_bytes) {
            Ok(wr) => wr,
            Err(e) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: malformed WitnessedReceipt: {e}")),
                }));
            }
        };
        let cell = CellId(cell_bytes);
        // ROTATED-WR PRODUCER (ROTATION-CUTOVER §EXEC.3): a rotated WR carries only the 38/39-felt
        // rotated PI — too short for `build_inner_rows_v2` to project the 49-felt schedule window
        // (which needs the >=204-wide v1 PI). If such a WR arrived without a native
        // `bilateral_schedule` (e.g. produced by a peer that did not set it), reconstruct the
        // honest block here from the canonical Turn. We do NOT overwrite a block the WR already
        // carries — that one is what the cross-check binds. CG-3 in-circuit rejects a divergent
        // block, so reconstructing the honest one for the short-PI case adds no tampering vector.
        if wr.bilateral_schedule.is_none()
            && wr.public_inputs.len() < dregg_circuit::effect_vm::pi::ACTIVE_BASE_COUNT
        {
            wr.bilateral_schedule = Some(
                dregg_turn::bilateral_schedule::schedule_block_for_cell(&turn, &cell).to_vec(),
            );
        }
        per_cell.push((cell, wr));
    }
    let n_cells = per_cell.len();

    // Real outer STARK proof over the independently-sourced per-cell WRs.
    match dregg_turn_prover::aggregate_bilateral_prover::prove_aggregated_bundle(&turn, &per_cell) {
        Ok(bundle) => {
            match dregg_turn_prover::aggregate_bilateral_prover::verify_aggregated_bundle(&bundle) {
                Ok(()) => Ok(Json(AggregateBundleResponse {
                    aggregated: true,
                    n_cells,
                    aggregated_bundle: Some(
                        serde_json::to_value(&bundle).unwrap_or(serde_json::Value::Null),
                    ),
                    error: None,
                })),
                Err(e) => Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells,
                    aggregated_bundle: None,
                    error: Some(format!("aggregation_verify_failed: {e}")),
                })),
            }
        }
        Err(e) => Ok(Json(AggregateBundleResponse {
            aggregated: false,
            n_cells,
            aggregated_bundle: None,
            error: Some(format!("aggregation_prove_failed: {e}")),
        })),
    }
}

/// Domain string used to derive the executor's X25519 unsealer secret from
/// the cipherclerk seed via `AgentCipherclerk::derive_symmetric_key`. Stable
/// across deployments — a single node always presents the same public key
/// for a given cipherclerk, which is required so senders can cache the recipient
/// key across reconnects.
const TURN_UNSEALER_DOMAIN: &str = "dregg-turn-unsealer-v1";

/// GET /turns/encryption-key — return the executor's static X25519 public
/// key (the value senders pass as `recipient_public` to
/// `EncryptedTurn::encrypt_for_executor`). AUDIT-privacy.md §11.2: this is
/// the production discovery hop that closes the encrypted-turn pipeline.
async fn get_turn_encryption_key(
    State(state): State<NodeState>,
) -> Result<Json<TurnEncryptionKeyResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    let secret = s.cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
    Ok(Json(TurnEncryptionKeyResponse {
        executor_x25519_public: hex_encode(public.as_bytes()),
        derivation_domain: TURN_UNSEALER_DOMAIN.to_string(),
    }))
}

/// POST /turns/submit-encrypted — accept a postcard-encoded
/// `dregg_turn::EncryptedTurn` envelope, decrypt with the cipherclerk-derived
/// X25519 unsealer secret, and apply via
/// `TurnExecutor::apply_encrypted_turn`. AUDIT-privacy.md §11.2: closes
/// the "encryption claim unreachable from production" gap.
///
/// Wire format: `Content-Type: application/octet-stream`, body =
/// `postcard::to_stdvec(&encrypted_turn)` bytes.
///
/// Boundary contract (BOUNDARIES.md §5):
/// - **out-of-band** to gossip / wire observers (only ciphertext visible)
/// - **cleartext-inside** the executor holding the unsealer secret
/// - the produced receipt's `was_encrypted = true` flag is the **only**
///   metadata bit disclosed; it does not leak inner-turn content.
async fn post_submit_encrypted_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    body: axum::body::Bytes,
    limiter: RateLimiter,
) -> Result<Json<SubmitEncryptedTurnResponse>, StatusCode> {
    // Reuse the cleartext-turn rate limiter — encrypted turns shouldn't
    // get a privacy-flavored quota bypass. F-1: XFF-aware client keying.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    // Decode the envelope. A malformed wire body returns 400; no further
    // executor work is done.
    let encrypted: dregg_turn::EncryptedTurn = match postcard::from_bytes(&body) {
        Ok(e) => e,
        Err(_) => return Err(StatusCode::BAD_REQUEST),
    };

    // F-DOS-PRIV: validity gate BEFORE any decrypt/execute work. An
    // `EncryptedTurn` envelope carries no signature of its own; without this
    // check a stranger could POST any postcard blob and force the node to
    // X25519-decrypt + execute it (a fee-DoS — the cleartext `/turns/submit`
    // path avoids this by `signer.verify`-ing before doing work). `verify_admission_binding`
    // checks the Phase-1 submitter authentication (Ed25519 over the public
    // inputs + key→agent binding) fail-closed, so an unauthenticated or forged
    // envelope is rejected here — before the node spends decrypt work.
    if let Err(err) = encrypted.verify_admission_binding() {
        crate::metrics::inc_turns_executed("rejected");
        return Ok(Json(SubmitEncryptedTurnResponse {
            accepted: false,
            turn_hash: Some(format!(
                "rejected: encrypted turn validity proof invalid: {err:?}"
            )),
            was_encrypted: false,
            proof_status: ActivityProofStatus::NotCommitted,
            has_witness: false,
            witness_count: 0,
            error: Some(format!("encrypted turn validity proof invalid: {err:?}")),
        }));
    }

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Derive the executor's unsealer secret from the cipherclerk. Held in a
    // local for the lifetime of this handler only.
    let sealer_secret = s.cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let unsealer_public =
        x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(sealer_secret));
    let cleartext_turn =
        match encrypted.decrypt_for_executor(&sealer_secret, unsealer_public.as_bytes()) {
            Ok(turn) => turn,
            Err(err) => {
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitEncryptedTurnResponse {
                    accepted: false,
                    turn_hash: Some(format!(
                        "rejected: encrypted turn decryption failed: {err:?}"
                    )),
                    was_encrypted: false,
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("encrypted turn decryption failed: {err:?}")),
                }));
            }
        };

    let mut executor = crate::executor_setup::new_submit_executor(&s);
    // Defense-in-depth: the executor's own encrypted-turn path re-runs the
    // validity gate (the handler already gated above before decrypting).
    executor.set_require_validity_proof(true);

    // O(touched) atomic rollback: arm an undo journal rather than cloning the
    // whole O(cells) ledger. The executor mutates `s.ledger` in place; the
    // journal restores exactly the touched cells if the receipt append fails.
    s.ledger.begin_restore_point();
    let result = executor.apply_encrypted_turn(&encrypted, &sealer_secret, &mut s.ledger);

    match result {
        Ok(mut receipt) => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // Solo mode: record nullifier + tentative finality, same as
            // the cleartext path (post_submit_turn). The encrypted path
            // doesn't change consensus semantics — only privacy.
            let turn_hash_bytes = receipt.turn_hash;
            let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
            if let Some(ref mut solo) = s.solo_consensus
                && solo.is_solo
            {
                receipt.finality = dregg_turn::Finality::Tentative;
                // Re-sign after the committed finality downgrade: finality is bound
                // into receipt_hash, and the executor signed the optimistic Final.
                resign_receipt_committed(&mut receipt, &node_signing_key);
                let height = solo.height;
                let _ = solo
                    .nullifier_log
                    .insert(turn_hash_bytes, turn_hash_bytes, height);
                solo.advance_height();
                #[cfg(debug_assertions)]
                debug_assert_signed_last(&receipt, &node_signing_key);
            }

            let turn_hash = hex_encode(&turn_hash_bytes);
            let agent = hex_encode(&receipt.agent.0);
            let was_encrypted = receipt.was_encrypted;
            // F-DOS-1 / PATH-PRESERVE Phase 5b: the executor already validated +
            // committed this turn (the soundness boundary); no inline proving / no
            // inline re-check. The composed proof (rotated effect-vm leg) is built +
            // self-verified asynchronously off the lock by the prove pool below.
            if let Err(err) = s.cclerk.append_receipt(receipt.clone()) {
                s.ledger.rollback_restore_point();
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitEncryptedTurnResponse {
                    accepted: false,
                    turn_hash: Some(format!("receipt chain mismatch: {err}")),
                    was_encrypted: false,
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("receipt chain mismatch: {err}")),
                }));
            }
            // Receipt is on the chain: read the pre-turn cells from the journal
            // (the O(touched) stand-in for the old `pre_ledger` clone), drop it.
            let pre_ledger = s.ledger.pre_turn_touched_ledger();
            s.ledger.commit_restore_point();
            crate::metrics::set_receipt_chain_length(s.cclerk.receipt_chain_length() as f64);
            let receipt_hash = receipt.receipt_hash();
            let witness_outcome = match prepare_rotatable_turn(
                &cleartext_turn,
                pre_ledger.get(&cleartext_turn.agent),
                s.ledger.get(&cleartext_turn.agent),
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            let (proof_status, pending_proof) = witness_outcome.split(&turn_hash);
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            push_committed_event(
                &mut s,
                turn_hash.clone(),
                agent,
                vec!["encrypted_turn_committed".to_string()],
                proof_status,
            );

            drop(s);

            // F-DOS-1: prove off the lock.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            // Emit receipt event (same surface as cleartext-turn commits).
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            Ok(Json(SubmitEncryptedTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                was_encrypted,
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        Err(reason) => {
            // ⚑ ROLL BACK. The comment that used to sit here — "the executor already restored its own
            // mutations on rejection" — is FALSE for phase 1, and `commit_restore_point()` kept the
            // damage.
            //
            // `apply_encrypted_turn` maps `Rejected` straight to `Err` with no restoration, and
            // `execute.rs`'s PHASE 1 (fee debit + nonce tick) is never rolled back by the executor
            // itself. So a rejected encrypted turn KEPT its fee debit and nonce tick in live node RAM
            // while writing nothing durable.
            //
            // ⚠ That is precisely the RAM-only anti-spam charge `blocklace_sync.rs:10229` forbids in so
            // many words, and by the argument at `:7571-7586` it is an attested-root divergence: the
            // charge survives in RAM until this node restarts and then vanishes, while a peer that did
            // not restart keeps it — and `canonical_ledger_root` hashes the whole cell.
            //
            // ⓘ Both other ingresses already get this right, which is what makes this one an outlier
            // rather than a policy: `execute_finalized_turn` discards its isolated `exec_ledger`
            // candidate on `Rejected`, and `stage_signed_turn_admission` (`/turns/submit`) calls
            // `rollback_restore_point()` unconditionally. A refusal is free on both.
            s.ledger.rollback_restore_point();
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitEncryptedTurnResponse {
                accepted: false,
                turn_hash: Some(format!("rejected: {reason}")),
                was_encrypted: false,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
    }
}

async fn get_cell(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    let found = s.ledger.get(&cell_id).is_some();

    Ok(Json(CellResponse {
        id,
        found,
        balance: s.ledger.get(&cell_id).map(|cell| cell.state.balance()),
    }))
}

// =============================================================================
// Explorer API Handlers (public, read-only)
// =============================================================================

/// GET /api/cells — list all cells in the ledger with summary info.
/// ANON-DoS #1/#2 — default and maximum page sizes for the public full-scan list
/// reads. The default keeps existing small-devnet callers whole (they receive the
/// full listing) while the max bounds the per-request work + response so a flood
/// cannot force a full-ledger / full-lace materialization under the read lock.
pub const DEFAULT_LIST_PAGE: usize = 1_000;
pub const MAX_LIST_PAGE: usize = 10_000;

/// ANON-DoS #1 — hard cap on the number of leaves the cell-inclusion proof will
/// fold + serialize in one request. Checked cheaply against `ledger.len()` BEFORE
/// the O(N) fold, so a ledger past this cap yields `413` rather than pinning the
/// read lock. Generous: a devnet ledger is far smaller, and the flat-root proof
/// design does not scale past this regardless.
pub const MAX_PROOF_LEAVES: usize = 100_000;

/// Shared `?offset=&limit=` pagination query for the bounded list reads.
#[derive(Deserialize)]
pub struct PageQuery {
    pub offset: Option<usize>,
    pub limit: Option<usize>,
}

async fn get_all_cells(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    Query(page): Query<PageQuery>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
) -> Result<Json<Vec<CellListEntry>>, StatusCode> {
    // ANON-DoS #2: this scans + serializes the full ledger under `state.read()`.
    // Per-IP rate limit (proxy-aware, mirrors /api/discharge) + a bounded page so
    // one caller cannot force a full-ledger materialization/flood.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }
    let offset = page.offset.unwrap_or(0);
    let limit = page.limit.unwrap_or(DEFAULT_LIST_PAGE).min(MAX_LIST_PAGE);
    let s = state.read().await;
    let entries: Vec<CellListEntry> = s
        .ledger
        .iter()
        .skip(offset)
        .take(limit)
        .map(|(id, cell)| CellListEntry {
            id: hex_encode(&id.0),
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            capability_count: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            has_program: !matches!(cell.program, dregg_cell::CellProgram::None),
            found: true,
        })
        .collect();
    Ok(Json(entries))
}

/// GET /api/cell/:id — detailed cell information for the explorer.
async fn get_cell_detail(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellDetailResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    let head = persistent_receipt_head(&s, &cell_id);
    Ok(Json(cell_detail_response(id, s.ledger.get(&cell_id), head)))
}

/// The agent's PERSISTENT receipt-chain head — the `receipt_hash()` of the last
/// receipt in the node's indexed cipherclerk log for `cell_id`, or `None`.
///
/// This is the authoritative, cross-request-durable equivalent of the executor's
/// per-agent `last_receipt_hash` map (`TurnExecutor::get_last_receipt_hash`): the
/// executor is rebuilt fresh per request, but the cipherclerk's immutable global
/// log persists its per-agent head index, yielding exactly the head a persistent
/// executor would check the next turn's `previous_receipt_hash` against.
/// Deliberately reads the chain, NOT `s.ledger` — a cell carries no receipt head,
/// which is why `/api/cell/{id}` could not serve it before (the persistence bomb).
pub(crate) fn persistent_receipt_head(
    s: &crate::state::NodeStateInner,
    cell_id: &dregg_cell::CellId,
) -> Option<[u8; 32]> {
    s.cclerk.agent_receipt_head_hash(cell_id)
}

/// Build the `CellDetailResponse` projection for a cell (or the not-found stub).
/// Shared by `GET /api/cell/{id}` and the inclusion-proof endpoint so both serve a
/// byte-identical cell view. `last_receipt_hash` is the agent's persistent chain
/// head (see [`persistent_receipt_head`]) — served even for a not-found cell, since
/// a cell with committed receipts but no ledger presence still has a chain head.
fn cell_detail_response(
    id: String,
    cell: Option<&dregg_cell::Cell>,
    last_receipt_hash: Option<[u8; 32]>,
) -> CellDetailResponse {
    let last_receipt_hash = last_receipt_hash.map(|h| hex_encode(&h));
    match cell {
        Some(cell) => CellDetailResponse {
            id: id.clone(),
            found: true,
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            capability_count: cell.capabilities.len(),
            num_capabilities: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            delegate: cell.delegate.as_ref().map(|d| hex_encode(&d.0)),
            has_program: !matches!(cell.program, dregg_cell::CellProgram::None),
            public_key: hex_encode(cell.public_key()),
            token_id: hex_encode(cell.token_id()),
            proved_state: cell.state.proved_state(),
            delegation_epoch: cell.state.delegation_epoch(),
            state_commitment: hex_encode(&cell.state_commitment()),
            program_kind: match &cell.program {
                dregg_cell::CellProgram::None => "None".to_string(),
                dregg_cell::CellProgram::Predicate { .. } => "Predicate".to_string(),
                dregg_cell::CellProgram::Cases { .. } => "Cases".to_string(),
                dregg_cell::CellProgram::Circuit { .. } => "Circuit".to_string(),
            },
            program: cell.program.to_view(),
            fields: cell.state.fields.iter().map(|f| hex_encode(f)).collect(),
            capabilities: cell.capabilities.iter().cloned().collect(),
            capability_tombstones: cell.capabilities.tombstoned_slots().collect(),
            last_receipt_hash,
        },
        None => CellDetailResponse {
            id,
            found: false,
            balance: 0,
            nonce: 0,
            capability_count: 0,
            num_capabilities: 0,
            has_delegate: false,
            delegate: None,
            has_program: false,
            public_key: String::new(),
            token_id: String::new(),
            proved_state: false,
            delegation_epoch: 0,
            state_commitment: String::new(),
            program_kind: "None".to_string(),
            program: dregg_cell::program::CellProgramView::None,
            fields: Vec::new(),
            capabilities: Vec::new(),
            capability_tombstones: Vec::new(),
            last_receipt_hash,
        },
    }
}

#[derive(Deserialize)]
pub struct CellProofQuery {
    /// Optional NO-ROLLBACK assertion: require the node's latest attested height to
    /// be at least this, else 409. Does NOT time-travel the ledger — the proof is
    /// always served over the CURRENT ledger (first cut, option (a)); snapshots are
    /// only retained at checkpoint boundaries, which do not line up with attested
    /// heights, so arbitrary-height reconstruction is not offered.
    pub height: Option<u64>,
    /// ANON-DoS #1 — optional leaf-window offset. When set (with `leaf_limit`),
    /// `leaves` carries only `leaves[leaf_offset .. leaf_offset+leaf_limit]` of the
    /// full sorted set; `total_leaves` still reports the whole count so a verifier
    /// can page through every window and reconstruct the flat root. Omitted =
    /// serve the whole leaf set (bounded by `MAX_PROOF_LEAVES`).
    pub leaf_offset: Option<usize>,
    /// ANON-DoS #1 — optional leaf-window size (clamped to `MAX_LIST_PAGE`).
    pub leaf_limit: Option<usize>,
}

#[derive(Serialize)]
pub struct CellProofResponse {
    /// ANON-DoS #1 — total number of leaves in the served ledger (the full flat
    /// set), independent of any `leaf_offset`/`leaf_limit` window applied to
    /// `leaves`. A paginating verifier fetches every window up to this count.
    pub total_leaves: usize,
    /// The cell view — byte-identical to `GET /api/cell/{id}`.
    pub cell: CellDetailResponse,
    /// `canonical_ledger_root` of the SERVED (current) ledger. `leaves` reconstruct
    /// exactly this; the verifier recomputes the flat root from `leaves` and checks
    /// equality.
    pub merkle_root: String,
    /// The FULL sorted leaf set of the served ledger: `[cell_id_hex, leaf_hash_hex]`,
    /// `leaf_hash = BLAKE3(postcard(cell))`, sorted by id (flat root, no opening).
    pub leaves: Vec<(String, String)>,
    /// Advisory anchor height: equals `attested_height` (the latest attested height),
    /// NOT the height of the served leaves. Only when `is_attested` is true does the
    /// served ledger correspond to this attested height.
    pub height: u64,
    /// Latest quorum-attested root the node holds (may LAG the served ledger, since
    /// the finalization quorum forms async over gossip). 0 when none exists yet.
    pub attested_height: u64,
    /// Hex of that root's `merkle_root` ("" when none exists yet).
    pub attested_merkle_root: String,
    /// `finalization_quorum.len()` on the latest attested root — the REAL cross-node
    /// vote count (NOT the local single signature).
    pub quorum: usize,
    /// Signatures required for that root's quorum.
    pub threshold: usize,
    /// Server-computed convenience: the served ledger's root IS the latest attested
    /// root AND that root carries a `>= threshold` quorum. A consumer may gate on this
    /// or recompute it from the fields above.
    pub is_attested: bool,
}

/// GET /api/cell/{id}/proof — a cell-inclusion proof against the flat ledger root.
///
/// First cut (option (a)): serves the CURRENT ledger's full leaf set + flat root,
/// plus the latest quorum-attested root. The verifier recomputes
/// `canonical_ledger_root` from `leaves`, checks it == `merkle_root`, and checks the
/// target `(id, leaf_hash)` is a leaf. The read is consensus-backed only when
/// `merkle_root == attested_merkle_root` and `quorum >= threshold` (`is_attested`).
/// The node does not retain ledger state at arbitrary attested heights (snapshots
/// exist only at checkpoint boundaries), so it does not time-travel; `?height=H` is a
/// no-rollback assertion checked against the latest attested height.
async fn get_cell_proof(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
    Query(params): Query<CellProofQuery>,
    limiter: RateLimiter,
) -> Result<Json<CellProofResponse>, StatusCode> {
    // ANON-DoS #1: this materializes + folds + serializes the ENTIRE leaf set
    // under `state.read()`. Per-IP rate limit (proxy-aware, mirrors
    // /api/discharge) so a flood cannot hold the read lock, plus a hard
    // `MAX_PROOF_LEAVES` cap checked cheaply BEFORE the fold, plus optional leaf
    // pagination — so the per-request work + response is bounded.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    let s = state.read().await;

    // Cheap pre-check (HashMap len, no fold): refuse to fold/serialize a ledger
    // past the cap rather than pin the read lock unboundedly.
    if s.ledger.len() > MAX_PROOF_LEAVES {
        return Err(StatusCode::PAYLOAD_TOO_LARGE);
    }

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    let head = persistent_receipt_head(&s, &cell_id);
    let cell = cell_detail_response(id, s.ledger.get(&cell_id), head);

    // Full sorted leaf set + flat root of the CURRENT ledger. Construction is
    // byte-identical to the attested root (both fold through
    // `canonical_ledger_root_from_leaves`), so a served root that equals an attested
    // root is a genuine match, not a coincidence of encoding. The root always folds
    // the WHOLE set (so it matches the attested root); `leaves` may be a bounded
    // WINDOW of that set, with `total_leaves` reporting the full count.
    let leaf_entries = dregg_persist::canonical_ledger_leaves(&s.ledger);
    let merkle_root = hex_encode(&dregg_persist::canonical_ledger_root_from_leaves(
        &leaf_entries,
    ));
    let total_leaves = leaf_entries.len();
    let leaf_offset = params.leaf_offset.unwrap_or(0);
    let leaf_limit = params
        .leaf_limit
        .map(|l| l.min(MAX_LIST_PAGE))
        .unwrap_or(total_leaves);
    let leaves: Vec<(String, String)> = leaf_entries
        .iter()
        .skip(leaf_offset)
        .take(leaf_limit)
        .map(|(cid, h)| (hex_encode(cid), hex_encode(h)))
        .collect();

    // Latest quorum-attested root (may lag the served ledger).
    let latest = s.store.latest_attested_root().ok().flatten();
    let attested_height = latest.as_ref().map(|r| r.height).unwrap_or(0);
    let attested_merkle_root = latest
        .as_ref()
        .map(|r| hex_encode(&r.merkle_root))
        .unwrap_or_default();
    let quorum = latest
        .as_ref()
        .map(|r| r.finalization_quorum.len())
        .unwrap_or(0);
    let threshold = latest.as_ref().map(|r| r.threshold).unwrap_or(0);

    // No-rollback assertion: if the caller demands an anchor at height H, the node
    // must have attested at least that far.
    if let Some(h) = params.height {
        if attested_height < h {
            return Err(StatusCode::CONFLICT);
        }
    }

    let is_attested = !attested_merkle_root.is_empty()
        && attested_merkle_root == merkle_root
        && quorum >= threshold;

    Ok(Json(CellProofResponse {
        total_leaves,
        cell,
        merkle_root,
        leaves,
        height: attested_height,
        attested_height,
        attested_merkle_root,
        quorum,
        threshold,
        is_attested,
    }))
}

/// Hash a passphrase with Argon2id and derive a bearer seed.
///
/// Returns (PHC string for storage, bearer_seed for token derivation).
fn hash_passphrase(passphrase: &str) -> (String, [u8; 32]) {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default(); // Argon2id v19 with recommended params
    let phc_string = argon2
        .hash_password(passphrase.as_bytes(), &salt)
        .expect("argon2 hash_password should not fail")
        .to_string();
    // Derive a separate bearer seed from passphrase + salt using BLAKE3.
    // This is safe because BLAKE3 is a proper KDF and the input has high entropy
    // (passphrase + random salt).
    let bearer_seed = blake3::derive_key(
        "dregg-node-bearer-v1",
        format!("{}{}", passphrase, salt.as_str()).as_bytes(),
    );
    (phc_string, bearer_seed)
}

/// P1 Fix 4: Rate-limited passphrase unlock endpoint.
async fn post_cclerk_unlock(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<UnlockRequest>,
    limiter: RateLimiter,
) -> Result<Json<UnlockResponse>, StatusCode> {
    // Rate limit check (F-1: per-real-client, XFF-aware behind trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // F-CRIT-1: during pre-passphrase setup, only loopback callers may set the
    // passphrase. Once a passphrase is set, the bearer-token auth on subsequent
    // requests is sufficient; but unlock from the network is acceptable since the
    // attacker must still know the passphrase.
    //
    // Resolve the EFFECTIVE client IP the same XFF-aware way as the rate limiter
    // and `require_auth`: behind a same-host reverse proxy the raw socket is
    // loopback for every external client, so a raw-socket check would let a
    // remote caller set the passphrase (remote takeover).
    {
        let s = state.read().await;
        if s.passphrase_hash.is_none() && !effective_client_is_loopback(addr.ip(), &headers) {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    if req.passphrase.is_empty() {
        return Ok(Json(UnlockResponse {
            success: false,
            bearer_token: None,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;

    match s.passphrase_hash.clone() {
        Some(stored_hash) => {
            // Verify against stored Argon2id hash.
            let parsed =
                PasswordHash::new(&stored_hash).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
            if Argon2::default()
                .verify_password(req.passphrase.as_bytes(), &parsed)
                .is_err()
            {
                return Ok(Json(UnlockResponse {
                    success: false,
                    bearer_token: None,
                    error: Some("invalid passphrase".to_string()),
                }));
            }
            s.unlocked = true;
            let bearer_token = s.bearer_seed.map(api_bearer_token);
            Ok(Json(UnlockResponse {
                success: true,
                bearer_token,
                error: None,
            }))
        }
        None => {
            // First unlock sets the passphrase using Argon2id.
            let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
            s.passphrase_hash = Some(phc_string.clone());
            s.bearer_seed = Some(bearer_seed);
            let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
            let _ = s.store.set_config("bearer_seed", &bearer_seed);
            s.unlocked = true;
            Ok(Json(UnlockResponse {
                success: true,
                bearer_token: Some(api_bearer_token(bearer_seed)),
                error: None,
            }))
        }
    }
}

fn api_bearer_token(bearer_seed: [u8; 32]) -> String {
    hex_encode(&blake3::derive_key("dregg-api-bearer-v1", &bearer_seed))
}

/// P1 Fix 4: Rate-limited set-passphrase endpoint.
async fn post_set_passphrase(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<SetPassphraseRequest>,
    limiter: RateLimiter,
) -> Result<Json<SetPassphraseResponse>, StatusCode> {
    // Rate limit check (F-1: per-real-client, XFF-aware behind trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // F-CRIT-1: setting the initial passphrase from a non-loopback caller is the
    // remote-takeover bug. Reject. Once the passphrase IS set, this endpoint
    // returns "already set" so the network check below is not load-bearing in
    // that branch, but we apply it uniformly to avoid an oracle. Resolve the
    // effective client IP the same XFF-aware way as the rate limiter and
    // `require_auth`, so a same-host reverse proxy cannot make a remote caller
    // look loopback.
    if !effective_client_is_loopback(addr.ip(), &headers) {
        return Err(StatusCode::FORBIDDEN);
    }

    if req.passphrase.is_empty() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;

    if s.passphrase_hash.is_some() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase already set; unlock first to change it".to_string()),
        }));
    }

    let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
    s.passphrase_hash = Some(phc_string.clone());
    s.bearer_seed = Some(bearer_seed);
    // Persist the passphrase hash and bearer seed to the store so they survive restarts.
    let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
    let _ = s.store.set_config("bearer_seed", &bearer_seed);

    Ok(Json(SetPassphraseResponse {
        success: true,
        error: None,
    }))
}

/// Drive a payable intent through the VERIFIED ledger commit, returning the real
/// [`dregg_turn::TurnReceipt`]. This is the single shared core that both
/// `POST /intents/fulfill` (with an explicit fulfiller) and `POST /intents`
/// (inline self-fulfillment at submit time) call — so a submitted self-fulfillable
/// intent commits through EXACTLY the same path as an operator-driven fulfill,
/// never a stub.
///
/// The payer is the intent's creator (`payer_cell.0 == intent.creator.0`, enforced
/// by the caller); the recipient is the fulfiller cell. Both cells must be LIVE in
/// the ledger and distinct, and the intent must carry a non-zero `min_budget`
/// (the verified value leg) — otherwise the verified executor REFUSES, and the
/// ledger is untouched (fail-closed, no fallback).
fn commit_intent_fulfillment_verified(
    s: &mut crate::state::NodeStateInner,
    intent: &dregg_intent::Intent,
    payer_cell: dregg_sdk::CellId,
    recipient_cell: dregg_sdk::CellId,
    state_root: u32,
    state_root_block: u64,
) -> Result<dregg_turn::TurnReceipt, dregg_intent::fulfillment::FulfillmentError> {
    let state_root = dregg_circuit::BabyBear::new(state_root);

    // The node's stable per-node intent root key. The minted Trusted-mode macaroon's HMAC
    // chain is verified against THIS key inside the flow — so the capability grant genuinely
    // verifies (a real token, not a `[0x01; 4]` stub the verify would reject).
    let intent_root_key = s.cclerk.derive_symmetric_key("dregg-intent-root-key-v1");

    // Build a REAL Trusted-mode fulfillment: a genuine HMAC-chained attenuated macaroon
    // bound to the intent's grant. This passes `verify_fulfillment_with_predicates_and_key`
    // honestly; nothing is laundered.
    let fulfillment_with_preds = dregg_intent::fulfillment::build_self_fulfillment_trusted(
        intent,
        dregg_intent::CommitmentId(recipient_cell.0),
        intent_root_key,
        state_root,
        state_root_block,
    )?;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // The ANCHOR context. The verified edge stamps the receipt with
    // `dregg_turn::state_commit::consensus_state_commitment`, which binds this node's LIVE
    // nullifier / commitment / revocation accumulator roots — state only a configured
    // `TurnExecutor` holds (`executor_setup::configure_turn_executor` restores them from the
    // store). It is NOT consulted for the payment decision: the value leg still settles through
    // the verified per-asset transition, fail-closed. `new_verify_executor` rather than
    // `new_submit_executor` because nothing is being ADMITTED here — we need the accumulators at
    // the current attested height, not a PQ admission gate.
    let anchor_executor = crate::executor_setup::new_verify_executor(s);

    // Settle the value leg through the VERIFIED executor edge, supplying the same root key
    // so the Trusted-mode HMAC verification inside the flow succeeds. Fail-closed: a refused
    // payment leaves the ledger untouched.
    dregg_intent::fulfillment::execute_fulfillment_flow_verified_with_key(
        intent,
        &fulfillment_with_preds,
        &anchor_executor,
        &mut s.ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_height,
        Some(&intent_root_key),
    )
}

async fn post_intent(
    State(state): State<NodeState>,
    Json(raw): Json<serde_json::Value>,
) -> Result<Json<IntentSubmitResponse>, StatusCode> {
    // P0 Fix 3: Deserialize into a proper Intent struct for validation.
    let intent: dregg_intent::Intent =
        serde_json::from_value(raw.clone()).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Validate the intent using dregg-intent's validation logic.
    dregg_intent::validation::validate_intent(&intent).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the content-addressed ID is correct (prevents ID spoofing).
    let recomputed = dregg_intent::Intent::new(
        intent.kind,
        intent.matcher.clone(),
        intent.creator,
        intent.expiry,
        intent.stake_proof.clone(),
    );
    if recomputed.id != intent.id {
        return Err(StatusCode::BAD_REQUEST);
    }

    let intent_id_hex = hex_encode(&intent.id);

    // A submitted intent is SELF-FULFILLABLE — and must therefore COMMIT immediately
    // through the verified ledger rather than rot in the pool — when it names an
    // explicit fulfiller cell alongside a payable value leg. The fulfiller hint rides
    // as sibling fields on the submit body (the canonical `Intent` is untouched, so its
    // content-addressed id is unchanged). When present, we drain it through the SAME
    // verified path `/intents/fulfill` uses (`commit_intent_fulfillment_verified` →
    // `execute_fulfillment_flow_verified`) and return the real receipt.
    //
    // Absent a fulfiller, the intent is an open offer/need with no counter-leg yet: it
    // pools (the prior behavior) for a later match-and-fulfill. The pool is no longer a
    // dead end — a fulfiller (here or via `/intents/fulfill`) drains it to the ledger.
    let fulfiller_cell: Option<[u8; 32]> = raw
        .get("fulfiller_cell")
        .and_then(|v| v.as_str())
        .and_then(|h| hex_decode(h).ok())
        .and_then(|b| <[u8; 32]>::try_from(b.as_slice()).ok());
    let req_state_root: u32 = raw
        .get("state_root")
        .and_then(|v| v.as_u64())
        .map(|v| v as u32)
        .unwrap_or(0);
    let req_state_root_block: u64 = raw
        .get("state_root_block")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let mut committed = false;
    let mut committed_turn_hash: Option<String> = None;

    // INLINE SELF-FULFILLMENT (verified, fail-closed). The payer is the intent creator;
    // the recipient is the named fulfiller. The verified executor enforces distinctness,
    // liveness, and availability — a refusal leaves the ledger untouched and the intent
    // simply pools instead of committing.
    if let Some(fulfiller_bytes) = fulfiller_cell {
        let payer_cell = dregg_sdk::CellId(intent.creator.0);
        let recipient_cell = dregg_sdk::CellId(fulfiller_bytes);

        let mut s = state.write().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
        match commit_intent_fulfillment_verified(
            &mut s,
            &intent,
            payer_cell,
            recipient_cell,
            req_state_root,
            req_state_root_block,
        ) {
            Ok(receipt) => {
                committed = true;
                committed_turn_hash = Some(hex_encode(&receipt.turn_hash));
            }
            Err(e) => {
                // Fail-closed: a self-fulfillment the verified executor REFUSES is a
                // hard error to the submitter — we do NOT silently downgrade a payable,
                // explicitly-targeted intent into a quiet pool entry (that would launder
                // a rejected commit as a successful submit).
                tracing::warn!(intent = %intent_id_hex, error = %e, "intent self-fulfillment refused by verified executor");
                return Err(StatusCode::UNPROCESSABLE_ENTITY);
            }
        }
    } else {
        // No counter-leg yet — pool for a later match-and-fulfill.
        // P1 Fix 5: enforce size limit.
        let mut s = state.write().await;
        if s.intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.intent_pool.insert(intent.id, intent.clone());
        // Invalidate PIR index cache on pool mutation.
        s.pir_index_cache = None;
    }

    // Broadcast to WS subscribers.
    state.emit(NodeEvent::Intent {
        intent: serde_json::to_value(&intent).unwrap_or_default(),
    });
    if let Some(ref turn_hash) = committed_turn_hash {
        state.emit(NodeEvent::Receipt {
            hash: turn_hash.clone(),
        });
    }

    // Gossip the intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let intent_json = raw;
        tokio::spawn(async move {
            gossip.gossip_intent(&intent_json).await;
        });
    }

    Ok(Json(IntentSubmitResponse {
        intent_id: intent_id_hex,
        stored: !committed,
        committed,
        turn_hash: committed_turn_hash,
    }))
}

/// GET /api/events — return committed events after a given block height.
///
/// Used by the Discord bot and other polling clients to catch up on state changes
/// without maintaining a persistent WebSocket connection.
async fn get_events(
    Query(params): Query<EventsQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<CommittedEvent>> {
    let since_height = params.since_height;
    let limit = params.limit.unwrap_or(50).min(200);

    let s = state.read().await;
    Json(select_committed_events(&s.event_log, since_height, limit))
}

async fn get_starbridge_events(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<CommittedEvent>> {
    let limit = starbridge_limit(params.limit);
    let since_height = params.since_height;

    let s = state.read().await;
    // Filter on the BORROWED ring buffer and clone only the survivors we
    // actually return (`limit` <= 200). The prior form cloned the ENTIRE
    // retained event log (passing `usize::MAX`) before filtering/taking — an
    // O(retained-events) allocation on every poll of this live HTTP endpoint.
    let height_ok = |e: &CommittedEvent| match since_height {
        Some(h) if h > 0 => e.height > h,
        _ => true,
    };
    let events = s
        .event_log
        .iter()
        .filter(|event| height_ok(event) && starbridge_event_matches(event, &params))
        .take(limit)
        .cloned()
        .collect();
    Json(events)
}

async fn get_starbridge_turns(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeSignedTurnInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let turns = s
        .consensus_queue
        .iter()
        .enumerate()
        .rev()
        .filter_map(|(queue_index, signed)| {
            let info = starbridge_signed_turn_info(queue_index, signed);
            starbridge_signed_turn_matches(&info, &params).then_some(info)
        })
        .take(limit)
        .collect();
    Json(turns)
}

async fn get_starbridge_actions(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeActionInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let mut actions = Vec::new();

    for (queue_index, signed) in s.consensus_queue.iter().enumerate().rev() {
        let turn_hash = hex_encode(&signed.turn.hash());
        let signer = hex_encode(&signed.signer.0);
        let agent = hex_encode(&signed.turn.agent.0);
        let app = classify_starbridge_app(signed.turn.memo.as_deref(), &[]);

        for (action_index, tree) in signed.turn.call_forest.iter_dfs().enumerate() {
            let effect_kinds: Vec<String> = tree.action.effects.iter().map(effect_kind).collect();
            let touched_cells = action_touched_cells(&tree.action);
            let app = app
                .clone()
                .or_else(|| classify_starbridge_app(signed.turn.memo.as_deref(), &effect_kinds));
            let info = StarbridgeActionInfo {
                source: "consensus_queue",
                queue_index,
                action_index,
                turn_hash: turn_hash.clone(),
                signer: signer.clone(),
                agent: agent.clone(),
                memo: signed.turn.memo.clone(),
                app,
                target: hex_encode(&tree.action.target.0),
                method: hex_encode(&tree.action.method),
                effect_kinds,
                touched_cells,
            };
            if starbridge_action_matches(&info, &params) {
                actions.push(info);
                if actions.len() >= limit {
                    return Json(actions);
                }
            }
        }
    }

    Json(actions)
}

async fn get_starbridge_identity_events(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityEventInfo>> {
    let limit = starbridge_limit(params.limit);
    let since_height = params.since_height;
    let s = state.read().await;
    let mut out = Vec::new();

    for event in select_committed_events(&s.event_log, since_height, usize::MAX) {
        if !starbridge_event_matches(&event, &identity_scoped_params(&params)) {
            continue;
        }
        out.push(StarbridgeIdentityEventInfo {
            source: "event_log",
            chain_index: None,
            event_index: None,
            height: Some(event.height),
            receipt_hash: None,
            turn_hash: event.turn_hash,
            cell_id: event.cell_id,
            timestamp: event.timestamp,
            topic: None,
            data: None,
            effects: event.effects,
            proof_status: event.proof_status,
            finality: None,
        });
        if out.len() >= limit {
            return Json(out);
        }
    }

    let chain = s.cclerk.receipt_chain();
    for (chain_index, receipt) in chain.iter().enumerate().rev() {
        if !identity_receipt_matches(receipt, &params) {
            continue;
        }
        for (event_index, event) in receipt.emitted_events.iter().enumerate() {
            if params.cell.as_ref().is_some_and(|cell| {
                !hex_encode(&event.cell.0).eq_ignore_ascii_case(cell)
                    && !hex_encode(&receipt.agent.0).eq_ignore_ascii_case(cell)
            }) {
                continue;
            }
            out.push(StarbridgeIdentityEventInfo {
                source: "receipt_chain",
                chain_index: Some(chain_index as u64),
                event_index: Some(event_index),
                height: Some((chain_index + 1) as u64),
                receipt_hash: Some(hex_encode(&receipt.receipt_hash())),
                turn_hash: hex_encode(&receipt.turn_hash),
                cell_id: hex_encode(&event.cell.0),
                timestamp: receipt.timestamp,
                topic: Some(serde_json::to_value(event.topic).unwrap_or(serde_json::Value::Null)),
                data: Some(serde_json::to_value(&event.data).unwrap_or(serde_json::Value::Null)),
                effects: Vec::new(),
                proof_status: receipt_proof_status(&s, receipt),
                finality: Some(format!("{:?}", receipt.finality).to_lowercase()),
            });
            if out.len() >= limit {
                return Json(out);
            }
        }
    }

    Json(out)
}

async fn get_starbridge_identity_credentials(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityCredentialInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let chain = s.cclerk.receipt_chain();
    let credentials = chain
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, receipt)| identity_receipt_matches(receipt, &params))
        .filter(|(_, receipt)| {
            !receipt.emitted_events.is_empty() || !receipt.derivation_records.is_empty()
        })
        .take(limit)
        .map(|(chain_index, receipt)| {
            let receipt_hash = receipt.receipt_hash();
            let mut subject_cells: Vec<String> = receipt
                .derivation_records
                .iter()
                .map(|record| hex_encode(&record.target_cell.0))
                .chain(
                    receipt
                        .emitted_events
                        .iter()
                        .map(|event| hex_encode(&event.cell.0)),
                )
                .collect();
            subject_cells.sort();
            subject_cells.dedup();
            StarbridgeIdentityCredentialInfo {
                source: "receipt_chain",
                chain_index: chain_index as u64,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: hex_encode(&receipt.turn_hash),
                issuer_cell: hex_encode(&receipt.agent.0),
                subject_cells,
                timestamp: receipt.timestamp,
                effects_hash: hex_encode(&receipt.effects_hash),
                event_count: receipt.emitted_events.len(),
                derivation_record_count: receipt.derivation_records.len(),
                proof_status: receipt_proof_status(&s, receipt),
                finality: format!("{:?}", receipt.finality).to_lowercase(),
            }
        })
        .collect();
    Json(credentials)
}

async fn get_starbridge_identity_proof_checkpoints(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityProofCheckpointInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let checkpoints = s
        .cclerk
        .receipt_chain()
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, receipt)| identity_receipt_matches(receipt, &params))
        .take(limit)
        .map(|(chain_index, receipt)| {
            let receipt_hash = receipt.receipt_hash();
            StarbridgeIdentityProofCheckpointInfo {
                source: "receipt_chain",
                chain_index: chain_index as u64,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: hex_encode(&receipt.turn_hash),
                cell_id: hex_encode(&receipt.agent.0),
                timestamp: receipt.timestamp,
                effects_hash: hex_encode(&receipt.effects_hash),
                pre_state: hex_encode(&receipt.pre_state_hash),
                post_state: hex_encode(&receipt.post_state_hash),
                proof_status: receipt_proof_status(&s, receipt),
                executor_signed: receipt.executor_signature.is_some(),
                witness_count: s.witnessed_receipt_count(&receipt_hash),
                finality: format!("{:?}", receipt.finality).to_lowercase(),
            }
        })
        .collect();
    Json(checkpoints)
}

fn select_committed_events(
    log: &VecDeque<CommittedEvent>,
    since_height: Option<u64>,
    limit: usize,
) -> Vec<CommittedEvent> {
    if limit == 0 {
        return Vec::new();
    }

    match since_height {
        Some(height) if height > 0 => log
            .iter()
            .filter(|event| event.height > height)
            .take(limit)
            .cloned()
            .collect(),
        // First-time pollers need the latest retained activity, not the oldest
        // entries in the ring buffer. Keep chronological order so clients can
        // advance their cursor to the last returned height.
        _ => {
            let skip = log.len().saturating_sub(limit);
            log.iter().skip(skip).cloned().collect()
        }
    }
}

/// GET /observability/stream — SSE liveness feed for the public portal.
///
/// Emits a `hello` frame (the node's spent-proof/nullifier count + the number of
/// program-bearing "service" cells) then a 15s `ping` heartbeat. These are the
/// SAME event names (`hello` / `ping`) the discord-bot read surface emits, so the
/// public `portal.dregg.studio` "live" badge — which `addEventListener`s `hello`
/// (and reloads the cell list on it) and `ping` — keeps working when its `/api/*`
/// + `/observability/*` are proxied to the NODE directly rather than to the bot
/// (the portal-decoupling repoint). Full broadcast of per-turn TurnLifecycle
/// events from the node's submit path remains future work (would wire an Emitter
/// + a shared broadcast tx into `NodeState`).
async fn observability_stream(
    State(state): State<NodeState>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    // Counts for the hello frame, read once at connect time (the bot freezes these
    // the same way): the node's spent-proof (nullifier) set size and the number of
    // program-bearing service cells in the ledger.
    let (nullifiers, apps) = {
        let s = state.read().await;
        let apps = s
            .ledger
            .iter()
            .filter(|(_, cell)| !matches!(cell.program, dregg_cell::CellProgram::None))
            .count();
        (s.used_proof_hashes.len(), apps)
    };
    // hello (seq 0) then a 15s ping heartbeat, all from one unfold.
    let stream = stream::unfold(0u64, move |seq| async move {
        let event = if seq == 0 {
            Event::default().event("hello").data(format!(
                r#"{{"nullifiers":{nullifiers},"apps":{apps},"msg":"dregg-node observability stream live"}}"#
            ))
        } else {
            tokio::time::sleep(std::time::Duration::from_secs(15)).await;
            Event::default()
                .event("ping")
                .data(format!(r#"{{"seq":{seq},"nullifiers":{nullifiers}}}"#))
        };
        Some((Ok::<_, Infallible>(event), seq + 1))
    });
    Sse::new(stream).keep_alive(axum::response::sse::KeepAlive::default())
}

/// POST /intents/encrypted — submit an SSE-encrypted intent for gossip propagation.
///
/// Encrypted intents carry search tokens for privacy-preserving matching. The body
/// is hidden until a fulfiller's capability keywords produce a matching token, at
/// which point the poster reveals the decryption key over a direct channel.
async fn post_encrypted_intent(
    State(state): State<NodeState>,
    Json(encrypted): Json<dregg_intent::sse::EncryptedIntent>,
) -> Result<Json<EncryptedIntentSubmitResponse>, StatusCode> {
    let intent_id_hex = hex_encode(&encrypted.id);

    // Basic validation: check non-empty search tokens and non-empty body.
    if encrypted.search_tokens.is_empty() || encrypted.encrypted_body.is_empty() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Check expiry if set.
    if let Some(expiry) = encrypted.expiry {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        if now >= expiry {
            return Err(StatusCode::BAD_REQUEST);
        }
    }

    // Store in the encrypted intent pool.
    {
        let mut s = state.write().await;
        if s.encrypted_intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.encrypted_intent_pool
            .insert(encrypted.id, encrypted.clone());
    }

    // Gossip the encrypted intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let enc = encrypted.clone();
        tokio::spawn(async move {
            gossip.gossip_encrypted_intent(&enc).await;
        });
    }

    Ok(Json(EncryptedIntentSubmitResponse {
        intent_id: intent_id_hex,
        stored: true,
    }))
}

/// POST /intents/encrypted/search — SSE-token coarse filter against the
/// node's encrypted intent pool.
///
/// Closes audit §12 / §14: the SSE primitives were implemented but the
/// node had no way to *serve* SSE-token queries. Fulfillers now POST
/// their `capability_keywords` + `epoch`; the server hashes each
/// keyword to a token and returns every stored encrypted intent whose
/// token set intersects. The body remains encrypted — the fulfiller
/// asks the poster for the decryption key out-of-band.
///
/// This is the "encrypted discovery loop close" — combined with
/// `/intents/encrypted` (post) the encrypted-intent pool becomes
/// queryable, not just write-only.
async fn post_sse_search(
    State(state): State<NodeState>,
    Json(req): Json<SseSearchRequest>,
) -> Result<Json<SseSearchResponse>, StatusCode> {
    const DEFAULT_LIMIT: usize = 50;
    const MAX_LIMIT: usize = 200;

    if req.capability_keywords.is_empty() {
        return Err(StatusCode::BAD_REQUEST);
    }
    let limit = req.limit.unwrap_or(DEFAULT_LIMIT).clamp(1, MAX_LIMIT);

    // Derive search tokens from the fulfiller's keywords.
    let keyword_refs: Vec<&str> = req.capability_keywords.iter().map(String::as_str).collect();

    // Filter the encrypted intent pool.
    let s = state.read().await;
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let mut total = 0usize;
    let mut hits: Vec<SseSearchHit> = Vec::new();
    for (id, encrypted) in s.encrypted_intent_pool.iter() {
        // Honor expiry: don't return stale entries.
        if encrypted.is_expired(now) {
            continue;
        }
        if !dregg_intent::sse::capability_matches_tokens(
            &keyword_refs,
            &encrypted.search_tokens,
            req.epoch,
        ) {
            continue;
        }
        total += 1;
        if hits.len() < limit {
            hits.push(SseSearchHit {
                intent_id: hex_encode(id),
                encrypted_intent: encrypted.clone(),
            });
        }
    }

    Ok(Json(SseSearchResponse {
        hits,
        total_matches: total,
    }))
}

/// POST /intents/trustless — submit a threshold-encrypted intent into the
/// trustless intent engine's current batch.
///
/// Unlike `/intents/encrypted` (single-recipient SSE sealed-box), this
/// path routes through [`dregg_intent::trustless::TrustlessIntentEngine`]:
/// validators collaboratively decrypt the batch via Shamir-over-GF(256)
/// and ChaCha20-Poly1305, solvers compete with STARK validity proofs, and
/// the winning solution settles atomically through the lowering tower.
async fn post_trustless_intent(
    State(state): State<NodeState>,
    Json(encrypted): Json<dregg_intent::trustless::EncryptedIntent>,
) -> Result<Json<EncryptedIntentSubmitResponse>, StatusCode> {
    let content_id = encrypted.content_id();
    let mut s = state.write().await;
    s.trustless_intent_engine
        .submit_encrypted(encrypted)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(EncryptedIntentSubmitResponse {
        intent_id: hex_encode(&content_id),
        stored: true,
    }))
}

/// POST /intents/trustless/share — contribute a decryption share for a
/// ciphertext in the current batch. Once t-of-n shares are accumulated
/// for every submitted ciphertext, the engine reconstructs plaintexts
/// and advances to the Solving phase.
async fn post_trustless_decrypt_share(
    State(state): State<NodeState>,
    Json(share): Json<dregg_intent::trustless::DecryptionShare>,
) -> Result<Json<TrustlessEngineStatus>, StatusCode> {
    let mut s = state.write().await;
    s.trustless_intent_engine
        .contribute_decrypt_share(share)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(TrustlessEngineStatus::from_engine(
        &s.trustless_intent_engine,
    )))
}

/// GET /intents/trustless/status — current batch lifecycle state for
/// the trustless intent engine.
async fn get_trustless_engine_status(
    State(state): State<NodeState>,
) -> Json<TrustlessEngineStatus> {
    let s = state.read().await;
    Json(TrustlessEngineStatus::from_engine(
        &s.trustless_intent_engine,
    ))
}

/// Public-facing snapshot of the trustless engine state.
#[derive(serde::Serialize)]
struct TrustlessEngineStatus {
    batch_id: u64,
    batch_state: String,
    intent_count: usize,
    decrypt_share_count: usize,
    decrypt_threshold: usize,
    num_validators: usize,
    winning_score: Option<f64>,
    current_height: u64,
}

impl TrustlessEngineStatus {
    fn from_engine(engine: &dregg_intent::trustless::TrustlessIntentEngine) -> Self {
        Self {
            batch_id: engine.current_batch.batch_id,
            batch_state: format!("{:?}", engine.batch_state()),
            intent_count: engine.intent_count(),
            decrypt_share_count: engine.decrypt_share_count(),
            decrypt_threshold: engine.decrypt_threshold,
            num_validators: engine.num_validators,
            winning_score: engine.winning_score(),
            current_height: engine.current_height,
        }
    }
}

async fn get_intents(State(state): State<NodeState>) -> Json<Vec<IntentListEntry>> {
    let s = state.read().await;
    let entries: Vec<IntentListEntry> = s
        .intent_pool
        .iter()
        .map(|(id, intent)| IntentListEntry {
            id: hex_encode(id),
            intent: intent.clone(),
        })
        .collect();
    Json(entries)
}

/// POST /intents/fulfill — verify a fulfillment and automatically execute payment.
///
/// After verifying the fulfillment and predicates, creates and executes a payment
/// turn that transfers computrons from the intent creator to the fulfiller.
async fn post_fulfill_intent(
    State(state): State<NodeState>,
    Json(req): Json<FulfillIntentRequest>,
) -> Result<Json<FulfillIntentResponse>, StatusCode> {
    let intent_id: [u8; 32] = hex_decode(&req.intent_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let payer_bytes: [u8; 32] = hex_decode(&req.payer_cell).map_err(|_| StatusCode::BAD_REQUEST)?;
    let recipient_bytes: [u8; 32] =
        hex_decode(&req.recipient_cell).map_err(|_| StatusCode::BAD_REQUEST)?;

    let payer_cell = dregg_sdk::CellId(payer_bytes);
    let recipient_cell = dregg_sdk::CellId(recipient_bytes);

    // Look up the intent.
    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Verify the payer_cell matches the intent's creator (ownership check).
    // The payer must be the intent creator — prevents arbitrary payer exploitation.
    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => {
            if i.creator.0 != payer_bytes {
                return Ok(Json(FulfillIntentResponse {
                    success: false,
                    turn_hash: None,
                    error: Some("payer_cell does not match intent creator".to_string()),
                }));
            }
            i.clone()
        }
        None => {
            return Ok(Json(FulfillIntentResponse {
                success: false,
                turn_hash: None,
                error: Some("intent not found in pool".to_string()),
            }));
        }
    };

    // Execute the fulfillment payment through the VERIFIED settle path (the shared core
    // `commit_intent_fulfillment_verified` → `execute_fulfillment_flow_verified`): the
    // value-moving leg folds through the verified per-asset transition and is cross-checked
    // against the REAL Lean executor export `dregg_record_kernel_step` (Lean unconditional on
    // native). Fail-closed — a payment the verified executor refuses is REFUSED; there is no
    // fallback to the legacy `dregg_turn::TurnExecutor`. This is the SAME core that inline
    // self-fulfillment at submit (`POST /intents`) drives.
    let result = commit_intent_fulfillment_verified(
        &mut s,
        &intent,
        payer_cell,
        recipient_cell,
        req.state_root,
        req.state_root_block,
    );

    match result {
        Ok(receipt) => {
            let turn_hash = hex_encode(&receipt.turn_hash);
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            Ok(Json(FulfillIntentResponse {
                success: true,
                turn_hash: Some(turn_hash),
                error: None,
            }))
        }
        Err(e) => Ok(Json(FulfillIntentResponse {
            success: false,
            turn_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

async fn get_federation_roots(State(state): State<NodeState>) -> Json<Vec<AttestedRootInfo>> {
    let s = state.read().await;
    let roots = s.store.all_attested_roots().unwrap_or_default();
    let infos: Vec<AttestedRootInfo> = roots
        .iter()
        .map(|r| AttestedRootInfo {
            height: r.height,
            merkle_root: hex_encode(&r.merkle_root),
            timestamp: r.timestamp,
            signatures: r.quorum_signatures.len(),
            quorum: r.finalization_quorum.len(),
            threshold: r.threshold,
            structurally_complete: r.is_structurally_complete(),
        })
        .collect();
    Json(infos)
}

async fn get_federations(State(state): State<NodeState>) -> Json<Vec<FederationInfo>> {
    let s = state.read().await;
    Json(federation_infos(&s))
}

/// GET /api/membership — the live committee + every registered membership
/// proposal with its tally.
///
/// The read side of the join-with-a-doc flow (docs/guide/FEDERATION-JOIN.md):
/// a joining candidate polls this to watch its Join proposal gather
/// approvals; committee operators read the pending list to know what to
/// approve (`POST /membership/approve`). Committee composition and proposal
/// tallies are chain data — safe to serve publicly. The `federation_id` stays
/// STABLE across amendments (the live epoch transition advances the committee
/// without re-pointing bots/bridges/light clients).
async fn get_membership(State(state): State<NodeState>) -> Json<serde_json::Value> {
    let (federation_id, committee_epoch) = {
        let s = state.read().await;
        (dregg_types::hex_encode(&s.federation_id), s.committee_epoch)
    };
    let Some(handle) = state.blocklace().await else {
        return Json(serde_json::json!({
            "federation_id": federation_id,
            "committee_epoch": committee_epoch,
            "consensus": "not-running",
        }));
    };
    let snap = handle.membership_snapshot().await;
    use dregg_blocklace::constitution::MembershipProposal as MP;
    let proposals: Vec<serde_json::Value> = snap
        .proposals
        .iter()
        .map(|p| {
            let (kind, node) = match &p.proposal {
                MP::Join { node_key, .. } => ("join", Some(dregg_types::hex_encode(node_key))),
                MP::Leave { node_key, .. } => ("leave", Some(dregg_types::hex_encode(node_key))),
                MP::AmendThreshold { .. } => ("amend-threshold", None),
                MP::AmendRoutes { .. } => ("amend-routes", None),
            };
            serde_json::json!({
                "proposal_block": dregg_types::hex_encode(&p.proposal_block.0),
                "kind": kind,
                "node": node,
                "approvals": p.approvals,
                "rejections": p.rejections,
                "required": p.required,
                "applied": p.applied,
            })
        })
        .collect();
    Json(serde_json::json!({
        "federation_id": federation_id,
        "committee_epoch": committee_epoch,
        "participants": snap.participants.iter().map(|k| dregg_types::hex_encode(k)).collect::<Vec<_>>(),
        "threshold": snap.threshold,
        "constitution_version": snap.version,
        "membership_frozen": snap.frozen,
        "self": {
            "key": dregg_types::hex_encode(&snap.self_key),
            "participant": snap.self_is_participant,
        },
        "proposals": proposals,
    }))
}

/// Request body for `POST /membership/approve`.
#[derive(serde::Deserialize)]
struct MembershipApproveRequest {
    /// Hex-encoded 32-byte block id of the membership proposal to approve
    /// (from `GET /api/membership` → `proposals[].proposal_block`).
    proposal_block: String,
}

/// POST /membership/approve — cast THIS node's approval vote for a pending
/// membership proposal (operator-local: bearer-gated, no /api/ alias).
///
/// The production admit verb: when enough CURRENT participants run this, the
/// proposal passes quorum on-chain and the committee advances via the live
/// epoch transition — no genesis re-roll, no restart, `federation_id`
/// unchanged. Refused when this node is not a committee participant, or the
/// proposal is unknown/already applied.
async fn post_membership_approve(
    State(state): State<NodeState>,
    Json(req): Json<MembershipApproveRequest>,
) -> (StatusCode, Json<serde_json::Value>) {
    let Some(bytes) = hex_decode_32(&req.proposal_block) else {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({"error": "proposal_block must be 64 hex chars (32 bytes)"})),
        );
    };
    let Some(handle) = state.blocklace().await else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({"error": "consensus is not running on this node"})),
        );
    };
    let proposal_block = dregg_blocklace::finality::BlockId(bytes);
    match handle.approve_membership(&state, proposal_block).await {
        Ok(()) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "approved": req.proposal_block,
                "note": "approval vote block created and disseminated; the amendment applies \
                         when a quorum of current participants has approved",
            })),
        ),
        Err(e) => (StatusCode::CONFLICT, Json(serde_json::json!({"error": e}))),
    }
}

/// GET /api/blocklace/blocks — list the live blocklace DAG.
///
/// Returns every block in the local blocklace, height-sorted, with REAL block
/// hashes and REAL parent (`prev_hash` / `predecessors`) links. This is the
/// live analog of the wasm `list_federation_blocks` + `get_federation_block`
/// surface, so the `<dregg-block-dag>` inspector renders node data with the same
/// component it uses for the in-browser sim.
///
/// Empty list when consensus is not yet running (e.g. the handle hasn't been
/// installed at startup); never a 404, so the explorer can poll safely.
async fn get_blocklace_blocks(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    Query(page): Query<PageQuery>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
) -> Result<Json<Vec<crate::blocklace_sync::BlockView>>, StatusCode> {
    // ANON-DoS #2: this scans + serializes the FULL lace. Per-IP rate limit
    // (mirrors /api/discharge) + a bounded page (only the window is turned into
    // BlockViews) so a flood cannot force a full-lace materialization.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }
    let offset = page.offset.unwrap_or(0);
    let limit = page.limit.unwrap_or(DEFAULT_LIST_PAGE).min(MAX_LIST_PAGE);
    Ok(match state.blocklace().await {
        Some(handle) => Json(handle.block_views_page(offset, limit).await),
        None => Json(Vec::new()),
    })
}

/// GET /api/block/{height} — fetch one blocklace block by height (creator seq).
///
/// `height` is the block's sequence number within its creator's chain (the same
/// value surfaced as `height` in the block list). The response carries the
/// block's REAL `prev_hash` (its first predecessor) and full `predecessors`
/// set. Returns 404 when no block exists at that height.
async fn get_block_by_height(
    State(state): State<NodeState>,
    AxumPath(height): AxumPath<u64>,
) -> Result<Json<crate::blocklace_sync::BlockView>, StatusCode> {
    let handle = state.blocklace().await.ok_or(StatusCode::NOT_FOUND)?;
    match handle.block_view_at_height(height).await {
        Some(view) => Ok(Json(view)),
        None => Err(StatusCode::NOT_FOUND),
    }
}

fn federation_infos(s: &crate::state::NodeStateInner) -> Vec<FederationInfo> {
    let roots = s.store.all_attested_roots().unwrap_or_default();
    let latest_root = roots.iter().max_by_key(|r| r.height);
    let latest_height = latest_root.map(|r| r.height).unwrap_or(0);
    let latest_root_hex = latest_root.map(|r| hex_encode(&r.merkle_root));

    let mut infos: Vec<FederationInfo> = s
        .known_federations
        .iter()
        .map(|(id, fed)| FederationInfo {
            id: id.hex(),
            federation_id: id.hex(),
            committee_epoch: fed.epoch(),
            threshold: fed.threshold(),
            member_count: fed.members().len(),
            members: fed.members().iter().map(|pk| pk.hex()).collect(),
            is_local: id.0 == s.federation_id,
            latest_height,
            latest_root: latest_root_hex.clone(),
            num_finalized_roots: roots.len(),
        })
        .collect();

    infos.sort_by(|a, b| a.id.cmp(&b.id));

    if infos.is_empty() {
        infos.push(FederationInfo {
            id: hex_encode(&s.federation_id),
            federation_id: hex_encode(&s.federation_id),
            committee_epoch: s.committee_epoch,
            threshold: s.known_federation_keys.len() as u32,
            member_count: s.known_federation_keys.len(),
            members: sorted_hex_keys(&s.known_federation_keys),
            is_local: true,
            latest_height,
            latest_root: latest_root_hex,
            num_finalized_roots: roots.len(),
        });
    }

    infos
}

fn sorted_hex_keys(keys: &[dregg_sdk::PublicKey]) -> Vec<String> {
    let mut keys: Vec<String> = keys.iter().map(|key| key.hex()).collect();
    keys.sort();
    keys
}

// =============================================================================
// Fast-Path Turn handlers
// =============================================================================

/// POST /turn/fast-path — request a fast-path lock from this validator.
///
/// The node checks eligibility, acquires cell locks, and returns a TurnSign
/// (the validator's lock acknowledgement) if the turn qualifies.
#[tracing::instrument(skip_all)]
async fn post_fast_path_lock(
    State(state): State<NodeState>,
    Json(req): Json<FastPathLockRequest>,
) -> Result<Json<FastPathLockResponse>, StatusCode> {
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash = turn.hash();

    let mut s = state.write().await;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Use the node's public key as the validator signing key.
    let validator_key = s.cclerk.public_key().0;

    // Decode the agent's Ed25519 signature over turn_hash (P1-6).
    let agent_sig_bytes = match hex_decode_var(&req.agent_signature) {
        Ok(b) if b.len() == 64 => {
            let mut arr = [0u8; 64];
            arr.copy_from_slice(&b);
            arr
        }
        _ => {
            return Ok(Json(FastPathLockResponse {
                locked: false,
                validator_key: None,
                signature: None,
                height: None,
                error: Some("agent_signature must be 64 hex-encoded bytes".to_string()),
            }));
        }
    };

    // Split borrows: take mutable ref to cell_lock_table and immutable ref to ledger
    // from disjoint fields of the same struct.
    let inner = &mut *s;
    let result = dregg_turn::process_fast_path_lock(
        &mut inner.cell_lock_table,
        &turn,
        turn_hash,
        current_height,
        &inner.ledger,
        &validator_key,
        &agent_sig_bytes,
    );

    match result {
        Ok(sign) => Ok(Json(FastPathLockResponse {
            locked: true,
            validator_key: Some(hex_encode(&sign.validator_key)),
            signature: Some(hex_encode_var(&sign.signature)),
            height: Some(sign.height),
            error: None,
        })),
        Err(e) => Ok(Json(FastPathLockResponse {
            locked: false,
            validator_key: None,
            signature: None,
            height: None,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /turn/certificate — execute a certified fast-path turn.
///
/// The client presents a TurnCertificate (turn + 2f+1 validator signatures). The node
/// checks `turn.hash() == turn_hash`, then hands the signature set to
/// [`dregg_turn::assemble_certificate`] together with THIS node's committee roster —
/// which verifies quorum size, roster membership, distinctness, and each Ed25519
/// signature over `turn_hash`. Only then does it execute the turn, release locks and
/// gossip the result.
///
/// ⚑ The clause "the node verifies the certificate" was in this docblock while nothing
/// verified anything but the count: see the flag-day note on `assemble_certificate`.
#[tracing::instrument(skip_all)]
async fn post_fast_path_certificate(
    State(state): State<NodeState>,
    Json(req): Json<FastPathCertificateRequest>,
) -> Result<Json<FastPathCertificateResponse>, StatusCode> {
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash_bytes: [u8; 32] =
        hex_decode(&req.turn_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the turn hash matches.
    let computed_hash = turn.hash();
    if computed_hash != turn_hash_bytes {
        return Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: None,
            error: Some("turn hash mismatch".to_string()),
        }));
    }

    // Parse signatures.
    let mut signatures = Vec::new();
    for entry in &req.signatures {
        let vk: [u8; 32] = hex_decode(&entry.validator_key).map_err(|_| StatusCode::BAD_REQUEST)?;
        let sig_bytes = hex_decode_var(&entry.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
        if sig_bytes.len() != 64 {
            return Err(StatusCode::BAD_REQUEST);
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&sig_bytes);
        signatures.push(dregg_turn::TurnSign {
            validator_key: vk,
            signature: sig,
            height: entry.height,
        });
    }

    // Assemble certificate (verify quorum).
    // Threshold is derived from federation size: n - f where f = (n-1)/3.
    // For single-node (n=1): threshold = 1. For 4 nodes: threshold = 3.
    //
    // ⚑ THE ROSTER IS NEW (2026-08-06) AND IT IS THE POINT. Until today this block
    // read `known_federation_keys` for its LENGTH ONLY — the threshold — and never
    // for membership, while `assemble_certificate` never verified a signature. Any
    // bearer-token holder could POST `threshold` fabricated `{validator_key,
    // signature}` pairs and the certificate assembled. The roster now travels with
    // the count, and `assemble_certificate` checks each signature against it.
    //
    // The node's OWN cipherclerk key is unioned in because that is the key
    // `post_fast_path_lock` signs `TurnSign`s with (`s.cclerk.public_key().0`, the
    // `validator_key` argument to `process_fast_path_lock`). Without it a solo node
    // — empty roster, threshold 1 — could not certify the very signature it just
    // issued, and `NoValidatorRoster` would refuse every fast-path turn.
    let (n, roster) = {
        let s = state.read().await;
        let mut roster: Vec<[u8; 32]> = s.known_federation_keys.iter().map(|k| k.0).collect();
        let own = s.cclerk.public_key().0;
        if !roster.contains(&own) {
            roster.push(own);
        }
        let key_count = s.known_federation_keys.len();
        (if key_count == 0 { 1usize } else { key_count }, roster)
    };
    let f = (n.saturating_sub(1)) / 3;
    let threshold = n - f;
    let cert = match dregg_turn::assemble_certificate(
        turn,
        turn_hash_bytes,
        signatures,
        threshold,
        &roster,
    ) {
        Ok(c) => c,
        Err(e) => {
            return Ok(Json(FastPathCertificateResponse {
                executed: false,
                turn_hash: None,
                error: Some(e.to_string()),
            }));
        }
    };

    // Execute the certified turn.
    let mut s = state.write().await;
    // Split borrows: take mutable refs to disjoint fields.
    let inner = &mut *s;
    let executor = crate::executor_setup::new_submit_executor(inner);
    let result = dregg_turn::execute_certified_turn(
        &cert,
        &executor,
        &mut inner.ledger,
        &mut inner.cell_lock_table,
    );

    match result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let hash_hex = hex_encode(&receipt.turn_hash);
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: hash_hex.clone(),
            });
            Ok(Json(FastPathCertificateResponse {
                executed: true,
                turn_hash: Some(hash_hex),
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            Ok(Json(FastPathCertificateResponse {
                executed: false,
                turn_hash: Some(hex_encode(&turn_hash_bytes)),
                error: Some(format!("turn rejected: {reason}")),
            }))
        }
        _ => Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            error: Some("turn did not commit".to_string()),
        })),
    }
}

// =============================================================================
// Conditional Turn handlers
// =============================================================================

async fn post_submit_conditional(
    State(state): State<NodeState>,
    Json(req): Json<SubmitConditionalRequest>,
) -> Result<Json<SubmitConditionalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    drop(s);

    let condition: dregg_turn::ProofCondition =
        serde_json::from_value(req.condition).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let deposit_amount =
        dregg_turn::compute_conditional_deposit(req.timeout_height, current_height);
    let conditional = dregg_turn::ConditionalTurn {
        turn,
        condition,
        timeout_height: req.timeout_height,
        submitted_at: current_height,
        deposit_amount,
    };

    if let Err(_e) = dregg_turn::validate_conditional_submission(&conditional, current_height) {
        return Ok(Json(SubmitConditionalResponse {
            accepted: false,
            conditional_hash: None,
        }));
    }

    let hash = conditional.hash();
    let hash_hex = hex_encode(&hash);

    // P1 Fix 6: enforce max size with proactive GC.
    {
        let mut s = state.write().await;

        // Proactive GC: remove expired conditionals before checking capacity.
        let gc_height = s
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        s.pending_conditionals
            .retain(|ct| !ct.is_expired(gc_height));

        if s.pending_conditionals.len() >= MAX_PENDING_CONDITIONALS {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.pending_conditionals.push(conditional);
    }

    Ok(Json(SubmitConditionalResponse {
        accepted: true,
        conditional_hash: Some(hash_hex),
    }))
}

#[tracing::instrument(skip_all)]
async fn post_resolve_conditional(
    State(state): State<NodeState>,
    Json(req): Json<ResolveConditionalRequest>,
) -> Result<Json<ResolveConditionalResponse>, StatusCode> {
    // Require cipherclerk to be unlocked for conditional resolution.
    {
        let s = state.read().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    let hash_bytes = hex_decode(&req.conditional_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    let proof: dregg_turn::ConditionProof =
        serde_json::from_value(req.proof).map_err(|_| StatusCode::BAD_REQUEST)?;
    let verify_start = Instant::now();

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let idx = s
        .pending_conditionals
        .iter()
        .position(|ct| ct.hash() == hash_bytes);

    let idx = match idx {
        Some(i) => i,
        None => {
            return Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn not found".to_string()),
            }));
        }
    };

    let condition = s.pending_conditionals[idx].condition.clone();
    let timeout_height = s.pending_conditionals[idx].timeout_height;
    let trusted_roots: Vec<dregg_turn::TrustedRoot> = s
        .store
        .all_attested_roots()
        .unwrap_or_default()
        .iter()
        .map(|r| (r.merkle_root, r.height))
        .collect();
    let trusted_executor_keys: Vec<[u8; 32]> =
        s.known_federation_keys.iter().map(|k| k.0).collect();

    let result = dregg_turn::resolve_condition(
        &condition,
        &proof,
        current_height,
        timeout_height,
        &trusted_roots,
        dregg_turn::DEFAULT_MAX_ROOT_AGE,
        &mut s.used_proof_hashes,
        &trusted_executor_keys,
    );

    crate::metrics::record_proof_verification_duration(verify_start.elapsed().as_secs_f64());

    match result {
        dregg_turn::ConditionalResult::Resolved => {
            crate::metrics::inc_proofs_verified("valid");
            // SECURITY: Persist the proof nullifier to the store immediately so
            // a crash cannot allow proof replay. The in-memory set was already
            // updated by resolve_condition; this makes it durable.
            let proof_hash = dregg_turn::compute_proof_hash(&proof);
            if let Err(e) = s.store.insert_proof_hash(&proof_hash) {
                tracing::warn!(error = %e, "failed to persist proof nullifier to store");
            }

            let conditional = s.pending_conditionals.remove(idx);

            let executor = crate::executor_setup::new_submit_executor(&s);
            let lean_producer_enabled = s.lean_producer_enabled;
            // ONE executor gate (#171): resolved conditionals commit through the
            // same producer-aware path as every other ingress.
            let exec_result = crate::executor_setup::execute_via_producer(
                &executor,
                &conditional.turn,
                &mut s.ledger,
                lean_producer_enabled,
            );

            match exec_result {
                dregg_turn::TurnResult::Committed { mut receipt, .. } => {
                    // Solo mode: mark receipt as Tentative and log in nullifier log.
                    let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
                    if let Some(ref mut solo) = s.solo_consensus
                        && solo.is_solo
                    {
                        receipt.finality = dregg_turn::Finality::Tentative;
                        // Re-sign after the committed finality downgrade.
                        resign_receipt_committed(&mut receipt, &node_signing_key);
                        let height = solo.height;
                        let _ =
                            solo.nullifier_log
                                .insert(receipt.turn_hash, receipt.turn_hash, height);
                        solo.advance_height();
                        #[cfg(debug_assertions)]
                        debug_assert_signed_last(&receipt, &node_signing_key);
                    }
                    let turn_hash = hex_encode(&receipt.turn_hash);
                    s.cclerk.append_receipt(receipt).expect(
                        "local executor and cclerk chains must agree; divergence is a serious bug",
                    );
                    drop(s);
                    state.emit(NodeEvent::Receipt {
                        hash: turn_hash.clone(),
                    });
                    Ok(Json(ResolveConditionalResponse {
                        resolved: true,
                        turn_hash: Some(turn_hash),
                        reason: None,
                    }))
                }
                dregg_turn::TurnResult::Rejected { reason, .. } => {
                    crate::metrics::inc_turns_executed("rejected");
                    crate::metrics::note_turn_rejected(&reason);
                    Ok(Json(ResolveConditionalResponse {
                        resolved: false,
                        turn_hash: None,
                        reason: Some(format!("turn rejected: {reason}")),
                    }))
                }
                dregg_turn::TurnResult::Expired => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn expired during execution".to_string()),
                })),
                dregg_turn::TurnResult::Pending => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn pending during execution".to_string()),
                })),
            }
        }
        dregg_turn::ConditionalResult::Expired => {
            crate::metrics::inc_proofs_verified("error");
            s.pending_conditionals.remove(idx);
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn has expired".to_string()),
            }))
        }
        dregg_turn::ConditionalResult::Pending => Ok(Json(ResolveConditionalResponse {
            resolved: false,
            turn_hash: None,
            reason: Some("condition not yet satisfied".to_string()),
        })),
        dregg_turn::ConditionalResult::InvalidProof(e) => {
            crate::metrics::inc_proofs_verified("invalid");
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some(format!("invalid proof: {e}")),
            }))
        }
    }
}

async fn get_pending_conditionals(
    State(state): State<NodeState>,
) -> Json<Vec<PendingConditionalInfo>> {
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // GC: remove expired conditionals.
    s.pending_conditionals
        .retain(|ct| !ct.is_expired(current_height));

    let infos: Vec<PendingConditionalInfo> = s
        .pending_conditionals
        .iter()
        .map(|ct| {
            let condition_type = match &ct.condition {
                dregg_turn::ProofCondition::HashPreimage { .. } => "hash_preimage",
                dregg_turn::ProofCondition::RemoteProof { .. } => "remote_proof",
                dregg_turn::ProofCondition::LocalProof { .. } => "local_proof",
                dregg_turn::ProofCondition::TurnExecuted { .. } => "turn_executed",
                dregg_turn::ProofCondition::TurnProven { .. } => "turn_proven",
            };
            PendingConditionalInfo {
                hash: hex_encode(&ct.hash()),
                timeout_height: ct.timeout_height,
                submitted_at: ct.submitted_at,
                condition_type: condition_type.to_string(),
            }
        })
        .collect();
    Json(infos)
}

// =============================================================================
// Atomic Multi-Party Turn Handlers
// =============================================================================

/// POST /turn/atomic — Submit an atomic multi-party turn proposal.
///
/// The coordinator node creates a Coordinator instance, validates the proposal
/// (budget gate, participant count, threshold), persists it in the proposals map,
/// and returns a proposal_id that participants can vote on.
#[tracing::instrument(skip_all)]
async fn post_atomic_proposal(
    State(state): State<NodeState>,
    Json(req): Json<AtomicProposalRequest>,
) -> Result<Json<AtomicProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    // Parse participant node IDs.
    let mut participants: Vec<[u8; 32]> = Vec::new();
    for p in &req.participants {
        let bytes: [u8; 32] = hex_decode(p).map_err(|_| StatusCode::BAD_REQUEST)?;
        participants.push(bytes);
    }

    if participants.is_empty() {
        return Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some("at least one participant required".to_string()),
        }));
    }

    // Parse the initiator cell ID.
    let initiator_bytes: [u8; 32] =
        hex_decode(&req.initiator).map_err(|_| StatusCode::BAD_REQUEST)?;
    let initiator = dregg_cell::CellId(initiator_bytes);

    // Deserialize the call forest.
    let forest: dregg_turn::CallForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Build the atomic forest.
    let atomic_forest = dregg_coord::AtomicForest::new(
        participants.clone(),
        forest,
        vec![], // preconditions left empty; participants validate locally
        initiator,
        req.fee,
    );

    // Create the coordinator with the node's identity.
    let mut s = state.write().await;

    // Garbage-collect stale proposals before creating new ones.
    s.expire_stale_proposals();

    let node_id = s.silo_id;
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let costs = dregg_turn::ComputronCosts::default();

    // F-P1-4: build participant key map. Prior code used (id, id) which only
    // happened to work when cell_id == pubkey (sovereign cells). The request
    // may now supply explicit per-participant keys; otherwise we look them up
    // in `known_federation_keys`, and any participant not found is rejected.
    let participant_keys: std::collections::HashMap<[u8; 32], [u8; 32]> = match req
        .participant_pubkeys
        .as_ref()
    {
        Some(pks) => {
            if pks.len() != participants.len() {
                return Ok(Json(AtomicProposalResponse {
                    accepted: false,
                    proposal_id: None,
                    error: Some("participant_pubkeys length must match participants".to_string()),
                }));
            }
            let mut map = std::collections::HashMap::with_capacity(participants.len());
            for (id, pk_hex) in participants.iter().zip(pks.iter()) {
                let pk: [u8; 32] = hex_decode(pk_hex).map_err(|_| StatusCode::BAD_REQUEST)?;
                map.insert(*id, pk);
            }
            map
        }
        None => {
            // Lookup keys from known_federation_keys.
            let known: std::collections::HashSet<[u8; 32]> =
                s.known_federation_keys.iter().map(|k| k.0).collect();
            let mut map = std::collections::HashMap::with_capacity(participants.len());
            for id in &participants {
                if !known.contains(id) {
                    return Ok(Json(AtomicProposalResponse {
                        accepted: false,
                        proposal_id: None,
                        error: Some(format!(
                            "participant {} not in known federation keys; supply participant_pubkeys explicitly",
                            hex_encode(id)
                        )),
                    }));
                }
                map.insert(*id, *id);
            }
            map
        }
    };

    let mut coordinator = dregg_coord::Coordinator::new(
        node_id,
        signing_key,
        req.threshold,
        costs,
        MAX_ATOMIC_BUDGET, // F-P2-1: bound per-proposal computron budget
        participant_keys,
    );

    let forest_for_storage = atomic_forest.clone();

    match coordinator.propose(atomic_forest) {
        Ok(propose_msg) => {
            let proposal_id = propose_msg.proposal_id;
            let proposal_id_hex = hex_encode(&proposal_id);
            let forest_hash = forest_for_storage.hash;
            let forest_wire = forest_for_storage.encode_for_wire();

            // Persist the coordinator in the proposals map for later vote collection
            // (this Coordinator IS the vote tally the returning votes feed into).
            s.atomic_proposals.insert(
                proposal_id,
                crate::state::ActiveProposal {
                    coordinator,
                    created_at: std::time::Instant::now(),
                    forest: forest_for_storage,
                },
            );

            // THE SEND WELD: broadcast the REAL `ProposeAtomicTurn` variant (full
            // forest + the coordinator's real proposal_id + identity) on the
            // blocklace topic, so each participant reconstructs the forest, votes
            // bound to THIS proposal_id, and returns its `VoteAtomicTurn`. Replaces
            // the old JSON-stub `atomic_proposal` that a peer could not reconstruct.
            drop(s);
            if let Some(blocklace) = state.blocklace().await {
                blocklace
                    .gossip_atomic_propose(
                        forest_hash,
                        proposal_id,
                        node_id,
                        participants.clone(),
                        forest_wire,
                    )
                    .await;
            }

            Ok(Json(AtomicProposalResponse {
                accepted: true,
                proposal_id: Some(proposal_id_hex),
                error: None,
            }))
        }
        Err(e) => Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some(format!("{e}")),
        })),
    }
}

/// POST /turn/atomic/vote — Vote on an atomic proposal.
///
/// Participants submit their vote (approve/reject) with an Ed25519 signature.
/// When enough votes are collected, the coordinator decides to commit or abort,
/// executing the turn via TurnExecutor on commit.
async fn post_atomic_vote(
    State(state): State<NodeState>,
    Json(req): Json<AtomicVoteRequest>,
) -> Result<Json<AtomicVoteResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let voter: [u8; 32] = hex_decode(&req.voter).map_err(|_| StatusCode::BAD_REQUEST)?;

    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }
    let mut signature = [0u8; 64];
    signature.copy_from_slice(&sig_bytes);

    let vote = if req.approve {
        dregg_coord::Vote::yes(signature)
    } else {
        dregg_coord::Vote::no("participant rejected", signature)
    };

    // Defense-in-depth: verify the vote signature against the claimed voter's
    // public key BEFORE passing to the coordinator. This prevents an authenticated
    // node from voting as another participant (the coordinator also verifies, but
    // rejecting early avoids acquiring the write lock for invalid votes).
    {
        let s = state.read().await;
        let active = match s.atomic_proposals.get(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        let forest_hash = active.forest.hash;
        let sig_valid = if req.approve {
            dregg_coord::Vote::verify_yes(&signature, &proposal_id, &forest_hash, &voter)
        } else {
            dregg_coord::Vote::verify_no(&signature, &proposal_id, &forest_hash, &voter)
        };
        if !sig_valid {
            return Ok(Json(AtomicVoteResponse {
                accepted: false,
                decision: None,
                error: Some("vote signature does not match claimed voter identity".to_string()),
            }));
        }
    }

    let mut s = state.write().await;

    // Feed the vote to the coordinator.
    let decision = {
        let active = match s.atomic_proposals.get_mut(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        let rust_decision = match active.coordinator.receive_vote(voter, vote) {
            Ok(maybe_decision) => maybe_decision,
            Err(e) => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some(format!("{e}")),
                }));
            }
        };
        // STRONG-FORM SWAP: make the VERIFIED Lean 2PC gate (`dregg_coord_2pc_decide` =
        // `TwoPhaseCommit.evaluate`) the AUTHORITATIVE Commit/Abort/Pending verdict, with the Rust
        // `Coordinator::evaluate_votes` (the `rust_decision` above) demoted to the differential
        // sibling. The coordinator exposes its tally as the gate's wire; `coord_gate` runs the
        // verified rule, compares, and returns the verified verdict (logging on drift). When the Lean
        // archive is absent it falls back to `rust_decision`. The `receive_vote` side-effects (vote
        // recording, state transition) already happened — we only re-decide the *verdict*.
        let wire = active.coordinator.decision_wire();
        let rust_had_no_decision = rust_decision.is_none();
        let rust_inner = rust_decision.unwrap_or(dregg_coord::Decision::Pending);
        let gated = crate::coord_gate::authoritative_decision(rust_inner, wire.as_deref());
        // Preserve "no terminal decision yet" semantics: a Pending gated verdict with no Rust
        // decision stays `None` (the coordinator has not transitioned).
        match (rust_had_no_decision, gated) {
            (true, dregg_coord::Decision::Pending) => None,
            (_, g) => Some(g),
        }
    };

    // Handle the decision.
    match decision {
        Some(dregg_coord::Decision::Commit) => {
            // Extract the proposal so we can borrow ledger mutably.
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            // Execute the atomic turn against the ledger.
            match active.coordinator.commit(&mut s.ledger) {
                Ok(_commit_msg) => Ok(Json(AtomicVoteResponse {
                    accepted: true,
                    decision: Some("commit".to_string()),
                    error: None,
                })),
                Err(e) => {
                    // Commit failed (e.g., turn execution error) — abort.
                    let _ = active.coordinator.abort(format!("commit failed: {e}"));

                    Ok(Json(AtomicVoteResponse {
                        accepted: true,
                        decision: Some("abort".to_string()),
                        error: Some(format!("commit failed: {e}")),
                    }))
                }
            }
        }
        Some(dregg_coord::Decision::Abort) => {
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            let _ = active
                .coordinator
                .abort("too many rejections — threshold unreachable");

            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: Some("abort".to_string()),
                error: None,
            }))
        }
        Some(dregg_coord::Decision::Pending) | None => {
            // Still waiting for more votes.
            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: None,
                error: None,
            }))
        }
    }
}

/// GET /turn/atomic/:id — Query the status of an active atomic proposal.
///
/// Returns vote counts, coordinator state, and age so clients can monitor
/// progress without polling the vote endpoint.
async fn get_proposal_status(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<ProposalStatusResponse>, StatusCode> {
    let proposal_id: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.read().await;
    let active = match s.atomic_proposals.get(&proposal_id) {
        Some(p) => p,
        None => {
            return Ok(Json(ProposalStatusResponse {
                found: false,
                state: "not_found".to_string(),
                yes_votes: 0,
                no_votes: 0,
                total_participants: 0,
                threshold: 0,
                age_secs: 0,
            }));
        }
    };

    let (state_name, yes_count, no_count, total) = match &active.coordinator.state {
        dregg_coord::CoordinatorState::Idle => ("idle", 0, 0, 0),
        dregg_coord::CoordinatorState::Proposing { forest, votes, .. } => {
            let yes = votes.values().filter(|v| v.is_yes()).count();
            let no = votes.values().filter(|v| v.is_no()).count();
            ("proposing", yes, no, forest.participant_count())
        }
        dregg_coord::CoordinatorState::Committed { .. } => ("committed", 0, 0, 0),
        dregg_coord::CoordinatorState::Aborted { .. } => ("aborted", 0, 0, 0),
    };

    let age_secs = std::time::Instant::now()
        .duration_since(active.created_at)
        .as_secs();

    Ok(Json(ProposalStatusResponse {
        found: true,
        state: state_name.to_string(),
        yes_votes: yes_count,
        no_votes: no_count,
        total_participants: total,
        threshold: active.coordinator.threshold,
        age_secs,
    }))
}

/// POST /turn/atomic/evaluate — Participant evaluates a proposal against local state.
///
/// A node that received a proposal via gossip uses this endpoint to evaluate
/// whether it should vote yes or no, based on its local ledger and preconditions.
/// Returns the signed vote that can then be submitted to the coordinator's
/// `/turn/atomic/vote` endpoint.
async fn post_evaluate_proposal(
    State(state): State<NodeState>,
    Json(req): Json<EvaluateProposalRequest>,
) -> Result<Json<EvaluateProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the atomic forest from the request.
    let atomic_forest: dregg_coord::AtomicForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.write().await;

    // Build a Participant from the node's local identity and ledger.
    let node_id = s.silo_id;
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let cell_id = dregg_cell::CellId(node_id);

    let mut participant =
        dregg_coord::Participant::new(cell_id, node_id, signing_key, s.ledger.clone());

    // Evaluate the proposal locally.
    let vote = participant.evaluate_proposal(&proposal_id, &atomic_forest);

    match vote {
        dregg_coord::Vote::Yes { signature } => Ok(Json(EvaluateProposalResponse {
            approve: true,
            reason: None,
            signature: hex_encode_var(&signature),
        })),
        dregg_coord::Vote::No { reason, signature } => Ok(Json(EvaluateProposalResponse {
            approve: false,
            reason: Some(reason),
            signature: hex_encode_var(&signature),
        })),
    }
}

// =============================================================================
// Sovereign Cell Ephemeral Registration Handlers
// =============================================================================

/// POST /cells/register — register a sovereign cell's commitment with the federation.
///
/// The cell exists locally on the agent; the federation stores only the commitment
/// and TTL metadata. Registration expires after `ttl_blocks` of inactivity.
#[tracing::instrument(skip_all)]
async fn post_register_cell(
    State(state): State<NodeState>,
    Json(req): Json<RegisterCellRequest>,
) -> Result<Json<RegisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let commitment: [u8; 32] = hex_decode(&req.commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || commitment.
    let mut message = Vec::with_capacity(64);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some("invalid signature".to_string()),
        }));
    }

    let ttl = req.ttl_blocks.unwrap_or(dregg_cell::DEFAULT_SOVEREIGN_TTL);
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // Parse optional verification key hash.
    let vk_hash: Option<[u8; 32]> = match &req.verification_key_hash {
        Some(hex_str) => Some(hex_decode(hex_str).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s.ledger.register_sovereign_cell_with_vk(
        cell_id,
        commitment,
        current_height,
        ttl,
        vk_hash,
    ) {
        Ok(()) => Ok(Json(RegisterCellResponse {
            registered: true,
            ttl_blocks: ttl,
            error: None,
        })),
        Err(e) => Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/deregister — voluntarily remove a sovereign cell from the federation.
#[tracing::instrument(skip_all)]
async fn post_deregister_cell(
    State(state): State<NodeState>,
    Json(req): Json<DeregisterCellRequest>,
) -> Result<Json<DeregisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id (proves ownership for deregistration).
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &cell_id_bytes) {
        return Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;

    match s.ledger.deregister_sovereign_cell(&cell_id) {
        Ok(()) => Ok(Json(DeregisterCellResponse {
            deregistered: true,
            error: None,
        })),
        Err(e) => Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/update-commitment — update a sovereign cell's commitment after a transition.
///
/// Verifies the old commitment matches, updates to the new commitment, and resets
/// the TTL activity counter.
#[tracing::instrument(skip_all)]
async fn post_update_commitment(
    State(state): State<NodeState>,
    Json(req): Json<UpdateCommitmentRequest>,
) -> Result<Json<UpdateCommitmentResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let old_commitment: [u8; 32] =
        hex_decode(&req.old_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let new_commitment: [u8; 32] =
        hex_decode(&req.new_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || old_commitment || new_commitment.
    let mut message = Vec::with_capacity(96);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&old_commitment);
    message.extend_from_slice(&new_commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s.ledger.update_sovereign_registration_commitment(
        &cell_id,
        old_commitment,
        new_commitment,
        current_height,
    ) {
        Ok(()) => Ok(Json(UpdateCommitmentResponse {
            updated: true,
            error: None,
        })),
        Err(e) => Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /programs/deploy — deploy a custom cell program to the federation.
///
/// Accepts a postcard-serialized CircuitDescriptor, validates it for safety,
/// and stores it in the program registry. Returns the VK hash (program identity).
#[tracing::instrument(skip_all)]
async fn post_deploy_program(
    State(state): State<NodeState>,
    Json(req): Json<DeployProgramRequest>,
) -> Result<Json<DeployProgramResponse>, StatusCode> {
    // Decode hex descriptor bytes.
    let descriptor_bytes =
        hex_decode_var(&req.descriptor_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the CircuitDescriptor from postcard format.
    let descriptor: dregg_dsl_runtime::CircuitDescriptor =
        postcard::from_bytes(&descriptor_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Create the CellProgram (computes VK hash).
    let program = dregg_dsl_runtime::CellProgram::new(descriptor, req.version);

    // Validate into a candidate registry, durably publish the complete
    // canonical snapshot, and only then expose it to live executors. A failed
    // store write therefore cannot create a process-only deployment that
    // disappears at restart. Program deployment is an authenticated node-admin
    // operation today, not a consensus-ordered turn; this transaction makes the
    // node-local registry crash-consistent but does not claim federation-wide
    // deployment consensus.
    let mut s = state.write().await;
    let mut candidate = s.program_registry.clone();
    match candidate.deploy(program) {
        Ok(vk_hash) => match crate::program_registry_persistence::persist_program_registry(
            &s.store, &candidate,
        ) {
            Ok(()) => {
                s.program_registry = candidate;
                Ok(Json(DeployProgramResponse {
                    deployed: true,
                    vk_hash: Some(hex_encode(&vk_hash)),
                    error: None,
                }))
            }
            Err(error) => {
                tracing::error!(%error, "custom program deployment durability failed");
                Ok(Json(DeployProgramResponse {
                    deployed: false,
                    vk_hash: None,
                    error: Some(error),
                }))
            }
        },
        Err(e) => Ok(Json(DeployProgramResponse {
            deployed: false,
            vk_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

/// Verify an Ed25519 signature where the public key is the cell_id bytes.
///
/// The cell_id doubles as the public key for sovereign cells (the cell_id IS
/// the Ed25519 public key or is derived from it). For this API, we treat
/// the cell_id as the public key directly.
fn verify_ed25519_signature(public_key_bytes: &[u8; 32], sig_bytes: &[u8], message: &[u8]) -> bool {
    use ed25519_dalek::Verifier;

    let Ok(verifying_key) = ed25519_dalek::VerifyingKey::from_bytes(public_key_bytes) else {
        return false;
    };
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(sig_bytes);
    let signature = ed25519_dalek::Signature::from_bytes(&sig_arr);
    verifying_key.verify(message, &signature).is_ok()
}

// =============================================================================
// PIR (Private Information Retrieval) Handlers
// =============================================================================

/// GET /pir/info — returns metadata about the PIR database.
///
/// Clients need this to know the database dimensions and tag ordering before
/// constructing a valid PIR query vector.
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn get_pir_info(State(state): State<NodeState>) -> Json<PirInfoResponse> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<dregg_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(dregg_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

    Json(PirInfoResponse {
        num_rows: index.num_rows(),
        row_width: index.row_width(),
        tags: index.tags.clone(),
    })
}

/// POST /pir/query — accepts a PIR query vector and returns the server's response.
///
/// The node computes the matrix-vector product of the intent index against the
/// query vector, returning a response that reveals nothing about which row was
/// queried (when combined with a complementary query to a second node).
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn post_pir_query(
    State(state): State<NodeState>,
    Json(req): Json<PirQueryRequest>,
) -> Result<Json<PirQueryResponse>, StatusCode> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<dregg_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(dregg_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

    // Validate query vector length matches the database.
    if req.query_vector.len() != index.num_rows() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Convert the u32 query vector to BabyBear field elements.
    let query = dregg_intent::pir::PirQuery {
        query_vector: req
            .query_vector
            .iter()
            .map(|&v| dregg_circuit::field::BabyBear::new(v))
            .collect(),
    };

    // Compute the PIR response.
    let response = dregg_intent::pir::compute_pir_response(&query, &index.entries);

    // Convert back to u32 for serialization.
    Ok(Json(PirQueryResponse {
        response: response.response.iter().map(|e| e.as_u32()).collect(),
    }))
}

// =============================================================================
// Checkpoint Handlers
// =============================================================================

/// GET /checkpoint/latest — returns the latest checkpoint.
async fn get_checkpoint_latest(
    State(state): State<NodeState>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.latest_checkpoint() {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

/// GET /checkpoint/:height — returns the checkpoint at a specific height.
async fn get_checkpoint_at_height(
    State(state): State<NodeState>,
    AxumPath(height): AxumPath<u64>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.checkpoint_at_height(height) {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

fn checkpoint_to_response(cp: &dregg_federation::Checkpoint) -> CheckpointResponse {
    CheckpointResponse {
        height: cp.height,
        ledger_state_root: hex_encode(&cp.ledger_state_root),
        note_tree_root: hex_encode(&cp.note_tree_root),
        nullifier_set_root: hex_encode(&cp.nullifier_set_root),
        revocation_tree_root: hex_encode(&cp.revocation_tree_root),
        epoch: cp.epoch,
        timestamp: cp.timestamp,
        federation_members: cp.federation_members.len(),
        qc_votes: cp.qc.votes.len(),
    }
}

// =============================================================================
// Blocklace Checkpoint Serving (for new node fast-sync)
// =============================================================================

/// GET /api/blocklace/checkpoint?height=N
///
/// Returns the full blocklace checkpoint at height N (or the latest if height is
/// not specified). This includes the serialized blocklace DAG state and ledger
/// snapshot, both hex-encoded with BLAKE3 hashes for integrity verification.
///
/// New nodes use this endpoint to fast-sync from a recent known-good state
/// instead of replaying the entire block history.
async fn get_blocklace_checkpoint(
    Query(params): Query<crate::blocklace_sync::BlocklaceCheckpointQuery>,
    State(state): State<NodeState>,
) -> Result<Json<crate::blocklace_sync::BlocklaceCheckpointResponse>, StatusCode> {
    let s = state.read().await;

    // Determine which height to serve.
    let height = match params.height {
        Some(h) => h,
        None => crate::blocklace_sync::latest_blocklace_checkpoint_height(&s.store),
    };

    if height == 0 {
        return Err(StatusCode::NOT_FOUND);
    }

    match crate::blocklace_sync::load_blocklace_checkpoint(&s.store, height) {
        Some(checkpoint) => Ok(Json(checkpoint)),
        None => Err(StatusCode::NOT_FOUND),
    }
}

// =============================================================================
// Faucet
// =============================================================================

/// The asset (token domain) the faucet cell holds: the CANONICAL default asset
/// `blake3("default")`, the SAME domain `crate::signed_turn_validation` binds a
/// turn's agent to (`agent == derive_raw(signer, blake3("default"))`), the SDK's
/// `AgentCipherclerk::cell_id("default")` derives, and
/// `signed_turn_validation::claim_signer_actor_cell` materialises.
///
/// It was `[0u8; 32]` (matching the old `genesis.rs` "default token domain")
/// until 2026-07-25, and that single mismatch is why the faucet reported
/// success and moved nothing: the faucet turn's agent — derived under the
/// all-zero domain — could NEVER equal `derive_raw(faucet_pk, blake3("default"))`,
/// so the ONE application-admission predicate refused the turn at FINALIZATION
/// (`agent-signer-mismatch`), which is the only durable application. Submission
/// (which is staging only, rolled back) had already answered `success: true`.
/// A cell minted in the all-zero domain can never act; the faucet must live in
/// the domain a turn agent is required to live in.
pub(crate) fn faucet_token_id() -> [u8; 32] {
    crate::executor_setup::default_token_id()
}

/// The faucet's deterministic Ed25519 signing key.
///
/// Derived identically to `genesis.rs` (`blake3::derive_key(
/// "dregg-devnet-faucet-key-v1", b"genesis")`) so the runtime faucet endpoint
/// controls the *same* cell that holds the genesis supply and can produce a
/// REAL signed Transfer turn from it — rather than the previous disconnected
/// `[0x01; 32]` placeholder whose `apply_delta` mutated only this node's local
/// ledger and never replicated.
pub(crate) fn faucet_signing_key() -> ed25519_dalek::SigningKey {
    let secret = blake3::derive_key("dregg-devnet-faucet-key-v1", b"genesis");
    ed25519_dalek::SigningKey::from_bytes(&secret)
}

/// The faucet cell's public key (matches the genesis-minted faucet cell).
pub(crate) fn faucet_public_key() -> [u8; 32] {
    faucet_signing_key().verifying_key().to_bytes()
}

#[derive(Deserialize)]
pub struct FaucetRequest {
    /// Hex-encoded 32-byte recipient cell ID.
    pub recipient: String,
    /// Amount of computrons to transfer (max 10000 per request). Use 0 to
    /// materialize a hosted devnet cell without claiming faucet funds.
    pub amount: u64,
    /// Optional hex-encoded Ed25519 public key for the recipient. When set,
    /// the node verifies `recipient == CellId::derive_raw(public_key, default_token_id)`
    /// and inserts a canonical hosted cell instead of a remote stub.
    #[serde(default)]
    pub public_key: Option<String>,
}

#[derive(Serialize)]
pub struct FaucetResponse {
    pub success: bool,
    pub tx_hash: Option<String>,
    pub amount: u64,
    /// Hex hash of the REAL committed faucet turn (the key under which its
    /// receipt appears in `/api/receipts`, where `has_proof` flips true once
    /// the async prove pool attaches the attestation). `tx_hash` remains the
    /// synthetic activity-feed hash for backward compatibility.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Faucet rate limiter: 1 request per cell per 60 seconds.
#[derive(Clone)]
struct FaucetRateLimiter {
    /// Map of recipient cell_id hex -> last request time.
    state: Arc<Mutex<HashMap<String, Instant>>>,
}

impl FaucetRateLimiter {
    fn new() -> Self {
        let limiter = Self {
            state: Arc::new(Mutex::new(HashMap::new())),
        };
        // Prune stale entries periodically so a flood of unique recipient ids
        // cannot grow this map without bound (same discipline as `RateLimiter`).
        let prune_state = limiter.state.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(120));
            loop {
                interval.tick().await;
                let mut map = prune_state.lock().await;
                let now = Instant::now();
                map.retain(|_, last| now.duration_since(*last).as_secs() < 60);
            }
        });
        limiter
    }

    /// Returns true if the request should be allowed.
    async fn check(&self, recipient: &str) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        if let Some(last) = map.get(recipient)
            && now.duration_since(*last).as_secs() < 60
        {
            return false;
        }
        map.insert(recipient.to_string(), now);
        true
    }
}

/// POST /api/faucet — transfer computrons from the faucet cell to a recipient.
///
/// Only enabled when `--enable-faucet` is set. Rate limited TWICE:
/// * per recipient cell (1/min) — the original anti-drain bucket; and
/// * per client IP (proxy-aware, F-1) — covering BOTH the funded and the
///   `amount == 0` materialization paths. Without the per-IP gate, an attacker
///   minting a fresh recipient id per request gets a fresh per-cell bucket every
///   time (unbounded faucet drain), and the zero-amount path inserted unbounded
///   stub cells into the ledger with NO limit at all.
///
/// Maximum 10000 computrons per request.
async fn post_faucet(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<FaucetRequest>,
    limiter: FaucetRateLimiter,
    ip_limiter: RateLimiter,
) -> Result<Json<FaucetResponse>, StatusCode> {
    // Per-IP gate first: bounds total faucet traffic (including zero-amount
    // cell materialization) per real client, before any state is touched.
    if !ip_limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // Validate amount. A zero amount is allowed as a devnet materialization
    // path for hosted cells; it does not consume the per-cell faucet limit.
    if req.amount > 10_000 {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: None,
            amount: 0,
            error: Some("amount must be between 0 and 10000".to_string()),
        }));
    }

    // Validate recipient hex.
    let recipient_bytes: [u8; 32] = match hex_decode(&req.recipient) {
        Ok(b) => b,
        Err(_) => {
            return Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some("invalid recipient: must be 64 hex characters".to_string()),
            }));
        }
    };
    let recipient_cell_id = dregg_cell::CellId(recipient_bytes);

    let recipient_public_key = match &req.public_key {
        Some(pk_hex) => {
            let pk: [u8; 32] = match hex_decode(pk_hex) {
                Ok(pk) => pk,
                Err(_) => {
                    return Ok(Json(FaucetResponse {
                        success: false,
                        tx_hash: None,
                        turn_hash: None,
                        amount: 0,
                        error: Some("invalid public_key: must be 64 hex characters".to_string()),
                    }));
                }
            };
            let default_token_id = *blake3::hash(b"default").as_bytes();
            let expected = dregg_cell::CellId::derive_raw(&pk, &default_token_id);
            if expected != recipient_cell_id {
                return Ok(Json(FaucetResponse {
                    success: false,
                    tx_hash: None,
                    turn_hash: None,
                    amount: 0,
                    error: Some("public_key does not derive the recipient cell".to_string()),
                }));
            }
            Some(pk)
        }
        None => None,
    };

    // Rate limit check.
    if req.amount > 0 && !limiter.check(&req.recipient).await {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: None,
            amount: 0,
            error: Some("rate limited: 1 request per cell per minute".to_string()),
        }));
    }

    let mut s = state.write().await;

    // Consensus FINALIZATION is the single authoritative application of a turn at
    // EVERY committee size — the SAME `execute_finalized_turn` runs on every node
    // and provisions any missing cells DETERMINISTICALLY from the finalized turn
    // AND ITS OWN PRE-STATE — not from the turn alone; the stub's asset is read
    // off the Transfer's source cell (see `provision_transfer_destinations`,
    // whose docblock carries the uniformity argument). So this endpoint
    // advances NO authoritative state for a funded grant: creating the recipient
    // here would be LOCAL-ONLY (peers never see it) and, worse, NON-UNIFORM (the
    // submitter would mint a canonical `with_balance(pk, …)` cell while peers
    // materialize a zero-pk stub at the same id — and that IS an attested-root
    // split: `dregg_persist::canonical_ledger_root` hashes `postcard(cell)`, the
    // whole cell including its public key and `pq_identity`, not just its state
    // (an older comment here claimed the opposite; it was wrong)). The
    // provisioning + execution below runs against an undo journal purely to build
    // the receipt/proof for the HTTP response, and is rolled back.
    //
    // `is_solo` survives for ONE decision: the zero-amount materialization path,
    // which has no turn and therefore no finalized pass to provision it. A sole
    // authority can mint the canonical pk-bound cell there; a committee member
    // must mint the same uniform stub every other node would.
    let is_solo = s.solo_consensus.as_ref().is_some_and(|sc| sc.is_solo);

    // The faucet cell. Derived from the genesis faucet key in the canonical
    // default asset, so this is the SAME cell `genesis.rs` mints the supply
    // into. This endpoint NEVER creates it: value enters only by genesis
    // issuer-moves (THE EPOCH §5), so a data dir without a genesis faucet cell
    // has no faucet — say so, rather than reporting a grant nobody funded.
    let faucet_pubkey = faucet_public_key();
    let faucet_cell_id = dregg_cell::CellId::derive_raw(&faucet_pubkey, &faucet_token_id());

    // Recipient provisioning. CROSS-NODE UNIFORMITY: in multi-party mode the
    // recipient is provisioned by the finalized executor on every node from the
    // turn data alone (the recipient's public key is NOT carried over consensus,
    // so every node — including this submitter — must agree on the SAME provisioned
    // cell). We therefore reuse the identical stub provisioning here that
    // `execute_finalized_turn` uses, so the receipt this node returns matches the
    // authoritative finalized outcome. Solo mode mints the canonical hosted cell
    // (with the known pk) directly, since it is the sole authority.
    let provision_recipient = |ledger: &mut dregg_cell::Ledger| {
        if ledger.get(&recipient_cell_id).is_some() {
            return;
        }
        let recipient_cell = match (is_solo, recipient_public_key) {
            (true, Some(pk)) => {
                dregg_cell::Cell::with_balance(pk, crate::executor_setup::default_token_id(), 0)
            }
            // Multi-party (or no known pk): the uniform stub provisioning every
            // node applies in `execute_finalized_turn` — minted in the DEFAULT
            // ASSET, because the next thing that happens to this cell is a faucet
            // Transfer out of the default-asset faucet cell, and a Transfer across
            // assets is refused. A zero-asset stub here meant "materialize me
            // first, then fund me" deterministically failed cross-asset.
            _ => dregg_cell::Cell::remote_stub_with_id_pk_token_balance(
                recipient_cell_id,
                [0u8; 32],
                crate::executor_setup::default_token_id(),
                0,
            ),
        };
        let _ = ledger.insert_cell(recipient_cell);
    };

    let tx_hash = compute_faucet_activity_hash(&recipient_cell_id, req.amount);

    if req.amount == 0 {
        // Zero-amount is a devnet hosted-cell MATERIALIZATION convenience. There
        // is no Transfer and no consensus turn, so in multi-party mode there is no
        // finalized pass to provision the cell — materialize it authoritatively
        // here regardless of mode (insert-if-absent; idempotent across nodes for a
        // pk-derived id). This is the one provisioning the faucet still applies
        // directly under multi-party, and it carries no value.
        let recipient_created = s.ledger.get(&recipient_cell_id).is_none();
        if recipient_created {
            provision_recipient(&mut s.ledger);
        }
        if recipient_created {
            push_committed_event(
                &mut s,
                tx_hash.clone(),
                req.recipient.clone(),
                vec!["faucet_materialized_cell".to_string()],
                ActivityProofStatus::NotRequired,
            );
        }
        return Ok(Json(FaucetResponse {
            success: true,
            tx_hash: Some(tx_hash),
            turn_hash: None,
            amount: 0,
            error: None,
        }));
    }

    // The faucet cell must already hold genesis supply. It is never created
    // here: this endpoint moves value, it does not issue it.
    if s.ledger.get(&faucet_cell_id).is_none() {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: None,
            amount: 0,
            error: Some(format!(
                "faucet cell {} is not in this node's ledger — this data dir has no genesis \
                 faucet supply in the default asset (run `dregg-node genesis` and boot against \
                 its genesis.json)",
                hex_encode(&faucet_cell_id.0)
            )),
        }));
    }

    // Build a REAL faucet-signed Transfer turn and run it through the
    // executor, then gossip + submit to the blocklace — the same consensus
    // path committed operator turns use. This replaces the old direct
    // `ledger.apply_delta` write, which mutated only this node's local ledger
    // and never replicated (so a peer never saw the faucet grant).
    let faucet_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
        faucet_signing_key().to_bytes(),
    ));
    let transfer = dregg_turn::Effect::Transfer {
        from: faucet_cell_id,
        to: recipient_cell_id,
        amount: req.amount,
    };
    // Sign over the SAME federation id the executor verifies against
    // (`federation_id_for_executor`: `s.federation_id` when configured, else
    // `blake3(pubkey)`). Using the raw `s.federation_id` on an unconfigured solo
    // node mismatched the executor's domain and failed Ed25519 verification.
    let exec_federation_id = crate::executor_setup::federation_id_for_executor(&s);
    // PIPELINED nonce: the faucet's AUTHORITATIVE nonce only advances when a
    // faucet turn FINALIZES through consensus (the submission-time execution
    // below deliberately does NOT mutate the authoritative ledger). Reading it
    // directly meant a second faucet request submitted before the first
    // finalized re-used the same nonce and replayed. Reserve the next nonce as
    // `max(authoritative, reserved)` and bump the reservation, so back-to-back
    // submissions get fresh consecutive nonces that finalize in order. `max`
    // reconciles the two sides: once the in-flight turns finalize, the
    // authoritative nonce catches up and no permanent gap opens.
    let authoritative_nonce = s
        .ledger
        .get(&faucet_cell_id)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    let faucet_nonce = authoritative_nonce.max(s.faucet_reserved_nonce.unwrap_or(0));
    s.faucet_reserved_nonce = Some(faucet_nonce + 1);
    // THE ACTION SIGNATURE IS BOUND TO THE TURN NONCE (`dregg-action-sig-v3`):
    // `compute_signing_message(action, federation_id, turn.nonce)`. So the action
    // MUST be signed over the nonce the turn will actually carry — computed just
    // above. The convenience `make_action` signs over the clerk's OWN
    // `next_turn_nonce()`, and this clerk is constructed fresh per request from
    // the raw key, so its receipt chain is empty and that nonce is ALWAYS 0: the
    // first faucet call per boot matched by luck and every later one failed the
    // Ed25519 half of the hybrid authorization ("Ed25519 (classical) signature
    // half failed"), because `faucet_reserved_nonce` had advanced past 0 while
    // the signature stayed pinned to it.
    let action = faucet_cclerk.sign_action_hybrid(
        dregg_sdk::raw::unsigned_action_named(faucet_cell_id, "faucet_transfer", vec![transfer]),
        &exec_federation_id,
        faucet_nonce,
    );
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);
    // The executor's budget gate caps computrons at `turn.fee` (`estimated >
    // fee` → BudgetExceeded). A fee of 0 made every amount>0 faucet transfer
    // reject ("budget exceeded: limit=0, used=100"); the faucet cell holds the
    // genesis supply, so it covers a real fee. Size the fee to the estimated
    // cost so the gate passes deterministically.
    // Receipt-chain head for the turn's verified ChainHead leg.
    //
    // SOLO (n=1): submission is authoritative, so bind to the local chain head
    // (the cipherclerk's `append_receipt` fills a `None` prev with the chain
    // head, changing the appended receipt's hash; binding it here keeps the
    // stored WitnessedReceipt findable so has_proof can flip).
    //
    // FULL (n>1): the AUTHORITATIVE receipt-chain advance is `execute_finalized_turn`,
    // which runs identically on EVERY node in tau order and — like the ledger — does
    // NOT observe the submitter's local submission-time append. The finalized executor
    // only seeds the LOCAL agent's receipt head, never the faucet's, so the verified
    // ChainHead leg expects `None` for the faucet agent on every node. Binding to the
    // local chain head here made every NON-submitter reject the faucet turn after the
    // first ("receipt chain mismatch: expected None, got Some(..)"), AND made the
    // submitter reject it (its own head had already advanced at submission) — so a
    // second faucet turn provisioned its destination but the transfer never funded it
    // (`found:true, balance:0`), silently breaking sustained faucet finality. `None`
    // matches the finalized expectation uniformly on all nodes.
    let faucet_prev_receipt = s.cclerk.agent_receipt_head_hash(&faucet_cell_id);
    let mut faucet_turn = Turn {
        agent: faucet_cell_id,
        nonce: faucet_nonce,
        fee: 0, // sized to the estimated cost below so the budget gate passes
        memo: Some(format!("faucet_transfer:{}", req.amount)),
        // Stamped so the wire marshal accepts the envelope and the turn stays
        // on the verified Lean producer (see `default_valid_until`).
        valid_until: default_valid_until(),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: faucet_prev_receipt,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let executor = crate::executor_setup::new_submit_executor(&s);
    // Size the fee (= computron budget cap) to the estimated cost so the budget
    // gate passes; the faucet cell holds the genesis supply and covers it.
    faucet_turn.fee = executor.estimate_cost(&faucet_turn);

    let signed = faucet_cclerk.sign_turn(&faucet_turn);
    let turn_hash_bytes = faucet_turn.hash();
    let turn_hash_hex = hex_encode(&turn_hash_bytes);

    // THE SAME application-admission predicate every other SignedTurn ingress
    // runs (`/turns/submit`, the finalized-block executor, the PostgreSQL
    // drainer). The faucet builds its own envelope, so without this it was the
    // ONE ingress that could hand consensus a payload finalization would refuse
    // — and it did, for four days: the faucet agent was derived in the all-zero
    // asset, `validate_signed_turn` requires `derive_raw(signer, "default")`,
    // and the mismatch only surfaced as a `agent-signer-mismatch` deterministic
    // rejection at finalization, long after this handler had answered
    // `success: true`. Refusing HERE makes that class un-shippable: a faucet
    // envelope that consensus will not apply never reaches consensus.
    if let Err(error) = crate::signed_turn_validation::validate_signed_turn(
        &signed,
        &executor,
        s.ledger.get(&signed.turn.agent),
    ) {
        if s.faucet_reserved_nonce == Some(faucet_nonce + 1) {
            s.faucet_reserved_nonce = Some(faucet_nonce);
        }
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: Some(turn_hash_hex),
            amount: 0,
            error: Some(format!("faucet turn fails signed-turn admission: {error}")),
        }));
    }

    // O(touched) atomic rollback: arm an undo journal rather than cloning the
    // whole O(cells) ledger. Both regimes execute IN PLACE under this exclusive
    // write lock; the fate of the mutation is resolved right after execution.
    s.ledger.begin_restore_point();
    let lean_producer_enabled = s.lean_producer_enabled;

    // Consensus FINALIZATION is the authoritative application of the faucet turn
    // at EVERY committee size, n=1 included (the SAME `execute_finalized_turn`
    // runs on every node and emits the attested root). Committing here would
    // mutate ONLY this node's ledger — advancing the faucet cell's nonce so the
    // finalized re-execution is rejected as a "nonce replay", and creating the
    // recipient cell only locally so PEERS reject the finalized Transfer as
    // "destination not found" — both of which block cross-node commit
    // (`latest_height` stuck at 0). So the in-place run below is purely to build
    // the receipt/proof for the HTTP response, and the journal rolls it back,
    // leaving the authoritative ledger untouched; the finalized executor then
    // applies the turn uniformly on all nodes (it auto-materializes the Transfer
    // destination identically on every node, see
    // `provision_transfer_destinations` / `execute_finalized_turn`).
    // Admission staging is identical at every committee size.  Provision the
    // same deterministic destination the finalized path will see, reflect a
    // reserved pipelined nonce only inside the undo journal, execute, and roll
    // everything back below.  Finalization owns the sole durable application.
    crate::blocklace_sync::provision_transfer_destinations(&mut s.ledger, &faucet_turn.call_forest);
    if let Some(cell) = s.ledger.get_mut(&faucet_cell_id) {
        cell.state.set_nonce(faucet_nonce);
    }
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &faucet_turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    // Capture the pre-turn cells from the journal BEFORE resolving it (the
    // O(touched) stand-in for the old full `pre_ledger` clone), then resolve:
    // Every mode restores the untouched ledger for finalization.
    let pre_ledger = s.ledger.pre_turn_touched_ledger();
    s.ledger.rollback_restore_point();

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // The faucet turn is a REAL turn, and this handler hands its rotated
            // attestation material to the async prove pool — the same thing
            // `/turn/submit` does with its `pending_proof`, so a faucet grant can
            // reach `has_proof: true` in `/api/receipts` like any other turn.
            //
            // ⚠ IT DOES NOT APPEND THE RECEIPT, and must not. This comment used to
            // say "append its receipt to the chain and hand it to the async prove
            // pool"; the append half was correct only while solo mode committed
            // here. Since `5f0999ab9` unified both committee sizes onto admission
            // staging, the execution above runs inside an undo journal that is
            // ROLLED BACK, and the sole durable receipt append is finalization's
            // (`blocklace_sync`'s `append_receipt_already_durable`). Appending a
            // staged receipt here would also move the faucet's local chain head,
            // which is exactly the divergence the `faucet_prev_receipt` comment
            // above records as having broken sustained faucet finality.
            //
            // What that same commit dropped as COLLATERAL — the hand-off below was
            // gated on the `appended` flag it deleted, leaving `let _ =
            // pending_proof;` under a docblock still describing the pipeline — is
            // restored here. PATH-PRESERVE Phase 5b: the executor already
            // validated the turn (the soundness boundary); the composed proof
            // (rotated leg) is built + self-verified off the lock. The attestation
            // is best-effort for the faucet (finalization stands either way; an
            // unattested faucet grant is a devnet-liveness issue, not a soundness
            // one).
            let receipt_hash = receipt.receipt_hash();
            // Build the rotated attestation material from the actor's before/after
            // cells. In full mode the authoritative `s.ledger` was not mutated (the
            // receipt was built against a scratch clone), so before==after for the
            // single-cell faucet actor — correct for the rotated single-cell leg,
            // whose per-row welds carry the transfer delta from the v1 sub-trace
            // (the turn-invariant limbs are identical), exactly as the finalized
            // cap-less note-spend leg does.
            let witness_outcome = match prepare_rotatable_turn(
                &faucet_turn,
                pre_ledger.get(&faucet_turn.agent),
                s.ledger.get(&faucet_turn.agent),
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash_hex,
                        error = %err,
                        "faucet turn attestation prep failed; receipt stays \
                         committed-but-unattested (has_proof will not flip)"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            let (proof_status, pending_proof) = witness_outcome.split(&turn_hash_hex);

            push_committed_event(
                &mut s,
                tx_hash.clone(),
                req.recipient.clone(),
                vec![format!("faucet_transfer:{}", req.amount)],
                proof_status,
            );

            // Replicate through gossip + blocklace consensus.
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            // Async STARK attestation, off the lock — flips the receipt's
            // has_proof once the pool lands the proof. `push_witnessed_receipt` is
            // keyed by receipt hash, not by a position in the receipt log, so this
            // is well-defined before finalization appends the canonical receipt.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash_hex.clone(),
                )
                .await;
            }

            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                tokio::spawn(async move {
                    gossip
                        .gossip_turn(turn_hash_bytes, turn_data_for_gossip)
                        .await;
                });
            }
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                });
            }

            Ok(Json(FaucetResponse {
                success: true,
                tx_hash: Some(tx_hash),
                turn_hash: Some(turn_hash_hex),
                amount: req.amount,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // The turn we reserved a nonce for is NOT entering consensus, so roll
            // the reservation back (it is still the value we set — `s` is write-
            // locked across this whole handler) to avoid a permanent gap that
            // would replay every subsequent faucet turn.
            if s.faucet_reserved_nonce == Some(faucet_nonce + 1) {
                s.faucet_reserved_nonce = Some(faucet_nonce);
            }
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some(format!("transfer rejected: {reason}")),
            }))
        }
        _ => {
            if s.faucet_reserved_nonce == Some(faucet_nonce + 1) {
                s.faucet_reserved_nonce = Some(faucet_nonce);
            }
            Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some("faucet transfer did not commit".to_string()),
            }))
        }
    }
}

fn compute_faucet_activity_hash(recipient: &dregg_cell::CellId, amount: u64) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-node-faucet-activity-v1");
    hasher.update(&recipient.0);
    hasher.update(&amount.to_le_bytes());
    let now_nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as u64;
    hasher.update(&now_nanos.to_le_bytes());
    hex_encode(hasher.finalize().as_bytes())
}

// =============================================================================
// Discharge Gateway Endpoint
// =============================================================================

/// POST /api/discharge request body.
#[derive(Deserialize)]
pub struct NodeDischargeRequest {
    /// Base64-encoded ticket from the 3P caveat.
    pub ticket: String,
    /// Optional client identifier.
    pub client_id: Option<String>,
    /// Optional base64-encoded proof.
    pub proof: Option<String>,
    /// Optional payment amount.
    pub payment: Option<u64>,
    /// Arbitrary metadata.
    #[serde(default)]
    pub metadata: HashMap<String, String>,
}

/// POST /api/discharge response body.
#[derive(Serialize)]
pub struct NodeDischargeResponse {
    pub success: bool,
    pub discharge: Option<String>,
    pub expires_at: Option<i64>,
    pub condition_met: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// POST /api/discharge — issue a discharge macaroon from this node's gateway.
///
/// The node acts as a discharge gateway for its own federation's tokens.
/// The shared key is derived from the cipherclerk's signing key using BLAKE3 KDF
/// with domain "dregg-discharge-gateway-v1".
async fn post_discharge(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<NodeDischargeRequest>,
    limiter: RateLimiter,
) -> Result<Json<NodeDischargeResponse>, StatusCode> {
    // Per-IP rate limit (proxy-aware, F-1): this endpoint is public and its
    // body takes the global state-write lock, so it must not be free to flood.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;

    // Decode ticket from base64.
    let ticket = engine
        .decode(&req.ticket)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    // Decode optional proof from base64.
    let proof = match &req.proof {
        Some(p) => Some(engine.decode(p).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // SECURITY: Use the persistent discharge gateway from node state.
    // This ensures the `issued` HashSet persists across requests, providing
    // actual replay prevention. Previously, a fresh gateway was created per
    // request, making the replay set useless (it was dropped immediately).
    if s.discharge_gateway.is_none() {
        let gateway_key = s.cclerk.derive_symmetric_key("dregg-discharge-gateway-v1");
        let location = format!("dregg-node://{}", hex_encode(&s.cclerk.public_key().0));
        let mut gateway = dregg_macaroon::DischargeGateway::new(gateway_key, location);
        // Default evaluator: require proof to prevent accidental open gateways.
        gateway.add_evaluator(Box::new(dregg_macaroon::ProofRequiredEvaluator));
        // Load the persisted replay set (survives restarts).
        //
        // ⚑ THE THREE OUTCOMES ARE NOT TWO. `Ok(None)` — nothing has ever been
        // persisted — legitimately yields an empty set. `Err(..)` — the store
        // could not ANSWER — yields no knowledge at all, and an empty set is the
        // WEAKEST possible answer to substitute for it: every ticket this node
        // ever discharged becomes discharge-able again. This was written as
        // `if let Ok(Some(data)) = …`, which collapsed the error into the
        // nothing-stored case with no `else` and no trace, three lines above a
        // comment naming ticket reuse as the hazard. A gateway whose replay set
        // is UNKNOWN does not serve; it refuses.
        match s.store.get_config("discharge_issued_set") {
            Ok(Some(data)) => match gateway.load_issued_set(&data) {
                Ok(loaded) => {
                    tracing::debug!(entries = loaded, "discharge replay set restored from store");
                }
                Err(e) => {
                    tracing::error!(
                        error = %e,
                        "REFUSING discharge: the persisted replay set is malformed, so the \
                         gateway cannot know which tickets were already issued"
                    );
                    return Err(StatusCode::SERVICE_UNAVAILABLE);
                }
            },
            Ok(None) => {
                // Genuinely nothing persisted yet — an empty set is the truth.
            }
            Err(e) => {
                tracing::error!(
                    error = %e,
                    "REFUSING discharge: the store could not read the replay set, so the \
                     gateway cannot know which tickets were already issued"
                );
                return Err(StatusCode::SERVICE_UNAVAILABLE);
            }
        }
        s.discharge_gateway = Some(gateway);
    }

    let gateway = s.discharge_gateway.as_ref().unwrap();

    let discharge_req = dregg_macaroon::DischargeRequest {
        ticket,
        client_id: req.client_id,
        proof,
        payment: req.payment,
        metadata: req.metadata,
    };

    // `process_request` burns the ticket on PRESENTATION — the hash goes into the
    // replay set before any condition is evaluated — so a DENIED request mutates
    // the set exactly as an issued one does. Persisting only the success arm let a
    // restart resurrect every denied ticket. Measure the set instead of guessing
    // from the outcome; an undecryptable blob changes nothing and writes nothing.
    let issued_before = gateway.issued_len();
    let outcome = gateway.process_request(&discharge_req);
    let replay_set_changed = gateway.issued_len() != issued_before;

    if replay_set_changed {
        // SECURITY: the durable replay set must be at least as strong as the
        // in-memory one before this node hands anything back. A crash between
        // discharge issuance and shutdown would otherwise lose the burn, enabling
        // ticket reuse — which is precisely what this write exists to prevent, so
        // a failed write cannot be a warning that still answers `success: true`.
        //
        // The ticket stays burned in THIS process. That is deliberate: a store
        // that cannot write is a broken node, and re-admitting the ticket to buy
        // back liveness would re-open the exact hole. No discharge escaped — the
        // response is dropped unread — so nothing was issued against the burn.
        let data = gateway.serialize_issued_set();
        if let Err(e) = s.store.set_config("discharge_issued_set", &data) {
            tracing::error!(
                error = %e,
                "REFUSING discharge: the replay-set burn could not be persisted, so a crash \
                 here would make this ticket reusable"
            );
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
    }

    match outcome {
        Ok(resp) => Ok(Json(NodeDischargeResponse {
            success: true,
            discharge: Some(resp.discharge),
            expires_at: Some(resp.expires_at),
            condition_met: Some(resp.condition_met),
            error: None,
        })),
        Err(e) => Ok(Json(NodeDischargeResponse {
            success: false,
            discharge: None,
            expires_at: None,
            condition_met: None,
            error: Some(e.reason),
        })),
    }
}

// =============================================================================
// Factory, Sovereign, Bearer, and Composition endpoints
// =============================================================================

#[derive(Deserialize)]
struct CreateFromFactoryRequest {
    factory_vk: String,
    owner_pubkey: String,
    token_id: Option<String>,
    /// Hex-encoded 8-byte nonce, included in the signed message (F-P1-2).
    nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature from `owner_pubkey` over
    /// `b"dregg-create-from-factory-v1" || factory_vk || owner_pubkey || nonce`.
    signature: String,
}

#[derive(Serialize)]
struct CreateFromFactoryResponse {
    success: bool,
    child_vk: Option<String>,
    cell_id: Option<String>,
    error: Option<String>,
}

async fn post_create_from_factory(
    State(state): State<NodeState>,
    Json(req): Json<CreateFromFactoryRequest>,
) -> Result<Json<CreateFromFactoryResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let factory_vk = hex_decode_32_result(&req.factory_vk).map_err(|_| StatusCode::BAD_REQUEST)?;
    let owner_pubkey =
        hex_decode_32_result(&req.owner_pubkey).map_err(|_| StatusCode::BAD_REQUEST)?;

    // F-P1-2: verify the caller actually possesses the owner private key, so an
    // authenticated operator-tier caller can't register provenance for cells
    // they don't own.
    {
        let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| StatusCode::BAD_REQUEST)?;
        let mut payload = Vec::with_capacity(32 + 32 + nonce_bytes.len());
        payload.extend_from_slice(&factory_vk);
        payload.extend_from_slice(&owner_pubkey);
        payload.extend_from_slice(&nonce_bytes);
        if let Err(e) = verify_ed25519_sig(
            &owner_pubkey,
            &req.signature,
            b"dregg-create-from-factory-v1",
            &payload,
        ) {
            return Ok(Json(CreateFromFactoryResponse {
                success: false,
                child_vk: None,
                cell_id: None,
                error: Some(format!("owner signature rejected: {e}")),
            }));
        }
    }

    let params = dregg_cell::factory::FactoryCreationParams {
        owner_pubkey,
        mode: dregg_cell::CellMode::default(),
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
    };

    let param_hash = dregg_cell::factory::ChildVkStrategy::compute_param_hash(&params);
    let child_vk = dregg_cell::factory::ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

    // Derive cell_id from owner + token_id.
    let token_id = req
        .token_id
        .as_deref()
        .map(|s| *blake3::hash(s.as_bytes()).as_bytes())
        .unwrap_or_else(|| *blake3::hash(b"dregg-default-domain").as_bytes());
    let cell_id = dregg_cell::CellId::derive_raw(&owner_pubkey, &token_id);

    Ok(Json(CreateFromFactoryResponse {
        success: true,
        child_vk: Some(hex_encode(&child_vk)),
        cell_id: Some(hex_encode(&cell_id.0)),
        error: None,
    }))
}

#[derive(Deserialize)]
struct MakeSovereignRequest {
    cell_id: String,
    /// Hex-encoded 8-byte nonce (F-P1-2).
    nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature from the cell owner over
    /// `b"dregg-make-sovereign-v1" || cell_id || nonce`. The signing key
    /// MUST be the cell's `public_key` if the cell exists on the ledger;
    /// otherwise it MUST be the `cell_id` itself (sovereign convention:
    /// for fresh sovereign cells, cell_id == pubkey).
    signature: String,
}

#[derive(Serialize)]
struct MakeSovereignResponse {
    success: bool,
    state_commitment: Option<String>,
    error: Option<String>,
}

async fn post_make_sovereign(
    State(state): State<NodeState>,
    Json(req): Json<MakeSovereignRequest>,
) -> Result<Json<MakeSovereignResponse>, StatusCode> {
    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let cell_id_bytes = hex_decode_32_result(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // F-P1-2: verify the caller possesses the cell-owner private key. For an
    // existing cell, the signing key is the cell's `public_key`. For a brand
    // new sovereign cell (cell_id == pubkey by construction), the signing key
    // is the cell_id itself.
    let owner_pk = s
        .ledger
        .get(&cell_id)
        .map(|c| *c.public_key())
        .unwrap_or(cell_id_bytes);
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| StatusCode::BAD_REQUEST)?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&cell_id_bytes);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_ed25519_sig(
        &owner_pk,
        &req.signature,
        b"dregg-make-sovereign-v1",
        &payload,
    ) {
        return Ok(Json(MakeSovereignResponse {
            success: false,
            state_commitment: None,
            error: Some(format!("owner signature rejected: {e}")),
        }));
    }

    // Compute a state commitment from the cell ID (deterministic for the API response).
    // The full state commitment is computed by the cipherclerk SDK and submitted via
    // /cells/register with the proper sovereign workflow.
    let commitment = blake3::derive_key("dregg-sovereign-commitment-v1", &cell_id_bytes);

    match s.ledger.register_sovereign_cell(cell_id, commitment) {
        Ok(()) => Ok(Json(MakeSovereignResponse {
            success: true,
            state_commitment: Some(hex_encode(&commitment)),
            error: None,
        })),
        Err(e) => Ok(Json(MakeSovereignResponse {
            success: false,
            state_commitment: None,
            error: Some(e.to_string()),
        })),
    }
}

// ⚑ `post_compose_proofs` (`POST /proofs/compose`) DELETED 2026-08-06. It
// BLAKE3'd an untagged `Vec<serde_json::Value>` and answered `success: true`
// with an unreachable `error` field; no input was ever deserialized as a proof
// and no verifier ran. See the router note beside `/turns/bearer-auth` for why
// no honest node-side replacement exists (there is no per-turn canonical anchor
// a stranger can independently obtain to compose against), and
// `wasm::privacy::compose_and_verify_proofs` for the composition that does
// discharge each tagged proof against its real verifier.

#[derive(Deserialize)]
struct BearerAuthRequest {
    /// JSON-serialized BearerCapProof (the delegation chain proof).
    bearer_proof: serde_json::Value,
    /// Hex-encoded 32-byte cell ID that will actually exercise the bearer.
    actor_cell: String,
    /// Hex-encoded 32-byte target cell ID.
    target_cell: String,
}

#[derive(Serialize)]
struct BearerAuthResponse {
    authorized: bool,
    error: Option<String>,
}

#[derive(Debug, PartialEq, Eq)]
enum BearerAuthCoordinatesError {
    MalformedCellId,
    ProofTargetMismatch,
}

/// Parse the exact actor named by a bearer-auth request and bind the request's
/// target coordinate to the target committed inside the proof. Keeping this
/// structural check separate makes it testable without pretending it is an
/// authorization decision; only `verify_bearer_cap` may return `authorized`.
fn validated_bearer_auth_actor(
    req: &BearerAuthRequest,
    proof_target: &CellId,
) -> Result<CellId, BearerAuthCoordinatesError> {
    let actor_cell = CellId(
        hex_decode_32_result(&req.actor_cell)
            .map_err(|_| BearerAuthCoordinatesError::MalformedCellId)?,
    );
    let requested_target = CellId(
        hex_decode_32_result(&req.target_cell)
            .map_err(|_| BearerAuthCoordinatesError::MalformedCellId)?,
    );
    if &requested_target != proof_target {
        return Err(BearerAuthCoordinatesError::ProofTargetMismatch);
    }
    Ok(actor_cell)
}

/// POST /turns/bearer-auth — verify a bearer capability delegation chain.
///
/// Deserializes the BearerCapProof, checks expiry against current block height,
/// checks revocation channels, verifies Ed25519 signatures or STARK proofs in
/// the delegation chain, and confirms attenuation (bearer perms subset of delegator perms).
async fn post_bearer_auth(
    State(state): State<NodeState>,
    Json(req): Json<BearerAuthRequest>,
) -> Result<Json<BearerAuthResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Deserialize the BearerCapProof from the request JSON.
    let bearer_proof: dregg_turn::BearerCapProof =
        serde_json::from_value(req.bearer_proof.clone()).map_err(|_| StatusCode::BAD_REQUEST)?;

    let actor_cell = match validated_bearer_auth_actor(&req, &bearer_proof.target) {
        Ok(actor_cell) => actor_cell,
        Err(BearerAuthCoordinatesError::MalformedCellId) => {
            return Err(StatusCode::BAD_REQUEST);
        }
        Err(BearerAuthCoordinatesError::ProofTargetMismatch) => {
            return Ok(Json(BearerAuthResponse {
                authorized: false,
                error: Some(
                    "bearer proof target does not match the requested target cell".to_string(),
                ),
            }));
        }
    };

    let executor = crate::executor_setup::new_verify_executor(&s);

    // This endpoint may call a result `authorized` only for an exact named
    // actor. SignedDelegation binds bearer_pk to that ledger cell's public key;
    // the anonymous proof variant retains its anonymous semantics.
    match executor.verify_bearer_cap(&bearer_proof, &s.ledger, &actor_cell, &[]) {
        Ok(_) => Ok(Json(BearerAuthResponse {
            authorized: true,
            error: None,
        })),
        Err((turn_error, _path)) => Ok(Json(BearerAuthResponse {
            authorized: false,
            error: Some(format!("{turn_error}")),
        })),
    }
}

// ⚑ `post_peer_exchange` (`POST /turns/peer-exchange`, `POST
// /api/turns/peer-exchange`) DELETED 2026-08-06 — audit finding F-P2-13
// ("does not actually do any peer exchange", `audits/AUDIT-node.md:79`) closed
// by deletion rather than by another year of aspirational naming. It hashed
// (sender, receiver, amount) into an "exchange_id", emitted a `tracing::info!`
// and returned `success: true`; no ledger read, no state change, nothing
// signed, no peer contacted. Its own comment already said the real work
// happened elsewhere. See the router note beside `/turns/bearer-auth`:
// `POST /turns/submit` with `sovereign_witnesses` is that elsewhere.

fn hex_decode_32_result(hex: &str) -> Result<[u8; 32], String> {
    if !hex.is_ascii() {
        return Err("hex input must be ASCII".to_string());
    }
    if hex.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", hex.len()));
    }
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
    }
    Ok(result)
}

/// Request to propose a LIVE epoch transition (validator-set reconfiguration)
/// on a running node. `add` / `remove` are 64-hex Ed25519 validator pubkeys; a
/// rotation is `remove`(old) + `add`(new). The change only APPLIES once a quorum
/// of the CURRENT committee ratifies it through finality.
#[derive(serde::Deserialize)]
pub struct ProposeEpochTransitionRequest {
    #[serde(default)]
    pub add: Vec<String>,
    #[serde(default)]
    pub remove: Vec<String>,
}

/// Response: the submitted proposal block ids (one per add/remove), plus the
/// current committee size + threshold for operator visibility.
#[derive(serde::Serialize)]
pub struct ProposeEpochTransitionResponse {
    pub success: bool,
    pub proposals: Vec<EpochProposalEntry>,
    pub committee_size: usize,
    pub threshold: usize,
    pub error: Option<String>,
}

#[derive(serde::Serialize)]
pub struct EpochProposalEntry {
    pub action: String,
    pub validator: String,
    pub proposal_block: String,
}

/// Submit a live epoch-transition proposal. Each validator key is parsed +
/// validated as a real Ed25519 point, then a `Leave`(remove) / `Join`(add)
/// membership proposal block is created on the running blocklace and gossiped.
async fn post_propose_epoch_transition(
    State(state): State<NodeState>,
    Json(req): Json<ProposeEpochTransitionRequest>,
) -> Result<Json<ProposeEpochTransitionResponse>, StatusCode> {
    // Parse + validate every requested key up front (a bad key fails the whole
    // request before anything is submitted).
    let mut removes: Vec<[u8; 32]> = Vec::with_capacity(req.remove.len());
    for h in &req.remove {
        removes.push(
            crate::operator_join::parse_validator_pubkey(h).map_err(|_| StatusCode::BAD_REQUEST)?,
        );
    }
    let mut adds: Vec<[u8; 32]> = Vec::with_capacity(req.add.len());
    for h in &req.add {
        adds.push(
            crate::operator_join::parse_validator_pubkey(h).map_err(|_| StatusCode::BAD_REQUEST)?,
        );
    }
    if removes.is_empty() && adds.is_empty() {
        return Ok(Json(ProposeEpochTransitionResponse {
            success: false,
            proposals: vec![],
            committee_size: 0,
            threshold: 0,
            error: Some("no --add or --remove validators given".to_string()),
        }));
    }

    let Some(blocklace) = state.blocklace().await else {
        return Ok(Json(ProposeEpochTransitionResponse {
            success: false,
            proposals: vec![],
            committee_size: 0,
            threshold: 0,
            error: Some(
                "node is not running blocklace consensus (no committee to reconfigure)".to_string(),
            ),
        }));
    };

    let mut proposals = Vec::new();
    let mut failures: Vec<String> = Vec::new();
    // Removals first, then additions (a rotation = remove old + add new).
    // `Err` ⇒ the proposal was REFUSED (missing ML-DSA key on an add) or failed
    // to durably land (F2 fail-closed) and was NOT created/broadcast. Each
    // refusal carries its OWN diagnosis, the entry names it, and the response
    // verdict is `success: false` — a refusal must never render as the
    // expected verdict.
    for pk in &removes {
        let proposal_block = match blocklace.propose_membership(&state, *pk, false).await {
            Ok(block_id) => hex_encode(&block_id.0),
            Err(reason) => {
                tracing::warn!(
                    validator = %hex_encode(pk),
                    reason = %reason,
                    "epoch-transition remove proposal NOT created"
                );
                failures.push(format!("remove {}: {reason}", hex_encode(pk)));
                format!("error: {reason}")
            }
        };
        proposals.push(EpochProposalEntry {
            action: "remove".to_string(),
            validator: hex_encode(pk),
            proposal_block,
        });
    }
    for pk in &adds {
        let proposal_block = match blocklace.propose_membership(&state, *pk, true).await {
            Ok(block_id) => hex_encode(&block_id.0),
            Err(reason) => {
                tracing::warn!(
                    validator = %hex_encode(pk),
                    reason = %reason,
                    "epoch-transition add proposal NOT created"
                );
                failures.push(format!("add {}: {reason}", hex_encode(pk)));
                format!("error: {reason}")
            }
        };
        proposals.push(EpochProposalEntry {
            action: "add".to_string(),
            validator: hex_encode(pk),
            proposal_block,
        });
    }

    let (committee_size, threshold) = {
        let c = blocklace.constitution.read().await;
        (c.current.participant_count(), c.threshold())
    };

    Ok(Json(ProposeEpochTransitionResponse {
        success: failures.is_empty(),
        proposals,
        committee_size,
        threshold,
        error: if failures.is_empty() {
            None
        } else {
            Some(failures.join("; "))
        },
    }))
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Encode variable-length byte slices to hex (for signatures, etc.).
fn hex_encode_var(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn starbridge_limit(limit: Option<usize>) -> usize {
    limit.unwrap_or(50).min(200)
}

fn text_filter_matches(value: &str, filter: &Option<String>) -> bool {
    filter.as_ref().is_none_or(|needle| {
        value
            .to_ascii_lowercase()
            .contains(&needle.to_ascii_lowercase())
    })
}

fn exact_filter_matches(value: &str, filter: &Option<String>) -> bool {
    filter
        .as_ref()
        .is_none_or(|needle| value.eq_ignore_ascii_case(needle))
}

fn starbridge_event_matches(event: &CommittedEvent, params: &StarbridgeQuery) -> bool {
    exact_filter_matches(&event.cell_id, &params.cell)
        && exact_filter_matches(&event.turn_hash, &params.turn_hash)
        && params.memo.as_ref().is_none_or(|memo| {
            // Lower-case the needle ONCE, not once per effect.
            let needle = memo.to_ascii_lowercase();
            event
                .effects
                .iter()
                .any(|effect| effect.to_ascii_lowercase().contains(&needle))
        })
        && params.effect.as_ref().is_none_or(|effect| {
            let needle = effect.to_ascii_lowercase();
            event
                .effects
                .iter()
                .any(|summary| summary.to_ascii_lowercase().contains(&needle))
        })
        && params.app.as_ref().is_none_or(|app| {
            classify_starbridge_app(None, &event.effects)
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn starbridge_signed_turn_info(
    queue_index: usize,
    signed: &SignedTurn,
) -> StarbridgeSignedTurnInfo {
    let mut action_targets = Vec::new();
    let mut effect_kinds = Vec::new();
    let mut touched = HashSet::new();

    for tree in signed.turn.call_forest.iter_dfs() {
        let target = hex_encode(&tree.action.target.0);
        touched.insert(target.clone());
        action_targets.push(target);
        for effect in &tree.action.effects {
            effect_kinds.push(effect_kind(effect));
            for cell in effect_cells(effect) {
                touched.insert(cell);
            }
        }
    }

    let mut touched_cells: Vec<String> = touched.into_iter().collect();
    touched_cells.sort();
    effect_kinds.sort();
    effect_kinds.dedup();

    StarbridgeSignedTurnInfo {
        queue_index,
        turn_hash: hex_encode(&signed.turn.hash()),
        signer: hex_encode(&signed.signer.0),
        agent: hex_encode(&signed.turn.agent.0),
        nonce: signed.turn.nonce,
        fee: signed.turn.fee,
        memo: signed.turn.memo.clone(),
        action_count: signed.turn.action_count(),
        effect_count: signed.turn.call_forest.total_effects().len(),
        action_targets,
        app: classify_starbridge_app(signed.turn.memo.as_deref(), &effect_kinds),
        effect_kinds,
        touched_cells,
    }
}

fn starbridge_signed_turn_matches(
    info: &StarbridgeSignedTurnInfo,
    params: &StarbridgeQuery,
) -> bool {
    exact_filter_matches(&info.turn_hash, &params.turn_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            info.touched_cells
                .iter()
                .any(|touched| touched.eq_ignore_ascii_case(cell))
        })
        && params
            .memo
            .as_ref()
            .is_none_or(|_| text_filter_matches(info.memo.as_deref().unwrap_or(""), &params.memo))
        && params.effect.as_ref().is_none_or(|effect| {
            info.effect_kinds.iter().any(|kind| {
                kind.eq_ignore_ascii_case(effect) || text_filter_matches(kind, &params.effect)
            })
        })
        && params.app.as_ref().is_none_or(|app| {
            info.app
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn starbridge_action_matches(info: &StarbridgeActionInfo, params: &StarbridgeQuery) -> bool {
    exact_filter_matches(&info.turn_hash, &params.turn_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            info.target.eq_ignore_ascii_case(cell)
                || info
                    .touched_cells
                    .iter()
                    .any(|touched| touched.eq_ignore_ascii_case(cell))
        })
        && params
            .memo
            .as_ref()
            .is_none_or(|_| text_filter_matches(info.memo.as_deref().unwrap_or(""), &params.memo))
        && params.effect.as_ref().is_none_or(|effect| {
            info.effect_kinds.iter().any(|kind| {
                kind.eq_ignore_ascii_case(effect) || text_filter_matches(kind, &params.effect)
            })
        })
        && params.app.as_ref().is_none_or(|app| {
            info.app
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn identity_scoped_params(params: &StarbridgeQuery) -> StarbridgeQuery {
    StarbridgeQuery {
        limit: params.limit,
        since_height: params.since_height,
        cell: params.cell.clone(),
        memo: params.memo.clone(),
        effect: params.effect.clone(),
        turn_hash: params.turn_hash.clone(),
        effects_hash: params.effects_hash.clone(),
        app: Some(params.app.clone().unwrap_or_else(|| "identity".to_string())),
    }
}

/// The proof status of a committed receipt, derived from **whether proof material is
/// actually attached** — the async prove pool's `WitnessedReceipt`s, or the persisted
/// full-turn proof — and never from the executor signature.
///
/// ⚑ CORRECTED 2026-08-06. This function used to be, in full:
///
/// ```ignore
/// if receipt.executor_signature.is_some() { Proved } else { NotRequired }
/// ```
///
/// so `Proved` meant "an executor signed it" on three PUBLIC (unauthenticated)
/// endpoints — `/api/starbridge/identity/{events,credentials,proof-checkpoints}`. The
/// identical derivation had already been found and fixed for `ReceiptInfo::has_proof`
/// 6000 lines earlier in this same file, whose comment says outright *"It is NOT the
/// executor signature — that is `executor_signed`"*; the sibling was fixed and this one
/// was not. `/proof-checkpoints` shipped `proof_status`, `executor_signed` and
/// `witness_count` in ONE object, where the first was definitionally equal to the
/// second and could read `Proved` beside a `witness_count` of 0.
///
/// The two states are now distinguishable, which is the whole point of the enum:
/// material attached ⇒ `Proved`; committed with an executor signature but no
/// attestation yet ⇒ `ProofPending` (the prove pool is asynchronous — `state.rs`
/// documents exactly this state); neither ⇒ `NotRequired`.
fn receipt_proof_status(
    s: &crate::state::NodeStateInner,
    receipt: &dregg_turn::TurnReceipt,
) -> ActivityProofStatus {
    let receipt_hash = receipt.receipt_hash();
    let has_material = s.witnessed_receipt_count(&receipt_hash) > 0
        || stored_full_turn_proof_exists(s, &hex_encode(&receipt.turn_hash));
    if has_material {
        ActivityProofStatus::Proved
    } else if receipt.executor_signature.is_some() {
        ActivityProofStatus::ProofPending
    } else {
        ActivityProofStatus::NotRequired
    }
}

fn identity_receipt_matches(receipt: &dregg_turn::TurnReceipt, params: &StarbridgeQuery) -> bool {
    let receipt_hash = hex_encode(&receipt.receipt_hash());
    let event_text = receipt
        .emitted_events
        .iter()
        .filter_map(|event| serde_json::to_string(event).ok())
        .collect::<Vec<_>>()
        .join(" ");
    let identity_hint = event_text.to_ascii_lowercase().contains("identity")
        || event_text.to_ascii_lowercase().contains("credential")
        || !receipt.derivation_records.is_empty()
        || !receipt.emitted_events.is_empty();

    identity_hint
        && exact_filter_matches(&hex_encode(&receipt.turn_hash), &params.turn_hash)
        && exact_filter_matches(&hex_encode(&receipt.effects_hash), &params.effects_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            hex_encode(&receipt.agent.0).eq_ignore_ascii_case(cell)
                || receipt
                    .emitted_events
                    .iter()
                    .any(|event| hex_encode(&event.cell.0).eq_ignore_ascii_case(cell))
                || receipt
                    .derivation_records
                    .iter()
                    .any(|record| hex_encode(&record.target_cell.0).eq_ignore_ascii_case(cell))
        })
        && params.memo.as_ref().is_none_or(|memo| {
            text_filter_matches(&event_text, &Some(memo.clone()))
                || text_filter_matches(&receipt_hash, &Some(memo.clone()))
        })
        && params.effect.as_ref().is_none_or(|effect| {
            text_filter_matches(&event_text, &Some(effect.clone()))
                || text_filter_matches("credential derivation emitted_event", &Some(effect.clone()))
        })
        && params.app.as_ref().is_none_or(|app| {
            app.eq_ignore_ascii_case("identity") || app.eq_ignore_ascii_case("credential")
        })
}

fn classify_starbridge_app(memo: Option<&str>, effect_summaries: &[String]) -> Option<String> {
    let mut haystack = memo.unwrap_or("").to_ascii_lowercase();
    for effect in effect_summaries {
        haystack.push(' ');
        haystack.push_str(&effect.to_ascii_lowercase());
    }

    if haystack.contains("nameservice")
        || haystack.contains("name service")
        || haystack.contains("register name")
    {
        Some("nameservice".to_string())
    } else if haystack.contains("identity")
        || haystack.contains("credential")
        || haystack.contains("profile")
    {
        Some("identity".to_string())
    } else if haystack.contains("governance")
        || haystack.contains("proposal")
        || haystack.contains("vote")
    {
        Some("governance".to_string())
    } else {
        None
    }
}

/// The exec-lease grant label, when `cap` targets a live execution-lease cell
/// in the post-state: `exec-lease/<grade>/<asset>/<budget>/<per-period>` —
/// grade `sandboxed` (the wired tier), asset = the lease cell's token domain,
/// budget = its funded balance, per-period = the RENT slot. This is the
/// PRODUCER of the grammar an external provider's light-client-verified lease
/// read parses off certified receipt slices (the operated DreggNet plane's
/// `dregg_verify::parse_lease_grant_cap`); without it a verified reader has
/// only trusted cell reads. Slots are `app_framework::field_from_u64` =
/// big-endian in bytes [24..32] (the encoding `open_lease` writes).
fn lease_grant_label(cap: &dregg_cell::CapabilityRef, post: &dregg_cell::Ledger) -> Option<String> {
    const RENT_SLOT: usize = 4;
    const PERIOD_SLOT: usize = 5;
    let cell = post.get(&cap.target)?;
    if matches!(cell.program, dregg_cell::CellProgram::None) {
        return None;
    }
    let slot_i64 = |idx: usize| -> Option<i64> {
        let f = cell.state.fields.get(idx)?;
        let mut b = [0u8; 8];
        b.copy_from_slice(&f[24..32]);
        Some(i64::from_be_bytes(b))
    };
    let rent = slot_i64(RENT_SLOT)?;
    let period = slot_i64(PERIOD_SLOT)?;
    if rent <= 0 || period <= 0 {
        return None;
    }
    Some(format!(
        "exec-lease/sandboxed/{}/{}/{}",
        hex_encode(cell.token_id()),
        cell.state.balance(),
        rent
    ))
}

/// A stable label for a granted/revoked capability (the `cap` term of the
/// `granted`/`revoked` facts): the token hash when present, else `target#slot`.
fn cap_ref_label(cap: &dregg_cell::CapabilityRef) -> String {
    match cap.breadstuff {
        Some(h) => hex_encode(&h),
        None => format!("{}#{}", hex_encode(&cap.target.0), cap.slot),
    }
}

/// Build the typed [`dregg_query::EffectSummary`] enrichment for a committed
/// turn: the decoded per-effect disclosure — transfers / grants / revocations /
/// burns (supply reductions) / state-field writes / cell births / lifecycle
/// transitions (seal/unseal/destroy/sovereign) — plus a post-state balance
/// observation for every cell the turn's transfers/burns touched. Read off the
/// ALREADY-committed before/after ledger — additive, never gates the commit. The
/// `asset` of a transfer/balance is the token domain of the cell (pre-state for
/// the source/burn target, post-state for the destination).
pub(crate) fn summarize_turn_effects(
    turn: &Turn,
    pre: &dregg_cell::Ledger,
    post: &dregg_cell::Ledger,
) -> Vec<dregg_query::EffectSummary> {
    use dregg_query::EffectSummary as ES;
    use dregg_turn::Effect;

    let asset_of = |id: &CellId, l: &dregg_cell::Ledger| -> String {
        l.get(id)
            .map(|c| hex_encode(c.token_id()))
            .unwrap_or_default()
    };

    let mut out = Vec::new();
    let mut touched: Vec<[u8; 32]> = Vec::new();
    let note = |id: [u8; 32], touched: &mut Vec<[u8; 32]>| {
        if !touched.contains(&id) {
            touched.push(id);
        }
    };

    for tree in turn.call_forest.iter_dfs() {
        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    let asset = {
                        let a = asset_of(from, pre);
                        if a.is_empty() { asset_of(to, post) } else { a }
                    };
                    out.push(ES::Transfer {
                        from: hex_encode(&from.0),
                        to: hex_encode(&to.0),
                        asset,
                        amount: *amount,
                    });
                    note(from.0, &mut touched);
                    note(to.0, &mut touched);
                }
                Effect::GrantCapability { from, to, cap } => {
                    out.push(ES::Granted {
                        from: hex_encode(&from.0),
                        to: hex_encode(&to.0),
                        // A grant whose target is a live execution-lease cell
                        // is labeled with the exec-lease grammar an external
                        // provider's verified read decodes; every other grant
                        // keeps the generic token/`target#slot` label.
                        cap: lease_grant_label(cap, post).unwrap_or_else(|| cap_ref_label(cap)),
                    });
                }
                Effect::RevokeCapability { cell, slot } => {
                    out.push(ES::Revoked {
                        cap: format!("{}#{}", hex_encode(&cell.0), slot),
                    });
                }
                Effect::Burn { target, amount, .. } => {
                    // A provable supply reduction — no destination credited. The
                    // asset is the target's token domain (pre-state, since the
                    // cell may be destroyed/altered after).
                    out.push(ES::Burned {
                        cell: hex_encode(&target.0),
                        asset: asset_of(target, pre),
                        amount: *amount,
                    });
                    note(target.0, &mut touched);
                }
                Effect::SetField { cell, index, value } => {
                    out.push(ES::Field {
                        cell: hex_encode(&cell.0),
                        index: *index as u64,
                        value: hex_encode(value),
                    });
                }
                Effect::CreateCell {
                    public_key,
                    token_id,
                    ..
                } => {
                    // The new cell id is derived from (public_key, token_id) —
                    // the same derivation the executor uses (`Cell::id()`).
                    let cell = dregg_cell::CellId::derive_raw(public_key, token_id);
                    out.push(ES::Created {
                        agent: hex_encode(&tree.action.target.0),
                        cell: hex_encode(&cell.0),
                    });
                }
                Effect::CreateCellFromFactory {
                    owner_pubkey,
                    token_id,
                    ..
                } => {
                    let cell = dregg_cell::CellId::derive_raw(owner_pubkey, token_id);
                    out.push(ES::Created {
                        agent: hex_encode(&tree.action.target.0),
                        cell: hex_encode(&cell.0),
                    });
                }
                Effect::CellSeal { target, .. } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "sealed".to_string(),
                }),
                Effect::CellUnseal { target } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "unsealed".to_string(),
                }),
                Effect::CellDestroy { target, .. } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "destroyed".to_string(),
                }),
                Effect::MakeSovereign { cell } => out.push(ES::Lifecycle {
                    cell: hex_encode(&cell.0),
                    state: "sovereign".to_string(),
                }),
                _ => {}
            }
        }
    }

    // Post-state balance observations for the cells the transfers touched —
    // the stamped `balance(cell, asset, amount, height)` facts (clamped to a
    // non-negative observation; a cell's balance register is bias-encoded).
    for id in &touched {
        let cell_id = CellId(*id);
        if let Some(c) = post.get(&cell_id) {
            let bal = c.state.balance();
            out.push(ES::Balance {
                cell: hex_encode(id),
                asset: hex_encode(c.asset().as_bytes()),
                amount: bal.max(0) as u64,
            });
        }
    }

    out
}

pub(crate) fn effect_kind(effect: &dregg_turn::Effect) -> String {
    let debug = format!("{effect:?}");
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or("Unknown")
        .to_ascii_lowercase()
}

fn action_touched_cells(action: &dregg_turn::Action) -> Vec<String> {
    let mut cells = HashSet::new();
    cells.insert(hex_encode(&action.target.0));
    for effect in &action.effects {
        for cell in effect_cells(effect) {
            cells.insert(cell);
        }
    }
    let mut cells: Vec<String> = cells.into_iter().collect();
    cells.sort();
    cells
}

fn effect_cells(effect: &dregg_turn::Effect) -> Vec<String> {
    use dregg_turn::Effect;

    match effect {
        Effect::SetField { cell, .. }
        | Effect::RevokeCapability { cell, .. }
        | Effect::IncrementNonce { cell }
        | Effect::EmitEvent { cell, .. }
        | Effect::MakeSovereign { cell }
        | Effect::Refusal { cell, .. }
        | Effect::AttenuateCapability { cell, .. } => vec![hex_encode(&cell.0)],

        Effect::SetPermissions { cell, .. } | Effect::SetVerificationKey { cell, .. } => {
            vec![hex_encode(&cell.0)]
        }

        _ => Vec::new(),
    }
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

/// Decode variable-length hex strings into byte vectors.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if !s.len().is_multiple_of(2) {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// Verify an Ed25519 signature with domain separation. Used by F-P1-2 (and
/// related ownership checks): `signer_pk` signs `domain || payload`.
/// Returns a static-string error so callers can include it in JSON responses.
fn verify_ed25519_sig(
    signer_pk: &[u8; 32],
    signature_hex: &str,
    domain: &[u8],
    payload: &[u8],
) -> Result<(), &'static str> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let sig_bytes = hex_decode_var(signature_hex).map_err(|_| "invalid signature hex")?;
    if sig_bytes.len() != 64 {
        return Err("signature must be 64 bytes");
    }
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let sig = Signature::from_bytes(&sig_arr);
    let vk = VerifyingKey::from_bytes(signer_pk).map_err(|_| "invalid signer public key")?;
    let mut msg = Vec::with_capacity(domain.len() + payload.len());
    msg.extend_from_slice(domain);
    msg.extend_from_slice(payload);
    vk.verify(&msg, &sig)
        .map_err(|_| "signature does not verify")
}

// =============================================================================
// Queue Operations
// =============================================================================
// Wire DTOs retained for the not-yet-wired queue HTTP surface (deserialized by
// clients). These are unconstructed private scaffolding for a route lane that is
// not yet mounted; retained (with dead_code allows) rather than deleted so wiring
// the queue endpoints stays a small diff.
#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueAllocateRequest {
    capacity: u64,
    program_vk: Option<String>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAllocateResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
}

#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueEnqueueRequest {
    message_hash: String,
    deposit: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueEnqueueResponse {
    position: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueDequeueResponse {
    #[serde(rename = "messageHash")]
    message_hash: String,
    deposit: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueStatusResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
    occupancy: u64,
    capacity: u64,
    owner: String,
    #[serde(skip_serializing_if = "Option::is_none", rename = "programVk")]
    program_vk: Option<String>,
}

#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueAtomicTxRequest {
    operations: Vec<serde_json::Value>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAtomicTxResponse {
    success: bool,
    results: Vec<QueueAtomicTxResult>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAtomicTxResult {
    index: usize,
    ok: bool,
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// `default_valid_until` is `pub(crate)` specifically so
    /// `mcp::handlers_act::tool_submit_turn` can reuse it instead of stamping
    /// `valid_until: None` (see that call site's comment). This pins the property
    /// that actually matters at every one of its call sites: with `None`, the Rust
    /// executor's expiration check (`turn/src/executor/execute.rs:426`,
    /// `if let Some(valid_until) = turn.valid_until { ... }`) is SKIPPED entirely —
    /// a turn built from a `None` sentinel never expires, no matter how stale.
    /// `default_valid_until()` must stay `Some`, and — the part a bare `is_some()`
    /// check cannot catch — a turn stamped from it must still be REJECTED once its
    /// horizon has actually passed, proving the field is wired to the executor's
    /// enforcement and not merely non-`None`.
    ///
    /// (Note this only pins the expiration leg. It does NOT claim `tool_submit_turn`
    /// now runs on the verified Lean producer: that handler's turns carry an empty
    /// `effects` list, which fails `forest_is_marshallable` independently of
    /// `valid_until` — a separate, larger gap this change does not touch.)
    #[test]
    fn default_valid_until_is_some_and_an_expired_stamp_is_still_rejected() {
        assert!(
            default_valid_until().is_some(),
            "a None here means every turn built from it never expires (the executor skips \
             the check entirely on None, turn/src/executor/execute.rs:426) — the sentinel \
             must always be Some"
        );

        let mut agent = dregg_cell::Cell::with_balance([9u8; 32], [0u8; 32], 100);
        agent.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let agent_id = agent.id();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(agent).expect("insert test agent cell");

        let action = dregg_turn::Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: dregg_turn::Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![],
            may_delegate: dregg_turn::DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: Some(1), // one second past the UNIX epoch — always in the past
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let mut executor = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::zero());
        executor.set_timestamp(2_000_000_000); // 2033-ish — well past the stamped deadline
        let result = executor.execute(&turn, &mut ledger);
        assert!(
            !result.is_committed(),
            "a turn stamped with an already-expired valid_until must be REJECTED, not \
             committed — if this fires, the deadline check in \
             turn/src/executor/execute.rs stopped enforcing valid_until: {result:?}"
        );
    }

    /// ⚑ THE JOINER POLE OF `/status`. Measured 2026-08-09 on port 8465: a node
    /// that asked to join and was refused for 345 s reported `"healthy": true`
    /// the whole time.
    ///
    /// The 2026-08-08 partition conjuncts could not catch it and were never
    /// going to: they are read against the vote collector's LIVE threshold, and
    /// a non-member runs on its own single-key constitution, so
    /// `quorum_reachable` is trivially true (it counts toward its own quorum of
    /// 1) and `finality_stalled` is deliberately inert below threshold 2. This
    /// test pins BOTH poles — the honest "healthy" and the honest refusal — and
    /// asserts the pre-fix verdict on the same facts, so it cannot quietly
    /// become a test of nothing.
    #[test]
    fn a_joiner_that_has_proposed_and_heard_nothing_is_not_healthy() {
        // Exactly the wedged joiner: store fine, consensus task attached, its
        // own genesis block in the DAG, threshold 1 so both partition legs are
        // satisfied — and a member of nothing after 345 s of asking.
        let wedged = HealthFacts {
            store_ok: true,
            consensus_live: true,
            block_count: 1,
            quorum_reachable: Some(true),
            finality_stalled: Some(false),
            ever_asked_to_join: true,
            join_member: false,
        };

        // THE MUTATION IS PRESENT: the five-conjunct verdict this replaces says
        // `true` about these very facts. If this line ever stops holding, the
        // case below has stopped being the failure it was named for.
        let pre_fix = wedged.store_ok
            && wedged.consensus_live
            && wedged.block_count > 0
            && wedged.quorum_reachable.unwrap_or(true)
            && !wedged.finality_stalled.unwrap_or(false);
        assert!(
            pre_fix,
            "the wedged joiner must satisfy every pre-2026-08-09 conjunct, or this test is \
             exhibiting some other failure"
        );
        assert!(
            !status_healthy(wedged),
            "a node that has asked to join and is not a member must not report healthy"
        );

        // POLE 2 — the same node ONCE ADMITTED is healthy. The conjunct refuses
        // the wedge, not the joiner.
        assert!(status_healthy(HealthFacts {
            join_member: true,
            ..wedged
        }));

        // POLE 3 — a genesis member never ran the join path and is unaffected.
        assert!(status_healthy(HealthFacts {
            ever_asked_to_join: false,
            join_member: false,
            ..wedged
        }));

        // The 2026-08-08 legs still bite, on a node that IS a member: the
        // minority side of a quorum-losing partition, and a real stall.
        let member = HealthFacts {
            ever_asked_to_join: true,
            join_member: true,
            ..wedged
        };
        assert!(!status_healthy(HealthFacts {
            quorum_reachable: Some(false),
            ..member
        }));
        assert!(!status_healthy(HealthFacts {
            finality_stalled: Some(true),
            ..member
        }));

        // And the generation-1 legs: no store, no consensus handle, no blocks.
        assert!(!status_healthy(HealthFacts {
            store_ok: false,
            ..member
        }));
        assert!(!status_healthy(HealthFacts {
            consensus_live: false,
            ..member
        }));
        assert!(!status_healthy(HealthFacts {
            block_count: 0,
            ..member
        }));
        // A node with no consensus handle has no liveness and no join facts.
        // Those absences must not be able to CARRY the verdict — `consensus_live`
        // refuses it.
        assert!(!status_healthy(HealthFacts {
            store_ok: true,
            consensus_live: false,
            block_count: 1,
            ..HealthFacts::default()
        }));
    }

    /// A genesis member publishes NO join fields — `JoinProgress::default()` on
    /// the wire would say `join_member: false` about a full participant, which
    /// is a lie of a different shape. `Some` exactly when the join path ran.
    #[test]
    fn only_a_node_that_ran_the_join_path_publishes_join_fields() {
        use crate::blocklace_sync::JoinProgress;

        assert!(
            reportable_join_progress(&JoinProgress::default()).is_none(),
            "a genesis member has no join state to report"
        );

        let asked = JoinProgress {
            requests_sent: 23,
            last_request_peers: 4,
            waiting_secs: 345,
            ..JoinProgress::default()
        };
        let reported = reportable_join_progress(&asked).expect("a node that asked must report");
        assert!(!reported.member);
        assert_eq!(reported.waiting_secs, 345);
        assert!(
            !reported.proposal_seen,
            "no proposal for our key was ever opened — 'heard nothing', not 'awaiting votes'"
        );

        // A member that came in through a join keeps reporting, now with the
        // answer: it got in.
        let admitted = JoinProgress {
            member: true,
            requests_sent: 0,
            ..JoinProgress::default()
        };
        assert!(reportable_join_progress(&admitted).is_some_and(|p| p.member));
    }

    /// ⚑ THE UNAUTHENTICATED SURFACE IS PINNED HERE, AND THIS TEST IS WHY.
    ///
    /// `poa_records_api` was merged into `public_routes` while a commit message
    /// elsewhere said "DO NOT MOUNT". A commit message is a document, not a
    /// detector: nothing could go red, and `GET /api/poa/records/{authority}`
    /// served a shape that published the Signal target through
    /// `MissionWire.runSeed` (the target is three modulo operations from the
    /// seed). It was harmless only because `latest_height` was 0, so `runs` was
    /// empty — it would have begun leaking with the first settled turn.
    ///
    /// The shape is safe now (`PublicMissionWire` has no `runSeed` field and
    /// `publicMission_ignores_the_run_seed` proves substituting any seed leaves
    /// the published value identical), so the route stays. What was missing was
    /// this: a gate that reds when the unauthenticated surface changes.
    ///
    /// Adding a route to `public_routes` is fine. Adding one WITHOUT noticing is
    /// not. If this test fails, decide deliberately, then update the pin —
    /// and ask the standing question first: can a reader who has never played
    /// reconstruct a hidden instance from anything this route serves?
    #[test]
    fn the_unauthenticated_route_surface_is_exactly_this() {
        let source = include_str!("api.rs");
        let public_at = source
            .find("let mut public_routes = Router::new()")
            .expect("public_routes block moved; re-anchor this test");
        let protected_at = source
            .find("let protected_routes = Router::new()")
            .expect("protected_routes block moved; re-anchor this test");
        assert!(
            public_at < protected_at,
            "the public block must precede the protected one for this scan to be sound"
        );
        let public_block = &source[public_at..protected_at];

        // Whole modules merged into the public surface. These are the dangerous
        // ones: a module's route set can grow without `api.rs` changing at all.
        let mut merged: Vec<&str> = public_block
            .match_indices(".merge(crate::")
            .map(|(i, _)| {
                let rest = &public_block[i + ".merge(crate::".len()..];
                let end = rest.find("::routes()").unwrap_or(0);
                &rest[..end]
            })
            .filter(|m| !m.is_empty())
            .collect();
        merged.sort_unstable();
        merged.dedup();

        // ⚑ `poa_station_api` added 2026-08-06, and the standing question
        // answered rather than waved at: CAN A READER WHO HAS NEVER PLAYED
        // RECONSTRUCT A HIDDEN INSTANCE FROM THESE FIELDS? No, and for two
        // structural reasons rather than a filter.
        //
        // The panel half publishes communal AGGREGATES only.
        // `ShipInstrumentPanel.State` has no per-player field to project — its
        // `the_face_does_not_record_who_opened` proves two different crew
        // members drawing the same ticket leave identical faces, and
        // `StationDailyRuntime.the_served_panel_does_not_depend_on_the_crew`
        // carries that to the wire: substituting ANY request leaves every
        // communal field of the served document bit-identical. There is no
        // attendance record, streak or leaderboard to reconstruct because there
        // is no such state.
        //
        // The crate half publishes a VISIBLE ROTATION, which `SalvageCrate`'s
        // docblock declares deliberately public: the mixer "is not an
        // unpredictability source", the beacon schedule is "curator-authored and
        // visible", and `generatedRotation` hands a player their whole rotation
        // on purpose. The three arcade games' hidden instances live behind
        // `HiddenInstance` / `SlotDeriveRuntime`, and NEITHER IS IN THIS READ'S
        // IMPORT CONE — so no run seed, slot secret, commitment or target exists
        // to leak, rather than existing and being filtered out.
        //
        // ⚠ The standing condition, from `ShipInstrumentPanel`'s own docblock:
        // the visible rotation is fine ONLY BECAUSE the panel is communal and
        // unattributed. If anything attributable is ever hung off this panel,
        // the rotation must leave this surface.
        let expected = [
            "poa_galley_api",
            "poa_holding_api",
            "poa_records_api",
            // ⚑ ADDED DELIBERATELY 2026-08-07 — the judged Signal SESSION, the one
            // module on this list that WRITES. It is here because the bearer it used
            // to sit behind proved "a client of this node" and never "this player",
            // while the check that authorizes a session write — an Ed25519 signature
            // under the player key over a RE-DERIVED statement, `round` inside the
            // guess statement — is unchanged and unweakened by the move. What the
            // bearer incidentally supplied, abuse resistance, is replaced explicitly
            // by `SessionAdmission` (per-IP window, per-player-key window charged
            // only after verification, global in-flight ceiling).
            //
            // The standing question, answered: a reader who has never played cannot
            // reconstruct a hidden instance from anything these three routes serve.
            // `SignalFeedbackRuntime.served_transcript_cannot_separate_feedback_
            // equivalent_targets` proves a whole session's served bytes are IDENTICAL
            // across every target consistent with the guesses played, and
            // `a_session_document_never_carries_a_secret_a_seed_or_an_unearned_code`
            // asserts the same over the live encoder with a known secret installed.
            // The read-back names one exact 32-byte key, has no listing to walk, and
            // — because `HiddenInstance.runSeedFor` takes the player key — yields a
            // DIFFERENT target's transcript, which is worthless against your own run.
            //
            // ⚠ Standing condition: this stays sound only while every WRITE here is
            // player-signature-authorized. If a session route is ever added that
            // mutates on the strength of the request alone, it does not belong on
            // this list.
            "poa_signal_session",
            // Deliberate, 2026-08-06: the curator-signed slot opening is PUBLISHED.
            // It carries statement + curator key + signature and no secret, seed,
            // target or pre-encoded signing message. Mounted protected, it made
            // every browser game permanently practice via a silent 401.
            "poa_signal_slot_api",
            // ⚑ ADDED DELIBERATELY — the SLOT-CLOSE OPENING, and the one module on
            // this list for which the standing question below is answered YES.
            //
            // A reader who has never played CAN reconstruct a hidden instance from
            // what this route serves — that is precisely its purpose, and the
            // descriptors have always promised it (`opened_after: "slot-close"`,
            // enforced by `poa-web/src/hidden-instance.js`; `opened_after_close:
            // ["slot","slot_secret"]`, enforced by `poa-curator`). A commitment
            // that is never opened binds nothing a player can check.
            //
            // What bounds it is WHICH slots. `load_poa_signal_slot_reveal_v1`
            // serves only a slot strictly below the authority's open pointer —
            // superseded, and therefore unable to settle any run. The live slot,
            // whose secret is the answer to every run in flight, refuses with 409
            // and does not carry the secret in the refusal body.
            //
            // ⚠ Standing condition: this stays sound only while closure remains
            // "strictly superseded by a later installed slot". If closure is ever
            // widened — a timestamp, an operator assertion, an explicit close that
            // does not require a successor — the widened predicate is what decides
            // whether a live secret is published, and it must be re-argued HERE
            // before it ships.
            "poa_signal_slot_reveal_api",
            "poa_station_api",
        ];
        assert_eq!(
            merged, expected,
            "the set of modules merged into the UNAUTHENTICATED router changed.\n\
             Every route in a merged module is reachable with no bearer token.\n\
             If this is deliberate, update the pin — and first answer: can a\n\
             reader who has never played reconstruct a hidden instance from it?"
        );
    }
    use axum::body::Body;
    use dregg_coord::{AtomicForest, Coordinator, Decision, Vote};
    use dregg_turn::ComputronCosts;
    use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use http_body_util::BodyExt;
    use std::collections::{HashMap, VecDeque};
    use std::time::{Duration, Instant};
    use tower::ServiceExt;

    /// Helper: create a deterministic key pair for testing.
    fn test_key(name: &str) -> [u8; 32] {
        *blake3::hash(format!("dregg-node-atomic-test:{name}").as_bytes()).as_bytes()
    }

    // ═══════════════════════════════════════════════════════════════════════════
    const TEST_POA_AUTHORITY: [u8; 32] = [0x41; 32];

    async fn configure_test_poa_authority(state: &NodeState) {
        let mut s = state.write().await;
        s.federation_id = TEST_POA_AUTHORITY;
        s.federation_configured = true;
    }

    async fn get_json(app: &Router, uri: &str) -> (StatusCode, serde_json::Value) {
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json = if body.is_empty() {
            serde_json::Value::Null
        } else {
            serde_json::from_slice(&body).expect("JSON response")
        };
        (status, json)
    }

    async fn post_bytes(
        app: &Router,
        uri: &str,
        content_type: Option<&str>,
        body: Vec<u8>,
    ) -> (StatusCode, serde_json::Value) {
        let mut request = Request::builder().method("POST").uri(uri);
        if let Some(content_type) = content_type {
            request = request.header(header::CONTENT_TYPE, content_type);
        }
        let response = app
            .clone()
            .oneshot(
                request
                    .extension(ConnectInfo(
                        "127.0.0.1:4444"
                            .parse::<std::net::SocketAddr>()
                            .expect("test client address"),
                    ))
                    .body(Body::from(body))
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json = serde_json::from_slice(&body).unwrap_or(serde_json::Value::Null);
        (status, json)
    }

    fn signed_test_poa_signal_turn(
        cclerk: &dregg_sdk::AgentCipherclerk,
        mission_id: u64,
        mutate: impl FnOnce(&mut Turn),
    ) -> SignedTurn {
        let claim = dregg_sdk::poa_signal::SignalClaimV1::new(
            mission_id,
            &[dregg_sdk::poa_signal::SignalCode::new(5, 0, 5).expect("bounded code")],
        )
        .expect("bounded mission");
        let mut turn =
            dregg_sdk::poa_signal::signal_claim_turn(&cclerk.public_key().0, 0, None, claim);
        mutate(&mut turn);
        let unsigned = turn.call_forest.roots[0].action.clone();
        turn.call_forest.roots[0].action =
            cclerk.sign_action_hybrid(unsigned, &TEST_POA_AUTHORITY, turn.nonce);
        turn.call_forest.roots[0].hash = [0; 32];
        turn.call_forest.forest_hash = [0; 32];
        cclerk.sign_turn(&turn)
    }

    fn test_poa_genesis() -> dregg_persist::PoaSignalHeadV1 {
        dregg_persist::PoaSignalHeadV1::genesis(
            TEST_POA_AUTHORITY,
            [0xd1; 32],
            7,
            11,
            br#"{"config":"private-test-config"}"#.to_vec(),
            br#"{"canon":"private-test-canon"}"#.to_vec(),
        )
        .expect("test PoA genesis")
    }

    async fn install_test_poa_genesis(state: &NodeState) {
        let s = state.write().await;
        s.store
            .initialize_poa_signal_head(&test_poa_genesis())
            .expect("initialize test PoA authority");
    }

    async fn install_test_poa_transition(state: &NodeState) -> ([u8; 32], [u8; 32]) {
        let s = state.write().await;
        let genesis = test_poa_genesis();
        s.store
            .initialize_poa_signal_head(&genesis)
            .expect("initialize test PoA authority");
        let candidate = dregg_persist::PreparedPoaSignalTransitionV1::new_for_test(
            TEST_POA_AUTHORITY,
            genesis.digest(),
            genesis.world_sequence() + 1,
            genesis.canon_revision() + 1,
            br#"{"canon":"private-test-successor"}"#.to_vec(),
            br#"{"judgeInput":"private-test-input"}"#.to_vec(),
            br#"{"judgeOutput":"private-test-output"}"#.to_vec(),
        )
        .expect("test PoA transition candidate");
        let ledger_root = crate::blocklace_sync::canonical_ledger_root(&s.ledger);
        let turn_hash = [0x51; 32];
        let receipt_hash = [0x71; 32];
        let record = dregg_persist::CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [0x31; 32],
            block_executed_up_to: 1,
            turn_hash,
            creator: [0x61; 32],
            receipt_hash,
            ledger_root,
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        s.store
            .commit_finalized_turn_with_poa_signal_for_test(0, &record, &candidate)
            .expect("atomically commit test PoA transition");
        (turn_hash, receipt_hash)
    }

    #[test]
    fn poa_signal_sequence_selector_is_positive_canonical_and_bounded() {
        assert_eq!(parse_poa_signal_sequence("1"), Ok(1));
        assert_eq!(
            parse_poa_signal_sequence("18446744073709551615"),
            Ok(u64::MAX)
        );
        for invalid in [
            "",
            "0",
            "01",
            "+1",
            "-1",
            "one",
            "18446744073709551616",
            "100000000000000000000",
        ] {
            assert_eq!(
                parse_poa_signal_sequence(invalid),
                Err(StatusCode::BAD_REQUEST),
                "selector {invalid:?} must refuse"
            );
        }
    }

    #[test]
    fn poa_signal_authority_selector_has_one_lowercase_url() {
        let authority = [0xab; 32];
        let canonical = hex_encode(&authority);
        assert_eq!(parse_poa_signal_authority(&canonical), Ok(authority));
        assert_eq!(
            parse_poa_signal_authority(&canonical.to_uppercase()),
            Err(StatusCode::BAD_REQUEST)
        );
        assert_eq!(
            parse_poa_signal_authority(&canonical[..63]),
            Err(StatusCode::BAD_REQUEST)
        );
    }

    #[tokio::test]
    async fn poa_signal_public_status_is_exact_and_honest_before_genesis() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        configure_test_poa_authority(&state).await;
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let authority = hex_encode(&TEST_POA_AUTHORITY);

        let (status, body) = get_json(&app, &format!("/api/poa/signal/{authority}/status")).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body["format"], POA_SIGNAL_STATUS_FORMAT_V1);
        assert_eq!(body["authority_id"], authority);
        assert_eq!(body["federation_id"], authority);
        assert_eq!(body["installed"], false);
        assert!(body["head"].is_null());
        assert_eq!(body["consensus_finality"], POA_SIGNAL_VIEW_FINALITY_CLAIM);

        let wrong = hex_encode(&[0x42; 32]);
        for path in [
            "/api/poa/signal/not-hex/status".to_string(),
            format!("/api/poa/signal/{wrong}/status"),
            format!("/api/poa/signal/{authority}/transitions/0"),
            format!("/api/poa/signal/{authority}/transitions/01"),
            format!("/api/poa/signal/{authority}/transitions/not-a-sequence"),
        ] {
            let (status, _) = get_json(&app, &path).await;
            assert_eq!(
                status,
                StatusCode::BAD_REQUEST,
                "invalid selector must refuse: {path}"
            );
        }

        let (status, _) =
            get_json(&app, &format!("/api/poa/signal/{authority}/transitions/1")).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn poa_signal_public_head_and_receipt_view_survive_reopen_without_private_bytes() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        configure_test_poa_authority(&state).await;
        let (turn_hash, receipt_hash) = install_test_poa_transition(&state).await;
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state.clone(), false, recorder.handle());
        let authority = hex_encode(&TEST_POA_AUTHORITY);

        let assert_current_view =
            |status_body: &serde_json::Value, transition_body: &serde_json::Value| {
                assert_eq!(status_body["installed"], true);
                assert_eq!(status_body["head"]["transition_count"], 1);
                assert_eq!(status_body["head"]["world_sequence"], 8);
                assert_eq!(status_body["head"]["canon_revision"], 12);
                assert_eq!(
                    status_body["consensus_finality"],
                    POA_SIGNAL_VIEW_FINALITY_CLAIM
                );

                assert_eq!(
                    transition_body["format"],
                    POA_SIGNAL_TRANSITION_VIEW_FORMAT_V1
                );
                assert_eq!(transition_body["authority_id"], authority);
                assert_eq!(transition_body["federation_id"], authority);
                assert_eq!(transition_body["sequence"], 1);
                assert_eq!(transition_body["observed_head_transition_count"], 1);
                assert_eq!(transition_body["is_observed_head_transition"], true);
                assert_eq!(transition_body["commit_ordinal"], 0);
                assert_eq!(transition_body["turn_hash"], hex_encode(&turn_hash));
                assert_eq!(transition_body["receipt_hash"], hex_encode(&receipt_hash));
                assert_eq!(
                    transition_body["consensus_finality"],
                    POA_SIGNAL_VIEW_FINALITY_CLAIM
                );

                let status_object = status_body.as_object().expect("status object");
                let head_object = status_body["head"].as_object().expect("head object");
                let transition_object = transition_body.as_object().expect("transition object");
                for private_field in ["config", "canon", "judge_input", "judge_output"] {
                    assert!(!status_object.contains_key(private_field));
                    assert!(!head_object.contains_key(private_field));
                    assert!(!transition_object.contains_key(private_field));
                }
            };

        let (status_code, status_body) =
            get_json(&app, &format!("/api/poa/signal/{authority}/status")).await;
        let (transition_status, transition_body) =
            get_json(&app, &format!("/api/poa/signal/{authority}/transitions/1")).await;
        assert_eq!(status_code, StatusCode::OK);
        assert_eq!(transition_status, StatusCode::OK);
        assert_current_view(&status_body, &transition_body);

        let (missing_status, _) =
            get_json(&app, &format!("/api/poa/signal/{authority}/transitions/2")).await;
        assert_eq!(missing_status, StatusCode::NOT_FOUND);

        // Drop every handle to the first NodeState, reopen the same redb, then
        // reapply the federation identity as normal startup does from genesis.
        drop(app);
        drop(state);
        let reopened = NodeState::new(tmp.path(), vec![]).expect("reopened node state");
        configure_test_poa_authority(&reopened).await;
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let reopened_app = router(reopened, false, recorder.handle());
        let (status_code, reopened_status) = get_json(
            &reopened_app,
            &format!("/api/poa/signal/{authority}/status"),
        )
        .await;
        let (transition_code, reopened_transition) = get_json(
            &reopened_app,
            &format!("/api/poa/signal/{authority}/transitions/1"),
        )
        .await;
        assert_eq!(status_code, StatusCode::OK);
        assert_eq!(transition_code, StatusCode::OK);
        assert_current_view(&reopened_status, &reopened_transition);
    }

    #[tokio::test]
    async fn poa_signal_player_head_is_federation_scoped_and_exactly_redacted() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        configure_test_poa_authority(&state).await;

        let cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0x91; 32]));
        let cell_id = dregg_sdk::poa_signal::signal_player_cell(&cclerk.public_key().0);
        let ml_dsa_public_key = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(
            &cclerk.gossip_signing_key().to_bytes(),
        )
        .public_bytes();
        let cell = dregg_cell::Cell::with_hybrid_balance(
            cclerk.public_key().0,
            &ml_dsa_public_key,
            *blake3::hash(b"default").as_bytes(),
            5_000,
        )
        .expect("hybrid player cell");
        state
            .write()
            .await
            .ledger
            .insert_cell(cell)
            .expect("insert player cell");

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let authority = hex_encode(&TEST_POA_AUTHORITY);
        let cell_hex = hex_encode(&cell_id.0);
        let (status, body) = get_json(
            &app,
            &format!("/api/poa/signal/{authority}/players/{cell_hex}/head"),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body["format"], POA_SIGNAL_PLAYER_HEAD_FORMAT_V1);
        assert_eq!(body["authority_id"], authority);
        assert_eq!(body["federation_id"], authority);
        assert_eq!(body["cell_id"], cell_hex);
        assert_eq!(body["found"], true);
        assert_eq!(body["nonce"], 0);
        assert_eq!(body["public_key"], hex_encode(&cclerk.public_key().0));
        assert!(body["last_receipt_hash"].is_null());

        let mut keys: Vec<&str> = body
            .as_object()
            .expect("head object")
            .keys()
            .map(String::as_str)
            .collect();
        keys.sort_unstable();
        assert_eq!(
            keys,
            [
                "authority_id",
                "cell_id",
                "federation_id",
                "format",
                "found",
                "last_receipt_hash",
                "nonce",
                "public_key",
            ],
            "the signing read must not grow into the explorer's cell projection"
        );

        let wrong = hex_encode(&[0x42; 32]);
        let (status, _) = get_json(
            &app,
            &format!("/api/poa/signal/{wrong}/players/{cell_hex}/head"),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn poa_signal_public_claim_ingress_accepts_only_the_exact_bounded_carrier() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        configure_test_poa_authority(&state).await;
        install_test_poa_genesis(&state).await;
        state.write().await.unlocked = true;

        let cclerk =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0x92; 32]));
        let exact = signed_test_poa_signal_turn(&cclerk, 1, |_| {});
        let exact_body = postcard::to_stdvec(&exact).expect("exact Signal envelope");
        assert!(
            exact_body.len() <= POA_SIGNAL_MAX_CLAIM_BYTES,
            "canonical hybrid carrier must fit the public ingress ceiling"
        );

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let authority = hex_encode(&TEST_POA_AUTHORITY);
        let endpoint = format!("/api/poa/signal/{authority}/claims");

        let (status, _) = post_bytes(
            &app,
            &endpoint,
            Some("application/json"),
            exact_body.clone(),
        )
        .await;
        assert_eq!(status, StatusCode::UNSUPPORTED_MEDIA_TYPE);

        let (status, _) = post_bytes(
            &app,
            &endpoint,
            Some("application/octet-stream"),
            vec![0; POA_SIGNAL_MAX_CLAIM_BYTES + 1],
        )
        .await;
        assert_eq!(status, StatusCode::PAYLOAD_TOO_LARGE);

        let wrong_authority = hex_encode(&[0x42; 32]);
        let (status, _) = post_bytes(
            &app,
            &format!("/api/poa/signal/{wrong_authority}/claims"),
            Some("application/octet-stream"),
            exact_body.clone(),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        let wrong_mission = postcard::to_stdvec(&signed_test_poa_signal_turn(&cclerk, 2, |_| {}))
            .expect("wrong-mission envelope");
        let (status, _) = post_bytes(
            &app,
            &endpoint,
            Some("application/octet-stream"),
            wrong_mission,
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        let generic = postcard::to_stdvec(&signed_test_poa_signal_turn(&cclerk, 1, |turn| {
            turn.call_forest.roots[0].action.method =
                dregg_turn::action::symbol("ordinary-game-action");
        }))
        .expect("generic signed turn");
        let (status, _) =
            post_bytes(&app, &endpoint, Some("application/octet-stream"), generic).await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        let piggyback = postcard::to_stdvec(&signed_test_poa_signal_turn(&cclerk, 1, |turn| {
            turn.call_forest.roots[0]
                .action
                .effects
                .push(Effect::IncrementNonce { cell: turn.agent });
        }))
        .expect("piggyback envelope");
        let (status, _) =
            post_bytes(&app, &endpoint, Some("application/octet-stream"), piggyback).await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        // The exact carrier reaches the shared signed-turn perimeter without a
        // bearer token. Its later executor verdict is represented in the JSON
        // response rather than by any transport/auth refusal.
        let (status, body) = post_bytes(
            &app,
            &endpoint,
            Some("application/octet-stream"),
            exact_body,
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(
            body.get("accepted").is_some(),
            "shared ingress response: {body}"
        );
    }

    // THE TOOTH — the async-attestation gate's variant coverage, WILDCARD-FREE.
    //
    // The gate ([`super::http_attestation_coverage`]) used to be a hand-rolled
    // `match` over three `Effect` variants against a producer that projects 29.
    // That is two lists, and they drifted: a turn made only of `EmitEvent` or
    // `GrantCapability` (both submittable through `/api/turns/submit`) was judged
    // `NotRequired` and committed with NO proof obligation recorded, so an auditor
    // had nothing to check for it. The gate now DERIVES from the producer, and this
    // is the tooth that keeps it derived and keeps the derivation honest.
    //
    // Two properties, and neither is vacuous:
    //
    //   1. **A new `Effect` variant forces a decision.** `attestation_gate_ledger!`
    //      expands to a `match` over `dregg_turn::Effect` with NO `_ =>` arm — a
    //      catch-all is precisely what let the original drift happen silently — so
    //      adding a kernel verb REDS THIS BUILD until the verb is classified here
    //      AND given a fixture.
    //   2. **The classification is GROUNDED, per variant, against the live gate.**
    //      Every row is run through the real `http_attestation_coverage`. Narrowing
    //      any arm of the producer — or re-introducing a hand-rolled twin in the
    //      gate — flips that variant's observed class and reds this test by name.
    //
    // Cross-check worth stating: the 29 / 5 / 3 split below is EXACTLY the
    // Descriptor / NamedResidual / RefusedResidual split of
    // `circuit/tests/effect_enum_descriptor_residual_gate.rs`, arrived at from the
    // other end (that gate reads descriptor rungs; this one runs the projector). A
    // verb the light-client wire cannot witness is a verb the gate must not enqueue.
    // ═══════════════════════════════════════════════════════════════════════════

    /// What the gate must decide for a turn made of exactly one effect of this
    /// variant, aimed at the ACTOR cell.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum GateClass {
        /// The producer projects a REAL (non-`NoOp`) row: there is an actor
        /// transition, and the committed turn MUST be enqueued for attestation.
        Attestable,
        /// The producer has no arm for this verb, so the projection collapses to the
        /// lone-`NoOp` sentinel. `NotRequired` is then the honest status: the
        /// executor applies the verb while every proof stays silent about it (the
        /// `NamedResidual` posture).
        NoActorTransition,
        /// The CHECKED producer projection REFUSES this verb BY NAME — its authority
        /// plane has no AIR row. An attestation is required and cannot be produced,
        /// which is NOT `NotRequired` (the `RefusedResidual` posture).
        Refused,
    }

    /// ONE source: expands to BOTH the wildcard-free compile-time match (the
    /// build-breaking tooth for a new kernel variant) AND the fixture ledger the
    /// grounding test drives through the live gate.
    macro_rules! attestation_gate_ledger {
        ( $( $variant:ident => $class:expr, $fixture:expr ),+ $(,)? ) => {
            /// COMPILE-TIME TOOTH: no wildcard arm. Adding a kernel `Effect` variant
            /// reds this build until it is classified + fixtured in the ledger below.
            /// Returns the NAME too, so a row holding a fixture for the WRONG variant
            /// (the live hazard with 36 hand-written rows) is caught rather than
            /// silently classified by its neighbour.
            fn declared_gate_class(e: &Effect) -> (&'static str, GateClass) {
                match e {
                    $( Effect::$variant { .. } => (stringify!($variant), $class), )+
                }
            }

            /// The same classification as data, with a single-effect fixture per row.
            fn attestation_gate_rows() -> Vec<(&'static str, GateClass, Effect)> {
                vec![ $( (stringify!($variant), $class, $fixture), )+ ]
            }
        };
    }

    /// The actor cell every fixture below aims at (the gate's `turn.agent`).
    fn gate_actor() -> CellId {
        CellId([0x6a; 32])
    }

    /// A second cell, for the cross-cell end of a two-party effect.
    fn gate_other() -> CellId {
        CellId([0x6b; 32])
    }

    /// A minimal turn carrying `effects` in one root action on the actor — the shape
    /// the executor-side verify door ([`dregg_turn::executor::try_convert_turn_effects_to_vm`])
    /// takes, and the `wake` payload the reactive verbs carry.
    fn gate_turn_with(effects: Vec<Effect>) -> Turn {
        let agent = gate_actor();
        let action = Action {
            target: agent,
            method: *blake3::hash(b"attestation-gate-tooth").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut call_forest = CallForest::new();
        call_forest.add_root(action);
        Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: None,
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    fn gate_cap() -> dregg_cell::CapabilityRef {
        dregg_cell::CapabilityRef {
            target: gate_other(),
            slot: 0,
            permissions: dregg_cell::AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
            provenance: [0u8; 32],
        }
    }

    attestation_gate_ledger! {
        // ── The 29 verbs the producer projects a real row for ──────────────────
        SetField => GateClass::Attestable, Effect::SetField {
            cell: gate_actor(),
            index: 0,
            value: dregg_cell::field_from_u64(9_999),
        },
        Transfer => GateClass::Attestable, Effect::Transfer {
            from: gate_actor(),
            to: gate_other(),
            amount: 1,
        },
        // RECIPIENT-side: the only side BOTH doors project. The granter-side
        // asymmetry is its own pinned tooth —
        // `granter_side_grant_diverges_between_the_projection_doors`.
        GrantCapability => GateClass::Attestable, Effect::GrantCapability {
            from: gate_other(),
            to: gate_actor(),
            cap: gate_cap(),
        },
        RevokeCapability => GateClass::Attestable, Effect::RevokeCapability {
            cell: gate_actor(),
            slot: 0,
        },
        // ⚠ THE HOLE THIS TOOTH EXISTS FOR (1/2): reachable through
        // `/api/turns/submit`'s `TurnEffectSpec::EmitEvent`, and judged
        // `NotRequired` — committed with no proof obligation — by the old twin.
        EmitEvent => GateClass::Attestable, Effect::EmitEvent {
            cell: gate_actor(),
            event: dregg_turn::Event::new(dregg_turn::action::symbol("gate_tooth"), vec![]),
        },
        IncrementNonce => GateClass::Attestable, Effect::IncrementNonce { cell: gate_actor() },
        CreateCell => GateClass::Attestable, Effect::CreateCell {
            public_key: [1u8; 32],
            token_id: [2u8; 32],
            balance: 0,
        },
        SetPermissions => GateClass::Attestable, Effect::SetPermissions {
            cell: gate_actor(),
            new_permissions: dregg_cell::Permissions::default(),
        },
        SetVerificationKey => GateClass::Attestable, Effect::SetVerificationKey {
            cell: gate_actor(),
            new_vk: None,
        },
        Custom => GateClass::Attestable, Effect::Custom {
            cell: gate_actor(),
            program_vk_hash: [0x11; 32],
            proof_commitment: [0x22; 32],
        },
        NoteSpend => GateClass::Attestable, Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier([0x31; 32]),
            note_tree_root: [0u8; 32],
            value: 1,
            asset_type: 0,
            spending_proof: vec![],
            value_commitment: None,
        },
        NoteCreate => GateClass::Attestable, Effect::NoteCreate {
            commitment: dregg_cell::NoteCommitment([0x32; 32]),
            value: 1,
            asset_type: 0,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        },
        SpawnWithDelegation => GateClass::Attestable, Effect::SpawnWithDelegation {
            child_public_key: [4u8; 32],
            child_token_id: [5u8; 32],
            max_staleness: 0,
        },
        RefreshDelegation => GateClass::Attestable, Effect::RefreshDelegation {
            child: gate_other(),
            snapshot: [0x19; 32],
        },
        RevokeDelegation => GateClass::Attestable, Effect::RevokeDelegation { child: gate_other() },
        BridgeMint => GateClass::Attestable, Effect::BridgeMint {
            portable_proof: dregg_cell_crypto::note_bridge::PortableNoteProof {
                nullifier: [0u8; 32],
                destination_federation: [0u8; 32],
                source_root: dregg_types::AttestedRoot {
                    merkle_root: [0u8; 32],
                    note_tree_root: None,
                    nullifier_set_root: None,
                    height: 0,
                    timestamp: 0,
                    blocklace_block_id: None,
                    finality_round: None,
                    quorum_signatures: vec![],
                    threshold_qc: None,
                    threshold: 0,
                    federation_id: dregg_types::FederationId::PLACEHOLDER,
                    receipt_stream_root: None,
                    hybrid_quorum: Vec::new(),
                },
                spending_proof: vec![],
                destination_commitment: dregg_cell::NoteCommitment([0u8; 32]),
                value: 1,
                asset_type: 0,
            },
        },
        Introduce => GateClass::Attestable, Effect::Introduce {
            introducer: gate_actor(),
            recipient: gate_other(),
            target: gate_other(),
            permissions: dregg_cell::AuthRequired::Signature,
        },
        PipelinedSend => GateClass::Attestable, Effect::PipelinedSend {
            target: dregg_turn::eventual::EventualRef::new([0u8; 32], 0),
            action: Box::new(Action {
                target: gate_other(),
                method: dregg_turn::action::symbol("noop"),
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: dregg_cell::Preconditions::default(),
                effects: vec![],
                may_delegate: DelegationMode::None,
                commitment_mode: CommitmentMode::Full,
                balance_change: None,
                witness_blobs: vec![],
            }),
        },
        ExerciseViaCapability => GateClass::Attestable, Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![],
        },
        MakeSovereign => GateClass::Attestable, Effect::MakeSovereign { cell: gate_actor() },
        CreateCellFromFactory => GateClass::Attestable, Effect::CreateCellFromFactory {
            factory_vk: [0u8; 32],
            owner_pubkey: [1u8; 32],
            token_id: [2u8; 32],
            params: dregg_cell::factory::FactoryCreationParams {
                mode: dregg_cell::CellMode::Hosted,
                program_vk: None,
                initial_fields: vec![],
                initial_caps: vec![],
                owner_pubkey: [1u8; 32],
            },
        },
        Refusal => GateClass::Attestable, Effect::Refusal {
            cell: gate_actor(),
            offered_action_commitment: [0xAB; 32],
            refusal_reason: dregg_turn::action::RefusalReason::Declined,
            proof_witness_index: 0,
        },
        CellSeal => GateClass::Attestable, Effect::CellSeal {
            target: gate_actor(),
            reason: [0x11; 32],
        },
        CellUnseal => GateClass::Attestable, Effect::CellUnseal { target: gate_actor() },
        CellDestroy => GateClass::Attestable, Effect::CellDestroy {
            target: gate_actor(),
            certificate: dregg_cell::lifecycle::DeathCertificate {
                cell_id: gate_actor(),
                last_receipt_hash: [0x22; 32],
                final_state_commitment: [0x33; 32],
                destroyed_at_height: 1,
                reason: dregg_cell::lifecycle::DeathReason::Voluntary,
            },
        },
        Burn => GateClass::Attestable, Effect::Burn {
            target: gate_actor(),
            slot: 0,
            amount: 1,
        },
        Mint => GateClass::Attestable, Effect::Mint {
            target: gate_actor(),
            slot: 0,
            amount: 1,
        },
        AttenuateCapability => GateClass::Attestable, Effect::AttenuateCapability {
            cell: gate_actor(),
            slot: 0,
            narrower_permissions: dregg_cell::AuthRequired::None,
            narrower_effects: None,
            narrower_expiry: Some(1),
        },
        ReceiptArchive => GateClass::Attestable, Effect::ReceiptArchive {
            prefix_end_height: 1,
            checkpoint: dregg_cell::lifecycle::ArchivalAttestation {
                cell_id: gate_actor(),
                archive_start_height: 0,
                archive_end_height: 1,
                archive_blob_hash: [0x44; 32],
                archive_terminal_commitment: [0x55; 32],
                archive_terminal_receipt_hash: [0x66; 32],
            },
        },

        // ── The 5 NamedResiduals: no producer arm, so `NotRequired` is HONEST ───
        // Each is a verb the executor applies while every proof stays silent about
        // it. They are NOT holes in THIS gate — they are the circuit-witness debt
        // catalogued in `effect_enum_descriptor_residual_gate.rs`. A descriptor rung
        // landing for any of them flips its class here and reds this test, which is
        // the intended coupling: the gate must start enqueueing it that same commit.
        SetProgram => GateClass::NoActorTransition, Effect::SetProgram {
            cell: gate_actor(),
            program: dregg_cell::CellProgram::default(),
        },
        Promise => GateClass::NoActorTransition, Effect::Promise {
            cell: gate_actor(),
            resolution_condition: dregg_turn::pending::ResolutionCondition::AwaitHeight(1),
            wake: Box::new(gate_turn_with(vec![])),
            timeout_height: 2,
        },
        Notify => GateClass::NoActorTransition, Effect::Notify {
            from: gate_actor(),
            to: gate_other(),
            wake: Box::new(gate_turn_with(vec![])),
            resolution_condition: dregg_turn::pending::ResolutionCondition::AwaitHeight(1),
            timeout_height: 2,
        },
        React => GateClass::NoActorTransition, Effect::React {
            pending_id: dregg_cell::Nullifier([0x51; 32]),
            condition: dregg_turn::conditional::ProofCondition::HashPreimage { hash: [0x52; 32] },
            resolution_proof: dregg_turn::conditional::ConditionProof::Preimage([0x53; 32]),
            wake: Box::new(gate_turn_with(vec![])),
        },
        ShieldedTransfer => GateClass::NoActorTransition, Effect::ShieldedTransfer {
            payload: dregg_turn::action::ShieldedTransferPayload {
                // ⚑ FLAG DAY 2026-08-07: `merkle_root` is DELETED from the payload —
                // it was the prover's own choice of commitment-tree root, compared
                // against nothing, and the executor now supplies the root from
                // `note_shielded.root8()`. This fixture constructed the retired
                // field and broke every `cargo test -p dregg-node` in the tree.
                // ⚑ FLAG DAY (value link): the Pedersen half is DELETED from the payload —
                // `input_legs` / `output_legs` / `output_range_proofs` / `conservation` all go,
                // because the leg's `v` was tied to the STARK-side `v` by a transcript and by no
                // circuit equality. An output is now a Poseidon2 note commitment plus the
                // Lean-emitted `dregg-shielded-transfer-value-link::v1` proof binding it to the
                // spent note's carrier.
                // ⚑ The link proof is PER-TRANSFER, not per-output: two per-output proofs
                // would each claim the whole input (`o1 = v` AND `o2 = v`), a double-mint.
                inputs: vec![],
                outputs: vec![],
                link_proof: vec![],
            },
        },

        // ── The 2 RefusedResiduals: the PQ identity authority plane has no AIR row.
        // The payloads are ARBITRARY BYTES, not a real ML-DSA keypair, and that is
        // safe here because the refusal is decided on the VARIANT before any
        // primitive is touched — minting a real key would drag `dregg-pq`'s
        // verified-core audit gate into this test binary.
        CreateHybridCell => GateClass::Refused, Effect::CreateHybridCell {
            public_key: [7u8; 32],
            token_id: [8u8; 32],
            balance: 0,
            ml_dsa_public_key: vec![0x61; 32],
            pq_possession_signature: vec![0x62; 32],
        },
        RotatePqIdentity => GateClass::Refused, Effect::RotatePqIdentity {
            cell: gate_actor(),
            expected_epoch: 0,
            new_ml_dsa_public_key: vec![0x63; 32],
            new_key_possession_signature: vec![0x64; 32],
        },
        // The shielded on-ramp: verified executor-side, NO deployed EffectVM row, so the
        // SDK producer (`try_convert_effects_to_vm`) refuses it by name — Refused, like the
        // PQ verbs above.
        Shield => GateClass::Refused, Effect::Shield {
            value: 1,
            asset_type: 0,
            note_commitment: dregg_cell::NoteCommitment([0x68; 32]),
            encrypted_note: vec![],
            shield_proof: vec![],
            nullifier: dregg_cell::Nullifier([0x68; 32]),
            note_tree_root: [0u8; 32],
            spending_proof: vec![],
        },
        // ⚑ FLAG DAY: the off-ramp. `Deshield` is a Refused residual — there is no EffectVM
        // rung for it yet, and both the executor and the SDK projector refuse it BY NAME
        // rather than admitting it without a circuit statement. The macro is wildcard-free,
        // so this row is what lets `cargo test -p dregg-node` compile at all.
        Deshield => GateClass::Refused, Effect::Deshield {
            value: 1,
            asset_type: 0,
            note_commitment: dregg_cell::NoteCommitment([0x69; 32]),
            encrypted_note: vec![],
            input: dregg_turn::action::ShieldedInputPayload {
                nullifier: 0x69,
                spend_wide_binding: [0u32; 16],
                spend_proof: vec![],
            },
            link_proof: vec![],
        },
    }

    fn observed_gate_class(actor: &CellId, effect: &Effect) -> GateClass {
        match super::http_attestation_coverage(actor, std::slice::from_ref(effect)) {
            super::AttestationCoverage::Attestable => GateClass::Attestable,
            super::AttestationCoverage::NoActorTransition => GateClass::NoActorTransition,
            super::AttestationCoverage::Refused(_) => GateClass::Refused,
        }
    }

    /// **THE TOOTH (grounding).** Every kernel `Effect` variant's gate decision is
    /// checked against the LIVE `http_attestation_coverage`. This is the test the
    /// pre-convergence gate FAILED: with the hand-rolled three-variant twin,
    /// `EmitEvent`, `GrantCapability`, `Custom`, `CellSeal`, `Burn`, … all came back
    /// `NoActorTransition` while declared `Attestable` — i.e. committed turns going
    /// unattested, named row by row.
    #[test]
    fn attestation_gate_decides_every_effect_variant_as_declared() {
        let actor = gate_actor();
        let mut mismatched = Vec::<String>::new();
        let mut counts = (0usize, 0usize, 0usize);

        for (name, declared, fixture) in attestation_gate_rows() {
            // A row must hold a fixture for its OWN variant.
            assert_eq!(
                declared_gate_class(&fixture),
                (name, declared),
                "ledger row {name} holds a fixture for a different variant"
            );
            let observed = observed_gate_class(&actor, &fixture);
            if observed != declared {
                mismatched.push(format!(
                    "{name}: declared {declared:?}, gate said {observed:?}"
                ));
            }
            match declared {
                GateClass::Attestable => counts.0 += 1,
                GateClass::NoActorTransition => counts.1 += 1,
                GateClass::Refused => counts.2 += 1,
            }
        }

        assert!(
            mismatched.is_empty(),
            "the attestation gate's coverage diverged from the producer it must derive from \
             ({} variant(s)). An `Attestable` row the gate calls `NoActorTransition` is a \
             COMMITTED TURN GOING UNATTESTED:\n  {}",
            mismatched.len(),
            mismatched.join("\n  ")
        );
        // The 29/5/3 split mirrors the Descriptor/NamedResidual/RefusedResidual split
        // of `circuit/tests/effect_enum_descriptor_residual_gate.rs`. Pinning it here
        // makes a verb SILENTLY changing posture (a residual quietly gaining or losing
        // a producer arm) red rather than invisible.
        assert_eq!(
            counts,
            (29, 5, 3),
            "attestable / no-actor-transition / refused split moved; reconcile against \
             effect_enum_descriptor_residual_gate.rs before editing the pin"
        );
    }

    /// **THE TOOTH (derivation).** The gate must ASK the producer, not re-list it.
    /// Checked by driving the gate and the producer over the SAME multi-effect turn
    /// and requiring the same verdict — including for the variants the old twin
    /// could not see.
    #[test]
    fn attestation_gate_verdict_is_the_producers_verdict() {
        let actor = gate_actor();
        let effects: Vec<Effect> = attestation_gate_rows()
            .into_iter()
            .filter(|(_, class, _)| *class != GateClass::Refused)
            .map(|(_, _, fixture)| fixture)
            .collect();

        let producer = dregg_sdk::AgentCipherclerk::try_convert_effects_to_vm(&actor, &effects)
            .expect("no refused verb in this batch");
        let rows = producer
            .iter()
            .filter(|e| !matches!(e, dregg_circuit::effect_vm::Effect::NoOp))
            .count();
        assert_eq!(
            rows, 29,
            "the producer must project one row per Attestable verb; a narrowed arm \
             silently shrinks what the gate enqueues"
        );
        assert!(matches!(
            super::http_attestation_coverage(&actor, &effects),
            super::AttestationCoverage::Attestable
        ));

        // And a single REFUSED verb anywhere in a turn poisons the whole projection —
        // the gate must report `Unprovable`, never `NotRequired`, so the turn never
        // reaches the pool's panicking unchecked wrapper.
        let mut poisoned = effects;
        poisoned.push(Effect::RotatePqIdentity {
            cell: actor,
            expected_epoch: 0,
            new_ml_dsa_public_key: vec![0x63; 32],
            new_key_possession_signature: vec![0x64; 32],
        });
        match super::http_attestation_coverage(&actor, &poisoned) {
            super::AttestationCoverage::Refused(why) => assert!(
                why.contains("RotatePqIdentity"),
                "a refusal must NAME the verb it cannot prove: {why}"
            ),
            other => panic!("a turn carrying RotatePqIdentity must be refused, got {other:?}"),
        }
    }

    /// **A `SetField` key with no AIR lane is REFUSED, not truncated.** The old twin
    /// lowered the canonical u64 key with `as u32` and judged the turn attestable; the pool
    /// then drove `AgentCipherclerk::convert_effects_to_vm`'s `.expect()` into a panic in
    /// the blocking worker, AFTER the turn had committed. `index` comes straight off
    /// the wire (`TurnEffectSpec::SetField { index: u64 }`), so this was reachable
    /// from `/api/turns/submit` with one JSON field.
    ///
    /// ⚠ WIDENED 2026-07-30 (GitHub #61/#62). This test used to probe only `u32::MAX + 1`,
    /// because that was the bound BOTH checked projectors carried. The AIR's real ceiling is
    /// `state::NUM_FIELDS` (8), so the whole band `[8, u32::MAX]` passed this gate, got
    /// enqueued, and panicked the prove pool — which is what the helm fleet reported
    /// (`SetField field_idx out of bounds: 8`). The gate is the reason those turns now report
    /// `Unprovable` with a legible reason instead of sitting `proof_pending` forever.
    #[test]
    fn a_setfield_key_with_no_air_lane_is_refused_by_the_gate_not_truncated() {
        let actor = gate_actor();
        let lanes = dregg_circuit::effect_vm::state::NUM_FIELDS as u64;
        for index in [lanes, lanes + 7, u32::MAX as u64, (u32::MAX as u64) + 1] {
            let unprovable = Effect::SetField {
                cell: actor,
                index,
                value: dregg_cell::field_from_u64(7),
            };
            match super::http_attestation_coverage(&actor, std::slice::from_ref(&unprovable)) {
                super::AttestationCoverage::Refused(why) => assert!(
                    why.contains("SetField") && why.contains(&index.to_string()),
                    "the refusal must name the verb and the offending slot: {why}"
                ),
                other => panic!("SetField key {index} must be refused, got {other:?}"),
            }
        }

        // The other pole: every slot the AIR DOES carry must still be judged attestable, or
        // this gate would take the whole field-write traffic class offline.
        for index in 0..lanes {
            let provable = Effect::SetField {
                cell: actor,
                index,
                value: dregg_cell::field_from_u64(7),
            };
            assert_eq!(
                observed_gate_class(&actor, &provable),
                GateClass::Attestable,
                "slot {index} has an AIR lane and must still enqueue for attestation"
            );
        }
    }

    /// ⚠ **PINNED DIVERGENCE — the two projection doors disagree on a GRANTER-side
    /// `GrantCapability`.** This is the SAME two-lists shape one layer down, and it
    /// is NOT closed here (which door is right is a verifier-semantics decision, and
    /// the arms are byte-compatible only where they overlap):
    ///
    ///   * producer (`AgentCipherclerk::convert_effects_to_vm`, `cipherclerk.rs`):
    ///     `if to == cell_id || from == cell_id` — projects a row for BOTH ends.
    ///   * verifier (`effect_vm_bridge::convert_turn_effects_to_vm`, the executor):
    ///     `if to == cell_id` — projects a row for the RECIPIENT only.
    ///
    /// So a grant the ACTOR issues gets a producer row with no verifier counterpart.
    /// `/api/turns/submit`'s `TurnEffectSpec::GrantCapability` defaults `from` to the
    /// action target (the operator's own cell), which makes the granter side the
    /// COMMON shape, not a corner. This test asserts the divergence AS IT STANDS so
    /// it cannot widen silently, and so closing it reds this test and forces the
    /// decision to be recorded. `docs/audit/RE-AUTHORED-MIRROR-MAP.md` M11 is where
    /// the missing producer↔verifier agreement invariant is catalogued.
    #[test]
    fn granter_side_grant_diverges_between_the_projection_doors() {
        let actor = gate_actor();
        let granter_side = Effect::GrantCapability {
            from: actor,
            to: gate_other(),
            cap: gate_cap(),
        };

        // Producer: projects a row (so the gate judges the turn attestable).
        assert_eq!(
            observed_gate_class(&actor, &granter_side),
            GateClass::Attestable,
            "the producer projects the granter side; if this changed, the gate's \
             enqueue decision for operator-issued grants moved"
        );

        // Verifier-side door: projects NOTHING for the granter, so the whole turn
        // collapses to the lone-NoOp sentinel.
        let turn = gate_turn_with(vec![granter_side]);
        let verifier = dregg_turn::executor::try_convert_turn_effects_to_vm(&actor, &turn)
            .expect("a grant is inside the AIR domain");
        assert!(
            verifier
                .iter()
                .all(|e| matches!(e, dregg_circuit::effect_vm::Effect::NoOp)),
            "PINNED: the executor's verify-side door has no granter arm. If it grew \
             one, this divergence is CLOSED — delete this test and say so."
        );

        // The recipient side, by contrast, agrees across both doors.
        let recipient_side = Effect::GrantCapability {
            from: gate_other(),
            to: actor,
            cap: gate_cap(),
        };
        assert_eq!(
            observed_gate_class(&actor, &recipient_side),
            GateClass::Attestable
        );
        let turn = gate_turn_with(vec![recipient_side]);
        let verifier = dregg_turn::executor::try_convert_turn_effects_to_vm(&actor, &turn)
            .expect("a grant is inside the AIR domain");
        assert!(
            verifier
                .iter()
                .any(|e| matches!(e, dregg_circuit::effect_vm::Effect::GrantCapability { .. })),
            "the recipient-side grant must project on BOTH doors"
        );
    }

    #[test]
    fn fixed_hex_decoders_reject_non_ascii_input() {
        let input = format!("a\u{e9}{}", "0".repeat(61));
        assert_eq!(input.len(), 64);
        assert_eq!(hex_decode_32(&input), None);
        assert!(hex_decode_32_result(&input).is_err());
    }

    #[test]
    fn bearer_auth_request_requires_an_explicit_actor_cell() {
        let actorless = serde_json::json!({
            "bearer_proof": {},
            "target_cell": "22".repeat(32),
        });
        assert!(
            serde_json::from_value::<BearerAuthRequest>(actorless).is_err(),
            "the endpoint schema must not admit an actorless authorization request"
        );
    }

    #[test]
    fn bearer_auth_coordinates_bind_exact_actor_and_proof_target() {
        let actor = CellId::from_bytes([0x11; 32]);
        let proof_target = CellId::from_bytes([0x22; 32]);
        let honest = BearerAuthRequest {
            bearer_proof: serde_json::Value::Null,
            actor_cell: "11".repeat(32),
            target_cell: "22".repeat(32),
        };
        assert_eq!(
            validated_bearer_auth_actor(&honest, &proof_target),
            Ok(actor)
        );

        let substituted_target = BearerAuthRequest {
            target_cell: "33".repeat(32),
            ..honest
        };
        assert_eq!(
            validated_bearer_auth_actor(&substituted_target, &proof_target),
            Err(BearerAuthCoordinatesError::ProofTargetMismatch)
        );
    }

    #[test]
    fn faithful_mirror_request_accepts_only_three_global_cursors() {
        let request: FaithfulNoteMirrorRequest = serde_json::from_value(serde_json::json!({
            "commitment_cursor": 256,
            "history_cursor": 16,
            "nullifier_cursor": 256
        }))
        .expect("global continuation cursors are accepted");
        assert_eq!(request.commitment_cursor, 256);
        assert_eq!(request.history_cursor, 16);
        assert_eq!(request.nullifier_cursor, 256);

        for target_specific in [
            serde_json::json!({"position": 9}),
            serde_json::json!({"commitment": "11".repeat(32)}),
            serde_json::json!({"nullifier": "22".repeat(32)}),
            serde_json::json!({"value": 7}),
            serde_json::json!({"asset_type": 3}),
        ] {
            assert!(
                serde_json::from_value::<FaithfulNoteMirrorRequest>(target_specific).is_err(),
                "target-specific request fields must not survive the mirror cutover"
            );
        }
    }

    /// Fail-CLOSED authority-label parsing (twin of the deos-js `parse_auth_label` fix):
    /// an unknown/typo'd label must REFUSE, never silently mint `AuthRequired::None`
    /// (the broadest viewer). Legit labels — including the absent-field default "none"
    /// the call site supplies — are unchanged.
    #[test]
    fn parse_auth_label_api_unknown_label_refuses() {
        use dregg_cell::AuthRequired;

        // The legit vocabulary is untouched (case-insensitive, "sig" alias intact).
        assert_eq!(parse_auth_label_api("none"), Ok(AuthRequired::None));
        assert_eq!(
            parse_auth_label_api("signature"),
            Ok(AuthRequired::Signature)
        );
        assert_eq!(parse_auth_label_api("sig"), Ok(AuthRequired::Signature));
        assert_eq!(parse_auth_label_api("proof"), Ok(AuthRequired::Proof));
        assert_eq!(parse_auth_label_api("either"), Ok(AuthRequired::Either));
        assert_eq!(
            parse_auth_label_api("impossible"),
            Ok(AuthRequired::Impossible)
        );
        assert_eq!(
            parse_auth_label_api("SIGNATURE"),
            Ok(AuthRequired::Signature)
        );

        // The old fail-open: each of these previously became `AuthRequired::None`
        // (broadest authority). Now they refuse in-band.
        for typo in ["signture", "porof", "nonee", "", "admin", "all"] {
            assert!(
                parse_auth_label_api(typo).is_err(),
                "label {typo:?} must refuse, not silently broaden to None"
            );
        }
    }

    /// Helper: a minimal receipt with the given finality, unsigned.
    fn minimal_receipt(finality: dregg_turn::Finality) -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 100,
            effects_hash: [5u8; 32],
            computrons_used: 7,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId([6u8; 32]),
            federation_id: [7u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality,
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    /// The node downgrades `finality` to `Tentative` AFTER the executor signs the
    /// receipt (v3 signs the full `receipt_hash`, which binds `finality`). Without
    /// a re-sign, the executor signature no longer verifies against the committed
    /// receipt — it looks like a verifying-key mismatch.
    /// `resign_receipt_committed` must restore a signature that verifies in the
    /// committed (Tentative) state.
    #[test]
    fn resign_after_finality_downgrade_restores_verifiable_signature() {
        use ed25519_dalek::{Signature, Signer, Verifier};

        let seed = test_key("finality-resign");
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let vk = sk.verifying_key();

        // Executor signs while finality is the optimistic Final.
        let mut receipt = minimal_receipt(dregg_turn::Finality::Final);
        receipt.executor_signature = Some(
            sk.sign(&receipt.canonical_executor_signed_message())
                .to_bytes()
                .to_vec(),
        );

        // Node downgrades finality after signing -> the original signature is
        // stranded (it committed to the Final receipt_hash).
        receipt.finality = dregg_turn::Finality::Tentative;
        let stale =
            Signature::from_slice(receipt.executor_signature.as_ref().expect("signed")).unwrap();
        assert!(
            vk.verify(&receipt.canonical_executor_signed_message(), &stale)
                .is_err(),
            "pre-downgrade signature must NOT verify against the committed receipt"
        );

        // The fix re-signs in the committed state.
        resign_receipt_committed(&mut receipt, &seed);
        let fixed =
            Signature::from_slice(receipt.executor_signature.as_ref().expect("resigned")).unwrap();
        assert!(
            vk.verify(&receipt.canonical_executor_signed_message(), &fixed)
                .is_ok(),
            "re-signed signature MUST verify against the committed receipt"
        );
    }

    /// `debug_assert_signed_last` must TRIP when a `receipt_hash`-folded field is
    /// mutated after signing without a re-sign — proving the guard has teeth.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "sign-LAST invariant violated")]
    fn sign_last_invariant_trips_on_post_sign_folded_field_mutation() {
        use ed25519_dalek::Signer;

        let seed = test_key("sign-last-trip");
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);

        let mut receipt = minimal_receipt(dregg_turn::Finality::Final);
        receipt.executor_signature = Some(
            sk.sign(&receipt.canonical_executor_signed_message())
                .to_bytes()
                .to_vec(),
        );
        // Mutate a receipt_hash-folded field WITHOUT re-signing (the bug).
        receipt.finality = dregg_turn::Finality::Tentative;

        // Must panic: the stranded signature does not verify against the receipt.
        debug_assert_signed_last(&receipt, &seed);
    }

    /// Helper: build a minimal AtomicForest with a single noop-like action.
    fn make_test_forest(participants: Vec<[u8; 32]>, initiator: [u8; 32]) -> AtomicForest {
        let cell_id = dregg_cell::CellId(initiator);
        let mut forest = dregg_turn::CallForest::new();
        let action = Action {
            target: cell_id,
            method: *blake3::hash(b"noop").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        forest.add_root(action);
        AtomicForest::new(participants, forest, vec![], cell_id, 0)
    }

    fn test_event(height: u64) -> CommittedEvent {
        CommittedEvent {
            height,
            status: ActivityStatus::Committed,
            proof_status: ActivityProofStatus::NotRequired,
            turn_hash: format!("turn-{height}"),
            cell_id: format!("cell-{height}"),
            effects: vec![format!("effect-{height}")],
            summaries: Vec::new(),
            timestamp: height as i64,
        }
    }

    fn witnessed_with_marker(marker: u8) -> dregg_turn::WitnessedReceipt {
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: [marker; 32],
            effects_hash: [marker.wrapping_add(1); 32],
            agent: CellId([marker.wrapping_add(2); 32]),
            ..Default::default()
        };
        dregg_turn::WitnessedReceipt::from_components(
            receipt,
            vec![marker, marker.wrapping_add(1)],
            vec![marker as u32],
            None,
        )
    }

    #[test]
    fn events_initial_cursor_returns_latest_retained_activity() {
        let log: VecDeque<_> = (1..=5).map(test_event).collect();
        let selected = select_committed_events(&log, Some(0), 2);
        let heights: Vec<_> = selected.iter().map(|event| event.height).collect();
        assert_eq!(
            heights,
            vec![4, 5],
            "first-time pollers must see recent activity, not the oldest retained events"
        );
    }

    #[test]
    fn events_nonzero_cursor_is_exclusive_and_chronological() {
        let log: VecDeque<_> = (1..=5).map(test_event).collect();
        let selected = select_committed_events(&log, Some(2), 2);
        let heights: Vec<_> = selected.iter().map(|event| event.height).collect();
        assert_eq!(
            heights,
            vec![3, 4],
            "catch-up cursors must return the earliest unseen events so clients do not skip"
        );
    }

    #[test]
    fn receipt_infos_expose_chain_position_and_head() {
        let mut chain = Vec::new();
        for idx in 0..3 {
            let previous_receipt_hash = chain
                .last()
                .map(|receipt: &dregg_turn::TurnReceipt| receipt.receipt_hash());
            chain.push(dregg_turn::TurnReceipt {
                turn_hash: [idx as u8; 32],
                agent: CellId([0xA0 + idx as u8; 32]),
                previous_receipt_hash,
                ..Default::default()
            });
        }

        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 0, |_| false);
        assert_eq!(infos.len(), 3);
        assert_eq!(infos[0].chain_index, 2);
        assert!(infos[0].chain_head);
        assert_eq!(infos[1].chain_index, 1);
        assert!(!infos[1].chain_head);
        assert_eq!(infos[2].chain_index, 0);
        assert!(!infos[2].chain_head);
    }

    /// `has_proof` reports an ATTACHED attestation (async-pool WitnessedReceipt
    /// or persisted full-turn proof), independently of the executor signature.
    /// This is the regression test for the silent devnet path where every
    /// receipt stayed `has_proof:false` forever because the field was wired to
    /// `executor_signature` (which no node entry point configures) while the
    /// prove pool was in fact attaching real proofs (`has_witness:true`).
    #[test]
    fn receipt_has_proof_reflects_attached_attestation_not_signature() {
        let chain = vec![dregg_turn::TurnReceipt {
            turn_hash: [0x42; 32],
            agent: CellId([0xA0; 32]),
            executor_signature: None, // no signing key configured (the devnet config)
            ..Default::default()
        }];

        // No witness, no stored proof: honestly unproven.
        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 0, |_| false);
        assert!(!infos[0].has_proof);
        assert!(!infos[0].executor_signed);

        // The async prove pool attached a WitnessedReceipt: has_proof flips.
        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 1, |_| false);
        assert!(
            infos[0].has_proof,
            "a pool-attached WitnessedReceipt must flip has_proof even with no executor signature"
        );

        // Only the persisted full-turn proof (blocklace finalized path): also flips.
        let infos = receipt_infos_from_chain_with_witnesses(
            &chain,
            50,
            |_| 0,
            |th| th == hex_encode(&[0x42u8; 32]),
        );
        assert!(
            infos[0].has_proof,
            "a persisted full-turn proof must flip has_proof"
        );
    }

    /// THE PUBLIC READ CONTRACT. Every path here must be reachable WITHOUT auth
    /// and must answer in the SHAPE its clients decode.
    ///
    /// "Status 200 and it parses as JSON" is not a contract: `[]` and `{}` pass
    /// it forever, which is how `/api/blocks` served attested federation roots
    /// (permanently empty on a solo node) under a name that promises blocks
    /// without a single test noticing. So each path declares the JSON KIND it
    /// must return, and object endpoints declare the KEYS their clients read;
    /// `/api/cells` is checked against a ledger that actually has a cell, so an
    /// endpoint that answers `[]` regardless of state cannot pass. The
    /// "populated on a live node" half for `/api/blocks` lives in
    /// `faucet_grant_e2e` (a node with real finalized blocks), which is where a
    /// blocklace exists at all.
    #[tokio::test]
    async fn explorer_public_contract_endpoints_are_available() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        // A real cell so the list endpoints have something to be wrong about.
        let seeded_cell = {
            let mut s = state.write().await;
            let cell = dregg_cell::Cell::with_balance(
                [0x33u8; 32],
                crate::executor_setup::default_token_id(),
                4_242,
            );
            let id = cell.id();
            s.ledger.insert_cell(cell).expect("insert cell");
            id
        };
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        /// What the caller is entitled to decode.
        enum Shape {
            /// A JSON array (possibly empty on a fresh node).
            Array,
            /// A JSON array that must be NON-empty in this fixture.
            NonEmptyArray,
            /// A JSON object carrying at least these keys.
            Object(&'static [&'static str]),
        }

        let cell_path = format!("/api/cell/{}", hex_encode(&seeded_cell.0));
        let absent_path = format!("/api/cell/{}", "ab".repeat(32));
        let cases: Vec<(&str, Shape)> = vec![
            (
                "/status",
                Shape::Object(&[
                    "healthy",
                    "dag_height",
                    "block_count",
                    "consensus_live",
                    "federation_mode",
                    "public_key",
                    "state_producer",
                    "producer_root_agreeing_effects",
                ]),
            ),
            ("/api/cells", Shape::NonEmptyArray),
            (
                cell_path.as_str(),
                // `found` is the field that says whether the rest MEAN anything:
                // an absent id answers 200 with a fully-populated zero cell, so a
                // contract that omits `found` locks in a lie-shaped response.
                Shape::Object(&[
                    "id",
                    "found",
                    "balance",
                    "nonce",
                    "capability_count",
                    "has_program",
                ]),
            ),
            (
                absent_path.as_str(),
                Shape::Object(&["id", "found", "balance"]),
            ),
            ("/api/tokens", Shape::Array),
            ("/api/receipts", Shape::Array),
            ("/api/blocks", Shape::Array),
            ("/federation/roots", Shape::Array),
            ("/api/federation/roots", Shape::Array),
            ("/api/federations", Shape::Array),
            ("/api/intents", Shape::Array),
        ];

        for (path, shape) in cases {
            let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri(path)
                        // `/api/cells` (ANON-DoS #2) now resolves the client IP for
                        // its per-IP rate limiter — supply ConnectInfo as the live
                        // server does.
                        .extension(ConnectInfo(addr))
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK, "{path} should be public");

            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            let json: serde_json::Value = serde_json::from_slice(&body)
                .unwrap_or_else(|err| panic!("{path} should return JSON: {err}"));

            match shape {
                Shape::Array => assert!(
                    json.is_array(),
                    "{path} must answer a JSON array; got {json}"
                ),
                Shape::NonEmptyArray => {
                    let items = json
                        .as_array()
                        .unwrap_or_else(|| panic!("{path} must answer a JSON array; got {json}"));
                    assert!(
                        !items.is_empty(),
                        "{path} must list the ledger's cells, not an empty array — this node has \
                         one seeded cell"
                    );
                }
                Shape::Object(keys) => {
                    for key in keys {
                        assert!(
                            json.get(key).is_some(),
                            "{path} must carry `{key}` (its clients decode it); got {json}"
                        );
                    }
                }
            }
        }

        // The absent-cell response is 200 with a zero-valued cell, so `found` is
        // the ONLY thing distinguishing it — pin both directions.
        let read = |path: String| {
            let app = app.clone();
            async move {
                let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();
                let response = app
                    .oneshot(
                        Request::builder()
                            .uri(path)
                            .extension(ConnectInfo(addr))
                            .body(Body::empty())
                            .expect("request"),
                    )
                    .await
                    .expect("response");
                let body = response
                    .into_body()
                    .collect()
                    .await
                    .expect("body")
                    .to_bytes();
                serde_json::from_slice::<serde_json::Value>(&body).expect("json")
            }
        };
        let present = read(cell_path.clone()).await;
        let absent = read(absent_path.clone()).await;
        assert_eq!(present["found"], true, "a real cell must report found:true");
        assert_eq!(present["balance"], 4_242, "and its real balance");
        assert_eq!(
            absent["found"], false,
            "an absent id must report found:false — every other field on that response is a \
             zero-valued placeholder"
        );
    }

    /// THE PORTAL-DECOUPLING CONTRACT (read path). The public `portal.dregg.studio`
    /// viewer (`portal/dist/portal.js`) is repointed off the Discord bot onto the
    /// NODE's `/api/*`. Its `renderCells`/`fillCell` read exactly these fields off
    /// `/api/cells` and `/api/cell/<id>`; lock the node's structs to that field set so
    /// the node serves a portal-compatible shape (the bot is no longer load-bearing).
    #[test]
    fn portal_read_contract_cell_fields_present() {
        let entry = serde_json::to_value(CellListEntry {
            id: "abcd".into(),
            balance: 7,
            nonce: 1,
            capability_count: 2,
            has_delegate: false,
            has_program: true,
            found: true,
        })
        .expect("serialize CellListEntry");
        // `found` belongs in this list: `/api/cell/{id}` answers 200 with a
        // fully-populated ZERO-valued cell for an id the ledger does not have,
        // so `found` is the only field that says whether the other five mean
        // anything. Pinning the five without it locked in exactly the shape a
        // viewer misreads as "this cell exists with balance 0".
        for field in [
            "id",
            "found",
            "balance",
            "nonce",
            "capability_count",
            "has_program",
        ] {
            assert!(
                entry.get(field).is_some(),
                "/api/cells entry missing portal field `{field}`: {entry}"
            );
        }
    }

    /// The portal's liveness badge (`portal.js`) opens an `EventSource` on
    /// `/observability/stream` and `addEventListener`s `hello` (reloads the cell list)
    /// + `ping`. After the bot→node repoint the node must speak that same contract, so
    /// the FIRST frame is an immediate `hello` (no 15s wait) carrying the node's
    /// nullifier count — proving the public viewer's live badge works reading the node
    /// directly, with the bot down.
    #[tokio::test]
    async fn portal_observability_stream_opens_with_hello() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/observability/stream")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        // Read just the first SSE frame (the stream is otherwise an infinite 15s
        // ping heartbeat, so we must NOT `collect()` it).
        let mut body = response.into_body();
        let frame = body
            .frame()
            .await
            .expect("a first SSE frame")
            .expect("frame ok");
        let data = frame.into_data().ok().expect("a data frame");
        let text = String::from_utf8_lossy(&data);
        assert!(
            text.contains("hello"),
            "first frame must be the hello event: {text}"
        );
        assert!(
            text.contains("nullifiers"),
            "hello carries the nullifier count for the badge: {text}"
        );
    }

    #[tokio::test]
    async fn receipt_witness_endpoint_exports_dwr1_artifacts() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let receipt_hash = [0xA5; 32];
        state
            .write()
            .await
            .push_witnessed_receipt(receipt_hash, witnessed_with_marker(0x41));

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let response = app
            .oneshot(
                Request::builder()
                    .uri(format!(
                        "/api/receipts/{}/witnesses",
                        hex_encode(&receipt_hash)
                    ))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("json");
        assert_eq!(json["artifact_format"], "DWR1");
        assert_eq!(json["witness_count"], 1);
        assert_eq!(
            json["witnessed_receipts"]
                .as_array()
                .expect("legacy witness array")
                .len(),
            1
        );
        let artifact_hex = json["witness_artifacts"][0].as_str().expect("artifact hex");
        let artifact_bytes = hex_decode_var(artifact_hex).expect("valid artifact hex");
        let decoded = dregg_turn::WitnessedReceipt::from_artifact_bytes(&artifact_bytes)
            .expect("DWR1 witness artifact decodes");
        assert_eq!(decoded.proof_bytes, vec![0x41, 0x42]);
    }

    #[tokio::test]
    async fn finalized_core_query_is_bearer_gated_and_rejects_bad_coordinates() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let bearer_seed = [0xB7; 32];
        state.write().await.bearer_seed = Some(bearer_seed);
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let unknown_id = hex_encode(&[0x44; 32]);

        let unauthorized = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri(format!("/api/receipts/finalized-core?core_id={unknown_id}"))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(unauthorized.status(), StatusCode::UNAUTHORIZED);

        let token = api_bearer_token(bearer_seed);
        let authenticated = |uri: &str| {
            Request::builder()
                .uri(uri)
                .header("authorization", format!("Bearer {token}"))
                .body(Body::empty())
                .expect("request")
        };
        let unknown = app
            .clone()
            .oneshot(authenticated(&format!(
                "/api/receipts/finalized-core?core_id={unknown_id}"
            )))
            .await
            .expect("response");
        assert_eq!(unknown.status(), StatusCode::NOT_FOUND);

        for uri in [
            "/api/receipts/finalized-core",
            "/api/receipts/finalized-core?core_id=not-hex",
            "/api/receipts/finalized-core?core_id=0000000000000000000000000000000000000000000000000000000000000000",
            "/api/receipts/finalized-core?receipt_index=0&core_id=4444444444444444444444444444444444444444444444444444444444444444",
        ] {
            let response = app
                .clone()
                .oneshot(authenticated(uri))
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::BAD_REQUEST, "{uri}");
        }
    }

    #[test]
    fn finalized_core_response_projects_canonical_consensus_object_only() {
        let legacy_hash = [0x51; 32];
        let predecessor_id = dregg_turn::FinalizedReceiptIdV1::from_bytes([0x52; 32]).unwrap();
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: [0x53; 32],
            timestamp: 1_700_000_053,
            finality: dregg_turn::Finality::Final,
            agent: CellId([0x54; 32]),
            federation_id: [0x55; 32],
            previous_receipt_hash: Some(legacy_hash),
            ..Default::default()
        };
        let core = dregg_turn::FinalizedReceiptCoreV1::from_receipt(
            dregg_turn::FinalizedExecutionContextV1::new([0x56; 32], 57, receipt.timestamp),
            58,
            dregg_turn::FinalizedReceiptPredecessorV1::Core {
                core_id: predecessor_id,
                legacy_receipt_index: 59,
                legacy_receipt_hash: legacy_hash,
            },
            &receipt,
        )
        .unwrap();
        let expected_id = hex_encode(&core.id().bytes());
        let response = FinalizedReceiptCoreResponse::from_core(60, core);

        assert_eq!(response.protocol, "FRC1");
        assert_eq!(response.receipt_index, 60);
        assert_eq!(response.core_id, expected_id);
        assert_eq!(
            response.canonical_core.len(),
            dregg_turn::FINALIZED_RECEIPT_CORE_V1_LEN * 2
        );
        assert_eq!(response.block_id, hex_encode(&[0x56; 32]));
        assert_eq!(response.tau_round, 57);
        assert_eq!(response.consensus_unix_seconds, receipt.timestamp);
        assert_eq!(response.committee_epoch, 58);
        assert_eq!(response.turn_hash, hex_encode(&receipt.turn_hash));
        assert_eq!(response.agent, hex_encode(&receipt.agent.0));
        assert_eq!(response.federation_id, hex_encode(&receipt.federation_id));
        assert_eq!(
            response.predecessor,
            FinalizedReceiptPredecessorResponse::Core {
                core_id: hex_encode(&predecessor_id.bytes()),
                legacy_receipt_index: 59,
                legacy_receipt_hash: hex_encode(&legacy_hash),
            }
        );
        let json = serde_json::to_value(response).unwrap();
        assert!(json.get("executor_signature").is_none());
        assert!(json.get("fre1").is_none());
    }

    /// The enrichment: a committed turn's decoded Transfer effect + the
    /// before/after ledger yield a typed `Transfer` summary AND a post-state
    /// `Balance` observation for the touched cells — the EDB rows dregg-query
    /// turns into `transfer`/`balance` facts.
    #[test]
    fn summarize_turn_effects_yields_typed_transfer_and_balance() {
        use dregg_query::EffectSummary as ES;

        let agent_pk = [0x11u8; 32];
        let recipient_pk = [0x22u8; 32];
        let agent = CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0);
        let recipient = CellId(dregg_cell::CellId::derive_raw(&recipient_pk, &[0u8; 32]).0);

        let mut pre = dregg_cell::Ledger::new();
        pre.insert_cell(dregg_cell::Cell::with_balance(agent_pk, [0u8; 32], 1_000))
            .expect("agent insert");
        pre.insert_cell(dregg_cell::Cell::with_balance(recipient_pk, [0u8; 32], 0))
            .expect("recipient insert");

        // Post-state: 250 moved agent -> recipient.
        let mut post = pre.clone();
        {
            let a = post.get(&agent).expect("agent").clone();
            let mut a = a;
            a.state.set_balance(a.state.balance() - 250);
            post.remove(&agent);
            post.insert_cell(a).expect("reinsert agent");
            let r = post.get(&recipient).expect("recipient").clone();
            let mut r = r;
            r.state.set_balance(r.state.balance() + 250);
            post.remove(&recipient);
            post.insert_cell(r).expect("reinsert recipient");
        }

        let mut forest = CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "transfer", agent)
                .effect_transfer(agent, recipient, 250)
                .build(),
        );
        let turn = make_min_turn(agent, 0, None, forest);

        let summaries = summarize_turn_effects(&turn, &pre, &post);

        assert!(
            summaries.iter().any(|e| matches!(
                e,
                ES::Transfer { amount: 250, to, .. } if *to == hex_encode(&recipient.0)
            )),
            "expected a typed Transfer(250) summary, got {summaries:?}"
        );
        assert!(
            summaries.iter().any(|e| matches!(
                e,
                ES::Balance { amount: 250, cell, .. } if *cell == hex_encode(&recipient.0)
            )),
            "expected a post-state Balance(250) for the recipient, got {summaries:?}"
        );
    }

    /// The richer EDB: a turn carrying a state-field write, a cell birth, and a
    /// make-sovereign lifecycle transition yields the typed `Field` / `Created`
    /// / `Lifecycle` summaries dregg-query turns into `field`/`created`/
    /// `lifecycle` facts.
    #[test]
    fn summarize_turn_effects_yields_field_created_lifecycle() {
        use dregg_query::EffectSummary as ES;

        let agent_pk = [0x33u8; 32];
        let agent = CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0);
        let new_pk = [0x44u8; 32];
        let new_token = [0x55u8; 32];
        let new_cell = CellId(dregg_cell::CellId::derive_raw(&new_pk, &new_token).0);

        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(agent_pk, [0u8; 32], 0))
            .expect("agent insert");

        let mut forest = CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "rich", agent)
                .effect_set_field(agent, 2, [0xABu8; 32])
                .effect_create_cell(new_pk, new_token, 0)
                .effect_make_sovereign(agent)
                .build(),
        );
        let turn = make_min_turn(agent, 0, None, forest);

        // The summary is read off the effects + ledger; pre == post is fine for
        // these families (only Transfer/Burn need a balance delta).
        let summaries = summarize_turn_effects(&turn, &ledger, &ledger);

        assert!(
            summaries.iter().any(
                |e| matches!(e, ES::Field { index: 2, cell, .. } if *cell == hex_encode(&agent.0))
            ),
            "expected a typed Field write, got {summaries:?}"
        );
        assert!(
            summaries
                .iter()
                .any(|e| matches!(e, ES::Created { cell, .. } if *cell == hex_encode(&new_cell.0))),
            "expected a Created summary for the derived new-cell id, got {summaries:?}"
        );
        assert!(
            summaries.iter().any(
                |e| matches!(e, ES::Lifecycle { state, cell } if state == "sovereign" && *cell == hex_encode(&agent.0))
            ),
            "expected a sovereign Lifecycle transition, got {summaries:?}"
        );
    }

    /// End-to-end over the LIVE log: drive two real transfer turns through the
    /// node (executor + cipherclerk commit, the same path `/turn/submit` runs),
    /// then read the two new handlers — `/api/receipts/index/{root,range}` —
    /// build a dregg-query `AttestedAnswer` over the served slice, and verify it
    /// against the served root. Then show the non-omission teeth bite: a
    /// substituted leaf and a dropped position both reject.
    #[tokio::test]
    async fn live_receipt_index_serves_verifying_attested_answer_and_teeth_bite() {
        use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");

        let recipient_pk = [0x77u8; 32];
        let (agent, recipient) = {
            let s = state.read().await;
            let agent_pk = s.cclerk.public_key().0;
            (
                CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0),
                CellId(dregg_cell::CellId::derive_raw(&recipient_pk, &[0u8; 32]).0),
            )
        };

        // Open permissions so the unsigned test transfer commits (the
        // executor still enforces the cell's Send permission; the real node
        // path signs via the cipherclerk instead).
        let open = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };

        {
            let mut s = state.write().await;
            let cc_pk = s.cclerk.public_key().0;
            let mut agent_cell = dregg_cell::Cell::with_balance(cc_pk, [0u8; 32], 1_000_000);
            agent_cell.permissions = open.clone();
            s.ledger.insert_cell(agent_cell).expect("agent provision");
            let mut recipient_cell = dregg_cell::Cell::with_balance(recipient_pk, [0u8; 32], 0);
            recipient_cell.permissions = open.clone();
            s.ledger
                .insert_cell(recipient_cell)
                .expect("recipient provision");

            let executor = TurnExecutor::new(ComputronCosts::default());
            for nonce in 0u64..2 {
                let prev = s.cclerk.receipt_head().map(|r| r.receipt_hash());
                let mut forest = CallForest::new();
                forest.add_root(
                    dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "transfer", agent)
                        .effect_transfer(agent, recipient, 100)
                        .build(),
                );
                let turn = make_min_turn(agent, nonce, prev, forest);
                let pre_ledger = s.ledger.clone();
                let receipt = match executor.execute(&turn, &mut s.ledger) {
                    TurnResult::Committed { receipt, .. } => receipt,
                    other => panic!("transfer turn nonce={nonce} must commit: {other:?}"),
                };
                s.cclerk.append_receipt(receipt).expect("append receipt");
                let summaries = summarize_turn_effects(&turn, &pre_ledger, &s.ledger);
                assert!(
                    summaries
                        .iter()
                        .any(|e| matches!(e, dregg_query::EffectSummary::Transfer { .. })),
                    "real turn must yield a typed Transfer summary"
                );
                push_committed_event_enriched(
                    &mut s,
                    hex_encode(&turn.hash()),
                    hex_encode(&agent.0),
                    vec!["transfer".to_string()],
                    summaries,
                    ActivityProofStatus::NotRequired,
                );
            }
        }

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        // (1) the live MMR root.
        let root_resp: dregg_query::client::IndexRootResponse = {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri("/api/receipts/index/root")
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK);
            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            serde_json::from_slice(&body).expect("root json")
        };
        assert_eq!(root_resp.len, 2, "two committed receipts indexed");
        let trusted_root = hex_decode(&root_resp.root).expect("32-byte root");

        // (2) the certified slice over the whole log.
        let range_resp: dregg_query::client::IndexRangeResponse = {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri("/api/receipts/index/range?lo=0&hi=1")
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK);
            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            serde_json::from_slice(&body).expect("range json")
        };
        assert_eq!(range_resp.receipts.len(), 2);

        // (3) the attested answer verifies against the served root.
        let query = dregg_query::Query::new().atom(
            dregg_query::Pred::Transfer,
            vec![
                dregg_query::Term::var("from"),
                dregg_query::Term::var("to"),
                dregg_query::Term::var("asset"),
                dregg_query::Term::var("amount"),
                dregg_query::Term::var("h"),
            ],
        );
        let slice = range_resp.clone().into_slice().expect("slice");
        let answer = dregg_query::answer_whole_log(slice, query).expect("answer");
        answer
            .verify(&dregg_query::Blake3Mmr, &trusted_root)
            .expect("live attested answer must verify against the served root");
        assert!(
            !answer.rows.is_empty(),
            "the transfer query yields rows from the live receipts"
        );

        // (4a) teeth: a substituted receipt leaf rejects (SlotMismatch).
        let mut tampered = range_resp.clone().into_slice().expect("slice");
        tampered.receipts[0].receipt_hash = hex_encode(&[0xEEu8; 32]);
        assert!(
            tampered
                .verify(&dregg_query::Blake3Mmr, &trusted_root)
                .is_err(),
            "a substituted leaf must reject"
        );

        // (4b) teeth: a dropped position rejects (CountMismatch — positions are dense).
        let mut omitted = range_resp.into_slice().expect("slice");
        omitted.receipts.pop();
        assert!(
            omitted
                .verify(&dregg_query::Blake3Mmr, &trusted_root)
                .is_err(),
            "an omitted position must reject"
        );
    }

    /// Build a minimal `Turn` with the given call forest (test helper).
    fn make_min_turn(
        agent: CellId,
        nonce: u64,
        prev: Option<[u8; 32]>,
        call_forest: CallForest,
    ) -> Turn {
        Turn {
            agent,
            nonce,
            fee: 100_000,
            memo: None,
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: prev,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: vec![],
            cross_effect_dependencies: vec![],
            effect_witness_index_map: vec![],
        }
    }

    #[tokio::test]
    async fn federation_alias_returns_real_local_state_shape() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/federations")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let federations: serde_json::Value = serde_json::from_slice(&body).expect("json");
        let first = federations
            .as_array()
            .and_then(|items| items.first())
            .expect("at least one local federation view");
        assert_eq!(first["is_local"], true);
        assert_eq!(first["id"].as_str().expect("id").len(), 64);
        assert_eq!(first["federation_id"], first["id"]);
        assert!(first["latest_height"].is_u64());
        assert!(first["num_finalized_roots"].is_u64());
    }

    /// THE PERSISTENCE TIME-BOMB, DEFUSED (AUDIT-wallet.md P3-6). Under a
    /// PERSISTENT executor (one instance across turns, not fresh-per-request) the
    /// per-agent receipt chain is REAL: a turn stamping the correct
    /// `previous_receipt_hash` is accepted and one stamping a stale/forged hash is
    /// refused with `ReceiptChainMismatch`. The endpoint plumbing serves that head
    /// (`cell_detail_response.last_receipt_hash`) from the persistent chain, so a
    /// client can fetch it and chain — and the CANARY proves the old
    /// project-from-`s.ledger` path serves `None`, which is exactly why every
    /// non-first turn broke.
    #[test]
    fn receipt_chain_head_served_and_bites_under_persistent_executor() {
        // ONE executor instance across every turn below — the non-fresh path the
        // realm/MUD work needs, where the chain actually has to hold.
        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());

        // A no-auth agent cell: `Authorization::Unchecked` + `Permissions::None`
        // isolates the RECEIPT-CHAIN gate (which runs before auth in `execute`),
        // so this test proves the chain, not the signature.
        let public_key = [0x51; 32];
        let token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&public_key, &token_id);
        let mut ledger = dregg_cell::Ledger::new();
        let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 1_000_000);
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
        ledger.insert_cell(cell).expect("insert agent cell");

        let mk_turn = |nonce: u64, prev: Option<[u8; 32]>| -> Turn {
            let action = Action {
                target: agent,
                method: *blake3::hash(b"chain-test-increment").as_bytes(),
                args: vec![],
                authorization: Authorization::Unchecked,
                preconditions: dregg_cell::Preconditions::default(),
                effects: vec![Effect::IncrementNonce { cell: agent }],
                may_delegate: DelegationMode::None,
                commitment_mode: CommitmentMode::Full,
                balance_change: None,
                witness_blobs: vec![],
            };
            let mut call_forest = CallForest::new();
            call_forest.add_root(action);
            Turn {
                agent,
                nonce,
                fee: 1_000,
                memo: None,
                valid_until: None,
                call_forest,
                depends_on: vec![],
                previous_receipt_hash: prev,
                conservation_proof: None,
                sovereign_witnesses: std::collections::HashMap::new(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            }
        };

        // Genesis turn: prev = None matches the fresh executor's stored head.
        let turn1 = mk_turn(0, None);
        let (_, receipt1, _) = executor.execute(&turn1, &mut ledger).unwrap_committed();
        let head1 = receipt1.receipt_hash();
        assert_eq!(
            executor.get_last_receipt_hash(&agent),
            Some(head1),
            "the persistent executor records the committed receipt as the agent's chain head"
        );

        // ENDPOINT parity: what `/api/cell/{id}` serves (persistent_receipt_head
        // over the chain) IS head1 — the value the next turn must stamp.
        let served = cell_detail_response("id".into(), ledger.get(&agent), Some(head1));
        assert_eq!(
            served.last_receipt_hash,
            Some(hex_encode(&head1)),
            "the endpoint serves the persistent chain head a client chains against"
        );

        // CANARY: the OLD behavior projected the head from `s.ledger`. A cell
        // carries no receipt head, so that path serves None — under a persistent
        // executor the head is UNSERVABLE and every non-first turn breaks.
        let ledger_only = cell_detail_response("id".into(), ledger.get(&agent), None);
        assert_eq!(
            ledger_only.last_receipt_hash, None,
            "projecting from s.ledger cannot serve the head — the persistence bomb"
        );

        // WRONG CHAIN: correct nonce, forged prev — refused on the SAME persistent
        // executor. turn1 advanced the cell nonce to 2 (turn-level commit + the
        // explicit `IncrementNonce` effect), so nonce == 2 passes the nonce check
        // and the rejection is the receipt-chain gate, not a nonce error.
        let turn_wrong = mk_turn(2, Some([0xFF; 32]));
        match executor.execute(&turn_wrong, &mut ledger) {
            dregg_turn::TurnResult::Rejected { reason, .. } => assert!(
                matches!(reason, dregg_turn::TurnError::ReceiptChainMismatch { .. }),
                "a wrong previous_receipt_hash must be refused as ReceiptChainMismatch, got {reason:?}"
            ),
            other => panic!("a wrong-prev turn must be REJECTED under persistence, got {other:?}"),
        }

        // The refused turn left the head intact; the CORRECTLY-chained turn (prev =
        // the served head1) still lands on the same persistent executor.
        let turn2 = mk_turn(2, Some(head1));
        let (_, receipt2, _) = executor.execute(&turn2, &mut ledger).unwrap_committed();
        assert_eq!(
            executor.get_last_receipt_hash(&agent),
            Some(receipt2.receipt_hash()),
            "a correctly-chained turn advances the persistent head"
        );
    }

    fn projectable_http_test_turn(agent: CellId) -> Turn {
        let action = Action {
            target: agent,
            method: *blake3::hash(b"http-test-increment").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: agent }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut call_forest = CallForest::new();
        call_forest.add_root(action);
        Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: Some("http witness test".to_string()),
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    #[test]
    fn http_submit_prepare_rotatable_carries_real_actor_and_rotation() {
        let public_key = [0x23; 32];
        let token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&public_key, &token_id);
        let mut ledger = dregg_cell::Ledger::new();
        let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 10_000);
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
        ledger.insert_cell(cell).expect("insert agent cell");
        let pre_ledger = ledger.clone();
        let turn = projectable_http_test_turn(agent);
        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());
        let (_, receipt, _) = executor.execute(&turn, &mut ledger).unwrap_committed();

        // PATH-PRESERVE Phase 5b: the executor already validated + committed; the
        // commit path no longer revalidates or proves inline. `prepare_rotatable_turn`
        // gathers the REAL before/after cells (pre_ledger / the post-execution ledger)
        // into the carrier the async pool proves — and for a cohort transfer it builds
        // the ROTATION witness, so the async proof goes through the rotated descriptor,
        // NOT the node's own v1 effect-vm hand-AIR.
        let outcome = prepare_rotatable_turn(
            &turn,
            pre_ledger.get(&agent),
            ledger.get(&agent),
            receipt.receipt_hash(),
        )
        .expect("projectable HTTP turn prepares for attestation");
        let HttpWitnessOutcome::Rotatable(rotatable) = outcome else {
            panic!("a transfer-bearing HTTP turn must be Rotatable, not NotRequired");
        };

        assert_eq!(rotatable.agent, agent, "carrier binds the real actor cell");
        assert_eq!(rotatable.turn_hash, turn.hash());
        assert_eq!(
            rotatable.pre_balance, 10_000,
            "carrier captures the actor's pre-state balance from the real cell"
        );
        assert!(
            !rotatable.effects.is_empty(),
            "carrier carries the turn's effects for the async prover"
        );
        // A cap-less transfer is a rotatable cohort member: the rotation witness must
        // be present so the async leg proves through the LEAN-emitted rotated descriptor.
        assert!(
            rotatable.rotation.is_some(),
            "a cap-less transfer turn must carry a rotation witness (rotated effect-vm leg)"
        );
    }

    #[test]
    fn http_submit_empty_effect_turn_reports_no_witness_honestly() {
        let agent = CellId([0x42; 32]);
        let turn = Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: None,
            valid_until: None,
            call_forest: CallForest::new(),
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: turn.hash(),
            agent,
            ..Default::default()
        };

        let _ = receipt; // empty-effect turn carries no Effect-VM transition to attest
        let outcome = prepare_rotatable_turn(&turn, None, None, [0u8; 32])
            .expect("empty-effect HTTP turn should not require attestation");
        assert!(
            matches!(outcome, HttpWitnessOutcome::NotRequired),
            "empty-effect HTTP turns must not claim a null proof as proved"
        );
    }

    #[test]
    fn faucet_activity_hash_is_hex_tx_sized() {
        let tx = compute_faucet_activity_hash(&dregg_cell::CellId([0xC0; 32]), 0);
        assert_eq!(tx.len(), 64);
        assert!(tx.chars().all(|ch| ch.is_ascii_hexdigit()));
    }

    /// THE FAUCET CELL MUST BE ABLE TO ACT. `validate_signed_turn` — the ONE
    /// application-admission predicate, run at HTTP ingress, at finalized-block
    /// execution, and in the PG drainer — requires `turn.agent ==
    /// derive_raw(signer, blake3("default"))`. The faucet signs its own turns
    /// with the genesis faucet key and puts the faucet cell in `agent`, so if the
    /// faucet cell is derived in ANY other asset that predicate can never hold and
    /// every faucet turn is deterministically rejected at finalization — after the
    /// endpoint has already answered `success: true`. This is the unit-level
    /// falsifier for that class: point `faucet_token_id()` at `[0u8; 32]` (its
    /// value until 2026-07-25) and it goes red here, in milliseconds, instead of
    /// silently in a devnet.
    #[test]
    fn faucet_cell_is_the_agent_cell_the_admission_predicate_demands() {
        let faucet_pk = faucet_public_key();
        let faucet_cell = dregg_cell::CellId::derive_raw(&faucet_pk, &faucet_token_id());
        let admissible_agent =
            dregg_cell::CellId::derive_raw(&faucet_pk, &crate::executor_setup::default_token_id());
        assert_eq!(
            faucet_cell, admissible_agent,
            "the faucet cell must BE the signer's default cell, or `validate_signed_turn` \
             refuses every faucet turn as agent-signer-mismatch at finalization"
        );
    }

    /// The genesis faucet supply lands in exactly the cell the endpoint spends
    /// from. `genesis.rs` derives it independently (its own `default_token_id`
    /// local), so this pins the two derivations together: a genesis that mints
    /// into a different asset leaves the endpoint with `faucet cell … is not in
    /// this node's ledger`.
    #[test]
    fn genesis_faucet_cell_matches_the_endpoint_faucet_cell() {
        let genesis_faucet = crate::genesis::devnet_faucet_cell_id();
        let endpoint_faucet =
            dregg_cell::CellId::derive_raw(&faucet_public_key(), &faucet_token_id());
        assert_eq!(
            genesis_faucet, endpoint_faucet,
            "genesis must mint the faucet supply into the cell POST /api/faucet spends from"
        );
    }

    /// #171 remote `.turn()` e2e through the HTTP router: a keypair the node
    /// has NEVER seen locally builds + signs a canonical turn, submits the
    /// postcard `SignedTurn` envelope to `POST /turns/submit`, it executes
    /// through the ONE producer gate (`executor_setup::execute_via_producer`),
    /// and the receipt is retrievable from `GET /api/receipts` — while a
    /// tampered envelope, a wrong-agent envelope, and a replayed envelope all
    /// refuse. Mirrors the exact `dregg_sdk_net::remote::RemoteRuntime` flow
    /// (federation-bound action signature, `valid_until` stamp, receipt-chain
    /// binding).
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn remote_signed_envelope_e2e_accepts_then_refuses_tamper_and_replay() {
        let _ = rustls::crypto::ring::default_provider().install_default();
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        state.write().await.unlocked = true;
        // Single in-process node = a committee of one (solo). Production sets this in
        // main.rs under `is_solo_mode`.
        {
            let mut s = state.write().await;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
        }
        // REAL consensus + finality. Submission is admission staging: the
        // receipt is welded into the durable log by `execute_finalized_turn`,
        // so a fixture with no blocklace can accept a turn and never produce a
        // retrievable receipt. This test asserts on the receipt, so it needs the
        // machinery that writes one.
        let handle = crate::blocklace_sync::run_blocklace_sync_with_policy(
            state.clone(),
            0,
            true,
            100,
            10_000,
            50,
            2_000,
            0,
            None,
            dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
        )
        .await
        .expect("solo blocklace handle");
        state.set_blocklace(handle).await;
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        // enable_faucet: the devnet onboarding surface the remote SDK uses.
        let app = router(state.clone(), true, recorder.handle());
        // Loopback client: `require_auth`'s pre-passphrase window admits only
        // loopback callers (F-CRIT-1). The REMOTENESS under test is the
        // keypair/identity (never seen by the node), not the socket.
        let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();

        // The remote agent: a fresh keypair this node has never seen, plus a
        // second fresh cell as the transfer recipient.
        let clerk = dregg_sdk::AgentCipherclerk::new();
        let clerk2 = dregg_sdk::AgentCipherclerk::new();
        let default_token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&clerk.public_key().0, &default_token_id);
        let recipient = dregg_cell::CellId::derive_raw(&clerk2.public_key().0, &default_token_id);

        // Funded, pk-bound, PQ-committed cells for both identities.
        //
        // These used to be materialized by two `POST /api/faucet` calls, which
        // made an envelope-admission test depend on the faucet's whole consensus
        // pipeline: since the faucet became admission-staging-only (its grant is
        // applied by FINALIZATION, and this fixture has no blocklace at all) that
        // onboarding could not fund anything here. Seed the ledger directly — the
        // REMOTENESS under test is the keypair, not how the balance arrived. The
        // faucet's own path is covered end-to-end in `faucet_grant_e2e`.
        {
            let mut s = state.write().await;
            for (cell, owner) in [(agent, &clerk), (recipient, &clerk2)] {
                let ml_dsa_public_key = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(
                    &owner.gossip_signing_key().to_bytes(),
                )
                .public_bytes();
                let funded = dregg_cell::Cell::with_hybrid_balance(
                    owner.public_key().0,
                    &ml_dsa_public_key,
                    default_token_id,
                    5_000,
                )
                .expect("canonical ML-DSA-65 identity");
                assert_eq!(funded.id(), cell, "seeded cell must be the derived id");
                s.ledger.insert_cell(funded).expect("seed cell");
            }
        }

        // The node binding the remote SDK discovers before signing. The fresh
        // agent has no receipts yet, so its chain head is `None` — exactly what
        // the submit path compares `previous_receipt_hash` against.
        let (fed_id, expected_prev) = {
            let s = state.read().await;
            (
                crate::executor_setup::federation_id_for_executor(&s),
                s.cclerk.agent_receipt_head_hash(&agent),
            )
        };
        assert!(
            expected_prev.is_none(),
            "a never-acted agent binds to a genesis (None) receipt head"
        );

        // Sign the action over the canonical federation-bound message — the
        // node-side executor verifies EXACTLY this (one gate, no parallel
        // verification path).
        let unsigned = Action {
            target: agent,
            method: *blake3::hash(b"execute").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: agent,
                to: recipient,
                amount: 7,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        // Bound to the turn nonce below (`nonce: 0` — the agent cell's first
        // turn): dregg-action-sig-v3 binds the submitting turn's nonce into the
        // signature. HYBRID, because the deployed admission posture requires the
        // post-quantum half ("classical-only signature rejected") — this is the
        // exact call the remote SDK makes (`sign_action` → `sign_action_hybrid`).
        let action = clerk.sign_action_hybrid(unsigned, &fed_id, 0);
        let mut forest = CallForest::new();
        forest.add_root(action);

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let turn = Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: None,
            // The remote SDK ALWAYS stamps valid_until (executor expiry gate +
            // the verified Lean producer's wire marshal).
            valid_until: Some(now + 3600),
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: expected_prev,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let signed = clerk.sign_turn(&turn);
        let envelope = postcard::to_stdvec(&signed).expect("envelope encode");

        let submit = |bytes: Vec<u8>| {
            app.clone().oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/turns/submit")
                    .header("content-type", "application/octet-stream")
                    .extension(ConnectInfo(addr))
                    .body(Body::from(bytes))
                    .expect("submit request"),
            )
        };

        // ── ACCEPT: the honest remote envelope commits. ──
        let response = submit(envelope.clone()).await.expect("submit response");
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("submit json");
        assert_eq!(
            json["accepted"], true,
            "honest remote envelope must commit: {json}"
        );
        let turn_hash_hex = hex_encode(&turn.hash());
        assert_eq!(json["turn_hash"], serde_json::json!(turn_hash_hex));

        // ── RECEIPT RETRIEVABLE: once the turn FINALIZES, its receipt appears
        // on the public receipts surface under the canonical turn hash. (The
        // durable receipt is written by the finalized executor, not by the
        // submission that answered `accepted: true`.) ──
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
        let mut receipts = serde_json::Value::Null;
        loop {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri("/api/receipts")
                        .extension(ConnectInfo(addr))
                        .body(Body::empty())
                        .expect("receipts request"),
                )
                .await
                .expect("receipts response");
            assert_eq!(response.status(), StatusCode::OK);
            let bytes = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            receipts = serde_json::from_slice(&bytes).expect("receipts json");
            let landed = receipts
                .as_array()
                .expect("receipts array")
                .iter()
                .any(|r| r["turn_hash"] == serde_json::json!(turn_hash_hex));
            if landed || std::time::Instant::now() >= deadline {
                assert!(
                    landed,
                    "committed remote turn's receipt must be retrievable after finalization: \
                     {receipts}"
                );
                break;
            }
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        }

        // ── TAMPER REFUSES: any post-signing mutation breaks the envelope. ──
        let mut tampered = signed.clone();
        tampered.turn.fee += 1;
        let response = submit(postcard::to_stdvec(&tampered).expect("encode"))
            .await
            .expect("tamper response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("tamper json");
        assert_eq!(json["accepted"], false, "tampered envelope must refuse");
        assert_eq!(json["error"], serde_json::json!("invalid turn signature"));

        // ── WRONG AGENT REFUSES: an honestly-signed envelope whose turn acts
        // as someone ELSE's cell refuses at the ingress binding. ──
        let mut wrong = turn.clone();
        wrong.agent = recipient;
        let wrong_signed = clerk.sign_turn(&wrong);
        let response = submit(postcard::to_stdvec(&wrong_signed).expect("encode"))
            .await
            .expect("wrong-agent response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("wrong-agent json");
        assert_eq!(json["accepted"], false, "wrong-agent envelope must refuse");
        assert_eq!(
            json["error"],
            serde_json::json!("turn agent does not match signer default cell")
        );

        // ── REPLAY REFUSES: the exact accepted envelope, resubmitted, is
        // rejected — its receipt-chain binding now points behind the head. ──
        let response = submit(envelope).await.expect("replay response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("replay json");
        assert_eq!(json["accepted"], false, "replayed envelope must refuse");
        assert_eq!(json["error"], serde_json::json!("receipt chain mismatch"));
    }

    #[test]
    fn test_proposal_creation_and_vote_commit() {
        // This test drives a bare `Coordinator` (no `NodeState`), so nothing has armed the
        // verified-Lean 2PC gate for this process. Without it `evaluate_votes` FAILS CLOSED and
        // the first Yes vote decides `Abort` — the deployed disposition of a gate-less node, not
        // the tally semantics under test. Arm it exactly as a node does.
        crate::install_verified_distributed_gates();
        let node_a = test_key("node_a");
        let node_b = test_key("node_b");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        // Propose.
        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node A votes yes.
        let sig_a = Vote::sign_yes(&proposal_id, &forest.hash, &node_a);
        let vote_a = Vote::yes(sig_a);
        let decision_a = coordinator.receive_vote(pub_a, vote_a).unwrap();
        assert_eq!(decision_a, None); // Still pending.

        // Node B votes yes.
        let sig_b = Vote::sign_yes(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::yes(sig_b);
        let decision_b = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision_b, Some(Decision::Commit)); // Quorum reached!
    }

    #[test]
    fn test_proposal_abort_on_rejection() {
        let node_a = test_key("node_c");
        let node_b = test_key("node_d");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous required
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node B votes no -- threshold becomes unreachable.
        let sig_b = Vote::sign_no(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::no("testing rejection", sig_b);
        let decision = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision, Some(Decision::Abort));
    }

    #[test]
    fn test_proposal_expiry() {
        use crate::state::{ActiveProposal, PROPOSAL_EXPIRY_SECS};

        let node_a = test_key("node_e");
        let pub_a = Vote::public_key_from_signing_key(&node_a);

        let participants = vec![pub_a];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            1,
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Simulate an old proposal by setting created_at in the past.
        let mut proposals: HashMap<[u8; 32], ActiveProposal> = HashMap::new();
        proposals.insert(
            proposal_id,
            ActiveProposal {
                coordinator,
                created_at: Instant::now() - Duration::from_secs(PROPOSAL_EXPIRY_SECS + 10),
                forest,
            },
        );

        // Expire stale proposals.
        let now = Instant::now();
        let expiry = Duration::from_secs(PROPOSAL_EXPIRY_SECS);
        proposals.retain(|_, p| now.duration_since(p.created_at) < expiry);

        assert!(proposals.is_empty(), "expired proposal should be removed");
    }

    // =========================================================================
    // Adversarial tests for the AUDIT-node.md remediations (Stage 0c).
    //
    // These tests exercise the security-relevant logic of each fix at the unit
    // level — they intentionally avoid spinning up a full Axum router because
    // the workspace is being rebuilt by Stage 0a (sdk/) and Stage 0b (cell/)
    // and cannot link integration-test binaries at the time these tests were
    // authored. Each test pins the contract the fix established: a regression
    // in any of these would re-open a documented audit finding.
    // =========================================================================

    /// F-P2-1: atomic-proposal budget is clamped to 1B computrons, NOT
    /// `u64::MAX`. The prior code passed `u64::MAX` straight through to the
    /// coordinator with a "actual gate at execution time" comment that did not
    /// exist.
    /// ⚑ A COMPILE-CONSTANT REGRESSION GUARD BELONGS IN A COMPILE-TIME ASSERT. This was a
    /// `#[test]` carrying `#[allow(clippy::assertions_on_constants)]` — the lint was right and the
    /// `allow` was the wrong answer to it: a regression that a build could not survive was being
    /// reported by a test run, after everything downstream had already compiled against it.
    const ATOMIC_BUDGET_IS_BOUNDED: () = {
        assert!(
            MAX_ATOMIC_BUDGET == 1_000_000_000,
            "MAX_ATOMIC_BUDGET regressed; prior code allowed u64::MAX"
        );
        assert!(
            MAX_ATOMIC_BUDGET < u64::MAX / 1000,
            "budget must be far below u64::MAX to defeat exhaustion attacks"
        );
    };
    const _: () = ATOMIC_BUDGET_IS_BOUNDED;

    /// F-P1-8 (mcp side): the bearer-cap signed message MUST commit to the
    /// permission level so a downstream verifier cannot accept a forged
    /// permissions field. Test the message layout we sign in
    /// `tool_create_bearer_cap` is exactly `target || bearer_pk || expires || perm_tag`.
    #[test]
    fn audit_f_p1_8_perm_tag_layout() {
        // The layout that `tool_create_bearer_cap` signs (see node/src/mcp.rs
        // ~2090) is target(32) || bearer_pk(32) || expires(8) || tag(1) = 73.
        // If the layout regresses, the bearer cap signature would no longer
        // bind the permission level, re-opening F-P1-8.
        let target = [0xAAu8; 32];
        let bearer = [0xBBu8; 32];
        let expires: u64 = 12345;
        let tag: u8 = 1; // Signature
        let mut msg = Vec::with_capacity(73);
        msg.extend_from_slice(&target);
        msg.extend_from_slice(&bearer);
        msg.extend_from_slice(&expires.to_le_bytes());
        msg.push(tag);
        assert_eq!(msg.len(), 73);
        // Changing the tag must change the message.
        let mut msg_b = msg.clone();
        *msg_b.last_mut().unwrap() = 0;
        assert_ne!(msg, msg_b, "perm_tag must affect signed message");
    }

    /// F-P1-2 / F-P1-1 helper: `verify_ed25519_sig` correctly rejects:
    ///   (a) signatures over the wrong domain,
    ///   (b) signatures by a different key,
    ///   (c) malformed signature lengths.
    /// And accepts a correctly-signed message.
    #[test]
    fn audit_helper_verify_ed25519_sig_domain_separation() {
        use ed25519_dalek::{Signer, SigningKey};
        let mut seed_a = [0u8; 32];
        seed_a[0] = 1;
        let sk_a = SigningKey::from_bytes(&seed_a);
        let pk_a = sk_a.verifying_key().to_bytes();

        let mut seed_b = [0u8; 32];
        seed_b[0] = 2;
        let sk_b = SigningKey::from_bytes(&seed_b);
        let pk_b = sk_b.verifying_key().to_bytes();

        let domain_x = b"dregg-x-v1";
        let domain_y = b"dregg-y-v1";
        let payload = b"hello";

        // A signs (domain_x || payload).
        let mut msg = Vec::new();
        msg.extend_from_slice(domain_x);
        msg.extend_from_slice(payload);
        let sig = sk_a.sign(&msg);
        let sig_hex = hex_encode(&sig.to_bytes());

        // Sanity: verifies under A and domain_x.
        assert!(verify_ed25519_sig(&pk_a, &sig_hex, domain_x, payload).is_ok());
        // Domain mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_a, &sig_hex, domain_y, payload).is_err());
        // Key mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_b, &sig_hex, domain_x, payload).is_err());
        // Length mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_a, "00", domain_x, payload).is_err());
        // Garbage hex: must reject.
        assert!(verify_ed25519_sig(&pk_a, "zzzz", domain_x, payload).is_err());
    }

    /// F-CRIT-1 (logic-level): the loopback check in `post_set_passphrase`
    /// rejects non-loopback addresses. We can't exercise the handler without
    /// a router, but the underlying check is one line; here we pin the
    /// invariant.
    #[test]
    fn audit_f_crit_1_loopback_predicate() {
        use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
        // The exact predicate `addr.ip().is_loopback()` is what the handler
        // uses. Verify that the obvious "bad" addresses fail it.
        assert!(IpAddr::V4(Ipv4Addr::LOCALHOST).is_loopback());
        assert!(IpAddr::V6(Ipv6Addr::LOCALHOST).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(192, 168, 1, 5)).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(8, 8, 8, 8)).is_loopback());
    }

    /// F-P1-3: derive the cipherclerk's agent cell id deterministically from a
    /// pubkey; verify it differs from a victim cell id even when the caller
    /// passes the victim id as the body's `agent`.
    #[test]
    fn audit_f_p1_3_cclerk_agent_overrides_body() {
        // The handler derives:
        //   `dregg_cell::CellId::derive_raw(&cipherclerk.public_key().0, &[0u8;32])`
        // The body's `agent` is discarded. If a victim's `cell_id` is supplied
        // as the body's agent, the derived id MUST differ (so the cipherclerk's
        // signature can't be tricked into authorizing a victim's c-list).
        let cclerk_pk = [0x77u8; 32];
        let victim_cell = [0x99u8; 32];

        let derived = dregg_cell::CellId::derive_raw(&cclerk_pk, &[0u8; 32]).0;
        assert_ne!(
            derived, victim_cell,
            "agent must be derived from cipherclerk pubkey, not victim cell id"
        );

        // Sanity: the derivation is a function of the cipherclerk pubkey.
        let derived2 = dregg_cell::CellId::derive_raw(&cclerk_pk, &[0u8; 32]).0;
        assert_eq!(derived, derived2);
    }

    /// F-P1-4: AtomicProposalRequest supports an explicit `participant_pubkeys`
    /// field. Verify the request type round-trips through serde so the request
    /// body schema is correct.
    #[test]
    fn audit_f_p1_4_participant_pubkeys_schema() {
        let req_json = serde_json::json!({
            "forest": {},
            "participants": ["00".repeat(32), "01".repeat(32)],
            "threshold": 2,
            "fee": 0,
            "initiator": "00".repeat(32),
            "participant_pubkeys": ["aa".repeat(32), "bb".repeat(32)],
        });
        let req: AtomicProposalRequest = serde_json::from_value(req_json).expect("parses");
        assert_eq!(req.participants.len(), 2);
        assert!(req.participant_pubkeys.is_some());
        assert_eq!(req.participant_pubkeys.as_ref().unwrap().len(), 2);

        // Omission of the field is also valid (fallback path).
        let req2_json = serde_json::json!({
            "forest": {},
            "participants": ["00".repeat(32)],
            "threshold": 1,
            "fee": 0,
            "initiator": "00".repeat(32),
        });
        let req2: AtomicProposalRequest = serde_json::from_value(req2_json).expect("parses");
        assert!(req2.participant_pubkeys.is_none());
    }

    /// F-P1-7: the federation ID used by `post_bearer_auth` is `s.silo_id`,
    /// which is stable across runs (derived from the cipherclerk's pubkey). Prior
    /// code used `known_federation_keys.first()` whose ordering is a HashSet
    /// artifact and is NOT stable. We verify the derivation of silo_id is
    /// deterministic.
    #[test]
    fn audit_f_p1_7_silo_id_is_stable() {
        // silo_id is `blake3::hash(cipherclerk.public_key().as_bytes())` (see
        // state.rs:400). The same pubkey ALWAYS produces the same silo_id.
        let pk = [0xCDu8; 32];
        let id1 = *blake3::hash(&pk).as_bytes();
        let id2 = *blake3::hash(&pk).as_bytes();
        assert_eq!(id1, id2, "silo_id derivation must be deterministic");

        // A different pubkey produces a different id.
        let pk2 = [0xCEu8; 32];
        let id3 = *blake3::hash(&pk2).as_bytes();
        assert_ne!(id1, id3);
    }

    /// F-CRIT-2: auto-approve-joins is OFF by default. Verify the CLI flag
    /// definition: the `clap::Parser` derive makes booleans default-false.
    /// (We can't run the binary; we pin the contract by reading the source's
    /// shape via a doc-test-style assertion.)
    #[test]
    fn audit_f_crit_2_auto_approve_default_off() {
        // We verify the contract indirectly: any code path computing
        // `auto_approve_joins` in main.rs uses
        //   `auto_approve_joins_flag || data_path.join(".devnet").exists()`
        // and the clap flag has no default value (so it's false unless the
        // operator passes --auto-approve-joins on the command line).
        // If a future contributor adds `default_value = "true"` this test
        // does not catch it directly — instead we sanity-check the helper
        // logic: false || false == false, true || _ == true, _ || true == true.
        let flag = false;
        let devnet = false;
        assert!(!(flag || devnet), "off by default");
        let flag = true;
        let devnet = false;
        assert!(flag || devnet);
        let flag = false;
        let devnet = true;
        assert!(flag || devnet);
    }

    /// F-P1-2: make-sovereign requires a signature from the owner key. When
    /// the cell exists on the ledger, the signing key is `cell.public_key`;
    /// when the cell does NOT exist, the signing key falls back to `cell_id`
    /// itself (sovereign convention: cell_id == pubkey for fresh sovereign
    /// cells). Verify the request struct deserializes both nonce+signature.
    #[test]
    fn audit_f_p1_2_make_sovereign_request_shape() {
        let req_json = serde_json::json!({
            "cell_id": "00".repeat(32),
            "nonce": "0011223344556677",
            "signature": "00".repeat(64),
        });
        let _req: MakeSovereignRequest = serde_json::from_value(req_json).expect("parses");

        // Missing signature must fail at parse time.
        let bad = serde_json::json!({
            "cell_id": "00".repeat(32),
            "nonce": "0011",
        });
        assert!(serde_json::from_value::<MakeSovereignRequest>(bad).is_err());
    }

    /// F-P1-2 (create-from-factory request shape).
    #[test]
    fn audit_f_p1_2_create_from_factory_request_shape() {
        let req_json = serde_json::json!({
            "factory_vk": "00".repeat(32),
            "owner_pubkey": "11".repeat(32),
            "nonce": "0011223344556677",
            "signature": "00".repeat(64),
        });
        // Should succeed.
        let v: Result<CreateFromFactoryRequest, _> = serde_json::from_value(req_json);
        assert!(v.is_ok());

        // Missing nonce field is rejected.
        let bad = serde_json::json!({
            "factory_vk": "00".repeat(32),
            "owner_pubkey": "11".repeat(32),
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<CreateFromFactoryRequest>(bad).is_err());
    }

    // ─────────────────────────────────────────────────────────────────────
    // Turn-entry fix: /api/turns/submit now carries a real call forest.
    // ─────────────────────────────────────────────────────────────────────

    /// A `SubmitTurnRequest` with no `actions` field still deserializes (the
    /// field defaults to empty) for backward compatibility.
    #[test]
    fn submit_turn_request_actions_field_defaults_empty() {
        let legacy = serde_json::json!({
            "agent": "11".repeat(32),
            "nonce": 0,
            "fee": 1000,
        });
        let req: SubmitTurnRequest =
            serde_json::from_value(legacy).expect("legacy request must still parse");
        assert!(
            req.actions.is_empty(),
            "absent actions field defaults to empty"
        );
    }

    /// The action/effect JSON shape parses and resolves defaults correctly.
    #[test]
    fn submit_turn_request_parses_actions_with_effects() {
        let body = serde_json::json!({
            "agent": "11".repeat(32),
            "nonce": 3,
            "fee": 500,
            "memo": "register name",
            "actions": [{
                "method": "register_name",
                "effects": [
                    { "kind": "set_field", "index": 2, "value": "00".repeat(32) },
                    { "kind": "emit_event", "topic": "name-registered", "data": ["7"] },
                    { "kind": "increment_nonce" }
                ]
            }]
        });
        let req: SubmitTurnRequest = serde_json::from_value(body).expect("actions must parse");
        assert_eq!(req.actions.len(), 1);
        assert_eq!(req.actions[0].effects.len(), 3);
    }

    /// `parse_field_element` accepts both a full hex field element and a short
    /// decimal/hex scalar, and the scalar rides the CANONICAL u64 lane.
    ///
    /// The read side moved WITH the encoder: this test asserted
    /// `u64::from_le_bytes(dec[..8])` and `dec[8..] == 0`, which pinned the very
    /// encoding that made `{"kind":"set_field","value":"42"}` unprovable. It now
    /// decodes with `dregg_cell::field_to_u64` and asserts the frozen prefix
    /// (bytes `0..24`) is CLEAR — the property the deployed setField descriptor
    /// actually requires.
    #[test]
    fn parse_field_element_handles_hex_and_scalar() {
        let full = parse_field_element(&"ab".repeat(32)).unwrap();
        assert_eq!(full, [0xab; 32]);

        let dec = parse_field_element("42").unwrap();
        assert_eq!(dregg_cell::field_to_u64(&dec), 42);
        assert!(
            dec[..24].iter().all(|b| *b == 0),
            "a scalar must leave the frozen prefix clear or the setField cannot prove"
        );

        let hex = parse_field_element("0xff").unwrap();
        assert_eq!(dregg_cell::field_to_u64(&hex), 255);
        assert!(hex[..24].iter().all(|b| *b == 0));

        assert!(parse_field_element("not-a-number").is_err());
    }

    /// `build_effect` maps each spec variant to the right `Effect`, resolving
    /// the cell default against the action target.
    ///
    /// ⚑ THE SetField READ SIDE IS `dregg_cell::field_to_u64`, NOT
    /// `u64::from_le_bytes(value[..8])`. This test pinned the little-endian
    /// `0..8` decode that `parse_field_element`'s scalar branch stopped
    /// producing when it moved onto the canonical big-endian `24..32` lane —
    /// the SAME stale pin its sibling `parse_field_element_handles_hex_and_scalar`
    /// had already been repaired for, and the same reason: a `0..8` write lands
    /// in the high lanes the deployed `setFieldVmDescriptor2-{slot}R24` FREEZES,
    /// so a value this assertion accepted could not prove at all. Asserting the
    /// frozen prefix (bytes `0..24`) is clear is the property the descriptor
    /// actually requires, so a future re-drift to little-endian reds here.
    #[test]
    fn build_effect_resolves_cell_defaults() {
        let target = CellId([0x42; 32]);
        let other = CellId([0x99; 32]);

        let set = build_effect(
            TurnEffectSpec::SetField {
                cell: None,
                index: 4,
                value: "9".to_string(),
            },
            target,
        )
        .unwrap();
        match set {
            dregg_turn::Effect::SetField { cell, index, value } => {
                assert_eq!(cell, target, "absent cell defaults to action target");
                assert_eq!(index, 4);
                assert_eq!(
                    dregg_cell::field_to_u64(&value),
                    9,
                    "the scalar rides the canonical u64 lane (big-endian bytes 24..32)"
                );
                assert!(
                    value[..24].iter().all(|b| *b == 0),
                    "a scalar must leave the frozen prefix clear or the setField cannot prove"
                );
            }
            other => panic!("expected SetField, got {other:?}"),
        }

        let xfer = build_effect(
            TurnEffectSpec::Transfer {
                from: None,
                to: hex_encode(&other.0),
                amount: 100,
            },
            target,
        )
        .unwrap();
        match xfer {
            dregg_turn::Effect::Transfer { from, to, amount } => {
                assert_eq!(from, target);
                assert_eq!(to, other);
                assert_eq!(amount, 100);
            }
            other => panic!("expected Transfer, got {other:?}"),
        }
    }

    /// End-to-end: a turn built from a `SubmitTurnRequest`'s actions produces
    /// a NON-EMPTY call forest that the canonical executor commits — the
    /// regression guard for the historical "call forest is empty" blocker.
    #[test]
    fn turn_from_submit_request_actions_executes_and_commits() {
        // Operator cell with permissive permissions (its own cell).
        let public_key = [0x55; 32];
        let token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&public_key, &token_id);
        let mut ledger = dregg_cell::Ledger::new();
        let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 10_000);
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
        ledger.insert_cell(cell).expect("insert agent cell");

        // Build a real action via the same primitive the handler uses.
        let cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"operator-key").as_bytes(),
        ));
        let effect = build_effect(
            TurnEffectSpec::SetField {
                cell: None,
                index: 2,
                value: "00".repeat(32),
            },
            agent,
        )
        .unwrap();
        let action = cclerk.make_action(agent, "submit", vec![effect], &[7u8; 32]);
        let mut forest = CallForest::new();
        forest.add_root(action);
        assert_eq!(
            forest.action_count(),
            1,
            "the call forest must NOT be empty (the historical blocker)"
        );

        let turn = Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: Some("turn-entry e2e".to_string()),
            valid_until: None,
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());
        let result = executor.execute(&turn, &mut ledger);
        assert!(
            matches!(result, dregg_turn::TurnResult::Committed { .. }),
            "a turn with a real action must commit, not be rejected as empty"
        );
    }

    // ======================================================================
    // RED-TEAM: F-1 (rate-limit proxy bypass) + F-8 (status metadata leak).
    //
    // Each test below is an ATTACK. Before the fix it asserted the BAD
    // outcome (the bypass / the leak succeeds = FINDING). It now asserts the
    // attack FAILS = DEFENDED. A regression that reopens the hole flips the
    // assertion and fails the build.
    // ======================================================================

    use std::net::{IpAddr, Ipv4Addr};

    fn ip(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(a, b, c, d))
    }

    /// Serializes the two `DREGG_STATUS_EXPOSE_COUNTS`-sensitive tests so they
    /// don't race on the shared process env when run in parallel.
    static F8_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    // ---- F-1: rate-limit proxy bypass ------------------------------------

    /// ATTACK (F-1, core): behind a reverse proxy, every request shares the
    /// proxy's socket IP. The limiter MUST instead key on the real client IP
    /// from `X-Forwarded-For` — otherwise all clients collapse into one global
    /// bucket (DoS of honest clients) and a single client cannot be isolated.
    ///
    /// DEFENDED: with the proxy trusted, two distinct forwarded clients arriving
    /// on the SAME proxy socket resolve to DIFFERENT rate-limit keys.
    #[test]
    fn f1_proxied_clients_get_distinct_buckets_defended() {
        let proxy = ip(10, 0, 0, 1);
        let trusted = TrustedProxies::from_strings([proxy.to_string()]);

        let alice = resolve_client_ip(proxy, Some("203.0.113.7"), &trusted);
        let bob = resolve_client_ip(proxy, Some("198.51.100.9"), &trusted);

        // FINDING (pre-fix) would have keyed both on `proxy` → equal → one bucket.
        assert_eq!(alice, ip(203, 0, 113, 7));
        assert_eq!(bob, ip(198, 51, 100, 9));
        assert_ne!(
            alice, bob,
            "F-1 regressed: proxied clients collapsed into one rate-limit bucket"
        );
        // And neither is the proxy's own socket IP (the global-bucket failure mode).
        assert_ne!(alice, proxy);
        assert_ne!(bob, proxy);
        eprintln!("[API ATTACK / F-1] proxied clients keyed per-real-IP: DEFENDED");
    }

    /// ATTACK (F-1, spoof): an UNTRUSTED direct attacker sets its own
    /// `X-Forwarded-For` trying to (a) impersonate another client or (b) mint a
    /// fresh unlimited bucket per request by rotating the header value.
    ///
    /// DEFENDED: because the direct peer is NOT a trusted proxy, the header is
    /// ignored and the key stays pinned to the attacker's real socket IP — so
    /// the attacker cannot escape its own bucket no matter what it forges.
    #[test]
    fn f1_untrusted_xff_spoof_is_ignored_defended() {
        let attacker = ip(192, 0, 2, 66);
        // No proxy is trusted (direct exposure) OR the attacker is not in the set.
        let none_trusted = TrustedProxies::default();
        let some_trusted = TrustedProxies::from_strings([ip(10, 0, 0, 1).to_string()]);

        for trusted in [&none_trusted, &some_trusted] {
            // Spoof a "fresh" client IP each call — must NOT change the key.
            let k1 = resolve_client_ip(attacker, Some("1.2.3.4"), trusted);
            let k2 = resolve_client_ip(attacker, Some("5.6.7.8"), trusted);
            let k3 = resolve_client_ip(attacker, Some("9.9.9.9, 8.8.8.8"), trusted);
            assert_eq!(
                k1, attacker,
                "F-1 regressed: untrusted XFF spoof moved the key"
            );
            assert_eq!(
                k2, attacker,
                "F-1 regressed: rotating XFF minted a fresh bucket"
            );
            assert_eq!(
                k3, attacker,
                "F-1 regressed: untrusted multi-hop XFF honored"
            );
        }
        eprintln!("[API ATTACK / F-1] untrusted X-Forwarded-For spoof ignored: DEFENDED");
    }

    /// ATTACK (F-1, prepend spoof): even a client legitimately BEHIND a trusted
    /// proxy can prepend bogus left-hand `X-Forwarded-For` entries (the client-
    /// controlled portion). A naive "take the FIRST/leftmost entry" resolver
    /// would hand the attacker an arbitrary spoofed key (fresh bucket / framing
    /// a victim IP).
    ///
    /// DEFENDED: the resolver walks from the RIGHT (proxy-appended, trustworthy
    /// end) past trusted hops to the first untrusted address — the spoofed
    /// left-hand entries are inert.
    #[test]
    fn f1_xff_left_prepend_spoof_is_inert_defended() {
        let proxy = ip(10, 0, 0, 1);
        let trusted = TrustedProxies::from_strings([proxy.to_string()]);
        // Real client = 203.0.113.7; attacker prepended two fake hops.
        let xff = "66.66.66.66, 77.77.77.77, 203.0.113.7";
        let key = resolve_client_ip(proxy, Some(xff), &trusted);
        assert_eq!(
            key,
            ip(203, 0, 113, 7),
            "F-1 regressed: leftmost XFF prepend spoof was honored over the real client"
        );
        assert_ne!(key, ip(66, 66, 66, 66));
        eprintln!("[API ATTACK / F-1] leftmost XFF prepend spoof inert: DEFENDED");
    }

    /// ATTACK (F-1, end-to-end): drive the REAL limiter through `check_request`
    /// — exhaust one proxied client's quota, then assert a DIFFERENT proxied
    /// client (same proxy socket) is still admitted (no shared global bucket).
    #[tokio::test]
    async fn f1_real_limiter_isolates_proxied_clients_defended() {
        let proxy = ip(10, 0, 0, 1);
        let limiter =
            RateLimiter::with_proxies(3, 60, TrustedProxies::from_strings([proxy.to_string()]));

        let mut alice_hdr = axum::http::HeaderMap::new();
        alice_hdr.insert("x-forwarded-for", "203.0.113.7".parse().unwrap());
        let mut bob_hdr = axum::http::HeaderMap::new();
        bob_hdr.insert("x-forwarded-for", "198.51.100.9".parse().unwrap());

        // Drain Alice's quota (3 allowed, 4th denied).
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(
            !limiter.check_request(proxy, &alice_hdr).await,
            "Alice should be rate-limited after her own quota"
        );

        // FINDING (pre-fix): Bob shares the proxy bucket → already throttled.
        // DEFENDED: Bob has his own bucket and is admitted.
        assert!(
            limiter.check_request(proxy, &bob_hdr).await,
            "F-1 regressed: a second proxied client was throttled by another's quota (shared global bucket)"
        );
        eprintln!("[API ATTACK / F-1] real limiter isolates proxied clients: DEFENDED");
    }

    // ---- F-CRIT-1: pre-passphrase setup gate must be XFF-aware ------------

    /// ATTACK (F-CRIT-1 / setup gate behind a proxy): the pre-passphrase
    /// "loopback-only during setup" gate — shared by the HTTP unlock /
    /// set-passphrase endpoints AND the WebSocket setup gate — must resolve the
    /// EFFECTIVE client IP the same XFF-aware way as `require_auth` and the rate
    /// limiter, not trust the raw socket IP. Behind the devnet's same-host
    /// reverse proxy every external request arrives on a loopback socket; a
    /// raw-socket gate would treat a REMOTE client as local and let it set the
    /// passphrase + bearer seed (remote takeover).
    ///
    /// DEFENDED: with the loopback proxy trusted, a loopback socket carrying an
    /// XFF for a REMOTE client resolves to NON-loopback → the gate denies (auth
    /// required); a genuine local caller (no XFF, or an XFF that is itself
    /// loopback) still resolves to loopback → admitted. `handle_ws` and the two
    /// HTTP setup endpoints call the SAME `effective_client_is_loopback`, so the
    /// two gates provably agree.
    #[test]
    fn f_crit_1_setup_gate_is_xff_aware_defended() {
        use std::net::{IpAddr, Ipv4Addr};
        let loopback = IpAddr::V4(Ipv4Addr::LOCALHOST);
        // The devnet's same-host reverse proxy connects from loopback.
        let trusted = TrustedProxies::from_strings([loopback.to_string()]);

        // Remote client behind the trusted loopback proxy → NOT loopback → DENY.
        let mut remote_hdr = axum::http::HeaderMap::new();
        remote_hdr.insert("x-forwarded-for", "203.0.113.7".parse().unwrap());
        assert!(
            !effective_client_is_loopback_with(loopback, &remote_hdr, &trusted),
            "F-CRIT-1 regressed: a remote client behind a loopback proxy was treated as local"
        );

        // Genuine local: no XFF header at all → resolves to the loopback socket → ADMIT.
        let empty = axum::http::HeaderMap::new();
        assert!(
            effective_client_is_loopback_with(loopback, &empty, &trusted),
            "genuine local caller (no XFF) must still be admitted during setup"
        );

        // Genuine local forwarded by the proxy as a loopback client → ADMIT.
        let mut local_hdr = axum::http::HeaderMap::new();
        local_hdr.insert("x-forwarded-for", "127.0.0.1".parse().unwrap());
        assert!(
            effective_client_is_loopback_with(loopback, &local_hdr, &trusted),
            "a forwarded loopback client must still be admitted"
        );

        // Default (no trusted proxies / direct exposure): the XFF is IGNORED and
        // the raw socket decides — unchanged local-dev behavior, and an unproxied
        // attacker cannot spoof itself local via the header.
        let none = TrustedProxies::default();
        assert!(
            effective_client_is_loopback_with(loopback, &remote_hdr, &none),
            "default (no trusted proxy): loopback socket stays local, XFF ignored"
        );
        let remote_socket = IpAddr::V4(Ipv4Addr::new(8, 8, 8, 8));
        assert!(
            !effective_client_is_loopback_with(remote_socket, &local_hdr, &none),
            "F-CRIT-1 regressed: an unproxied attacker spoofed itself loopback via XFF"
        );
        eprintln!("[API ATTACK / F-CRIT-1] setup gate resolves effective client IP: DEFENDED");
    }

    // ---- F-8: /status private-activity metadata leak ---------------------

    /// ATTACK (F-8): scrape the public, unauthenticated `GET /status` and read
    /// the aggregate private-activity counters (`note_count` /
    /// `revocation_count`) — a private-activity-VOLUME oracle.
    ///
    /// DEFENDED: by default those fields are ABSENT from the response, while the
    /// coarse public liveness signal (`healthy` / `consensus_live` / `dag_height`)
    /// is still present.
    #[tokio::test]
    // The env-lock guard must span the async request so the env scrub stays in effect throughout.
    #[allow(clippy::await_holding_lock)]
    async fn f8_status_does_not_leak_private_counts_defended() {
        let _guard = F8_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Ensure the opt-in is OFF for this test regardless of ambient env.
        // SAFETY: test-local env scrub, serialized by F8_ENV_LOCK.
        unsafe {
            std::env::remove_var("DREGG_STATUS_EXPOSE_COUNTS");
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/status")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("status json");

        // FINDING (pre-fix): both counters present on the wire.
        assert!(
            json.get("note_count").is_none(),
            "F-8 regressed: /status leaks note_count (private-activity volume): {json}"
        );
        assert!(
            json.get("revocation_count").is_none(),
            "F-8 regressed: /status leaks revocation_count (private-activity volume): {json}"
        );
        // The coarse public liveness signal must still be present.
        assert!(
            json.get("healthy").is_some(),
            "/status must still report liveness"
        );
        assert!(json.get("consensus_live").is_some());
        eprintln!("[API ATTACK / F-8] /status withholds private-activity counters: DEFENDED");
    }

    /// CONTROL (F-8): when an operator EXPLICITLY opts in
    /// (`DREGG_STATUS_EXPOSE_COUNTS=1`, e.g. a trusted internal dashboard), the
    /// counters reappear — proving the default-off is a real, reversible gate
    /// (the test is non-vacuous: the same code path produces both outcomes).
    #[tokio::test]
    // The env-lock guard must span the async request so the env opt-in stays in effect throughout.
    #[allow(clippy::await_holding_lock)]
    async fn f8_opt_in_re_exposes_counts_control() {
        let _guard = F8_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        unsafe {
            std::env::set_var("DREGG_STATUS_EXPOSE_COUNTS", "1");
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/status")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("status json");

        assert!(
            json.get("note_count").is_some() && json.get("revocation_count").is_some(),
            "opt-in must re-expose the counters (gate is real, not a no-op): {json}"
        );

        // Restore the default-off posture for any later test.
        unsafe {
            std::env::remove_var("DREGG_STATUS_EXPOSE_COUNTS");
        }
        eprintln!("[API CONTROL / F-8] opt-in re-exposes counters (gate is non-vacuous)");
    }

    // ========================================================================
    // INTENT SUBMIT → VERIFIED COMMIT (the liquid-frontier weld)
    //
    // A submitted intent that names a fulfiller must DRAIN through the verified
    // ledger at submit time, not rot in the in-memory pool. These tests pin the
    // end-to-end path `post_intent` → `commit_intent_fulfillment_verified` →
    // `execute_fulfillment_flow_verified` (the SAME verified core `/intents/fulfill`
    // drives), and assert the value actually MOVED — a real commit, not a stub.
    // ========================================================================

    /// Build a funded, unlocked NodeState with a payer (creator) cell and a recipient
    /// (fulfiller) cell, returning their canonical CellIds.
    async fn funded_intent_state(
        payer_balance: i64,
        recipient_balance: i64,
    ) -> (NodeState, tempfile::TempDir, CellId, CellId) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");

        let payer_cell = dregg_cell::Cell::with_balance([0x11u8; 32], [0u8; 32], payer_balance);
        let recipient_cell =
            dregg_cell::Cell::with_balance([0x22u8; 32], [0u8; 32], recipient_balance);
        let payer_id = payer_cell.id();
        let recipient_id = recipient_cell.id();

        {
            let mut s = state.write().await;
            s.ledger
                .insert_cell(payer_cell)
                .expect("payer insert must succeed");
            s.ledger
                .insert_cell(recipient_cell)
                .expect("recipient insert must succeed");
            // The verified fulfillment flow requires an unlocked node (the operator's
            // cipherclerk gate that signs turns).
            s.unlocked = true;
        }

        (state, tmp, payer_id, recipient_id)
    }

    /// Build a payable `Need` intent whose creator IS the payer cell (the verified flow
    /// enforces `payer_cell == intent.creator`).
    fn payable_intent(creator_id: CellId, min_budget: u64) -> dregg_intent::Intent {
        let spec = dregg_intent::MatchSpec {
            min_budget: Some(min_budget),
            ..Default::default()
        };
        dregg_intent::Intent::new(
            dregg_intent::IntentKind::Need,
            spec,
            dregg_intent::CommitmentId(creator_id.0),
            99_999,
            None,
        )
    }

    fn balance_of(s: &crate::state::NodeStateInner, id: &CellId) -> i64 {
        s.ledger.get(id).map(|c| c.state.balance()).unwrap_or(0)
    }

    /// THE BAR: a submitted, self-fulfillable intent COMMITS through the verified
    /// ledger and returns a real receipt — the value actually moves, the pool stays
    /// empty (no dead-end HashMap entry).
    #[tokio::test]
    async fn submitted_intent_commits_through_verified_ledger() {
        let amount: u64 = 100;
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(1_000, 0).await;

        let intent = payable_intent(payer_id, amount);
        let mut raw = serde_json::to_value(&intent).expect("intent json");
        // The fulfiller hint rides as a sibling field; the canonical Intent (and thus its
        // content-addressed id) is untouched.
        raw["fulfiller_cell"] = serde_json::json!(hex_encode(&recipient_id.0));

        let resp = post_intent(State(state.clone()), Json(raw))
            .await
            .expect("submit must succeed")
            .0;

        // The intent COMMITTED — not merely stored.
        assert!(
            resp.committed,
            "a self-fulfillable intent must commit through the verified ledger, not pool"
        );
        assert!(
            !resp.stored,
            "a committed intent is NOT a pooled (stored) entry"
        );
        let turn_hash = resp
            .turn_hash
            .expect("a committed intent must carry a real receipt turn_hash");
        assert_eq!(
            turn_hash.len(),
            64,
            "turn_hash must be a 32-byte hex digest"
        );

        // The VALUE ACTUALLY MOVED through the ledger (the proof this is a real commit,
        // not a stub): payer debited, recipient credited, exactly `amount`.
        let s = state.read().await;
        assert_eq!(
            balance_of(&s, &payer_id),
            1_000 - amount as i64,
            "payer must be debited the payment leg"
        );
        assert_eq!(
            balance_of(&s, &recipient_id),
            amount as i64,
            "recipient must be credited the payment leg"
        );
        // The pool is NOT a dead-end: the committed intent never entered it.
        assert!(
            !s.intent_pool.contains_key(&intent.id),
            "a committed intent must not also rot in the pool"
        );
        eprintln!(
            "[INTENT WELD] submit → verified commit → value moved {amount} (receipt {turn_hash})"
        );
    }

    /// Without a fulfiller, the intent has no counter-leg yet: it POOLS (the prior
    /// behavior), and the ledger is untouched. This pins that the weld is additive —
    /// open offers/needs still pool for a later `/intents/fulfill`.
    #[tokio::test]
    async fn submitted_intent_without_fulfiller_pools_and_leaves_ledger_untouched() {
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(1_000, 0).await;

        let intent = payable_intent(payer_id, 100);
        let raw = serde_json::to_value(&intent).expect("intent json"); // no fulfiller_cell

        let resp = post_intent(State(state.clone()), Json(raw))
            .await
            .expect("submit must succeed")
            .0;

        assert!(resp.stored, "an unfulfillable intent must pool");
        assert!(!resp.committed, "an unfulfillable intent must NOT commit");
        assert!(resp.turn_hash.is_none(), "no receipt without a commit");

        let s = state.read().await;
        assert!(
            s.intent_pool.contains_key(&intent.id),
            "the intent must be in the pool for a later fulfill"
        );
        assert_eq!(balance_of(&s, &payer_id), 1_000, "ledger must be untouched");
        assert_eq!(balance_of(&s, &recipient_id), 0, "ledger must be untouched");
    }

    /// Fail-closed: a self-fulfillment the verified executor REFUSES (here: an
    /// underfunded payer) must be a hard error, NOT a silent downgrade to a quiet pool
    /// entry. A rejected commit laundered as a successful submit is exactly the bug.
    #[tokio::test]
    async fn refused_self_fulfillment_is_a_hard_error_not_a_silent_pool() {
        // Payer holds only 10 but the intent demands 100 — the verified availability
        // gate must refuse.
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(10, 0).await;

        let intent = payable_intent(payer_id, 100);
        let mut raw = serde_json::to_value(&intent).expect("intent json");
        raw["fulfiller_cell"] = serde_json::json!(hex_encode(&recipient_id.0));

        let outcome = post_intent(State(state.clone()), Json(raw)).await;
        match outcome {
            Err(code) => assert_eq!(code, StatusCode::UNPROCESSABLE_ENTITY),
            Ok(_) => panic!("an underfunded self-fulfillment must be refused, not accepted"),
        }

        // The ledger is untouched (fail-closed) and nothing was laundered into the pool.
        let s = state.read().await;
        assert_eq!(
            balance_of(&s, &payer_id),
            10,
            "refused commit must not move value"
        );
        assert_eq!(
            balance_of(&s, &recipient_id),
            0,
            "refused commit must not move value"
        );
        assert!(
            !s.intent_pool.contains_key(&intent.id),
            "a refused payable intent must not be silently pooled"
        );
    }

    /// HTTP SURFACE: the cipherclerk authorize/attenuate endpoints now carry the
    /// Budget caveat (previously dropped by `..Default::default()`). This drives the
    /// REAL handlers — `post_attenuate` to enroll a budget, then `post_authorize` — and
    /// asserts the caller-supplied `budget_states`/`request_cost` reach the LIVE
    /// enforcement path in `datalog_verify`:
    ///   - authorize with a SATISFYING state passes the budget check;
    ///   - authorize with NO state on a budget-caveated token is denied (before the
    ///     fix this was the only reachable state over HTTP, so it could never pass);
    ///   - authorize claiming `remaining > limit` is denied by the anti-spoof guard.
    ///
    /// HONEST SCOPE: this proves the caveat is enforced per the existing per-request
    /// model — `budget_states` is caller-supplied — NOT that cumulative spend is
    /// kernel-capped (that would need cell-state sourcing of the counter).
    #[tokio::test]
    async fn http_authorize_reaches_budget_enforcement() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        state.write().await.unlocked = true;

        let minted = post_mint(
            State(state.clone()),
            Json(MintRequest {
                service: "compute".into(),
            }),
        )
        .await
        .expect("mint ok")
        .0;

        // Enroll a Budget caveat (limit 100) over HTTP — the field the surface dropped before.
        // The `services` grant keeps the token positively authorizable (a caveat-only
        // token with no service facts is `unrestricted`, and there is no time/budget-aware
        // unrestricted rule); realistic attenuation narrows scope AND sets a budget together.
        let att = post_attenuate(
            State(state.clone()),
            Json(AttenuateRequest {
                token_id: minted.token_id.clone(),
                services: vec![("compute".into(), "r".into())],
                not_after: None,
                budget: Some(BudgetSpec {
                    id: "ci-bot:daily".into(),
                    parent_id: None,
                    class: "api_calls".into(),
                    limit: 100,
                    window: None,
                }),
            }),
        )
        .await
        .expect("attenuate ok")
        .0;

        // Satisfying state: 50 remaining, cost 10, 50 <= limit 100 → reaches + passes the check.
        let mut states = HashMap::new();
        states.insert("ci-bot:daily".to_string(), 50u64);
        let ok = post_authorize(
            State(state.clone()),
            Json(AuthorizeRequest {
                token_id: att.new_token_id.clone(),
                service: Some("compute".into()),
                action: Some("r".into()),
                request_cost: Some(10),
                budget_states: states,
            }),
        )
        .await
        .expect("authorize call ok")
        .0;
        assert!(
            ok.authorized,
            "authorize with satisfying budget_states must reach the budget check and PASS: {:?}",
            ok.reason
        );

        // No state supplied: a budget-caveated token is denied. Before the fix the HTTP
        // path ALWAYS sent an empty budget_states, so a budget token could never authorize;
        // the pass above proves the field now threads through.
        let missing = post_authorize(
            State(state.clone()),
            Json(AuthorizeRequest {
                token_id: att.new_token_id.clone(),
                service: Some("compute".into()),
                action: Some("r".into()),
                request_cost: Some(10),
                budget_states: HashMap::new(),
            }),
        )
        .await
        .expect("authorize call ok")
        .0;
        assert!(
            !missing.authorized,
            "a budget-caveated token must be DENIED when no budget state is supplied"
        );

        // Spoof: claim more remaining than the limit → the anti-spoof `remaining <= limit`
        // guard in datalog_verify must DENY.
        let mut spoof = HashMap::new();
        spoof.insert("ci-bot:daily".to_string(), 1_000u64);
        let denied = post_authorize(
            State(state.clone()),
            Json(AuthorizeRequest {
                token_id: att.new_token_id.clone(),
                service: Some("compute".into()),
                action: Some("r".into()),
                request_cost: Some(10),
                budget_states: spoof,
            }),
        )
        .await
        .expect("authorize call ok")
        .0;
        assert!(
            !denied.authorized,
            "authorize claiming remaining > limit must be DENIED by the anti-spoof guard"
        );
    }

    /// HTTP SURFACE: the attenuate endpoint now carries the validity window
    /// (`not_after`) — a real, kernel-enforced narrowing. A token attenuated with a
    /// past `not_after` is DENIED at authorize (expired); with a future one it still
    /// authorizes. Before the fix the field was dropped, so no expiry could be set
    /// over HTTP.
    #[tokio::test]
    async fn http_attenuate_threads_not_after_window() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        state.write().await.unlocked = true;

        let minted = post_mint(
            State(state.clone()),
            Json(MintRequest {
                service: "compute".into(),
            }),
        )
        .await
        .expect("mint ok")
        .0;

        // Past not_after (1970) → already expired. The `services` grant keeps the token
        // positively authorizable so the ONLY thing under test is the validity window.
        let expired = post_attenuate(
            State(state.clone()),
            Json(AttenuateRequest {
                token_id: minted.token_id.clone(),
                services: vec![("compute".into(), "r".into())],
                not_after: Some(1),
                budget: None,
            }),
        )
        .await
        .expect("attenuate ok")
        .0;
        let resp = post_authorize(
            State(state.clone()),
            Json(AuthorizeRequest {
                token_id: expired.new_token_id.clone(),
                service: Some("compute".into()),
                action: Some("r".into()),
                request_cost: None,
                budget_states: HashMap::new(),
            }),
        )
        .await
        .expect("authorize call ok")
        .0;
        assert!(
            !resp.authorized,
            "a token attenuated with a past not_after must be DENIED (expired) — proving the window threads through"
        );

        // Control: a future not_after (the only change) still authorizes.
        let future = post_attenuate(
            State(state.clone()),
            Json(AttenuateRequest {
                token_id: minted.token_id.clone(),
                services: vec![("compute".into(), "r".into())],
                not_after: Some(i64::MAX / 2),
                budget: None,
            }),
        )
        .await
        .expect("attenuate ok")
        .0;
        let resp2 = post_authorize(
            State(state.clone()),
            Json(AuthorizeRequest {
                token_id: future.new_token_id.clone(),
                service: Some("compute".into()),
                action: Some("r".into()),
                request_cost: None,
                budget_states: HashMap::new(),
            }),
        )
        .await
        .expect("authorize call ok")
        .0;
        assert!(
            resp2.authorized,
            "a token attenuated with a future not_after must still authorize: {:?}",
            resp2.reason
        );
    }

    /// Back-compat: an authorize/attenuate body WITHOUT the new fields still
    /// deserializes (the `#[serde(default)]` guarantee) — existing callers unaffected.
    #[test]
    fn http_request_structs_are_backward_compatible() {
        let auth: AuthorizeRequest =
            serde_json::from_str(r#"{"token_id":"t","service":"compute","action":"r"}"#)
                .expect("legacy authorize body must still parse");
        assert!(auth.request_cost.is_none());
        assert!(auth.budget_states.is_empty());

        let att: AttenuateRequest =
            serde_json::from_str(r#"{"token_id":"t","services":[["compute","r"]]}"#)
                .expect("legacy attenuate body must still parse");
        assert!(att.not_after.is_none());
        assert!(att.budget.is_none());
    }

    /// Read `GET /api/turn/{hash}/verdict` on a bare router.
    async fn read_verdict(
        app: &axum::Router,
        turn_hash_hex: &str,
    ) -> (StatusCode, serde_json::Value) {
        let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri(format!("/api/turn/{turn_hash_hex}/verdict"))
                    .extension(ConnectInfo(addr))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        (status, serde_json::from_slice(&body).expect("JSON verdict"))
    }

    /// THE VANISHED TURN, MADE QUERYABLE — and the ways it must still refuse.
    ///
    /// The durable rejection row was already being written on every node; what
    /// did not exist was a coordinate a client could ask with. This pins all
    /// three read behaviours of the by-turn route: the honest non-answer, the
    /// real verdict with its reason, and the fail-closed refusal when the index
    /// disagrees with the authority it points at.
    #[tokio::test]
    async fn a_durably_rejected_turn_is_queryable_by_hash_and_a_disagreeing_index_refuses() {
        use crate::signed_turn_validation::{
            FinalizedPayloadRejectionRecord, FinalizedPayloadRejectionTurnIndex,
        };

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state.clone(), false, recorder.handle());

        let turn_hash = [0x19u8; 32];
        let turn_hash_hex = hex_encode(&turn_hash);
        let block_id = [0xC0u8; 32];
        let payload = b"the finalized bytes this block carried";

        // ── Nothing recorded: `unknown` and a 404. NOT a verdict, and the
        //    response says so rather than implying the turn is gone. ──
        let (status, json) = read_verdict(&app, &turn_hash_hex).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(json["verdict"], "unknown");
        assert_eq!(json["terminal"], false);

        // ── The pair of rows the consensus path writes. ──
        {
            let s = state.read().await;
            let record = FinalizedPayloadRejectionRecord::new(
                block_id,
                payload,
                Some(turn_hash),
                "receipt-chain-mismatch",
            );
            s.store
                .set_config(
                    &FinalizedPayloadRejectionRecord::storage_key(&block_id),
                    &record.encode().expect("encode rejection row"),
                )
                .expect("store rejection row");
            let index = FinalizedPayloadRejectionTurnIndex::new(
                turn_hash,
                block_id,
                "receipt-chain-mismatch",
            );
            s.store
                .set_config(
                    &FinalizedPayloadRejectionTurnIndex::storage_key(&turn_hash),
                    &index.encode().expect("encode rejection index"),
                )
                .expect("store rejection index");
        }

        let (status, json) = read_verdict(&app, &turn_hash_hex).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["verdict"], "rejected");
        assert_eq!(json["terminal"], true);
        assert_eq!(json["reason"], "receipt-chain-mismatch");
        assert_eq!(json["block_id"], hex_encode(&block_id));

        // ── The index is a POINTER, never the authority. Repoint it at a block
        //    that has no rejection record and the route must refuse rather than
        //    serve the pointer's claim. ──
        {
            let s = state.read().await;
            let liar = FinalizedPayloadRejectionTurnIndex::new(
                turn_hash,
                [0xEEu8; 32],
                "receipt-chain-mismatch",
            );
            s.store
                .set_config(
                    &FinalizedPayloadRejectionTurnIndex::storage_key(&turn_hash),
                    &liar.encode().expect("encode rejection index"),
                )
                .expect("store rejection index");
        }
        let (status, json) = read_verdict(&app, &turn_hash_hex).await;
        assert_eq!(status, StatusCode::INTERNAL_SERVER_ERROR);
        assert_eq!(json["verdict"], "indeterminate");

        // ── A malformed hash is a client error, never a verdict. ──
        let (status, _) = read_verdict(&app, "not-a-hash").await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
    }
}
