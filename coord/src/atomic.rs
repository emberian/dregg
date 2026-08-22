//! Layer 2: Atomic Multi-Party Turns.
//!
//! Multiple agents on different nodes contribute actions to ONE call forest.
//! The combined forest is only committed if ALL participants' preconditions are met.
//! Uses a simple 2-phase commit: Propose -> Vote -> Commit/Abort.
//! If any participant's preconditions fail, the entire forest is aborted.
//! The committed forest gets a threshold QC (everyone who participated signs).

use std::collections::HashMap;
use std::time::{Duration, Instant};

use dregg_cell::{CellId, Ledger, Preconditions};
use dregg_turn::{CallForest, ComputronCosts, Turn, TurnExecutor, TurnReceipt, TurnResult};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::error::CoordError;

/// Validity horizon (wall-clock seconds) for atomic-turn proposals built with this
/// default.
///
/// `Turn::valid_until` (`turn/src/turn.rs`) is compared against the executor's
/// wall-clock `current_timestamp`, entirely separate from `block_height`
/// (`turn/src/executor/mod.rs`). `None` skips the executor's expiration check
/// entirely (`turn/src/executor/execute.rs:426`) — a turn built that way never
/// expires, no matter how stale. Mirrors `default_valid_until` in `node/src/api.rs` /
/// `sdk/src/runtime.rs` / `intent/src/fulfillment.rs` (same rationale, same fix, same
/// 1-hour horizon); `dregg-coord` depends on none of those crates, hence its own copy.
///
/// `pub`, not `pub(crate)`: the one production call site that proposes an atomic
/// forest lives in `dregg-node` (`node/src/api.rs`), a different crate.
const ATOMIC_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

/// Wall-clock Unix seconds, `now`.
///
/// Shared by [`default_valid_until`] (stamps the deadline) and `commit`/`apply_commit`
/// (stamp the executor's clock the deadline is checked against — see the note on
/// `TurnExecutor::current_timestamp` at both call sites: without it, `valid_until`
/// alone is inert here).
fn wall_clock_now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

pub fn default_valid_until() -> Option<i64> {
    Some(wall_clock_now_secs() + ATOMIC_TURN_VALIDITY_HORIZON_SECS)
}

// ─── AtomicForest ──────────────────────────────────────────────────────────────

/// A multi-party call forest: actions contributed by multiple participants
/// that must all commit atomically or all abort.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicForest {
    /// Cell IDs of all participants (the nodes that must agree).
    pub participants: Vec<[u8; 32]>,
    /// The combined call forest from all parties.
    pub forest: CallForest,
    /// Per-participant preconditions that must hold for the commit.
    pub preconditions: Vec<(CellId, Preconditions)>,
    /// The initiating agent (who pays the fee and owns the turn).
    pub initiator: CellId,
    /// The fee for this atomic turn.
    pub fee: u64,
    /// Wall-clock deadline (Unix seconds) for the `Turn` this forest will become.
    ///
    /// Decided ONCE, here, at propose time — NOT re-derived independently by
    /// `Coordinator::commit()` and `Participant::apply_commit()`, which build the same
    /// logical `Turn` at different times, on different machines. If each stamped its
    /// own `now + horizon` independently, a participant applying a commit long after
    /// the coordinator built it would launder a stale proposal into artificial
    /// freshness — the exact bug this field exists to close, reopened by a different
    /// door. Included in `hash` (below), so every participant sees and implicitly
    /// signs off on the deadline before voting Yes.
    pub valid_until: Option<i64>,
    /// BLAKE3 hash of the entire atomic forest structure.
    pub hash: [u8; 32],
}

impl AtomicForest {
    /// Create a new atomic forest, computing its hash.
    ///
    /// `valid_until` is REQUIRED (not defaulted to `None` here) so every call site
    /// makes an explicit choice. Production callers should use
    /// [`default_valid_until`]; test fixtures that don't exercise expiration are free
    /// to pass `None` — see `no_atomic_forest_field_omits_the_unbounded_sentinel_by_typo`
    /// in this module's tests for why that is a different, unenforceable-by-type
    /// property from `Turn::valid_until: None` being reachable in `commit`/`apply_commit`.
    pub fn new(
        participants: Vec<[u8; 32]>,
        forest: CallForest,
        preconditions: Vec<(CellId, Preconditions)>,
        initiator: CellId,
        fee: u64,
        valid_until: Option<i64>,
    ) -> Self {
        let forest_hash = forest.compute_hash();
        let hash = Self::compute_hash(
            &participants,
            &forest_hash,
            &preconditions,
            &initiator,
            fee,
            valid_until,
        );
        AtomicForest {
            participants,
            forest,
            preconditions,
            initiator,
            fee,
            valid_until,
            hash,
        }
    }

    /// Compute the hash of an atomic forest from its components.
    ///
    /// SECURITY: Hashes the FULL precondition contents (via `Preconditions::hash()`)
    /// to prevent hash collisions where different precondition values produce
    /// identical forest hashes. This binds the signature to the exact preconditions
    /// agreed upon.
    fn compute_hash(
        participants: &[[u8; 32]],
        forest_hash: &[u8; 32],
        preconditions: &[(CellId, Preconditions)],
        initiator: &CellId,
        fee: u64,
        valid_until: Option<i64>,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-coord:atomic-forest");
        for p in participants {
            hasher.update(p);
        }
        hasher.update(forest_hash);
        for (cell_id, preconds) in preconditions {
            hasher.update(cell_id.as_bytes());
            // Hash the full precondition contents to prevent collision attacks.
            hasher.update(&preconds.hash());
        }
        hasher.update(initiator.as_bytes());
        hasher.update(&fee.to_le_bytes());
        // Tagged explicitly (a leading 0/1 byte) so None and Some(0) hash differently.
        match valid_until {
            Some(v) => {
                hasher.update(&[1u8]);
                hasher.update(&v.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        };
        *hasher.finalize().as_bytes()
    }

    /// Validate that the forest is structurally sound.
    pub fn validate(&self) -> Result<(), CoordError> {
        if self.participants.is_empty() {
            return Err(CoordError::NoParticipants);
        }
        if self.forest.is_empty() {
            return Err(CoordError::EmptyForest);
        }
        Ok(())
    }

    /// Get the number of participants.
    pub fn participant_count(&self) -> usize {
        self.participants.len()
    }

    /// Check if a node is a participant.
    pub fn is_participant(&self, node_id: &[u8; 32]) -> bool {
        self.participants.contains(node_id)
    }

    /// Estimate the computron cost of executing this forest given a cost table.
    ///
    /// This is a lower-bound estimate used for budget gating at proposal time.
    pub fn estimated_cost(&self, costs: &ComputronCosts) -> u64 {
        let action_count = self.forest.action_count() as u64;
        // Each action has a base cost and at least one effect.
        action_count.saturating_mul(costs.action_base.saturating_add(costs.effect_base))
    }

    /// The canonical wire encoding of an atomic forest — the `forest_data` payload
    /// of a `PeerMessage::ProposeAtomicTurn`.
    ///
    /// THE BROADCAST FIX (coord half): the previous mesh path wrapped a 2-field
    /// JSON stub `{"type":"atomic_proposal","proposal_id":...}` and gossiped it via
    /// `PublishTurn` — the receiving peer could not reconstruct the forest from it
    /// (no participants, no preconditions, no call forest), so it dropped on decode
    /// (`blocklace_sync.rs`'s `_ => return`). This is the RICHER payload: the full,
    /// self-describing forest a receiving participant needs to evaluate the proposal
    /// against its own local ledger. Postcard-framed (the same codec `dregg-net`
    /// uses for the enclosing `PeerMessage`).
    pub fn encode_for_wire(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("AtomicForest serialization cannot fail")
    }

    /// Reconstruct an atomic forest from the `forest_data` of a received
    /// `PeerMessage::ProposeAtomicTurn`. The receive-side counterpart of
    /// [`Self::encode_for_wire`]; the funnel calls this to lift the gossiped
    /// proposal back into the in-process coord engine instead of dropping it.
    pub fn decode_from_wire(bytes: &[u8]) -> Result<Self, CoordError> {
        postcard::from_bytes(bytes).map_err(|e| CoordError::WireDecode(e.to_string()))
    }
}

// ─── Vote ──────────────────────────────────────────────────────────────────────

/// A participant's vote on a proposed atomic forest.
#[derive(Clone, Debug)]
pub enum Vote {
    /// The participant agrees: preconditions met, ready to commit.
    Yes {
        /// Signature over `proposal_id || forest_hash || VOTE_YES_FLAG`.
        signature: [u8; 64],
    },
    /// The participant rejects: preconditions failed or policy violation.
    No {
        /// Human-readable reason for rejection.
        reason: String,
        /// Signature over `proposal_id || forest_hash || VOTE_NO_FLAG`.
        /// Prevents network adversaries from injecting fake No votes.
        signature: [u8; 64],
    },
}

/// Flag byte included in the signing message to distinguish Yes from No votes.
const VOTE_YES_FLAG: u8 = 0x01;
/// Flag byte included in the signing message to distinguish No from Yes votes.
const VOTE_NO_FLAG: u8 = 0x00;
/// Flag byte for abort message signatures.
const ABORT_FLAG: u8 = 0x02;

impl Vote {
    /// Create a Yes vote with a signature.
    pub fn yes(signature: [u8; 64]) -> Self {
        Vote::Yes { signature }
    }

    /// Create a No vote with a reason and signature.
    pub fn no(reason: impl Into<String>, signature: [u8; 64]) -> Self {
        Vote::No {
            reason: reason.into(),
            signature,
        }
    }

    /// Whether this is a Yes vote.
    pub fn is_yes(&self) -> bool {
        matches!(self, Vote::Yes { .. })
    }

    /// Whether this is a No vote.
    pub fn is_no(&self) -> bool {
        matches!(self, Vote::No { .. })
    }

    /// Construct the signing message for a vote.
    ///
    /// The message includes `proposal_id || forest_hash || vote_flag` to prevent
    /// replay across proposals and ensure Yes/No signatures are not interchangeable.
    fn signing_message(proposal_id: &[u8; 32], forest_hash: &[u8; 32], flag: u8) -> Vec<u8> {
        let mut msg = Vec::with_capacity(65);
        msg.extend_from_slice(proposal_id);
        msg.extend_from_slice(forest_hash);
        msg.push(flag);
        msg
    }

    /// Create a real Ed25519 signature for a Yes vote.
    ///
    /// Signs over `proposal_id || forest_hash || VOTE_YES_FLAG` to bind the vote
    /// to a specific proposal and prevent cross-proposal replay.
    pub fn sign_yes(
        proposal_id: &[u8; 32],
        forest_hash: &[u8; 32],
        signing_key_bytes: &[u8; 32],
    ) -> [u8; 64] {
        let signing_key = SigningKey::from_bytes(signing_key_bytes);
        let msg = Self::signing_message(proposal_id, forest_hash, VOTE_YES_FLAG);
        let sig = signing_key.sign(&msg);
        sig.to_bytes()
    }

    /// Create a real Ed25519 signature for a No vote.
    ///
    /// Signs over `proposal_id || forest_hash || VOTE_NO_FLAG` to prevent
    /// network adversaries from injecting fake No votes.
    pub fn sign_no(
        proposal_id: &[u8; 32],
        forest_hash: &[u8; 32],
        signing_key_bytes: &[u8; 32],
    ) -> [u8; 64] {
        let signing_key = SigningKey::from_bytes(signing_key_bytes);
        let msg = Self::signing_message(proposal_id, forest_hash, VOTE_NO_FLAG);
        let sig = signing_key.sign(&msg);
        sig.to_bytes()
    }

    /// Verify a Yes vote signature against the expected public key.
    pub fn verify_yes(
        signature: &[u8; 64],
        proposal_id: &[u8; 32],
        forest_hash: &[u8; 32],
        pubkey_bytes: &[u8; 32],
    ) -> bool {
        let Ok(verifying_key) = VerifyingKey::from_bytes(pubkey_bytes) else {
            return false;
        };
        let msg = Self::signing_message(proposal_id, forest_hash, VOTE_YES_FLAG);
        let sig = Signature::from_bytes(signature);
        verifying_key.verify_strict(&msg, &sig).is_ok()
    }

    /// Verify a No vote signature against the expected public key.
    pub fn verify_no(
        signature: &[u8; 64],
        proposal_id: &[u8; 32],
        forest_hash: &[u8; 32],
        pubkey_bytes: &[u8; 32],
    ) -> bool {
        let Ok(verifying_key) = VerifyingKey::from_bytes(pubkey_bytes) else {
            return false;
        };
        let msg = Self::signing_message(proposal_id, forest_hash, VOTE_NO_FLAG);
        let sig = Signature::from_bytes(signature);
        verifying_key.verify_strict(&msg, &sig).is_ok()
    }

    /// Derive the Ed25519 public key from a signing key (for test setup).
    pub fn public_key_from_signing_key(signing_key_bytes: &[u8; 32]) -> [u8; 32] {
        let signing_key = SigningKey::from_bytes(signing_key_bytes);
        signing_key.verifying_key().to_bytes()
    }
}

// ─── Decision ──────────────────────────────────────────────────────────────────

/// The outcome of the voting phase.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Decision {
    /// Enough Yes votes: threshold reached, proceed to commit.
    Commit,
    /// Too many No votes: impossible to reach threshold, abort.
    Abort,
    /// Still waiting for more votes.
    Pending,
}

/// Decide the 2PC verdict via the VERIFIED Lean export `dregg_coord_2pc_decide`
/// (= `Dregg2.Coord.TwoPhaseCommit.evaluate`). Returns `Some(decision)` when the gate ran, or `None`
/// when the verified gate is unavailable (archive lacks the export / no gate registered) — in which
/// case [`Coordinator::evaluate_votes`] FAILS CLOSED (Abort) on the live path rather than running a
/// native decider. The wire is `"y=<yes>;n=<no>;N=<participants>;t=<threshold>"`; the gate returns
/// `Decision2pc` which we map onto this crate's `Decision`. Routes through the
/// [`crate::verified_gate`] seam so the crate has no hard dependency on the Lean archive.
fn verified_decision(yes: usize, no: usize, n: usize, threshold: usize) -> Option<Decision> {
    use crate::verified_gate::Verdict2pc;
    let gate = crate::verified_gate::gate()?;
    if !gate.distributed_exports_available() {
        return None;
    }
    let wire = format!("y={yes};n={no};N={n};t={threshold}");
    match gate.decide_2pc(&wire) {
        Some(Verdict2pc::Commit) => Some(Decision::Commit),
        Some(Verdict2pc::Abort) => Some(Decision::Abort),
        Some(Verdict2pc::Pending) => Some(Decision::Pending),
        // FFI / wire error ⇒ `None`, which the caller (`evaluate_votes`) turns into the fail-closed
        // `evaluate_votes_no_gate()` — an ABORT from `Proposing`, not the native Rust tally.
        None => None,
    }
}

// TEST-ONLY fault injection that lets the NATIVE 2PC sibling decide on the gate-absent path.
//
// ⚑ WHY IT EXISTS: `evaluate_votes_no_gate` used to be TWO functions — fail-closed `Abort` under
// `cfg(not(test))`, `evaluate_votes_native()` (which can return `Commit`) under `cfg(test)`. A test
// build whose gate-absent path can COMMIT where production ABORTS means the crate's own tests never
// exercised the production disposition at all. It now has ONE body, and the differentials that need
// native tally semantics through the REAL `receive_vote` path ARM THIS FLAG BY NAME. The divergence
// is therefore declared and per-test instead of being a silently different code path for the whole
// test binary.
//
// THREAD-LOCAL, not a static: cargo runs this crate's tests concurrently in one process, and a
// process-wide flag would let one test's arming change another's disposition.
//
// (Plain `//` comments, not `///`: a doc comment on a macro invocation is an `unused_doc_comments`
// warning — the macro would have to emit the docs itself.)
#[cfg(test)]
thread_local! {
    static FORCE_NATIVE_2PC_DIFFERENTIAL: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
fn native_2pc_differential_armed() -> bool {
    FORCE_NATIVE_2PC_DIFFERENTIAL.with(|c| c.get())
}

/// TEST-ONLY RAII arming of the native 2PC differential sibling for THIS thread. Held by the tests
/// that drive `receive_vote` and need the native tally verdict (the `coord_diff` / `entangled_diff`
/// differentials and the coordinator lifecycle tests); dropping it restores the PRODUCTION
/// fail-closed disposition. See [`FORCE_NATIVE_2PC_DIFFERENTIAL`].
#[cfg(test)]
pub(crate) struct NativeDifferentialArmed;

#[cfg(test)]
impl NativeDifferentialArmed {
    pub(crate) fn new() -> Self {
        FORCE_NATIVE_2PC_DIFFERENTIAL.with(|c| c.set(true));
        Self
    }
}

#[cfg(test)]
impl Drop for NativeDifferentialArmed {
    fn drop(&mut self) {
        FORCE_NATIVE_2PC_DIFFERENTIAL.with(|c| c.set(false));
    }
}

// ─── Messages ──────────────────────────────────────────────────────────────────

/// Message sent by the coordinator to propose an atomic turn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProposeMessage {
    /// The proposed atomic forest.
    pub forest: AtomicForest,
    /// The coordinator's node ID.
    pub coordinator: [u8; 32],
    /// Unique proposal ID (hash of forest + coordinator + timestamp).
    pub proposal_id: [u8; 32],
}

/// Message sent by the coordinator to commit the atomic turn.
#[derive(Clone, Debug)]
pub struct CommitMessage {
    /// The proposal this commit refers to.
    pub proposal_id: [u8; 32],
    /// The turn receipt from execution.
    pub receipt: TurnReceipt,
    /// Aggregated signatures from all Yes voters.
    pub signatures: Vec<([u8; 32], [u8; 64])>,
}

/// Message sent by the coordinator to abort the atomic turn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AbortMessage {
    /// The proposal this abort refers to.
    pub proposal_id: [u8; 32],
    /// Why the abort happened.
    pub reason: String,
    /// Which participants voted No (if any).
    pub rejectors: Vec<[u8; 32]>,
    /// Coordinator signature over `proposal_id || ABORT_FLAG`.
    /// Prevents network adversaries from injecting fake abort messages.
    #[serde(with = "crate::serde_sig")]
    pub signature: [u8; 64],
}

// ─── CoordinatorState ──────────────────────────────────────────────────────────

/// The state machine for the 2-phase commit coordinator.
#[derive(Clone, Debug)]
pub enum CoordinatorState {
    /// No active proposal.
    Idle,
    /// A proposal has been sent, collecting votes.
    Proposing {
        forest: AtomicForest,
        votes: HashMap<[u8; 32], Vote>,
        proposal_id: [u8; 32],
        /// When the proposal was created (for timeout detection).
        proposed_at: Option<Instant>,
    },
    /// The atomic turn was successfully committed.
    Committed {
        receipt: TurnReceipt,
        proposal_id: [u8; 32],
    },
    /// The atomic turn was aborted.
    Aborted {
        reason: String,
        proposal_id: [u8; 32],
    },
}

impl CoordinatorState {
    /// Get a string name for this state (for error messages).
    pub fn name(&self) -> &'static str {
        match self {
            CoordinatorState::Idle => "Idle",
            CoordinatorState::Proposing { .. } => "Proposing",
            CoordinatorState::Committed { .. } => "Committed",
            CoordinatorState::Aborted { .. } => "Aborted",
        }
    }
}

// ─── Coordinator ───────────────────────────────────────────────────────────────

/// Drives the 2-phase commit protocol for atomic multi-party turns.
///
/// Lifecycle:
/// 1. `propose()` — transition from Idle to Proposing, emit ProposeMessage.
/// 2. `receive_vote()` — collect votes; returns Decision when threshold is met or impossible.
/// 3. `commit()` — apply the forest to the ledger if Decision::Commit.
/// 4. `abort()` — emit AbortMessage if Decision::Abort or timeout.
/// 5. `check_timeout()` — poll for proposal timeout; returns AbortMessage if expired.
///
/// # Threshold Model
///
/// The threshold is configurable: commit requires at least `threshold` Yes votes
/// (not necessarily all participants). For unanimous agreement, set
/// `threshold == participants.len()`. This supports flexible quorum policies
/// where a strict subset of participants suffices for commitment.
#[derive(Clone, Debug)]
pub struct Coordinator {
    /// Current state of the coordinator.
    pub state: CoordinatorState,
    /// How many Yes votes are needed to commit.
    pub threshold: usize,
    /// The coordinator's node ID.
    pub node_id: [u8; 32],
    /// The coordinator's Ed25519 signing key (32-byte seed).
    /// Used to sign AbortMessages so participants can verify authenticity.
    pub signing_key: [u8; 32],
    /// Cost table for computron metering.
    pub costs: ComputronCosts,
    /// Maximum computron budget for an atomic turn.
    pub max_budget: u64,
    /// Map from participant cell_id (node_id) to their Ed25519 public key.
    /// Used to verify vote signatures.
    pub participant_keys: HashMap<[u8; 32], [u8; 32]>,
    /// Maximum time a proposal may remain in `Proposing` state before being
    /// automatically aborted. The caller is responsible for calling
    /// `check_timeout()` periodically (event-loop style).
    pub proposal_timeout: Duration,
}

impl Coordinator {
    /// Create a new coordinator with full security parameters.
    ///
    /// - `threshold`: minimum Yes votes required to commit.
    /// - `costs`: computron cost table for metering.
    /// - `max_budget`: if the forest's estimated cost exceeds this, reject at propose time.
    /// - `participant_keys`: map of node_id -> Ed25519 public key bytes.
    ///   Vote signatures are verified against these keys.
    /// - `signing_key`: the coordinator's Ed25519 signing key for signing AbortMessages.
    ///
    /// The default proposal timeout is 30 seconds. Use `with_proposal_timeout()`
    /// to override.
    pub fn new(
        node_id: [u8; 32],
        signing_key: [u8; 32],
        threshold: usize,
        costs: ComputronCosts,
        max_budget: u64,
        participant_keys: HashMap<[u8; 32], [u8; 32]>,
    ) -> Self {
        Coordinator {
            state: CoordinatorState::Idle,
            threshold,
            node_id,
            signing_key,
            costs,
            max_budget,
            participant_keys,
            proposal_timeout: Duration::from_secs(30),
        }
    }

    /// Set the proposal timeout duration.
    ///
    /// If a proposal remains in `Proposing` state longer than this duration,
    /// `check_timeout()` will return an `AbortMessage`.
    pub fn with_proposal_timeout(mut self, timeout: Duration) -> Self {
        self.proposal_timeout = timeout;
        self
    }

    /// Propose an atomic forest for multi-party commitment.
    ///
    /// Transitions: Idle -> Proposing.
    /// Returns a ProposeMessage to send to all participants.
    ///
    /// Rejects proposals whose estimated cost exceeds `max_budget`.
    pub fn propose(&mut self, forest: AtomicForest) -> Result<ProposeMessage, CoordError> {
        if !matches!(self.state, CoordinatorState::Idle) {
            return Err(CoordError::InvalidCoordinatorState {
                expected: "Idle",
                actual: self.state.name(),
            });
        }

        forest.validate()?;

        if self.threshold == 0 || self.threshold > forest.participants.len() {
            return Err(CoordError::InvalidThreshold {
                threshold: self.threshold,
                participants: forest.participants.len(),
            });
        }

        // Budget gate: reject proposals that would exceed the coordinator's max budget.
        let estimated = forest.estimated_cost(&self.costs);
        if estimated > self.max_budget {
            return Err(CoordError::BudgetExceeded {
                estimated,
                max_budget: self.max_budget,
            });
        }

        let proposal_id = self.compute_proposal_id(&forest);

        let msg = ProposeMessage {
            forest: forest.clone(),
            coordinator: self.node_id,
            proposal_id,
        };

        self.state = CoordinatorState::Proposing {
            forest,
            votes: HashMap::new(),
            proposal_id,
            proposed_at: Some(Instant::now()),
        };

        Ok(msg)
    }

    /// Receive a vote from a participant.
    ///
    /// Both `Vote::Yes` and `Vote::No` signatures are verified against the
    /// participant's registered public key before accepting the vote. Invalid
    /// signatures are rejected with `CoordError::InvalidVoteSignature`.
    ///
    /// Signatures are bound to the specific `proposal_id` and `forest_hash` to
    /// prevent cross-proposal replay attacks.
    ///
    /// Returns `Some(Decision)` when a definitive outcome is reached,
    /// or `None` if still waiting.
    pub fn receive_vote(
        &mut self,
        from: [u8; 32],
        vote: Vote,
    ) -> Result<Option<Decision>, CoordError> {
        let (forest, votes, proposal_id) = match &mut self.state {
            CoordinatorState::Proposing {
                forest,
                votes,
                proposal_id,
                ..
            } => (forest, votes, *proposal_id),
            other => {
                return Err(CoordError::InvalidCoordinatorState {
                    expected: "Proposing",
                    actual: other.name(),
                });
            }
        };

        // Verify participant is in the forest.
        if !forest.is_participant(&from) {
            return Err(CoordError::UnknownParticipant { id: from });
        }

        // Check for duplicate votes.
        if votes.contains_key(&from) {
            return Err(CoordError::DuplicateVote { participant: from });
        }

        // CRITICAL: Verify Ed25519 signature on all votes (Yes and No).
        // Signatures are bound to (proposal_id, forest_hash, vote_flag) to prevent
        // replay across proposals and fake vote injection.
        let pubkey_bytes = self
            .participant_keys
            .get(&from)
            .ok_or(CoordError::UnknownParticipant { id: from })?;
        match &vote {
            Vote::Yes { signature } => {
                if !Vote::verify_yes(signature, &proposal_id, &forest.hash, pubkey_bytes) {
                    return Err(CoordError::InvalidVoteSignature { participant: from });
                }
            }
            Vote::No { signature, .. } => {
                if !Vote::verify_no(signature, &proposal_id, &forest.hash, pubkey_bytes) {
                    return Err(CoordError::InvalidVoteSignature { participant: from });
                }
            }
        }

        votes.insert(from, vote);

        // Check if we can decide.
        let decision = self.evaluate_votes();
        Ok(if decision == Decision::Pending {
            None
        } else {
            Some(decision)
        })
    }

    /// Commit the atomic forest to a ledger after receiving enough Yes votes.
    ///
    /// Transitions: Proposing -> Committed.
    /// Returns a CommitMessage and the TurnReceipt.
    pub fn commit(&mut self, ledger: &mut Ledger) -> Result<CommitMessage, CoordError> {
        let (forest, votes, proposal_id) = match &self.state {
            CoordinatorState::Proposing {
                forest,
                votes,
                proposal_id,
                ..
            } => (forest.clone(), votes.clone(), *proposal_id),
            other => {
                return Err(CoordError::InvalidCoordinatorState {
                    expected: "Proposing",
                    actual: other.name(),
                });
            }
        };

        // Verify threshold is met.
        let yes_count = votes.values().filter(|v| v.is_yes()).count();
        if yes_count < self.threshold {
            return Err(CoordError::ThresholdNotMet {
                required: self.threshold,
                received: yes_count,
            });
        }

        // Build a Turn from the atomic forest.
        let agent_cell = ledger
            .get(&forest.initiator)
            .ok_or(CoordError::TurnExecution(
                dregg_turn::TurnError::CellNotFound {
                    id: forest.initiator,
                },
            ))?;
        let nonce = agent_cell.state.nonce();

        let turn = Turn {
            agent: forest.initiator,
            nonce,
            call_forest: forest.forest.clone(),
            fee: forest.fee,
            memo: Some("atomic multi-party turn".to_string()),
            // Read from the forest, NOT re-derived here: commit() and apply_commit()
            // build the same logical Turn at different times/places (coordinator now,
            // each participant potentially much later). Independently stamping
            // `now + horizon` at each site would let a participant launder a stale
            // proposal into artificial freshness. See AtomicForest::valid_until's doc.
            valid_until: forest.valid_until,
            depends_on: Vec::new(),
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

        // Execute the turn with proper metering.
        let mut executor = TurnExecutor::new(self.costs.clone());
        // `TurnExecutor::new` defaults `current_timestamp` to 0 — without advancing it,
        // the expiration check (`turn/src/executor/execute.rs:426`,
        // `if self.current_timestamp > valid_until`) can never fire no matter what
        // `turn.valid_until` says, making the fix above inert. This executor is
        // constructed fresh per call and isn't wired through the node's
        // `executor_setup::configure_turn_executor` (unlike the thin-HTTP path), so
        // nothing else sets this; do it here.
        executor.current_timestamp = wall_clock_now_secs();
        let result = executor.execute(&turn, ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Collect signatures from Yes voters.
                let signatures: Vec<([u8; 32], [u8; 64])> = votes
                    .iter()
                    .filter_map(|(id, vote)| {
                        if let Vote::Yes { signature } = vote {
                            Some((*id, *signature))
                        } else {
                            None
                        }
                    })
                    .collect();

                let msg = CommitMessage {
                    proposal_id,
                    receipt: receipt.clone(),
                    signatures,
                };

                self.state = CoordinatorState::Committed {
                    receipt,
                    proposal_id,
                };

                Ok(msg)
            }
            TurnResult::Rejected { reason, .. } => Err(CoordError::TurnExecution(reason)),
            TurnResult::Expired | TurnResult::Pending => {
                unreachable!("execute() never returns Expired/Pending")
            }
        }
    }

    /// Abort the current proposal.
    ///
    /// Transitions: Proposing -> Aborted.
    /// Returns a signed AbortMessage to send to all participants.
    pub fn abort(&mut self, reason: impl Into<String>) -> Result<AbortMessage, CoordError> {
        let (votes, proposal_id) = match &self.state {
            CoordinatorState::Proposing {
                votes, proposal_id, ..
            } => (votes.clone(), *proposal_id),
            other => {
                return Err(CoordError::InvalidCoordinatorState {
                    expected: "Proposing",
                    actual: other.name(),
                });
            }
        };

        let reason_str = reason.into();
        let rejectors: Vec<[u8; 32]> = votes
            .iter()
            .filter_map(|(id, vote)| if vote.is_no() { Some(*id) } else { None })
            .collect();

        let signature = Self::sign_abort(&proposal_id, &self.signing_key);

        let msg = AbortMessage {
            proposal_id,
            reason: reason_str.clone(),
            rejectors,
            signature,
        };

        self.state = CoordinatorState::Aborted {
            reason: reason_str,
            proposal_id,
        };

        Ok(msg)
    }

    /// Sign an abort message: signs over `proposal_id || ABORT_FLAG`.
    fn sign_abort(proposal_id: &[u8; 32], signing_key_bytes: &[u8; 32]) -> [u8; 64] {
        let signing_key = SigningKey::from_bytes(signing_key_bytes);
        let mut msg = Vec::with_capacity(33);
        msg.extend_from_slice(proposal_id);
        msg.push(ABORT_FLAG);
        let sig = signing_key.sign(&msg);
        sig.to_bytes()
    }

    /// Verify an abort message signature against the coordinator's public key.
    ///
    /// ⚑ **NOTHING CALLS THIS, AND THERE IS NOTHING FOR IT TO CALL FROM.** Measured
    /// 2026-07-27: zero call sites tree-wide, tests included. The reason is structural, not an
    /// oversight of one call — the abort leg is WRITE-ONLY. [`Coordinator::abort`] mints a
    /// signed [`AbortMessage`], `sign_abort` signs it, this verifies it, and
    /// [`Participant`] has **no handler that consumes one**: it has `apply_commit` for a
    /// `CommitMessage` and `timeout_abort` for its own unilateral, message-free release, and
    /// nothing in between. A participant that voted Yes and is sent an abort cannot act on it;
    /// it waits out `vote_timeout`.
    ///
    /// Do not "fix" this by adding a handler that calls this function. `atomic::Coordinator`
    /// and `atomic::Participant` are constructed ONLY by test code across the entire tree
    /// (`coord/src/tests.rs`, `coord_diff.rs`, `entangled_diff.rs`, `private_leg.rs` — which is
    /// `#![cfg(test)]` — and `coord/tests/twin_fail_closed.rs`); no node, sdk, or wasm path
    /// builds either. A handler here would have no production caller of its own, so wiring it
    /// would quiet the census (`baseline/production-callers.tsv`) without one more line running
    /// on any deployed path. The real disposition is a subsystem call: delete this 2PC pair or
    /// deploy it.
    pub fn verify_abort(abort_msg: &AbortMessage, coordinator_pubkey: &[u8; 32]) -> bool {
        let Ok(verifying_key) = VerifyingKey::from_bytes(coordinator_pubkey) else {
            return false;
        };
        let mut msg = Vec::with_capacity(33);
        msg.extend_from_slice(&abort_msg.proposal_id);
        msg.push(ABORT_FLAG);
        let sig = Signature::from_bytes(&abort_msg.signature);
        verifying_key.verify_strict(&msg, &sig).is_ok()
    }

    /// Check whether the current proposal has timed out.
    ///
    /// Returns `Some(AbortMessage)` if the proposal has been pending longer than
    /// `proposal_timeout`, transitioning the coordinator to `Aborted` state.
    /// Returns `None` if not in `Proposing` state or the timeout has not elapsed.
    ///
    /// The caller is responsible for calling this periodically (event-loop style).
    ///
    /// ⚑ **THERE IS NO SUCH EVENT LOOP.** Measured 2026-07-27: zero call sites tree-wide, tests
    /// included. Read the classification honestly — this is NOT a decider despite the `check_`
    /// prefix that puts it in `baseline/production-callers.tsv`'s guard class: it refuses
    /// nothing and validates nothing, it POLLS a clock and emits an abort. Its absence is a
    /// LIVENESS gap (a proposal stays `Proposing` forever, and every participant that voted Yes
    /// holds its lock until its own `vote_timeout`), not a soundness one. Same subsystem verdict
    /// as [`Self::verify_abort`]: `atomic::Coordinator` has no production constructor anywhere.
    pub fn check_timeout(&mut self, now: Instant) -> Option<AbortMessage> {
        let (proposed_at, proposal_id) = match &self.state {
            CoordinatorState::Proposing {
                proposed_at,
                proposal_id,
                ..
            } => (*proposed_at, *proposal_id),
            _ => return None,
        };

        let start = proposed_at?;
        if now.duration_since(start) < self.proposal_timeout {
            return None;
        }

        // Timeout exceeded -- abort.
        let votes = match &self.state {
            CoordinatorState::Proposing { votes, .. } => votes.clone(),
            _ => return None,
        };

        let rejectors: Vec<[u8; 32]> = votes
            .iter()
            .filter_map(|(id, vote)| if vote.is_no() { Some(*id) } else { None })
            .collect();

        let reason = format!("proposal timed out after {:?}", self.proposal_timeout);
        let signature = Self::sign_abort(&proposal_id, &self.signing_key);

        let msg = AbortMessage {
            proposal_id,
            reason: reason.clone(),
            rejectors,
            signature,
        };

        self.state = CoordinatorState::Aborted {
            reason,
            proposal_id,
        };

        Some(msg)
    }

    /// Reset the coordinator to Idle state.
    pub fn reset(&mut self) {
        self.state = CoordinatorState::Idle;
    }

    /// Evaluate the current votes to determine if a decision can be made.
    ///
    /// The AUTHORITATIVE verdict is the verified Lean 2PC gate
    /// (`Dregg2.Exec.DistributedExports::dregg_coord_2pc_decide` = `TwoPhaseCommit.evaluate`,
    /// carried by `coord_2pc_decide_eq`), routed through the [`crate::verified_gate`] seam. So the
    /// coordinator inherits `evaluate_not_commit_and_abort` (no conflicting Commit+Abort) and
    /// `commit_needs_threshold` by construction.
    ///
    /// When no verified gate is registered (a native node that never installed the
    /// `dregg-exec-lean` gate, or an archive lacking the export) the live path FAILS CLOSED — it
    /// returns [`Decision::Abort`] rather than silently running an unverified Rust decider. A
    /// production node MUST install the gate; refusing to commit is the safe verdict when it is
    /// absent. That disposition is [`Self::evaluate_votes_no_gate`], and it is now IDENTICAL under
    /// `cfg(test)` and in a release/consumer build.
    fn evaluate_votes(&self) -> Decision {
        if let Some((yes, no, n, thr)) = self.current_tally()
            && let Some(d) = verified_decision(yes, no, n, thr)
        {
            return d;
        }
        self.evaluate_votes_no_gate()
    }

    /// The live-path disposition when the verified 2PC gate is unavailable: FAIL CLOSED. A
    /// terminal/idle state has no tally to decide (Pending, as before); a `Proposing` state with no
    /// linked verified gate refuses to commit ([`Decision::Abort`]) — never a silent native decision.
    ///
    /// ⚑ ONE BODY FOR EVERY CFG. This function used to have TWO definitions: the fail-closed one
    /// above under `cfg(not(test))`, and `self.evaluate_votes_native()` under `cfg(test)` — which CAN
    /// RETURN `Decision::Commit`. So `cargo test -p dregg-coord` exercised a gate-absent disposition
    /// that a deployed node does not have: the crate's own tests could not have caught a regression
    /// in the production refusal, because they never ran it. (Only `coord/tests/twin_fail_closed.rs`
    /// did, by linking the crate WITHOUT `cfg(test)`.) The divergence is now a DECLARED, narrowly
    /// scoped, test-only FAULT INJECTOR that the DIFFERENTIALS ARM EXPLICITLY
    /// ([`native_2pc_differential_armed`]) — the default disposition in a test build is the
    /// production one.
    fn evaluate_votes_no_gate(&self) -> Decision {
        #[cfg(test)]
        {
            // The native sibling is the DIFFERENTIAL against `TwoPhaseCommit.evaluate`
            // (`coord_diff.rs`). It decides only for a test that armed it by name.
            if native_2pc_differential_armed() {
                return self.evaluate_votes_native();
            }
        }
        match self.state {
            CoordinatorState::Proposing { .. } => Decision::Abort,
            _ => Decision::Pending,
        }
    }

    /// The NATIVE Rust 2PC decision — the DIFFERENTIAL sibling of the verified Lean gate, retained
    /// ONLY under `cfg(test)` so it is cross-checked against `TwoPhaseCommit.evaluate` in
    /// `coord_diff.rs` and can NEVER decide on a live path. Byte-for-byte `TwoPhaseCommit.evaluate`:
    /// `if yes ≥ threshold Commit else if no > n − threshold Abort else Pending`.
    #[cfg(test)]
    fn evaluate_votes_native(&self) -> Decision {
        let (forest, votes) = match &self.state {
            CoordinatorState::Proposing { forest, votes, .. } => (forest, votes),
            _ => return Decision::Pending,
        };

        let total_participants = forest.participants.len();
        let yes_count = votes.values().filter(|v| v.is_yes()).count();
        let no_count = votes.values().filter(|v| v.is_no()).count();

        if yes_count >= self.threshold {
            Decision::Commit
        } else if no_count > total_participants - self.threshold {
            // Too many No votes — threshold can never be reached.
            Decision::Abort
        } else {
            Decision::Pending
        }
    }

    /// The current vote tally `(yes, no, participants, threshold)` while Proposing, or `None` in a
    /// terminal/idle state.
    ///
    /// This is the SAFETY content of `evaluate_votes` (pure counting). It is exposed so the node can
    /// build the wire for the VERIFIED Lean 2PC gate (`Dregg2.Exec.DistributedExports`'s
    /// `dregg_coord_2pc_decide` = `TwoPhaseCommit.evaluate`). The node makes the Lean gate the
    /// AUTHORITATIVE decider and keeps this Rust `evaluate_votes` as the DIFFERENTIAL sibling.
    pub fn current_tally(&self) -> Option<(usize, usize, usize, usize)> {
        match &self.state {
            CoordinatorState::Proposing { forest, votes, .. } => {
                let yes = votes.values().filter(|v| v.is_yes()).count();
                let no = votes.values().filter(|v| v.is_no()).count();
                Some((yes, no, forest.participants.len(), self.threshold))
            }
            _ => None,
        }
    }

    /// Encode the current tally as the `dregg_coord_2pc_decide` wire
    /// (`"y=<yes>;n=<no>;N=<participants>;t=<threshold>"`), or `None` if not Proposing. The verified
    /// Lean gate decodes this to a `TwoPhaseCommit.Tally` and returns the verdict that
    /// `coord_2pc_decide_eq` proves equal to `TwoPhaseCommit.evaluate`.
    pub fn decision_wire(&self) -> Option<String> {
        self.current_tally()
            .map(|(yes, no, n, thr)| format!("y={yes};n={no};N={n};t={thr}"))
    }

    /// Compute a unique proposal ID for THIS coordinator's view of a forest.
    fn compute_proposal_id(&self, forest: &AtomicForest) -> [u8; 32] {
        Self::proposal_id_for(&forest.hash, &self.node_id)
    }

    /// Compute the proposal id from `(forest_hash, coordinator)` — the canonical
    /// binding `H("dregg-coord:proposal" || forest_hash || coordinator)`.
    ///
    /// Exposed so a 2PC PARTICIPANT receiving a `ProposeAtomicTurn` can RECOMPUTE
    /// and verify the coordinator's claimed `proposal_id` (closing the proposal-id
    /// gap: the participant then signs its vote over the SAME id the coordinator
    /// will tally against, instead of binding to the bare `forest_hash`).
    pub fn proposal_id_for(forest_hash: &[u8; 32], coordinator: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-coord:proposal");
        hasher.update(forest_hash);
        hasher.update(coordinator);
        *hasher.finalize().as_bytes()
    }
}

// ─── Participant ───────────────────────────────────────────────────────────────

/// A node participating in an atomic multi-party turn.
///
/// The participant evaluates proposals against its local ledger view
/// and decides whether to vote Yes or No.
///
/// After voting Yes, the participant holds a lock until receiving a CommitMessage
/// or until `vote_timeout` expires. If the coordinator crashes, the participant
/// can unilaterally abort after timeout (safe because the coordinator cannot form
/// a QC without continued lock from this participant).
#[derive(Clone, Debug)]
pub struct Participant {
    /// The cell ID this participant owns/controls.
    pub cell_id: CellId,
    /// The participant's node ID (for signing).
    pub node_id: [u8; 32],
    /// The participant's Ed25519 signing key (32-byte seed).
    pub signing_key: [u8; 32],
    /// Local ledger view.
    pub ledger: Ledger,
    /// Computron cost table used for local replay.
    pub costs: ComputronCosts,
    /// Maximum time to wait for a commit/abort after voting Yes.
    /// After this duration, the participant may unilaterally release its lock.
    pub vote_timeout: Duration,
    /// Timestamp when the participant last voted Yes (for timeout detection).
    pub voted_yes_at: Option<Instant>,
    /// The proposal_id the participant is currently participating in.
    pub active_proposal: Option<[u8; 32]>,
}

impl Participant {
    /// Create a new participant with a signing key.
    pub fn new(cell_id: CellId, node_id: [u8; 32], signing_key: [u8; 32], ledger: Ledger) -> Self {
        Participant {
            cell_id,
            node_id,
            signing_key,
            ledger,
            costs: ComputronCosts::default_costs(),
            vote_timeout: Duration::from_secs(60),
            voted_yes_at: None,
            active_proposal: None,
        }
    }

    /// Create a new participant with specific costs (for testing with zero costs).
    pub fn with_costs(
        cell_id: CellId,
        node_id: [u8; 32],
        signing_key: [u8; 32],
        ledger: Ledger,
        costs: ComputronCosts,
    ) -> Self {
        Participant {
            cell_id,
            node_id,
            signing_key,
            ledger,
            costs,
            vote_timeout: Duration::from_secs(60),
            voted_yes_at: None,
            active_proposal: None,
        }
    }

    /// Set the vote timeout duration.
    pub fn with_vote_timeout(mut self, timeout: Duration) -> Self {
        self.vote_timeout = timeout;
        self
    }

    /// Check if this participant's vote has timed out (coordinator presumed crashed).
    ///
    /// Returns `true` if the participant voted Yes and the timeout has elapsed,
    /// meaning it is safe to unilaterally release the lock.
    pub fn has_vote_timed_out(&self, now: Instant) -> bool {
        if let Some(voted_at) = self.voted_yes_at {
            now.duration_since(voted_at) >= self.vote_timeout
        } else {
            false
        }
    }

    /// Unilaterally abort after vote timeout.
    ///
    /// Safe because the coordinator cannot form a QC without this participant's
    /// continued lock. Clears the active proposal state.
    pub fn timeout_abort(&mut self) {
        self.voted_yes_at = None;
        self.active_proposal = None;
    }

    /// Evaluate a proposed atomic forest and produce a vote.
    ///
    /// The participant checks:
    /// 1. That it is listed as a participant.
    /// 2. That its preconditions are satisfied on its local ledger.
    /// 3. That the forest structure is valid.
    ///
    /// If all checks pass, returns Vote::Yes with a signature bound to `proposal_id`.
    /// Otherwise, returns Vote::No with a reason and signature.
    ///
    /// The `proposal_id` comes from the ProposeMessage and is included in the
    /// signing message to bind the vote to a specific proposal (preventing replay).
    pub fn evaluate_proposal(&mut self, proposal_id: &[u8; 32], forest: &AtomicForest) -> Vote {
        // Check we're a participant.
        if !forest.is_participant(&self.node_id) {
            let sig = Vote::sign_no(proposal_id, &forest.hash, &self.signing_key);
            return Vote::no("not listed as participant", sig);
        }

        // Check structural validity.
        if let Err(e) = forest.validate() {
            let sig = Vote::sign_no(proposal_id, &forest.hash, &self.signing_key);
            return Vote::no(format!("invalid forest: {e}"), sig);
        }

        // Check our preconditions.
        for (cell_id, preconditions) in &forest.preconditions {
            if cell_id == &self.cell_id
                && let Some(ref cell_pre) = preconditions.cell_state
            {
                // Look up our cell in the local ledger.
                match self.ledger.get(&self.cell_id) {
                    Some(cell) => {
                        if let Err(e) = cell_pre.evaluate(&cell.state) {
                            let sig = Vote::sign_no(proposal_id, &forest.hash, &self.signing_key);
                            return Vote::no(format!("precondition failed: {e:?}"), sig);
                        }
                    }
                    None => {
                        let sig = Vote::sign_no(proposal_id, &forest.hash, &self.signing_key);
                        return Vote::no("our cell not found in local ledger", sig);
                    }
                }
            }
        }

        // All checks passed -- sign the vote bound to proposal_id.
        let signature = Vote::sign_yes(proposal_id, &forest.hash, &self.signing_key);
        self.voted_yes_at = Some(Instant::now());
        self.active_proposal = Some(*proposal_id);
        Vote::yes(signature)
    }

    /// Apply a committed atomic forest to our local ledger.
    ///
    /// Called after receiving a CommitMessage from the coordinator.
    /// Verifies the CommitMessage has valid QC signatures before applying.
    /// Replays the turn execution locally to update state.
    ///
    /// # Parameters
    /// - `commit`: the CommitMessage from the coordinator (contains QC signatures).
    /// - `forest`: the atomic forest being committed.
    /// - `participant_keys`: map of node_id -> Ed25519 public key for QC verification.
    /// - `threshold`: minimum number of valid signatures required in the QC.
    pub fn apply_commit(
        &mut self,
        commit: &CommitMessage,
        forest: &AtomicForest,
        participant_keys: &HashMap<[u8; 32], [u8; 32]>,
        threshold: usize,
    ) -> Result<TurnReceipt, CoordError> {
        // Verify the commit message has enough valid signatures (QC).
        if commit.signatures.len() < threshold {
            return Err(CoordError::ThresholdNotMet {
                required: threshold,
                received: commit.signatures.len(),
            });
        }

        // Verify each signature in the QC is valid and bound to the proposal.
        let proposal_id = &commit.proposal_id;
        for (node_id, signature) in &commit.signatures {
            let pubkey_bytes = participant_keys
                .get(node_id)
                .ok_or(CoordError::UnknownParticipant { id: *node_id })?;
            if !Vote::verify_yes(signature, proposal_id, &forest.hash, pubkey_bytes) {
                return Err(CoordError::InvalidVoteSignature {
                    participant: *node_id,
                });
            }
        }

        // Build the same turn the coordinator would have built.
        let agent_cell = self
            .ledger
            .get(&forest.initiator)
            .ok_or(CoordError::TurnExecution(
                dregg_turn::TurnError::CellNotFound {
                    id: forest.initiator,
                },
            ))?;
        let nonce = agent_cell.state.nonce();

        let turn = Turn {
            agent: forest.initiator,
            nonce,
            call_forest: forest.forest.clone(),
            fee: forest.fee,
            memo: Some("atomic multi-party turn".to_string()),
            // Read from the forest, NOT re-derived here: commit() and apply_commit()
            // build the same logical Turn at different times/places (coordinator now,
            // each participant potentially much later). Independently stamping
            // `now + horizon` at each site would let a participant launder a stale
            // proposal into artificial freshness. See AtomicForest::valid_until's doc.
            valid_until: forest.valid_until,
            depends_on: Vec::new(),
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

        let mut executor = TurnExecutor::new(self.costs.clone());
        // See the identical comment in Coordinator::commit(): without advancing
        // current_timestamp past its TurnExecutor::new default of 0, valid_until can
        // never be exceeded and the expiration check is inert.
        executor.current_timestamp = wall_clock_now_secs();
        let result = executor.execute(&turn, &mut self.ledger);

        // Clear active proposal state on successful apply.
        self.voted_yes_at = None;
        self.active_proposal = None;

        match result {
            TurnResult::Committed { receipt, .. } => Ok(receipt),
            TurnResult::Rejected { reason, .. } => Err(CoordError::TurnExecution(reason)),
            TurnResult::Expired | TurnResult::Pending => {
                unreachable!("execute() never returns Expired/Pending")
            }
        }
    }

    /// Verify a commit message's signatures against the forest hash using Ed25519.
    ///
    /// `participant_keys` maps node_id -> public key bytes.
    /// Verifies signatures are bound to the proposal_id (not just forest hash).
    pub fn verify_commit(
        &self,
        commit: &CommitMessage,
        forest: &AtomicForest,
        participant_keys: &HashMap<[u8; 32], [u8; 32]>,
    ) -> bool {
        let proposal_id = &commit.proposal_id;
        for (node_id, signature) in &commit.signatures {
            let Some(pubkey_bytes) = participant_keys.get(node_id) else {
                return false;
            };
            if !Vote::verify_yes(signature, proposal_id, &forest.hash, pubkey_bytes) {
                return false;
            }
        }
        true
    }
}

// ─── AtomicForestBuilder ───────────────────────────────────────────────────────

/// Builder for constructing atomic forests incrementally.
pub struct AtomicForestBuilder {
    participants: Vec<[u8; 32]>,
    forest: CallForest,
    preconditions: Vec<(CellId, Preconditions)>,
    initiator: Option<CellId>,
    fee: u64,
    valid_until: Option<i64>,
}

impl AtomicForestBuilder {
    /// Create a new builder.
    ///
    /// `valid_until` defaults to [`default_valid_until()`], NOT `None` — a builder
    /// whose caller forgets to set it should still produce an expiring turn. Call
    /// [`Self::set_valid_until`] to override (e.g. a test that wants `None`, or a
    /// caller with its own horizon policy).
    pub fn new() -> Self {
        AtomicForestBuilder {
            participants: Vec::new(),
            forest: CallForest::new(),
            preconditions: Vec::new(),
            initiator: None,
            fee: 0,
            valid_until: default_valid_until(),
        }
    }

    /// Add a participant by node ID.
    pub fn add_participant(&mut self, node_id: [u8; 32]) -> &mut Self {
        self.participants.push(node_id);
        self
    }

    /// Set the call forest.
    pub fn set_forest(&mut self, forest: CallForest) -> &mut Self {
        self.forest = forest;
        self
    }

    /// Add a precondition for a specific cell.
    pub fn add_precondition(&mut self, cell_id: CellId, preconditions: Preconditions) -> &mut Self {
        self.preconditions.push((cell_id, preconditions));
        self
    }

    /// Set the initiator (fee payer).
    pub fn set_initiator(&mut self, initiator: CellId) -> &mut Self {
        self.initiator = Some(initiator);
        self
    }

    /// Set the fee.
    pub fn set_fee(&mut self, fee: u64) -> &mut Self {
        self.fee = fee;
        self
    }

    /// Override the validity deadline (defaults to [`default_valid_until()`] — see
    /// [`Self::new`]).
    pub fn set_valid_until(&mut self, valid_until: Option<i64>) -> &mut Self {
        self.valid_until = valid_until;
        self
    }

    /// Build the atomic forest.
    pub fn build(self) -> Result<AtomicForest, CoordError> {
        let initiator = self.initiator.ok_or(CoordError::NoParticipants)?;
        let forest = AtomicForest::new(
            self.participants,
            self.forest,
            self.preconditions,
            initiator,
            self.fee,
            self.valid_until,
        );
        forest.validate()?;
        Ok(forest)
    }
}

impl Default for AtomicForestBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ─── PrivateLeg: the WITNESSLESS participant role ───────────────────────────────
//
// A private participant maintains its cell entirely OFFLINE. It never publishes its
// `RecordKernelState` (balances, caps, nullifiers) in cleartext — not to the other
// participants, not to the chain. It takes part in the multi-cell atomic turn by
// contributing ONLY a commitment to its private pre/post state + a ZK proof that its
// side of the turn was a real, guarded, conserving, authorized executor step.
//
// This is the Rust production-wiring of `Dregg2/Distributed/PrivateLeg.lean` (keystone
// `joint_turn_sound_with_private_legs`) and `metatheory/docs/PRIVATE-OFFLINE-CELLS.md` §4/§7. Where
// the public legs of an `AtomicForest` apply an `Action`/`Effect` to the shared `Ledger`,
// a private leg is `(commit_pre, commit_post, proof)` and NEVER touches the shared machine.
//
// SCOPE (matches the Lean keystone): this is the SOUNDNESS-side of the role —
//   * the commit-path verify-gate `MixedAdmissible` (every private leg's proof verifies +
//     binds the shared `jid`), and
//   * state-root continuity across turns (`commit_post[i] == commit_pre[i+1]`, mirroring
//     `Dregg2/Distributed/HistoryAggregation.lean::ChainBound`).
// LIVENESS is explicitly out of scope (Lean §7, doc §7): a private participant that goes
// dark aborts the all-or-none turn, exactly as a public participant voting No does. That
// is a safety-preserving failure; data-availability of the offline cell is the maintainer's
// own problem by construction (that is the point of holding it offline).

/// The asset column a private leg moves. Mirrors the Lean `AssetId` (per-asset conservation
/// is per this column). Opaque 32-byte asset/token identifier on the wire.
pub type AssetId = [u8; 32];

/// A commitment to a hidden `RecordKernelState`. In production this is the Poseidon2 state
/// root (`Circuit/StateCommit.lean::recStateCommit`, injective under the CR floor); here it
/// is carried as an opaque 32-byte field-element commitment, exactly as the Lean model keeps
/// `commitPre`/`commitPost : ℤ` abstract so the role is carrier-agnostic.
pub type StateCommit = [u8; 32];

/// The CG-2 shared turn-id a leg consents to (Mina's `account_updates_hash`). Both public and
/// private legs of one mixed turn bind to ONE of these — that is the Agreement face.
pub type JointId = [u8; 32];

/// The public face of a PRIVATE leg: everything the offline maintainer broadcasts. The hidden
/// `RecordKernelState` is deliberately NOT a field — that is the whole point of the role.
///
/// Mirrors the Lean `PrivateLeg.PrivLeg` structure exactly:
/// `(asset, commitPre, commitPost, jid)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateLeg {
    /// The asset column this private leg moves (per-asset conservation is per this column).
    pub asset: AssetId,
    /// Commitment to the hidden PRE state (Poseidon2 state root in production).
    pub commit_pre: StateCommit,
    /// Commitment to the hidden POST state.
    pub commit_post: StateCommit,
    /// The CG-2 shared turn-id this leg consents to — how the forest binds the leg in.
    pub jid: JointId,
}

impl PrivateLeg {
    /// Construct the public face of a private leg.
    pub fn new(
        asset: AssetId,
        commit_pre: StateCommit,
        commit_post: StateCommit,
        jid: JointId,
    ) -> Self {
        PrivateLeg {
            asset,
            commit_pre,
            commit_post,
            jid,
        }
    }

    /// The canonical byte-encoding of a private leg's PUBLIC face — the statement the ZK proof
    /// must bind. This is the bytes a faithful AIR commits as its public inputs: the asset
    /// column, both state-root commitments, and the shared `jid`. A proof binds THIS leg iff
    /// its bound statement-digest equals `statement_digest()` (see `PrivateLegProof`).
    ///
    /// Domain-separated so a private-leg statement can never be confused with any other digest.
    pub fn statement_digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-coord:private-leg-stmt");
        hasher.update(&self.asset);
        hasher.update(&self.commit_pre);
        hasher.update(&self.commit_post);
        hasher.update(&self.jid);
        *hasher.finalize().as_bytes()
    }
}

/// A private leg's ZK proof — the §8 STARK floor, the SAME `VerifierKernel` carrier every
/// other circuit verification in the tree rests on (`Crypto/PortalFloor.lean::VerifierKernel`).
///
/// On the Lean side the per-leg statement is `PrivLegHolds scommit pl` ("∃ hidden kPre/kPost:
/// `recKExecAsset` commits, the published commitments match, conservation & authority hold"),
/// and an accepting proof discharges it via `verify_sound` — the extractability carrier, an
/// explicit hypothesis, NEVER a Lean law. Here, faithfully, the proof carries the
/// `bound_statement` digest it was produced for; `verify` checks that digest equals the leg's
/// `statement_digest()`. A proof that binds a DIFFERENT statement (in particular a different
/// `jid`, or different commitments) does NOT verify for this leg — that is the anti-ghost.
///
/// The named crypto floor is exactly: an accepting proof certifies a real guarded offline
/// executor step existed whose commitments are the published ones. Modelling the STARK as an
/// opaque carrier here (rather than re-running plonky3) is faithful to the keystone — the same
/// way `entangled_diff.rs` treats the Ed25519 vote signature as the named assumption — and the
/// `bound_statement` binding makes the jid-binding tooth REAL, not vacuous.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateLegProof {
    /// The statement digest this proof was produced for. A faithful AIR exposes the leg's
    /// public face (`asset || commit_pre || commit_post || jid`) as public inputs; this digest
    /// is the commitment to that PI vector. The verify-gate refuses any proof whose bound
    /// statement is not the leg's own — binding the proof to the asset, the commitments, AND
    /// the shared `jid`.
    pub bound_statement: [u8; 32],
    /// Whether the underlying STARK is accepting. In production this is the result of running
    /// the plonky3 verifier on the proof bytes against the leg's public inputs; the named §8
    /// extractability floor says an accepting proof certifies a real offline step.
    pub stark_ok: bool,
}

impl PrivateLegProof {
    /// Build the proof an HONEST offline maintainer broadcasts for a leg: it binds exactly that
    /// leg's statement and its STARK is accepting. (The real prover runs the AIR over the hidden
    /// witness; here we construct the carrier whose `verify` will accept against this leg.)
    pub fn for_leg(leg: &PrivateLeg) -> Self {
        PrivateLegProof {
            bound_statement: leg.statement_digest(),
            stark_ok: true,
        }
    }

    /// **The commit-path verify-gate for ONE private leg** — the per-leg conjunct of
    /// `MixedAdmissible`. The proof verifies against `leg` iff:
    ///   (1) the underlying STARK is accepting (`stark_ok`), AND
    ///   (2) the proof binds THIS leg's exact statement — `bound_statement == leg
    ///       .statement_digest()`, which includes the shared `jid`.
    ///
    /// (2) is the anti-ghost: a proof produced for a different statement (a different `jid`, or
    /// "conjure value from nothing" commitments) fails to bind, mirroring the Lean
    /// `privLeg_forged_rejected` tooth — only the extractability carrier could ever rescue an
    /// unbound proof, and the honest carrier here refuses it.
    pub fn verify(&self, leg: &PrivateLeg) -> bool {
        self.stark_ok && self.bound_statement == leg.statement_digest()
    }
}

/// A private leg paired with its published proof — the wire object the offline maintainer
/// broadcasts into the forest. Mirrors the Lean `PrivateLeg.PrivContribution`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateContribution {
    /// The public face of the private leg (commitments + asset + jid; NO hidden state).
    pub leg: PrivateLeg,
    /// The ZK proof certifying the offline step (the §8 STARK carrier).
    pub proof: PrivateLegProof,
}

impl PrivateContribution {
    /// Construct a contribution from a leg and its proof.
    pub fn new(leg: PrivateLeg, proof: PrivateLegProof) -> Self {
        PrivateContribution { leg, proof }
    }
}

/// The MIXED joint turn: some legs PUBLIC (run on the shared `Ledger` via the existing
/// `AtomicForest` 2PC path), some legs PRIVATE (proof-only offline contributions). All consent
/// to ONE `jid` (CG-2). Mirrors the Lean `PrivateLeg.MixedJoint`.
///
/// `public_forest` is the ordinary `AtomicForest` (the PUBLIC backbone, untouched — its legs
/// apply actions to the shared machine). `private_legs` are the witnessless contributions; they
/// never touch the shared machine and are admitted purely by their verifying, jid-bound proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MixedJoint {
    /// The CG-2 shared turn-id every leg (public + private) consents to.
    pub jid: JointId,
    /// The public legs, as an ordinary atomic forest applied to the shared ledger.
    pub public_forest: AtomicForest,
    /// The private, proof-only offline contributions.
    pub private_legs: Vec<PrivateContribution>,
}

/// Why a mixed joint turn was refused at the commit-path verify-gate. The private-leg analog of
/// a `Vote::No` / a failed precondition — a safety-preserving abort of the all-or-none turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MixedAdmitError {
    /// A private leg's ZK proof failed to verify (STARK rejected, OR the proof did not bind
    /// this leg's statement). `index` is its position in `private_legs`.
    PrivateProofRejected { index: usize },
    /// A private leg consents to a DIFFERENT `jid` than the shared turn id — it is not part of
    /// THIS turn. `index` is its position; `leg_jid`/`turn_jid` are the mismatch.
    PrivateJidMismatch {
        index: usize,
        leg_jid: JointId,
        turn_jid: JointId,
    },
}

impl core::fmt::Display for MixedAdmitError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MixedAdmitError::PrivateProofRejected { index } => {
                write!(
                    f,
                    "private leg {index}: ZK proof rejected (STARK or binding)"
                )
            }
            MixedAdmitError::PrivateJidMismatch {
                index,
                leg_jid,
                turn_jid,
            } => {
                write!(
                    f,
                    "private leg {index}: jid mismatch (leg {}, turn {})",
                    hex4_prefix(leg_jid),
                    hex4_prefix(turn_jid)
                )
            }
        }
    }
}

impl MixedJoint {
    /// Construct a mixed joint turn from its shared id, public forest, and private contributions.
    pub fn new(
        jid: JointId,
        public_forest: AtomicForest,
        private_legs: Vec<PrivateContribution>,
    ) -> Self {
        MixedJoint {
            jid,
            public_forest,
            private_legs,
        }
    }

    /// **The PRIVATE half of `MixedAdmissible`** (Lean `PrivateLeg.MixedAdmissible`, conjuncts 2
    /// and 3). The commit-path verify-gate for the witnessless participants: it returns `Ok(())`
    /// iff EVERY private leg
    ///   * consents to the shared `jid` (CG-2 binding), AND
    ///   * has a proof that verifies AND binds its own statement (the §8 carrier + anti-ghost).
    ///
    /// The PUBLIC conjunct (`jointApplyAll public_forest = some k'`) is the existing 2PC commit
    /// path on the shared `Ledger` (`Coordinator::commit`); this method is the additional gate a
    /// coordinator runs BEFORE committing a turn that carries private participants. Together they
    /// are full `MixedAdmissible`: the whole mixed turn commits all-or-none.
    ///
    /// Fail-closed: the FIRST offending private leg is reported and the turn is refused. A dark /
    /// missing private participant simply never produces a verifying proof, so the turn aborts —
    /// liveness-out-of-scope, safety preserved.
    pub fn check_private_legs_admissible(&self) -> Result<(), MixedAdmitError> {
        for (index, pc) in self.private_legs.iter().enumerate() {
            // CG-2: the leg must consent to THIS turn's shared id.
            if pc.leg.jid != self.jid {
                return Err(MixedAdmitError::PrivateJidMismatch {
                    index,
                    leg_jid: pc.leg.jid,
                    turn_jid: self.jid,
                });
            }
            // The §8 ZK carrier + anti-ghost: the proof must verify AND bind this exact leg
            // (asset, both commitments, and — via the statement digest — the shared jid).
            if !pc.proof.verify(&pc.leg) {
                return Err(MixedAdmitError::PrivateProofRejected { index });
            }
        }
        Ok(())
    }
}

// ─── PrivateLegChain: state-root continuity across turns (HistoryAggregation.ChainBound) ─────

/// A `ChainBound` violation for a long-lived offline cell: the `commit_post` of one turn does
/// not equal the `commit_pre` of its successor, so the published state-root history is not a
/// continuous chain. `index` is the position of the earlier leg in the sequence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainBreak {
    /// The position of the leg whose `commit_post` failed to match the next leg's `commit_pre`.
    pub index: usize,
    /// The `commit_post` published by leg `index`.
    pub expected_pre: StateCommit,
    /// The `commit_pre` published by leg `index + 1`.
    pub found_pre: StateCommit,
}

/// **State-root continuity across the turns of ONE offline cell** — the production analog of
/// `Dregg2/HistoryAggregation.lean::ChainBound`. A private participant that lives across many
/// turns publishes a SEQUENCE of `PrivateLeg`s; for the published commitment history to be a
/// coherent evolution of ONE offline cell, the `commit_post` of each turn must be the
/// `commit_pre` of the next:
/// ```text
///   commit_post[i] == commit_pre[i+1]   for every consecutive pair
/// ```
/// (Exactly `ChainBound`'s `step.prevRoot == prior.postRoot` carried to the private-leg roots.)
///
/// Returns `Ok(())` for an empty or singleton sequence (trivially chained), or the FIRST
/// `ChainBreak`. This is what binds a private participant's turns into one continuous offline
/// history without ever revealing a state: only the roots are checked, never the witnesses.
pub fn check_chain_bound(legs: &[PrivateLeg]) -> Result<(), ChainBreak> {
    for (index, pair) in legs.windows(2).enumerate() {
        let prior = &pair[0];
        let next = &pair[1];
        if prior.commit_post != next.commit_pre {
            return Err(ChainBreak {
                index,
                expected_pre: prior.commit_post,
                found_pre: next.commit_pre,
            });
        }
    }
    Ok(())
}

/// Format the first 4 bytes of a 32-byte id as hex (local display helper for `MixedAdmitError`).
fn hex4_prefix(bytes: &[u8; 32]) -> String {
    format!(
        "{:02x}{:02x}{:02x}{:02x}...",
        bytes[0], bytes[1], bytes[2], bytes[3]
    )
}
