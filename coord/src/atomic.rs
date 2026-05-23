//! Layer 2: Atomic Multi-Party Turns.
//!
//! Multiple agents on different nodes contribute actions to ONE call forest.
//! The combined forest is only committed if ALL participants' preconditions are met.
//! Uses a simple 2-phase commit: Propose -> Vote -> Commit/Abort.
//! If any participant's preconditions fail, the entire forest is aborted.
//! The committed forest gets a threshold QC (everyone who participated signs).

use std::collections::HashMap;
use std::time::{Duration, Instant};

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use pyana_cell::{CellId, Ledger, Preconditions};
use pyana_turn::{CallForest, ComputronCosts, Turn, TurnExecutor, TurnReceipt, TurnResult};
use serde::{Deserialize, Serialize};

use crate::error::CoordError;

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
    /// BLAKE3 hash of the entire atomic forest structure.
    pub hash: [u8; 32],
}

impl AtomicForest {
    /// Create a new atomic forest, computing its hash.
    pub fn new(
        participants: Vec<[u8; 32]>,
        forest: CallForest,
        preconditions: Vec<(CellId, Preconditions)>,
        initiator: CellId,
        fee: u64,
    ) -> Self {
        let forest_hash = forest.compute_hash();
        let hash = Self::compute_hash(&participants, &forest_hash, &preconditions, &initiator, fee);
        AtomicForest {
            participants,
            forest,
            preconditions,
            initiator,
            fee,
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
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-coord:atomic-forest");
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
                pyana_turn::TurnError::CellNotFound {
                    id: forest.initiator,
                },
            ))?;
        let nonce = agent_cell.state.nonce;

        let turn = Turn {
            agent: forest.initiator,
            nonce,
            call_forest: forest.forest.clone(),
            fee: forest.fee,
            memo: Some("atomic multi-party turn".to_string()),
            valid_until: None,
            depends_on: Vec::new(),
            previous_receipt_hash: None,
            conservation_proof: None,
        };

        // Execute the turn with proper metering.
        let executor = TurnExecutor::new(self.costs.clone());
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
    fn evaluate_votes(&self) -> Decision {
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

    /// Compute a unique proposal ID.
    fn compute_proposal_id(&self, forest: &AtomicForest) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-coord:proposal");
        hasher.update(&forest.hash);
        hasher.update(&self.node_id);
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
                pyana_turn::TurnError::CellNotFound {
                    id: forest.initiator,
                },
            ))?;
        let nonce = agent_cell.state.nonce;

        let turn = Turn {
            agent: forest.initiator,
            nonce,
            call_forest: forest.forest.clone(),
            fee: forest.fee,
            memo: Some("atomic multi-party turn".to_string()),
            valid_until: None,
            depends_on: Vec::new(),
            previous_receipt_hash: None,
            conservation_proof: None,
        };

        let executor = TurnExecutor::new(self.costs.clone());
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
}

impl AtomicForestBuilder {
    /// Create a new builder.
    pub fn new() -> Self {
        AtomicForestBuilder {
            participants: Vec::new(),
            forest: CallForest::new(),
            preconditions: Vec::new(),
            initiator: None,
            fee: 0,
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

    /// Build the atomic forest.
    pub fn build(self) -> Result<AtomicForest, CoordError> {
        let initiator = self.initiator.ok_or(CoordError::NoParticipants)?;
        let forest = AtomicForest::new(
            self.participants,
            self.forest,
            self.preconditions,
            initiator,
            self.fee,
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
