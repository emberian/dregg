//! Constitutional Consensus: Democratic Membership Amendment Protocol.
//!
//! From the Constitutional Consensus paper (arXiv:2505.19216): participants in a
//! federation can propose and vote on membership changes. The constitution defines
//! the participant set, supermajority threshold, and rules for amendment.
//!
//! Key concepts:
//! - **Constitution**: the current participant set + threshold + version.
//! - **MembershipProposal**: a proposal to join, leave, or amend the threshold.
//! - **H-Rule**: changing the threshold from T to T' requires max(T, T') votes.
//! - **Timeout-based auto-leave**: nodes silent for `timeout_waves` waves are
//!   proposed for removal. When they return, they re-join via a Join proposal.
//! - **Voting via blocks**: votes reference the proposal block in their causal past.
//! - **n=1 case**: with a single participant, every wave finalizes instantly (self
//!   is always the leader with threshold=1). Adding a peer grows the threshold;
//!   their timeout shrinks it back.
//!
//! ⚑ **The participant set NEVER mutates on an equivocation** (flag day
//! 2026-08-08, exclusion-by-past). `auto_evict` — a node-local, gossip-arrival-
//! ordered `participants.retain` + threshold recompute — is DELETED. It made the
//! τ participant set a function of local arrival order (node A holding both fork
//! halves ran at `n−1`, node B holding one ran at `n`; `wave_leader = participants
//! [wave % n]` then elects different leaders for the same wave: the F-CO-1 silent
//! fork through a second door), and it reverted on restart (never a block, never
//! in `committee_replay`'s fold). Both source papers keep `Π` fixed on
//! equivocation: exclusion is `node(b) ∉ byz(⌊b⌋)` — a predicate over each
//! block's own causal closure (blocklace paper arXiv:2402.08068 §4.3; Cordial
//! Miners `approves`, Alg. 1:17), evaluated inside τ (`ordering.rs::approves`,
//! Lean `Dregg2.Distributed.ExclusionByPast` / `BlocklaceFinality.hasEquivInPast`),
//! carried by the two-tips evidence floor (`finality.rs::CreatorTips`).
//! Membership changes remain what they always were here: VOTED proposals folded
//! from finalized blocks — committed state alone.

use serde::{Deserialize, Serialize};

use crate::finality::BlockId;

// ─── Constitution ──────────────────────────────────────────────────────────────

/// The federation's constitution (amendable by participants).
///
/// Tracks the current participant set, supermajority threshold, and version.
/// Each amendment increments the version, providing a linearizable history.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constitution {
    /// Current participant set (public keys, sorted for determinism).
    pub participants: Vec<[u8; 32]>,
    /// Supermajority threshold (default: 2n/3 + 1).
    pub threshold: usize,
    /// Waves without a block from a participant before auto-leave is proposed.
    /// A participant silent for this many waves is considered timed out.
    pub timeout_waves: u64,
    /// Constitution version (incremented on each amendment).
    pub version: u64,
    /// Grace period (in waves) before a recently-rejoined node can be evicted again.
    /// Prevents oscillation in small federations where timeout-eviction + rejoin
    /// creates a livelock cycle. Default: 2 * timeout_waves.
    pub rejoin_grace_waves: u64,
    /// Minimum duration (in waves) a node must be a member before it can be
    /// evicted via timeout. Prevents rapid eviction of newly joined nodes that
    /// haven't had time to produce blocks yet. Default: timeout_waves / 2.
    pub min_membership_duration: u64,
    /// When true, if more than 50% of participants timeout simultaneously,
    /// membership changes are frozen (no evictions). This assumes a network
    /// partition rather than mass node failure. Default: true.
    pub partition_detection: bool,
    /// Commitment to the current routing DFA (Blake3 hash of transition table).
    /// None = no governance-controlled routing (permissive).
    pub routes_commitment: Option<[u8; 32]>,
}

impl Constitution {
    /// Create a new constitution with the given initial participants.
    ///
    /// Threshold defaults to 2n/3 + 1 (supermajority).
    /// `timeout_waves` is the number of consecutive waves without a block
    /// before a participant is proposed for auto-leave.
    pub fn new(mut participants: Vec<[u8; 32]>, timeout_waves: u64) -> Self {
        participants.sort();
        participants.dedup();
        let threshold = compute_threshold(participants.len());
        Constitution {
            participants,
            threshold,
            timeout_waves,
            version: 0,
            rejoin_grace_waves: timeout_waves.saturating_mul(2),
            min_membership_duration: timeout_waves / 2,
            partition_detection: true,
            routes_commitment: None,
        }
    }

    /// Number of participants in the federation.
    pub fn participant_count(&self) -> usize {
        self.participants.len()
    }

    /// Check if a key is a current participant.
    pub fn is_participant(&self, key: &[u8; 32]) -> bool {
        self.participants.contains(key)
    }

    /// The number of votes required for a given proposal to pass.
    ///
    /// Implements the H-rule: amending the threshold from T to T' requires
    /// max(T, T') votes. This prevents a minority from lowering the threshold
    /// to seize control, or a majority from raising it to lock others out.
    pub fn required_votes_for(&self, proposal: &MembershipProposal) -> usize {
        match proposal {
            MembershipProposal::AmendThreshold { new_threshold } => {
                // H-rule: need max(current, new) votes
                std::cmp::max(self.threshold, *new_threshold)
            }
            // Route amendments use the current threshold (same as membership changes).
            MembershipProposal::AmendRoutes { .. } => self.threshold,
            _ => self.threshold,
        }
    }

    /// Apply a membership proposal to the constitution.
    ///
    /// This mutates the participant set, recomputes the threshold (for
    /// join/leave), and increments the version. `Ok(true)` = applied,
    /// `Ok(false)` = inert no-op (already a member / not a member / unchanged
    /// threshold), `Err` = the step is REFUSED BY NAME by the configuration
    /// step bound ([`config_step_allowed`], the Lean-authored
    /// `ConfigBoundary.classifyStep`) and NOTHING was mutated.
    ///
    /// Each ratified proposal is one configuration step of a single change
    /// (`j=1,l=0` for Join, `j=0,l=1` for Leave) — batched steps only arrive
    /// when the DBRB merge rule (D2) lands, and the bound is already stated
    /// over the general `(joins, leaves)` shape for it.
    pub fn apply_proposal(&mut self, proposal: &MembershipProposal) -> Result<bool, StepRefusal> {
        match proposal {
            MembershipProposal::Join {
                node_key,
                justification: _,
            } => {
                if self.participants.contains(node_key) {
                    return Ok(false); // Already a member
                }
                config_step_allowed(self.participants.len(), 1, 0)?;
                self.participants.push(*node_key);
                self.participants.sort();
                self.threshold = compute_threshold(self.participants.len());
                self.version += 1;
                Ok(true)
            }
            MembershipProposal::Leave {
                node_key,
                reason: _,
            } => {
                if !self.participants.contains(node_key) {
                    return Ok(false); // Not a member
                }
                config_step_allowed(self.participants.len(), 0, 1)?;
                self.participants.retain(|k| k != node_key);
                self.threshold = compute_threshold(self.participants.len());
                self.version += 1;
                Ok(true)
            }
            MembershipProposal::AmendThreshold { new_threshold } => {
                // ⚠ LOADED GUN, named: this variant decouples the threshold
                // from the roster, which the install discipline pins together
                // (`T(c)` a function of the configuration). It is dead from the
                // wire (FEDERATION-DESIGN-GAPS §2.12) and should be DELETED —
                // deletion drags `MembershipSafety.lean`'s H-rule model with it
                // and is its own pass.
                if *new_threshold == self.threshold {
                    return Ok(false); // No change
                }
                if *new_threshold == 0 || *new_threshold > self.participants.len() {
                    return Ok(false); // Invalid threshold
                }
                self.threshold = *new_threshold;
                self.version += 1;
                Ok(true)
            }
            MembershipProposal::AmendRoutes {
                new_routes_commitment,
                description: _,
            } => {
                // Update the routes commitment. Applied immediately (no grace period).
                self.routes_commitment = Some(*new_routes_commitment);
                self.version += 1;
                Ok(true)
            }
        }
    }
}

// ─── Membership Proposals ──────────────────────────────────────────────────────

/// A proposal to change federation membership or rules.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MembershipProposal {
    /// Add a new participant to the federation.
    Join {
        node_key: [u8; 32],
        /// Justification (e.g., stake proof, governance vote).
        justification: Vec<u8>,
    },
    /// Remove a participant (voluntary leave or eviction).
    Leave {
        node_key: [u8; 32],
        reason: LeaveReason,
    },
    /// Amend the supermajority threshold.
    /// The H-rule applies: changing from T to T' requires max(T, T') votes.
    AmendThreshold { new_threshold: usize },
    /// Amend the federation's routing table commitment.
    /// Cannot be combined with membership changes in the same proposal (separation of concerns).
    /// Applied immediately after threshold is reached (no grace period).
    AmendRoutes {
        /// Blake3 hash of the new DFA transition table.
        new_routes_commitment: [u8; 32],
        /// Human-readable description of what changed.
        description: String,
    },
}

/// Reason for a participant leaving the federation.
///
/// There is deliberately NO `Evicted`-on-equivocation variant: an equivocator is
/// excluded from ordering by the per-closure predicate (`node(b) ∉ byz(⌊b⌋)`),
/// never by a membership change — and the variant was constructed zero times
/// (the never-keep-a-no-op rule). A committee that wants an equivocator OUT of
/// the roster votes an ordinary `Leave` like any other membership change.
/// (⚑ wire flag day: removing the variant shifts the postcard enum tags —
/// old serialized proposals refuse to decode; the devnet re-genesis covers it.)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LeaveReason {
    /// Participant chose to leave.
    Voluntary,
    /// Participant timed out: no blocks produced for `timeout_waves` consecutive waves.
    /// The participant can rejoin by submitting a Join proposal once they come back online.
    Timeout {
        /// The last wave in which the participant produced a block.
        last_active_wave: u64,
        /// The wave at which the timeout was detected.
        detected_at_wave: u64,
    },
}

// ─── Membership Votes ──────────────────────────────────────────────────────────

/// A vote on a membership proposal.
///
/// Votes are expressed as block payloads that reference the proposal block
/// in their causal past. A proposal passes when `threshold` distinct approving
/// votes exist in the blocklace.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembershipVote {
    /// The block ID containing the proposal being voted on.
    pub proposal_block: BlockId,
    /// Whether this vote approves (true) or rejects (false) the proposal.
    pub approve: bool,
}

// ─── Vote Tracker ──────────────────────────────────────────────────────────────

/// Tracks votes for pending membership proposals.
///
/// A proposal passes when it accumulates the required number of approving votes
/// from distinct participants AND is in the causal past of a finalized leader.
#[derive(Clone, Debug, Default)]
pub struct VoteTracker {
    /// proposal_block_id -> set of approving voter keys.
    approvals: std::collections::HashMap<BlockId, std::collections::HashSet<[u8; 32]>>,
    /// proposal_block_id -> set of rejecting voter keys.
    rejections: std::collections::HashMap<BlockId, std::collections::HashSet<[u8; 32]>>,
    /// proposal_block_id -> the proposal itself (for lookup).
    proposals: std::collections::HashMap<BlockId, MembershipProposal>,
    /// Proposals that have been applied (to prevent double-application).
    applied: std::collections::HashSet<BlockId>,
}

impl VoteTracker {
    /// Create a new empty vote tracker.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a proposal. Returns false if already registered.
    pub fn register_proposal(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
    ) -> bool {
        if self.proposals.contains_key(&proposal_block) {
            return false;
        }
        self.proposals.insert(proposal_block, proposal);
        self.approvals.entry(proposal_block).or_default();
        self.rejections.entry(proposal_block).or_default();
        true
    }

    /// Record a vote. The voter must be a current participant.
    ///
    /// Returns the current approval count for this proposal.
    pub fn record_vote(
        &mut self,
        vote: &MembershipVote,
        voter: [u8; 32],
        constitution: &Constitution,
    ) -> usize {
        // Only current participants can vote.
        if !constitution.is_participant(&voter) {
            return self.approval_count(&vote.proposal_block);
        }

        // Only vote on known proposals.
        if !self.proposals.contains_key(&vote.proposal_block) {
            return 0;
        }

        if vote.approve {
            self.approvals
                .entry(vote.proposal_block)
                .or_default()
                .insert(voter);
        } else {
            self.rejections
                .entry(vote.proposal_block)
                .or_default()
                .insert(voter);
        }

        self.approval_count(&vote.proposal_block)
    }

    /// Every registered proposal with its live tally:
    /// `(proposal_block, proposal, approvals, rejections, applied)`.
    /// Backs the operator-facing membership surface (`GET /api/membership`);
    /// `applied` marks proposals that already amended the constitution (kept
    /// registered for idempotent re-processing, no longer pending).
    pub fn proposal_tallies(&self) -> Vec<(BlockId, MembershipProposal, usize, usize, bool)> {
        let mut v: Vec<(BlockId, MembershipProposal, usize, usize, bool)> = self
            .proposals
            .iter()
            .map(|(pb, p)| {
                (
                    *pb,
                    p.clone(),
                    self.approval_count(pb),
                    self.rejection_count(pb),
                    self.applied.contains(pb),
                )
            })
            .collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    }

    /// Get the number of approvals for a proposal.
    pub fn approval_count(&self, proposal_block: &BlockId) -> usize {
        self.approvals
            .get(proposal_block)
            .map(|s| s.len())
            .unwrap_or(0)
    }

    /// Get the number of rejections for a proposal.
    pub fn rejection_count(&self, proposal_block: &BlockId) -> usize {
        self.rejections
            .get(proposal_block)
            .map(|s| s.len())
            .unwrap_or(0)
    }

    /// Check if a proposal has reached the required vote threshold.
    pub fn has_passed(&self, proposal_block: &BlockId, constitution: &Constitution) -> bool {
        if self.applied.contains(proposal_block) {
            return false; // Already applied
        }
        let proposal = match self.proposals.get(proposal_block) {
            Some(p) => p,
            None => return false,
        };
        let required = constitution.required_votes_for(proposal);
        self.approval_count(proposal_block) >= required
    }

    /// Get the proposal for a given block ID.
    pub fn get_proposal(&self, proposal_block: &BlockId) -> Option<&MembershipProposal> {
        self.proposals.get(proposal_block)
    }

    /// Mark a proposal as applied (prevents double-application).
    pub fn mark_applied(&mut self, proposal_block: &BlockId) {
        self.applied.insert(*proposal_block);
    }

    /// Check if a proposal has already been applied.
    pub fn is_applied(&self, proposal_block: &BlockId) -> bool {
        self.applied.contains(proposal_block)
    }

    /// Get all proposals that have passed but not yet been applied.
    pub fn pending_passed(&self, constitution: &Constitution) -> Vec<BlockId> {
        self.proposals
            .keys()
            .filter(|id| self.has_passed(id, constitution))
            .copied()
            .collect()
    }
}

// ─── Constitution Manager ──────────────────────────────────────────────────────

/// Manages the full lifecycle of constitutional amendments.
///
/// Integrates the Constitution, VoteTracker, and history of past constitutions
/// (for verifying blocks against the constitution that was active when they
/// were created).
///
/// Also tracks per-participant activity for timeout-based auto-leave:
/// participants that produce no blocks for `constitution.timeout_waves`
/// consecutive waves are proposed for removal.
#[derive(Clone, Debug)]
pub struct ConstitutionManager {
    /// The current (active) constitution.
    pub current: Constitution,
    /// Vote tracker for pending proposals.
    pub votes: VoteTracker,
    /// History of past constitutions (version -> constitution snapshot).
    /// Used to verify blocks against the constitution active at their creation time.
    history: Vec<Constitution>,
    /// Last wave in which each participant produced a block.
    /// Used for timeout-based auto-leave detection.
    last_active_wave: std::collections::HashMap<[u8; 32], u64>,
    /// The current wave number (advanced externally as ordering progresses).
    pub current_wave: u64,
    /// Pending timeout-leave proposals (participants for whom we've already
    /// proposed auto-leave, to avoid duplicate proposals).
    pending_timeout_leaves: std::collections::HashSet<[u8; 32]>,
    /// Wave at which each participant joined (or rejoined) the federation.
    /// Used for `min_membership_duration` enforcement and `rejoin_grace_waves`.
    joined_at_wave: std::collections::HashMap<[u8; 32], u64>,
    /// Whether membership changes are currently frozen due to partition detection.
    /// Set to true when >50% of participants timeout simultaneously.
    /// Cleared when activity resumes from a majority of participants.
    pub membership_frozen: bool,
}

impl ConstitutionManager {
    /// Create a new constitution manager with the given initial constitution.
    pub fn new(constitution: Constitution) -> Self {
        let history = vec![constitution.clone()];
        // Initialize all participants as active at wave 0.
        let last_active_wave = constitution
            .participants
            .iter()
            .map(|k| (*k, 0u64))
            .collect();
        // All initial participants are considered "joined at wave 0".
        let joined_at_wave = constitution
            .participants
            .iter()
            .map(|k| (*k, 0u64))
            .collect();
        ConstitutionManager {
            current: constitution,
            votes: VoteTracker::new(),
            history,
            last_active_wave,
            current_wave: 0,
            pending_timeout_leaves: std::collections::HashSet::new(),
            joined_at_wave,
            membership_frozen: false,
        }
    }

    /// Create from initial participants with default timeout (in waves).
    pub fn from_participants(participants: Vec<[u8; 32]>, timeout_waves: u64) -> Self {
        Self::new(Constitution::new(participants, timeout_waves))
    }

    /// Get the constitution at a specific version.
    pub fn constitution_at_version(&self, version: u64) -> Option<&Constitution> {
        self.history.get(version as usize)
    }

    /// Process a proposal: register it in the vote tracker.
    pub fn submit_proposal(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
    ) -> bool {
        self.votes.register_proposal(proposal_block, proposal)
    }

    /// Process a vote on a proposal.
    ///
    /// Returns `Some(proposal_block)` if the proposal has now reached threshold
    /// and is ready to be applied (pending finality confirmation).
    pub fn submit_vote(&mut self, vote: &MembershipVote, voter: [u8; 32]) -> Option<BlockId> {
        self.votes.record_vote(vote, voter, &self.current);
        if self.votes.has_passed(&vote.proposal_block, &self.current) {
            Some(vote.proposal_block)
        } else {
            None
        }
    }

    /// Apply a proposal that has passed AND been confirmed via finality.
    ///
    /// This is called when the proposal is in the causal past of a finalized
    /// leader (Cordial Miners finality) — super-ratification of that leader IS
    /// the old configuration's certificate over the install, and the position
    /// of this block in the committed order IS the install point (identical on
    /// every honest node; Lean `ConfigBoundary.install_position_immutable`).
    ///
    /// `Ok(true)` = applied; `Ok(false)` = not passed / no proposal / inert;
    /// `Err` = the step bound REFUSED the change BY NAME and nothing mutated —
    /// distinct from `Ok(false)` so a refused proposal can never be mistaken
    /// for one still gathering votes. The refusal is also logged here (the one
    /// choke point every caller shares).
    pub fn apply_if_passed(&mut self, proposal_block: &BlockId) -> Result<bool, StepRefusal> {
        if !self.votes.has_passed(proposal_block, &self.current) {
            return Ok(false);
        }

        let proposal = match self.votes.get_proposal(proposal_block) {
            Some(p) => p.clone(),
            None => return Ok(false),
        };

        // Track the joining node for grace period enforcement.
        let joining_node = match &proposal {
            MembershipProposal::Join { node_key, .. } => Some(*node_key),
            _ => None,
        };

        match self.current.apply_proposal(&proposal) {
            Ok(true) => {
                self.votes.mark_applied(proposal_block);
                self.history.push(self.current.clone());

                // Record join time for newly added members (for min_membership_duration
                // and rejoin_grace_waves enforcement).
                if let Some(node_key) = joining_node {
                    self.joined_at_wave.insert(node_key, self.current_wave);
                    // Initialize their last_active_wave so they get a full timeout
                    // window from their join time, not from wave 0.
                    self.last_active_wave.insert(node_key, self.current_wave);
                }

                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(refusal) => {
                tracing::warn!(
                    proposal_block = %proposal_block,
                    refusal = %refusal,
                    "configuration step REFUSED BY NAME: the ratified proposal does not \
                     install (roster unchanged); re-propose after the roster moves"
                );
                Err(refusal)
            }
        }
    }

    // ─── Timeout-Based Auto-Leave ───────────────────────────────────────────

    /// Record that a participant produced a block in the given wave.
    ///
    /// This resets their timeout counter. If they were pending a timeout-leave
    /// proposal, that pending state is cleared.
    ///
    /// If membership is currently frozen (partition detection), checks whether
    /// enough participants are now active to unfreeze.
    pub fn record_activity(&mut self, participant: &[u8; 32], wave: u64) {
        let entry = self.last_active_wave.entry(*participant).or_insert(0);
        if wave > *entry {
            *entry = wave;
        }
        // If they were pending a timeout leave, they're back - clear it.
        self.pending_timeout_leaves.remove(participant);

        // Auto-unfreeze: if membership is frozen and a majority of participants
        // are now active (activity within timeout_waves), unfreeze.
        if self.membership_frozen && self.current.timeout_waves > 0 {
            let active_count = self
                .current
                .participants
                .iter()
                .filter(|p| {
                    let last = self.last_active_wave.get(*p).copied().unwrap_or(0);
                    wave.saturating_sub(last) <= self.current.timeout_waves
                })
                .count();
            if active_count * 2 > self.current.participants.len() {
                self.membership_frozen = false;
            }
        }
    }

    /// Advance the current wave and check for timeouts.
    ///
    /// Returns a list of `MembershipProposal::Leave` for participants that
    /// have been silent for `timeout_waves` consecutive waves. The caller
    /// is responsible for submitting these as proposals to the vote tracker.
    ///
    /// This implements the "sleepy validator" pattern: nodes that go offline
    /// are gradually removed, reducing the effective participant count and
    /// threshold so that the remaining active nodes can continue making progress.
    pub fn advance_wave(&mut self, new_wave: u64) -> Vec<MembershipProposal> {
        self.current_wave = new_wave;
        self.check_timeouts()
    }

    /// Check for participants that have timed out (no blocks for timeout_waves).
    ///
    /// Returns proposals for auto-leave due to timeout. Each participant
    /// is proposed at most once (tracked in `pending_timeout_leaves`).
    ///
    /// Anti-oscillation protections:
    /// - `min_membership_duration`: newly joined nodes get a grace period before eviction.
    /// - `rejoin_grace_waves`: recently rejoined nodes get extra timeout tolerance.
    /// - `partition_detection`: if >50% timeout simultaneously, freezes membership changes.
    fn check_timeouts(&mut self) -> Vec<MembershipProposal> {
        let timeout_waves = self.current.timeout_waves;
        // If timeout is 0, auto-leave is disabled.
        if timeout_waves == 0 {
            return vec![];
        }

        // If membership is frozen (partition detected), don't propose any evictions.
        if self.membership_frozen {
            return vec![];
        }

        let mut proposals = Vec::new();
        let mut timed_out_count = 0usize;
        let participant_count = self.current.participants.len();

        // First pass: count how many participants would time out.
        for participant in &self.current.participants {
            let last_active = self.last_active_wave.get(participant).copied().unwrap_or(0);
            let effective_timeout = self.effective_timeout_for(participant, timeout_waves);
            if self.current_wave.saturating_sub(last_active) > effective_timeout {
                timed_out_count += 1;
            }
        }

        // Partition detection: if >50% of participants timeout simultaneously,
        // this is likely a network partition, not mass node failure. Freeze
        // membership changes to prevent cascading evictions.
        if self.current.partition_detection
            && participant_count > 1
            && timed_out_count * 2 > participant_count
        {
            self.membership_frozen = true;
            return vec![];
        }

        // Second pass: generate proposals for timed-out participants.
        for participant in &self.current.participants {
            // Skip if we've already proposed this participant for timeout-leave.
            if self.pending_timeout_leaves.contains(participant) {
                continue;
            }

            // min_membership_duration: don't evict nodes that haven't been members
            // long enough to reasonably produce blocks.
            let joined_at = self.joined_at_wave.get(participant).copied().unwrap_or(0);
            let membership_duration = self.current_wave.saturating_sub(joined_at);
            if membership_duration < self.current.min_membership_duration {
                continue;
            }

            let last_active = self.last_active_wave.get(participant).copied().unwrap_or(0);
            let effective_timeout = self.effective_timeout_for(participant, timeout_waves);

            if self.current_wave.saturating_sub(last_active) > effective_timeout {
                proposals.push(MembershipProposal::Leave {
                    node_key: *participant,
                    reason: LeaveReason::Timeout {
                        last_active_wave: last_active,
                        detected_at_wave: self.current_wave,
                    },
                });
                self.pending_timeout_leaves.insert(*participant);
            }
        }

        proposals
    }

    /// Compute the effective timeout for a participant, accounting for
    /// `rejoin_grace_waves` (recently rejoined nodes get extra time).
    fn effective_timeout_for(&self, participant: &[u8; 32], base_timeout: u64) -> u64 {
        let joined_at = self.joined_at_wave.get(participant).copied().unwrap_or(0);

        // Genesis participants (joined_at == 0) don't get rejoin grace —
        // the grace period is specifically for nodes that were evicted and
        // re-joined, to prevent evict-rejoin-evict oscillation.
        if joined_at == 0 {
            return base_timeout;
        }

        let membership_duration = self.current_wave.saturating_sub(joined_at);

        // If the node rejoined recently (within rejoin_grace_waves), give it
        // extra timeout tolerance to avoid evict-rejoin-evict oscillation.
        if membership_duration < self.current.rejoin_grace_waves {
            base_timeout.saturating_add(self.current.rejoin_grace_waves)
        } else {
            base_timeout
        }
    }

    /// Unfreeze membership changes (call when activity resumes after a partition).
    ///
    /// Should be called when a majority of participants become active again,
    /// indicating the partition has healed.
    pub fn unfreeze_membership(&mut self) {
        self.membership_frozen = false;
    }

    /// Get the last wave in which a participant was active.
    pub fn last_wave_with_block_from(&self, participant: &[u8; 32]) -> Option<u64> {
        self.last_active_wave.get(participant).copied()
    }

    // ─── Query Methods ──────────────────────────────────────────────────────

    /// Get the current participant list (for use in ordering/cordiality checks).
    pub fn participants(&self) -> &[[u8; 32]] {
        &self.current.participants
    }

    /// Get the current threshold.
    pub fn threshold(&self) -> usize {
        self.current.threshold
    }

    /// Get the current constitution version.
    pub fn version(&self) -> u64 {
        self.current.version
    }

    /// Get the timeout threshold in waves.
    pub fn timeout_waves(&self) -> u64 {
        self.current.timeout_waves
    }

    /// Get the current reference group (for use with tau_unified).
    ///
    /// This bridges the Constitution model to the unified blocklace model:
    /// the Constitution's participant set becomes a ReferenceGroup that can
    /// be passed to `tau_unified` for ordering over a shared DAG.
    pub fn as_reference_group(&self) -> crate::ordering::ReferenceGroup {
        crate::ordering::ReferenceGroup::from_constitution(&self.current)
    }

    /// Get the current routes commitment (None = no governance routing).
    pub fn routes_commitment(&self) -> Option<[u8; 32]> {
        self.current.routes_commitment
    }

    /// Check if a given routes commitment matches the current governance state.
    ///
    /// Returns false if there is no routes commitment set (permissive mode).
    pub fn verify_routes_commitment(&self, commitment: &[u8; 32]) -> bool {
        self.current.routes_commitment.as_ref() == Some(commitment)
    }
}

// ─── Helpers ───────────────────────────────────────────────────────────────────

/// Compute the default supermajority threshold for n participants.
///
/// DELEGATES to [`crate::ordering::supermajority_threshold`] — THE one quorum
/// formula (#170 unification): `⌊2n/3⌋ + 1`. `n = 0` returns 1 (fail-closed):
/// an empty constitution can never ratify anything, instead of a vacuous
/// threshold of 0 that an empty vote set would satisfy.
pub fn compute_threshold(n: usize) -> usize {
    crate::ordering::supermajority_threshold(n)
}

// ─── The configuration step bound (the install discipline's refusal gate) ─────
//
// SUBSTRATE: this is a byte-for-byte transcription of the AUTHORED consensus
// rule `Dregg2.Distributed.ConfigBoundary.classifyStep` (metatheory), the same
// pairing `supermajority_threshold` has with `QuorumThreshold.lean`. The Lean
// side carries the soundness theorem (`stepAllowed_quorums_share_honest`): an
// allowed step keeps cross-configuration quorum intersection strictly above the
// Byzantine budget of the smaller roster — DZ (Duan & Zhang, *Foundations of
// Dynamic BFT*) Lemma C.8's counting argument, quantified over all n. Change
// NOTHING here without changing the Lean first.

/// The Byzantine budget `f(n) = ⌊(n−1)/3⌋` (Lean `ConfigBoundary.faultBudget`;
/// `supermajority_threshold n = n − f(n)` for `n ≥ 1`). Below 4 members the
/// budget is ZERO — such a roster tolerates nothing, which is what the roster
/// floor refuses to land on.
pub fn fault_budget(n: usize) -> usize {
    n.saturating_sub(1) / 3
}

/// A configuration step REFUSED BY NAME. Mirrors the refusal constructors of
/// the Lean `ConfigBoundary.StepVerdict` one-for-one. A refused step mutates
/// NOTHING — refusal is the enforcement, and the name is the diagnosis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepRefusal {
    /// More leaves than the roster has members (Lean `refuseLeavesExceedRoster`).
    LeavesExceedRoster { roster: usize, leaves: usize },
    /// The step would leave an EMPTY roster, which could never certify anything
    /// again (Lean `refuseEmptySurvivors`).
    EmptySurvivors {
        roster: usize,
        joins: usize,
        leaves: usize,
    },
    /// The step breaks cross-configuration quorum intersection: the old and new
    /// rosters' supermajority quorums could fail to share an honest member, so
    /// a Byzantine member could equivocate across the boundary (Lean
    /// `refuseIntersectionBound`, DZ Lemma C.8). Concretely refused: 3 joins
    /// from n=4 (the 4→7 step), 3 leaves from n=7, and ⚑ one join + one leave
    /// at n=4 in a single step (the mixed-step sharpening the flat "≤2 changes"
    /// rule misses — `churnStepOk_breaks_at_one_one_from_four`).
    IntersectionBound {
        roster: usize,
        joins: usize,
        leaves: usize,
    },
    /// The step would shrink a BFT-capable roster (`n ≥ 4`) below 4 members —
    /// onto a roster whose fault budget is zero. This is the teeth for the
    /// NON-CONTIGUOUS leave trap (Lean `leaveStepOk_vacuous_at_four_from_seven`:
    /// at n=7, 4 leaves pass the counting bound VACUOUSLY while 3 fail it).
    /// Sub-4 bootstrap rosters are exempt: their safety is vacuous everywhere
    /// and named so, not manufactured.
    RosterFloor { roster: usize, survivors: usize },
}

impl std::fmt::Display for StepRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StepRefusal::LeavesExceedRoster { roster, leaves } => write!(
                f,
                "REFUSED ConfigStep::LeavesExceedRoster: {leaves} leave(s) from a \
                 {roster}-member roster"
            ),
            StepRefusal::EmptySurvivors {
                roster,
                joins,
                leaves,
            } => write!(
                f,
                "REFUSED ConfigStep::EmptySurvivors: {joins} join(s) / {leaves} leave(s) \
                 from a {roster}-member roster would leave nobody"
            ),
            StepRefusal::IntersectionBound {
                roster,
                joins,
                leaves,
            } => write!(
                f,
                "REFUSED ConfigStep::IntersectionBound: {joins} join(s) / {leaves} \
                 leave(s) from a {roster}-member roster breaks cross-configuration \
                 quorum intersection (DZ C.8; Lean ConfigBoundary.churnStepOk)"
            ),
            StepRefusal::RosterFloor { roster, survivors } => write!(
                f,
                "REFUSED ConfigStep::RosterFloor: shrinking a {roster}-member roster to \
                 {survivors} (< 4) lands on a roster that tolerates zero faults"
            ),
        }
    }
}

/// **The configuration step rule** — byte-for-byte the Lean
/// `ConfigBoundary.classifyStep`: a step of `joins` joins and `leaves` leaves
/// from an `n`-member roster either installs (returning the survivor count
/// `n + joins − leaves`) or is refused by the FIRST failing check's name.
/// Checks, in order: leaves only remove existing members; survivors nonempty;
/// the intersection bound; the roster floor.
///
/// The bound counts JOINS as untrusted (a joiner substitutes for an old-roster
/// member in the new quorum). D4's learner phase — state transfer from a quorum
/// of the old roster, with the temporary member provably unable to act — is
/// what would lift the join ceiling; it is NOT built, so joins stay counted.
/// Leaves are bounded permanently: no state transfer can substitute for a
/// departed member's vote (DZ Case (2) is pure counting).
pub fn config_step_allowed(n: usize, joins: usize, leaves: usize) -> Result<usize, StepRefusal> {
    if leaves > n {
        return Err(StepRefusal::LeavesExceedRoster { roster: n, leaves });
    }
    let survivors = n + joins - leaves;
    if survivors < 1 {
        return Err(StepRefusal::EmptySurvivors {
            roster: n,
            joins,
            leaves,
        });
    }
    let smaller = n.min(survivors);
    if crate::ordering::supermajority_threshold(n)
        + crate::ordering::supermajority_threshold(survivors)
        < n + joins + fault_budget(smaller) + 1
    {
        return Err(StepRefusal::IntersectionBound {
            roster: n,
            joins,
            leaves,
        });
    }
    if n >= 4 && survivors < 4 {
        return Err(StepRefusal::RosterFloor {
            roster: n,
            survivors,
        });
    }
    Ok(survivors)
}

// ─── Phase 3: Governance as a Lens ────────────────────────────────────────────

/// How a reference group manages its membership.
///
/// The Constitution becomes OPTIONAL governance layered on top of emergent
/// referencing. This enum captures the three modes of membership management.
#[derive(Clone, Debug)]
pub enum GovernanceMode {
    /// Governed: constitutional vote required to join/leave.
    /// This is the current behavior — preserved for DAOs, formal organizations.
    Constitutional { manager: ConstitutionManager },
    /// Permissionless: anyone can join by referencing, leave by stopping.
    /// No votes, no threshold for admission. Still has timeout-based cleanup.
    /// Good for open communities, public goods, permissionless networks.
    Open {
        /// Timeout: if a strand stops referencing for N waves, remove from group
        timeout_waves: u64,
    },
    /// Invite-only: existing members can unilaterally add new members.
    /// No threshold vote needed — any single member can invite.
    /// Good for small teams, friend groups.
    InviteOnly {
        /// Current members (managed by invitation, not vote)
        members: Vec<[u8; 32]>,
        /// Timeout: if a strand stops producing for N waves, remove from group
        timeout_waves: u64,
    },
}

/// The result of processing a membership event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipChange {
    /// A new member was added to the group.
    Added([u8; 32]),
    /// A member was removed from the group.
    Removed([u8; 32]),
    /// No change occurred.
    NoChange,
    /// The change requires a constitutional vote (only for Constitutional mode).
    RequiresVote(MembershipProposal),
}

/// A reference group with optional governance.
///
/// This is the unified type that replaces the old "federation" concept.
/// It wraps a `ReferenceGroup` (the set of strands running tau) with a
/// governance mode (how membership is managed) and a subscription (for
/// dissemination filtering).
#[derive(Clone, Debug)]
pub struct GovernedReferenceGroup {
    /// The current reference group (who we run tau over).
    pub group: crate::ordering::ReferenceGroup,
    /// How membership is managed.
    pub governance: GovernanceMode,
    /// The subscription this group uses for dissemination.
    pub subscription: crate::dissemination::Subscription,
    /// Optional name (for discovery in namespace).
    pub name: Option<String>,
    /// Last active wave per member (for timeout tracking in Open/InviteOnly modes).
    last_active: std::collections::HashMap<[u8; 32], u64>,
}

impl GovernedReferenceGroup {
    /// Create a governed group (traditional federation behavior).
    ///
    /// Membership changes require constitutional vote. Preserves all existing
    /// ConstitutionManager behavior.
    pub fn constitutional(participants: Vec<[u8; 32]>, timeout_waves: u64) -> Self {
        let constitution = Constitution::new(participants.clone(), timeout_waves);
        let manager = ConstitutionManager::new(constitution);
        let group = crate::ordering::ReferenceGroup::new(participants.clone(), timeout_waves);
        let subscription = crate::dissemination::Subscription::from_reference_group(&group);
        let last_active = participants.iter().map(|k| (*k, 0u64)).collect();
        GovernedReferenceGroup {
            group,
            governance: GovernanceMode::Constitutional { manager },
            subscription,
            name: None,
            last_active,
        }
    }

    /// Create an open group (permissionless).
    ///
    /// Anyone can join by referencing group members. Members are removed
    /// after `timeout_waves` of inactivity. No proposals, no votes.
    pub fn open(initial_members: Vec<[u8; 32]>, timeout_waves: u64) -> Self {
        let group = crate::ordering::ReferenceGroup::new(initial_members.clone(), timeout_waves);
        let subscription = crate::dissemination::Subscription::from_reference_group(&group);
        let last_active = initial_members.iter().map(|k| (*k, 0u64)).collect();
        GovernedReferenceGroup {
            group,
            governance: GovernanceMode::Open { timeout_waves },
            subscription,
            name: None,
            last_active,
        }
    }

    /// Create an invite-only group.
    ///
    /// Any existing member can unilaterally invite a new member. Removal
    /// happens via timeout (inactivity).
    pub fn invite_only(founder: [u8; 32], timeout_waves: u64) -> Self {
        let members = vec![founder];
        let group = crate::ordering::ReferenceGroup::new(members.clone(), timeout_waves);
        let subscription = crate::dissemination::Subscription::from_reference_group(&group);
        let last_active = std::collections::HashMap::from([(founder, 0u64)]);
        GovernedReferenceGroup {
            group,
            governance: GovernanceMode::InviteOnly {
                members: members.clone(),
                timeout_waves,
            },
            subscription,
            name: None,
            last_active,
        }
    }

    /// Process a potential new member (behavior depends on governance mode).
    ///
    /// - **Open**: auto-adds the new strand.
    /// - **InviteOnly**: requires `inviter` to be a current member.
    /// - **Constitutional**: returns `RequiresVote` with a Join proposal.
    pub fn on_new_reference(&mut self, new_strand: [u8; 32], wave: u64) -> MembershipChange {
        // Already a member? No change.
        if self.group.is_member(&new_strand) {
            return MembershipChange::NoChange;
        }

        match &mut self.governance {
            GovernanceMode::Open { .. } => {
                // Auto-add: permissionless join.
                self.group.participants.push(new_strand);
                self.group.participants.sort();
                self.group.threshold =
                    crate::ordering::supermajority_threshold(self.group.participants.len());
                self.subscription.subscribe(new_strand);
                self.last_active.insert(new_strand, wave);
                MembershipChange::Added(new_strand)
            }
            GovernanceMode::InviteOnly { members, .. } => {
                // In invite-only mode, on_new_reference is used when an existing
                // member explicitly invites (the caller must verify the inviter).
                // For the raw "someone referenced us" case, this is a no-op.
                // Use `invite()` method instead for explicit invitations.
                // Here we treat it as a no-op (non-member referencing doesn't auto-add).
                let _ = members;
                MembershipChange::NoChange
            }
            GovernanceMode::Constitutional { .. } => {
                // Requires a vote. Return the proposal for the caller to submit.
                MembershipChange::RequiresVote(MembershipProposal::Join {
                    node_key: new_strand,
                    justification: vec![],
                })
            }
        }
    }

    /// Invite a member (for InviteOnly mode).
    ///
    /// The `inviter` must be a current member. Returns `Added` if successful,
    /// `NoChange` if the inviter is not a member or the strand is already a member.
    pub fn invite(
        &mut self,
        inviter: &[u8; 32],
        new_strand: [u8; 32],
        wave: u64,
    ) -> MembershipChange {
        if self.group.is_member(&new_strand) {
            return MembershipChange::NoChange;
        }

        match &mut self.governance {
            GovernanceMode::InviteOnly { members, .. } => {
                if !members.contains(inviter) {
                    return MembershipChange::NoChange;
                }
                // Inviter is valid, add the new member.
                members.push(new_strand);
                members.sort();
                self.group.participants.push(new_strand);
                self.group.participants.sort();
                self.group.threshold =
                    crate::ordering::supermajority_threshold(self.group.participants.len());
                self.subscription.subscribe(new_strand);
                self.last_active.insert(new_strand, wave);
                MembershipChange::Added(new_strand)
            }
            _ => MembershipChange::NoChange,
        }
    }

    /// Process inactivity (behavior depends on governance mode).
    ///
    /// If a strand has been inactive for longer than the timeout, it is removed.
    /// - **Open**: auto-removes after timeout.
    /// - **InviteOnly**: auto-removes after timeout.
    /// - **Constitutional**: returns `RequiresVote` with a Leave proposal.
    pub fn on_inactivity(
        &mut self,
        strand: [u8; 32],
        last_active: u64,
        current_wave: u64,
    ) -> MembershipChange {
        if !self.group.is_member(&strand) {
            return MembershipChange::NoChange;
        }

        let timeout = match &self.governance {
            GovernanceMode::Open { timeout_waves } => *timeout_waves,
            GovernanceMode::InviteOnly { timeout_waves, .. } => *timeout_waves,
            GovernanceMode::Constitutional { .. } => {
                // Constitutional mode uses its own timeout logic.
                // Return a proposal for removal.
                if current_wave.saturating_sub(last_active) > 0 {
                    return MembershipChange::RequiresVote(MembershipProposal::Leave {
                        node_key: strand,
                        reason: LeaveReason::Timeout {
                            last_active_wave: last_active,
                            detected_at_wave: current_wave,
                        },
                    });
                }
                return MembershipChange::NoChange;
            }
        };

        if current_wave.saturating_sub(last_active) > timeout {
            // Remove the inactive strand.
            self.group.participants.retain(|k| k != &strand);
            self.group.threshold =
                crate::ordering::supermajority_threshold(self.group.participants.len());
            self.subscription.unsubscribe(&strand);
            self.last_active.remove(&strand);

            // Also remove from InviteOnly's member list if applicable.
            if let GovernanceMode::InviteOnly { members, .. } = &mut self.governance {
                members.retain(|k| k != &strand);
            }

            MembershipChange::Removed(strand)
        } else {
            MembershipChange::NoChange
        }
    }

    /// Record activity from a member at a given wave.
    pub fn record_activity(&mut self, strand: &[u8; 32], wave: u64) {
        if let Some(entry) = self.last_active.get_mut(strand)
            && wave > *entry
        {
            *entry = wave;
        }
    }

    /// Get the last active wave for a member.
    pub fn last_active_wave(&self, strand: &[u8; 32]) -> Option<u64> {
        self.last_active.get(strand).copied()
    }

    /// Get the current ReferenceGroup (for tau_unified).
    pub fn reference_group(&self) -> &crate::ordering::ReferenceGroup {
        &self.group
    }

    /// Get the subscription (for dissemination filtering).
    pub fn subscription(&self) -> &crate::dissemination::Subscription {
        &self.subscription
    }

    /// Run tau over this group's subset of the blocklace.
    pub fn finalize(
        &self,
        blocklace: &crate::Blocklace,
        config: &crate::ordering::OrderingConfig,
    ) -> Vec<crate::BlockId> {
        crate::ordering::tau_unified(blocklace, &self.group, config)
    }

    /// Get the current member count.
    pub fn member_count(&self) -> usize {
        self.group.participants.len()
    }

    /// Check if a strand is a member.
    pub fn is_member(&self, strand: &[u8; 32]) -> bool {
        self.group.is_member(strand)
    }
}

/// Bridge: upgrade an existing ConstitutionManager to a GovernedReferenceGroup.
impl ConstitutionManager {
    /// Upgrade to a GovernedReferenceGroup (preserves all existing behavior).
    ///
    /// The resulting group uses `GovernanceMode::Constitutional`, meaning
    /// all membership changes still require a threshold vote.
    pub fn into_governed_group(self) -> GovernedReferenceGroup {
        let participants = self.current.participants.clone();
        let timeout_waves = self.current.timeout_waves;
        let group = crate::ordering::ReferenceGroup::new(participants.clone(), timeout_waves);
        let subscription = crate::dissemination::Subscription::from_reference_group(&group);
        let last_active = participants.iter().map(|k| (*k, 0u64)).collect();
        GovernedReferenceGroup {
            group,
            governance: GovernanceMode::Constitutional { manager: self },
            subscription,
            name: None,
            last_active,
        }
    }
}

// ─── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn make_node_key(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn make_participants(n: u8) -> Vec<[u8; 32]> {
        (1..=n).map(|i| make_node_key(i)).collect()
    }

    /// Default timeout in waves for testing.
    const TEST_TIMEOUT_WAVES: u64 = 10;

    // ─── Constitution basics ────────────────────────────────────────────────

    #[test]
    fn constitution_new_computes_threshold() {
        let c = Constitution::new(make_participants(4), TEST_TIMEOUT_WAVES);
        assert_eq!(c.threshold, 3); // floor(2*4/3) + 1 = 3
        assert_eq!(c.participant_count(), 4);
        assert_eq!(c.version, 0);
        assert_eq!(c.timeout_waves, TEST_TIMEOUT_WAVES);
    }

    #[test]
    fn constitution_threshold_values() {
        assert_eq!(compute_threshold(3), 3); // 2*3/3 + 1 = 3
        assert_eq!(compute_threshold(4), 3); // 2*4/3 + 1 = 3
        assert_eq!(compute_threshold(7), 5); // 2*7/3 + 1 = 5
        assert_eq!(compute_threshold(10), 7); // 2*10/3 + 1 = 7
        assert_eq!(compute_threshold(1), 1); // 2*1/3 + 1 = 1
        assert_eq!(compute_threshold(0), 1); // empty constitution: fail-closed
        // THE one quorum formula (#170): the constitution threshold IS the
        // blocklace supermajority — no second formula to drift.
        for n in 0..=64 {
            assert_eq!(
                compute_threshold(n),
                crate::ordering::supermajority_threshold(n),
                "constitution threshold diverges from the unified quorum at n={n}"
            );
        }
    }

    // ─── Propose join → threshold approvals → member added ──────────────────

    #[test]
    fn propose_join_threshold_approvals_member_added() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // threshold for 3 participants = 3
        assert_eq!(mgr.threshold(), 3);

        // Propose adding node 4
        let new_node = make_node_key(4);
        let proposal = MembershipProposal::Join {
            node_key: new_node,
            justification: b"stake proof".to_vec(),
        };
        let proposal_block = BlockId([0xAA; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        // Vote from participant 1
        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        let result = mgr.submit_vote(&vote, make_node_key(1));
        assert_eq!(result, None); // Not yet passed

        // Vote from participant 2
        let result = mgr.submit_vote(&vote, make_node_key(2));
        assert_eq!(result, None); // Still not passed (need 3)

        // Vote from participant 3 -- reaches threshold
        let result = mgr.submit_vote(&vote, make_node_key(3));
        assert_eq!(result, Some(proposal_block));

        // Apply (simulating finality confirmation)
        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert!(mgr.current.is_participant(&new_node));
        assert_eq!(mgr.current.participant_count(), 4);
        assert_eq!(mgr.current.version, 1);
        // Threshold updated: floor(2*4/3) + 1 = 3
        assert_eq!(mgr.current.threshold, 3);
    }

    // ─── Propose leave → threshold approvals → member removed ───────────────

    #[test]
    fn propose_leave_threshold_approvals_member_removed() {
        // Five members: a leave from four is refused by the roster floor
        // (`ratified_leave_from_four_is_refused_by_name_and_mutates_nothing`),
        // so the smallest roster a member can leave is five.
        let participants = make_participants(5);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // threshold for 5 = 4
        assert_eq!(mgr.threshold(), 4);

        let leaving_node = make_node_key(4);
        let proposal = MembershipProposal::Leave {
            node_key: leaving_node,
            reason: LeaveReason::Voluntary,
        };
        let proposal_block = BlockId([0xBB; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };

        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        assert_eq!(mgr.submit_vote(&vote, make_node_key(3)), None);
        let result = mgr.submit_vote(&vote, make_node_key(5));
        assert_eq!(result, Some(proposal_block));

        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert!(!mgr.current.is_participant(&leaving_node));
        assert_eq!(mgr.current.participant_count(), 4);
        assert_eq!(mgr.current.version, 1);
    }

    // ─── H-rule: amend threshold requires max(current, new) votes ───────────

    #[test]
    fn h_rule_amend_threshold_from_2_to_3_requires_3_votes() {
        // Start with 4 participants, threshold manually set to 2.
        let mut constitution = Constitution::new(make_participants(4), TEST_TIMEOUT_WAVES);
        constitution.threshold = 2; // Override default for this test

        let mut mgr = ConstitutionManager::new(constitution);
        assert_eq!(mgr.threshold(), 2);

        let proposal = MembershipProposal::AmendThreshold { new_threshold: 3 };

        // H-rule: max(2, 3) = 3 votes needed
        assert_eq!(mgr.current.required_votes_for(&proposal), 3);

        let proposal_block = BlockId([0xCC; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };

        // 2 votes not enough
        mgr.submit_vote(&vote, make_node_key(1));
        let result = mgr.submit_vote(&vote, make_node_key(2));
        assert_eq!(result, None);

        // 3rd vote passes
        let result = mgr.submit_vote(&vote, make_node_key(3));
        assert_eq!(result, Some(proposal_block));

        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.current.threshold, 3);
        assert_eq!(mgr.current.version, 1);
    }

    #[test]
    fn h_rule_amend_threshold_from_3_to_2_also_requires_3_votes() {
        // Start with 4 participants, threshold = 3 (default)
        let constitution = Constitution::new(make_participants(4), TEST_TIMEOUT_WAVES);
        let mut mgr = ConstitutionManager::new(constitution);
        assert_eq!(mgr.threshold(), 3);

        let proposal = MembershipProposal::AmendThreshold { new_threshold: 2 };

        // H-rule: max(3, 2) = 3 votes needed (current threshold wins)
        assert_eq!(mgr.current.required_votes_for(&proposal), 3);

        let proposal_block = BlockId([0xDD; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };

        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        let result = mgr.submit_vote(&vote, make_node_key(3));
        assert_eq!(result, Some(proposal_block));

        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.current.threshold, 2);
    }

    // ─── The configuration step bound (ConfigBoundary transcription) ────────

    /// The TRANSCRIPTION DIFFERENTIAL: `config_step_allowed` pins the exact
    /// golden verdicts of the Lean-authored rule (the named `example` rows of
    /// `Dregg2.Distributed.ConfigBoundary`). The Lean carries the soundness
    /// theorem (`stepAllowed_quorums_share_honest`); this pins the Rust
    /// transcription to it, both polarities, refusals BY NAME.
    #[test]
    fn config_step_allowed_matches_lean_goldens() {
        use super::StepRefusal as R;
        // Allowed steps (Lean `stepAllowed … = true`).
        assert_eq!(config_step_allowed(4, 1, 0), Ok(5)); // 4→5 join
        assert_eq!(config_step_allowed(4, 2, 0), Ok(6)); // 4→6 join (tight)
        assert_eq!(config_step_allowed(7, 2, 0), Ok(9)); // 7→9 join (tight)
        assert_eq!(config_step_allowed(6, 4, 0), Ok(10)); // 3∣n admits MORE than 2
        assert_eq!(config_step_allowed(5, 0, 1), Ok(4)); // 5→4 leave
        assert_eq!(config_step_allowed(1, 1, 0), Ok(2)); // solo growth
        assert_eq!(config_step_allowed(1, 2, 0), Ok(3));
        assert_eq!(config_step_allowed(3, 2, 0), Ok(5)); // bootstrap 3→5
        assert_eq!(config_step_allowed(0, 1, 0), Ok(1)); // genesis from empty

        // Refused steps, BY NAME (Lean `classifyStep … = .refuse…`).
        assert_eq!(
            config_step_allowed(4, 3, 0), // 4→7: DZ's own broken example
            Err(R::IntersectionBound {
                roster: 4,
                joins: 3,
                leaves: 0
            })
        );
        assert_eq!(
            config_step_allowed(7, 3, 0), // 7→10
            Err(R::IntersectionBound {
                roster: 7,
                joins: 3,
                leaves: 0
            })
        );
        assert_eq!(
            config_step_allowed(7, 0, 3), // the NON-CONTIGUOUS leave failure
            Err(R::IntersectionBound {
                roster: 7,
                joins: 0,
                leaves: 3
            })
        );
        assert_eq!(
            config_step_allowed(7, 0, 4), // vacuously-"safe" endpoint: floor refuses
            Err(R::RosterFloor {
                roster: 7,
                survivors: 3
            })
        );
        assert_eq!(
            config_step_allowed(4, 0, 1), // 4→3: the floor's headline case
            Err(R::RosterFloor {
                roster: 4,
                survivors: 3
            })
        );
        assert_eq!(
            // ⚑ the MIXED-step sharpening: one join + one leave at n=4 — "two
            // changes" — breaks intersection (churnStepOk_breaks_at_one_one_from_four).
            config_step_allowed(4, 1, 1),
            Err(R::IntersectionBound {
                roster: 4,
                joins: 1,
                leaves: 1
            })
        );
        assert_eq!(
            config_step_allowed(1, 0, 1), // solo leaving itself
            Err(R::EmptySurvivors {
                roster: 1,
                joins: 0,
                leaves: 1
            })
        );
        assert_eq!(
            config_step_allowed(2, 0, 3),
            Err(R::LeavesExceedRoster {
                roster: 2,
                leaves: 3
            })
        );
    }

    /// Refusal at the APPLY level, both poles, mutation asserted present: a
    /// ratified Leave from n=4 gathers a real quorum (the mutation is live —
    /// at n=5, with the one further approval that roster needs, it installs), and the roster floor refuses it
    /// by name with NOTHING mutated; `Err` is distinct from the not-passed
    /// `Ok(false)`, so a refused proposal can never read as "still pending".
    #[test]
    fn ratified_leave_from_four_is_refused_by_name_and_mutates_nothing() {
        let participants = make_participants(4);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);
        assert_eq!(mgr.threshold(), 3);

        let leave = MembershipProposal::Leave {
            node_key: make_node_key(4),
            reason: LeaveReason::Voluntary,
        };
        let proposal_block = BlockId([0xB4; 32]);
        mgr.submit_proposal(proposal_block, leave);
        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        let passed = mgr.submit_vote(&vote, make_node_key(3));
        // MUTATION PRESENT: the proposal genuinely passed its vote.
        assert_eq!(passed, Some(proposal_block), "the leave IS ratified");

        // THE REFUSAL POLE: named, and nothing moves.
        assert_eq!(
            mgr.apply_if_passed(&proposal_block),
            Err(StepRefusal::RosterFloor {
                roster: 4,
                survivors: 3
            })
        );
        assert_eq!(mgr.participants().len(), 4, "refusal mutates nothing");
        assert_eq!(mgr.version(), 0, "no version advance on refusal");
        assert!(mgr.current.is_participant(&make_node_key(4)));

        // THE INSTALL POLE (the same shape, one step wider): admit a 5th
        // member first, and the identical leave now installs — join-then-leave
        // is the replacement flow the floor forces.
        let join = MembershipProposal::Join {
            node_key: make_node_key(5),
            justification: vec![],
        };
        let join_block = BlockId([0xB5; 32]);
        mgr.submit_proposal(join_block, join);
        let jvote = MembershipVote {
            proposal_block: join_block,
            approve: true,
        };
        mgr.submit_vote(&jvote, make_node_key(1));
        mgr.submit_vote(&jvote, make_node_key(2));
        mgr.submit_vote(&jvote, make_node_key(3));
        assert!(
            mgr.apply_if_passed(&join_block).unwrap(),
            "the join installs"
        );
        assert_eq!(mgr.participants().len(), 5);

        // The join raised the threshold to 4, so the leave's three approvals
        // no longer ratify it: not passed, which is `Ok(false)` and not the
        // floor's `Err`. One more approval (the new member's) ratifies it, and
        // at n=5 the apply clears the floor and installs.
        assert_eq!(mgr.threshold(), 4);
        assert_eq!(mgr.apply_if_passed(&proposal_block), Ok(false));
        assert_eq!(
            mgr.submit_vote(&vote, make_node_key(5)),
            Some(proposal_block)
        );
        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.participants().len(), 4);
        assert!(!mgr.current.is_participant(&make_node_key(4)));
    }

    // ─── Constitution versioning ────────────────────────────────────────────

    #[test]
    fn constitution_versioning_history_preserved() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // Version 0: initial 3 participants
        assert_eq!(mgr.version(), 0);
        let v0 = mgr.constitution_at_version(0).unwrap().clone();
        assert_eq!(v0.participant_count(), 3);

        // Add a member (simulating full flow)
        let new_node = make_node_key(4);
        let proposal = MembershipProposal::Join {
            node_key: new_node,
            justification: vec![],
        };
        let proposal_block = BlockId([0xEE; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block);

        // Version 1: 4 participants
        assert_eq!(mgr.version(), 1);
        let v1 = mgr.constitution_at_version(1).unwrap();
        assert_eq!(v1.participant_count(), 4);

        // Old version still accessible
        let v0_again = mgr.constitution_at_version(0).unwrap();
        assert_eq!(v0_again.participant_count(), 3);
    }

    // ─── Non-participants cannot vote ───────────────────────────────────────

    #[test]
    fn non_participant_vote_ignored() {
        let participants = make_participants(3);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let proposal = MembershipProposal::Join {
            node_key: make_node_key(4),
            justification: vec![],
        };
        let proposal_block = BlockId([0xFF; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        // Non-participant tries to vote
        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        let result = mgr.submit_vote(&vote, make_node_key(99));
        assert_eq!(result, None);
        assert_eq!(mgr.votes.approval_count(&proposal_block), 0);
    }

    // ─── Double-application prevention ──────────────────────────────────────

    #[test]
    fn proposal_cannot_be_applied_twice() {
        let participants = make_participants(3);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let proposal = MembershipProposal::Join {
            node_key: make_node_key(4),
            justification: vec![],
        };
        let proposal_block = BlockId([0x11; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));

        // First application succeeds.
        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.current.participant_count(), 4);

        // Second application fails (already applied).
        assert!(!mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.current.participant_count(), 4); // unchanged
    }

    // ─── Duplicate vote ignored ─────────────────────────────────────────────

    #[test]
    fn duplicate_vote_from_same_participant_counted_once() {
        let participants = make_participants(3);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let proposal = MembershipProposal::Join {
            node_key: make_node_key(4),
            justification: vec![],
        };
        let proposal_block = BlockId([0x22; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };

        // Same participant votes multiple times
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(1));

        // Only counted once
        assert_eq!(mgr.votes.approval_count(&proposal_block), 1);
    }

    // ─── Integration: membership change with wave boundary ──────────────────

    #[test]
    fn membership_change_updates_participant_list_for_ordering() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // Verify initial state matches what ordering uses
        assert_eq!(mgr.participants().len(), 3);

        // After adding a member, ordering should use new list
        let new_node = make_node_key(4);
        let proposal = MembershipProposal::Join {
            node_key: new_node,
            justification: vec![],
        };
        let proposal_block = BlockId([0x33; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block);

        // Now ordering should use 4 participants
        assert_eq!(mgr.participants().len(), 4);
        assert!(mgr.participants().contains(&new_node));

        // Wave leader computation uses the new set
        let leader = crate::ordering::wave_leader(0, mgr.participants());
        assert!(mgr.current.is_participant(&leader));
    }

    // ─── n=1: instant finality, single participant ──────────────────────────

    #[test]
    fn n1_single_participant_threshold_is_one() {
        let participants = vec![make_node_key(1)];
        let mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        // With n=1, threshold = floor(2*1/3) + 1 = 1
        assert_eq!(mgr.threshold(), 1);
        assert_eq!(mgr.participants().len(), 1);

        // The single participant is always the leader
        let leader = crate::ordering::wave_leader(0, mgr.participants());
        assert_eq!(leader, make_node_key(1));
    }

    // ─── n=1 -> n=2: peer joins, threshold increases ────────────────────────

    #[test]
    fn n1_to_n2_peer_joins_threshold_increases() {
        let participants = vec![make_node_key(1)];
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        assert_eq!(mgr.threshold(), 1);

        // Propose adding node 2
        let new_node = make_node_key(2);
        let proposal = MembershipProposal::Join {
            node_key: new_node,
            justification: b"hello".to_vec(),
        };
        let proposal_block = BlockId([0x50; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        // With threshold=1, a single vote from node 1 suffices
        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        let result = mgr.submit_vote(&vote, make_node_key(1));
        assert_eq!(result, Some(proposal_block));

        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.participants().len(), 2);
        // threshold for 2 = floor(2*2/3) + 1 = 2
        assert_eq!(mgr.threshold(), 2);
    }

    // ─── n=2 -> n=1: peer times out, threshold decreases ────────────────────

    #[test]
    fn n2_to_n1_peer_timeout_decreases_threshold() {
        let participants = make_participants(2);
        let mut mgr = ConstitutionManager::from_participants(participants, 5); // 5-wave timeout

        assert_eq!(mgr.threshold(), 2);
        assert_eq!(mgr.participants().len(), 2);

        // Node 1 is active, node 2 is silent
        mgr.record_activity(&make_node_key(1), 1);
        mgr.record_activity(&make_node_key(1), 2);
        mgr.record_activity(&make_node_key(1), 3);

        // Advance to wave 7 (node 2 last active at wave 0, timeout=5, so 7-0=7 > 5)
        let proposals = mgr.advance_wave(7);
        assert_eq!(proposals.len(), 1);

        match &proposals[0] {
            MembershipProposal::Leave { node_key, reason } => {
                assert_eq!(*node_key, make_node_key(2));
                match reason {
                    LeaveReason::Timeout {
                        last_active_wave,
                        detected_at_wave,
                    } => {
                        assert_eq!(*last_active_wave, 0);
                        assert_eq!(*detected_at_wave, 7);
                    }
                    _ => panic!("expected Timeout reason"),
                }
            }
            _ => panic!("expected Leave proposal"),
        }

        // Submit and approve the timeout-leave proposal
        let proposal_block = BlockId([0x60; 32]);
        mgr.submit_proposal(proposal_block, proposals[0].clone());

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        // Both participants can vote (threshold=2)
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2)); // even the timed-out node can vote

        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
        assert_eq!(mgr.participants().len(), 1);
        // Back to threshold=1
        assert_eq!(mgr.threshold(), 1);
    }

    // ─── Timeout: duplicate proposal not generated ──────────────────────────

    #[test]
    fn timeout_not_proposed_twice() {
        let participants = make_participants(2);
        let mut mgr = ConstitutionManager::from_participants(participants, 3);

        // Node 1 stays active; node 2 is silent
        mgr.record_activity(&make_node_key(1), 4);

        // Advance past timeout for node 2 (last active=0, wave=5, 5-0=5 > 3)
        let proposals1 = mgr.advance_wave(5);
        assert_eq!(proposals1.len(), 1);

        // Advance again - should NOT re-propose node 2
        mgr.record_activity(&make_node_key(1), 5);
        let proposals2 = mgr.advance_wave(6);
        assert_eq!(proposals2.len(), 0);
    }

    // ─── Returning node: timed-out node reconnects and rejoins ──────────────

    #[test]
    fn returning_node_can_rejoin() {
        let participants = make_participants(2);
        let mut mgr = ConstitutionManager::from_participants(participants, 3);

        // Node 1 stays active; node 2 is silent
        mgr.record_activity(&make_node_key(1), 4);
        let proposals = mgr.advance_wave(5);
        assert_eq!(proposals.len(), 1);

        // Apply the leave (simulating full vote + finality)
        let leave_block = BlockId([0x70; 32]);
        mgr.submit_proposal(leave_block, proposals[0].clone());
        let vote = MembershipVote {
            proposal_block: leave_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        let _ = mgr.apply_if_passed(&leave_block);

        assert_eq!(mgr.participants().len(), 1);
        assert!(!mgr.current.is_participant(&make_node_key(2)));

        // Node 2 comes back and proposes Join
        let rejoin_proposal = MembershipProposal::Join {
            node_key: make_node_key(2),
            justification: b"I'm back".to_vec(),
        };
        let rejoin_block = BlockId([0x71; 32]);
        mgr.submit_proposal(rejoin_block, rejoin_proposal);

        // With threshold=1, a single vote from node 1 suffices
        let vote2 = MembershipVote {
            proposal_block: rejoin_block,
            approve: true,
        };
        let result = mgr.submit_vote(&vote2, make_node_key(1));
        assert_eq!(result, Some(rejoin_block));

        assert!(mgr.apply_if_passed(&rejoin_block).unwrap());
        assert_eq!(mgr.participants().len(), 2);
        assert!(mgr.current.is_participant(&make_node_key(2)));
    }

    // ─── H-rule: can't lower threshold without new threshold's approval ─────

    // ─── Timeout disabled when timeout_waves = 0 ────────────────────────────

    #[test]
    fn timeout_disabled_when_zero() {
        let participants = make_participants(3);
        let mut mgr = ConstitutionManager::from_participants(participants, 0);

        // Even after many waves with no activity, no proposals generated
        let proposals = mgr.advance_wave(100);
        assert!(proposals.is_empty());
    }

    // ─── Activity resets pending timeout ────────────────────────────────────

    #[test]
    fn activity_clears_pending_timeout() {
        let participants = make_participants(2);
        let mut mgr = ConstitutionManager::from_participants(participants, 3);

        // Node 1 stays active; node 2 is silent
        mgr.record_activity(&make_node_key(1), 4);

        // Node 2 times out, proposal generated
        let proposals = mgr.advance_wave(5);
        assert_eq!(proposals.len(), 1);

        // Node 2 comes back alive! Record activity.
        mgr.record_activity(&make_node_key(2), 6);

        // Now if we advance further, node 2 should NOT be re-proposed
        // (their pending_timeout_leave was cleared by record_activity)
        mgr.record_activity(&make_node_key(1), 7);
        let proposals2 = mgr.advance_wave(7);
        assert!(proposals2.is_empty());

        // And even much later, they shouldn't be proposed (last active = wave 6)
        mgr.record_activity(&make_node_key(1), 8);
        mgr.record_activity(&make_node_key(2), 8);
        let proposals3 = mgr.advance_wave(8);
        assert!(proposals3.is_empty());
    }

    // ─── Route Governance ───────────────────────────────────────────────────

    #[test]
    fn route_amendment_propose_vote_passes_at_threshold() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // threshold for 3 participants = 3
        assert_eq!(mgr.threshold(), 3);

        let new_routes = [0xAB; 32];
        let proposal = MembershipProposal::AmendRoutes {
            new_routes_commitment: new_routes,
            description: "add /api/v2 routes".to_string(),
        };
        let proposal_block = BlockId([0xA0; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };

        // Two votes not enough
        mgr.submit_vote(&vote, make_node_key(1));
        let result = mgr.submit_vote(&vote, make_node_key(2));
        assert_eq!(result, None);

        // Third vote passes (threshold = 3)
        let result = mgr.submit_vote(&vote, make_node_key(3));
        assert_eq!(result, Some(proposal_block));

        // Apply
        assert!(mgr.apply_if_passed(&proposal_block).unwrap());
    }

    #[test]
    fn route_commitment_updates_after_passage() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // Initially no routes commitment
        assert_eq!(mgr.routes_commitment(), None);

        let new_routes = [0xCD; 32];
        let proposal = MembershipProposal::AmendRoutes {
            new_routes_commitment: new_routes,
            description: "initial routing table".to_string(),
        };
        let proposal_block = BlockId([0xA1; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block);

        // Routes commitment updated
        assert_eq!(mgr.routes_commitment(), Some(new_routes));
        assert_eq!(mgr.current.routes_commitment, Some(new_routes));
    }

    #[test]
    fn route_history_preserved_in_constitution_history() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // Version 0: no routes
        assert_eq!(mgr.version(), 0);
        let v0 = mgr.constitution_at_version(0).unwrap();
        assert_eq!(v0.routes_commitment, None);

        // Amend routes
        let routes_v1 = [0xDE; 32];
        let proposal = MembershipProposal::AmendRoutes {
            new_routes_commitment: routes_v1,
            description: "v1 routes".to_string(),
        };
        let proposal_block = BlockId([0xA2; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block);

        // Version 1: routes set
        assert_eq!(mgr.version(), 1);
        let v1 = mgr.constitution_at_version(1).unwrap();
        assert_eq!(v1.routes_commitment, Some(routes_v1));

        // Original version still shows None
        let v0_again = mgr.constitution_at_version(0).unwrap();
        assert_eq!(v0_again.routes_commitment, None);

        // Amend routes again
        let routes_v2 = [0xEF; 32];
        let proposal2 = MembershipProposal::AmendRoutes {
            new_routes_commitment: routes_v2,
            description: "v2 routes".to_string(),
        };
        let proposal_block2 = BlockId([0xA3; 32]);
        mgr.submit_proposal(proposal_block2, proposal2);

        let vote2 = MembershipVote {
            proposal_block: proposal_block2,
            approve: true,
        };
        mgr.submit_vote(&vote2, make_node_key(1));
        mgr.submit_vote(&vote2, make_node_key(2));
        mgr.submit_vote(&vote2, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block2);

        assert_eq!(mgr.version(), 2);
        let v2 = mgr.constitution_at_version(2).unwrap();
        assert_eq!(v2.routes_commitment, Some(routes_v2));

        // v1 still preserved
        let v1_again = mgr.constitution_at_version(1).unwrap();
        assert_eq!(v1_again.routes_commitment, Some(routes_v1));
    }

    #[test]
    fn verify_routes_commitment_returns_true_false_correctly() {
        let participants = make_participants(3);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        let commitment = [0x42; 32];
        let wrong_commitment = [0x99; 32];

        // Before any route is set, verify returns false for anything
        assert!(!mgr.verify_routes_commitment(&commitment));
        assert!(!mgr.verify_routes_commitment(&wrong_commitment));

        // Set routes
        let proposal = MembershipProposal::AmendRoutes {
            new_routes_commitment: commitment,
            description: "set routes".to_string(),
        };
        let proposal_block = BlockId([0xA4; 32]);
        mgr.submit_proposal(proposal_block, proposal);

        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        mgr.submit_vote(&vote, make_node_key(1));
        mgr.submit_vote(&vote, make_node_key(2));
        mgr.submit_vote(&vote, make_node_key(3));
        let _ = mgr.apply_if_passed(&proposal_block);

        // Now verify returns true for the correct commitment
        assert!(mgr.verify_routes_commitment(&commitment));
        // And false for a wrong commitment
        assert!(!mgr.verify_routes_commitment(&wrong_commitment));
    }

    // ─── Phase 3: GovernedReferenceGroup Tests ─────────────────────────────

    #[test]
    fn constitutional_mode_preserves_existing_behavior() {
        // Constitutional mode should require a vote for join.
        let participants = make_participants(3);
        let mut grp =
            GovernedReferenceGroup::constitutional(participants.clone(), TEST_TIMEOUT_WAVES);

        assert_eq!(grp.member_count(), 3);
        assert!(grp.is_member(&make_node_key(1)));
        assert!(!grp.is_member(&make_node_key(4)));

        // Trying to add a new strand via on_new_reference should return RequiresVote.
        let change = grp.on_new_reference(make_node_key(4), 1);
        match change {
            MembershipChange::RequiresVote(MembershipProposal::Join { node_key, .. }) => {
                assert_eq!(node_key, make_node_key(4));
            }
            _ => panic!(
                "constitutional mode should require a vote, got {:?}",
                change
            ),
        }

        // Member count unchanged.
        assert_eq!(grp.member_count(), 3);
        assert!(!grp.is_member(&make_node_key(4)));
    }

    #[test]
    fn open_mode_new_reference_auto_adds_member() {
        let initial = make_participants(2);
        let mut grp = GovernedReferenceGroup::open(initial.clone(), 5);

        assert_eq!(grp.member_count(), 2);

        // A new strand references the group -> auto-added in open mode.
        let new_strand = make_node_key(3);
        let change = grp.on_new_reference(new_strand, 10);
        assert_eq!(change, MembershipChange::Added(new_strand));

        // Now a member.
        assert_eq!(grp.member_count(), 3);
        assert!(grp.is_member(&new_strand));

        // Subscription also updated.
        assert!(grp.subscription().is_directly_subscribed(&new_strand));
    }

    #[test]
    fn open_mode_inactivity_auto_removes_member() {
        let initial = make_participants(3);
        let mut grp = GovernedReferenceGroup::open(initial.clone(), 5);

        assert_eq!(grp.member_count(), 3);

        // Record some activity for members 1 and 2, but not 3.
        grp.record_activity(&make_node_key(1), 10);
        grp.record_activity(&make_node_key(2), 10);
        // Member 3 last active at wave 0.

        // Check inactivity at wave 7 (7 - 0 = 7 > 5 timeout).
        let change = grp.on_inactivity(make_node_key(3), 0, 7);
        assert_eq!(change, MembershipChange::Removed(make_node_key(3)));

        assert_eq!(grp.member_count(), 2);
        assert!(!grp.is_member(&make_node_key(3)));
        assert!(!grp.subscription().is_directly_subscribed(&make_node_key(3)));
    }

    #[test]
    fn open_mode_no_removal_before_timeout() {
        let initial = make_participants(3);
        let mut grp = GovernedReferenceGroup::open(initial.clone(), 10);

        // Member 3 last active at wave 5. Current wave 12. 12-5=7 <= 10 timeout.
        grp.record_activity(&make_node_key(3), 5);
        let change = grp.on_inactivity(make_node_key(3), 5, 12);
        assert_eq!(change, MembershipChange::NoChange);
        assert!(grp.is_member(&make_node_key(3)));
    }

    #[test]
    fn invite_only_member_invites_new_strand_added() {
        let founder = make_node_key(1);
        let mut grp = GovernedReferenceGroup::invite_only(founder, 10);

        assert_eq!(grp.member_count(), 1);
        assert!(grp.is_member(&founder));

        // Founder invites node 2.
        let new_member = make_node_key(2);
        let change = grp.invite(&founder, new_member, 5);
        assert_eq!(change, MembershipChange::Added(new_member));
        assert_eq!(grp.member_count(), 2);
        assert!(grp.is_member(&new_member));
    }

    #[test]
    fn invite_only_non_member_cannot_invite() {
        let founder = make_node_key(1);
        let mut grp = GovernedReferenceGroup::invite_only(founder, 10);

        // Non-member (node 99) tries to invite node 2.
        let non_member = make_node_key(99);
        let new_strand = make_node_key(2);
        let change = grp.invite(&non_member, new_strand, 5);
        assert_eq!(change, MembershipChange::NoChange);
        assert_eq!(grp.member_count(), 1);
        assert!(!grp.is_member(&new_strand));
    }

    #[test]
    fn governed_group_finalize_produces_correct_ordering() {
        // GovernedReferenceGroup::finalize() should produce the same result
        // as tau_unified called directly on the reference group.
        let participants = make_participants(3);
        let grp = GovernedReferenceGroup::open(participants.clone(), 10);

        // Build a SIX-round blocklace. Three would not do: under CM Def. 6 (`ordering::tau`'s
        // anchor-chain rule) a one-wave lace orders exactly its anchor, so the agreement below
        // would be checked on a single block. Six rounds give a two-anchor chain.
        let mut bl = crate::Blocklace::new();
        let mut blocks_by_round: Vec<Vec<crate::BlockId>> = Vec::new();

        for round in 1..=6u64 {
            let preds: Vec<crate::BlockId> = if round == 1 {
                vec![]
            } else {
                blocks_by_round[(round - 2) as usize].clone()
            };
            let mut round_blocks = Vec::new();
            for (i, &p) in participants.iter().enumerate() {
                let block =
                    crate::Block::new(p, round - 1, preds.clone(), vec![round as u8, i as u8]);
                let id = bl.insert_unverified(block).unwrap();
                round_blocks.push(id);
            }
            blocks_by_round.push(round_blocks);
        }

        let config = crate::ordering::OrderingConfig::default();

        // Via GovernedReferenceGroup::finalize
        let result_grp = grp.finalize(&bl, &config);

        // Via tau_unified directly
        let result_direct = crate::ordering::tau_unified(&bl, grp.reference_group(), &config);

        assert_eq!(result_grp, result_direct);
        // 3 participants x rounds 1-3, ordered by wave 1's anchor, plus wave 0's anchor.
        assert_eq!(result_grp.len(), 10);
    }

    #[test]
    fn subscription_auto_updates_when_membership_changes() {
        let initial = make_participants(2);
        let mut grp = GovernedReferenceGroup::open(initial.clone(), 5);

        // Initially subscribed to members 1 and 2.
        assert!(grp.subscription().is_directly_subscribed(&make_node_key(1)));
        assert!(grp.subscription().is_directly_subscribed(&make_node_key(2)));
        assert!(!grp.subscription().is_directly_subscribed(&make_node_key(3)));

        // Add member 3 via open reference.
        grp.on_new_reference(make_node_key(3), 1);
        assert!(grp.subscription().is_directly_subscribed(&make_node_key(3)));

        // Remove member 2 via inactivity.
        let change = grp.on_inactivity(make_node_key(2), 0, 10);
        assert_eq!(change, MembershipChange::Removed(make_node_key(2)));
        assert!(!grp.subscription().is_directly_subscribed(&make_node_key(2)));
    }

    #[test]
    fn bridge_constitution_manager_into_governed_group_preserves_state() {
        let participants = make_participants(4);
        let mgr = ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        let governed = mgr.into_governed_group();

        // Preserves member set.
        assert_eq!(governed.member_count(), 4);
        for p in &participants {
            assert!(governed.is_member(p));
        }

        // Governance mode is Constitutional.
        match &governed.governance {
            GovernanceMode::Constitutional { manager } => {
                assert_eq!(manager.threshold(), compute_threshold(4));
                assert_eq!(manager.timeout_waves(), TEST_TIMEOUT_WAVES);
            }
            _ => panic!("expected Constitutional governance mode"),
        }

        // Subscription covers all members.
        for p in &participants {
            assert!(governed.subscription().is_directly_subscribed(p));
        }
    }

    #[test]
    fn mixed_constitutional_and_open_groups_same_blocklace() {
        // Two groups (one constitutional, one open) can coexist on the same blocklace
        // and produce independent orderings.
        let all_participants: Vec<[u8; 32]> = (1..=6u8).map(make_node_key).collect();

        // Build a shared blocklace with all 6 participants. SIX rounds, not three: under CM
        // Def. 6 (`ordering::tau`'s anchor-chain rule) each group's rounds 1-3 are ordered by its
        // OWN wave-1 anchor at round 4, so a three-round lace would finalize one block per group
        // and the disjointness check below would be nearly free.
        let mut bl = crate::Blocklace::new();
        let mut blocks_by_round: Vec<Vec<crate::BlockId>> = Vec::new();

        for round in 1..=6u64 {
            let preds: Vec<crate::BlockId> = if round == 1 {
                vec![]
            } else {
                blocks_by_round[(round - 2) as usize].clone()
            };
            let mut round_blocks = Vec::new();
            for (i, &p) in all_participants.iter().enumerate() {
                let block =
                    crate::Block::new(p, round - 1, preds.clone(), vec![round as u8, i as u8]);
                let id = bl.insert_unverified(block).unwrap();
                round_blocks.push(id);
            }
            blocks_by_round.push(round_blocks);
        }

        // Constitutional group: participants 1, 2, 3.
        let const_group = GovernedReferenceGroup::constitutional(
            vec![make_node_key(1), make_node_key(2), make_node_key(3)],
            10,
        );

        // Open group: participants 4, 5, 6.
        let open_group = GovernedReferenceGroup::open(
            vec![make_node_key(4), make_node_key(5), make_node_key(6)],
            10,
        );

        let config = crate::ordering::OrderingConfig::default();
        let result_const = const_group.finalize(&bl, &config);
        let result_open = open_group.finalize(&bl, &config);

        // Both should finalize their own members' blocks.
        assert_eq!(
            result_const.len(),
            10,
            "constitutional group: 3 members * rounds 1-3, plus wave 1's anchor"
        );
        assert_eq!(
            result_open.len(),
            10,
            "open group: 3 members * rounds 1-3, plus wave 1's anchor"
        );

        // Outputs should be completely disjoint (different members).
        let set_const: std::collections::HashSet<crate::BlockId> =
            result_const.iter().copied().collect();
        let set_open: std::collections::HashSet<crate::BlockId> =
            result_open.iter().copied().collect();
        assert!(
            set_const.is_disjoint(&set_open),
            "constitutional and open groups should produce disjoint orderings"
        );

        // Verify creators match expected groups.
        for &bid in &result_const {
            let block = bl.get(&bid).unwrap();
            assert!(
                [make_node_key(1), make_node_key(2), make_node_key(3)].contains(&block.creator),
                "constitutional group output should only have members 1,2,3"
            );
        }
        for &bid in &result_open {
            let block = bl.get(&bid).unwrap();
            assert!(
                [make_node_key(4), make_node_key(5), make_node_key(6)].contains(&block.creator),
                "open group output should only have members 4,5,6"
            );
        }
    }

    #[test]
    fn open_mode_duplicate_reference_no_double_add() {
        let initial = make_participants(2);
        let mut grp = GovernedReferenceGroup::open(initial, 5);

        let new_strand = make_node_key(3);

        // First reference -> Added.
        let change1 = grp.on_new_reference(new_strand, 1);
        assert_eq!(change1, MembershipChange::Added(new_strand));
        assert_eq!(grp.member_count(), 3);

        // Second reference -> NoChange (already a member).
        let change2 = grp.on_new_reference(new_strand, 2);
        assert_eq!(change2, MembershipChange::NoChange);
        assert_eq!(grp.member_count(), 3);
    }

    #[test]
    fn invite_only_inactivity_removes_member() {
        let founder = make_node_key(1);
        let mut grp = GovernedReferenceGroup::invite_only(founder, 5);

        // Invite member 2.
        grp.invite(&founder, make_node_key(2), 0);
        assert_eq!(grp.member_count(), 2);

        // Member 2 goes inactive. Timeout check at wave 10 (10 - 0 = 10 > 5).
        let change = grp.on_inactivity(make_node_key(2), 0, 10);
        assert_eq!(change, MembershipChange::Removed(make_node_key(2)));
        assert_eq!(grp.member_count(), 1);
        assert!(!grp.is_member(&make_node_key(2)));
    }
}
