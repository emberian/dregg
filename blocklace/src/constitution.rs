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
//! - **Auto-eviction**: equivocation proofs immediately remove the equivocator.
//! - **Timeout-based auto-leave**: nodes silent for `timeout_waves` waves are
//!   proposed for removal. When they return, they re-join via a Join proposal.
//! - **Voting via blocks**: votes reference the proposal block in their causal past.
//! - **n=1 case**: with a single participant, every wave finalizes instantly (self
//!   is always the leader with threshold=1). Adding a peer grows the threshold;
//!   their timeout shrinks it back.

use serde::{Deserialize, Serialize};

use crate::finality::{BlockId, EquivocationProof};

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
    /// join/leave), increments the version, and returns true if the change
    /// was actually applied (e.g., false if trying to add an existing member).
    pub fn apply_proposal(&mut self, proposal: &MembershipProposal) -> bool {
        match proposal {
            MembershipProposal::Join {
                node_key,
                justification: _,
            } => {
                if self.participants.contains(node_key) {
                    return false; // Already a member
                }
                self.participants.push(*node_key);
                self.participants.sort();
                self.threshold = compute_threshold(self.participants.len());
                self.version += 1;
                true
            }
            MembershipProposal::Leave {
                node_key,
                reason: _,
            } => {
                let before = self.participants.len();
                self.participants.retain(|k| k != node_key);
                if self.participants.len() == before {
                    return false; // Not a member
                }
                self.threshold = compute_threshold(self.participants.len());
                self.version += 1;
                true
            }
            MembershipProposal::AmendThreshold { new_threshold } => {
                if *new_threshold == self.threshold {
                    return false; // No change
                }
                if *new_threshold == 0 || *new_threshold > self.participants.len() {
                    return false; // Invalid threshold
                }
                self.threshold = *new_threshold;
                self.version += 1;
                true
            }
            MembershipProposal::AmendRoutes {
                new_routes_commitment,
                description: _,
            } => {
                // Update the routes commitment. Applied immediately (no grace period).
                self.routes_commitment = Some(*new_routes_commitment);
                self.version += 1;
                true
            }
        }
    }

    /// Auto-evict an equivocator based on cryptographic proof.
    ///
    /// Since equivocation proofs are self-evident (two conflicting signed blocks),
    /// this does NOT require a vote -- it applies immediately.
    ///
    /// Returns true if the equivocator was actually a participant and was removed.
    pub fn auto_evict_equivocator(&mut self, proof: &EquivocationProof) -> bool {
        let evicted = proof.creator;
        if !self.participants.contains(&evicted) {
            return false;
        }
        self.participants.retain(|k| k != &evicted);
        self.threshold = compute_threshold(self.participants.len());
        self.version += 1;
        true
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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LeaveReason {
    /// Participant chose to leave.
    Voluntary,
    /// Participant was evicted due to equivocation.
    Evicted {
        /// The two conflicting blocks (serialized for compactness).
        block_a_bytes: Vec<u8>,
        block_b_bytes: Vec<u8>,
    },
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
    /// leader (Cordial Miners finality). Returns true if successfully applied.
    pub fn apply_if_passed(&mut self, proposal_block: &BlockId) -> bool {
        if !self.votes.has_passed(proposal_block, &self.current) {
            return false;
        }

        let proposal = match self.votes.get_proposal(proposal_block) {
            Some(p) => p.clone(),
            None => return false,
        };

        // Track the joining node for grace period enforcement.
        let joining_node = match &proposal {
            MembershipProposal::Join { node_key, .. } => Some(*node_key),
            _ => None,
        };

        if self.current.apply_proposal(&proposal) {
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

            true
        } else {
            false
        }
    }

    /// Auto-evict an equivocator. Does not require voting.
    ///
    /// Returns true if the equivocator was removed from the constitution.
    pub fn auto_evict(&mut self, proof: &EquivocationProof) -> bool {
        if self.current.auto_evict_equivocator(proof) {
            self.last_active_wave.remove(&proof.creator);
            self.pending_timeout_leaves.remove(&proof.creator);
            self.joined_at_wave.remove(&proof.creator);
            self.history.push(self.current.clone());
            true
        } else {
            false
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
/// Uses floor(2n/3) + 1, matching the BFT requirement of tolerating < n/3 faults.
pub fn compute_threshold(n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    (n * 2 / 3) + 1
}

// ─── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::finality::{Block, Payload};
    use ed25519_dalek::SigningKey;
    use rand::rngs::OsRng;

    fn random_key() -> SigningKey {
        SigningKey::generate(&mut OsRng)
    }

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
        assert_eq!(compute_threshold(0), 0);
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
        assert!(mgr.apply_if_passed(&proposal_block));
        assert!(mgr.current.is_participant(&new_node));
        assert_eq!(mgr.current.participant_count(), 4);
        assert_eq!(mgr.current.version, 1);
        // Threshold updated: floor(2*4/3) + 1 = 3
        assert_eq!(mgr.current.threshold, 3);
    }

    // ─── Propose leave → threshold approvals → member removed ───────────────

    #[test]
    fn propose_leave_threshold_approvals_member_removed() {
        let participants = make_participants(4);
        let mut mgr =
            ConstitutionManager::from_participants(participants.clone(), TEST_TIMEOUT_WAVES);

        // threshold for 4 = 3
        assert_eq!(mgr.threshold(), 3);

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
        let result = mgr.submit_vote(&vote, make_node_key(3));
        assert_eq!(result, Some(proposal_block));

        assert!(mgr.apply_if_passed(&proposal_block));
        assert!(!mgr.current.is_participant(&leaving_node));
        assert_eq!(mgr.current.participant_count(), 3);
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

        assert!(mgr.apply_if_passed(&proposal_block));
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

        assert!(mgr.apply_if_passed(&proposal_block));
        assert_eq!(mgr.current.threshold, 2);
    }

    // ─── Auto-eviction: equivocator detected → immediately removed ──────────

    #[test]
    fn auto_eviction_equivocator_immediately_removed() {
        let participants = make_participants(4);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let equivocator_key = random_key();
        let equivocator_pub = equivocator_key.verifying_key().to_bytes();

        // First, add the equivocator as a participant
        mgr.current.participants.push(equivocator_pub);
        mgr.current.participants.sort();
        mgr.current.threshold = compute_threshold(mgr.current.participant_count());
        mgr.current.version += 1;

        assert!(mgr.current.is_participant(&equivocator_pub));
        let count_before = mgr.current.participant_count();

        // Create equivocation proof: two blocks at same seq with different content
        let block_a = Block::new(
            &equivocator_key,
            1,
            Payload::Data(b"version A".to_vec()),
            vec![],
        );
        let block_b = Block::new(
            &equivocator_key,
            1,
            Payload::Data(b"version B".to_vec()),
            vec![],
        );

        let proof = EquivocationProof {
            creator: equivocator_pub,
            block_a,
            block_b,
        };

        // Auto-evict: no voting needed
        assert!(mgr.auto_evict(&proof));
        assert!(!mgr.current.is_participant(&equivocator_pub));
        assert_eq!(mgr.current.participant_count(), count_before - 1);
    }

    #[test]
    fn auto_eviction_non_participant_returns_false() {
        let participants = make_participants(3);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let non_member_key = random_key();
        let non_member_pub = non_member_key.verifying_key().to_bytes();

        let block_a = Block::new(&non_member_key, 1, Payload::Data(b"A".to_vec()), vec![]);
        let block_b = Block::new(&non_member_key, 1, Payload::Data(b"B".to_vec()), vec![]);

        let proof = EquivocationProof {
            creator: non_member_pub,
            block_a,
            block_b,
        };

        assert!(!mgr.auto_evict(&proof));
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
        mgr.apply_if_passed(&proposal_block);

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
        assert!(mgr.apply_if_passed(&proposal_block));
        assert_eq!(mgr.current.participant_count(), 4);

        // Second application fails (already applied).
        assert!(!mgr.apply_if_passed(&proposal_block));
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
        mgr.apply_if_passed(&proposal_block);

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

        assert!(mgr.apply_if_passed(&proposal_block));
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

        assert!(mgr.apply_if_passed(&proposal_block));
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
        mgr.apply_if_passed(&leave_block);

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

        assert!(mgr.apply_if_passed(&rejoin_block));
        assert_eq!(mgr.participants().len(), 2);
        assert!(mgr.current.is_participant(&make_node_key(2)));
    }

    // ─── H-rule: can't lower threshold without new threshold's approval ─────

    #[test]
    fn h_rule_lowering_threshold_requires_current_threshold() {
        // 4 participants, threshold=3 (default).
        let participants = make_participants(4);
        let mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let lower = MembershipProposal::AmendThreshold { new_threshold: 2 };
        // max(3, 2) = 3 votes required to lower
        assert_eq!(mgr.current.required_votes_for(&lower), 3);

        let raise = MembershipProposal::AmendThreshold { new_threshold: 4 };
        // max(3, 4) = 4 votes required to raise
        assert_eq!(mgr.current.required_votes_for(&raise), 4);
    }

    // ─── Auto-eviction: equivocator detected -> immediately removed ─────────

    #[test]
    fn auto_eviction_clears_timeout_tracking() {
        let participants = make_participants(4);
        let mut mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        let equivocator_key = random_key();
        let equivocator_pub = equivocator_key.verifying_key().to_bytes();

        // Add equivocator as participant
        mgr.current.participants.push(equivocator_pub);
        mgr.current.participants.sort();
        mgr.current.threshold = compute_threshold(mgr.current.participant_count());
        mgr.current.version += 1;

        // Record some activity for the equivocator
        mgr.record_activity(&equivocator_pub, 5);
        assert_eq!(mgr.last_wave_with_block_from(&equivocator_pub), Some(5));

        // Create equivocation proof
        let block_a = Block::new(
            &equivocator_key,
            1,
            Payload::Data(b"version A".to_vec()),
            vec![],
        );
        let block_b = Block::new(
            &equivocator_key,
            1,
            Payload::Data(b"version B".to_vec()),
            vec![],
        );
        let proof = EquivocationProof {
            creator: equivocator_pub,
            block_a,
            block_b,
        };

        // Auto-evict: no voting, clears timeout tracking
        assert!(mgr.auto_evict(&proof));
        assert!(!mgr.current.is_participant(&equivocator_pub));
        assert_eq!(mgr.last_wave_with_block_from(&equivocator_pub), None);
    }

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
        assert!(mgr.apply_if_passed(&proposal_block));
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
        mgr.apply_if_passed(&proposal_block);

        // Routes commitment updated
        assert_eq!(mgr.routes_commitment(), Some(new_routes));
        assert_eq!(mgr.current.routes_commitment, Some(new_routes));
    }

    #[test]
    fn route_amendment_requires_same_threshold_as_membership() {
        let participants = make_participants(4);
        let mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        // threshold for 4 = 3
        assert_eq!(mgr.threshold(), 3);

        let route_proposal = MembershipProposal::AmendRoutes {
            new_routes_commitment: [0x11; 32],
            description: "test".to_string(),
        };
        let join_proposal = MembershipProposal::Join {
            node_key: make_node_key(5),
            justification: vec![],
        };

        // Both require the same threshold
        assert_eq!(mgr.current.required_votes_for(&route_proposal), 3);
        assert_eq!(mgr.current.required_votes_for(&join_proposal), 3);
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
        mgr.apply_if_passed(&proposal_block);

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
        mgr.apply_if_passed(&proposal_block2);

        assert_eq!(mgr.version(), 2);
        let v2 = mgr.constitution_at_version(2).unwrap();
        assert_eq!(v2.routes_commitment, Some(routes_v2));

        // v1 still preserved
        let v1_again = mgr.constitution_at_version(1).unwrap();
        assert_eq!(v1_again.routes_commitment, Some(routes_v1));
    }

    #[test]
    fn initial_constitution_has_no_routes_commitment() {
        let participants = make_participants(5);
        let mgr = ConstitutionManager::from_participants(participants, TEST_TIMEOUT_WAVES);

        assert_eq!(mgr.routes_commitment(), None);
        assert_eq!(mgr.current.routes_commitment, None);
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
        mgr.apply_if_passed(&proposal_block);

        // Now verify returns true for the correct commitment
        assert!(mgr.verify_routes_commitment(&commitment));
        // And false for a wrong commitment
        assert!(!mgr.verify_routes_commitment(&wrong_commitment));
    }
}
