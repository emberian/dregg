//! Simplified Morpheus-shaped consensus protocol.
//!
//! This implements the core semantics of the Morpheus protocol without pulling
//! in the full BLS12-381 threshold signature machinery:
//!
//! - **Proposal**: A designated proposer (rotating leader) creates a block
//!   containing pending revocation events.
//! - **Voting**: Nodes validate the proposed block and cast votes.
//! - **Finalization**: Once threshold votes are collected, a quorum certificate
//!   is formed and the block is finalized.
//! - **View changes**: If the leader is faulty/offline, nodes can advance the
//!   view to select a new leader.
//!
//! The protocol guarantees:
//! - Safety: No two conflicting blocks at the same height are finalized.
//! - Liveness: As long as n - f nodes are honest, blocks are finalized.
//!
//! Uses Ed25519 signatures for asymmetric public-key verification.

use crate::types::*;

// =============================================================================
// Consensus Parameters
// =============================================================================

/// Configuration for the consensus protocol.
#[derive(Clone, Debug)]
pub struct ConsensusConfig {
    /// Total number of nodes in the federation.
    pub num_nodes: usize,
    /// The BFT threshold: minimum votes needed to finalize (typically 2f + 1).
    pub threshold: usize,
    /// Maximum Byzantine faults tolerated (f = (n-1)/3).
    pub max_faults: usize,
    /// The current epoch number. Increments on reconfiguration.
    pub epoch: u64,
    /// Explicit member list (public keys). Empty means legacy mode (count-only).
    pub members: Vec<PublicKey>,
}

impl ConsensusConfig {
    /// Create a new consensus configuration for n nodes.
    /// Threshold is set to n - f where f = floor((n-1)/3).
    ///
    /// This is the legacy constructor that does not set explicit members.
    pub fn new(num_nodes: usize) -> Self {
        let max_faults = (num_nodes - 1) / 3;
        let threshold = num_nodes - max_faults;
        Self {
            num_nodes,
            threshold,
            max_faults,
            epoch: 0,
            members: Vec::new(),
        }
    }

    /// Create an initial (genesis) configuration with an explicit member set.
    pub fn genesis(members: Vec<PublicKey>) -> Self {
        let num_nodes = members.len();
        let max_faults = (num_nodes - 1) / 3;
        let threshold = num_nodes - max_faults;
        Self {
            num_nodes,
            threshold,
            max_faults,
            epoch: 0,
            members,
        }
    }

    /// Create the next epoch configuration with a new member set.
    pub fn next_epoch(&self, new_members: Vec<PublicKey>) -> Self {
        let num_nodes = new_members.len();
        let max_faults = (num_nodes - 1) / 3;
        let threshold = num_nodes - max_faults;
        Self {
            num_nodes,
            threshold,
            max_faults,
            epoch: self.epoch + 1,
            members: new_members,
        }
    }

    /// Determine the leader for a given view.
    pub fn leader_for_view(&self, view: u64) -> usize {
        (view as usize) % self.num_nodes
    }
}

// =============================================================================
// Reconfiguration
// =============================================================================

/// Error type for consensus operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusError {
    /// The proposal's epoch does not match the current epoch.
    EpochMismatch { expected: u64, got: u64 },
    /// The proposer is not a current member.
    NotAMember,
    /// A reconfiguration is already pending.
    ReconfigAlreadyPending,
    /// No pending reconfiguration to vote on.
    NoPendingReconfig,
    /// The voter has already voted.
    AlreadyVoted,
    /// The voter is not a current member.
    VoterNotMember,
    /// The new member set is empty.
    EmptyMemberSet,
}

impl std::fmt::Display for ConsensusError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EpochMismatch { expected, got } => {
                write!(f, "epoch mismatch: expected {}, got {}", expected, got)
            }
            Self::NotAMember => write!(f, "proposer is not a current member"),
            Self::ReconfigAlreadyPending => write!(f, "reconfiguration already pending"),
            Self::NoPendingReconfig => write!(f, "no pending reconfiguration"),
            Self::AlreadyVoted => write!(f, "voter already voted"),
            Self::VoterNotMember => write!(f, "voter is not a current member"),
            Self::EmptyMemberSet => write!(f, "new member set cannot be empty"),
        }
    }
}

impl std::error::Error for ConsensusError {}

/// A proposal to reconfigure the federation at the next epoch boundary.
#[derive(Clone, Debug)]
pub struct ReconfigurationProposal {
    /// The current epoch (must match the orchestrator's current epoch).
    pub epoch: u64,
    /// The proposed new member set for the next epoch.
    pub new_members: Vec<PublicKey>,
    /// The proposer's public key (must be a current member).
    pub proposer: PublicKey,
    /// Signature over the proposal content by the proposer.
    pub signature: Signature,
}

impl ReconfigurationProposal {
    /// Compute the canonical message to sign for a reconfiguration proposal.
    pub fn signing_message(epoch: u64, new_members: &[PublicKey]) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-reconfig-proposal-v1");
        msg.extend_from_slice(&epoch.to_le_bytes());
        for member in new_members {
            msg.extend_from_slice(&member.0);
        }
        msg
    }

    /// Compute a hash of this proposal (for vote tracking).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-reconfig-proposal-hash-v1");
        hasher.update(&self.epoch.to_le_bytes());
        for member in &self.new_members {
            hasher.update(&member.0);
        }
        hasher.update(&self.proposer.0);
        hasher.update(&self.signature.0);
        *hasher.finalize().as_bytes()
    }

    /// Verify that the proposer's signature is valid.
    pub fn verify_signature(&self) -> bool {
        let msg = Self::signing_message(self.epoch, &self.new_members);
        self.proposer.verify(&msg, &self.signature)
    }
}

/// Tracks votes on a pending reconfiguration proposal.
#[derive(Clone, Debug)]
pub struct ReconfigurationVotes {
    /// The proposal being voted on.
    pub proposal: ReconfigurationProposal,
    /// Hash of the proposal.
    pub proposal_hash: [u8; 32],
    /// Public keys of members who have voted in favor.
    pub voters: Vec<PublicKey>,
}

// =============================================================================
// Consensus State Machine
// =============================================================================

/// The state of a node's consensus participation.
#[derive(Clone, Debug)]
pub struct ConsensusState {
    /// The node's ID in the federation.
    pub node_id: usize,
    /// The node's signing key.
    pub signing_key: SigningKey,
    /// The current view number.
    pub current_view: u64,
    /// The current block height (last finalized + 1).
    pub current_height: u64,
    /// Hash of the last finalized block.
    pub last_finalized_hash: [u8; 32],
    /// Pending revocation events waiting to be included in a block.
    pub pending_events: Vec<RevocationEvent>,
    /// Votes collected for the current proposal.
    pub collected_votes: Vec<Vote>,
    /// The current proposal (if any).
    pub current_proposal: Option<RevocationBlock>,
    /// Whether this node has voted in the current view.
    pub has_voted: bool,
    /// Whether this node is online (for simulating Byzantine faults).
    pub is_online: bool,
    /// Consensus configuration.
    pub config: ConsensusConfig,
    /// Finalized blocks history.
    pub finalized_blocks: Vec<(RevocationBlock, QuorumCertificate)>,
    /// The current epoch number (mirrors config.epoch).
    pub epoch: u64,
    /// Pending reconfiguration proposal and its votes.
    pub pending_reconfig: Option<ReconfigurationVotes>,
}

impl ConsensusState {
    /// Create a new consensus state for a node.
    pub fn new(node_id: usize, signing_key: SigningKey, config: ConsensusConfig) -> Self {
        // Genesis block hash.
        let genesis_hash = compute_genesis_hash(&config);
        let epoch = config.epoch;

        Self {
            node_id,
            signing_key,
            current_view: 1,
            current_height: 1,
            last_finalized_hash: genesis_hash,
            pending_events: Vec::new(),
            collected_votes: Vec::new(),
            current_proposal: None,
            has_voted: false,
            is_online: true,
            config,
            finalized_blocks: Vec::new(),
            epoch,
            pending_reconfig: None,
        }
    }

    /// Whether this node is the leader for the current view.
    pub fn is_leader(&self) -> bool {
        self.config.leader_for_view(self.current_view) == self.node_id
    }

    /// Submit a revocation event to the pending queue.
    pub fn submit_revocation(&mut self, event: RevocationEvent) {
        self.pending_events.push(event);
    }

    /// As leader: create a proposal block from pending events.
    /// Returns None if there are no pending events or this node isn't the leader.
    pub fn create_proposal(&mut self) -> Option<RevocationBlock> {
        if !self.is_leader() || self.pending_events.is_empty() {
            return None;
        }

        let events = std::mem::take(&mut self.pending_events);
        let block_hash = RevocationBlock::compute_hash(
            self.current_height,
            self.current_view,
            self.node_id,
            &events,
            &self.last_finalized_hash,
        );

        let block = RevocationBlock {
            height: self.current_height,
            view: self.current_view,
            proposer: self.node_id,
            events,
            prev_hash: self.last_finalized_hash,
            block_hash,
        };

        self.current_proposal = Some(block.clone());
        Some(block)
    }

    /// As a voter: validate and vote on a proposed block.
    /// Returns None if the node has already voted, is offline, or the block is invalid.
    pub fn vote_on_proposal(&mut self, block: &RevocationBlock) -> Option<Vote> {
        if !self.is_online || self.has_voted {
            return None;
        }

        // Validate the block.
        if !self.validate_block(block) {
            return None;
        }

        // Cast the vote.
        self.has_voted = true;
        self.current_proposal = Some(block.clone());

        let vote_message = self.vote_message(block);
        let signature = sign(&self.signing_key, &vote_message);

        Some(Vote {
            block_hash: block.block_hash,
            height: block.height,
            view: block.view,
            voter: self.node_id,
            signature,
        })
    }

    /// Collect a vote. Returns a QuorumCertificate if threshold is reached.
    pub fn collect_vote(&mut self, vote: Vote) -> Option<QuorumCertificate> {
        // Verify the vote is for the current proposal.
        if let Some(ref proposal) = self.current_proposal {
            if vote.block_hash != proposal.block_hash {
                return None;
            }
        } else {
            return None;
        }

        // Don't count duplicate votes from the same node.
        if self.collected_votes.iter().any(|v| v.voter == vote.voter) {
            return None;
        }

        self.collected_votes.push(vote);

        // Check if we've reached threshold.
        if self.collected_votes.len() >= self.config.threshold {
            let qc = QuorumCertificate {
                block_hash: self.current_proposal.as_ref().unwrap().block_hash,
                height: self.current_height,
                view: self.current_view,
                aggregate_qc: None,
                votes: self
                    .collected_votes
                    .iter()
                    .map(|v| (v.voter, v.signature.clone()))
                    .collect(),
                threshold: self.config.threshold,
            };
            return Some(qc);
        }

        None
    }

    /// Finalize a block with its quorum certificate.
    /// Advances the state to the next height/view.
    pub fn finalize_block(&mut self, block: RevocationBlock, qc: QuorumCertificate) {
        self.last_finalized_hash = block.block_hash;
        self.finalized_blocks.push((block, qc));
        self.current_height += 1;
        self.current_view += 1;
        self.collected_votes.clear();
        self.current_proposal = None;
        self.has_voted = false;
    }

    /// Advance the view (when the leader is faulty).
    pub fn advance_view(&mut self) {
        self.current_view += 1;
        self.collected_votes.clear();
        self.current_proposal = None;
        self.has_voted = false;
    }

    /// Set the node's online status.
    pub fn set_online(&mut self, online: bool) {
        self.is_online = online;
    }

    /// Validate a proposed block.
    fn validate_block(&self, block: &RevocationBlock) -> bool {
        // Check height.
        if block.height != self.current_height {
            return false;
        }
        // Check view.
        if block.view != self.current_view {
            return false;
        }
        // Check prev_hash.
        if block.prev_hash != self.last_finalized_hash {
            return false;
        }
        // Verify the block hash.
        let expected_hash = RevocationBlock::compute_hash(
            block.height,
            block.view,
            block.proposer,
            &block.events,
            &block.prev_hash,
        );
        if block.block_hash != expected_hash {
            return false;
        }
        // Block must have at least one event.
        if block.events.is_empty() {
            return false;
        }
        true
    }

    /// Compute the message that is signed when voting.
    fn vote_message(&self, block: &RevocationBlock) -> Vec<u8> {
        QuorumCertificate::vote_message(&block.block_hash, block.height, block.view)
    }
}

// =============================================================================
// Consensus Orchestrator
// =============================================================================

/// Drives a full consensus round for a set of nodes.
///
/// This is a synchronous orchestrator that simulates the message-passing
/// that would happen asynchronously in a real deployment.
pub struct ConsensusOrchestrator {
    /// The consensus configuration.
    pub config: ConsensusConfig,
    /// Optional threshold committee for producing aggregate BLS QCs.
    /// When present, `run_round` will sign the vote message with each voting
    /// member's BLS key and aggregate the shares into a ThresholdQC.
    pub committee: Option<crate::threshold::FederationCommittee>,
    /// Optional BLS member secrets, indexed by node_id.
    /// Required for producing BLS partial signatures during `run_round`.
    pub member_secrets: Vec<crate::threshold::MemberSecret>,
    /// Pending reconfiguration proposal and its collected votes.
    pub pending_reconfig: Option<ReconfigurationVotes>,
}

impl ConsensusOrchestrator {
    /// Create a new orchestrator.
    pub fn new(config: ConsensusConfig) -> Self {
        Self {
            config,
            committee: None,
            member_secrets: Vec::new(),
            pending_reconfig: None,
        }
    }

    /// Set a threshold committee for producing aggregate BLS QCs during consensus.
    ///
    /// When a committee is configured along with member secrets, the orchestrator
    /// will collect BLS signature shares from voting members and aggregate them
    /// into a constant-size ThresholdQC on the finalized QuorumCertificate.
    pub fn with_threshold_committee(
        mut self,
        committee: crate::threshold::FederationCommittee,
        member_secrets: Vec<crate::threshold::MemberSecret>,
    ) -> Self {
        self.committee = Some(committee);
        self.member_secrets = member_secrets;
        self
    }

    /// Propose a reconfiguration of the federation.
    ///
    /// The proposal must be signed by a current member and target the current epoch.
    /// Only one reconfiguration may be pending at a time.
    pub fn propose_reconfiguration(
        &mut self,
        proposal: ReconfigurationProposal,
    ) -> Result<(), ConsensusError> {
        // Check epoch matches.
        if proposal.epoch != self.config.epoch {
            return Err(ConsensusError::EpochMismatch {
                expected: self.config.epoch,
                got: proposal.epoch,
            });
        }

        // Check proposer is a current member (only if members are tracked).
        if !self.config.members.is_empty()
            && !self.config.members.contains(&proposal.proposer)
        {
            return Err(ConsensusError::NotAMember);
        }

        // Check no pending reconfig.
        if self.pending_reconfig.is_some() {
            return Err(ConsensusError::ReconfigAlreadyPending);
        }

        // Check new member set is non-empty.
        if proposal.new_members.is_empty() {
            return Err(ConsensusError::EmptyMemberSet);
        }

        // Verify the proposer's signature.
        if !proposal.verify_signature() {
            return Err(ConsensusError::NotAMember);
        }

        let proposal_hash = proposal.hash();
        // The proposer's vote counts as the first vote.
        let voters = vec![proposal.proposer.clone()];

        self.pending_reconfig = Some(ReconfigurationVotes {
            proposal,
            proposal_hash,
            voters,
        });

        Ok(())
    }

    /// Vote on a pending reconfiguration proposal.
    ///
    /// The voter must be a current member and must provide the correct proposal hash.
    pub fn vote_reconfiguration(
        &mut self,
        proposal_hash: [u8; 32],
        voter: &SigningKey,
    ) -> Result<(), ConsensusError> {
        let reconfig = self
            .pending_reconfig
            .as_mut()
            .ok_or(ConsensusError::NoPendingReconfig)?;

        // Verify the proposal hash matches.
        if reconfig.proposal_hash != proposal_hash {
            return Err(ConsensusError::NoPendingReconfig);
        }

        let voter_pubkey = voter.public_key();

        // Check voter is a current member (only if members are tracked).
        if !self.config.members.is_empty()
            && !self.config.members.contains(&voter_pubkey)
        {
            return Err(ConsensusError::VoterNotMember);
        }

        // Check voter hasn't already voted.
        if reconfig.voters.contains(&voter_pubkey) {
            return Err(ConsensusError::AlreadyVoted);
        }

        reconfig.voters.push(voter_pubkey);
        Ok(())
    }

    /// Get the pending reconfiguration proposal, if any.
    pub fn pending_reconfiguration(&self) -> Option<&ReconfigurationProposal> {
        self.pending_reconfig.as_ref().map(|r| &r.proposal)
    }

    /// Check if the pending reconfiguration has reached the vote threshold.
    pub fn reconfig_has_quorum(&self) -> bool {
        match &self.pending_reconfig {
            Some(reconfig) => reconfig.voters.len() >= self.config.threshold,
            None => false,
        }
    }

    /// Apply the pending reconfiguration if it has reached quorum.
    ///
    /// Returns the new `ConsensusConfig` if applied, or `None` if there is no
    /// pending reconfig or it hasn't reached threshold.
    pub fn apply_pending_reconfiguration(&mut self) -> Option<ConsensusConfig> {
        if !self.reconfig_has_quorum() {
            return None;
        }

        let reconfig = self.pending_reconfig.take()?;
        let new_config = self.config.next_epoch(reconfig.proposal.new_members);
        self.config = new_config.clone();
        Some(new_config)
    }

    /// Run a single consensus round: propose, vote, finalize.
    ///
    /// Returns the finalized block and QC, or None if consensus failed
    /// (e.g., not enough online nodes).
    pub fn run_round(
        &mut self,
        states: &mut [ConsensusState],
    ) -> Option<(RevocationBlock, QuorumCertificate)> {
        // Find the leader.
        let view = states[0].current_view;
        let leader_id = self.config.leader_for_view(view);

        // If leader is offline, try advancing views until we find an online leader.
        if !states[leader_id].is_online {
            // Advance all nodes' views.
            for state in states.iter_mut() {
                if state.is_online {
                    state.advance_view();
                }
            }
            // Retry with new view.
            let new_view = states.iter().find(|s| s.is_online).map(|s| s.current_view)?;
            let new_leader = self.config.leader_for_view(new_view);
            if !states[new_leader].is_online {
                // Still offline — try one more view change.
                for state in states.iter_mut() {
                    if state.is_online {
                        state.advance_view();
                    }
                }
            }
        }

        // Get current view from an online node.
        let current_view = states.iter().find(|s| s.is_online)?.current_view;
        let leader_id = self.config.leader_for_view(current_view);

        if !states[leader_id].is_online {
            return None;
        }

        // Distribute pending events to the leader.
        let mut all_pending: Vec<RevocationEvent> = Vec::new();
        for state in states.iter_mut() {
            if state.is_online {
                all_pending.extend(state.pending_events.drain(..));
            }
        }
        // Give all events to the leader.
        states[leader_id].pending_events = all_pending;

        // Leader creates proposal.
        let proposal = states[leader_id].create_proposal()?;

        // Leader votes for its own proposal.
        let leader_vote = states[leader_id].vote_on_proposal(&proposal)?;
        states[leader_id].collect_vote(leader_vote);

        // Other nodes vote.
        let mut votes = Vec::new();
        for state in states.iter_mut() {
            if state.node_id == leader_id {
                continue;
            }
            if let Some(vote) = state.vote_on_proposal(&proposal) {
                votes.push(vote);
            }
        }

        // Leader collects votes.
        let mut qc = None;
        for vote in votes {
            if let Some(certificate) = states[leader_id].collect_vote(vote) {
                qc = Some(certificate);
                break;
            }
        }

        let mut qc = qc?;

        // If a threshold committee is available, collect BLS signature shares
        // from voting members and aggregate into a constant-size ThresholdQC.
        if let Some(ref committee) = self.committee {
            let message = QuorumCertificate::vote_message(
                &qc.block_hash,
                qc.height,
                qc.view,
            );

            // Collect BLS shares from all voters that have member secrets.
            let voter_ids: Vec<usize> = qc.votes.iter().map(|(id, _)| *id).collect();
            let mut bls_shares = Vec::new();
            for voter_id in &voter_ids {
                if let Some(member_secret) = self.member_secrets.get(*voter_id) {
                    let share = committee.sign_share(member_secret, &message);
                    bls_shares.push((member_secret.index, share));
                }
            }

            if bls_shares.len() >= committee.threshold_value as usize {
                if let Ok(threshold_qc) = committee.aggregate(&bls_shares, &message) {
                    qc.aggregate_qc = Some(threshold_qc);
                }
            }
        }

        // Finalize on all online nodes.
        for state in states.iter_mut() {
            if state.is_online {
                state.finalize_block(proposal.clone(), qc.clone());
            }
        }

        // After finalization, check if a pending reconfiguration has reached quorum.
        // If so, apply it: the new config takes effect for the NEXT round.
        if self.reconfig_has_quorum() {
            if let Some(new_config) = self.apply_pending_reconfiguration() {
                // Update all online nodes to use the new configuration.
                for state in states.iter_mut() {
                    if state.is_online {
                        state.config = new_config.clone();
                        state.epoch = new_config.epoch;
                        state.pending_reconfig = None;
                    }
                }
            }
        }

        Some((proposal, qc))
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute the genesis block hash (deterministic for a given config).
fn compute_genesis_hash(config: &ConsensusConfig) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-federation genesis v1");
    hasher.update(&(config.num_nodes as u64).to_le_bytes());
    hasher.update(&(config.threshold as u64).to_le_bytes());
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::generate_keypair;

    fn setup_nodes(n: usize) -> (ConsensusConfig, Vec<ConsensusState>) {
        let config = ConsensusConfig::new(n);
        let states: Vec<ConsensusState> = (0..n)
            .map(|i| {
                let (sk, _pk) = generate_keypair();
                ConsensusState::new(i, sk, config.clone())
            })
            .collect();
        (config, states)
    }

    #[test]
    fn config_4_nodes() {
        let config = ConsensusConfig::new(4);
        assert_eq!(config.threshold, 3);
        assert_eq!(config.max_faults, 1);
    }

    #[test]
    fn config_7_nodes() {
        let config = ConsensusConfig::new(7);
        assert_eq!(config.threshold, 5);
        assert_eq!(config.max_faults, 2);
    }

    #[test]
    fn leader_rotation() {
        let config = ConsensusConfig::new(4);
        assert_eq!(config.leader_for_view(1), 1);
        assert_eq!(config.leader_for_view(2), 2);
        assert_eq!(config.leader_for_view(3), 3);
        assert_eq!(config.leader_for_view(4), 0);
    }

    #[test]
    fn basic_consensus_round() {
        let (config, mut states) = setup_nodes(4);
        let mut orchestrator = ConsensusOrchestrator::new(config);

        // Submit a revocation event.
        let event = RevocationEvent {
            token_id: "token-1".to_string(),
            authority_id: 0,
            signature: Signature([42u8; 64]),
        };
        states[0].submit_revocation(event);

        // Run consensus.
        let result = orchestrator.run_round(&mut states);
        assert!(result.is_some());

        let (block, qc) = result.unwrap();
        assert_eq!(block.height, 1);
        assert_eq!(block.events.len(), 1);
        assert_eq!(block.events[0].token_id, "token-1");
        assert!(qc.is_valid());
        assert!(qc.votes.len() >= 3);
    }

    #[test]
    fn consensus_with_fault() {
        let (config, mut states) = setup_nodes(4);
        let mut orchestrator = ConsensusOrchestrator::new(config);

        // Take one node offline.
        states[3].set_online(false);

        // Submit a revocation event.
        let event = RevocationEvent {
            token_id: "token-2".to_string(),
            authority_id: 1,
            signature: Signature([43u8; 64]),
        };
        states[0].submit_revocation(event);

        // Should still reach consensus with 3/4 nodes.
        let result = orchestrator.run_round(&mut states);
        assert!(result.is_some());

        let (_block, qc) = result.unwrap();
        assert!(qc.is_valid());
    }

    #[test]
    fn consensus_fails_with_too_many_faults() {
        let (config, mut states) = setup_nodes(4);
        let mut orchestrator = ConsensusOrchestrator::new(config);

        // Take two nodes offline (exceeds f=1).
        states[2].set_online(false);
        states[3].set_online(false);

        let event = RevocationEvent {
            token_id: "token-3".to_string(),
            authority_id: 0,
            signature: Signature([44u8; 64]),
        };
        states[0].submit_revocation(event);

        // Should fail — only 2 nodes online, need 3.
        let result = orchestrator.run_round(&mut states);
        assert!(result.is_none());
    }

    #[test]
    fn multiple_rounds() {
        let (config, mut states) = setup_nodes(4);
        let mut orchestrator = ConsensusOrchestrator::new(config);

        // Round 1.
        states[0].submit_revocation(RevocationEvent {
            token_id: "token-a".to_string(),
            authority_id: 0,
            signature: Signature([1u8; 64]),
        });
        let r1 = orchestrator.run_round(&mut states);
        assert!(r1.is_some());
        let (b1, _) = r1.unwrap();
        assert_eq!(b1.height, 1);

        // Round 2.
        states[1].submit_revocation(RevocationEvent {
            token_id: "token-b".to_string(),
            authority_id: 1,
            signature: Signature([2u8; 64]),
        });
        let r2 = orchestrator.run_round(&mut states);
        assert!(r2.is_some());
        let (b2, _) = r2.unwrap();
        assert_eq!(b2.height, 2);
        assert_eq!(b2.prev_hash, b1.block_hash);
    }
}
