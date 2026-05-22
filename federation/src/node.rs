//! Federation node implementation.
//!
//! A federation node is a process that:
//! - Holds an authority keypair
//! - Maintains a local revocation accumulator (Merkle tree of revoked token IDs)
//! - Participates in Morpheus consensus to agree on the current revocation root
//! - Exposes an API for: `revoke(token_id)`, `get_attested_root()`,
//!   `verify_non_membership(token_id)`
//!
//! Each node maintains its own copy of the revocation tree. After consensus
//! finalizes a block of revocations, all nodes apply the same set of
//! revocations to their local trees, ensuring they converge on the same root.
//!
//! This module also contains the BFT consensus simulation types
//! (`ConsensusConfig`, `ConsensusState`, `ConsensusOrchestrator`) that power
//! the synchronous `Federation` harness.

use crate::revocation::{RevocationTree, RevocationVerifier};
use crate::types::*;

// =============================================================================
// Consensus Parameters
// =============================================================================

/// Configuration for the BFT consensus protocol.
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
    /// Whether to require authentication (signature verification).
    pub require_authentication: bool,
}

impl ConsensusConfig {
    /// Create a new consensus configuration for n nodes.
    /// Threshold is set to n - f where f = floor((n-1)/3).
    pub fn new(num_nodes: usize) -> Self {
        let max_faults = (num_nodes - 1) / 3;
        let threshold = num_nodes - max_faults;
        Self {
            num_nodes,
            threshold,
            max_faults,
            epoch: 0,
            members: Vec::new(),
            require_authentication: true,
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
            require_authentication: true,
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
            require_authentication: self.require_authentication,
        }
    }

    /// Determine the leader for a given view.
    pub fn leader_for_view(&self, view: u64) -> usize {
        (view as usize) % self.num_nodes
    }
}

// =============================================================================
// Consensus Error
// =============================================================================

/// Error type for consensus operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusError {
    EpochMismatch { expected: u64, got: u64 },
    NotAMember,
    ReconfigAlreadyPending,
    NoPendingReconfig,
    AlreadyVoted,
    VoterNotMember,
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

// =============================================================================
// Reconfiguration
// =============================================================================

/// A proposal to reconfigure the federation at the next epoch boundary.
#[derive(Clone, Debug)]
pub struct ReconfigurationProposal {
    pub epoch: u64,
    pub new_members: Vec<PublicKey>,
    pub proposer: PublicKey,
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
    pub proposal: ReconfigurationProposal,
    pub proposal_hash: [u8; 32],
    pub voters: Vec<(PublicKey, Signature)>,
}

// =============================================================================
// Consensus State Machine
// =============================================================================

/// State roots to be committed in a block proposal.
#[derive(Clone, Debug)]
pub struct PendingStateRoots {
    pub pre_state_root: [u8; 32],
    pub post_state_root: [u8; 32],
    pub note_tree_root: [u8; 32],
    pub nullifier_set_root: [u8; 32],
}

/// The state of a node's consensus participation.
#[derive(Clone, Debug)]
pub struct ConsensusState {
    pub node_id: usize,
    pub signing_key: SigningKey,
    pub current_view: u64,
    pub current_height: u64,
    pub last_finalized_hash: [u8; 32],
    pub pending_events: Vec<RevocationEvent>,
    pub collected_votes: Vec<Vote>,
    pub current_proposal: Option<RevocationBlock>,
    pub has_voted: bool,
    pub is_online: bool,
    pub config: ConsensusConfig,
    pub finalized_blocks: Vec<(RevocationBlock, QuorumCertificate)>,
    pub epoch: u64,
    pub pending_reconfig: Option<ReconfigurationVotes>,
    pub local_state_root: [u8; 32],
    pub pending_state_roots: Option<PendingStateRoots>,
}

impl ConsensusState {
    /// Create a new consensus state for a node.
    pub fn new(node_id: usize, signing_key: SigningKey, config: ConsensusConfig) -> Self {
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
            local_state_root: [0u8; 32],
            pending_state_roots: None,
        }
    }

    /// Set the local state root for divergence detection.
    pub fn set_local_state_root(&mut self, root: [u8; 32]) {
        self.local_state_root = root;
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
    pub fn create_proposal(&mut self) -> Option<RevocationBlock> {
        let roots = self
            .pending_state_roots
            .take()
            .unwrap_or(PendingStateRoots {
                pre_state_root: [0u8; 32],
                post_state_root: [0u8; 32],
                note_tree_root: [0u8; 32],
                nullifier_set_root: [0u8; 32],
            });
        self.create_proposal_with_state_roots(
            roots.pre_state_root,
            roots.post_state_root,
            roots.note_tree_root,
            roots.nullifier_set_root,
        )
    }

    /// As leader: create a proposal block with explicit state roots.
    pub fn create_proposal_with_state_roots(
        &mut self,
        pre_state_root: [u8; 32],
        post_state_root: [u8; 32],
        note_tree_root: [u8; 32],
        nullifier_set_root: [u8; 32],
    ) -> Option<RevocationBlock> {
        if !self.is_leader() || self.pending_events.is_empty() {
            return None;
        }

        let events = std::mem::take(&mut self.pending_events);
        let block_hash = RevocationBlock::compute_hash_with_state_roots(
            self.current_height,
            self.current_view,
            self.node_id,
            &events,
            &self.last_finalized_hash,
            &pre_state_root,
            &post_state_root,
            &note_tree_root,
            &nullifier_set_root,
        );

        let proposer_signature = sign(&self.signing_key, &block_hash);

        let block = RevocationBlock {
            height: self.current_height,
            view: self.current_view,
            proposer: self.node_id,
            events,
            prev_hash: self.last_finalized_hash,
            block_hash,
            proposer_signature: Some(proposer_signature),
            pre_state_root,
            post_state_root,
            note_tree_root,
            nullifier_set_root,
            transition_proof: None,
        };

        self.current_proposal = Some(block.clone());
        Some(block)
    }

    /// As a voter: validate and vote on a proposed block.
    pub fn vote_on_proposal(&mut self, block: &RevocationBlock) -> Option<Vote> {
        if !self.is_online || self.has_voted {
            return None;
        }

        if !self.validate_block(block) {
            return None;
        }

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
        if let Some(ref proposal) = self.current_proposal {
            if vote.block_hash != proposal.block_hash {
                return None;
            }
        } else {
            return None;
        }

        if self.collected_votes.iter().any(|v| v.voter == vote.voter) {
            return None;
        }

        if !self.config.members.is_empty() {
            if let Some(voter_pubkey) = self.config.members.get(vote.voter) {
                let vote_msg =
                    QuorumCertificate::vote_message(&vote.block_hash, vote.height, vote.view);
                if !voter_pubkey.verify(&vote_msg, &vote.signature) {
                    return None;
                }
            } else {
                return None;
            }
        } else if self.config.require_authentication {
            tracing::warn!(
                "INSECURE: accepting vote without signature verification (legacy mode)"
            );
        }

        self.collected_votes.push(vote);

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

    fn validate_block(&self, block: &RevocationBlock) -> bool {
        if block.height != self.current_height {
            return false;
        }
        if block.view != self.current_view {
            return false;
        }
        if block.prev_hash != self.last_finalized_hash {
            return false;
        }
        let expected_hash = RevocationBlock::compute_hash_with_state_roots(
            block.height,
            block.view,
            block.proposer,
            &block.events,
            &block.prev_hash,
            &block.pre_state_root,
            &block.post_state_root,
            &block.note_tree_root,
            &block.nullifier_set_root,
        );
        if block.block_hash != expected_hash {
            return false;
        }
        if block.events.is_empty() {
            return false;
        }
        let expected_leader = self.config.leader_for_view(block.view);
        if block.proposer != expected_leader {
            return false;
        }
        // Divergence detection.
        let zero = [0u8; 32];
        if self.local_state_root != zero {
            if block.pre_state_root == zero {
                return false;
            }
            if block.pre_state_root != self.local_state_root {
                return false;
            }
        }
        // Proposer signature verification.
        if !self.config.members.is_empty() {
            match &block.proposer_signature {
                Some(sig) => {
                    if let Some(proposer_pubkey) = self.config.members.get(block.proposer) {
                        if !proposer_pubkey.verify(&block.block_hash, sig) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                None => {
                    return false;
                }
            }
        } else if self.config.require_authentication {
            tracing::warn!(
                "INSECURE: accepting proposal without proposer signature verification (legacy mode)"
            );
        }
        true
    }

    fn vote_message(&self, block: &RevocationBlock) -> Vec<u8> {
        QuorumCertificate::vote_message(&block.block_hash, block.height, block.view)
    }
}

// =============================================================================
// Consensus Orchestrator
// =============================================================================

/// Drives a full consensus round for a set of nodes (synchronous simulation).
pub struct ConsensusOrchestrator {
    pub config: ConsensusConfig,
    pub committee: Option<crate::threshold::FederationCommittee>,
    pub member_secrets: Vec<crate::threshold::MemberSecret>,
    pub pending_reconfig: Option<ReconfigurationVotes>,
    pub epoch_length: u64,
}

impl ConsensusOrchestrator {
    pub fn new(config: ConsensusConfig) -> Self {
        Self {
            config,
            committee: None,
            member_secrets: Vec::new(),
            pending_reconfig: None,
            epoch_length: 0,
        }
    }

    pub fn new_with_epoch_length(config: ConsensusConfig, epoch_length: u64) -> Self {
        Self {
            config,
            committee: None,
            member_secrets: Vec::new(),
            pending_reconfig: None,
            epoch_length,
        }
    }

    pub fn with_threshold_committee(
        mut self,
        committee: crate::threshold::FederationCommittee,
        member_secrets: Vec<crate::threshold::MemberSecret>,
    ) -> Self {
        self.committee = Some(committee);
        self.member_secrets = member_secrets;
        self
    }

    pub fn propose_reconfiguration(
        &mut self,
        proposal: ReconfigurationProposal,
    ) -> Result<(), ConsensusError> {
        if proposal.epoch != self.config.epoch {
            return Err(ConsensusError::EpochMismatch {
                expected: self.config.epoch,
                got: proposal.epoch,
            });
        }
        if !self.config.members.is_empty() && !self.config.members.contains(&proposal.proposer) {
            return Err(ConsensusError::NotAMember);
        }
        if self.pending_reconfig.is_some() {
            return Err(ConsensusError::ReconfigAlreadyPending);
        }
        if proposal.new_members.is_empty() {
            return Err(ConsensusError::EmptyMemberSet);
        }
        if !proposal.verify_signature() {
            return Err(ConsensusError::NotAMember);
        }

        let proposal_hash = proposal.hash();
        let proposer_sig = proposal.signature.clone();
        let voters = vec![(proposal.proposer.clone(), proposer_sig)];

        self.pending_reconfig = Some(ReconfigurationVotes {
            proposal,
            proposal_hash,
            voters,
        });

        Ok(())
    }

    pub fn vote_reconfiguration(
        &mut self,
        proposal_hash: [u8; 32],
        voter: &SigningKey,
    ) -> Result<(), ConsensusError> {
        let reconfig = self
            .pending_reconfig
            .as_mut()
            .ok_or(ConsensusError::NoPendingReconfig)?;

        if reconfig.proposal_hash != proposal_hash {
            return Err(ConsensusError::NoPendingReconfig);
        }

        let voter_pubkey = voter.public_key();

        if !self.config.members.is_empty() && !self.config.members.contains(&voter_pubkey) {
            return Err(ConsensusError::VoterNotMember);
        }

        if reconfig.voters.iter().any(|(pk, _)| pk == &voter_pubkey) {
            return Err(ConsensusError::AlreadyVoted);
        }

        let vote_sig = sign(voter, &proposal_hash);

        if !voter_pubkey.verify(&proposal_hash, &vote_sig) {
            return Err(ConsensusError::VoterNotMember);
        }

        reconfig.voters.push((voter_pubkey, vote_sig));
        Ok(())
    }

    pub fn pending_reconfiguration(&self) -> Option<&ReconfigurationProposal> {
        self.pending_reconfig.as_ref().map(|r| &r.proposal)
    }

    pub fn reconfig_has_quorum(&self) -> bool {
        match &self.pending_reconfig {
            Some(reconfig) => reconfig.voters.len() >= self.config.threshold,
            None => false,
        }
    }

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
    pub fn run_round(
        &mut self,
        states: &mut [ConsensusState],
    ) -> Option<(RevocationBlock, QuorumCertificate)> {
        let view = states[0].current_view;
        let leader_id = self.config.leader_for_view(view);

        if !states[leader_id].is_online {
            for state in states.iter_mut() {
                if state.is_online {
                    state.advance_view();
                }
            }
            let new_view = states
                .iter()
                .find(|s| s.is_online)
                .map(|s| s.current_view)?;
            let new_leader = self.config.leader_for_view(new_view);
            if !states[new_leader].is_online {
                for state in states.iter_mut() {
                    if state.is_online {
                        state.advance_view();
                    }
                }
            }
        }

        let current_view = states.iter().find(|s| s.is_online)?.current_view;
        let leader_id = self.config.leader_for_view(current_view);

        if !states[leader_id].is_online {
            return None;
        }

        let mut all_pending: Vec<RevocationEvent> = Vec::new();
        for state in states.iter_mut() {
            if state.is_online {
                all_pending.extend(state.pending_events.drain(..));
            }
        }
        states[leader_id].pending_events = all_pending;

        let proposal = states[leader_id].create_proposal()?;

        let leader_vote = states[leader_id].vote_on_proposal(&proposal)?;
        states[leader_id].collect_vote(leader_vote);

        let mut votes = Vec::new();
        for state in states.iter_mut() {
            if state.node_id == leader_id {
                continue;
            }
            if let Some(vote) = state.vote_on_proposal(&proposal) {
                votes.push(vote);
            }
        }

        let mut qc = None;
        for vote in votes {
            if let Some(certificate) = states[leader_id].collect_vote(vote) {
                qc = Some(certificate);
                break;
            }
        }

        let mut qc = qc?;

        if let Some(ref committee) = self.committee {
            let message = QuorumCertificate::vote_message(&qc.block_hash, qc.height, qc.view);
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

        for state in states.iter_mut() {
            if state.is_online {
                state.finalize_block(proposal.clone(), qc.clone());
            }
        }

        let finalized_height = proposal.height;
        let at_epoch_boundary = self.epoch_length == 0
            || crate::epoch::is_epoch_boundary(finalized_height, self.epoch_length);

        if self.reconfig_has_quorum() && at_epoch_boundary {
            if let Some(new_config) = self.apply_pending_reconfiguration() {
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
// Federation Node
// =============================================================================

/// A single federation node that participates in revocation consensus.
#[derive(Clone)]
pub struct FederationNode {
    /// The node's identity.
    pub identity: NodeIdentity,
    /// The node's signing key.
    pub signing_key: SigningKey,
    /// The local revocation tree (Merkle tree of revoked token IDs).
    pub revocation_tree: RevocationTree,
    /// The latest attested root (after consensus finalization).
    pub attested_root: Option<AttestedRoot>,
    /// Tokens minted by this node.
    pub minted_tokens: Vec<Token>,
    /// Whether this node is online.
    pub is_online: bool,
}

impl FederationNode {
    /// Create a new federation node.
    pub fn new(name: &str, id: usize) -> Self {
        let (signing_key, public_key) = generate_keypair();

        Self {
            identity: NodeIdentity {
                name: name.to_string(),
                id,
                public_key,
            },
            signing_key,
            revocation_tree: RevocationTree::new(),
            attested_root: None,
            minted_tokens: Vec::new(),
            is_online: true,
        }
    }

    /// Mint a new token.
    pub fn mint_token(&mut self, holder: &str) -> Token {
        let mut id_bytes = [0u8; 16];
        getrandom::fill(&mut id_bytes).expect("getrandom failed");
        let token_id = hex_encode(&id_bytes[..8]);

        let sig_message = format!("mint:{}", token_id);
        let signature = sign(&self.signing_key, sig_message.as_bytes());

        let token = Token {
            id: token_id,
            holder: holder.to_string(),
            issuer_id: self.identity.id,
            issuer_key: self.identity.public_key.clone(),
            signature,
        };

        self.minted_tokens.push(token.clone());
        token
    }

    /// Create a revocation event (to be submitted to consensus).
    pub fn create_revocation_event(&self, token_id: &str) -> RevocationEvent {
        let revoke_message = format!("revoke:{}", token_id);
        let signature = sign(&self.signing_key, revoke_message.as_bytes());

        RevocationEvent {
            token_id: token_id.to_string(),
            authority_id: self.identity.id,
            signature,
        }
    }

    /// Apply a finalized block of revocations to the local tree.
    pub fn apply_finalized_block(&mut self, block: &RevocationBlock) {
        let token_ids: Vec<String> = block.events.iter().map(|e| e.token_id.clone()).collect();
        self.revocation_tree.revoke_batch(&token_ids);
    }

    /// Compute the current state root (revocation tree Merkle root).
    /// This is the pre-state root before any new events are applied.
    pub fn compute_state_root(&mut self) -> [u8; 32] {
        self.revocation_tree.root()
    }

    /// Update the attested root after consensus finalization.
    pub fn update_attested_root(&mut self, qc: &QuorumCertificate, nodes: &[NodeIdentity]) {
        let merkle_root = self.revocation_tree.root();
        let timestamp = current_timestamp();

        let quorum_signatures = qc.quorum_signatures(nodes);

        self.attested_root = Some(AttestedRoot {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height: qc.height,
            timestamp,
            threshold_qc: qc
                .aggregate_qc
                .as_ref()
                .map(|q| pyana_types::ThresholdQC(q.to_bytes())),
            quorum_signatures,
            threshold: qc.threshold,
        });
    }

    /// Get the current attested root.
    pub fn get_attested_root(&self) -> Option<&AttestedRoot> {
        self.attested_root.as_ref()
    }

    /// Verify that a token is NOT revoked (produces a non-membership proof).
    pub fn verify_non_membership(&self, token_id: &str) -> Option<RevocationProof> {
        let attested_root = self.attested_root.as_ref()?;
        RevocationVerifier::build_proof(&self.revocation_tree, attested_root, token_id)
    }

    /// Check if a token is in the local revocation set.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revocation_tree.is_revoked(token_id)
    }

    /// Get the current Merkle root of the revocation tree.
    pub fn current_root(&mut self) -> [u8; 32] {
        self.revocation_tree.root()
    }

    /// Set the node's online status.
    pub fn set_online(&mut self, online: bool) {
        self.is_online = online;
    }
}

// =============================================================================
// Federation
// =============================================================================

/// A federation of multiple nodes participating in revocation consensus.
pub struct Federation {
    /// The federation nodes.
    pub nodes: Vec<FederationNode>,
    /// Consensus states for each node.
    pub consensus_states: Vec<ConsensusState>,
    /// The consensus orchestrator.
    pub orchestrator: ConsensusOrchestrator,
    /// The consensus configuration.
    pub config: ConsensusConfig,
    /// History of all finalized blocks.
    pub finalized_history: Vec<(RevocationBlock, QuorumCertificate)>,
}

impl Federation {
    /// Create a new federation with the given node names.
    pub fn new(names: &[&str]) -> Self {
        let n = names.len();
        let config = ConsensusConfig::new(n);

        let nodes: Vec<FederationNode> = names
            .iter()
            .enumerate()
            .map(|(i, name)| FederationNode::new(name, i))
            .collect();

        let consensus_states: Vec<ConsensusState> = nodes
            .iter()
            .map(|node| {
                ConsensusState::new(node.identity.id, node.signing_key.clone(), config.clone())
            })
            .collect();

        let orchestrator = ConsensusOrchestrator::new(config.clone());

        Self {
            nodes,
            consensus_states,
            orchestrator,
            config,
            finalized_history: Vec::new(),
        }
    }

    /// Get the node identities for QC signature resolution.
    pub fn node_identities(&self) -> Vec<NodeIdentity> {
        self.nodes.iter().map(|n| n.identity.clone()).collect()
    }

    /// Submit a revocation event from a specific node.
    pub fn submit_revocation(&mut self, from_node: usize, token_id: &str) {
        let event = self.nodes[from_node].create_revocation_event(token_id);
        // Submit to the node's consensus state.
        self.consensus_states[from_node].submit_revocation(event);
    }

    /// Run a consensus round and apply the result to all nodes.
    /// Returns the finalized block and QC, or None if consensus failed.
    pub fn run_consensus_round(&mut self) -> Option<(RevocationBlock, QuorumCertificate)> {
        // Sync online status and local state roots for divergence detection.
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if i < self.consensus_states.len() {
                self.consensus_states[i].set_online(node.is_online);
                // Update the consensus state's local_state_root from the node's
                // revocation tree. This enables divergence detection in validate_block().
                let root = node.compute_state_root();
                self.consensus_states[i].set_local_state_root(root);
                // Set pending_state_roots so that any node that becomes leader
                // will include proper state roots in its proposal. This ensures
                // divergence detection works correctly.
                self.consensus_states[i].pending_state_roots = Some(PendingStateRoots {
                    pre_state_root: root,
                    post_state_root: [0u8; 32], // computed after applying events
                    note_tree_root: [0u8; 32],
                    nullifier_set_root: [0u8; 32],
                });
            }
        }

        // Run the consensus round.
        let result = self.orchestrator.run_round(&mut self.consensus_states)?;
        let (block, qc) = result;

        // Apply the finalized block to all online nodes.
        let identities = self.node_identities();
        for node in &mut self.nodes {
            if node.is_online {
                node.apply_finalized_block(&block);
                node.update_attested_root(&qc, &identities);
            }
        }

        // Keep Federation.config in sync if the orchestrator applied a reconfig.
        if self.config.epoch != self.orchestrator.config.epoch {
            self.config = self.orchestrator.config.clone();
        }

        self.finalized_history.push((block.clone(), qc.clone()));
        Some((block, qc))
    }

    /// Run a consensus round with state root commitments.
    ///
    /// This variant computes pre/post state roots for the proposing node,
    /// enabling divergence detection and light client verification.
    pub fn run_consensus_round_with_state_roots(
        &mut self,
    ) -> Option<(RevocationBlock, QuorumCertificate, LightClientProof)> {
        // Sync online status and local state roots for divergence detection.
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if i < self.consensus_states.len() {
                self.consensus_states[i].set_online(node.is_online);
                let root = node.compute_state_root();
                self.consensus_states[i].set_local_state_root(root);
            }
        }

        // Determine leader and compute pre_state_root from the leader's tree.
        let view = self
            .consensus_states
            .iter()
            .find(|s| s.is_online)?
            .current_view;
        let leader_id = self.config.leader_for_view(view);
        if leader_id >= self.nodes.len() || !self.nodes[leader_id].is_online {
            // Fall back to standard round if leader identification fails.
            return self.run_consensus_round().map(|(b, qc)| {
                let proof = LightClientProof::from_block(&b, &qc);
                (b, qc, proof)
            });
        }

        let pre_state_root = self.nodes[leader_id].compute_state_root();

        // Simulate what events will be included: gather all pending events
        // and apply them to a clone of the leader's tree to get post_state_root.
        let pending_events: Vec<RevocationEvent> = self
            .consensus_states
            .iter()
            .filter(|s| s.is_online)
            .flat_map(|s| s.pending_events.clone())
            .collect();

        let mut tree_clone = self.nodes[leader_id].revocation_tree.clone();
        let token_ids: Vec<String> = pending_events.iter().map(|e| e.token_id.clone()).collect();
        tree_clone.revoke_batch(&token_ids);
        let post_state_root = tree_clone.root();

        // Note tree and nullifier set roots are not managed by the federation
        // revocation tree directly -- they come from the store layer. For now,
        // we use zero roots (the node crate can override these when it has store access).
        let note_tree_root = [0u8; 32];
        let nullifier_set_root = [0u8; 32];

        // Inject state roots into the leader's consensus state for proposal creation.
        // We do this by temporarily overriding the create_proposal path.
        // Actually, we need to use the orchestrator which calls create_proposal internally.
        // The cleanest approach: set state roots on the consensus state, then let
        // run_round use them. Let's add support for that.

        // Store the state roots on the leader's consensus state for the orchestrator.
        self.consensus_states[leader_id].pending_state_roots = Some(PendingStateRoots {
            pre_state_root,
            post_state_root,
            note_tree_root,
            nullifier_set_root,
        });

        // Run the consensus round.
        let result = self.orchestrator.run_round(&mut self.consensus_states)?;
        let (block, qc) = result;

        // Apply the finalized block to all online nodes.
        let identities = self.node_identities();
        for node in &mut self.nodes {
            if node.is_online {
                node.apply_finalized_block(&block);
                node.update_attested_root(&qc, &identities);
            }
        }

        // Keep Federation.config in sync if the orchestrator applied a reconfig.
        if self.config.epoch != self.orchestrator.config.epoch {
            self.config = self.orchestrator.config.clone();
        }

        let proof = LightClientProof::from_block(&block, &qc);
        self.finalized_history.push((block.clone(), qc.clone()));
        Some((block, qc, proof))
    }

    /// Mint a token at a specific node.
    pub fn mint_token(&mut self, node_id: usize, holder: &str) -> Token {
        self.nodes[node_id].mint_token(holder)
    }

    /// Crash a node (take it offline for Byzantine fault simulation).
    pub fn crash_node(&mut self, node_id: usize) {
        self.nodes[node_id].set_online(false);
        self.consensus_states[node_id].set_online(false);
    }

    /// Recover a crashed node, replaying any finalized blocks it missed while offline.
    ///
    /// This performs state-sync: the node catches up with the federation's finalized
    /// history by applying blocks it missed to its local revocation tree and updating
    /// its consensus state (height, view, last_finalized_hash) to match.
    pub fn recover_node(&mut self, node_id: usize) {
        self.nodes[node_id].set_online(true);
        self.consensus_states[node_id].set_online(true);

        // Replay finalized blocks the node missed while it was offline.
        let node_height = self.consensus_states[node_id].finalized_blocks.len();
        let federation_height = self.finalized_history.len();

        if node_height < federation_height {
            let identities = self.node_identities();
            for i in node_height..federation_height {
                let (block, qc) = self.finalized_history[i].clone();
                // Apply the block to the node's revocation tree.
                self.nodes[node_id].apply_finalized_block(&block);
                self.nodes[node_id].update_attested_root(&qc, &identities);
                // Update the node's consensus state.
                self.consensus_states[node_id].finalize_block(block, qc);
            }
        }
    }

    /// Get the number of online nodes.
    pub fn online_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_online).count()
    }

    /// Verify a token's non-revocation from a specific node's perspective.
    pub fn verify_non_membership_from(
        &self,
        verifier_node: usize,
        token_id: &str,
    ) -> Option<RevocationProof> {
        self.nodes[verifier_node].verify_non_membership(token_id)
    }

    /// Check if all online nodes agree on the same root.
    pub fn roots_agree(&mut self) -> bool {
        let mut roots: Vec<[u8; 32]> = Vec::new();
        for node in &mut self.nodes {
            if node.is_online {
                roots.push(node.current_root());
            }
        }
        if roots.is_empty() {
            return true;
        }
        roots.windows(2).all(|w| w[0] == w[1])
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::revocation::RevocationVerifier;

    #[test]
    fn create_federation() {
        let fed = Federation::new(&["alpha", "beta", "gamma", "delta"]);
        assert_eq!(fed.nodes.len(), 4);
        assert_eq!(fed.config.threshold, 3);
        assert_eq!(fed.config.max_faults, 1);
    }

    #[test]
    fn mint_tokens() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");
        let t2 = fed.mint_token(1, "Bob");
        assert_ne!(t1.id, t2.id);
        assert_eq!(t1.issuer_id, 0);
        assert_eq!(t2.issuer_id, 1);
    }

    #[test]
    fn revocation_consensus() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");

        // Submit revocation.
        fed.submit_revocation(0, &t1.id);

        // Run consensus.
        let result = fed.run_consensus_round();
        assert!(result.is_some());

        let (block, qc) = result.unwrap();
        assert_eq!(block.events.len(), 1);
        assert_eq!(block.events[0].token_id, t1.id);
        assert!(qc.is_valid());

        // All nodes should agree on the root.
        assert!(fed.roots_agree());

        // Token should be revoked on all nodes.
        for node in &fed.nodes {
            assert!(node.is_revoked(&t1.id));
        }
    }

    #[test]
    fn non_membership_proof_after_revocation() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");
        let t2 = fed.mint_token(1, "Bob");

        // Revoke t1.
        fed.submit_revocation(0, &t1.id);
        fed.run_consensus_round();

        // t2 should have a valid non-membership proof.
        let proof = fed.verify_non_membership_from(2, &t2.id);
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let verification = RevocationVerifier::verify(&proof);
        assert!(verification.valid);

        // t1 should NOT have a non-membership proof (it's revoked).
        let no_proof = fed.verify_non_membership_from(2, &t1.id);
        assert!(no_proof.is_none());
    }

    #[test]
    fn byzantine_fault_tolerance() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");

        // Crash one node.
        fed.crash_node(3);

        // Submit revocation.
        fed.submit_revocation(0, &t1.id);

        // Should still reach consensus.
        let result = fed.run_consensus_round();
        assert!(result.is_some());

        // Online nodes should agree.
        let mut online_roots: Vec<[u8; 32]> = Vec::new();
        for node in &mut fed.nodes {
            if node.is_online {
                online_roots.push(node.current_root());
            }
        }
        assert_eq!(online_roots.len(), 3);
        assert!(online_roots.windows(2).all(|w| w[0] == w[1]));
    }
}
