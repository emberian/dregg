//! Route governance: propose, vote on, and amend the routing table democratically.
//!
//! The governance model implements threshold voting (2n/3 + 1 required to pass):
//! - Any participant can propose a new route table (as a JSON description)
//! - Participants vote approve/reject on pending proposals
//! - When a proposal reaches threshold, it is enacted atomically
//! - History of all enacted amendments is preserved for auditing
//!
//! ## Circuit provability
//!
//! - "I am a valid participant" → membership proof (body membership circuit)
//! - "I voted on proposal P" → signature proof bound to proposal commitment
//! - "Proposal P reached threshold T" → aggregated vote count proof
//! - "The routing table changed from C_old to C_new via proposal P" → state transition proof

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::routes::{RouteEntry, RoutingTable};
use crate::storage::hex;

/// A participant in the governance process.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Participant {
    /// Unique identifier (could be a CellId hex, public key, etc.).
    pub id: String,
    /// Human-readable name.
    pub name: Option<String>,
    /// Weight of this participant's vote (default 1).
    pub weight: u32,
}

/// A vote on a proposal.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Vote {
    /// Who voted.
    pub participant_id: String,
    /// Whether they approve.
    pub approve: bool,
    /// Unix timestamp of the vote.
    pub timestamp: u64,
}

/// Status of a governance proposal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProposalStatus {
    /// Awaiting votes.
    Pending,
    /// Reached threshold and was enacted.
    Passed,
    /// Explicitly rejected (enough reject votes to make passage impossible).
    Rejected,
    /// Superseded by a later proposal that passed.
    Superseded,
}

/// A governance proposal to amend the routing table.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proposal {
    /// Unique proposal ID (blake3 of proposer + proposed routes + timestamp).
    pub id: String,
    /// Who proposed this amendment.
    pub proposer: String,
    /// The proposed new route table entries.
    pub proposed_routes: Vec<RouteEntry>,
    /// The blake3 commitment of the proposed route table.
    pub proposed_commitment: String,
    /// Human-readable description of why this change is needed.
    pub description: String,
    /// Current status.
    pub status: ProposalStatus,
    /// Votes cast so far.
    pub votes: Vec<Vote>,
    /// Unix timestamp when proposed.
    pub created_at: u64,
    /// Unix timestamp when resolved (passed/rejected), if applicable.
    pub resolved_at: Option<u64>,
}

/// Record of an enacted amendment (for history).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Amendment {
    /// The proposal that was enacted.
    pub proposal_id: String,
    /// The old route table commitment (before this amendment).
    pub old_commitment: String,
    /// The new route table commitment (after this amendment).
    pub new_commitment: String,
    /// Version number of the new table.
    pub version: u64,
    /// Unix timestamp of enactment.
    pub enacted_at: u64,
}

/// The constitution: governance parameters + participant set.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Constitution {
    /// Set of authorized participants.
    pub participants: Vec<Participant>,
    /// Voting threshold formula: threshold = (total_weight * 2) / 3 + 1
    /// This is computed dynamically from the participant set.
    pub threshold_numerator: u32,
    pub threshold_denominator: u32,
    /// Current routing table commitment hash.
    pub routes_commitment: String,
}

/// Governance engine managing proposals, votes, and amendments.
#[derive(Clone)]
pub struct GovernanceEngine {
    /// The set of participants authorized to vote.
    participants: Arc<RwLock<Vec<Participant>>>,
    /// Pending and resolved proposals.
    proposals: Arc<RwLock<Vec<Proposal>>>,
    /// History of enacted amendments.
    amendments: Arc<RwLock<Vec<Amendment>>>,
    /// The live routing table (shared with the router).
    routing_table: Arc<RwLock<RoutingTable>>,
}

impl GovernanceEngine {
    /// Create a new governance engine with initial participants and routing table.
    pub fn new(participants: Vec<Participant>, routing_table: Arc<RwLock<RoutingTable>>) -> Self {
        Self {
            participants: Arc::new(RwLock::new(participants)),
            proposals: Arc::new(RwLock::new(Vec::new())),
            amendments: Arc::new(RwLock::new(Vec::new())),
            routing_table,
        }
    }

    /// Compute the voting threshold from the current participant set.
    /// threshold = (total_weight * 2) / 3 + 1
    pub async fn threshold(&self) -> u32 {
        let participants = self.participants.read().await;
        let total_weight: u32 = participants.iter().map(|p| p.weight).sum();
        (total_weight * 2) / 3 + 1
    }

    /// Get the total voting weight.
    pub async fn total_weight(&self) -> u32 {
        self.participants
            .read()
            .await
            .iter()
            .map(|p| p.weight)
            .sum()
    }

    /// Check if an ID corresponds to a registered participant.
    pub async fn is_participant(&self, id: &str) -> bool {
        self.participants.read().await.iter().any(|p| p.id == id)
    }

    /// Get the weight of a participant (0 if not found).
    pub async fn participant_weight(&self, id: &str) -> u32 {
        self.participants
            .read()
            .await
            .iter()
            .find(|p| p.id == id)
            .map(|p| p.weight)
            .unwrap_or(0)
    }

    /// Propose a new route table amendment.
    ///
    /// Returns the proposal ID on success.
    pub async fn propose(
        &self,
        proposer: String,
        proposed_routes: Vec<RouteEntry>,
        description: String,
    ) -> Result<String, GovernanceError> {
        // Verify proposer is a participant.
        if !self.is_participant(&proposer).await {
            return Err(GovernanceError::NotParticipant);
        }

        // Compute commitment for the proposed routes.
        let mut proposed_table = RoutingTable::new();
        for entry in &proposed_routes {
            proposed_table.add_route(entry.clone());
        }
        let proposed_commitment = hex::encode(proposed_table.commitment());

        // Generate proposal ID.
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        let id_input = format!("{proposer}:{proposed_commitment}:{now}");
        let id = hex::encode(*blake3::hash(id_input.as_bytes()).as_bytes());

        let proposal = Proposal {
            id: id.clone(),
            proposer,
            proposed_routes,
            proposed_commitment,
            description,
            status: ProposalStatus::Pending,
            votes: Vec::new(),
            created_at: now,
            resolved_at: None,
        };

        self.proposals.write().await.push(proposal);
        Ok(id)
    }

    /// Cast a vote on a pending proposal.
    ///
    /// Returns the updated proposal status after the vote.
    pub async fn vote(
        &self,
        proposal_id: &str,
        voter: String,
        approve: bool,
    ) -> Result<ProposalStatus, GovernanceError> {
        // Verify voter is a participant.
        if !self.is_participant(&voter).await {
            return Err(GovernanceError::NotParticipant);
        }

        let mut proposals = self.proposals.write().await;
        let proposal = proposals
            .iter_mut()
            .find(|p| p.id == proposal_id)
            .ok_or(GovernanceError::ProposalNotFound)?;

        // Must be pending.
        if proposal.status != ProposalStatus::Pending {
            return Err(GovernanceError::ProposalNotPending);
        }

        // Check for duplicate vote.
        if proposal.votes.iter().any(|v| v.participant_id == voter) {
            return Err(GovernanceError::AlreadyVoted);
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        proposal.votes.push(Vote {
            participant_id: voter.clone(),
            approve,
            timestamp: now,
        });

        // Check if threshold is reached.
        let threshold = self.threshold().await;
        let approve_weight = self.tally_approve_weight(proposal).await;
        let reject_weight = self.tally_reject_weight(proposal).await;
        let total_weight = self.total_weight().await;

        if approve_weight >= threshold {
            proposal.status = ProposalStatus::Passed;
            proposal.resolved_at = Some(now);
            let proposed_routes = proposal.proposed_routes.clone();
            let proposal_id = proposal.id.clone();
            let proposed_commitment = proposal.proposed_commitment.clone();
            drop(proposals);

            // Enact the amendment.
            self.enact_amendment(proposal_id, proposed_routes, proposed_commitment)
                .await;

            Ok(ProposalStatus::Passed)
        } else if reject_weight > total_weight - threshold {
            // Enough rejections that passage is impossible.
            proposal.status = ProposalStatus::Rejected;
            proposal.resolved_at = Some(now);
            Ok(ProposalStatus::Rejected)
        } else {
            Ok(ProposalStatus::Pending)
        }
    }

    /// Tally approve weight for a proposal.
    async fn tally_approve_weight(&self, proposal: &Proposal) -> u32 {
        let mut weight = 0;
        for vote in &proposal.votes {
            if vote.approve {
                weight += self.participant_weight(&vote.participant_id).await;
            }
        }
        weight
    }

    /// Tally reject weight for a proposal.
    async fn tally_reject_weight(&self, proposal: &Proposal) -> u32 {
        let mut weight = 0;
        for vote in &proposal.votes {
            if !vote.approve {
                weight += self.participant_weight(&vote.participant_id).await;
            }
        }
        weight
    }

    /// Enact a passed amendment: atomically swap the live routing table.
    async fn enact_amendment(
        &self,
        proposal_id: String,
        new_routes: Vec<RouteEntry>,
        new_commitment: String,
    ) {
        let mut table = self.routing_table.write().await;
        let old_commitment = hex::encode(table.commitment());
        table.replace_all(new_routes);
        let version = table.version;
        drop(table);

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        let amendment = Amendment {
            proposal_id,
            old_commitment,
            new_commitment,
            version,
            enacted_at: now,
        };

        self.amendments.write().await.push(amendment);
    }

    /// Get the current constitution state.
    pub async fn constitution(&self) -> Constitution {
        let participants = self.participants.read().await.clone();
        let table = self.routing_table.read().await;
        let routes_commitment = hex::encode(table.commitment());

        Constitution {
            participants,
            threshold_numerator: 2,
            threshold_denominator: 3,
            routes_commitment,
        }
    }

    /// Get all pending proposals.
    pub async fn pending_proposals(&self) -> Vec<Proposal> {
        self.proposals
            .read()
            .await
            .iter()
            .filter(|p| p.status == ProposalStatus::Pending)
            .cloned()
            .collect()
    }

    /// Get all proposals (including resolved).
    pub async fn all_proposals(&self) -> Vec<Proposal> {
        self.proposals.read().await.clone()
    }

    /// Get amendment history.
    pub async fn amendment_history(&self) -> Vec<Amendment> {
        self.amendments.read().await.clone()
    }

    /// Get the live routing table (read-only snapshot).
    pub async fn current_routes(&self) -> RoutingTable {
        self.routing_table.read().await.clone()
    }
}

/// Errors from governance operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GovernanceError {
    /// The caller is not a registered participant.
    NotParticipant,
    /// The proposal was not found.
    ProposalNotFound,
    /// The proposal is not in Pending status.
    ProposalNotPending,
    /// The participant has already voted on this proposal.
    AlreadyVoted,
}

impl std::fmt::Display for GovernanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GovernanceError::NotParticipant => write!(f, "not a registered participant"),
            GovernanceError::ProposalNotFound => write!(f, "proposal not found"),
            GovernanceError::ProposalNotPending => write!(f, "proposal is not pending"),
            GovernanceError::AlreadyVoted => write!(f, "already voted on this proposal"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::routes::RouteClass;

    fn test_participants() -> Vec<Participant> {
        vec![
            Participant {
                id: "alice".to_string(),
                name: Some("Alice".to_string()),
                weight: 1,
            },
            Participant {
                id: "bob".to_string(),
                name: Some("Bob".to_string()),
                weight: 1,
            },
            Participant {
                id: "carol".to_string(),
                name: Some("Carol".to_string()),
                weight: 1,
            },
        ]
    }

    #[tokio::test]
    async fn threshold_calculation() {
        let table = Arc::new(RwLock::new(RoutingTable::default_dao()));
        let engine = GovernanceEngine::new(test_participants(), table);

        // 3 participants with weight 1 each. threshold = (3*2)/3 + 1 = 3.
        assert_eq!(engine.threshold().await, 3);
    }

    #[tokio::test]
    async fn propose_and_pass() {
        let table = Arc::new(RwLock::new(RoutingTable::default_dao()));
        let engine = GovernanceEngine::new(test_participants(), table.clone());

        let new_routes = vec![
            RouteEntry {
                prefix: "/public/".to_string(),
                class: RouteClass::Public,
                description: None,
            },
            RouteEntry {
                prefix: "/grants/".to_string(),
                class: RouteClass::MembersOnly,
                description: Some("New grants route".to_string()),
            },
        ];

        let proposal_id = engine
            .propose(
                "alice".to_string(),
                new_routes,
                "Add /grants/ route".to_string(),
            )
            .await
            .unwrap();

        // Vote: alice approves.
        let status = engine
            .vote(&proposal_id, "alice".to_string(), true)
            .await
            .unwrap();
        assert_eq!(status, ProposalStatus::Pending);

        // Vote: bob approves.
        let status = engine
            .vote(&proposal_id, "bob".to_string(), true)
            .await
            .unwrap();
        assert_eq!(status, ProposalStatus::Pending);

        // Vote: carol approves → threshold reached (3/3 >= 3).
        let status = engine
            .vote(&proposal_id, "carol".to_string(), true)
            .await
            .unwrap();
        assert_eq!(status, ProposalStatus::Passed);

        // Verify the routing table was updated.
        let current = table.read().await;
        assert_eq!(current.version, 1);
        assert_eq!(current.len(), 2);
    }

    #[tokio::test]
    async fn non_participant_cannot_propose() {
        let table = Arc::new(RwLock::new(RoutingTable::default_dao()));
        let engine = GovernanceEngine::new(test_participants(), table);

        let err = engine
            .propose("eve".to_string(), vec![], "malicious".to_string())
            .await
            .unwrap_err();
        assert_eq!(err, GovernanceError::NotParticipant);
    }

    #[tokio::test]
    async fn duplicate_vote_rejected() {
        let table = Arc::new(RwLock::new(RoutingTable::default_dao()));
        let engine = GovernanceEngine::new(test_participants(), table);

        let proposal_id = engine
            .propose("alice".to_string(), vec![], "test".to_string())
            .await
            .unwrap();

        engine
            .vote(&proposal_id, "alice".to_string(), true)
            .await
            .unwrap();

        let err = engine
            .vote(&proposal_id, "alice".to_string(), true)
            .await
            .unwrap_err();
        assert_eq!(err, GovernanceError::AlreadyVoted);
    }
}
