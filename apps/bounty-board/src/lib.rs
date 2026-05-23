//! Federated bounty board: a privacy-preserving work marketplace built on pyana.
//!
//! # Architecture
//!
//! ```text
//! +-------------+     +--------------+     +-------------+
//! |   Issuer    |---->| Bounty Board |<----|   Worker    |
//! |  (wallet)   |     |   (node)     |     |  (wallet)   |
//! +-------------+     +--------------+     +-------------+
//!        |                    |                     |
//!   Post bounty         Store state          Claim + deliver
//!   (attenuated cap)   (intents + cells)    (conditional turn)
//! ```
//!
//! Workers prove qualifications without revealing identity. Issuers don't learn
//! who's working until delivery. Payment is released atomically via conditional
//! turns.

pub mod payment;
pub mod qualification;
pub mod state;

use pyana_app_framework::CellId;
use pyana_app_framework::PredicateType;
use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use pyana_turn::TurnReceipt;
use serde::{Deserialize, Serialize};

// =============================================================================
// Core Types
// =============================================================================

/// A bounty posted by an issuer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Bounty {
    /// Content-addressed bounty ID (BLAKE3 hash of creation parameters).
    pub id: [u8; 32],
    /// The issuer's cell identity.
    pub issuer_cell: CellId,
    /// Human-readable title.
    pub title: String,
    /// Full description of the work to be done.
    pub description: String,
    /// Reward amount (in the smallest denomination of the reward asset).
    pub reward_amount: u64,
    /// Asset type identifier for the reward.
    pub reward_asset: u64,
    /// Block height after which the bounty expires.
    pub deadline_height: u64,
    /// What qualifications a worker must prove to claim this bounty.
    pub qualification: QualificationRequirement,
    /// Current status of the bounty.
    pub status: BountyStatus,
    /// The attenuated token held in escrow for payment (serialized form).
    pub reward_token: Option<SerializedToken>,
    /// Block height at which this bounty was created.
    pub created_at: u64,
    /// Tags for filtering and discovery.
    pub tags: Vec<String>,
}

/// Serialized form of a held token for storage/transmission.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SerializedToken {
    pub encoded: String,
    pub service: String,
    pub label: String,
}

/// What qualifications a worker must demonstrate to claim a bounty.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum QualificationRequirement {
    /// Anyone can claim this bounty.
    None,
    /// Worker must prove federation membership (ring membership STARK).
    FederationMember,
    /// Worker must prove a predicate about a private attribute.
    PredicateProof {
        predicate_type: PredicateType,
        attribute: String,
        threshold: u64,
    },
    /// Worker must prove they've completed at least N prior bounties (IVC chain).
    StandingProof { min_completed_bounties: u64 },
}

/// The lifecycle status of a bounty.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BountyStatus {
    /// Available for workers to claim.
    Open,
    /// A worker has claimed this bounty (commitment hides their identity).
    Claimed {
        /// Blinded worker identity: Poseidon2(worker_key || randomness).
        worker_commitment: [u8; 32],
        /// Block height at which the claim was made.
        claimed_at: u64,
    },
    /// Worker has submitted completed work with proof.
    Submitted {
        /// Blinded worker identity (must match the claim).
        worker_commitment: [u8; 32],
        /// BLAKE3 hash of the completion proof bytes.
        completion_proof_hash: [u8; 32],
    },
    /// Issuer has approved the submission; payment is pending release.
    Approved,
    /// Payment has been released to the worker.
    Paid {
        /// Receipt hash proving the payment turn was executed.
        receipt_hash: [u8; 32],
    },
    /// The bounty expired without completion.
    Expired,
    /// The bounty is under dispute.
    Disputed { reason: String },
}

// =============================================================================
// Request / Response Types
// =============================================================================

/// Request to create a new bounty.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CreateBountyRequest {
    pub title: String,
    pub description: String,
    pub reward_amount: u64,
    pub reward_asset: u64,
    pub deadline_height: u64,
    pub qualification: QualificationRequirement,
    pub tags: Vec<String>,
    /// The issuer's cell ID (hex-encoded).
    pub issuer_cell: String,
    /// Serialized reward token for escrow.
    pub reward_token: Option<SerializedToken>,
}

/// Request to claim a bounty (worker presents blinded identity + qualification proof).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClaimRequest {
    /// The bounty to claim.
    pub bounty_id: String,
    /// Blinded worker identity: hash(worker_key || randomness).
    /// This commitment hides the worker's real identity from the issuer.
    pub worker_commitment: [u8; 32],
    /// Optional qualification proof (STARK bytes proving the worker meets requirements).
    pub qualification_proof: Option<Vec<u8>>,
}

/// Request to submit completed work.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubmitRequest {
    /// The bounty being completed.
    pub bounty_id: String,
    /// Must match the commitment used during claim.
    pub worker_commitment: [u8; 32],
    /// Evidence of completion.
    pub completion_evidence: CompletionEvidence,
    /// Cryptographic proof that work was done (receipt chain, STARK, etc.).
    pub completion_proof: Vec<u8>,
}

/// Evidence that work was completed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CompletionEvidence {
    /// A chain of turn receipts proving on-chain work was performed.
    ReceiptChain { receipts: Vec<TurnReceipt> },
    /// An external artifact with a content hash for verification.
    ExternalProof { url: String, hash: [u8; 32] },
    /// Peer review attestations from other federation members.
    PeerReview {
        /// Each attestation is a signed message from a reviewer.
        reviewer_attestations: Vec<Vec<u8>>,
    },
}

/// Request to approve a submission (issuer action).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ApproveRequest {
    pub bounty_id: String,
    /// Issuer's cell ID for authorization.
    pub issuer_cell: String,
}

/// Filter parameters for listing bounties.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BountyFilter {
    pub tag: Option<String>,
    pub min_reward: Option<u64>,
    pub max_reward: Option<u64>,
    pub status: Option<String>,
}

/// Summary of a bounty for list responses.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BountySummary {
    pub id: String,
    pub title: String,
    pub reward_amount: u64,
    pub reward_asset: u64,
    pub deadline_height: u64,
    pub status: String,
    pub tags: Vec<String>,
    pub qualification: String,
}

/// Detailed bounty status response.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BountyStatusResponse {
    pub id: String,
    pub title: String,
    pub description: String,
    pub reward_amount: u64,
    pub reward_asset: u64,
    pub deadline_height: u64,
    pub status: BountyStatus,
    pub tags: Vec<String>,
    pub qualification: QualificationRequirement,
    pub created_at: u64,
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute a bounty ID from its creation parameters.
pub fn compute_bounty_id(
    issuer_cell: &CellId,
    title: &str,
    reward_amount: u64,
    created_at: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-bounty-id-v1");
    hasher.update(issuer_cell.as_bytes());
    hasher.update(title.as_bytes());
    hasher.update(&reward_amount.to_le_bytes());
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute a worker commitment (blinded identity).
///
/// The worker hashes their public key with randomness to produce an
/// unlinkable commitment. The same worker claiming different bounties
/// produces different commitments (different randomness each time).
pub fn compute_worker_commitment(worker_key: &[u8; 32], randomness: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-worker-commitment-v1");
    hasher.update(worker_key);
    hasher.update(randomness);
    *hasher.finalize().as_bytes()
}

/// Encode a bounty ID as hex string.
pub fn bounty_id_hex(id: &[u8; 32]) -> String {
    bytes32_to_hex(id)
}

/// Decode a hex string to a bounty ID.
pub fn bounty_id_from_hex(hex: &str) -> Option<[u8; 32]> {
    hex_to_bytes32(hex).ok()
}

/// Format a BountyStatus as a simple string label.
pub fn status_label(status: &BountyStatus) -> &'static str {
    match status {
        BountyStatus::Open => "open",
        BountyStatus::Claimed { .. } => "claimed",
        BountyStatus::Submitted { .. } => "submitted",
        BountyStatus::Approved => "approved",
        BountyStatus::Paid { .. } => "paid",
        BountyStatus::Expired => "expired",
        BountyStatus::Disputed { .. } => "disputed",
    }
}

/// Format a QualificationRequirement as a human-readable label.
pub fn qualification_label(req: &QualificationRequirement) -> String {
    match req {
        QualificationRequirement::None => "none".to_string(),
        QualificationRequirement::FederationMember => "federation_member".to_string(),
        QualificationRequirement::PredicateProof {
            attribute,
            threshold,
            ..
        } => format!("{attribute} >= {threshold}"),
        QualificationRequirement::StandingProof {
            min_completed_bounties,
        } => format!("completed >= {min_completed_bounties}"),
    }
}
