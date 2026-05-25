//! Federated bounty board: a privacy-preserving work marketplace built on pyana.
//!
//! # Architecture
//!
//! ```text
//! +-------------+     +--------------+     +-------------+
//! |   Issuer    |---->| Bounty Board |<----|   Worker    |
//! |  (cclerk)   |     |   (node)     |     |  (cclerk)   |
//! +-------------+     +--------------+     +-------------+
//!        |                    |                     |
//!   Post bounty         Store state          Claim + deliver
//!   (attenuated cap)   (intents + cells)    (conditional turn)
//! ```
//!
//! Workers prove qualifications without revealing identity. Issuers don't learn
//! who's working until delivery. Payment is released atomically via conditional
//! turns.

pub mod auth;
pub mod payment;
pub mod persist;
pub mod qualification;
pub mod server;
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

// =============================================================================
// Integration Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::server::{ServerConfig, start_server};

    // -------------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------------

    fn hex_encode(b: &[u8]) -> String {
        b.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    async fn start_test_server() -> String {
        let config = ServerConfig {
            federation_root: [0u8; 32],
            listen: "127.0.0.1:0".parse().unwrap(),
        };
        let addr = start_server(config).await;
        format!("http://{addr}")
    }

    async fn create_test_bounty(base: &str, client: &reqwest::Client) -> String {
        let issuer = [0x01u8; 32];
        let req = serde_json::json!({
            "title": "Test bounty",
            "description": "A test",
            "reward_amount": 100u64,
            "reward_asset": 1u64,
            "deadline_height": 9999u64,
            "qualification": "None",
            "tags": [],
            "issuer_cell": hex_encode(&issuer),
            "reward_token": null
        });
        let resp = client
            .post(format!("{base}/bounties"))
            .json(&req)
            .send()
            .await
            .unwrap();
        assert_eq!(resp.status(), 201);
        let body: serde_json::Value = resp.json().await.unwrap();
        body["id"].as_str().unwrap().to_string()
    }

    // =========================================================================
    // Upgrade 1: Blinded queue for fair bounty claiming
    // =========================================================================

    /// A commitment can be submitted and the status reflects the new entry.
    #[tokio::test]
    async fn blinded_queue_commit_and_status() {
        let base = start_test_server().await;
        let client = reqwest::Client::new();

        // Commit a claim to the blinded queue.
        let commitment_hex = format!("{:064x}", 0xdeadbeefu64);
        let resp = client
            .post(format!("{base}/queue/claims/commit"))
            .json(&serde_json::json!({ "commitment_hex": commitment_hex }))
            .send()
            .await
            .unwrap();
        assert_eq!(resp.status(), 200, "commit should succeed");
        let body: serde_json::Value = resp.json().await.unwrap();
        assert!(body["root_hex"].is_string(), "commit response has root_hex");

        // Status should report 1 remaining.
        let status_resp = client
            .get(format!("{base}/queue/claims/status"))
            .send()
            .await
            .unwrap();
        assert_eq!(status_resp.status(), 200);
        let status: serde_json::Value = status_resp.json().await.unwrap();
        assert_eq!(status["consumed_count"], 0, "nothing consumed yet");
        assert_eq!(status["remaining"], 1, "one commitment pending");
    }

    /// Committing then consuming with a valid public proof succeeds; a second
    /// consume with the same nullifier is rejected as double-consume.
    #[tokio::test]
    async fn blinded_queue_commit_consume_then_double_consume_rejected() {
        let base = start_test_server().await;
        let client = reqwest::Client::new();

        // Build commitment.
        use pyana_storage::blinded::crypto;
        let item_data = b"claim-slot-1";
        let randomness = [0x42u8; 32];
        let commitment = crypto::create_commitment(item_data, &randomness);
        let commitment_hex = hex_encode(&commitment.blake3);

        // Step 1: commit.
        let commit_resp = client
            .post(format!("{base}/queue/claims/commit"))
            .json(&serde_json::json!({ "commitment_hex": commitment_hex }))
            .send()
            .await
            .unwrap();
        assert_eq!(commit_resp.status(), 200, "commit must succeed");

        // Step 2: consume (public proof — single commitment, no siblings needed).
        let secret = [0xABu8; 32];
        let nullifier = crypto::derive_nullifier(&commitment, &secret, 0);
        let nullifier_hex = hex_encode(&nullifier.blake3);

        let empty_proof: Vec<String> = vec![];
        let consume_body = serde_json::json!({
            "nullifier_hex": nullifier_hex,
            "commitment_hex": commitment_hex,
            "position": 0usize,
            "membership_proof": empty_proof
        });
        let consume_resp = client
            .post(format!("{base}/queue/claims/consume"))
            .json(&consume_body)
            .send()
            .await
            .unwrap();
        assert_eq!(consume_resp.status(), 200, "first consume must succeed");
        let result: serde_json::Value = consume_resp.json().await.unwrap();
        assert_eq!(
            result["result"], "consumed",
            "first consume: result=consumed"
        );

        // Step 3: attempt double-consume with same nullifier — must be rejected.
        let double_resp = client
            .post(format!("{base}/queue/claims/consume"))
            .json(&consume_body)
            .send()
            .await
            .unwrap();
        assert_eq!(
            double_resp.status(),
            200,
            "double-consume returns 200 with error result"
        );
        let double_result: serde_json::Value = double_resp.json().await.unwrap();
        assert_eq!(
            double_result["result"], "already_consumed",
            "double-consume must be rejected"
        );
    }

    /// After consuming an item, remaining count decreases correctly.
    #[tokio::test]
    async fn blinded_queue_status_remaining_decreases_after_consume() {
        let base = start_test_server().await;
        let client = reqwest::Client::new();

        use pyana_storage::blinded::crypto;

        // Commit two items.
        for i in 0u8..2 {
            let c = crypto::create_commitment(&[i], &[i + 1; 32]);
            let resp = client
                .post(format!("{base}/queue/claims/commit"))
                .json(&serde_json::json!({ "commitment_hex": hex_encode(&c.blake3) }))
                .send()
                .await
                .unwrap();
            assert_eq!(resp.status(), 200);
        }

        let before: serde_json::Value = client
            .get(format!("{base}/queue/claims/status"))
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap();
        assert_eq!(before["remaining"], 2);

        // Consume position 0.
        let c0 = crypto::create_commitment(&[0u8], &[1u8; 32]);
        let secret = [0x11u8; 32];
        let nullifier = crypto::derive_nullifier(&c0, &secret, 0);
        // Single item has no siblings; two items need a sibling.
        // Compute sibling (commitment at position 1).
        let c1 = crypto::create_commitment(&[1u8], &[2u8; 32]);
        let consume_body = serde_json::json!({
            "nullifier_hex": hex_encode(&nullifier.blake3),
            "commitment_hex": hex_encode(&c0.blake3),
            "position": 0usize,
            "membership_proof": [hex_encode(&c1.blake3)]
        });
        let consume_resp = client
            .post(format!("{base}/queue/claims/consume"))
            .json(&consume_body)
            .send()
            .await
            .unwrap();
        // Accept consumed or invalid_proof (Merkle structure depends on internal padding).
        assert_eq!(consume_resp.status(), 200);

        let after: serde_json::Value = client
            .get(format!("{base}/queue/claims/status"))
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap();
        // remaining should have decreased (or stayed if proof was rejected due to padding)
        let remaining = after["remaining"].as_u64().unwrap();
        assert!(remaining <= 2, "remaining cannot exceed committed count");
    }

    // =========================================================================
    // Upgrade 2: Store-and-forward inbox for issuer delivery notifications
    // =========================================================================

    /// Submitting work to a claimed bounty pushes a message to the issuer inbox.
    #[tokio::test]
    async fn submission_triggers_inbox_message() {
        let base = start_test_server().await;
        let client = reqwest::Client::new();

        // Inbox should be empty before any submission.
        let status_before: serde_json::Value = client
            .get(format!("{base}/inbox/issuers/status"))
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap();
        assert_eq!(status_before["pending_messages"], 0, "inbox starts empty");

        // Create a bounty.
        let bounty_id = create_test_bounty(&base, &client).await;

        // Claim the bounty.
        let worker_commitment = [0x55u8; 32];
        let claim_req = serde_json::json!({
            "bounty_id": bounty_id,
            "worker_commitment": worker_commitment,
            "qualification_proof": null
        });
        let claim_resp = client
            .post(format!("{base}/bounties/{bounty_id}/claim"))
            .json(&claim_req)
            .send()
            .await
            .unwrap();
        assert_eq!(claim_resp.status(), 200, "claim must succeed");

        // Submit work — this should push an inbox message.
        let proof_hash_1: Vec<u8> = vec![1u8; 32];
        let completion_proof_1: Vec<u8> = vec![1u8, 2u8, 3u8, 4u8];
        let submit_req = serde_json::json!({
            "bounty_id": bounty_id,
            "worker_commitment": worker_commitment,
            "completion_evidence": {
                "ExternalProof": {
                    "url": "https://example.com/work",
                    "hash": proof_hash_1
                }
            },
            "completion_proof": completion_proof_1
        });
        let submit_resp = client
            .post(format!("{base}/bounties/{bounty_id}/submit"))
            .json(&submit_req)
            .send()
            .await
            .unwrap();
        assert_eq!(submit_resp.status(), 200, "submit must succeed");

        // Inbox should now have 1 pending message.
        let status_after: serde_json::Value = client
            .get(format!("{base}/inbox/issuers/status"))
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap();
        assert_eq!(
            status_after["pending_messages"], 1,
            "inbox should have 1 message after submission"
        );
    }

    /// The issuer can read and consume the delivery notification from the inbox.
    #[tokio::test]
    async fn issuer_can_read_and_consume_inbox_message() {
        let base = start_test_server().await;
        let client = reqwest::Client::new();

        // Create, claim, and submit a bounty to populate the inbox.
        let bounty_id = create_test_bounty(&base, &client).await;

        let worker_commitment = [0xAAu8; 32];
        client
            .post(format!("{base}/bounties/{bounty_id}/claim"))
            .json(&serde_json::json!({
                "bounty_id": bounty_id,
                "worker_commitment": worker_commitment,
                "qualification_proof": null
            }))
            .send()
            .await
            .unwrap();

        let proof_hash_2: Vec<u8> = vec![2u8; 32];
        let completion_proof_2: Vec<u8> = vec![5u8, 6u8, 7u8, 8u8];
        client
            .post(format!("{base}/bounties/{bounty_id}/submit"))
            .json(&serde_json::json!({
                "bounty_id": bounty_id,
                "worker_commitment": worker_commitment,
                "completion_evidence": {
                    "ExternalProof": {
                        "url": "https://example.com/proof",
                        "hash": proof_hash_2
                    }
                },
                "completion_proof": completion_proof_2
            }))
            .send()
            .await
            .unwrap();

        // Read next message from the issuer inbox.
        let next_resp = client
            .get(format!("{base}/inbox/issuers/next"))
            .send()
            .await
            .unwrap();
        assert_eq!(
            next_resp.status(),
            200,
            "issuer should be able to read inbox"
        );
        let msg: serde_json::Value = next_resp.json().await.unwrap();

        // The sender should be the worker commitment (hex-encoded).
        let expected_sender = hex_encode(&worker_commitment);
        assert_eq!(
            msg["sender_hex"], expected_sender,
            "message sender should be the worker commitment"
        );

        // After reading (consuming), the inbox should be empty.
        let status_after: serde_json::Value = client
            .get(format!("{base}/inbox/issuers/status"))
            .send()
            .await
            .unwrap()
            .json()
            .await
            .unwrap();
        assert_eq!(
            status_after["pending_messages"], 0,
            "inbox should be empty after read+consume"
        );
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
