//! Core types for the pyana federation consensus system.
//!
//! Cryptographic primitives (`PublicKey`, `Signature`, `SigningKey`) and helpers
//! (`generate_keypair`, `sign`, `verify`, `hex_encode`) are re-exported from the
//! canonical `pyana-types` crate. Federation-specific consensus types (blocks,
//! votes, QCs, attested roots, messages) are defined here.

use serde::{Deserialize, Serialize};
use std::fmt;

// Re-export canonical cryptographic primitives and AttestedRoot from pyana-types.
pub use pyana_types::{
    AttestedRoot, PublicKey, Signature, SigningKey, generate_keypair, hex_encode, sign, verify,
};

// =============================================================================
// Node Identity
// =============================================================================

/// Identity of a federation node.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeIdentity {
    /// Human-readable name (e.g., "alpha.org").
    pub name: String,
    /// Numeric index in the federation.
    pub id: usize,
    /// The node's public key.
    pub public_key: PublicKey,
}

impl fmt::Display for NodeIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

// =============================================================================
// Revocation Events
// =============================================================================

/// A revocation event submitted to consensus.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RevocationEvent {
    /// The token ID being revoked.
    pub token_id: String,
    /// The authority that issued the revocation.
    pub authority_id: usize,
    /// Signature over the token_id by the revoking authority.
    pub signature: Signature,
}

// =============================================================================
// Consensus Types
// =============================================================================

/// A block of revocations that has been proposed for consensus.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevocationBlock {
    /// The block height (monotonically increasing).
    pub height: u64,
    /// The view number in which this block was proposed.
    pub view: u64,
    /// The proposer's node ID.
    pub proposer: usize,
    /// The revocation events in this block.
    pub events: Vec<RevocationEvent>,
    /// Hash of the previous block (chain integrity).
    pub prev_hash: [u8; 32],
    /// Hash of this block's content.
    pub block_hash: [u8; 32],
    /// Signature over `block_hash` by the proposer (proves identity).
    /// If `None`, the block is unsigned (legacy/test mode).
    #[serde(default)]
    pub proposer_signature: Option<Signature>,
}

impl RevocationBlock {
    /// Compute the block hash from its contents.
    pub fn compute_hash(
        height: u64,
        view: u64,
        proposer: usize,
        events: &[RevocationEvent],
        prev_hash: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-federation block v1");
        hasher.update(&height.to_le_bytes());
        hasher.update(&view.to_le_bytes());
        hasher.update(&(proposer as u64).to_le_bytes());
        hasher.update(prev_hash);
        for event in events {
            hasher.update(event.token_id.as_bytes());
            hasher.update(&(event.authority_id as u64).to_le_bytes());
            hasher.update(&event.signature.0);
        }
        *hasher.finalize().as_bytes()
    }
}

/// A vote from a node for a specific block.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Vote {
    /// The block being voted on.
    pub block_hash: [u8; 32],
    /// The block height being voted on.
    pub height: u64,
    /// The view in which this vote was cast.
    pub view: u64,
    /// The voter's node ID.
    pub voter: usize,
    /// Signature over the vote message.
    pub signature: Signature,
}

/// A quorum certificate: proof that threshold nodes voted for a block.
///
/// Supports two modes:
/// - **Threshold QC** (preferred): A single constant-size BLS aggregate signature.
/// - **Individual votes** (legacy): N individual Ed25519 (voter_id, signature) pairs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuorumCertificate {
    /// The block hash that was certified.
    pub block_hash: [u8; 32],
    /// The block height.
    pub height: u64,
    /// The view number.
    pub view: u64,
    /// The threshold aggregate QC (constant-size, preferred).
    pub aggregate_qc: Option<crate::threshold::ThresholdQC>,
    /// The collected votes (voter_id, signature) pairs (legacy).
    pub votes: Vec<(usize, Signature)>,
    /// The threshold required.
    pub threshold: usize,
}

impl QuorumCertificate {
    /// Whether this QC has enough votes and all signatures are valid.
    ///
    /// If a threshold aggregate QC is present, it must be verified via
    /// `verify_with_committee()` — this method falls through to vote-based
    /// verification. An aggregate QC does NOT short-circuit this check.
    pub fn is_valid_with_keys(&self, nodes: &[NodeIdentity]) -> bool {
        // If an aggregate QC is present, require committee-based verification
        // (via verify_with_committee). Do NOT short-circuit here.
        if self.aggregate_qc.is_some() {
            // Fall through to vote-based verification as a sanity check.
            // Callers with a committee should use verify_with_committee() instead.
        }
        if self.votes.len() < self.threshold {
            return false;
        }
        // Build the vote message that was signed.
        let vote_message = Self::vote_message(&self.block_hash, self.height, self.view);
        for (voter_id, sig) in &self.votes {
            match nodes.get(*voter_id) {
                Some(node) => {
                    if !node.public_key.verify(&vote_message, sig) {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    /// Verify this QC using the threshold committee.
    ///
    /// This is the preferred verification path: checks the constant-size
    /// aggregate BLS signature against the committee's verifier key.
    pub fn verify_with_committee(&self, committee: &crate::threshold::FederationCommittee) -> bool {
        match &self.aggregate_qc {
            Some(qc) => {
                let message = Self::vote_message(&self.block_hash, self.height, self.view);
                committee.verify(qc, &message).is_ok()
            }
            None => false,
        }
    }

    /// Whether this QC has enough votes (count-only check, for backwards compat).
    ///
    /// If an aggregate QC is present, requires proper BLS verification via
    /// `verify_with_committee()`. This method only validates vote counts.
    pub fn is_valid(&self) -> bool {
        if self.aggregate_qc.is_some() {
            // An aggregate QC requires proper BLS verification.
            // Do NOT short-circuit — fall through to vote count check.
        }
        self.votes.len() >= self.threshold
    }

    /// Build the canonical vote message for signature verification.
    pub fn vote_message(block_hash: &[u8; 32], height: u64, view: u64) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-federation-vote-v1");
        msg.extend_from_slice(block_hash);
        msg.extend_from_slice(&height.to_le_bytes());
        msg.extend_from_slice(&view.to_le_bytes());
        msg
    }

    /// Extract (PublicKey, Signature) pairs given a node identity table.
    pub fn quorum_signatures(&self, nodes: &[NodeIdentity]) -> Vec<(PublicKey, Signature)> {
        self.votes
            .iter()
            .filter_map(|(voter_id, sig)| {
                nodes
                    .get(*voter_id)
                    .map(|node| (node.public_key.clone(), sig.clone()))
            })
            .collect()
    }
}

// =============================================================================
// Attested Root (re-exported from pyana-types, with federation-specific helpers)
// =============================================================================

/// Verify an attested root using the threshold committee.
///
/// This is the preferred verification path: checks the constant-size
/// aggregate BLS signature against the committee's verifier key.
///
/// Deserializes the opaque `ThresholdQC` bytes stored in the `AttestedRoot`
/// into the federation's rich `ThresholdQC` type for BLS verification.
pub fn verify_attested_root_with_committee(
    root: &AttestedRoot,
    committee: &crate::threshold::FederationCommittee,
) -> bool {
    match &root.threshold_qc {
        Some(opaque_qc) => {
            // Deserialize the opaque bytes into the federation ThresholdQC.
            match crate::threshold::ThresholdQC::from_bytes(&opaque_qc.0) {
                Some(qc) => {
                    let message = root.signing_message();
                    committee.verify(&qc, &message).is_ok()
                }
                None => false,
            }
        }
        None => false,
    }
}

/// Verify an agent's state using a receipt chain as an alternative to
/// Merkle membership proof.
///
/// This is the "federation exit" path: an agent with a valid receipt chain
/// can prove their state without the federation vouching for it. The chain
/// proves that the state was produced by a sequence of valid, executor-checked
/// turns from genesis.
///
/// # Arguments
///
/// * `receipts` - The agent's full receipt chain from genesis.
/// * `expected_post_state` - The state commitment the chain should prove.
///
/// # Returns
///
/// `Ok(())` if the receipt chain is valid and its head matches the expected
/// state commitment. This is equivalent to a Merkle membership proof for the
/// purposes of state verification.
pub fn verify_via_receipt_chain(
    receipts: &[pyana_turn::TurnReceipt],
    expected_post_state: Option<[u8; 32]>,
) -> Result<(), pyana_turn::VerifyError> {
    let head_state = pyana_turn::verify_receipt_chain_head(receipts)?;
    if let Some(expected) = expected_post_state {
        if head_state != expected {
            return Err(pyana_turn::VerifyError::StateChainBreak {
                index: receipts.len() - 1,
                expected_pre_state: expected,
                actual_pre_state: head_state,
            });
        }
    }
    Ok(())
}

// =============================================================================
// Revocation Proof (for verifiers)
// =============================================================================

/// A proof that a token is NOT revoked, anchored to an attested root.
///
/// A verifier checks:
/// 1. The attested root has sufficient quorum signatures from trusted authorities.
/// 2. The non-membership proof is valid against the attested Merkle root.
/// 3. The attested root's timestamp is recent enough.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevocationProof {
    /// The token ID being proved non-revoked.
    pub token_id: String,
    /// The attested root this proof is relative to.
    pub attested_root: AttestedRoot,
    /// The non-membership proof from the Merkle tree.
    pub non_membership: pyana_commit::NonMembershipProof,
}

// =============================================================================
// Network Messages
// =============================================================================

/// A signed view-change message indicating a node wants to advance the view.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ViewChangeMessage {
    /// The new view being requested.
    pub new_view: u64,
    /// The current block height.
    pub height: u64,
    /// The voter's node ID.
    pub voter: usize,
    /// Signature over the view-change content by the voter.
    pub signature: Signature,
}

impl ViewChangeMessage {
    /// Compute the canonical message that is signed for a view-change.
    pub fn signing_message(new_view: u64, height: u64) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-view-change-v1");
        msg.extend_from_slice(&new_view.to_le_bytes());
        msg.extend_from_slice(&height.to_le_bytes());
        msg
    }
}

/// Messages exchanged between federation nodes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConsensusMessage {
    /// A proposal for a new block of revocations.
    Propose(RevocationBlock),
    /// A vote for a proposed block.
    VoteMsg(Vote),
    /// A finalized quorum certificate.
    Finalize(QuorumCertificate, RevocationBlock),
    /// A revocation request from a client.
    RevokeRequest(RevocationEvent),
    /// Request for the current attested root.
    GetAttestedRoot,
    /// Response with the current attested root.
    AttestedRootResponse(AttestedRoot),
    /// A view-change request (leader timeout).
    ViewChange(ViewChangeMessage),
}

/// An addressed message (source, destination, payload).
#[derive(Clone, Debug)]
pub struct AddressedMessage {
    /// Source node ID.
    pub from: usize,
    /// Destination node ID (or usize::MAX for broadcast).
    pub to: usize,
    /// The consensus message.
    pub message: ConsensusMessage,
}

impl AddressedMessage {
    /// Create a broadcast message (to all nodes).
    pub fn broadcast(from: usize, message: ConsensusMessage) -> Self {
        Self {
            from,
            to: usize::MAX,
            message,
        }
    }

    /// Create a directed message to a specific node.
    pub fn directed(from: usize, to: usize, message: ConsensusMessage) -> Self {
        Self { from, to, message }
    }

    /// Whether this is a broadcast message.
    pub fn is_broadcast(&self) -> bool {
        self.to == usize::MAX
    }
}

// =============================================================================
// Token (simplified for the federation demo)
// =============================================================================

/// A simplified token representation for the federation demo.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Token {
    /// Unique token identifier.
    pub id: String,
    /// Human-readable description of the token holder.
    pub holder: String,
    /// The issuing authority's node ID.
    pub issuer_id: usize,
    /// Issuing authority's public key.
    pub issuer_key: PublicKey,
    /// Signature over the token ID by the issuer.
    pub signature: Signature,
}

// =============================================================================
// Helpers
// =============================================================================

/// Get current timestamp in seconds (simplified, uses a counter for determinism in demo).
pub fn current_timestamp() -> i64 {
    // In production, this would be real wall-clock time.
    // For the demo, we use an incrementing value based on block height.
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(1700000000)
}
