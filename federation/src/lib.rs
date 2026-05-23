//! `pyana-federation`: Multi-node federated revocation attestation.
//!
//! This crate integrates the Morpheus consensus protocol with the pyana token
//! system to provide real multi-node federated revocation attestation.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Federation (N nodes)                          │
//! │                                                                  │
//! │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐      │
//! │  │  Node 0  │  │  Node 1  │  │  Node 2  │  │  Node 3  │      │
//! │  │          │  │          │  │          │  │          │      │
//! │  │ Merkle   │  │ Merkle   │  │ Merkle   │  │ Merkle   │      │
//! │  │ Tree     │  │ Tree     │  │ Tree     │  │ Tree     │      │
//! │  │          │  │          │  │          │  │          │      │
//! │  │ Consensus│  │ Consensus│  │ Consensus│  │ Consensus│      │
//! │  │ State    │  │ State    │  │ State    │  │ State    │      │
//! │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘      │
//! │       │              │              │              │            │
//! │       └──────────────┴──────────────┴──────────────┘            │
//! │                         │                                        │
//! │              Morpheus Consensus Protocol                         │
//! │              (Propose -> Vote -> Finalize)                       │
//! │                         │                                        │
//! │                    Attested Root                                  │
//! │              (merkle_root, height, quorum_sigs)                   │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # How it works
//!
//! 1. **Revocation submission**: An authority node creates a signed revocation
//!    event for a token ID.
//!
//! 2. **Consensus**: The Morpheus-shaped protocol (propose/vote/finalize)
//!    agrees on a block of revocations. A quorum (n - f) of nodes must vote
//!    for the block to be finalized.
//!
//! 3. **State update**: After finalization, all nodes apply the revocations
//!    to their local Merkle trees. Since the tree is deterministic and
//!    insertion-order-independent, all nodes converge on the same root.
//!
//! 4. **Attested root**: The resulting `(merkle_root, block_height, timestamp,
//!    quorum_signatures)` tuple is the attested root. Verifiers trust it
//!    because it has signatures from >= threshold federation members.
//!
//! 5. **Non-membership proofs**: A verifier checks that a token is NOT in
//!    the revocation tree by obtaining a non-membership proof against the
//!    attested root.
//!
//! # Modules
//!
//! - [`types`]: Core data types (AttestedRoot, RevocationProof, messages, crypto)
//! - [`revocation`]: Revocation Merkle tree + non-membership proofs
//! - [`network`]: Channel-based networking between nodes
//! - [`node`]: Federation node implementation (includes BFT consensus simulation)

pub mod checkpoint;
pub mod epoch;
#[cfg(feature = "morpheus")]
pub mod morpheus_adapter;
pub mod network;
pub mod node;
pub mod revocation;
pub mod threshold;
pub mod threshold_decrypt;
pub mod transport;
pub mod types;

// Re-export primary types.
pub use checkpoint::{
    Checkpoint, CheckpointError, DEFAULT_CHECKPOINT_INTERVAL, create_checkpoint,
    finalize_checkpoint, is_checkpoint_height, verify_checkpoint,
};
pub use node::{
    ConsensusConfig, ConsensusError, ConsensusOrchestrator, ConsensusState, Federation,
    FederationNode, PendingStateRoots, ReconfigurationProposal, ReconfigurationVotes,
};
pub use revocation::{RevocationTree, RevocationVerification, RevocationVerifier};
pub use threshold::{
    FederationCommittee, MemberSecret, ThresholdError, ThresholdQC, generate_test_committee,
};
pub use threshold_decrypt::{
    DecryptionShare, KeyShare, ThresholdCiphertext, ThresholdDecryptError, ThresholdEncryptionKey,
    combine_shares, generate_epoch_key, produce_decryption_share, threshold_encrypt,
};
pub use transport::{
    FederationEnvelope, FederationTransport, LocalTransport, NetworkConsensusNode,
    TcpFederationTransport, TransportError,
};
pub use types::{
    AttestedRoot, ConsensusMessage, LightClientProof, NodeIdentity, PublicKey, QuorumCertificate,
    RevocationBlock, RevocationEvent, RevocationProof, Signature, SigningKey, Token,
    ViewChangeMessage, Vote, generate_keypair, sign, verify, verify_attested_root_with_committee,
    verify_via_receipt_chain,
};

// =============================================================================
// Canonical BFT Threshold Functions
// =============================================================================

/// Canonical BFT quorum threshold: minimum votes needed for safety.
///
/// For n validators tolerating f = floor((n-1)/3) Byzantine faults,
/// quorum = n - f.
///
/// This is the ONE correct formula used throughout the system.
/// - n=1 -> 1, n=2 -> 2, n=3 -> 2, n=4 -> 3, n=7 -> 5, n=10 -> 7
pub fn quorum_threshold(n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    let f = fault_tolerance(n);
    n - f
}

/// Maximum Byzantine faults tolerable for n validators.
///
/// f = floor((n-1)/3)
pub fn fault_tolerance(n: usize) -> usize {
    n.saturating_sub(1) / 3
}

#[cfg(test)]
mod threshold_tests {
    use super::*;

    #[test]
    fn test_quorum_threshold() {
        assert_eq!(quorum_threshold(1), 1);
        assert_eq!(quorum_threshold(2), 2);
        assert_eq!(quorum_threshold(3), 2);
        assert_eq!(quorum_threshold(4), 3);
        assert_eq!(quorum_threshold(7), 5);
        assert_eq!(quorum_threshold(10), 7);
    }

    #[test]
    fn test_fault_tolerance() {
        assert_eq!(fault_tolerance(1), 0);
        assert_eq!(fault_tolerance(2), 0);
        assert_eq!(fault_tolerance(3), 0);
        assert_eq!(fault_tolerance(4), 1);
        assert_eq!(fault_tolerance(7), 2);
        assert_eq!(fault_tolerance(10), 3);
    }
}
