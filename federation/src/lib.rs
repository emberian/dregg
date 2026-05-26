//! `dregg-federation`: Multi-node federated revocation attestation.
//!
//! Historically this crate hosted a Morpheus-shaped BFT consensus simulation;
//! the live consensus engine is now `dregg-blocklace` (Cordial Miners DAG +
//! tau ordering). What remains here are the federated revocation primitives
//! (Merkle accumulator, attested roots, quorum signatures) plus the solo /
//! threshold / checkpoint utilities the live node consumes.
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
//! │              BFT Consensus (blocklace, see dregg-blocklace)      │
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
//! 2. **Consensus**: The BFT protocol (propose/vote/finalize, as implemented
//!    by `dregg-blocklace`) agrees on a block of revocations. A quorum (n - f)
//!    of nodes must vote for the block to be finalized.
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
//! - [`node`]: Federation node implementation (includes BFT consensus simulation)

pub mod checkpoint;
pub mod cross_fed_bundle;
pub mod epoch;
pub mod federation;
pub mod identity;
pub mod node;
pub mod receipt;
pub mod revocation;
pub mod solo;
pub mod threshold;
pub mod threshold_decrypt;
#[cfg(feature = "runtime")]
pub mod transport;
pub mod types;

// Re-export primary types.
pub use checkpoint::{
    Checkpoint, CheckpointError, DEFAULT_CHECKPOINT_INTERVAL, create_checkpoint,
    finalize_checkpoint, is_checkpoint_height, verify_checkpoint,
};
// The unified `Federation` type (FEDERATION-UNIFICATION-DESIGN.md §2).
// Frees the bare name `Federation` for the canonical attestation context;
// the Morpheus-era simulator type that previously held this name is now
// re-exported as `MorpheusFederation` pending its deletion (design §6 step 7).
pub use cross_fed_bundle::CrossFedReceiptBundle;
pub use federation::{Federation, KnownFederations, LocalSeat};
pub use identity::{derive_federation_id, derive_federation_id_with_epoch};
// NOTE (FEDERATION-UNIFICATION-DESIGN.md §6 step 6): the Morpheus BFT
// simulator (`node.rs` + `transport.rs`) is legally dead — `dregg-blocklace`
// is the live consensus path. The simulator survives as in-crate code only
// because `teasting`, `wasm`, and `demo/sdk-consensus` still import it. As
// each of those consumers migrates to drive a real blocklace, the relevant
// `node.rs` symbols can be deleted; the unified `Federation` type
// (`federation::Federation`) is the canonical replacement at the type-system
// layer. The re-exports below are kept only so the existing simulator
// consumers compile.
pub use dregg_types::FederationId;
pub use node::{
    ConsensusConfig, ConsensusError, ConsensusOrchestrator, ConsensusState,
    Federation as MorpheusFederation, FederationNode, PendingStateRoots, ReconfigurationProposal,
    ReconfigurationVotes,
};
pub use receipt::{FederationReceipt, FederationReceiptBody, ReceiptQc};
pub use revocation::{RevocationTree, RevocationVerification, RevocationVerifier};
pub use solo::{
    NullifierConflict, NullifierLog, NullifierLogEntry, SoloConsensusState, is_solo_committee,
};
pub use threshold::{
    FederationCommittee, MemberSecret, ThresholdError, ThresholdQC, generate_test_committee,
    generate_test_committee_with_seed,
};
pub use threshold_decrypt::{
    DecryptionShare, KeyShare, ThresholdCiphertext, ThresholdDecryptError, ThresholdEncryptionKey,
    combine_shares, generate_epoch_key, produce_decryption_share, threshold_encrypt,
};
#[cfg(feature = "runtime")]
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
/// For n validators tolerating f = floor(n/3) Byzantine faults,
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
/// f = floor(n/3)
///
/// Standard BFT: a system of n nodes can tolerate at most floor(n/3) faulty nodes
/// while maintaining safety (no conflicting commits) and liveness (progress continues).
pub fn fault_tolerance(n: usize) -> usize {
    n / 3
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
        assert_eq!(fault_tolerance(0), 0);
        assert_eq!(fault_tolerance(1), 0);
        assert_eq!(fault_tolerance(2), 0);
        assert_eq!(fault_tolerance(3), 1);
        assert_eq!(fault_tolerance(4), 1);
        assert_eq!(fault_tolerance(7), 2);
        assert_eq!(fault_tolerance(10), 3);
    }
}
