//! Production `ThresholdVerifier` backed by `pyana-federation`'s
//! `FederationCommittee` + `ThresholdQC` BLS aggregate verifier.
//!
//! This module is feature-gated behind `federation-verifier` so that
//! lightweight consumers (apps that don't need governance-bound DFA swaps,
//! or that vend their own verifier impl) don't pull in the federation KZG/BLS
//! stack as a transitive dependency.
//!
//! # Usage
//!
//! ```ignore
//! use std::sync::Arc;
//! use pyana_dfa::{GovernedRouter, RouteTableBuilder, RouteTarget};
//! use pyana_dfa::federation_verifier::FederationQcVerifier;
//! use pyana_federation::threshold::FederationCommittee;
//!
//! let committee: FederationCommittee = /* loaded from federation state */;
//! let verifier = Arc::new(FederationQcVerifier::new(committee));
//! let table = RouteTableBuilder::new()
//!     .route("/x/*", RouteTarget::handler("xh"))
//!     .compile();
//! let router = GovernedRouter::with_verifier(table, verifier);
//! ```
//!
//! # Wire-format
//!
//! `GovernanceProof::proof_data` is a postcard-encoded
//! `pyana_federation::threshold::ThresholdQC`. The verifier reconstructs the
//! QC, builds the canonical signing message `old_commitment ‖ new_commitment`,
//! and delegates to `FederationCommittee::verify(&qc, &message)`.

use std::fmt;

use pyana_federation::threshold::{FederationCommittee, ThresholdQC};

use crate::router::ThresholdVerifier;

/// A `ThresholdVerifier` that delegates to `FederationCommittee::verify`.
///
/// `proof_data` is interpreted as a postcard-encoded [`ThresholdQC`]; the
/// signed message is the concatenation `old_commitment || new_commitment`.
pub struct FederationQcVerifier {
    committee: FederationCommittee,
}

impl FederationQcVerifier {
    pub fn new(committee: FederationCommittee) -> Self {
        Self { committee }
    }

    pub fn committee(&self) -> &FederationCommittee {
        &self.committee
    }

    /// The canonical signing message: `old || new`.
    pub fn signing_message(old_commitment: &[u8; 32], new_commitment: &[u8; 32]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(old_commitment);
        buf[32..].copy_from_slice(new_commitment);
        buf
    }
}

impl fmt::Debug for FederationQcVerifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FederationQcVerifier").finish_non_exhaustive()
    }
}

impl ThresholdVerifier for FederationQcVerifier {
    fn verify(
        &self,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        proof_data: &[u8],
    ) -> Result<(), String> {
        let qc: ThresholdQC = postcard::from_bytes(proof_data)
            .map_err(|e| format!("ThresholdQC decode failed: {e}"))?;
        let message = Self::signing_message(old_commitment, new_commitment);
        self.committee
            .verify(&qc, &message)
            .map_err(|e| format!("ThresholdQC verification failed: {e}"))
    }
}
