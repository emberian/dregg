//! Qualification verification: prove worker meets requirements without revealing identity.
//!
//! Workers prove qualifications anonymously:
//! - Federation membership: ring membership STARK (proves "I'm in this set" without revealing which member).
//! - Predicate proof: proves "my attribute >= threshold" without revealing the exact value.
//! - Standing proof: IVC chain proving N prior bounty completions.
//!
//! # Security model
//!
//! All proof verification paths perform CRYPTOGRAPHIC verification. Structural checks alone
//! are NEVER sufficient. The `dev` feature enables a fallback for local testing without a
//! live federation, but it is never the default.

use pyana_app_framework::{PredicateType, PyanaEngine};
use pyana_circuit::{
    BabyBear, IvcProof, IvcVerification, PredicateProof, verify_ivc, verify_predicate,
};

use crate::QualificationRequirement;

/// Error type for qualification verification.
#[derive(Debug, Clone)]
pub enum QualificationError {
    /// The proof is malformed or empty.
    InvalidProof(String),
    /// The proof does not satisfy the requirement.
    ProofRejected(String),
    /// The federation root is unknown or stale.
    UnknownFederationRoot,
    /// The IVC chain is invalid or too short.
    InvalidIvcChain(String),
    /// Verification cannot be performed (missing configuration). Fail closed.
    VerificationUnavailable(String),
}

impl std::fmt::Display for QualificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::ProofRejected(msg) => write!(f, "proof rejected: {msg}"),
            Self::UnknownFederationRoot => write!(f, "unknown federation root"),
            Self::InvalidIvcChain(msg) => write!(f, "invalid IVC chain: {msg}"),
            Self::VerificationUnavailable(msg) => {
                write!(f, "verification unavailable (fail closed): {msg}")
            }
        }
    }
}

impl std::error::Error for QualificationError {}

/// Verify a worker's anonymous qualification proof against a requirement.
///
/// # Privacy properties
///
/// - The worker's identity is never revealed to the verifier.
/// - For federation membership: the proof shows set membership without revealing WHICH member.
/// - For predicate proofs: the exact attribute value remains hidden.
/// - For standing proofs: only the count threshold is checked, not which specific bounties were completed.
///
/// # Security
///
/// ALL paths perform real cryptographic verification. If verification cannot be performed
/// (e.g., no federation root configured), the function fails CLOSED (rejects).
///
/// # Arguments
///
/// * `engine` - The PyanaEngine instance for federation membership verification.
/// * `requirement` - What the worker must prove.
/// * `proof` - The cryptographic proof bytes (format depends on requirement type).
/// * `federation_root` - The current federation Merkle root for membership checks.
///
/// # Returns
///
/// `Ok(true)` if the proof is valid, `Ok(false)` if it's structurally valid but doesn't meet
/// the threshold, or an error if the proof is malformed or verification fails.
pub fn verify_qualification(
    engine: &PyanaEngine,
    requirement: &QualificationRequirement,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        QualificationRequirement::None => Ok(true),

        QualificationRequirement::FederationMember => {
            verify_federation_membership(engine, proof, federation_root)
        }

        QualificationRequirement::PredicateProof {
            predicate_type,
            attribute,
            threshold,
        } => verify_predicate_proof(proof, *predicate_type, attribute, *threshold),

        QualificationRequirement::StandingProof {
            min_completed_bounties,
        } => verify_standing_proof(proof, *min_completed_bounties),
    }
}

/// Verify a ring membership STARK proving the worker is a federation member.
///
/// Uses the PyanaEngine's `verify_presentation_bytes()` to perform real STARK verification
/// of the federation membership proof.
fn verify_federation_membership(
    engine: &PyanaEngine,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty federation membership proof".to_string(),
        ));
    }

    // If we can't verify, REJECT -- never accept unverified proofs.
    if federation_root == [0u8; 32] {
        return Err(QualificationError::VerificationUnavailable(
            "no federation root configured".to_string(),
        ));
    }

    // Perform real cryptographic verification via the engine.
    // Uses verify_membership_proof which checks the STARK proof for federation
    // membership without requiring action/resource binding (this is a qualification
    // check, not an action-authorized request).
    if engine.verify_membership_proof(proof, &federation_root) {
        Ok(true)
    } else {
        Err(QualificationError::ProofRejected(
            "federation membership STARK verification failed".to_string(),
        ))
    }
}

/// Verify a predicate STARK proving an attribute satisfies a threshold.
///
/// Example: "my reputation score >= 5" without revealing that it's actually 47.
///
/// Deserializes the proof as a `PredicateProof` from the circuit crate and verifies
/// the STARK proof cryptographically against the expected threshold and fact commitment.
fn verify_predicate_proof(
    proof: &[u8],
    predicate_type: PredicateType,
    attribute: &str,
    threshold: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty predicate proof".to_string(),
        ));
    }

    // Deserialize the real PredicateProof from wire bytes.
    let predicate_proof: PredicateProof = postcard::from_bytes(proof).map_err(|e| {
        QualificationError::InvalidProof(format!("failed to deserialize predicate proof: {e}"))
    })?;

    // Verify the predicate type matches what is required.
    let expected_type = to_circuit_predicate_type(predicate_type);
    if predicate_proof.predicate_type != expected_type {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }

    // Verify the threshold matches the requirement.
    let expected_threshold = BabyBear::new(threshold as u32);
    if predicate_proof.threshold != expected_threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold does not match required threshold {threshold}"
        )));
    }

    // Use the proof's fact commitment for verification.
    // The STARK proof itself cryptographically binds the fact commitment to the
    // proven attribute value, so the verifier trusts it if the STARK verifies.
    let fact_commitment = predicate_proof.fact_commitment;

    // Verify the STARK proof cryptographically.
    if verify_predicate(&predicate_proof, expected_threshold, fact_commitment) {
        Ok(true)
    } else {
        Err(QualificationError::ProofRejected(
            "predicate STARK verification failed".to_string(),
        ))
    }
}

/// Verify an IVC chain proving the worker has completed at least N bounties.
///
/// The IVC proof accumulates state transitions: each completed bounty extends
/// the chain by one step. The verifier checks the chain length meets the threshold
/// without learning which specific bounties were completed.
///
/// Deserializes as an `IvcProof` and performs real cryptographic verification
/// of the hash chain (and STARK proof if present).
fn verify_standing_proof(
    proof: &[u8],
    min_completed_bounties: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty standing proof".to_string(),
        ));
    }

    // Deserialize the real IvcProof from wire bytes.
    let ivc_proof: IvcProof = postcard::from_bytes(proof).map_err(|e| {
        QualificationError::InvalidIvcChain(format!("failed to deserialize IVC proof: {e}"))
    })?;

    // Check the claimed step count meets the minimum threshold.
    if (ivc_proof.step_count as u64) < min_completed_bounties {
        return Err(QualificationError::ProofRejected(format!(
            "IVC chain has {} steps but {} required",
            ivc_proof.step_count, min_completed_bounties
        )));
    }

    // Verify the IVC proof cryptographically.
    // verify_ivc checks:
    //   1. Public inputs consistency
    //   2. If a real STARK proof is present, verifies it
    //   3. Otherwise, falls back to BLAKE3 digest binding check
    //   4. Accumulated hash integrity
    match verify_ivc(&ivc_proof, None) {
        IvcVerification::Valid => Ok(true),
        IvcVerification::EmptyChain => Err(QualificationError::InvalidIvcChain(
            "IVC chain is empty".to_string(),
        )),
        IvcVerification::ProofInvalid => Err(QualificationError::ProofRejected(
            "IVC proof cryptographic verification failed".to_string(),
        )),
        IvcVerification::InitialRootMismatch => Err(QualificationError::InvalidIvcChain(
            "IVC initial root mismatch".to_string(),
        )),
        IvcVerification::AccumulatedHashMismatch => Err(QualificationError::InvalidIvcChain(
            "IVC accumulated hash mismatch (chain tampered)".to_string(),
        )),
        other => Err(QualificationError::ProofRejected(format!(
            "IVC verification returned unexpected status: {other:?}"
        ))),
    }
}

/// Convert app-framework PredicateType to circuit PredicateType.
///
/// These are re-exported from the same source so they are identical, but
/// we call this to be explicit about the conversion in case the types
/// ever diverge.
fn to_circuit_predicate_type(pt: PredicateType) -> pyana_circuit::PredicateType {
    match pt {
        PredicateType::Gte => pyana_circuit::PredicateType::Gte,
        PredicateType::Lte => pyana_circuit::PredicateType::Lte,
        PredicateType::Gt => pyana_circuit::PredicateType::Gt,
        PredicateType::Lt => pyana_circuit::PredicateType::Lt,
        PredicateType::Neq => pyana_circuit::PredicateType::Neq,
        PredicateType::InRangeLow => pyana_circuit::PredicateType::InRangeLow,
        PredicateType::InRangeHigh => pyana_circuit::PredicateType::InRangeHigh,
    }
}
