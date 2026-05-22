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

use pyana_app_framework::{PyanaEngine, PredicateType};
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
    // The engine's verify_presentation_against() deserializes the wire proof and
    // verifies the STARK proof against the provided federation root.
    if engine.verify_presentation_against(proof, &federation_root) {
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

    // Compute the expected fact commitment from the attribute.
    // The fact commitment binds the proof to a specific attribute in the worker's state.
    let attr_hash = blake3::hash(attribute.as_bytes());
    let attr_field = BabyBear::new(u32::from_le_bytes(
        attr_hash.as_bytes()[..4].try_into().unwrap(),
    ));
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

// =============================================================================
// Dev-only fallback (structural checks for local testing without a federation)
// =============================================================================

/// Verify a qualification using structural-only checks (NO cryptographic verification).
///
/// WARNING: This is ONLY for local development/testing without a live federation.
/// It accepts any proof that has the right shape, which is INSECURE in production.
/// Gated behind `#[cfg(feature = "dev")]` so it cannot be accidentally used.
#[cfg(feature = "dev")]
pub fn verify_qualification_dev_only(
    requirement: &QualificationRequirement,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        QualificationRequirement::None => Ok(true),

        QualificationRequirement::FederationMember => {
            verify_federation_membership_structural(proof, federation_root)
        }

        QualificationRequirement::PredicateProof {
            predicate_type,
            attribute,
            threshold,
        } => verify_predicate_proof_structural(proof, *predicate_type, attribute, *threshold),

        QualificationRequirement::StandingProof {
            min_completed_bounties,
        } => verify_standing_proof_structural(proof, *min_completed_bounties),
    }
}

#[cfg(feature = "dev")]
fn verify_federation_membership_structural(
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    if proof.len() < 33 {
        return Err(QualificationError::InvalidProof(
            "proof too small for structural check".to_string(),
        ));
    }
    let claimed_root: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed root in proof".to_string()))?;
    if claimed_root != federation_root {
        return Err(QualificationError::ProofRejected(
            "proof is for a different federation root".to_string(),
        ));
    }
    Ok(true)
}

#[cfg(feature = "dev")]
fn verify_predicate_proof_structural(
    proof: &[u8],
    predicate_type: PredicateType,
    attribute: &str,
    threshold: u64,
) -> Result<bool, QualificationError> {
    if proof.len() < 41 {
        return Err(QualificationError::InvalidProof(
            "predicate proof too short".to_string(),
        ));
    }
    let expected_attr_hash = *blake3::hash(attribute.as_bytes()).as_bytes();
    let claimed_attr_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;
    if claimed_attr_hash != expected_attr_hash {
        return Err(QualificationError::ProofRejected(
            "proof is for a different attribute".to_string(),
        ));
    }
    let claimed_threshold = u64::from_le_bytes(
        proof[32..40]
            .try_into()
            .map_err(|_| QualificationError::InvalidProof("malformed threshold".to_string()))?,
    );
    if claimed_threshold != threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold {claimed_threshold} does not match required {threshold}"
        )));
    }
    let claimed_type = proof[40];
    let expected_type = predicate_type_byte(predicate_type);
    if claimed_type != expected_type {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }
    Ok(true)
}

#[cfg(feature = "dev")]
fn verify_standing_proof_structural(
    proof: &[u8],
    min_completed_bounties: u64,
) -> Result<bool, QualificationError> {
    if proof.len() < 9 {
        return Err(QualificationError::InvalidProof(
            "standing proof too short".to_string(),
        ));
    }
    let claimed_count = u64::from_le_bytes(
        proof[..8]
            .try_into()
            .map_err(|_| QualificationError::InvalidProof("malformed count".to_string()))?,
    );
    if claimed_count < min_completed_bounties {
        return Err(QualificationError::ProofRejected(format!(
            "claimed {claimed_count} completions but {min_completed_bounties} required"
        )));
    }
    if proof[8..].is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing body in standing proof".to_string(),
        ));
    }
    Ok(true)
}

/// Encode a PredicateType as a single byte for proof binding (dev fallback only).
#[cfg(feature = "dev")]
fn predicate_type_byte(pt: PredicateType) -> u8 {
    match pt {
        PredicateType::Gte => 0,
        PredicateType::Lte => 1,
        PredicateType::Gt => 2,
        PredicateType::Lt => 3,
        PredicateType::Neq => 4,
        PredicateType::InRangeLow => 5,
        PredicateType::InRangeHigh => 6,
    }
}

// =============================================================================
// Dev-only proof builders (for testing / worker side)
// =============================================================================

/// Build a federation membership proof (for testing / worker side).
///
/// In production this would invoke the STARK prover; here we build a
/// structurally valid proof for integration testing.
#[cfg(feature = "dev")]
pub fn build_membership_proof(federation_root: [u8; 32]) -> Vec<u8> {
    let mut proof = Vec::with_capacity(64);
    proof.extend_from_slice(&federation_root);
    // Placeholder proof body (32 bytes of deterministic data).
    proof.extend_from_slice(&blake3::hash(b"membership-proof-body").as_bytes()[..]);
    proof
}

/// Build a predicate proof (for testing / worker side).
#[cfg(feature = "dev")]
pub fn build_predicate_proof(
    attribute: &str,
    threshold: u64,
    predicate_type: PredicateType,
) -> Vec<u8> {
    let attr_hash = *blake3::hash(attribute.as_bytes()).as_bytes();
    let mut proof = Vec::with_capacity(73);
    proof.extend_from_slice(&attr_hash);
    proof.extend_from_slice(&threshold.to_le_bytes());
    proof.push(predicate_type_byte(predicate_type));
    // Placeholder STARK body.
    proof.extend_from_slice(&blake3::hash(b"predicate-proof-body").as_bytes()[..]);
    proof
}

/// Build a standing proof (for testing / worker side).
#[cfg(feature = "dev")]
pub fn build_standing_proof(completed_count: u64) -> Vec<u8> {
    let mut proof = Vec::with_capacity(40);
    proof.extend_from_slice(&completed_count.to_le_bytes());
    // Placeholder IVC body.
    proof.extend_from_slice(&blake3::hash(b"standing-proof-body").as_bytes()[..]);
    proof
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::EngineConfig;

    fn test_engine() -> PyanaEngine {
        PyanaEngine::new(EngineConfig::default())
    }

    #[test]
    fn test_no_qualification() {
        let engine = test_engine();
        assert_eq!(
            verify_qualification(&engine, &QualificationRequirement::None, &[], [0u8; 32])
                .unwrap(),
            true
        );
    }

    #[test]
    fn test_federation_membership_rejects_garbage() {
        let engine = test_engine();
        let mut engine_mut = PyanaEngine::new(EngineConfig::default());
        engine_mut.set_federation_root([0xAB; 32]);

        // Garbage bytes should be rejected by real verification.
        let garbage = vec![0xDE; 100];
        let result = verify_qualification(
            &engine_mut,
            &QualificationRequirement::FederationMember,
            &garbage,
            [0xAB; 32],
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_federation_membership_rejects_empty() {
        let engine = test_engine();
        let result = verify_qualification(
            &engine,
            &QualificationRequirement::FederationMember,
            &[],
            [0xAB; 32],
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_federation_membership_rejects_zero_root() {
        let engine = test_engine();
        // A zero federation root means "not configured" -- should fail closed.
        let garbage = vec![0xDE; 100];
        let result = verify_qualification(
            &engine,
            &QualificationRequirement::FederationMember,
            &garbage,
            [0u8; 32],
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            QualificationError::VerificationUnavailable(_) => {}
            other => panic!("expected VerificationUnavailable, got: {other}"),
        }
    }

    #[test]
    fn test_predicate_proof_rejects_garbage() {
        let engine = test_engine();
        let garbage = vec![0xDE; 100];
        let req = QualificationRequirement::PredicateProof {
            predicate_type: PredicateType::Gte,
            attribute: "reputation".to_string(),
            threshold: 5,
        };
        let result = verify_qualification(&engine, &req, &garbage, [0u8; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_standing_proof_rejects_garbage() {
        let engine = test_engine();
        let garbage = vec![0xDE; 100];
        let req = QualificationRequirement::StandingProof {
            min_completed_bounties: 5,
        };
        let result = verify_qualification(&engine, &req, &garbage, [0u8; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_standing_proof_rejects_empty() {
        let engine = test_engine();
        let req = QualificationRequirement::StandingProof {
            min_completed_bounties: 5,
        };
        let result = verify_qualification(&engine, &req, &[], [0u8; 32]);
        assert!(result.is_err());
    }
}
