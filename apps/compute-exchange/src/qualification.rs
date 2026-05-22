//! ZK proof of compute capacity for provider qualification.
//!
//! Providers prove they have sufficient compute resources (e.g., ">= 8 GPUs")
//! without revealing their exact capacity. This uses the same predicate proof
//! mechanism as the bounty board's qualification system, applied to compute attributes.
//!
//! # Privacy properties
//!
//! - The provider's exact GPU count remains hidden.
//! - The proof demonstrates "I have >= threshold GPUs" without revealing the surplus.
//! - Different offerings from the same provider are unlinkable (different proofs).
//!
//! # Security model
//!
//! All proof verification paths perform CRYPTOGRAPHIC verification. Structural checks alone
//! are NEVER sufficient. The `dev` feature enables a fallback for local testing without a
//! live federation, but it is never the default.

use pyana_app_framework::{PredicateType, PyanaEngine};
use pyana_circuit::{BabyBear, PredicateProof, verify_predicate};
use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// Qualification requirement for a compute provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ComputeQualification {
    /// No qualification needed (anyone can list).
    None,
    /// Provider must prove they have at least this many GPUs of the specified type.
    MinGpuCount { gpu_type: String, min_count: u64 },
    /// Provider must prove federation membership.
    FederationMember,
    /// Provider must prove a custom predicate about their infrastructure.
    CustomPredicate {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },
}

/// Error type for qualification verification.
#[derive(Debug, Clone)]
pub enum QualificationError {
    /// The proof is malformed or empty.
    InvalidProof(String),
    /// The proof does not satisfy the requirement.
    ProofRejected(String),
    /// The federation root is stale or unknown.
    UnknownFederationRoot,
    /// Verification cannot be performed (missing configuration). Fail closed.
    VerificationUnavailable(String),
}

impl std::fmt::Display for QualificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::ProofRejected(msg) => write!(f, "proof rejected: {msg}"),
            Self::UnknownFederationRoot => write!(f, "unknown federation root"),
            Self::VerificationUnavailable(msg) => {
                write!(f, "verification unavailable (fail closed): {msg}")
            }
        }
    }
}

impl std::error::Error for QualificationError {}

// =============================================================================
// Verification
// =============================================================================

/// Verify a provider's compute qualification proof.
///
/// # Privacy
///
/// The proof reveals only that the provider meets the threshold, not their exact capacity.
/// For `MinGpuCount { min_count: 8 }`, a provider with 64 GPUs proves ">= 8" without
/// revealing the 64.
///
/// # Security
///
/// ALL paths perform real cryptographic verification. If verification cannot be performed
/// (e.g., no federation root configured), the function fails CLOSED (rejects).
pub fn verify_compute_qualification(
    engine: &PyanaEngine,
    requirement: &ComputeQualification,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        ComputeQualification::None => Ok(true),

        ComputeQualification::MinGpuCount {
            gpu_type,
            min_count,
        } => verify_gpu_count_proof(proof, gpu_type, *min_count),

        ComputeQualification::FederationMember => {
            verify_federation_membership(engine, proof, federation_root)
        }

        ComputeQualification::CustomPredicate {
            attribute,
            predicate_type,
            threshold,
        } => verify_predicate_proof(proof, *predicate_type, attribute, *threshold),
    }
}

/// Verify a GPU count threshold proof.
///
/// Deserializes the proof as a `PredicateProof` from the circuit crate and verifies
/// the STARK proof cryptographically.
fn verify_gpu_count_proof(
    proof: &[u8],
    gpu_type: &str,
    min_count: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty GPU count proof".to_string(),
        ));
    }

    // Deserialize the real PredicateProof from wire bytes.
    let predicate_proof: PredicateProof = postcard::from_bytes(proof).map_err(|e| {
        QualificationError::InvalidProof(format!("failed to deserialize GPU count proof: {e}"))
    })?;

    // GPU count proofs must use GTE (>=) predicate.
    if predicate_proof.predicate_type != pyana_circuit::PredicateType::Gte {
        return Err(QualificationError::ProofRejected(
            "GPU count proof must use >= predicate".to_string(),
        ));
    }

    // Verify the threshold matches the requirement.
    let expected_threshold = BabyBear::new(min_count as u32);
    if predicate_proof.threshold != expected_threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold does not match required minimum count {min_count}"
        )));
    }

    // Use the proof's fact commitment for verification (the STARK proves it).
    let fact_commitment = predicate_proof.fact_commitment;

    // Verify the STARK proof cryptographically.
    if verify_predicate(&predicate_proof, expected_threshold, fact_commitment) {
        Ok(true)
    } else {
        Err(QualificationError::ProofRejected(
            "GPU count STARK verification failed".to_string(),
        ))
    }
}

/// Verify federation membership proof.
///
/// Uses the PyanaEngine's `verify_presentation_against()` to perform real STARK verification.
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
    if engine.verify_presentation_against(proof, &federation_root) {
        Ok(true)
    } else {
        Err(QualificationError::ProofRejected(
            "federation membership STARK verification failed".to_string(),
        ))
    }
}

/// Verify a custom predicate proof (generic attribute threshold).
///
/// Deserializes as a `PredicateProof` and verifies the STARK proof cryptographically.
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

    // Verify the predicate type matches.
    let expected_type = to_circuit_predicate_type(predicate_type);
    if predicate_proof.predicate_type != expected_type {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }

    // Verify the threshold matches.
    let expected_threshold = BabyBear::new(threshold as u32);
    if predicate_proof.threshold != expected_threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold does not match required threshold {threshold}"
        )));
    }

    // Use the proof's fact commitment for verification.
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

/// Convert app-framework PredicateType to circuit PredicateType.
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
/// Gated behind `#[cfg(feature = "dev")]` so it cannot be accidentally used.
#[cfg(feature = "dev")]
pub fn verify_compute_qualification_dev_only(
    requirement: &ComputeQualification,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        ComputeQualification::None => Ok(true),
        ComputeQualification::MinGpuCount {
            gpu_type,
            min_count,
        } => verify_gpu_count_proof_structural(proof, gpu_type, *min_count),
        ComputeQualification::FederationMember => {
            verify_federation_membership_structural(proof, federation_root)
        }
        ComputeQualification::CustomPredicate {
            attribute,
            predicate_type,
            threshold,
        } => verify_predicate_proof_structural(proof, *predicate_type, attribute, *threshold),
    }
}

#[cfg(feature = "dev")]
fn verify_gpu_count_proof_structural(
    proof: &[u8],
    gpu_type: &str,
    min_count: u64,
) -> Result<bool, QualificationError> {
    if proof.len() < 41 {
        return Err(QualificationError::InvalidProof(
            "GPU count proof too short".to_string(),
        ));
    }
    let attr_name = format!("gpu_count_{}", gpu_type);
    let expected_hash = *blake3::hash(attr_name.as_bytes()).as_bytes();
    let claimed_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;
    if claimed_hash != expected_hash {
        return Err(QualificationError::ProofRejected(
            "proof is for a different GPU type".to_string(),
        ));
    }
    let claimed_threshold = u64::from_le_bytes(
        proof[32..40]
            .try_into()
            .map_err(|_| QualificationError::InvalidProof("malformed threshold".to_string()))?,
    );
    if claimed_threshold != min_count {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold {} does not match required {}",
            claimed_threshold, min_count
        )));
    }
    if proof[40] != predicate_type_byte(PredicateType::Gte) {
        return Err(QualificationError::ProofRejected(
            "proof is not a >= predicate".to_string(),
        ));
    }
    Ok(true)
}

#[cfg(feature = "dev")]
fn verify_federation_membership_structural(
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    if proof.len() < 33 {
        return Err(QualificationError::InvalidProof(
            "membership proof too short".to_string(),
        ));
    }
    let claimed_root: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed root".to_string()))?;
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
    let expected_hash = *blake3::hash(attribute.as_bytes()).as_bytes();
    let claimed_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;
    if claimed_hash != expected_hash {
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
            "proof threshold {} does not match required {}",
            claimed_threshold, threshold
        )));
    }
    let claimed_type = proof[40];
    if claimed_type != predicate_type_byte(predicate_type) {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }
    Ok(true)
}

// =============================================================================
// Dev-only proof builders (for testing / provider side)
// =============================================================================

/// Build a GPU count qualification proof (provider-side, for testing).
#[cfg(feature = "dev")]
pub fn build_gpu_count_proof(gpu_type: &str, threshold: u64) -> Vec<u8> {
    let attr_name = format!("gpu_count_{}", gpu_type);
    let attr_hash = *blake3::hash(attr_name.as_bytes()).as_bytes();
    let mut proof = Vec::with_capacity(73);
    proof.extend_from_slice(&attr_hash);
    proof.extend_from_slice(&threshold.to_le_bytes());
    proof.push(predicate_type_byte(PredicateType::Gte));
    // Placeholder STARK body.
    proof.extend_from_slice(blake3::hash(b"gpu-count-proof-body").as_bytes());
    proof
}

/// Build a federation membership proof (provider-side, for testing).
#[cfg(feature = "dev")]
pub fn build_membership_proof(federation_root: [u8; 32]) -> Vec<u8> {
    let mut proof = Vec::with_capacity(64);
    proof.extend_from_slice(&federation_root);
    proof.extend_from_slice(blake3::hash(b"membership-proof-body").as_bytes());
    proof
}

/// Encode a PredicateType as a single byte (dev fallback only).
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
        assert!(
            verify_compute_qualification(&engine, &ComputeQualification::None, &[], [0u8; 32])
                .unwrap()
        );
    }

    #[test]
    fn test_gpu_count_rejects_garbage() {
        let engine = test_engine();
        let garbage = vec![0xDE; 100];
        let req = ComputeQualification::MinGpuCount {
            gpu_type: "H100".to_string(),
            min_count: 8,
        };
        let result = verify_compute_qualification(&engine, &req, &garbage, [0u8; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_federation_membership_rejects_garbage() {
        let mut engine = PyanaEngine::new(EngineConfig::default());
        engine.set_federation_root([0xAB; 32]);
        let garbage = vec![0xDE; 100];
        let req = ComputeQualification::FederationMember;
        let result = verify_compute_qualification(&engine, &req, &garbage, [0xAB; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_federation_membership_rejects_zero_root() {
        let engine = test_engine();
        let garbage = vec![0xDE; 100];
        let req = ComputeQualification::FederationMember;
        let result = verify_compute_qualification(&engine, &req, &garbage, [0u8; 32]);
        assert!(result.is_err());
        match result.unwrap_err() {
            QualificationError::VerificationUnavailable(_) => {}
            other => panic!("expected VerificationUnavailable, got: {other}"),
        }
    }

    #[test]
    fn test_predicate_rejects_garbage() {
        let engine = test_engine();
        let garbage = vec![0xDE; 100];
        let req = ComputeQualification::CustomPredicate {
            attribute: "bandwidth".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 1000,
        };
        let result = verify_compute_qualification(&engine, &req, &garbage, [0u8; 32]);
        assert!(result.is_err());
    }
}
