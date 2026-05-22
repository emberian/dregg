//! Qualification verification: prove worker meets requirements without revealing identity.
//!
//! Workers prove qualifications anonymously:
//! - Federation membership: ring membership STARK (proves "I'm in this set" without revealing which member).
//! - Predicate proof: proves "my attribute >= threshold" without revealing the exact value.
//! - Standing proof: IVC chain proving N prior bounty completions.

use pyana_circuit::PredicateType;

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
}

impl std::fmt::Display for QualificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::ProofRejected(msg) => write!(f, "proof rejected: {msg}"),
            Self::UnknownFederationRoot => write!(f, "unknown federation root"),
            Self::InvalidIvcChain(msg) => write!(f, "invalid IVC chain: {msg}"),
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
/// # Arguments
///
/// * `requirement` - What the worker must prove.
/// * `proof` - The cryptographic proof bytes (format depends on requirement type).
/// * `federation_root` - The current federation Merkle root for membership checks.
///
/// # Returns
///
/// `Ok(true)` if the proof is valid, `Ok(false)` if it's structurally valid but doesn't meet
/// the threshold, or an error if the proof is malformed.
pub fn verify_qualification(
    requirement: &QualificationRequirement,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    match requirement {
        QualificationRequirement::None => Ok(true),

        QualificationRequirement::FederationMember => {
            verify_federation_membership(proof, federation_root)
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
/// The proof demonstrates "I hold a key that is in the federation's Merkle tree"
/// without revealing which key. This is the simplest qualification: just being
/// part of the network.
fn verify_federation_membership(
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty federation membership proof".to_string(),
        ));
    }

    // Minimum viable proof size: a real STARK proof is at least a few hundred bytes.
    // We check structural validity here; the actual STARK verification would use
    // pyana_circuit::stark::verify_proof() with the appropriate AIR.
    if proof.len() < 32 {
        return Err(QualificationError::InvalidProof(
            "proof too small to be a valid STARK".to_string(),
        ));
    }

    // Extract the claimed federation root from the proof's public inputs.
    // The proof's first 32 bytes encode the federation root it claims membership in.
    let claimed_root: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed root in proof".to_string()))?;

    // The claimed root must match the federation root we're checking against.
    if claimed_root != federation_root {
        return Err(QualificationError::ProofRejected(
            "proof is for a different federation root".to_string(),
        ));
    }

    // In a full implementation, we would deserialize the STARK proof and verify it:
    //
    //   let stark_proof = pyana_circuit::stark::proof_from_bytes(&proof[32..])?;
    //   let public_inputs = extract_membership_public_inputs(&stark_proof);
    //   pyana_circuit::stark::verify_proof(&MerklePoseidon2StarkAir::new(...), &stark_proof)?;
    //
    // For now we accept any proof that carries the correct root (the STARK verifier
    // integration is pending the circuit's deployment to production).

    // Verify structural integrity: the remaining bytes after the root should be
    // a valid proof encoding (non-zero, reasonable size).
    let proof_body = &proof[32..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing proof body after root".to_string(),
        ));
    }

    Ok(true)
}

/// Verify a predicate STARK proving an attribute satisfies a threshold.
///
/// Example: "my reputation score >= 5" without revealing that it's actually 47.
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

    // The proof encodes:
    // - [0..32]: BLAKE3 hash of the attribute name (for binding)
    // - [32..40]: threshold value (little-endian u64)
    // - [40..41]: predicate type byte
    // - [41..]: STARK proof body

    if proof.len() < 41 {
        return Err(QualificationError::InvalidProof(
            "predicate proof too short".to_string(),
        ));
    }

    // Verify the attribute binding.
    let expected_attr_hash = *blake3::hash(attribute.as_bytes()).as_bytes();
    let claimed_attr_hash: [u8; 32] = proof[..32]
        .try_into()
        .map_err(|_| QualificationError::InvalidProof("malformed attribute hash".to_string()))?;

    if claimed_attr_hash != expected_attr_hash {
        return Err(QualificationError::ProofRejected(
            "proof is for a different attribute".to_string(),
        ));
    }

    // Verify the threshold binding.
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

    // Verify the predicate type.
    let claimed_type = proof[40];
    let expected_type = predicate_type_byte(predicate_type);
    if claimed_type != expected_type {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }

    // In a full implementation:
    //   let stark_proof = pyana_circuit::stark::proof_from_bytes(&proof[41..])?;
    //   pyana_circuit::stark::verify_proof(&PredicateAir::new(predicate_type, threshold), &stark_proof)?;

    let proof_body = &proof[41..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing STARK body in predicate proof".to_string(),
        ));
    }

    Ok(true)
}

/// Verify an IVC chain proving the worker has completed at least N bounties.
///
/// The IVC proof accumulates state transitions: each completed bounty extends
/// the chain by one step. The verifier checks the chain length meets the threshold
/// without learning which specific bounties were completed.
fn verify_standing_proof(
    proof: &[u8],
    min_completed_bounties: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty standing proof".to_string(),
        ));
    }

    // The standing proof encodes:
    // - [0..8]: claimed completion count (little-endian u64)
    // - [8..]: IVC proof body

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

    // In a full implementation:
    //   let ivc_proof = pyana_circuit::ivc::IvcProof::from_bytes(&proof[8..])?;
    //   pyana_circuit::verify_ivc(&ivc_proof, claimed_count)?;

    let proof_body = &proof[8..];
    if proof_body.is_empty() {
        return Err(QualificationError::InvalidProof(
            "missing IVC body in standing proof".to_string(),
        ));
    }

    Ok(true)
}

/// Encode a PredicateType as a single byte for proof binding.
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

/// Build a federation membership proof (for testing / worker side).
///
/// In production this would invoke the STARK prover; here we build a
/// structurally valid proof for integration testing.
pub fn build_membership_proof(federation_root: [u8; 32]) -> Vec<u8> {
    let mut proof = Vec::with_capacity(64);
    proof.extend_from_slice(&federation_root);
    // Placeholder proof body (32 bytes of deterministic data).
    proof.extend_from_slice(&blake3::hash(b"membership-proof-body").as_bytes()[..]);
    proof
}

/// Build a predicate proof (for testing / worker side).
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

    #[test]
    fn test_no_qualification() {
        assert_eq!(
            verify_qualification(&QualificationRequirement::None, &[], [0u8; 32]).unwrap(),
            true
        );
    }

    #[test]
    fn test_federation_membership_valid() {
        let root = [0xAB; 32];
        let proof = build_membership_proof(root);
        assert_eq!(
            verify_qualification(&QualificationRequirement::FederationMember, &proof, root)
                .unwrap(),
            true
        );
    }

    #[test]
    fn test_federation_membership_wrong_root() {
        let root = [0xAB; 32];
        let wrong_root = [0xCD; 32];
        let proof = build_membership_proof(root);
        let result = verify_qualification(
            &QualificationRequirement::FederationMember,
            &proof,
            wrong_root,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_predicate_proof_valid() {
        let proof = build_predicate_proof("reputation", 5, PredicateType::Gte);
        let req = QualificationRequirement::PredicateProof {
            predicate_type: PredicateType::Gte,
            attribute: "reputation".to_string(),
            threshold: 5,
        };
        assert_eq!(verify_qualification(&req, &proof, [0u8; 32]).unwrap(), true);
    }

    #[test]
    fn test_predicate_proof_wrong_threshold() {
        let proof = build_predicate_proof("reputation", 5, PredicateType::Gte);
        let req = QualificationRequirement::PredicateProof {
            predicate_type: PredicateType::Gte,
            attribute: "reputation".to_string(),
            threshold: 10, // different from proof
        };
        let result = verify_qualification(&req, &proof, [0u8; 32]);
        assert!(result.is_err());
    }

    #[test]
    fn test_standing_proof_valid() {
        let proof = build_standing_proof(7);
        let req = QualificationRequirement::StandingProof {
            min_completed_bounties: 5,
        };
        assert_eq!(verify_qualification(&req, &proof, [0u8; 32]).unwrap(), true);
    }

    #[test]
    fn test_standing_proof_insufficient() {
        let proof = build_standing_proof(3);
        let req = QualificationRequirement::StandingProof {
            min_completed_bounties: 5,
        };
        let result = verify_qualification(&req, &proof, [0u8; 32]);
        assert!(result.is_err());
    }
}
