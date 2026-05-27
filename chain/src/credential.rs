//! Anonymous credential wrapping for on-chain verification.
//!
//! This module provides the host-side logic for wrapping dregg anonymous credential
//! presentations into SP1/Groth16 proofs that can be verified by the
//! [`IDreggCredentialGate`] contract on Base.
//!
//! # Architecture
//!
//! ```text
//! AnonymousPresentation (ring membership + predicate proof)
//!        |
//!        | wrap_credential_for_chain()
//!        v
//! SP1 Guest (verifies the STARK presentation inside RISC-V zkVM)
//!        |
//!        v
//! EvmCredentialProof (Groth16 proof + public inputs for contract)
//! ```
//!
//! # Privacy Guarantees
//!
//! The resulting on-chain proof reveals ONLY:
//! - Which federation's membership tree was proven against (`federation_root`)
//! - What predicate was satisfied (`predicate_hash`)
//! - A presentation nullifier (optional, for sybil resistance)
//!
//! The proof hides:
//! - The presenter's identity (ring membership)
//! - The credential's serial number (blinded)
//! - The private attribute value (only predicate satisfaction is proven)
//! - Whether this is the same user who presented before (unlinkable)

use crate::error::ChainError;
use serde::{Deserialize, Serialize};

/// An anonymous credential presentation ready for on-chain submission.
///
/// This is the input to `wrap_credential_for_chain`. In production, it comes from
/// `dregg-bridge`'s `BridgePresentationBuilder::prove()` which generates the full
/// STARK proof of ring membership + predicate satisfaction.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AnonymousPresentation {
    /// The STARK proof bytes (from `proof_to_bytes()`).
    /// Proves: ring membership + predicate satisfaction + credential binding.
    pub stark_proof_bytes: Vec<u8>,

    /// Public inputs to the STARK verifier (field elements as u32).
    /// Typically: [federation_root_limbs..., predicate_hash_limbs..., nullifier_limbs...]
    pub public_inputs: Vec<u32>,

    /// The presentation nullifier (deterministic from credential + action domain).
    /// Used for sybil resistance: same credential cannot present twice per action.
    /// Set to all-zeros for unlinkable (non-sybil-resistant) presentations.
    pub presentation_nullifier: [u8; 32],
}

/// A credential proof formatted for the IDreggCredentialGate contract.
///
/// Contains the Groth16 proof and the public inputs that the contract will check.
/// The contract calls the SP1 Verifier Gateway to verify the Groth16 proof,
/// then checks that the committed public values match the expected federation root
/// and predicate hash.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvmCredentialProof {
    /// The Groth16 proof bytes (from SP1 wrapping).
    pub proof_bytes: Vec<u8>,

    /// The public values committed by the SP1 guest.
    /// Encodes: (valid: bool, federation_root: [u8;32], predicate_hash: [u8;32], nullifier: [u8;32])
    pub public_values: Vec<u8>,

    /// The SP1 program verification key (identifies the credential verifier program).
    pub vkey: String,

    /// The SP1 Verifier Gateway address on Base.
    pub verifier_address: String,

    /// The federation root this proof was generated against.
    pub federation_root: [u8; 32],

    /// The predicate hash this proof proves satisfaction of.
    pub predicate_hash: [u8; 32],

    /// The presentation nullifier (for sybil resistance).
    pub presentation_nullifier: [u8; 32],
}

/// Public values committed by the SP1 guest for credential verification.
///
/// These are the values that the on-chain contract checks after proof verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct CredentialPublicValues {
    /// Whether the STARK proof verified successfully.
    valid: bool,
    /// The federation root (which membership tree was proven against).
    federation_root: [u8; 32],
    /// The predicate hash (what was proven).
    predicate_hash: [u8; 32],
    /// Presentation nullifier for sybil resistance.
    presentation_nullifier: [u8; 32],
}

/// Wrap an anonymous credential presentation for on-chain verification.
///
/// The resulting proof can be verified by the `IDreggCredentialGate` contract on Base.
///
/// # Arguments
/// * `presentation` - The anonymous presentation (STARK proof of ring membership + predicate)
/// * `federation_root` - The root of the federation member tree (32 bytes)
/// * `predicate_hash` - Hash identifying what's being proven (e.g., `keccak256("age >= 18")`)
///
/// # Returns
/// An `EvmCredentialProof` containing the Groth16 proof and public inputs ready for
/// submission to the `IDreggCredentialGate` contract.
///
/// # Mock Mode
/// Without the `prove` feature, this produces a simulated proof suitable for testing
/// the integration flow end-to-end.
pub async fn wrap_credential_for_chain(
    presentation: &AnonymousPresentation,
    federation_root: [u8; 32],
    predicate_hash: [u8; 32],
) -> Result<EvmCredentialProof, ChainError> {
    // Validate the presentation has a well-formed STARK proof header
    if presentation.stark_proof_bytes.len() < 5 || &presentation.stark_proof_bytes[0..4] != b"DREG"
    {
        return Err(ChainError::InvalidProof(
            "anonymous presentation has invalid STARK proof header".to_string(),
        ));
    }

    #[cfg(feature = "mock")]
    {
        return mock_wrap_credential(presentation, federation_root, predicate_hash).await;
    }

    #[cfg(all(feature = "prove", not(feature = "mock")))]
    {
        return real_wrap_credential(presentation, federation_root, predicate_hash).await;
    }

    #[cfg(not(any(feature = "mock", feature = "prove")))]
    {
        let _ = (presentation, federation_root, predicate_hash);
        Err(ChainError::ToolchainMissing)
    }
}

/// Mock implementation for development without SP1 toolchain.
#[cfg(feature = "mock")]
async fn mock_wrap_credential(
    presentation: &AnonymousPresentation,
    federation_root: [u8; 32],
    predicate_hash: [u8; 32],
) -> Result<EvmCredentialProof, ChainError> {
    use blake3::Hasher;

    // Generate a deterministic mock Groth16 proof
    let mut hasher = Hasher::new();
    hasher.update(b"mock-credential-groth16:");
    hasher.update(&presentation.stark_proof_bytes);
    hasher.update(&federation_root);
    hasher.update(&predicate_hash);
    let mock_proof = hasher.finalize().as_bytes().to_vec();

    // Serialize public values as the guest would commit them
    let public_values = CredentialPublicValues {
        valid: true,
        federation_root,
        predicate_hash,
        presentation_nullifier: presentation.presentation_nullifier,
    };
    let public_values_bytes = bincode::serialize(&public_values)
        .map_err(|e| ChainError::InvalidProof(format!("serialization error: {e}")))?;

    Ok(EvmCredentialProof {
        proof_bytes: mock_proof,
        public_values: public_values_bytes,
        vkey: crate::SP1_PROGRAM_VKEY.to_string(),
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
        federation_root,
        predicate_hash,
        presentation_nullifier: presentation.presentation_nullifier,
    })
}

/// Verify a credential proof locally (mock mode).
///
/// In production, this would be done by the on-chain contract. This function
/// is useful for testing the proof format before submitting on-chain.
pub fn verify_credential_proof_locally(proof: &EvmCredentialProof) -> Result<bool, ChainError> {
    if proof.proof_bytes.is_empty() {
        return Err(ChainError::InvalidProof("empty proof bytes".to_string()));
    }
    if proof.public_values.is_empty() {
        return Err(ChainError::InvalidProof("empty public values".to_string()));
    }

    // Decode the public values
    let values: CredentialPublicValues = bincode::deserialize(&proof.public_values)
        .map_err(|e| ChainError::InvalidProof(format!("cannot decode public values: {e}")))?;

    // Check that the committed values match the proof's metadata
    if values.federation_root != proof.federation_root {
        return Err(ChainError::InvalidProof(
            "federation root mismatch between public values and proof metadata".to_string(),
        ));
    }
    if values.predicate_hash != proof.predicate_hash {
        return Err(ChainError::InvalidProof(
            "predicate hash mismatch between public values and proof metadata".to_string(),
        ));
    }

    Ok(values.valid)
}

/// Compute the predicate hash for a given predicate string.
///
/// On-chain, this would be `keccak256(predicate_string)`. Off-chain, we use blake3
/// for consistency with dregg's hash function. The contract would map between the two.
pub fn compute_predicate_hash(predicate: &str) -> [u8; 32] {
    *blake3::hash(predicate.as_bytes()).as_bytes()
}

/// Compute a presentation nullifier for sybil resistance.
///
/// The nullifier is deterministic from the credential serial and action domain,
/// but unlinkable to the credential's identity.
///
/// `nullifier = blake3("dregg-presentation-nullifier-v1", credential_serial || action_domain)`
pub fn compute_presentation_nullifier(
    credential_serial: &[u8; 32],
    action_domain: &str,
) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + action_domain.len());
    input.extend_from_slice(credential_serial);
    input.extend_from_slice(action_domain.as_bytes());
    blake3::derive_key("dregg-presentation-nullifier-v1", &input)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mock_presentation() -> AnonymousPresentation {
        let mut stark_proof = b"DREG".to_vec();
        stark_proof.push(1); // version
        stark_proof.extend_from_slice(&[0u8; 100]); // mock proof body

        AnonymousPresentation {
            stark_proof_bytes: stark_proof,
            public_inputs: vec![12345, 67890],
            presentation_nullifier: [0xAA; 32],
        }
    }

    #[tokio::test]
    async fn test_wrap_credential_rejects_invalid_proof() {
        let bad = AnonymousPresentation {
            stark_proof_bytes: b"garbage".to_vec(),
            public_inputs: vec![],
            presentation_nullifier: [0; 32],
        };
        let result = wrap_credential_for_chain(&bad, [0; 32], [0; 32]).await;
        assert!(result.is_err());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_wrap_credential_succeeds() {
        let presentation = mock_presentation();
        let fed_root = [0x11; 32];
        let pred_hash = [0x22; 32];

        let result = wrap_credential_for_chain(&presentation, fed_root, pred_hash).await;
        assert!(result.is_ok());

        let proof = result.unwrap();
        assert_eq!(proof.federation_root, fed_root);
        assert_eq!(proof.predicate_hash, pred_hash);
        assert_eq!(proof.presentation_nullifier, [0xAA; 32]);
        assert!(!proof.proof_bytes.is_empty());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_verify_credential_proof_locally() {
        let presentation = mock_presentation();
        let fed_root = [0x11; 32];
        let pred_hash = [0x22; 32];

        let proof = wrap_credential_for_chain(&presentation, fed_root, pred_hash)
            .await
            .unwrap();
        let verified = verify_credential_proof_locally(&proof).unwrap();
        assert!(verified);
    }

    #[test]
    fn test_predicate_hash_deterministic() {
        let h1 = compute_predicate_hash("age >= 18");
        let h2 = compute_predicate_hash("age >= 18");
        assert_eq!(h1, h2);

        let h3 = compute_predicate_hash("age >= 21");
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_presentation_nullifier_deterministic_and_domain_separated() {
        let serial = [0x42; 32];
        let n1 = compute_presentation_nullifier(&serial, "mint:token:123");
        let n2 = compute_presentation_nullifier(&serial, "mint:token:123");
        assert_eq!(n1, n2);

        // Different action domain -> different nullifier
        let n3 = compute_presentation_nullifier(&serial, "vote:proposal:456");
        assert_ne!(n1, n3);

        // Different credential -> different nullifier
        let other_serial = [0x99; 32];
        let n4 = compute_presentation_nullifier(&other_serial, "mint:token:123");
        assert_ne!(n1, n4);
    }
}
