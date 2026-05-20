//! SP1 proof wrapping: STARK proof -> Groth16 proof for EVM verification.

use crate::error::ChainError;
use serde::{Deserialize, Serialize};

/// A Groth16 proof ready for EVM on-chain verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvmProof {
    /// The Groth16 proof bytes (formatted for the SP1 verifier contract).
    pub proof_bytes: Vec<u8>,
    /// The public values committed by the SP1 guest program.
    /// Contains: verification_result (bool) + original public inputs (leaf, root).
    pub public_values: Vec<u8>,
    /// The SP1 program verification key (identifies our STARK verifier program).
    pub vkey: String,
    /// The address of the SP1 verifier contract to call.
    pub verifier_address: String,
}

/// Generate a Groth16 proof wrapping a pyana STARK proof for EVM verification.
///
/// This function:
/// 1. Sets up the SP1 prover with our guest program ELF
/// 2. Passes the STARK proof + public inputs as guest program inputs
/// 3. Executes the guest (which runs the full STARK verifier)
/// 4. Generates a Groth16 proof of correct execution
/// 5. Returns proof bytes formatted for the on-chain SP1 verifier
///
/// # Arguments
/// * `stark_proof_bytes` - Serialized STARK proof (from `circuit::stark::proof_to_bytes()`)
/// * `public_inputs` - The public inputs (e.g., `[leaf_hash, merkle_root]` as u32 field elements)
///
/// # Requirements
/// Without the `prove` feature (default `mock` mode), this produces simulated proofs
/// suitable for testing the integration flow. With `prove` enabled:
/// - SP1 toolchain must be installed (`sp1up`)
/// - Guest program must be built (`cd chain/program && cargo prove build`)
///
/// # Returns
/// An `EvmProof` containing the Groth16 proof bytes and metadata for on-chain submission.
pub async fn wrap_for_evm(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    #[cfg(feature = "mock")]
    {
        return mock_wrap(stark_proof_bytes, public_inputs).await;
    }

    #[cfg(all(feature = "prove", not(feature = "mock")))]
    {
        return real_wrap(stark_proof_bytes, public_inputs).await;
    }

    #[cfg(not(any(feature = "mock", feature = "prove")))]
    {
        let _ = (stark_proof_bytes, public_inputs);
        Err(ChainError::ToolchainMissing)
    }
}

/// Mock implementation for development without SP1 toolchain.
#[cfg(feature = "mock")]
async fn mock_wrap(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    use blake3::Hasher;

    // Validate that the proof bytes look reasonable
    if stark_proof_bytes.len() < 5 || &stark_proof_bytes[0..4] != b"PYNA" {
        return Err(ChainError::InvalidProof(
            "invalid proof header (expected PYNA magic)".to_string(),
        ));
    }

    // Generate a deterministic mock proof (hash of inputs)
    let mut hasher = Hasher::new();
    hasher.update(b"mock-groth16-proof:");
    hasher.update(stark_proof_bytes);
    for pi in public_inputs {
        hasher.update(&pi.to_le_bytes());
    }
    let mock_proof = hasher.finalize().as_bytes().to_vec();

    // Serialize public values as the guest would
    let public_values = bincode::serialize(&(true, public_inputs.to_vec()))
        .map_err(|e| ChainError::InvalidProof(e.to_string()))?;

    Ok(EvmProof {
        proof_bytes: mock_proof,
        public_values,
        vkey: crate::SP1_PROGRAM_VKEY.to_string(),
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
    })
}

/// Real SP1 proving implementation (requires SP1 toolchain).
///
/// This compiles and runs only with `--features prove`.
/// The SP1 toolchain (`sp1up`) must be installed and the guest program
/// must have been built with `cargo prove build`.
#[cfg(all(feature = "prove", not(feature = "mock")))]
async fn real_wrap(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    use sp1_sdk::prelude::*;

    // Load the guest program ELF (built by `cargo prove build`)
    // This macro embeds the ELF at compile time from the build artifact.
    let elf_bytes = include_elf!("pyana-sp1-program");

    // Set up the CPU prover
    let client = sp1_sdk::ProverClient::builder().cpu().build().await;

    // Prepare stdin with the STARK proof and public inputs
    let mut stdin = SP1Stdin::new();

    // Write the raw STARK proof bytes (the guest deserializes with bincode)
    // We serialize the proof as a Vec<u8> so the guest can read it generically
    stdin.write(&stark_proof_bytes.to_vec());
    stdin.write(&public_inputs.to_vec());

    // Setup proving key from ELF
    let elf = Elf::decode(elf_bytes).map_err(|e| ChainError::ProvingFailed(e.to_string()))?;
    let pk = client
        .setup(elf)
        .await
        .map_err(|e| ChainError::ProvingFailed(format!("{e}")))?;

    // Generate the Groth16 proof (this is the expensive step - may take minutes)
    let proof_result = client
        .prove(&pk, stdin)
        .groth16()
        .await
        .map_err(|e| ChainError::ProvingFailed(format!("{e}")))?;

    // Extract the proof bytes formatted for the EVM verifier contract
    let proof_bytes = proof_result.bytes();
    let public_values = proof_result.public_values.as_slice().to_vec();
    let vkey = pk.verifying_key().bytes32();

    Ok(EvmProof {
        proof_bytes,
        public_values,
        vkey,
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_mock_wrap_rejects_invalid_proof() {
        let result = wrap_for_evm(b"garbage", &[1, 2]).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ChainError::InvalidProof(_)));
    }

    #[tokio::test]
    async fn test_mock_wrap_accepts_valid_header() {
        // Minimal valid-looking proof: PYNA magic + version byte + some data
        let mut fake_proof = b"PYNA".to_vec();
        fake_proof.push(1);
        fake_proof.extend_from_slice(&[0u8; 100]);

        let result = wrap_for_evm(&fake_proof, &[12345, 67890]).await;
        assert!(result.is_ok());

        let evm_proof = result.unwrap();
        assert!(!evm_proof.proof_bytes.is_empty());
        assert!(!evm_proof.public_values.is_empty());
        assert!(!evm_proof.verifier_address.is_empty());
    }

    #[tokio::test]
    async fn test_mock_wrap_deterministic() {
        let mut proof = b"PYNA".to_vec();
        proof.push(1);
        proof.extend_from_slice(&[42u8; 64]);

        let r1 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        let r2 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        assert_eq!(r1.proof_bytes, r2.proof_bytes);
    }

    #[tokio::test]
    async fn test_evm_proof_serialization_roundtrip() {
        let mut proof = b"PYNA".to_vec();
        proof.push(1);
        proof.extend_from_slice(&[99u8; 64]);

        let evm_proof = wrap_for_evm(&proof, &[111, 222]).await.unwrap();
        let json = serde_json::to_string(&evm_proof).unwrap();
        let deserialized: EvmProof = serde_json::from_str(&json).unwrap();
        assert_eq!(evm_proof.proof_bytes, deserialized.proof_bytes);
        assert_eq!(evm_proof.public_values, deserialized.public_values);
    }
}
