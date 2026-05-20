//! Mock utilities for testing the chain integration without SP1 toolchain.
//!
//! This module provides helpers that simulate the full proving pipeline:
//! STARK proof -> SP1 wrapping -> EVM verification, all without external dependencies.

use crate::error::ChainError;
use crate::prove::EvmProof;

/// Simulate the full end-to-end flow: generate a STARK proof, wrap it, verify it.
///
/// This is useful for integration testing the API surface without the SP1 toolchain.
pub async fn mock_end_to_end(
    leaf_hash: u32,
    merkle_root: u32,
) -> Result<EvmProof, ChainError> {
    // Build a fake STARK proof with valid header
    let mut stark_proof = b"PYNA".to_vec();
    stark_proof.push(1); // version
    // Minimal proof body (not a real proof, but has the right structure for mock)
    stark_proof.extend_from_slice(&[0u8; 64]); // trace commitment
    stark_proof.extend_from_slice(&[0u8; 64]); // constraint commitment
    stark_proof.extend_from_slice(&0u32.to_le_bytes()); // 0 fri commitments
    stark_proof.extend_from_slice(&0u32.to_le_bytes()); // 0 fri final poly
    stark_proof.extend_from_slice(&2u32.to_le_bytes()); // 2 public inputs
    stark_proof.extend_from_slice(&leaf_hash.to_le_bytes());
    stark_proof.extend_from_slice(&merkle_root.to_le_bytes());

    let public_inputs = vec![leaf_hash, merkle_root];

    crate::wrap_for_evm(&stark_proof, &public_inputs).await
}

/// Check if the SP1 toolchain is available on this system.
pub fn sp1_toolchain_available() -> bool {
    std::process::Command::new("cargo")
        .args(["prove", "--version"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Print setup instructions for the SP1 toolchain.
pub fn print_setup_instructions() {
    eprintln!("=== SP1 Toolchain Setup ===");
    eprintln!();
    eprintln!("The SP1 toolchain is required for real proof generation.");
    eprintln!("Install it with:");
    eprintln!();
    eprintln!("  curl -L https://sp1.succinct.xyz | bash");
    eprintln!("  sp1up");
    eprintln!();
    eprintln!("Then build the guest program:");
    eprintln!();
    eprintln!("  cd chain/program && cargo prove build");
    eprintln!();
    eprintln!("After that, use `--features prove` instead of `--features mock`:");
    eprintln!();
    eprintln!("  cargo build -p pyana-chain --no-default-features --features prove");
    eprintln!();
    eprintln!("For on-chain verification, also enable the `on-chain` feature:");
    eprintln!();
    eprintln!("  cargo build -p pyana-chain --no-default-features --features prove,on-chain");
    eprintln!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_mock_end_to_end() {
        let proof = mock_end_to_end(12345, 67890).await.unwrap();
        assert!(!proof.proof_bytes.is_empty());
        assert!(!proof.public_values.is_empty());

        // Verify the mock proof
        let verified = crate::verify_on_chain(
            &proof,
            "http://localhost:8545",
            &proof.verifier_address,
        )
        .await
        .unwrap();
        assert!(verified);
    }
}
