//! Standalone verification utilities for presentation proofs.
//!
//! This module provides convenience functions for verifying authorization proofs
//! without needing to construct a full wallet or runtime. These are intended for
//! the verifier side of a presentation exchange.

use crate::error::SdkError;

/// Verify a serialized authorization proof against a federation root.
///
/// This is the verifier-side entry point: given proof bytes (produced by
/// [`AgentWallet::prove_authorization`](crate::AgentWallet::prove_authorization))
/// and the federation root of trust, check whether the proof is valid.
///
/// The proof bytes should be a serialized `BridgePresentationProof` (via postcard)
/// or raw STARK proof bytes (from `BridgePresentationProof::issuer_proof_bytes()`).
///
/// # Arguments
///
/// * `proof_bytes` - Serialized proof bytes.
/// * `federation_root` - The 32-byte federation root of trust (public parameter).
///
/// # Returns
///
/// `Ok(true)` if the proof verifies successfully, `Ok(false)` if the proof is
/// structurally valid but verification fails, or `Err(...)` if the proof cannot
/// be deserialized.
///
/// # Example
///
/// ```no_run
/// use pyana_sdk::verify_authorization_proof;
///
/// let proof_bytes: Vec<u8> = /* received from presenter */ vec![];
/// let federation_root: [u8; 32] = /* known public parameter */ [0u8; 32];
///
/// match verify_authorization_proof(&proof_bytes, &federation_root) {
///     Ok(true) => println!("Authorization verified!"),
///     Ok(false) => println!("Proof invalid"),
///     Err(e) => println!("Deserialization error: {}", e),
/// }
/// ```
pub fn verify_authorization_proof(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
) -> Result<bool, SdkError> {
    use pyana_circuit::BabyBear;
    use pyana_circuit::stark;

    // Interpret as raw STARK proof bytes (the standard wire format produced by
    // BridgePresentationProof::issuer_proof_bytes()).
    let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|_| {
        SdkError::Wire("proof bytes could not be deserialized as a STARK proof".into())
    })?;

    // SECURITY: Use new_canonical() for values from external (potentially adversarial)
    // proof data. This ensures modular reduction is applied, preventing non-canonical
    // representations that could cause malleability (same field element with different
    // byte encodings comparing as unequal).
    let pi: Vec<BabyBear> = stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    if pi.len() < 2 {
        return Ok(false);
    }

    // Check federation root matches.
    let expected_root = if federation_root[4..].iter().all(|&b| b == 0) {
        BabyBear::new(u32::from_le_bytes([
            federation_root[0],
            federation_root[1],
            federation_root[2],
            federation_root[3],
        ]))
    } else {
        pyana_bridge::present::bytes_to_babybear(federation_root)
    };

    if pi[1] != expected_root {
        return Ok(false);
    }

    // Try Poseidon2 AIR first (production), then linear AIR (legacy).
    use pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir;
    if stark::verify(&MerklePoseidon2StarkAir, &stark_proof, &pi).is_ok() {
        return Ok(true);
    }

    let air = stark::MerkleStarkAir;
    Ok(stark::verify(&air, &stark_proof, &pi).is_ok())
}
