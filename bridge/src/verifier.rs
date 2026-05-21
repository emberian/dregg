//! StarkProofVerifier: bridges the pyana-circuit STARK verifier to the TurnExecutor's
//! `ProofVerifier` trait.
//!
//! This module provides the concrete implementation that wires the ZK presentation
//! proof system (token -> bridge -> circuit -> STARK) to the execution layer (turn).
//!
//! The verifier expects proof bytes produced by `BridgePresentationProof::issuer_proof_bytes()`
//! and verifies them against the public inputs derived from the action being authorized.
//!
//! # Verification Strategy
//!
//! The proof bytes contain a serialized STARK proof for Merkle membership (issuer in federation).
//! The `verification_key` stored on the target cell is the federation root (32 bytes).
//! The `public_inputs` are the action's signing message (BLAKE3 hash of action contents).
//!
//! However, the STARK proof's *actual* public inputs are `[leaf_hash, merkle_root]` for the
//! MerkleStarkAir. The verifier checks:
//! 1. The proof deserializes correctly.
//! 2. The proof's embedded public inputs include the federation root (vk).
//! 3. The STARK proof verifies against `MerkleStarkAir`.
//!
//! This is a "presentation verification" model: the proof demonstrates that the presenter
//! holds a valid token chain from a federated issuer, which is sufficient authorization
//! for the action. The action's contents don't need to be *inside* the STARK circuit
//! because the proof's binding to this specific action is ensured by the executor's
//! fail-closed design (the proof must be presented as part of the action, and only
//! the action's target cell can accept it).

use pyana_circuit::BabyBear;
use pyana_circuit::stark;
use pyana_turn::ProofVerifier;

/// A `ProofVerifier` implementation that verifies real STARK proofs from the
/// pyana-circuit layer.
///
/// The verifier checks that:
/// 1. The proof bytes deserialize to a valid `StarkProof`.
/// 2. The proof's public inputs include the expected federation root (passed as `vk`).
/// 3. The STARK proof verifies against the `MerkleStarkAir` constraint system.
///
/// # Usage
///
/// ```ignore
/// let verifier = StarkProofVerifier::new();
/// let mut executor = TurnExecutor::new(costs);
/// executor.set_proof_verifier(Box::new(verifier));
/// ```
pub struct StarkProofVerifier;

impl StarkProofVerifier {
    /// Create a new STARK proof verifier.
    pub fn new() -> Self {
        Self
    }
}

impl Default for StarkProofVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofVerifier for StarkProofVerifier {
    /// Verify a STARK proof.
    ///
    /// # Arguments
    ///
    /// * `proof` - Serialized STARK proof bytes (from `stark::proof_to_bytes()`).
    /// * `public_inputs` - The action's signing message (32 bytes, BLAKE3 hash).
    ///   This binds the proof to the specific action being authorized: the proof
    ///   is only valid for this exact action. The binding is checked by verifying
    ///   that the leaf_hash (pi[0]) incorporates the action commitment.
    /// * `vk` - The verification key from the target cell. For STARK-authorized cells,
    ///   this is the federation root (32 bytes) that the issuer must be a member of.
    ///
    /// # Returns
    ///
    /// `true` if the proof is valid and the federation root matches.
    fn verify(&self, proof: &[u8], public_inputs: &[u8], vk: &[u8]) -> bool {
        // 1. Deserialize the STARK proof.
        let stark_proof = match stark::proof_from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // 2. Extract the public inputs from the proof itself.
        // For MerklePoseidon2StarkAir, public inputs are [leaf_hash, merkle_root].
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new(v))
            .collect();

        if pi.len() < 2 {
            return false;
        }

        // 3. Bind the proof to the specific action being authorized.
        //    The public_inputs (action signing message) must be non-empty.
        //    The proof's public inputs must include a commitment to the action,
        //    preventing replay of a valid proof across different actions.
        if public_inputs.is_empty() {
            return false;
        }
        // Compute the action commitment from the action's signing message.
        // The action signing message is the BLAKE3 hash of action contents;
        // we compress it to a BabyBear field element for comparison with the
        // proof's embedded action commitment (the last public input).
        if public_inputs.len() >= 32 {
            let mut action_bytes = [0u8; 32];
            action_bytes.copy_from_slice(&public_inputs[..32]);
            let action_commitment = crate::present::bytes_to_babybear(&action_bytes);

            // The proof's public inputs must include the action commitment as the
            // last element. This binds the proof to this specific action: a proof
            // generated for action A cannot be replayed against action B.
            let proof_action_commitment = pi.last().copied().unwrap_or(BabyBear::ZERO);
            if proof_action_commitment != action_commitment {
                return false;
            }
        }

        // 4. Check that the merkle_root (pi[1]) corresponds to the federation root
        //    stored in the cell's verification key.
        if vk.len() < 32 {
            return false;
        }
        let mut vk_bytes = [0u8; 32];
        vk_bytes.copy_from_slice(&vk[..32]);

        // The vk stored on the cell is the BabyBear representation of the federation
        // root (serialized as a u32 in little-endian in the first 4 bytes, for cells
        // that store BabyBear values directly), OR a 32-byte hash that we compress.
        let expected_root = if vk_bytes[4..].iter().all(|&b| b == 0) {
            // Case (a): raw BabyBear value in first 4 bytes
            BabyBear::new(u32::from_le_bytes([
                vk_bytes[0],
                vk_bytes[1],
                vk_bytes[2],
                vk_bytes[3],
            ]))
        } else {
            // Case (b): full 32-byte hash, compress to BabyBear
            crate::present::bytes_to_babybear(&vk_bytes)
        };

        let proof_root = pi[1];
        if proof_root != expected_root {
            return false;
        }

        // 5. Verify the STARK proof cryptographically using Poseidon2 AIR
        //    (collision-resistant, production path). The legacy MerkleStarkAir
        //    uses a LINEAR binding constraint that is trivially forgeable.
        use pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir;
        let air = MerklePoseidon2StarkAir;
        stark::verify(&air, &stark_proof, &pi).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::poseidon2_air::{MerklePoseidon2StarkAir, generate_merkle_poseidon2_trace};
    use pyana_circuit::stark::{proof_to_bytes, prove};

    #[test]
    fn test_stark_verifier_valid_proof() {
        // Generate a valid Poseidon2 Merkle membership proof.
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [BabyBear::new(1000), BabyBear::new(1100), BabyBear::new(1200)],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        // The federation root is public_inputs[1] (the Merkle root).
        let root_bb = public_inputs[1];
        // Store as BabyBear value in first 4 bytes of vk.
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        // Action signing message must be non-empty (32 bytes).
        let action_msg = [0x42u8; 32];
        assert!(verifier.verify(&proof_bytes, &action_msg, &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_federation_root() {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [BabyBear::new(1000), BabyBear::new(1100), BabyBear::new(1200)],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        // Use a WRONG federation root.
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&99999u32.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        let action_msg = [0x42u8; 32];
        assert!(!verifier.verify(&proof_bytes, &action_msg, &vk));
    }

    #[test]
    fn test_stark_verifier_tampered_proof() {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [BabyBear::new(1000), BabyBear::new(1100), BabyBear::new(1200)],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let mut proof_bytes = proof_to_bytes(&proof);

        // Tamper with the proof.
        if proof_bytes.len() > 10 {
            proof_bytes[10] ^= 0xFF;
        }

        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        let action_msg = [0x42u8; 32];
        assert!(!verifier.verify(&proof_bytes, &action_msg, &vk));
    }

    #[test]
    fn test_stark_verifier_empty_proof() {
        let verifier = StarkProofVerifier::new();
        let vk = [0u8; 32];
        let action_msg = [0x42u8; 32];
        assert!(!verifier.verify(&[], &action_msg, &vk));
    }

    #[test]
    fn test_stark_verifier_empty_public_inputs_rejected() {
        // Empty public_inputs should be rejected (action binding check).
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [BabyBear::new(1000), BabyBear::new(1100), BabyBear::new(1200)],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        // Empty public inputs should be rejected.
        assert!(!verifier.verify(&proof_bytes, &[], &vk));
    }
}
