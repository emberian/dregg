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
use pyana_circuit::binding::compute_action_binding;
use pyana_circuit::stark;
use pyana_turn::ProofVerifier;

/// A `ProofVerifier` implementation that verifies real STARK proofs from the
/// pyana-circuit layer.
///
/// The verifier checks that:
/// 1. The proof bytes deserialize to a valid `StarkProof`.
/// 2. The proof's public inputs include the expected federation root (passed as `vk`).
/// 3. The action binding matches the requested action and resource.
/// 4. The STARK proof verifies against the Poseidon2 `MerklePoseidon2StarkAir` constraint system.
///
/// # Timestamp Freshness
///
/// When `max_proof_age_secs` is set (non-zero), the verifier also checks that the
/// proof's timestamp (if present as the 4th public input) is within the allowed window.
/// The current time is obtained from `std::time::SystemTime::now()`.
///
/// # Usage
///
/// ```ignore
/// let verifier = StarkProofVerifier::with_max_age(300); // 5 minutes
/// let mut executor = TurnExecutor::new(costs);
/// executor.set_proof_verifier(Box::new(verifier));
/// ```
pub struct StarkProofVerifier {
    /// Maximum age of a proof in seconds. 0 means no freshness check.
    max_proof_age_secs: i64,
}

impl StarkProofVerifier {
    /// Create a new STARK proof verifier with no timestamp freshness check.
    pub fn new() -> Self {
        Self {
            max_proof_age_secs: 0,
        }
    }

    /// Create a new STARK proof verifier with timestamp freshness enforcement.
    ///
    /// Proofs with a timestamp older than `max_age_secs` from the current time
    /// will be rejected. Use `DEFAULT_MAX_PROOF_AGE_SECS` (300s) for typical use.
    pub fn with_max_age(max_age_secs: i64) -> Self {
        Self {
            max_proof_age_secs: max_age_secs,
        }
    }
}

impl Default for StarkProofVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofVerifier for StarkProofVerifier {
    /// Verify a STARK proof bound to (action, resource) against a verification key.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool {
        // 1. Deserialize the STARK proof.
        let stark_proof = match stark::proof_from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // 2. Extract the public inputs from the proof itself.
        // SECURITY: Use new_canonical() for values from external (potentially adversarial)
        // proof data to prevent non-canonical BabyBear representations.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Expect at least [leaf_hash, merkle_root, action_binding]
        if pi.len() < 3 {
            return false;
        }

        // 3. Verify the action binding commitment.
        let expected_binding = compute_action_binding(action, resource);
        let proof_binding = pi.last().copied().unwrap_or(BabyBear::ZERO);
        if proof_binding != expected_binding {
            return false;
        }

        // 4. Check that the merkle_root (pi[1]) corresponds to the federation root
        //    stored in the cell's verification key.
        if vk.len() < 32 {
            return false;
        }
        let mut vk_bytes = [0u8; 32];
        vk_bytes.copy_from_slice(&vk[..32]);

        let expected_root = if vk_bytes[4..].iter().all(|&b| b == 0) {
            BabyBear::new_canonical(u32::from_le_bytes([
                vk_bytes[0],
                vk_bytes[1],
                vk_bytes[2],
                vk_bytes[3],
            ]))
        } else {
            crate::present::bytes_to_babybear(&vk_bytes)
        };

        let proof_root = pi[1];
        if proof_root != expected_root {
            return false;
        }

        // 5. Timestamp freshness check (if configured).
        // The timestamp is the 4th public input (index 3) when present.
        if self.max_proof_age_secs > 0 && pi.len() >= 4 {
            let proof_timestamp = pi[3].0 as i64;
            if proof_timestamp == 0 {
                // No timestamp in proof — reject when freshness is required.
                return false;
            }
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let age = now.saturating_sub(proof_timestamp);
            if age > self.max_proof_age_secs || age < -self.max_proof_age_secs {
                return false;
            }
        }

        // 6. Verify the STARK proof cryptographically using Poseidon2 AIR.
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
    use pyana_circuit::binding::compute_action_binding;

    /// Helper: generate a valid proof with action binding (3 public inputs).
    /// Uses the canonical `compute_action_binding` to produce the binding commitment.
    fn generate_bound_proof(action: &str, resource: &str) -> (Vec<u8>, Vec<BabyBear>) {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [BabyBear::new(1000), BabyBear::new(1100), BabyBear::new(1200)],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, mut public_inputs) =
            generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        // Append the canonical action binding as third public input.
        let binding = compute_action_binding(action, resource);
        public_inputs.push(binding);

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);
        (proof_bytes, public_inputs)
    }

    #[test]
    fn test_stark_verifier_valid_proof() {
        let (proof_bytes, public_inputs) = generate_bound_proof("read", "api/v1/users");

        // The federation root is public_inputs[1] (the Merkle root).
        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_federation_root() {
        let (proof_bytes, _public_inputs) = generate_bound_proof("read", "api/v1/users");

        // Use a WRONG federation root.
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&99999u32.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_tampered_proof() {
        let (mut proof_bytes, public_inputs) = generate_bound_proof("read", "api/v1/users");

        // Tamper with the proof.
        if proof_bytes.len() > 10 {
            proof_bytes[10] ^= 0xFF;
        }

        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_empty_proof() {
        let verifier = StarkProofVerifier::new();
        let vk = [0u8; 32];
        assert!(!verifier.verify(&[], "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_action_rejected() {
        // A proof bound to (read, api/v1/users) should be rejected for (write, api/v1/users).
        let (proof_bytes, public_inputs) = generate_bound_proof("read", "api/v1/users");

        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "write", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_resource_rejected() {
        // A proof bound to (read, api/v1/users) should be rejected for (read, api/v1/posts).
        let (proof_bytes, public_inputs) = generate_bound_proof("read", "api/v1/users");

        let root_bb = public_inputs[1];
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/posts", &vk));
    }
}
