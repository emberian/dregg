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

use std::sync::Arc;

use pyana_circuit::BabyBear;
use pyana_circuit::binding::compute_action_binding;
use pyana_circuit::stark;
use pyana_dsl_runtime::ProgramRegistry;
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
/// When `max_proof_age_secs` is set (non-zero), the verifier REQUIRES that the
/// proof's 4th public input contains a valid timestamp within the allowed window.
/// Proofs without a timestamp field (fewer than 4 public inputs) are rejected.
/// This prevents a prover from stripping the timestamp to bypass freshness checks.
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
    /// Proofs MUST include a timestamp as the 4th public input (index 3).
    /// Proofs without a timestamp field are rejected. Proofs with a timestamp
    /// older than `max_age_secs` from the current time are also rejected.
    /// Use `DEFAULT_MAX_PROOF_AGE_SECS` (300s) for typical use.
    ///
    /// **NOTE**: The standard `BridgePresentationBuilder::prove()` path does not
    /// include a timestamp in the issuer membership STARK proof's public inputs
    /// (the timestamp is only in the circuit-level `PresentationPublicInputs`).
    /// Provers targeting verifiers with `with_max_age` must explicitly append a
    /// Unix timestamp as pi[3] when generating the STARK proof.
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

        // Expect at least [leaf_hash, merkle_root, action_binding[0..4]]
        if pi.len() < 2 + pyana_circuit::ACTION_BINDING_WIDTH {
            return false;
        }

        // 3. Verify the action binding commitment (4 elements, 124-bit security).
        // The action binding occupies pi[2..6] (after leaf_hash and merkle_root).
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
            if pi[2 + i] != expected_binding[i] {
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

        // The VK encodes a BabyBear field element as its canonical u32 representation
        // in the first 4 bytes (little-endian). This matches the prover's encoding
        // (via `bb_to_bytes` / `babybear_to_bytes32`) used in BridgePresentationBuilder
        // and the SDK. Bytes 4-31 are reserved and ignored.
        //
        // NOTE: `bytes_to_babybear` (Poseidon2 hash of 8 limbs) is NOT used here because
        // it is a one-way compression function that cannot round-trip with the canonical
        // BabyBear-to-bytes encoding. The prover stores `root.0.to_le_bytes()` in bytes
        // 0-3, and the verifier must recover it with the inverse operation.
        let expected_root = BabyBear::new_canonical(u32::from_le_bytes([
            vk_bytes[0],
            vk_bytes[1],
            vk_bytes[2],
            vk_bytes[3],
        ]));

        let proof_root = pi[1];
        if proof_root != expected_root {
            return false;
        }

        // 5. Timestamp freshness check (if configured).
        // The timestamp is after the 4-element action binding: pi[6] (index 2+4=6).
        // SECURITY: When freshness is required (max_proof_age_secs > 0), the proof
        // MUST include a timestamp. Rejecting proofs without timestamps prevents a
        // prover from stripping the timestamp to bypass freshness enforcement.
        let timestamp_idx = 2 + pyana_circuit::ACTION_BINDING_WIDTH; // = 6
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                // Timestamp required but proof does not include one — reject.
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
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

/// Known AIR names that are handled by the existing hardcoded verification path.
///
/// If a proof's `air_name` matches one of these, the `DslAwareProofVerifier` delegates
/// to the standard `MerklePoseidon2StarkAir` (or `BlindedMerklePoseidon2StarkAir`) path.
/// Otherwise, the proof is treated as a custom program proof and dispatched to the
/// `ProgramRegistry` for DSL circuit verification.
const KNOWN_AIR_NAMES: &[&str] = &[
    "pyana-merkle-poseidon2-v1",
    "pyana-blinded-merkle-poseidon2-v1",
    "pyana-poseidon2-v1",
    "pyana-merkle-poseidon2-round-v1",
];

/// A `ProofVerifier` that supports both hardcoded AIRs and DSL-generated circuits.
///
/// This is the production verifier for sovereign cell proofs. It dispatches:
///
/// - **Known AIR names** (poseidon2, merkle, blinded-merkle): verified via the
///   existing `MerklePoseidon2StarkAir` / `BlindedMerklePoseidon2StarkAir` path,
///   including action binding and timestamp freshness checks.
///
/// - **Custom programs** (unrecognized `air_name`): the VK bytes are interpreted
///   as a 32-byte program VK hash. The program is looked up in the attached
///   `ProgramRegistry`, and the proof is verified against its `DslCircuit`.
///
/// # Usage
///
/// ```ignore
/// let registry = Arc::new(ProgramRegistry::new());
/// // ... deploy programs to registry ...
/// let verifier = DslAwareProofVerifier::new(registry);
/// executor.set_proof_verifier(Box::new(verifier));
/// ```
pub struct DslAwareProofVerifier {
    /// Maximum age of a proof in seconds. 0 means no freshness check.
    /// Applies only to the known-AIR path.
    max_proof_age_secs: i64,
    /// Program registry for custom DSL circuit verification.
    registry: Arc<ProgramRegistry>,
}

impl DslAwareProofVerifier {
    /// Create a new DSL-aware verifier with no timestamp freshness check.
    pub fn new(registry: Arc<ProgramRegistry>) -> Self {
        Self {
            max_proof_age_secs: 0,
            registry,
        }
    }

    /// Create a new DSL-aware verifier with timestamp freshness enforcement
    /// for the known-AIR path.
    pub fn with_max_age(registry: Arc<ProgramRegistry>, max_age_secs: i64) -> Self {
        Self {
            max_proof_age_secs: max_age_secs,
            registry,
        }
    }

    /// Verify a proof using the known Merkle/Poseidon2 AIR path.
    ///
    /// This is equivalent to `StarkProofVerifier::verify` and handles proofs
    /// generated by the standard presentation builder (issuer membership).
    fn verify_known_air(
        &self,
        stark_proof: &stark::StarkProof,
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        // Extract public inputs with canonical reduction.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Expect at least [leaf_hash, merkle_root, action_binding[0..4]]
        if pi.len() < 2 + pyana_circuit::ACTION_BINDING_WIDTH {
            return false;
        }

        // Verify the action binding commitment.
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
            if pi[2 + i] != expected_binding[i] {
                return false;
            }
        }

        // Check that the merkle_root (pi[1]) corresponds to the federation root (vk).
        if vk.len() < 32 {
            return false;
        }
        let expected_root =
            BabyBear::new_canonical(u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]]));
        if pi[1] != expected_root {
            return false;
        }

        // Timestamp freshness check (if configured).
        let timestamp_idx = 2 + pyana_circuit::ACTION_BINDING_WIDTH;
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
            if proof_timestamp == 0 {
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

        // Dispatch to the correct AIR based on air_name.
        use pyana_circuit::poseidon2_air::{
            BlindedMerklePoseidon2StarkAir, MerklePoseidon2StarkAir,
        };
        use pyana_circuit::stark::StarkAir;
        if stark_proof.air_name == BlindedMerklePoseidon2StarkAir.air_name() {
            stark::verify(&BlindedMerklePoseidon2StarkAir, stark_proof, &pi).is_ok()
        } else {
            stark::verify(&MerklePoseidon2StarkAir, stark_proof, &pi).is_ok()
        }
    }

    /// Verify a proof using the DSL circuit path via `ProgramRegistry`.
    ///
    /// The VK bytes are interpreted as the 32-byte program VK hash. The program
    /// is looked up in the registry, and the proof is verified against its
    /// `DslCircuit` AIR.
    ///
    /// # Action Binding Convention for DSL Programs
    ///
    /// DSL programs follow the same public input convention as known AIRs:
    /// the action binding (4 BabyBear elements) occupies `pi[0..4]`, and the
    /// optional timestamp occupies `pi[4]`. Programs that declare fewer than
    /// 5 public inputs cannot pass freshness checks when `max_proof_age_secs > 0`.
    ///
    /// This prevents a valid DSL proof from being replayed to authorize a
    /// different action on the same cell.
    fn verify_dsl_program(
        &self,
        stark_proof: &stark::StarkProof,
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        if vk.len() < 32 {
            return false;
        }

        let mut vk_hash = [0u8; 32];
        vk_hash.copy_from_slice(&vk[..32]);

        // Look up the program in the registry.
        let program = match self.registry.get(&vk_hash) {
            Some(p) => p,
            None => return false,
        };

        // Extract public inputs from the proof.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Action binding check: pi[0..4] must match the expected action binding.
        // This prevents replay of a valid proof to authorize a different action.
        if pi.len() < pyana_circuit::ACTION_BINDING_WIDTH {
            return false;
        }
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
            if pi[i] != expected_binding[i] {
                return false;
            }
        }

        // Timestamp freshness check (same logic as the known-AIR path).
        // For DSL programs, the timestamp lives at pi[ACTION_BINDING_WIDTH] (index 4).
        let timestamp_idx = pyana_circuit::ACTION_BINDING_WIDTH; // = 4
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                // Timestamp required but proof does not include one — reject.
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
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

        // Verify using the program's DslCircuit.
        let circuit = pyana_dsl_runtime::DslCircuit::new(program.descriptor.clone());
        stark::verify(&circuit, stark_proof, &pi).is_ok()
    }
}

impl ProofVerifier for DslAwareProofVerifier {
    /// Verify a STARK proof, dispatching to the known-AIR path or DSL circuit path.
    ///
    /// Dispatch logic:
    /// - If the proof's `air_name` matches a known AIR name (poseidon2, merkle, etc.),
    ///   verify using the hardcoded `MerklePoseidon2StarkAir` path with action binding
    ///   and freshness checks.
    /// - If the proof's `air_name` is unrecognized (custom VK), interpret the `vk` bytes
    ///   as a program VK hash and verify via the `ProgramRegistry` / `DslCircuit`.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool {
        // 1. Deserialize the STARK proof.
        let stark_proof = match stark::proof_from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // 2. Dispatch based on air_name.
        if KNOWN_AIR_NAMES.contains(&stark_proof.air_name.as_str()) {
            self.verify_known_air(&stark_proof, action, resource, vk)
        } else {
            self.verify_dsl_program(&stark_proof, action, resource, vk)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::binding::compute_action_binding;
    use pyana_circuit::poseidon2_air::{MerklePoseidon2StarkAir, generate_merkle_poseidon2_trace};
    use pyana_circuit::stark::{proof_to_bytes, prove};

    /// Encode a BabyBear value as a 32-byte verification key.
    ///
    /// The canonical VK encoding stores the BabyBear's u32 representation in the
    /// first 4 bytes (little-endian), with remaining bytes zeroed. This is the
    /// encoding used by the prover (BridgePresentationBuilder / SDK) and the
    /// verifier's `new_canonical(u32_from_first_4_bytes)` extraction.
    fn babybear_to_vk(bb: BabyBear) -> [u8; 32] {
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&bb.0.to_le_bytes());
        vk
    }

    /// Helper: generate a valid proof with action binding (3 public inputs: leaf, root, binding).
    /// Returns (proof_bytes, public_inputs, vk_bytes).
    fn generate_bound_proof(action: &str, resource: &str) -> (Vec<u8>, Vec<BabyBear>, [u8; 32]) {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [
                BabyBear::new(1000),
                BabyBear::new(1100),
                BabyBear::new(1200),
            ],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, mut public_inputs) =
            generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        // Append the canonical action binding as third public input.
        let binding = compute_action_binding(action, resource);
        for &elem in binding.iter() {
            public_inputs.push(elem);
        }

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        // Encode the Merkle root (pi[1]) as the VK using the canonical encoding.
        let vk = babybear_to_vk(public_inputs[1]);

        (proof_bytes, public_inputs, vk)
    }

    /// Helper: generate a valid proof with 4 public inputs (leaf, root, binding, timestamp).
    /// The timestamp is included as the 4th public input for freshness-checked verifiers.
    fn generate_bound_proof_with_timestamp(
        action: &str,
        resource: &str,
        timestamp: u32,
    ) -> (Vec<u8>, Vec<BabyBear>, [u8; 32]) {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [
                BabyBear::new(1000),
                BabyBear::new(1100),
                BabyBear::new(1200),
            ],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, mut public_inputs) =
            generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        // Append the canonical action binding as third public input.
        let binding = compute_action_binding(action, resource);
        for &elem in binding.iter() {
            public_inputs.push(elem);
        }

        // Append timestamp as 4th public input.
        public_inputs.push(BabyBear::new(timestamp));

        let air = MerklePoseidon2StarkAir;
        let proof = prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        let vk = babybear_to_vk(public_inputs[1]);

        (proof_bytes, public_inputs, vk)
    }

    #[test]
    fn test_stark_verifier_valid_proof() {
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_federation_root() {
        let (proof_bytes, _public_inputs, _vk) = generate_bound_proof("read", "api/v1/users");

        // Use a WRONG federation root.
        let wrong_vk = babybear_to_vk(BabyBear::new(99999));

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &wrong_vk));
    }

    #[test]
    fn test_stark_verifier_tampered_proof() {
        let (mut proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        // Tamper with the proof.
        if proof_bytes.len() > 10 {
            proof_bytes[10] ^= 0xFF;
        }

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
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "write", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_resource_rejected() {
        // A proof bound to (read, api/v1/users) should be rejected for (read, api/v1/posts).
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/posts", &vk));
    }

    // =========================================================================
    // Timestamp freshness enforcement tests (Fix 2)
    // =========================================================================

    #[test]
    fn test_stark_verifier_no_max_age_accepts_without_timestamp() {
        // A verifier with max_age=0 should accept proofs without a timestamp field.
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new(); // max_age = 0
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_missing_timestamp() {
        // SECURITY: A prover cannot strip the timestamp to bypass freshness enforcement.
        // When max_proof_age_secs > 0, proofs without a timestamp (pi.len() < 4) are rejected.
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::with_max_age(300); // 5 minutes
        // The proof has only 3 public inputs (no timestamp) — should be rejected.
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_accepts_fresh_timestamp() {
        // A proof with a recent timestamp should be accepted.
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;

        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", now);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_stale_timestamp() {
        // A proof with a timestamp older than max_age should be rejected.
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;

        // Proof timestamp is 600 seconds in the past (max_age is 300).
        let stale_timestamp = now.saturating_sub(600);
        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", stale_timestamp);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_zero_timestamp() {
        // A proof with timestamp=0 is treated as "no timestamp" and rejected.
        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", 0);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_vk_with_nonzero_trailing_bytes() {
        // Regression test: VK bytes 4-31 being non-zero should NOT affect the result.
        // This tests that the old content-dependent heuristic has been removed.
        let (proof_bytes, public_inputs, _vk) = generate_bound_proof("read", "api/v1/users");

        // Encode with non-zero bytes in positions 4-31.
        let root_bb = public_inputs[1];
        let mut vk_nonzero = [0xFFu8; 32];
        vk_nonzero[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        // Should still verify correctly — only first 4 bytes matter.
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk_nonzero));
    }
}
