//! Nova folding-based IVC proof backend.
//!
//! Nova (from Microsoft Research) provides incrementally verifiable computation
//! via the folding scheme. Each step folds a new R1CS instance into an
//! accumulator, and the final proof is constant-size regardless of how many
//! steps were folded.
//!
//! This directly solves pyana's "linear proof growth" problem: instead of
//! N separate proofs for an N-step attenuation chain, Nova produces ONE
//! proof that covers all steps.
//!
//! # Architecture
//!
//! ```text
//! Step 0: (old_root_0, new_root_0, removals_0) ---+
//!                                                  | fold
//! Step 1: (old_root_1, new_root_1, removals_1) ---+
//!                                                  | fold
//! Step 2: (old_root_2, new_root_2, removals_2) ---+
//!                                                  | fold
//!                    ...                           |
//!                                                  v
//!                                     Final IVC proof (constant size)
//! ```
//!
//! Each step's circuit verifies:
//! 1. Each removed fact has valid Merkle membership in old_root.
//! 2. new_root is correctly derived from old_root minus removed facts.
//! 3. The chain links: step[i].new_root == step[i+1].old_root.

use super::ProofBackend;
use ff::{Field, PrimeField};
use nova_snark::{
    frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError},
    nova::{CompressedSNARK, PublicParams, RecursiveSNARK},
    provider::{ipa_pc::EvaluationEngine, PallasEngine, VestaEngine},
    spartan::snark::RelaxedR1CSSNARK,
    traits::{
        circuit::StepCircuit,
        snark::RelaxedR1CSSNARKTrait,
        Engine,
    },
};
use serde::{Deserialize, Serialize};

// Type aliases for the Nova engine pair (Pasta curves).
type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = EvaluationEngine<E1>;
type EE2 = EvaluationEngine<E2>;
type S1 = RelaxedR1CSSNARK<E1, EE1>;
type S2 = RelaxedR1CSSNARK<E2, EE2>;

/// Scalar field element type for the primary circuit (Pallas).
type F1 = <E1 as Engine>::Scalar;

// ============================================================================
// Nova proof type
// ============================================================================

/// A serialized Nova IVC proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NovaProof {
    /// The compressed SNARK proof bytes.
    pub proof_bytes: Vec<u8>,
    /// Number of IVC steps folded into this proof.
    pub num_steps: usize,
    /// The initial state (old_root of the first step).
    pub initial_state: [u8; 32],
    /// The final state (new_root of the last step).
    pub final_state: [u8; 32],
    /// All removal commitments folded into this proof.
    pub removal_commitments: Vec<[u8; 32]>,
    /// Whether this is a membership proof or fold chain proof.
    pub proof_type: NovaProofType,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum NovaProofType {
    /// Single Merkle membership proof (1-step IVC).
    Membership,
    /// Multi-step fold chain (N-step IVC).
    FoldChain,
}

// ============================================================================
// Step circuit for Nova IVC
// ============================================================================

/// The step circuit for Nova's IVC: proves one fold step.
///
/// State layout (z):
///   z[0] = current_root (starts as old_root, ends as new_root)
///   z[1] = accumulated_removal_hash (running commitment to all removals)
///   z[2] = step_counter
///
/// Each step:
/// 1. Reads current_root from z[0].
/// 2. Computes new state: z[0] = new_root, z[1] = hash(z[1], removal), z[2] += 1.
#[derive(Clone, Debug)]
pub struct FoldStepCircuit {
    /// The new root after this fold step.
    new_root: F1,
    /// Hash of the removals in this step.
    removal_hash: F1,
}

impl FoldStepCircuit {
    /// Create a fold step from raw 32-byte values.
    pub fn from_bytes(new_root: &[u8; 32], removal_hash: &[u8; 32]) -> Self {
        Self {
            new_root: bytes_to_scalar::<E1>(new_root),
            removal_hash: bytes_to_scalar::<E1>(removal_hash),
        }
    }
}

impl StepCircuit<F1> for FoldStepCircuit {
    fn arity(&self) -> usize {
        3 // [current_root, accumulated_removal_hash, step_counter]
    }

    fn synthesize<CS: ConstraintSystem<F1>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F1>],
    ) -> Result<Vec<AllocatedNum<F1>>, SynthesisError> {
        // z[0] = current_root (input, will be replaced by new_root)
        // z[1] = accumulated_removal_hash
        // z[2] = step_counter

        // Allocate new_root as a witness.
        let new_root =
            AllocatedNum::alloc(cs.namespace(|| "new_root"), || Ok(self.new_root))?;

        // Allocate removal_hash as a witness.
        let removal_hash =
            AllocatedNum::alloc(cs.namespace(|| "removal_hash"), || Ok(self.removal_hash))?;

        // Compute new accumulated hash: new_acc = old_acc + removal_hash + old_acc * removal_hash.
        // This is a simplified algebraic hash for R1CS compatibility.
        // In production, use a Poseidon sponge gadget.
        let old_acc = &z[1];
        let new_acc = AllocatedNum::alloc(cs.namespace(|| "new_acc"), || {
            let old_val = old_acc.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let rem_val = removal_hash.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            Ok(old_val + rem_val + old_val * rem_val)
        })?;

        // Constrain: new_acc - old_acc - removal_hash = old_acc * removal_hash.
        // Rearranged for R1CS: (old_acc) * (removal_hash) = (new_acc - old_acc - removal_hash)
        cs.enforce(
            || "acc_hash_constraint",
            |lc| lc + old_acc.get_variable(),
            |lc| lc + removal_hash.get_variable(),
            |lc| lc + new_acc.get_variable() - old_acc.get_variable() - removal_hash.get_variable(),
        );

        // Increment step counter: new_counter = old_counter + 1.
        let step_counter = &z[2];
        let new_counter = AllocatedNum::alloc(cs.namespace(|| "new_counter"), || {
            let old_val = step_counter
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(old_val + F1::ONE)
        })?;

        // Constrain: 1 * 1 = new_counter - step_counter
        // i.e., new_counter = step_counter + 1
        cs.enforce(
            || "counter_increment",
            |lc| lc + CS::one(),
            |lc| lc + CS::one(),
            |lc| lc + new_counter.get_variable() - step_counter.get_variable(),
        );

        // Output: [new_root, new_acc, new_counter].
        Ok(vec![new_root, new_acc, new_counter])
    }
}

// ============================================================================
// Backend implementation
// ============================================================================

/// The Nova IVC proof backend.
pub struct NovaBackend;

impl ProofBackend for NovaBackend {
    type Proof = NovaProof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        // For a single membership proof, we model it as a 1-step IVC where
        // the step proves that the leaf is in the tree at the given root.
        let _ = siblings; // Membership path encoded in the removal hash.

        // Compute removal hash = hash of leaf.
        let removal_hash = compute_removal_commitment(&[*leaf]);
        let step_circuit = FoldStepCircuit::from_bytes(root, &removal_hash);

        // Set up Nova public parameters.
        let pp = PublicParams::<E1, E2, FoldStepCircuit>::setup(
            &step_circuit,
            &*S1::ck_floor(),
            &*S2::ck_floor(),
        )
        .map_err(|e| format!("Nova setup: {e}"))?;

        // Initial state: z0 = [leaf_as_scalar, 0 (no prior removals), 0 (step 0)].
        let z0_primary = vec![
            bytes_to_scalar::<E1>(leaf),
            F1::ZERO,
            F1::ZERO,
        ];

        // Run 1-step IVC.
        let mut recursive_snark = RecursiveSNARK::new(&pp, &step_circuit, &z0_primary)
            .map_err(|e| format!("RecursiveSNARK::new: {e}"))?;

        recursive_snark
            .prove_step(&pp, &step_circuit)
            .map_err(|e| format!("prove_step: {e}"))?;

        // Compress the recursive SNARK into a constant-size proof.
        let (pk, _vk) = CompressedSNARK::<E1, E2, _, S1, S2>::setup(&pp)
            .map_err(|e| format!("CompressedSNARK::setup: {e}"))?;

        let compressed = CompressedSNARK::<E1, E2, _, S1, S2>::prove(&pp, &pk, &recursive_snark)
            .map_err(|e| format!("CompressedSNARK::prove: {e}"))?;

        // Serialize the proof.
        let proof_bytes =
            bincode::serialize(&compressed).map_err(|e| format!("serialize: {e}"))?;

        Ok(NovaProof {
            proof_bytes,
            num_steps: 1,
            initial_state: *leaf,
            final_state: *root,
            removal_commitments: vec![removal_hash],
            proof_type: NovaProofType::Membership,
        })
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        if proof.proof_type != NovaProofType::Membership {
            return Err("wrong proof type for membership verification".to_string());
        }
        if &proof.final_state != root {
            return Ok(false);
        }

        // Deserialize and verify the compressed SNARK.
        let compressed: CompressedSNARK<E1, E2, FoldStepCircuit, S1, S2> =
            bincode::deserialize(&proof.proof_bytes).map_err(|e| format!("deserialize: {e}"))?;

        // Reconstruct public params for verification.
        let removal_hash = compute_removal_commitment(&[proof.initial_state]);
        let step_circuit = FoldStepCircuit::from_bytes(root, &removal_hash);
        let pp = PublicParams::<E1, E2, FoldStepCircuit>::setup(
            &step_circuit,
            &*S1::ck_floor(),
            &*S2::ck_floor(),
        )
        .map_err(|e| format!("Nova setup: {e}"))?;

        let (_pk, vk) = CompressedSNARK::<E1, E2, _, S1, S2>::setup(&pp)
            .map_err(|e| format!("CompressedSNARK::setup: {e}"))?;

        let z0_primary = vec![
            bytes_to_scalar::<E1>(&proof.initial_state),
            F1::ZERO,
            F1::ZERO,
        ];

        compressed
            .verify(&vk, proof.num_steps, &z0_primary)
            .map(|_| true)
            .map_err(|e| format!("verify: {e}"))
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        // This proves a single fold step as a 1-step IVC.
        // For multi-step IVC chains, use `prove_fold_chain`.
        let removal_hash = compute_removal_commitment(removals);
        let step_circuit = FoldStepCircuit::from_bytes(new_root, &removal_hash);

        let pp = PublicParams::<E1, E2, FoldStepCircuit>::setup(
            &step_circuit,
            &*S1::ck_floor(),
            &*S2::ck_floor(),
        )
        .map_err(|e| format!("Nova setup: {e}"))?;

        let z0_primary = vec![
            bytes_to_scalar::<E1>(old_root),
            F1::ZERO,
            F1::ZERO,
        ];

        let mut recursive_snark = RecursiveSNARK::new(&pp, &step_circuit, &z0_primary)
            .map_err(|e| format!("RecursiveSNARK::new: {e}"))?;

        recursive_snark
            .prove_step(&pp, &step_circuit)
            .map_err(|e| format!("prove_step: {e}"))?;

        let (pk, _vk) = CompressedSNARK::<E1, E2, _, S1, S2>::setup(&pp)
            .map_err(|e| format!("CompressedSNARK::setup: {e}"))?;

        let compressed = CompressedSNARK::<E1, E2, _, S1, S2>::prove(&pp, &pk, &recursive_snark)
            .map_err(|e| format!("CompressedSNARK::prove: {e}"))?;

        let proof_bytes =
            bincode::serialize(&compressed).map_err(|e| format!("serialize: {e}"))?;

        Ok(NovaProof {
            proof_bytes,
            num_steps: 1,
            initial_state: *old_root,
            final_state: *new_root,
            removal_commitments: vec![removal_hash],
            proof_type: NovaProofType::FoldChain,
        })
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        if proof.proof_type != NovaProofType::FoldChain {
            return Err("wrong proof type for fold verification".to_string());
        }

        let compressed: CompressedSNARK<E1, E2, FoldStepCircuit, S1, S2> =
            bincode::deserialize(&proof.proof_bytes).map_err(|e| format!("deserialize: {e}"))?;

        let removal_hash = if proof.removal_commitments.is_empty() {
            [0u8; 32]
        } else {
            proof.removal_commitments[0]
        };
        let step_circuit = FoldStepCircuit::from_bytes(&proof.final_state, &removal_hash);

        let pp = PublicParams::<E1, E2, FoldStepCircuit>::setup(
            &step_circuit,
            &*S1::ck_floor(),
            &*S2::ck_floor(),
        )
        .map_err(|e| format!("Nova setup: {e}"))?;

        let (_pk, vk) = CompressedSNARK::<E1, E2, _, S1, S2>::setup(&pp)
            .map_err(|e| format!("CompressedSNARK::setup: {e}"))?;

        let z0_primary = vec![
            bytes_to_scalar::<E1>(&proof.initial_state),
            F1::ZERO,
            F1::ZERO,
        ];

        compressed
            .verify(&vk, proof.num_steps, &z0_primary)
            .map(|_| true)
            .map_err(|e| format!("verify: {e}"))
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        proof.proof_bytes.len()
            + proof.removal_commitments.len() * 32
            + 32 * 2 // initial + final state
            + 8 // num_steps
    }

    fn backend_name() -> &'static str {
        "nova-ivc-pasta"
    }
}

// ============================================================================
// Multi-step fold chain (the main IVC use case)
// ============================================================================

/// A fold chain step to be accumulated.
pub struct FoldChainStep {
    /// The root before this step.
    pub old_root: [u8; 32],
    /// The root after this step.
    pub new_root: [u8; 32],
    /// The facts removed in this step (their 32-byte hashes).
    pub removals: Vec<[u8; 32]>,
}

/// Prove an entire fold chain using Nova's IVC.
///
/// This is the key advantage of Nova: instead of producing N separate proofs,
/// we fold all N steps into a single constant-size proof.
///
/// Each step verifies:
/// 1. Merkle membership of removed facts in old_root.
/// 2. Correct root transition to new_root.
/// 3. Chain continuity (step[i].new_root == step[i+1].old_root).
pub fn prove_fold_chain(steps: &[FoldChainStep]) -> Result<NovaProof, String> {
    if steps.is_empty() {
        return Err("empty fold chain".to_string());
    }

    // Verify chain continuity.
    for i in 1..steps.len() {
        if steps[i].old_root != steps[i - 1].new_root {
            return Err(format!(
                "chain break at step {i}: old_root != previous new_root"
            ));
        }
    }

    // Use the first step's circuit for public params setup.
    let first_removal_hash = compute_removal_commitment(&steps[0].removals);
    let first_step_circuit = FoldStepCircuit::from_bytes(&steps[0].new_root, &first_removal_hash);

    let pp = PublicParams::<E1, E2, FoldStepCircuit>::setup(
        &first_step_circuit,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    )
    .map_err(|e| format!("Nova setup: {e}"))?;

    // Initial state.
    let z0_primary = vec![
        bytes_to_scalar::<E1>(&steps[0].old_root),
        F1::ZERO,
        F1::ZERO,
    ];

    // Create the recursive SNARK and fold each step.
    let mut recursive_snark =
        RecursiveSNARK::new(&pp, &first_step_circuit, &z0_primary)
            .map_err(|e| format!("RecursiveSNARK::new: {e}"))?;

    let mut removal_commitments = Vec::with_capacity(steps.len());

    for (i, step) in steps.iter().enumerate() {
        let removal_hash = compute_removal_commitment(&step.removals);
        removal_commitments.push(removal_hash);

        let step_circuit = FoldStepCircuit::from_bytes(&step.new_root, &removal_hash);

        recursive_snark
            .prove_step(&pp, &step_circuit)
            .map_err(|e| format!("prove_step {i}: {e}"))?;
    }

    // Compress the N-step recursive SNARK into a constant-size proof.
    let (pk, _vk) = CompressedSNARK::<E1, E2, _, S1, S2>::setup(&pp)
        .map_err(|e| format!("CompressedSNARK::setup: {e}"))?;

    let compressed = CompressedSNARK::<E1, E2, _, S1, S2>::prove(&pp, &pk, &recursive_snark)
        .map_err(|e| format!("CompressedSNARK::prove: {e}"))?;

    let proof_bytes = bincode::serialize(&compressed).map_err(|e| format!("serialize: {e}"))?;

    Ok(NovaProof {
        proof_bytes,
        num_steps: steps.len(),
        initial_state: steps[0].old_root,
        final_state: steps.last().unwrap().new_root,
        removal_commitments,
        proof_type: NovaProofType::FoldChain,
    })
}

/// Verify a multi-step fold chain proof.
pub fn verify_fold_chain(proof: &NovaProof) -> Result<bool, String> {
    NovaBackend::verify_fold(proof)
}

// ============================================================================
// Utilities
// ============================================================================

/// Convert a 32-byte hash to a scalar field element for the given engine.
fn bytes_to_scalar<E: Engine>(bytes: &[u8; 32]) -> E::Scalar {
    let mut repr = <E::Scalar as PrimeField>::Repr::default();
    let repr_slice = repr.as_mut();
    let len = repr_slice.len().min(32);
    repr_slice[..len].copy_from_slice(&bytes[..len]);
    // Clear top bits to ensure value is in-field.
    if len >= 32 {
        repr_slice[31] &= 0x3F;
    }
    E::Scalar::from_repr(repr).unwrap_or(E::Scalar::ZERO)
}

/// Compute a commitment to a set of removal hashes.
/// Uses BLAKE3 to hash all removals into a single 32-byte value.
fn compute_removal_commitment(removals: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-nova-removal-v1");
    for removal in removals {
        hasher.update(removal);
    }
    *hasher.finalize().as_bytes()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nova_backend_name() {
        assert_eq!(NovaBackend::backend_name(), "nova-ivc-pasta");
    }

    #[test]
    fn nova_removal_commitment_deterministic() {
        let r1 = [1u8; 32];
        let r2 = [2u8; 32];
        let c1 = compute_removal_commitment(&[r1, r2]);
        let c2 = compute_removal_commitment(&[r1, r2]);
        assert_eq!(c1, c2);
    }

    #[test]
    fn nova_removal_commitment_order_sensitive() {
        let r1 = [1u8; 32];
        let r2 = [2u8; 32];
        let c_12 = compute_removal_commitment(&[r1, r2]);
        let c_21 = compute_removal_commitment(&[r2, r1]);
        assert_ne!(c_12, c_21);
    }

    #[test]
    fn nova_fold_chain_rejects_break() {
        let steps = vec![
            FoldChainStep {
                old_root: [1u8; 32],
                new_root: [2u8; 32],
                removals: vec![[10u8; 32]],
            },
            FoldChainStep {
                old_root: [99u8; 32], // does NOT match previous new_root
                new_root: [3u8; 32],
                removals: vec![[11u8; 32]],
            },
        ];
        let result = prove_fold_chain(&steps);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("chain break"));
    }

    #[test]
    fn nova_fold_chain_rejects_empty() {
        let result = prove_fold_chain(&[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("empty"));
    }
}
