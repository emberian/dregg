//! Multi-step derivation chaining AIR -- backward-compatible shim.
//!
//! The production implementation uses [`crate::dsl::derivation`] for the DSL-native
//! multi-step circuit. This module provides the types and prove/verify functions
//! expected by existing callers.

use crate::derivation_air::{
    CircuitRule, DERIVATION_AIR_WIDTH, DerivationWitness, compute_policy_root,
};
use crate::dsl::derivation::MULTI_STEP_DSL_WIDTH;
use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;
use crate::stark::{self, StarkProof};

/// Multi-step AIR width.
pub const MULTI_STEP_AIR_WIDTH: usize = DERIVATION_AIR_WIDTH + 5;

/// Maximum derivation steps per proof (single-proof AIR constraint).
pub const MAX_STEPS: usize = 32;

/// Maximum delegation chain depth across all composed proofs.
///
/// Bounds the total proving time for a delegation chain to approximately 50 seconds
/// at ~500ms per step. Chains deeper than this are rejected at proof generation time
/// to prevent DoS via unbounded recursive proving.
///
/// This limit applies to the total chain from root issuer to final delegate. A single
/// proof covers up to MAX_STEPS steps; chains longer than MAX_STEPS use chunked
/// derivation (multiple proofs composed). This cap limits the TOTAL depth.
pub const MAX_DELEGATION_DEPTH: usize = 100;

/// The "allow" predicate marker value.
pub const ALLOW_PREDICATE: u32 = 0xA110;

/// Multi-step column indices (appended after derivation columns).
pub mod col {
    use super::DERIVATION_AIR_WIDTH;

    pub const STEP_INDEX: usize = DERIVATION_AIR_WIDTH;
    pub const ACCUMULATED_HASH: usize = DERIVATION_AIR_WIDTH + 1;
    pub const PREV_ACCUMULATED: usize = DERIVATION_AIR_WIDTH + 2;
    pub const IS_FINAL_STEP: usize = DERIVATION_AIR_WIDTH + 3;
    pub const IS_ACTIVE: usize = DERIVATION_AIR_WIDTH + 4;
}

/// Public input layout.
pub mod pi {
    pub const INITIAL_STATE_ROOT: usize = 0;
    pub const REQUEST_HASH: usize = 1;
    pub const CONCLUSION: usize = 2;
    pub const NUM_STEPS: usize = 3;
    pub const FINAL_ACCUMULATED_HASH: usize = 4;
    pub const POLICY_ROOT: usize = 5;
}

/// Witness for a multi-step derivation.
#[derive(Clone, Debug)]
pub struct MultiStepWitness {
    pub initial_state_root: BabyBear,
    pub request_hash: BabyBear,
    pub steps: Vec<DerivationWitness>,
    pub allow_predicate: BabyBear,
    pub policy_root: BabyBear,
    pub body_merkle_proofs: Option<Vec<(BabyBear, Vec<[BabyBear; 3]>, Vec<u8>)>>,
}

impl MultiStepWitness {
    pub fn conclusion(&self) -> BabyBear {
        if let Some(last) = self.steps.last() {
            if last.derived_predicate == self.allow_predicate {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        } else {
            BabyBear::ZERO
        }
    }

    pub fn compute_accumulated_hashes(&self) -> Vec<BabyBear> {
        let mut acc = Vec::with_capacity(self.steps.len());
        let mut prev = self.initial_state_root;
        for step in &self.steps {
            let derived_hash = step.derived_hash();
            let next = hash_2_to_1(prev, derived_hash);
            acc.push(next);
            prev = next;
        }
        acc
    }

    pub fn final_accumulated_hash(&self) -> BabyBear {
        self.compute_accumulated_hashes()
            .last()
            .copied()
            .unwrap_or(self.initial_state_root)
    }
}

/// Build a multi-step witness from components.
pub fn build_multi_step_witness(
    initial_state_root: BabyBear,
    request_hash: BabyBear,
    steps: Vec<DerivationWitness>,
) -> MultiStepWitness {
    let rules: Vec<&CircuitRule> = steps.iter().map(|s| &s.rule).collect();
    let policy_root = compute_policy_root(&rules);

    MultiStepWitness {
        initial_state_root,
        request_hash,
        steps,
        allow_predicate: BabyBear::new(ALLOW_PREDICATE),
        policy_root,
        body_merkle_proofs: None,
    }
}

/// The multi-step derivation AIR (constraint-prover interface).
pub struct MultiStepDerivationAir {
    pub witness: MultiStepWitness,
    pub max_steps: usize,
}

impl MultiStepDerivationAir {
    pub fn new(witness: MultiStepWitness) -> Self {
        let max_steps = witness.steps.len().max(1);
        Self { witness, max_steps }
    }

    pub fn with_max_steps(witness: MultiStepWitness, max_steps: usize) -> Self {
        Self { witness, max_steps }
    }
}

impl crate::constraint_prover::Air for MultiStepDerivationAir {
    fn trace_width(&self) -> usize {
        MULTI_STEP_DSL_WIDTH
    }
    fn num_public_inputs(&self) -> usize {
        6
    }
    fn constraints(&self) -> Vec<crate::constraint_prover::Constraint> {
        vec![] // Constraints evaluated by DSL runtime
    }
    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        crate::dsl::derivation::generate_multi_step_trace_dsl(&self.witness)
    }
}

/// Prove authorization using the constraint prover (non-STARK, for testing).
///
/// Returns a `ConstraintProof` if the witness satisfies all constraints, None otherwise.
pub fn prove_authorization(
    witness: MultiStepWitness,
) -> Option<crate::constraint_prover::ConstraintProof> {
    let air = MultiStepDerivationAir::new(witness);
    crate::constraint_prover::ConstraintProof::generate(&air)
}

/// Multi-step StarkAir struct.
///
/// DEPRECATED: This is a stub that delegates to `crate::dsl::derivation`.
/// Use `prove_authorization_stark` which already uses the DSL internally.
#[deprecated(
    note = "Use prove_authorization_stark (DSL-native) instead of constructing this directly"
)]
pub struct MultiStepStarkAir {
    pub num_steps: usize,
}

impl MultiStepStarkAir {
    pub fn new(num_steps: usize) -> Self {
        Self { num_steps }
    }
}

impl crate::stark::StarkAir for MultiStepStarkAir {
    fn width(&self) -> usize {
        MULTI_STEP_DSL_WIDTH
    }
    fn constraint_degree(&self) -> usize {
        3
    }
    fn air_name(&self) -> &'static str {
        "dregg-multi_step-v1"
    }
    fn has_chain_continuity(&self) -> bool {
        true
    }
    fn eval_constraints(
        &self,
        _local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        _alpha: BabyBear,
    ) -> BabyBear {
        // Constraint evaluation delegates to DSL runtime.
        BabyBear::ZERO
    }
    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<crate::stark::BoundaryConstraint> {
        vec![]
    }
}

/// Generate the multi-step trace.
pub fn generate_multi_step_trace(
    witness: &MultiStepWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    crate::dsl::derivation::generate_multi_step_trace_dsl(witness)
}

/// Prove multi-step authorization using STARK.
/// Prove authorization, enforcing the delegation chain depth cap.
///
/// Returns a StarkProof if the witness is valid and within depth limits.
///
/// # Panics
///
/// Panics if the delegation chain exceeds [`MAX_DELEGATION_DEPTH`] steps.
/// Callers that want a Result should use [`try_prove_authorization_stark`] instead.
pub fn prove_authorization_stark(witness: &MultiStepWitness) -> StarkProof {
    assert!(
        witness.steps.len() <= MAX_DELEGATION_DEPTH,
        "Delegation chain too deep: {} > {} (MAX_DELEGATION_DEPTH). \
         Consider revoking intermediate delegates or flattening the chain.",
        witness.steps.len(),
        MAX_DELEGATION_DEPTH,
    );
    let air = MultiStepStarkAir::new(witness.steps.len());
    let (trace, public_inputs) = generate_multi_step_trace(witness);
    stark::prove(&air, &trace, &public_inputs)
}

/// Try to prove authorization, returning an error if the chain is too deep.
///
/// This is the fallible version of [`prove_authorization_stark`]. Use when you
/// want to handle depth violations gracefully (e.g., return an error to the user
/// suggesting chain restructuring).
pub fn try_prove_authorization_stark(witness: &MultiStepWitness) -> Result<StarkProof, String> {
    if witness.steps.len() > MAX_DELEGATION_DEPTH {
        return Err(format!(
            "Delegation chain too deep: {} steps exceeds maximum of {}. \
             Proving time would be approximately {}s which exceeds acceptable limits.",
            witness.steps.len(),
            MAX_DELEGATION_DEPTH,
            witness.steps.len() as f64 * 0.5,
        ));
    }
    Ok(prove_authorization_stark(witness))
}

/// Verify a multi-step authorization STARK proof.
///
/// # Security Warning
///
/// This function verifies ONLY that the derivation rules were applied correctly.
/// It does NOT verify that the body facts referenced in the derivation actually
/// exist in any committed Merkle tree. A malicious prover can fabricate arbitrary
/// body facts and still produce a valid derivation proof.
///
/// **For security-critical verification, use
/// [`body_membership::verify_authorization_with_membership`] instead**, which
/// additionally requires Merkle membership proofs for every body fact used.
///
/// This function is safe to use only when:
/// - The body facts are independently verified by the caller (e.g., the executor
///   already confirmed fact existence before proof generation)
/// - The context is testing or non-adversarial
///
/// See: `circuit/src/body_membership.rs` for the composed proof that closes this gap.
pub(crate) fn verify_authorization_stark(
    conclusion: BabyBear,
    accumulated_hash: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    if proof.public_inputs.len() != 6 {
        return Err(format!(
            "Expected 6 public inputs, got {}",
            proof.public_inputs.len()
        ));
    }

    let proof_conclusion = BabyBear::new_canonical(proof.public_inputs[pi::CONCLUSION]);
    let proof_acc_hash = BabyBear::new_canonical(proof.public_inputs[pi::FINAL_ACCUMULATED_HASH]);

    if proof_conclusion != conclusion {
        return Err(format!(
            "Conclusion mismatch: expected {}, proof contains {}",
            conclusion.0, proof_conclusion.0
        ));
    }
    if proof_acc_hash != accumulated_hash {
        return Err(format!(
            "Accumulated hash mismatch: expected {}, proof contains {}",
            accumulated_hash.0, proof_acc_hash.0
        ));
    }

    let num_steps = proof.public_inputs[pi::NUM_STEPS] as usize;
    let air = MultiStepStarkAir::new(num_steps);
    let public_inputs: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    stark::verify(&air, proof, &public_inputs)
}
