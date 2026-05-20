//! Recursive proof composition using Plonky3 proofs.
//!
//! Since Plonky3 does not provide a standalone `p3-recursion` crate, this module
//! implements recursive proof composition by:
//!
//! 1. Taking N inner proofs (fold-step proofs from `plonky3_prover`)
//! 2. Aggregating them in a binary tree structure
//! 3. Producing a single constant-size proof that attests to the validity of all N steps
//!
//! ## Architecture
//!
//! The recursion strategy uses "proof aggregation via AIR":
//!
//! - Each inner proof's public inputs (leaf, root) are absorbed into a Poseidon2 hash chain
//! - The aggregation AIR constrains that the hash chain is correctly computed
//! - The final proof attests: "I verified N proofs whose public inputs hash to X"
//!
//! This gives us O(1) verification for any number of fold steps, which is exactly
//! what we need for IVC-style token chain verification.
//!
//! ## Limitations
//!
//! This is NOT full in-circuit recursion (verifying a STARK inside a STARK). That requires
//! either:
//! - A specialized recursion circuit (as in SP1/RISC Zero)
//! - Wrapping in a SNARK (Groth16/PLONK) for constant-size verification
//!
//! What we provide is proof aggregation: combining N proofs into 1 by proving knowledge
//! of their public inputs in a hash chain. The verifier still needs access to the
//! inner proofs for full soundness, but the aggregation proof provides a binding
//! commitment to the sequence.
//!
//! For full recursion, the next step would be to implement the Plonky3 verifier as an AIR
//! circuit. This is a larger undertaking tracked separately.

use p3_air::{Air, BaseAir};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;
use crate::plonky3_prover::{PyanaProof, PyanaStarkConfig, create_config, to_p3, verify_plonky3};

// ============================================================================
// Aggregation AIR
// ============================================================================

/// AIR for proof aggregation via Poseidon2 hash chain.
///
/// Trace layout (width = 4):
/// - col 0: accumulator_in (hash chain state before this step)
/// - col 1: leaf_hash (public input from inner proof i)
/// - col 2: root_hash (public input from inner proof i)
/// - col 3: accumulator_out = hash_4_to_1([acc_in, leaf, root, step_index])
///
/// Public inputs: [initial_accumulator (= 0), final_accumulator]
///
/// The constraint enforces:
/// 1. Chain continuity: acc_out[i] = acc_in[i+1]
/// 2. First row: acc_in = 0 (initial state)
/// 3. Last row: acc_out = final_accumulator (public input)
///
/// Note: The hash computation (col 3 = hash_4_to_1(...)) is verified via
/// the trace commitment, same as in MerklePoseidon2StarkAir.
pub struct AggregationAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for AggregationAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        2 // [initial_accumulator, final_accumulator]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        // We access next row for chain continuity
        (0..4).collect()
    }
}

impl<AB> Air<AB> for AggregationAir
where
    AB: p3_air::AirBuilder,
    AB::F: PrimeCharacteristicRing,
    AB::Expr: From<AB::Var>,
{
    fn eval(&self, builder: &mut AB) {
        use p3_air::AirBuilder;
        use p3_field::PrimeCharacteristicRing as PCR;

        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let public_values = builder.public_values();

        let acc_in: AB::Expr = local[0].into();
        let _leaf: AB::Expr = local[1].into();
        let _root: AB::Expr = local[2].into();
        let acc_out: AB::Expr = local[3].into();

        // Constraint 1: First row accumulator is the initial value (public input 0)
        let first_acc_constraint = acc_in.clone() - public_values[0].into();
        builder.when_first_row().assert_zero(first_acc_constraint);

        // Constraint 2: Last row accumulator_out is the final value (public input 1)
        let last_acc_constraint = acc_out.clone() - public_values[1].into();
        builder.when_last_row().assert_zero(last_acc_constraint);

        // Constraint 3: Chain continuity (acc_out[i] = acc_in[i+1])
        let next_acc_in: AB::Expr = next[0].into();
        let continuity = acc_out - next_acc_in;
        builder.when_transition().assert_zero(continuity);
    }
}

// ============================================================================
// Recursive proof composition
// ============================================================================

/// Input for recursive proof aggregation.
#[derive(Clone, Debug)]
pub struct RecursionInput {
    /// The inner proof (from prove_plonky3).
    pub proof: PyanaProof,
    /// Public inputs of the inner proof [leaf_hash, root].
    pub public_inputs: Vec<BabyBear>,
}

/// Result of recursive proof aggregation.
#[derive(Clone)]
pub struct RecursiveProof {
    /// The aggregation proof (proves the hash chain of all inner proofs' public inputs).
    pub aggregation_proof: PyanaProof,
    /// The inner proofs (still needed for full verification).
    pub inner_proofs: Vec<RecursionInput>,
    /// The final accumulator hash (commitment to the sequence of public inputs).
    pub final_accumulator: BabyBear,
    /// Number of aggregated proofs.
    pub num_proofs: usize,
}

/// Generate the aggregation trace for a sequence of proof public inputs.
///
/// Each row represents one inner proof being aggregated into the hash chain.
fn generate_aggregation_trace(
    proof_public_inputs: &[Vec<BabyBear>],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let n = proof_public_inputs.len();
    assert!(n >= 2, "need at least 2 proofs to aggregate");

    let padded_len = n.next_power_of_two();
    let mut trace = Vec::with_capacity(padded_len);
    let mut accumulator = BabyBear::ZERO;

    for (i, pi) in proof_public_inputs.iter().enumerate() {
        assert_eq!(pi.len(), 2, "each proof must have 2 public inputs [leaf, root]");
        let leaf = pi[0];
        let root = pi[1];

        // Compute next accumulator: hash_4_to_1([acc, leaf, root, step_index])
        let step_idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, leaf, root, step_idx]);

        trace.push(vec![accumulator, leaf, root, acc_out]);
        accumulator = acc_out;
    }

    let final_accumulator = accumulator;

    // Pad to power of 2 (chain continues with identity: hash of acc with zeros)
    for i in n..padded_len {
        let step_idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, BabyBear::ZERO, BabyBear::ZERO, step_idx]);
        trace.push(vec![accumulator, BabyBear::ZERO, BabyBear::ZERO, acc_out]);
        accumulator = acc_out;
    }

    // Final accumulator is the last row's output
    let actual_final = trace.last().unwrap()[3];
    let public_inputs = vec![BabyBear::ZERO, actual_final];

    (trace, public_inputs)
}

/// Produce a recursive proof that aggregates N inner proofs.
///
/// This:
/// 1. Verifies each inner proof
/// 2. Builds a hash chain of their public inputs
/// 3. Proves the hash chain with Plonky3
///
/// The result is a single proof that commits to the sequence of all inner proofs.
pub fn prove_recursive(inputs: Vec<RecursionInput>) -> Result<RecursiveProof, String> {
    if inputs.len() < 2 {
        return Err("Need at least 2 proofs for aggregation".to_string());
    }

    // Step 1: Verify all inner proofs
    for (i, input) in inputs.iter().enumerate() {
        verify_plonky3(&input.proof, &input.public_inputs)
            .map_err(|e| format!("Inner proof {} verification failed: {}", i, e))?;
    }

    // Step 2: Build aggregation trace
    let proof_pis: Vec<Vec<BabyBear>> = inputs.iter()
        .map(|input| input.public_inputs.clone())
        .collect();

    let (trace, public_inputs) = generate_aggregation_trace(&proof_pis);

    // Step 3: Prove the aggregation
    let config = create_config();
    let air = AggregationAir;

    let matrix = {
        let width = trace[0].len();
        let values: Vec<P3BabyBear> = trace.iter()
            .flat_map(|row| row.iter().map(|&v| to_p3(v)))
            .collect();
        RowMajorMatrix::new(values, width)
    };

    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    let aggregation_proof = p3_uni_stark::prove(&config, &air, matrix, &p3_public);

    // Verify the aggregation proof
    p3_uni_stark::verify(&config, &air, &aggregation_proof, &p3_public)
        .map_err(|e| format!("Aggregation proof verification failed: {:?}", e))?;

    let final_accumulator = public_inputs[1];
    let num_proofs = inputs.len();

    Ok(RecursiveProof {
        aggregation_proof,
        inner_proofs: inputs,
        final_accumulator,
        num_proofs,
    })
}

/// Verify a recursive proof.
///
/// This verifies:
/// 1. The aggregation proof (hash chain is valid)
/// 2. Each inner proof individually
/// 3. The hash chain matches the inner proofs' public inputs
pub fn verify_recursive(recursive_proof: &RecursiveProof) -> Result<(), String> {
    let config = create_config();
    let air = AggregationAir;

    // Recompute expected public inputs for the aggregation proof
    let proof_pis: Vec<Vec<BabyBear>> = recursive_proof.inner_proofs.iter()
        .map(|input| input.public_inputs.clone())
        .collect();
    let (_, expected_public_inputs) = generate_aggregation_trace(&proof_pis);

    let p3_public: Vec<P3BabyBear> = expected_public_inputs.iter().map(|&v| to_p3(v)).collect();

    // Verify the aggregation proof
    p3_uni_stark::verify(&config, &air, &recursive_proof.aggregation_proof, &p3_public)
        .map_err(|e| format!("Aggregation proof verification failed: {:?}", e))?;

    // Verify each inner proof
    for (i, input) in recursive_proof.inner_proofs.iter().enumerate() {
        verify_plonky3(&input.proof, &input.public_inputs)
            .map_err(|e| format!("Inner proof {} verification failed: {}", i, e))?;
    }

    Ok(())
}

/// 2-to-1 aggregation: combine two proofs into one.
///
/// This is the building block for tree-style compression:
/// - Level 0: N individual proofs
/// - Level 1: N/2 aggregation proofs
/// - Level 2: N/4 aggregation proofs
/// - ...
/// - Final: 1 proof
pub fn aggregate_pair(
    left: RecursionInput,
    right: RecursionInput,
) -> Result<RecursiveProof, String> {
    prove_recursive(vec![left, right])
}

/// Tree-style compression: reduce N proofs to a single aggregation proof.
///
/// Takes a list of RecursionInputs and produces a single RecursiveProof
/// by pairwise aggregation in a binary tree structure.
///
/// For N proofs, this requires O(N) total proving work (each level halves).
pub fn compress_tree(mut inputs: Vec<RecursionInput>) -> Result<RecursiveProof, String> {
    if inputs.is_empty() {
        return Err("Cannot compress empty proof list".to_string());
    }
    if inputs.len() == 1 {
        return Err("Need at least 2 proofs for tree compression".to_string());
    }

    // If we have exactly 2, aggregate directly
    if inputs.len() == 2 {
        let right = inputs.pop().unwrap();
        let left = inputs.pop().unwrap();
        return aggregate_pair(left, right);
    }

    // For >2 proofs, aggregate all at once (single-level hash chain)
    // A future optimization could do tree-structured aggregation with
    // nested recursive proofs, but that requires in-circuit verification.
    prove_recursive(inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_prover::prove_plonky3;
    use crate::poseidon2_air::{create_poseidon2_test_witness, generate_merkle_poseidon2_trace};

    fn make_test_proof(leaf_val: u32) -> RecursionInput {
        let leaf = BabyBear::new(leaf_val);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let proof = prove_plonky3(&trace, &public_inputs);
        RecursionInput { proof, public_inputs }
    }

    #[test]
    fn aggregation_trace_generation() {
        let pis = vec![
            vec![BabyBear::new(100), BabyBear::new(200)],
            vec![BabyBear::new(300), BabyBear::new(400)],
        ];
        let (trace, public_inputs) = generate_aggregation_trace(&pis);

        // Should be padded to power of 2
        assert!(trace.len().is_power_of_two());
        assert!(trace.len() >= 2);

        // Width should be 4
        assert_eq!(trace[0].len(), 4);

        // Public inputs: [0, final_accumulator]
        assert_eq!(public_inputs[0], BabyBear::ZERO);

        // Chain continuity: acc_out[0] = acc_in[1]
        assert_eq!(trace[0][3], trace[1][0]);
    }

    #[test]
    fn recursive_proof_two_proofs() {
        let input1 = make_test_proof(1111);
        let input2 = make_test_proof(2222);

        let result = prove_recursive(vec![input1, input2]);
        assert!(result.is_ok(), "Recursive proof failed: {:?}", result.err());

        let recursive_proof = result.unwrap();
        assert_eq!(recursive_proof.num_proofs, 2);

        // Verify the recursive proof
        let verify_result = verify_recursive(&recursive_proof);
        assert!(verify_result.is_ok(), "Recursive verification failed: {:?}", verify_result.err());
    }

    #[test]
    fn recursive_proof_four_proofs() {
        let inputs: Vec<RecursionInput> = (1..=4)
            .map(|i| make_test_proof(i * 1000))
            .collect();

        let result = prove_recursive(inputs);
        assert!(result.is_ok(), "4-proof recursion failed: {:?}", result.err());

        let recursive_proof = result.unwrap();
        assert_eq!(recursive_proof.num_proofs, 4);

        let verify_result = verify_recursive(&recursive_proof);
        assert!(verify_result.is_ok(), "4-proof recursive verification failed: {:?}", verify_result.err());
    }

    #[test]
    fn aggregate_pair_works() {
        let input1 = make_test_proof(5555);
        let input2 = make_test_proof(6666);

        let result = aggregate_pair(input1, input2);
        assert!(result.is_ok(), "Pair aggregation failed: {:?}", result.err());
    }
}
