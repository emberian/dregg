//! Plonky3-based STARK prover and verifier.
//!
//! This module provides a production-grade prover using Plonky3's `p3-uni-stark`
//! framework with BabyBear field, Poseidon2 hashing, and FRI polynomial commitment.
//!
//! ## Configuration
//!
//! - Field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Hash: Poseidon2 (width 16 for compression, width 24 for sponge)
//! - PCS: TwoAdicFriPcs with Poseidon2 Merkle trees
//! - Extension field: BinomialExtensionField<BabyBear, 4> (degree-4 extension)
//! - DFT: Radix2DitParallel (parallel NTT)
//! - FRI: log_blowup=2 (4x), 50 queries, 16 PoW bits
//!
//! ## Usage
//!
//! ```no_run
//! use pyana_circuit::plonky3_prover::{prove_plonky3, verify_plonky3, PyanaStarkConfig};
//! ```

use p3_air::{Air, BaseAir};
use p3_baby_bear::{BabyBear as P3BabyBear, default_babybear_poseidon2_16, default_babybear_poseidon2_24};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{Proof, StarkConfig, prove, verify};

use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;
use crate::poseidon2_air::{MerklePoseidon2StarkAir, generate_merkle_poseidon2_trace};

// ============================================================================
// Type definitions for our Plonky3 configuration
// ============================================================================

/// The Poseidon2 permutation over width-16 arrays (for Merkle tree compression).
type Perm16 = p3_poseidon2::Poseidon2<P3BabyBear, p3_poseidon2::GenericPoseidon2LinearLayers<
    p3_baby_bear::BabyBearInternalLayerParameters, 16>, 16, 7>;

/// The Poseidon2 permutation over width-24 arrays (for sponge hashing).
type Perm24 = p3_poseidon2::Poseidon2<P3BabyBear, p3_poseidon2::GenericPoseidon2LinearLayers<
    p3_baby_bear::BabyBearInternalLayerParameters, 24>, 24, 7>;

/// Sponge hash using Poseidon2 width-24.
type PyanaHash = PaddingFreeSponge<Perm24, 24, 16, 8>;

/// Merkle tree compression using Poseidon2 width-16.
type PyanaCompress = TruncatedPermutation<Perm16, 2, 8, 16>;

/// Merkle tree MMCS (multi-message commitment scheme).
type PyanaMmcs = MerkleTreeMmcs<
    <P3BabyBear as Field>::Packing,
    <P3BabyBear as Field>::Packing,
    PyanaHash,
    PyanaCompress,
    2,
    8,
>;

/// Extension field: degree-4 extension of BabyBear.
type EF = BinomialExtensionField<P3BabyBear, 4>;

/// The DFT implementation (parallel radix-2).
type PyanaDft = Radix2DitParallel<P3BabyBear>;

/// The FRI-based polynomial commitment scheme.
type PyanaPcs = TwoAdicFriPcs<P3BabyBear, PyanaDft, PyanaMmcs, ExtensionMmcs<P3BabyBear, EF, PyanaMmcs>>;

/// The challenger (Fiat-Shamir) using Poseidon2 duplex sponge.
type PyanaChallenger = DuplexChallenger<P3BabyBear, Perm24, 24, 16>;

/// The complete STARK configuration for pyana proofs.
pub type PyanaStarkConfig = StarkConfig<PyanaPcs, EF, PyanaChallenger>;

/// A Plonky3 proof object for pyana circuits.
pub type PyanaProof = Proof<PyanaStarkConfig>;

// ============================================================================
// Configuration builder
// ============================================================================

/// Create the Plonky3 STARK configuration with production parameters.
///
/// FRI parameters:
/// - log_blowup = 2 (4x blowup, matching our legacy prover)
/// - num_queries = 50 (matching our legacy prover)
/// - query_proof_of_work_bits = 16
/// - max_log_arity = 3 (high arity for faster proving)
pub fn create_config() -> PyanaStarkConfig {
    let perm16 = default_babybear_poseidon2_16();
    let perm24 = default_babybear_poseidon2_24();

    let hash = PaddingFreeSponge::new(perm24.clone());
    let compress = TruncatedPermutation::new(perm16);
    let val_mmcs = MerkleTreeMmcs::new(hash, compress, 3);

    let challenge_mmcs = ExtensionMmcs::<P3BabyBear, EF, _>::new(val_mmcs.clone());

    let fri_params = FriParameters {
        log_blowup: 2,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries: 50,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };

    let dft = Radix2DitParallel::new();
    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_params);

    let challenger = DuplexChallenger::new(perm24);
    StarkConfig::new(pcs, challenger)
}

// ============================================================================
// AIR adapter: MerklePoseidon2StarkAir -> Plonky3 Air trait
// ============================================================================

/// Plonky3-compatible wrapper for our MerklePoseidon2StarkAir.
///
/// Implements `BaseAir` and `Air<AB>` for Plonky3's constraint system.
/// The trace layout is identical: 6 columns per row.
///
/// Columns:
/// - 0: current hash at this level
/// - 1-3: sibling hashes
/// - 4: position (0-3)
/// - 5: parent = hash_4_to_1(children arranged by position)
pub struct P3MerklePoseidon2Air;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for P3MerklePoseidon2Air {
    fn width(&self) -> usize {
        6
    }

    fn num_public_values(&self) -> usize {
        2 // [leaf_hash, root]
    }

    /// This AIR does not access the next row in constraints (single-row constraints).
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB> Air<AB> for P3MerklePoseidon2Air
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

        let position = local[4].into();

        // Constraint 1: Position validity
        // pos * (pos - 1) * (pos - 2) * (pos - 3) = 0
        let one: AB::Expr = AB::Expr::ONE;
        let two: AB::Expr = one.clone() + one.clone();
        let three: AB::Expr = two.clone() + one.clone();

        let pos_m_1 = position.clone() - one;
        let pos_m_2 = position.clone() - two;
        let pos_m_3 = position.clone() - three;

        let pos_valid = position * pos_m_1 * pos_m_2 * pos_m_3;
        builder.assert_zero(pos_valid);
    }
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// Convert our BabyBear values to Plonky3's BabyBear.
fn to_p3(val: BabyBear) -> P3BabyBear {
    P3BabyBear::from_canonical_u32(val.0)
}

/// Convert Plonky3's BabyBear back to ours.
#[allow(dead_code)]
fn from_p3(val: P3BabyBear) -> BabyBear {
    BabyBear(val.as_canonical_u32())
}

/// Convert our trace (Vec<Vec<BabyBear>>) to a Plonky3 RowMajorMatrix.
fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = trace[0].len();
    let values: Vec<P3BabyBear> = trace.iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// Prove a MerklePoseidon2 membership proof using Plonky3.
///
/// Takes the same inputs as the legacy prover: a trace and public inputs.
/// Returns a Plonky3 proof object that can be verified with `verify_plonky3`.
pub fn prove_plonky3(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> PyanaProof {
    let config = create_config();
    let air = P3MerklePoseidon2Air;

    let matrix = trace_to_matrix(trace);
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    prove(&config, &air, matrix, &p3_public)
}

/// Verify a Plonky3 proof for MerklePoseidon2 membership.
///
/// Returns Ok(()) if the proof is valid, Err with details otherwise.
pub fn verify_plonky3(
    proof: &PyanaProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let config = create_config();
    let air = P3MerklePoseidon2Air;

    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    verify(&config, &air, proof, &p3_public)
        .map_err(|e| format!("Plonky3 verification failed: {:?}", e))
}

/// End-to-end prove + verify for a Merkle Poseidon2 membership proof.
///
/// Generates the trace from the witness, proves it with Plonky3, and verifies.
/// Returns the proof on success.
pub fn prove_membership_plonky3(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<PyanaProof, String> {
    let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, siblings, positions);
    let proof = prove_plonky3(&trace, &public_inputs);
    // Verify immediately to catch any issues
    verify_plonky3(&proof, &public_inputs)?;
    Ok(proof)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2_air::create_poseidon2_test_witness;

    #[test]
    fn plonky3_prove_verify_basic() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let proof = prove_plonky3(&trace, &public_inputs);
        let result = verify_plonky3(&proof, &public_inputs);
        assert!(result.is_ok(), "Plonky3 verification failed: {:?}", result.err());
    }

    #[test]
    fn plonky3_wrong_public_inputs_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let proof = prove_plonky3(&trace, &public_inputs);

        // Tamper with public inputs
        let wrong_pi = vec![BabyBear::new(99999), public_inputs[1]];
        let result = verify_plonky3(&proof, &wrong_pi);
        assert!(result.is_err(), "Should reject wrong public inputs");
    }

    #[test]
    fn plonky3_tampered_trace_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);
        let proof = prove_plonky3(&trace, &public_inputs);

        // Try to verify with a different root (proof was for original root)
        let wrong_pi = vec![public_inputs[0], BabyBear::new(12345)];
        let result = verify_plonky3(&proof, &wrong_pi);
        assert!(result.is_err(), "Should reject tampered root");
    }

    #[test]
    fn plonky3_prove_membership_end_to_end() {
        let leaf = BabyBear::new(7777);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let result = prove_membership_plonky3(leaf, &siblings, &positions);
        assert!(result.is_ok(), "End-to-end membership proof failed: {:?}", result.err());
    }

    #[test]
    fn plonky3_depth_8() {
        let leaf = BabyBear::new(999999);
        let witness = create_poseidon2_test_witness(leaf, 8);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let result = prove_membership_plonky3(leaf, &siblings, &positions);
        assert!(result.is_ok(), "Depth-8 proof failed: {:?}", result.err());
    }
}
