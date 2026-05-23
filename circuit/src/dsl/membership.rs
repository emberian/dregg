//! DSL-native Merkle Poseidon2 membership proving and verification.
//!
//! This module provides the production prove/verify API for Merkle membership
//! proofs. It replaces the old hand-written `MerklePoseidon2StarkAir` and
//! `BlindedMerklePoseidon2StarkAir` in `circuit/src/poseidon2_air.rs`.
//!
//! # What this provides
//!
//! - Standard 4-ary Merkle membership (prove leaf is in tree)
//! - Blinded (ring) membership (prove leaf is in tree without revealing which)
//! - Position/direction bits (0..3 enforced via degree-4 polynomial constraint)
//! - Trace generators with proper padding to power-of-two
//! - Production `prove_*` / `verify_*` functions that use the DSL circuit descriptors
//!
//! # Security Model
//!
//! The DSL version uses `hash_fact` (via `ConstraintExpr::Hash`) rather than
//! `hash_4_to_1` with Lagrange child selection. The security property is preserved:
//! the parent hash is uniquely determined by (current, siblings, position). The
//! binding is self-consistent because both trace generation and constraint evaluation
//! use the same `hash_fact` function.

use crate::field::BabyBear;
use crate::poseidon2::hash_fact;
use crate::stark::{self, StarkProof};

use crate::dsl::descriptors::{
    self, BLINDED_MERKLE_P2_WIDTH, MERKLE_P2_WIDTH, blinded_merkle_poseidon2_circuit, merkle_col,
    merkle_poseidon2_circuit,
};

// ============================================================================
// Trace Generation: Standard Merkle Poseidon2
// ============================================================================

/// Generate a valid Merkle membership trace for the DSL Poseidon2 circuit.
///
/// Each row represents one level of the 4-ary Merkle tree (leaf to root).
/// The parent hash is computed as `hash_fact(current, [sib0, sib1, sib2, position])`.
///
/// Returns (trace, public_inputs) where public_inputs = [leaf_hash, root].
pub fn generate_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        // Parent = hash_fact(current, [sib0, sib1, sib2, position])
        let parent = hash_fact(current, &[sib0, sib1, sib2, position]);

        trace.push(vec![current, sib0, sib1, sib2, position, parent]);
        current = parent;
    }

    // Pad to power of two (minimum 2 rows). Padding rows must satisfy all constraints:
    // - Position validity: position=0 satisfies pos*(pos-1)*(pos-2)*(pos-3)=0
    // - Hash binding: parent = hash_fact(current, [0, 0, 0, 0])
    // - Chain continuity: next[current] = local[parent]
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[merkle_col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_parent = hash_fact(prev_parent, &[pad_sib0, pad_sib1, pad_sib2, pad_pos]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
        ]);
    }

    let root = trace.last().unwrap()[merkle_col::PARENT];
    let public_inputs = vec![leaf_hash, root];
    (trace, public_inputs)
}

/// Generate a test witness (deterministic siblings/positions).
///
/// Returns (siblings, positions, expected_root).
pub fn create_test_witness(
    leaf_hash: BabyBear,
    depth: usize,
) -> (Vec<[BabyBear; 3]>, Vec<u8>, BabyBear) {
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = (i % 4) as u8;
        let sibs = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let position = BabyBear::new(pos as u32);
        current = hash_fact(current, &[sibs[0], sibs[1], sibs[2], position]);
        siblings.push(sibs);
        positions.push(pos);
    }

    (siblings, positions, current) // current = expected root
}

// ============================================================================
// Trace Generation: Blinded Merkle Poseidon2
// ============================================================================

/// Generate a blinded Merkle membership trace.
///
/// Public inputs are [blinded_leaf, root] where:
///   blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
///
/// The leaf_hash remains private (not bound to any public input).
pub fn generate_blinded_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
    blinding_factor: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        let parent = hash_fact(current, &[sib0, sib1, sib2, position]);

        // Blinding column: real value at row 0, zero elsewhere
        let row_blinding = if i == 0 {
            blinding_factor
        } else {
            BabyBear::ZERO
        };
        // Blinded column: hash_fact(current, [blinding]) -- must be correct on every row
        let row_blinded = hash_fact(current, &[row_blinding]);

        trace.push(vec![
            current,
            sib0,
            sib1,
            sib2,
            position,
            parent,
            row_blinding,
            row_blinded,
        ]);
        current = parent;
    }

    // Pad to power of two
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[merkle_col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_parent = hash_fact(prev_parent, &[pad_sib0, pad_sib1, pad_sib2, pad_pos]);
        // Blinding=0 on padding rows; blinded = hash_fact(prev_parent, [0])
        let pad_blinded = hash_fact(prev_parent, &[BabyBear::ZERO]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
            BabyBear::ZERO,
            pad_blinded,
        ]);
    }

    let root = trace.last().unwrap()[merkle_col::PARENT];
    // blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
    let blinded_leaf = hash_fact(leaf_hash, &[blinding_factor]);
    let public_inputs = vec![blinded_leaf, root];
    (trace, public_inputs)
}

// ============================================================================
// Production Prove/Verify: Standard Merkle Poseidon2
// ============================================================================

/// Prove Merkle membership using the DSL circuit.
///
/// Generates a STARK proof that `leaf` is a member of the Poseidon2 Merkle tree
/// whose root is computed from the given siblings and positions.
///
/// Returns a `StarkProof` on success, or an error message on failure.
pub fn prove_membership_dsl(
    leaf: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<StarkProof, String> {
    if siblings.len() < 2 {
        return Err("need at least depth 2 for STARK".into());
    }
    if siblings.len() != positions.len() {
        return Err("siblings/positions length mismatch".into());
    }

    let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, siblings, positions);
    let circuit = merkle_poseidon2_circuit();
    let proof = stark::prove(&circuit, &trace, &public_inputs);
    Ok(proof)
}

/// Verify a Merkle membership proof produced by [`prove_membership_dsl`].
///
/// Checks that the proof is valid for the given leaf and root.
pub fn verify_membership_dsl(
    proof: &StarkProof,
    leaf: BabyBear,
    root: BabyBear,
) -> Result<(), String> {
    let public_inputs = vec![leaf, root];
    let circuit = merkle_poseidon2_circuit();
    stark::verify(&circuit, proof, &public_inputs)
}

/// Verify a Merkle membership proof with arbitrary public inputs.
///
/// This is used when the proof has additional public inputs beyond [leaf, root]
/// (e.g., action binding, composition commitment, revealed facts commitment).
pub fn verify_membership_dsl_full(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let circuit = merkle_poseidon2_circuit();
    stark::verify(&circuit, proof, public_inputs)
}

// ============================================================================
// Production Prove/Verify: Blinded Merkle Poseidon2
// ============================================================================

/// Prove blinded (ring) Merkle membership using the DSL circuit.
///
/// Generates a STARK proof that the prover knows a leaf in the tree, without
/// revealing which leaf. The public inputs are [blinded_leaf, root] where:
///   blinded_leaf = hash_fact(leaf, [blinding])
///
/// The blinding factor should be fresh random per presentation for unlinkability.
pub fn prove_blinded_membership_dsl(
    leaf: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
    blinding: BabyBear,
) -> Result<StarkProof, String> {
    if siblings.len() < 2 {
        return Err("need at least depth 2 for STARK".into());
    }
    if siblings.len() != positions.len() {
        return Err("siblings/positions length mismatch".into());
    }

    let (trace, public_inputs) =
        generate_blinded_merkle_poseidon2_trace(leaf, siblings, positions, blinding);
    let circuit = blinded_merkle_poseidon2_circuit();
    let proof = stark::prove(&circuit, &trace, &public_inputs);
    Ok(proof)
}

/// Verify a blinded Merkle membership proof produced by [`prove_blinded_membership_dsl`].
///
/// Checks that the proof is valid for the given blinded_leaf and root.
pub fn verify_blinded_membership_dsl(
    proof: &StarkProof,
    blinded_leaf: BabyBear,
    root: BabyBear,
) -> Result<(), String> {
    let public_inputs = vec![blinded_leaf, root];
    let circuit = blinded_merkle_poseidon2_circuit();
    stark::verify(&circuit, proof, &public_inputs)
}

/// Verify a blinded membership proof with arbitrary public inputs.
///
/// This is used when the proof has additional public inputs beyond [blinded_leaf, root]
/// (e.g., action binding, composition commitment).
pub fn verify_blinded_membership_dsl_full(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let circuit = blinded_merkle_poseidon2_circuit();
    stark::verify(&circuit, proof, public_inputs)
}

// ============================================================================
// Legacy compatibility types (re-exported from merkle_types.rs)
// ============================================================================

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH,
    create_test_witness as create_test_witness_legacy,
};

// ============================================================================
// AIR Name Constants (for dispatch)
// ============================================================================

/// The AIR name for standard DSL Merkle Poseidon2 membership proofs.
pub const MERKLE_POSEIDON2_AIR_NAME: &str = descriptors::MERKLE_POSEIDON2_AIR_NAME;

/// The AIR name for blinded DSL Merkle membership proofs.
pub const BLINDED_MERKLE_AIR_NAME: &str = descriptors::BLINDED_MERKLE_AIR_NAME;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prove_verify_standard_membership() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, root) = create_test_witness(leaf, 4);

        let proof = prove_membership_dsl(leaf, &siblings, &positions).unwrap();
        let result = verify_membership_dsl(&proof, leaf, root);
        assert!(
            result.is_ok(),
            "Standard membership should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn prove_verify_standard_depth_8() {
        let leaf = BabyBear::new(7777);
        let (siblings, positions, root) = create_test_witness(leaf, 8);

        let proof = prove_membership_dsl(leaf, &siblings, &positions).unwrap();
        let result = verify_membership_dsl(&proof, leaf, root);
        assert!(
            result.is_ok(),
            "Depth-8 membership should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn standard_wrong_leaf_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, root) = create_test_witness(leaf, 4);

        let proof = prove_membership_dsl(leaf, &siblings, &positions).unwrap();
        let result = verify_membership_dsl(&proof, BabyBear::new(99999), root);
        assert!(result.is_err(), "Wrong leaf should be rejected");
    }

    #[test]
    fn standard_wrong_root_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, root) = create_test_witness(leaf, 4);

        let proof = prove_membership_dsl(leaf, &siblings, &positions).unwrap();
        let result = verify_membership_dsl(&proof, leaf, BabyBear::new(99999));
        assert!(result.is_err(), "Wrong root should be rejected");
    }

    #[test]
    fn prove_verify_blinded_membership() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(987654321);

        let proof = prove_blinded_membership_dsl(leaf, &siblings, &positions, blinding).unwrap();

        let (_, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let blinded_leaf = pi[0];
        let root = pi[1];

        let result = verify_blinded_membership_dsl(&proof, blinded_leaf, root);
        assert!(
            result.is_ok(),
            "Blinded membership should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn blinded_unlinkability() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);

        let blinding_1 = BabyBear::new(111111);
        let blinding_2 = BabyBear::new(222222);

        let (_, pi_1) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_1);
        let (_, pi_2) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_2);

        // Same root (same tree)
        assert_eq!(pi_1[1], pi_2[1]);
        // Different blinded_leaf (unlinkable)
        assert_ne!(pi_1[0], pi_2[0]);
    }

    #[test]
    fn blinded_wrong_root_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(555555);

        let proof = prove_blinded_membership_dsl(leaf, &siblings, &positions, blinding).unwrap();

        let (_, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let blinded_leaf = pi[0];

        let result = verify_blinded_membership_dsl(&proof, blinded_leaf, BabyBear::new(99999));
        assert!(result.is_err(), "Wrong root should be rejected");
    }

    #[test]
    fn blinded_wrong_blinded_leaf_rejected() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);
        let blinding = BabyBear::new(555555);

        let proof = prove_blinded_membership_dsl(leaf, &siblings, &positions, blinding).unwrap();

        let (_, pi) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding);
        let root = pi[1];

        let result = verify_blinded_membership_dsl(&proof, BabyBear::new(77777), root);
        assert!(result.is_err(), "Wrong blinded_leaf should be rejected");
    }

    #[test]
    fn air_name_matches_descriptor() {
        let circuit = merkle_poseidon2_circuit();
        use crate::stark::StarkAir;
        assert_eq!(circuit.air_name(), MERKLE_POSEIDON2_AIR_NAME);

        let blinded_circuit = blinded_merkle_poseidon2_circuit();
        assert_eq!(blinded_circuit.air_name(), BLINDED_MERKLE_AIR_NAME);
    }
}
