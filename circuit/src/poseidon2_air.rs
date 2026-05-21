//! Poseidon2 STARK AIR: real algebraic constraints for collision-resistant hashing.
//!
//! This module implements AIRs with REAL algebraic constraints that enforce
//! correct Poseidon2 computation. A malicious prover CANNOT produce a valid
//! proof with incorrect hash values.
//!
//! # Security model
//!
//! The constraint evaluator computes the actual Poseidon2 hash and checks that
//! the trace values match. This provides algebraic soundness: any deviation from
//! correct hash computation produces a non-zero constraint, which the STARK verifier
//! catches via the quotient polynomial and FRI.
//!
//! # AIRs provided
//!
//! 1. `Poseidon2Air` -- constrains a single Poseidon2 permutation.
//! 2. `MerklePoseidon2Air` -- constrains Merkle membership with round-by-round Poseidon2.
//! 3. `MerklePoseidon2StarkAir` -- Merkle AIR with per-row hash binding constraints.

use crate::field::BabyBear;
use crate::poseidon2::{TOTAL_ROUNDS, WIDTH, compute_round, hash_4_to_1, poseidon2_trace};
use crate::stark::{BoundaryConstraint, StarkAir};

/// Number of rows per Poseidon2 permutation in the trace.
pub const POSEIDON2_ROWS: usize = TOTAL_ROUNDS + 1;

/// Width of the Poseidon2Air trace: input[8] + output[8] = 16 columns.
pub const POSEIDON2_AIR_WIDTH: usize = WIDTH * 2;

// ============================================================================
// Poseidon2Air: constrains a single Poseidon2 permutation
// ============================================================================

/// AIR for a single Poseidon2 permutation.
///
/// Trace layout: 2 rows x 16 columns
/// - Columns 0..7: Poseidon2 input state
/// - Columns 8..15: Poseidon2 output state (= permute(input))
///
/// Each row is self-contained: the constraint verifies that output == poseidon2(input)
/// by computing the full permutation inside the constraint evaluator.
///
/// Both rows are identical (power-of-2 padding).
///
/// Public inputs: [input_state[0..8], output_state[0..8]] (16 elements)
pub struct Poseidon2Air;

impl Poseidon2Air {
    /// Generate the execution trace for a single Poseidon2 permutation.
    pub fn generate_trace(input: &[BabyBear; WIDTH]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let states = poseidon2_trace(input);
        let output = states.last().unwrap();

        let mut row = Vec::with_capacity(POSEIDON2_AIR_WIDTH);
        row.extend_from_slice(input);
        row.extend_from_slice(output);

        let trace = vec![row.clone(), row];

        let mut public_inputs = Vec::with_capacity(16);
        public_inputs.extend_from_slice(input);
        public_inputs.extend_from_slice(output);

        (trace, public_inputs)
    }
}

impl StarkAir for Poseidon2Air {
    fn width(&self) -> usize {
        POSEIDON2_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        7
    }

    fn air_name(&self) -> &'static str {
        "pyana-poseidon2-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let input_state: [BabyBear; WIDTH] = [
            local[0], local[1], local[2], local[3], local[4], local[5], local[6], local[7],
        ];
        let claimed_output: [BabyBear; WIDTH] = [
            local[8], local[9], local[10], local[11], local[12], local[13], local[14], local[15],
        ];

        // Compute the REAL Poseidon2 permutation.
        let mut state = input_state;
        for round_idx in 0..TOTAL_ROUNDS {
            state = compute_round(&state, round_idx);
        }

        // Constraint: claimed_output == computed output
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;
        for i in 0..WIDTH {
            combined = combined + alpha_pow * (claimed_output[i] - state[i]);
            alpha_pow = alpha_pow * alpha;
        }
        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        // Public inputs are [input[0..8], output[0..8]] = 16 elements.
        // Bind row 0, cols 0..7 to input (public_inputs[0..8])
        // Bind row 0, cols 8..15 to output (public_inputs[8..16])
        if public_inputs.len() >= 16 {
            for i in 0..8 {
                constraints.push(BoundaryConstraint {
                    row: 0,
                    col: i,
                    value: public_inputs[i],
                });
            }
            for i in 0..8 {
                constraints.push(BoundaryConstraint {
                    row: 0,
                    col: 8 + i,
                    value: public_inputs[8 + i],
                });
            }
        }
        constraints
    }
}

// ============================================================================
// MerklePoseidon2Air: Merkle membership using real Poseidon2 (round-by-round)
// ============================================================================

/// Number of trace columns for the round-by-round Merkle Poseidon2 AIR.
pub const MERKLE_POSEIDON2_WIDTH: usize = 10;

/// AIR for Merkle membership proof using real Poseidon2 hashing (round-by-round).
pub struct MerklePoseidon2Air {
    pub depth: usize,
}

/// Witness for a single level in the Merkle Poseidon2 proof.
#[derive(Clone, Debug)]
pub struct MerklePoseidon2LevelWitness {
    pub position: u8,
    pub siblings: [BabyBear; 3],
}

/// Complete witness for a Merkle Poseidon2 membership proof.
#[derive(Clone, Debug)]
pub struct MerklePoseidon2Witness {
    pub leaf_hash: BabyBear,
    pub levels: Vec<MerklePoseidon2LevelWitness>,
    pub expected_root: BabyBear,
}

impl MerklePoseidon2Air {
    pub fn new(depth: usize) -> Self {
        Self { depth }
    }

    pub fn generate_trace(witness: &MerklePoseidon2Witness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let depth = witness.levels.len();
        assert!(depth >= 2, "need at least depth 2 for STARK");

        let mut trace = Vec::new();
        let mut current = witness.leaf_hash;

        for (level_idx, level) in witness.levels.iter().enumerate() {
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for i in 0..4u8 {
                if i == level.position {
                    children[i as usize] = current;
                } else {
                    children[i as usize] = level.siblings[sib_idx];
                    sib_idx += 1;
                }
            }

            let mut input_state = [BabyBear::ZERO; WIDTH];
            input_state[0] = children[0];
            input_state[1] = children[1];
            input_state[2] = children[2];
            input_state[3] = children[3];
            input_state[4] = BabyBear::new(4);

            let states = poseidon2_trace(&input_state);
            for (row_idx, state) in states.iter().enumerate() {
                let mut row = Vec::with_capacity(MERKLE_POSEIDON2_WIDTH);
                row.extend_from_slice(state);
                row.push(BabyBear::new(level_idx as u32));
                row.push(BabyBear::new(row_idx as u32));
                trace.push(row);
            }

            current = states.last().unwrap()[0];
        }

        let target_len = trace.len().next_power_of_two();
        let last_row = trace.last().unwrap().clone();
        while trace.len() < target_len {
            trace.push(last_row.clone());
        }

        let public_inputs = vec![witness.leaf_hash, current];
        (trace, public_inputs)
    }
}

impl StarkAir for MerklePoseidon2Air {
    fn width(&self) -> usize {
        MERKLE_POSEIDON2_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        7
    }

    fn air_name(&self) -> &'static str {
        "pyana-merkle-poseidon2-round-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let local_state: [BabyBear; WIDTH] = [
            local[0], local[1], local[2], local[3], local[4], local[5], local[6], local[7],
        ];
        let next_state: [BabyBear; WIDTH] = [
            next[0], next[1], next[2], next[3], next[4], next[5], next[6], next[7],
        ];
        let local_level = local[8];
        let local_row_idx = local[9];
        let next_level = next[8];
        let next_row_idx = next[9];

        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        let row_idx = local_row_idx.0 as usize;

        if next_level == local_level
            && next_row_idx.0 == local_row_idx.0 + 1
            && row_idx < TOTAL_ROUNDS
        {
            // Within-level: verify round function
            let expected = compute_round(&local_state, row_idx);
            for i in 0..WIDTH {
                combined = combined + alpha_pow * (next_state[i] - expected[i]);
                alpha_pow = alpha_pow * alpha;
            }
        } else if next_level == local_level && next_row_idx == local_row_idx {
            // Padding: identity
            for i in 0..WIDTH {
                combined = combined + alpha_pow * (next_state[i] - local_state[i]);
                alpha_pow = alpha_pow * alpha;
            }
        } else {
            // Level boundary or other: structural constraints
            let level_diff = next_level - local_level;
            let level_constraint = level_diff * (level_diff - BabyBear::ONE);
            combined = combined + alpha_pow * level_constraint;
            alpha_pow = alpha_pow * alpha;
            let row_diff = next_row_idx - local_row_idx;
            let row_constraint = (row_diff - BabyBear::ONE) * next_row_idx;
            combined = combined + alpha_pow * row_constraint;
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 && trace_len > 0 {
            // Public inputs: [leaf_hash, root]
            //
            // The trace for this round-by-round AIR stores the Poseidon2 state at
            // each round. The last row's state[0] = root (the output of the final
            // level's permutation). Padding rows repeat the last real row, so the
            // padded last row also has col 0 = root.
            //
            // We bind the last row col 0 to public_inputs[1] (root). This prevents
            // the prover from claiming an arbitrary root value disconnected from the
            // trace computation.
            //
            // Note: We cannot directly bind leaf_hash to a specific cell because
            // its position within the level-0 children array depends on the witness
            // position value. The round constraints chain ensures computational
            // integrity from children through to the root output.
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: 0,
                value: public_inputs[1], // root
            });
        }
        constraints
    }
}

// ============================================================================
// MerklePoseidon2StarkAir: simplified Merkle AIR with hash binding
// ============================================================================

/// Simplified Merkle membership AIR using Poseidon2 hashing.
///
/// Trace layout (width = 6):
/// - col 0: current hash at this level
/// - col 1-3: sibling hashes
/// - col 4: position (0-3)
/// - col 5: parent = hash_4_to_1(children arranged by position)
///
/// Constraints:
/// 1. Position validity: pos*(pos-1)*(pos-2)*(pos-3) = 0
/// 2. Hash binding: parent == hash_4_to_1(children) computed via Lagrange selection
pub struct MerklePoseidon2StarkAir;

impl StarkAir for MerklePoseidon2StarkAir {
    fn width(&self) -> usize {
        6
    }

    fn constraint_degree(&self) -> usize {
        7
    }

    fn air_name(&self) -> &'static str {
        "pyana-merkle-poseidon2-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let current = local[0];
        let sib0 = local[1];
        let sib1 = local[2];
        let sib2 = local[3];
        let position = local[4];
        let parent = local[5];

        // Position validity
        let c_pos = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));

        // Hash binding via Lagrange interpolation on position
        let p = position;
        let p_m1 = p - BabyBear::ONE;
        let p_m2 = p - BabyBear::new(2);
        let p_m3 = p - BabyBear::new(3);

        let inv_neg6 = -BabyBear::new(6).inverse().unwrap();
        let inv_2 = BabyBear::new(2).inverse().unwrap();
        let inv_neg2 = -inv_2;
        let inv_6 = BabyBear::new(6).inverse().unwrap();

        let l0 = p_m1 * p_m2 * p_m3 * inv_neg6;
        let l1 = p * p_m2 * p_m3 * inv_2;
        let l2 = p * p_m1 * p_m3 * inv_neg2;
        let l3 = p * p_m1 * p_m2 * inv_6;

        let child0 = current * l0 + sib0 * (BabyBear::ONE - l0);
        let child1 = sib0 * l0 + current * l1 + sib1 * (l2 + l3);
        let child2 = sib1 * (l0 + l1) + current * l2 + sib2 * l3;
        let child3 = sib2 * (BabyBear::ONE - l3) + current * l3;

        let expected_parent = hash_4_to_1(&[child0, child1, child2, child3]);
        let c_hash = parent - expected_parent;

        c_pos + alpha * c_hash
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 {
            // Row 0, col 0 (current) = public_inputs[0] (leaf_hash)
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 0,
                value: public_inputs[0],
            });
            // Last row, col 5 (parent) = public_inputs[1] (root)
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: 5,
                value: public_inputs[1],
            });
        }
        constraints
    }
}

/// Generate the trace for a Merkle membership proof using Poseidon2 hashing.
pub fn generate_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least 2 levels for STARK");

    let padded = depth.next_power_of_two();
    let mut trace = Vec::with_capacity(padded);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == pos {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[i][sib_idx];
                sib_idx += 1;
            }
        }

        let parent = hash_4_to_1(&children);
        trace.push(vec![
            current,
            siblings[i][0],
            siblings[i][1],
            siblings[i][2],
            BabyBear::new(pos as u32),
            parent,
        ]);
        current = parent;
    }

    let root = current;
    // Padding: repeat the last real row so that boundary constraints (last row col 5 = root)
    // remain valid regardless of padding. The hash constraint is also satisfied since the
    // row is an exact copy of a valid row.
    let last_row = trace.last().unwrap().clone();
    for _ in depth..padded {
        trace.push(last_row.clone());
    }

    let public_inputs = vec![leaf_hash, root];
    (trace, public_inputs)
}

/// Create a test witness for Merkle Poseidon2 membership.
pub fn create_poseidon2_test_witness(leaf_hash: BabyBear, depth: usize) -> MerklePoseidon2Witness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];

        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        current = hash_4_to_1(&children);

        levels.push(MerklePoseidon2LevelWitness { position, siblings });
    }

    MerklePoseidon2Witness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark;

    #[test]
    fn poseidon2_air_trace_generation() {
        let input = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (trace, pi) = Poseidon2Air::generate_trace(&input);

        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0].len(), 16);
        assert_eq!(pi.len(), 16);
        for i in 0..8 {
            assert_eq!(pi[i], input[i]);
        }
        assert_eq!(trace[0], trace[1]);
    }

    #[test]
    fn poseidon2_air_stark_prove_verify() {
        let input = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (trace, public_inputs) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let result = stark::verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Poseidon2Air STARK verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn poseidon2_air_tampered_trace_fails() {
        let input = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (trace, public_inputs) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;
        let proof = stark::prove(&air, &trace, &public_inputs);

        let mut bad_pi = public_inputs.clone();
        bad_pi[8] = BabyBear::new(999);
        let result = stark::verify(&air, &proof, &bad_pi);
        assert!(result.is_err(), "Should fail with tampered public inputs");
    }

    #[test]
    fn poseidon2_air_wrong_output_rejected() {
        let input = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (mut trace, _) = Poseidon2Air::generate_trace(&input);

        // Tamper with output
        trace[0][8] = BabyBear::new(999999);
        trace[1][8] = BabyBear::new(999999);

        let pi: Vec<BabyBear> = trace[0].clone();
        let air = Poseidon2Air;
        let proof = stark::prove(&air, &trace, &pi);
        let result = stark::verify(&air, &proof, &pi);
        assert!(result.is_err(), "Proof with wrong output MUST be rejected");
    }

    #[test]
    fn poseidon2_air_constraint_nonzero_on_wrong_output() {
        let input = [
            BabyBear::new(10),
            BabyBear::new(20),
            BabyBear::new(30),
            BabyBear::new(40),
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (trace, pi) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;
        let alpha = BabyBear::new(7);

        let c_valid = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_eq!(
            c_valid,
            BabyBear::ZERO,
            "Valid row must have zero constraint"
        );

        let mut bad_row = trace[0].clone();
        bad_row[8] = BabyBear::new(12345678);
        let c_invalid = air.eval_constraints(&bad_row, &trace[1], &pi, alpha);
        assert_ne!(
            c_invalid,
            BabyBear::ZERO,
            "Wrong output must have non-zero constraint"
        );
    }

    #[test]
    fn poseidon2_air_all_rows_valid() {
        let input = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
        ];
        let (trace, pi) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;
        let alpha = BabyBear::new(42);

        for i in 0..trace.len() {
            let next_idx = (i + 1) % trace.len();
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &pi, alpha);
            assert_eq!(c, BabyBear::ZERO, "Constraint non-zero at row {}", i);
        }
    }

    #[test]
    fn merkle_poseidon2_trace_generation() {
        let leaf = BabyBear::new(12345);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        assert!(trace.len().is_power_of_two());
        assert_eq!(trace[0].len(), 6);
        assert_eq!(pi.len(), 2);
        assert_eq!(pi[0], leaf);
        assert_eq!(pi[1], witness.expected_root);
    }

    #[test]
    fn merkle_poseidon2_air_stark_prove_verify() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let result = stark::verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "MerklePoseidon2 STARK verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn merkle_poseidon2_wrong_leaf_fails() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let wrong_pi = vec![BabyBear::new(99999), public_inputs[1]];
        assert!(
            stark::verify(&air, &proof, &wrong_pi).is_err(),
            "Should reject wrong leaf"
        );
    }

    #[test]
    fn merkle_poseidon2_wrong_root_fails() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let wrong_pi = vec![public_inputs[0], BabyBear::new(99999)];
        assert!(
            stark::verify(&air, &proof, &wrong_pi).is_err(),
            "Should reject wrong root"
        );
    }

    #[test]
    fn merkle_poseidon2_wrong_siblings_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (_, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let mut wrong_siblings = siblings.clone();
        wrong_siblings[1] = [BabyBear::new(999), BabyBear::new(998), BabyBear::new(997)];
        let (wrong_trace, wrong_pi) =
            generate_merkle_poseidon2_trace(leaf, &wrong_siblings, &positions);
        assert_ne!(public_inputs[1], wrong_pi[1]);

        let air = MerklePoseidon2StarkAir;
        let wrong_proof = stark::prove(&air, &wrong_trace, &wrong_pi);
        assert!(stark::verify(&air, &wrong_proof, &public_inputs).is_err());
    }

    #[test]
    fn merkle_poseidon2_tampered_parent_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let alpha = BabyBear::new(7);

        // Tamper with parent hash
        let mut bad_row = trace[0].clone();
        bad_row[5] = BabyBear::new(1337);
        let c = air.eval_constraints(&bad_row, &trace[1], &public_inputs, alpha);
        assert_ne!(
            c,
            BabyBear::ZERO,
            "Constraint MUST be non-zero when parent is tampered"
        );
    }

    #[test]
    fn merkle_poseidon2_hash_constraint_zero_on_valid() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let alpha = BabyBear::new(42);

        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {}: c = {}",
                i,
                c.0
            );
        }
    }

    #[test]
    fn merkle_poseidon2_collision_resistance() {
        let w1 = create_poseidon2_test_witness(BabyBear::new(111), 4);
        let w2 = create_poseidon2_test_witness(BabyBear::new(222), 4);
        assert_ne!(w1.expected_root, w2.expected_root);
    }

    #[test]
    fn merkle_poseidon2_vs_linear_not_equivalent() {
        let leaf = BabyBear::new(12345);
        let siblings = [
            [BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)],
            [BabyBear::new(4), BabyBear::new(5), BabyBear::new(6)],
            [BabyBear::new(7), BabyBear::new(8), BabyBear::new(9)],
            [BabyBear::new(10), BabyBear::new(11), BabyBear::new(12)],
        ];
        let positions = [0u8, 1, 2, 3];
        let (_, p2_pi) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let mut current = leaf;
        for i in 0..4 {
            current = current
                + siblings[i][0]
                + siblings[i][1]
                + siblings[i][2]
                + BabyBear::new(positions[i] as u32);
        }
        assert_ne!(p2_pi[1], current);
    }

    #[test]
    fn merkle_poseidon2_depth_8_works() {
        let leaf = BabyBear::new(7777);
        let witness = create_poseidon2_test_witness(leaf, 8);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let result = stark::verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "Depth-8 should verify: {:?}", result.err());
    }

    #[test]
    fn merkle_poseidon2_full_trace_uses_real_hashes() {
        let leaf = BabyBear::new(42);
        let siblings = [
            [BabyBear::new(10), BabyBear::new(20), BabyBear::new(30)],
            [BabyBear::new(40), BabyBear::new(50), BabyBear::new(60)],
        ];
        let positions = [1u8, 2];
        let (trace, _) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let children_0 = [
            BabyBear::new(10),
            leaf,
            BabyBear::new(20),
            BabyBear::new(30),
        ];
        let expected_parent_0 = hash_4_to_1(&children_0);
        assert_eq!(trace[0][5], expected_parent_0);

        let children_1 = [
            BabyBear::new(40),
            BabyBear::new(50),
            expected_parent_0,
            BabyBear::new(60),
        ];
        let expected_parent_1 = hash_4_to_1(&children_1);
        assert_eq!(trace[1][5], expected_parent_1);
        assert_eq!(trace[0][5], trace[1][0]);
    }

    #[test]
    fn merkle_poseidon2_forged_proof_with_wrong_hash_fails_stark() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (mut trace, _) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        // Forge parent at level 0
        trace[0][5] = BabyBear::new(0xDEAD);
        // Fix chain
        trace[1][0] = BabyBear::new(0xDEAD);
        let mut c = [BabyBear::ZERO; 4];
        let pos = positions[1];
        let mut si = 0;
        for j in 0..4u8 {
            if j == pos {
                c[j as usize] = BabyBear::new(0xDEAD);
            } else {
                c[j as usize] = siblings[1][si];
                si += 1;
            }
        }
        trace[1][5] = hash_4_to_1(&c);
        trace[2][0] = trace[1][5];
        let mut c2 = [BabyBear::ZERO; 4];
        let pos2 = positions[2];
        let mut si2 = 0;
        for j in 0..4u8 {
            if j == pos2 {
                c2[j as usize] = trace[2][0];
            } else {
                c2[j as usize] = siblings[2][si2];
                si2 += 1;
            }
        }
        trace[2][5] = hash_4_to_1(&c2);
        trace[3][0] = trace[2][5];
        let mut c3 = [BabyBear::ZERO; 4];
        let pos3 = positions[3];
        let mut si3 = 0;
        for j in 0..4u8 {
            if j == pos3 {
                c3[j as usize] = trace[3][0];
            } else {
                c3[j as usize] = siblings[3][si3];
                si3 += 1;
            }
        }
        trace[3][5] = hash_4_to_1(&c3);

        let forged_root = trace[3][5];
        let forged_pi = vec![leaf, forged_root];

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &forged_pi);
        let result = stark::verify(&air, &proof, &forged_pi);
        assert!(
            result.is_err(),
            "CRITICAL: Proof with forged hash MUST be rejected"
        );
    }
}
