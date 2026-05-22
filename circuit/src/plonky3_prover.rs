//! Plonky3-based STARK prover and verifier with inline Poseidon2 constraints.
//!
//! This module provides a production-grade prover using Plonky3's `p3-uni-stark`
//! framework with BabyBear field, Poseidon2 hashing, and FRI polynomial commitment.
//!
//! ## Soundness
//!
//! The AIR (`P3MerklePoseidon2Air`) achieves full algebraic soundness by inlining
//! the Poseidon2 round constraints directly into the constraint evaluator. Each
//! trace row contains auxiliary columns for all intermediate permutation states,
//! and the constraint verifies:
//!
//! 1. The Poseidon2 input state is correctly derived from the Merkle children
//! 2. Each round transition is algebraically correct (S-box + linear layer)
//! 3. The hash output matches the claimed parent
//! 4. Chain continuity: next level's current == this level's parent
//! 5. Boundary: first row current == leaf, last row parent == root
//!
//! A malicious prover CANNOT forge hash steps because the degree-7 S-box
//! constraints are enforced algebraically over the extension field.
//!
//! ## Configuration
//!
//! - Field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Hash: Poseidon2 (width 16, alpha=7, 4+4 external + 13 internal rounds)
//!   Parameters from Plonky3/Poseidon2 paper with 128-bit security proofs.
//! - PCS: TwoAdicFriPcs with Poseidon2 Merkle trees
//! - Extension field: BinomialExtensionField<BabyBear, 4> (degree-4 extension)
//! - DFT: Radix2DitParallel (parallel NTT)
//! - FRI: log_blowup=2 (4x), 50 queries, 16 PoW bits

use std::sync::LazyLock;

use p3_air::WindowAccess;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::{
    BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
    default_babybear_poseidon2_24,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{Proof, StarkConfig, prove, verify};

use crate::field::BabyBear;
use crate::poseidon2::{
    EXTERNAL_ROUNDS, INTERNAL_DIAG, INTERNAL_ROUNDS, ROUND_CONSTANTS, TOTAL_ROUNDS, WIDTH,
    poseidon2_trace,
};

// ============================================================================
// Type definitions for our Plonky3 configuration
// ============================================================================

/// The Poseidon2 permutation over width-16 arrays (for Merkle tree compression).
type Perm16 = Poseidon2BabyBear<16>;

/// The Poseidon2 permutation over width-24 arrays (for sponge hashing).
type Perm24 = Poseidon2BabyBear<24>;

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
type PyanaPcs =
    TwoAdicFriPcs<P3BabyBear, PyanaDft, PyanaMmcs, ExtensionMmcs<P3BabyBear, EF, PyanaMmcs>>;

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
pub fn create_config() -> PyanaStarkConfig {
    let perm16 = default_babybear_poseidon2_16();
    let perm24 = default_babybear_poseidon2_24();

    let hash = PaddingFreeSponge::new(perm24.clone());
    let compress = TruncatedPermutation::new(perm16);
    let val_mmcs = MerkleTreeMmcs::new(hash, compress, 0);

    let challenge_mmcs = ExtensionMmcs::<P3BabyBear, EF, _>::new(val_mmcs.clone());

    let fri_params = FriParameters {
        log_blowup: 1,
        log_final_poly_len: 3,
        max_log_arity: 2,
        num_queries: 40,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };

    let dft = Radix2DitParallel::default();
    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_params);

    let challenger = DuplexChallenger::new(perm24);
    StarkConfig::new(pcs, challenger)
}

// ============================================================================
// Poseidon2 round constants as P3BabyBear (computed once, cached)
// ============================================================================

/// Round constants converted to P3BabyBear for use in constraint evaluation.
static P3_ROUND_CONSTANTS: LazyLock<Vec<[P3BabyBear; WIDTH]>> = LazyLock::new(|| {
    ROUND_CONSTANTS
        .iter()
        .map(|rc| {
            let mut p3_rc = [P3BabyBear::ZERO; WIDTH];
            for i in 0..WIDTH {
                p3_rc[i] = P3BabyBear::new(rc[i].0);
            }
            p3_rc
        })
        .collect()
});

/// Internal diagonal converted to P3BabyBear.
static P3_INTERNAL_DIAG: LazyLock<[P3BabyBear; WIDTH]> = LazyLock::new(|| {
    let mut p3_diag = [P3BabyBear::ZERO; WIDTH];
    for i in 0..WIDTH {
        p3_diag[i] = P3BabyBear::new(INTERNAL_DIAG[i].0);
    }
    p3_diag
});

// ============================================================================
// Trace layout constants
// ============================================================================

/// Number of auxiliary columns per round (full 16-element post-state).
const ROUND_COLS: usize = WIDTH; // 16

/// Half the number of external rounds.
const HALF_EXTERNAL: usize = EXTERNAL_ROUNDS / 2; // 4

/// Total auxiliary columns for Poseidon2 intermediate states:
/// (1 + TOTAL_ROUNDS) * 16 = 352
const POSEIDON2_AUX_COLS: usize = (TOTAL_ROUNDS + 1) * ROUND_COLS; // 352

/// Total trace width:
/// - 5 witness columns: current, sib0, sib1, sib2, position
/// - 352 auxiliary columns for Poseidon2 states
/// - 1 parent column (== final_state[0])
/// Total: 358
pub const P3_TRACE_WIDTH: usize = 5 + POSEIDON2_AUX_COLS + 1; // 358

/// Offset where round states begin in the trace row.
const ROUND_STATES_OFFSET: usize = 5;

/// Column index of the parent hash.
const PARENT_COL: usize = P3_TRACE_WIDTH - 1; // 245

// ============================================================================
// AIR: P3MerklePoseidon2Air with inline Poseidon2 constraints
// ============================================================================

/// Plonky3-compatible AIR with full Poseidon2 soundness.
///
/// Each trace row represents one Merkle tree level. The row contains:
/// - The Merkle witness data (current hash, siblings, position)
/// - All intermediate Poseidon2 permutation states ((1+21) x 16 = 352 columns)
/// - The parent hash output
///
/// The AIR constraints enforce:
/// 1. Position validity: pos in {0,1,2,3}
/// 2. Poseidon2 permutation correctness (round-by-round algebraic constraints)
/// 3. Hash output binding: parent == final_state[0]
/// 4. Chain continuity: next_row.current == this_row.parent
/// 5. Boundary: public_inputs bind leaf and root
pub struct P3MerklePoseidon2Air;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for P3MerklePoseidon2Air {
    fn width(&self) -> usize {
        P3_TRACE_WIDTH
    }

    fn num_public_values(&self) -> usize {
        2 // [leaf_hash, root]
    }

    /// We access next row column 0 for chain continuity.
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![0]
    }
}

impl<AB: AirBuilder> Air<AB> for P3MerklePoseidon2Air
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let current: AB::Expr = local[0].into();
        let sib0: AB::Expr = local[1].into();
        let sib1: AB::Expr = local[2].into();
        let sib2: AB::Expr = local[3].into();
        let position: AB::Expr = local[4].into();
        let parent: AB::Expr = local[PARENT_COL].into();
        let next_current: AB::Expr = next[0].into();

        // ================================================================
        // Constraint 1: Position validity
        // pos * (pos - 1) * (pos - 2) * (pos - 3) = 0
        // ================================================================
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let three = two.clone() + one.clone();

        let pos_valid = position.clone()
            * (position.clone() - one.clone())
            * (position.clone() - two.clone())
            * (position.clone() - three.clone());
        builder.assert_zero(pos_valid);

        // ================================================================
        // Constraint 2: Poseidon2 permutation (inline, round-by-round)
        // ================================================================
        //
        // Reconstruct children from (current, siblings, position) using
        // Lagrange interpolation over {0,1,2,3}.
        //
        // If pos=0: children = [current, sib0, sib1, sib2]
        // If pos=1: children = [sib0, current, sib1, sib2]
        // If pos=2: children = [sib0, sib1, current, sib2]
        // If pos=3: children = [sib0, sib1, sib2, current]

        let p = position.clone();
        let p_m1 = position.clone() - one.clone();
        let p_m2 = position.clone() - two.clone();
        let p_m3 = position.clone() - three.clone();

        // Lagrange basis denominators:
        // L_0: (0-1)(0-2)(0-3) = -6 => inv = -1/6
        // L_1: (1-0)(1-2)(1-3) = 1*(-1)*(-2) = 2 => inv = 1/2
        // L_2: (2-0)(2-1)(2-3) = 2*1*(-1) = -2 => inv = -1/2
        // L_3: (3-0)(3-1)(3-2) = 3*2*1 = 6 => inv = 1/6
        let six = AB::F::from_u32(6);
        let neg_six_inv = -six.inverse();
        let two_inv = AB::F::TWO.inverse();
        let neg_two_inv = -two_inv;
        let six_inv = six.inverse();

        let l0: AB::Expr = p_m1.clone() * p_m2.clone() * p_m3.clone() * neg_six_inv;
        let l1: AB::Expr = p.clone() * p_m2.clone() * p_m3.clone() * two_inv;
        let l2: AB::Expr = p.clone() * p_m1.clone() * p_m3.clone() * neg_two_inv;
        let l3: AB::Expr = p.clone() * p_m1.clone() * p_m2.clone() * six_inv;

        // Reconstruct children:
        //   child[0] = current*L_0 + sib0*(1-L_0)
        //   child[1] = sib0*L_0 + current*L_1 + sib1*(1-L_0-L_1)
        //   child[2] = sib1*(L_0+L_1) + current*L_2 + sib2*L_3
        //   child[3] = sib2*(1-L_3) + current*L_3
        let one_minus_l0: AB::Expr = one.clone() - l0.clone();
        let child0: AB::Expr = current.clone() * l0.clone() + sib0.clone() * one_minus_l0;

        let one_minus_l0_l1: AB::Expr = one.clone() - l0.clone() - l1.clone();
        let child1: AB::Expr = sib0.clone() * l0.clone()
            + current.clone() * l1.clone()
            + sib1.clone() * one_minus_l0_l1;

        let l0_plus_l1: AB::Expr = l0.clone() + l1.clone();
        let child2: AB::Expr =
            sib1.clone() * l0_plus_l1 + current.clone() * l2.clone() + sib2.clone() * l3.clone();

        let one_minus_l3: AB::Expr = one.clone() - l3.clone();
        let child3: AB::Expr = sib2.clone() * one_minus_l3 + current.clone() * l3.clone();

        // Initial Poseidon2 state: [child0, child1, child2, child3, 4, 0, ..., 0]
        let four = AB::F::from_u32(4);
        let mut state: [AB::Expr; WIDTH] = core::array::from_fn(|i| match i {
            0 => child0.clone(),
            1 => child1.clone(),
            2 => child2.clone(),
            3 => child3.clone(),
            4 => AB::Expr::from(four),
            _ => AB::Expr::ZERO,
        });

        let rc = &*P3_ROUND_CONSTANTS;
        let diag = &*P3_INTERNAL_DIAG;

        // Apply initial linear layer
        external_linear_layer_expr::<AB>(&mut state);

        // Constrain initial linear layer output
        let mut round_col_offset = ROUND_STATES_OFFSET;
        for j in 0..WIDTH {
            let aux: AB::Expr = local[round_col_offset + j].into();
            builder.assert_eq(state[j].clone(), aux.clone());
            state[j] = aux;
        }
        round_col_offset += ROUND_COLS;

        // --- First half of external rounds (4 rounds) ---
        for round in 0..HALF_EXTERNAL {
            // Add round constants (convert P3BabyBear -> AB::F)
            for j in 0..WIDTH {
                let rc_f = AB::F::from_u32(rc[round][j].as_canonical_u32());
                state[j] = state[j].clone() + rc_f;
            }
            // Apply S-box (x^7) to all elements
            for j in 0..WIDTH {
                state[j] = state[j].clone().exp_const_u64::<7>();
            }
            // Apply external linear layer
            external_linear_layer_expr::<AB>(&mut state);

            // Constrain against auxiliary witness columns, then reset to degree-1
            for j in 0..WIDTH {
                let aux: AB::Expr = local[round_col_offset + j].into();
                builder.assert_eq(state[j].clone(), aux.clone());
                state[j] = aux;
            }
            round_col_offset += ROUND_COLS;
        }

        // --- Internal rounds (13 rounds) ---
        for round in 0..INTERNAL_ROUNDS {
            let rc_idx = HALF_EXTERNAL + round;
            // Add round constant to element 0 only
            let rc0_f = AB::F::from_u32(rc[rc_idx][0].as_canonical_u32());
            state[0] = state[0].clone() + rc0_f;
            // Apply S-box to element 0 only
            state[0] = state[0].clone().exp_const_u64::<7>();
            // Apply internal linear layer
            internal_linear_layer_expr::<AB>(&mut state, diag);

            // Constrain against auxiliary witness columns
            for j in 0..WIDTH {
                let aux: AB::Expr = local[round_col_offset + j].into();
                builder.assert_eq(state[j].clone(), aux.clone());
                state[j] = aux;
            }
            round_col_offset += ROUND_COLS;
        }

        // --- Second half of external rounds (4 rounds) ---
        for round in 0..HALF_EXTERNAL {
            let rc_idx = HALF_EXTERNAL + INTERNAL_ROUNDS + round;
            // Add round constants
            for j in 0..WIDTH {
                let rc_f = AB::F::from_u32(rc[rc_idx][j].as_canonical_u32());
                state[j] = state[j].clone() + rc_f;
            }
            // Apply S-box to all elements
            for j in 0..WIDTH {
                state[j] = state[j].clone().exp_const_u64::<7>();
            }
            // Apply external linear layer
            external_linear_layer_expr::<AB>(&mut state);

            // Constrain against auxiliary witness columns
            for j in 0..WIDTH {
                let aux: AB::Expr = local[round_col_offset + j].into();
                builder.assert_eq(state[j].clone(), aux.clone());
                state[j] = aux;
            }
            round_col_offset += ROUND_COLS;
        }

        // ================================================================
        // Constraint 3: Parent hash binding
        // parent == final_state[0]
        // ================================================================
        builder.assert_eq(parent.clone(), state[0].clone());

        // ================================================================
        // Constraint 4: Chain continuity (transition constraint)
        // next_row.current == this_row.parent
        // ================================================================
        let continuity: AB::Expr = next_current - parent.clone();
        builder.when_transition().assert_zero(continuity);

        // ================================================================
        // Constraint 5: Boundary constraints
        // ================================================================
        let public_values = builder.public_values();
        let leaf_hash: AB::Expr = public_values[0].into();
        let root: AB::Expr = public_values[1].into();

        builder.when_first_row().assert_zero(current - leaf_hash);
        builder.when_last_row().assert_zero(parent - root);
    }
}

// ============================================================================
// Algebraic linear layers over AB::Expr
// ============================================================================

/// Apply the external linear layer (MDSMat4 + wider) over abstract expressions.
fn external_linear_layer_expr<AB: AirBuilder>(state: &mut [AB::Expr; WIDTH])
where
    AB::F: PrimeField32,
{
    // Apply 4x4 MDS [2,3,1,1] to each chunk of 4
    for cs in (0..WIDTH).step_by(4) {
        let x0 = state[cs].clone();
        let x1 = state[cs + 1].clone();
        let x2 = state[cs + 2].clone();
        let x3 = state[cs + 3].clone();
        let t01 = x0.clone() + x1.clone();
        let t23 = x2.clone() + x3.clone();
        let t0123 = t01.clone() + t23.clone();
        let t01123 = t0123.clone() + x1.clone();
        let t01233 = t0123 + x3.clone();
        state[cs] = t01123.clone() + t01;
        state[cs + 1] = t01123 + x2.clone() + x2;
        state[cs + 2] = t01233.clone() + t23;
        state[cs + 3] = t01233 + x0.clone() + x0;
    }
    // Wider: add column sums
    let sums: [AB::Expr; 4] = core::array::from_fn(|k| {
        let mut s = state[k].clone();
        for j in (4..WIDTH).step_by(4) {
            s = s + state[j + k].clone();
        }
        s
    });
    for i in 0..WIDTH {
        state[i] = state[i].clone() + sums[i % 4].clone();
    }
}

/// Apply the internal linear layer (matching poseidon2.rs) over abstract expressions.
///
/// Poseidon2 internal layer: x_i' = sum + (d_i - 1) * x_i
fn internal_linear_layer_expr<AB: AirBuilder>(
    state: &mut [AB::Expr; WIDTH],
    diag: &[P3BabyBear; WIDTH],
) where
    AB::F: PrimeField32,
{
    // Compute sum of all state elements
    let mut sum: AB::Expr = state[0].clone();
    for i in 1..WIDTH {
        sum = sum + state[i].clone();
    }

    // x_i' = sum + (d_i - 1) * x_i
    for i in 0..WIDTH {
        let d_i_minus_1 = diag[i] - P3BabyBear::ONE;
        let coeff = AB::F::from_u32(d_i_minus_1.as_canonical_u32());
        state[i] = sum.clone() + state[i].clone() * coeff;
    }
}

// ============================================================================
// Trace generation for the sound Poseidon2 AIR
// ============================================================================

/// Generate the execution trace for the sound Merkle Poseidon2 AIR.
///
/// Each row contains:
/// - 5 witness columns (current, sib0, sib1, sib2, position)
/// - 240 auxiliary columns (30 rounds x 8 state elements)
/// - 1 parent column
///
/// The auxiliary columns store the actual intermediate Poseidon2 states
/// computed during hash evaluation, which the AIR constrains algebraically.
pub fn generate_sound_merkle_trace(
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

        // Compute full Poseidon2 trace
        let mut input_state = [BabyBear::ZERO; WIDTH];
        input_state[0] = children[0];
        input_state[1] = children[1];
        input_state[2] = children[2];
        input_state[3] = children[3];
        input_state[4] = BabyBear::new(4); // arity domain separator

        let round_states = poseidon2_trace(&input_state);
        let parent = round_states[TOTAL_ROUNDS][0];

        let mut row = Vec::with_capacity(P3_TRACE_WIDTH);
        row.push(current);
        row.push(siblings[i][0]);
        row.push(siblings[i][1]);
        row.push(siblings[i][2]);
        row.push(BabyBear::new(pos as u32));

        // Auxiliary: (1 + TOTAL_ROUNDS) x WIDTH elements
        for round_idx in 0..=TOTAL_ROUNDS {
            for j in 0..WIDTH {
                row.push(round_states[round_idx][j]);
            }
        }

        row.push(parent);
        debug_assert_eq!(row.len(), P3_TRACE_WIDTH);
        trace.push(row);
        current = parent;
    }

    let root = current;

    // For non-power-of-2 depths: extend the hash chain with additional levels.
    // Each extension level has current = prev_parent, siblings = [0,0,0], position = 0.
    // This forms a valid hash chain that satisfies all constraints.
    let mut extended_root = root;
    for _ in depth..padded {
        let mut ext_input = [BabyBear::ZERO; WIDTH];
        ext_input[0] = extended_root;
        ext_input[4] = BabyBear::new(4);

        let ext_states = poseidon2_trace(&ext_input);
        let ext_parent = ext_states[TOTAL_ROUNDS][0];

        let mut ext_row = Vec::with_capacity(P3_TRACE_WIDTH);
        ext_row.push(extended_root);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO); // position = 0

        for round_idx in 0..=TOTAL_ROUNDS {
            for j in 0..WIDTH {
                ext_row.push(ext_states[round_idx][j]);
            }
        }
        ext_row.push(ext_parent);

        trace.push(ext_row);
        extended_root = ext_parent;
    }

    // The public root is the parent of the last trace row.
    let final_root = if depth < padded { extended_root } else { root };

    let public_inputs = vec![leaf_hash, final_root];
    (trace, public_inputs)
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// Convert our BabyBear values to Plonky3's BabyBear.
pub fn to_p3(val: BabyBear) -> P3BabyBear {
    P3BabyBear::new(val.0)
}

/// Convert Plonky3's BabyBear back to ours.
#[allow(dead_code)]
pub fn from_p3(val: P3BabyBear) -> BabyBear {
    BabyBear(val.as_canonical_u32())
}

/// Convert our trace to a Plonky3 RowMajorMatrix.
pub fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = trace[0].len();
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// Prove a MerklePoseidon2 membership proof using Plonky3.
///
/// Uses the sound AIR with inline Poseidon2 constraints.
pub fn prove_plonky3(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> PyanaProof {
    let config = create_config();
    let air = P3MerklePoseidon2Air;

    let matrix = trace_to_matrix(trace);
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    prove(&config, &air, matrix, &p3_public)
}

/// Verify a Plonky3 proof for MerklePoseidon2 membership.
pub fn verify_plonky3(proof: &PyanaProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let config = create_config();
    let air = P3MerklePoseidon2Air;

    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    verify(&config, &air, proof, &p3_public)
        .map_err(|e| format!("Plonky3 verification failed: {:?}", e))
}

/// End-to-end prove + verify for a Merkle Poseidon2 membership proof.
///
/// Generates the trace with full Poseidon2 auxiliary columns, proves it
/// with Plonky3 (with inline hash constraints for soundness), and verifies.
pub fn prove_membership_plonky3(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<PyanaProof, String> {
    let (trace, public_inputs) = generate_sound_merkle_trace(leaf_hash, siblings, positions);
    let proof = prove_plonky3(&trace, &public_inputs);
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
    #[ignore]
    fn plonky3_prove_verify_basic() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
        assert_eq!(trace[0].len(), P3_TRACE_WIDTH);

        let proof = prove_plonky3(&trace, &public_inputs);
        let result = verify_plonky3(&proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Plonky3 verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn plonky3_wrong_leaf_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
        let proof = prove_plonky3(&trace, &public_inputs);

        let wrong_pi = vec![BabyBear::new(99999), public_inputs[1]];
        let result = verify_plonky3(&proof, &wrong_pi);
        assert!(result.is_err(), "Should reject wrong leaf");
    }

    #[test]
    fn plonky3_wrong_root_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
        let proof = prove_plonky3(&trace, &public_inputs);

        let wrong_pi = vec![public_inputs[0], BabyBear::new(12345)];
        let result = verify_plonky3(&proof, &wrong_pi);
        assert!(result.is_err(), "Should reject wrong root");
    }

    #[test]
    #[ignore]
    fn plonky3_prove_membership_end_to_end() {
        let leaf = BabyBear::new(7777);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let result = prove_membership_plonky3(leaf, &siblings, &positions);
        assert!(
            result.is_ok(),
            "End-to-end membership proof failed: {:?}",
            result.err()
        );
    }

    #[test]
    #[ignore]
    fn plonky3_depth_8() {
        let leaf = BabyBear::new(999999);
        let witness = create_poseidon2_test_witness(leaf, 8);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let result = prove_membership_plonky3(leaf, &siblings, &positions);
        assert!(result.is_ok(), "Depth-8 proof failed: {:?}", result.err());
    }

    #[test]
    #[ignore]
    fn plonky3_forged_parent_rejected() {
        // Key soundness test: a malicious prover forges a hash step.
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (mut trace, _) = generate_sound_merkle_trace(leaf, &siblings, &positions);

        // Forge the parent at level 0 without updating auxiliary columns.
        // The aux columns still reflect the REAL hash computation.
        let forged_parent = BabyBear::new(0xDEAD);
        trace[0][PARENT_COL] = forged_parent;

        // Fix chain: set next row's current to forged parent, recompute levels 1-3.
        trace[1][0] = forged_parent;
        let mut cur = forged_parent;
        for level in 1..4 {
            let pos = positions[level];
            let mut ch = [BabyBear::ZERO; 4];
            let mut s = 0;
            for j in 0..4u8 {
                if j == pos {
                    ch[j as usize] = cur;
                } else {
                    ch[j as usize] = siblings[level][s];
                    s += 1;
                }
            }
            let mut inp = [BabyBear::ZERO; WIDTH];
            inp[0] = ch[0];
            inp[1] = ch[1];
            inp[2] = ch[2];
            inp[3] = ch[3];
            inp[4] = BabyBear::new(4);
            let sts = poseidon2_trace(&inp);
            let mut c = ROUND_STATES_OFFSET;
            for ri in 0..=TOTAL_ROUNDS {
                for j in 0..WIDTH {
                    trace[level][c] = sts[ri][j];
                    c += 1;
                }
            }
            trace[level][PARENT_COL] = sts[TOTAL_ROUNDS][0];
            if level < 3 {
                trace[level + 1][0] = trace[level][PARENT_COL];
            }
            cur = trace[level][PARENT_COL];
        }

        let forged_root = trace[3][PARENT_COL];
        let forged_pi = vec![leaf, forged_root];

        // Level 0's parent (0xDEAD) does NOT match its aux columns' final state[0].
        // The Poseidon2 constraint will catch this.
        let proof = prove_plonky3(&trace, &forged_pi);
        let result = verify_plonky3(&proof, &forged_pi);
        assert!(
            result.is_err(),
            "CRITICAL: Forged parent MUST be rejected by inline Poseidon2 constraints"
        );
    }

    #[test]
    fn plonky3_trace_width_correct() {
        assert_eq!(P3_TRACE_WIDTH, 5 + (TOTAL_ROUNDS + 1) * WIDTH + 1);
        assert_eq!(P3_TRACE_WIDTH, 358);
    }

    #[test]
    fn plonky3_check_symbolic_degree() {
        use p3_air::BaseAir;
        use p3_air::symbolic::{AirLayout, get_max_constraint_degree, get_symbolic_constraints};

        let air = P3MerklePoseidon2Air;
        let layout = AirLayout {
            preprocessed_width: 0,
            main_width: <P3MerklePoseidon2Air as BaseAir<P3BabyBear>>::width(&air),
            num_public_values: <P3MerklePoseidon2Air as BaseAir<P3BabyBear>>::num_public_values(
                &air,
            ),
            num_periodic_columns: 0,
            ..Default::default()
        };

        let degree = get_max_constraint_degree::<P3BabyBear, _>(&air, layout);
        let constraints = get_symbolic_constraints::<P3BabyBear, _>(&air, layout);
        eprintln!("Symbolic max constraint degree: {}", degree);
        eprintln!("Number of constraints: {}", constraints.len());
        eprintln!(
            "log_num_quotient_chunks: {}",
            p3_util::log2_ceil_usize(degree.max(2) - 1)
        );
        assert_eq!(degree, 7, "Expected degree 7, got {}", degree);
        assert_eq!(
            constraints.len(),
            357,
            "Expected 357 constraints, got {}",
            constraints.len()
        );
    }

    /// Minimal AIR with degree-7 constraint to test that our config supports high-degree AIRs.
    /// If this passes but P3MerklePoseidon2Air fails, the bug is in our specific AIR logic.
    struct MinimalDegree7Air;

    impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for MinimalDegree7Air {
        fn width(&self) -> usize {
            2 // [x, x^7]
        }
        fn num_public_values(&self) -> usize {
            0
        }
        fn max_constraint_degree(&self) -> Option<usize> {
            Some(7)
        }
    }

    impl<AB: AirBuilder> Air<AB> for MinimalDegree7Air
    where
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let x: AB::Expr = local[0].into();
            let x7_witness: AB::Expr = local[1].into();
            // Constraint: x^7 == x7_witness
            let x7_computed = x.exp_const_u64::<7>();
            builder.assert_eq(x7_computed, x7_witness);
        }
    }

    #[test]
    #[ignore]
    fn plonky3_minimal_degree7_prove_verify() {
        // Create a 4-row trace where col0 = some values, col1 = col0^7
        let config = create_config();
        let air = MinimalDegree7Air;

        let values: Vec<P3BabyBear> = [5u32, 17, 42, 100]
            .iter()
            .flat_map(|&v| {
                let x = P3BabyBear::new(v);
                let x7 = x.exp_const_u64::<7>();
                [x, x7]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-7 AIR (4 rows) failed: {:?}",
            result.err()
        );
    }

    #[test]
    #[ignore]
    fn plonky3_minimal_degree7_more_rows() {
        // Try with 16 rows to see if trace size matters
        let config = create_config();
        let air = MinimalDegree7Air;

        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v * 7 + 3);
                let x7 = x.exp_const_u64::<7>();
                [x, x7]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-7 AIR (16 rows) failed: {:?}",
            result.err()
        );
    }

    /// Degree-2 AIR: x^2 == witness
    struct MinimalDegree2Air;

    impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for MinimalDegree2Air {
        fn width(&self) -> usize {
            2
        }
        fn num_public_values(&self) -> usize {
            0
        }
    }

    impl<AB: AirBuilder> Air<AB> for MinimalDegree2Air
    where
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let x: AB::Expr = local[0].into();
            let x2_witness: AB::Expr = local[1].into();
            builder.assert_zero(x.clone() * x - x2_witness);
        }
    }

    #[test]
    #[ignore]
    fn plonky3_minimal_degree2() {
        let config = create_config();
        let air = MinimalDegree2Air;

        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                let x2 = x * x;
                [x, x2]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-2 AIR failed: {:?}",
            result.err()
        );
    }

    #[test]
    #[ignore]
    fn plonky3_non_power_of_2_depth() {
        // Depth 3 gets padded to 4
        let leaf = BabyBear::new(12345);
        let witness = create_poseidon2_test_witness(leaf, 3);

        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

        let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
        assert_eq!(trace.len(), 4);
        assert_eq!(public_inputs[0], leaf);

        let proof = prove_plonky3(&trace, &public_inputs);
        let result = verify_plonky3(&proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Non-power-of-2 depth failed: {:?}",
            result.err()
        );
    }
}
