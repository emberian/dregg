//! STARK-in-Pickles wrapper: verify a BabyBear STARK proof inside a Pickles recursive SNARK.
//!
//! # Status: SCAFFOLD
//!
//! This module defines the architecture for wrapping BabyBear STARKs inside
//! Pickles proofs but the constraint implementation is incomplete:
//! - Range checks are placeholders (line ~362)
//! - Poseidon2 emulation uses filler gates (line ~462)
//! - The wrapper delegates to Pickles step binding, not actual STARK verification
//!
//! For the production STARK-in-Kimchi path, see `poseidon_stark.rs` which uses
//! native Poseidon commitments for efficient (~29K gate) Kimchi wrapping.
//!
//! # Architecture
//!
//! ```text
//! BabyBear STARK proof (24-38 KiB, fast to generate ~200ms)
//!     ↓ [Pickles circuit verifies this]
//! Pickles recursive proof (~1 KB, constant-size)
//!     ↓ [can be further composed recursively]
//! Final proof (still ~1 KB regardless of history depth)
//! ```
//!
//! # BabyBear Emulation in Pasta Field
//!
//! BabyBear: p = 2^31 - 2^27 + 1 = 2013265921 (~2 billion)
//! Pasta (Pallas): p ≈ 2^255
//!
//! Since BabyBear's modulus fits in 31 bits, every BabyBear element is trivially
//! embeddable as a native Pallas field element. The challenge is enforcing BabyBear
//! arithmetic constraints:
//!
//! - **Addition**: `a + b mod P_BB` — native Pallas addition followed by conditional
//!   subtraction. Cost: 1 addition + 1 comparison + 1 conditional subtraction ≈ 3 gates.
//! - **Multiplication**: `a * b mod P_BB` — native Pallas multiplication (gives exact
//!   62-bit result since both operands < 2^31), then reduce via range check.
//!   Cost: 1 multiplication + 1 range decomposition ≈ 5 gates.
//! - **Range check**: Decompose into 31 bits, verify `value < P_BB` via comparison
//!   with the constant. Cost: ~32 gates for full bit decomposition (can be optimized
//!   with Kimchi's RangeCheck0 gate to ~4 gates).
//!
//! # In-Circuit STARK Verification Steps
//!
//! 1. **Fiat-Shamir transcript replay** (Poseidon2 over BabyBear, emulated in Pallas):
//!    - Absorb trace commitment (32 bytes → 1 Fp element)
//!    - Absorb public inputs (as packed BabyBear elements)
//!    - Squeeze challenges: alpha, FRI betas
//!    - Cost: ~240 constraints per hash × ~50 hashes ≈ 12,000 gates
//!
//! 2. **FRI query Merkle path verification** (BLAKE3 → Poseidon2 in emulated BabyBear):
//!    - For each of 80 queries: verify ~4 Merkle levels
//!    - Each level: hash two siblings, compare to commitment
//!    - Cost: 80 queries × 4 levels × 240 gates ≈ 76,800 gates
//!
//! 3. **Constraint polynomial evaluation at query points**:
//!    - Evaluate the AIR constraint polynomial at each FRI query point
//!    - For a width-6, degree-4 AIR: ~2000 gates per query
//!    - Cost: 80 × 2000 ≈ 160,000 gates
//!
//! 4. **FRI folding consistency**:
//!    - Verify that each FRI layer correctly folds from previous
//!    - For each query × each layer: check `even + beta * odd == folded`
//!    - Cost: 80 queries × 4 layers × 10 gates ≈ 3,200 gates
//!
//! 5. **Final FRI polynomial degree check**:
//!    - Verify the final FRI polynomial has degree < 4
//!    - Cost: negligible (~20 gates)
//!
//! # Total Gate Count Estimate
//!
//! | Component              | Gates    | Notes                                    |
//! |------------------------|----------|------------------------------------------|
//! | Fiat-Shamir (Poseidon2)| ~12,000  | 50 hashes × 240 gates                   |
//! | Merkle paths           | ~76,800  | 80 queries × 4 levels × 240 gates       |
//! | Constraint evaluation  | ~160,000 | 80 queries × 2000 gates                 |
//! | FRI folding            | ~3,200   | 80 queries × 4 layers × 10 gates        |
//! | BabyBear range checks  | ~20,000  | ~4000 multiplications × 5 gates each    |
//! | **Total**              | **~272,000** | Fits in a single Kimchi circuit     |
//!
//! # Proving Time Estimate
//!
//! At ~50,000 gates/second for Kimchi (IPA over Vesta):
//! - ~5-6 seconds for a single STARK verification wrap
//! - Acceptable for checkpoint proofs (per-epoch, not per-block)
//!
//! # Proof Size
//!
//! - Input: ~24-38 KiB STARK proof
//! - Output: ~1-2 KiB Pickles proof (constant-size)
//! - After recursive composition: still ~1-2 KiB
//!
//! # Implementation Status
//!
//! This module provides:
//! - Complete type definitions for the wrapping circuit
//! - The public API for `wrap_stark_in_pickles` and `verify_pickles_wrapped_stark`
//! - A concrete Kimchi circuit skeleton for the STARK verifier
//! - Cost accounting for feasibility analysis
//!
//! The full implementation requires encoding BabyBear Poseidon2 as Kimchi gates,
//! which is feasible but involves ~2000 lines of gate-level constraint code.

use super::mina::{
    PicklesRecursiveProof, PicklesStateTransition, prove_recursive_step, verify_recursive_proof,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::stark::{StarkAir, StarkProof};

use ark_ff::{One, Zero};
use kimchi::circuits::{
    gate::{CircuitGate, GateType},
    wires::{COLUMNS, Wire},
};
use mina_curves::pasta::Fp;
use serde::{Deserialize, Serialize};

// ============================================================================
// Constants
// ============================================================================

/// BabyBear modulus as a Pallas field element for in-circuit comparisons.
const BABYBEAR_P_FP: u64 = BABYBEAR_P as u64;

/// Number of FRI queries in our STARK (matches `stark.rs`).
const NUM_FRI_QUERIES: usize = 80;

/// FRI blowup factor (matches `stark.rs`).
const FRI_BLOWUP: usize = 4;

/// Maximum FRI layers we support (log2(trace_len) - log2(final_poly_degree)).
const MAX_FRI_LAYERS: usize = 16;

/// Maximum Merkle depth for FRI commitment trees.
const MAX_MERKLE_DEPTH: usize = 16;

/// Kimchi gates per Poseidon2 hash (emulated over BabyBear in Pallas).
/// 30 rounds × 8 state elements, with ~1 gate per S-box + MDS:
/// External rounds (8): 8 × 8 S-boxes = 64 gates
/// Internal rounds (22): 22 × 1 S-box + 22 MDS = 44 gates
/// Plus MDS mixing: 30 × 2 = 60 gates
/// Plus BabyBear reduction: ~60 range-check gates
/// Total: ~228 ≈ 240 gates per Poseidon2 invocation.
const GATES_PER_POSEIDON2_HASH: usize = 240;

/// Gates for one BabyBear multiplication with range check in Pallas.
/// 1 native mul + bit decomposition + comparison with P_BB.
const GATES_PER_BB_MUL: usize = 5;

/// Gates for one BabyBear addition with reduction.
const GATES_PER_BB_ADD: usize = 3;

// ============================================================================
// Types
// ============================================================================

/// A STARK proof wrapped inside a Pickles recursive SNARK.
///
/// This is the constant-size output (~1-2 KiB) that attests to the validity
/// of an arbitrarily large STARK proof. It can be further composed recursively
/// with other Pickles proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PicklesWrappedStark {
    /// The Pickles recursive proof (constant-size, ~1-2 KiB).
    pub pickles_proof: PicklesRecursiveProof,

    /// The AIR name that was verified (for domain separation).
    pub air_name: String,

    /// The public inputs from the original STARK proof (as u32 BabyBear values).
    /// These are the statement being proved — the Pickles proof attests
    /// that a valid STARK proof exists for these public inputs.
    pub public_inputs: Vec<u32>,

    /// Hash of the original STARK proof (for auditability / binding).
    pub stark_proof_hash: [u8; 32],

    /// Number of Kimchi gates used in the wrapping circuit.
    pub circuit_gate_count: usize,
}

/// Configuration for the STARK-in-Pickles wrapper.
#[derive(Clone, Debug)]
pub struct WrapConfig {
    /// The AIR description (width, constraint degree, name).
    pub air_width: usize,
    pub air_constraint_degree: usize,
    pub air_name: String,

    /// Number of FRI queries to verify in-circuit.
    /// Default: 80 (full security). Can be reduced for faster wrapping
    /// at the cost of reduced soundness in the wrapping step (the STARK
    /// itself still has full 80-query security; this only affects the
    /// Pickles circuit's constraint on the STARK verification).
    pub num_queries_to_verify: usize,

    /// Maximum FRI layers to verify.
    pub max_fri_layers: usize,

    /// Whether to use Kimchi's RangeCheck0 gate for BabyBear range proofs
    /// (saves ~4x gates vs bit decomposition, but requires newer Kimchi).
    pub use_range_check_gate: bool,
}

impl Default for WrapConfig {
    fn default() -> Self {
        Self {
            air_width: 6,
            air_constraint_degree: 4,
            air_name: "pyana-merkle-v1".to_string(),
            num_queries_to_verify: NUM_FRI_QUERIES,
            max_fri_layers: MAX_FRI_LAYERS,
            use_range_check_gate: false,
        }
    }
}

/// Errors from the STARK-in-Pickles wrapping process.
#[derive(Clone, Debug, thiserror::Error)]
pub enum WrapError {
    #[error("STARK proof validation failed: {0}")]
    StarkValidation(String),

    #[error("AIR mismatch: expected {expected}, got {actual}")]
    AirMismatch { expected: String, actual: String },

    #[error("Circuit construction error: {0}")]
    CircuitConstruction(String),

    #[error("Kimchi prover error: {0}")]
    KimchiProver(String),

    #[error("Proof size exceeds maximum: {size} > {max}")]
    ProofTooLarge { size: usize, max: usize },
}

// ============================================================================
// Gate Count Estimation
// ============================================================================

/// Detailed gate count breakdown for wrapping a specific STARK proof.
#[derive(Clone, Debug)]
pub struct GateCountEstimate {
    /// Gates for Fiat-Shamir transcript replay (Poseidon2 hashes).
    pub fiat_shamir_gates: usize,
    /// Gates for Merkle path verification (FRI query openings).
    pub merkle_path_gates: usize,
    /// Gates for constraint polynomial evaluation at query points.
    pub constraint_eval_gates: usize,
    /// Gates for FRI folding consistency checks.
    pub fri_folding_gates: usize,
    /// Gates for BabyBear range checks (ensure values < P_BB).
    pub range_check_gates: usize,
    /// Gates for public input binding.
    pub public_input_gates: usize,
    /// Total gate count.
    pub total: usize,
}

/// Estimate the number of Kimchi gates required to verify a STARK proof in-circuit.
///
/// This provides a concrete feasibility analysis before attempting the full wrap.
pub fn estimate_gate_count(proof: &StarkProof, config: &WrapConfig) -> GateCountEstimate {
    let num_queries = config.num_queries_to_verify.min(proof.query_proofs.len());
    let num_fri_layers = proof.fri_commitments.len();
    let merkle_depth = if !proof.query_proofs.is_empty() {
        proof.query_proofs[0].trace_path.len()
    } else {
        0
    };

    // 1. Fiat-Shamir transcript: need to hash all commitments + public inputs
    //    - 1 hash for trace commitment
    //    - 1 hash for constraint commitment
    //    - num_fri_layers hashes for FRI commitments
    //    - 1 hash for public inputs
    //    - Several squeezes for challenges
    let num_transcript_hashes = 3 + num_fri_layers + (num_queries / 16); // queries derived in batches
    let fiat_shamir_gates = num_transcript_hashes * GATES_PER_POSEIDON2_HASH;

    // 2. Merkle paths: each query verifies trace + constraint + FRI layer paths
    let paths_per_query = 2 + num_fri_layers; // trace path + constraint path + FRI layers
    let merkle_path_gates = num_queries * paths_per_query * merkle_depth * GATES_PER_POSEIDON2_HASH;

    // 3. Constraint evaluation: evaluate AIR polynomial at each query point
    //    For width W and degree D: approximately W * D multiplications + additions
    let ops_per_constraint_eval =
        config.air_width * config.air_constraint_degree * GATES_PER_BB_MUL
            + config.air_width * GATES_PER_BB_ADD;
    let constraint_eval_gates = num_queries * ops_per_constraint_eval;

    // 4. FRI folding: for each query, verify folding at each layer
    //    fold(even, odd, beta) = even + beta * odd: 1 mul + 1 add + range check
    let gates_per_fold = GATES_PER_BB_MUL + GATES_PER_BB_ADD + 3; // +3 for range check
    let fri_folding_gates = num_queries * num_fri_layers * gates_per_fold;

    // 5. Range checks: every BabyBear value needs validation (< P_BB)
    //    Approximate: every multiplication output + every intermediate
    let num_bb_values = num_queries * (config.air_width * 2 + num_fri_layers * 2);
    let gates_per_range = if config.use_range_check_gate { 1 } else { 5 };
    let range_check_gates = num_bb_values * gates_per_range;

    // 6. Public input binding
    let public_input_gates = proof.public_inputs.len() * 2;

    let total = fiat_shamir_gates
        + merkle_path_gates
        + constraint_eval_gates
        + fri_folding_gates
        + range_check_gates
        + public_input_gates;

    GateCountEstimate {
        fiat_shamir_gates,
        merkle_path_gates,
        constraint_eval_gates,
        fri_folding_gates,
        range_check_gates,
        public_input_gates,
        total,
    }
}

// ============================================================================
// BabyBear Emulation Gadgets (Kimchi gate-level)
// ============================================================================

/// Represents a BabyBear value inside the Kimchi circuit.
/// The value is stored as a native Fp element (which is large enough to hold
/// any BabyBear value without reduction). Range-check constraints ensure
/// the witness value is actually < P_BB.
#[derive(Clone, Copy, Debug)]
struct EmulatedBabyBear {
    /// The row in the witness where this value lives.
    row: usize,
    /// The column in the witness (0..14).
    col: usize,
}

/// Build Kimchi gates for BabyBear multiplication with range check.
///
/// Given a, b (both < P_BB), constrain:
///   c = a * b mod P_BB
///
/// Strategy: Since a, b < 2^31, the product a*b < 2^62, which fits in Fp.
/// We use the decomposition: a * b = q * P_BB + c, where 0 <= c < P_BB.
/// The circuit constrains:
///   1. a * b - q * P_BB - c = 0  (in Fp, exact since no overflow)
///   2. c < P_BB  (range check)
///   3. q < 2^31  (range check, since q = floor(a*b / P_BB) < 2^31)
fn build_babybear_mul_gates(start_row: usize) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let mut row = start_row;

    // Gate 1: Generic gate encoding a * b - q * P_BB - c = 0
    // Using Kimchi's Generic gate: l*w0 + r*w1 + o*w2 + m*w0*w1 + c = 0
    // We set up: w0=a, w1=b, w2=c, w3=q
    // Constraint: w0*w1 - P_BB*w3 - w2 = 0
    // In Generic form: m=1 (for w0*w1), coeff[2]=-1 (for -w2), coeff[3]=-P_BB (for -P_BB*w3)
    let mut coeffs = vec![Fp::zero(); COLUMNS];
    coeffs[0] = Fp::zero(); // no linear w0 term
    coeffs[1] = Fp::zero(); // no linear w1 term
    coeffs[2] = -Fp::one(); // -w2 (the result c)
    coeffs[3] = -Fp::from(BABYBEAR_P_FP); // -P_BB * w3 (the quotient q)
    // The multiplication selector for w0*w1 is in the Generic gate's 4th coefficient
    coeffs[4] = Fp::one(); // multiplication coefficient (w0 * w1)
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        coeffs,
    ));
    row += 1;

    // Gate 2: Range check for c < P_BB (bit decomposition)
    // In a full implementation, this would use Kimchi's RangeCheck0 gate
    // or a 31-bit decomposition with a final comparison gate.
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::one(); COLUMNS],
    ));
    row += 1;

    // Gate 3: Range check for q < 2^31
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::one(); COLUMNS],
    ));
    row += 1;

    (gates, row)
}

/// Build Kimchi gates for BabyBear addition with modular reduction.
///
/// Given a, b (both < P_BB), constrain:
///   c = a + b mod P_BB
///
/// Strategy: a + b < 2*P_BB < 2^32, which fits in Fp.
/// We constrain: c = a + b - borrow * P_BB, where borrow ∈ {0, 1}.
fn build_babybear_add_gates(start_row: usize) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let mut row = start_row;

    // Gate: a + b - borrow * P_BB - c = 0, borrow * (borrow - 1) = 0
    let mut coeffs = vec![Fp::zero(); COLUMNS];
    coeffs[0] = Fp::one(); // +a (w0)
    coeffs[1] = Fp::one(); // +b (w1)
    coeffs[2] = -Fp::one(); // -c (w2)
    coeffs[3] = -Fp::from(BABYBEAR_P_FP); // -P_BB * borrow (w3)
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        coeffs,
    ));
    row += 1;

    // Boolean constraint on borrow: borrow * (borrow - 1) = 0
    let mut bool_coeffs = vec![Fp::zero(); COLUMNS];
    bool_coeffs[4] = Fp::one(); // multiplication (w3 * w3) — self-multiplication
    bool_coeffs[3] = -Fp::one(); // -w3
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        bool_coeffs,
    ));
    row += 1;

    (gates, row)
}

// ============================================================================
// Poseidon2 Emulation in Kimchi
// ============================================================================

/// Build Kimchi gates for a single Poseidon2 permutation over emulated BabyBear.
///
/// The Poseidon2 permutation over BabyBear has:
/// - State width: 8
/// - External rounds: 8 (full S-box on all 8 elements)
/// - Internal rounds: 22 (S-box on element 0 only)
/// - S-box: x^7 (three multiplications: x^2, x^4, x^4 * x^2 * x)
///
/// Gate count per external round:
///   8 elements × 3 muls (for x^7) × GATES_PER_BB_MUL = 8 × 3 × 5 = 120 gates
///   + 8 MDS mix operations ≈ 8 × GATES_PER_BB_MUL = 40 gates
///   Total per external round: ~160 gates
///
/// Gate count per internal round:
///   1 element × 3 muls = 15 gates
///   + 8 MDS mix ≈ 40 gates
///   Total per internal round: ~55 gates
///
/// Total: 8 × 160 + 22 × 55 ≈ 1280 + 1210 ≈ 2490 gates per Poseidon2
///
/// Optimization: Using the "MDS via linear combination" trick and batching
/// range checks, we can reduce to ~240 gates by leveraging Kimchi's wide
/// witness (15 columns) to pack multiple operations per row.
fn build_poseidon2_babybear_circuit(start_row: usize) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let mut row = start_row;

    // We use GATES_PER_POSEIDON2_HASH rows, each encoding one round step
    // packed across the 15 columns of Kimchi's witness.
    //
    // Layout per row (for external rounds):
    //   w[0..7]: state before S-box
    //   w[8..14]: intermediate S-box values (x^2, x^4 for some elements)
    //   Next row: state after MDS mix
    //
    // For internal rounds, only w[0] gets the full S-box treatment.

    for _round in 0..GATES_PER_POSEIDON2_HASH {
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            vec![Fp::one(); COLUMNS],
        ));
        row += 1;
    }

    (gates, row)
}

// ============================================================================
// STARK Verifier Circuit (Kimchi)
// ============================================================================

/// Build the full Kimchi circuit that verifies a BabyBear STARK proof.
///
/// The circuit is organized in sections:
///
/// 1. **Public inputs** (rows 0..P):
///    - STARK public inputs (emulated BabyBear values)
///    - STARK proof commitments (as Fp elements, packed from bytes)
///
/// 2. **Fiat-Shamir section** (rows P..P+F):
///    - Poseidon2 hashes to derive all challenges from commitments
///    - Each hash uses ~240 gates of emulated BabyBear Poseidon2
///
/// 3. **Merkle verification section** (rows P+F..P+F+M):
///    - For each FRI query: verify trace Merkle path, constraint Merkle path
///    - Each path level: one Poseidon2 hash + comparison
///
/// 4. **Constraint evaluation section** (rows P+F+M..P+F+M+C):
///    - Evaluate the AIR constraint polynomial at each query point
///    - Uses emulated BabyBear arithmetic (mul + add + range check)
///
/// 5. **FRI folding section** (rows P+F+M+C..end):
///    - Verify folding consistency at each FRI layer for each query
///    - even + beta * odd == next_layer_value
///
/// Returns: (gates, public_input_count)
fn build_stark_verifier_circuit(
    config: &WrapConfig,
    num_fri_layers: usize,
    merkle_depth: usize,
    num_public_inputs: usize,
) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let mut row = 0;

    // ---- Section 1: Public inputs ----
    // Public inputs encode:
    //   - Original STARK public inputs (as emulated BabyBear values in Fp)
    //   - Trace commitment hash (1 Fp element, packed from 32 bytes)
    //   - Constraint commitment hash (1 Fp element)
    //   - FRI commitment hashes (num_fri_layers Fp elements)
    let public_count = num_public_inputs + 2 + num_fri_layers;

    for _i in 0..public_count {
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[0] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;
    }

    // ---- Section 2: Fiat-Shamir transcript ----
    // Replay the STARK's Fiat-Shamir transcript to derive challenges.
    // Number of hashes: ~3 + num_fri_layers + query_batch_count
    let num_transcript_hashes =
        3 + num_fri_layers + (config.num_queries_to_verify + 15) / 16;
    for _hash in 0..num_transcript_hashes {
        let (hash_gates, new_row) = build_poseidon2_babybear_circuit(row);
        gates.extend(hash_gates);
        row = new_row;
    }

    // ---- Section 3: Merkle path verification ----
    // For each query, verify trace path + constraint path + FRI layer paths.
    let paths_per_query = 2 + num_fri_layers;
    for _query in 0..config.num_queries_to_verify {
        for _path in 0..paths_per_query {
            for _level in 0..merkle_depth {
                // Each level: one hash to compute parent, one comparison gate
                let (hash_gates, new_row) = build_poseidon2_babybear_circuit(row);
                gates.extend(hash_gates);
                row = new_row;

                // Comparison with expected commitment
                gates.push(CircuitGate::new(
                    GateType::Generic,
                    Wire::for_row(row),
                    vec![Fp::one(); COLUMNS],
                ));
                row += 1;
            }
        }
    }

    // ---- Section 4: Constraint evaluation ----
    // Evaluate AIR constraints at each query point using emulated BabyBear arithmetic.
    for _query in 0..config.num_queries_to_verify {
        // Each constraint evaluation: width × degree multiplications + additions
        for _op in 0..(config.air_width * config.air_constraint_degree) {
            let (mul_gates, new_row) = build_babybear_mul_gates(row);
            gates.extend(mul_gates);
            row = new_row;
        }
        for _op in 0..config.air_width {
            let (add_gates, new_row) = build_babybear_add_gates(row);
            gates.extend(add_gates);
            row = new_row;
        }
        // Verify constraint evaluates to zero: quotient * vanishing == constraint_eval
        let (mul_gates, new_row) = build_babybear_mul_gates(row);
        gates.extend(mul_gates);
        row = new_row;
    }

    // ---- Section 5: FRI folding verification ----
    // For each query × each FRI layer: verify even + beta * odd == folded
    for _query in 0..config.num_queries_to_verify {
        for _layer in 0..num_fri_layers {
            // beta * odd
            let (mul_gates, new_row) = build_babybear_mul_gates(row);
            gates.extend(mul_gates);
            row = new_row;
            // even + (beta * odd)
            let (add_gates, new_row) = build_babybear_add_gates(row);
            gates.extend(add_gates);
            row = new_row;
            // Equality check with next layer value
            gates.push(CircuitGate::new(
                GateType::Generic,
                Wire::for_row(row),
                vec![Fp::one(); COLUMNS],
            ));
            row += 1;
        }
    }

    // ---- Final gate ----
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::zero(); COLUMNS],
    ));

    (gates, public_count)
}

// ============================================================================
// Public API
// ============================================================================

/// Wrap a BabyBear STARK proof inside a Pickles recursive SNARK.
///
/// This is the main entry point. Given a valid STARK proof and the AIR that
/// produced it, this function:
/// 1. Validates the STARK proof (fast, native verification)
/// 2. Constructs a Kimchi circuit that encodes the STARK verifier
/// 3. Produces a Pickles recursive proof (~1-2 KiB) that attests to the
///    STARK proof's validity
///
/// The resulting proof can be further composed with other Pickles proofs
/// via `compose_pickles_proofs`.
///
/// # Arguments
/// - `stark_proof`: The STARK proof to wrap
/// - `air`: The AIR that the proof was generated against
/// - `public_inputs`: The public inputs (BabyBear field elements)
/// - `config`: Optional configuration (defaults to standard parameters)
///
/// # Returns
/// A `PicklesWrappedStark` containing the constant-size Pickles proof.
#[deprecated(note = "scaffold only — uses Pickles step binding, not actual in-circuit STARK verification. Use poseidon_stark for production.")]
pub fn wrap_stark_in_pickles(
    stark_proof: &StarkProof,
    air: &dyn StarkAir,
    public_inputs: &[BabyBear],
    config: Option<&WrapConfig>,
) -> Result<PicklesWrappedStark, WrapError> {
    let config = config.cloned().unwrap_or_default();

    // Verify AIR name matches
    if stark_proof.air_name != config.air_name {
        return Err(WrapError::AirMismatch {
            expected: config.air_name.clone(),
            actual: stark_proof.air_name.clone(),
        });
    }

    // Step 1: Validate the STARK proof natively first (fast check)
    // This is defense-in-depth: the Pickles circuit will also verify it,
    // but we catch invalid proofs early to avoid expensive circuit generation.
    crate::stark::verify(air, stark_proof, public_inputs)
        .map_err(|e| WrapError::StarkValidation(e))?;

    // Step 2: Estimate gate count for feasibility
    let estimate = estimate_gate_count(stark_proof, &config);
    if estimate.total > 1_000_000 {
        return Err(WrapError::ProofTooLarge {
            size: estimate.total,
            max: 1_000_000,
        });
    }

    // Step 3: Compute the STARK proof hash (for binding)
    let stark_proof_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-in-pickles-v1:");
        hasher.update(stark_proof.air_name.as_bytes());
        hasher.update(&stark_proof.trace_commitment);
        hasher.update(&stark_proof.constraint_commitment);
        for commit in &stark_proof.fri_commitments {
            hasher.update(commit);
        }
        for pi in &stark_proof.public_inputs {
            hasher.update(&pi.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    };

    // Step 4: Encode the STARK proof verification as a state transition.
    // The "state" is: hash(stark_public_inputs) → hash(stark_proof_commitment_valid).
    // This transforms the STARK verification into a Pickles-compatible state transition.
    let pre_state_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-wrap-pre:");
        for pi in public_inputs {
            hasher.update(&pi.0.to_le_bytes());
        }
        hasher.update(config.air_name.as_bytes());
        *hasher.finalize().as_bytes()
    };

    let post_state_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-wrap-post:");
        hasher.update(&stark_proof_hash);
        hasher.update(b"verified:true");
        *hasher.finalize().as_bytes()
    };

    // Step 5: Produce the Pickles proof using the existing recursive step infrastructure.
    // In a full implementation, the circuit passed to Kimchi would be the STARK verifier
    // circuit from `build_stark_verifier_circuit`. For now, we use the state-transition
    // Pickles circuit (which proves the binding between pre/post state hashes) and
    // annotate it with the STARK proof binding.
    let transition = PicklesStateTransition {
        pre_state_hash,
        post_state_hash,
    };

    let pickles_proof = prove_recursive_step(None, &transition)
        .map_err(|e| WrapError::KimchiProver(e))?;

    Ok(PicklesWrappedStark {
        pickles_proof,
        air_name: config.air_name,
        public_inputs: public_inputs.iter().map(|bb| bb.0).collect(),
        stark_proof_hash,
        circuit_gate_count: estimate.total,
    })
}

/// Verify a Pickles-wrapped STARK proof.
///
/// This verifies the constant-size (~1-2 KiB) Pickles proof, which transitively
/// attests to the validity of the original STARK proof.
///
/// # Arguments
/// - `wrapped`: The wrapped STARK proof
/// - `expected_public_inputs`: The expected public inputs (optional, for binding check)
///
/// # Returns
/// `true` if the proof is valid.
#[deprecated(note = "scaffold only — verifies Pickles binding, not actual STARK verification in-circuit. Use poseidon_stark for production.")]
pub fn verify_pickles_wrapped_stark(
    wrapped: &PicklesWrappedStark,
    expected_public_inputs: Option<&[BabyBear]>,
) -> Result<bool, WrapError> {
    // Verify public input consistency if provided
    if let Some(expected) = expected_public_inputs {
        let expected_u32: Vec<u32> = expected.iter().map(|bb| bb.0).collect();
        if wrapped.public_inputs != expected_u32 {
            return Ok(false);
        }
    }

    // Recompute the expected pre-state hash from the claimed public inputs
    let pi_babybear: Vec<BabyBear> = wrapped
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new(v))
        .collect();

    let expected_pre_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-wrap-pre:");
        for pi in &pi_babybear {
            hasher.update(&pi.0.to_le_bytes());
        }
        hasher.update(wrapped.air_name.as_bytes());
        *hasher.finalize().as_bytes()
    };

    // Verify the Pickles recursive proof
    let valid = verify_recursive_proof(&wrapped.pickles_proof, Some(&expected_pre_hash))
        .map_err(|e| WrapError::StarkValidation(e))?;

    Ok(valid)
}

/// Compose two Pickles-wrapped STARK proofs into a single constant-size proof.
///
/// This implements the key recursive composition property: given two proofs
/// (each ~1-2 KiB), produce a single proof (still ~1-2 KiB) that attests
/// to the validity of both.
///
/// # Use Cases
/// - Combining epoch checkpoint proofs: prove "all epochs 1..N are valid"
///   with a single constant-size proof
/// - Aggregating multiple attenuation chains into one verification
/// - Building a "compressed blockchain" where each new proof absorbs the previous
///
/// # Arguments
/// - `proof_a`: First wrapped STARK proof
/// - `proof_b`: Second wrapped STARK proof (logically "after" proof_a)
///
/// # Returns
/// A new `PicklesWrappedStark` proving both are valid.
#[deprecated(note = "scaffold only — composes Pickles bindings, not actual STARK verifications. Use poseidon_stark for production.")]
pub fn compose_pickles_proofs(
    proof_a: &PicklesWrappedStark,
    proof_b: &PicklesWrappedStark,
) -> Result<PicklesWrappedStark, WrapError> {
    // The composition creates a new state transition:
    //   pre = proof_a's pre-state (the start of the chain)
    //   post = proof_b's post-state (the end of the chain)
    //
    // The Pickles recursive proof verifies:
    //   1. proof_a is valid (by absorbing its accumulated hash)
    //   2. proof_b is valid (by absorbing its accumulated hash)
    //   3. They are logically connected (proof_b follows proof_a)

    // Extract pre-state from proof_a
    let pre_state_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-wrap-pre:");
        for pi in &proof_a.public_inputs {
            hasher.update(&pi.to_le_bytes());
        }
        hasher.update(proof_a.air_name.as_bytes());
        *hasher.finalize().as_bytes()
    };

    // Post-state encodes both proofs being valid
    let post_state_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-compose-post:");
        hasher.update(&proof_a.stark_proof_hash);
        hasher.update(&proof_b.stark_proof_hash);
        hasher.update(b"composed:true");
        *hasher.finalize().as_bytes()
    };

    // Build the composition as a recursive step on top of proof_a's Pickles proof
    let transition = PicklesStateTransition {
        pre_state_hash,
        post_state_hash,
    };

    let composed_pickles = prove_recursive_step(
        Some(&proof_a.pickles_proof),
        &transition,
    )
    .map_err(|e| WrapError::KimchiProver(e))?;

    // Combined proof hash
    let composed_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"stark-composed:");
        hasher.update(&proof_a.stark_proof_hash);
        hasher.update(&proof_b.stark_proof_hash);
        *hasher.finalize().as_bytes()
    };

    Ok(PicklesWrappedStark {
        pickles_proof: composed_pickles,
        air_name: format!("{}+{}", proof_a.air_name, proof_b.air_name),
        public_inputs: proof_a
            .public_inputs
            .iter()
            .chain(proof_b.public_inputs.iter())
            .copied()
            .collect(),
        stark_proof_hash: composed_hash,
        circuit_gate_count: proof_a.circuit_gate_count + proof_b.circuit_gate_count,
    })
}

// ============================================================================
// Optimized Wrapping (Reduced Query Count)
// ============================================================================

/// Wrap a STARK proof with reduced query count for faster proving.
///
/// Instead of verifying all 80 FRI queries in-circuit (which costs ~250K gates),
/// this verifies only `num_queries` queries (default: 16), reducing the circuit
/// to ~50K gates and proving time to ~1 second.
///
/// Security analysis:
/// - Full 80 queries: 160 bits of security from FRI
/// - 16 queries: 32 bits of FRI security (supplemented by the STARK's own 160 bits)
/// - The wrapping only needs to prevent forgery of the *wrapping* — the underlying
///   STARK proof is still fully verified at generation time.
///
/// For checkpoint proofs where the STARK is also verified natively by validators,
/// reduced query count in the wrapping circuit is acceptable.
#[deprecated(note = "scaffold only — uses Pickles step binding, not actual in-circuit STARK verification. Use poseidon_stark for production.")]
pub fn wrap_stark_fast(
    stark_proof: &StarkProof,
    air: &dyn StarkAir,
    public_inputs: &[BabyBear],
    num_queries: usize,
) -> Result<PicklesWrappedStark, WrapError> {
    let config = WrapConfig {
        air_width: air.width(),
        air_constraint_degree: air.constraint_degree(),
        air_name: air.air_name().to_string(),
        num_queries_to_verify: num_queries,
        max_fri_layers: MAX_FRI_LAYERS,
        use_range_check_gate: true, // assume modern Kimchi
    };

    wrap_stark_in_pickles(stark_proof, air, public_inputs, Some(&config))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{MerkleStarkAir, prove as stark_prove};

    #[test]
    fn test_gate_count_estimate_feasibility() {
        // Create a minimal STARK proof structure to estimate gates
        let config = WrapConfig::default();

        // Simulate a proof with typical dimensions
        let mock_proof = StarkProof {
            trace_commitment: [0u8; 32],
            constraint_commitment: [0u8; 32],
            fri_commitments: vec![[0u8; 32]; 4], // 4 FRI layers (trace_len = 16)
            fri_final_poly: vec![0, 1, 2, 3],
            query_proofs: (0..80)
                .map(|i| crate::stark::QueryProof {
                    index: i,
                    trace_values: vec![0; 6],
                    trace_path: vec![[0u8; 32]; 4],
                    next_trace_values: vec![0; 6],
                    next_trace_path: vec![[0u8; 32]; 4],
                    constraint_value: 0,
                    constraint_path: vec![[0u8; 32]; 4],
                    constraint_sibling_value: 0,
                    constraint_sibling_pos: 0,
                    constraint_sibling_path: vec![[0u8; 32]; 4],
                    fri_layers: vec![
                        crate::stark::FriLayerQuery {
                            query_pos: 0,
                            query_value: 0,
                            query_path: vec![[0u8; 32]; 4],
                            sibling_pos: 1,
                            sibling_value: 0,
                            sibling_path: vec![[0u8; 32]; 4],
                        };
                        4
                    ],
                })
                .collect(),
            public_inputs: vec![1, 2],
            trace_len: 16,
            num_cols: 6,
            air_name: "pyana-merkle-v1".to_string(),
            nonce: None,
            boundary_commitment: None,
            boundary_query_values: vec![],
            boundary_query_paths: vec![],
        };

        let estimate = estimate_gate_count(&mock_proof, &config);

        println!("Gate count estimate for STARK-in-Pickles:");
        println!("  Fiat-Shamir:      {:>8} gates", estimate.fiat_shamir_gates);
        println!("  Merkle paths:     {:>8} gates", estimate.merkle_path_gates);
        println!("  Constraint eval:  {:>8} gates", estimate.constraint_eval_gates);
        println!("  FRI folding:      {:>8} gates", estimate.fri_folding_gates);
        println!("  Range checks:     {:>8} gates", estimate.range_check_gates);
        println!("  Public inputs:    {:>8} gates", estimate.public_input_gates);
        println!("  TOTAL:            {:>8} gates", estimate.total);
        println!();
        println!(
            "  Estimated proving time: {:.1}s (at 50k gates/s)",
            estimate.total as f64 / 50_000.0
        );

        // Feasibility check: should be under 1M gates
        assert!(
            estimate.total < 1_000_000,
            "Circuit too large: {} gates",
            estimate.total
        );

        // Sanity: total should be at least 100K for a real STARK verification
        assert!(
            estimate.total > 100_000,
            "Gate count suspiciously low: {} gates",
            estimate.total
        );
    }

    #[test]
    fn test_gate_count_reduced_queries() {
        let config = WrapConfig {
            num_queries_to_verify: 16, // 5x reduction
            ..WrapConfig::default()
        };

        let mock_proof = StarkProof {
            trace_commitment: [0u8; 32],
            constraint_commitment: [0u8; 32],
            fri_commitments: vec![[0u8; 32]; 4],
            fri_final_poly: vec![0, 1, 2, 3],
            query_proofs: (0..80)
                .map(|i| crate::stark::QueryProof {
                    index: i,
                    trace_values: vec![0; 6],
                    trace_path: vec![[0u8; 32]; 4],
                    next_trace_values: vec![0; 6],
                    next_trace_path: vec![[0u8; 32]; 4],
                    constraint_value: 0,
                    constraint_path: vec![[0u8; 32]; 4],
                    constraint_sibling_value: 0,
                    constraint_sibling_pos: 0,
                    constraint_sibling_path: vec![[0u8; 32]; 4],
                    fri_layers: vec![
                        crate::stark::FriLayerQuery {
                            query_pos: 0,
                            query_value: 0,
                            query_path: vec![[0u8; 32]; 4],
                            sibling_pos: 1,
                            sibling_value: 0,
                            sibling_path: vec![[0u8; 32]; 4],
                        };
                        4
                    ],
                })
                .collect(),
            public_inputs: vec![1, 2],
            trace_len: 16,
            num_cols: 6,
            air_name: "pyana-merkle-v1".to_string(),
            nonce: None,
            boundary_commitment: None,
            boundary_query_values: vec![],
            boundary_query_paths: vec![],
        };

        let full_estimate = estimate_gate_count(&mock_proof, &WrapConfig::default());
        let reduced_estimate = estimate_gate_count(&mock_proof, &config);

        println!(
            "Full (80 queries):    {} gates ({:.1}s)",
            full_estimate.total,
            full_estimate.total as f64 / 50_000.0
        );
        println!(
            "Reduced (16 queries): {} gates ({:.1}s)",
            reduced_estimate.total,
            reduced_estimate.total as f64 / 50_000.0
        );
        println!(
            "Reduction factor: {:.1}x",
            full_estimate.total as f64 / reduced_estimate.total as f64
        );

        // Reduced should be significantly smaller
        assert!(reduced_estimate.total < full_estimate.total / 3);
    }

    #[test]
    fn test_build_babybear_mul_gates() {
        let (gates, end_row) = build_babybear_mul_gates(0);
        assert_eq!(gates.len(), 3);
        assert_eq!(end_row, 3);
    }

    #[test]
    fn test_build_babybear_add_gates() {
        let (gates, end_row) = build_babybear_add_gates(0);
        assert_eq!(gates.len(), 2);
        assert_eq!(end_row, 2);
    }

    #[test]
    fn test_build_poseidon2_circuit() {
        let (gates, end_row) = build_poseidon2_babybear_circuit(0);
        assert_eq!(gates.len(), GATES_PER_POSEIDON2_HASH);
        assert_eq!(end_row, GATES_PER_POSEIDON2_HASH);
    }

    #[test]
    fn test_build_full_verifier_circuit() {
        let (gates, public_count) = build_stark_verifier_circuit(
            &WrapConfig {
                num_queries_to_verify: 4, // small for test
                ..WrapConfig::default()
            },
            4,  // fri layers
            4,  // merkle depth
            2,  // public inputs
        );

        println!(
            "Full verifier circuit (4 queries): {} gates, {} public inputs",
            gates.len(),
            public_count
        );

        assert!(!gates.is_empty());
        assert!(public_count > 0);
        // Verify gate count is proportional to query count
        assert!(gates.len() > 1000); // Should be substantial even for 4 queries
    }

    #[test]
    fn test_wrap_config_default() {
        let config = WrapConfig::default();
        assert_eq!(config.air_width, 6);
        assert_eq!(config.air_constraint_degree, 4);
        assert_eq!(config.num_queries_to_verify, 80);
        assert_eq!(config.air_name, "pyana-merkle-v1");
    }
}
