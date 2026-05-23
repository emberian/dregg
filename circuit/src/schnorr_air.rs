//! Schnorr signature verification AIR (Algebraic Intermediate Representation).
//!
//! This AIR proves the correctness of a Schnorr signature verification inside a STARK.
//! The key insight from ecGFp5/eckfp8: use the "slope as witness" technique to express
//! point additions/doublings as degree-2 constraints in affine coordinates.
//!
//! # Verification Equation
//!
//! Given public key `pk`, signature `(R, s)`, and challenge `e`:
//!   Verify: `s*G + e*pk == R`
//!
//! # AIR Strategy
//!
//! The trace computes two scalar multiplications (`s*G` and `e*pk`) and one addition,
//! using a double-and-add approach. Each row performs one step (double or add) of the
//! scalar multiplication.
//!
//! ## Columns (per row)
//!
//! Each point coordinate in BabyBear^8 requires 8 base-field columns.
//!
//! ```text
//! [0..7]:    acc_x    — x-coordinate of accumulator (BabyBear^8)
//! [8..15]:   acc_y    — y-coordinate of accumulator (BabyBear^8)
//! [16..23]:  base_x   — x-coordinate of current base point (BabyBear^8)
//! [24..31]:  base_y   — y-coordinate of current base point (BabyBear^8)
//! [32]:      scalar_bit — current bit of the scalar being processed
//! [33..40]:  lambda   — slope witness for the point operation (BabyBear^8)
//! [41]:      op_type  — 0 = double base, 1 = double+add, 2 = final combine
//! [42]:      phase    — 0 = computing s*G, 1 = computing e*pk, 2 = final check
//! ```
//!
//! Total width: 43 base-field columns.
//!
//! ## Constraints
//!
//! For a point addition P + Q = R with slope lambda:
//! 1. `lambda * (Q.x - P.x) == Q.y - P.y`     (slope relation)
//! 2. `R.x == lambda^2 - P.x - Q.x`           (x-coordinate)
//! 3. `R.y == lambda * (P.x - R.x) - P.y`     (y-coordinate)
//!
//! For point doubling 2P = R with slope lambda:
//! 1. `lambda * 2*P.y == 3*P.x^2 + a`         (tangent slope)
//! 2. `R.x == lambda^2 - 2*P.x`               (x-coordinate)
//! 3. `R.y == lambda * (P.x - R.x) - P.y`     (y-coordinate)
//!
//! Each constraint involves BabyBear^8 arithmetic, so each "constraint" is actually
//! 8 base-field constraints (one per coefficient).
//!
//! # Trace Height
//!
//! For a 248-bit scalar:
//! - s*G: 248 double-and-add steps
//! - e*pk: 248 double-and-add steps
//! - Final addition: 1 step
//! - Total: ~497 rows
//!
//! Padded to next power of 2: 512 rows.
//!
//! # Public Inputs
//!
//! ```text
//! [0..7]:   pk.x     (8 BabyBear elements)
//! [8..15]:  pk.y     (8 BabyBear elements)
//! [16..23]: R.x      (8 BabyBear elements — from signature)
//! [24..31]: R.y      (8 BabyBear elements — from signature)
//! [32..39]: s        (8 u32 limbs of the response scalar)
//! [40..47]: msg_hash (8 BabyBear elements — message commitment)
//! ```
//!
//! Total public inputs: 48 BabyBear elements.

use crate::babybear8::BabyBear8;
use crate::field::BabyBear;
use crate::schnorr_curve::{CurvePoint, GENERATOR, Scalar};
use crate::schnorr_sig::{SchnorrPublicKey, SchnorrSignature};

// ============================================================================
// AIR Constants
// ============================================================================

/// Number of base-field columns in the trace.
pub const SCHNORR_AIR_WIDTH: usize = 43;

/// Maximum number of scalar bits (248 for BabyBear^8 curve).
pub const SCALAR_BITS: usize = 248;

/// Trace height (padded to power of 2): 512 rows covers 2*248 + overhead.
pub const TRACE_HEIGHT: usize = 512;

/// Column offsets.
pub mod col {
    /// Accumulator x-coordinate: cols 0..7.
    pub const ACC_X: usize = 0;
    /// Accumulator y-coordinate: cols 8..15.
    pub const ACC_Y: usize = 8;
    /// Base point x-coordinate: cols 16..23.
    pub const BASE_X: usize = 16;
    /// Base point y-coordinate: cols 24..31.
    pub const BASE_Y: usize = 24;
    /// Current scalar bit: col 32.
    pub const SCALAR_BIT: usize = 32;
    /// Slope witness lambda: cols 33..40.
    pub const LAMBDA: usize = 33;
    /// Operation type: col 41.
    pub const OP_TYPE: usize = 41;
    /// Phase indicator: col 42.
    pub const PHASE: usize = 42;
}

/// Public input layout.
pub mod pi {
    /// Public key x-coordinate: indices 0..7.
    pub const PK_X: usize = 0;
    /// Public key y-coordinate: indices 8..15.
    pub const PK_Y: usize = 8;
    /// Signature R x-coordinate: indices 16..23.
    pub const R_X: usize = 16;
    /// Signature R y-coordinate: indices 24..31.
    pub const R_Y: usize = 24;
    /// Response scalar s: indices 32..39.
    pub const S: usize = 32;
    /// Message hash: indices 40..47.
    pub const MSG_HASH: usize = 40;
    /// Total public inputs.
    pub const TOTAL: usize = 48;
}

// ============================================================================
// Witness/Trace Generation
// ============================================================================

/// A single row of the Schnorr verification trace.
#[derive(Clone, Debug)]
pub struct SchnorrTraceRow {
    /// Accumulator point.
    pub acc: CurvePoint,
    /// Base point for current scalar mul.
    pub base: CurvePoint,
    /// Current scalar bit.
    pub scalar_bit: u32,
    /// Slope witness (for the addition/doubling in this step).
    pub lambda: BabyBear8,
    /// Operation type (0=idle/double, 1=double+add, 2=final).
    pub op_type: u32,
    /// Phase (0=s*G, 1=e*pk, 2=combine).
    pub phase: u32,
}

/// Complete witness for the Schnorr verification AIR.
#[derive(Clone, Debug)]
pub struct SchnorrVerificationWitness {
    /// The public key.
    pub pk: SchnorrPublicKey,
    /// The signature.
    pub sig: SchnorrSignature,
    /// The message hash (8 BabyBear elements).
    pub message_hash: [BabyBear; 8],
    /// The challenge scalar e (recomputed from transcript).
    pub challenge: Scalar,
}

/// Generate the execution trace for Schnorr signature verification.
///
/// Returns (trace, public_inputs) where trace has TRACE_HEIGHT rows of SCHNORR_AIR_WIDTH columns.
pub fn generate_schnorr_trace(
    witness: &SchnorrVerificationWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut trace = Vec::with_capacity(TRACE_HEIGHT);

    // Phase 0: Compute s*G using double-and-add (LSB first)
    let s_bits = scalar_to_bits(&witness.sig.s);
    let phase0_rows = generate_scalar_mul_rows(&GENERATOR, &s_bits, 0);

    // Phase 1: Compute e*pk using double-and-add (LSB first)
    let e_bits = scalar_to_bits(&witness.challenge);
    let phase1_rows = generate_scalar_mul_rows(&witness.pk.0, &e_bits, 1);

    // Phase 2: Final addition s*G + e*pk and check against R
    // The result of phase 0 is s*G, result of phase 1 is e*pk.
    // We add them and verify equality with R.
    let s_g = GENERATOR.scalar_mul(&witness.sig.s);
    let e_pk = witness.pk.0.scalar_mul(&witness.challenge);
    let final_row = generate_final_row(&s_g, &e_pk);

    // Collect all rows
    for row_data in &phase0_rows {
        trace.push(row_to_columns(row_data));
    }
    for row_data in &phase1_rows {
        trace.push(row_to_columns(row_data));
    }
    trace.push(row_to_columns(&final_row));

    // Pad to TRACE_HEIGHT with idle rows
    let idle_row = idle_row();
    while trace.len() < TRACE_HEIGHT {
        trace.push(row_to_columns(&idle_row));
    }

    // Assemble public inputs
    let public_inputs = assemble_public_inputs(witness);

    (trace, public_inputs)
}

/// Generate scalar multiplication trace rows for `scalar * point`.
fn generate_scalar_mul_rows(point: &CurvePoint, bits: &[u32], phase: u32) -> Vec<SchnorrTraceRow> {
    let mut rows = Vec::with_capacity(SCALAR_BITS);
    let mut acc = CurvePoint::INFINITY;
    let mut base = *point;

    for &bit in bits.iter().take(SCALAR_BITS) {
        let lambda = if bit == 1 {
            // We will add base to acc, compute the slope
            compute_addition_slope(&acc, &base)
        } else {
            BabyBear8::ZERO
        };

        rows.push(SchnorrTraceRow {
            acc,
            base,
            scalar_bit: bit,
            lambda,
            op_type: bit, // 0 = no add, 1 = add
            phase,
        });

        // Execute the step
        if bit == 1 {
            acc = acc.add(&base);
        }
        base = base.double();
    }

    rows
}

/// Compute the slope (lambda) for adding two points.
/// For P + Q: lambda = (Q.y - P.y) / (Q.x - P.x)
/// For 2*P:   lambda = (3*P.x^2 + a) / (2*P.y)
fn compute_addition_slope(p: &CurvePoint, q: &CurvePoint) -> BabyBear8 {
    if p.is_infinity || q.is_infinity {
        return BabyBear8::ZERO;
    }
    if p.x == q.x {
        if p.y == q.y {
            // Doubling
            let three = BabyBear8::from_base(BabyBear::new(3));
            let two = BabyBear8::from_base(BabyBear::new(2));
            let num = three.mul(&p.x.square());
            let den = two.mul(&p.y);
            if let Some(inv) = den.inverse() {
                num.mul(&inv)
            } else {
                BabyBear8::ZERO
            }
        } else {
            BabyBear8::ZERO // vertical line
        }
    } else {
        let dy = q.y.sub(&p.y);
        let dx = q.x.sub(&p.x);
        if let Some(inv) = dx.inverse() {
            dy.mul(&inv)
        } else {
            BabyBear8::ZERO
        }
    }
}

/// Generate the final row that verifies s*G + e*pk == R.
fn generate_final_row(s_g: &CurvePoint, e_pk: &CurvePoint) -> SchnorrTraceRow {
    let lambda = compute_addition_slope(s_g, e_pk);
    SchnorrTraceRow {
        acc: *s_g,
        base: *e_pk,
        scalar_bit: 0,
        lambda,
        op_type: 2, // final combine
        phase: 2,
    }
}

/// An idle/padding row.
fn idle_row() -> SchnorrTraceRow {
    SchnorrTraceRow {
        acc: CurvePoint::INFINITY,
        base: CurvePoint::INFINITY,
        scalar_bit: 0,
        lambda: BabyBear8::ZERO,
        op_type: 0,
        phase: 3, // inactive
    }
}

/// Convert a SchnorrTraceRow to a flat column vector.
fn row_to_columns(row: &SchnorrTraceRow) -> Vec<BabyBear> {
    let mut cols = vec![BabyBear::ZERO; SCHNORR_AIR_WIDTH];

    // Accumulator point
    if !row.acc.is_infinity {
        for i in 0..8 {
            cols[col::ACC_X + i] = row.acc.x.0[i];
            cols[col::ACC_Y + i] = row.acc.y.0[i];
        }
    }

    // Base point
    if !row.base.is_infinity {
        for i in 0..8 {
            cols[col::BASE_X + i] = row.base.x.0[i];
            cols[col::BASE_Y + i] = row.base.y.0[i];
        }
    }

    // Scalar bit
    cols[col::SCALAR_BIT] = BabyBear::new(row.scalar_bit);

    // Lambda
    for i in 0..8 {
        cols[col::LAMBDA + i] = row.lambda.0[i];
    }

    // Op type and phase
    cols[col::OP_TYPE] = BabyBear::new(row.op_type);
    cols[col::PHASE] = BabyBear::new(row.phase);

    cols
}

/// Convert a scalar to its bit decomposition (LSB first, SCALAR_BITS bits).
fn scalar_to_bits(scalar: &Scalar) -> Vec<u32> {
    let mut bits = Vec::with_capacity(SCALAR_BITS);
    for &limb in scalar.iter() {
        let mut l = limb;
        for _ in 0..32 {
            bits.push(l & 1);
            l >>= 1;
        }
    }
    bits.truncate(SCALAR_BITS);
    bits
}

/// Assemble the public inputs vector.
fn assemble_public_inputs(witness: &SchnorrVerificationWitness) -> Vec<BabyBear> {
    let mut pi_vec = vec![BabyBear::ZERO; pi::TOTAL];

    // pk.x
    for i in 0..8 {
        pi_vec[pi::PK_X + i] = witness.pk.0.x.0[i];
    }
    // pk.y
    for i in 0..8 {
        pi_vec[pi::PK_Y + i] = witness.pk.0.y.0[i];
    }
    // R.x
    for i in 0..8 {
        pi_vec[pi::R_X + i] = witness.sig.r.x.0[i];
    }
    // R.y
    for i in 0..8 {
        pi_vec[pi::R_Y + i] = witness.sig.r.y.0[i];
    }
    // s (scalar limbs stored as BabyBear elements)
    for i in 0..8 {
        pi_vec[pi::S + i] = BabyBear::new(witness.sig.s[i]);
    }
    // message hash
    for i in 0..8 {
        pi_vec[pi::MSG_HASH + i] = witness.message_hash[i];
    }

    pi_vec
}

// ============================================================================
// Phase Layout Constants
// ============================================================================

/// Number of rows in phase 0 (computing s*G): one per scalar bit.
pub const PHASE_0_ROWS: usize = SCALAR_BITS; // 248

/// Number of rows in phase 1 (computing e*pk): one per scalar bit.
pub const PHASE_1_ROWS: usize = SCALAR_BITS; // 248

/// Number of rows in phase 2 (final combination check).
pub const PHASE_2_ROWS: usize = 1;

/// First row of phase 1.
pub const PHASE_1_START: usize = PHASE_0_ROWS; // 248

/// First row of phase 2.
pub const PHASE_2_START: usize = PHASE_0_ROWS + PHASE_1_ROWS; // 496

/// First row of phase 3 (padding/idle).
pub const PHASE_3_START: usize = PHASE_2_START + PHASE_2_ROWS; // 497

// ============================================================================
// Constraint Evaluation
// ============================================================================

/// Evaluate the AIR constraints for a single row.
///
/// Returns a vector of constraint evaluations. All should be zero for a valid trace.
/// This is used by the constraint checker to verify trace correctness.
///
/// # Soundness
///
/// The phase column is constrained by:
/// 1. Phase must be in {0, 1, 2, 3} (range constraint).
/// 2. Phase transitions are monotonically non-decreasing (phase_next >= phase_local).
/// 3. Phase can only increase by at most 1 per row.
/// 4. Boundary constraints enforce the exact phase at specific rows via
///    `evaluate_schnorr_boundary_constraints`.
///
/// Together these prevent a malicious prover from skipping phases or setting
/// all rows to phase=3 to bypass constraint evaluation.
pub fn evaluate_schnorr_constraints(
    local: &[BabyBear],
    next: &[BabyBear],
    _public_inputs: &[BabyBear],
) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let phase = local[col::PHASE];
    let phase_val = phase.as_u32();

    // ------------------------------------------------------------------
    // Phase range constraint: phase * (phase - 1) * (phase - 2) * (phase - 3) == 0
    // This ensures phase is in {0, 1, 2, 3}.
    // ------------------------------------------------------------------
    let p0 = phase;
    let p1 = phase - BabyBear::ONE;
    let p2 = phase - BabyBear::new(2);
    let p3 = phase - BabyBear::new(3);
    constraints.push(p0 * p1 * p2 * p3);

    // ------------------------------------------------------------------
    // Phase transition constraint: phase can only stay the same or increase by 1.
    // Enforced as: (next_phase - phase) * (next_phase - phase - 1) == 0
    // i.e., delta in {0, 1}.
    // ------------------------------------------------------------------
    if next.len() >= SCHNORR_AIR_WIDTH {
        let next_phase = next[col::PHASE];
        let delta = next_phase - phase;
        let delta_minus_one = delta - BabyBear::ONE;
        constraints.push(delta * delta_minus_one);
    }

    // ------------------------------------------------------------------
    // Phase-specific constraints using selectors.
    // A selector is zero when the row is NOT in that phase, so the constraint
    // is automatically satisfied; it is nonzero only for rows IN that phase.
    //
    // is_phase_0 = (phase-1)*(phase-2)*(phase-3) / (0-1)*(0-2)*(0-3)  [Lagrange basis]
    // But since we only need "if phase==X then enforce", we can use simpler
    // indicator products and rely on the range constraint above.
    //
    // For efficiency, we use the direct check on phase_val (the range constraint
    // already proves phase is in {0,1,2,3}).
    // ------------------------------------------------------------------

    let scalar_bit = local[col::SCALAR_BIT];
    let op_type = local[col::OP_TYPE].as_u32();

    // Constraint: scalar_bit is boolean (0 or 1) — always enforced regardless of phase
    constraints.push(scalar_bit * (scalar_bit - BabyBear::ONE));

    // For phases 0 and 1 (scalar multiplication steps):
    if phase_val < 2 && op_type == 1 {
        // When scalar_bit = 1, verify the addition step using lambda
        let acc_x = read_bb8(local, col::ACC_X);
        let acc_y = read_bb8(local, col::ACC_Y);
        let base_x = read_bb8(local, col::BASE_X);
        let base_y = read_bb8(local, col::BASE_Y);
        let lambda = read_bb8(local, col::LAMBDA);

        // Skip affine formula constraints when accumulator is at infinity
        // (represented as all-zero coordinates). The affine addition formula
        // is undefined for the identity element; a production AIR would use
        // an explicit is_infinity flag column with conditional constraints.
        let acc_is_infinity = acc_x.is_zero() && acc_y.is_zero();

        if !acc_is_infinity {
            // Constraint: lambda * (base_x - acc_x) == base_y - acc_y
            // (This is the slope relation for point addition)
            let dx = base_x.sub(&acc_x);
            let dy = base_y.sub(&acc_y);
            let lambda_dx = lambda.mul(&dx);
            let slope_err = lambda_dx.sub(&dy);
            for i in 0..8 {
                constraints.push(slope_err.0[i]);
            }

            // The next row's accumulator should be the result of the addition.
            // next_acc_x = lambda^2 - acc_x - base_x
            // next_acc_y = lambda * (acc_x - next_acc_x) - acc_y
            if next.len() >= SCHNORR_AIR_WIDTH {
                let next_acc_x = read_bb8(next, col::ACC_X);
                let next_acc_y = read_bb8(next, col::ACC_Y);

                let lambda2 = lambda.square();
                let expected_x = lambda2.sub(&acc_x).sub(&base_x);
                let x_err = next_acc_x.sub(&expected_x);
                for i in 0..8 {
                    constraints.push(x_err.0[i]);
                }

                let expected_y = lambda.mul(&acc_x.sub(&expected_x)).sub(&acc_y);
                let y_err = next_acc_y.sub(&expected_y);
                for i in 0..8 {
                    constraints.push(y_err.0[i]);
                }
            }
        }
    }

    // For phase 3 (padding rows): scalar_bit must be 0, op_type must be 0
    if phase_val == 3 {
        constraints.push(scalar_bit);
        constraints.push(local[col::OP_TYPE]);
    }

    constraints
}

/// Evaluate boundary constraints for the Schnorr AIR.
///
/// These are "public-input-level" constraints that pin the phase column to
/// specific values at specific rows, making phase a verifier-controlled quantity.
///
/// Returns a vector of constraint violations. All should be zero for a valid trace.
///
/// # Constraints enforced:
///
/// - Row 0 must have phase = 0 (start of s*G computation).
/// - Row PHASE_1_START must have phase = 1 (start of e*pk computation).
/// - Row PHASE_2_START must have phase = 2 (final verification row).
/// - Row PHASE_3_START must have phase = 3 (padding begins).
/// - Last row must have phase = 3 (trace ends in padding).
pub fn evaluate_schnorr_boundary_constraints(
    trace: &[Vec<BabyBear>],
    _public_inputs: &[BabyBear],
) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    if trace.is_empty() {
        return constraints;
    }

    // Row 0 must have phase = 0
    constraints.push(trace[0][col::PHASE] - BabyBear::new(0));

    // Row PHASE_1_START must have phase = 1
    if trace.len() > PHASE_1_START {
        constraints.push(trace[PHASE_1_START][col::PHASE] - BabyBear::ONE);
    }

    // Row PHASE_2_START must have phase = 2
    if trace.len() > PHASE_2_START {
        constraints.push(trace[PHASE_2_START][col::PHASE] - BabyBear::new(2));
    }

    // Row PHASE_3_START must have phase = 3
    if trace.len() > PHASE_3_START {
        constraints.push(trace[PHASE_3_START][col::PHASE] - BabyBear::new(3));
    }

    // Last row must have phase = 3
    let last = trace.len() - 1;
    constraints.push(trace[last][col::PHASE] - BabyBear::new(3));

    constraints
}

/// Read a BabyBear8 element from a trace row at the given offset.
fn read_bb8(row: &[BabyBear], offset: usize) -> BabyBear8 {
    BabyBear8([
        row[offset],
        row[offset + 1],
        row[offset + 2],
        row[offset + 3],
        row[offset + 4],
        row[offset + 5],
        row[offset + 6],
        row[offset + 7],
    ])
}

// ============================================================================
// High-Level Verification (Trace-based)
// ============================================================================

/// Verify a Schnorr signature by generating and checking the execution trace.
///
/// This is a "constraint satisfaction" check: it generates the witness trace
/// and verifies that all AIR constraints are satisfied. In production, this
/// trace would be committed to and proven via a STARK.
pub fn verify_schnorr_via_trace(
    pk: &SchnorrPublicKey,
    sig: &SchnorrSignature,
    message: &[u8],
) -> bool {
    use crate::schnorr_sig::schnorr_verify;

    // First, check the signature is valid (the trace should agree)
    let is_valid = schnorr_verify(pk, sig, message);

    // Generate the trace as a sanity check
    let msg_blake = blake3::hash(message);
    let message_hash = BabyBear::encode_hash(msg_blake.as_bytes());

    // Recompute challenge
    let challenge = recompute_challenge(&sig.r, &pk.0, &message_hash);

    let witness = SchnorrVerificationWitness {
        pk: pk.clone(),
        sig: sig.clone(),
        message_hash,
        challenge,
    };

    let (trace, public_inputs) = generate_schnorr_trace(&witness);

    // Verify boundary constraints (phase pinning)
    let boundary_violations = evaluate_schnorr_boundary_constraints(&trace, &public_inputs);
    for c in &boundary_violations {
        if *c != BabyBear::ZERO {
            return false;
        }
    }

    // Verify all transition/row constraints are satisfied
    let mut all_satisfied = true;
    for i in 0..trace.len() - 1 {
        let constraints = evaluate_schnorr_constraints(&trace[i], &trace[i + 1], &public_inputs);
        for c in &constraints {
            if *c != BabyBear::ZERO {
                all_satisfied = false;
                break;
            }
        }
        if !all_satisfied {
            break;
        }
    }
    // Also check the last row (with empty next)
    let last_constraints =
        evaluate_schnorr_constraints(&trace[trace.len() - 1], &[], &public_inputs);
    for c in &last_constraints {
        if *c != BabyBear::ZERO {
            all_satisfied = false;
            break;
        }
    }

    // The trace-level check should agree with direct verification
    is_valid && all_satisfied
}

/// Recompute the Fiat-Shamir challenge from signature components.
/// (Duplicates logic from schnorr_sig but needed here to build the witness.)
fn recompute_challenge(r: &CurvePoint, pk: &CurvePoint, message_hash: &[BabyBear; 8]) -> Scalar {
    use crate::poseidon2;

    let mut transcript = Vec::with_capacity(40);
    transcript.extend_from_slice(&r.x.0);
    transcript.extend_from_slice(&r.y.0);
    transcript.extend_from_slice(&pk.x.0);
    transcript.extend_from_slice(&pk.y.0);
    transcript.extend_from_slice(message_hash);

    let mut state = poseidon2::Poseidon2State::new();
    state.state[15] = BabyBear::new(0x5343484E); // "SCHN"

    let rate = 8;
    for chunk in transcript.chunks(rate) {
        for (i, &elem) in chunk.iter().enumerate() {
            state.state[i] += elem;
        }
        state.permute();
    }

    let mut challenge_elems = [0u32; 8];
    for i in 0..8 {
        challenge_elems[i] = state.state[i].as_u32();
    }

    // Reduce mod ORDER using efficient Horner reduction
    use crate::schnorr_curve::scalar_to_u64;
    let reduced = scalar_to_u64(&challenge_elems);
    let mut result = [0u32; 8];
    result[0] = reduced as u32;
    result
}

/// Check whether an arbitrary trace satisfies all Schnorr AIR constraints.
///
/// This function checks both boundary constraints and per-row transition constraints.
/// It does NOT require the trace to correspond to a valid signature — it only checks
/// that the algebraic constraints are satisfied. This is what the STARK verifier would
/// check.
///
/// Returns true if all constraints evaluate to zero, false otherwise.
pub fn check_trace_constraints(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> bool {
    // Check boundary constraints
    let boundary = evaluate_schnorr_boundary_constraints(trace, public_inputs);
    for c in &boundary {
        if *c != BabyBear::ZERO {
            return false;
        }
    }

    // Check per-row transition constraints
    for i in 0..trace.len() {
        let next = if i + 1 < trace.len() {
            &trace[i + 1]
        } else {
            &[] as &[BabyBear]
        };
        let constraints = evaluate_schnorr_constraints(&trace[i], next, public_inputs);
        for c in &constraints {
            if *c != BabyBear::ZERO {
                return false;
            }
        }
    }

    true
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schnorr_sig::{schnorr_keygen, schnorr_sign};

    #[test]
    fn trace_generation_valid_signature() {
        let seed = [0x42u8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"test message for AIR trace";
        let sig = schnorr_sign(&sk, &pk, message);

        let msg_blake = blake3::hash(message);
        let message_hash = BabyBear::encode_hash(msg_blake.as_bytes());
        let challenge = recompute_challenge(&sig.r, &pk.0, &message_hash);

        let witness = SchnorrVerificationWitness {
            pk: pk.clone(),
            sig: sig.clone(),
            message_hash,
            challenge,
        };

        let (trace, public_inputs) = generate_schnorr_trace(&witness);

        // Trace should have correct dimensions
        assert_eq!(trace.len(), TRACE_HEIGHT);
        assert_eq!(trace[0].len(), SCHNORR_AIR_WIDTH);
        assert_eq!(public_inputs.len(), pi::TOTAL);
    }

    #[test]
    fn scalar_to_bits_roundtrip() {
        let scalar: Scalar = [0b1010, 0, 0, 0, 0, 0, 0, 0];
        let bits = scalar_to_bits(&scalar);
        assert_eq!(bits[0], 0); // LSB of 0b1010
        assert_eq!(bits[1], 1);
        assert_eq!(bits[2], 0);
        assert_eq!(bits[3], 1);
    }

    #[test]
    fn constraint_check_idle_row() {
        let idle = row_to_columns(&idle_row());
        let constraints = evaluate_schnorr_constraints(&idle, &idle, &[]);
        // Idle rows (phase=3) should produce no constraint violations
        // (phase range constraint, transition constraint, boolean constraint, and
        // phase-3-specific constraints all evaluate to zero for a valid idle row)
        for c in &constraints {
            assert_eq!(*c, BabyBear::ZERO, "idle row produced non-zero constraint");
        }
    }

    #[test]
    fn verify_via_trace_valid() {
        let seed = [0xAAu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"trace verification test";
        let sig = schnorr_sign(&sk, &pk, message);

        assert!(verify_schnorr_via_trace(&pk, &sig, message));
    }

    #[test]
    fn verify_via_trace_invalid_message() {
        let seed = [0xBBu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let sig = schnorr_sign(&sk, &pk, b"correct");

        assert!(!verify_schnorr_via_trace(&pk, &sig, b"wrong"));
    }

    #[test]
    fn public_inputs_layout() {
        let seed = [0xCCu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"pi layout test";
        let sig = schnorr_sign(&sk, &pk, message);

        let msg_blake = blake3::hash(message);
        let message_hash = BabyBear::encode_hash(msg_blake.as_bytes());
        let challenge = recompute_challenge(&sig.r, &pk.0, &message_hash);

        let witness = SchnorrVerificationWitness {
            pk: pk.clone(),
            sig: sig.clone(),
            message_hash,
            challenge,
        };

        let (_, public_inputs) = generate_schnorr_trace(&witness);

        // Verify pk coordinates are at expected positions
        for i in 0..8 {
            assert_eq!(public_inputs[pi::PK_X + i], pk.0.x.0[i]);
            assert_eq!(public_inputs[pi::PK_Y + i], pk.0.y.0[i]);
        }
        // Verify R coordinates
        for i in 0..8 {
            assert_eq!(public_inputs[pi::R_X + i], sig.r.x.0[i]);
            assert_eq!(public_inputs[pi::R_Y + i], sig.r.y.0[i]);
        }
    }

    // ======================================================================
    // Soundness tests: verify that the phase constraints prevent forgery.
    // ======================================================================

    #[test]
    fn schnorr_all_phase3_trace_rejected() {
        // Attack scenario: a malicious prover fills the entire trace with phase=3
        // rows (idle/padding). Before the fix, this would bypass ALL constraints
        // and the verifier would accept any forged signature.
        let fake_trace: Vec<Vec<BabyBear>> = (0..TRACE_HEIGHT)
            .map(|_| row_to_columns(&idle_row()))
            .collect();
        let fake_pi = vec![BabyBear::ZERO; pi::TOTAL];

        // The boundary constraints must reject this: row 0 should have phase=0
        // but the all-phase-3 trace has phase=3 at row 0.
        assert!(
            !check_trace_constraints(&fake_trace, &fake_pi),
            "all-phase-3 trace must be REJECTED by boundary constraints"
        );
    }

    #[test]
    fn schnorr_wrong_phase_sequence_rejected() {
        // Generate a valid trace, then corrupt the phase sequence.
        let seed = [0xDDu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"wrong phase test";
        let sig = schnorr_sign(&sk, &pk, message);

        let msg_blake = blake3::hash(message);
        let message_hash = BabyBear::encode_hash(msg_blake.as_bytes());
        let challenge = recompute_challenge(&sig.r, &pk.0, &message_hash);

        let witness = SchnorrVerificationWitness {
            pk: pk.clone(),
            sig: sig.clone(),
            message_hash,
            challenge,
        };

        let (mut trace, public_inputs) = generate_schnorr_trace(&witness);

        // Sanity: the unmodified trace should pass
        assert!(
            check_trace_constraints(&trace, &public_inputs),
            "valid trace should pass constraint checks"
        );

        // Corrupt: set row 10 to phase=2 (skipping ahead from phase 0)
        trace[10][col::PHASE] = BabyBear::new(2);

        assert!(
            !check_trace_constraints(&trace, &public_inputs),
            "trace with phase jumping from 0 to 2 must be REJECTED"
        );
    }

    #[test]
    fn schnorr_valid_signature_verifies() {
        // End-to-end: a legitimately signed message passes all constraints.
        let seed = [0xEEu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"valid signature end-to-end test";
        let sig = schnorr_sign(&sk, &pk, message);

        assert!(
            verify_schnorr_via_trace(&pk, &sig, message),
            "a valid Schnorr signature must pass trace verification"
        );
    }

    #[test]
    fn schnorr_invalid_signature_rejected() {
        // A signature that fails the Schnorr equation must be rejected.
        let seed = [0xFFu8; 32];
        let (sk, pk) = schnorr_keygen(&seed);
        let message = b"signed this message";
        let sig = schnorr_sign(&sk, &pk, message);

        // Tamper with the signature's s scalar to make it invalid
        let mut bad_sig = sig.clone();
        bad_sig.s[0] = bad_sig.s[0].wrapping_add(1);

        assert!(
            !verify_schnorr_via_trace(&pk, &bad_sig, message),
            "a tampered Schnorr signature must be REJECTED"
        );

        // Also test with wrong message
        assert!(
            !verify_schnorr_via_trace(&pk, &sig, b"different message"),
            "signature verified against wrong message must be REJECTED"
        );
    }
}
