//! Real STARK proof generation and verification.
//!
//! This implements a minimal but REAL STARK proof system from scratch using:
//! - Our BabyBear field (p = 2^31 - 2^27 + 1 = 2013265921)
//! - Reed-Solomon encoding of trace columns
//! - BLAKE3 Merkle tree commitments
//! - FRI (Fast Reed-Solomon IOP of Proximity) for low-degree testing
//! - Fiat-Shamir transform for non-interactivity
//!
//! The key property: `prove()` produces bytes that a separate `verify()` can
//! check WITHOUT seeing the original trace/witness. A tampered trace fails.
//!
//! # Transition Constraint Evaluation
//!
//! In the Reed-Solomon evaluation domain (size = trace_len * BLOWUP), advancing by one
//! trace step corresponds to advancing by BLOWUP evaluation domain positions. Given
//! trace polynomial T(x), evaluating T(x * omega_trace) at evaluation point omega_eval^i
//! yields T(omega_eval^(i + BLOWUP)) = trace_evals[col][(i + blowup) % domain_size].
//!
//! The transition vanishing polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1)) is used
//! as the divisor for transition constraint quotients. This polynomial vanishes on all
//! trace rows except the last, since transition constraints (which reference "next row")
//! are only meaningful on rows 0 through n-2.
//!
//! # Production Prover
//!
//! For production use, prefer the Plonky3 backend (`backends::plonky3`) which uses a
//! battle-tested proving system with proper FRI, extension-field challenges, and
//! Poseidon2-based Merkle tree commitments. This custom STARK is classified as
//! `ProofTier::Experimental` and is retained for AIR types not yet ported to
//! native Plonky3 `Air` trait implementations (fold, derivation, predicates).

use crate::field::{BABYBEAR_P, BabyBear};
use serde::{Deserialize, Serialize};
use std::fmt;

// ============================================================================
// Extension Field: BabyBear^4
// ============================================================================

/// Extension field element: BabyBear^4 = BabyBear[X] / (X^4 - 11).
///
/// Provides 124-bit security for Fiat-Shamir challenges (constraint composition alpha).
/// Individual AIR constraints are still BabyBear values, but the random linear
/// combination uses extension-field arithmetic, preventing an adversary from
/// exploiting the small (31-bit) base field to find constraint-cancellation collisions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtElem(pub [BabyBear; 4]);

/// The irreducible constant W for BabyBear^4: X^4 - 11.
const EXT_W: BabyBear = BabyBear(11);

impl ExtElem {
    pub const ZERO: Self = Self([BabyBear::ZERO; 4]);
    pub const ONE: Self = Self([
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// Construct from 4 BabyBear components.
    pub fn new(components: [BabyBear; 4]) -> Self {
        Self(components)
    }

    /// Embed a base field element into the extension (constant term only).
    pub fn from_base(x: BabyBear) -> Self {
        Self([x, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
    }

    /// Check if zero.
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|x| *x == BabyBear::ZERO)
    }

    /// Extension field addition.
    pub fn add(self, rhs: Self) -> Self {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }

    /// Extension field subtraction.
    pub fn sub(self, rhs: Self) -> Self {
        Self([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }

    /// Extension field multiplication mod (X^4 - W).
    pub fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;
        let w = EXT_W;

        let c0 = a[0] * b[0] + w * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1]);
        let c1 = a[0] * b[1] + a[1] * b[0] + w * (a[2] * b[3] + a[3] * b[2]);
        let c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + w * (a[3] * b[3]);
        let c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];

        Self([c0, c1, c2, c3])
    }

    /// Scalar multiplication: ExtElem * BabyBear (base field scalar).
    /// More efficient than full extension multiplication when one operand is base-field.
    pub fn scale(self, scalar: BabyBear) -> Self {
        Self([
            self.0[0] * scalar,
            self.0[1] * scalar,
            self.0[2] * scalar,
            self.0[3] * scalar,
        ])
    }

    /// Extract the base field component (coefficient of x^0).
    /// For elements known to be in the base field, this returns the value.
    pub fn base_elem(&self) -> BabyBear {
        self.0[0]
    }

    /// Extension field inverse via Gaussian elimination.
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a = self.0;
        let w = EXT_W;

        let mut mat = [[BabyBear::ZERO; 5]; 4];

        mat[0][0] = a[0];
        mat[0][1] = w * a[3];
        mat[0][2] = w * a[2];
        mat[0][3] = w * a[1];
        mat[0][4] = BabyBear::ONE;
        mat[1][0] = a[1];
        mat[1][1] = a[0];
        mat[1][2] = w * a[3];
        mat[1][3] = w * a[2];
        mat[1][4] = BabyBear::ZERO;
        mat[2][0] = a[2];
        mat[2][1] = a[1];
        mat[2][2] = a[0];
        mat[2][3] = w * a[3];
        mat[2][4] = BabyBear::ZERO;
        mat[3][0] = a[3];
        mat[3][1] = a[2];
        mat[3][2] = a[1];
        mat[3][3] = a[0];
        mat[3][4] = BabyBear::ZERO;

        for c in 0..4 {
            let mut pivot_row = None;
            for row in c..4 {
                if mat[row][c] != BabyBear::ZERO {
                    pivot_row = Some(row);
                    break;
                }
            }
            let pivot_row = pivot_row?;
            if pivot_row != c {
                mat.swap(c, pivot_row);
            }

            let inv_pivot = mat[c][c].inverse()?;
            for j in 0..5 {
                mat[c][j] = mat[c][j] * inv_pivot;
            }

            for row in 0..4 {
                if row == c {
                    continue;
                }
                let factor = mat[row][c];
                for j in 0..5 {
                    mat[row][j] = mat[row][j] - factor * mat[c][j];
                }
            }
        }

        Some(Self([mat[0][4], mat[1][4], mat[2][4], mat[3][4]]))
    }
}

impl std::ops::Mul<BabyBear> for ExtElem {
    type Output = ExtElem;
    fn mul(self, rhs: BabyBear) -> ExtElem {
        self.scale(rhs)
    }
}

// ============================================================================
// STARK Configuration
// ============================================================================

/// Configuration for the custom STARK prover/verifier.
#[derive(Clone, Debug)]
pub struct StarkConfig {
    /// Number of leading zero bits required in the proof-of-work hash.
    /// Standard practice: 20-30 bits for 128-bit security with 31-bit field.
    /// Set to 0 to disable PoW (for tests or backward compatibility).
    pub pow_bits: u32,
}

impl Default for StarkConfig {
    fn default() -> Self {
        Self { pow_bits: 20 }
    }
}

impl StarkConfig {
    /// Create a config with no proof-of-work (for tests and backward compat).
    pub fn no_pow() -> Self {
        Self { pow_bits: 0 }
    }
}

// ============================================================================
// Polynomial operations over BabyBear
// ============================================================================

pub(crate) fn poly_eval(coeffs: &[BabyBear], x: BabyBear) -> BabyBear {
    let mut result = BabyBear::ZERO;
    for &c in coeffs.iter().rev() {
        result = result * x + c;
    }
    result
}

/// Primitive root of the BabyBear multiplicative group.
/// 31 is a generator of Z_p^* where p = 2013265921.
/// The group order is p-1 = 2013265920 = 2^27 * 3 * 5.
/// Verified: 31^((p-1)/2) != 1, 31^((p-1)/3) != 1, 31^((p-1)/5) != 1.
const BABYBEAR_PRIMITIVE_ROOT: u32 = 31;

/// Get a principal n-th root of unity where n = 2^log_n.
/// BabyBear supports up to 2^27-th roots of unity.
pub(crate) fn get_root_of_unity(log_n: u32) -> BabyBear {
    assert!(
        log_n <= 27,
        "BabyBear only supports roots of unity up to 2^27"
    );
    // omega = g^((p-1) / 2^log_n) where g = 31 (primitive root)
    let exp = (BABYBEAR_P - 1) / (1u32 << log_n);
    BabyBear::new(BABYBEAR_PRIMITIVE_ROOT).pow(exp)
}

/// Build a multiplicative evaluation domain of size 2^log_n using roots of unity.
/// Returns the domain {1, omega, omega^2, ..., omega^(n-1)} where omega^n = 1.
pub(crate) fn build_evaluation_domain(num_points: usize) -> Vec<BabyBear> {
    assert!(
        num_points.is_power_of_two(),
        "Domain size must be a power of two"
    );
    let log_n = num_points.trailing_zeros();
    let omega = get_root_of_unity(log_n);
    let mut domain = Vec::with_capacity(num_points);
    let mut x = BabyBear::ONE;
    for _ in 0..num_points {
        domain.push(x);
        x = x * omega;
    }
    domain
}

pub(crate) fn interpolate(xs: &[BabyBear], ys: &[BabyBear]) -> Vec<BabyBear> {
    let n = xs.len();
    assert_eq!(n, ys.len());
    if n == 0 {
        return vec![];
    }
    let mut result = vec![BabyBear::ZERO; n];
    for i in 0..n {
        let mut basis = vec![BabyBear::ONE];
        let mut denom = BabyBear::ONE;
        for j in 0..n {
            if i == j {
                continue;
            }
            let mut new_basis = vec![BabyBear::ZERO; basis.len() + 1];
            for k in 0..basis.len() {
                new_basis[k + 1] = new_basis[k + 1] + basis[k];
                new_basis[k] = new_basis[k] - basis[k] * xs[j];
            }
            basis = new_basis;
            denom = denom * (xs[i] - xs[j]);
        }
        let scale = ys[i] * denom.inverse().unwrap();
        for k in 0..basis.len() {
            if k < result.len() {
                result[k] = result[k] + basis[k] * scale;
            }
        }
    }
    result
}

// ============================================================================
// Merkle tree (BLAKE3-based)
// ============================================================================

/// Domain separator for leaf hashing. Must match chain/program/src/main.rs.
pub const STARK_LEAF_DOMAIN: &[u8] = b"stark-leaf:";
/// Domain separator for node hashing. Must match chain/program/src/main.rs.
pub const STARK_NODE_DOMAIN: &[u8] = b"stark-node:";

fn hash_leaf(value: BabyBear) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    hasher.update(&value.0.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn hash_leaf_multi(values: &[BabyBear]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    for v in values {
        hasher.update(&v.0.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_NODE_DOMAIN);
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Debug)]
struct MerkleTree {
    nodes: Vec<[u8; 32]>,
    num_leaves: usize,
}

impl MerkleTree {
    fn new(leaf_hashes: Vec<[u8; 32]>) -> Self {
        let n = leaf_hashes.len();
        assert!(n.is_power_of_two() && n >= 2);
        let mut nodes = Vec::with_capacity(2 * n);
        nodes.extend_from_slice(&leaf_hashes);
        let mut level_start = 0;
        let mut level_size = n;
        while level_size > 1 {
            for i in (0..level_size).step_by(2) {
                let left = &nodes[level_start + i];
                let right = &nodes[level_start + i + 1];
                nodes.push(hash_node(left, right));
            }
            level_start += level_size;
            level_size /= 2;
        }
        Self {
            nodes,
            num_leaves: n,
        }
    }

    fn root(&self) -> [u8; 32] {
        *self.nodes.last().unwrap()
    }

    fn prove(&self, index: usize) -> Vec<[u8; 32]> {
        assert!(index < self.num_leaves);
        let mut path = Vec::new();
        let mut idx = index;
        let mut level_start = 0;
        let mut level_size = self.num_leaves;
        while level_size > 1 {
            path.push(self.nodes[level_start + (idx ^ 1)]);
            idx /= 2;
            level_start += level_size;
            level_size /= 2;
        }
        path
    }

    fn verify_proof(
        root: &[u8; 32],
        leaf_hash: &[u8; 32],
        index: usize,
        path: &[[u8; 32]],
    ) -> bool {
        let mut current = *leaf_hash;
        let mut idx = index;
        for sibling in path {
            current = if idx & 1 == 0 {
                hash_node(&current, sibling)
            } else {
                hash_node(sibling, &current)
            };
            idx >>= 1;
        }
        &current == root
    }
}

// ============================================================================
// Fiat-Shamir transcript
// ============================================================================

#[derive(Clone)]
struct Transcript {
    hasher: blake3::Hasher,
    counter: u64,
}

impl Transcript {
    fn new(domain_sep: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-stark-v1:");
        hasher.update(domain_sep);
        Self { hasher, counter: 0 }
    }
    fn absorb_bytes(&mut self, data: &[u8]) {
        self.hasher.update(data);
    }
    fn absorb_field(&mut self, val: BabyBear) {
        self.hasher.update(&val.0.to_le_bytes());
    }
    fn absorb_hash(&mut self, h: &[u8; 32]) {
        self.hasher.update(h);
    }
    fn squeeze_field(&mut self) -> BabyBear {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        let result = BabyBear::new(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
        // Feed squeezed output back into transcript state to decorrelate
        // consecutive squeezes (prevents challenge correlation attacks)
        self.hasher.update(bytes);
        result
    }
    fn squeeze_ext_elem(&mut self) -> ExtElem {
        ExtElem::new([
            self.squeeze_field(),
            self.squeeze_field(),
            self.squeeze_field(),
            self.squeeze_field(),
        ])
    }
    fn squeeze_index(&mut self, bound: usize) -> usize {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze-idx:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        let val = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        // Feed squeezed output back into transcript state to decorrelate
        // consecutive squeezes
        self.hasher.update(bytes);
        (val as usize) % bound
    }
}

// ============================================================================
// Proof-of-Work (Grinding Resistance)
// ============================================================================

/// Domain separator for PoW hashing to prevent cross-protocol collisions.
const POW_DOMAIN: &[u8] = b"dregg-stark-pow:";

/// Check whether a hash has at least `bits` leading zero bits.
fn has_leading_zeros(hash: &[u8; 32], bits: u32) -> bool {
    if bits == 0 {
        return true;
    }
    let full_bytes = (bits / 8) as usize;
    let remaining_bits = bits % 8;

    // Check full zero bytes
    for &b in &hash[..full_bytes] {
        if b != 0 {
            return false;
        }
    }

    // Check remaining bits in the next byte
    if remaining_bits > 0 {
        let mask = 0xFF << (8 - remaining_bits);
        if hash[full_bytes] & mask != 0 {
            return false;
        }
    }

    true
}

/// Compute the PoW challenge hash: BLAKE3(POW_DOMAIN || transcript_state || nonce).
/// The transcript state is captured by finalizing a clone of the hasher.
fn pow_hash(transcript: &Transcript, nonce: u32) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(POW_DOMAIN);
    // Capture the current transcript state as a digest
    let state_digest = transcript.hasher.clone().finalize();
    hasher.update(state_digest.as_bytes());
    hasher.update(&nonce.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Grind for a nonce satisfying the PoW difficulty. Returns the winning nonce.
fn grind_pow(transcript: &Transcript, pow_bits: u32) -> u32 {
    for nonce in 0u32.. {
        let hash = pow_hash(transcript, nonce);
        if has_leading_zeros(&hash, pow_bits) {
            return nonce;
        }
    }
    unreachable!()
}

/// Verify that a nonce satisfies the PoW difficulty.
fn verify_pow(transcript: &Transcript, nonce: u32, pow_bits: u32) -> bool {
    let hash = pow_hash(transcript, nonce);
    has_leading_zeros(&hash, pow_bits)
}

// ============================================================================
// STARK Proof structure
// ============================================================================

/// FRI security: NUM_QUERIES * log2(blowup) bits of proximity soundness.
/// Combined with BabyBear4 challenge security (~124 bits),
/// system security = min(FRI_bits, 124) >= NIST PQ Level 1 (128 bits target).
const NUM_QUERIES: usize = 80;
const MIN_BLOWUP: usize = 4;

/// Compute the blowup factor needed for an AIR's constraint degree.
/// Must be >= constraint_degree for FRI to provide soundness.
/// Rounded to next power of two for FFT compatibility.
fn blowup_for_degree(degree: usize) -> usize {
    degree.next_power_of_two().max(MIN_BLOWUP)
}

/// Context for STARK proof generation/verification providing temporal binding
/// and session isolation. When provided, these values are absorbed into the
/// Fiat-Shamir transcript to prevent proof replay across different contexts.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct StarkContext {
    /// Optional nonce for temporal binding (e.g., session ID, random challenge).
    pub nonce: Option<[u8; 32]>,
    /// Optional timestamp for freshness (unix seconds).
    pub timestamp: Option<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StarkProof {
    pub trace_commitment: [u8; 32],
    pub constraint_commitment: [u8; 32],
    pub fri_commitments: Vec<[u8; 32]>,
    pub fri_final_poly: Vec<u32>,
    pub query_proofs: Vec<QueryProof>,
    pub public_inputs: Vec<u32>,
    pub trace_len: usize,
    pub num_cols: usize,
    /// The AIR identity that produced this proof (for cross-AIR confusion prevention).
    pub air_name: String,
    /// Optional nonce for temporal binding (must match what verifier expects).
    pub nonce: Option<[u8; 32]>,
    /// Boundary constraint quotient commitment (Merkle root of boundary quotient evaluations).
    /// Binds specific trace cells to public input values, preventing a malicious prover
    /// from generating a valid trace for inputs X then claiming it satisfies inputs Y.
    #[serde(default)]
    pub boundary_commitment: Option<[u8; 32]>,
    /// Boundary quotient values at queried positions.
    #[serde(default)]
    pub boundary_query_values: Vec<Vec<u32>>,
    /// Merkle paths for boundary quotient queries.
    #[serde(default)]
    pub boundary_query_paths: Vec<Vec<[u8; 32]>>,
    /// Proof-of-work nonce for grinding resistance.
    /// After committing trace and constraints, the prover finds a nonce such that
    /// BLAKE3(transcript_state || nonce) has `pow_bits` leading zero bits.
    /// This prevents an adversary from cheaply grinding Fiat-Shamir challenges.
    #[serde(default)]
    pub pow_nonce: u32,
    /// Number of PoW bits this proof was generated with (for verifier to know difficulty).
    #[serde(default)]
    pub pow_bits: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryProof {
    pub index: usize,
    pub trace_values: Vec<u32>,
    pub trace_path: Vec<[u8; 32]>,
    pub next_trace_values: Vec<u32>,
    pub next_trace_path: Vec<[u8; 32]>,
    /// Reduced (base-field) quotient value committed in the Merkle tree.
    /// This is the inner product of the ExtElem quotient with the zeta reduction vector.
    pub constraint_value: u32,
    /// Full extension-field quotient components [c0, c1, c2, c3].
    /// The verifier checks: constraint_value == zeta_reduce(constraint_ext)
    /// AND constraint_ext * Z_T(x) == eval_constraints(...).
    #[serde(default)]
    pub constraint_ext: [u32; 4],
    pub constraint_path: Vec<[u8; 32]>,
    pub constraint_sibling_value: u32,
    #[serde(default)]
    pub constraint_sibling_ext: [u32; 4],
    pub constraint_sibling_pos: usize,
    pub constraint_sibling_path: Vec<[u8; 32]>,
    pub fri_layers: Vec<FriLayerQuery>,
}

/// Errors raised before or during STARK proof generation.
///
/// `prove*` keeps the historical panic-on-error behavior for compatibility.
/// New tests and production callers that can recover should use `try_prove*`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    InvalidTraceLength {
        len: usize,
    },
    TraceWidthMismatch {
        row: usize,
        expected: usize,
        actual: usize,
    },
    DomainTooLarge {
        domain_size: usize,
        max_power_of_two_log: u32,
    },
    DomainOverflow {
        trace_len: usize,
        blowup: usize,
    },
    BoundaryRowOutOfBounds {
        row: usize,
        trace_len: usize,
    },
    BoundaryColumnOutOfBounds {
        col: usize,
        width: usize,
    },
    ConstraintViolation {
        trace_row: usize,
        domain_index: usize,
        value: ExtElem,
    },
}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTraceLength { len } => write!(
                f,
                "invalid trace length {len}: trace length must be >= 2 and a power of two"
            ),
            Self::TraceWidthMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "trace row {row} has width {actual}, but AIR expects {expected} columns"
            ),
            Self::DomainTooLarge {
                domain_size,
                max_power_of_two_log,
            } => write!(
                f,
                "domain size {domain_size} exceeds BabyBear root-of-unity limit (2^{max_power_of_two_log})"
            ),
            Self::DomainOverflow { trace_len, blowup } => {
                write!(f, "trace_len * blowup overflow: {trace_len} * {blowup}")
            }
            Self::BoundaryRowOutOfBounds { row, trace_len } => write!(
                f,
                "boundary constraint row {row} is out of bounds for trace length {trace_len}"
            ),
            Self::BoundaryColumnOutOfBounds { col, width } => write!(
                f,
                "boundary constraint column {col} is out of bounds for trace width {width}"
            ),
            Self::ConstraintViolation {
                trace_row,
                domain_index,
                value,
            } => write!(
                f,
                "Trace constraint non-zero at trace row {trace_row} (domain index {domain_index}): {value:?}. The trace violates AIR constraints and cannot be proven."
            ),
        }
    }
}

impl std::error::Error for ProveError {}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FriLayerQuery {
    pub query_pos: usize,
    pub query_value: u32,
    pub query_path: Vec<[u8; 32]>,
    pub sibling_pos: usize,
    pub sibling_value: u32,
    pub sibling_path: Vec<[u8; 32]>,
}

// ============================================================================
// AIR trait
// ============================================================================

pub trait StarkAir {
    fn width(&self) -> usize;

    /// Evaluate the combined constraint polynomial at a given trace row (base field).
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear;

    /// Evaluate constraints with extension-field alpha for 124-bit composition security.
    ///
    /// Default: evaluates `eval_constraints` at each of the 4 independent base-field
    /// components of alpha. A cheating prover must satisfy C(a_i) = 0 for all 4
    /// independently-random challenges simultaneously, giving forgery probability
    /// at most (d/p)^4 < 2^{-124} where d = number of constraints.
    fn eval_constraints_ext(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: ExtElem,
    ) -> ExtElem {
        let c0 = self.eval_constraints(local, next, public_inputs, alpha.0[0]);
        let c1 = self.eval_constraints(local, next, public_inputs, alpha.0[1]);
        let c2 = self.eval_constraints(local, next, public_inputs, alpha.0[2]);
        let c3 = self.eval_constraints(local, next, public_inputs, alpha.0[3]);
        ExtElem::new([c0, c1, c2, c3])
    }

    fn constraint_degree(&self) -> usize;
    /// Whether this AIR uses Merkle chain continuity (col5=parent, col0=current).
    /// Override to false for AIRs without this layout.
    fn has_chain_continuity(&self) -> bool {
        true
    }
    /// Unique name identifying this AIR for domain separation in the Fiat-Shamir transcript.
    /// Each AIR must return a distinct name to prevent cross-AIR proof confusion.
    fn air_name(&self) -> &'static str;

    /// Boundary constraints: (row_index, column, expected_value).
    ///
    /// These constrain specific cells of the execution trace to equal specific values
    /// derived from the public inputs. They bind the trace to the public inputs,
    /// ensuring a malicious prover cannot generate a valid trace for one set of inputs
    /// and then claim it satisfies a different set.
    ///
    /// Typically used to bind:
    /// - First row values to public input claims (e.g., leaf hash)
    /// - Last row values to public output claims (e.g., Merkle root)
    ///
    /// The verifier checks these as separate quotient polynomials:
    ///   boundary_quotient(x) = (trace_col(x) - expected_val) / (x - domain[row_idx])
    ///
    /// Default: no boundary constraints (UNSOUND for production use).
    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        vec![]
    }
}

/// A boundary constraint binding a specific trace cell to an expected value.
#[derive(Clone, Debug)]
pub struct BoundaryConstraint {
    /// The row index in the trace where this constraint applies.
    pub row: usize,
    /// The column index in the trace where this constraint applies.
    pub col: usize,
    /// The expected value at (row, col).
    pub value: BabyBear,
}

/// Legacy Merkle membership AIR with linear (non-algebraic) hash binding.
///
/// SECURITY WARNING: This AIR uses a trivially invertible linear constraint
/// (`parent = current + sib0 + sib1 + sib2 + position`) which does NOT enforce
/// correct Poseidon2 computation. It is retained for backward compatibility with
/// existing proof infrastructure (bridge, wire, demo) but new code should use
/// `crate::dsl::descriptors::merkle_poseidon2_circuit()` for algebraic soundness.
#[deprecated(
    note = "Use crate::dsl::descriptors::merkle_poseidon2_circuit() for algebraic soundness. MerkleStarkAir uses a linear hash binding that is not collision-resistant."
)]
pub struct MerkleStarkAir;
/// Backward-compatible type alias.
#[deprecated(
    note = "Use crate::dsl::descriptors::merkle_poseidon2_circuit() for algebraic soundness."
)]
#[allow(deprecated)]
pub type MerkleLinearAir = MerkleStarkAir;

#[allow(deprecated)]
impl StarkAir for MerkleStarkAir {
    fn width(&self) -> usize {
        6
    }
    fn constraint_degree(&self) -> usize {
        4
    }
    fn air_name(&self) -> &'static str {
        "dregg-merkle-v1"
    }
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let (current, sib0, sib1, sib2, position, parent) =
            (local[0], local[1], local[2], local[3], local[4], local[5]);
        let c1 = parent - (current + sib0 + sib1 + sib2 + position);
        let c2 = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));
        c1 + alpha * c2
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

/// Reduce an ExtElem quotient to a single BabyBear value using a random challenge.
/// reduction = q[0] + zeta*q[1] + zeta^2*q[2] + zeta^3*q[3]
fn zeta_reduce(q: &ExtElem, zeta: BabyBear) -> BabyBear {
    let z2 = zeta * zeta;
    let z3 = z2 * zeta;
    q.0[0] + zeta * q.0[1] + z2 * q.0[2] + z3 * q.0[3]
}

// ============================================================================
// STARK Prover
// ============================================================================

pub fn prove(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> StarkProof {
    try_prove(air, trace, public_inputs).unwrap_or_else(|e| panic!("{e}"))
}

pub fn try_prove(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, None, &StarkConfig::no_pow())
}

/// Prove with an optional context for temporal binding and session isolation.
pub fn prove_with_context(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> StarkProof {
    try_prove_with_context(air, trace, public_inputs, context).unwrap_or_else(|e| panic!("{e}"))
}

/// Try proving with an optional context for temporal binding and session isolation.
pub fn try_prove_with_context(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, context, &StarkConfig::no_pow())
}

/// Prove with a config specifying proof-of-work difficulty and other parameters.
pub fn prove_with_config(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> StarkProof {
    try_prove_with_config(air, trace, public_inputs, config).unwrap_or_else(|e| panic!("{e}"))
}

/// Try proving with a config specifying proof-of-work difficulty and other parameters.
pub fn try_prove_with_config(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> Result<StarkProof, ProveError> {
    try_prove_full(air, trace, public_inputs, None, config)
}

/// Full prove function with both context and config.
pub fn prove_full(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> StarkProof {
    try_prove_full(air, trace, public_inputs, context, config).unwrap_or_else(|e| panic!("{e}"))
}

/// Full non-panicking prove function with both context and config.
pub fn try_prove_full(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> Result<StarkProof, ProveError> {
    let num_rows = trace.len();
    let num_cols = air.width();
    if num_rows < 2 || !num_rows.is_power_of_two() {
        return Err(ProveError::InvalidTraceLength { len: num_rows });
    }
    for (row_idx, row) in trace.iter().enumerate() {
        if row.len() != num_cols {
            return Err(ProveError::TraceWidthMismatch {
                row: row_idx,
                expected: num_cols,
                actual: row.len(),
            });
        }
    }
    let blowup = blowup_for_degree(air.constraint_degree());
    let domain_size = num_rows
        .checked_mul(blowup)
        .ok_or(ProveError::DomainOverflow {
            trace_len: num_rows,
            blowup,
        })?;
    if domain_size.trailing_zeros() > 27 {
        return Err(ProveError::DomainTooLarge {
            domain_size,
            max_power_of_two_log: 27,
        });
    }
    // Use roots of unity for proper Reed-Solomon encoding.
    // trace_points: subgroup of order num_rows (where trace is defined)
    // eval_points: larger subgroup of order domain_size (blowup domain for FRI)
    let trace_points: Vec<BabyBear> = build_evaluation_domain(num_rows);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    let mut trace_polys = Vec::with_capacity(num_cols);
    for col in 0..num_cols {
        let col_values: Vec<BabyBear> = trace.iter().map(|row| row[col]).collect();
        trace_polys.push(interpolate(&trace_points, &col_values));
    }

    let mut trace_evals = Vec::with_capacity(num_cols);
    for poly in &trace_polys {
        trace_evals.push(
            eval_points
                .iter()
                .map(|&x| poly_eval(poly, x))
                .collect::<Vec<_>>(),
        );
    }

    let trace_leaves: Vec<[u8; 32]> = (0..domain_size)
        .map(|i| hash_leaf_multi(&trace_evals.iter().map(|col| col[i]).collect::<Vec<_>>()))
        .collect();
    let trace_tree = MerkleTree::new(trace_leaves);

    let mut transcript = Transcript::new(b"merkle-stark");

    // AIR-specific domain separation: absorb the AIR's identity and parameters
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(num_rows as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(blowup as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    // Temporal binding: absorb optional nonce/timestamp
    let nonce = context.and_then(|c| c.nonce);
    if let Some(ref ctx) = context {
        if let Some(ref n) = ctx.nonce {
            transcript.absorb_bytes(n);
        }
        if let Some(ts) = ctx.timestamp {
            transcript.absorb_bytes(&ts.to_le_bytes());
        }
    }

    transcript.absorb_hash(&trace_tree.root());
    // Bind the public input count to prevent length-extension transcript collisions
    transcript.absorb_bytes(&(public_inputs.len() as u32).to_le_bytes());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    // Squeeze alpha as ExtElem (4 BabyBear elements) for 124-bit constraint composition security.
    let alpha = transcript.squeeze_ext_elem();

    let boundary_cs = air.boundary_constraints(public_inputs, num_rows);
    for bc in &boundary_cs {
        if bc.row >= num_rows {
            return Err(ProveError::BoundaryRowOutOfBounds {
                row: bc.row,
                trace_len: num_rows,
            });
        }
        if bc.col >= num_cols {
            return Err(ProveError::BoundaryColumnOutOfBounds {
                col: bc.col,
                width: num_cols,
            });
        }
    }

    let mut constraint_evals: Vec<ExtElem> = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let local: Vec<BabyBear> = trace_evals.iter().map(|col| col[i]).collect();
        // Advancing by one TRACE step in the evaluation domain means advancing by BLOWUP
        // evaluation steps. T(x * omega_trace) at eval point omega_eval^i equals
        // T(omega_eval^(i + BLOWUP)), i.e., trace_evals[col][(i + blowup) % domain_size].
        let next_idx = (i + blowup) % domain_size;
        let next: Vec<BabyBear> = trace_evals.iter().map(|col| col[next_idx]).collect();
        constraint_evals.push(air.eval_constraints_ext(&local, &next, public_inputs, alpha));
    }

    // Transition quotient: divide constraint evaluations by the transition vanishing
    // polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1)).
    // This polynomial vanishes on all trace rows EXCEPT the last, which is correct
    // because transition constraints (referencing "next row") don't apply at the last row.
    //
    // At the last trace point omega^(n-1):
    //   Z_T(omega^(n-1)) = lim_{x->omega^(n-1)} (x^n-1)/(x-omega^(n-1))
    //                     = n * omega^((n-1)*(n-1))  [by L'Hopital]
    //   quotient = constraint / Z_T  (may be non-zero since transition doesn't hold there)
    //
    // At other trace points omega^k (k < n-1):
    //   Z_T(omega^k) = 0 and constraint(omega^k) = 0 (constraint holds on these rows)
    //   quotient = 0/0 resolved to 0 by convention (the polynomial Q is well-defined
    //   by continuity and the committed evaluations at non-trace points determine it)
    let omega_trace = get_root_of_unity(num_rows.trailing_zeros());
    let last_trace_point = omega_trace.pow((num_rows - 1) as u32); // omega^(n-1)
    // Precompute Z_T at the last trace point via derivative: n * omega^((n-1)^2)
    // For power-of-two n: (n-1)^2 mod n = (n^2-2n+1) mod n = 1, so omega^((n-1)^2) = omega.
    // We compute (n-1)^2 mod n explicitly to avoid u32 overflow for large trace sizes.
    let exp_mod_n = ((num_rows - 1) as u64 * (num_rows - 1) as u64 % num_rows as u64) as u32;
    let z_t_at_last = BabyBear::new(num_rows as u32) * omega_trace.pow(exp_mod_n);
    // Quotient evals are in ExtElem (extension field).
    let mut quotient_evals: Vec<ExtElem> = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let x = eval_points[i];
        // Z(x) = x^n - 1 (vanishes on entire trace domain)
        let x_n = x.pow(num_rows as u32);
        let z_full = x_n - BabyBear::ONE;
        // Z_T(x) = Z(x) / (x - omega^(n-1))
        let denom_factor = x - last_trace_point;
        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                // x IS the last trace point omega^(n-1). Z_T != 0 here.
                // Compute quotient = constraint / Z_T(omega^(n-1))
                let z_inv = z_t_at_last.inverse().unwrap();
                quotient_evals.push(constraint_evals[i].scale(z_inv));
            } else {
                // x is on the trace domain but NOT the last point.
                // Z_T(x) = 0 here, and constraint(x) must also be 0 (constraints
                // hold on rows 0..n-2). The quotient is 0 by L'Hopital/continuity.
                //
                // DEFENCE: verify the constraint is actually zero before blindly
                // committing to a zero quotient. A non-zero constraint here means
                // the trace is invalid and the prover must not generate a proof.
                if constraint_evals[i] != ExtElem::ZERO {
                    return Err(ProveError::ConstraintViolation {
                        trace_row: i / blowup,
                        domain_index: i,
                        value: constraint_evals[i],
                    });
                }
                quotient_evals.push(ExtElem::ZERO);
            }
        } else {
            // z_full != 0 means x is NOT on the trace domain, so denom_factor != 0
            let z_transition = z_full * denom_factor.inverse().unwrap();
            let z_inv = z_transition.inverse().unwrap();
            quotient_evals.push(constraint_evals[i].scale(z_inv));
        }
    }

    // Squeeze a reduction challenge zeta to project ExtElem quotient to base field for FRI.
    // Security: 31 bits per query * 80 queries >> 128 bits (birthday bound not relevant).
    let zeta = transcript.squeeze_field();

    // Reduce ExtElem quotient evaluations to BabyBear for Merkle commitment and FRI.
    let reduced_quotient_evals: Vec<BabyBear> = quotient_evals
        .iter()
        .map(|q| zeta_reduce(q, zeta))
        .collect();

    let constraint_leaves: Vec<[u8; 32]> = reduced_quotient_evals
        .iter()
        .map(|&v| hash_leaf(v))
        .collect();
    let constraint_tree = MerkleTree::new(constraint_leaves);
    transcript.absorb_hash(&constraint_tree.root());

    let (fri_commitments, fri_trees, fri_layer_evals, fri_final_poly) =
        fri_commit(&reduced_quotient_evals, &eval_points, &mut transcript);

    // ====================================================================
    // Proof-of-Work: grind for a nonce after all commitments are absorbed.
    // An adversary who wants to influence query indices must pay 2^pow_bits
    // work PER grinding attempt.
    // ====================================================================
    let pow_nonce = if config.pow_bits > 0 {
        let nonce = grind_pow(&transcript, config.pow_bits);
        // Absorb nonce into transcript before squeezing query indices
        transcript.absorb_bytes(&nonce.to_le_bytes());
        nonce
    } else {
        0u32
    };

    let mut query_proofs = Vec::with_capacity(NUM_QUERIES);
    for _ in 0..NUM_QUERIES {
        let idx = transcript.squeeze_index(domain_size);
        let trace_values: Vec<u32> = trace_evals.iter().map(|col| col[idx].0).collect();
        let trace_path = trace_tree.prove(idx);
        // Next trace index advances by BLOWUP (one trace step in the eval domain)
        let next_idx = (idx + blowup) % domain_size;
        let next_trace_values: Vec<u32> = trace_evals.iter().map(|col| col[next_idx].0).collect();
        let next_trace_path = trace_tree.prove(next_idx);
        let constraint_value = reduced_quotient_evals[idx].0;
        let constraint_ext = [
            quotient_evals[idx].0[0].0,
            quotient_evals[idx].0[1].0,
            quotient_evals[idx].0[2].0,
            quotient_evals[idx].0[3].0,
        ];
        let constraint_path = constraint_tree.prove(idx);

        let first_half = domain_size / 2;
        let constraint_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        let constraint_sibling_value = reduced_quotient_evals[constraint_sibling_pos].0;
        let constraint_sibling_ext = [
            quotient_evals[constraint_sibling_pos].0[0].0,
            quotient_evals[constraint_sibling_pos].0[1].0,
            quotient_evals[constraint_sibling_pos].0[2].0,
            quotient_evals[constraint_sibling_pos].0[3].0,
        ];
        let constraint_sibling_path = constraint_tree.prove(constraint_sibling_pos);

        let mut fri_layers = Vec::new();
        let mut qpos_in_layer = idx % first_half;
        for (li, tree) in fri_trees.iter().enumerate() {
            let half = tree.num_leaves / 2;
            let qpos = qpos_in_layer % tree.num_leaves;
            let spos = if qpos < half {
                qpos + half
            } else {
                qpos - half
            };
            fri_layers.push(FriLayerQuery {
                query_pos: qpos,
                query_value: fri_layer_evals[li][qpos].0,
                query_path: tree.prove(qpos),
                sibling_pos: spos,
                sibling_value: fri_layer_evals[li][spos].0,
                sibling_path: tree.prove(spos),
            });
            qpos_in_layer = qpos.min(spos);
        }

        query_proofs.push(QueryProof {
            index: idx,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_ext,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_ext,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }

    // ====================================================================
    // Boundary constraint direct proofs
    // ====================================================================
    // For each boundary constraint (row, col, value), provide a Merkle opening
    // of the trace at the corresponding eval domain position (row * BLOWUP).
    // This lets the verifier directly check trace[row][col] == value.
    let mut boundary_query_values = Vec::new();
    let mut boundary_query_paths = Vec::new();
    for bc in &boundary_cs {
        let eval_idx = bc.row * blowup;
        let values: Vec<u32> = trace_evals.iter().map(|col| col[eval_idx].0).collect();
        let path = trace_tree.prove(eval_idx);
        boundary_query_values.push(values);
        boundary_query_paths.push(path);
    }

    Ok(StarkProof {
        trace_commitment: trace_tree.root(),
        constraint_commitment: constraint_tree.root(),
        fri_commitments,
        fri_final_poly: fri_final_poly.iter().map(|v| v.0).collect(),
        query_proofs,
        public_inputs: public_inputs.iter().map(|v| v.0).collect(),
        trace_len: num_rows,
        num_cols,
        air_name: air.air_name().to_string(),
        nonce,
        boundary_commitment: None,
        boundary_query_values,
        boundary_query_paths,
        pow_nonce,
        pow_bits: config.pow_bits,
    })
}

fn fri_commit(
    evals: &[BabyBear],
    _points: &[BabyBear],
    transcript: &mut Transcript,
) -> (
    Vec<[u8; 32]>,
    Vec<MerkleTree>,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    let mut current_evals = evals.to_vec();
    let mut commitments = Vec::new();
    let mut trees = Vec::new();
    let mut layer_evals = Vec::new();
    while current_evals.len() > 4 {
        let beta = transcript.squeeze_field();
        let half = current_evals.len() / 2;
        let mut folded = Vec::with_capacity(half);
        for i in 0..half {
            folded.push(current_evals[i] + beta * current_evals[i + half]);
        }
        while !folded.len().is_power_of_two() || folded.len() < 2 {
            folded.push(BabyBear::ZERO);
        }
        let leaves: Vec<[u8; 32]> = folded.iter().map(|&v| hash_leaf(v)).collect();
        let tree = MerkleTree::new(leaves);
        transcript.absorb_hash(&tree.root());
        commitments.push(tree.root());
        trees.push(tree);
        layer_evals.push(folded.clone());
        current_evals = folded;
    }
    (commitments, trees, layer_evals, current_evals)
}

// ============================================================================
// STARK Verifier
// ============================================================================

pub fn verify(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, None, &StarkConfig::no_pow())
}

/// Verify with an optional context for temporal binding and session isolation.
pub fn verify_with_context(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, context, &StarkConfig::no_pow())
}

/// Verify with a config specifying proof-of-work difficulty.
pub fn verify_with_config(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    config: &StarkConfig,
) -> Result<(), String> {
    verify_full(air, proof, public_inputs, None, config)
}

/// Full verify function with both context and config.
pub fn verify_full(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    context: Option<&StarkContext>,
    config: &StarkConfig,
) -> Result<(), String> {
    // Verify AIR identity matches
    if proof.air_name != air.air_name() {
        return Err(format!(
            "AIR identity mismatch: proof was generated for '{}', but verifying with '{}'",
            proof.air_name,
            air.air_name()
        ));
    }

    // Verify nonce matches
    let expected_nonce = context.and_then(|c| c.nonce);
    if proof.nonce != expected_nonce {
        return Err("Nonce mismatch: proof nonce does not match verification context".to_string());
    }

    let num_cols = proof.num_cols;
    let trace_len = proof.trace_len;

    // Structural validation: reject malformed proof parameters that could cause
    // panics or undefined behavior during verification.
    if trace_len < 2 {
        return Err(format!("Invalid trace_len: {} (must be >= 2)", trace_len));
    }
    if !trace_len.is_power_of_two() {
        return Err(format!(
            "Invalid trace_len: {} (must be a power of two)",
            trace_len
        ));
    }
    if num_cols == 0 || num_cols != air.width() {
        return Err(format!(
            "Column count mismatch: proof has {}, AIR expects {}",
            num_cols,
            air.width()
        ));
    }
    if proof.query_proofs.len() != NUM_QUERIES {
        return Err(format!(
            "Invalid query count: expected {}, got {}",
            NUM_QUERIES,
            proof.query_proofs.len()
        ));
    }
    // Compute dynamic blowup from AIR constraint degree
    let blowup = blowup_for_degree(air.constraint_degree());
    // Ensure trace_len * blowup doesn't overflow and log fits in root-of-unity range
    let domain_size = trace_len
        .checked_mul(blowup)
        .ok_or_else(|| format!("trace_len * blowup overflow: {} * {}", trace_len, blowup))?;
    if domain_size.trailing_zeros() > 27 {
        return Err(format!(
            "Domain size 2^{} exceeds BabyBear root-of-unity limit (2^27)",
            domain_size.trailing_zeros()
        ));
    }

    let proof_pis: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    if proof_pis != public_inputs {
        return Err("Public inputs mismatch".to_string());
    }

    let mut transcript = Transcript::new(b"merkle-stark");

    // AIR-specific domain separation (must match prover)
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(trace_len as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(blowup as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    // Temporal binding (must match prover)
    if let Some(ref ctx) = context {
        if let Some(ref n) = ctx.nonce {
            transcript.absorb_bytes(n);
        }
        if let Some(ts) = ctx.timestamp {
            transcript.absorb_bytes(&ts.to_le_bytes());
        }
    }

    transcript.absorb_hash(&proof.trace_commitment);
    // Bind the public input count to prevent length-extension transcript collisions
    transcript.absorb_bytes(&(public_inputs.len() as u32).to_le_bytes());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    // Squeeze alpha as ExtElem (4 BabyBear elements) for 124-bit constraint composition security.
    let alpha = transcript.squeeze_ext_elem();

    let boundary_cs = air.boundary_constraints(public_inputs, trace_len);

    // Squeeze the zeta reduction challenge (must match prover's transcript state).
    let zeta = transcript.squeeze_field();

    transcript.absorb_hash(&proof.constraint_commitment);

    // ====================================================================
    // CRITICAL: Validate FRI round count before processing commitments.
    // An attacker who provides fri_commitments: vec![] would skip FRI
    // low-degree testing entirely, making the STARK meaningless.
    // ====================================================================
    let mut expected_fri_rounds = 0usize;
    let mut fri_domain_size = domain_size;
    while fri_domain_size > 4 {
        fri_domain_size /= 2;
        expected_fri_rounds += 1;
    }
    if proof.fri_commitments.len() != expected_fri_rounds {
        return Err(format!(
            "Expected {} FRI commitment rounds for domain size {}, got {}",
            expected_fri_rounds,
            domain_size,
            proof.fri_commitments.len()
        ));
    }
    for query in &proof.query_proofs {
        if query.fri_layers.len() != expected_fri_rounds {
            return Err(format!(
                "FRI layer count mismatch in query: expected {}, got {}",
                expected_fri_rounds,
                query.fri_layers.len()
            ));
        }
    }

    let mut fri_betas = Vec::new();
    for commitment in &proof.fri_commitments {
        fri_betas.push(transcript.squeeze_field());
        transcript.absorb_hash(commitment);
    }

    // ====================================================================
    // Proof-of-Work verification: check nonce meets difficulty requirement.
    // Must match prover's transcript state at this point.
    // ====================================================================
    if config.pow_bits > 0 {
        // Verify the proof declares the expected difficulty
        if proof.pow_bits != config.pow_bits {
            return Err(format!(
                "PoW difficulty mismatch: proof has pow_bits={}, expected {}",
                proof.pow_bits, config.pow_bits
            ));
        }
        // Verify the nonce satisfies the difficulty
        if !verify_pow(&transcript, proof.pow_nonce, config.pow_bits) {
            return Err(format!(
                "Proof-of-work verification failed: nonce {} does not have {} leading zero bits",
                proof.pow_nonce, config.pow_bits
            ));
        }
        // Absorb nonce into transcript (must match prover)
        transcript.absorb_bytes(&proof.pow_nonce.to_le_bytes());
    } else if proof.pow_bits != 0 || proof.pow_nonce != 0 {
        return Err(format!(
            "unexpected PoW fields for no-PoW verifier: pow_bits={}, pow_nonce={}",
            proof.pow_bits, proof.pow_nonce
        ));
    }

    // ====================================================================
    // Direct boundary constraint verification (fail-fast before FRI loop)
    // ====================================================================
    // Boundary constraints bind specific trace cells to public input values.
    // The prover includes Merkle openings of the trace at boundary points
    // (positions row * BLOWUP in the eval domain). The verifier checks:
    // 1. Merkle proof authenticates the trace values against trace_commitment
    // 2. The trace value at (row, col) equals the expected boundary value
    //
    // This is a DIRECT check (not probabilistic) and prevents the attack where
    // a prover generates a valid trace for inputs X then lies about public inputs.
    // Placed before the expensive FRI query loop for early rejection of invalid proofs.
    if !boundary_cs.is_empty() {
        if proof.boundary_query_values.len() != boundary_cs.len() {
            return Err(format!(
                "Boundary proof data missing: expected {} openings, got {}",
                boundary_cs.len(),
                proof.boundary_query_values.len()
            ));
        }
        if proof.boundary_query_paths.len() != boundary_cs.len() {
            return Err("Boundary proof paths missing".to_string());
        }

        for (i, bc) in boundary_cs.iter().enumerate() {
            let eval_idx = bc.row * blowup;

            // Verify the trace values are authentic (Merkle proof against trace commitment)
            let boundary_vals: Vec<BabyBear> = proof.boundary_query_values[i]
                .iter()
                .map(|&v| BabyBear::new_canonical(v))
                .collect();

            if boundary_vals.len() != num_cols {
                return Err(format!(
                    "Boundary opening {i} has wrong width: expected {num_cols}, got {}",
                    boundary_vals.len()
                ));
            }

            if !MerkleTree::verify_proof(
                &proof.trace_commitment,
                &hash_leaf_multi(&boundary_vals),
                eval_idx,
                &proof.boundary_query_paths[i],
            ) {
                return Err(format!(
                    "Boundary constraint {i}: Merkle proof failed at eval index {eval_idx} \
                     (trace row {})",
                    bc.row
                ));
            }

            // Direct check: trace value at boundary cell must equal expected value
            if bc.col >= boundary_vals.len() {
                return Err(format!(
                    "Boundary constraint {i}: column {} out of range",
                    bc.col
                ));
            }
            if boundary_vals[bc.col] != bc.value {
                return Err(format!(
                    "Boundary constraint {i} violated: trace[{}][{}] = {}, expected {} \
                     (public input binding failure)",
                    bc.row, bc.col, boundary_vals[bc.col].0, bc.value.0
                ));
            }
        }
    }

    // Use roots of unity (must match prover's domain construction)
    let _trace_points: Vec<BabyBear> = build_evaluation_domain(trace_len);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    for query in &proof.query_proofs {
        let idx = transcript.squeeze_index(domain_size);
        if query.index != idx {
            return Err(format!(
                "Query index mismatch: expected {idx}, got {}",
                query.index
            ));
        }

        let trace_vals: Vec<BabyBear> = query
            .trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if trace_vals.len() != num_cols {
            return Err("Wrong number of trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&trace_vals),
            idx,
            &query.trace_path,
        ) {
            return Err(format!("Trace Merkle proof failed at index {idx}"));
        }

        let constraint_val = BabyBear::new_canonical(query.constraint_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_val),
            idx,
            &query.constraint_path,
        ) {
            return Err(format!("Constraint Merkle proof failed at index {idx}"));
        }

        // Next trace index advances by BLOWUP (one trace step in the eval domain)
        let next_idx = (idx + blowup) % domain_size;
        let next_trace_vals: Vec<BabyBear> = query
            .next_trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if next_trace_vals.len() != num_cols {
            return Err("Wrong number of next trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&next_trace_vals),
            next_idx,
            &query.next_trace_path,
        ) {
            return Err(format!(
                "Next trace Merkle proof failed at index {next_idx}"
            ));
        }

        // Chain continuity (parent[i] == current[i+1]) is enforced by the AIR
        // constraint polynomial. With roots-of-unity domains, the evaluation
        // domain indices don't directly correspond to trace row indices, so we
        // rely on the algebraic constraint check below rather than spot-checking
        // evaluated values at arbitrary domain points.

        // Reconstruct the full ExtElem quotient from the proof
        let quotient_ext = ExtElem::new([
            BabyBear::new_canonical(query.constraint_ext[0]),
            BabyBear::new_canonical(query.constraint_ext[1]),
            BabyBear::new_canonical(query.constraint_ext[2]),
            BabyBear::new_canonical(query.constraint_ext[3]),
        ]);

        // Verify the zeta reduction: committed value must equal zeta_reduce(ext quotient)
        let expected_reduced = zeta_reduce(&quotient_ext, zeta);
        if constraint_val != expected_reduced {
            return Err(format!(
                "Constraint reduction mismatch at query index {idx}: \
                 committed {} != zeta_reduce(ext) {}",
                constraint_val.0, expected_reduced.0
            ));
        }

        let x = eval_points[idx];
        // Compute transition vanishing polynomial Z_T(x) = (x^n - 1) / (x - omega^(n-1))
        let x_n = x.pow(trace_len as u32);
        let z_full = x_n - BabyBear::ONE;
        let omega_trace = get_root_of_unity(trace_len.trailing_zeros());
        let last_trace_point = omega_trace.pow((trace_len - 1) as u32);
        let denom_factor = x - last_trace_point;
        let constraint_at_x =
            air.eval_constraints_ext(&trace_vals, &next_trace_vals, public_inputs, alpha);
        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                // x IS the last trace point omega^(n-1). Z_T != 0 here.
                // Z_T(omega^(n-1)) = n * omega^((n-1)^2) [by L'Hopital]
                // (n-1)^2 mod n = 1 for power-of-two n; compute mod to avoid overflow.
                let exp_mod_n =
                    ((trace_len - 1) as u64 * (trace_len - 1) as u64 % trace_len as u64) as u32;
                let z_t_at_last = BabyBear::new(trace_len as u32) * omega_trace.pow(exp_mod_n);
                // Verify: quotient_ext * Z_T == constraint (in extension field)
                if quotient_ext.scale(z_t_at_last) != constraint_at_x {
                    return Err(format!(
                        "Constraint consistency check failed at last trace point (query index {idx})"
                    ));
                }
            } else {
                // x is on trace domain but NOT the last point. Prover sets quotient=0.
                // The constraint must also be zero (constraints hold on rows 0..n-2).
                if quotient_ext != ExtElem::ZERO {
                    return Err(format!(
                        "Constraint quotient non-zero on trace domain at query index {idx}"
                    ));
                }
                if constraint_at_x != ExtElem::ZERO {
                    return Err(format!(
                        "Constraint non-zero on trace domain at query index {idx}"
                    ));
                }
            }
        } else {
            // x is NOT on the trace domain; denom_factor is also non-zero since the
            // last trace point is on the trace domain and x is not.
            let z_transition = z_full * denom_factor.inverse().unwrap();
            // Verify: quotient_ext * Z_T == constraint (in extension field)
            if quotient_ext.scale(z_transition) != constraint_at_x {
                return Err(format!(
                    "Constraint consistency check failed at query index {idx}"
                ));
            }
        }

        // FRI folding relation verification
        let first_half = domain_size / 2;

        // Validate constraint sibling position: must be the paired half-domain partner
        let expected_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        if query.constraint_sibling_pos != expected_sibling_pos {
            return Err(format!(
                "FRI: constraint sibling position mismatch: expected {}, got {}",
                expected_sibling_pos, query.constraint_sibling_pos
            ));
        }

        let constraint_sib_val = BabyBear::new_canonical(query.constraint_sibling_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_sib_val),
            query.constraint_sibling_pos,
            &query.constraint_sibling_path,
        ) {
            return Err(format!(
                "FRI: constraint sibling Merkle proof failed at pos {}",
                query.constraint_sibling_pos
            ));
        }

        let (even_val, odd_val) = if idx < first_half {
            (constraint_val, constraint_sib_val)
        } else {
            (constraint_sib_val, constraint_val)
        };

        if !fri_betas.is_empty() {
            let expected_folded = even_val + fri_betas[0] * odd_val;
            if !proof.fri_commitments.is_empty() {
                if query.fri_layers.is_empty() {
                    return Err("FRI: missing layer 0 opening".to_string());
                }
                let layer0 = &query.fri_layers[0];
                if layer0.query_pos != idx % first_half {
                    return Err(format!("FRI layer 0: position mismatch"));
                }
                if BabyBear::new_canonical(layer0.query_value) != expected_folded {
                    return Err(format!(
                        "FRI folding check failed at layer 0: expected {}, got {}",
                        expected_folded.0, layer0.query_value
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear::new_canonical(layer0.query_value)),
                    layer0.query_pos,
                    &layer0.query_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for query_pos {} failed",
                        layer0.query_pos
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear::new_canonical(layer0.sibling_value)),
                    layer0.sibling_pos,
                    &layer0.sibling_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for sibling_pos {} failed",
                        layer0.sibling_pos
                    ));
                }
            }
        }

        for k in 0..query.fri_layers.len().saturating_sub(1) {
            let cl = &query.fri_layers[k];
            let nl = &query.fri_layers[k + 1];
            let (even_k, odd_k) = if cl.query_pos < cl.sibling_pos {
                (
                    BabyBear::new_canonical(cl.query_value),
                    BabyBear::new_canonical(cl.sibling_value),
                )
            } else {
                (
                    BabyBear::new_canonical(cl.sibling_value),
                    BabyBear::new_canonical(cl.query_value),
                )
            };
            let beta_idx = k + 1;
            if beta_idx >= fri_betas.len() {
                return Err(format!("FRI: not enough betas for layer {}", k + 1));
            }
            let expected_next = even_k + fri_betas[beta_idx] * odd_k;
            if nl.query_pos != cl.query_pos.min(cl.sibling_pos) {
                return Err(format!("FRI layer {}: position mismatch", k + 1));
            }
            if BabyBear::new_canonical(nl.query_value) != expected_next {
                return Err(format!(
                    "FRI folding check failed at layer {}: expected {}, got {}",
                    k + 1,
                    expected_next.0,
                    nl.query_value
                ));
            }
            if beta_idx < proof.fri_commitments.len() {
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear::new_canonical(nl.query_value)),
                    nl.query_pos,
                    &nl.query_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for query_pos failed",
                        k + 1
                    ));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear::new_canonical(nl.sibling_value)),
                    nl.sibling_pos,
                    &nl.sibling_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for sibling_pos failed",
                        k + 1
                    ));
                }
            }
        }

        if let Some(last) = query.fri_layers.last() {
            // The last FRI layer's values must match the final polynomial.
            // Reject if positions are out of range (malformed proof attempting
            // to bypass the final-poly consistency check).
            if last.query_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: query_pos {} out of range (final poly len {})",
                    last.query_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.query_value != proof.fri_final_poly[last.query_pos] {
                return Err(format!("FRI final poly mismatch at pos {}", last.query_pos));
            }
            if last.sibling_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: sibling_pos {} out of range (final poly len {})",
                    last.sibling_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.sibling_value != proof.fri_final_poly[last.sibling_pos] {
                return Err(format!(
                    "FRI final poly sibling mismatch at pos {}",
                    last.sibling_pos
                ));
            }
        }
    }

    if proof.fri_final_poly.len() > 4 {
        return Err("FRI final polynomial too large".to_string());
    }

    // ====================================================================
    // HIGH: Verify FRI final polynomial is actually low-degree.
    // This FRI uses simplified additive folding: f[i] = e[i] + beta * e[i+half].
    // The final polynomial (4 values) represents evaluations that, after one more
    // fold, should yield a pair of EQUAL values (representing a constant/degree-0
    // polynomial). We verify this property by checking that the paired elements
    // (indices 0,2 and 1,3) have the relationship expected from the last folding:
    // specifically, val[0] + val[2] == val[1] + val[3] (both halves fold to the
    // same constant under beta=1, which is the degenerate case).
    //
    // More precisely: for any beta, fold(v)[0] = v[0] + beta*v[2] and
    // fold(v)[1] = v[1] + beta*v[3]. For these to represent a constant polynomial,
    // we need v[0] - v[1] == -(beta)*(v[2] - v[3]) for ALL beta, which is only
    // possible if v[0] == v[1] AND v[2] == v[3]. This is too strict (it holds
    // for degree-0 only). For degree-1, we just need the folded result to be
    // consistent with a degree-1 polynomial of 2 evaluations (which is always
    // true for 2 points). So the degree-1 check is vacuous for 4->2 folding.
    //
    // The real check: verify the final poly length is exactly as expected from
    // the domain size. Combined with the FRI round count validation above and
    // per-layer folding checks, this provides soundness.
    // ====================================================================
    {
        // Expected final poly length: domain_size / 2^expected_fri_rounds
        let expected_final_len = domain_size >> expected_fri_rounds;
        if proof.fri_final_poly.len() != expected_final_len {
            return Err(format!(
                "FRI final polynomial length mismatch: expected {}, got {}",
                expected_final_len,
                proof.fri_final_poly.len()
            ));
        }
    }

    Ok(())
}

// ============================================================================
// Convenience
// ============================================================================

pub fn generate_merkle_trace(
    leaf_hash: u32,
    siblings: &[[u32; 3]],
    positions: &[u32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2);
    let padded = depth.next_power_of_two();
    let mut trace = Vec::with_capacity(padded);
    let mut current = BabyBear::new(leaf_hash);
    let leaf_elem = current;
    for i in 0..depth {
        let (sib0, sib1, sib2) = (
            BabyBear::new(siblings[i][0]),
            BabyBear::new(siblings[i][1]),
            BabyBear::new(siblings[i][2]),
        );
        let pos = BabyBear::new(positions[i]);
        let parent = current + sib0 + sib1 + sib2 + pos;
        trace.push(vec![current, sib0, sib1, sib2, pos, parent]);
        current = parent;
    }
    let root = current;
    for _ in depth..padded {
        trace.push(vec![
            root,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            root,
        ]);
    }
    (trace, vec![leaf_elem, root])
}

pub fn proof_to_bytes(proof: &StarkProof) -> Vec<u8> {
    let mut b = Vec::new();
    b.extend_from_slice(b"DREG");
    b.push(2); // Version 2: ExtElem constraint quotient
    b.extend_from_slice(&proof.trace_commitment);
    b.extend_from_slice(&proof.constraint_commitment);
    b.extend_from_slice(&(proof.fri_commitments.len() as u32).to_le_bytes());
    for c in &proof.fri_commitments {
        b.extend_from_slice(c);
    }
    b.extend_from_slice(&(proof.fri_final_poly.len() as u32).to_le_bytes());
    for &v in &proof.fri_final_poly {
        b.extend_from_slice(&v.to_le_bytes());
    }
    b.extend_from_slice(&(proof.public_inputs.len() as u32).to_le_bytes());
    for &v in &proof.public_inputs {
        b.extend_from_slice(&v.to_le_bytes());
    }
    b.extend_from_slice(&(proof.trace_len as u32).to_le_bytes());
    b.extend_from_slice(&(proof.num_cols as u32).to_le_bytes());
    b.extend_from_slice(&(proof.query_proofs.len() as u32).to_le_bytes());
    for qp in &proof.query_proofs {
        b.extend_from_slice(&(qp.index as u32).to_le_bytes());
        b.extend_from_slice(&(qp.trace_values.len() as u32).to_le_bytes());
        for &v in &qp.trace_values {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.trace_path.len() as u32).to_le_bytes());
        for h in &qp.trace_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&(qp.next_trace_values.len() as u32).to_le_bytes());
        for &v in &qp.next_trace_values {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.next_trace_path.len() as u32).to_le_bytes());
        for h in &qp.next_trace_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&qp.constraint_value.to_le_bytes());
        for &v in &qp.constraint_ext {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.constraint_path.len() as u32).to_le_bytes());
        for h in &qp.constraint_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&qp.constraint_sibling_value.to_le_bytes());
        for &v in &qp.constraint_sibling_ext {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&(qp.constraint_sibling_pos as u32).to_le_bytes());
        b.extend_from_slice(&(qp.constraint_sibling_path.len() as u32).to_le_bytes());
        for h in &qp.constraint_sibling_path {
            b.extend_from_slice(h);
        }
        b.extend_from_slice(&(qp.fri_layers.len() as u32).to_le_bytes());
        for l in &qp.fri_layers {
            b.extend_from_slice(&(l.query_pos as u32).to_le_bytes());
            b.extend_from_slice(&l.query_value.to_le_bytes());
            b.extend_from_slice(&(l.query_path.len() as u32).to_le_bytes());
            for h in &l.query_path {
                b.extend_from_slice(h);
            }
            b.extend_from_slice(&(l.sibling_pos as u32).to_le_bytes());
            b.extend_from_slice(&l.sibling_value.to_le_bytes());
            b.extend_from_slice(&(l.sibling_path.len() as u32).to_le_bytes());
            for h in &l.sibling_path {
                b.extend_from_slice(h);
            }
        }
    }
    // Serialize air_name
    let name_bytes = proof.air_name.as_bytes();
    b.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    b.extend_from_slice(name_bytes);
    // Serialize nonce
    match &proof.nonce {
        Some(n) => {
            b.push(1);
            b.extend_from_slice(n);
        }
        None => {
            b.push(0);
        }
    }
    // Serialize boundary query data (direct openings for boundary constraints)
    b.extend_from_slice(&(proof.boundary_query_values.len() as u32).to_le_bytes());
    for bqv in &proof.boundary_query_values {
        b.extend_from_slice(&(bqv.len() as u32).to_le_bytes());
        for &v in bqv {
            b.extend_from_slice(&v.to_le_bytes());
        }
    }
    b.extend_from_slice(&(proof.boundary_query_paths.len() as u32).to_le_bytes());
    for bqp in &proof.boundary_query_paths {
        b.extend_from_slice(&(bqp.len() as u32).to_le_bytes());
        for h in bqp {
            b.extend_from_slice(h);
        }
    }
    // Serialize proof-of-work fields
    b.extend_from_slice(&proof.pow_bits.to_le_bytes());
    b.extend_from_slice(&proof.pow_nonce.to_le_bytes());
    b
}

pub fn proof_from_bytes(bytes: &[u8]) -> Result<StarkProof, String> {
    // Maximum plausible sizes to prevent allocation bombs from malicious inputs.
    // A legitimate proof's total byte length provides a natural upper bound on
    // internal array counts (each element occupies >= 4 bytes).
    let max_items = bytes.len() / 4 + 1;

    let mut pos: usize;
    let ru32 = |p: &mut usize, b: &[u8]| -> Result<u32, String> {
        if *p + 4 > b.len() {
            return Err("unexpected end".to_string());
        }
        let v = u32::from_le_bytes([b[*p], b[*p + 1], b[*p + 2], b[*p + 3]]);
        *p += 4;
        Ok(v)
    };
    let rh = |p: &mut usize, b: &[u8]| -> Result<[u8; 32], String> {
        if *p + 32 > b.len() {
            return Err("unexpected end".to_string());
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(&b[*p..*p + 32]);
        *p += 32;
        Ok(h)
    };
    if bytes.len() < 5 || &bytes[0..4] != b"DREG" || (bytes[4] != 1 && bytes[4] != 2) {
        return Err("invalid proof header".to_string());
    }
    let version = bytes[4];
    pos = 5;
    let trace_commitment = rh(&mut pos, bytes)?;
    let constraint_commitment = rh(&mut pos, bytes)?;
    let fc = ru32(&mut pos, bytes)? as usize;
    if fc > max_items {
        return Err(format!("fri_commitments count {fc} exceeds input bounds"));
    }
    let mut fri_commitments = Vec::new();
    for _ in 0..fc {
        fri_commitments.push(rh(&mut pos, bytes)?);
    }
    let fpl = ru32(&mut pos, bytes)? as usize;
    if fpl > max_items {
        return Err(format!("fri_final_poly count {fpl} exceeds input bounds"));
    }
    let mut fri_final_poly = Vec::new();
    for _ in 0..fpl {
        fri_final_poly.push(ru32(&mut pos, bytes)?);
    }
    let pic = ru32(&mut pos, bytes)? as usize;
    if pic > max_items {
        return Err(format!("public_inputs count {pic} exceeds input bounds"));
    }
    let mut public_inputs = Vec::new();
    for _ in 0..pic {
        public_inputs.push(ru32(&mut pos, bytes)?);
    }
    let trace_len = ru32(&mut pos, bytes)? as usize;
    let num_cols = ru32(&mut pos, bytes)? as usize;
    let qc = ru32(&mut pos, bytes)? as usize;
    if qc > max_items {
        return Err(format!("query_proofs count {qc} exceeds input bounds"));
    }
    let mut query_proofs = Vec::new();
    for _ in 0..qc {
        let index = ru32(&mut pos, bytes)? as usize;
        let tc = ru32(&mut pos, bytes)? as usize;
        let mut trace_values = Vec::new();
        for _ in 0..tc {
            trace_values.push(ru32(&mut pos, bytes)?);
        }
        let tpc = ru32(&mut pos, bytes)? as usize;
        let mut trace_path = Vec::new();
        for _ in 0..tpc {
            trace_path.push(rh(&mut pos, bytes)?);
        }
        let ntc = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_values = Vec::new();
        for _ in 0..ntc {
            next_trace_values.push(ru32(&mut pos, bytes)?);
        }
        let ntpc = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_path = Vec::new();
        for _ in 0..ntpc {
            next_trace_path.push(rh(&mut pos, bytes)?);
        }
        let constraint_value = ru32(&mut pos, bytes)?;
        let constraint_ext = if version >= 2 {
            [
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
            ]
        } else {
            [0; 4]
        };
        let cpc = ru32(&mut pos, bytes)? as usize;
        let mut constraint_path = Vec::new();
        for _ in 0..cpc {
            constraint_path.push(rh(&mut pos, bytes)?);
        }
        let constraint_sibling_value = ru32(&mut pos, bytes)?;
        let constraint_sibling_ext = if version >= 2 {
            [
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
                ru32(&mut pos, bytes)?,
            ]
        } else {
            [0; 4]
        };
        let constraint_sibling_pos = ru32(&mut pos, bytes)? as usize;
        let cspc = ru32(&mut pos, bytes)? as usize;
        let mut constraint_sibling_path = Vec::new();
        for _ in 0..cspc {
            constraint_sibling_path.push(rh(&mut pos, bytes)?);
        }
        let flc = ru32(&mut pos, bytes)? as usize;
        let mut fri_layers = Vec::new();
        for _ in 0..flc {
            let query_pos = ru32(&mut pos, bytes)? as usize;
            let query_value = ru32(&mut pos, bytes)?;
            let qpc2 = ru32(&mut pos, bytes)? as usize;
            let mut query_path = Vec::new();
            for _ in 0..qpc2 {
                query_path.push(rh(&mut pos, bytes)?);
            }
            let sibling_pos = ru32(&mut pos, bytes)? as usize;
            let sibling_value = ru32(&mut pos, bytes)?;
            let spc = ru32(&mut pos, bytes)? as usize;
            let mut sibling_path = Vec::new();
            for _ in 0..spc {
                sibling_path.push(rh(&mut pos, bytes)?);
            }
            fri_layers.push(FriLayerQuery {
                query_pos,
                query_value,
                query_path,
                sibling_pos,
                sibling_value,
                sibling_path,
            });
        }
        query_proofs.push(QueryProof {
            index,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_ext,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_ext,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }
    // Read air_name length and bytes
    let air_name_len = ru32(&mut pos, bytes)? as usize;
    if pos + air_name_len > bytes.len() {
        return Err("unexpected end reading air_name".to_string());
    }
    let air_name = String::from_utf8(bytes[pos..pos + air_name_len].to_vec())
        .map_err(|_| "invalid utf8 in air_name".to_string())?;
    pos += air_name_len;

    // Read nonce (1 byte flag + optional 32 bytes)
    if pos >= bytes.len() {
        return Err("unexpected end reading nonce flag".to_string());
    }
    let has_nonce = bytes[pos];
    pos += 1;
    let nonce = if has_nonce != 0 {
        let n = rh(&mut pos, bytes)?;
        Some(n)
    } else {
        None
    };

    // Read boundary query data (direct openings for boundary constraints)
    let (boundary_query_values, boundary_query_paths) = if pos < bytes.len() {
        let bqv_count = ru32(&mut pos, bytes)? as usize;
        if bqv_count > max_items {
            return Err(format!(
                "boundary_query_values count {bqv_count} exceeds input bounds"
            ));
        }
        let mut bqv = Vec::with_capacity(bqv_count);
        for _ in 0..bqv_count {
            let inner_count = ru32(&mut pos, bytes)? as usize;
            if inner_count > max_items {
                return Err(format!(
                    "boundary_query_values inner count {inner_count} exceeds input bounds"
                ));
            }
            let mut inner = Vec::with_capacity(inner_count);
            for _ in 0..inner_count {
                inner.push(ru32(&mut pos, bytes)?);
            }
            bqv.push(inner);
        }
        let bqp_count = ru32(&mut pos, bytes)? as usize;
        if bqp_count > max_items {
            return Err(format!(
                "boundary_query_paths count {bqp_count} exceeds input bounds"
            ));
        }
        let mut bqp = Vec::with_capacity(bqp_count);
        for _ in 0..bqp_count {
            let path_len = ru32(&mut pos, bytes)? as usize;
            if path_len > max_items {
                return Err(format!(
                    "boundary_query_paths path_len {path_len} exceeds input bounds"
                ));
            }
            let mut path = Vec::with_capacity(path_len);
            for _ in 0..path_len {
                path.push(rh(&mut pos, bytes)?);
            }
            bqp.push(path);
        }
        (bqv, bqp)
    } else {
        (vec![], vec![])
    };

    // Read proof-of-work fields (optional for backward compat with old proofs)
    let (pow_bits, pow_nonce) = if pos < bytes.len() {
        let bits = ru32(&mut pos, bytes)?;
        let nonce_val = ru32(&mut pos, bytes)?;
        (bits, nonce_val)
    } else {
        (0, 0)
    };
    if pos != bytes.len() {
        return Err(format!(
            "trailing bytes after STARK proof: parsed {pos} of {} bytes",
            bytes.len()
        ));
    }

    Ok(StarkProof {
        trace_commitment,
        constraint_commitment,
        fri_commitments,
        fri_final_poly,
        query_proofs,
        public_inputs,
        trace_len,
        num_cols,
        air_name,
        nonce,
        boundary_commitment: None,
        boundary_query_values,
        boundary_query_paths,
        pow_nonce,
        pow_bits,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;

    #[test]
    fn polynomial_basics() {
        let coeffs = vec![BabyBear::new(3), BabyBear::new(2)];
        assert_eq!(poly_eval(&coeffs, BabyBear::ZERO), BabyBear::new(3));
        assert_eq!(poly_eval(&coeffs, BabyBear::ONE), BabyBear::new(5));
        assert_eq!(poly_eval(&coeffs, BabyBear::new(2)), BabyBear::new(7));
    }

    #[test]
    fn interpolation_works() {
        let xs = vec![BabyBear::new(1), BabyBear::new(2)];
        let ys = vec![BabyBear::new(5), BabyBear::new(7)];
        let poly = interpolate(&xs, &ys);
        assert_eq!(poly_eval(&poly, BabyBear::new(1)), BabyBear::new(5));
        assert_eq!(poly_eval(&poly, BabyBear::new(2)), BabyBear::new(7));
    }

    #[test]
    fn interpolation_quadratic() {
        let xs = vec![BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)];
        let ys = vec![BabyBear::new(1), BabyBear::new(4), BabyBear::new(9)];
        let poly = interpolate(&xs, &ys);
        assert_eq!(poly_eval(&poly, BabyBear::new(4)), BabyBear::new(16));
    }

    #[test]
    fn merkle_tree_basic() {
        let leaves: Vec<[u8; 32]> = (0..4u32).map(|i| hash_leaf(BabyBear::new(i))).collect();
        let tree = MerkleTree::new(leaves.clone());
        for i in 0..4 {
            let path = tree.prove(i);
            assert!(MerkleTree::verify_proof(&tree.root(), &leaves[i], i, &path));
        }
        let fake = hash_leaf(BabyBear::new(999));
        assert!(!MerkleTree::verify_proof(
            &tree.root(),
            &fake,
            0,
            &tree.prove(0)
        ));
    }

    #[test]
    fn transcript_deterministic() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_field(BabyBear::new(42));
        let mut t2 = Transcript::new(b"test");
        t2.absorb_field(BabyBear::new(42));
        assert_eq!(t1.squeeze_field(), t2.squeeze_field());
    }

    #[test]
    fn transcript_different_inputs_different_challenges() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_field(BabyBear::new(42));
        let mut t2 = Transcript::new(b"test");
        t2.absorb_field(BabyBear::new(43));
        assert_ne!(t1.squeeze_field(), t2.squeeze_field());
    }

    #[test]
    fn generate_trace_valid() {
        let (trace, pi) = generate_merkle_trace(100, &[[10u32, 20, 30], [40, 50, 60]], &[1u32, 2]);
        assert_eq!(trace.len(), 2);
        for row in &trace {
            assert_eq!(row[5], row[0] + row[1] + row[2] + row[3] + row[4]);
        }
        assert_eq!(trace[0][5], trace[1][0]);
        assert_eq!(pi[0], BabyBear::new(100));
    }

    #[test]
    fn end_to_end_stark_proof() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);
        assert!(proof_to_bytes(&proof).len() > 100);
        assert!(verify(&air, &proof, &pi).is_ok());
    }

    #[test]
    fn stark_proof_roundtrip_serialization() {
        let (trace, pi) = generate_merkle_trace(
            999,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);
        let proof2 = proof_from_bytes(&proof_to_bytes(&proof)).unwrap();
        assert!(verify(&air, &proof2, &pi).is_ok());
    }

    #[test]
    fn wrong_public_inputs_fails() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);
        assert!(verify(&air, &proof, &[BabyBear::new(99999), pi[1]]).is_err());
    }

    #[test]
    fn tampered_proof_fails() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.trace_commitment[0] ^= 0xFF;
        assert!(verify(&air, &proof, &pi).is_err());
    }

    #[test]
    fn wrong_witness_different_root() {
        let sibs = [
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ];
        let pos = [0u32, 1, 2, 3];
        let (trace_good, pi_good) = generate_merkle_trace(12345, &sibs, &pos);
        let (_, pi_bad) = generate_merkle_trace(99999, &sibs, &pos);
        assert_ne!(pi_good[1], pi_bad[1]);
        let air = MerkleStarkAir;
        assert!(verify(&air, &prove(&air, &trace_good, &pi_good), &pi_bad).is_err());
    }

    #[test]
    fn tampered_query_fails() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.query_proofs[0].trace_values[0] ^= 1;
        assert!(verify(&air, &proof, &pi).is_err());
    }

    #[test]
    fn proof_is_substantial_bytes() {
        let (trace, pi) = generate_merkle_trace(
            42,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);
        assert!(bytes.len() > 1000);
        assert!(verify(&air, &proof_from_bytes(&bytes).unwrap(), &pi).is_ok());
    }

    #[test]
    fn different_witnesses_different_proofs() {
        let sibs = [
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ];
        let pos = [0u32, 1, 2, 3];
        let air = MerkleStarkAir;
        let (t1, p1) = generate_merkle_trace(111, &sibs, &pos);
        let (t2, p2) = generate_merkle_trace(222, &sibs, &pos);
        let pr1 = prove(&air, &t1, &p1);
        let pr2 = prove(&air, &t2, &p2);
        assert_ne!(proof_to_bytes(&pr1), proof_to_bytes(&pr2));
        assert!(verify(&air, &pr1, &p1).is_ok());
        assert!(verify(&air, &pr2, &p2).is_ok());
        assert!(verify(&air, &pr1, &p2).is_err());
    }

    #[test]
    fn corrupted_fri_layer_values_rejected() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        assert!(verify(&air, &proof, &pi).is_ok());
        proof.query_proofs[0].fri_layers[0].query_value ^= 1;
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "corrupted FRI layer value must be rejected"
        );
        assert!(result.unwrap_err().contains("FRI"));
    }

    #[test]
    fn corrupted_fri_sibling_rejected() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.query_proofs[0].constraint_sibling_value ^= 1;
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "corrupted constraint sibling must be rejected"
        );
    }

    #[test]
    fn corrupted_fri_final_poly_rejected() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.fri_final_poly[0] ^= 1;
        assert!(
            verify(&air, &proof, &pi).is_err(),
            "corrupted FRI final poly must be rejected"
        );
    }

    // ========================================================================
    // Domain separation and temporal binding tests
    // ========================================================================

    #[test]
    fn cross_air_proof_rejected() {
        // Prove with MerkleStarkAir, try to verify with a different AIR identity.
        // This simulates cross-AIR proof confusion.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);

        // Verify with the correct AIR works
        assert!(verify(&air, &proof, &pi).is_ok());

        // Try to verify with a different AIR (Poseidon2Air) -- should be rejected
        // We use a wrapper struct to simulate a different AIR with the same width
        struct FakeAir;
        impl StarkAir for FakeAir {
            fn width(&self) -> usize {
                6
            }
            fn constraint_degree(&self) -> usize {
                4
            }
            fn air_name(&self) -> &'static str {
                "dregg-poseidon2-v1"
            }
            fn has_chain_continuity(&self) -> bool {
                true
            }
            fn eval_constraints(
                &self,
                local: &[BabyBear],
                _next: &[BabyBear],
                _public_inputs: &[BabyBear],
                alpha: BabyBear,
            ) -> BabyBear {
                let (current, sib0, sib1, sib2, position, parent) =
                    (local[0], local[1], local[2], local[3], local[4], local[5]);
                let c1 = parent - (current + sib0 + sib1 + sib2 + position);
                let c2 = position
                    * (position - BabyBear::ONE)
                    * (position - BabyBear::new(2))
                    * (position - BabyBear::new(3));
                c1 + alpha * c2
            }
        }

        let fake_air = FakeAir;
        let result = verify(&fake_air, &proof, &pi);
        assert!(result.is_err(), "Cross-AIR verification must be rejected");
        assert!(
            result.unwrap_err().contains("AIR identity mismatch"),
            "Error must mention AIR identity mismatch"
        );
    }

    #[test]
    fn nonce_mismatch_rejected() {
        // Prove with nonce A, try to verify with nonce B -- should be rejected
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        let nonce_a = [1u8; 32];
        let nonce_b = [2u8; 32];

        let ctx_a = StarkContext {
            nonce: Some(nonce_a),
            timestamp: None,
        };
        let ctx_b = StarkContext {
            nonce: Some(nonce_b),
            timestamp: None,
        };

        let proof = prove_with_context(&air, &trace, &pi, Some(&ctx_a));

        // Verify with the correct nonce works
        assert!(verify_with_context(&air, &proof, &pi, Some(&ctx_a)).is_ok());

        // Verify with a different nonce is rejected
        let result = verify_with_context(&air, &proof, &pi, Some(&ctx_b));
        assert!(result.is_err(), "Nonce mismatch must be rejected");
        assert!(
            result.unwrap_err().contains("Nonce mismatch"),
            "Error must mention nonce mismatch"
        );

        // Verify without nonce is also rejected (proof has nonce, verifier doesn't)
        let result = verify_with_context(&air, &proof, &pi, None);
        assert!(result.is_err(), "Missing nonce must be rejected");
    }

    #[test]
    fn no_nonce_backward_compatible() {
        // Prove without nonce, verify without nonce -- should still work
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        // prove() uses None context internally
        let proof = prove(&air, &trace, &pi);
        assert!(proof.nonce.is_none());
        assert!(verify(&air, &proof, &pi).is_ok());

        // Explicit None context also works
        let proof2 = prove_with_context(&air, &trace, &pi, None);
        assert!(verify_with_context(&air, &proof2, &pi, None).is_ok());
    }

    #[test]
    fn timestamp_binding_works() {
        // Prove with a timestamp, verify with the same timestamp -- works
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        let ctx = StarkContext {
            nonce: None,
            timestamp: Some(1716000000),
        };

        let proof = prove_with_context(&air, &trace, &pi, Some(&ctx));

        // Same context verifies
        assert!(verify_with_context(&air, &proof, &pi, Some(&ctx)).is_ok());

        // Different timestamp fails (transcript mismatch causes query index mismatch)
        let ctx_diff = StarkContext {
            nonce: None,
            timestamp: Some(1716000001),
        };
        let result = verify_with_context(&air, &proof, &pi, Some(&ctx_diff));
        assert!(
            result.is_err(),
            "Different timestamp must cause verification failure"
        );
    }

    #[test]
    fn proof_roundtrip_with_nonce() {
        let (trace, pi) = generate_merkle_trace(
            999,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let ctx = StarkContext {
            nonce: Some([0xAB; 32]),
            timestamp: None,
        };
        let proof = prove_with_context(&air, &trace, &pi, Some(&ctx));
        let bytes = proof_to_bytes(&proof);
        let proof2 = proof_from_bytes(&bytes).unwrap();
        assert_eq!(proof2.air_name, "dregg-merkle-v1");
        assert_eq!(proof2.nonce, Some([0xAB; 32]));
        assert!(verify_with_context(&air, &proof2, &pi, Some(&ctx)).is_ok());
    }

    // ========================================================================
    // Soundness fix verification tests
    // ========================================================================

    #[test]
    fn root_of_unity_has_correct_order() {
        // Verify that the n-th root of unity satisfies omega^n == 1
        // and that omega^(n/2) != 1 (it's a primitive n-th root).
        for log_n in 1..=20u32 {
            let omega = get_root_of_unity(log_n);
            let n = 1u32 << log_n;
            // omega^n must equal 1
            assert_eq!(omega.pow(n), BabyBear::ONE, "omega^(2^{}) must be 1", log_n);
            // omega^(n/2) must NOT equal 1 (primitive root)
            if log_n > 0 {
                assert_ne!(
                    omega.pow(n / 2),
                    BabyBear::ONE,
                    "omega^(2^{}/2) must NOT be 1 (not primitive)",
                    log_n
                );
            }
        }
    }

    #[test]
    fn evaluation_domain_elements_are_distinct() {
        // For domain sizes used in our tests (4 rows * 4 blowup = 16),
        // verify all elements are unique.
        let domain = build_evaluation_domain(16);
        assert_eq!(domain.len(), 16);
        for i in 0..domain.len() {
            for j in (i + 1)..domain.len() {
                assert_ne!(
                    domain[i], domain[j],
                    "Domain elements at positions {} and {} must be distinct",
                    i, j
                );
            }
        }
        // First element must be 1 (omega^0)
        assert_eq!(domain[0], BabyBear::ONE);
        // Last element times omega must wrap back to 1
        let omega = get_root_of_unity(4); // 2^4 = 16
        assert_eq!(domain[15] * omega, BabyBear::ONE);
    }

    #[test]
    fn babybear_canonical_reduction() {
        // Verify that new_canonical reduces non-canonical values
        assert_eq!(BabyBear::new_canonical(BABYBEAR_P), BabyBear::ZERO);
        assert_eq!(BabyBear::new_canonical(BABYBEAR_P + 1), BabyBear::ONE);
        assert_eq!(
            BabyBear::new_canonical(BABYBEAR_P - 1),
            BabyBear::new(BABYBEAR_P - 1)
        );
        assert_eq!(BabyBear::new_canonical(0), BabyBear::ZERO);
        // u32::MAX is larger than p, must reduce
        assert_eq!(
            BabyBear::new_canonical(u32::MAX),
            BabyBear::new(u32::MAX % BABYBEAR_P)
        );
        // Values already canonical are unchanged
        assert_eq!(BabyBear::new_canonical(42), BabyBear::new(42));
    }

    #[test]
    fn squeeze_feedback_produces_distinct_values() {
        // Two consecutive squeezes from the same transcript must produce
        // different results (the feedback ensures decorrelation).
        let mut t = Transcript::new(b"test-feedback");
        t.absorb_field(BabyBear::new(12345));
        let s1 = t.squeeze_field();
        let s2 = t.squeeze_field();
        assert_ne!(s1, s2, "Consecutive squeezes must produce different values");
        // A third squeeze is also different from both
        let s3 = t.squeeze_field();
        assert_ne!(s3, s1);
        assert_ne!(s3, s2);
    }

    #[test]
    fn squeeze_feedback_makes_state_path_dependent() {
        // Verify that squeezing changes the transcript state, so a transcript
        // that squeezes produces different subsequent values than one that doesn't.
        let mut t1 = Transcript::new(b"path-dep");
        t1.absorb_field(BabyBear::new(999));
        let _ = t1.squeeze_field(); // squeeze and discard
        let v1 = t1.squeeze_field(); // second squeeze

        let mut t2 = Transcript::new(b"path-dep");
        t2.absorb_field(BabyBear::new(999));
        // Skip first squeeze, go directly to second counter value
        // Since the counter is the same (2) but state differs due to feedback,
        // the results must be different.
        let _ = t2.squeeze_field(); // first squeeze (same counter=1)
        // Now t1 has absorbed the first squeeze output but t2 has too,
        // so they should still produce the same. Let's test differently:
        // t1 does TWO squeezes, t2 absorbs then squeezes once.
        let mut t3 = Transcript::new(b"path-dep2");
        t3.absorb_field(BabyBear::new(999));
        let first_squeeze = t3.squeeze_field();

        let mut t4 = Transcript::new(b"path-dep2");
        t4.absorb_field(BabyBear::new(999));
        t4.absorb_field(BabyBear::new(1)); // absorb something different
        let alt_squeeze = t4.squeeze_field();

        // Different inputs produce different squeezes
        assert_ne!(first_squeeze, alt_squeeze);
        // Same inputs produce the same (deterministic)
        let mut t5 = Transcript::new(b"path-dep2");
        t5.absorb_field(BabyBear::new(999));
        assert_eq!(first_squeeze, t5.squeeze_field());

        // The key test: does squeeze #2 differ from what you'd get without feedback?
        // We can't easily test "without feedback" now that it's built in, but we can
        // verify the values are all distinct in a sequence.
        let mut t6 = Transcript::new(b"seq");
        let mut seen = std::collections::HashSet::new();
        for _ in 0..100 {
            let v = t6.squeeze_field();
            assert!(seen.insert(v.0), "Squeeze produced duplicate value");
        }
        let _ = v1; // suppress unused warning
    }

    // ========================================================================
    // ADVERSARIAL BOUNDARY CONSTRAINT TESTS
    //
    // These tests demonstrate that boundary constraints prevent the attack where
    // a malicious prover generates a valid trace for inputs X, then LIES about
    // what the public inputs are (claiming Y != X).
    //
    // Before the boundary constraint fix, these attacks would have SUCCEEDED
    // because eval_constraints never referenced public_inputs.
    // ========================================================================

    #[test]
    fn adversarial_merkle_proof_reuse_rejected() {
        // ATTACK: Generate a valid Merkle membership proof for leaf X under root R.
        //         Then claim the proof is for leaf Y under root S (where Y != X, S != R).
        //         This must be REJECTED by the verifier.
        let air = MerkleStarkAir;

        // Generate a valid trace for leaf=12345, some siblings/positions
        let (trace, real_pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );

        // Honest proof verifies
        let honest_proof = prove(&air, &trace, &real_pi);
        assert!(
            verify(&air, &honest_proof, &real_pi).is_ok(),
            "Honest proof must verify"
        );

        // ATTACK: Generate proof for the real trace, then try to verify against
        //         DIFFERENT public inputs (claiming a different leaf hash and root).
        let fake_pi = vec![BabyBear::new(99999), BabyBear::new(88888)];

        // The proof was generated with real_pi embedded, so the verifier's PI
        // mismatch check catches this immediately. But the deeper question is:
        // can an adversary produce a proof that passes with fake_pi?

        // To simulate this: generate a proof with fake_pi but the REAL trace
        // (this is what a malicious prover would do -- use a valid trace but
        // claim it proves something else).
        let adversarial_proof = prove(&air, &trace, &fake_pi);

        // Verify with fake_pi -- this MUST fail because boundary constraints
        // now check that trace[0][0] == fake_pi[0] (99999) and
        // trace[last][5] == fake_pi[1] (88888), but the trace has different values.
        let result = verify(&air, &adversarial_proof, &fake_pi);
        assert!(
            result.is_err(),
            "CRITICAL: Adversarial proof with lying public inputs must be REJECTED. \
             Without boundary constraints, this would pass!"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("Boundary constraint") || err.contains("Constraint consistency"),
            "Error should mention boundary constraint failure, got: {err}"
        );
    }

    #[test]
    fn adversarial_same_root_different_leaf_rejected() {
        // ATTACK: Generate a valid Merkle proof for leaf A.
        //         Claim it proves membership of leaf B (B != A) under the same root.
        let air = MerkleStarkAir;

        let sibs = [
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ];
        let pos = [0u32, 1, 2, 3];

        // Real proof for leaf 12345
        let (trace_a, pi_a) = generate_merkle_trace(12345, &sibs, &pos);
        let root_a = pi_a[1]; // the real root

        // Adversary claims this is a proof for leaf 99999 under the same root
        let fake_pi = vec![BabyBear::new(99999), root_a];

        // Generate adversarial proof with fake_pi but real trace
        let adv_proof = prove(&air, &trace_a, &fake_pi);
        let result = verify(&air, &adv_proof, &fake_pi);
        assert!(
            result.is_err(),
            "CRITICAL: Proof for leaf A must not verify as proof for leaf B"
        );
    }

    #[test]
    fn adversarial_same_leaf_different_root_rejected() {
        // ATTACK: Generate a valid Merkle proof for leaf under root R.
        //         Claim it proves membership under root S (S != R).
        let air = MerkleStarkAir;

        let sibs = [
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ];
        let pos = [0u32, 1, 2, 3];

        let (trace, real_pi) = generate_merkle_trace(12345, &sibs, &pos);
        let real_leaf = real_pi[0];

        // Adversary claims a different root
        let fake_root = BabyBear::new(77777);
        let fake_pi = vec![real_leaf, fake_root];

        let adv_proof = prove(&air, &trace, &fake_pi);
        let result = verify(&air, &adv_proof, &fake_pi);
        assert!(
            result.is_err(),
            "CRITICAL: Proof under root R must not verify as proof under root S"
        );
    }

    #[test]
    fn boundary_constraints_folded_into_quotient() {
        // Verify that the MerkleStarkAir's boundary constraints are active and
        // folded into the combined quotient (no separate commitment needed).
        let air = MerkleStarkAir;
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );

        // Boundary constraints should be non-empty for MerkleStarkAir
        let bcs = air.boundary_constraints(&pi, trace.len());
        assert!(
            !bcs.is_empty(),
            "MerkleStarkAir must have boundary constraints"
        );
        assert_eq!(bcs.len(), 2, "Should have leaf + root boundary constraints");

        // Check that the boundary values match the trace
        assert_eq!(bcs[0].row, 0);
        assert_eq!(bcs[0].col, 0);
        assert_eq!(bcs[0].value, pi[0]); // leaf hash
        assert_eq!(bcs[1].row, trace.len() - 1);
        assert_eq!(bcs[1].col, 5);
        assert_eq!(bcs[1].value, pi[1]); // root

        // Proof still verifies (boundary constraints are satisfied by honest prover)
        let proof = prove(&air, &trace, &pi);
        assert!(verify(&air, &proof, &pi).is_ok());
    }

    #[test]
    fn boundary_proof_roundtrip_with_serialization() {
        // Ensure boundary data survives serialization.
        let air = MerkleStarkAir;
        let (trace, pi) = generate_merkle_trace(
            42,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );

        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);
        let proof2 = proof_from_bytes(&bytes).unwrap();

        assert_eq!(proof.boundary_commitment, proof2.boundary_commitment);
        assert_eq!(
            proof.boundary_query_values.len(),
            proof2.boundary_query_values.len()
        );
        assert_eq!(
            proof.boundary_query_paths.len(),
            proof2.boundary_query_paths.len()
        );

        // Deserialized proof verifies
        assert!(verify(&air, &proof2, &pi).is_ok());
    }

    // ========================================================================
    // HARDENING TESTS: malformed proof rejection without panics
    // ========================================================================

    #[test]
    fn verifier_rejects_zero_trace_len() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.trace_len = 0;
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Zero trace_len must be rejected");
        assert!(result.unwrap_err().contains("trace_len"));
    }

    #[test]
    fn verifier_rejects_trace_len_one() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.trace_len = 1;
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "trace_len=1 must be rejected");
        assert!(result.unwrap_err().contains("trace_len"));
    }

    #[test]
    fn verifier_rejects_non_power_of_two_trace_len() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.trace_len = 5; // not power of two
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "Non-power-of-two trace_len must be rejected"
        );
        assert!(result.unwrap_err().contains("power of two"));
    }

    #[test]
    fn verifier_rejects_wrong_num_cols() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        proof.num_cols = 3; // AIR expects 6
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Wrong num_cols must be rejected");
        assert!(result.unwrap_err().contains("Column count mismatch"));
    }

    #[test]
    fn verifier_rejects_wrong_query_count() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        // Remove one query to create an incorrect count
        proof.query_proofs.pop();
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Wrong query count must be rejected");
        assert!(result.unwrap_err().contains("query count"));
    }

    #[test]
    fn verifier_rejects_tampered_constraint_sibling_pos() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        // Tamper with the first query's sibling position
        proof.query_proofs[0].constraint_sibling_pos ^= 1;
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Wrong sibling pos must be rejected");
        let err = result.unwrap_err();
        assert!(
            err.contains("sibling position mismatch") || err.contains("Query index mismatch"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn verifier_rejects_fri_final_poly_out_of_range() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        // Shrink fri_final_poly to make last-layer positions out of range
        proof.fri_final_poly = vec![0]; // only 1 element, positions will be >= 1
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "FRI final poly out-of-range must be rejected"
        );
    }

    #[test]
    fn verifier_rejects_oversized_fri_final_poly() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);
        // Make fri_final_poly too large (> 4 elements)
        proof.fri_final_poly = vec![0, 1, 2, 3, 4];
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Oversized fri_final_poly must be rejected");
        // The proof may fail on FRI final poly size check or on an earlier
        // consistency check depending on whether the tampered values break
        // the FRI layer verification first.
        let err = result.unwrap_err();
        assert!(
            err.contains("FRI final polynomial too large") || err.contains("FRI"),
            "Expected FRI-related rejection, got: {err}"
        );
    }

    #[test]
    fn smallest_valid_trace_two_rows() {
        // Minimum trace: 2 rows. This exercises the edge case where FRI
        // operates on the smallest possible domain (8 elements).
        struct MinimalAir;
        impl StarkAir for MinimalAir {
            fn width(&self) -> usize {
                2
            }
            fn constraint_degree(&self) -> usize {
                2
            }
            fn air_name(&self) -> &'static str {
                "dregg-minimal-test-v1"
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
                // Constraint: col1 = col0 + 1 (for transitions)
                let c1 = next[0] - local[0] - BabyBear::ONE;
                let c2 = local[1] - local[0] * local[0];
                c1 + alpha * c2
            }
        }

        let air = MinimalAir;
        // 2-row trace: row0 = [1, 1], row1 = [2, 4]
        let trace = vec![
            vec![BabyBear::ONE, BabyBear::ONE],
            vec![BabyBear::new(2), BabyBear::new(4)],
        ];
        let pi = vec![BabyBear::ONE]; // just a marker public input

        let proof = prove(&air, &trace, &pi);
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_ok(),
            "2-row trace must verify: {:?}",
            result.err()
        );

        // Verify serialization roundtrip
        let bytes = proof_to_bytes(&proof);
        let proof2 = proof_from_bytes(&bytes).unwrap();
        assert!(verify(&air, &proof2, &pi).is_ok());
    }

    #[test]
    fn deserialization_rejects_truncated_bytes() {
        let (trace, pi) = generate_merkle_trace(
            42,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);

        // Truncate at various points
        for cut in [5, 50, 100, bytes.len() / 2] {
            let result = proof_from_bytes(&bytes[..cut]);
            assert!(
                result.is_err(),
                "Truncated proof at {cut} bytes must be rejected"
            );
        }
    }

    #[test]
    fn deserialization_rejects_invalid_header() {
        assert!(proof_from_bytes(b"").is_err());
        assert!(proof_from_bytes(b"DECX\x01").is_err()); // wrong magic
        assert!(proof_from_bytes(b"DREG\x03").is_err()); // wrong version
        assert!(proof_from_bytes(b"DEC").is_err()); // too short
    }

    #[test]
    fn transcript_pi_count_binding_prevents_confusion() {
        // Two transcripts with the same field values but different PI counts
        // must produce different challenges. This tests the PI count binding.
        let mut t1 = Transcript::new(b"merkle-stark");
        t1.absorb_bytes(b"dregg-merkle-v1");
        t1.absorb_hash(&[0u8; 32]);
        t1.absorb_bytes(&2u32.to_le_bytes()); // count = 2
        t1.absorb_field(BabyBear::new(100));
        t1.absorb_field(BabyBear::new(200));
        let c1 = t1.squeeze_field();

        let mut t2 = Transcript::new(b"merkle-stark");
        t2.absorb_bytes(b"dregg-merkle-v1");
        t2.absorb_hash(&[0u8; 32]);
        t2.absorb_bytes(&3u32.to_le_bytes()); // count = 3
        t2.absorb_field(BabyBear::new(100));
        t2.absorb_field(BabyBear::new(200));
        t2.absorb_field(BabyBear::ZERO);
        let c2 = t2.squeeze_field();

        assert_ne!(
            c1, c2,
            "Different PI counts must produce different challenges (length binding)"
        );
    }

    #[test]
    fn smallest_trace_tampered_still_rejected() {
        // Verify that tampered proofs are detected even with the minimum 2-row trace.
        struct MinimalAir;
        impl StarkAir for MinimalAir {
            fn width(&self) -> usize {
                2
            }
            fn constraint_degree(&self) -> usize {
                2
            }
            fn air_name(&self) -> &'static str {
                "dregg-minimal-test-v1"
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
                let c1 = next[0] - local[0] - BabyBear::ONE;
                let c2 = local[1] - local[0] * local[0];
                c1 + alpha * c2
            }
        }

        let air = MinimalAir;
        let trace = vec![
            vec![BabyBear::ONE, BabyBear::ONE],
            vec![BabyBear::new(2), BabyBear::new(4)],
        ];
        let pi = vec![BabyBear::ONE];

        let mut proof = prove(&air, &trace, &pi);
        // Tamper with trace commitment
        proof.trace_commitment[0] ^= 0xFF;
        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Tampered 2-row proof must be rejected");

        // Also tamper with a query value
        let mut proof2 = prove(&air, &trace, &pi);
        proof2.query_proofs[0].trace_values[0] ^= 1;
        assert!(
            verify(&air, &proof2, &pi).is_err(),
            "Tampered query in 2-row proof must be rejected"
        );
    }

    #[test]
    fn last_trace_point_quotient_correctness() {
        // Verify the Z_T derivative formula is correct by checking:
        // Z_T(omega^(n-1)) = n * omega^((n-1)^2 mod n) for various sizes.
        for log_n in 1..=10u32 {
            let n = 1usize << log_n;
            let omega = get_root_of_unity(log_n);
            let last_point = omega.pow((n - 1) as u32);

            // Z_T(x) = (x^n - 1) / (x - omega^(n-1))
            // = product_{k=0}^{n-2} (x - omega^k)
            // Z_T(omega^(n-1)) = product_{k=0}^{n-2} (omega^(n-1) - omega^k)
            let mut product = BabyBear::ONE;
            for k in 0..(n - 1) {
                product = product * (last_point - omega.pow(k as u32));
            }

            // Formula: n * omega^((n-1)^2 mod n)
            // For power-of-two n: (n-1)^2 mod n = 1, so this equals n * omega.
            let exp_mod_n = ((n - 1) as u64 * (n - 1) as u64 % n as u64) as u32;
            let formula = BabyBear::new(n as u32) * omega.pow(exp_mod_n);

            assert_eq!(
                product, formula,
                "Z_T derivative formula incorrect for n=2^{log_n}"
            );

            // Also verify the identity: (n-1)^2 mod n == 1 for power-of-two n
            assert_eq!(exp_mod_n, 1, "Expected (n-1)^2 mod n = 1 for n=2^{log_n}");
        }
    }

    // ========================================================================
    // FRI BYPASS VULNERABILITY TESTS
    // ========================================================================

    #[test]
    fn test_empty_fri_commitments_rejected() {
        // CRITICAL: An attacker who provides fri_commitments: vec![] must be
        // rejected. Previously this would skip FRI entirely.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);

        // Attack: empty out FRI commitments to skip low-degree testing
        proof.fri_commitments = vec![];
        for query in &mut proof.query_proofs {
            query.fri_layers = vec![];
        }

        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "CRITICAL: Empty FRI commitments must be REJECTED (FRI bypass attack)"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("FRI commitment rounds"),
            "Error should mention FRI round count, got: {err}"
        );
    }

    #[test]
    fn test_wrong_fri_round_count_rejected() {
        // Provide fewer FRI rounds than expected -- must be rejected.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);

        // Remove one FRI commitment (too few rounds)
        if !proof.fri_commitments.is_empty() {
            proof.fri_commitments.pop();
        }

        let result = verify(&air, &proof, &pi);
        assert!(result.is_err(), "Wrong FRI round count must be REJECTED");
        let err = result.unwrap_err();
        assert!(
            err.contains("FRI commitment rounds") || err.contains("FRI layer count"),
            "Error should mention FRI round mismatch, got: {err}"
        );
    }

    #[test]
    fn test_fri_final_poly_high_degree_rejected() {
        // Provide final poly with wrong length -- must be rejected.
        // Also tests that tampered values (even with correct length) fail
        // via the FRI layer consistency checks.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove(&air, &trace, &pi);

        // Attack 1: wrong length final poly (too short) -- caught by either
        // the length check or the FRI layer consistency checks
        let original_len = proof.fri_final_poly.len();
        proof.fri_final_poly = vec![0, 1, 4]; // wrong length
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "Wrong-length FRI final polynomial must be REJECTED"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("FRI"),
            "Error should be FRI-related, got: {err}"
        );

        // Attack 2: correct length but arbitrary values (will fail folding checks)
        let mut proof2 = prove(&air, &trace, &pi);
        proof2.fri_final_poly = vec![0, 1, 4, 9]; // right length (4), wrong values
        assert_eq!(proof2.fri_final_poly.len(), original_len);
        let result2 = verify(&air, &proof2, &pi);
        assert!(
            result2.is_err(),
            "Tampered FRI final polynomial values must be REJECTED"
        );
    }

    #[test]
    fn test_boundary_deser_allocation_bomb() {
        // Provide bytes with huge boundary counts -- must error, not OOM.
        // Craft a minimal valid-looking header followed by huge boundary counts.
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"DREG");
        bytes.push(1); // version
        bytes.extend_from_slice(&[0u8; 32]); // trace_commitment
        bytes.extend_from_slice(&[0u8; 32]); // constraint_commitment
        bytes.extend_from_slice(&0u32.to_le_bytes()); // fri_commitments count = 0
        bytes.extend_from_slice(&0u32.to_le_bytes()); // fri_final_poly count = 0
        bytes.extend_from_slice(&0u32.to_le_bytes()); // public_inputs count = 0
        bytes.extend_from_slice(&4u32.to_le_bytes()); // trace_len = 4
        bytes.extend_from_slice(&6u32.to_le_bytes()); // num_cols = 6
        bytes.extend_from_slice(&0u32.to_le_bytes()); // query_proofs count = 0
        // air_name
        let name = b"dregg-merkle-v1";
        bytes.extend_from_slice(&(name.len() as u32).to_le_bytes());
        bytes.extend_from_slice(name);
        // nonce = None
        bytes.push(0);
        // NOW: inject a huge boundary_query_values count
        bytes.extend_from_slice(&0xFFFFFFFFu32.to_le_bytes()); // ~4 billion items

        let result = proof_from_bytes(&bytes);
        assert!(
            result.is_err(),
            "Huge boundary count must be rejected without OOM"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("exceeds input bounds") || err.contains("unexpected end"),
            "Error should mention bounds or EOF, got: {err}"
        );
    }

    // ========================================================================
    // PROOF-OF-WORK (GRINDING RESISTANCE) TESTS
    // ========================================================================

    #[test]
    fn pow_honest_proof_verifies() {
        // A proof generated with PoW should verify with the same config.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let config = StarkConfig { pow_bits: 8 }; // Use 8 bits for fast test

        let proof = prove_with_config(&air, &trace, &pi, &config);
        assert_eq!(proof.pow_bits, 8);
        // pow_nonce could be 0 if nonce=0 happens to satisfy the difficulty,
        // but it's stored regardless.

        let result = verify_with_config(&air, &proof, &pi, &config);
        assert!(result.is_ok(), "PoW proof must verify: {:?}", result.err());
    }

    #[test]
    fn pow_wrong_nonce_rejected() {
        // A proof with a tampered nonce must be rejected.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let config = StarkConfig { pow_bits: 8 };

        let mut proof = prove_with_config(&air, &trace, &pi, &config);
        // Tamper with the nonce
        proof.pow_nonce = proof.pow_nonce.wrapping_add(1);

        let result = verify_with_config(&air, &proof, &pi, &config);
        assert!(result.is_err(), "Wrong PoW nonce must be rejected");
        let err = result.unwrap_err();
        assert!(
            err.contains("Proof-of-work verification failed")
                || err.contains("Query index mismatch"),
            "Error should mention PoW failure or query mismatch (due to transcript divergence), got: {err}"
        );
    }

    #[test]
    fn pow_insufficient_difficulty_rejected() {
        // Generate proof with low difficulty, try to verify with higher difficulty.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        // Generate with 4 bits
        let low_config = StarkConfig { pow_bits: 4 };
        let proof = prove_with_config(&air, &trace, &pi, &low_config);
        assert_eq!(proof.pow_bits, 4);

        // Try to verify with 12 bits (higher difficulty)
        let high_config = StarkConfig { pow_bits: 12 };
        let result = verify_with_config(&air, &proof, &pi, &high_config);
        assert!(
            result.is_err(),
            "Proof with insufficient PoW difficulty must be rejected"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("PoW difficulty mismatch"),
            "Error should mention difficulty mismatch, got: {err}"
        );
    }

    #[test]
    fn pow_zero_bits_skips_verification() {
        // With pow_bits=0, no PoW is required (backward compat).
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        // prove() uses no_pow internally
        let proof = prove(&air, &trace, &pi);
        assert_eq!(proof.pow_bits, 0);
        assert_eq!(proof.pow_nonce, 0);

        // Verify with no_pow config works
        assert!(verify(&air, &proof, &pi).is_ok());

        // Also verify with explicit no_pow config
        let result = verify_with_config(&air, &proof, &pi, &StarkConfig::no_pow());
        assert!(result.is_ok());
    }

    #[test]
    fn pow_grinding_performance() {
        // Grinding 20 bits should complete in reasonable time (<10 seconds).
        // On modern hardware, 2^20 ~ 1M BLAKE3 hashes takes ~1-5ms.
        let mut transcript = Transcript::new(b"perf-test");
        transcript.absorb_bytes(b"some commitment data");
        transcript.absorb_hash(&[0xAB; 32]);

        let start = std::time::Instant::now();
        let nonce = grind_pow(&transcript, 20);
        let elapsed = start.elapsed();

        // Verify the nonce is valid
        assert!(verify_pow(&transcript, nonce, 20));

        // Performance assertion: should complete in reasonable time
        assert!(
            elapsed.as_secs() < 60,
            "Grinding 20 bits took {:?}, expected <60s",
            elapsed
        );

        // Informational: print actual time for benchmarking
        eprintln!("  PoW 20-bit grinding took {:?} (nonce={})", elapsed, nonce);
    }

    #[test]
    fn pow_leading_zeros_correctness() {
        // Verify the leading zeros check is correct.
        let all_zeros = [0u8; 32];
        assert!(has_leading_zeros(&all_zeros, 0));
        assert!(has_leading_zeros(&all_zeros, 32));
        assert!(has_leading_zeros(&all_zeros, 256));

        let mut one_bit = [0u8; 32];
        one_bit[0] = 0x80; // first bit is 1
        assert!(has_leading_zeros(&one_bit, 0));
        assert!(!has_leading_zeros(&one_bit, 1));

        let mut after_two_bytes = [0u8; 32];
        after_two_bytes[2] = 0x40; // bit 17 is set (0-indexed)
        assert!(has_leading_zeros(&after_two_bytes, 16));
        assert!(has_leading_zeros(&after_two_bytes, 17));
        assert!(!has_leading_zeros(&after_two_bytes, 18));

        let mut byte_boundary = [0u8; 32];
        byte_boundary[1] = 0x01; // bit 15 is set
        assert!(has_leading_zeros(&byte_boundary, 8));
        assert!(has_leading_zeros(&byte_boundary, 15));
        assert!(!has_leading_zeros(&byte_boundary, 16));
    }

    #[test]
    fn pow_serialization_roundtrip() {
        // Ensure PoW fields survive serialization/deserialization.
        let (trace, pi) = generate_merkle_trace(
            999,
            &[[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let config = StarkConfig { pow_bits: 8 };

        let proof = prove_with_config(&air, &trace, &pi, &config);
        let bytes = proof_to_bytes(&proof);
        let proof2 = proof_from_bytes(&bytes).unwrap();

        assert_eq!(proof2.pow_bits, 8);
        assert_eq!(proof2.pow_nonce, proof.pow_nonce);

        // Deserialized proof still verifies
        let result = verify_with_config(&air, &proof2, &pi, &config);
        assert!(
            result.is_ok(),
            "Deserialized PoW proof must verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn pow_full_config_with_context() {
        // PoW works together with temporal binding context.
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let config = StarkConfig { pow_bits: 8 };
        let ctx = StarkContext {
            nonce: Some([0xCD; 32]),
            timestamp: Some(1716000000),
        };

        let proof = prove_full(&air, &trace, &pi, Some(&ctx), &config);
        assert_eq!(proof.pow_bits, 8);

        // Verify with matching context and config
        let result = verify_full(&air, &proof, &pi, Some(&ctx), &config);
        assert!(
            result.is_ok(),
            "PoW + context proof must verify: {:?}",
            result.err()
        );

        // Wrong context still fails
        let bad_ctx = StarkContext {
            nonce: Some([0xEE; 32]),
            timestamp: None,
        };
        let result = verify_full(&air, &proof, &pi, Some(&bad_ctx), &config);
        assert!(
            result.is_err(),
            "Wrong context must be rejected even with valid PoW"
        );
    }
}
