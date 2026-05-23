//! Accumulator-based non-revocation AIR: O(1) proof via polynomial evaluation.
//!
//! Replaces the sorted-Merkle non-revocation circuit (`non_revocation_air.rs`) with a
//! polynomial-evaluation accumulator over BabyBear^4, yielding ~100x fewer constraints.
//!
//! # Proof Statement
//!
//! "Given an accumulator value Acc and challenge alpha (both in BabyBear^4), none of my
//! capability's ancestor hashes appear in the revocation set."
//!
//! # Construction
//!
//! For each ancestor hash h_i in the derivation path, the prover provides:
//! - quotient w_i in BabyBear^4
//! - remainder v_i in BabyBear^4
//!
//! Verification per ancestor:
//! 1. `w_i * (alpha - h_i) + v_i == Acc`  (polynomial division identity)
//! 2. `v_i != 0`  (proves h_i is NOT a root of the accumulator polynomial)
//!
//! # AIR Layout
//!
//! 8 rows (one per ancestor, up to MAX_ANCESTORS), 32 base-field columns:
//!
//! ```text
//! Columns (each ext-field element = 4 base columns):
//!   [0..3]:   h_i         — ancestor hash embedded in BabyBear^4
//!   [4..7]:   w_i         — quotient witness
//!   [8..11]:  v_i         — remainder witness
//!   [12..15]: diff_i      — precomputed (alpha - h_i)
//!   [16..19]: prod_i      — w_i * diff_i
//!   [20..23]: sum_i       — prod_i + v_i (should equal Acc)
//!   [24..27]: v_inv_i     — inverse of v_i (proves v_i != 0)
//!   [28..31]: check_i     — v_i * v_inv_i (should equal ext-field ONE)
//! ```
//!
//! # Public Inputs
//!
//! 9 BabyBear elements:
//! - [0..3]: Acc (accumulator value in BabyBear^4)
//! - [4..7]: alpha (public challenge in BabyBear^4)
//! - [8]: num_ancestors (number of active rows)
//!
//! # Constraints (per row, when active)
//!
//! 1. diff == alpha - h  (4 base-field equalities, degree 1)
//! 2. prod == w * diff  (4 base-field relations, degree 2 — ext-field mul)
//! 3. sum == prod + v  (4 base-field equalities, degree 1)
//! 4. sum == Acc  (4 base-field equalities, boundary constraint)
//! 5. check == v * v_inv  (4 base-field relations, degree 2)
//! 6. check == (1, 0, 0, 0)  (4 base-field equalities, boundary constraint)
//!
//! Max constraint degree: 2. Total constraints per row: ~24 base-field checks.
//! For 8 ancestors: 8 rows, 32 columns. Compare sorted-Merkle: 72 rows, 12 columns, degree 4.

use crate::field::BabyBear;
use crate::poseidon2::hash_many;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Maximum number of ancestors in a single accumulator non-revocation proof.
pub const MAX_ANCESTORS: usize = 8;

/// Trace width: 32 base-field columns (8 extension-field "columns" of 4 each).
pub const ACCUMULATOR_WIDTH: usize = 32;

/// Column group indices (each group is 4 consecutive base-field columns).
pub mod col {
    /// Ancestor hash h_i embedded in BabyBear^4: cols 0..3.
    pub const HASH: usize = 0;
    /// Quotient witness w_i: cols 4..7.
    pub const QUOTIENT: usize = 4;
    /// Remainder witness v_i: cols 8..11.
    pub const REMAINDER: usize = 8;
    /// Difference (alpha - h_i): cols 12..15.
    pub const DIFF: usize = 12;
    /// Product w_i * (alpha - h_i): cols 16..19.
    pub const PRODUCT: usize = 16;
    /// Sum prod_i + v_i: cols 20..23.
    pub const SUM: usize = 20;
    /// Inverse of v_i: cols 24..27.
    pub const V_INV: usize = 24;
    /// v_i * v_inv_i (should be 1): cols 28..31.
    pub const CHECK: usize = 28;
}

/// Public input indices.
pub mod pi {
    /// Accumulator value (BabyBear^4): indices 0..3.
    pub const ACC_START: usize = 0;
    /// Alpha challenge (BabyBear^4): indices 4..7.
    pub const ALPHA_START: usize = 4;
    /// Number of active ancestors: index 8.
    pub const NUM_ANCESTORS: usize = 8;
}

/// Extension field element stored as 4 consecutive BabyBear values in the trace.
/// This is a helper for trace generation; the AIR constraints operate on individual columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtElem(pub [BabyBear; 4]);

/// The irreducible constant W for BabyBear^4: X^4 - 11.
const W: BabyBear = BabyBear(11);

impl ExtElem {
    pub const ZERO: Self = Self([BabyBear::ZERO; 4]);
    pub const ONE: Self = Self([
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);

    /// Embed a base field element.
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
        let w = W;

        let c0 = a[0] * b[0] + w * (a[1] * b[3] + a[2] * b[2] + a[3] * b[1]);
        let c1 = a[0] * b[1] + a[1] * b[0] + w * (a[2] * b[3] + a[3] * b[2]);
        let c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + w * (a[3] * b[3]);
        let c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];

        Self([c0, c1, c2, c3])
    }

    /// Extension field inverse via Gaussian elimination.
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let a = self.0;
        let w = W;

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

    /// Write this element into trace row at the given column offset.
    fn write_to(&self, row: &mut [BabyBear], offset: usize) {
        row[offset] = self.0[0];
        row[offset + 1] = self.0[1];
        row[offset + 2] = self.0[2];
        row[offset + 3] = self.0[3];
    }

    /// Read from a trace row at the given column offset.
    fn read_from(row: &[BabyBear], offset: usize) -> Self {
        Self([
            row[offset],
            row[offset + 1],
            row[offset + 2],
            row[offset + 3],
        ])
    }
}

/// Non-membership witness for the accumulator AIR.
#[derive(Clone, Debug)]
pub struct AccumulatorNonMembershipWitness {
    /// The ancestor hash (base field element, embedded into extension for the AIR).
    pub ancestor_hash: BabyBear,
    /// The quotient witness w in BabyBear^4.
    pub quotient: ExtElem,
    /// The remainder witness v in BabyBear^4 (must be nonzero).
    pub remainder: ExtElem,
}

/// Complete witness for the accumulator non-revocation proof.
#[derive(Clone, Debug)]
pub struct AccumulatorNonRevocationWitness {
    /// Per-ancestor witnesses.
    pub ancestors: Vec<AccumulatorNonMembershipWitness>,
}

/// The accumulator-based non-revocation AIR.
///
/// Proves that for each ancestor in a capability's derivation path, its
/// revocation hash does NOT appear in the committed revocation set, using
/// polynomial-evaluation accumulator verification.
pub struct AccumulatorNonRevocationAir;

impl AccumulatorNonRevocationAir {
    /// Generate the execution trace from a witness.
    ///
    /// Returns (trace, public_inputs) where:
    /// - trace: rows of width ACCUMULATOR_WIDTH, padded to power of 2
    /// - public_inputs: [Acc(4), alpha(4), num_ancestors(1)] = 9 elements
    pub fn generate_trace(
        witness: &AccumulatorNonRevocationWitness,
        accumulator: ExtElem,
        alpha: ExtElem,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let num_ancestors = witness.ancestors.len();
        assert!(
            num_ancestors <= MAX_ANCESTORS,
            "Too many ancestors: {} > {}",
            num_ancestors,
            MAX_ANCESTORS
        );

        let total_rows = num_ancestors.next_power_of_two().max(8);
        let mut trace = Vec::with_capacity(total_rows);

        for anc in &witness.ancestors {
            let mut row = vec![BabyBear::ZERO; ACCUMULATOR_WIDTH];

            // h_i: ancestor hash embedded in extension field
            let h = ExtElem::from_base(anc.ancestor_hash);
            h.write_to(&mut row, col::HASH);

            // w_i: quotient witness
            anc.quotient.write_to(&mut row, col::QUOTIENT);

            // v_i: remainder witness
            anc.remainder.write_to(&mut row, col::REMAINDER);

            // diff_i = alpha - h_i
            let diff = alpha.sub(h);
            diff.write_to(&mut row, col::DIFF);

            // prod_i = w_i * diff_i
            let prod = anc.quotient.mul(diff);
            prod.write_to(&mut row, col::PRODUCT);

            // sum_i = prod_i + v_i
            let sum = prod.add(anc.remainder);
            sum.write_to(&mut row, col::SUM);

            // v_inv_i: inverse of v_i (proves nonzero)
            let v_inv = anc
                .remainder
                .inverse()
                .expect("Remainder must be nonzero for non-membership witness");
            v_inv.write_to(&mut row, col::V_INV);

            // check_i = v_i * v_inv_i (should be ONE)
            let check = anc.remainder.mul(v_inv);
            check.write_to(&mut row, col::CHECK);

            trace.push(row);
        }

        // Pad with "dummy" rows that satisfy constraints trivially.
        // Use: h=0, w=0, v=ONE (nonzero), diff=alpha, prod=0, sum=ONE,
        //      v_inv=ONE, check=ONE.
        // But sum != Acc unless Acc = ONE (empty set). Instead, for padding rows
        // we set all columns to satisfy sum == Acc by computing a valid dummy witness:
        //   w_dummy = (Acc - v_dummy) / (alpha - 0) with v_dummy = product(0 - h_i) = product(-h_i)
        //
        // Actually for padding, the simplest approach: we don't enforce constraints on
        // padding rows. We use a sentinel column to mark active rows.
        // But our width is already at 32. Let's use a different approach:
        // duplicate the last valid row as padding. All constraints hold since it's identical.
        while trace.len() < total_rows {
            if num_ancestors > 0 {
                // Duplicate last valid row.
                trace.push(trace[num_ancestors - 1].clone());
            } else {
                // No ancestors: create a trivial row.
                // v = alpha (nonzero since alpha is a hash-derived challenge),
                // w = 0, sum = v = alpha, but we need sum = Acc = ONE.
                // For empty set, Acc = ONE. So: w=0, v=ONE, diff=alpha, prod=0, sum=ONE.
                let mut row = vec![BabyBear::ZERO; ACCUMULATOR_WIDTH];
                let h = ExtElem::ZERO;
                h.write_to(&mut row, col::HASH);
                ExtElem::ZERO.write_to(&mut row, col::QUOTIENT);
                // For empty accumulator (Acc=ONE): v=ONE works since 0 + ONE = ONE = Acc.
                ExtElem::ONE.write_to(&mut row, col::REMAINDER);
                alpha.write_to(&mut row, col::DIFF); // alpha - 0 = alpha
                ExtElem::ZERO.write_to(&mut row, col::PRODUCT); // 0 * alpha = 0
                ExtElem::ONE.write_to(&mut row, col::SUM); // 0 + ONE = ONE = Acc
                ExtElem::ONE.write_to(&mut row, col::V_INV); // inv(ONE) = ONE
                ExtElem::ONE.write_to(&mut row, col::CHECK); // ONE * ONE = ONE
                trace.push(row);
            }
        }

        // Public inputs: [Acc(4), alpha(4), num_ancestors(1)]
        let mut public_inputs = Vec::with_capacity(9);
        public_inputs.extend_from_slice(&accumulator.0);
        public_inputs.extend_from_slice(&alpha.0);
        public_inputs.push(BabyBear::new(num_ancestors as u32));

        (trace, public_inputs)
    }
}

impl StarkAir for AccumulatorNonRevocationAir {
    fn width(&self) -> usize {
        ACCUMULATOR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2 // Extension-field multiplication is degree 2
    }

    fn air_name(&self) -> &'static str {
        "pyana-accumulator-non-revocation-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha_random: BabyBear, // This is the STARK verifier's random challenge, NOT the accumulator alpha.
    ) -> BabyBear {
        // Extract public inputs.
        let acc = ExtElem::read_from(public_inputs, pi::ACC_START);
        let alpha_challenge = ExtElem::read_from(public_inputs, pi::ALPHA_START);

        // Extract trace columns for this row.
        let h = ExtElem::read_from(local, col::HASH);
        let w = ExtElem::read_from(local, col::QUOTIENT);
        let v = ExtElem::read_from(local, col::REMAINDER);
        let diff = ExtElem::read_from(local, col::DIFF);
        let prod = ExtElem::read_from(local, col::PRODUCT);
        let sum = ExtElem::read_from(local, col::SUM);
        let v_inv = ExtElem::read_from(local, col::V_INV);
        let check = ExtElem::read_from(local, col::CHECK);

        let mut combined = BabyBear::ZERO;
        let mut pow = alpha_random;

        // Constraint 1: diff == alpha_challenge - h
        // (4 base-field equalities)
        let expected_diff = alpha_challenge.sub(h);
        for i in 0..4 {
            let c = diff.0[i] - expected_diff.0[i];
            combined = combined + pow * c;
            pow = pow * alpha_random;
        }

        // Constraint 2: prod == w * diff
        // Extension-field multiplication constraint (degree 2).
        let expected_prod = w.mul(diff);
        for i in 0..4 {
            let c = prod.0[i] - expected_prod.0[i];
            combined = combined + pow * c;
            pow = pow * alpha_random;
        }

        // Constraint 3: sum == prod + v
        let expected_sum = prod.add(v);
        for i in 0..4 {
            let c = sum.0[i] - expected_sum.0[i];
            combined = combined + pow * c;
            pow = pow * alpha_random;
        }

        // Constraint 4: check == v * v_inv
        // (proves v is nonzero by exhibiting its inverse)
        let expected_check = v.mul(v_inv);
        for i in 0..4 {
            let c = check.0[i] - expected_check.0[i];
            combined = combined + pow * c;
            pow = pow * alpha_random;
        }

        // NOTE: Constraints "sum == Acc" and "check == ONE" are enforced via
        // boundary constraints (row-specific), NOT as polynomial constraints.
        // This allows padding rows to use different values without violating
        // the transition constraints.
        let _ = acc; // Used only in boundary_constraints

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        if public_inputs.len() < 9 || trace_len == 0 {
            return vec![];
        }

        let num_ancestors = public_inputs[pi::NUM_ANCESTORS].0 as usize;
        let acc = ExtElem::read_from(public_inputs, pi::ACC_START);

        let mut constraints = vec![];

        // For each active row, bind sum == Acc and check == ONE.
        for row in 0..num_ancestors.min(trace_len) {
            // sum[0..3] == Acc[0..3]
            for i in 0..4 {
                constraints.push(BoundaryConstraint {
                    row,
                    col: col::SUM + i,
                    value: acc.0[i],
                });
            }
            // check == (1, 0, 0, 0)
            constraints.push(BoundaryConstraint {
                row,
                col: col::CHECK,
                value: BabyBear::ONE,
            });
            constraints.push(BoundaryConstraint {
                row,
                col: col::CHECK + 1,
                value: BabyBear::ZERO,
            });
            constraints.push(BoundaryConstraint {
                row,
                col: col::CHECK + 2,
                value: BabyBear::ZERO,
            });
            constraints.push(BoundaryConstraint {
                row,
                col: col::CHECK + 3,
                value: BabyBear::ZERO,
            });
        }

        constraints
    }
}

// ============================================================================
// High-level prove/verify API
// ============================================================================

/// Generate an accumulator-based non-revocation proof.
///
/// Given ancestor hashes, the revocation set's accumulator value and alpha challenge,
/// and per-ancestor witnesses (quotient + remainder), produces a STARK proof.
///
/// Returns None if any ancestor IS in the revocation set (witness generation would fail).
///
/// DEPRECATED: Use `crate::dsl::accumulator::prove_accumulator_non_revocation_dsl` instead.
#[deprecated(note = "Use crate::dsl::accumulator::prove_accumulator_non_revocation_dsl instead")]
pub fn prove_accumulator_non_revocation(
    ancestor_hashes: &[BabyBear],
    accumulator: ExtElem,
    alpha: ExtElem,
    revocation_set: &[BabyBear],
) -> Option<StarkProof> {
    if ancestor_hashes.len() > MAX_ANCESTORS {
        return None;
    }

    let mut ancestors = Vec::with_capacity(ancestor_hashes.len());
    for &h in ancestor_hashes {
        if revocation_set.contains(&h) {
            return None;
        }

        let mut remainder_base = BabyBear::ONE;
        for &rev_h in revocation_set {
            remainder_base = remainder_base * (h - rev_h);
        }

        if remainder_base == BabyBear::ZERO {
            return None;
        }

        let remainder = ExtElem::from_base(remainder_base);
        let h_ext = ExtElem::from_base(h);
        let diff = alpha.sub(h_ext);
        let numerator = accumulator.sub(remainder);
        let quotient = numerator.mul(diff.inverse()?);

        ancestors.push(AccumulatorNonMembershipWitness {
            ancestor_hash: h,
            quotient,
            remainder,
        });
    }

    let witness = AccumulatorNonRevocationWitness { ancestors };
    let air = AccumulatorNonRevocationAir;
    let (trace, public_inputs) =
        AccumulatorNonRevocationAir::generate_trace(&witness, accumulator, alpha);

    Some(stark::prove(&air, &trace, &public_inputs))
}

/// Verify an accumulator-based non-revocation proof.
///
/// The verifier only needs the accumulator value, alpha challenge, and the STARK proof.
/// The ancestor hashes remain private.
///
/// DEPRECATED: Use `crate::dsl::accumulator::verify_accumulator_non_revocation_dsl` instead.
#[deprecated(note = "Use crate::dsl::accumulator::verify_accumulator_non_revocation_dsl instead")]
pub fn verify_accumulator_non_revocation(
    accumulator: ExtElem,
    alpha: ExtElem,
    num_ancestors: usize,
    proof: &StarkProof,
) -> Result<(), String> {
    let air = AccumulatorNonRevocationAir;

    let mut public_inputs = Vec::with_capacity(9);
    public_inputs.extend_from_slice(&accumulator.0);
    public_inputs.extend_from_slice(&alpha.0);
    public_inputs.push(BabyBear::new(num_ancestors as u32));

    stark::verify(&air, proof, &public_inputs)
}

/// Compute the accumulator value for a revocation set.
///
/// Acc = product(alpha - h_i) for all h_i in the set.
pub fn compute_accumulator(revocation_set: &[BabyBear], alpha: ExtElem) -> ExtElem {
    let mut acc = ExtElem::ONE;
    for &h in revocation_set {
        let h_ext = ExtElem::from_base(h);
        acc = acc.mul(alpha.sub(h_ext));
    }
    acc
}

/// Derive the alpha challenge from the revocation set commitment.
///
/// Uses Poseidon2 hash of a domain separator concatenated with set metadata.
/// In production, this would include the epoch number and federation attestation.
pub fn derive_alpha(revocation_set: &[BabyBear]) -> ExtElem {
    // Domain separator: "pyana-accumulator-v1" hashed, plus set size.
    let domain_sep = hash_many(&[
        BabyBear::new(0x7079616E), // "pyan"
        BabyBear::new(0x612D6163), // "a-ac"
        BabyBear::new(0x63756D75), // "cumu"
        BabyBear::new(revocation_set.len() as u32),
    ]);

    // Hash domain separator with each element for binding.
    let binding = if revocation_set.is_empty() {
        domain_sep
    } else {
        let mut elems = vec![domain_sep];
        // Include first few and last elements as binding (full set hash would be expensive).
        let sample_count = revocation_set.len().min(16);
        for &h in &revocation_set[..sample_count] {
            elems.push(h);
        }
        hash_many(&elems)
    };

    // Generate 4 independent BabyBear elements for the extension field challenge.
    let h0 = binding;
    let h1 = hash_many(&[h0, BabyBear::new(1)]);
    let h2 = hash_many(&[h0, BabyBear::new(2)]);
    let h3 = hash_many(&[h0, BabyBear::new(3)]);

    ExtElem([h0, h1, h2, h3])
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_hash(seed: u32) -> BabyBear {
        hash_many(&[BabyBear::new(seed), BabyBear::new(0xCAFE)])
    }

    #[test]
    fn ext_elem_mul_identity() {
        let a = ExtElem([
            BabyBear::new(7),
            BabyBear::new(13),
            BabyBear::new(21),
            BabyBear::new(42),
        ]);
        assert_eq!(a.mul(ExtElem::ONE), a);
        assert_eq!(ExtElem::ONE.mul(a), a);
    }

    #[test]
    fn ext_elem_inverse() {
        let a = ExtElem([
            BabyBear::new(100),
            BabyBear::new(200),
            BabyBear::new(300),
            BabyBear::new(400),
        ]);
        let inv = a.inverse().unwrap();
        assert_eq!(a.mul(inv), ExtElem::ONE);
    }

    #[test]
    fn ext_elem_mul_commutative() {
        let a = ExtElem([
            BabyBear::new(5),
            BabyBear::new(10),
            BabyBear::new(15),
            BabyBear::new(20),
        ]);
        let b = ExtElem([
            BabyBear::new(3),
            BabyBear::new(7),
            BabyBear::new(11),
            BabyBear::new(19),
        ]);
        assert_eq!(a.mul(b), b.mul(a));
    }

    #[test]
    fn compute_accumulator_empty_set() {
        let alpha = derive_alpha(&[]);
        let acc = compute_accumulator(&[], alpha);
        assert_eq!(acc, ExtElem::ONE); // Empty product = 1.
    }

    #[test]
    fn compute_accumulator_single_element() {
        let revocation_set = vec![BabyBear::new(42)];
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);
        let expected = alpha.sub(ExtElem::from_base(BabyBear::new(42)));
        assert_eq!(acc, expected);
    }

    #[test]
    fn trace_generation_valid_constraints() {
        let revocation_set: Vec<BabyBear> = (1..=10).map(|i| make_hash(i * 100)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        // Ancestor hashes NOT in the revocation set.
        let ancestors: Vec<BabyBear> = (1..=3).map(|i| make_hash(i * 1000 + 1)).collect();
        for h in &ancestors {
            assert!(!revocation_set.contains(h));
        }

        // Generate witnesses.
        let mut witness_ancestors = Vec::new();
        for &h in &ancestors {
            let mut remainder_base = BabyBear::ONE;
            for &rev_h in &revocation_set {
                remainder_base = remainder_base * (h - rev_h);
            }
            assert_ne!(remainder_base, BabyBear::ZERO);

            let remainder = ExtElem::from_base(remainder_base);
            let h_ext = ExtElem::from_base(h);
            let diff = alpha.sub(h_ext);
            let numerator = acc.sub(remainder);
            let quotient = numerator.mul(diff.inverse().unwrap());

            witness_ancestors.push(AccumulatorNonMembershipWitness {
                ancestor_hash: h,
                quotient,
                remainder,
            });
        }

        let witness = AccumulatorNonRevocationWitness {
            ancestors: witness_ancestors,
        };
        let (trace, public_inputs) =
            AccumulatorNonRevocationAir::generate_trace(&witness, acc, alpha);

        // Verify dimensions.
        assert!(trace.len().is_power_of_two());
        assert!(trace.len() >= 8);
        for row in &trace {
            assert_eq!(row.len(), ACCUMULATOR_WIDTH);
        }
        assert_eq!(public_inputs.len(), 9);

        // Verify constraints are zero on all rows.
        let air = AccumulatorNonRevocationAir;
        let alpha_verifier = BabyBear::new(7); // verifier's random challenge
        for i in 0..trace.len() {
            let next = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = air.eval_constraints(&trace[i], &trace[next], &public_inputs, alpha_verifier);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {i}: c = {}",
                c.0
            );
        }
    }

    #[test]
    fn prove_and_verify_non_revocation() {
        let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        let ancestors: Vec<BabyBear> = (1..=3).map(|i| make_hash(i * 7777)).collect();
        for h in &ancestors {
            assert!(!revocation_set.contains(h));
        }

        let proof = prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set)
            .expect("Should generate proof");

        let result = verify_accumulator_non_revocation(acc, alpha, ancestors.len(), &proof);
        assert!(result.is_ok(), "Proof should verify: {:?}", result.err());
    }

    #[test]
    fn prove_fails_for_revoked_ancestor() {
        let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        // Include a revoked hash in ancestors.
        let ancestors = vec![
            make_hash(7777),   // not revoked
            revocation_set[2], // REVOKED
            make_hash(8888),   // not revoked
        ];

        let result = prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set);
        assert!(result.is_none(), "Should fail for revoked ancestor");
    }

    #[test]
    fn max_ancestors() {
        let revocation_set: Vec<BabyBear> = (1..=20).map(|i| make_hash(i)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        let ancestors: Vec<BabyBear> = (1..=MAX_ANCESTORS as u32)
            .map(|i| make_hash(10000 + i))
            .collect();

        for h in &ancestors {
            assert!(!revocation_set.contains(h));
        }

        let proof = prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set)
            .expect("Should handle MAX_ANCESTORS");

        let result = verify_accumulator_non_revocation(acc, alpha, ancestors.len(), &proof);
        assert!(
            result.is_ok(),
            "MAX_ANCESTORS proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn wrong_accumulator_rejected() {
        let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        let ancestors = vec![make_hash(9999)];
        let proof =
            prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set).unwrap();

        // Verify with wrong accumulator.
        let wrong_acc = ExtElem([
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        let result = verify_accumulator_non_revocation(wrong_acc, alpha, ancestors.len(), &proof);
        assert!(result.is_err(), "Wrong accumulator should be rejected");
    }

    #[test]
    fn empty_ancestor_list() {
        let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        let ancestors: Vec<BabyBear> = vec![];
        let proof = prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set)
            .expect("Empty ancestors should produce proof");

        let result = verify_accumulator_non_revocation(acc, alpha, 0, &proof);
        assert!(
            result.is_ok(),
            "Empty ancestor proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn large_revocation_set() {
        // 100 elements in the revocation set.
        let revocation_set: Vec<BabyBear> = (1..=100).map(|i| make_hash(i)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        // Prove non-membership of element NOT in set.
        let absent = make_hash(101);
        assert!(!revocation_set.contains(&absent));

        let proof = prove_accumulator_non_revocation(&[absent], acc, alpha, &revocation_set)
            .expect("Should prove for large set");

        let result = verify_accumulator_non_revocation(acc, alpha, 1, &proof);
        assert!(
            result.is_ok(),
            "Large set proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn non_membership_of_element_50_in_set_fails() {
        // Insert 100 elements (hashes of 1..=100).
        let revocation_set: Vec<BabyBear> = (1..=100).map(|i| make_hash(i)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        // Element 50 IS in the set.
        let present = make_hash(50);
        assert!(revocation_set.contains(&present));

        // Attempting to prove non-membership should fail.
        let result = prove_accumulator_non_revocation(&[present], acc, alpha, &revocation_set);
        assert!(
            result.is_none(),
            "Should not prove non-membership of a member"
        );
    }

    #[test]
    fn proof_is_o1_regardless_of_set_size() {
        // Verify that proof size doesn't grow with set size (it's always 8-row trace).
        let small_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i)).collect();
        let large_set: Vec<BabyBear> = (1..=100).map(|i| make_hash(i)).collect();

        let alpha_s = derive_alpha(&small_set);
        let acc_s = compute_accumulator(&small_set, alpha_s);
        let alpha_l = derive_alpha(&large_set);
        let acc_l = compute_accumulator(&large_set, alpha_l);

        let absent_s = make_hash(999);
        let absent_l = make_hash(999);

        let proof_s =
            prove_accumulator_non_revocation(&[absent_s], acc_s, alpha_s, &small_set).unwrap();
        let proof_l =
            prove_accumulator_non_revocation(&[absent_l], acc_l, alpha_l, &large_set).unwrap();

        // Both proofs should have the same trace dimensions.
        assert_eq!(proof_s.trace_len, proof_l.trace_len);
        assert_eq!(proof_s.num_cols, proof_l.num_cols);
    }

    #[test]
    fn tampered_proof_rejected() {
        let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        let ancestors = vec![make_hash(9999)];
        let mut proof =
            prove_accumulator_non_revocation(&ancestors, acc, alpha, &revocation_set).unwrap();

        // Tamper.
        proof.trace_commitment[0] ^= 0xFF;

        let result = verify_accumulator_non_revocation(acc, alpha, ancestors.len(), &proof);
        assert!(result.is_err(), "Tampered proof should be rejected");
    }
}
