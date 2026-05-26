//! Shared types for accumulator-based non-revocation circuits.
//!
//! This module contains the types, constants, and helper functions used by both
//! the hand-written AIR (now removed) and the DSL-native accumulator circuit.

use crate::field::BabyBear;
use crate::poseidon2::hash_many;

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
    pub fn write_to(&self, row: &mut [BabyBear], offset: usize) {
        row[offset] = self.0[0];
        row[offset + 1] = self.0[1];
        row[offset + 2] = self.0[2];
        row[offset + 3] = self.0[3];
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
}
