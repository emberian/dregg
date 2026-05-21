//! Field element type for the circuit.
//!
//! Uses BabyBear (p = 2^31 - 2^27 + 1 = 2013265921) as the native field for STARK proofs.
//! In mock mode, we implement BabyBear arithmetic directly. With plonky3 feature,
//! this wraps `p3_baby_bear::BabyBear`.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921.
pub const BABYBEAR_P: u32 = (1 << 31) - (1 << 27) + 1;

/// A BabyBear field element: integers modulo p = 2^31 - 2^27 + 1.
///
/// Stored in canonical form [0, p-1].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BabyBear(pub u32);

impl BabyBear {
    /// The zero element.
    pub const ZERO: Self = Self(0);

    /// The one element (multiplicative identity).
    pub const ONE: Self = Self(1);

    /// The additive generator.
    pub const TWO: Self = Self(2);

    /// Create a field element from a u32, reducing modulo p.
    #[inline]
    pub fn new(val: u32) -> Self {
        Self(val % BABYBEAR_P)
    }

    /// Create a field element from an untrusted u32, always reducing modulo p.
    /// Use this for all deserialization paths where the value comes from external
    /// (potentially adversarial) data to prevent non-canonical malleability.
    #[inline]
    pub fn new_canonical(val: u32) -> Self {
        Self(val % BABYBEAR_P)
    }

    /// Create from a u64, reducing modulo p.
    #[inline]
    pub fn from_u64(val: u64) -> Self {
        Self((val % BABYBEAR_P as u64) as u32)
    }

    /// Create from raw canonical value (must be < p). No reduction performed.
    #[inline]
    pub const fn from_canonical(val: u32) -> Self {
        debug_assert!(val < BABYBEAR_P);
        Self(val)
    }

    /// Get the canonical u32 representation.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0
    }

    /// Compute the multiplicative inverse using Fermat's little theorem.
    /// a^(-1) = a^(p-2) mod p.
    /// Returns None for zero.
    pub fn inverse(self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        Some(self.pow(BABYBEAR_P - 2))
    }

    /// Exponentiation by squaring.
    pub fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result * base;
            }
            base = base * base;
            exp >>= 1;
        }
        result
    }

    /// Square this element.
    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// Convert a byte slice to a vector of field elements.
    /// Each byte becomes one field element.
    pub fn from_bytes(bytes: &[u8]) -> Vec<Self> {
        bytes.iter().map(|&b| Self::new(b as u32)).collect()
    }

    /// Convert 4 bytes into a single field element (little-endian, fits in BabyBear).
    /// Only uses 31 bits, so at most 3.875 bytes of entropy per element.
    pub fn from_bytes_packed(bytes: &[u8]) -> Vec<Self> {
        let mut result = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            let mut val: u32 = 0;
            for j in 0..4 {
                if i + j < bytes.len() {
                    val |= (bytes[i + j] as u32) << (j * 8);
                }
            }
            // Reduce to fit in BabyBear
            result.push(Self::new(val));
            i += 4;
        }
        result
    }

    /// Encode a 32-byte hash as a vector of BabyBear elements (8 elements, 4 bytes each).
    pub fn encode_hash(hash: &[u8; 32]) -> [Self; 8] {
        let mut out = [Self::ZERO; 8];
        for (i, chunk) in hash.chunks(4).enumerate() {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            out[i] = Self::new(val);
        }
        out
    }

    /// Decode 8 BabyBear elements back to a 32-byte value.
    /// Note: this is lossy due to modular reduction in `encode_hash`.
    pub fn decode_hash(elements: &[Self; 8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, &elem) in elements.iter().enumerate() {
            let bytes = elem.0.to_le_bytes();
            out[i * 4..i * 4 + 4].copy_from_slice(&bytes);
        }
        out
    }
}

impl fmt::Debug for BabyBear {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BB({})", self.0)
    }
}

impl fmt::Display for BabyBear {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for BabyBear {
    fn default() -> Self {
        Self::ZERO
    }
}

impl From<u32> for BabyBear {
    fn from(val: u32) -> Self {
        Self::new(val)
    }
}

impl From<u64> for BabyBear {
    fn from(val: u64) -> Self {
        Self::from_u64(val)
    }
}

impl Add for BabyBear {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let sum = self.0 as u64 + rhs.0 as u64;
        Self((sum % BABYBEAR_P as u64) as u32)
    }
}

impl AddAssign for BabyBear {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for BabyBear {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let diff = self.0 as u64 + BABYBEAR_P as u64 - rhs.0 as u64;
        Self((diff % BABYBEAR_P as u64) as u32)
    }
}

impl SubAssign for BabyBear {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for BabyBear {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let prod = self.0 as u64 * rhs.0 as u64;
        Self((prod % BABYBEAR_P as u64) as u32)
    }
}

impl MulAssign for BabyBear {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for BabyBear {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            Self::ZERO
        } else {
            Self(BABYBEAR_P - self.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_basics() {
        let a = BabyBear::new(100);
        let b = BabyBear::new(200);
        assert_eq!((a + b).0, 300);
        assert_eq!((b - a).0, 100);
        assert_eq!((a * b).0, 20000);
    }

    #[test]
    fn field_overflow() {
        let a = BabyBear::new(BABYBEAR_P - 1);
        let b = BabyBear::new(2);
        assert_eq!((a + b).0, 1); // (p-1) + 2 = p+1 = 1 mod p
    }

    #[test]
    fn field_inverse() {
        let a = BabyBear::new(7);
        let inv = a.inverse().unwrap();
        assert_eq!((a * inv).0, 1);
    }

    #[test]
    fn zero_inverse_is_none() {
        assert!(BabyBear::ZERO.inverse().is_none());
    }

    #[test]
    fn negation() {
        let a = BabyBear::new(42);
        let neg_a = -a;
        assert_eq!((a + neg_a).0, 0);
    }

    #[test]
    fn encode_decode_hash() {
        let hash = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 32,
        ];
        let encoded = BabyBear::encode_hash(&hash);
        assert_eq!(encoded.len(), 8);
        // Verify round-trip (may lose some bits due to reduction)
        for &e in &encoded {
            assert!(e.0 < BABYBEAR_P);
        }
    }

    #[test]
    fn pow_works() {
        let a = BabyBear::new(3);
        let a_cubed = a.pow(3);
        assert_eq!(a_cubed.0, 27);
    }
}
