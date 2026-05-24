//! Witness-generation and algebraic verification primitives for the pyana-dsl
//! differential testing infrastructure.
//!
//! The differential test (`02-testing.md` section 2) emits, for each
//! `#[pyana_caveat]`, a `proptest!` test that asserts the Rust evaluator
//! (`{name}_check`) and the AIR descriptor's algebraic constraints agree on
//! the same input.
//!
//! This module centralizes the per-constraint-shape witness construction and
//! the "constraint evaluates to zero on the trace" check. Today, every
//! backend (gen_plonky3, gen_kimchi, emit_stark_impl, ...) reproduces this
//! algebra independently. The differential test uses *only* this module, so
//! drift between hand-written backends is detectable.
//!
//! Supported shapes today (covering all of [`crate::Constraint`] for caveats):
//!
//! - `RangeCheck { diff_col, bit_col }` — witness is `diff = right - left`
//!   when the requirement is `left <= right` (and symmetrically for `>=`).
//!   The algebraic check is `diff` fits in 64 bits — i.e. the subtraction
//!   did not underflow.
//!
//! - `Equality { .. }` — witness is just `left == right`.
//!
//! - `NonEquality { inverse_col }` — witness is the multiplicative inverse
//!   of `(left - right)` in u128 arithmetic. The algebraic check is
//!   `(left - right) * inv == 1`.
//!
//! - `MerkleMembership` — witness is the path. For HashSet-backed caveats
//!   we model this as "element is in set" without recomputing the Merkle
//!   tree (the AIR-side hash chain is verified independently by the backend
//!   tests). The differential test for membership uses the canonical
//!   `HashSet::contains` semantics — that's the meaning the IR captures.
//!
//! `Transition { .. }` (effect mutations) is NOT covered yet — see
//! the `compile_error!` stub in `gen_diff_test.rs` for the rationale.

/// A single typed scalar input to a differential check.
///
/// Caveats accept `u64` and `[u8; 32]` parameters (and `&HashSet<u64>`,
/// `&Set` for membership). We treat `[u8; 32]` as 32 stable bytes for
/// equality comparisons.
#[derive(Debug, Clone)]
pub enum DiffValue {
    /// A `u64` parameter value.
    U64(u64),
    /// A `[u8; 32]` parameter value.
    Bytes32([u8; 32]),
}

impl DiffValue {
    /// Best-effort interpretation as `u64`. For `Bytes32`, returns the
    /// little-endian interpretation of the first 8 bytes (lossy — only
    /// meaningful for equality checks).
    pub fn as_u64_lossy(&self) -> u64 {
        match self {
            DiffValue::U64(v) => *v,
            DiffValue::Bytes32(b) => {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&b[..8]);
                u64::from_le_bytes(buf)
            }
        }
    }

    /// True iff both values are byte-for-byte equal.
    pub fn bitwise_equal(&self, other: &DiffValue) -> bool {
        match (self, other) {
            (DiffValue::U64(a), DiffValue::U64(b)) => a == b,
            (DiffValue::Bytes32(a), DiffValue::Bytes32(b)) => a == b,
            _ => false,
        }
    }
}

/// Outcome of running the AIR-side differential check for one requirement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiffOutcome {
    /// All constraints witnessed; the AIR descriptor would accept the trace.
    Accept,
    /// At least one constraint cannot be witnessed; the AIR descriptor
    /// would reject the trace.
    Reject,
}

/// Verify a `LessEqual(left, right)` requirement.
///
/// Witness: `diff = right - left` as `u128` (so underflow is observable
/// instead of wrapping). Algebraic constraint: `diff < 2^64`. If
/// `left <= right` the subtraction is non-negative, the witness fits in 64
/// bits, and the high-bit indicator (bit_col) is 0; we return Accept.
/// Otherwise Reject.
pub fn check_le(left: u64, right: u64) -> DiffOutcome {
    let l = left as u128;
    let r = right as u128;
    if r < l {
        // Underflow in u64 subtraction → AIR's bit_col witness would be 1
        // (or no valid witness exists in u64). The AIR rejects.
        return DiffOutcome::Reject;
    }
    let diff = r - l;
    debug_assert!(diff < (1u128 << 64));
    DiffOutcome::Accept
}

/// Verify a `GreaterEqual(left, right)` requirement.
///
/// Symmetric to [`check_le`] with sides swapped.
pub fn check_ge(left: u64, right: u64) -> DiffOutcome {
    check_le(right, left)
}

/// Verify an `Equal(left, right)` requirement, for both u64 and [u8; 32].
pub fn check_equal(left: &DiffValue, right: &DiffValue) -> DiffOutcome {
    if left.bitwise_equal(right) {
        DiffOutcome::Accept
    } else {
        DiffOutcome::Reject
    }
}

/// Verify a `NotEqual(left, right)` requirement.
///
/// Witness: `inv = 1 / (left - right)` in modular arithmetic. The constraint
/// `(left - right) * inv == 1` is unsatisfiable iff `left == right`.
pub fn check_not_equal(left: &DiffValue, right: &DiffValue) -> DiffOutcome {
    if left.bitwise_equal(right) {
        DiffOutcome::Reject
    } else {
        DiffOutcome::Accept
    }
}

/// Verify a `Membership(set, element)` requirement.
///
/// The AIR-side witness is the Merkle path; the algebraic check is that
/// hashing the leaf with the siblings according to the position bits yields
/// the root. For the differential test the semantic-truth we cross-check
/// against the Rust evaluator is `HashSet::contains`. Backend-specific
/// Merkle-tree witness validity is tested by each backend's own tests.
pub fn check_membership(set: &std::collections::HashSet<u64>, element: u64) -> DiffOutcome {
    if set.contains(&element) {
        DiffOutcome::Accept
    } else {
        DiffOutcome::Reject
    }
}

/// Trait to lift a runtime parameter value into a [`DiffValue`].
///
/// Implemented for `u64`, `[u8; 32]`, and references thereto so that the
/// macro-emitted `__pyana_diff_to_value(&expr)` shim can accept either.
pub trait IntoDiffValue {
    fn into_diff_value(&self) -> DiffValue;
}

impl IntoDiffValue for u64 {
    fn into_diff_value(&self) -> DiffValue {
        DiffValue::U64(*self)
    }
}

impl IntoDiffValue for [u8; 32] {
    fn into_diff_value(&self) -> DiffValue {
        DiffValue::Bytes32(*self)
    }
}

impl<T: IntoDiffValue + ?Sized> IntoDiffValue for &T {
    fn into_diff_value(&self) -> DiffValue {
        (**self).into_diff_value()
    }
}

/// Combine multiple per-requirement outcomes with logical AND. Used when an
/// IR statement is `match` with multiple arms or when the body has several
/// `require!` calls — the AIR accepts iff *every* constraint accepts.
pub fn combine_and<I: IntoIterator<Item = DiffOutcome>>(iter: I) -> DiffOutcome {
    for o in iter {
        if o == DiffOutcome::Reject {
            return DiffOutcome::Reject;
        }
    }
    DiffOutcome::Accept
}
