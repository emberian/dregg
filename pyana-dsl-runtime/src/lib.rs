//! Runtime types for pyana-dsl generated code.
//!
//! This crate provides the types that proc-macro-generated code depends on:
//! `ConstraintError`, `AirConstraintSet`, and `Constraint`.

/// Error returned when a caveat constraint is violated at runtime.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintError {
    /// A `require!()` check failed within a caveat.
    CaveatViolation(&'static str),
}

impl core::fmt::Display for ConstraintError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ConstraintError::CaveatViolation(name) => {
                write!(f, "caveat '{}' violated", name)
            }
        }
    }
}

impl std::error::Error for ConstraintError {}

/// Descriptor for an AIR constraint set generated from a pyana caveat.
///
/// This is metadata — it describes the constraint topology (trace width,
/// column assignments, constraint types) without containing the actual
/// AIR implementation. A separate codegen step or runtime interpreter
/// uses this descriptor to produce the real AIR.
#[derive(Debug, Clone)]
pub struct AirConstraintSet {
    /// Name of the constraint (matches the original function name).
    pub name: &'static str,
    /// Total trace width (number of columns).
    pub width: usize,
    /// The constraints that must hold over the trace.
    pub constraints: Vec<Constraint>,
    /// Names of columns that are public inputs.
    pub public_inputs: Vec<&'static str>,
}

/// A single constraint within an AIR descriptor.
#[derive(Debug, Clone)]
pub enum Constraint {
    /// Range check: `diff = a - b` must be non-negative.
    /// Enforced via a high-bit check column.
    RangeCheck {
        desc: &'static str,
        diff_col: usize,
        bit_col: usize,
    },
    /// Equality: two expressions must be equal.
    Equality { desc: &'static str },
    /// Non-equality: two expressions must differ.
    /// Requires an inverse witness column.
    NonEquality {
        desc: &'static str,
        inverse_col: usize,
    },
}
