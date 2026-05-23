//! Runtime types for pyana-dsl generated code.
//!
//! This crate provides the types that proc-macro-generated code depends on:
//! `ConstraintError`, `AirConstraintSet`, `Constraint`, `KimchiCircuitDescriptor`,
//! `EffectDescriptor`, and supporting types.
//!
//! The [`circuit`] module provides a runtime-interpreted `StarkAir` implementation
//! driven by a [`circuit::CircuitDescriptor`], enabling DSL macros to emit data
//! rather than 2000 lines of codegen.
//!
//! # Smart Contract Runtime
//!
//! The [`circuit::CellProgram`] and [`circuit::ProgramRegistry`] types form the
//! smart contract runtime: user-defined cell programs (submitted as serialized
//! `CircuitDescriptor`s at deploy time) are validated, stored, and verified at
//! runtime via proof-carrying turns.

pub mod circuit;

// Re-export primary smart contract runtime types.
pub use circuit::{
    CellProgram, CircuitDescriptor, DslCircuit, ProgramError, ProgramRegistry,
    ProgramValidationError,
};

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

/// Descriptor for an AIR constraint set generated from a pyana caveat or effect.
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
    /// State transition: old_value -> new_value with an operation.
    /// Used for mutations in effects.
    Transition {
        desc: &'static str,
        old_col: usize,
        new_col: usize,
    },
    /// Merkle membership proof: element is in a committed set.
    /// The proof occupies `tree_depth * 2 + 1` columns starting at `start_col`.
    MerkleMembership {
        desc: &'static str,
        tree_depth: usize,
        start_col: usize,
    },
}

/// Descriptor for a Kimchi circuit generated from a pyana constraint.
#[derive(Debug, Clone)]
pub struct KimchiCircuitDescriptor {
    /// The gates in the circuit.
    pub gates: Vec<KimchiGate>,
    /// Number of public input cells.
    pub public_input_count: usize,
    /// Total trace width (number of witness columns).
    pub trace_width: usize,
}

/// A single gate in a Kimchi circuit.
#[derive(Debug, Clone)]
pub struct KimchiGate {
    /// The type of gate.
    pub typ: GateType,
    /// Coefficients for the gate polynomial.
    /// For Generic gates: `[c0, c1, c2, c3, c4]` enforcing
    /// `c0*w0 + c1*w1 + c2*w2 + c3*w3 + c4*w4 = 0`.
    pub coeffs: Vec<i64>,
    /// Number of wires used by this gate.
    pub wires: usize,
}

/// Kimchi gate types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateType {
    /// Generic arithmetic gate with linear combination of wires.
    Generic,
    /// Poseidon hash permutation gate (12 wires per round).
    Poseidon,
}

/// Descriptor for a pyana effect (constraint with state mutation).
#[derive(Debug, Clone)]
pub struct EffectDescriptor {
    /// Name of the effect function.
    pub name: &'static str,
    /// Names of parameters that are mutated.
    pub mutable_params: Vec<&'static str>,
    /// Required permission to invoke this effect (e.g., "Send").
    pub required_permission: Option<&'static str>,
}

/// Descriptor for a membership constraint (used for set operations).
#[derive(Debug, Clone)]
pub struct MembershipConstraint {
    /// Depth of the Merkle tree.
    pub tree_depth: usize,
    /// Identifier for the hash function used (e.g., "poseidon", "sha256").
    pub hash_function: &'static str,
}
