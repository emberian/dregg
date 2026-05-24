//! Runtime types for pyana-dsl generated code.
//!
//! This crate re-exports DSL infrastructure from `pyana_circuit::dsl`. The actual
//! implementation lives in `pyana-circuit` to avoid circular dependencies.
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

// Re-export all DSL modules from pyana-circuit.
pub use pyana_circuit::dsl::accumulator;
pub use pyana_circuit::dsl::circuit;
pub use pyana_circuit::dsl::derivation;
pub use pyana_circuit::dsl::descriptors;
pub use pyana_circuit::dsl::fold;
pub use pyana_circuit::dsl::garbled;
pub use pyana_circuit::dsl::membership;
pub use pyana_circuit::dsl::note_spending;
pub use pyana_circuit::dsl::predicates;
pub use pyana_circuit::dsl::revocation;
pub use pyana_circuit::dsl::temporal_absence;

// Re-export the composition module which stays here (no circuit dependency needed
// beyond what pyana_circuit::dsl already provides).
pub mod composition;

/// Algebraic witness-construction helpers used by `gen_diff_test`-emitted
/// proptests and by the cross-backend differential harness in
/// `pyana-dsl-differential`.
pub mod diff_witness;

// Re-export composition primitives.
#[allow(deprecated)]
pub use composition::{
    AttachedSubProof, ComposedCircuitDescriptor, ComposedDslCircuit, ComposedProof,
    ComposedVerification, IvcBinding, SubProofBinding, compose_aggregate, compose_and,
    compose_chain, compose_or, compute_descriptor_vk_elements, generate_and_trace,
    generate_chain_trace, verify_composed, verify_composed_full,
};

#[cfg(feature = "plonky3")]
pub mod dsl_plonky3;

// Re-export Plonky3 DSL proving API.
#[cfg(feature = "plonky3")]
pub use dsl_plonky3::{DslP3Air, prove_dsl_plonky3, verify_dsl_plonky3};

// Re-export primary smart contract runtime types.
pub use pyana_circuit::dsl::{
    BoundaryDef, BoundaryRow, CellProgram, CircuitDescriptor, ColumnDef, ColumnKind,
    ConstraintExpr, DslCircuit, PolyTerm, ProgramError, ProgramRegistry, ProgramValidationError,
};

// Re-export production garbled circuit evaluation API.
pub use pyana_circuit::dsl::garbled::{
    ExtendedGateRecord, GarbledDslProof, GateType as GarbledGateType, prove_garbled_evaluation_dsl,
    prove_garbled_evaluation_extended_dsl, prove_private_threshold_dsl,
    verify_garbled_evaluation_dsl, verify_private_threshold_dsl,
};

// Re-export production temporal absence API.
pub use pyana_circuit::dsl::temporal_absence::{
    DslTimelineEntry, TemporalAbsenceDslProof, TemporalAbsenceDslWitness,
    prove_temporal_absence_dsl, verify_temporal_absence_dsl,
};

// Re-export production non-revocation proving API.
pub use pyana_circuit::dsl::revocation::{
    DslRevocationTree, NonMembershipWitnessDsl, REVOCATION_TREE_DEPTH, SENTINEL_MAX, SENTINEL_MIN,
    TREE_DEPTH, generate_non_revocation_trace, non_revocation_dsl_circuit,
    prove_non_revocation_dsl, revocation_hash_to_field, verify_non_revocation_dsl,
};

// Re-export DSL-native fold proving API.
pub use pyana_circuit::dsl::fold::{
    FOLD_DSL_PI_COUNT, FOLD_DSL_WIDTH, fold_circuit_descriptor, fold_dsl_circuit,
    generate_fold_trace, prove_fold_dsl, prove_fold_stark, verify_fold_dsl, verify_fold_stark,
};

// Re-export DSL-native note spending proving API.
pub use pyana_circuit::dsl::note_spending::{
    generate_note_spending_trace, note_spending_circuit_descriptor, note_spending_dsl_circuit,
    prove_note_spend, prove_note_spend_dsl, verify_note_spend, verify_note_spend_dsl,
    verify_note_spend_dsl_with_destination,
};

// Re-export DSL-native accumulator proving API.
pub use pyana_circuit::dsl::accumulator::{
    ACCUMULATOR_DSL_WIDTH, accumulator_circuit_descriptor, accumulator_dsl_circuit,
    generate_accumulator_trace, prove_accumulator_non_revocation,
    prove_accumulator_non_revocation_dsl, verify_accumulator_non_revocation,
    verify_accumulator_non_revocation_dsl,
};

// Re-export DSL-native derivation proving API.
pub use pyana_circuit::dsl::derivation::{
    BODY_HASH_INV_START, EXTENDED_TRACE_WIDTH, MULTI_STEP_DSL_WIDTH, derivation_circuit_descriptor,
    derivation_dsl_circuit, generate_derivation_trace_dsl, generate_multi_step_trace_dsl,
    prove_authorization_dsl, prove_derivation_dsl, verify_authorization_dsl, verify_derivation_dsl,
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
/// This is metadata -- it describes the constraint topology (trace width,
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
/// Kimchi gate types (for KimchiCircuitDescriptor).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KimchiGateType {
    /// Generic arithmetic gate.
    Generic,
    /// Poseidon hash permutation gate.
    Poseidon,
}

/// A single gate in a Kimchi circuit.
#[derive(Debug, Clone)]
pub struct KimchiGate {
    /// The type of gate.
    pub typ: KimchiGateType,
    /// Coefficients for the gate polynomial.
    /// For Generic gates: `[c0, c1, c2, c3, c4]` enforcing
    /// `c0*w0 + c1*w1 + c2*w2 + c3*w3 + c4*w4 = 0`.
    pub coeffs: Vec<i64>,
    /// Number of wires used by this gate.
    pub wires: usize,
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

// ============================================================================
// Kimchi/Pickles Bridge
// ============================================================================

/// Re-export the circuit-crate's DSL-to-Kimchi bridge types.
///
/// When the `kimchi-bridge` feature is enabled, consumers can convert a
/// `KimchiCircuitDescriptor` (produced by the DSL codegen) into real Kimchi
/// gates and prove recursively via Pickles.
#[cfg(feature = "kimchi-bridge")]
pub mod kimchi_bridge {
    pub use pyana_circuit::backends::kimchi_native::from_dsl::{
        DslCircuitDescriptor, DslGate, DslGateType, DslRecursiveStep, compute_state_hash,
        dsl_flat_witness_to_kimchi, dsl_to_kimchi_gates, dsl_witness_to_kimchi, prove_dsl_chain,
        prove_dsl_circuit, prove_dsl_recursive, verify_dsl_proof, verify_dsl_recursive,
    };

    use super::{KimchiCircuitDescriptor, KimchiGateType};

    /// Convert a `KimchiCircuitDescriptor` (DSL codegen output) into a
    /// `DslCircuitDescriptor` (circuit-crate input for Kimchi proving).
    pub fn to_dsl_descriptor(desc: &KimchiCircuitDescriptor) -> DslCircuitDescriptor {
        DslCircuitDescriptor {
            gates: desc
                .gates
                .iter()
                .map(|g| DslGate {
                    typ: match g.typ {
                        KimchiGateType::Generic => DslGateType::Generic,
                        KimchiGateType::Poseidon => DslGateType::Poseidon,
                    },
                    coeffs: g.coeffs.clone(),
                    wires: g.wires,
                })
                .collect(),
            public_input_count: desc.public_input_count,
            trace_width: desc.trace_width,
        }
    }
}
