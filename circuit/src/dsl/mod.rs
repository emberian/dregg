//! DSL circuit runtime: descriptors, trace generators, prove/verify functions.
//!
//! This module contains the production DSL infrastructure that was previously
//! split across `dregg-dsl-runtime`. It lives here to avoid a circular dependency
//! (circuit depends on dsl-runtime which depends on circuit).
//!
//! The [`circuit`] sub-module provides the runtime-interpreted `StarkAir` implementation
//! driven by a [`circuit::CircuitDescriptor`], enabling DSL macros to emit data
//! rather than 2000 lines of codegen.
//!
//! # Smart Contract Runtime
//!
//! The [`circuit::CellProgram`] and [`circuit::ProgramRegistry`] types form the
//! smart contract runtime: user-defined cell programs (submitted as serialized
//! `CircuitDescriptor`s at deploy time) are validated, stored, and verified at
//! runtime via proof-carrying turns.

pub mod accumulator;
pub mod cap_membership;
pub mod circuit;
pub mod committed_threshold;
pub mod deco_payment;
pub mod derivation;
pub mod dfa_routing;
// `dsl_p3_air` routes DSL circuits through the audited Plonky3 batch-STARK
// prover/verifier; it requires `p3-air` / `p3-batch-stark` — both verify-floor
// deps, now always-on. Its prove/verify functions (`revocation::*_p3`,
// `derivation::*_p3`) ride it; the recursion-free batch STARK is part of the
// verify floor (`p3-batch-stark`'s `verify_batch` is prover-free), so this module
// is unconditional.
pub mod descriptors;
pub mod dsl_p3_air;
pub mod fold;
pub mod garbled;
pub mod membership;
pub mod note_spending;
pub mod openable_fields_insertion;
pub mod predicates;
pub mod revocation;
pub mod temporal_absence;
pub mod tiered_revocation;

// Re-export primary smart contract runtime types.
pub use circuit::{
    BoundaryDef, BoundaryRow, CellProgram, CircuitDescriptor, ColumnDef, ColumnKind,
    ConstraintExpr, DslCircuit, LookupTable, PolyTerm, ProgramError, ProgramRegistry,
    ProgramValidationError, intern_air_name,
};

// Re-export production garbled circuit evaluation API.
pub use garbled::{
    ExtendedGateRecord, GarbledDslProof, GateType, prove_garbled_evaluation_dsl,
    prove_garbled_evaluation_extended_dsl, prove_private_threshold_dsl,
    verify_garbled_evaluation_dsl, verify_private_threshold_dsl,
};

// Re-export production temporal absence API.
pub use temporal_absence::{
    DslTimelineEntry, TemporalAbsenceDslProof, TemporalAbsenceDslWitness,
    prove_temporal_absence_dsl, verify_temporal_absence_dsl,
};

// Re-export the production DFA message-routing (route-commitment-binding) API.
pub use dfa_routing::{
    build_routing_witness, compute_table_commitment, dfa_routing_circuit, dfa_routing_descriptor,
    prove_dfa_routing, verify_dfa_routing,
};

// Re-export production non-revocation proving API.
pub use revocation::{
    DslRevocationTree, NonMembershipWitnessDsl, REVOCATION_TREE_DEPTH, SENTINEL_MAX, SENTINEL_MIN,
    TREE_DEPTH, generate_non_revocation_trace, non_revocation_dsl_circuit,
    prove_non_revocation_dsl, revocation_hash_to_field, verify_non_revocation_dsl,
};

// Re-export DSL-native fold proving API.
pub use fold::{
    FOLD_AIR_WIDTH, FOLD_DSL_PI_COUNT, FOLD_DSL_WIDTH, FoldAir, FoldWitness, RemovedFact,
    build_membership_proof, build_shared_tree, compute_root_transition_hash,
    compute_test_checks_commitment, create_test_fold, fold_circuit_descriptor, fold_dsl_circuit,
    generate_fold_trace, prove_fold_dsl, prove_fold_stark, verify_fold_dsl, verify_fold_stark,
    verify_root_transition,
};

// Re-export legacy Merkle types for backward compatibility.
pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness,
    create_test_witness as create_test_witness_legacy,
};

// Re-export DSL-native note spending proving API.
pub use note_spending::{
    dsl_commitment, dsl_merkle_root, dsl_nullifier, generate_note_spending_trace,
    generate_note_spending_trace_with_value_hi, note_spending_circuit_descriptor,
    note_spending_dsl_circuit, prove_note_spend, prove_note_spend_dsl, prove_note_spend_dsl_full,
    verify_note_spend, verify_note_spend_dsl, verify_note_spend_dsl_full,
    verify_note_spend_dsl_with_destination,
};

// Re-export DSL-native accumulator proving API.
pub use accumulator::{
    ACCUMULATOR_DSL_WIDTH, accumulator_circuit_descriptor, accumulator_dsl_circuit,
    generate_accumulator_trace, prove_accumulator_non_revocation,
    prove_accumulator_non_revocation_dsl, verify_accumulator_non_revocation,
    verify_accumulator_non_revocation_dsl,
};

// Re-export DSL-native committed-threshold proving API.
pub use committed_threshold::{
    committed_threshold_circuit_descriptor, committed_threshold_dsl_circuit,
    generate_committed_threshold_trace, prove_committed_threshold_dsl,
    verify_committed_threshold_dsl,
};

// Re-export DSL-native derivation proving API.
pub use derivation::{
    BODY_HASH_INV_START, EXTENDED_TRACE_WIDTH, MULTI_STEP_DSL_WIDTH, derivation_circuit_descriptor,
    derivation_dsl_circuit, generate_derivation_trace_dsl, generate_multi_step_trace_dsl,
    prove_authorization_dsl, prove_derivation_dsl, verify_authorization_dsl, verify_derivation_dsl,
};

// Re-export tiered revocation API.
pub use tiered_revocation::{
    CHECKPOINT_INTERVAL, DEFAULT_HOT_CAPACITY, TieredNonRevocationProof, TieredRevocationSet,
};
