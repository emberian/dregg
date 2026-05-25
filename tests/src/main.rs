//! Adversarial test suite for the pyana ZK token system.
//!
//! This test crate exercises all security-critical boundaries of the system
//! with malicious inputs, Byzantine behavior, and edge cases.

// This is a test-only crate; helper functions are used within submodules
// but not exported, which triggers dead_code warnings.
#![allow(dead_code)]

#[cfg(feature = "__legacy_tests")]
mod budget;
#[cfg(feature = "__legacy_tests")]
mod commitment;
#[cfg(feature = "__legacy_tests")]
mod fuzz;
#[cfg(feature = "__legacy_tests")]
mod soundness;
#[cfg(feature = "__legacy_tests")]
mod trace_attacks;

// End-to-end integration tests: token -> proof -> turn execution
#[cfg(feature = "__legacy_tests")]
mod integration;

// Full pipeline integration tests: all layers with real crypto
#[cfg(feature = "__legacy_tests")]
mod full_pipeline;

// Adversarial boundary tests: property-based + scenario-driven
#[cfg(feature = "__wip_tests")]
mod adversarial_boundaries;

// End-to-end adversarial integration tests: full pipeline with tampering detection
#[cfg(feature = "__wip_tests")]
mod adversarial_pipeline;

// Wire format end-to-end: wallet.authorize() -> postcard -> PyanaEngine::verify
#[cfg(feature = "__wip_tests")]
mod wire_format_e2e;

// Sovereign proof-carrying turns (Phase 2): wallet generates proof -> executor verifies
mod sovereign_proof;

// DSL circuit full pipeline: descriptor -> CellProgram -> ProgramRegistry -> executor dispatch
mod dsl_pipeline;

// CapTP effects pipeline: ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff via Effect VM STARK
pub mod captp_effects_pipeline;

// DFA routing proven in circuit: transition table commitment + STARK proof of classification
pub mod dfa_circuit;

// End-to-end service mesh: CAS, splice, mount, governance vote + route table
pub mod service_mesh_e2e;

// End-to-end protocol soundness: exhaustively round-trip every Effect variant
// through executor + projection + AIR. See dev-philosophy/02-testing.md section 3.
pub mod every_variant_roundtrip;

// Atomic per-variant tests for every StateConstraint variant at the
// cell-side evaluator surface. See CAVEAT-LAYER-COVERAGE.md §1 for the
// 21+ variants × 4 layers matrix this exercises.
pub mod state_constraint_variants;

// StateConstraint variants exercised through the full TurnExecutor —
// catches placeholder-context regressions (CAVEAT-LAYER-COVERAGE.md §6.2,
// §6.3, §6.4).
pub mod state_constraint_executor;

// Multi-variant Predicate(Vec<_>) conjunction tests and cross-cutting
// composition of slot caveats + cap caveats + Authorization::Custom on
// the same turn.
pub mod state_constraint_composition;

// Per-variant tests for every WitnessedPredicateKind (Dfa, Temporal,
// MerkleMembership, BlindedSet, BridgePredicate, PedersenEquality, Custom).
// Positive/adversarial/registry-lookup. Most blocked on caveat-correctness
// registry dispatch (CAVEAT-LAYER-COVERAGE.md §5, §6.6).
pub mod witnessed_predicate_kinds;

// Per-variant tests for every Authorization variant (Signature, Proof,
// Breadstuff, Bearer, CapTpDelivered, Custom). Positive/adversarial/
// cross-federation replay (threat T6).
pub mod authorization_variants;

// γ.2 bilateral binding tests: Transfer/Grant/Introduce id agreement
// across per-cell proofs (STAGE-7-GAMMA-2-PI-DESIGN.md).
pub mod gamma2_bilateral_binding;

// Sovereign witness tests: Phase 1 algebraic teeth + wire-malleability
// (T9 from EXECUTOR-HONESTY-AUDIT.md, AUDIT-sovereign-witness-teeth.md).
pub mod sovereign_witness_threats;

// Executor honesty threats T1-T15 from EXECUTOR-HONESTY-AUDIT.md.
// Each test exercises one defense.
pub mod executor_honesty_threats;

// Slot caveat composition stress tests: 16-variant Predicate(Vec<_>)
// conjunctions, large AnyOf disjunctions, and Cases-program operation-
// scoped dispatch (CAVEAT-LAYER-COVERAGE.md §1, §8). Goes broader than
// state_constraint_composition.rs.
pub mod slot_caveat_composition_stress;
