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
mod byzantine;
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
