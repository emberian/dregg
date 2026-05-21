//! Adversarial test suite for the pyana ZK token system.
//!
//! This test crate exercises all security-critical boundaries of the system
//! with malicious inputs, Byzantine behavior, and edge cases.

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
mod adversarial_boundaries;
