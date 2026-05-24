//! # pyana-protocol-tests
//!
//! Protocol-invariant property tests for pyana.
//!
//! The thesis (from `dev-philosophy/02-testing.md`): pyana has thousands of
//! unit and integration tests, but the audit-discovered bugs were
//! *protocol-level* — invariants that hold across the input space, not in
//! the specific scenarios someone happened to write tests for.
//!
//! This crate fills that gap. Each module under `invariants/` picks one
//! claimed protocol property (e.g. "balance conservation: sum of
//! balance_change across a turn equals zero net of fee") and uses
//! [`proptest`] strategies from `generators/` to drive the executor against
//! it across many randomized inputs.
//!
//! ## Layout
//!
//! - [`generators`] — `proptest::Strategy` impls that emit *valid-shaped*
//!   inputs the executor will accept. Hard part: a turn that parses cleanly
//!   and has internally-consistent authorization/preconditions, not garbage
//!   that exercises rejection paths.
//! - [`invariants`] — one module per invariant. Each module hosts a
//!   `proptest!` block that consumes the generators, drives the executor,
//!   and asserts the property holds.
//! - [`Invariant`] — a tiny trait so future scaffolding can enumerate /
//!   document invariants. The actual tests still live in module-scope so
//!   `cargo test` picks them up.
//!
//! ## Status
//!
//! - `balance_conservation`        — IMPLEMENTED
//! - `nonce_monotonicity`          — IMPLEMENTED
//! - `receipt_chain`               — IMPLEMENTED
//! - `capability_attenuation`      — STUB (next session)
//! - `facet_attenuation`           — STUB (next session)
//! - `sealed_field_integrity`      — STUB (next session; compile_fail tests)
//! - `permission_enforcement`      — STUB (next session)

#![allow(dead_code)]

pub mod generators;
pub mod invariants;

/// Marker trait for a protocol invariant. The implementer is a unit struct
/// describing the property — actual proptest cases live in module-scope
/// `#[test]` functions so `cargo test` discovers them.
///
/// Future tooling could enumerate `Invariant::all()` to produce a coverage
/// matrix; for now the trait exists mainly as documentation of intent.
pub trait Invariant {
    /// A short human-readable name (`"balance_conservation"`).
    const NAME: &'static str;

    /// One-sentence description suitable for failure reports.
    const DESCRIPTION: &'static str;
}
