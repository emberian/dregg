//! Cross-backend differential testing for `pyana-dsl`.
//!
//! # Mission
//!
//! Given the same caveat predicate expressed once via `#[pyana_caveat]`, all
//! seven `gen_*` backends in `pyana-dsl/src/` must produce verifiers that agree
//! on accept/reject for any given input. This crate emits a battery of
//! canonical predicates, drives a curated input set through every backend it
//! can run in-process, and asserts that every runnable backend reports the
//! same verdict.
//!
//! # Backend Roster
//!
//! The DSL has seven code generators:
//!
//! | Backend     | Emits                              | Runtime verifiable in this crate?               |
//! |-------------|------------------------------------|-------------------------------------------------|
//! | `gen_rust`     | `{name}_check(...)` evaluator   | YES — call the function directly.               |
//! | `gen_datalog`  | `{name}_datalog() -> &'static str` Datalog rule string | YES — mini in-crate Datalog evaluator. |
//! | `gen_air`      | `{name}_air_constraints() -> AirConstraintSet` topology descriptor | YES — re-derive accept/reject via the IR-aligned `pyana_dsl_runtime::diff_witness` primitives, sanity-checked against the descriptor's column accounting. |
//! | `gen_kimchi`   | `{name}_kimchi() -> KimchiCircuitDescriptor` gate descriptor | YES — Generic-gate simulator that fills the canonical witness per IR shape and asserts every gate's `c_i * w_i` polynomial evaluates to zero. Poseidon gates (membership-only) are checked structurally. |
//! | `gen_plonky3`  | `{Name}P3Air` native Plonky3 AIR struct | YES (subset) — for the predicate shapes we can build a generic `CircuitDescriptor` over (arithmetic comparisons, equalities), we round-trip through `prove_dsl_plonky3` + `verify_dsl_plonky3`. Membership shapes require Poseidon2 gadgets and are marked SKIP. |
//! | `gen_midnight` | `{name}_midnight_zkir() -> &'static str` ZKIR v3 JSON | NO — Midnight ZKIR is consumed by an off-chain proof server. We lint the emitted JSON (parses, mentions every param, terminates with an `output` instruction) but do not execute it. |
//! | `gen_sp1`      | `{name}_sp1_guest() -> &'static str` SP1 guest source | NO — running the guest requires the SP1 RISC-V toolchain (`sp1-prove`/`cargo prove build`). We lint the source (has `main`, declares each input via `sp1_zkvm::io::read`) but do not execute it. |
//!
//! # Predicate Suite
//!
//! See [`predicates`]. We cover the IR shapes a caveat can take today:
//!
//! - Pure inequalities: `<=`, `>=`
//! - Equality, non-equality (on `u64` and `[u8; 32]`)
//! - Conjunction (multiple `require!` in one body)
//! - Bound-relative comparisons (`threshold + step <= cap`)
//! - Set membership (`set.contains(elem)`)
//! - Combined: membership AND inequality
//!
//! For each predicate we curate a small, deterministic input set spanning
//! positive cases, negative cases, and boundary values (zero, one,
//! `u64::MAX`, near-overflow, byte-array all-zeros, byte-array all-ones).
//!
//! # Failure Narration
//!
//! When backends disagree, [`agreement::AgreementMatrix`] reports which
//! backends voted Accept vs Reject, what the input was, and which backends
//! were Skipped. The test binary panics with a structured report so the
//! offender is identifiable in CI logs.

pub mod agreement;
pub mod air_runner;
pub mod datalog_eval;
pub mod harness;
pub mod kimchi_sim;
pub mod midnight_lint;
pub mod plonky3_runner;
pub mod predicates;
pub mod sp1_lint;

pub use agreement::{AgreementMatrix, BackendName, BackendVerdict, RowReport};
