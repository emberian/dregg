//! pyana-dfa: canonical DFA routing engine and userspace dispatch primitive.
//!
//! This crate is the load-bearing home of pyana's DFA pattern dispatch. It exists
//! because three earlier implementations
//! (`wire::dfa_router`, `apps/governed-namespace::routes`, `rbg::routing`) each
//! solved part of the problem and none subsumed the others.
//!
//! What this crate provides:
//!
//! * [`compiler`] — `Pattern → Nfa → Dfa` compilation with `u32` state IDs,
//!   real combinators (concat, alternation, intersection, byte ranges, offsets,
//!   repetition, bit-level matches), and `Pattern::All` via product construction.
//! * [`router`] — [`RouteTarget`] (with an open [`RouteTarget::Userspace`]
//!   variant that lets starbridge-apps register their own destination kinds),
//!   [`RouteTable`] (`u32` states, BLAKE3 commitment), [`Router`] (linear-time
//!   classification), [`GovernedRouter`] (CAS + governance-proof gated table
//!   swap), and the userspace [`KindRegistry`].
//! * [`air`] — [`AirTraceRow`] + [`generate_air_trace`] + [`verify_air_trace`],
//!   the trace shape the STARK DFA AIR (`tests/src/dfa_circuit.rs` and
//!   `circuit::dsl::circuit`) consumes.
//! * [`filter`] — [`TopicFilter`] for gossip topic classification and
//!   [`FilterTree`] for capability-secure revocation (lifted from
//!   `rbg::routing`).
//!
//! # Userspace API
//!
//! Starbridge-apps author a DFA route like this:
//!
//! ```rust
//! use pyana_dfa::{Dfa, RouteTarget, GovernedRouter};
//! use pyana_dfa::compiler::Pattern;
//!
//! let table = Dfa::builder()
//!     .route("/health", RouteTarget::handler("health_check"))
//!     .route("/cells/stablecoin/*", RouteTarget::handler("cell:stablecoin"))
//!     .route_pattern(
//!         Pattern::seq(vec![Pattern::word(b"\x01"), Pattern::any_byte()]),
//!         RouteTarget::userspace("auth_v1", &b"caveat-1"[..]),
//!     )
//!     .compile();
//!
//! let router = GovernedRouter::new(table);
//! let decision = router.classify_path(b"/health");
//! assert!(decision.is_some());
//! ```
//!
//! # Composition notes
//!
//! * **Slot caveats × DFA:** orthogonal. Routes pick `where`; caveats decide
//!   `whether`. Compose at the dispatcher, not in either evaluator.
//! * **Intent × DFA:** `MatchSpec` matching stays structural; what becomes
//!   DFA-mediated is *gossip topic visibility* (via [`filter::TopicFilter`]).
//! * **CapTP × DFA:** swiss-table is keystone fast path. DFA wraps it as
//!   *pre-filter* at ingress (drop malformed framing before swiss lookup)
//!   and *post-filter* at fan-out (topic classification on Receipts).

#![forbid(unsafe_code)]

pub mod air;
pub mod compiler;
#[cfg(feature = "federation-verifier")]
pub mod federation_verifier;
pub mod filter;
pub mod router;

pub use air::{
    AirTrace, AirTraceRow, DfaError, compile_to_air, compile_to_air_from_table, generate_air_trace,
    verify_acceptance, verify_air_trace,
};
pub use compiler::{DEAD_STATE, Dfa, Pattern, StateId, Transition};
pub use filter::{FilterTree, TopicFilter};
pub use router::{
    Classification, DispatchDecision, GovernanceProof, GovernedRouter, KindRegistry, RouteTable,
    RouteTableBuilder, RouteTarget, RouteUpdateError, Router, StubVerifier, ThresholdVerifier,
    UserspaceTarget,
};
