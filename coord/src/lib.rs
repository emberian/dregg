//! # dregg-coord
//!
//! Three-layer turn coordination for the Dregg agent network.
//!
//! ## Layer 1: Causal Chaining (cheap, async, no coordination needed)
//!
//! Every turn a node produces includes hash-pointers to the latest turns it has seen.
//! This creates a DAG of happened-before relationships. Any node can verify
//! "turn T2 happened after turn T1" by following the hash links. No global ordering
//! is required — just local causal consistency.
//!
//! ## Layer 2: Atomic Multi-Party Turns (expensive, requires coordination)
//!
//! Multiple agents on different nodes contribute actions to ONE call forest.
//! The combined forest is only committed if ALL participants' preconditions are met.
//! Uses a simple 2-phase commit: Propose -> Vote -> Commit/Abort.
//! If any participant's preconditions fail, the entire forest is aborted.
//! The committed forest gets a threshold QC (everyone who participated signs).
//!
//! ## Layer 3: Stingray Bounded Counters (concurrent spending, no coordination)
//!
//! Based on the Stingray protocol (arXiv:2501.06531). An agent's total resource
//! balance is split into per-silo slices. Each silo may debit locally up to its
//! slice ceiling without any cross-silo coordination. The invariant
//! `slice_ceiling = balance * (f+1) / (2f+1)` ensures that, even with f Byzantine
//! silos, total honest spending cannot exceed the true balance. Slices are reconciled
//! periodically via a signed spending-certificate rebalance. Fast-unlock allows
//! immediate release of locked resources after a 2PC abort without waiting for an
//! epoch timeout.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────────────────┐
//! │  Layer 1: Causal Chaining                                                │
//! │                                                                          │
//! │    [T1]──────►[T2]──────►[T4]                                           │
//! │      │                     ▲                                             │
//! │      └──────►[T3]──────────┘                                            │
//! │                                                                          │
//! │  (each turn carries hash-pointers to its causal dependencies)            │
//! └──────────────────────────────────────────────────────────────────────────┘
//!
//! ┌──────────────────────────────────────────────────────────────────────────┐
//! │  Layer 2: Atomic Multi-Party                                             │
//! │                                                                          │
//! │    Node A ──► Propose(forest) ──► Node B                                │
//! │    Node A ◄── Vote::Yes ◄──────── Node B                                │
//! │    Node A ──► Commit(receipt) ──► Node B                                │
//! │                                                                          │
//! │  (2PC: all-or-nothing commitment of a shared call forest)                │
//! └──────────────────────────────────────────────────────────────────────────┘
//!
//! ┌──────────────────────────────────────────────────────────────────────────┐
//! │  Layer 3: Stingray Bounded Counters                                      │
//! │                                                                          │
//! │    balance B, silos S, Byzantine tolerance f                             │
//! │    slice_ceiling = B * (f+1) / (2f+1)                                   │
//! │                                                                          │
//! │    Silo A ──debit──► local slice A (no coordination)                    │
//! │    Silo B ──debit──► local slice B (no coordination)                    │
//! │    Rebalance ◄── cert_A + cert_B ──► new slices                         │
//! │                                                                          │
//! │  (concurrent spending; Ed25519-signed certificates; fast unlock)         │
//! └──────────────────────────────────────────────────────────────────────────┘
//! ```

// THE VERIFIED PQ CORES, for THIS crate's lib-test binary, at PROCESS START.
//
// `dregg-coord` never calls `dregg-pq` itself — it reaches it through `dregg_blocklace::
// finality::Block::new` / `Blocklace::new_simple`, which derive the block author's ML-DSA-65
// half from its ed25519 seed. `dregg-blocklace` installs a core only under its OWN `cfg(test)`,
// which is not set when it is compiled as a dependency, so with nothing installed `dregg-pq`
// refuses the derivation with an uncatchable `process::abort()`.
//
// `shared_budget::tests::install_pq_cores()` and `coord_diff` already did this per-test — and
// that is exactly the shape this replaces. Two of `shared_budget`'s own tests
// (`test_resource_state_lifecycle`, `test_try_optimistic_debit_resumes_after_resolution`) were
// not on that hand-audited call list and died as bare SIGABRTs. A process-start initializer
// makes the install a property of the BINARY, so no test can be left off a list again.
// `#[cfg(test)]`, so the shipped crate stays archive-free.
#[cfg(test)]
dregg_pq_testkit::install_at_process_start!();

pub mod atomic;
pub mod budget;
pub mod causal;
pub mod error;
pub mod serde_sig;
pub mod shared_budget;
pub mod verified_gate;

#[cfg(test)]
mod tests;

// The witnessless-participant turn role: the commit-path verify-gate (`MixedJoint`'s
// `check_private_legs_admissible`) + state-root continuity (`check_chain_bound`), the Rust
// production-wiring of `Dregg2/Distributed/PrivateLeg.lean` (keystone
// `joint_turn_sound_with_private_legs`) and `metatheory/docs/PRIVATE-OFFLINE-CELLS.md`.
#[cfg(test)]
mod private_leg;

// Differential: the verified Lean `Dregg2/Distributed/EntangledJoint.lean` model (N-cell atomic
// coordinated turn) ⟺ the real `atomic` 2PC + the `shared_budget` non-overspend gate.
#[cfg(test)]
mod entangled_diff;

// Differential: the verified Lean `Dregg2/Coord/*` models (the genuinely-uncovered coordination
// semantics) ⟺ the real `causal::CausalDag` happened-before DAG, `atomic::evaluate_votes` 2PC
// decision machine, and `shared_budget::SharedResourceBudget::resolve_with_ordering` tau-resolution.
#[cfg(test)]
mod coord_diff;

// Re-exports for convenience.
pub use atomic::{
    AbortMessage, AssetId, AtomicForest, ChainBreak, CommitMessage, Coordinator, CoordinatorState,
    Decision, JointId, MixedAdmitError, MixedJoint, Participant, PrivateContribution, PrivateLeg,
    PrivateLegProof, ProposeMessage, StateCommit, Vote, check_chain_bound, default_valid_until,
};
pub use budget::{
    BudgetError, BudgetSlice, FastUnlockManager, StingrayCounter, UnlockCertificate, UnlockRequest,
};
pub use causal::CausalDag;
pub use error::CoordError;
pub use verified_gate::{CoordVerifiedGate, Verdict2pc, register_coord_verified_gate};
