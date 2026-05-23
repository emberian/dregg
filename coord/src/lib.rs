//! # pyana-coord
//!
//! Two-layer turn coordination for the Pyana agent network.
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
//! ```

pub mod atomic;
pub mod budget;
pub mod causal;
pub mod error;
pub mod serde_sig;
pub mod shared_budget;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use atomic::{
    AbortMessage, AtomicForest, CommitMessage, Coordinator, CoordinatorState, Decision,
    Participant, ProposeMessage, Vote,
};
pub use budget::{
    BudgetCoordinator, BudgetError, BudgetSlice, FastUnlockManager, UnlockCertificate,
    UnlockRequest,
};
pub use causal::{CausalDag, CausalLedger, CausalTurn};
pub use error::CoordError;
pub use shared_budget::{
    DebitResolution, ResourceState, SharedBudgetError, SharedBudgetObserver, SharedResourceBudget,
};
