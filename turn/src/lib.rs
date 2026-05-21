//! `pyana-turn`: Call-forest transaction model for atomic agent execution turns.
//!
//! A Turn is an atomic unit of agent execution, modeled after Mina's zkApp command structure.
//! It contains a *call forest* — a tree of actions that either all commit or all rollback.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────┐
//! │  Turn (atomic transaction)                                    │
//! │  ┌────────────────────────────────────────────────────────┐  │
//! │  │  CallForest                                             │  │
//! │  │  ┌──────────┐  ┌──────────┐  ┌──────────┐             │  │
//! │  │  │ CallTree │  │ CallTree │  │ CallTree │  ...         │  │
//! │  │  │ (root 1) │  │ (root 2) │  │ (root 3) │             │  │
//! │  │  │   │      │  │   │      │  │          │             │  │
//! │  │  │   ├─child│  │   └─child│  │          │             │  │
//! │  │  │   └─child│  │          │  │          │             │  │
//! │  │  │     └─gc │  │          │  │          │             │  │
//! │  │  └──────────┘  └──────────┘  └──────────┘             │  │
//! │  └────────────────────────────────────────────────────────┘  │
//! └──────────────────────────────────────────────────────────────┘
//! ```
//!
//! The key insight from Mina: the call forest IS the transaction. You don't prove
//! individual operations — you prove the entire tree. Authorization flows from
//! parent to child via capability delegation.
//!
//! # Modules
//!
//! - [`action`]: Action, Authorization, DelegationMode, Effect, Event
//! - [`forest`]: CallTree, CallForest
//! - [`turn`]: Turn, TurnReceipt, TurnResult
//! - [`executor`]: TurnExecutor, ComputronCosts, execution logic
//! - [`error`]: TurnError
//! - [`builder`]: TurnBuilder, ActionBuilder

pub mod action;
pub mod budget_gate;
pub mod builder;
pub mod composer;
pub mod conditional;
pub mod error;
pub mod eventual;
pub mod executor;
pub mod forest;
pub(crate) mod journal;
pub mod obligation;
pub mod routing;
pub mod turn;
pub mod verify;

#[cfg(test)]
mod tests;

// Re-export primary types at crate root.
pub use action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, Event};
pub use budget_gate::{BudgetGate, BudgetSlice};
pub use builder::{ActionBuilder, TurnBuilder};
pub use composer::{ComposeError, SignedFragment, TurnComposer};
pub use conditional::{
    ConditionProof, ConditionalResult, ConditionalTurn, DEFAULT_MAX_ROOT_AGE,
    MAX_CONDITIONAL_DEADLINE, ProofCondition, TrustedRoot, compute_proof_hash,
    resolve_condition, validate_conditional_submission,
};
pub use obligation::{
    MAX_OBLIGATION_DEADLINE, ObligationError, ObligationOutcome, ProofObligation, check_expiry,
    create_obligation, validate_obligation_deadline,
    fulfill_obligation,
};
pub use error::TurnError;
pub use eventual::{CycleError, EventualRef, Pipeline, PipelineError, Target, TurnOutput};
pub use executor::{
    ComputronCosts, ProofVerifier, ResolutionTable, TurnExecutor, execute_pipeline,
    resolve_eventual_ref,
};
pub use forest::{CallForest, CallTree};
pub use routing::RoutingDirective;
pub use turn::{Turn, TurnReceipt, TurnResult};
pub use verify::{
    VerifyError, sign_receipt, verify_receipt_chain, verify_receipt_chain_head,
    verify_receipt_chain_with_keys, verify_receipt_extends,
};
