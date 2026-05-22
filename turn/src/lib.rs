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
pub mod conflict;
pub mod encrypted;
pub mod error;
pub mod escrow;
pub mod eventual;
pub mod execution_path;
pub mod executor;
pub mod fast_path;
pub mod forest;
pub(crate) mod journal;
pub mod obligation;
pub mod pending;
pub mod routing;
pub mod turn;
pub mod verify;

#[cfg(test)]
mod tests;

// Re-export primary types at crate root.
pub use action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, Event};
pub use budget_gate::{BudgetGate, BudgetSlice};
pub use builder::{ActionBuilder, TurnBuilder};
pub use composer::{ComposeError, ComposedTurn, SignedFragment, TurnComposer};
pub use conditional::{
    BASE_CONDITIONAL_DEPOSIT, ConditionProof, ConditionalResult, ConditionalTurn,
    DEFAULT_MAX_ROOT_AGE, MAX_CONDITIONAL_DEADLINE, PER_BLOCK_DEPOSIT, ProofCondition, TrustedRoot,
    burn_conditional_deposit, compute_conditional_deposit, compute_proof_hash,
    refund_conditional_deposit, resolve_condition, validate_conditional_submission,
};
pub use conflict::{ConflictSet, build_conflict_set, extract_access_sets};
pub use encrypted::{
    ConflictBucket, EncryptedTurn, EncryptedTurnError, TurnOrdering, TurnValidityProof,
    TurnValidityPublicInputs, order_encrypted_turns,
};
pub use error::TurnError;
pub use escrow::{EscrowCondition, EscrowRecord};
pub use eventual::{
    CycleError, EventualRef, OutputRef, Pipeline, PipelineBuilder, PipelineError, PipelineResult,
    Target, TurnBatch, TurnOutput,
};
pub use execution_path::{ExecutionPath, compute_execution_path};
pub use executor::{
    ComputronCosts, ObligationRecord, ProofVerifier, ResolutionTable, TurnExecutor,
    execute_pipeline, execute_pipeline_result, resolve_eventual_ref,
};
pub use fast_path::{
    CellLockEntry, CellLockTable, FastPathConfig, FastPathError, TurnCertificate, TurnSign,
    assemble_certificate, clear_all_locks, execute_certified_turn, expire_stale_locks,
    is_fast_path_eligible, process_fast_path_lock, verify_turn_sign,
};
pub use forest::{CallForest, CallTree};
pub use obligation::{
    MAX_OBLIGATION_DEADLINE, ObligationError, ObligationOutcome, ProofObligation, check_expiry,
    create_obligation, fulfill_obligation, validate_obligation_deadline,
};
pub use pending::{
    BrokenReason, PendingEntry, PendingHandle, PendingStatus, PendingTurnRegistry,
    ResolutionCondition, ResolutionEvent, ResolutionOutcome,
};
pub use routing::RoutingDirective;
pub use turn::{EmittedEvent, Turn, TurnReceipt, TurnResult};
pub use verify::{
    VerifyError, sign_receipt, verify_receipt_chain, verify_receipt_chain_head,
    verify_receipt_chain_with_keys, verify_receipt_extends,
};
