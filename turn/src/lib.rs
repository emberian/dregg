//! `pyana-turn`: Call-forest transaction model for atomic agent execution turns.
//!
//! # Trust Model
//!
//! This crate spans TWO trust levels with a clear boundary:
//!
//! ## Executor-Trusted (classical path)
//! - Modules: [`executor`], [`forest`], [`action`], [`journal`], [`escrow`], [`obligation`]
//! - The executor walks the call forest, checks authorization, and applies effects.
//! - Soundness depends on honest federation execution (BFT replication).
//! - External parties trust the federation's attested state root.
//!
//! ## Trustless (proof-carrying path)
//! - Modules: [`verify`], sovereign cell proof verification in [`executor::verify_and_commit_proof`]
//! - Proof-carrying sovereign turns (Phase 3) are independently verifiable via STARK.
//! - The executor only checks the proof and updates a commitment -- no state interpretation.
//!
//! ## Trust Boundary
//! The boundary lives inside `executor.rs` at the `execution_proof` branch:
//! - If `turn.execution_proof` is `Some`: **TRUSTLESS** path (verify proof, update commitment)
//! - If `turn.execution_proof` is `None`: **EXECUTOR-TRUSTED** path (classical execution)
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
pub mod aggregate_bilateral_prover;
pub mod bilateral_schedule;
pub mod binding_proof;
pub mod budget_gate;
pub mod builder;
pub mod composer;
pub mod conditional;
pub mod conflict;
pub mod dsl;
pub mod economics;
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
pub mod presence_discharge;
pub mod queue_programs;
pub mod routing;
pub mod turn;
pub mod verify;
pub mod witnessed_receipt;

#[cfg(test)]
mod tests;

// Re-export primary types at crate root.
pub use action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    Effect, Event, QueueTxOp,
};
pub use budget_gate::{BudgetGate, BudgetSlice};
pub use builder::{
    ActionBuilder, Authorized, Bearer, Breadstuff, NeedsAuth, Proved, Signed, TurnBuilder,
    UncheckedOptIn,
};
pub use composer::{ComposeError, ComposedTurn, SignedFragment, TurnComposer};
pub use conditional::{
    BASE_CONDITIONAL_DEPOSIT, ConditionProof, ConditionalResult, ConditionalTurn,
    DEFAULT_MAX_ROOT_AGE, MAX_CONDITIONAL_DEADLINE, PER_BLOCK_DEPOSIT, ProofCondition, TrustedRoot,
    burn_conditional_deposit, compute_conditional_deposit, compute_proof_hash,
    refund_conditional_deposit, resolve_condition, validate_conditional_submission,
};
pub use conflict::{ConflictSet, build_conflict_set, extract_access_sets};
pub use economics::{EpochMinter, MintResult, MintingPolicy};
pub use encrypted::{
    ConflictBucket, EncryptedTurn, EncryptedTurnError, TurnOrdering, TurnValidityProof,
    TurnValidityPublicInputs, order_encrypted_turns,
};
pub use error::TurnError;
pub use escrow::{
    CommittedEscrow, EscrowClaimAuth, EscrowCondition, EscrowRecord, compute_condition_commitment,
    compute_identity_commitment, verify_escrow_claim, verify_escrow_claim_commitment,
};
pub use eventual::{
    CycleError, EventualRef, OutputRef, Pipeline, PipelineBuilder, PipelineError, PipelineResult,
    Target, TurnBatch, TurnOutput,
};
pub use execution_path::{ExecutionPath, compute_execution_path};
pub use executor::{
    AtomicProofEntry, AtomicSovereignTurn, AtomicTurnError, CellMigrationManager, ComputronCosts,
    MigrationCancelReason, MigrationError, MigrationState, MixedAtomicResult, MixedAtomicTurn,
    ObligationRecord, ProofVerifier, ResolutionTable, TurnExecutor, execute_pipeline,
    execute_pipeline_result, resolve_eventual_ref,
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
// `Precondition` and friends collapsed into `pyana_cell::preconditions`
// per PREDICATE-INVENTORY §4.3 case 1. Re-export from cell for any
// callers that still reach for them through the turn crate root.
pub use aggregate_bilateral_prover::{
    AggregatedBundle, prove_aggregated_bundle, verify_aggregated_bundle,
};
pub use presence_discharge::{
    PresenceCaveat as PresenceCapCaveat, PresenceClaimRequirement, PresenceDischarge,
    PresenceDischargeError, verify_presence_discharge,
};
pub use pyana_cell::{Precondition, Preconditions, PreconditionsBuilder};
pub use queue_programs::{
    EnqueueValidationContext, QueueConstraint, QueueProgram, QueueProgramError,
    QueueProgramRegistry, ValidationResult, compute_validation_hash, validate_enqueue,
    vk_hash_to_field,
};
pub use routing::{IntroductionExport, RoutingDirective};
pub use turn::{
    CustomProgramProof, EmittedEvent, Finality, SovereignCellWitness, Turn, TurnReceipt, TurnResult,
};
pub use verify::{
    VerifyError, sign_receipt, verify_receipt_chain, verify_receipt_chain_head,
    verify_receipt_chain_with_keys, verify_receipt_extends,
};
pub use witnessed_receipt::{
    AggregateMembership, RecursiveProofVariant, WitnessAvailability, WitnessBundle,
    WitnessedReceipt,
};
