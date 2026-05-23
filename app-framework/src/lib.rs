//! # pyana-app-framework
//!
//! Reusable patterns extracted from pyana application implementations
//! (bounty-board, compute-exchange). Provides:
//!
//! - **Proof verification middleware** (`middleware`): Axum extractor for verifying
//!   pyana presentation proofs from HTTP headers.
//! - **Generic content store** (`store`): Thread-safe async CRUD store keyed by
//!   32-byte identifiers.
//! - **Escrow lifecycle helpers** (`escrow`): High-level wrappers for creating,
//!   releasing, and refunding escrows via `PyanaEngine`.
//! - **Hex utilities** (`hex`): Encode/decode 32-byte arrays to/from hex strings.
//!
//! # Re-exports
//!
//! Commonly needed types from sub-crates are re-exported so apps can import from
//! a single dependency instead of reaching into `pyana-intent`, `pyana-turn`, etc.

pub mod escrow;
pub mod hex;
#[cfg(feature = "middleware")]
pub mod middleware;
pub mod store;

// =============================================================================
// Re-exports: types that apps commonly need from sub-crates
// =============================================================================

/// Fill constraints for partial intent fulfillment.
pub use pyana_intent::FillConstraints;

/// Escrow condition and record types from the turn crate.
pub use pyana_turn::escrow::{EscrowCondition, EscrowRecord};

/// Predicate types for qualification proofs.
pub use pyana_circuit::PredicateType;

/// Commit-reveal fulfillment protocol types.
pub use pyana_intent::commit_reveal_fulfillment::{
    CommitRevealFulfiller, CommitRevealFulfillmentError, FulfillmentCommitment,
    FulfillmentRegistry, FulfillmentResult, compute_commitment_hash,
};

// Re-export the SDK engine for convenience.
pub use pyana_sdk::embed::{EngineConfig, PyanaEngine};

// Re-export CellId since nearly all app code uses it.
pub use pyana_types::CellId;
