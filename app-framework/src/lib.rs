//! # pyana-app-framework
//!
//! Production-grade application framework for pyana apps. Extracts and unifies
//! the shared patterns that every pyana HTTP service needs:
//!
//! - **Server infrastructure** (`server`): [`AppConfig`](server::AppConfig) for
//!   env-based configuration, [`AppServer`](server::AppServer) builder with health,
//!   CORS, and admin auth pre-wired.
//! - **Admin authentication** (`auth`): [`AdminAuth`](auth::AdminAuth) extractor
//!   for bearer-token-protected admin endpoints, with constant-time comparison.
//! - **Persistence** (`persistence`): [`JsonPersistence`](persistence::JsonPersistence)
//!   for atomic write-then-rename state snapshots.
//! - **Proof verification middleware** (`middleware`): Axum extractors for verifying
//!   pyana presentation proofs from HTTP headers.
//! - **Generic content store** (`store`): Thread-safe async CRUD store keyed by
//!   32-byte identifiers.
//! - **Escrow lifecycle helpers** (`escrow`): High-level wrappers for creating,
//!   releasing, and refunding escrows via `PyanaEngine`.
//! - **Hex utilities** (`hex`): Encode/decode 32-byte arrays to/from hex strings.
//!
//! # Quick Start
//!
//! ```ignore
//! use pyana_app_framework::server::{AppConfig, AppServer};
//! use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
//! use pyana_app_framework::persistence::JsonPersistence;
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = AppConfig::from_env();
//!     AppServer::new(config)
//!         .service_name("my-app")
//!         .with_health()
//!         .with_cors()
//!         .routes(my_routes(state))
//!         .serve()
//!         .await
//!         .unwrap();
//! }
//! ```
//!
//! # Re-exports
//!
//! Commonly needed types from sub-crates are re-exported so apps can import from
//! a single dependency instead of reaching into `pyana-intent`, `pyana-turn`, etc.

pub mod auth;
pub mod authorizer;
pub mod batch_executor;
pub mod blinded_endpoint;
pub mod captp_server;
pub mod cipherclerk;
pub mod discovery;
pub mod dispute;
pub mod escrow;
pub mod fee_policy;
pub mod fields;
pub mod hex;
pub mod inbox_endpoint;
pub mod middleware;
pub mod multi_group;
pub mod persistence;
pub mod queue_endpoint;
pub mod ring_trade;
pub mod server;
pub mod starbridge;
pub mod store;
pub mod vk;

/// Legacy module alias — `cipherclerk` was renamed to `cipherclerk`. This
/// alias keeps `pyana_app_framework::cipherclerk::...` callers compiling
/// during the migration. New code should reach for `cipherclerk`.
#[doc(hidden)]
pub mod cclerk {
    //! Legacy module: forwards to `cipherclerk` and re-exports
    //! `AppCipherclerk` (renamed to `AppCipherclerk`) so pre-rename callers
    //! keep building. New code should reach for `cipherclerk`.
    pub use crate::cipherclerk::AppCipherclerk;
    pub use crate::cipherclerk::*;
}

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

// Re-export server and auth types at crate root for ergonomics.
pub use auth::{AdminAuth, AdminMode, AdminToken, HasAdminToken};
pub use authorizer::{
    AuthContext, AuthError, Authorizer, BearerAuthorizer, CapabilityAuthorizer,
    RejectingAuthorizer, SignedAuthorizer,
};
pub use cipherclerk::AppCipherclerk;
pub use persistence::JsonPersistence;
pub use server::{AppConfig, AppServer, ErrorResponse, api_error};

/// Short alias for [`AppCipherclerk`].
pub use cipherclerk::AppCipherclerk as AppCClerk;

/// Legacy alias for [`AppCipherclerk`].
///
/// Preserved while downstream apps migrate to the new name. New code
/// should reach for [`AppCipherclerk`] (or the short [`AppCClerk`]).
// pub use cipherclerk::AppCipherclerk as AppCipherclerk; // already re-exported above

// Re-export common action / effect types so apps build effects through
// the framework rather than reaching into `pyana_turn` directly.
pub use pyana_cell::state::FieldElement;
pub use pyana_turn::Turn;
pub use pyana_turn::action::{Action, Authorization, DelegationMode, Effect, Event, symbol};

// Re-export the SDK cipherclerk at the framework root so applications
// that need to *construct* one (typically in `main`) don't have to add
// `pyana-sdk` to their Cargo.toml. App code outside `main` should
// reach for [`AppCipherclerk`] (the narrow handle), not
// [`AgentCipherclerk`].
pub use pyana_sdk::AgentCipherclerk;

/// Legacy alias for [`AgentCipherclerk`], re-exported from the SDK.
// pub use pyana_sdk::AgentCipherclerk as AgentCipherclerk; // already re-exported above

// Re-export dispute framework types for apps implementing optimistic settlement.
pub use dispute::BlindedDisputable;
pub use dispute::{
    ArbiterStrategy, ComputeMetrics, DeliveryClaim, Disputable, DisputeConfig, DisputeError,
    DisputeEvidence, DisputeResolution, OptimisticSettlement, SettlementState,
};
pub use dispute::{DisputeId, SettlementId as DisputeSettlementId};

// New-world module re-exports.
pub use batch_executor::{BatchExecution, BatchExecutor, ClientTurnRequest};
pub use captp_server::CapTpServer;
pub use discovery::{DiscoveryError, NameRegistration, NameserviceClient};
pub use fee_policy::{AcceptedAsset, FeePolicy};
pub use multi_group::MultiGroupConfig;
pub use ring_trade::{LegId, RingTradeParticipant};

// Starbridge mounting point. The canonical surface every
// starbridge-app receives via `register(ctx)`.
pub use starbridge::{
    FactoryRegistry, InspectorDescriptor, InspectorRegistry, StarbridgeAppContext,
};

// Re-export the embedded executor at the framework root for the
// common pattern: build a cipherclerk, build an executor, hand them
// to a StarbridgeAppContext.
pub use cipherclerk::{EmbeddedExecutor, ExecutorSubmitError};

// Re-export FactoryDescriptor from pyana-cell at the framework root
// so starbridge-apps only need pyana-app-framework in their Cargo.toml
// to construct factory descriptors.
pub use pyana_cell::{
    AuthRequired, CapGrant, CapTarget, CapTemplate, CellMode, CellProgram, ChildVkStrategy,
    FactoryDescriptor, FieldConstraint, ProvingSystemId, StateConstraint, VerifierFingerprint,
    VkComponents, canonical_vk_v2,
};
// Re-export the types needed to build non-trivial CellProgram::Cases — previously
// every app had to add pyana-cell to its own Cargo.toml just to get these.
pub use pyana_cell::program::{AuthorizedSet, TransitionCase, TransitionGuard};
pub use pyana_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};

// Re-export the canonical field-element encoding helpers so apps can use them
// without duplicating these in every crate.
pub use fields::{field_from_bytes, field_from_u64, hex_encode_32};

// VK v2: re-export the layered VK encoders from `vk` module at the
// framework root. These *shadow* the cell crate's v1 `canonical_program_vk`
// / `canonical_predicate_vk` re-exports — apps that import from
// `pyana_app_framework` automatically pick up the v2 layered hashes,
// closing the "same spec, different AIR" gap that v1 left open.
// (`VK-AS-RE-EXECUTION-RECIPE.md` §v2.)
pub use vk::{
    DEFAULT_PROVING_SYSTEM, PLONKY3_PINNED_REV, canonical_predicate_vk,
    canonical_program_bytes_hash, canonical_program_vk, effect_vm_air_fingerprint,
    effect_vm_verifier_fingerprint, validate_child_vk_canonical,
};
