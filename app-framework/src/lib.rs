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
pub mod discovery;
pub mod dispute;
pub mod escrow;
pub mod fee_policy;
pub mod hex;
pub mod inbox_endpoint;
pub mod middleware;
pub mod multi_group;
pub mod persistence;
pub mod queue_endpoint;
pub mod ring_trade;
pub mod server;
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

// Re-export server and auth types at crate root for ergonomics.
pub use auth::{AdminAuth, AdminMode, AdminToken, HasAdminToken};
pub use authorizer::{
    AuthContext, AuthError, Authorizer, BearerAuthorizer, CapabilityAuthorizer,
    RejectingAuthorizer, SignedAuthorizer,
};
pub use persistence::JsonPersistence;
pub use server::{AppConfig, AppServer, ErrorResponse, api_error};

// Re-export dispute framework types for apps implementing optimistic settlement.
pub use dispute::{
    ArbiterStrategy, ComputeMetrics, DeliveryClaim, Disputable, DisputeConfig, DisputeError,
    DisputeEvidence, DisputeResolution, OptimisticSettlement, SettlementState,
};
pub use dispute::{DisputeId, SettlementId as DisputeSettlementId};
pub use dispute::BlindedDisputable;

// New-world module re-exports.
pub use batch_executor::{BatchExecution, BatchExecutor, ClientTurnRequest};
pub use captp_server::CapTpServer;
pub use discovery::{DiscoveryError, NameRegistration, NameserviceClient};
pub use fee_policy::{AcceptedAsset, FeePolicy};
pub use multi_group::MultiGroupConfig;
pub use ring_trade::{LegId, RingTradeParticipant};
