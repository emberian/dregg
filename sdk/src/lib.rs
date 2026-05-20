//! # pyana-sdk
//!
//! The unified agent SDK for the pyana federation protocol.
//!
//! This crate provides a single ergonomic entry point for agents that need to:
//! - Hold and manage authorization tokens (macaroon-backed)
//! - Attenuate and delegate tokens to sub-agents
//! - Sign and submit execution turns
//! - Generate zero-knowledge presentation proofs
//! - Interact with remote silos over the wire protocol
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                      AgentRuntime                                 │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
//! │  │ AgentWallet  │  │   Ledger     │  │    SiloClient        │  │
//! │  │ (identity +  │  │   (local     │  │    (remote silo      │  │
//! │  │  tokens)     │  │    state)    │  │     interaction)     │  │
//! │  └──────────────┘  └──────────────┘  └──────────────────────┘  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Quick Start
//!
//! ```no_run
//! use pyana_sdk::{AgentWallet, AgentRuntime};
//! use pyana_token::Attenuation;
//!
//! // Create a wallet with a fresh identity
//! let mut wallet = AgentWallet::new();
//!
//! // Mint a root token for our service
//! let root_token = wallet.mint_token(b"my-secret-root-key-32-bytes!!!!!", "my-service");
//!
//! // Attenuate it for a specific task
//! let restricted = wallet.attenuate(&root_token, &Attenuation {
//!     services: vec![("dns".into(), "r".into())],
//!     ..Default::default()
//! }).unwrap();
//! ```

pub mod wallet;
pub mod client;
pub mod runtime;
pub mod error;

// Re-export primary types at crate root for convenience.
pub use wallet::{
    AgentWallet, HeldToken, DelegatedToken, SignedTurn,
    VerificationMode, AuthorizationPresentation, FactIndex,
};
pub use client::{SiloClient, PresentationResult};
pub use runtime::{AgentRuntime, SubAgent};
pub use error::SdkError;

// Re-export commonly needed types from dependencies so users don't need
// to add them separately.
pub use pyana_types::{PublicKey, Signature};
pub use pyana_cell::{CellId, Ledger};
pub use pyana_token::{Attenuation, AuthRequest, AuthToken};
pub use pyana_turn::{Turn, TurnReceipt, TurnBuilder, Effect};
pub use pyana_turn::{VerifyError, verify_receipt_chain, verify_receipt_chain_head, verify_receipt_extends};
