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

pub mod client;
pub mod committed_turn;
pub mod discharge;
pub mod discovery;
pub mod embed;
pub mod error;
pub mod mnemonic;
pub mod privacy;
pub mod runtime;
pub mod verify;
pub mod wallet;
pub mod wordlist;

// Re-export primary types at crate root for convenience.
pub use client::{PresentationResult, RevocationStatus, SiloClient};
pub use committed_turn::{
    CommittedNoteInput, CommittedNoteOutput, CommittedTurnBuilder, OwnedNote,
};
pub use error::SdkError;
pub use runtime::{AgentRuntime, SubAgent};
pub use wallet::{
    AgentWallet, AuthorizationPresentation, DelegatedToken, DisclosureSpec, FactDisclosure,
    FactIndex, HeldToken, OwnedStealthNote, SignedTurn, VerificationMode,
};

// Re-export commonly needed types from dependencies so users don't need
// to add them separately.
pub use pyana_cell::{CellId, Ledger};
pub use pyana_circuit::{BabyBear, IvcProof, verify_ivc};
pub use pyana_token::{Attenuation, AuthRequest, AuthToken};
pub use pyana_turn::{Effect, Turn, TurnBuilder, TurnReceipt};
pub use pyana_turn::{
    VerifyError, verify_receipt_chain, verify_receipt_chain_head, verify_receipt_extends,
};
pub use pyana_types::{PublicKey, Signature};

// Re-export verifier types from the bridge layer for standalone proof verification.
#[allow(deprecated)]
pub use pyana_bridge::present::{BridgePresentationProof, verify_presentation};
pub use pyana_bridge::verifier::StarkProofVerifier;
pub use pyana_circuit::PresentationVerification;

// Re-export mnemonic generation at crate root for convenience.
pub use mnemonic::generate_mnemonic;

// Re-export privacy primitives for stealth addresses, value commitments, and encrypted intents.
pub use pyana_cell::stealth::{
    StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress,
};
pub use pyana_cell::value_commitment::{
    BulletproofRangeProof, ConservationProof, FullConservationProof, ValueCommitment,
    ValueCommitmentBytes,
};
pub use pyana_intent::sse::EncryptedIntent;

// Re-export the no-IO embed layer for service integration.
pub use embed::{EmbedError, EngineConfig, PyanaEngine, WireCodec};

// Re-export privacy API types at crate root for convenience.
pub use privacy::{
    AccumulatorNonMembershipProof, AnonymousPresentation, NonRevocationProof, NoteSecret,
    NoteTransferProof, UnlinkablePredicateProof, verify_accumulator_non_membership,
    verify_anonymous_presentation, verify_non_revocation_proof, verify_note_spending,
};

// Re-export discharge gateway client functions.
pub use discharge::{authorize_with_discharges, extract_third_party_tickets, obtain_discharge};

// Re-export standalone verification functions.
#[cfg(any(test, feature = "dev"))]
pub use verify::verify_any_tier;
pub use verify::{
    verify_authorization_proof, verify_disclosure_presentation, verify_production,
    verify_selective_disclosure, verify_selective_presentation, verify_validated_ivc_proof,
};

// Re-export proof tier types for downstream use.
pub use pyana_circuit::{CryptographicProof, ProofTier, VerifiedProof};
