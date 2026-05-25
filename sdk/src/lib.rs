//! # pyana-sdk
//!
//! # Trust Model
//!
//! This crate operates at the **CLIENT-LOCAL** trust level.
//!
//! - **Soundness**: The SDK runs entirely on the user's device. It manages private keys,
//!   token chains, and proof generation locally. The user trusts their own device and
//!   the SDK's correct implementation. No other party can observe or interfere with
//!   SDK operations (assuming a secure device).
//! - **Assumptions**: The user's device is not compromised. Private keys remain in local
//!   memory/storage. The SDK correctly implements proof generation, token attenuation,
//!   and turn signing. Network interactions are authenticated (TLS to silos).
//! - **Verifiable by**: Only the user. The SDK's outputs (signed turns, proofs,
//!   presentations) are verified by the federation, but the SDK's internal state
//!   (held tokens, wallet contents) is private to the user.
//!
//! ## Security Properties
//! - Key material never leaves the device (unless explicitly exported)
//! - Proof generation is local (witness data stays on-device)
//! - Token attenuation preserves the narrowing invariant (cannot escalate)
//! - Selective disclosure reveals only chosen facts
//!
//! ## What the SDK Does NOT Trust
//! - Remote silos (verified via TLS + receipt chains)
//! - Federation state (verified via attested roots + STARK proofs)
//! - Other agents (interactions mediated by capabilities)
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
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                          AgentRuntime                                    │
//! │  ┌────────────────────┐  ┌──────────────┐  ┌──────────────────────┐    │
//! │  │ AgentCipherclerk   │  │   Ledger     │  │    SiloClient        │    │
//! │  │ (identity +        │  │   (local     │  │    (remote silo      │    │
//! │  │  tokens + keys)    │  │    state)    │  │     interaction)     │    │
//! │  └────────────────────┘  └──────────────┘  └──────────────────────┘    │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # The cipherclerk
//!
//! `AgentCipherclerk` (alias `AgentCClerk`, legacy alias `AgentWallet`) is the
//! agent-side *cryptographic clerk*: it holds signing keys, authorization
//! tokens, the receipt chain, and presents credentials/proofs on behalf of a
//! Principal. The name borrows from Greg Egan's *Polis* (and its descendants),
//! where a citizen's "cipherclerk" is the autonomous component that manages
//! their cryptographic identity and capability handles. "Wallet" was a poor
//! fit — wallets connote value storage, but a pyana cipherclerk's authority
//! is mostly *capabilities*, not balances.
//!
//! # Quick Start
//!
//! ```no_run
//! use pyana_sdk::{AgentCipherclerk, AgentRuntime};
//! use pyana_token::Attenuation;
//!
//! // Create a cipherclerk with a fresh identity
//! let mut cclerk = AgentCipherclerk::new();
//!
//! // Mint a root token for our service
//! let root_token = cclerk.mint_token(b"my-secret-root-key-32-bytes!!!!!", "my-service");
//!
//! // Attenuate it for a specific task
//! let restricted = cclerk.attenuate(&root_token, &Attenuation {
//!     services: vec![("dns".into(), "r".into())],
//!     ..Default::default()
//! }).unwrap();
//! ```

// Modules that pull tokio / pyana-wire / pyana-captp are gated so the crate
// stays buildable on wasm32 (set `default-features = false`). Anything in
// the always-on group below is wasm-friendly.
#[cfg(feature = "captp")]
pub mod captp_client;
pub mod cipherclerk;
#[cfg(feature = "network")]
pub mod client;
pub mod committed_turn;
#[cfg(feature = "network")]
pub mod discharge;
#[cfg(feature = "network")]
pub mod discovery;
#[cfg(feature = "network")]
pub mod embed;
pub mod error;
pub mod full_turn_proof;
pub mod mnemonic;
#[cfg(feature = "captp")]
pub mod names;
pub mod privacy;
pub mod runtime;
pub mod verify;
pub mod wordlist;

/// Legacy module name for the cipherclerk surface.
///
/// During the rename window this re-exports `cipherclerk` plus an
/// `AgentWallet` alias so downstream `use pyana_sdk::wallet::...`
/// paths keep compiling. New code should reach for
/// `pyana_sdk::cipherclerk`.
#[doc(hidden)]
pub mod wallet {
    pub use crate::cipherclerk::*;
    pub use crate::cipherclerk::AgentCipherclerk as AgentWallet;
}

// Re-export primary types at crate root for convenience.
pub use cipherclerk::{
    AgentCipherclerk, AuthorizationPresentation, DelegatedToken, DelegationAuthority,
    DisclosureSpec, FactDisclosure, FactIndex, HeldToken, LocalDelegation, OwnedStealthNote,
    SignedTurn, VerificationMode,
};
#[cfg(feature = "network")]
pub use client::{PresentationResult, RevocationStatus, SiloClient};
pub use committed_turn::{
    CommittedNoteInput, CommittedNoteOutput, CommittedTurnBuilder, OwnedNote,
};
pub use error::SdkError;
pub use runtime::{AgentRuntime, SubAgent};

/// Short alias for [`AgentCipherclerk`] — the "capability clerk" handle.
///
/// Use in tight scopes where the full name would dominate signatures.
pub use cipherclerk::AgentCipherclerk as AgentCClerk;

/// Legacy alias for [`AgentCipherclerk`].
///
/// Preserved while downstream consumers (apps, starbridge-apps, the
/// discord bot, the extension wallet) migrate. New code should reach
/// for [`AgentCipherclerk`] (or the short [`AgentCClerk`] alias).
pub use cipherclerk::AgentCipherclerk as AgentWallet;

// Re-export commonly needed types from dependencies so users don't need
// to add them separately.
pub use pyana_cell::{CellId, Ledger};
pub use pyana_circuit::{BabyBear, IvcProof, verify_ivc};
pub use pyana_token::{Attenuation, AuthRequest, AuthToken};
pub use pyana_turn::{Effect, QueueTxOp, Turn, TurnBuilder, TurnReceipt};
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
#[cfg(feature = "network")]
pub use embed::{EmbedError, EngineConfig, PyanaEngine, WireCodec};

// Re-export privacy API types at crate root for convenience.
pub use privacy::{
    AccumulatorNonMembershipProof, AnonymousPresentation, NonRevocationProof, NoteSecret,
    NoteTransferProof, UnlinkablePredicateProof, verify_accumulator_non_membership,
    verify_anonymous_presentation, verify_non_revocation_proof, verify_note_spending,
};

// Re-export full turn proof composition API.
pub use full_turn_proof::{
    FullTurnProof, FullTurnVerifyError, FullTurnWitness, TurnProofComponents, prove_full_turn,
    prove_turn_self_sovereign, prove_turn_with_auth, verify_full_turn,
};

// Re-export discharge gateway client functions.
#[cfg(feature = "network")]
pub use discharge::{authorize_with_discharges, extract_third_party_tickets, obtain_discharge};

// Re-export standalone verification functions.
#[cfg(any(test, feature = "dev"))]
pub use verify::verify_any_tier;
pub use verify::{
    build_federation_tree, verify_authorization_proof, verify_committed_threshold,
    verify_disclosure_presentation, verify_production, verify_selective_disclosure,
    verify_selective_presentation, verify_validated_ivc_proof,
};

// Re-export proof tier types for downstream use.
pub use pyana_circuit::{CryptographicProof, ProofTier, VerifiedProof};

// Re-export name resolution types for the petname system.
#[cfg(feature = "captp")]
pub use names::{
    CipherclerkNames, EdgeNameEntry, NameError, NameProvenance, NameResolver, PetnameDb,
    PetnameEntry, ProposedNameEntry, ResolvedName, WhoisResult,
};

/// Legacy alias for [`CipherclerkNames`].
#[cfg(feature = "captp")]
pub use names::CipherclerkNames as WalletNames;

// Re-export CapTP client types for capability sharing and pipelining.
#[cfg(feature = "captp")]
pub use captp_client::{CapTpClient, CapTpConfig, EventualRef, LiveRef};
#[cfg(feature = "captp")]
pub use pyana_captp::handoff::HandoffCertificate;
#[cfg(feature = "captp")]
pub use pyana_captp::pipeline::PipelinedAction;
#[cfg(feature = "captp")]
pub use pyana_captp::uri::PyanaUri;
#[cfg(feature = "captp")]
pub use pyana_captp::{FederationId, GroupId};
