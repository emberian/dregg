//! # dregg-sdk
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
//!   (held tokens, cipherclerk contents) is private to the user.
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
//! The unified agent SDK for the dregg federation protocol.
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
//! `AgentCipherclerk` (alias `AgentCClerk`, legacy alias `AgentCipherclerk`) is the
//! agent-side *cryptographic clerk*: it holds signing keys, authorization
//! tokens, the receipt chain, and presents credentials/proofs on behalf of a
//! Principal. The name borrows from Greg Egan's *Polis* (and its descendants),
//! where a citizen's "cipherclerk" is the autonomous component that manages
//! their cryptographic identity and capability handles. "Cipherclerk" was a poor
//! fit — cipherclerks connote value storage, but a dregg cipherclerk's authority
//! is mostly *capabilities*, not balances.
//!
//! # Quick Start
//!
//! ```no_run
//! use dregg_sdk::{AgentCipherclerk, AgentRuntime};
//! use dregg_token::Attenuation;
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

// Modules that pull tokio / dregg-wire / dregg-captp are gated so the crate
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
pub mod witness_artifact;
pub mod wordlist;

/// Legacy module name for the cipherclerk surface.
///
/// During the rename window this re-exports `cipherclerk` plus an
/// `AgentCipherclerk` alias so downstream `use dregg_sdk::cipherclerk::...`
/// paths keep compiling. New code should reach for
/// `dregg_sdk::cipherclerk`.
#[doc(hidden)]
pub mod cclerk {
    pub use crate::cipherclerk::AgentCipherclerk;
    pub use crate::cipherclerk::*;
}

// Re-export primary types at crate root for convenience.
pub use cipherclerk::{
    AgentCipherclerk, AuthorizationPresentation, ChainAppendError, DelegatedToken,
    DelegationAuthority, DisclosureSpec, FactDisclosure, FactIndex, HeldToken, LocalDelegation,
    OwnedStealthNote, SignedTurn, VerificationMode,
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
/// discord bot, the extension cipherclerk) migrate. New code should reach
/// for [`AgentCipherclerk`] (or the short [`AgentCClerk`] alias).
// pub use cipherclerk::AgentCipherclerk as AgentCipherclerk; // already re-exported above

// Re-export commonly needed types from dependencies so users don't need
// to add them separately.
pub use dregg_cell::{CellId, Ledger};
pub use dregg_circuit::{BabyBear, IvcProof, verify_ivc};
pub use dregg_token::{Attenuation, AuthRequest, AuthToken};
pub use dregg_turn::{Effect, QueueTxOp, Turn, TurnBuilder, TurnReceipt, WitnessedReceipt};
pub use dregg_turn::{
    VerifyError, verify_receipt_chain, verify_receipt_chain_head, verify_receipt_extends,
};
pub use dregg_types::{PublicKey, Signature};

// Re-export verifier types from the bridge layer for standalone proof verification.
pub use dregg_bridge::present::BridgePresentationProof;
pub use dregg_bridge::verifier::StarkProofVerifier;
pub use dregg_circuit::PresentationVerification;

// Re-export mnemonic generation at crate root for convenience.
pub use mnemonic::generate_mnemonic;

// Re-export privacy primitives for stealth addresses, value commitments, and encrypted intents.
pub use dregg_cell::stealth::{
    StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress,
};
pub use dregg_cell::value_commitment::{
    BulletproofRangeProof, ConservationProof, FullConservationProof, ValueCommitment,
    ValueCommitmentBytes,
};
pub use dregg_intent::sse::EncryptedIntent;

// Re-export the no-IO embed layer for service integration.
#[cfg(feature = "network")]
pub use embed::{DreggEngine, EmbedError, EngineConfig, WireCodec};

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
pub use witness_artifact::{
    WITNESSED_RECEIPT_ARTIFACT_FORMAT, decode_witnessed_receipt_artifact,
    decode_witnessed_receipt_artifact_hex, encode_witnessed_receipt_artifact,
};

// Re-export proof tier types for downstream use.
pub use dregg_circuit::{CryptographicProof, ProofTier, VerifiedProof};

// Re-export name resolution types for the petname system.
#[cfg(feature = "captp")]
pub use names::{
    CipherclerkNames, EdgeNameEntry, NameError, NameProvenance, NameResolver, PetnameDb,
    PetnameEntry, ProposedNameEntry, ResolvedName, WhoisResult,
};

/// Legacy alias for [`CipherclerkNames`].
#[cfg(feature = "captp")]
// pub use names::CipherclerkNames as CipherclerkNames; // already re-exported above

// Re-export CapTP client types for capability sharing and pipelining.
#[cfg(feature = "captp")]
pub use captp_client::{CapTpClient, CapTpConfig, EventualRef, LiveRef};
#[cfg(feature = "captp")]
pub use dregg_captp::handoff::HandoffCertificate;
#[cfg(feature = "captp")]
pub use dregg_captp::pipeline::PipelinedAction;
#[cfg(feature = "captp")]
pub use dregg_captp::uri::DreggUri;
#[cfg(feature = "captp")]
pub use dregg_captp::{FederationId, GroupId};
