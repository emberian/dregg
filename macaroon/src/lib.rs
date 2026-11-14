//! Dregg Macaroon Library
//!
//! Macaroons are HMAC-authenticated bearer tokens with cryptographically
//! enforced caveat attenuation. Inspired by [Google's macaroons paper][paper]
//! and [Fly.io's implementation][flyio].
//!
//! # Core Properties
//!
//! - **Attenuation**: Caveats can only restrict access, never expand it.
//!   Removing a caveat is cryptographically impossible (HMAC chain).
//! - **Third-party delegation**: External services can be required to
//!   discharge caveats, enabling pluggable authentication without the
//!   verifier contacting the third party.
//! - **Offline verification**: Everything needed to verify is in the tokens
//!   themselves — no network calls required.
//! - **Composable**: Multiple caveats stack with AND semantics.
//!
//! # Modules
//!
//! - [`macaroon`] — Core `Macaroon` type: create, attenuate, verify, bind
//! - [`caveat`] — `Caveat` trait, `CaveatSet`, wire encoding
//! - [`caveat_3p`] — Third-party caveats: tickets, discharge, encryption
//! - [`crypto`] — HMAC-SHA256 chaining, XChaCha20-Poly1305 sealing
//! - [`format`] — Wire format: MsgPack + base64url + `em2_` prefix
//! - [`access`] — `Access` trait for domain-specific authorization
//! - [`action`] — `Action` bitmask for resource permissions
//! - [`resource`] — `ResourceSet<ID, Action>` for typed resource→action maps
//! - [`error`] — Error types
//!
//! [paper]: https://research.google/pubs/pub41892/
//! [flyio]: https://fly.io/blog/macaroons-escalated-quickly/

pub mod access;
pub mod action;
pub mod caveat;
#[cfg(feature = "crypto")]
pub mod caveat_3p;
/// Differential: the verified Lean `Dregg2.Authority.CaveatChain` FIRST-PARTY model ⟺ this crate's
/// real HMAC chain (`Macaroon::{new, add_first_party, verify}`): replay agreement (`replayTag` ==
/// real tail byte-for-byte), `honest_chain_verifies`, and the integrity teeth (removal / tamper /
/// wrong-key REJECTED). Test-only. Companion to `discharge_diff` (the third-party half).
#[cfg(all(test, feature = "crypto"))]
mod caveat_chain_diff;
#[cfg(feature = "crypto")]
pub mod crypto;
/// Differential: the verified Lean `Dregg2.Authority.MacaroonDischarge` model ⟺ this crate's real
/// third-party discharge binding (`bind_discharge`/`verify_discharge`): replay agreement, the
/// unbound-rejected fail-closed tooth, and no-cross-root-replay. Test-only.
#[cfg(all(test, feature = "crypto"))]
mod discharge_diff;
#[cfg(feature = "crypto")]
pub mod discharge_gateway;
pub mod error;
#[cfg(feature = "crypto")]
pub mod format;
#[cfg(feature = "crypto")]
pub mod macaroon;
pub mod resource;

// Re-export primary types at crate root.
pub use access::Access;
pub use action::Action;
pub use caveat::{Caveat, CaveatSet, CaveatType, WireCaveat};
#[cfg(feature = "crypto")]
pub use caveat_3p::ThirdPartyCaveat;
#[cfg(feature = "crypto")]
pub use discharge_gateway::{
    AllOfEvaluator, AllowlistEvaluator, AnyOfEvaluator, CAV_DISCHARGE_HOLDER,
    CAV_DISCHARGE_PAYMENT, CAV_DISCHARGE_PROOF, ConditionEvaluator, DischargeContext,
    DischargeError, DischargeGateway, DischargeRequest, DischargeResponse, PaymentAttestation,
    PaymentEvaluator, PaymentVerifierFn, ProofAttestation, ProofVerifierFn, RateLimitEvaluator,
    ReplaySetLoadError, TicketCondition, TimeWindowEvaluator, VerifyingProofEvaluator,
    ticket_caveats, ticket_digest,
};
pub use error::{CaveatError, MacaroonError, MacaroonResult};
#[cfg(feature = "crypto")]
pub use format::{decode_token, encode_token};
#[cfg(feature = "crypto")]
pub use macaroon::{Macaroon, Nonce, create_discharge};
pub use resource::ResourceSet;

#[cfg(feature = "crypto")]
pub mod ingress;
