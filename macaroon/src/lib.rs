//! Pyana Macaroon Library
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
pub mod caveat_3p;
pub mod crypto;
pub mod discharge_gateway;
pub mod error;
pub mod format;
pub mod macaroon;
pub mod resource;

// Re-export primary types at crate root.
pub use access::Access;
pub use action::Action;
pub use caveat::{Caveat, CaveatSet, CaveatType, WireCaveat};
pub use caveat_3p::ThirdPartyCaveat;
pub use discharge_gateway::{
    AllOfEvaluator, AllowlistEvaluator, AlwaysAllow, AnyOfEvaluator, ConditionEvaluator,
    DischargeError, DischargeGateway, DischargeRequest, DischargeResponse, PaymentEvaluator,
    ProofRequiredEvaluator, RateLimitEvaluator, TimeWindowEvaluator,
};
pub use error::{CaveatError, MacaroonError, MacaroonResult};
pub use format::{decode_token, encode_token};
pub use macaroon::{Macaroon, Nonce, create_discharge};
pub use resource::ResourceSet;
