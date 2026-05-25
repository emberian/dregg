//! `pyana-credentials` — Verifiable credentials for pyana, lifted from
//! `bridge::present` + `macaroon` (PYANA-FLAWS-FROM-APPS.md G31).
//!
//! # Why this crate exists
//!
//! `apps/identity/` (audited 2026-05-24) re-invented a credentials primitive
//! badly: `Credential` had no signature field, `Presentation::verify` trusted
//! a `verified: bool` set on the holder, and 4-byte truncation flowed through
//! `AttributeValue::Text`. Meanwhile, `bridge::present::BridgePresentationBuilder`
//! already implements the *correct* shape — federation-bound issuer membership,
//! real STARK presentation proof, selective disclosure, predicate proofs,
//! unlinkable multi-show — but was buried under a name that didn't advertise
//! "this is the credential primitive". `PYANA-FLAWS-FROM-APPS.md` G31 calls
//! out the promotion explicitly:
//!
//! > Promote `bridge::present` to a top-level "Pyana credentials" module.
//! > `BridgePresentationBuilder` + `macaroon/` already implement what
//! > `apps/identity/` claims to do, *correctly*, with federation-bound issuer
//! > membership and real STARK presentation. The identity app reinvents a
//! > strict subset, badly. Promote this to documented `pyana-credentials` and
//! > deprecate the app's reinvention.
//!
//! # Public surface
//!
//! - [`Credential`] — a credential bound to an issuer, a holder, and a set
//!   of attribute attenuations. Backed by a real signed macaroon, never a
//!   credential-shaped struct with no signature.
//! - [`Presentation`] — a ZK proof that some authorization derives from a
//!   valid credential, without revealing the credential or attribute values
//!   except those the holder explicitly chose to disclose.
//! - [`PredicateRequest`] — selectively prove `Gte`/`Lte`/`InRange`/etc.
//!   over a credential attribute without revealing the attribute value.
//! - [`RevocationProof`] — federation-attested non-revocation against a
//!   published revocation root.
//! - [`issue`] / [`present`] / [`verify`] / [`revoke`] — the canonical
//!   four operations.
//!
//! # What this crate is NOT
//!
//! - It is not a new circuit. All ZK heavy lifting routes through
//!   `pyana-bridge` and `pyana-circuit` exactly as before. This crate is
//!   the ergonomic surface, not a parallel cryptosystem.
//! - It is not a wallet. Key custody is the caller's problem; this crate
//!   accepts already-minted `MacaroonToken`s or root keys.
//! - It does not enumerate identity-domain schemas (KYC, employment,
//!   government ID). Schemas are caller-defined; this crate provides the
//!   plumbing.
//!
//! # Anonymous presentation (`WitnessedPredicate::BlindedMembership`)
//!
//! The Mega-Caveats lane wired `WitnessedPredicateKind::BlindedSet` as the
//! anonymous-set-membership predicate. [`present_anonymous`] composes a
//! `Presentation` with a blinded membership proof so the verifier learns
//! only "the presenter holds *some* credential from this issuer", not which
//! one. The blinding factor is fresh per presentation, so multi-show is
//! unlinkable.

#![forbid(unsafe_code)]

mod issuance;
mod presentation;
mod revocation;
mod schema;
mod verification;

pub use issuance::{Credential, IssuanceError, IssuerKeys, issue};
pub use presentation::{
    Presentation, PresentationError, PresentationOptions, present, present_anonymous,
};
pub use revocation::{RevocationProof, RevocationRegistry, revoke};
pub use schema::{AttrValue, AttributeAttenuation, CredentialAttributes, CredentialSchema};
pub use verification::{
    VerificationError, VerificationOptions, VerifiedPresentation, verify, verify_anonymous,
};

// Re-export underlying types so callers don't need to depend on
// `pyana-bridge` directly when composing their own flows. This is the
// "promote to dedicated module" goal of G31.
pub use pyana_bridge::present::{
    BridgePresentationProof, FederationRegistry, Predicate, WirePresentationProof,
};

// Re-export PredicateRequest from our schema module (different from the
// raw `Predicate` enum — `PredicateRequest` couples a predicate with the
// attribute it applies to).
pub use schema::PredicateRequest;
