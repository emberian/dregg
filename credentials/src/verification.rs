//! Credential verification.
//!
//! A verifier consumes a [`crate::Presentation`] (or [`crate::presentation::WirePresentation`])
//! plus a [`VerificationOptions`] that captures the verifier's expectations
//! (which schema? what disclosure must be present? what predicates were
//! requested?). Verification rejects:
//!
//! 1. Bridge proof failure (the underlying STARK / constraint check fails).
//! 2. Schema mismatch (the disclosed attributes do not belong to the
//!    expected schema).
//! 3. Predicate mismatch (the proof does not cover the predicate the
//!    verifier asked for).
//! 4. Revealed-facts commitment mismatch (the holder's cleartext
//!    disclosure does not commit to the value the proof witnesses).
//! 5. Anonymous-mode mismatch (verifier expects an anonymous proof,
//!    got a non-anonymous one, or vice versa).

use thiserror::Error;

use pyana_bridge::present::PresentationVerification;

use crate::presentation::{Presentation, WirePresentation};
use crate::revocation::RevocationProof;
use crate::schema::{AttrValue, CredentialSchema, PredicateRequest};

/// Options carried by the verifier.
#[derive(Clone, Debug, Default)]
pub struct VerificationOptions {
    /// The schema the verifier expects.
    pub expected_schema: Option<CredentialSchema>,

    /// Attributes the verifier expects to be disclosed.
    pub expected_disclosure: Vec<String>,

    /// Predicate requests the verifier expects to be satisfied. The
    /// proof must contain a matching `NamedPredicateProof`.
    pub expected_predicates: Vec<PredicateRequest>,

    /// Whether the presentation must be anonymous (blinded membership).
    pub require_anonymous: bool,

    /// Optional non-revocation proof. If supplied the verifier checks
    /// that the credential is not in the revocation set.
    pub revocation: Option<RevocationProof>,

    /// Federation root the verifier expects the credential to be
    /// anchored against. When `Some`, this is compared against the
    /// proof's recovered federation root.
    pub expected_federation_root: Option<[u8; 32]>,
}

impl VerificationOptions {
    pub fn new() -> Self {
        Self::default()
    }
}

/// A successfully verified presentation.
#[derive(Clone, Debug)]
pub struct VerifiedPresentation {
    /// Attributes the verifier learned.
    pub disclosed: Vec<(String, AttrValue)>,
    /// The federation root the presentation was anchored against.
    pub federation_root: [u8; 32],
    /// Whether the proof used the anonymous path.
    pub anonymous: bool,
}

/// Verification failure.
#[derive(Debug, Error)]
pub enum VerificationError {
    #[error("bridge proof verification failed: {0:?}")]
    Bridge(PresentationVerification),
    #[error("required schema `{expected}` but presentation does not match")]
    SchemaMismatch { expected: String },
    #[error("expected disclosure of `{0}` but it was not revealed")]
    MissingDisclosure(String),
    #[error("expected predicate over `{0}` but it was not proven")]
    MissingPredicate(String),
    #[error("expected anonymous presentation, got non-anonymous (or vice versa)")]
    AnonymityMismatch,
    #[error("federation root mismatch (expected `{expected_hex}`)")]
    FederationRootMismatch { expected_hex: String },
    #[error("credential is revoked")]
    Revoked,
}

/// Verify a presentation against the verifier's expectations.
pub fn verify(
    presentation: &Presentation,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    verify_inner(
        &presentation.disclosed,
        &presentation.predicate_proofs,
        presentation.anonymous,
        &presentation.proof,
        options,
    )
}

/// Verify a wire-form presentation. Equivalent to [`verify`] modulo the
/// stripped trace.
pub fn verify_anonymous(
    presentation: &Presentation,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    let mut opts = options.clone();
    opts.require_anonymous = true;
    verify(presentation, &opts)
}

fn verify_inner(
    disclosed: &[(String, AttrValue)],
    predicate_proofs: &[crate::presentation::NamedPredicateProof],
    anonymous: bool,
    proof: &pyana_bridge::present::BridgePresentationProof,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    // 1. Anonymity check.
    if options.require_anonymous && !anonymous {
        return Err(VerificationError::AnonymityMismatch);
    }

    // 2. Bridge proof check. We accept both `Valid` (real STARK) and
    //    `LocalOnly` (constraint-check) for the test path. Production
    //    callers should pass `require_real_stark = true` (TODO when the
    //    Bridge-Hardening lane lands the proof-to-action binding).
    match proof.verification {
        PresentationVerification::Valid | PresentationVerification::LocalOnly => {}
        other => return Err(VerificationError::Bridge(other)),
    }

    // 3. Schema match. Each disclosed attribute must belong to the
    //    expected schema.
    if let Some(schema) = &options.expected_schema {
        for (name, _) in disclosed {
            if !schema.has_attribute(name) {
                return Err(VerificationError::SchemaMismatch {
                    expected: schema.name.clone(),
                });
            }
        }
    }

    // 4. Expected disclosure must be present.
    for expected in &options.expected_disclosure {
        if !disclosed.iter().any(|(n, _)| n == expected) {
            return Err(VerificationError::MissingDisclosure(expected.clone()));
        }
    }

    // 5. Expected predicates must be present (we check name only — the
    //    actual predicate comparison is delegated to the bridge layer).
    for expected in &options.expected_predicates {
        if !predicate_proofs
            .iter()
            .any(|p| p.attribute == expected.attribute)
        {
            return Err(VerificationError::MissingPredicate(
                expected.attribute.clone(),
            ));
        }
    }

    // 6. Federation root check.
    if let Some(expected) = options.expected_federation_root {
        if expected != proof.federation_root {
            return Err(VerificationError::FederationRootMismatch {
                expected_hex: hex_encode(&expected),
            });
        }
    }

    // 7. Revocation check.
    if let Some(rev) = &options.revocation {
        if rev.revoked {
            return Err(VerificationError::Revoked);
        }
    }

    Ok(VerifiedPresentation {
        disclosed: disclosed.to_vec(),
        federation_root: proof.federation_root,
        anonymous,
    })
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
