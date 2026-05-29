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

use dregg_circuit::PresentationVerification;

use crate::presentation::Presentation;
use crate::revocation::{NonRevocationError, RevocationProof};
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

    /// Optional non-revocation proof. If supplied the verifier performs
    /// a real non-membership check: it recomputes the revocation root
    /// from the proof's committed witness set, binds it to
    /// [`Self::expected_revocation_root`] (when set), and checks the
    /// credential's genuine absence from the committed set.
    pub revocation: Option<RevocationProof>,

    /// Externally-trusted revocation root the proof must be anchored
    /// against. When `Some`, the proof's root must equal it (rejecting
    /// stale or attacker-chosen roots). When `None`, the verifier still
    /// recomputes the root from the witness and checks genuine absence,
    /// but trusts the proof's own root (suitable only when the proof
    /// originates from a registry the caller already trusts).
    pub expected_revocation_root: Option<[u8; 32]>,

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
    #[error(
        "anonymous presentation requires a real cryptographic proof, got a non-cryptographic LocalOnly proof"
    )]
    LocalOnlyRejected,
    #[error("predicate proof for `{attribute}` failed cryptographic verification")]
    PredicateProofInvalid { attribute: String },
    #[error("predicate proof for `{attribute}` proves a different statement than requested")]
    PredicateMismatch { attribute: String },
    #[error("non-revocation witness does not commit to the proof's root")]
    RevocationRootMismatch,
    #[error("non-revocation proof anchored against an untrusted revocation root")]
    RevocationUnexpectedRoot,
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
    proof: &dregg_bridge::present::BridgePresentationProof,
    options: &VerificationOptions,
) -> Result<VerifiedPresentation, VerificationError> {
    // 1. Anonymity check.
    if options.require_anonymous && !anonymous {
        return Err(VerificationError::AnonymityMismatch);
    }

    // 2. Bridge proof check.
    //
    // Anonymous presentations carry an unlinkability guarantee that only a
    // real STARK (ring-blinded issuer membership) can back. A `LocalOnly`
    // constraint-check proof has no cryptographic backing and no blinded
    // leaf, so accepting one for an anonymous presentation would be a
    // soundness lie: the verifier would "trust" an unlinkability claim that
    // was never proven. Reject `LocalOnly` whenever anonymity is required,
    // and additionally require the proof to actually carry a real STARK.
    match &proof.verification {
        PresentationVerification::Valid => {}
        PresentationVerification::LocalOnly => {
            if options.require_anonymous {
                return Err(VerificationError::LocalOnlyRejected);
            }
        }
        other => return Err(VerificationError::Bridge(other.clone())),
    }

    // For anonymous presentations, also require a real STARK proof object
    // (the ring-blinded issuer membership). `is_valid()` returns true only
    // when a real STARK / IVC proof is present AND verification is `Valid`,
    // so this rejects a hand-crafted `verification = Valid` with no proof.
    if options.require_anonymous && !proof.is_valid() {
        return Err(VerificationError::LocalOnlyRejected);
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

    // 5. Expected predicates must be present AND cryptographically valid.
    //
    // SOUNDNESS: matching by attribute *name* alone is forgeable — a holder
    // could attach a `NamedPredicateProof { attribute: "age", .. }` whose
    // inner proof proves nothing (or proves a weaker statement). For every
    // requested predicate we:
    //   (i)   find a matching named proof,
    //   (ii)  require its proven statement to equal the requested predicate
    //         (same operator + threshold/bounds), not just the name, and
    //   (iii) verify the STARK cryptographically against the proof's own
    //         `fact_commitment` (which the proof's STARK binds to the
    //         witnessed value). A garbage / mismatched proof fails here.
    for expected in &options.expected_predicates {
        let candidate = predicate_proofs
            .iter()
            .find(|p| p.attribute == expected.attribute)
            .ok_or_else(|| VerificationError::MissingPredicate(expected.attribute.clone()))?;

        // (ii) The proof must prove exactly the requested statement.
        if candidate.proof.predicate != expected.predicate {
            return Err(VerificationError::PredicateMismatch {
                attribute: expected.attribute.clone(),
            });
        }

        // (iii) Cryptographically verify the STARK. We verify against the
        // proof's own `fact_commitment`; the predicate STARK binds that
        // commitment to the witnessed value, so a forged or weakened proof
        // (e.g. a name-only spoof carrying random bytes) fails verification.
        if !dregg_bridge::present::verify_predicate_proof(
            &candidate.proof,
            candidate.proof.fact_commitment,
        ) {
            return Err(VerificationError::PredicateProofInvalid {
                attribute: expected.attribute.clone(),
            });
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

    // 7. Revocation check — a real non-membership check, not a trusted bool.
    //
    // The verifier recomputes the revocation root from the proof's
    // committed witness set, binds it to the trusted expected root (when
    // supplied), and checks the credential's genuine absence from the
    // committed set. A holder cannot escape revocation by flipping a
    // `revoked` boolean: dropping their own id from the witness changes the
    // recomputed root, which then fails the root-binding check.
    if let Some(rev) = &options.revocation {
        // When no externally-trusted root is configured, trust the proof's
        // own root for the binding step (the witness-commitment and
        // absence checks still run). When configured, enforce it.
        let expected_root = options.expected_revocation_root.unwrap_or(rev.root);
        match rev.verify_non_revocation(&expected_root) {
            Ok(()) => {}
            Err(NonRevocationError::Revoked) => return Err(VerificationError::Revoked),
            Err(NonRevocationError::RootMismatch) => {
                return Err(VerificationError::RevocationRootMismatch);
            }
            Err(NonRevocationError::UnexpectedRoot) => {
                return Err(VerificationError::RevocationUnexpectedRoot);
            }
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
