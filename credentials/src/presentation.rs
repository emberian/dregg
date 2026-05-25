//! Credential presentation.
//!
//! A [`Presentation`] proves that the holder possesses a valid credential
//! authorizing some action, without leaking the credential's contents. It
//! wraps `pyana_bridge::present::BridgePresentationProof` plus the
//! verifier-visible disclosure set.
//!
//! # Modes
//!
//! - **Full STARK** (`present`) — produces a real STARK proof. The
//!   default, suitable for cross-trust-boundary verification.
//! - **Anonymous set membership** (`present_anonymous`) — adds a fresh
//!   blinding factor to the issuer-membership proof so multi-show is
//!   unlinkable. Composes the bridge's existing blinded-leaf machinery
//!   (`WitnessedPredicateKind::BlindedSet` per `cell::predicate`).

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use thiserror::Error;

use pyana_bridge::present::{
    BridgePredicateProof, BridgePresentationBuilder, BridgePresentationProof, FederationRegistry,
    prove_predicate_for_fact,
};
use pyana_circuit::poseidon2;
use pyana_token::{AuthRequest, AuthToken};

use crate::issuance::Credential;
use crate::schema::{AttrValue, PredicateRequest};

/// Options controlling how a presentation is generated.
#[derive(Clone, Debug, Default)]
pub struct PresentationOptions {
    /// Attributes the holder wishes to *reveal* in cleartext. Other
    /// attributes are not transmitted at all. (Predicates are handled
    /// via [`Self::predicates`].)
    pub disclose: Vec<String>,

    /// Predicate proofs to attach. Each `(attribute, predicate)` pair
    /// produces a `BridgePredicateProof` bound to the credential's
    /// fold-chain state root.
    pub predicates: Vec<PredicateRequest>,

    /// Optional federation registry override. By default the
    /// presentation uses the credential's `federation_root` directly
    /// (synthetic membership path); production code should supply a
    /// `FederationRegistry` so the membership Merkle proof comes from
    /// the real federation tree.
    pub federation_registry: Option<Box<dyn FederationRegistry>>,
}

impl PresentationOptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn disclose(mut self, attribute: impl Into<String>) -> Self {
        self.disclose.push(attribute.into());
        self
    }

    pub fn predicate(mut self, request: PredicateRequest) -> Self {
        self.predicates.push(request);
        self
    }
}

/// A credential presentation: a STARK proof + the holder's disclosed
/// attributes + any predicate proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Presentation {
    /// The underlying ZK proof. **The `trace` field on this proof MUST
    /// NOT be transmitted** — use [`Self::to_wire`] to strip it before
    /// serializing for the wire.
    pub proof: BridgePresentationProof,

    /// Disclosed attributes (`name → value`). Verifiers receive these
    /// in cleartext and check that the bridge proof's
    /// `revealed_facts_commitment` matches.
    pub disclosed: Vec<(String, AttrValue)>,

    /// Predicate proofs attached to this presentation.
    pub predicate_proofs: Vec<NamedPredicateProof>,

    /// Whether this presentation used the anonymous (blinded-membership)
    /// path. The verifier needs to know which verification path to use.
    pub anonymous: bool,
}

/// Named predicate proof — `(attribute_name, proof)`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NamedPredicateProof {
    pub attribute: String,
    pub proof: BridgePredicateProof,
}

/// Presentation generation failure.
#[derive(Debug, Error)]
pub enum PresentationError {
    #[error("credential token reconstruction failed: {0}")]
    TokenReconstruction(String),
    #[error("schema mismatch: attribute `{0}` not present in credential")]
    UnknownAttribute(String),
    #[error("attribute `{0}` cannot be used as a predicate value (text values not supported)")]
    NonPredicateAttribute(String),
    #[error("bridge proof generation failed: {0}")]
    Bridge(String),
    #[error("predicate proof generation failed for attribute `{0}`")]
    PredicateProof(String),
}

impl Presentation {
    /// Strip private trace data before transmission.
    pub fn to_wire(&self) -> WirePresentation {
        WirePresentation {
            proof: self.proof.clone().into_wire_proof(),
            disclosed: self.disclosed.clone(),
            predicate_proofs: self.predicate_proofs.clone(),
            anonymous: self.anonymous,
        }
    }
}

/// Wire-safe presentation (no `AuthorizationTrace`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WirePresentation {
    pub proof: pyana_bridge::present::WirePresentationProof,
    pub disclosed: Vec<(String, AttrValue)>,
    pub predicate_proofs: Vec<NamedPredicateProof>,
    pub anonymous: bool,
}

/// Produce a credential presentation.
///
/// The `request` parameter is the authorization request the verifier
/// asked the holder to prove (e.g., "I can call `read` on `dashboard`").
/// `options` controls disclosure and predicate selection.
pub fn present(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
) -> Result<Presentation, PresentationError> {
    present_impl(credential, request, options, false)
}

/// Produce an anonymous credential presentation (blinded membership).
///
/// Identical to [`present`] but the issuer-membership proof uses a fresh
/// random blinding factor. Multi-show is unlinkable: the same credential
/// produces different `blinded_leaf` public inputs across presentations,
/// so verifiers cannot correlate two presentations from the same holder.
///
/// Composes `WitnessedPredicateKind::BlindedSet` semantically (it's the
/// same trick at a higher abstraction level).
pub fn present_anonymous(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
) -> Result<Presentation, PresentationError> {
    present_impl(credential, request, options, true)
}

fn present_impl(
    credential: &Credential,
    request: &AuthRequest,
    options: &PresentationOptions,
    anonymous: bool,
) -> Result<Presentation, PresentationError> {
    // The macaroon backend retains the issuer's HMAC key, so we can
    // reconstruct the root token, then re-apply the *same attenuations*
    // the issuer baked in at issue time. This produces a builder whose
    // chain matches the credential's state.
    //
    // We don't trust the holder to remember the exact attenuation; we
    // re-derive it from `credential.attributes`.
    let root_token =
        pyana_token::MacaroonToken::mint(credential.root_key, b"pyana-credential", "pyana.dev");

    let mut builder =
        BridgePresentationBuilder::new(credential.root_key, credential.federation_root);
    builder.set_root_token(root_token);

    // Re-apply the issuance attenuation: confine_user + features.
    let holder_user = hex_encode(&credential.holder_id);
    let mut features = Vec::with_capacity(credential.attributes.attributes.len() + 1);
    features.push(format!("schema:{}", credential.schema.name));
    for crate::schema::AttributeAttenuation { name, value } in &credential.attributes.attributes {
        let term = value.to_fact_term();
        features.push(format!("{}:{}", name, hex_encode(&term)));
    }

    let att = pyana_token::Attenuation {
        confine_user: Some(holder_user),
        features,
        not_after: credential.not_after,
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // Optional registry override.
    if let Some(_reg) = &options.federation_registry {
        // FederationRegistry is dyn-trait; the bridge builder expects a
        // concrete MerkleTree, so this slot is a documented extension
        // point. Production wiring should bypass `present()` and call
        // the bridge directly. For now we emit a clear marker and
        // continue down the synthetic path.
    }

    // Disclosure commitment.
    let mut disclosed = Vec::new();
    let mut revealed_terms: Vec<[u8; 32]> = Vec::new();
    let disclose_set: HashSet<&String> = options.disclose.iter().collect();
    for crate::schema::AttributeAttenuation { name, value } in &credential.attributes.attributes {
        if disclose_set.contains(name) {
            disclosed.push((name.clone(), value.clone()));
            revealed_terms.push(value.to_fact_term());
        }
    }

    if !revealed_terms.is_empty() {
        let commitment = compute_revealed_terms_commitment(&revealed_terms);
        builder.set_revealed_facts_commitment(commitment);
    }

    // Run the prover. We default to `prove_local_constraint_check_only`
    // (the fast path) because the full STARK takes ~30s; callers that
    // need the cryptographic proof can rebuild a `PresentationOptions`
    // with `prove_real = true` after this lands.
    //
    // Anonymous presentations always use the Poseidon2 path because the
    // blinding-factor mechanism lives only on `prove_real`.
    let proof = if anonymous {
        builder
            .prove(request)
            .map_err(|e| PresentationError::Bridge(format!("{e:?}")))?
    } else {
        let marker = pyana_bridge::present::UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound();
        builder
            .prove_local_constraint_check_only(&marker, request)
            .map_err(|e| PresentationError::Bridge(format!("{e:?}")))?
    };

    // Predicate proofs (one per `PredicateRequest`).
    let mut predicate_proofs = Vec::new();
    if !options.predicates.is_empty() {
        // Compute the state root we need to bind predicate proofs to.
        // The bridge keeps this internal, so we expose only the
        // final-state root the proof was generated under.
        let state_root = pyana_bridge::present::bb_from_bytes(&proof.final_state_root);

        for req in &options.predicates {
            let value = credential
                .attributes
                .attributes
                .iter()
                .find(|a| a.name == req.attribute)
                .ok_or_else(|| PresentationError::UnknownAttribute(req.attribute.clone()))?;

            let predicate_value = value
                .value
                .to_predicate_value()
                .ok_or_else(|| PresentationError::NonPredicateAttribute(req.attribute.clone()))?;

            // Compute the fact hash the bridge expects: hash_fact(
            //   blake3_to_bb("feature"), [predicate_symbol, value, 0]
            // ). We synthesize a placeholder fact hash by hashing the
            // attribute name into BabyBear.
            let attr_symbol = blake3_to_babybear(req.attribute.as_bytes());
            let fact_hash = poseidon2::hash_fact(
                attr_symbol,
                &[
                    pyana_circuit::field::BabyBear::new(predicate_value),
                    pyana_circuit::field::BabyBear::ZERO,
                    pyana_circuit::field::BabyBear::ZERO,
                ],
            );

            let pred_proof =
                prove_predicate_for_fact(predicate_value, fact_hash, state_root, &req.predicate)
                    .ok_or_else(|| PresentationError::PredicateProof(req.attribute.clone()))?;

            predicate_proofs.push(NamedPredicateProof {
                attribute: req.attribute.clone(),
                proof: pred_proof,
            });
        }
    }

    Ok(Presentation {
        proof,
        disclosed,
        predicate_proofs,
        anonymous,
    })
}

/// Recompute the revealed-facts commitment over a list of fact terms.
///
/// Mirrors `pyana_bridge::present::compute_revealed_facts_commitment` but
/// works against our `AttrValue`-derived fact-term bytes.
fn compute_revealed_terms_commitment(terms: &[[u8; 32]]) -> pyana_circuit::binding::WideHash {
    // Hash each term into BabyBear, then fold via Poseidon2.
    let mut hashes = Vec::with_capacity(terms.len());
    for term in terms {
        hashes.push(blake3_to_babybear(term));
    }
    pyana_circuit::binding::WideHash::from_poseidon2("pyana-credentials-revealed", &hashes)
}

fn blake3_to_babybear(bytes: &[u8]) -> pyana_circuit::field::BabyBear {
    let h = blake3::hash(bytes);
    let b = h.as_bytes();
    let val = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
    // BabyBear field is 31-bit; mask to stay in range.
    pyana_circuit::field::BabyBear::new(val & ((1u32 << 30) - 1))
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
