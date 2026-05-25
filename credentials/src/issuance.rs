//! Credential issuance.
//!
//! Issuing a credential mints a root macaroon under the issuer's HMAC key
//! and applies a single attenuation that binds the holder + the attribute
//! values. The result is a [`Credential`] that the holder can store and
//! later present without further interaction with the issuer.
//!
//! # Wire shape
//!
//! A credential is a triple:
//! 1. The issuer's 32-byte HMAC root key (the issuer keeps a copy; the
//!    holder receives a *derived* per-credential subkey when needed —
//!    see G39 / G40 of PYANA-FLAWS-FROM-APPS.md for the non-revocation
//!    binding work this enables).
//! 2. The macaroon token bytes (`em2_...` base64-encoded).
//! 3. The federation root the credential was anchored against. Verifiers
//!    use this root to reconstruct the issuer membership Merkle proof.
//!
//! The issuer never sends their HMAC root key to the holder — the holder
//! receives only the encoded macaroon. The `Credential` struct's
//! `root_key` field is the *holder's* re-derivation slot, populated only
//! when the holder constructs a `Credential` from an encoded token they
//! already trust (e.g., when reconstructing from disk).

use macaroon::Macaroon;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;

use pyana_token::{Attenuation, AuthToken, MacaroonToken};

use crate::schema::{AttrValue, AttributeAttenuation, CredentialAttributes, CredentialSchema};

/// Issuer keys: a 32-byte HMAC root key plus a 32-byte federation membership
/// commitment.
///
/// The HMAC key is used to mint root macaroons; the federation commitment
/// is the 32-byte root of the issuer-membership Merkle tree that verifiers
/// use to check the issuer is recognized.
#[derive(Clone, Debug)]
pub struct IssuerKeys {
    /// HMAC root key for macaroon minting. **Never share this.**
    pub root_key: [u8; 32],
    /// Federation membership root (the value verifiers compare against).
    pub federation_root: [u8; 32],
    /// Issuer key identifier — typically a hash of the issuer's public
    /// signature key. Bound into the macaroon's `kid`.
    pub kid: Vec<u8>,
    /// Macaroon location field. By convention this is a stable identifier
    /// for the issuer's domain (e.g., `"pyana.dev"`).
    pub location: String,
}

impl IssuerKeys {
    /// Build an issuer-keys triple.
    pub fn new(
        root_key: [u8; 32],
        federation_root: [u8; 32],
        kid: impl Into<Vec<u8>>,
        location: impl Into<String>,
    ) -> Self {
        Self {
            root_key,
            federation_root,
            kid: kid.into(),
            location: location.into(),
        }
    }
}

/// A verifiable credential.
///
/// Carries an encoded macaroon (the issuer-signed proof of the attribute
/// bindings) plus the metadata a verifier needs to reconstruct the
/// issuer-membership proof. The `attributes` field is held in cleartext
/// here for the *holder's* convenience — selective disclosure is enforced
/// at presentation time, not by withholding the attribute map.
///
/// # Privacy
///
/// A `Credential` is the holder's possession. It is **never** transmitted
/// to a verifier; only [`crate::Presentation`]s leave the holder's machine.
/// The presentation proof leaks only what the holder explicitly disclosed
/// plus the federation root the credential was issued against.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Credential {
    /// The base64-encoded macaroon (`em2_...`).
    pub encoded: String,

    /// The issuer's HMAC root key. The holder needs this to reconstruct
    /// the `MacaroonToken` for attenuation/presentation. The issuer
    /// transmits this *out-of-band* over a secure channel (e.g., the
    /// `pyana-storage::Inbox` encrypted-to-holder primitive — G12).
    pub root_key: [u8; 32],

    /// The federation root this credential is anchored against.
    pub federation_root: [u8; 32],

    /// The schema describing the credential's attribute layout.
    pub schema: CredentialSchema,

    /// Cleartext attribute values, retained for the holder's selective
    /// disclosure logic. Never transmitted.
    pub attributes: CredentialAttributes,

    /// Holder identifier — a 32-byte hash committed in the credential
    /// (typically `blake3(holder_pk)`).
    pub holder_id: [u8; 32],

    /// Issuance timestamp (Unix seconds).
    pub issued_at: i64,

    /// Optional expiry timestamp (Unix seconds). `None` = no expiry.
    pub not_after: Option<i64>,
}

impl Credential {
    /// Reconstruct the `MacaroonToken` from this credential. Used at
    /// presentation time.
    pub fn token(&self) -> Result<MacaroonToken, IssuanceError> {
        MacaroonToken::from_encoded(&self.encoded, self.root_key)
            .map_err(|e| IssuanceError::Encoding(e.to_string()))
    }

    /// Compute a stable 32-byte credential id (the BLAKE3 hash of the
    /// encoded macaroon). Suitable for use as a revocation key.
    pub fn id(&self) -> [u8; 32] {
        *blake3::hash(self.encoded.as_bytes()).as_bytes()
    }
}

/// Issuance failure.
#[derive(Debug, Error)]
pub enum IssuanceError {
    #[error("schema mismatch: attribute `{0}` not in schema `{1}`")]
    UnknownAttribute(String, String),
    #[error("schema mismatch: required attribute `{0}` missing")]
    MissingAttribute(String),
    #[error("macaroon encoding error: {0}")]
    Encoding(String),
    #[error("attenuation rejected by macaroon backend: {0}")]
    Backend(String),
}

/// Issue a credential.
///
/// Mints a fresh macaroon under `issuer.root_key`, then attenuates it
/// with the holder binding (`confine_user`) and the requested attribute
/// values (`features` carrying `name=value` pairs).
///
/// The macaroon-backend attenuation vocabulary is deliberately narrow —
/// it only knows about apps/services/features/users/expiry — so attribute
/// values are encoded into the `features` slot as `name:value` strings.
/// At presentation time the bridge converts these into facts whose
/// predicate is `feature` and whose subject is the holder.
pub fn issue(
    issuer: &IssuerKeys,
    schema: &CredentialSchema,
    holder_id: [u8; 32],
    attributes: CredentialAttributes,
    issued_at: i64,
    not_after: Option<i64>,
) -> Result<Credential, IssuanceError> {
    // Verify every supplied attribute is in the schema.
    for AttributeAttenuation { name, .. } in &attributes.attributes {
        if !schema.has_attribute(name) {
            return Err(IssuanceError::UnknownAttribute(
                name.clone(),
                schema.name.clone(),
            ));
        }
    }

    // Mint the root macaroon.
    let root = MacaroonToken::mint(issuer.root_key, &issuer.kid, &issuer.location);

    // Build the issuance attenuation:
    //   * confine_user = hex(holder_id)
    //   * features    = ["schema:<name>", "<attr_name>:<value-hex>", ...]
    //   * not_after   = expiry (if set)
    let holder_user = hex_encode(&holder_id);
    let mut features = Vec::with_capacity(attributes.attributes.len() + 1);
    features.push(format!("schema:{}", schema.name));
    for AttributeAttenuation { name, value } in &attributes.attributes {
        features.push(encode_attribute(name, value));
    }

    let att = Attenuation {
        confine_user: Some(holder_user),
        features,
        not_after,
        ..Default::default()
    };

    let attenuated = root
        .attenuate(&att)
        .map_err(|e| IssuanceError::Backend(e.to_string()))?;

    let encoded = attenuated
        .to_encoded()
        .map_err(|e| IssuanceError::Encoding(e.to_string()))?;

    Ok(Credential {
        encoded,
        root_key: issuer.root_key,
        federation_root: issuer.federation_root,
        schema: schema.clone(),
        attributes,
        holder_id,
        issued_at,
        not_after,
    })
}

/// Encode an attribute `(name, value)` pair as a `features` entry.
///
/// The encoded form is `name:<hex-of-fact-term>` so that values round-trip
/// through macaroon's UTF-8 caveat representation. The fact-term is the
/// canonical 32-byte digest used downstream by the bridge.
fn encode_attribute(name: &str, value: &AttrValue) -> String {
    let term = value.to_fact_term();
    format!("{}:{}", name, hex_encode(&term))
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Helper for the test path: pull the attribute name/value pairs out of
/// a credential, indexed by name.
#[doc(hidden)]
pub fn attribute_map(creds: &Credential) -> BTreeMap<String, AttrValue> {
    creds
        .attributes
        .attributes
        .iter()
        .map(|a| (a.name.clone(), a.value.clone()))
        .collect()
}

// Silence the unused import warning if the consumer doesn't reach into
// the macaroon crate.
#[allow(dead_code)]
fn _macaroon_type_anchor() -> Option<Macaroon> {
    None
}
