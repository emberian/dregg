//! Credential schema and attribute types.
//!
//! A credential schema names the attributes a credential carries (e.g.,
//! "age", "country", "kyc_level"). The schema is data; the issuer signs
//! the attribute *values* into the macaroon at issue time. This crate
//! deliberately does not curate domain schemas (KYC, government ID,
//! employment) — that's caller territory.

use serde::{Deserialize, Serialize};

pub use pyana_bridge::present::Predicate;

/// A credential schema description.
///
/// Schemas pin the attribute set the credential is expected to carry.
/// Verifiers reject presentations whose attribute set diverges from the
/// schema they expect.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CredentialSchema {
    /// Human-readable schema name (e.g., `"gov-id-v1"`).
    pub name: String,

    /// Ordered list of attribute names. Order matters: the bridge fold
    /// chain hashes them in the order they appear here, so verifiers
    /// must agree on the order to recompute the fact commitments.
    pub attributes: Vec<String>,
}

impl CredentialSchema {
    /// Construct a schema from an ordered attribute list.
    pub fn new(name: impl Into<String>, attributes: Vec<String>) -> Self {
        Self {
            name: name.into(),
            attributes,
        }
    }

    /// Returns `true` if the schema declares the given attribute name.
    pub fn has_attribute(&self, name: &str) -> bool {
        self.attributes.iter().any(|a| a == name)
    }
}

/// A typed attribute value.
///
/// Unlike `apps/identity/AttributeValue`, this enum does *not* truncate
/// strings to 4 bytes when hashing — text is hashed in full via blake3
/// and the resulting 32-byte digest is what carries through the circuit
/// as a fact term. (See G4 in `PYANA-FLAWS-FROM-APPS.md` — the 4-byte
/// truncation is one of the most-reproduced bugs in the codebase.)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AttrValue {
    /// An integer (fits in `u64`, but predicate comparisons run in
    /// BabyBear so values >= 2^31 will not be compared soundly without
    /// range checks — see G4).
    Integer(u64),
    /// A string. Hashed via blake3 → 32-byte digest. Not truncated.
    Text(String),
    /// A date encoded as days since the Unix epoch.
    Date(u32),
    /// A boolean flag.
    Bool(bool),
}

impl AttrValue {
    /// Convert to the canonical 32-byte fact term used in the macaroon
    /// caveat encoding.
    pub fn to_fact_term(&self) -> [u8; 32] {
        match self {
            AttrValue::Integer(v) => {
                let mut out = [0u8; 32];
                out[24..32].copy_from_slice(&v.to_be_bytes());
                out
            }
            AttrValue::Text(s) => *blake3::hash(s.as_bytes()).as_bytes(),
            AttrValue::Date(d) => {
                let mut out = [0u8; 32];
                out[28..32].copy_from_slice(&d.to_be_bytes());
                out
            }
            AttrValue::Bool(b) => {
                let mut out = [0u8; 32];
                out[31] = if *b { 1 } else { 0 };
                out
            }
        }
    }

    /// Convert to a u32 value suitable for `prove_predicate_for_fact`.
    /// Returns `None` for values that don't fit (long text, etc.).
    pub fn to_predicate_value(&self) -> Option<u32> {
        match self {
            AttrValue::Integer(v) => u32::try_from(*v).ok(),
            AttrValue::Date(d) => Some(*d),
            AttrValue::Bool(b) => Some(if *b { 1 } else { 0 }),
            AttrValue::Text(_) => None,
        }
    }
}

/// A single attribute the issuer binds into the credential.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttributeAttenuation {
    /// Attribute name (must appear in the credential's schema).
    pub name: String,
    /// Attribute value.
    pub value: AttrValue,
}

/// Map of attribute name → value used at issuance time.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CredentialAttributes {
    pub attributes: Vec<AttributeAttenuation>,
}

impl CredentialAttributes {
    /// Build a fresh attribute map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append an attribute. Returns `self` for builder chaining.
    pub fn with(mut self, name: impl Into<String>, value: AttrValue) -> Self {
        self.attributes.push(AttributeAttenuation {
            name: name.into(),
            value,
        });
        self
    }

    /// Look up an attribute by name.
    pub fn get(&self, name: &str) -> Option<&AttrValue> {
        self.attributes
            .iter()
            .find(|a| a.name == name)
            .map(|a| &a.value)
    }
}

/// A predicate request issued by a verifier: "prove this attribute
/// satisfies this predicate, without revealing the value".
///
/// The holder produces a `BridgePredicateProof` (re-exported from
/// `pyana-bridge`) bound to the credential's state root.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PredicateRequest {
    /// Attribute name the predicate applies to.
    pub attribute: String,
    /// The predicate (e.g., `Predicate::Gte(18)`).
    pub predicate: Predicate,
}

impl PredicateRequest {
    pub fn new(attribute: impl Into<String>, predicate: Predicate) -> Self {
        Self {
            attribute: attribute.into(),
            predicate,
        }
    }
}
