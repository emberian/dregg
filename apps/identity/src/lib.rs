//! Decentralized identity and verifiable credentials system built on pyana ZK proofs.
//!
//! Demonstrates the full credential lifecycle:
//! - Issue: Issuer creates a signed credential attesting facts about the holder
//! - Hold: Holder stores credentials in a wallet
//! - Present: Holder proves specific attributes via selective disclosure or predicates
//! - Verify: Verifier checks presentations without learning private data
//! - Revoke: Issuer revokes credentials; revoked credentials cannot produce valid proofs
//!
//! # Privacy Properties
//!
//! - **Selective Disclosure**: Reveal only chosen attributes from a credential
//! - **Predicate Proofs**: Prove comparisons (age >= 18) without revealing the value
//! - **Anonymous Credentials**: Prove membership in a set without revealing which member
//! - **Unlinkability**: Presentations from the same credential are unlinkable across verifiers
//! - **Non-Revocation**: Prove a credential has not been revoked without revealing which one

pub mod anonymous;
pub mod credential;
pub mod holder;
pub mod issuer;
pub mod presentation;
pub mod revocation;
pub mod server;
pub mod verifier;

#[cfg(test)]
mod tests;

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2;

/// A unique identifier for a credential (hash of its contents).
pub type CredentialId = [u8; 32];

/// A unique identifier for an issuer (derived from their public key).
pub type IssuerId = [u8; 32];

/// A unique identifier for a holder (stealth address or public key hash).
pub type HolderId = [u8; 32];

/// An attribute name (string-based for ergonomics, hashed for circuits).
pub type AttributeName = String;

/// An attribute value that can be committed to in ZK circuits.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AttributeValue {
    /// An integer value (fits in BabyBear field element).
    Integer(u32),
    /// A string value (hashed for circuit use).
    Text(String),
    /// A date stored as days since epoch (for date arithmetic).
    Date(u32),
    /// A boolean flag.
    Bool(bool),
    /// Raw field element.
    Field(u32),
}

impl AttributeValue {
    /// Convert to a BabyBear field element for use in circuits.
    pub fn to_field(&self) -> BabyBear {
        match self {
            AttributeValue::Integer(v) => BabyBear::new(*v),
            AttributeValue::Text(s) => {
                let hash = blake3::hash(s.as_bytes());
                let bytes = hash.as_bytes();
                let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                BabyBear::new(val)
            }
            AttributeValue::Date(d) => BabyBear::new(*d),
            AttributeValue::Bool(b) => {
                if *b {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                }
            }
            AttributeValue::Field(v) => BabyBear::new(*v),
        }
    }
}

/// Compute a field element from a credential ID.
pub fn credential_id_to_field(id: &CredentialId) -> BabyBear {
    let elements = BabyBear::encode_hash(id);
    poseidon2::hash_many(&elements)
}

/// Compute a field element from an issuer ID.
pub fn issuer_id_to_field(id: &IssuerId) -> BabyBear {
    let elements = BabyBear::encode_hash(id);
    poseidon2::hash_many(&elements)
}
