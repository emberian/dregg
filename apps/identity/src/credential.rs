//! Credential schema, issuance, and storage.
//!
//! A credential is a set of attributes (key-value pairs) issued by an authority
//! and bound to a holder. The credential is committed to via Poseidon2 hashing,
//! producing a Merkle leaf suitable for inclusion in federation trees.

use crate::{AttributeName, AttributeValue, CredentialId, HolderId, IssuerId};
use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2;
use std::collections::BTreeMap;

/// A credential schema defining what attributes a credential type contains.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CredentialSchema {
    /// Human-readable name of the credential type (e.g., "GovernmentID", "EmploymentCert").
    pub name: String,
    /// The issuer who defines this schema.
    pub issuer_id: IssuerId,
    /// Ordered list of attribute names in this schema.
    pub attributes: Vec<AttributeName>,
}

/// A signed credential issued to a holder.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Credential {
    /// Unique identifier (hash of credential contents).
    pub id: CredentialId,
    /// The schema this credential conforms to.
    pub schema_name: String,
    /// The issuer who created this credential.
    pub issuer_id: IssuerId,
    /// The holder this credential is bound to.
    pub holder_id: HolderId,
    /// Attribute values, keyed by attribute name.
    pub attributes: BTreeMap<AttributeName, AttributeValue>,
    /// Issuance timestamp (days since epoch).
    pub issued_at: u32,
    /// Optional expiration (days since epoch). 0 means no expiry.
    pub expires_at: u32,
    /// The credential commitment (Poseidon2 hash of all attributes).
    pub commitment: BabyBear,
    /// Revocation hash: if this appears in the revocation tree, the credential is revoked.
    pub revocation_hash: BabyBear,
}

impl Credential {
    /// Compute the credential commitment from its attributes.
    ///
    /// The commitment is `Poseidon2(issuer_field, holder_field, attr_0, attr_1, ..., attr_n)`.
    /// This binding prevents attribute substitution attacks.
    pub fn compute_commitment(
        issuer_id: &IssuerId,
        holder_id: &HolderId,
        attributes: &BTreeMap<AttributeName, AttributeValue>,
    ) -> BabyBear {
        let issuer_field = crate::issuer_id_to_field(issuer_id);
        let holder_field = {
            let elements = BabyBear::encode_hash(holder_id);
            poseidon2::hash_many(&elements)
        };

        let mut inputs = vec![issuer_field, holder_field];
        for (_name, value) in attributes.iter() {
            inputs.push(value.to_field());
        }
        poseidon2::hash_many(&inputs)
    }

    /// Compute the revocation hash for this credential.
    ///
    /// This is derived from the credential ID so that the issuer can add it
    /// to the revocation tree without knowing the credential's private attributes.
    pub fn compute_revocation_hash(id: &CredentialId) -> BabyBear {
        pyana_dsl_runtime::revocation::revocation_hash_to_field(id)
    }

    /// Get a specific attribute value.
    pub fn get_attribute(&self, name: &str) -> Option<&AttributeValue> {
        self.attributes.get(name)
    }

    /// Get a specific attribute as a field element.
    pub fn get_attribute_field(&self, name: &str) -> Option<BabyBear> {
        self.attributes.get(name).map(|v| v.to_field())
    }

    /// Compute the fact hash for a specific attribute (for predicate proofs).
    ///
    /// The fact hash is `Poseidon2(predicate_symbol, value, 0, 0)` where predicate_symbol
    /// is the hash of the attribute name.
    pub fn attribute_fact_hash(&self, attr_name: &str) -> Option<BabyBear> {
        let value = self.get_attribute_field(attr_name)?;
        let predicate_symbol = {
            let hash = blake3::hash(attr_name.as_bytes());
            let bytes = hash.as_bytes();
            let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
            BabyBear::new(val)
        };
        Some(poseidon2::hash_fact(
            predicate_symbol,
            &[value, BabyBear::ZERO, BabyBear::ZERO],
        ))
    }

    /// Compute the fact commitment binding an attribute to this credential's state.
    ///
    /// This is used as the public input for predicate proofs, binding the proven
    /// value to this specific credential.
    pub fn attribute_fact_commitment(&self, attr_name: &str) -> Option<BabyBear> {
        let fact_hash = self.attribute_fact_hash(attr_name)?;
        Some(pyana_circuit::dsl::predicates::compute_fact_commitment(
            fact_hash,
            self.commitment,
        ))
    }
}

/// Builder for constructing credentials.
pub struct CredentialBuilder {
    schema_name: String,
    issuer_id: IssuerId,
    holder_id: HolderId,
    attributes: BTreeMap<AttributeName, AttributeValue>,
    issued_at: u32,
    expires_at: u32,
}

impl CredentialBuilder {
    /// Create a new credential builder.
    pub fn new(schema_name: &str, issuer_id: IssuerId, holder_id: HolderId) -> Self {
        Self {
            schema_name: schema_name.to_string(),
            issuer_id,
            holder_id,
            attributes: BTreeMap::new(),
            issued_at: 0,
            expires_at: 0,
        }
    }

    /// Add an attribute to the credential.
    pub fn attribute(mut self, name: &str, value: AttributeValue) -> Self {
        self.attributes.insert(name.to_string(), value);
        self
    }

    /// Set the issuance timestamp.
    pub fn issued_at(mut self, timestamp: u32) -> Self {
        self.issued_at = timestamp;
        self
    }

    /// Set the expiration timestamp (0 for no expiry).
    pub fn expires_at(mut self, timestamp: u32) -> Self {
        self.expires_at = timestamp;
        self
    }

    /// Build the credential, computing its ID and commitment.
    pub fn build(self) -> Credential {
        let commitment =
            Credential::compute_commitment(&self.issuer_id, &self.holder_id, &self.attributes);

        // Compute credential ID from all content.
        let id_input = format!(
            "{}:{}:{}:{}",
            self.schema_name,
            hex::encode(self.issuer_id),
            hex::encode(self.holder_id),
            commitment.as_u32(),
        );
        let id_hash = blake3::hash(id_input.as_bytes());
        let id: CredentialId = *id_hash.as_bytes();

        let revocation_hash = Credential::compute_revocation_hash(&id);

        Credential {
            id,
            schema_name: self.schema_name,
            issuer_id: self.issuer_id,
            holder_id: self.holder_id,
            attributes: self.attributes,
            issued_at: self.issued_at,
            expires_at: self.expires_at,
            commitment,
            revocation_hash,
        }
    }
}

/// Encode bytes as hex string (simple implementation to avoid extra deps).
mod hex {
    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes
            .as_ref()
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect()
    }
}
