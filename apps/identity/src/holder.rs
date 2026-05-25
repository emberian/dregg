//! Credential cclerk: store, select, and compose credential presentations.
//!
//! The holder stores their credentials and can:
//! - Select which credentials to use in a presentation
//! - Choose which attributes to reveal (selective disclosure)
//! - Compose multiple credentials into a single multi-credential presentation

use crate::credential::Credential;
use crate::presentation::PresentationRequest;
use crate::{CredentialId, HolderId};
use std::collections::BTreeMap;

/// A credential cclerk held by an identity holder.
pub struct CredentialWallet {
    /// The holder's identifier.
    pub holder_id: HolderId,
    /// Stored credentials indexed by ID.
    credentials: BTreeMap<CredentialId, Credential>,
}

impl CredentialWallet {
    /// Create a new empty cclerk for a holder.
    pub fn new(holder_id: HolderId) -> Self {
        Self {
            holder_id,
            credentials: BTreeMap::new(),
        }
    }

    /// Store a credential in the cclerk.
    pub fn store(&mut self, credential: Credential) {
        self.credentials.insert(credential.id, credential);
    }

    /// Remove a credential from the cclerk.
    pub fn remove(&mut self, id: &CredentialId) -> Option<Credential> {
        self.credentials.remove(id)
    }

    /// Get a credential by ID.
    pub fn get(&self, id: &CredentialId) -> Option<&Credential> {
        self.credentials.get(id)
    }

    /// List all credential IDs.
    pub fn list_ids(&self) -> Vec<CredentialId> {
        self.credentials.keys().copied().collect()
    }

    /// Find credentials matching a schema name.
    pub fn find_by_schema(&self, schema_name: &str) -> Vec<&Credential> {
        self.credentials
            .values()
            .filter(|c| c.schema_name == schema_name)
            .collect()
    }

    /// Find credentials from a specific issuer.
    pub fn find_by_issuer(&self, issuer_id: &[u8; 32]) -> Vec<&Credential> {
        self.credentials
            .values()
            .filter(|c| &c.issuer_id == issuer_id)
            .collect()
    }

    /// Select credentials that can satisfy a presentation request.
    ///
    /// Returns the selected credentials that together can fulfill all requirements
    /// in the request. Returns None if the cclerk cannot satisfy the request.
    pub fn select_for_request(&self, request: &PresentationRequest) -> Option<Vec<&Credential>> {
        let mut selected = Vec::new();

        for requirement in &request.requirements {
            // Find a credential that has the required attribute.
            let matching = self
                .credentials
                .values()
                .find(|c| c.attributes.contains_key(&requirement.attribute_name));

            match matching {
                Some(cred) => {
                    if !selected.iter().any(|s: &&Credential| s.id == cred.id) {
                        selected.push(cred);
                    }
                }
                None => return None,
            }
        }

        Some(selected)
    }

    /// Number of credentials in the cclerk.
    pub fn len(&self) -> usize {
        self.credentials.len()
    }

    /// Whether the cclerk is empty.
    pub fn is_empty(&self) -> bool {
        self.credentials.is_empty()
    }
}
