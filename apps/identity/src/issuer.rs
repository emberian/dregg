//! Issuer registry: credential issuance, revocation, and status management.
//!
//! An issuer is an entity (government, employer, bank) that creates credentials
//! attesting facts about holders. The issuer maintains:
//! - A registry of issued credentials
//! - A revocation tree (sorted Merkle) for revoking credentials
//! - Membership in a federation (Merkle tree of trusted issuers)

use crate::credential::{Credential, CredentialBuilder, CredentialSchema};
use crate::{AttributeValue, CredentialId, HolderId, IssuerId};
use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2;
use pyana_dsl_runtime::revocation::{DslRevocationTree, TREE_DEPTH as REVOCATION_TREE_DEPTH};
use std::collections::BTreeMap;

/// An issuer that can create and revoke credentials.
pub struct IssuerRegistry {
    /// The issuer's unique identifier.
    pub issuer_id: IssuerId,
    /// The issuer's public key hash (for federation membership).
    pub public_key_hash: BabyBear,
    /// Schemas this issuer supports.
    schemas: BTreeMap<String, CredentialSchema>,
    /// All issued credentials (by ID).
    issued: BTreeMap<CredentialId, Credential>,
    /// Revoked credential hashes.
    revoked_hashes: Vec<BabyBear>,
    /// The current revocation tree (rebuilt on revocation).
    revocation_tree: DslRevocationTree,
}

impl IssuerRegistry {
    /// Create a new issuer registry.
    pub fn new(issuer_id: IssuerId) -> Self {
        let public_key_hash = crate::issuer_id_to_field(&issuer_id);
        Self {
            issuer_id,
            public_key_hash,
            schemas: BTreeMap::new(),
            issued: BTreeMap::new(),
            revoked_hashes: Vec::new(),
            revocation_tree: DslRevocationTree::new(Vec::new(), REVOCATION_TREE_DEPTH),
        }
    }

    /// Register a credential schema.
    pub fn register_schema(&mut self, schema: CredentialSchema) {
        self.schemas.insert(schema.name.clone(), schema);
    }

    /// Issue a credential to a holder.
    ///
    /// Returns the issued credential, which the holder can store in their cclerk.
    pub fn issue(
        &mut self,
        schema_name: &str,
        holder_id: HolderId,
        attributes: BTreeMap<String, AttributeValue>,
        issued_at: u32,
        expires_at: u32,
    ) -> Option<Credential> {
        // Verify schema exists (if any are registered).
        if !self.schemas.is_empty() && !self.schemas.contains_key(schema_name) {
            return None;
        }

        let mut builder = CredentialBuilder::new(schema_name, self.issuer_id, holder_id)
            .issued_at(issued_at)
            .expires_at(expires_at);

        for (name, value) in attributes {
            builder = builder.attribute(&name, value);
        }

        let credential = builder.build();
        self.issued.insert(credential.id, credential.clone());
        Some(credential)
    }

    /// Revoke a credential by its ID.
    ///
    /// Adds the credential's revocation hash to the revocation tree.
    /// After this, any non-revocation proof for this credential will fail.
    pub fn revoke(&mut self, credential_id: &CredentialId) -> bool {
        let revocation_hash = Credential::compute_revocation_hash(credential_id);

        // Check not already revoked.
        if self.revoked_hashes.iter().any(|h| *h == revocation_hash) {
            return false;
        }

        self.revoked_hashes.push(revocation_hash);
        // Rebuild the revocation tree with the new entry.
        self.revocation_tree =
            DslRevocationTree::new(self.revoked_hashes.clone(), REVOCATION_TREE_DEPTH);
        true
    }

    /// Check if a credential is revoked.
    pub fn is_revoked(&self, credential_id: &CredentialId) -> bool {
        let revocation_hash = Credential::compute_revocation_hash(credential_id);
        self.revocation_tree.contains(&revocation_hash)
    }

    /// Get the current revocation tree root.
    pub fn revocation_root(&self) -> BabyBear {
        self.revocation_tree.root()
    }

    /// Get a reference to the revocation tree (for generating non-revocation proofs).
    pub fn revocation_tree(&self) -> &DslRevocationTree {
        &self.revocation_tree
    }

    /// Get a credential by ID.
    pub fn get_credential(&self, id: &CredentialId) -> Option<&Credential> {
        self.issued.get(id)
    }

    /// Get the number of issued credentials.
    pub fn num_issued(&self) -> usize {
        self.issued.len()
    }

    /// Get the number of revoked credentials.
    pub fn num_revoked(&self) -> usize {
        self.revoked_hashes.len()
    }
}

/// A federation of trusted issuers, represented as a Poseidon2 Merkle tree.
///
/// Verifiers check that a credential's issuer is a member of the federation
/// before accepting a presentation.
pub struct IssuerFederation {
    /// Member issuer public key hashes.
    members: Vec<BabyBear>,
    /// The federation Merkle root.
    root: BabyBear,
    /// Tree depth.
    depth: usize,
}

impl IssuerFederation {
    /// Create a federation from a set of issuer public key hashes.
    pub fn new(issuer_hashes: Vec<BabyBear>, depth: usize) -> Self {
        let root = Self::compute_root(&issuer_hashes, depth);
        Self {
            members: issuer_hashes,
            root,
            depth,
        }
    }

    /// Compute the Merkle root for a set of members.
    fn compute_root(members: &[BabyBear], depth: usize) -> BabyBear {
        let capacity = 4usize.pow(depth as u32);
        let mut level: Vec<BabyBear> = Vec::with_capacity(capacity);
        level.extend_from_slice(members);
        level.resize(capacity, BabyBear::ZERO);

        for _ in 0..depth {
            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(poseidon2::hash_4_to_1(&[
                    chunk[0], chunk[1], chunk[2], chunk[3],
                ]));
            }
            level = next_level;
        }

        assert_eq!(level.len(), 1);
        level[0]
    }

    /// Get the federation root.
    pub fn root(&self) -> BabyBear {
        self.root
    }

    /// Check if an issuer is a member.
    pub fn contains(&self, issuer_hash: &BabyBear) -> bool {
        self.members.contains(issuer_hash)
    }

    /// Generate a Merkle membership proof for an issuer.
    ///
    /// Returns (siblings_per_level, positions_per_level) for the issuer membership AIR.
    pub fn prove_membership(
        &self,
        issuer_hash: &BabyBear,
    ) -> Option<(Vec<[BabyBear; 3]>, Vec<u8>)> {
        let position = self.members.iter().position(|h| h == issuer_hash)?;

        let capacity = 4usize.pow(self.depth as u32);
        let mut padded = Vec::with_capacity(capacity);
        padded.extend_from_slice(&self.members);
        padded.resize(capacity, BabyBear::ZERO);

        let mut siblings = Vec::with_capacity(self.depth);
        let mut positions = Vec::with_capacity(self.depth);
        let mut level = padded;
        let mut idx = position;

        for _ in 0..self.depth {
            let group_base = (idx / 4) * 4;
            let pos_in_group = (idx % 4) as u8;
            positions.push(pos_in_group);

            let mut sibs = [BabyBear::ZERO; 3];
            let mut sib_idx = 0;
            for i in 0..4 {
                if i == pos_in_group as usize {
                    continue;
                }
                sibs[sib_idx] = level[group_base + i];
                sib_idx += 1;
            }
            siblings.push(sibs);

            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(poseidon2::hash_4_to_1(&[
                    chunk[0], chunk[1], chunk[2], chunk[3],
                ]));
            }
            level = next_level;
            idx = idx / 4;
        }

        Some((siblings, positions))
    }

    /// Number of members.
    pub fn num_members(&self) -> usize {
        self.members.len()
    }

    /// Tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }
}
