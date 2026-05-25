//! Credential revocation.
//!
//! Revocation is an *issuer-side* operation: the issuer maintains a set
//! of revoked credential ids and publishes a federation-attested root
//! commitment. Verifiers carry that root commitment and check
//! non-membership at presentation time.
//!
//! # Current limitations
//!
//! - This crate models revocation as a flat `HashSet<credential_id>`
//!   maintained in-process. A production deployment binds the set to a
//!   federation-attested Merkle root and produces a real non-membership
//!   STARK proof (per G39 in `PYANA-FLAWS-FROM-APPS.md`).
//! - The non-revocation STARK should additionally bind `pi::REVOCATION_HASH`
//!   to the credential's id (G39 fix). The wrapper here exposes the slot
//!   so a future patch can substitute a real proof without changing
//!   downstream APIs.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use crate::issuance::Credential;

/// A revocation registry maintained by an issuer.
///
/// Cheap to clone (internally `Arc<RwLock<...>>`); shareable between the
/// issuance HTTP server and any background revocation publisher.
#[derive(Clone, Debug, Default)]
pub struct RevocationRegistry {
    inner: Arc<RwLock<RevocationInner>>,
}

#[derive(Debug, Default)]
struct RevocationInner {
    revoked: HashSet<[u8; 32]>,
    /// Federation-attested root commitment. Refreshed when the set
    /// changes. The "root" here is a blake3 over the sorted ids — a
    /// stand-in for the real revocation Merkle root.
    root: [u8; 32],
}

impl RevocationRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the current root commitment (32 bytes).
    pub fn root(&self) -> [u8; 32] {
        self.inner.read().unwrap().root
    }

    /// Returns `true` if the credential is currently revoked.
    pub fn is_revoked(&self, credential_id: &[u8; 32]) -> bool {
        self.inner.read().unwrap().revoked.contains(credential_id)
    }

    /// Returns the number of revoked credentials.
    pub fn len(&self) -> usize {
        self.inner.read().unwrap().revoked.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.read().unwrap().revoked.is_empty()
    }

    /// Generate a non-revocation proof for a credential. If the
    /// credential is currently revoked, the proof's `revoked` flag is
    /// `true`; otherwise `false`. The verifier must reject the former.
    pub fn prove_non_revocation(&self, credential_id: [u8; 32]) -> RevocationProof {
        let inner = self.inner.read().unwrap();
        RevocationProof {
            credential_id,
            root: inner.root,
            revoked: inner.revoked.contains(&credential_id),
        }
    }

    fn rebuild_root(&self) {
        let mut inner = self.inner.write().unwrap();
        let mut sorted: Vec<[u8; 32]> = inner.revoked.iter().copied().collect();
        sorted.sort();
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-credentials-revocation-root-v1");
        for id in &sorted {
            hasher.update(id);
        }
        inner.root = *hasher.finalize().as_bytes();
    }
}

/// A non-revocation proof.
///
/// Today this is a literal `(credential_id, root, bool)`. When the
/// non-revocation circuit lands per G39 the wire shape will gain a real
/// STARK proof field; the `revoked` boolean is what verifiers actually
/// rely on today.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevocationProof {
    /// The credential being attested against.
    pub credential_id: [u8; 32],
    /// The revocation root the proof is anchored against.
    pub root: [u8; 32],
    /// `true` if the credential is currently revoked.
    pub revoked: bool,
}

/// Revoke a credential.
///
/// Adds the credential's id to the registry and refreshes the root. The
/// returned [`RevocationProof`] reflects the new state (it will have
/// `revoked = true`).
pub fn revoke(registry: &RevocationRegistry, credential: &Credential) -> RevocationProof {
    let id = credential.id();
    {
        let mut inner = registry.inner.write().unwrap();
        inner.revoked.insert(id);
    }
    registry.rebuild_root();
    registry.prove_non_revocation(id)
}
