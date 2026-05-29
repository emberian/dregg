//! Credential revocation.
//!
//! Revocation is an *issuer-side* operation: the issuer maintains a set
//! of revoked credential ids and publishes a federation-attested root
//! commitment. Verifiers carry that root commitment and check
//! non-membership at presentation time.
//!
//! # Soundness model
//!
//! A [`RevocationProof`] is **not** a self-asserted `revoked` boolean — a
//! malicious holder could simply flip such a bool. Instead the proof
//! carries the full sorted committed revocation set (the *witness*) and
//! the verifier:
//!
//! 1. Recomputes the root from the witness and checks it equals the
//!    proof's claimed `root` (the witness must commit to the published
//!    root — a holder cannot substitute a smaller set).
//! 2. Checks the proof's `root` equals the verifier's externally-trusted
//!    `expected_revocation_root` (so a holder cannot present a stale or
//!    attacker-chosen root).
//! 3. Performs the actual non-membership check: the candidate
//!    `credential_id` must be *absent* from the committed set.
//!
//! This is the in-process analogue of a sorted-leaf Merkle non-membership
//! proof (cf. `cell::predicate::WitnessedPredicateKind::NonMembership`):
//! the root binds the set, and absence is verified against that bound set
//! rather than trusted. A production deployment swaps the full-set witness
//! for a sorted-neighbor Merkle witness against a federation-attested root
//! (per G39 in `DREGG-FLAWS-FROM-APPS.md`) without changing the verifier's
//! contract: recompute-root → match-expected → check-absence.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use crate::issuance::Credential;

/// A revocation registry maintained by an issuer.
///
/// Cheap to clone (internally `Arc<RwLock<...>>`); shareable between the
/// issuance HTTP server and any background revocation publisher.
#[derive(Clone, Debug)]
pub struct RevocationRegistry {
    inner: Arc<RwLock<RevocationInner>>,
}

impl Default for RevocationRegistry {
    fn default() -> Self {
        Self::new()
    }
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
        // A fresh registry must publish the REAL commitment over its (empty)
        // set — `compute_revocation_root(&[])` — not the all-zero struct
        // default. The verifier recomputes the root from the proof's witness
        // set and binds it to this published root; a zero placeholder would
        // never match `compute_revocation_root(&[])` and would reject every
        // honest pre-revocation non-membership proof.
        let reg = Self {
            inner: Arc::new(RwLock::new(RevocationInner::default())),
        };
        reg.rebuild_root();
        reg
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

    /// Generate a non-revocation proof for a credential.
    ///
    /// The proof carries the full sorted committed revocation set as a
    /// witness so the verifier can independently recompute the root and
    /// check the candidate id's absence — it does not rely on a trusted
    /// `revoked` boolean. See [`RevocationProof::verify_non_revocation`].
    pub fn prove_non_revocation(&self, credential_id: [u8; 32]) -> RevocationProof {
        let inner = self.inner.read().unwrap();
        let mut revoked_set: Vec<[u8; 32]> = inner.revoked.iter().copied().collect();
        revoked_set.sort();
        let revoked = inner.revoked.contains(&credential_id);
        RevocationProof {
            credential_id,
            root: inner.root,
            revoked,
            revoked_set,
        }
    }

    fn rebuild_root(&self) {
        let mut inner = self.inner.write().unwrap();
        let mut sorted: Vec<[u8; 32]> = inner.revoked.iter().copied().collect();
        sorted.sort();
        inner.root = compute_revocation_root(&sorted);
    }
}

/// Compute the revocation-set root commitment over a *sorted* id list.
///
/// This is the single source of truth for the root binding: both the
/// issuer (when rebuilding the registry root) and the verifier (when
/// re-deriving the root from a [`RevocationProof`]'s witness) call it, so
/// a holder cannot present a witness that hashes to a different root than
/// the one they claim.
///
/// The caller must pass the ids already sorted ascending; the function
/// re-sorts defensively so an out-of-order witness cannot be smuggled
/// past the root check (it would hash to the canonical order regardless).
pub fn compute_revocation_root(ids: &[[u8; 32]]) -> [u8; 32] {
    let mut sorted: Vec<[u8; 32]> = ids.to_vec();
    sorted.sort();
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-credentials-revocation-root-v1");
    for id in &sorted {
        hasher.update(id);
    }
    *hasher.finalize().as_bytes()
}

/// A non-revocation proof.
///
/// Carries a verifiable witness — the full sorted committed revocation
/// set — rather than a trusted `revoked` boolean. The verifier recomputes
/// the root from `revoked_set`, binds it to a trusted expected root, and
/// checks the candidate `credential_id`'s absence. See
/// [`Self::verify_non_revocation`].
///
/// When the non-revocation STARK lands per G39 the `revoked_set` witness
/// is replaced by a sorted-neighbor Merkle witness against a
/// federation-attested root; the verifier contract (recompute → match →
/// absence) is unchanged.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevocationProof {
    /// The credential being attested against.
    pub credential_id: [u8; 32],
    /// The revocation root the proof is anchored against.
    pub root: [u8; 32],
    /// Convenience flag mirroring set membership. **Not trusted by the
    /// verifier** — [`Self::verify_non_revocation`] recomputes absence
    /// from `revoked_set`. Retained for diagnostics and the issuer-side
    /// `revoke()` return value.
    pub revoked: bool,
    /// The sorted committed revocation set. The verifier recomputes the
    /// root from this witness; a holder cannot drop their own id from it
    /// without changing the root (which then fails the expected-root bind).
    pub revoked_set: Vec<[u8; 32]>,
}

/// Why a non-revocation check failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonRevocationError {
    /// The witness set does not hash to the proof's claimed root: the
    /// holder tampered with the committed set.
    RootMismatch,
    /// The proof's root does not match the verifier's trusted expected
    /// root: stale or attacker-chosen revocation root.
    UnexpectedRoot,
    /// The candidate credential is present in the committed set: revoked.
    Revoked,
}

impl RevocationProof {
    /// Cryptographically check non-revocation against an externally
    /// trusted revocation root.
    ///
    /// Fail-closed contract:
    /// 1. `compute_revocation_root(revoked_set) == self.root` — the
    ///    witness must commit to the claimed root.
    /// 2. `expected_root == self.root` — the claimed root must match the
    ///    verifier's trusted root.
    /// 3. `!revoked_set.contains(credential_id)` — genuine absence.
    ///
    /// Returns `Ok(())` only when all three hold.
    pub fn verify_non_revocation(
        &self,
        expected_root: &[u8; 32],
    ) -> Result<(), NonRevocationError> {
        // 1. The witness must commit to the proof's claimed root.
        if compute_revocation_root(&self.revoked_set) != self.root {
            return Err(NonRevocationError::RootMismatch);
        }
        // 2. The claimed root must equal the verifier's trusted root.
        if *expected_root != self.root {
            return Err(NonRevocationError::UnexpectedRoot);
        }
        // 3. Genuine non-membership against the committed set.
        if self.revoked_set.contains(&self.credential_id) {
            return Err(NonRevocationError::Revoked);
        }
        Ok(())
    }
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
