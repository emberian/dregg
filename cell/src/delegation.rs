//! Snapshot+refresh delegation model for capability inheritance.
//!
//! In E-style delegation, a child cell inherits its parent's capabilities as a
//! SNAPSHOT. The child can act offline using the snapshot, and periodically
//! refreshes to pick up new capabilities. Revocation is eventual, bounded by
//! `max_staleness` — acceptors may reject stale snapshots at verification time.
//!
//! # Commitment Binding
//!
//! To prevent a malicious parent from constructing a `DelegatedRef` containing
//! fabricated capabilities, the struct includes a `clist_commitment` field: a
//! BLAKE3 hash of the parent's serialized c-list at snapshot time. Verifiers can
//! cross-check this commitment against the parent's known state on the ledger.
//!
//! Additionally, the parent signs over `(clist_commitment, delegation_epoch, child_cell_id)`
//! so that a verifier can cryptographically confirm the delegation is authentic.

use serde::{Deserialize, Serialize};

use crate::capability::CapabilityRef;
use crate::id::CellId;

/// Serde helper for `[u8; 64]` (Ed25519 signatures in DelegatedRef).
mod delegation_sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

/// A delegated capability snapshot from a parent cell.
///
/// This represents the E-style delegation model: the child receives a point-in-time
/// copy of the parent's c-list. The child can act using this snapshot without
/// contacting the parent. Freshness is checked by acceptors (remote verifiers),
/// not by the executor.
///
/// # Security: Commitment Binding
///
/// The `clist_commitment` is a BLAKE3 hash of the parent's full serialized c-list
/// at the time this snapshot was created. This binds the delegated capabilities to
/// the parent's actual state — a malicious parent cannot fabricate capabilities that
/// weren't in their c-list without producing an invalid commitment.
///
/// The `parent_signature` is an Ed25519 signature over
/// `(clist_commitment || delegation_epoch || child_cell_id)`, proving the parent
/// authorized this specific delegation. Verifiers can check this signature against
/// the parent's known public key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DelegatedRef {
    /// The parent cell this delegation comes from.
    pub source: CellId,
    /// The child cell this delegation targets.
    pub child: CellId,
    /// Snapshot of capabilities inherited from parent.
    pub snapshot: Vec<CapabilityRef>,
    /// Parent's delegation epoch when this snapshot was taken.
    pub delegation_epoch: u64,
    /// Timestamp when this snapshot was last refreshed.
    pub refreshed_at: u64,
    /// Maximum acceptable staleness (seconds). Acceptors may reject
    /// if `now - refreshed_at > max_staleness`. Zero means "always refresh."
    pub max_staleness: u64,
    /// BLAKE3 hash of the parent's full serialized c-list at snapshot time.
    ///
    /// Verifiers cross-check this against the parent's known ledger state to
    /// confirm the delegated capabilities were actually held by the parent.
    /// If the parent revokes or changes their c-list, this commitment won't match.
    pub clist_commitment: [u8; 32],
    /// Ed25519 signature from the parent over (clist_commitment || delegation_epoch || child_cell_id).
    ///
    /// Proves the parent authorized this delegation. Verifiable against the parent's
    /// public key without contacting the parent.
    #[serde(with = "delegation_sig_serde")]
    pub parent_signature: [u8; 64],
}

impl DelegatedRef {
    /// Create a new delegated reference with commitment binding.
    ///
    /// The `clist_commitment` should be computed via [`Self::compute_clist_commitment`]
    /// over the parent's full c-list. The `parent_signature` should be an Ed25519
    /// signature over the message produced by [`Self::signing_message`].
    pub fn new(
        source: CellId,
        child: CellId,
        snapshot: Vec<CapabilityRef>,
        delegation_epoch: u64,
        refreshed_at: u64,
        max_staleness: u64,
        clist_commitment: [u8; 32],
        parent_signature: [u8; 64],
    ) -> Self {
        DelegatedRef {
            source,
            child,
            snapshot,
            delegation_epoch,
            refreshed_at,
            max_staleness,
            clist_commitment,
            parent_signature,
        }
    }

    /// Compute the BLAKE3 commitment over a serialized c-list.
    ///
    /// The input should be the postcard-serialized bytes of the parent's full
    /// `CapabilitySet` (or `Vec<CapabilityRef>`) at the time of delegation.
    /// This is domain-separated to prevent cross-protocol confusion.
    pub fn compute_clist_commitment(serialized_clist: &[u8]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-delegation-clist-commitment-v1");
        hasher.update(serialized_clist);
        *hasher.finalize().as_bytes()
    }

    /// Compute the message that the parent signs for this delegation.
    ///
    /// The signed message is:
    /// `BLAKE3_derive_key("pyana-delegation-sig-v1", clist_commitment || delegation_epoch_le || child_cell_id_bytes)`
    pub fn signing_message(
        clist_commitment: &[u8; 32],
        delegation_epoch: u64,
        child_cell_id: &CellId,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-delegation-sig-v1");
        hasher.update(clist_commitment);
        hasher.update(&delegation_epoch.to_le_bytes());
        hasher.update(child_cell_id.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Verify the parent's signature over this delegation.
    ///
    /// Returns `true` if the signature is valid for the given parent public key.
    #[cfg(feature = "crypto")]
    pub fn verify_parent_signature(&self, parent_pubkey: &[u8; 32]) -> bool {
        use ed25519_dalek::{Signature, VerifyingKey};

        let message =
            Self::signing_message(&self.clist_commitment, self.delegation_epoch, &self.child);
        let signature = Signature::from_bytes(&self.parent_signature);

        if let Ok(vk) = VerifyingKey::from_bytes(parent_pubkey) {
            vk.verify_strict(&message, &signature).is_ok()
        } else {
            false
        }
    }

    /// Check if this delegation is stale relative to the given timestamp.
    ///
    /// A staleness of zero means "always stale" (always refresh before use).
    /// Otherwise, the delegation is stale if `now - refreshed_at > max_staleness`.
    pub fn is_stale(&self, now: u64) -> bool {
        if self.max_staleness == 0 {
            return true; // always stale = always refresh
        }
        now.saturating_sub(self.refreshed_at) > self.max_staleness
    }

    /// Check if a specific capability is available in the snapshot.
    pub fn has_capability(&self, target: &CellId) -> bool {
        self.snapshot.iter().any(|cap| &cap.target == target)
    }

    /// Get capabilities for a specific target from the snapshot.
    pub fn capabilities_for(&self, target: &CellId) -> Vec<&CapabilityRef> {
        self.snapshot
            .iter()
            .filter(|cap| &cap.target == target)
            .collect()
    }

    /// Number of capabilities in this snapshot.
    pub fn len(&self) -> usize {
        self.snapshot.len()
    }

    /// Whether the snapshot is empty.
    pub fn is_empty(&self) -> bool {
        self.snapshot.is_empty()
    }
}
