//! Canonical cell lifecycle.
//!
//! Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.5`, the cell-lifecycle
//! terminal-object gap is the foundational structural absence in the cell
//! model: there was no first-class enumeration of the states a cell can
//! inhabit — "live", "sealed (frozen but reversible)", "destroyed
//! (permanent retirement)", "migrated (relocated to another federation)",
//! "archived (history pruned)". These were implicit in side-channels
//! (`Permissions::frozen()`, `MigrationState::Completed`, etc.) but not
//! a first-class structural shape.
//!
//! This module makes the lifecycle explicit. The default for every freshly
//! constructed cell is [`CellLifecycle::Live`]; existing code paths that
//! construct a cell preserve that default, and the canonical commitment
//! folds the lifecycle byte in so that any transition is bound into the
//! state-commitment chain.

use serde::{Deserialize, Serialize};

use crate::id::CellId;

/// The canonical lifecycle state of a cell.
///
/// A cell starts [`Self::Live`]. It may transition to:
///
/// - [`Self::Sealed`] — *reversible* quiescence. The cell rejects new
///   effects but state and history are preserved. `Unseal` returns to
///   [`Self::Live`].
/// - [`Self::Migrated`] — the cell was relocated to another federation;
///   the local federation retains a tombstone pointing at the destination.
/// - [`Self::Destroyed`] — *permanent* retirement; the cell carries a
///   witnessed [`DeathCertificate`] in its final state and cannot return.
/// - [`Self::Archived`] — the cell's receipt-chain prefix was archived;
///   the cell remains live but its prior history is now summarized by a
///   checkpoint hash.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellLifecycle {
    /// The cell is live; effects flow normally.
    Live,
    /// The cell is sealed. New effects are rejected; state and history
    /// preserved. Reversible via `Effect::CellUnseal`.
    Sealed {
        /// Free-form 32-byte hash of the sealing reason (commit-only;
        /// cleartext lives off-chain).
        reason_hash: [u8; 32],
        /// Federation height at which the seal was applied.
        sealed_at: u64,
    },
    /// The cell was relocated to another federation. The destination
    /// cell id (post-migration) is recorded so observers can follow.
    Migrated {
        /// The destination cell id at the new federation.
        to: CellId,
        /// Attestation hash binding the migration to the destination
        /// federation's acceptance receipt.
        attestation: [u8; 32],
        /// Federation height of the migration finalization.
        migrated_at: u64,
    },
    /// The cell is permanently retired. The [`DeathCertificate`] hash is
    /// bound into this variant so verifiers can prove "this cell is
    /// permanently retired" rather than inferring from absence.
    Destroyed {
        /// Hash of the [`DeathCertificate`] bound into the cell's final
        /// state. The full certificate lives off-chain (or in a
        /// federation-level Merkle tree of death certificates).
        death_certificate_hash: [u8; 32],
        /// Federation height at which destruction took effect.
        destroyed_at: u64,
    },
    /// The cell remains live but its receipt-chain prefix prior to
    /// `archived_through` was archived; replays start from the checkpoint.
    Archived {
        /// Hash of the off-chain archival blob (the serialized chain
        /// prefix).
        checkpoint_hash: [u8; 32],
        /// The last receipt-chain height that has been archived. The
        /// live chain's `previous_receipt_hash` at height
        /// `archived_through + 1` points into the checkpoint.
        archived_through: u64,
    },
}

impl Default for CellLifecycle {
    fn default() -> Self {
        CellLifecycle::Live
    }
}

impl CellLifecycle {
    /// Discriminant byte used by the canonical state commitment.
    ///
    /// Values are stable; new variants append at the end with a fresh
    /// discriminant.
    pub(crate) fn discriminant(&self) -> u8 {
        match self {
            CellLifecycle::Live => 0,
            CellLifecycle::Sealed { .. } => 1,
            CellLifecycle::Migrated { .. } => 2,
            CellLifecycle::Destroyed { .. } => 3,
            CellLifecycle::Archived { .. } => 4,
        }
    }

    /// Whether this lifecycle state accepts new effects.
    ///
    /// Returns `true` only for [`Self::Live`] and [`Self::Archived`] —
    /// archived cells remain live (archival prunes history only).
    pub fn accepts_effects(&self) -> bool {
        matches!(self, CellLifecycle::Live | CellLifecycle::Archived { .. })
    }

    /// Whether this lifecycle state is *permanent* — i.e. no further
    /// transition is allowed. Currently only [`Self::Destroyed`] and
    /// [`Self::Migrated`].
    pub fn is_terminal(&self) -> bool {
        matches!(
            self,
            CellLifecycle::Destroyed { .. } | CellLifecycle::Migrated { .. }
        )
    }

    /// Whether the cell is in a sealed (quiescent but reversible) state.
    pub fn is_sealed(&self) -> bool {
        matches!(self, CellLifecycle::Sealed { .. })
    }

    /// Whether the cell is permanently destroyed.
    pub fn is_destroyed(&self) -> bool {
        matches!(self, CellLifecycle::Destroyed { .. })
    }
}

/// A federation-attested artifact recording a cell's permanent retirement.
///
/// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. The certificate is bound
/// into the cell's final [`CellLifecycle::Destroyed`] state by hash so
/// any holder of the cell's final commitment can demonstrate "this cell
/// was retired at height H with this reason."
///
/// The certificate carries the *minimum* canonical retirement evidence:
/// the cell's identity, its final receipt-chain head, its final state
/// commitment, the height of destruction, and a reason hash. The signing
/// quorum (the federation that witnessed the destruction) attaches a
/// detached signature in a higher-level wrapping — this struct itself is
/// the *content* that gets signed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeathCertificate {
    /// The cell being retired.
    pub cell_id: CellId,
    /// Receipt hash of the cell's last live turn (the receipt-chain
    /// terminator).
    pub last_receipt_hash: [u8; 32],
    /// The state commitment the cell carried at the moment of death.
    pub final_state_commitment: [u8; 32],
    /// Federation height at which destruction took effect.
    pub destroyed_at_height: u64,
    /// Reason for retirement (free-form; opaque to the substrate).
    pub reason: DeathReason,
}

/// Reason for cell destruction. Substrate-opaque; the federation records
/// the value, downstream auditors decode per their conventions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeathReason {
    /// Voluntary retirement by the cell owner (graceful shutdown).
    Voluntary,
    /// Forced retirement by the federation (e.g. policy violation).
    Forced,
    /// Cell migration to another federation; the local copy is being
    /// retired because the destination has accepted custody.
    Migrated,
    /// App-specific reason — the 32-byte hash is opaque to the substrate.
    Custom { reason_hash: [u8; 32] },
}

impl DeathCertificate {
    /// Compute the BLAKE3 hash of this certificate (the value bound into
    /// [`CellLifecycle::Destroyed`]).
    pub fn certificate_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-cell:death-certificate v1");
        hasher.update(self.cell_id.as_bytes());
        hasher.update(&self.last_receipt_hash);
        hasher.update(&self.final_state_commitment);
        hasher.update(&self.destroyed_at_height.to_le_bytes());
        match &self.reason {
            DeathReason::Voluntary => hasher.update(&[0u8]),
            DeathReason::Forced => hasher.update(&[1u8]),
            DeathReason::Migrated => hasher.update(&[2u8]),
            DeathReason::Custom { reason_hash } => {
                hasher.update(&[3u8]);
                hasher.update(reason_hash)
            }
        };
        *hasher.finalize().as_bytes()
    }
}

/// A receipt-chain archival attestation. Per
/// `PROTOCOL-CATEGORICAL-ANALYSIS.md §4.2`.
///
/// Lives alongside [`CellLifecycle::Archived`] in the cell's lifecycle
/// state. Verifiers reconstructing the chain see a single chain link
/// `previous_receipt_hash == archive_terminal_receipt_hash`; the prior
/// history is summarized by `archive_blob_hash`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArchivalAttestation {
    /// The cell whose chain prefix is archived.
    pub cell_id: CellId,
    /// First chain-height included in the archive (inclusive).
    pub archive_start_height: u64,
    /// Last chain-height included in the archive (inclusive). This is
    /// the value mirrored into [`CellLifecycle::Archived::archived_through`].
    pub archive_end_height: u64,
    /// BLAKE3 hash of the off-chain archival blob (the serialized chain
    /// prefix). Verifiers consult off-chain storage with this hash.
    pub archive_blob_hash: [u8; 32],
    /// State commitment at `archive_end_height` (post-state of the last
    /// receipt in the archived prefix).
    pub archive_terminal_commitment: [u8; 32],
    /// Receipt hash at `archive_end_height` — the live chain's
    /// `previous_receipt_hash` at `archive_end_height + 1` matches this.
    pub archive_terminal_receipt_hash: [u8; 32],
}

impl ArchivalAttestation {
    /// Compute the canonical hash of this attestation. The 32-byte output
    /// is what gets folded into [`CellLifecycle::Archived::checkpoint_hash`].
    pub fn checkpoint_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-cell:archival-attestation v1");
        hasher.update(self.cell_id.as_bytes());
        hasher.update(&self.archive_start_height.to_le_bytes());
        hasher.update(&self.archive_end_height.to_le_bytes());
        hasher.update(&self.archive_blob_hash);
        hasher.update(&self.archive_terminal_commitment);
        hasher.update(&self.archive_terminal_receipt_hash);
        *hasher.finalize().as_bytes()
    }

    /// Validate basic structural invariants: `start ≤ end`, all hashes
    /// non-zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.archive_start_height > self.archive_end_height {
            return Err("archive_start_height > archive_end_height");
        }
        if self.archive_blob_hash == [0u8; 32] {
            return Err("archive_blob_hash is zero");
        }
        if self.archive_terminal_receipt_hash == [0u8; 32] {
            return Err("archive_terminal_receipt_hash is zero");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    #[test]
    fn live_default() {
        let lc = CellLifecycle::default();
        assert!(matches!(lc, CellLifecycle::Live));
        assert!(lc.accepts_effects());
        assert!(!lc.is_terminal());
        assert!(!lc.is_sealed());
        assert!(!lc.is_destroyed());
    }

    #[test]
    fn sealed_rejects_effects_but_reversible() {
        let lc = CellLifecycle::Sealed {
            reason_hash: [9u8; 32],
            sealed_at: 100,
        };
        assert!(!lc.accepts_effects());
        assert!(!lc.is_terminal());
        assert!(lc.is_sealed());
    }

    #[test]
    fn destroyed_is_terminal_and_rejects() {
        let lc = CellLifecycle::Destroyed {
            death_certificate_hash: [7u8; 32],
            destroyed_at: 200,
        };
        assert!(!lc.accepts_effects());
        assert!(lc.is_terminal());
        assert!(lc.is_destroyed());
    }

    #[test]
    fn migrated_is_terminal() {
        let lc = CellLifecycle::Migrated {
            to: cid(1),
            attestation: [5u8; 32],
            migrated_at: 300,
        };
        assert!(!lc.accepts_effects());
        assert!(lc.is_terminal());
    }

    #[test]
    fn archived_still_accepts_effects() {
        let lc = CellLifecycle::Archived {
            checkpoint_hash: [3u8; 32],
            archived_through: 50,
        };
        assert!(lc.accepts_effects());
        assert!(!lc.is_terminal());
    }

    #[test]
    fn discriminants_are_distinct() {
        use std::collections::HashSet;
        let variants = vec![
            CellLifecycle::Live,
            CellLifecycle::Sealed {
                reason_hash: [0u8; 32],
                sealed_at: 0,
            },
            CellLifecycle::Migrated {
                to: cid(1),
                attestation: [0u8; 32],
                migrated_at: 0,
            },
            CellLifecycle::Destroyed {
                death_certificate_hash: [0u8; 32],
                destroyed_at: 0,
            },
            CellLifecycle::Archived {
                checkpoint_hash: [0u8; 32],
                archived_through: 0,
            },
        ];
        let discrs: HashSet<u8> = variants.iter().map(|v| v.discriminant()).collect();
        assert_eq!(discrs.len(), 5);
    }

    #[test]
    fn death_certificate_hash_is_deterministic() {
        let dc = DeathCertificate {
            cell_id: cid(2),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: [2u8; 32],
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        let a = dc.certificate_hash();
        let b = dc.certificate_hash();
        assert_eq!(a, b);
    }

    /// Adversarial: any field change must change the hash.
    #[test]
    fn death_certificate_hash_binds_every_field() {
        let base = DeathCertificate {
            cell_id: cid(2),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: [2u8; 32],
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        let h_base = base.certificate_hash();

        let mut c = base.clone();
        c.cell_id = cid(99);
        assert_ne!(c.certificate_hash(), h_base, "cell_id must bind");

        let mut c = base.clone();
        c.last_receipt_hash = [9u8; 32];
        assert_ne!(c.certificate_hash(), h_base, "last_receipt_hash must bind");

        let mut c = base.clone();
        c.final_state_commitment = [9u8; 32];
        assert_ne!(c.certificate_hash(), h_base, "final_state_commitment must bind");

        let mut c = base.clone();
        c.destroyed_at_height = 43;
        assert_ne!(c.certificate_hash(), h_base, "destroyed_at_height must bind");

        let mut c = base.clone();
        c.reason = DeathReason::Forced;
        assert_ne!(c.certificate_hash(), h_base, "reason discriminant must bind");

        // Custom-reason inner hash must bind.
        let custom_a = DeathReason::Custom {
            reason_hash: [1u8; 32],
        };
        let custom_b = DeathReason::Custom {
            reason_hash: [2u8; 32],
        };
        let mut ca = base.clone();
        ca.reason = custom_a;
        let mut cb = base.clone();
        cb.reason = custom_b;
        assert_ne!(
            ca.certificate_hash(),
            cb.certificate_hash(),
            "custom reason_hash must bind"
        );
    }

    #[test]
    fn archival_validate_rejects_inverted_range() {
        let a = ArchivalAttestation {
            cell_id: cid(1),
            archive_start_height: 100,
            archive_end_height: 50,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert!(a.validate().is_err());
    }

    #[test]
    fn archival_validate_rejects_zero_blob() {
        let a = ArchivalAttestation {
            cell_id: cid(1),
            archive_start_height: 0,
            archive_end_height: 10,
            archive_blob_hash: [0u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert!(a.validate().is_err());
    }

    #[test]
    fn archival_validate_rejects_zero_terminal_receipt() {
        let a = ArchivalAttestation {
            cell_id: cid(1),
            archive_start_height: 0,
            archive_end_height: 10,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [0u8; 32],
        };
        assert!(a.validate().is_err());
    }

    #[test]
    fn archival_checkpoint_hash_binds_every_field() {
        let base = ArchivalAttestation {
            cell_id: cid(1),
            archive_start_height: 0,
            archive_end_height: 10,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        let h = base.checkpoint_hash();

        let mut x = base.clone();
        x.archive_start_height = 1;
        assert_ne!(x.checkpoint_hash(), h);

        let mut x = base.clone();
        x.archive_end_height = 11;
        assert_ne!(x.checkpoint_hash(), h);

        let mut x = base.clone();
        x.archive_blob_hash = [9u8; 32];
        assert_ne!(x.checkpoint_hash(), h);

        let mut x = base.clone();
        x.archive_terminal_commitment = [9u8; 32];
        assert_ne!(x.checkpoint_hash(), h);

        let mut x = base.clone();
        x.archive_terminal_receipt_hash = [9u8; 32];
        assert_ne!(x.checkpoint_hash(), h);

        let mut x = base.clone();
        x.cell_id = cid(99);
        assert_ne!(x.checkpoint_hash(), h);
    }
}
