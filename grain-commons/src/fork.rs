//! **Fork-with-pedigree** — fork an installed grain, keep the lineage (docs/THE-GRAIN.md
//! face #2, §Commons).
//!
//! Forking a grain restores its committed `/var` image into a *fresh* grain under a new
//! owner, and starts a **new receipt chain rooted at the fork point**. What makes it a
//! fork and not a copy is **provenance**: a [`Pedigree`] is a Merkle path recording
//! *which `.spk` (which author)* the lineage descends from and *which fork points* it
//! passed through.
//!
//! ## Why the pedigree is trustworthy (and where its trust comes from)
//!
//! A [`Pedigree`] is a plain struct with public fields — on its own it asserts nothing.
//! Its trust is entirely *derived* from the two real facts [`fork_from_package`] binds it
//! to at the moment it is minted:
//!
//! 1. **The author is a signature-verified App ID.** [`fork_from_package`] only ever
//!    stamps `pedigree.author = pkg.app_id`, and a [`GrainPackage`] is obtained *only*
//!    from [`crate::package::install`], which verifies the `.spk`'s Ed25519 signature
//!    before it returns. So the author anchor is an app whose signature was checked — not
//!    a self-asserted label.
//! 2. **The backup provably belongs to that app.** The fork refuses unless the backup's
//!    `app_id` equals the package's signature-verified App ID
//!    ([`ForkError::ProvenanceMismatch`]), and [`sandstorm_bridge::grain::restore_grain`]
//!    re-witnesses that the reconstructed `/var` commits to the backup's `data_root`
//!    (a corrupt/tampered image is refused,
//!    [`sandstorm_bridge::grain::GrainError::BackupCorrupt`]). So the fork point is
//!    anchored at a *real committed root* of the *claimed* app, not an unrelated image.
//! 3. **The backup carries a valid owner signature (the decisive, third tooth).** A fork
//!    supplies the *expected owner key* of the source grain, and
//!    [`sandstorm_bridge::grain::restore_grain`] verifies the backup's ed25519
//!    attestation over `(app_id ‖ data_root)` against it
//!    ([`sandstorm_bridge::grain::GrainError::BadBackupSignature`]). Unlike the public
//!    `app_id`/`data_root` fields — both satisfiable by a hand-crafted backup — the
//!    signature cannot be forged without the owner's key. So a backup that *claims* a
//!    famous app it never came from has no valid signature and the fork is refused.
//!
//! Without those three checks a fork could stamp any (famous) author onto arbitrary state.
//! The pedigree invents no crypto of its own: [`Pedigree::provenance_root`] is a thin
//! blake3 fold *over* the verified App ID, the `.spk` content hash, and the real
//! content-addressed `data_root` chain — so a forged backup yields a different root.
//!
//! ## The two fork layers (this one, and `grain-fork`'s)
//!
//! The grain family has TWO fork surfaces on purpose, at different layers:
//!
//! * **This module** forks the *hosting image*: the `/var` backup (sandstorm-bridge's
//!   content-addressed heap) restored under a new owner, with the **pedigree** —
//!   who authored it, whose grain it descended from, at which committed root.
//!   Provenance across OWNERS.
//! * **`grain-fork`** (its own detached crate) forks the *committed kernel mind*: a
//!   real `dregg_cell::Cell` heap under a `hosted-lease::HostedLease`, with
//!   rewind and the PROVEN settlement-sound branch-and-stitch. Divergence and
//!   merge of STATE, conservation of value/authority.
//!
//! They are not duplicates — pedigree answers "where did this agent come from",
//! stitch answers "how do two divergent minds re-merge soundly". The named weld
//! (once the detached crates join one workspace) is to make the backup's
//! `data_root` BE the mind's committed checkpoint root, so a pedigree fork point
//! and a `grain-fork` ancestor root are the same 32 bytes.
//!
//! ## The trust boundary is CLOSED (was a residual; now the third tooth)
//!
//! `GrainBackup::app_id` is a plain field, so on its own it is not cryptographically tied
//! to the backed-up image. What ties it now is the OWNER ATTESTATION: a backup is signed
//! by its grain's owner over `(app_id ‖ data_root)`, and every fork path verifies that
//! signature against the *expected* owner key it is handed
//! ([`fork_from_package`]'s `expected_owner`; [`ForkedGrain::fork`] re-signs with the
//! grain's own owner key and verifies against its pubkey). The three teeth compose:
//! `app_id == pkg.app_id` (this backup agrees with itself), the `data_root` re-witness
//! (the image is internally consistent), and the signature (the backup provably came from
//! the expected owner's grain of that app). A *hand-crafted* backup whose `app_id` is set
//! to a famous app but whose bytes never passed that app has no valid owner signature and
//! is refused — the launder the earlier residual boundary named is now defeated.

use ed25519_dalek::{SigningKey, VerifyingKey};
use sandstorm_bridge::grain::{restore_grain, GrainBackup, GrainCell, GrainError};
use sandstorm_bridge::manifest::AppId;
use sandstorm_bridge::{GrainReceipt, Umem};
use serde::{Deserialize, Serialize};

use crate::package::GrainPackage;

/// One fork in an agent's lineage — the parent's committed state at the moment of the
/// fork, who forked it, and the child cell that resulted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForkPoint {
    /// The parent grain's committed `/var` `data_root` at the instant of the fork — the
    /// content-addressed point the child descends from (a Merkle anchor, not a label).
    pub parent_data_root: String,
    /// Who performed the fork (the new owner of the child).
    pub forker: String,
    /// The child grain cell the fork produced.
    pub child_cell_id: String,
}

/// An agent's **pedigree** — a Merkle path from the author's `.spk` through every fork.
/// The root anchor is the author's App ID (their signing key) and the `.spk` content
/// hash, then each [`ForkPoint`] extends the path with a real committed `data_root`.
///
/// This is a plain data record: its fields are public and it asserts nothing on its own.
/// Its provenance is only as trustworthy as the values [`fork_from_package`] binds into
/// it — a signature-verified author App ID plus a re-witnessed committed root (see the
/// module docs). Do not treat a hand-built [`Pedigree`] as authenticated.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pedigree {
    /// The App ID (author signing key) the lineage descends from — the provenance root.
    pub author: AppId,
    /// The content hash of the author's `.spk` the lineage started from.
    pub spk_hash: [u8; 32],
    /// The ordered fork points, oldest first. Empty = a freshly installed (unforked) grain.
    pub fork_points: Vec<ForkPoint>,
}

impl Pedigree {
    /// The pedigree at genesis: an installed package, not yet forked.
    pub fn genesis(author: AppId, spk_hash: [u8; 32]) -> Self {
        Pedigree {
            author,
            spk_hash,
            fork_points: Vec::new(),
        }
    }

    /// How many forks deep this lineage is (0 = the original install).
    pub fn depth(&self) -> usize {
        self.fork_points.len()
    }

    /// Whether this lineage descends from `author`. This is a bare field comparison and
    /// is only meaningful because [`fork_from_package`] refuses to stamp an author the
    /// fork does not genuinely descend from (a signature-verified App ID whose committed
    /// backup the fork actually carries). It is *not* a proof against a hand-built
    /// [`Pedigree`] — see the module docs' residual trust boundary.
    pub fn traces_to(&self, author: &AppId) -> bool {
        &self.author == author
    }

    /// The **provenance root** — a blake3 fold over the author anchor, the `.spk` content
    /// hash, and every fork point (each carrying the parent's real committed `data_root`),
    /// in order. Because each fork point's `parent_data_root` is a content commitment that
    /// [`restore_grain`] re-witnessed against the reconstructed `/var`, a forged backup
    /// (different bytes → different `data_root`) yields a different root. Change any
    /// anchor, edit any committed root, or reorder any fork and the root changes.
    pub fn provenance_root(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("grain-commons-pedigree-v1");
        h.update(self.author.0.as_bytes());
        h.update(&self.spk_hash);
        for fp in &self.fork_points {
            h.update(&(fp.parent_data_root.len() as u64).to_le_bytes());
            h.update(fp.parent_data_root.as_bytes());
            h.update(&(fp.forker.len() as u64).to_le_bytes());
            h.update(fp.forker.as_bytes());
            h.update(&(fp.child_cell_id.len() as u64).to_le_bytes());
            h.update(fp.child_cell_id.as_bytes());
        }
        *h.finalize().as_bytes()
    }
}

/// A forked grain: the fresh cell + its restored `/var`, its [`Pedigree`], and the new
/// receipt chain rooted at the fork point.
#[derive(Clone, Debug)]
pub struct ForkedGrain {
    /// The fresh grain cell (owned by the forker, in the `Sleeping` state, ready to wake).
    pub cell: GrainCell,
    /// The restored `/var` umem heap — byte-identical to the parent at the fork point.
    pub var: Umem,
    /// The lineage back to the author.
    pub pedigree: Pedigree,
    /// The child's receipt chain, rooted at the fork-point restore receipt.
    pub receipts: Vec<GrainReceipt>,
    /// **The new owner's ed25519 signing key** — the crypto identity of `cell.owner`,
    /// held so this grain can *attest its own backup* when it is forked again
    /// ([`ForkedGrain::fork`] signs the child's fork-point backup with this key and
    /// verifies the restore against its pubkey). Not public: it is a secret the forked
    /// grain holds, not part of the pedigree record. Threaded in at the fork site
    /// ([`fork_from_package`]'s `forker_signer`, or the previous fork's `new_owner_signer`).
    owner_key: SigningKey,
}

/// Why a fork was refused.
#[derive(Debug)]
pub enum ForkError {
    /// The image restore failed — a corrupt/tampered backup, or an illegal state
    /// (wraps [`GrainError`]; a fork can only descend from a genuine committed state).
    Restore(GrainError),
    /// The backup does not belong to the package the fork claims descent from: the
    /// backup's `app_id` disagrees with the package's signature-verified App ID. A fork
    /// may only root its pedigree at an author whose committed image it actually carries
    /// — this refuses stamping a (famous) author onto an unrelated backup's state.
    ProvenanceMismatch { claimed: AppId, backup: AppId },
}

impl std::fmt::Display for ForkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ForkError::Restore(e) => write!(f, "fork refused: {e}"),
            ForkError::ProvenanceMismatch { claimed, backup } => write!(
                f,
                "fork refused: backup app id {} does not match the claimed package author {}",
                backup.0, claimed.0
            ),
        }
    }
}
impl std::error::Error for ForkError {}

impl From<GrainError> for ForkError {
    fn from(e: GrainError) -> Self {
        ForkError::Restore(e)
    }
}

/// **Fork from an installed package** — the FIRST fork of a lineage. Restores `backup`
/// (a committed image of a running grain of `pkg`) into a fresh grain owned by `forker`,
/// rooting the [`Pedigree`] at the package author.
///
/// The restore is gated by all three pedigree teeth: `backup.app_id == pkg.app_id`, the
/// `data_root` re-witness, and — decisively — the backup's OWNER SIGNATURE. `expected_owner`
/// is the ed25519 public key the caller trusts to have produced this backup (out-of-band
/// knowledge of who owns the *source* grain, e.g. the source owner's registered identity
/// key). [`restore_grain`] verifies the backup's attestation over `(app_id ‖ data_root)`
/// against it, so a hand-crafted or wrong-key backup is refused
/// ([`GrainError::BadBackupSignature`], surfaced as [`ForkError::Restore`]).
///
/// `forker` names the new owner (the pedigree label + the child cell's owner); `forker_signer`
/// is that new owner's ed25519 signing key, held by the returned [`ForkedGrain`] so it can
/// attest its own backup if it is forked onward ([`ForkedGrain::fork`]). In a real deployment
/// `forker_signer` is the forker's registered identity key; here it is threaded in explicitly.
pub fn fork_from_package(
    pkg: &GrainPackage,
    backup: &GrainBackup,
    forker: impl Into<String>,
    forker_signer: &SigningKey,
    new_cell_id: impl Into<String>,
    expected_owner: &VerifyingKey,
) -> Result<ForkedGrain, ForkError> {
    // **Provenance binding.** `pkg.app_id` is signature-verified (it comes only from
    // `install`, which checks the `.spk` Ed25519 signature before returning). We stamp it
    // as the pedigree author — so we must refuse unless the backup we are about to root
    // the lineage on actually belongs to that same app. Without this, a fork could claim
    // descent from any author while carrying an unrelated backup's state, and
    // `traces_to(that author)` would return true.
    if backup.app_id != pkg.app_id {
        return Err(ForkError::ProvenanceMismatch {
            claimed: pkg.app_id.clone(),
            backup: backup.app_id.clone(),
        });
    }
    let forker = forker.into();
    let new_cell_id = new_cell_id.into();
    // The restore verifies the owner attestation against `expected_owner` (third tooth) and
    // re-witnesses the `data_root` — a forged/tampered/wrong-key backup never reaches a
    // pedigree stamp.
    let (cell, var, receipt) = restore_grain(
        backup,
        new_cell_id.clone(),
        forker.clone(),
        pkg.grain_spec(),
        expected_owner,
    )?;
    let pedigree = Pedigree {
        author: pkg.app_id.clone(),
        spk_hash: pkg.spk_hash,
        fork_points: vec![ForkPoint {
            parent_data_root: backup.data_root.clone(),
            forker,
            child_cell_id: new_cell_id,
        }],
    };
    Ok(ForkedGrain {
        cell,
        var,
        pedigree,
        receipts: vec![receipt],
        owner_key: forker_signer.clone(),
    })
}

impl ForkedGrain {
    /// **Fork this grain again** — extend the lineage. Backs up the current `/var` (a
    /// genuine committed image via [`GrainCell::backup`], signed with THIS grain's own
    /// owner key), restores it into a fresh grain owned by `new_owner`, and appends a
    /// [`ForkPoint`] anchored at the current `data_root`. The provenance still traces to
    /// the original author (the root anchor is preserved), one fork deeper.
    ///
    /// The backup is attested by the current owner (`self.owner_key`), and the restore
    /// verifies that attestation against the current owner's pubkey — so the third
    /// (signature) tooth threads through onward forks too, without any out-of-band key:
    /// the grain signs its own backup and checks its own signature. `new_owner_signer` is
    /// the *child's* owner key, carried into the returned [`ForkedGrain`] so it in turn can
    /// attest its own backup when forked further.
    pub fn fork(
        &self,
        new_owner: impl Into<String>,
        new_owner_signer: &SigningKey,
        new_cell_id: impl Into<String>,
    ) -> Result<ForkedGrain, ForkError> {
        let new_owner = new_owner.into();
        let new_cell_id = new_cell_id.into();
        // The current owner backs up the committed image (cap-gated, re-witnessable), signed
        // with this grain's own owner key so the backup carries a valid owner attestation.
        let (backup, _bk) = self
            .cell
            .backup(&self.cell.owner, &self.owner_key, &self.var)?;
        // Keep the lineage honest: the freshly-taken backup must carry the same app as
        // the author anchor this pedigree already descends from. In the genuine flow the
        // restored cell's spec app id is the author's, so this always holds; enforcing it
        // means an extended pedigree can never drift onto a different app.
        if backup.app_id != self.pedigree.author {
            return Err(ForkError::ProvenanceMismatch {
                claimed: self.pedigree.author.clone(),
                backup: backup.app_id.clone(),
            });
        }
        // Restore verifies the just-made attestation against the current owner's pubkey
        // (the key that signed it) — the signature tooth, self-checked on the onward fork.
        let (cell, var, receipt) = restore_grain(
            &backup,
            new_cell_id.clone(),
            new_owner.clone(),
            self.cell.spec.clone(),
            &self.owner_key.verifying_key(),
        )?;
        let mut pedigree = self.pedigree.clone();
        pedigree.fork_points.push(ForkPoint {
            parent_data_root: backup.data_root.clone(),
            forker: new_owner,
            child_cell_id: new_cell_id,
        });
        Ok(ForkedGrain {
            cell,
            var,
            pedigree,
            receipts: vec![receipt],
            owner_key: new_owner_signer.clone(),
        })
    }

    /// The most recent fork point (where this grain split from its parent).
    pub fn fork_point(&self) -> Option<&ForkPoint> {
        self.pedigree.fork_points.last()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::package::{publish, AgentBudget, AgentConfig, BrainChoice};
    use ed25519_dalek::SigningKey;

    /// A deterministic ed25519 key from a seed (owners' identity keys in these tests).
    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// alice (the source grain's owner) — the key her backups are attested with, and the
    /// key a fork of her backup must be verified against.
    fn alice_key() -> SigningKey {
        key(101)
    }

    /// A running grain of a published package, plus a committed backup of its `/var`,
    /// signed by the grain owner (alice). Callers verify against [`alice_key`]'s pubkey.
    fn published_grain_with_backup() -> (GrainPackage, GrainBackup) {
        let cfg = AgentConfig::new(
            "Assistant",
            ["web.fetch"],
            AgentBudget {
                max_spend: 100,
                max_tool_calls: 10,
            },
            BrainChoice::Replay,
        );
        let spk = publish(&cfg, &SigningKey::from_bytes(&[7u8; 32])).unwrap();
        let pkg = crate::package::install(&spk).unwrap();

        // A running grain accrues some `/var` state, then is backed up (owner-attested).
        let mut var = Umem::new();
        var.put("memory/goal", b"summarize the docs".to_vec());
        var.put("memory/step", b"3".to_vec());
        let grain = GrainCell::create("cell:orig", "user:alice", pkg.grain_spec());
        let (backup, _receipt) = grain.backup("user:alice", &alice_key(), &var).unwrap();
        (pkg, backup)
    }

    #[test]
    fn fork_preserves_pedigree_author_and_fork_point() {
        let (pkg, backup) = published_grain_with_backup();
        let forked = fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        )
        .unwrap();

        // Provenance traces to the author (the .spk signing key).
        assert!(forked.pedigree.traces_to(&pkg.app_id));
        assert_eq!(forked.pedigree.spk_hash, pkg.spk_hash);
        // The fork point is anchored at the exact committed state it descended from.
        let fp = forked.fork_point().unwrap();
        assert_eq!(fp.parent_data_root, backup.data_root);
        assert_eq!(fp.forker, "user:bob");
        // The child's /var is byte-identical to the parent at the fork point.
        assert_eq!(
            forked.var.get("memory/goal"),
            Some(&b"summarize the docs"[..])
        );
        assert_eq!(forked.var.commit().0, backup.data_root);
        // A fresh receipt chain, rooted at the fork-point restore.
        assert_eq!(forked.receipts.len(), 1);
        assert_eq!(forked.receipts[0].op, "restore");
        assert_eq!(forked.pedigree.depth(), 1);
    }

    #[test]
    fn a_second_fork_extends_the_path_and_still_traces_to_the_author() {
        let (pkg, backup) = published_grain_with_backup();
        let first = fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        )
        .unwrap();
        let root1 = first.pedigree.provenance_root();

        // Bob forks his fork to Carol. The onward fork re-signs with bob's own owner key
        // (carried in `first`) and hands carol her key for any further fork.
        let second = first.fork("user:carol", &key(103), "cell:fork2").unwrap();
        // Depth grew; the author anchor is preserved at the root of the path.
        assert_eq!(second.pedigree.depth(), 2);
        assert!(second.pedigree.traces_to(&pkg.app_id));
        // The lineage runs alice's data_root → bob's fork → carol's fork.
        assert_eq!(second.pedigree.fork_points[0].forker, "user:bob");
        assert_eq!(second.pedigree.fork_points[1].forker, "user:carol");
        // Extending the path changed the provenance root (a Merkle-path commitment).
        assert_ne!(second.pedigree.provenance_root(), root1);
        // The state still carried through both forks.
        assert_eq!(second.var.get("memory/step"), Some(&b"3"[..]));
    }

    #[test]
    fn provenance_root_is_deterministic_and_binds_the_author() {
        let (pkg, backup) = published_grain_with_backup();
        let a = fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        )
        .unwrap();
        let b = fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        )
        .unwrap();
        // Same lineage → same provenance root.
        assert_eq!(a.pedigree.provenance_root(), b.pedigree.provenance_root());
        // A different author anchor → a different root (provenance is bound in).
        let mut tampered = a.pedigree.clone();
        tampered.author = AppId("someone-else".into());
        assert_ne!(tampered.provenance_root(), a.pedigree.provenance_root());
    }

    /// A backup of a **different** app cannot be laundered into a fork claiming descent
    /// from an unrelated (e.g. famous) author. This is the forgery the adversarial review
    /// found: `fork_from_package(&pkg_A, &backup_of_B, ...)` used to stamp
    /// `pedigree.author = pkg_A.app_id` onto app B's state, and `traces_to(pkg_A.app_id)`
    /// returned true. It is now refused.
    #[test]
    fn a_fork_cannot_claim_an_author_its_backup_does_not_belong_to() {
        // A genuine package + committed backup of app A (signed by key 7).
        let (pkg_a, _backup_a) = published_grain_with_backup();

        // A committed backup of a DIFFERENT, unrelated app B (signed by key 42). This is
        // a perfectly genuine, re-witnessable backup — it just belongs to B, not A.
        let cfg_b = AgentConfig::new(
            "Evil",
            ["web.fetch"],
            AgentBudget {
                max_spend: 100,
                max_tool_calls: 10,
            },
            BrainChoice::Replay,
        );
        let spk_b = publish(&cfg_b, &SigningKey::from_bytes(&[42u8; 32])).unwrap();
        let pkg_b = crate::package::install(&spk_b).unwrap();
        assert_ne!(pkg_a.app_id, pkg_b.app_id);
        let mut var_b = Umem::new();
        var_b.put("memory/secret", b"B's private state".to_vec());
        let mallory = key(200);
        let grain_b = GrainCell::create("cell:b", "user:mallory", pkg_b.grain_spec());
        let (backup_b, _r) = grain_b.backup("user:mallory", &mallory, &var_b).unwrap();

        // Try to launder B's backup into a fork claiming descent from famous author A. The
        // backup is a perfectly genuine, correctly-signed backup of B — it just isn't A's;
        // the app-id provenance check refuses it before the restore even runs.
        match fork_from_package(
            &pkg_a,
            &backup_b,
            "user:mallory",
            &mallory,
            "cell:forgery",
            &mallory.verifying_key(),
        ) {
            Err(ForkError::ProvenanceMismatch { claimed, backup }) => {
                assert_eq!(claimed, pkg_a.app_id);
                assert_eq!(backup, pkg_b.app_id);
            }
            other => panic!("forged pedigree was NOT refused: {other:?}"),
        }
    }

    /// The dual of the refusal: a hand-crafted [`Pedigree`] can *assert* any author, but
    /// that assertion is worthless unless it was minted by `fork_from_package` off a
    /// verified package. This documents the trust boundary — `traces_to` is only a bare
    /// comparison; the authentication lives at the mint site's refusal above.
    #[test]
    fn a_hand_built_pedigree_is_not_authenticated_by_traces_to() {
        let famous = AppId("famous-author-app-id".into());
        // Anyone can construct this struct; nothing here checked a signature.
        let forged = Pedigree::genesis(famous.clone(), [0u8; 32]);
        // traces_to returns true — precisely why it must never be the sole check, and why
        // the real gate is fork_from_package refusing to MINT such a pedigree.
        assert!(forged.traces_to(&famous));
    }

    #[test]
    fn a_tampered_backup_cannot_be_forked() {
        let (pkg, mut backup) = published_grain_with_backup();
        // Inject an entry after the backup — its committed root no longer matches. The
        // recorded `data_root` (and thus the owner attestation over it) is unchanged, so
        // the signature tooth still passes; the `data_root` re-witness catches the injection.
        backup
            .var
            .push(("memory/evil".into(), b"injected".to_vec()));
        match fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        ) {
            Err(ForkError::Restore(GrainError::BackupCorrupt)) => {}
            other => panic!("tampered backup was forked: {other:?}"),
        }
    }

    /// The third (signature) tooth threads through the fork layer: a genuine, correctly
    /// app-id'd backup still cannot be forked if it is verified against the WRONG expected
    /// owner — the attestation does not verify under a key that did not sign it. This is
    /// the tooth that defeats a hand-crafted backup claiming a famous app: without the real
    /// owner's key there is no valid attestation to present.
    #[test]
    fn a_fork_against_the_wrong_expected_owner_is_refused() {
        let (pkg, backup) = published_grain_with_backup();
        // The restorer expects some OTHER owner's key than the one that actually signed
        // (alice's) — the backup's attestation does not verify under it.
        let wrong_owner = key(199);
        match fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &wrong_owner.verifying_key(),
        ) {
            Err(ForkError::Restore(GrainError::BadBackupSignature)) => {}
            other => panic!("a backup verified against the wrong owner was forked: {other:?}"),
        }
        // Against the RIGHT owner key the same backup forks fine (the tooth is not over-broad).
        assert!(fork_from_package(
            &pkg,
            &backup,
            "user:bob",
            &key(102),
            "cell:fork1",
            &alice_key().verifying_key(),
        )
        .is_ok());
    }
}
