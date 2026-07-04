//! # grain-fork — fork + branch-and-stitch a hosted agent grain's mind.
//!
//! *THE-GRAIN.md face #2, "Forkable — the mind is a umem cell you own", made real
//! on the hosting substrate.*
//!
//! A vendor hosts an agent as an opaque instance you cannot copy, roll back, or
//! branch. A **dregg grain** makes the *object* the source of truth: the mind is a
//! committed [`dregg_cell::Cell`] — its heap is the durable, projectable
//! working-memory image, its c-list is its authority — wrapped by a
//! [`hosted_lease::HostedLease`] (rent + own-obligor economics). Because the mind
//! is a real committed cell, everything proven about cells becomes true of it:
//!
//! * **[`Grain::fork`]** — copy the mind's committed image *at its checkpoint root*
//!   into a child grain under its OWN cap-confined lease. The child's genesis IS the
//!   parent's checkpoint root, so common ancestry is provable (not asserted). The
//!   state copies; **value and authority do not duplicate** — the mind carries no
//!   balance (value lives in the lease, its own obligor), and the child receives only
//!   the caps *deliberately conferred*, each of which the parent must actually hold.
//! * **[`Grain::rewind`]** — restore the mind to an earlier committed root,
//!   **fail-closed** on a boundary mismatch: the reified image must re-derive its
//!   sealed root under the kernel's real sorted-Poseidon2
//!   [`dregg_cell::compute_heap_root`] (the `root_binds_get` discipline), else the
//!   restore is refused and the live mind is left untouched. History is committed
//!   states you re-inhabit, not a transcript.
//! * **[`stitch`]** — merge a child's divergent state back through the PROVEN
//!   field-granular pushout + settlement-sound authority gate. We *consume*
//!   [`starbridge_v2::umem_membrane::stitch_projections`] (the per-address state
//!   pushout — disjoint learnings fold clean; a same-address clash surfaces a
//!   first-class [`UmemConflict`], never a silent last-writer-wins) and
//!   [`starbridge_v2::umem_membrane::settle_umem_stitch`] (the authority gate — a cap
//!   revoked between branch and settlement is LINEAR-DROPPED at the tip). These are
//!   the guts of `ForkMembraneHost::stitch_pair`, the operable shadow of
//!   `Metatheory.SettlementSoundness.stitch_drops_revoked_authority`. We do not
//!   reimplement the theorem — we call it.
//! * **[`Grain::absorb`]** — land a settled stitch, fail-closed three ways: a report
//!   minted for a DIFFERENT mind is refused outright ([`GrainError::ForeignStitch`]),
//!   an unsettled report is refused ([`GrainError::NotSettled`]), and the applied
//!   merge must RE-PROJECT to exactly the reported merged state
//!   ([`GrainError::AbsorbDivergence`]) — staged on a scratch copy, so the live mind
//!   is untouched by any refusal.
//!
//! ## What is proven vs what is composed
//!
//! The *pushout* and the *gate* are the proven pieces (`stitch_projections` /
//! `settle_umem_stitch`, over the `dregg_turn::umem` bridge that is the executable
//! shadow of the Lean `UniversalBridge`). This crate's contribution is the
//! *composition*: welding those onto the hosted grain (lease + committed mind cell)
//! so "fork / rewind / branch-and-stitch a *hosted* agent" is a real, tested API —
//! the collaborative agent no single-tenant vendor can build.
//!
//! ## The orthogonality that makes it sound
//!
//! State and authority are orthogonal, exactly as the proven shape requires. The
//! state pushout folds the mind's learnings (disjoint heap addresses merge; a genuine
//! collision is held fail-closed) REGARDLESS of authority. The authority gate,
//! separately, admits a conferred cap only if it is held at the settlement tip — a
//! cap the parent has since revoked cannot ride a stitch into its real mind.

use std::collections::BTreeMap;

use dregg_cell::{
    compute_fields_root, compute_heap_root, AuthRequired, Cell, CellId, FieldElement,
};
use dregg_turn::umem::{project_cell, UKey, UProjection, UVal};
use hosted_lease::{HostedLease, LeaseError, LeaseTerms, WORKING_BASE};

// The PROVEN stitch machinery — consumed, not reimplemented.
pub use starbridge_v2::umem_membrane::{
    settle_umem_stitch, stitch_projections, ConferredCap, SettledUmemStitch, UmemConflict,
    UmemStitch,
};

/// The heap collection the mind's working memory is laid into (the "EXEC" collection,
/// mirroring the lease's committed-image convention). A learning is a
/// `(MIND_COLL, key) -> value` heap cell; it projects to a `UKey::Heap` address the
/// stitch folds per-address.
pub const MIND_COLL: u32 = 0x0000_E3EC;

/// The lease working-memory key the mind's overflow-**fields** boundary root is
/// written at on every [`Grain::checkpoint`] (the heap root is the checkpoint's
/// digest; this rides in the same committed durable image), so a light client
/// watching the lease cursor sees BOTH state planes advance — a fields-only merge is
/// not invisible.
pub const FIELDS_ROOT_WORKING_KEY: u32 = WORKING_BASE + 0xF1;

/// Why a grain operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrainError {
    /// The hosting lease refused the operation (lapsed, ill-formed terms, a forge
    /// detector biting). Carries the lease's own message.
    Lease(String),
    /// A fork tried to confer a capability the parent does not hold. Authority is
    /// only ever *conferred*, never conjured — a fork cannot mint a cap.
    UnconferrableCap(CellId),
    /// A rewind named a boundary root this grain never committed.
    UnknownCheckpoint(String),
    /// **Fail-closed.** The reified checkpoint image does not re-derive its committed
    /// boundary root (a tampered snapshot) — the restore is refused and the live mind
    /// is left untouched (the `root_binds_get` discipline).
    BoundaryMismatch {
        /// The committed root the image was supposed to reproduce.
        committed: String,
        /// The root the (tampered) image actually folds to.
        recomputed: String,
    },
    /// An absorb was asked to land a stitch that has not settled (a live conflict
    /// remains). Resolve the conflict first.
    NotSettled,
    /// An absorb was handed a [`StitchReport`] minted for a DIFFERENT mind. Absorbing a
    /// foreign report would wipe this mind's planes (every own address reads as
    /// "forgotten" against the foreign merge) and implant the foreign learnings under
    /// this mind's identity — refused outright.
    ForeignStitch {
        /// The mind the report was stitched for.
        report: CellId,
        /// This grain's mind.
        mind: CellId,
    },
    /// **Fail-closed.** Applying the reported merge did not REPRODUCE the reported
    /// merged state (re-projecting the applied mind disagrees with
    /// `report.merged_state`) — the absorb is refused and the live mind is left
    /// untouched. This is the applied-merge ≡ reported-merge fidelity tooth: a report
    /// carrying anything the mind's planes cannot faithfully hold is refused, never
    /// silently part-applied.
    AbsorbDivergence,
}

impl std::fmt::Display for GrainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrainError::Lease(e) => write!(f, "hosting lease refused: {e}"),
            GrainError::UnconferrableCap(id) => write!(
                f,
                "cannot confer a capability the parent does not hold ({}): a fork \
                 mints no authority",
                hex32_id(id)
            ),
            GrainError::UnknownCheckpoint(root) => {
                write!(f, "no committed checkpoint for boundary root {root}")
            }
            GrainError::BoundaryMismatch {
                committed,
                recomputed,
            } => write!(
                f,
                "checkpoint image does not reproduce its committed boundary root \
                 (committed {committed}, recomputed {recomputed}): rewind refused \
                 (fail-closed)"
            ),
            GrainError::NotSettled => write!(
                f,
                "the stitch has a live same-address conflict — resolve it before \
                 absorbing"
            ),
            GrainError::ForeignStitch { report, mind } => write!(
                f,
                "the stitch report was minted for mind {} but this grain's mind is {} \
                 — a foreign report cannot be absorbed",
                hex32_id(report),
                hex32_id(mind)
            ),
            GrainError::AbsorbDivergence => write!(
                f,
                "applying the reported merge did not reproduce the reported merged \
                 state — absorb refused (fail-closed), live mind untouched"
            ),
        }
    }
}

impl std::error::Error for GrainError {}

impl From<LeaseError> for GrainError {
    fn from(e: LeaseError) -> Self {
        GrainError::Lease(format!("{e:?}"))
    }
}

/// One committed checkpoint of the mind: the sealed boundary roots of BOTH state
/// planes (openable heap + overflow fields) and the reified images that produced
/// them. The rewind timeline — a root-addressed history of committed states,
/// re-witnessed before re-inhabiting. Binding the field plane too closes the hole
/// where a fields-only merge (absorbed via the stitch's `Field` plane) was invisible
/// to the timeline and survived a rewind at its later value.
#[derive(Clone, Debug, PartialEq, Eq)]
struct GrainCheckpoint {
    /// The heap boundary root (`compute_heap_root` over `image`) — the grain's
    /// primary identity-of-state.
    root: [u8; 32],
    /// The overflow-fields boundary root (`compute_fields_root` over `fields`).
    fields_root: [u8; 32],
    image: BTreeMap<(u32, u32), FieldElement>,
    fields: BTreeMap<u64, FieldElement>,
}

/// A **grain** — a hosted agent whose mind is a committed, forkable, rewindable,
/// stitchable dregg cell, funded by its own lease.
pub struct Grain {
    /// The mind: a committed cell whose heap is the durable working-memory image
    /// (projected via [`project_cell`] and folded by the stitch) and whose c-list is
    /// its authority. Carries NO balance — value lives in [`Grain::lease`], so a fork
    /// of the mind mints no value.
    mind: Cell,
    /// The economic layer: rent obligor, own-obligor conservation, lapse audit, and a
    /// checkpoint cursor a light client sees advance. Its genesis digest is bound to
    /// the mind's checkpoint root.
    lease: HostedLease,
    /// The root-addressed checkpoint history (the rewind timeline).
    checkpoints: Vec<GrainCheckpoint>,
    /// The parent's mind projection at fork time — the shared-ancestor baseline this
    /// grain stitches against. `None` for a root (unforked) grain.
    baseline: Option<UProjection>,
    /// The fork-point boundary root this grain descends from (`None` for a root grain)
    /// — equal to the parent's checkpoint root AND to this grain's lease genesis
    /// digest (provable common ancestry).
    ancestor_root: Option<[u8; 32]>,
}

impl Grain {
    /// **Rent a fresh root grain.** Mints the mind cell (identity `mind_pk` / `token`,
    /// balance 0 — the mind holds no value), opens the hosting `lease` initialised to
    /// the mind's genesis boundary root, and commits the genesis checkpoint. `funding`
    /// seeds the lease cell's balance (what rent draws from).
    pub fn rent(
        mind_pk: [u8; 32],
        token: [u8; 32],
        terms: LeaseTerms,
        funding: i64,
    ) -> Result<Grain, GrainError> {
        let mut mind = Cell::with_balance(mind_pk, token, 0);
        mind.state.reseal_heap_root();
        mind.state.reseal_fields_root();
        let genesis_root = mind.state.heap_root;

        let lease_cell =
            Cell::with_balance(cell_bytes(terms.lease), cell_bytes(terms.asset), funding);
        let lease = HostedLease::open(lease_cell, terms, genesis_root)?;

        let mut grain = Grain {
            mind,
            lease,
            checkpoints: Vec::new(),
            baseline: None,
            ancestor_root: None,
        };
        grain.log_checkpoint();
        Ok(grain)
    }

    /// The mind's current committed boundary root (its checkpoint root) — the grain's
    /// 32-byte identity-of-state a fork descends from and a rewind returns to.
    pub fn root(&self) -> [u8; 32] {
        self.mind.state.heap_root
    }

    /// The mind's current committed boundary root, hex.
    pub fn root_hex(&self) -> String {
        hex32(&self.mind.state.heap_root)
    }

    /// The fork-point root this grain descends from (`None` for a root grain). Equal to
    /// the parent's checkpoint root at fork time AND to this grain's lease genesis
    /// digest — provable common ancestry.
    pub fn ancestor_root(&self) -> Option<[u8; 32]> {
        self.ancestor_root
    }

    /// The mind's identity cell id (shared across a fork — a fork IS the same mind,
    /// diverging).
    pub fn mind_id(&self) -> CellId {
        self.mind.id()
    }

    /// The mind's economic balance is always zero (value lives in the lease). Exposed
    /// so a caller can witness that a fork mints no value.
    pub fn mind_balance(&self) -> i64 {
        self.mind.state.balance()
    }

    /// The lease cell id (the grain's own obligor). Two grains never share it — a fork
    /// funds its own rent.
    pub fn obligor(&self) -> CellId {
        self.lease.cell().id()
    }

    /// Whether the hosting lease has lapsed (non-payment) — a lapsed grain refuses
    /// further durable delivery.
    pub fn is_lapsed(&self) -> bool {
        self.lease.is_lapsed()
    }

    /// A read-only borrow of the hosting lease (for metering / settlement / witnessing).
    pub fn lease(&self) -> &HostedLease {
        &self.lease
    }

    /// A mutable borrow of the hosting lease (to meter rent, audit lapse, etc.).
    pub fn lease_mut(&mut self) -> &mut HostedLease {
        &mut self.lease
    }

    // ── the mind's learnings (working memory) ───────────────────────────────────────

    /// **Learn** — write `value` at working-memory address `key` (a
    /// `(MIND_COLL, key)` heap cell). Reseals the boundary root; call
    /// [`checkpoint`](Grain::checkpoint) to commit it to the timeline + advance the
    /// lease cursor. This is the per-address divergence a stitch folds.
    pub fn learn(&mut self, key: u32, value: [u8; 32]) {
        self.mind.state.heap_map.insert((MIND_COLL, key), value);
        self.mind.state.reseal_heap_root();
    }

    /// **Forget** — clear working-memory address `key`, reseal.
    pub fn forget(&mut self, key: u32) -> bool {
        let removed = self.mind.state.heap_map.remove(&(MIND_COLL, key)).is_some();
        if removed {
            self.mind.state.reseal_heap_root();
        }
        removed
    }

    /// Read a working-memory value.
    pub fn recall(&self, key: u32) -> Option<[u8; 32]> {
        self.mind.state.heap_map.get(&(MIND_COLL, key)).copied()
    }

    // ── authority (the mind's c-list) ───────────────────────────────────────────────

    /// **Confer authority onto the mind** — grant a capability reaching `target`. The
    /// authority a stitch can carry back into a parent; the thing a settlement gate
    /// checks at the tip.
    pub fn grant(&mut self, target: CellId) {
        self.mind.capabilities.grant(target, AuthRequired::None);
    }

    /// **Revoke** the mind's capability reaching `target` (the one non-monotone op).
    /// After this, a stitch conferring `target` back drops it at the settlement tip.
    /// Returns whether a live cap was revoked.
    pub fn revoke(&mut self, target: CellId) -> bool {
        let slot = self
            .mind
            .capabilities
            .iter()
            .find(|c| c.target == target && c.permissions != AuthRequired::Impossible)
            .map(|c| c.slot);
        match slot {
            Some(s) => self.mind.capabilities.revoke(s),
            None => false,
        }
    }

    /// Whether the mind currently holds a live capability reaching `target`.
    pub fn holds(&self, target: CellId) -> bool {
        self.mind.capabilities.has_access(&target)
    }

    // ── checkpoint / rewind (the umem-cell time-travel discipline) ───────────────────

    /// **Checkpoint** — commit the mind's live state (BOTH planes: openable heap +
    /// overflow fields) to the root-addressed timeline and advance the lease's durable
    /// cursor with the heap root as its digest and the fields root as a committed
    /// working-memory entry ([`FIELDS_ROOT_WORKING_KEY`]) — so a light client sees the
    /// whole mind advance, including a fields-only merge. Idempotent in value:
    /// re-checkpointing an unchanged mind does not bloat the log. Returns the committed
    /// heap boundary root. Refuses fail-closed if the hosting lease has lapsed.
    pub fn checkpoint(&mut self) -> Result<[u8; 32], GrainError> {
        self.mind.state.reseal_heap_root();
        self.mind.state.reseal_fields_root();
        let root = self.mind.state.heap_root;
        let fields_root = self.mind.state.fields_root;
        // Advance the lease's Monotonic cursor with the mind's checkpoint root as the
        // durable digest (the fields root rides in the committed working image) — a
        // lapsed lease refuses (fail-closed).
        self.lease
            .checkpoint(root, &[(FIELDS_ROOT_WORKING_KEY, fields_root)])?;
        self.log_checkpoint();
        Ok(root)
    }

    /// **Rewind** — restore the mind to an earlier committed boundary `root` from this
    /// grain's timeline (the most recent checkpoint committed at that heap root),
    /// **fail-closed**: the reified images must re-derive their committed roots under
    /// the kernel's real `compute_heap_root` / `compute_fields_root`, else the restore
    /// is refused ([`GrainError::BoundaryMismatch`]) and the live mind is left
    /// untouched. A root never committed is refused ([`GrainError::UnknownCheckpoint`]).
    ///
    /// What time-travels: the mind's two STATE planes — the openable heap (all
    /// collections, [`MIND_COLL`] working memory included) and the overflow-fields map.
    /// What does not: identity, the c-list (authority is not state), the fixed kernel
    /// field slots (structural), and the lease's forward (Monotonic) cursor — the mind
    /// re-inhabits a committed state; the durable delivery history stands.
    pub fn rewind(&mut self, root: [u8; 32]) -> Result<(), GrainError> {
        let cp = self
            .checkpoints
            .iter()
            .rev()
            .find(|c| c.root == root)
            .cloned()
            .ok_or_else(|| GrainError::UnknownCheckpoint(hex32(&root)))?;

        // Re-witness BOTH planes: each reified image must fold back to its committed root.
        let recomputed = compute_heap_root(&cp.image);
        if recomputed != cp.root {
            return Err(GrainError::BoundaryMismatch {
                committed: hex32(&cp.root),
                recomputed: hex32(&recomputed),
            });
        }
        let recomputed_fields = compute_fields_root(&cp.fields);
        if recomputed_fields != cp.fields_root {
            return Err(GrainError::BoundaryMismatch {
                committed: hex32(&cp.fields_root),
                recomputed: hex32(&recomputed_fields),
            });
        }

        // Adopt: replace the mind's state planes with the reified images and reseal.
        self.mind.state.heap_map = cp.image.clone();
        self.mind.state.fields_map = cp.fields.clone();
        self.mind.state.reseal_heap_root();
        self.mind.state.reseal_fields_root();
        Ok(())
    }

    /// Every committed boundary root, oldest first (the rewind timeline).
    pub fn checkpoint_roots(&self) -> Vec<[u8; 32]> {
        self.checkpoints.iter().map(|c| c.root).collect()
    }

    // ── fork ─────────────────────────────────────────────────────────────────────────

    /// **Fork** — branch a child grain from this one's committed mind image at its
    /// checkpoint root. The child's mind is a byte-identical copy of the parent's at
    /// birth (same identity, same committed root — it IS the same mind, diverging),
    /// under its OWN cap-confined `child_terms` lease (its own obligor). The child's
    /// lease genesis digest IS the parent's current checkpoint root, so common ancestry
    /// is provable, not asserted.
    ///
    /// **Conservation.** The mind carries no balance, so the copy mints no value; the
    /// child's rent is funded independently (`child_funding` into its own lease cell).
    /// Authority does not duplicate: the child receives ONLY the caps in `confer`, and
    /// each must be a capability the parent actually holds — conferring one the parent
    /// lacks is refused ([`GrainError::UnconferrableCap`]). A fork mints no authority.
    pub fn fork(
        &self,
        child_terms: LeaseTerms,
        child_funding: i64,
        confer: &[CellId],
    ) -> Result<Grain, GrainError> {
        // The fork-point image the child descends from (the parent's committed mind).
        let mut child_mind = self.mind.clone();

        // Authority does NOT duplicate: strip the inherited c-list down to exactly the
        // deliberately-conferred caps, each of which the parent must actually hold.
        for target in confer {
            if !self.holds(*target) {
                return Err(GrainError::UnconferrableCap(*target));
            }
        }
        child_mind.capabilities = dregg_cell::CapabilitySet::new();
        for target in confer {
            child_mind.capabilities.grant(*target, AuthRequired::None);
        }
        child_mind.state.reseal_heap_root();

        let fork_root = self.mind.state.heap_root;

        // The child's OWN lease (own obligor), genesis == the parent's checkpoint root.
        let child_lease_cell = Cell::with_balance(
            cell_bytes(child_terms.lease),
            cell_bytes(child_terms.asset),
            child_funding,
        );
        let child_lease = HostedLease::open(child_lease_cell, child_terms, fork_root)?;

        // The stitch baseline is the parent's mind projection at fork time.
        let baseline = mind_projection(&self.mind);

        Ok(Grain {
            mind: child_mind,
            lease: child_lease,
            checkpoints: vec![GrainCheckpoint {
                root: fork_root,
                fields_root: self.mind.state.fields_root,
                image: self.mind.state.heap_map.clone(),
                fields: self.mind.state.fields_map.clone(),
            }],
            baseline: Some(baseline),
            ancestor_root: Some(fork_root),
        })
    }

    // ── absorb a settled stitch ───────────────────────────────────────────────────────

    /// **Absorb** a settled stitch into this (parent) grain: land the clean-merged mind
    /// state into the live mind and commit a checkpoint. Fail-closed three ways, each
    /// leaving the live mind untouched:
    ///
    /// * [`GrainError::ForeignStitch`] — the report was minted for a different mind
    ///   (absorbing it would wipe this mind's planes and implant foreign learnings
    ///   under this identity).
    /// * [`GrainError::NotSettled`] — a live same-address conflict remains; a collision
    ///   is never silently resolved.
    /// * [`GrainError::AbsorbDivergence`] — the applied merge, staged on a scratch copy
    ///   and RE-PROJECTED, does not reproduce `report.merged_state` exactly (the
    ///   applied-merge ≡ reported-merge fidelity tooth; nothing is ever part-applied).
    ///
    /// Returns the new committed root.
    pub fn absorb(&mut self, report: &StitchReport) -> Result<[u8; 32], GrainError> {
        if report.mind != self.mind.id() {
            return Err(GrainError::ForeignStitch {
                report: report.mind,
                mind: self.mind.id(),
            });
        }
        if !report.settles() {
            return Err(GrainError::NotSettled);
        }
        // Stage the merge on a scratch copy — the live mind is only replaced after the
        // fidelity tooth passes.
        let mut staged = self.mind.clone();
        // The pre-merge state planes. Any address present HERE but ABSENT from the
        // merged result was FORGOTTEN by the merge (a child `forget()` folds a key to
        // absence in the pushout) — it must be REMOVED, not silently left at its stale
        // parent value. Without this, the applied merge diverges from the reported one.
        let pre = mind_projection(&staged);
        for k in pre.keys() {
            if report.merged_state.contains_key(k) {
                continue;
            }
            match k {
                UKey::Heap {
                    collection, key, ..
                } => {
                    staged.state.heap_map.remove(&(*collection, *key));
                }
                // The overflow field map (slot ≥ STATE_SLOTS) is the deletable field
                // plane; fixed slots (< STATE_SLOTS) are structural and never fold to
                // absence, so a bare `remove` on `fields_map` is a safe no-op for them.
                UKey::Field { slot, .. } => {
                    staged.state.fields_map.remove(slot);
                }
                _ => {}
            }
        }
        // Land the clean-merged learnings — BOTH the openable heap AND the field planes.
        // Anything the planes cannot faithfully hold (a non-Bytes32 value, a key of
        // another cell) is NOT silently skipped: it fails the fidelity tooth below.
        for (k, v) in report.merged_state.iter() {
            match (k, v) {
                (
                    UKey::Heap {
                        collection, key, ..
                    },
                    UVal::Bytes32(bytes),
                ) => {
                    staged.state.heap_map.insert((*collection, *key), *bytes);
                }
                (UKey::Field { slot, .. }, UVal::Bytes32(bytes)) => {
                    // `set_field_ext` routes fixed slots to `fields[]` (invalidating a
                    // stale commitment) and overflow keys to `fields_map`.
                    staged.state.set_field_ext(*slot, *bytes);
                }
                _ => {}
            }
        }
        staged.state.reseal_heap_root();
        staged.state.reseal_fields_root();
        // THE FIDELITY TOOTH: re-projecting the applied mind must yield EXACTLY the
        // reported merged state. If not (an unappliable value, a foreign-cell key that
        // re-projects under this identity, any silent skip above), refuse — the live
        // mind was never touched.
        if mind_projection(&staged) != report.merged_state {
            return Err(GrainError::AbsorbDivergence);
        }
        self.mind = staged;
        self.checkpoint()
    }

    /// Convenience: stitch `child` back into `self` (the settlement tip). See [`stitch`].
    pub fn stitch_child(&self, child: &Grain) -> StitchReport {
        stitch(self, child)
    }

    // ── internals ─────────────────────────────────────────────────────────────────────

    /// Append the mind's current committed state to the timeline (deduping an identical
    /// trailing (heap, fields) root PAIR so a stop/stop does not bloat the log — a
    /// fields-only change still logs).
    fn log_checkpoint(&mut self) {
        let root = self.mind.state.heap_root;
        let fields_root = self.mind.state.fields_root;
        if self.checkpoints.last().map(|c| (c.root, c.fields_root)) != Some((root, fields_root)) {
            self.checkpoints.push(GrainCheckpoint {
                root,
                fields_root,
                image: self.mind.state.heap_map.clone(),
                fields: self.mind.state.fields_map.clone(),
            });
        }
    }

    /// TEST-ONLY: corrupt the reified image of the checkpoint at `root` WITHOUT updating
    /// its committed root, so a subsequent [`rewind`](Grain::rewind) must fail closed.
    #[cfg(test)]
    fn tamper_checkpoint(&mut self, root: [u8; 32]) {
        if let Some(cp) = self.checkpoints.iter_mut().find(|c| c.root == root) {
            let mut leaf = [0u8; 32];
            leaf[0] = 0xFF;
            // Insert a bogus leaf the committed root never bound.
            cp.image.insert((MIND_COLL, u32::MAX), leaf);
        }
    }

    /// TEST-ONLY: corrupt the reified FIELDS image of the checkpoint at `root` WITHOUT
    /// updating its committed fields root — the fields-plane rewind must fail closed.
    #[cfg(test)]
    fn tamper_checkpoint_fields(&mut self, root: [u8; 32]) {
        if let Some(cp) = self.checkpoints.iter_mut().find(|c| c.root == root) {
            let mut leaf = [0u8; 32];
            leaf[0] = 0xEE;
            cp.fields.insert(u64::MAX, leaf);
        }
    }
}

/// **The verdict of a grain stitch** — the field-granular state pushout PLUS the
/// settlement-sound authority gate, surfaced as a grain report. Mirrors
/// `BranchStitchSession::StitchVerdict`, built from the PROVEN
/// [`SettledUmemStitch`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StitchReport {
    /// The mind this report was stitched FOR (the parent/settlement-tip mind at stitch
    /// time; a genuine fork pair shares one mind id). [`Grain::absorb`] refuses a
    /// report minted for a different mind ([`GrainError::ForeignStitch`]).
    pub mind: CellId,
    /// The settled merged-mind root — `Some` iff there is no live conflict (fail-closed:
    /// a same-address clash withholds the root until explicitly resolved).
    pub settled_root: Option<[u8; 32]>,
    /// The working-memory addresses that folded CLEAN relative to the baseline — the
    /// child's (and parent's) disjoint learnings, all kept (co-drive, never
    /// last-writer-wins).
    pub merged: Vec<UKey>,
    /// Same-address collisions surfaced as first-class conflict objects (both attributed
    /// readings live). Empty ⟺ a clean merge.
    pub conflicts: Vec<UmemConflict>,
    /// Conferred caps HELD AT THE SETTLEMENT TIP — they ride the stitch into the parent.
    pub admitted_authority: Vec<ConferredCap>,
    /// Conferred caps NOT held at the tip (revoked between branch and settlement) — the
    /// linear DROP. "A cap I have since revoked cannot ride a stitch into my real mind."
    pub dropped_authority: Vec<ConferredCap>,
    /// The full clean-merged mind projection (used by [`Grain::absorb`]).
    merged_state: UProjection,
}

impl StitchReport {
    /// **Does the stitch settle?** Fail-closed: settles only when the state pushout has
    /// no live conflict. Linear-dropped authority does NOT block settlement (a revoked
    /// cap was simply never conferred) — authority and state are orthogonal.
    pub fn settles(&self) -> bool {
        self.conflicts.is_empty()
    }
}

/// **Stitch a child grain's divergent mind back into its parent** under the proven
/// field-granular pushout + settlement-sound authority gate.
///
/// `parent` is the settlement tip (authority is read HERE, after any revocation).
/// `child` carries its fork-point baseline. The state pushout
/// ([`stitch_projections`]) folds each side's disjoint learnings clean and surfaces a
/// same-address clash as a held [`UmemConflict`]; the authority gate
/// ([`settle_umem_stitch`]) admits a conferred cap only if the parent holds it at the
/// tip and LINEAR-DROPS one revoked-before-settlement. The two are orthogonal.
///
/// This is the operable shadow of `SettlementSoundness.stitch_drops_revoked_authority`
/// — consumed from `starbridge_v2::umem_membrane`, not reimplemented here.
pub fn stitch(parent: &Grain, child: &Grain) -> StitchReport {
    // The shared-ancestor baseline: the parent's mind at fork time (falls back to the
    // parent's current projection for an un-forked pair — a no-op baseline).
    let baseline = child
        .baseline
        .clone()
        .unwrap_or_else(|| mind_projection(&parent.mind));
    let a = mind_projection(&parent.mind);
    let b = mind_projection(&child.mind);

    // (1) THE STATE PUSHOUT — proven, field-granular, orthogonal to authority.
    let pushout: UmemStitch = stitch_projections(&baseline, &a, &b);

    // (2) THE CONFERRED AUTHORITY — the caps the child would carry back into the parent.
    let conferred = held_caps(&child.mind);
    // (3) THE SETTLEMENT TIP — the caps the parent holds NOW (after any revocation). The
    // cell-native twin of `settlement_held_at_tip`, feeding the SAME proven gate.
    let settlement_held = held_caps(&parent.mind);

    // (4) THE SETTLEMENT-SOUND GATE — proven; admits held caps, linear-drops revoked ones.
    let settled: SettledUmemStitch = settle_umem_stitch(pushout, &conferred, &settlement_held);

    // (5) SURFACE: the addresses that changed vs the baseline (the folded learnings).
    let merged: Vec<UKey> = settled
        .stitch
        .merged
        .iter()
        .filter(|(k, v)| baseline.get(k) != Some(v))
        .map(|(k, _)| k.clone())
        .collect();

    StitchReport {
        mind: parent.mind_id(),
        settled_root: settled.settled_root(),
        merged,
        conflicts: settled.stitch.conflicts.clone(),
        admitted_authority: settled.admitted.clone(),
        dropped_authority: settled.dropped.clone(),
        merged_state: settled.stitch.merged.clone(),
    }
}

/// Project a mind cell's STATE planes (working-memory heap + fields) into the universal
/// address space via the proven [`project_cell`], keeping only the learnings so the
/// state pushout is orthogonal to the authority (cap) planes handled by the gate.
fn mind_projection(cell: &Cell) -> UProjection {
    let mut full = UProjection::new();
    project_cell(cell, &mut full);
    full.into_iter()
        .filter(|(k, _)| matches!(k, UKey::Heap { .. } | UKey::Field { .. }))
        .collect()
}

/// The live capabilities a cell holds, as the gate's [`ConferredCap`] input — the
/// cell-native reading `settlement_held_at_tip` performs on a `World`. A revoked cap
/// (dropped from the live c-list) is structurally absent, so the gate drops any stitch
/// that tries to confer it.
fn held_caps(cell: &Cell) -> Vec<ConferredCap> {
    let mut caps: Vec<ConferredCap> = Vec::new();
    for cap in cell.capabilities.iter() {
        if cap.permissions == AuthRequired::Impossible {
            continue;
        }
        let cc = ConferredCap {
            target: cap.target,
            debit_reach: true,
        };
        if !caps.contains(&cc) {
            caps.push(cc);
        }
    }
    caps
}

fn cell_bytes(id: CellId) -> [u8; 32] {
    *id.as_bytes()
}

fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

fn hex32_id(id: &CellId) -> String {
    hex32(id.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// provider, lease-cell, asset; rent 100 every 50 blocks from 1000.
    fn terms(lease: u8, asset: u8) -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(lease), cid(asset), 100, 50, 1000, 0)
    }

    fn parent_grain() -> Grain {
        Grain::rent([0xA0; 32], [0x01; 32], terms(7, 9), 1_000_000).expect("rent a root grain")
    }

    /// TOOTH 1 — fork diverges from ONE root: the child is byte-identical at birth
    /// (same committed root, same recall), then a write to the child never touches the
    /// parent, and the two roots diverge.
    #[test]
    fn fork_diverges_from_one_root() {
        let mut parent = parent_grain();
        parent.learn(0, [0x11; 32]);
        parent.checkpoint().unwrap();
        let root0 = parent.root();

        let child = parent
            .fork(terms(70, 9), 1_000_000, &[])
            .expect("fork the grain");

        // Byte-identical at birth: same committed root, same identity, same learning.
        assert_eq!(child.root(), root0, "the fork starts at the parent's root");
        assert_eq!(
            child.ancestor_root(),
            Some(root0),
            "provable common ancestry"
        );
        assert_eq!(child.mind_id(), parent.mind_id(), "a fork IS the same mind");
        assert_eq!(child.recall(0), Some([0x11; 32]));

        // Diverge: the child learns something the parent never sees, and vice-versa.
        let mut child = child;
        child.learn(1, [0xCC; 32]);
        parent.learn(2, [0xDD; 32]);
        assert!(child.recall(1).is_some() && child.recall(2).is_none());
        assert!(parent.recall(2).is_some() && parent.recall(1).is_none());
        assert_ne!(child.root(), parent.root(), "the copies diverged");
    }

    /// TOOTH 2 — fork CONSERVES: no value and no authority are minted. The mind carries
    /// no balance, the child funds its own lease (a distinct obligor), the child holds
    /// only the deliberately-conferred caps, and conferring a cap the parent lacks is
    /// refused.
    #[test]
    fn fork_conserves_value_and_authority() {
        let mut parent = parent_grain();
        let gift = cid(0x91);
        let ungranted = cid(0xEE);
        parent.grant(gift);
        parent.checkpoint().unwrap();

        // Conferring a cap the parent does NOT hold is refused — a fork mints no cap.
        match parent.fork(terms(70, 9), 1_000_000, &[ungranted]) {
            Err(GrainError::UnconferrableCap(t)) => assert_eq!(t, ungranted),
            other => panic!("expected UnconferrableCap refusal, got {:?}", other.is_ok()),
        }

        // A clean fork conferring exactly `gift`.
        let child = parent.fork(terms(70, 9), 500_000, &[gift]).expect("fork");

        // No value minted: the mind holds no balance; the child is its own obligor.
        assert_eq!(child.mind_balance(), 0, "the mind mints no value on fork");
        assert_eq!(parent.mind_balance(), 0);
        assert_ne!(
            child.obligor(),
            parent.obligor(),
            "the child funds its own rent"
        );

        // No authority minted: the child holds ONLY the conferred cap, nothing else.
        assert!(
            child.holds(gift),
            "the deliberately-conferred cap is present"
        );
        assert!(!child.holds(ungranted));
    }

    /// TOOTH 3 — rewind is FAIL-CLOSED: an unknown root is refused, a tampered
    /// checkpoint image (one that no longer folds to its committed root) is refused with
    /// the live mind left untouched, and a genuine root restores.
    #[test]
    fn rewind_is_fail_closed() {
        let mut grain = parent_grain();
        grain.learn(0, [0x01; 32]);
        let r1 = grain.checkpoint().unwrap(); // "yesterday"
        grain.learn(0, [0x02; 32]);
        grain.learn(9, [0x09; 32]);
        grain.checkpoint().unwrap();

        // Unknown root → refused.
        assert!(matches!(
            grain.rewind([0x55; 32]),
            Err(GrainError::UnknownCheckpoint(_))
        ));

        // Tamper r1's reified image WITHOUT updating its committed root → fail closed,
        // live mind untouched.
        grain.tamper_checkpoint(r1);
        let live_before = grain.recall(0);
        assert!(matches!(
            grain.rewind(r1),
            Err(GrainError::BoundaryMismatch { .. })
        ));
        assert_eq!(
            grain.recall(0),
            live_before,
            "live mind untouched on refusal"
        );

        // A genuine (untampered) checkpoint rewinds cleanly.
        let mut grain2 = parent_grain();
        grain2.learn(0, [0xAA; 32]);
        let root_v1 = grain2.checkpoint().unwrap();
        grain2.learn(0, [0xBB; 32]);
        grain2.checkpoint().unwrap();
        grain2.rewind(root_v1).unwrap();
        assert_eq!(
            grain2.recall(0),
            Some([0xAA; 32]),
            "re-inhabited the earlier state"
        );
        assert_eq!(
            grain2.root(),
            root_v1,
            "the mind folds back to the committed root"
        );
    }

    /// TOOTH 4 — stitch merges DISJOINT learnings clean: the child learns at one
    /// address, the parent at another; both fold in, the stitch settles, and absorbing
    /// lands the child's learning in the parent.
    #[test]
    fn stitch_merges_disjoint_learnings() {
        let mut parent = parent_grain();
        parent.learn(0, [0x10; 32]);
        parent.checkpoint().unwrap();

        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");

        // Disjoint learnings: child at address 1, parent at address 2.
        child.learn(1, [0xC1; 32]);
        parent.learn(2, [0xD2; 32]);

        let report = stitch(&parent, &child);
        assert!(
            report.settles(),
            "disjoint learnings settle: {:?}",
            report.conflicts
        );
        assert!(
            report.settled_root.is_some(),
            "a settled stitch has a binding root"
        );
        let addr = |k: u32| UKey::Heap {
            cell: parent.mind_id(),
            collection: MIND_COLL,
            key: k,
        };
        assert!(
            report.merged.contains(&addr(1)),
            "the child's learning folded in"
        );
        assert!(
            report.merged.contains(&addr(2)),
            "the parent's learning folded in"
        );

        // Absorbing lands the child's disjoint learning in the parent's real mind.
        assert_eq!(parent.recall(1), None, "not yet absorbed");
        parent.absorb(&report).unwrap();
        assert_eq!(
            parent.recall(1),
            Some([0xC1; 32]),
            "child's learning absorbed"
        );
        assert_eq!(
            parent.recall(2),
            Some([0xD2; 32]),
            "parent's own learning intact"
        );
    }

    /// TOOTH 5 — a same-address COLLISION surfaces a first-class ConflictObject (both
    /// attributed readings live), does NOT settle (fail-closed), and absorbing is
    /// refused until it is resolved.
    #[test]
    fn same_address_collision_is_a_conflict_object() {
        let mut parent = parent_grain();
        parent.learn(0, [0x00; 32]);
        parent.checkpoint().unwrap();

        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");

        // Both drive the SAME address to DIFFERENT values — the genuine collision.
        parent.learn(5, [0xAA; 32]);
        child.learn(5, [0xBB; 32]);

        let report = stitch(&parent, &child);
        assert!(
            !report.settles(),
            "a same-address clash does NOT settle (fail-closed)"
        );
        assert!(
            report.settled_root.is_none(),
            "no settled root while a conflict is live"
        );

        let addr = UKey::Heap {
            cell: parent.mind_id(),
            collection: MIND_COLL,
            key: 5,
        };
        let conflict = report
            .conflicts
            .iter()
            .find(|c| c.key == addr)
            .expect("the conflict names the EXACT diverged address");
        // Both attributed readings live — the loser is never hidden.
        assert_eq!(
            conflict.a,
            Some(UVal::Bytes32([0xAA; 32])),
            "parent's reading lives"
        );
        assert_eq!(
            conflict.b,
            Some(UVal::Bytes32([0xBB; 32])),
            "child's reading lives"
        );

        // Absorbing an unsettled stitch is refused — never a silent last-writer-wins.
        assert_eq!(parent.absorb(&report), Err(GrainError::NotSettled));
    }

    /// TOOTH — a child DELETION (`forget`) folds to ABSENCE in the pushout and is APPLIED
    /// on absorb: the forgotten key is genuinely GONE from the parent's real mind, not
    /// left at its stale pre-fork value (the reported absorb/merge divergence).
    #[test]
    fn child_deletion_is_applied_to_parent_on_absorb() {
        let mut parent = parent_grain();
        parent.learn(7, [0x77; 32]); // a key that exists at fork time
        parent.learn(8, [0x88; 32]); // an untouched control key
        parent.checkpoint().unwrap();

        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");

        // The child FORGETS key 7; the parent touches neither (disjoint from the delete).
        assert!(child.forget(7), "child forgets a key it inherited at fork");

        let report = stitch(&parent, &child);
        assert!(
            report.settles(),
            "a lone deletion settles: {:?}",
            report.conflicts
        );

        // Before absorb the parent still holds the stale value.
        assert_eq!(parent.recall(7), Some([0x77; 32]), "not yet absorbed");
        parent.absorb(&report).unwrap();
        // The forget is APPLIED — the key is GONE, not silently left stale.
        assert_eq!(
            parent.recall(7),
            None,
            "the child's deletion landed in the parent"
        );
        assert_eq!(
            parent.recall(8),
            Some([0x88; 32]),
            "an untouched key survives absorb"
        );
    }

    /// TOOTH — a DELETE-vs-EDIT on the same address is a genuine conflict: the child
    /// forgets a key the parent concurrently re-edits, so the stitch does NOT settle
    /// (fail-closed) and absorbing is refused.
    #[test]
    fn delete_vs_edit_is_a_conflict_and_does_not_settle() {
        let mut parent = parent_grain();
        parent.learn(3, [0x30; 32]);
        parent.checkpoint().unwrap();

        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");

        // The parent re-edits key 3 while the child forgets it — a real collision.
        parent.learn(3, [0x31; 32]);
        assert!(
            child.forget(3),
            "child forgets the same key the parent re-edits"
        );

        let report = stitch(&parent, &child);
        assert!(
            !report.settles(),
            "a delete-vs-edit clash does NOT settle (fail-closed)"
        );
        assert_eq!(parent.absorb(&report), Err(GrainError::NotSettled));
        // The parent's live value is untouched by the refused absorb.
        assert_eq!(
            parent.recall(3),
            Some([0x31; 32]),
            "refused absorb leaves state intact"
        );
    }

    /// TOOTH — a FIELD-plane merge is absorbed too (previously silently dropped: absorb
    /// applied only the `Heap` plane). A child edits an overflow field slot; on absorb
    /// the parent's real mind carries it.
    #[test]
    fn field_plane_merge_is_absorbed() {
        let mut parent = parent_grain();
        parent.checkpoint().unwrap();

        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");

        // The child writes an overflow field (slot ≥ STATE_SLOTS → the projected `Field`
        // plane), which the parent never touched — a clean field-granular divergence.
        child.mind.state.set_field_ext(20, [0x20; 32]);

        let report = stitch(&parent, &child);
        assert!(
            report.settles(),
            "a lone field edit settles: {:?}",
            report.conflicts
        );
        assert_eq!(
            parent.mind.state.get_field_ext(20),
            None,
            "not yet absorbed"
        );

        parent.absorb(&report).unwrap();
        assert_eq!(
            parent.mind.state.get_field_ext(20),
            Some([0x20; 32]),
            "the child's field-plane edit landed in the parent (Heap-only absorb dropped it)"
        );
    }

    /// TOOTH — absorbing a FOREIGN grain's stitch report is refused outright: without the
    /// mind binding, a report from an unrelated pair reads every own address as
    /// "forgotten" (wiping the mind) and implants the foreign learnings under this
    /// identity. The live mind must be untouched by the refusal.
    #[test]
    fn absorb_refuses_a_foreign_grains_report() {
        // Grain A — the victim, with its own learnings.
        let mut a = parent_grain();
        a.learn(0, [0xA0; 32]);
        a.checkpoint().unwrap();
        let a_root = a.root();

        // An UNRELATED grain B (different mind identity) and its fork.
        let mut b = Grain::rent([0xB0; 32], [0x02; 32], terms(17, 9), 1_000_000).unwrap();
        b.learn(3, [0xB3; 32]);
        b.checkpoint().unwrap();
        let mut b_child = b.fork(terms(71, 9), 500_000, &[]).expect("fork B");
        b_child.learn(4, [0xB4; 32]);
        let report_b = stitch(&b, &b_child);
        assert!(
            report_b.settles(),
            "B's own stitch is a perfectly clean one"
        );
        assert_ne!(a.mind_id(), b.mind_id(), "genuinely foreign minds");

        // Absorbing B's report into A is REFUSED, naming both minds.
        match a.absorb(&report_b) {
            Err(GrainError::ForeignStitch { report, mind }) => {
                assert_eq!(report, b.mind_id());
                assert_eq!(mind, a.mind_id());
            }
            other => panic!("a foreign report was absorbed: {:?}", other.is_ok()),
        }
        // The live mind is untouched: nothing wiped, nothing implanted.
        assert_eq!(a.recall(0), Some([0xA0; 32]), "own learning survives");
        assert_eq!(a.recall(3), None, "no foreign learning implanted");
        assert_eq!(a.root(), a_root, "the committed root did not move");
    }

    /// TOOTH — absorb is fail-closed on a DIVERGENT report: if applying the reported
    /// merge cannot reproduce the reported merged state exactly (here: a value the
    /// mind's planes cannot hold), the absorb is refused and the live mind untouched —
    /// never a silent partial apply.
    #[test]
    fn absorb_refuses_a_report_it_cannot_faithfully_apply() {
        let mut parent = parent_grain();
        parent.learn(0, [0x10; 32]);
        parent.checkpoint().unwrap();
        let mut child = parent.fork(terms(70, 9), 500_000, &[]).expect("fork");
        child.learn(1, [0xC1; 32]);

        let mut report = stitch(&parent, &child);
        assert!(report.settles());
        // Corrupt the merged state with a value the heap plane cannot hold (a scalar at
        // a heap address). The apply loop cannot land it; the fidelity tooth must bite.
        report.merged_state.insert(
            UKey::Heap {
                cell: parent.mind_id(),
                collection: MIND_COLL,
                key: 999,
            },
            UVal::U64(7),
        );
        let root_before = parent.root();
        assert_eq!(parent.absorb(&report), Err(GrainError::AbsorbDivergence));
        assert_eq!(parent.root(), root_before, "live mind untouched on refusal");
        assert_eq!(parent.recall(1), None, "nothing was part-applied");

        // The untampered report still absorbs (the tooth is not over-broad).
        let clean = stitch(&parent, &child);
        parent.absorb(&clean).unwrap();
        assert_eq!(parent.recall(1), Some([0xC1; 32]));
    }

    /// TOOTH — the FIELD plane is bound into the timeline: a rewind restores the
    /// overflow-fields state alongside the heap, and a tampered fields image (one that
    /// no longer folds to its committed fields root) is refused fail-closed.
    #[test]
    fn rewind_restores_and_rewitnesses_the_field_plane() {
        let mut grain = parent_grain();
        grain.learn(0, [0x01; 32]);
        grain.mind.state.set_field_ext(20, [0x20; 32]);
        let r1 = grain.checkpoint().unwrap();

        // Advance BOTH planes past r1.
        grain.learn(0, [0x02; 32]);
        grain.mind.state.set_field_ext(20, [0x21; 32]);
        grain.checkpoint().unwrap();

        // Rewind re-inhabits BOTH planes' committed state.
        grain.rewind(r1).unwrap();
        assert_eq!(grain.recall(0), Some([0x01; 32]), "heap plane restored");
        assert_eq!(
            grain.mind.state.get_field_ext(20),
            Some([0x20; 32]),
            "field plane restored (previously silently left at its later value)"
        );

        // Tamper the fields image of a fresh grain's checkpoint → fail-closed refusal.
        let mut g2 = parent_grain();
        g2.learn(0, [0xAA; 32]);
        g2.mind.state.set_field_ext(21, [0x99; 32]);
        let root_v1 = g2.checkpoint().unwrap();
        g2.learn(0, [0xBB; 32]);
        g2.checkpoint().unwrap();
        g2.tamper_checkpoint_fields(root_v1);
        let live_field = g2.mind.state.get_field_ext(21);
        assert!(matches!(
            g2.rewind(root_v1),
            Err(GrainError::BoundaryMismatch { .. })
        ));
        assert_eq!(
            g2.mind.state.get_field_ext(21),
            live_field,
            "live mind untouched"
        );
        assert_eq!(g2.recall(0), Some([0xBB; 32]), "heap plane also untouched");
    }

    /// TOOTH 6 — a cap REVOKED mid-branch cannot outlive its revocation at stitch: the
    /// linear DROP, settlement-sound. Non-vacuous BOTH ways (admitted before, dropped
    /// after) while the disjoint state still settles.
    #[test]
    fn revoked_cap_cannot_outlive_revocation_at_stitch() {
        let mut parent = parent_grain();
        let gift = cid(0x91);
        parent.grant(gift);
        parent.checkpoint().unwrap();

        // The child is conferred the gift cap and both make DISJOINT edits (state
        // settles, orthogonal to authority).
        let mut child = parent.fork(terms(70, 9), 500_000, &[gift]).expect("fork");
        child.learn(1, [0xC1; 32]);
        parent.learn(2, [0xD2; 32]);

        // BEFORE the revoke: gift is held at the tip → admitted, nothing dropped.
        let before = stitch(&parent, &child);
        assert!(
            before.admitted_authority.iter().any(|c| c.target == gift),
            "gift is admitted before the revoke (the gate is non-vacuous)"
        );
        assert!(
            !before.dropped_authority.iter().any(|c| c.target == gift),
            "nothing dropped before the revoke"
        );
        assert!(
            before.settles(),
            "the disjoint state settles before the revoke"
        );

        // THE REVOCATION on the settlement tip (the parent revokes its own gift cap).
        assert!(parent.revoke(gift), "the parent revokes gift");
        assert!(!parent.holds(gift));

        // AFTER: the SAME stitch LINEAR-DROPS gift while the disjoint state still settles.
        let after = stitch(&parent, &child);
        assert!(
            after.dropped_authority.iter().any(|c| c.target == gift),
            "after the revoke gift is LINEAR-DROPPED (revoke_before_tip_unsettleable)"
        );
        assert!(
            !after.admitted_authority.iter().any(|c| c.target == gift),
            "the revoked gift is no longer admitted"
        );
        assert!(
            after.settles(),
            "the disjoint state still settles — authority is orthogonal"
        );
        assert!(
            after.settled_root.is_some(),
            "the state stitch is still binding"
        );

        // Non-vacuous both ways: the drop appeared ONLY after the revoke.
        assert_ne!(
            before.dropped_authority, after.dropped_authority,
            "the drop is the revocation, not a blanket refusal"
        );
    }
}
