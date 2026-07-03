//! Replay / time-travel over history — VERIFIED, not approximate.
//!
//! The live [`World`](crate::world::World) is an append-only engine: a turn maps
//! a pre-state to a post-state plus a receipt, and the ordered receipt chain IS
//! the history (the local blocklace). This module makes that history NAVIGABLE
//! and, crucially, makes the navigation *checkable*: scrubbing to any past point
//! reconstructs the world state at step k by REPLAY and asserts the
//! reconstructed canonical ledger root MATCHES the root recorded at k. Time
//! travel you can trust, because every landing is re-derived from genesis and
//! verified against the recorded commitment.
//!
//! # Agreement with the canonical recovery model
//!
//! This is the in-process, interactive form of the verified recovery model that
//! `persist/src/snapshot.rs` ships over the wire and
//! `metatheory/Dregg2/Distributed/CrashRecovery.lean` proves:
//!
//! ```text
//!   recover genesis log k = applyWrites (checkpoint genesis log k) (overlay log k)
//!                         = replay genesis log
//! ```
//!
//! We use the EXACT canonical commitment `snapshot.rs` binds against — the cell
//! crate's own deterministic, order-independent Merkle root
//! [`dregg_cell::Ledger::root`] (`snapshot.rs::snapshot_ledger_root`) — as the
//! "root tooth". A reconstructed ledger that commits to a root other than the
//! one recorded at step k is REFUSED (`ReplayError::RootMismatch`), the same
//! fail-closed anti-substitution discipline as `apply_snapshot`.
//!
//! And we mirror `recover = checkpoint ⊕ overlay`: [`History::replay_to`] can
//! start from genesis OR from the nearest recorded checkpoint and overlay the
//! post-checkpoint turns ([`History::replay_to_via_checkpoint`]); both land on
//! the same verified root (the [`CrashRecovery`] identity, checked in tests).
//!
//! # What this module records
//!
//! `World` keeps receipts but not the *input* turns, and its `state_root()` is a
//! different (height-folded) commitment. So replay needs the canonical history:
//! the ordered [`RecordedStep`]s — genesis installs + committed turns — each
//! carrying the canonical [`Ledger::root`] post-state tooth. [`History`] is that
//! recorder. It drives the SAME embedded executor `World` uses, so a replayed
//! turn commits identically (same chain-head threading, same verified
//! semantics) — replay is re-execution, not a parallel model.

use std::collections::BTreeMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::umem::{project_ledger, reify_ledger, UProjection};
use dregg_turn::{
    turn::{Turn, TurnReceipt, TurnResult},
    ComputronCosts, TurnExecutor,
};

// ===========================================================================
// The recorded history
// ===========================================================================

/// One recorded step of world history — the genesis installs and the committed
/// turns, in order. Replaying steps `0..=k` reconstructs the world at step k.
#[derive(Clone)]
pub enum RecordedStep {
    /// A cell installed directly at genesis (bypasses the executor — the way a
    /// node seeds its genesis block). Carries the full cell so replay
    /// reinstalls it verbatim.
    Genesis { cell: Box<Cell> },
    /// A turn committed against the embedded verified executor. Carries the
    /// input turn (so replay RE-EXECUTES it), the real receipt, and the
    /// canonical ledger root tooth recorded immediately after the commit.
    Committed {
        turn: Box<Turn>,
        receipt: Box<TurnReceipt>,
        /// The canonical [`Ledger::root`] of the post-state, recorded per step —
        /// the same commitment `snapshot.rs` binds against.
        ///
        /// HONEST BOUNDARY (what actually verifies replay): this is a per-step
        /// *copy* of the canonical tooth, equal by construction to the parallel
        /// [`History`]`.roots[k+1]` — both are set from the identical
        /// `ledger.root()` in [`History::record_commit`]. The value the replay path
        /// verifies the reconstructed ledger against is that parallel `roots` vector
        /// ([`History::root_at`]), checked once per landing at the end of
        /// [`History::replay_to`]; `apply_step` drops this per-step field via `..`
        /// and no verification path currently consults it. Editing only this field
        /// (leaving `roots[k]` honest) changes no replay outcome. It is surfaced via
        /// [`RecordedStep::root_after`] for external inspection, not verification.
        post_root: [u8; 32],
    },
}

impl RecordedStep {
    /// The per-step canonical root tooth this step carries *in isolation*, if any.
    ///
    /// `Some(post_root)` for a [`RecordedStep::Committed`] turn — the
    /// [`Ledger::root`] recorded immediately after that commit. `None` for a
    /// [`RecordedStep::Genesis`] install: a genesis step carries only its cell, not
    /// a root — the post-genesis root needs ledger context and lives ONLY in the
    /// parallel [`History`]`.roots` vector, so this step cannot hand one back
    /// without inventing it. (It formerly returned a `[0u8; 32]` placeholder here —
    /// a value that can never equal a real blake3 ledger root, so any verifier that
    /// keyed off it would spuriously reject every genesis step; `None` states the
    /// honest thing instead of a bogus tooth.)
    ///
    /// This is the recorded per-step *copy* (see [`RecordedStep::Committed`]'s
    /// `post_root`); the authoritative tooth the replay path verifies against is
    /// [`History::root_at`]. Use that for verification — this accessor is for
    /// inspection (timeline UIs, diagnostics), and today has no in-tree consumer.
    pub fn root_after(&self) -> Option<[u8; 32]> {
        match self {
            RecordedStep::Genesis { .. } => None,
            RecordedStep::Committed { post_root, .. } => Some(*post_root),
        }
    }

    /// A short human label for the timeline scrubber.
    pub fn label(&self) -> String {
        match self {
            RecordedStep::Genesis { cell } => {
                format!(
                    "genesis · cell {} ({})",
                    short(cell.id().as_bytes()),
                    cell.state.balance()
                )
            }
            RecordedStep::Committed { receipt, .. } => format!(
                "turn · agent {} · {} actions",
                short(receipt.agent.as_bytes()),
                receipt.action_count
            ),
        }
    }
}

/// A landing point in history: a step index and the root tooth recorded there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Checkpoint {
    /// The number of steps applied at this checkpoint (`replay_to(step)` lands
    /// here). `0` is genesis-empty.
    pub step: usize,
    /// The canonical ledger root committed at this checkpoint.
    pub root: [u8; 32],
}

/// The recorded, replayable history of a world.
///
/// Built by [`History::record`]ing the same operations a `World` performs, so it
/// holds the canonical ordered history plus, at each step, the canonical root
/// tooth. Every navigation ([`Self::replay_to`], [`Self::fork_at`],
/// [`Self::diff`]) re-derives state from genesis and verifies it.
pub struct History {
    steps: Vec<RecordedStep>,
    /// The canonical root tooth recorded *after* each step (parallel to
    /// `steps`, plus index 0 = the empty-ledger root). `roots[i]` is the root
    /// after applying steps `0..i`, so `roots[0]` is the empty root and
    /// `roots[steps.len()]` is the head root.
    roots: Vec<[u8; 32]>,
    /// The umem BOUNDARY captured after each step (parallel to `roots`): the
    /// [`project_ledger`] projection of the post-state ledger into the universal
    /// `(domain, collection, key) ↦ value` address space. `boundaries[i]` is the
    /// boundary after applying steps `0..i` (`boundaries[0]` = the empty-ledger
    /// projection). This is the umem time-travel revolution made live: the
    /// boundary IS the state, so [`Self::reify_to`] restores any past point by
    /// [`reify_ledger`] (a single inverse fold) instead of O(history)
    /// re-execution from genesis — consistency-checked against `roots[i]` all the
    /// same (a co-recorded round-trip check, strictly weaker than
    /// [`Self::replay_to`]'s re-execution ground truth — see [`Self::reify_to`]).
    boundaries: Vec<UProjection>,
    /// The fixed executor timestamp used for every recorded turn, so replay is
    /// bit-deterministic (a recorded receipt re-derives identically).
    timestamp: i64,
    /// The computron cost model the recording executor meters at — pinned to the
    /// live [`World`](crate::world::World)'s engine costs so a recorded turn
    /// re-derives bit-identically on replay (zero for `World::new`, the production
    /// model for `World::with_costs`).
    costs: ComputronCosts,
}

impl History {
    /// A fresh, empty history. `timestamp` is the wall-clock the recording
    /// executor used; replay reuses it so receipts re-derive identically.
    /// Free-metered (matches `World::new`).
    pub fn new(timestamp: i64) -> Self {
        Self::with_costs(timestamp, ComputronCosts::zero())
    }

    /// A fresh, empty history whose recording executor meters at `costs` — pinned
    /// to the live engine's cost model so replay re-derives identically when the
    /// world is metered ([`World::with_costs`], the swarm-budget substrate).
    pub fn with_costs(timestamp: i64, costs: ComputronCosts) -> Self {
        // root after 0 steps (the empty ledger); the umem boundary after 0 steps is
        // the empty-ledger projection.
        let roots = vec![Ledger::new().root()];
        let boundaries = vec![project_ledger(&Ledger::new())];
        History {
            steps: Vec::new(),
            roots,
            boundaries,
            timestamp,
            costs,
        }
    }

    /// The recording executor: an executor metering at the history's pinned costs
    /// and timestamp (matches the live [`World`](crate::world::World)'s engine).
    /// Public so a live `World` can stand up the recorder substrate it drives this
    /// history against, in lock-step with its engine.
    pub fn fresh_executor(&self) -> TurnExecutor {
        let mut e = TurnExecutor::new(self.costs.clone());
        e.set_timestamp(self.timestamp);
        e
    }

    /// The number of recorded steps (the head index).
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The recorded steps, in order.
    pub fn steps(&self) -> &[RecordedStep] {
        &self.steps
    }

    /// The canonical root tooth recorded after `step` steps (`step` in
    /// `0..=len()`; `step = 0` is the empty-ledger root, `step = len()` the
    /// head). Panics out of range.
    pub fn root_at(&self, step: usize) -> [u8; 32] {
        self.roots[step]
    }

    /// All checkpoints (every step is a landing point with a recorded root).
    pub fn checkpoints(&self) -> Vec<Checkpoint> {
        self.roots
            .iter()
            .enumerate()
            .map(|(step, root)| Checkpoint { step, root: *root })
            .collect()
    }

    // --- recording (mirrors World's genesis + commit paths) -----------------

    /// Record a genesis install. Installs `cell` into `ledger` directly (the
    /// genesis path) and appends the step + the new canonical root tooth.
    pub fn record_genesis(&mut self, ledger: &mut Ledger, cell: Cell) -> CellId {
        let id = cell.id();
        ledger
            .insert_cell(cell.clone())
            .expect("genesis insert is into a fresh slot");
        self.steps.push(RecordedStep::Genesis {
            cell: Box::new(cell),
        });
        self.roots.push(ledger.root());
        // Capture the umem boundary of the post-state (the reify_to fast-restore image).
        self.boundaries.push(project_ledger(ledger));
        id
    }

    /// Record a committed turn. Drives `executor.execute` against `ledger`
    /// exactly as `World::commit_turn` does (threads the chain head, advances
    /// it on commit), then appends the step + the new canonical root tooth.
    ///
    /// Returns the receipt on commit, or `None` if the real executor rejected
    /// the turn (a rejected turn is NOT recorded — it did not change history).
    pub fn record_commit(
        &mut self,
        executor: &TurnExecutor,
        ledger: &mut Ledger,
        mut turn: Turn,
    ) -> Option<TurnReceipt> {
        turn.previous_receipt_hash = executor.get_last_receipt_hash(&turn.agent);
        match executor.execute(&turn, ledger) {
            TurnResult::Committed { receipt, .. } => {
                executor.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                let post_root = ledger.root();
                self.steps.push(RecordedStep::Committed {
                    turn: Box::new(turn),
                    receipt: Box::new(receipt.clone()),
                    post_root,
                });
                self.roots.push(post_root);
                // Capture the umem boundary of the post-state (the reify_to image).
                self.boundaries.push(project_ledger(ledger));
                Some(receipt)
            }
            _ => None,
        }
    }

    // --- replay / scrub (VERIFIED) ------------------------------------------

    /// Reconstruct the world state at step `k` by REPLAY from genesis, and
    /// verify the reconstructed canonical ledger root matches the recorded
    /// tooth `roots[k]`. Fail-closed on mismatch.
    ///
    /// `k` is in `0..=len()`: `k = 0` is the empty pre-genesis ledger, `k =
    /// len()` is the head. This is `replay genesis (take k)` from the recovery
    /// model — re-executing every recorded turn up to k against a fresh
    /// executor over a fresh ledger.
    pub fn replay_to(&self, k: usize) -> Result<Ledger, ReplayError> {
        if k > self.steps.len() {
            return Err(ReplayError::OutOfRange {
                step: k,
                len: self.steps.len(),
            });
        }
        let mut ledger = Ledger::new();
        let executor = self.fresh_executor();
        for step in &self.steps[..k] {
            apply_step(&executor, &mut ledger, step)?;
        }
        // The root tooth: the reconstructed ledger MUST commit to the recorded
        // root at k (the same anti-substitution discipline as snapshot.rs).
        let got = ledger.root();
        let want = self.roots[k];
        if got != want {
            return Err(ReplayError::RootMismatch { step: k, got, want });
        }
        Ok(ledger)
    }

    /// **THE UMEM-BOUNDARY RESTORE — the live time-scrub's reconstruction path.**
    ///
    /// Reconstruct the world state at step `k` by RESTORING the umem boundary
    /// captured at `k` ([`reify_ledger`] over `boundaries[k]`) — a single inverse
    /// fold, NOT O(history) re-execution from genesis. This is the umem time-travel
    /// revolution wired into the live cockpit: "rewind to step k" = restore a
    /// boundary, exactly the `turn/tests/umem_time_travel.rs` keystone
    /// (`reify_ledger(project_ledger(L)) == L`) run on real recorded history.
    ///
    /// HONEST BOUNDARY (weaker than [`Self::replay_to`], despite the fast path):
    /// this restore is NOT held to `replay_to`'s anti-substitution discipline. It
    /// checks that the reified ledger commits to the recorded root tooth `roots[k]`
    /// ([`ReplayError::RootMismatch`] on failure) — but `boundaries[k]` and
    /// `roots[k]` are CO-RECORDED post-state artifacts, captured together from the
    /// SAME ledger in [`Self::record_commit`] / [`Self::record_genesis`]. So this
    /// check is the round-trip identity `reify_ledger(project_ledger(L)).root() ==
    /// L.root()` between two values recorded in lockstep — it confirms the boundary
    /// is INTERNALLY CONSISTENT with its co-recorded root, NOT that either agrees
    /// with re-executing the input turns. [`Self::replay_to`], by contrast, discards
    /// the recorded post-state and RE-DERIVES it from genesis — that re-execution is
    /// the actual anti-substitution ground truth. A JOINT substitution of the pair
    /// (`boundaries[k]` ← a forged-but-faithful `project_ledger(L')`, `roots[k]` ←
    /// `L'.root()`) passes this check while [`Self::replay_to`] catches it — pinned
    /// by the `reify_to_trusts_the_co_recorded_pair…` test.
    ///
    /// This is safe TODAY only because `History`'s `steps` / `roots` / `boundaries`
    /// are private, have no from-parts constructor and no `Serialize`/`Deserialize`,
    /// and are mutated ONLY in lockstep by the `record_*` methods — so the pair is
    /// always consistent with the turns that produced it. The gap would become a
    /// real substitution vector the moment a `History` is reconstructed from
    /// persisted or untrusted data; reach for [`Self::replay_to`] where independence
    /// from the recorded boundary actually matters.
    ///
    /// A cell whose state lies OUTSIDE the projection's faithful class (typed
    /// interfaces, capability tombstones, a post-revoke `next_slot` gap — the named
    /// `reify_seam` residuals) makes [`reify_ledger`] refuse rather than round-trip
    /// a lie; this method then FALLS BACK to root-verified [`Self::replay_to`], so
    /// the scrub is always correct — the umem boundary is the fast path, genesis
    /// replay the safety net. The returned [`ScrubSource`] reports which fired.
    pub fn reify_to(&self, k: usize) -> Result<(Ledger, ScrubSource), ReplayError> {
        if k >= self.boundaries.len() {
            return Err(ReplayError::OutOfRange {
                step: k,
                len: self.steps.len(),
            });
        }
        match reify_ledger(&self.boundaries[k]) {
            Ok(mut ledger) => {
                // The root tooth: the restored boundary MUST reproduce the recorded
                // commitment (the same fail-closed discipline as replay_to / snapshot.rs).
                let got = ledger.root();
                let want = self.roots[k];
                if got != want {
                    return Err(ReplayError::RootMismatch { step: k, got, want });
                }
                Ok((ledger, ScrubSource::UmemBoundary))
            }
            // The boundary holds a cell outside the faithful class — restore by
            // root-verified genesis replay instead (correct, just not O(1)).
            Err(_reify_err) => Ok((self.replay_to(k)?, ScrubSource::ReplayFallback)),
        }
    }

    /// Classify EVERY step's reversibility in a SINGLE forward pass — O(N) total
    /// instead of `replay_to(step-1)` per step (O(N²), the TIME-panel hang). Returns
    /// one entry per step: `Some(reversible)` for a committed turn (classified
    /// against the running pre-state ledger), `None` for a genesis step. The pre-
    /// state for step `i` is the running ledger BEFORE step `i` is applied — exactly
    /// what `replay_to(i)` would reconstruct, but reusing one running ledger.
    pub fn reversibility_classification(&self) -> Vec<Option<bool>> {
        let executor = self.fresh_executor();
        let mut ledger = Ledger::new();
        let mut out = Vec::with_capacity(self.steps.len());
        for step in &self.steps {
            match step {
                RecordedStep::Committed { turn, .. } => {
                    // `ledger` here == replay_to(i): the pre-state for this turn.
                    out.push(Some(turn.is_reversible(&ledger)));
                }
                RecordedStep::Genesis { .. } => out.push(None),
            }
            if apply_step(&executor, &mut ledger, step).is_err() {
                while out.len() < self.steps.len() {
                    out.push(None);
                }
                break;
            }
        }
        out
    }

    /// `recover = checkpoint ⊕ overlay`: reconstruct step `k` starting NOT from
    /// genesis but from the NEAREST recorded checkpoint at-or-below `k`, then
    /// overlaying (re-executing) only the post-checkpoint turns. This mirrors
    /// `snapshot.rs::apply_snapshot` (checkpoint ⊕ overlay) and MUST land on the
    /// same verified root as [`Self::replay_to`] (the `recover_eq_replay`
    /// identity — asserted in tests).
    ///
    /// Because replay re-executes turns (the executor is stateful in its
    /// chain-head table), the "checkpoint" here is a recorded *ledger snapshot*
    /// at `checkpoint_step`; we reconstruct that ledger by replay once, then
    /// continue executing from `checkpoint_step..k`. The point of the method is
    /// to demonstrate the checkpoint⊕overlay decomposition lands identically.
    pub fn replay_to_via_checkpoint(
        &self,
        k: usize,
        checkpoint_step: usize,
    ) -> Result<Ledger, ReplayError> {
        if k > self.steps.len() {
            return Err(ReplayError::OutOfRange {
                step: k,
                len: self.steps.len(),
            });
        }
        if checkpoint_step > k {
            return Err(ReplayError::OutOfRange {
                step: checkpoint_step,
                len: k,
            });
        }
        // The checkpoint half: reconstruct (and verify) the ledger AT the
        // checkpoint step. A fresh executor whose chain-head table we re-prime
        // by replaying through the checkpoint, then continue.
        let mut ledger = Ledger::new();
        let executor = self.fresh_executor();
        for step in &self.steps[..checkpoint_step] {
            apply_step(&executor, &mut ledger, step)?;
        }
        // Verify the checkpoint tooth.
        let cp_got = ledger.root();
        if cp_got != self.roots[checkpoint_step] {
            return Err(ReplayError::RootMismatch {
                step: checkpoint_step,
                got: cp_got,
                want: self.roots[checkpoint_step],
            });
        }
        // The overlay half: re-execute the post-checkpoint turns.
        for step in &self.steps[checkpoint_step..k] {
            apply_step(&executor, &mut ledger, step)?;
        }
        let got = ledger.root();
        let want = self.roots[k];
        if got != want {
            return Err(ReplayError::RootMismatch { step: k, got, want });
        }
        Ok(ledger)
    }

    // --- fork / what-if ------------------------------------------------------

    /// Branch at step `k`: reconstruct (verified) the world at k, apply a
    /// DIFFERENT turn `alt`, and run forward on the fork. The mainline is
    /// untouched (this builds a throwaway ledger). Returns the fork outcome
    /// including the divergence diff against the mainline at the same depth.
    ///
    /// "Same depth" = the mainline state at step `k+1` (one turn applied) vs the
    /// fork state after `alt`. If the mainline has no step `k+1` (k is the
    /// head), the comparison is against the mainline at k (the diff is then the
    /// fork's own delta).
    pub fn fork_at(&self, k: usize, alt: Turn) -> Result<Fork, ReplayError> {
        // Reconstruct + verify the branch point.
        let mut fork_ledger = self.replay_to(k)?;

        // Re-prime an executor's chain-head table to the branch point by
        // replaying through k (so the alt turn chains correctly), then apply alt.
        let executor = self.fresh_executor();
        {
            let mut warm = Ledger::new();
            for step in &self.steps[..k] {
                apply_step(&executor, &mut warm, step)?;
            }
        }
        let mut alt = alt;
        alt.previous_receipt_hash = executor.get_last_receipt_hash(&alt.agent);
        let outcome = match executor.execute(&alt, &mut fork_ledger) {
            TurnResult::Committed { receipt, .. } => {
                executor.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                ForkOutcome::Committed {
                    receipt: Box::new(receipt),
                }
            }
            TurnResult::Rejected { reason, at_action } => ForkOutcome::Rejected {
                reason: format!("{reason:?}"),
                at_action,
            },
            TurnResult::Expired => ForkOutcome::Rejected {
                reason: "conditional turn expired".into(),
                at_action: vec![],
            },
            TurnResult::Pending => ForkOutcome::Rejected {
                reason: "conditional turn pending".into(),
                at_action: vec![],
            },
        };

        let fork_root = fork_ledger.root();

        // The mainline state at the same depth (k+1 if it exists, else k).
        let mainline_depth = (k + 1).min(self.steps.len());
        let mut mainline_ledger = self.replay_to(mainline_depth)?;
        let mainline_root = mainline_ledger.root();

        // The divergence: the diff between mainline-at-depth and the fork.
        let divergence = diff_ledgers(&mainline_ledger, &fork_ledger);

        Ok(Fork {
            branch_step: k,
            outcome,
            fork_root,
            mainline_depth,
            mainline_root,
            divergence,
        })
    }

    // --- state diff ----------------------------------------------------------

    /// The state diff between two history points `i` and `j` (verified replays):
    /// the set of cells that were created, removed, or changed (balance / caps /
    /// nonce / fields) between step i and step j.
    pub fn diff(&self, i: usize, j: usize) -> Result<StateDiff, ReplayError> {
        let a = self.replay_to(i)?;
        let b = self.replay_to(j)?;
        Ok(diff_ledgers(&a, &b))
    }
}

/// Apply one recorded step to a ledger under a (warm) executor, re-deriving it.
fn apply_step(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    step: &RecordedStep,
) -> Result<(), ReplayError> {
    match step {
        RecordedStep::Genesis { cell } => {
            // Genesis is an idempotent direct install (fresh slot on replay).
            let _ = ledger.insert_cell(*cell.clone());
            Ok(())
        }
        RecordedStep::Committed { turn, receipt, .. } => {
            let mut t = turn.clone();
            t.previous_receipt_hash = executor.get_last_receipt_hash(&t.agent);
            match executor.execute(&t, ledger) {
                TurnResult::Committed { receipt: r, .. } => {
                    executor.set_last_receipt_hash(r.agent, r.receipt_hash());
                    Ok(())
                }
                other => Err(ReplayError::NondeterministicReplay {
                    expected_receipt: receipt.receipt_hash(),
                    got: format!("{other:?}"),
                }),
            }
        }
    }
}

// ===========================================================================
// Diffs
// ===========================================================================

/// A per-cell change between two world states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellChange {
    /// The cell exists at j but not at i.
    Created { balance: i64, caps: usize },
    /// The cell exists at i but not at j.
    Removed { balance: i64, caps: usize },
    /// The cell exists in both but some observable changed.
    Changed {
        balance_before: i64,
        balance_after: i64,
        caps_before: usize,
        caps_after: usize,
        nonce_before: u64,
        nonce_after: u64,
        fields_changed: bool,
    },
}

impl CellChange {
    /// A short human label for the diff view.
    pub fn label(&self) -> String {
        match self {
            CellChange::Created { balance, caps } => {
                format!("created (balance {balance}, {caps} caps)")
            }
            CellChange::Removed { balance, caps } => {
                format!("removed (was balance {balance}, {caps} caps)")
            }
            CellChange::Changed {
                balance_before,
                balance_after,
                caps_before,
                caps_after,
                nonce_before,
                nonce_after,
                fields_changed,
            } => {
                let mut parts = Vec::new();
                if balance_before != balance_after {
                    parts.push(format!("balance {balance_before}→{balance_after}"));
                }
                if caps_before != caps_after {
                    parts.push(format!("caps {caps_before}→{caps_after}"));
                }
                if nonce_before != nonce_after {
                    parts.push(format!("nonce {nonce_before}→{nonce_after}"));
                }
                if *fields_changed {
                    parts.push("fields".into());
                }
                if parts.is_empty() {
                    "changed".into()
                } else {
                    parts.join(", ")
                }
            }
        }
    }
}

/// The set of cell changes between two world states (sorted by cell id for
/// determinism). Empty when the two states are identical.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StateDiff {
    pub changes: Vec<(CellId, CellChange)>,
}

impl StateDiff {
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }
    pub fn len(&self) -> usize {
        self.changes.len()
    }
    /// The ids that changed (created/removed/changed), sorted.
    pub fn changed_ids(&self) -> Vec<CellId> {
        self.changes.iter().map(|(id, _)| *id).collect()
    }
}

/// Compute the diff between two ledgers (the changed cells/caps/balances).
pub fn diff_ledgers(a: &Ledger, b: &Ledger) -> StateDiff {
    let am: BTreeMap<[u8; 32], &Cell> = a.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();
    let bm: BTreeMap<[u8; 32], &Cell> = b.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();

    let mut changes: Vec<(CellId, CellChange)> = Vec::new();

    // Created + changed (walk b).
    for (idb, cb) in &bm {
        match am.get(idb) {
            None => changes.push((
                CellId::from_bytes(*idb),
                CellChange::Created {
                    balance: cb.state.balance(),
                    caps: cb.capabilities.len(),
                },
            )),
            Some(ca) => {
                let fields_changed = ca.state.fields != cb.state.fields;
                let changed = ca.state.balance() != cb.state.balance()
                    || ca.capabilities.len() != cb.capabilities.len()
                    || ca.state.nonce() != cb.state.nonce()
                    || fields_changed;
                if changed {
                    changes.push((
                        CellId::from_bytes(*idb),
                        CellChange::Changed {
                            balance_before: ca.state.balance(),
                            balance_after: cb.state.balance(),
                            caps_before: ca.capabilities.len(),
                            caps_after: cb.capabilities.len(),
                            nonce_before: ca.state.nonce(),
                            nonce_after: cb.state.nonce(),
                            fields_changed,
                        },
                    ));
                }
            }
        }
    }
    // Removed (walk a for ids absent in b).
    for (ida, ca) in &am {
        if !bm.contains_key(ida) {
            changes.push((
                CellId::from_bytes(*ida),
                CellChange::Removed {
                    balance: ca.state.balance(),
                    caps: ca.capabilities.len(),
                },
            ));
        }
    }
    changes.sort_by(|x, y| x.0.as_bytes().cmp(y.0.as_bytes()));
    StateDiff { changes }
}

// ===========================================================================
// Fork results
// ===========================================================================

/// What happened when the fork's alternate turn ran on the branch.
#[derive(Clone)]
pub enum ForkOutcome {
    Committed {
        receipt: Box<TurnReceipt>,
    },
    Rejected {
        reason: String,
        at_action: Vec<usize>,
    },
}

impl ForkOutcome {
    pub fn is_committed(&self) -> bool {
        matches!(self, ForkOutcome::Committed { .. })
    }
}

/// The result of a what-if fork: where it branched, what the alt turn did, the
/// fork's root, and the divergence from the mainline at the same depth.
pub struct Fork {
    pub branch_step: usize,
    pub outcome: ForkOutcome,
    pub fork_root: [u8; 32],
    /// The mainline depth the fork is compared against (k+1 or the head).
    pub mainline_depth: usize,
    pub mainline_root: [u8; 32],
    /// The diff of mainline-at-depth vs the fork (the divergence).
    pub divergence: StateDiff,
}

impl Fork {
    /// Whether the fork actually diverged from the mainline (different root or a
    /// non-empty state diff).
    pub fn diverged(&self) -> bool {
        self.fork_root != self.mainline_root || !self.divergence.is_empty()
    }
}

// ===========================================================================
// Errors
// ===========================================================================

/// How [`History::reify_to`] reconstructed a scrub point — surfaced so the cockpit
/// (and tests) can SEE the umem time-travel path is the one actually exercised.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScrubSource {
    /// Restored by [`reify_ledger`] over the captured umem boundary — the O(1)
    /// inverse fold, no genesis re-execution (the umem revolution, live).
    UmemBoundary,
    /// The boundary held a cell outside the faithful class, so the scrub fell back
    /// to root-verified [`History::replay_to`] (genesis re-execution).
    ReplayFallback,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayError {
    /// Asked to replay/diff to a step beyond the recorded history.
    OutOfRange { step: usize, len: usize },
    /// The reconstructed ledger root did NOT match the recorded tooth — the
    /// anti-substitution failure (fail-closed). If this fires on honest history
    /// it indicates a determinism bug; on tampered history it is the tooth
    /// catching the tamper.
    RootMismatch {
        step: usize,
        got: [u8; 32],
        want: [u8; 32],
    },
    /// A recorded turn that committed when first run did NOT commit on replay —
    /// the executor behaved nondeterministically (a real bug if it ever fires).
    NondeterministicReplay {
        expected_receipt: [u8; 32],
        got: String,
    },
}

impl std::fmt::Display for ReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayError::OutOfRange { step, len } => {
                write!(f, "replay step {step} out of range (history len {len})")
            }
            ReplayError::RootMismatch { step, got, want } => write!(
                f,
                "replay root mismatch at step {step}: reconstructed {} != recorded {} (fail-closed)",
                short(got),
                short(want)
            ),
            ReplayError::NondeterministicReplay {
                expected_receipt,
                got,
            } => write!(
                f,
                "nondeterministic replay: recorded commit {} re-ran as {got}",
                short(expected_receipt)
            ),
        }
    }
}

impl std::error::Error for ReplayError {}

// ===========================================================================
// The panel view-model (gpui-free, testable) + the gpui render fn
// ===========================================================================

/// The gpui-free view-model the replay panel renders: the timeline scrubber,
/// the state at the cursor, the diff view, and any fork branch. Built from a
/// [`History`] + a cursor; the cockpit holds the cursor and calls
/// [`History`] navigation on it.
///
/// This mirrors the `reflect::Inspectable` pattern: a gpui-free projection the
/// view renders, so it is `cargo test`-able without a window.
pub struct ReplayPanelModel {
    /// The timeline: every landing point (step + recorded root + label).
    pub timeline: Vec<TimelineEntry>,
    /// Where the scrubber cursor sits (a step in `0..=history.len()`).
    pub cursor: usize,
    /// The verified reconstruction at the cursor: the cells, sorted, plus
    /// whether the root tooth matched (it always should — a `false` is a bug
    /// surfaced to the operator).
    pub cursor_state: CursorState,
    /// The diff from the previous step to the cursor (what the cursor's turn
    /// did), if the cursor is not at genesis.
    pub diff_from_prev: Option<StateDiff>,
    /// An active what-if fork's summary, if one is pinned.
    pub fork: Option<ForkSummary>,
}

/// One landing point on the timeline scrubber.
#[derive(Clone)]
pub struct TimelineEntry {
    pub step: usize,
    pub root: [u8; 32],
    pub label: String,
}

/// The verified reconstructed state at the cursor.
pub struct CursorState {
    pub step: usize,
    pub root: [u8; 32],
    /// True iff the reconstructed root matched the recorded tooth (verified).
    pub root_verified: bool,
    /// The cells at the cursor (id, balance, caps), sorted by id.
    pub cells: Vec<(CellId, i64, usize)>,
}

/// A pinned fork's summary for the panel.
pub struct ForkSummary {
    pub branch_step: usize,
    pub committed: bool,
    pub diverged: bool,
    pub fork_root: [u8; 32],
    pub mainline_root: [u8; 32],
    pub divergence: StateDiff,
}

impl ReplayPanelModel {
    /// Build the panel model for `history` with the scrubber at `cursor`,
    /// optionally pinning a `fork` summary. Performs the VERIFIED replay at the
    /// cursor (and the prev-step diff); a replay error is surfaced as an
    /// unverified cursor state rather than a panic.
    pub fn build(history: &History, cursor: usize, fork: Option<&Fork>) -> Self {
        let timeline = history
            .checkpoints()
            .into_iter()
            .map(|cp| TimelineEntry {
                step: cp.step,
                root: cp.root,
                label: if cp.step == 0 {
                    "genesis (empty)".to_string()
                } else {
                    history.steps()[cp.step - 1].label()
                },
            })
            .collect();

        let cursor = cursor.min(history.len());
        let cursor_state = match history.replay_to(cursor) {
            Ok(ledger) => {
                let mut cells: Vec<(CellId, i64, usize)> = ledger
                    .iter()
                    .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
                    .collect();
                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                CursorState {
                    step: cursor,
                    root: history.root_at(cursor),
                    root_verified: true,
                    cells,
                }
            }
            Err(_) => CursorState {
                step: cursor,
                root: history.root_at(cursor.min(history.len())),
                root_verified: false,
                cells: Vec::new(),
            },
        };

        let diff_from_prev = if cursor > 0 {
            history.diff(cursor - 1, cursor).ok()
        } else {
            None
        };

        let fork = fork.map(|f| ForkSummary {
            branch_step: f.branch_step,
            committed: f.outcome.is_committed(),
            diverged: f.diverged(),
            fork_root: f.fork_root,
            mainline_root: f.mainline_root,
            divergence: f.divergence.clone(),
        });

        ReplayPanelModel {
            timeline,
            cursor,
            cursor_state,
            diff_from_prev,
            fork,
        }
    }
}

/// First 6 bytes of a hash/id, hex.
fn short(bytes: &[u8]) -> String {
    let h: String = bytes.iter().take(6).map(|b| format!("{b:02x}")).collect();
    format!("{h}…")
}

// --- the gpui panel (only under the gpui-ui build) --------------------------
//
// Self-contained: it does not depend on the binary crate's `views` module
// (which is private to the binary), so the library stays swarm-safe. The main
// loop calls `replay_panel(&model)` and places the returned element.

#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
mod palette {
    use gpui::{rgb, Hsla};
    pub fn panel() -> Hsla {
        rgb(0x161b22).into()
    }
    pub fn panel_hi() -> Hsla {
        rgb(0x1f2630).into()
    }
    pub fn border() -> Hsla {
        rgb(0x2b3340).into()
    }
    pub fn text() -> Hsla {
        rgb(0xd7dee8).into()
    }
    pub fn muted() -> Hsla {
        rgb(0x7d8794).into()
    }
    pub fn accent() -> Hsla {
        rgb(0x6cb6ff).into()
    }
    pub fn good() -> Hsla {
        rgb(0x57d977).into()
    }
    pub fn warn() -> Hsla {
        rgb(0xe3b341).into()
    }
    pub fn bad() -> Hsla {
        rgb(0xe5534b).into()
    }
}

/// Render the replay / time-travel panel from a [`ReplayPanelModel`].
///
/// Self-contained gpui element (timeline scrubber → cursor state → diff → fork).
/// The MAIN LOOP wires the cockpit: it holds the cursor + any pinned `Fork`,
/// rebuilds the model each frame via [`ReplayPanelModel::build`], and places
/// this element. Click handlers (scrub/fork buttons) belong to the cockpit; this
/// fn is the read-only presentation so the library stays free of the cockpit's
/// `Context<Cockpit>` type.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub fn replay_panel(model: &ReplayPanelModel) -> impl gpui::IntoElement {
    use gpui::{div, px, ParentElement, Styled};
    use palette as p;

    let mut col = div().flex().flex_col().gap_1().p_3().size_full();

    // Header.
    col = col.child(
        div()
            .text_xs()
            .text_color(p::muted())
            .child("REPLAY · verified time-travel"),
    );

    // The timeline scrubber.
    let mut scrubber = div().flex().flex_col().gap_0p5().mt_1();
    for entry in &model.timeline {
        let at_cursor = entry.step == model.cursor;
        scrubber = scrubber.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .py_0p5()
                .rounded_md()
                .bg(if at_cursor { p::panel_hi() } else { p::panel() })
                .child(
                    div()
                        .text_xs()
                        .text_color(if at_cursor { p::accent() } else { p::muted() })
                        .child(format!(
                            "{} k{}  {}",
                            if at_cursor { "▸" } else { "·" },
                            entry.step,
                            entry.label
                        )),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(p::muted())
                        .child(short(&entry.root)),
                ),
        );
    }
    col = col.child(scrubber);

    // The verified state at the cursor.
    let cs = &model.cursor_state;
    col = col.child(
        div().mt_2().flex().gap_2().child(
            div()
                .text_xs()
                .text_color(if cs.root_verified {
                    p::good()
                } else {
                    p::bad()
                })
                .child(if cs.root_verified {
                    format!("✓ root verified @k{} {}", cs.step, short(&cs.root))
                } else {
                    format!("✗ root UNVERIFIED @k{}", cs.step)
                }),
        ),
    );
    let mut state_col = div().flex().flex_col().gap_0p5().mt_1();
    for (id, bal, caps) in &cs.cells {
        state_col = state_col.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .child(
                    div()
                        .text_xs()
                        .text_color(p::text())
                        .child(format!("⬡ {}", short(id.as_bytes()))),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(if *bal < 0 { p::warn() } else { p::text() })
                        .child(format!("{bal} · {caps} caps")),
                ),
        );
    }
    col = col.child(state_col);

    // The diff from the previous step.
    if let Some(diff) = &model.diff_from_prev {
        let mut diff_col = div().flex().flex_col().gap_0p5().mt_2();
        diff_col = diff_col.child(div().text_xs().text_color(p::muted()).child(format!(
            "DIFF k{}→k{} ({} changed)",
            cs.step.saturating_sub(1),
            cs.step,
            diff.len()
        )));
        for (id, change) in &diff.changes {
            diff_col = diff_col.child(
                div()
                    .text_xs()
                    .text_color(p::accent())
                    .px_2()
                    .child(format!("{} {}", short(id.as_bytes()), change.label())),
            );
        }
        col = col.child(diff_col);
    }

    // The fork branch.
    if let Some(fork) = &model.fork {
        let color = if fork.diverged { p::warn() } else { p::muted() };
        let mut fork_col = div()
            .flex()
            .flex_col()
            .gap_0p5()
            .mt_2()
            .p_2()
            .rounded_md()
            .border_1()
            .border_color(p::border())
            .bg(p::panel());
        fork_col = fork_col.child(div().text_xs().text_color(color).child(format!(
            "FORK @k{} · {} · {}",
            fork.branch_step,
            if fork.committed {
                "committed"
            } else {
                "rejected"
            },
            if fork.diverged {
                "DIVERGED from mainline"
            } else {
                "no divergence"
            },
        )));
        fork_col = fork_col.child(div().text_xs().text_color(p::muted()).child(format!(
            "fork root {}  vs mainline {}",
            short(&fork.fork_root),
            short(&fork.mainline_root)
        )));
        for (id, change) in &fork.divergence.changes {
            fork_col = fork_col.child(div().text_xs().text_color(p::warn()).px_2().child(format!(
                "{} {}",
                short(id.as_bytes()),
                change.label()
            )));
        }
        col = col.child(fork_col);
    }

    let _ = px(0.); // keep the px import live across cfg permutations
    col
}

// ===========================================================================
// A demo-history builder, mirroring world::demo_world's flows so the panel
// boots into a real, navigable, verified history.
// ===========================================================================

/// Build a demo history with the SAME flows as `world::demo_world` (treasury /
/// service / user / issuer well + five committed turns), recorded for replay.
/// Returns the history, the final ledger, and the (treasury, service, user) ids.
///
/// Deterministic timestamp so replay is bit-exact (no wall-clock).
pub fn demo_history() -> (History, Ledger, [CellId; 3]) {
    use crate::world::{grant_capability, make_open_cell, set_field, transfer};
    use dregg_cell::AuthRequired;

    let mut history = History::new(1_700_000_000);
    let mut ledger = Ledger::new();
    let executor = history.fresh_executor();

    let treasury = history.record_genesis(&mut ledger, make_open_cell(0x11, 1_000_000));
    let user = history.record_genesis(&mut ledger, make_open_cell(0x33, 5_000));

    // The service holds a capability reaching the user (so a later grant is
    // legitimate under no-amplification).
    let mut service_cell = make_open_cell(0x22, 0);
    let user_cap_slot = service_cell
        .capabilities
        .grant(user, AuthRequired::None)
        .expect("fresh c-list has a free slot");
    let service = history.record_genesis(&mut ledger, service_cell);

    // An issuer well carrying −supply.
    let mut well = make_open_cell(0xEE, 0);
    let _ = well.state.well_debit_balance(1_000_000);
    history.record_genesis(&mut ledger, well);

    // Five real turns through the embedded executor (same as demo_world).
    let nonce = |l: &Ledger, a: &CellId| l.get(a).map(|c| c.state.nonce()).unwrap_or(0);

    let t1 = crate::world::bare_turn(
        treasury,
        nonce(&ledger, &treasury),
        vec![transfer(treasury, service, 250_000)],
    );
    history.record_commit(&executor, &mut ledger, t1);
    let t2 = crate::world::bare_turn(
        treasury,
        nonce(&ledger, &treasury),
        vec![transfer(treasury, user, 50_000)],
    );
    history.record_commit(&executor, &mut ledger, t2);
    let t3 = crate::world::bare_turn(
        user,
        nonce(&ledger, &user),
        vec![transfer(user, service, 1_000)],
    );
    history.record_commit(&executor, &mut ledger, t3);
    let t4 = crate::world::bare_turn(
        service,
        nonce(&ledger, &service),
        vec![grant_capability(service, service, user, user_cap_slot + 1)],
    );
    history.record_commit(&executor, &mut ledger, t4);
    let t5 = crate::world::bare_turn(
        service,
        nonce(&ledger, &service),
        vec![set_field(service, 0, [7u8; 32])],
    );
    history.record_commit(&executor, &mut ledger, t5);

    (history, ledger, [treasury, service, user])
}

// ===========================================================================
// Tests (headless — `cargo test --features embedded-executor`)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{bare_turn, make_open_cell, transfer};

    /// A small fixture history: two cells + three transfers, recorded.
    fn fixture() -> (History, Ledger, CellId, CellId) {
        let mut h = History::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();
        let a = h.record_genesis(&mut l, make_open_cell(1, 1_000));
        let b = h.record_genesis(&mut l, make_open_cell(2, 0));
        let nonce = |l: &Ledger, id: &CellId| l.get(id).map(|c| c.state.nonce()).unwrap_or(0);
        let t1 = bare_turn(a, nonce(&l, &a), vec![transfer(a, b, 100)]);
        assert!(h.record_commit(&ex, &mut l, t1).is_some());
        let t2 = bare_turn(a, nonce(&l, &a), vec![transfer(a, b, 50)]);
        assert!(h.record_commit(&ex, &mut l, t2).is_some());
        let t3 = bare_turn(b, nonce(&l, &b), vec![transfer(b, a, 30)]);
        assert!(h.record_commit(&ex, &mut l, t3).is_some());
        (h, l, a, b)
    }

    // --- VERIFIED SCRUB ------------------------------------------------------

    #[test]
    fn replay_to_each_step_matches_the_recorded_root() {
        let (h, live, _a, _b) = fixture();
        // 2 genesis + 3 turns = 5 steps.
        assert_eq!(h.len(), 5);
        // Every landing reconstructs to the recorded canonical root tooth.
        for k in 0..=h.len() {
            let rebuilt = h.replay_to(k).expect("replay must verify");
            // The verified replay's own root equals the recorded tooth.
            let mut rebuilt = rebuilt;
            assert_eq!(rebuilt.root(), h.root_at(k), "step {k} root tooth");
        }
        // The head replay reproduces the LIVE ledger exactly (root agreement).
        let mut head = h.replay_to(h.len()).unwrap();
        let mut live = live;
        assert_eq!(head.root(), live.root(), "head replay == live world");
    }

    // --- UMEM-BOUNDARY RESTORE (the live time-scrub path) -------------------

    #[test]
    fn reify_to_restores_via_umem_boundary_and_matches_replay() {
        let (h, live, _a, _b) = fixture();
        assert_eq!(h.len(), 5);
        for k in 0..=h.len() {
            let (mut reified, source) = h.reify_to(k).expect("umem-boundary restore verifies");
            // The live cockpit scrub restores via the UMEM BOUNDARY — the O(1)
            // reify_ledger inverse fold — NOT genesis re-execution.
            assert_eq!(
                source,
                ScrubSource::UmemBoundary,
                "step {k} restored via the umem boundary (the faithful class)"
            );
            // Root-verified: the restored boundary reproduces the recorded tooth…
            assert_eq!(reified.root(), h.root_at(k), "step {k} root tooth");
            // …and equals the independent genesis-replay reconstruction exactly.
            let mut replayed = h.replay_to(k).expect("replay reference");
            assert_eq!(
                reified.root(),
                replayed.root(),
                "step {k}: umem-boundary restore == genesis replay"
            );
        }
        // The head restore reproduces the LIVE ledger (root agreement).
        let (mut head, _) = h.reify_to(h.len()).unwrap();
        let mut live = live;
        assert_eq!(head.root(), live.root(), "head reify == live world");
    }

    #[test]
    fn reify_to_root_tooth_catches_a_tampered_recorded_root() {
        let (mut h, _l, _a, _b) = fixture();
        // Tamper the recorded root tooth at step 3: the umem-boundary restore must
        // refuse it (the reified ledger commits to the honest root, not the forge).
        let forged = {
            let mut r = h.root_at(3);
            r[0] ^= 0xff;
            r
        };
        h.roots[3] = forged;
        assert!(
            matches!(
                h.reify_to(3),
                Err(ReplayError::RootMismatch { step: 3, .. })
            ),
            "a tampered tooth must fail-closed on the umem-boundary restore too"
        );
        // Untampered steps still restore.
        assert!(h.reify_to(2).is_ok());
        assert!(h.reify_to(4).is_ok());
    }

    #[test]
    fn reify_to_out_of_range_is_rejected() {
        let (h, _l, _a, _b) = fixture();
        assert!(matches!(
            h.reify_to(h.len() + 1),
            Err(ReplayError::OutOfRange { .. })
        ));
    }

    #[test]
    fn root_after_carries_committed_teeth_and_none_for_genesis() {
        // The per-step tooth accessor (finding #12): a genesis step carries NO
        // self-contained root (it lives only in History.roots), so `root_after` is
        // `None` — not the old `[0u8; 32]` placeholder that could never equal a real
        // ledger root. A committed step's per-step copy equals the parallel
        // authoritative tooth `History::root_at(k+1)`.
        let (h, _l, _a, _b) = fixture();
        let steps = h.steps();
        assert_eq!(steps.len(), 5);
        // The two genesis installs.
        assert_eq!(steps[0].root_after(), None);
        assert_eq!(steps[1].root_after(), None);
        // The three committed turns: step k's post_root == roots[k + 1].
        for k in 2..steps.len() {
            assert_eq!(
                steps[k].root_after(),
                Some(h.root_at(k + 1)),
                "committed step {k} per-step tooth == History.roots[{}]",
                k + 1
            );
        }
    }

    #[test]
    fn reify_to_trusts_the_co_recorded_pair_a_joint_substitution_replay_to_catches() {
        // HONEST BOUNDARY (finding #16): reify_to root-checks the reified boundary
        // against roots[k], but boundaries[k] and roots[k] are CO-RECORDED post-state
        // artifacts (captured together in record_commit/record_genesis). The check is
        // therefore a round-trip consistency test between two values recorded in
        // lockstep — NOT the re-execution-from-genesis ground truth replay_to
        // enforces. A JOINT substitution of (boundary, root) passes reify_to while
        // replay_to catches it. This test PINS that weaker guarantee.
        let (mut h, _l, _a, _b) = fixture();

        // Substitute step 3's (boundary, root) with step 4's post-state — an
        // internally consistent, faithful-class pair that does NOT match what the
        // first three turns actually compute.
        let mut l4 = h.replay_to(4).expect("honest step-4 replay");
        h.boundaries[3] = project_ledger(&l4);
        h.roots[3] = l4.root();

        // reify_to TRUSTS the co-recorded pair: the reified boundary commits to the
        // (substituted) recorded root, so the restore is ACCEPTED — the honest
        // weakness. It hands back the step-4 ledger for a scrub aimed at step 3.
        let (mut reified, source) = h
            .reify_to(3)
            .expect("reify_to trusts the co-recorded (boundary, root) pair");
        assert_eq!(source, ScrubSource::UmemBoundary);
        assert_eq!(
            reified.root(),
            h.roots[4],
            "reify_to returned the step-4 ledger for a step-3 scrub"
        );

        // replay_to RE-EXECUTES the recorded input turns from genesis and CATCHES the
        // substitution: the honest step-3 root != the substituted tooth (fail-closed).
        assert!(
            matches!(
                h.replay_to(3),
                Err(ReplayError::RootMismatch { step: 3, .. })
            ),
            "replay_to re-derives from inputs and rejects the substitution reify_to accepted"
        );
    }

    #[test]
    fn replay_head_matches_canonical_ledger_root_like_snapshot_rs() {
        // The root tooth IS dregg_cell::Ledger::root — the SAME commitment
        // snapshot.rs binds against (snapshot_ledger_root). Verify the head
        // tooth equals a from-scratch genesis-replay root (the recover ==
        // replay reference).
        let (h, _live, _a, _b) = fixture();
        let mut scratch = Ledger::new();
        let ex = h.fresh_executor();
        for step in h.steps() {
            apply_step(&ex, &mut scratch, step).unwrap();
        }
        assert_eq!(scratch.root(), h.root_at(h.len()));
    }

    // --- checkpoint ⊕ overlay == replay (CrashRecovery identity) -------------

    #[test]
    fn checkpoint_plus_overlay_equals_replay() {
        let (h, _l, _a, _b) = fixture();
        // For every k and every checkpoint at-or-below k, the two
        // decompositions land on the SAME verified root (recover == replay).
        for k in 0..=h.len() {
            for cp in 0..=k {
                let mut via_genesis = h.replay_to(k).unwrap();
                let mut via_cp = h.replay_to_via_checkpoint(k, cp).unwrap();
                assert_eq!(
                    via_genesis.root(),
                    via_cp.root(),
                    "checkpoint {cp} ⊕ overlay != genesis replay at k={k}"
                );
                assert_eq!(via_cp.root(), h.root_at(k));
            }
        }
    }

    // --- the root tooth CATCHES tampering -----------------------------------

    #[test]
    fn a_tampered_recorded_root_fails_the_tooth() {
        let (mut h, _l, _a, _b) = fixture();
        // Tamper the recorded root at step 3 (anti-substitution): replay must
        // refuse it (the reconstructed root won't match the forged tooth).
        let forged = {
            let mut r = h.root_at(3);
            r[0] ^= 0xff;
            r
        };
        h.roots[3] = forged;
        let err = h.replay_to(3);
        assert!(
            matches!(err, Err(ReplayError::RootMismatch { step: 3, .. })),
            "tampered tooth must fail-closed, got {err:?}"
        );
        // Untampered steps still verify.
        assert!(h.replay_to(2).is_ok());
        assert!(h.replay_to(4).is_ok());
    }

    // --- FORK / what-if ------------------------------------------------------

    #[test]
    fn fork_diverges_and_leaves_the_mainline_intact() {
        let (h, _l, a, b) = fixture();
        // Mainline head root before forking.
        let mainline_head = h.root_at(h.len());

        // Branch at step 3 (after t1: a=900,b=100) with a DIFFERENT turn:
        // transfer a bigger amount than the mainline's t2.
        // Step 3 corresponds to "after the first turn" (2 genesis + 1 turn).
        let alt_nonce = h.replay_to(3).unwrap().get(&a).unwrap().state.nonce();
        let alt = bare_turn(a, alt_nonce, vec![transfer(a, b, 777)]);
        let fork = h
            .fork_at(3, alt)
            .expect("fork must replay+verify the branch point");

        assert!(
            fork.outcome.is_committed(),
            "the alt transfer should commit"
        );
        assert!(
            fork.diverged(),
            "a different turn must diverge from the mainline"
        );
        // The divergence names the changed cells (a and b both moved differently).
        let ids = fork.divergence.changed_ids();
        assert!(
            ids.contains(&a) || ids.contains(&b),
            "the fork's diff lists the moved cells"
        );

        // MAINLINE INTACT: the history's recorded roots are unchanged, and a
        // fresh replay still lands on the same head root.
        assert_eq!(h.root_at(h.len()), mainline_head);
        let mut head = h.replay_to(h.len()).unwrap();
        assert_eq!(head.root(), mainline_head);
    }

    #[test]
    fn fork_with_an_identical_turn_does_not_diverge() {
        let (h, _l, a, b) = fixture();
        // Branch at step 3 and apply EXACTLY the mainline's next turn (t2:
        // a→b 50). The fork must NOT diverge from the mainline at step 4.
        let nonce = h.replay_to(3).unwrap().get(&a).unwrap().state.nonce();
        let same = bare_turn(a, nonce, vec![transfer(a, b, 50)]);
        let fork = h.fork_at(3, same).unwrap();
        assert!(fork.outcome.is_committed());
        assert_eq!(
            fork.fork_root, fork.mainline_root,
            "replaying the same turn must match the mainline"
        );
        assert!(!fork.diverged(), "identical turn → no divergence");
    }

    // --- STATE DIFF ----------------------------------------------------------

    #[test]
    fn diff_lists_exactly_the_changed_cells() {
        let (h, _l, a, b) = fixture();
        // Between step 2 (just genesis: a=1000,b=0) and step 3 (after t1:
        // a→b 100), exactly cells a and b changed.
        let d = h.diff(2, 3).unwrap();
        assert_eq!(d.len(), 2, "exactly two cells changed");
        let ids = d.changed_ids();
        assert!(ids.contains(&a));
        assert!(ids.contains(&b));
        // a went 1000→900, b went 0→100.
        for (id, change) in &d.changes {
            if *id == a {
                assert!(matches!(
                    change,
                    CellChange::Changed {
                        balance_before: 1000,
                        balance_after: 900,
                        ..
                    }
                ));
            }
            if *id == b {
                assert!(matches!(
                    change,
                    CellChange::Changed {
                        balance_before: 0,
                        balance_after: 100,
                        ..
                    }
                ));
            }
        }
    }

    #[test]
    fn diff_of_a_step_to_itself_is_empty() {
        let (h, _l, _a, _b) = fixture();
        for k in 0..=h.len() {
            assert!(
                h.diff(k, k).unwrap().is_empty(),
                "step {k} vs itself is empty"
            );
        }
    }

    #[test]
    fn diff_detects_a_created_cell() {
        // Genesis steps create cells: between step 0 (empty) and step 1 (one
        // genesis cell) exactly one cell is Created.
        let (h, _l, _a, _b) = fixture();
        let d = h.diff(0, 1).unwrap();
        assert_eq!(d.len(), 1);
        assert!(matches!(d.changes[0].1, CellChange::Created { .. }));
    }

    // --- the demo history + the panel model ----------------------------------

    #[test]
    fn demo_history_is_fully_replayable_and_verified() {
        let (h, live, [treasury, service, user]) = demo_history();
        // 4 genesis + 5 turns = 9 steps.
        assert_eq!(h.len(), 9);
        // Every step verifies.
        for k in 0..=h.len() {
            assert!(h.replay_to(k).is_ok(), "demo step {k} must verify");
        }
        // Head replay reproduces the live ledger.
        let mut head = h.replay_to(h.len()).unwrap();
        let mut live = live;
        assert_eq!(head.root(), live.root());
        // The flows landed: service got 250_000 + 1_000.
        assert_eq!(head.get(&service).unwrap().state.balance(), 251_000);
        assert!(head.get(&user).unwrap().state.balance() > 0);
        let _ = treasury;
    }

    #[test]
    fn panel_model_builds_a_verified_cursor_and_diff() {
        let (h, _l, _t, _s) = (demo_history().0, (), (), ());
        // Put the cursor mid-history.
        let model = ReplayPanelModel::build(&h, 5, None);
        assert_eq!(model.cursor, 5);
        assert!(
            model.cursor_state.root_verified,
            "cursor reconstruction must verify"
        );
        assert_eq!(model.cursor_state.root, h.root_at(5));
        // The timeline has one entry per landing (len+1).
        assert_eq!(model.timeline.len(), h.len() + 1);
        // The cursor is mid-history so a prev-step diff exists.
        assert!(model.diff_from_prev.is_some());
    }

    #[test]
    fn panel_model_pins_a_fork_summary() {
        let (h, _l, a, b) = fixture();
        let nonce = h.replay_to(3).unwrap().get(&a).unwrap().state.nonce();
        let alt = bare_turn(a, nonce, vec![transfer(a, b, 500)]);
        let fork = h.fork_at(3, alt).unwrap();
        let model = ReplayPanelModel::build(&h, 3, Some(&fork));
        let fs = model.fork.expect("fork pinned");
        assert_eq!(fs.branch_step, 3);
        assert!(fs.committed);
        assert!(fs.diverged);
    }
}
