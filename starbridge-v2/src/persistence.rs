//! Native World persistence — M4 of the reflexive migration.
//!
//! This is the durable-image WELD: it makes a [`crate::world::World`] a durable,
//! rewindable image (close it, reopen it, land exactly where you were) by wiring
//! the ALREADY-BUILT node durability spine — `dregg_persist`'s redb commit log +
//! the checkpoint⊕overlay boot-recovery — onto the single commit seam the World
//! already has (`commit_turn`). It builds NO parallel persistence: every durable
//! call here is a `dregg_persist::PersistentStore` method, and the recovery
//! semantics are byte-identical to the node's (`node/src/state.rs`), so the World
//! INHERITS `CrashRecovery.lean::recover_eq_replay` rather than re-proving it.
//!
//! # What is durable
//!
//! * The **commit log** — one [`dregg_persist::CommitRecord`] per committed turn,
//!   written in ONE redb ACID transaction at `commit_turn` time, carrying the
//!   O(change) `touched_cells` post-state + the canonical post-state root tooth.
//! * The **input turns** — the postcard `Turn` alongside each commit, so the
//!   in-RAM [`crate::replay::History`] can be rebuilt verbatim and `replay_to(k)`
//!   works from ANY k after a reopen (the *rewindable* image, A.4).
//! * The **genesis installs** — the out-of-band genesis path (`install_genesis`,
//!   `set_cell_program`, …) bypasses the executor and emits NO `CommitRecord`, so
//!   each genesis cell is mirrored into a durable genesis table here (SEAM §2):
//!   without this an opened image would miss every genesis cell never later
//!   touched by a turn.
//!
//! # Recovery (the EXACT node recovery — inherits CrashRecovery.lean)
//!
//! [`recover`] runs the identical `node/src/state.rs:676-767` flow:
//!   1. load the latest full ledger checkpoint (or empty),
//!   2. apply the durable commit-log overlay since the checkpoint, last-writer-
//!      wins via [`upsert_cell`] (= `state.rs::upsert_cell`, remove-then-insert),
//!   3. FAIL-CLOSED convergence check: the reconstructed [`canonical_ledger_root`]
//!      MUST equal the root the last committed turn durably recorded, else
//!      [`OpenError::Divergent`] (refuse to open — a divergent image is a
//!      soundness event, exactly as `state.rs:732-754`).
//!
//! Because the overlay semantics are byte-identical (last-writer-wins
//! `upsert_cell` over a checkpoint), the recovered ledger equals the genesis
//! replay (`CrashRecovery.recover_eq_replay`): `World::open` lands on the state
//! `History::replay_to(head)` would.

use std::path::Path;

use dregg_cell::{Cell, Ledger};
use dregg_persist::{CommitRecord, LedgerCheckpoint, PersistentStore, StoreError};
use dregg_turn::turn::{Turn, TurnReceipt};

// NOTE: the recovered committed turns are carried as plain input `Turn`s; the
// in-RAM History/receipts/engine spine is rebuilt by RE-EXECUTING them through
// the SAME embedded executor (History::record_commit), which re-derives the real
// receipts AND re-primes each agent's receipt-chain head for free — so we never
// fabricate or carry a TurnReceipt across the durable boundary.

/// The durable convergence root — re-exported from the SHARED
/// [`dregg_persist::canonical_ledger_root`] (the M4 "shared pub fn lift" tail,
/// LANDED). The byte-for-byte replica that used to live here is RETIRED: the
/// single-image World now calls the SAME implementation as the node durability
/// spine, so there is one source of truth. The construction (domain
/// `"dregg-ledger-root-v2"`, sort-by-id, length-prefix, whole-cell postcard leaves)
/// is unchanged, so the recovered root stays byte-identical to the node's
/// `recovered_ledger_root()` — the fail-closed convergence check is preserved (and
/// covered by `close_and_reopen_restores_the_exact_image`).
///
/// REMAINING (the node lane, not this workspace): node's own `pub(crate)` copy in
/// `blocklace_sync.rs::canonical_ledger_root` is the last caller to migrate onto
/// this shared fn — its edit, the byte-pin unchanged.
pub use dregg_persist::canonical_ledger_root;

/// The METADATA_BYTES config-key prefix for a durably-persisted input `Turn`,
/// keyed by its commit ordinal (zero-padded so lexicographic == numeric order).
/// (A.4: the commit log carries post-state cells + teeth but NOT the input turn;
/// this sibling table carries the replayable input so `History` rebuilds and the
/// image is *rewindable*, not merely *resumable*.)
const TURN_KEY_PREFIX: &str = "sbv2_turn:";
/// The METADATA_BYTES config-key prefix for a durably-persisted genesis cell,
/// keyed by its CELL ID (hex). (SEAM §2: out-of-band genesis installs + in-place
/// genesis-path mutations — `set_cell_program`/`genesis_grant_cap`/
/// `genesis_open_permissions` — emit no `CommitRecord`; this table reconstructs
/// them on open. Keying by id makes a re-record LAST-WRITER-WINS, so an in-place
/// genesis mutation durably overwrites the prior genesis snapshot of that cell.
///
/// ⚠ KNOWN LIMITATION (reproduced + HORIZONLOG'd, 2026-06-20): this is sound ONLY
/// for a genesis-path mutation on a cell that NO committed turn has touched. A
/// mutation AFTER a turn touched the cell would record the post-mutation cell as
/// timeless "genesis", so recovery would re-execute that turn against the poisoned
/// base, diverge, and the fail-closed integrity check would REFUSE the image. To
/// prevent that data-loss-on-reopen, `World::set_cell_program` consults the FAIL-FAST
/// guard `genesis_mutation_would_break_reopen` and REFUSES such a mutation on a
/// durable image (an honest refusal). The sound full fix (which would let it succeed)
/// splits pre-chain vs post-chain genesis-path mutations in the durable log — HORIZONLOG.
/// Tests: `a_mid_session_set_cell_program_on_a_touched_cell_is_refused` (the guard) +
/// `a_genesis_setup_set_cell_program_survives_reopen` (the safe boundary).)
const GENESIS_KEY_PREFIX: &str = "sbv2_genesis:";
/// The config key holding the ordered list of durable genesis cell ids (postcard
/// `Vec<[u8;32]>`) — install order, so recovery reinstalls deterministically.
const GENESIS_ORDER_KEY: &str = "sbv2_genesis_order";
/// The config key holding the durable SESSION RECORD (postcard bytes) for this
/// image — the principal + the granted cap-template / c-list snapshot the login
/// ceremony left, so a relaunch restores the session without re-running the full
/// grant ceremony (SESSION RESUME — Houyhnhnm orthogonal persistence). The session
/// is keyed to the image (one root cell per per-user image), so a single key
/// suffices; logout overwrites it with a REVOKED marker so a revoked session does
/// not silently resume.
const SESSION_KEY: &str = "sbv2_session";

fn turn_key(ordinal: u64) -> String {
    format!("{TURN_KEY_PREFIX}{ordinal:020}")
}

fn genesis_key(id: &[u8; 32]) -> String {
    let hex: String = id.iter().map(|b| format!("{b:02x}")).collect();
    format!("{GENESIS_KEY_PREFIX}{hex}")
}

/// Why opening a durable image failed.
#[derive(Debug)]
pub enum OpenError {
    /// The underlying redb store could not be opened or read.
    Store(StoreError),
    /// FAIL-CLOSED: the reconstructed canonical ledger root did NOT equal the
    /// root the last committed turn durably recorded — a store-integrity event
    /// (e.g. a hand-edited checkpoint cell). The image is REFUSED rather than
    /// served as silently-wrong truth (mirrors `state.rs:732-754`).
    Divergent { got: [u8; 32], expected: [u8; 32] },
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenError::Store(e) => write!(f, "durable store error: {e}"),
            OpenError::Divergent { got, expected } => write!(
                f,
                "recovery convergence FAILED: reconstructed ledger root {} != durably recorded \
                 finalized root {} — refusing to open a divergent image (STORE INTEGRITY EVENT)",
                hex16(got),
                hex16(expected),
            ),
        }
    }
}

impl std::error::Error for OpenError {}

impl From<StoreError> for OpenError {
    fn from(e: StoreError) -> Self {
        OpenError::Store(e)
    }
}

fn hex16(b: &[u8; 32]) -> String {
    b.iter().take(8).map(|x| format!("{x:02x}")).collect()
}

/// The durable backing for a [`crate::world::World`]: the redb commit log +
/// checkpoint store, plus the in-RAM mirror of the durable commit cursor.
///
/// `None`-equivalent (absent) for an ephemeral world (`World::new`/`with_costs`/
/// `fork`); present only for a `World::open`ed image. Every successful
/// `commit_turn` dual-writes here when present.
pub struct WorldPersist {
    store: PersistentStore,
    /// The durable commit ordinal we last wrote (the `expected_ordinal` the next
    /// `commit_finalized_turn` must supply). The store remains the single source
    /// of truth (its torn-state guard re-checks it); this mirrors it for O(1)
    /// dual-write without a read-back.
    cursor: u64,
}

/// The fully-recovered image content `World::open` rebuilds its in-RAM spine on.
pub struct RecoveredImage {
    /// The recovered ledger (checkpoint ⊕ overlay, convergence-verified).
    pub ledger: Ledger,
    /// The durable genesis cells, in install order (for History::record_genesis).
    pub genesis_cells: Vec<Cell>,
    /// The durable input turns, in ordinal order. `World::open` RE-EXECUTES these
    /// through the embedded executor (History::record_commit) to rebuild the
    /// History/receipts/engine spine + re-prime each agent's chain head — the
    /// receipt is re-derived, never carried across the durable boundary (A.4).
    pub committed: Vec<Turn>,
    /// The durable commit cursor (== number of committed turns).
    pub cursor: u64,
}

impl WorldPersist {
    /// Open (or create) the durable store at `path`, mirroring its commit cursor.
    /// Creates the redb file + tables if absent (first run → empty store).
    pub fn open(path: &Path) -> Result<Self, OpenError> {
        let store = PersistentStore::open(path)?;
        let cursor = store.commit_cursor()?;
        Ok(WorldPersist { store, cursor })
    }

    /// The durable commit cursor mirror.
    pub fn cursor(&self) -> u64 {
        self.cursor
    }

    /// Persist a genesis install / in-place genesis mutation (SEAM §2): store the
    /// cell's current post-state under its id (LAST-WRITER-WINS) so recovery
    /// reconstructs it even if no later turn touches it. First write for an id
    /// also appends the id to the install-order list (deterministic recovery
    /// order); a re-record of an existing id just overwrites its snapshot.
    pub fn record_genesis(&self, cell: &Cell) -> Result<(), StoreError> {
        let id = cell.id().0;
        let bytes =
            postcard::to_stdvec(cell).map_err(|e| StoreError::Serialization(e.to_string()))?;
        let mut order = self.genesis_order()?;
        if !order.contains(&id) {
            order.push(id);
            let order_bytes = postcard::to_stdvec(&order)
                .map_err(|e| StoreError::Serialization(e.to_string()))?;
            self.store.set_config(GENESIS_ORDER_KEY, &order_bytes)?;
        }
        self.store.set_config(&genesis_key(&id), &bytes)?;
        Ok(())
    }

    /// Persist the opaque durable SESSION RECORD blob for this image (SESSION
    /// RESUME). Overwrites any prior record (last-writer-wins) — login writes the
    /// granted c-list snapshot; logout overwrites it with a REVOKED marker so a
    /// relaunch does not silently resume a revoked session.
    pub fn put_session(&self, bytes: &[u8]) -> Result<(), StoreError> {
        self.store.set_config(SESSION_KEY, bytes)
    }

    /// The durable SESSION RECORD blob for this image, if one was ever written
    /// (`None` on a fresh image that has never been logged into).
    pub fn get_session(&self) -> Result<Option<Vec<u8>>, StoreError> {
        self.store.get_config(SESSION_KEY)
    }

    fn genesis_order(&self) -> Result<Vec<[u8; 32]>, StoreError> {
        match self.store.get_config(GENESIS_ORDER_KEY)? {
            Some(bytes) => {
                postcard::from_bytes(&bytes).map_err(|e| StoreError::Serialization(e.to_string()))
            }
            None => Ok(Vec::new()),
        }
    }

    /// RECOVER a divergent/torn image to its last root-consistent commit ordinal,
    /// truncating the divergent tail (the [`PersistentStore::recover_to_last_
    /// consistent`] passthrough). Returns the number of divergent records dropped
    /// (0 ⇒ the image was already consistent). After this returns `Ok`, a fresh
    /// [`Self::recover`] converges at the recovered point — so a torn image opens
    /// at its last-good state instead of being refused (the owner is never
    /// stranded). Errs only when NO prefix is salvageable (the caller then offers
    /// "start fresh").
    pub fn recover_to_last_consistent(&self) -> Result<u64, StoreError> {
        self.store.recover_to_last_consistent()
    }

    /// The dual-write at `commit_turn` (A.2) — O(change): build the
    /// [`CommitRecord`] from the already-computed `touched` set's post-states +
    /// the canonical post-state root, commit it in ONE redb txn at the current
    /// cursor, AND persist the input `turn` (A.4) for rewind. Advances the
    /// in-RAM cursor on success.
    ///
    /// FAIL-CLOSED (A.2.1): a durable-write error is returned, NOT swallowed — the
    /// caller turns it into a refused commit so RAM and disk stay in lock-step
    /// (the node's discipline; *Green Or Bust*).
    pub fn dual_write(
        &mut self,
        height: u64,
        ledger: &Ledger,
        touched: &[dregg_cell::CellId],
        receipt: &TurnReceipt,
        turn: &Turn,
    ) -> Result<(), StoreError> {
        // The exact change-set, already in hand: post-state of every touched cell
        // that still exists post-commit (a cell DESTROYED this turn is gone from
        // the ledger, so `filter_map` drops it — matching the node; its removal is
        // carried by the next checkpoint, not the overlay, which only adds).
        let touched_cells: Vec<Cell> = touched
            .iter()
            .filter_map(|id| ledger.get(id).cloned())
            .collect();
        let record = CommitRecord {
            ordinal: 0, // assigned by the store at the cursor
            height,
            block_id: [0u8; 32], // single-image: no consensus anchor
            block_executed_up_to: height,
            turn_hash: receipt.turn_hash,
            creator: *receipt.agent.as_bytes(),
            receipt_hash: receipt.receipt_hash(),
            ledger_root: canonical_ledger_root(ledger),
            touched_cells,
        };
        // Persist the input turn FIRST (under the ordinal this commit will take),
        // so that if the commit txn lands, the turn is already durable; if the
        // turn write fails we abort before advancing the cursor (fail-closed).
        let bytes =
            postcard::to_stdvec(turn).map_err(|e| StoreError::Serialization(e.to_string()))?;
        self.store.set_config(&turn_key(self.cursor), &bytes)?;
        let assigned = self.store.commit_finalized_turn(self.cursor, &record)?;
        self.cursor = assigned + 1;
        Ok(())
    }

    /// Periodic / on-close durable full-ledger checkpoint (C.1): serialize the
    /// whole ledger to redb keyed by `height`, so recovery's overlay
    /// (`cell_overlay_since(height)`) is short. Non-fatal on error (a missed
    /// checkpoint only lengthens the next recovery overlay; the commit log is
    /// already durable).
    ///
    /// IMPORTANT — NO COMPACTION (the rewindable-image tradeoff, NAMED): the
    /// node's `checkpoint_ledger` CO-DRIVES `compact_below`, which DELETES the
    /// commit-log records a checkpoint subsumes. For the single-image World those
    /// records carry the input turns the rewindable `History` replays (A.4), so
    /// compacting them would make `replay_to(k)` for a compacted `k` impossible.
    /// We therefore write a NON-compacting checkpoint (`store_ledger_checkpoint_
    /// snapshot`): the checkpoint still bounds the recovery OVERLAY, while the
    /// commit log (the rewind tape) is retained. Bounding the commit log itself is
    /// the *separate* later move (SEAM §2's collapse) that switches History to a
    /// checkpoint-anchored tape; until then a rewindable image keeps its full tape.
    pub fn checkpoint(&self, ledger: &Ledger, height: u64) {
        let snapshot = LedgerCheckpoint {
            height,
            cells: ledger.iter().map(|(_, c)| c.clone()).collect(),
            sovereign_commitments: ledger
                .iter_sovereign_commitments()
                .map(|(id, c)| (id.0, *c))
                .collect(),
            sovereign_registrations: ledger
                .iter_sovereign_registrations()
                .map(|(id, r)| (id.0, r.clone()))
                .collect(),
        };
        if let Err(e) = self.store.store_ledger_checkpoint_snapshot(&snapshot) {
            eprintln!(
                "[starbridge-v2] durable ledger checkpoint at height {height} failed: {e} \
                 (commit log is durable; recovery overlay stays longer)"
            );
        }
    }

    /// Boot-recovery: run the EXACT node recovery (checkpoint-load → overlay via
    /// last-writer-wins `upsert_cell` → FAIL-CLOSED convergence check via the
    /// canonical root), then load the durable genesis cells + committed turns so
    /// the caller can rebuild the in-RAM History/receipts/chain-heads.
    pub fn recover(&self) -> Result<RecoveredImage, OpenError> {
        // 1. Load the latest full ledger checkpoint (or empty if none yet).
        let (mut ledger, checkpoint_height) = match self.store.load_latest_ledger_checkpoint()? {
            Some((h, l)) => (l, h),
            None => (Ledger::new(), 0),
        };

        // 2. Apply the durable commit-log overlay since the checkpoint, in ordinal
        //    order, LAST-WRITER-WINS (remove-then-insert) — exactly
        //    node::upsert_cell. This is the `recover = checkpoint ⊕ overlay` half.
        let overlay = self.store.cell_overlay_since(checkpoint_height)?;
        for cell in overlay {
            upsert_cell(&mut ledger, cell);
        }

        // 3. Convergence FAIL-CLOSED: the reconstructed canonical root MUST equal
        //    the root the last committed turn durably recorded.
        if let Some(expected) = self.store.recovered_ledger_root()? {
            let got = canonical_ledger_root(&ledger);
            if got != expected {
                return Err(OpenError::Divergent { got, expected });
            }
        }

        // 4. Load the durable genesis cells + committed turns for the in-RAM spine
        //    rebuild. The committed turns carry the input `Turn` (A.4) so History
        //    is rebuildable for rewind, and the `(creator, receipt_hash)` per
        //    ordinal re-derives each agent's chain head.
        let cursor = self.store.commit_cursor()?;
        let genesis_cells = self.load_genesis_cells()?;
        let committed = self.load_committed_turns(cursor)?;

        Ok(RecoveredImage {
            ledger,
            genesis_cells,
            committed,
            cursor,
        })
    }

    fn load_genesis_cells(&self) -> Result<Vec<Cell>, OpenError> {
        let order = self.genesis_order()?;
        let mut out = Vec::with_capacity(order.len());
        for id in &order {
            let bytes = self.store.get_config(&genesis_key(id))?.ok_or_else(|| {
                OpenError::Store(StoreError::Integrity(format!(
                    "durable genesis cell {} missing (corrupt store)",
                    hex16(id)
                )))
            })?;
            let cell: Cell = postcard::from_bytes(&bytes)
                .map_err(|e| StoreError::Serialization(e.to_string()))?;
            out.push(cell);
        }
        Ok(out)
    }

    fn load_committed_turns(&self, cursor: u64) -> Result<Vec<Turn>, OpenError> {
        let mut out = Vec::with_capacity(cursor as usize);
        for ordinal in 0..cursor {
            // The commit record must exist for every ordinal below the cursor (a
            // compacted ordinal — record removed under a covering checkpoint — has
            // no input turn to replay; the single-image World does not compact
            // below its own checkpoints in M4, so a gap here is a real integrity
            // event; the named checkpoint-only history variant of A.4 would
            // instead start History from the checkpoint genesis).
            if self.store.commit_record_at(ordinal)?.is_none() {
                return Err(OpenError::Store(StoreError::Integrity(format!(
                    "commit record at ordinal {ordinal} missing (compacted?) — History rebuild \
                     needs every input turn"
                ))));
            }
            let bytes = self.store.get_config(&turn_key(ordinal))?.ok_or_else(|| {
                OpenError::Store(StoreError::Integrity(format!(
                    "durable input turn {ordinal} missing (corrupt store)"
                )))
            })?;
            let turn: Turn = postcard::from_bytes(&bytes)
                .map_err(|e| StoreError::Serialization(e.to_string()))?;
            out.push(turn);
        }
        Ok(out)
    }
}

/// Last-writer-wins install of a recovery-overlay cell (= `node::upsert_cell`).
///
/// `Ledger::insert_cell` is a STRICT insert (first-writer-wins, keeps the
/// existing cell on a duplicate id) — wrong for recovery, where a cell the
/// checkpoint already holds must be OVERWRITTEN by its later overlay value in
/// ordinal order. The verified recovery model (`CrashRecovery.upd`) is a
/// last-writer-WINS point update: remove-then-insert. Recovery converges to the
/// committing image's finalized root precisely under this semantics.
fn upsert_cell(ledger: &mut Ledger, cell: Cell) {
    let _ = ledger.remove(&cell.id());
    let _ = ledger.insert_cell(cell);
}

// ===========================================================================
// Tests (headless — `cargo test --no-default-features --features embedded-executor`)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{bare_turn, set_program, transfer, World};
    use dregg_cell::CellId;
    use dregg_turn::ComputronCosts;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    /// A unique throwaway redb path under the OS temp dir (no `tempfile` dep).
    fn scratch_path() -> PathBuf {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        std::env::temp_dir().join(format!("sbv2-persist-{pid}-{nanos}-{n}.redb"))
    }

    const TS: i64 = 1_700_000_000;

    /// Build a durable image: genesis (treasury + user) + three committed
    /// transfers. Returns the path and the (treasury, user) ids.
    fn make_durable_image(path: &std::path::Path) -> (CellId, CellId, [u8; 32], usize) {
        let mut w = World::open_with_timestamp(path, ComputronCosts::zero(), TS)
            .expect("fresh open of an empty store");
        assert!(w.is_durable());
        let treasury = w.genesis_cell(0x11, 1_000_000);
        let user = w.genesis_cell(0x33, 5_000);
        for amount in [100u64, 250, 50] {
            let nonce = w
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, amount)]);
            assert!(w.commit_turn(t).is_committed(), "durable commit must land");
        }
        // Flush a checkpoint so recovery exercises checkpoint ⊕ overlay.
        w.checkpoint_now();
        let root = canonical_ledger_root(w.ledger());
        let cells = w.cell_count();
        (treasury, user, root, cells)
        // w dropped here — the redb file persists on disk.
    }

    /// THE NEVER-STRAND TOOTH (the login front door's core, gpui-free): a durable
    /// image with a TORN commit-log tail — a record whose recorded `ledger_root`
    /// does NOT match the reconstruction (a crash mid-write left an inconsistent
    /// tail) — would make `World::open` REFUSE the whole image (`OpenError::
    /// Divergent`), STRANDING the owner. `World::open_recovering` instead truncates
    /// the divergent tail to the last consistent commit and opens at the last-good
    /// state. Recovery succeeds where the clean open refused.
    #[test]
    fn open_recovering_salvages_a_torn_tail_where_plain_open_refuses() {
        let path = scratch_path();
        let (treasury, user, good_root, good_cells) = make_durable_image(&path);

        // Inject a TORN tail: open the store directly and append a commit record at
        // the next ordinal with a BOGUS `ledger_root` (modeling a crash that left a
        // record inconsistent with the post-state it claims). The image now has a
        // divergent head, so the convergence check fails.
        {
            let store = PersistentStore::open(&path).unwrap();
            let cursor = store.commit_cursor().unwrap();
            // Build the bad record off the last good one's coordinates.
            let last = store.commit_record_at(cursor - 1).unwrap().unwrap();
            let mut bad = CommitRecord {
                ordinal: cursor,
                height: last.height + 1,
                block_id: [0u8; 32],
                block_executed_up_to: last.height + 1,
                turn_hash: [0x7e; 32],
                creator: last.creator,
                receipt_hash: [0x7f; 32],
                ledger_root: [0xde; 32], // WRONG root — the tear.
                touched_cells: vec![],
            };
            bad.touched_cells = vec![]; // no cells → reconstruction unchanged, root mismatches
            store.commit_finalized_turn(cursor, &bad).unwrap();
            // store dropped → redb lock released for the reopen below.
        }

        // A clean open REFUSES the torn image (the strand the owner used to hit).
        let refused = World::open_with_timestamp(&path, ComputronCosts::zero(), TS);
        assert!(
            matches!(refused, Err(OpenError::Divergent { .. })),
            "a torn tail must make the CLEAN open refuse (the old strand)"
        );

        // The RECOVERING open salvages it: truncates the torn record, opens at the
        // last-good state — the owner is NOT stranded.
        let (recovered, dropped) =
            World::open_recovering_with_timestamp(&path, ComputronCosts::zero(), TS)
                .expect("open_recovering must salvage a torn tail, never strand");
        assert_eq!(dropped, 1, "exactly the one torn record is truncated");
        assert!(recovered.is_durable());
        // The recovered image is EXACTLY the last-good state.
        assert_eq!(
            canonical_ledger_root(recovered.ledger()),
            good_root,
            "recovered image is the last consistent state"
        );
        assert_eq!(recovered.cell_count(), good_cells);
        assert_eq!(
            recovered.ledger().get(&treasury).unwrap().state.balance(),
            1_000_000 - 100 - 250 - 50
        );
        assert_eq!(
            recovered.ledger().get(&user).unwrap().state.balance(),
            5_000 + 100 + 250 + 50
        );
        let _ = std::fs::remove_file(&path);
    }

    /// `open_recovering` on a CLEAN image is identical to a plain open (0 dropped).
    #[test]
    fn open_recovering_is_a_noop_on_a_clean_image() {
        let path = scratch_path();
        let (_t, _u, root, cells) = make_durable_image(&path);
        let (w, dropped) = World::open_recovering_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("clean image opens");
        assert_eq!(dropped, 0, "a clean image truncates nothing");
        assert_eq!(canonical_ledger_root(w.ledger()), root);
        assert_eq!(w.cell_count(), cells);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn close_and_reopen_restores_the_exact_image() {
        let path = scratch_path();
        let (treasury, user, root_before, cells_before) = make_durable_image(&path);

        // Reopen: the EXACT recovered image.
        let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("reopen must recover (convergence holds)");
        assert!(reopened.is_durable());

        // Roots match (the canonical convergence tooth) ...
        assert_eq!(
            canonical_ledger_root(reopened.ledger()),
            root_before,
            "reopened canonical root must equal the closed image's"
        );
        // ... and every cell matches by id + content.
        assert_eq!(reopened.cell_count(), cells_before, "cell count restored");
        assert_eq!(
            reopened.ledger().get(&treasury).unwrap().state.balance(),
            1_000_000 - 100 - 250 - 50,
            "treasury balance restored exactly"
        );
        assert_eq!(
            reopened.ledger().get(&user).unwrap().state.balance(),
            5_000 + 100 + 250 + 50,
            "user balance restored exactly"
        );

        // The rewindable image: History rebuilt → replay to any past step verifies.
        let h = reopened.recorded_turns();
        for k in 0..=h.len() {
            assert!(
                h.replay_to(k).is_ok(),
                "rewind step {k} verifies after reopen"
            );
        }

        let _ = std::fs::remove_file(&path);
    }

    /// **CORE-AUDIT.md finding 1 — the regression guard.** A committed turn that
    /// CREATES a cell mutates the newborn, a cell the syntactic `touched_cells`
    /// walk over the input turn does NOT enumerate. Before the executor-write-set
    /// fix, `dual_write` recorded the correct canonical post-root over an overlay
    /// that OMITTED the newborn, so recovery — reconstructing checkpoint ⊕ overlay,
    /// with NO checkpoint flushed here so the OVERLAY is the only source — rebuilt
    /// a ledger without the created cell and `World::open` refused a validly
    /// committed image (`OpenError::Divergent`). This proves the newborn now rides
    /// the overlay through a close + reopen. (The desktop's App Shelf / Exchange /
    /// Letter Office all create cells, so this is the durable desktop's real path.)
    #[test]
    fn a_committed_create_cell_survives_reopen_via_the_overlay() {
        let path = scratch_path();
        let (created, root, cells) = {
            let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
                .expect("fresh open of an empty store");
            let treasury = w.genesis_cell(0x11, 1_000_000);
            let before: std::collections::HashSet<CellId> =
                w.ledger().iter().map(|(id, _)| *id).collect();
            // A create-cell turn: the newborn is NOT in `touched_cells(&turn)`.
            let t = w.turn(treasury, vec![crate::world::create_cell(0x77)]);
            assert!(
                w.commit_turn(t).is_committed(),
                "the create-cell turn must commit"
            );
            let created = w
                .ledger()
                .iter()
                .map(|(id, _)| *id)
                .find(|id| !before.contains(id))
                .expect("a cell was born by the committed turn");
            // DELIBERATELY NO checkpoint_now(): recovery must reconstruct from the
            // commit-log OVERLAY (the path the bug corrupted), not a full snapshot.
            (created, canonical_ledger_root(w.ledger()), w.cell_count())
            // w dropped → the redb file persists on disk.
        };

        // The clean open must NOT diverge — the overlay carried the newborn.
        let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("reopen must not diverge — the created cell was recorded in the overlay");
        assert_eq!(
            canonical_ledger_root(reopened.ledger()),
            root,
            "the recovered root equals the committed root"
        );
        assert_eq!(
            reopened.cell_count(),
            cells,
            "cell count (incl. newborn) restored"
        );
        assert!(
            reopened.ledger().contains(&created),
            "the cell created by a committed turn survived the reopen"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_committed_turn_after_reopen_threads_the_chain_head() {
        // The chain-head re-prime: a NEW turn from an agent with durable history
        // must commit (would reject as ReceiptChainMismatch if not re-primed).
        let path = scratch_path();
        let (treasury, user, _root, _cells) = make_durable_image(&path);
        let mut reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS).unwrap();
        let nonce = reopened
            .ledger()
            .get(&treasury)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, 1)]);
        assert!(
            reopened.commit_turn(t).is_committed(),
            "a post-reopen turn must thread the re-primed chain head and commit"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_genesis_setup_set_cell_program_survives_reopen() {
        // THE SAFE BOUNDARY (the companion to the #[ignore]'d after-turn bug): a
        // `set_cell_program` at genesis SETUP — before the cell's first turn — DOES
        // survive close+reopen, because the genesis-mirror snapshot IS the cell's
        // pre-turn base, so recovery's turn re-execution sees the right program. This
        // pins the exact line: genesis-setup mutations are sound; post-turn ones are
        // the bug. (The predicate composer / organ setup are safe iff they program a
        // cell before any turn touches it.)
        use dregg_cell::CellProgram;
        let path = scratch_path();
        let cell_id;
        {
            let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
                .expect("fresh open of an empty store");
            let treasury = w.genesis_cell(0x11, 1_000);
            let user = w.genesis_cell(0x33, 0);
            // Program the user cell at SETUP — before any turn touches it.
            assert!(
                w.set_cell_program(&user, CellProgram::Predicate(vec![])),
                "genesis-setup set_cell_program succeeds"
            );
            // THEN commit a turn that does NOT mutate the programmed cell's program
            // (a transfer crediting it — its program is unchanged by the credit).
            let nonce = w
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, 100)]);
            assert!(w.commit_turn(t).is_committed(), "the turn commits");
            cell_id = user;
            // w dropped — the redb file persists.
        }
        let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("reopen recovers (the setup program is in the pre-turn base)");
        let prog = reopened
            .ledger()
            .get(&cell_id)
            .expect("cell restored")
            .program
            .clone();
        assert_eq!(
            prog,
            CellProgram::Predicate(vec![]),
            "a genesis-SETUP program survives reopen (the safe boundary)"
        );
    }

    /// THE FAIL-FAST GUARD for the genesis-mirror-after-turn durability bug (found
    /// 2026-06-20; HORIZONLOG). A genesis-path mutation (`set_cell_program` —
    /// reachable mid-session via the interactive predicate composer + organ setup) on
    /// a cell that a COMMITTED TURN already touched would make the durable image
    /// NON-REOPENABLE (the post-mutation cell, recorded as timeless "genesis", poisons
    /// recovery's re-execution of that turn). The guard
    /// (`World::genesis_mutation_would_break_reopen`) REFUSES it — an honest refusal
    /// rather than silent data-loss-on-reopen; the image stays clean. (The sound full
    /// fix — ordered pre/post-chain genesis events in the durable log — would instead
    /// make it SUCCEED + survive; HORIZONLOG.)
    #[test]
    fn a_mid_session_set_cell_program_on_a_touched_cell_is_refused() {
        use dregg_cell::CellProgram;
        let path = scratch_path();
        {
            let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
                .expect("fresh open of an empty store");
            let treasury = w.genesis_cell(0x11, 1_000);
            let user = w.genesis_cell(0x33, 0);
            let nonce = w
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, 100)]);
            assert!(
                w.commit_turn(t).is_committed(),
                "the mid-session turn commits"
            );
            // treasury was TOUCHED by the transfer → the guard refuses the program-set
            // (it would otherwise make the durable image non-reopenable).
            assert!(
                !w.set_cell_program(&treasury, CellProgram::Predicate(vec![])),
                "a genesis-path mutation on a turn-touched cell is refused (durable image)"
            );
            // The refusal did not partially apply — the program stays at the default.
            assert_eq!(
                w.ledger().get(&treasury).unwrap().program,
                CellProgram::None,
                "the refused mutation left the cell's program untouched"
            );
            // w dropped — the redb file persists on disk.
        }
        // The image reopens CLEANLY — the guard prevented the corrupting mutation.
        let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("reopen is clean — the guard prevented the non-reopenable image");
        assert!(reopened.is_durable());
    }

    /// THE ROOT FIX (the category error dissolved): a mid-session program change
    /// RIDDEN AS AN ORDERED `SetProgram` TURN survives close+reopen — where the
    /// out-of-band genesis-path `set_cell_program` mutation would have poisoned
    /// recovery (the guard above refuses that). The reprogram is now part of the
    /// durable COMMIT LOG (a `RecordedStep::Committed`), so recovery re-executes it
    /// in order and the recovered cell carries the new program. Runtime
    /// customization is an ordered turn, not timeless genesis.
    #[test]
    fn a_mid_session_set_program_turn_survives_reopen() {
        use dregg_cell::CellProgram;
        let path = scratch_path();
        let cell_id;
        {
            let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
                .expect("fresh open of an empty store");
            let treasury = w.genesis_cell(0x11, 1_000);
            let user = w.genesis_cell(0x33, 0);
            // A turn TOUCHES the user cell mid-session (the credit).
            let nonce = w
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, 100)]);
            assert!(
                w.commit_turn(t).is_committed(),
                "the mid-session turn commits"
            );
            // NOW reprogram the ALREADY-TOUCHED cell — but as an ORDERED `SetProgram`
            // turn (self-targeted on the user cell, whose open permissions gate the
            // program install). This is the redirect the genesis-path mutation used
            // to do unsoundly.
            let prog_turn = w.turn(
                user,
                vec![set_program(user, CellProgram::Predicate(vec![]))],
            );
            assert!(
                w.commit_turn(prog_turn).is_committed(),
                "the mid-session SetProgram turn commits"
            );
            assert_eq!(
                w.ledger().get(&user).unwrap().program,
                CellProgram::Predicate(vec![]),
                "the live cell carries the new program"
            );
            cell_id = user;
            // w dropped — the redb file persists.
        }
        // Reopen REPRODUCES the reprogram (it is in the durable commit log, NOT a
        // timeless genesis fact) — the durability bug is fixed AT ITS ROOT.
        let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("reopen recovers — the reprogram rode the commit log, in order");
        assert_eq!(
            reopened
                .ledger()
                .get(&cell_id)
                .expect("cell restored")
                .program,
            CellProgram::Predicate(vec![]),
            "a mid-session SetProgram TURN survives reopen (the category error dissolved)"
        );
        // And the rewindable history replays cleanly at every step.
        let h = reopened.recorded_turns();
        for k in 0..=h.len() {
            assert!(
                h.replay_to(k).is_ok(),
                "rewind step {k} verifies after reopen"
            );
        }
        let _ = std::fs::remove_file(&path);
    }

    /// The same fail-fast guard covers the OTHER two genesis-path mutators
    /// (`genesis_grant_cap` + `genesis_open_permissions`) — they too would make the
    /// durable image non-reopenable on a turn-touched cell, so they refuse it.
    #[test]
    fn the_sibling_genesis_path_mutators_are_also_guarded_on_a_touched_cell() {
        let path = scratch_path();
        let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), TS)
            .expect("fresh open of an empty store");
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x33, 0);
        let nonce = w
            .ledger()
            .get(&treasury)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let t = bare_turn(treasury, nonce, vec![transfer(treasury, sink, 100)]);
        assert!(
            w.commit_turn(t).is_committed(),
            "the mid-session turn commits"
        );
        // treasury was TOUCHED by the transfer → both genesis-path mutators refuse.
        assert_eq!(
            w.genesis_grant_cap(&treasury, sink),
            None,
            "genesis_grant_cap on a turn-touched holder is refused (durable image)"
        );
        assert!(
            !w.genesis_open_permissions(&treasury),
            "genesis_open_permissions on a turn-touched cell is refused (durable image)"
        );
        // A FRESH cell (never touched by a turn) is still mutable at setup — the guard
        // is narrow (only the unsafe post-turn case), not a blanket refusal.
        let fresh = w.genesis_cell(0x44, 0);
        assert!(
            w.genesis_grant_cap(&fresh, sink).is_some(),
            "a fresh untouched cell can still receive a genesis grant"
        );
    }

    #[test]
    fn fork_of_a_durable_world_never_persists() {
        let path = scratch_path();
        let (treasury, user, _root, _cells) = make_durable_image(&path);
        // Open, fork, commit on the fork, then DROP the open handle — redb holds a
        // single-writer lock per file, so the second reopen must come after the
        // first handle is released (a real desktop never opens the same image
        // twice concurrently either).
        {
            let reopened = World::open_with_timestamp(&path, ComputronCosts::zero(), TS).unwrap();
            let mut fork = reopened.fork();
            assert!(!fork.is_durable(), "a fork MUST be ephemeral");
            let nonce = fork
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = bare_turn(treasury, nonce, vec![transfer(treasury, user, 999)]);
            assert!(fork.commit_turn(t).is_committed());
            // reopened + fork drop here, releasing the redb handle.
        }
        // The fork's commit must NOT have advanced the durable cursor: a SECOND
        // reopen lands on the same (pre-fork) image.
        let reopened2 = World::open_with_timestamp(&path, ComputronCosts::zero(), TS).unwrap();
        assert_eq!(
            reopened2.ledger().get(&treasury).unwrap().state.balance(),
            1_000_000 - 100 - 250 - 50,
            "the fork's commit must NOT have touched the durable image"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_corrupt_checkpoint_refuses_to_open_fail_closed() {
        // NON-VACUITY: prove the convergence assertion fires on a genuinely
        // corrupt store (true) — the companion of the passing-on-genuine case
        // above (false). Tamper a checkpoint cell so checkpoint ⊕ overlay no
        // longer reconstructs the durably recorded root → OpenError::Divergent.
        let path = scratch_path();
        let (treasury, _user, _root, _cells) = make_durable_image(&path);

        // Open the store directly and overwrite the checkpoint with a TAMPERED
        // ledger (a hand-edited treasury balance). The commit log still records
        // the TRUE root, so recovery's convergence check must catch the mismatch.
        {
            let store = PersistentStore::open(&path).unwrap();
            let (cp_height, ledger) = store
                .load_latest_ledger_checkpoint()
                .unwrap()
                .expect("a checkpoint was flushed");
            let mut tampered = ledger;
            // Forge the treasury balance in the checkpoint.
            if let Some(c) = tampered.get_mut(&treasury) {
                c.state.set_balance(424_242);
            }
            store.checkpoint_ledger(&tampered, cp_height).unwrap();
        }

        let result = World::open_with_timestamp(&path, ComputronCosts::zero(), TS);
        // `World` is not `Debug`; classify the outcome to a printable string.
        let outcome = match &result {
            Ok(_) => "Ok(World) — opened a CORRUPT image (soundness failure)".to_string(),
            Err(e) => format!("Err({e})"),
        };
        assert!(
            matches!(result, Err(OpenError::Divergent { .. })),
            "a corrupt checkpoint must REFUSE to open (fail-closed), got {outcome}"
        );
        let _ = std::fs::remove_file(&path);
    }
}
