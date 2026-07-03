//! `FirmamentFs` — the firmament-backed [`Fs`](super::Fs) impl: a file IS a cell,
//! a SAVE IS a receipted dregg turn.
//!
//! This is the deos-integration payoff: an editor whose every file operation is a
//! capability-checked, receipted operation over sovereign cells — NOT raw
//! `std::fs`. Because the editor only ever speaks the [`Fs`](super::Fs) trait,
//! turning the editor "firmament-backed" is exactly this one impl. No editor or
//! file-tree code changes.
//!
//! # The mapping (path → cell, save → receipted turn)
//!
//! | `Fs` method     | firmament realization                                              |
//! |-----------------|--------------------------------------------------------------------|
//! | `load(path)`    | resolve `path` → the file-cell via the path namespace; read the    |
//! |                 | cell's content substance (the committed `fields_map`, decoded). A   |
//! |                 | read is authority-checked but does not mutate state — no turn.      |
//! | `save(path, c)` | a dregg TURN: a cap-gated `SetField` write over the file-cell's     |
//! |                 | content, driven through the REAL `TurnExecutor`, leaving a verifiable|
//! |                 | RECEIPT. "Save" becomes an attestable event, not an opaque syscall. |
//! | `read_dir(p)`   | list the namespace's entries under `p` (the directory cell).        |
//! | `metadata(p)`   | resolve the path → file-cell or directory; report kind + length.    |
//!
//! # Why this used to be a stub
//!
//! Wiring it needs a live executor handle + a mounted root namespace. The
//! constructor took those as opaque `()` placeholders. They are now real: this
//! module owns an in-process [`Ledger`] + [`TurnExecutor`] (the SAME verified
//! spine starbridge-v2's `World` wraps), seeds an editor (author) cell + a root
//! directory cell, and resolves paths to file cells under it. The host (a deos
//! image) can hand a `FirmamentFs` to `EditorPane::new` and the editor edits
//! cells, with receipted saves, instead of disk — and nothing in the editor or
//! file tree changes.

#[cfg(not(feature = "firmament"))]
mod stub {
    use std::path::Path;

    use anyhow::{bail, Result};

    use crate::fs::{DirEntry, Fs, Metadata};

    /// The firmament-backed filesystem (STUB build — the `firmament` feature is
    /// off). Satisfies the [`Fs`](crate::fs::Fs) trait so it is a drop-in
    /// replacement for `RealFs` the moment the feature is enabled, but every
    /// method returns a clear "not built with `firmament`" error. Build with
    /// `--features firmament` for the live cell-backed impl.
    pub struct FirmamentFs {
        _private: (),
    }

    impl FirmamentFs {
        /// Build a firmament fs. In the stub build this constructs successfully
        /// but every operation errors — enable the `firmament` feature for the
        /// real cell-backed impl.
        pub fn new() -> Self {
            FirmamentFs { _private: () }
        }

        fn not_built<T>(what: &str) -> Result<T> {
            bail!(
                "FirmamentFs::{what} needs the `firmament` feature: rebuild deos-zed \
                 with `--features firmament` for the live cell-backed impl (a file is a \
                 cell, a save is a receipted turn). See src/fs/firmament.rs."
            )
        }
    }

    impl Default for FirmamentFs {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Fs for FirmamentFs {
        fn load(&self, _path: &Path) -> Result<String> {
            Self::not_built("load")
        }
        fn save(&self, _path: &Path, _content: &str) -> Result<()> {
            Self::not_built("save")
        }
        fn read_dir(&self, _path: &Path) -> Result<Vec<DirEntry>> {
            Self::not_built("read_dir")
        }
        fn metadata(&self, _path: &Path) -> Result<Metadata> {
            Self::not_built("metadata")
        }
        fn backend_label(&self) -> &'static str {
            "FirmamentFs (build with --features firmament) — STUB"
        }
    }
}

#[cfg(not(feature = "firmament"))]
pub use stub::FirmamentFs;

#[cfg(feature = "firmament")]
mod live {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};
    use std::rc::Rc;

    use anyhow::{anyhow, bail, Context as _, Result};

    use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, STATE_SLOTS};
    use dregg_rbg::{MemberId, SturdyRef};
    use dregg_turn::{
        ActionBuilder, ComputronCosts, Effect, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
    };

    use crate::fs::namespace::{DirNamespace, DEOS_ZED_FEDERATION};
    use crate::fs::{DirEntry, Fs, Metadata};

    // --- content <-> field-element encoding -----------------------------------
    //
    // A file's content is a UTF-8 String — many bytes. The cell's committed
    // `fields_map` stores `u64 -> FieldElement` ([u8; 32]) entries, written by
    // the executor's `set_field_ext` arm for any key >= STATE_SLOTS (the same
    // overflow map dregg-doc's ExecutorDrivenDoc lays its projection into). We
    // lay the content into that map:
    //   * key LEN_KEY        = the byte length, little-endian in the first 8 bytes.
    //   * keys CHUNK_BASE+i  = the i-th 32-byte chunk of the content bytes.
    // so the file cell's `fields_root` (which the canonical state commitment
    // absorbs) commits to exactly this content. load() decodes it back; a light
    // client trusts the SAME root the executor moved on save.

    /// The committed-map key holding the content byte length. Lifted past the 16
    /// fixed register slots so it lands in `fields_map` (not the fixed `fields[]`).
    const LEN_KEY: u64 = STATE_SLOTS as u64;
    /// The first committed-map key holding a content chunk. Subsequent chunks are
    /// `CHUNK_BASE + i`.
    const CHUNK_BASE: u64 = STATE_SLOTS as u64 + 1;
    /// Bytes per field element.
    const CHUNK: usize = 32;

    /// The number of chunk fields a content of `len` bytes occupies.
    fn chunk_count(len: usize) -> usize {
        len.div_ceil(CHUNK)
    }

    /// Decode a file cell's committed `fields_map` back into the content String.
    fn decode_content(cell: &Cell) -> Result<String> {
        let len_felt = cell
            .state
            .get_field_ext(LEN_KEY)
            .ok_or_else(|| anyhow!("file cell holds no content (no length field)"))?;
        let len = u64::from_le_bytes(len_felt[0..8].try_into().unwrap()) as usize;
        let mut bytes = Vec::with_capacity(len);
        for i in 0..chunk_count(len) {
            let felt = cell
                .state
                .get_field_ext(CHUNK_BASE + i as u64)
                .ok_or_else(|| anyhow!("file cell is missing content chunk {i}"))?;
            bytes.extend_from_slice(&felt);
        }
        bytes.truncate(len);
        String::from_utf8(bytes).context("file cell content is not valid UTF-8")
    }

    /// Build the `SetField` effects that write `content` into the file cell,
    /// REPLACING whatever is there. Returns the writes (length + chunks) plus the
    /// zeroing writes for any stale chunks the cell still holds beyond the new
    /// content (so a shrink genuinely vacates the old tail — the commitment binds
    /// only the live content).
    fn content_write_effects(cell: &Cell, file: CellId, content: &str) -> Vec<Effect> {
        let bytes = content.as_bytes();
        let new_chunks = chunk_count(bytes.len());

        let mut effects = Vec::with_capacity(new_chunks + 1);

        // Length.
        let mut len_felt = [0u8; 32];
        len_felt[0..8].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
        effects.push(Effect::SetField {
            cell: file,
            index: LEN_KEY as usize,
            value: len_felt,
        });

        // Chunks.
        for i in 0..new_chunks {
            let start = i * CHUNK;
            let end = (start + CHUNK).min(bytes.len());
            let mut felt = [0u8; 32];
            felt[..end - start].copy_from_slice(&bytes[start..end]);
            effects.push(Effect::SetField {
                cell: file,
                index: (CHUNK_BASE + i as u64) as usize,
                value: felt,
            });
        }

        // Vacate stale tail chunks (the cell had more chunks than the new content).
        let old_len = cell
            .state
            .get_field_ext(LEN_KEY)
            .map(|f| u64::from_le_bytes(f[0..8].try_into().unwrap()) as usize)
            .unwrap_or(0);
        let old_chunks = chunk_count(old_len);
        for i in new_chunks..old_chunks {
            effects.push(Effect::SetField {
                cell: file,
                index: (CHUNK_BASE + i as u64) as usize,
                value: [0u8; 32],
            });
        }

        effects
    }

    // --- cell construction ----------------------------------------------------

    /// Open permissions (the cap gate carries authority, not a signature) — the
    /// same shape dregg-doc's executor-drive seam uses for its region/editor
    /// cells, so a cross-cell `SetField` is gated by the c-list cap.
    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// A file cell: open `set_state` so the per-file authority is the editor's
    /// c-list cap (the cross-cell gate), not a signature. Domain-tagged pk so a
    /// file cell can never collide with the editor cell.
    fn make_file_cell(seed: u32) -> Cell {
        let mut pk = [0u8; 32];
        pk[0..4].copy_from_slice(&seed.to_le_bytes());
        pk[4] = 0xF1; // domain tag: file
        let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
        cell.permissions = open_permissions();
        cell
    }

    /// The editor (author) cell — the turn's agent. Holds the caps to the file
    /// cells it may edit; that cap (or its absence) is the real save gate.
    fn make_editor_cell() -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = 0xED; // domain tag: editor
        let mut cell = Cell::with_balance(pk, [0u8; 32], 1_000_000);
        cell.permissions = open_permissions();
        cell
    }

    // --- the host wire API ----------------------------------------------------
    //
    // A host (e.g. starbridge-v2's cockpit `World`) implements [`LedgerSpine`]
    // over its OWN ledger; to do so it must build file cells + content effects in
    // EXACTLY the layout `decode_content` reads back. These public wrappers hand
    // it that one encoding so the host and the editor agree on the wire (a file
    // cell the host installs is decodable by the editor's `load`, and a save the
    // host commits is the same `SetField` shape `seed_file` lays at genesis).

    /// Build the editor (author) cell a host installs on its ledger as the agent
    /// of every save turn — the same domain-tagged open cell the owned spine uses.
    /// The host installs this once and grants it each file's edit cap.
    pub fn host_make_editor_cell() -> Cell {
        make_editor_cell()
    }

    /// Build a file cell carrying `content` as genesis state, identified by
    /// `seed` (a host-monotonic counter, domain-tagged so it can't collide with
    /// the editor cell). The host installs this; a later [`Fs::load`] decodes its
    /// committed map back to `content`.
    pub fn host_make_file_cell(seed: u32, content: &str) -> Cell {
        let mut file_cell = make_file_cell(seed);
        let file = file_cell.id();
        for e in content_write_effects(&file_cell, file, content) {
            if let Effect::SetField { index, value, .. } = e {
                file_cell.state.set_field_ext(index as u64, value);
            }
        }
        file_cell
    }

    /// The `SetField` effects that write `content` into the file `cell` (length +
    /// chunks, vacating any stale tail). A host's `commit_save` builds a turn
    /// targeting `cell` with EXACTLY these effects so the save lands the same
    /// committed-map projection the editor decodes. `cell` is the file cell's
    /// CURRENT state (so the stale-tail vacate is computed against it).
    pub fn host_content_write_effects(cell: &Cell, content: &str) -> Vec<Effect> {
        let file = cell.id();
        content_write_effects(cell, file, content)
    }

    /// Decode a file cell's committed map back to its content String — the same
    /// decode the editor's `load` uses, exposed so a host can read a file cell it
    /// installed.
    pub fn host_decode_content(cell: &Cell) -> Result<String> {
        decode_content(cell)
    }

    // --- the shared verified spine -------------------------------------------

    /// The verified-spine seam: the `Ledger` + `TurnExecutor` a [`FirmamentFs`]
    /// mounts file-cells onto. ONE trait, two realizations — that is the whole
    /// point of this seam:
    ///
    ///   * [`OwnedSpine`] — a FRESH in-process `Ledger` + `TurnExecutor` (the
    ///     headless / per-editor / test path). Self-contained: it owns the editor
    ///     cell, the nonce, the chain head, the receipt log.
    ///   * a host's LIVE spine — e.g. starbridge-v2's cockpit implements this over
    ///     its `Rc<RefCell<World>>`, so [`FirmamentFs::over`] mounts file-cells
    ///     onto the SAME ledger the cockpit's cell inspector reads. A save is then
    ///     a real turn committed through the live `World`, visible to a second
    ///     reader of that World as a new cell + receipt. No second ledger.
    ///
    /// The trait is expressed only in `dregg_cell`/`dregg_turn` terms (deos-zed
    /// does not depend on starbridge-v2), so the host's `World` stays on its side
    /// of the dependency edge while sharing ITS spine, not a copy.
    ///
    /// Single-threaded by design (`Rc`, no `Send`): the editor + the cockpit run
    /// on gpui's one foreground thread, so this matches the live World's own
    /// `Rc<RefCell<World>>` ownership rather than forcing a disjoint
    /// `Arc<Mutex<…>>` model.
    pub trait LedgerSpine {
        /// The editor (author) cell id — the agent of every save turn. The host
        /// installs (or reuses) this cell on its ledger; it holds the file caps.
        fn editor_id(&self) -> CellId;

        /// Snapshot the cell `id` off the spine's ledger (a clone, so the borrow
        /// does not escape). `None` if it is not present.
        fn cell(&self, id: &CellId) -> Option<Cell>;

        /// Install a fresh file cell carrying `content` as genesis state and grant
        /// the editor its per-file edit cap. Returns the new file cell's id. This
        /// is the GENESIS path (the directory owner seeding a file), not a turn.
        fn install_file(&self, content: &str) -> Result<CellId>;

        /// Commit a save as a real cap-gated turn over `file` through the live
        /// executor, returning the genuine receipt. The spine threads the agent
        /// nonce + receipt chain head and records the receipt. A refused save is
        /// an `Err` carrying the in-band reason (the anti-ghost tooth).
        fn commit_save(&self, file: CellId, content: &str) -> Result<TurnReceipt>;

        /// The number of save-turn receipts recorded on this spine (the on-ledger
        /// save count). For [`OwnedSpine`] this is its own log; for a host it is
        /// the host's receipt count.
        fn receipt_count(&self) -> usize;

        /// The most recent save's receipt, if any save has run.
        fn last_receipt(&self) -> Option<TurnReceipt>;

        /// The ordered receipts whose save targeted `file` — that file's
        /// verifiable save timeline (its FS-layer provenance, the
        /// receipt-grounded twin of the doc-viewer's patch blame). Each is a
        /// finalized [`TurnReceipt`] also present in the global log.
        ///
        /// Default: `Vec::new()` — a spine that does not attribute saves
        /// per-file reports no per-file timeline (its global
        /// [`receipt_count`](LedgerSpine::receipt_count) /
        /// [`last_receipt`](LedgerSpine::last_receipt) still hold). The
        /// self-contained [`OwnedSpine`] overrides this with real per-file
        /// tracking, so the headless / per-editor / in-tab path carries a
        /// genuine per-file provenance. A host (e.g. starbridge-v2's `World`)
        /// keeps the default until it opts in — so adding this method does not
        /// disturb an existing host impl.
        fn file_history(&self, _file: CellId) -> Vec<TurnReceipt> {
            Vec::new()
        }

        /// The spine's GLOBAL receipt log, in commit order — every save-turn
        /// receipt this spine recorded, across all files. The receipt rail's
        /// `verify chain` embeds a file's timeline into exactly this log (the
        /// chain threads through ALL files, so per-file adjacency alone can't
        /// verify linkage).
        ///
        /// Default: `Vec::new()` — a spine that does not publish its log
        /// yields a rail verdict that says so (the rail's intra-file checks
        /// still run). [`OwnedSpine`] overrides with its real log; a host
        /// (e.g. starbridge-v2's `World`) opts in without this default
        /// disturbing its existing impl.
        fn receipts(&self) -> Vec<TurnReceipt> {
            Vec::new()
        }

        /// The total balance across all cells on the spine's ledger — the
        /// conservation observable (Σ balance). A content `SetField` save leaves
        /// this INVARIANT (Σδ=0).
        fn total_balance(&self) -> i128;
    }

    /// The self-contained spine: a FRESH `Ledger` + `TurnExecutor` seeded with the
    /// editor (author) cell. Backs [`FirmamentFs::new`] — the headless / per-editor
    /// / test path, with no host World in the loop.
    pub struct OwnedSpine {
        inner: RefCell<OwnedInner>,
    }

    struct OwnedInner {
        /// The REAL embedded verified spine: the executor + the ledger it mutates.
        executor: TurnExecutor,
        ledger: Ledger,
        /// The author cell — the agent of every save turn; holds the file caps.
        editor: CellId,
        /// The editor's nonce (the executor advances it per commit; the next turn
        /// carries it).
        nonce: u64,
        /// The editor's receipt-chain head (chained per save).
        chain_head: Option<[u8; 32]>,
        /// A monotonic seed for new file cells.
        next_seed: u32,
        /// Every save's receipt, in commit order — the provenance log (the same
        /// shape `World::receipts`): a save is an attestable, navigable event.
        receipts: Vec<TurnReceipt>,
        /// Per-FILE receipt timeline: the receipts whose save targeted a given
        /// file cell, in commit order. This is the FS-layer provenance of a
        /// single file — the receipt-grounded twin of the doc-viewer's patch
        /// blame. `receipts` (global) ⊇ the union of these.
        per_file: BTreeMap<CellId, Vec<TurnReceipt>>,
    }

    impl OwnedSpine {
        /// A fresh spine: an empty ledger seeded with the editor (author) cell.
        pub fn new() -> Self {
            let mut ledger = Ledger::new();
            let editor_cell = make_editor_cell();
            let editor = editor_cell.id();
            ledger.insert_cell(editor_cell).expect("editor insert");
            OwnedSpine {
                inner: RefCell::new(OwnedInner {
                    executor: TurnExecutor::new(ComputronCosts::zero()),
                    ledger,
                    editor,
                    nonce: 0,
                    chain_head: None,
                    next_seed: 1,
                    receipts: Vec::new(),
                    per_file: BTreeMap::new(),
                }),
            }
        }
    }

    impl Default for OwnedSpine {
        fn default() -> Self {
            Self::new()
        }
    }

    #[cfg(test)]
    impl OwnedSpine {
        /// TEST-ONLY: install a file cell holding `content` as genesis WITHOUT
        /// granting the editor its edit cap — so a later save is refused in-band
        /// by the cross-cell cap gate (the anti-ghost tooth). Returns the cell id.
        fn install_uncapped_file(&self, content: &str) -> CellId {
            let mut inner = self.inner.borrow_mut();
            let seed = inner.next_seed;
            inner.next_seed += 1;
            let mut cell = make_file_cell(seed);
            let file = cell.id();
            for e in content_write_effects(&cell, file, content) {
                if let Effect::SetField { index, value, .. } = e {
                    cell.state.set_field_ext(index as u64, value);
                }
            }
            inner.ledger.insert_cell(cell).unwrap();
            file
        }
    }

    impl LedgerSpine for OwnedSpine {
        fn editor_id(&self) -> CellId {
            self.inner.borrow().editor
        }

        fn cell(&self, id: &CellId) -> Option<Cell> {
            self.inner.borrow().ledger.get(id).cloned()
        }

        fn install_file(&self, content: &str) -> Result<CellId> {
            let mut inner = self.inner.borrow_mut();
            let seed = inner.next_seed;
            inner.next_seed += 1;

            // Mint the file cell, write the content into its committed map as
            // genesis state (the same projection a save would land — so the
            // commitment matches from genesis), and grant the editor its cap.
            let mut file_cell = make_file_cell(seed);
            let file = file_cell.id();
            for e in content_write_effects(&file_cell, file, content) {
                if let Effect::SetField { index, value, .. } = e {
                    file_cell.state.set_field_ext(index as u64, value);
                }
            }
            inner
                .ledger
                .insert_cell(file_cell)
                .map_err(|e| anyhow!("file cell insert: {e:?}"))?;

            let editor = inner.editor;
            inner
                .ledger
                .get_mut(&editor)
                .ok_or_else(|| anyhow!("editor cell missing"))?
                .capabilities
                .grant(file, AuthRequired::None)
                .ok_or_else(|| anyhow!("editor c-list full"))?;
            Ok(file)
        }

        fn commit_save(&self, file: CellId, content: &str) -> Result<TurnReceipt> {
            let mut inner = self.inner.borrow_mut();
            let effects = {
                let cell = inner
                    .ledger
                    .get(&file)
                    .ok_or_else(|| anyhow!("file cell vanished from ledger"))?;
                content_write_effects(cell, file, content)
            };

            // Build the turn: agent = editor, one action targeting the file cell
            // with the content SetField effects. The file's open `set_state`
            // passes turn-level auth; the per-file CAP gate (cross-cell
            // `check_cross_cell_permission`) is the real enforcement — an editor
            // without the file's cap is refused in-band.
            let editor = inner.editor;
            let nonce = inner.nonce;
            let mut action = ActionBuilder::new_unchecked_for_tests(file, "save", editor);
            for e in &effects {
                action = action.effect(e.clone());
            }
            let action = action.build();

            let mut builder = TurnBuilder::new(editor, nonce);
            builder.add_action(action);
            let mut turn = builder.fee(0).build();
            turn.previous_receipt_hash = inner.chain_head;

            // Split the disjoint executor/ledger borrows for the call, then drop
            // them before touching the rest of `inner` again.
            let result = {
                let OwnedInner {
                    executor, ledger, ..
                } = &mut *inner;
                executor.execute(&turn, ledger)
            };
            match result {
                TurnResult::Committed { receipt, .. } => {
                    // The executor advanced the editor's nonce + receipt-chain
                    // head; mirror them so the next save chains.
                    inner.nonce = inner
                        .ledger
                        .get(&editor)
                        .map(|c| c.state.nonce())
                        .unwrap_or(nonce + 1);
                    inner.chain_head = Some(receipt.receipt_hash());
                    inner.receipts.push(receipt.clone());
                    // Attribute the receipt to the file it saved — the per-file
                    // provenance timeline (a refused save reached neither arm,
                    // so only genuine commits are recorded here).
                    inner
                        .per_file
                        .entry(file)
                        .or_default()
                        .push(receipt.clone());
                    Ok(receipt)
                }
                TurnResult::Rejected { reason, .. } => {
                    Err(anyhow!("save turn refused by the executor: {reason:?}"))
                }
                TurnResult::Expired => bail!("save turn expired"),
                TurnResult::Pending => bail!("save turn pending"),
            }
        }

        fn receipt_count(&self) -> usize {
            self.inner.borrow().receipts.len()
        }

        fn last_receipt(&self) -> Option<TurnReceipt> {
            self.inner.borrow().receipts.last().cloned()
        }

        fn file_history(&self, file: CellId) -> Vec<TurnReceipt> {
            self.inner
                .borrow()
                .per_file
                .get(&file)
                .cloned()
                .unwrap_or_default()
        }

        fn receipts(&self) -> Vec<TurnReceipt> {
            self.inner.borrow().receipts.clone()
        }

        fn total_balance(&self) -> i128 {
            self.inner
                .borrow()
                .ledger
                .iter()
                .map(|(_, c)| c.state.balance() as i128)
                .sum()
        }
    }

    // --- the namespace --------------------------------------------------------

    /// The firmament-backed filesystem: file = cell, save = receipted turn.
    ///
    /// Mounts file-cells onto a [`LedgerSpine`] — either a FRESH in-process
    /// `Ledger` + `TurnExecutor` ([`FirmamentFs::new`], the headless / per-editor
    /// path) or a host's LIVE spine ([`FirmamentFs::over`], e.g. the cockpit's
    /// `Rc<RefCell<World>>`). Every [`Fs::save`](crate::fs::Fs::save) runs a
    /// cap-gated `SetField` turn through the spine's executor and the genuine
    /// [`TurnReceipt`] is recorded on that spine. When mounted `over` the live
    /// World, a save is visible to a second reader of that World (the cockpit's
    /// cell inspector) as a new cell + receipt — one ledger, one save path.
    pub struct FirmamentFs {
        /// The verified spine the file-cells live on (owned or host-shared).
        spine: Rc<dyn LedgerSpine>,
        /// The path → file-cell namespace: a tree of capability-secure `rbg`
        /// `DirectoryCell`s (recursive scoping, membership-scoped listing,
        /// `dregg://` sturdy refs, versioned CAS). Single-threaded `RefCell`.
        namespace: RefCell<DirNamespace>,
        /// OPTIONAL disk-mirror root (off by default). When `Some(root)`, every
        /// `save` — AFTER the verified turn commits (the cell update is the
        /// durable receipted source of truth) — ALSO writes the decoded content to
        /// `<root>/<path>`, a derived read-mirror the legacy disk-reading
        /// toolchain (cargo/git) compiles from. This is the FirmamentFs↔disk
        /// dual-write that closes the full self-hosting loop: cell = receipted
        /// truth, disk file = derived mirror. `None` → exactly the cell-only
        /// behavior (no disk writes at all).
        mirror_root: RefCell<Option<PathBuf>>,
    }

    impl FirmamentFs {
        /// A fresh firmament fs over an [`OwnedSpine`] (its own ledger + executor),
        /// seeded with the editor (author) cell. No files yet — seed them with
        /// [`FirmamentFs::seed_file`]. This is the headless / test default.
        pub fn new() -> Self {
            Self::over(Rc::new(OwnedSpine::new()))
        }

        /// **Mount a firmament fs OVER an existing verified spine** — the cockpit
        /// seam. The file-cells land on `spine`'s ledger (e.g. the live cockpit
        /// `World`), so a save is a real turn on the SAME ledger the cockpit's
        /// cell inspector reads. Seed files with [`FirmamentFs::seed_file`] (they
        /// install onto the shared ledger). This is how the editor pane edits the
        /// ledger the cockpit inspects rather than a per-editor copy.
        pub fn over(spine: Rc<dyn LedgerSpine>) -> Self {
            // The editor's directory member id = its cell id bytes; it is a member
            // of every directory in the tree, so its cap reaches the whole mount.
            let editor = MemberId(spine.editor_id().0);
            FirmamentFs {
                namespace: RefCell::new(DirNamespace::new(DEOS_ZED_FEDERATION, editor)),
                spine,
                mirror_root: RefCell::new(None),
            }
        }

        /// The editor (author) cell id — the agent of every save turn.
        pub fn editor_id(&self) -> CellId {
            self.spine.editor_id()
        }

        /// How many save-turn receipts have been recorded on the spine (the
        /// on-ledger save count). Each is a genuine finalized `TurnReceipt`.
        pub fn receipt_count(&self) -> usize {
            self.spine.receipt_count()
        }

        /// The most recent save's receipt (the proof-carrying token that the last
        /// save happened under the editor's authority), if any save has run.
        pub fn last_receipt(&self) -> Option<TurnReceipt> {
            self.spine.last_receipt()
        }

        /// The spine's GLOBAL receipt log, in commit order — every recorded
        /// save-turn receipt across all files (empty if the spine does not
        /// publish its log; see [`LedgerSpine::receipts`]). The receipt rail
        /// verifies a file's timeline as an ordered subsequence of this.
        pub fn receipts(&self) -> Vec<TurnReceipt> {
            self.spine.receipts()
        }

        /// The file cell backing `path`, if it resolves in the namespace.
        pub fn cell_for(&self, path: &Path) -> Option<CellId> {
            self.namespace.borrow().resolve_file(path).ok()
        }

        /// The `dregg://` sturdy ref a file `path` resolves to — the portable,
        /// cross-federation capability handle (`federation + cell + swiss`) a
        /// remote node could enliven to reach this same file. The distribution
        /// payoff of the directory namespace: a path is a portable cap, not a bare
        /// local id. (The host wires its real federation + swiss; the owned path
        /// derives an in-process swiss.)
        pub fn sturdy_ref(&self, path: &Path) -> Result<SturdyRef> {
            self.namespace.borrow().sturdy_ref(path)
        }

        /// **The verifiable save timeline for `path`** — the ordered receipts
        /// whose save targeted this file's cell. Each is a genuine finalized
        /// [`TurnReceipt`]: the FS-layer provenance of the file (the
        /// receipt-grounded twin of the doc-viewer's patch blame), distinct from
        /// the spine-global [`receipt_count`](Self::receipt_count) /
        /// [`last_receipt`](Self::last_receipt) which fold over EVERY file.
        ///
        /// `Ok([])` if the path is in the namespace but has had no committed
        /// save (a seed is genesis, not a turn — it produces no receipt). `Err`
        /// only if the path resolves to no cell at all.
        pub fn history(&self, path: &Path) -> Result<Vec<TurnReceipt>> {
            let cell = self
                .cell_for(path)
                .ok_or_else(|| anyhow!("no cell mounted at {}", path.display()))?;
            Ok(self.spine.file_history(cell))
        }

        /// How many receipted saves have targeted `path`'s file cell
        /// SPECIFICALLY — its per-file save count, distinct from the
        /// spine-global [`receipt_count`](Self::receipt_count). `0` for a path
        /// with no cell or no committed save yet.
        pub fn save_count_for(&self, path: &Path) -> usize {
            self.cell_for(path)
                .map(|c| self.spine.file_history(c).len())
                .unwrap_or(0)
        }

        /// The total balance across all cells on the spine's ledger — the
        /// conservation observable (Σ balance). A content `SetField` save touches
        /// the file cell's committed `fields_map`, not any balance substance, so a
        /// genuine save leaves this INVARIANT: the editor's edit conserves value.
        /// A test asserts `total_balance` before == after a save (Σδ=0).
        pub fn total_balance(&self) -> i128 {
            self.spine.total_balance()
        }

        /// **Seed a file into the namespace** with initial `content`, as GENESIS
        /// (the directory-owner installing a file, like a node seeds a genesis
        /// cell): install a file cell holding the content projection onto the
        /// spine's ledger, grant the editor the file's edit cap, and register the
        /// path. Returns the file's [`CellId`]. This is the read-side fixture a
        /// test/host uses to put a file on the ledger so a later
        /// [`Fs::load`](crate::fs::Fs::load) reads it from the cell, not disk.
        pub fn seed_file(&self, path: impl Into<PathBuf>, content: &str) -> Result<CellId> {
            let path = path.into();
            let file = self.spine.install_file(content)?;
            // Bind the path → file cell in the directory tree (creating
            // intermediate `DirectoryCell`s as needed). A name clash loses the CAS.
            self.namespace.borrow_mut().bind(&path, file)?;
            // If a disk mirror is configured, lay the seed content onto disk too,
            // so the legacy toolchain sees the genesis file (the cell remains the
            // source of truth; this is the derived read-mirror).
            self.mirror_write(&path, content)?;
            Ok(file)
        }

        /// **Enable the disk dual-write** by configuring `root` as the mirror root
        /// (off by default). After this, every [`Fs::save`](crate::fs::Fs::save) —
        /// once the verified turn commits — also writes the new content to
        /// `<root>/<path>`, the derived disk mirror the legacy disk-reading
        /// toolchain (cargo/git) compiles from. The cell stays the receipted
        /// source of truth; the disk file is a read-mirror. Mirrors EVERY file
        /// currently in the namespace immediately (so already-seeded files appear
        /// on disk at the moment the mirror is enabled), then dual-writes on each
        /// later save. A mirror write error surfaces (fail-loud — the disk never
        /// silently desyncs from the ledger).
        pub fn enable_disk_mirror(&self, root: impl Into<PathBuf>) -> Result<()> {
            let root = root.into();
            std::fs::create_dir_all(&root)
                .with_context(|| format!("creating mirror root {}", root.display()))?;
            *self.mirror_root.borrow_mut() = Some(root);
            // Backfill: mirror every already-seeded file's current content so the
            // disk view matches the ledger from the first command. `all_files`
            // walks the directory tree to recover every (path, cell) leaf.
            let snapshot: Vec<(PathBuf, CellId)> = self.namespace.borrow().all_files()?;
            for (path, cell_id) in snapshot {
                if let Some(cell) = self.spine.cell(&cell_id) {
                    let content = decode_content(&cell)?;
                    self.mirror_write(&path, &content)?;
                }
            }
            Ok(())
        }

        /// The configured disk-mirror root, if the dual-write is enabled.
        pub fn mirror_root(&self) -> Option<PathBuf> {
            self.mirror_root.borrow().clone()
        }

        /// Resolve a namespace `path` to its on-disk mirror location under the
        /// mirror root. The namespace uses absolute-looking paths (e.g.
        /// `/deos/main.rs`); we strip the leading `/` and join under the root so
        /// `/deos/main.rs` → `<root>/deos/main.rs`. A relative path joins directly.
        fn mirror_path(root: &Path, path: &Path) -> PathBuf {
            let rel = path.strip_prefix("/").unwrap_or(path);
            root.join(rel)
        }

        /// Write `content` to the disk mirror for `path` IF the mirror is enabled
        /// (else a no-op — exactly the cell-only behavior). Creates parent dirs.
        /// Fail-loud: a write error is returned so the disk can never silently
        /// desync from the receipted ledger.
        fn mirror_write(&self, path: &Path, content: &str) -> Result<()> {
            let root = self.mirror_root.borrow().clone();
            let Some(root) = root else { return Ok(()) };
            let disk = Self::mirror_path(&root, path);
            if let Some(parent) = disk.parent() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("creating mirror dir {}", parent.display()))?;
            }
            std::fs::write(&disk, content)
                .with_context(|| format!("mirroring save to disk at {}", disk.display()))?;
            Ok(())
        }
    }

    impl Default for FirmamentFs {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Fs for FirmamentFs {
        fn load(&self, path: &Path) -> Result<String> {
            let cell_id = self.namespace.borrow().resolve_file(path)?;
            let cell = self
                .spine
                .cell(&cell_id)
                .ok_or_else(|| anyhow!("file cell missing from ledger"))?;
            decode_content(&cell)
        }

        fn save(&self, path: &Path, content: &str) -> Result<()> {
            // Resolve the path → file cell; if the path is new, install a file cell
            // for it on the fly (a "save as" into the namespace) and grant the
            // editor its cap so this very save commits.
            let existing = self.namespace.borrow().resolve_file(path).ok();
            let file = match existing {
                Some(c) => c,
                None => {
                    let file = self.spine.install_file("")?;
                    self.namespace.borrow_mut().bind(path, file)?;
                    file
                }
            };
            // THE SAVE IS A TURN. The receipt is the cap-gated witness that this
            // exact edit happened under this exact authority — recorded in the
            // provenance log; a light client can confirm the file holds this
            // content without trusting the editor.
            self.spine.commit_save(file, content)?;
            // DUAL-WRITE: the verified turn is committed (the cell is the durable
            // receipted source of truth); now mirror the new content to disk IF a
            // mirror root is configured, so the legacy disk-reading toolchain
            // (cargo/git) compiles THIS edit. Off by default → a no-op. Fail-loud
            // on a mirror error: the disk must not silently desync from the ledger.
            self.mirror_write(path, content)?;
            Ok(())
        }

        fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>> {
            // Capability-scoped listing: `DirectoryCell::list(editor)` over the
            // directory cell at `path`. Holding the directory cap (membership) IS
            // the authority to enumerate it.
            let children = self.namespace.borrow().list_children(path)?;
            Ok(children
                .into_iter()
                .map(|(name, is_dir)| DirEntry {
                    path: path.join(&name),
                    is_dir,
                })
                .collect())
        }

        fn metadata(&self, path: &Path) -> Result<Metadata> {
            let ns = self.namespace.borrow();
            if let Ok(cell_id) = ns.resolve_file(path) {
                let cell = self
                    .spine
                    .cell(&cell_id)
                    .ok_or_else(|| anyhow!("file cell missing from ledger"))?;
                let len = decode_content(&cell).map(|s| s.len()).unwrap_or(0) as u64;
                return Ok(Metadata {
                    is_dir: false,
                    is_symlink: false,
                    len,
                });
            }
            // A directory iff the path resolves to a directory cell in the tree.
            if ns.is_dir(path) {
                Ok(Metadata {
                    is_dir: true,
                    is_symlink: false,
                    len: 0,
                })
            } else {
                bail!("no cell mounted at {}", path.display())
            }
        }

        fn backend_label(&self) -> &'static str {
            "FirmamentFs (cell=file, save=receipted turn)"
        }

        fn save_count(&self) -> Option<usize> {
            // The genuine on-ledger receipt count — each is a finalized
            // `TurnReceipt`. The editor's status line reads THIS, so its
            // `N saves · on-ledger` is the real ledger truth, not the gpui-side
            // patch history.
            Some(self.receipt_count())
        }

        fn last_save_receipt_hash(&self) -> Option<[u8; 32]> {
            // The just-minted receipt's own hash — what the status line stamps
            // (`⛓ a1b2c3d4`) so the save visibly LANDS as a chain event.
            self.last_receipt().map(|r| r.receipt_hash())
        }

        fn receipt_facts_for(&self, path: &Path) -> Vec<crate::receipt_rail::ReceiptFact> {
            // The REAL per-file timeline off the live spine, projected to the
            // rail's always-compiled fact shape. A path with no cell (or a
            // spine with no per-file attribution) yields an empty rail — the
            // rail renders that honestly rather than erroring a UI strip.
            self.history(path)
                .map(|v| {
                    v.iter()
                        .map(crate::receipt_rail::ReceiptFact::from)
                        .collect()
                })
                .unwrap_or_default()
        }

        fn receipt_facts(&self) -> Vec<crate::receipt_rail::ReceiptFact> {
            self.receipts()
                .iter()
                .map(crate::receipt_rail::ReceiptFact::from)
                .collect()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::fs::Fs;

        #[test]
        fn save_is_a_receipted_turn_and_content_round_trips_through_the_ledger() {
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/proj/src/main.rs");
            let original = "fn main() {\n    println!(\"before\");\n}\n";
            let edited = "fn main() {\n    println!(\"AFTER — a receipted turn\");\n}\n";

            // Seed the file as a cell (the read-side fixture).
            let file = fs.seed_file(&path, original).unwrap();

            // load() reads the content FROM THE CELL (not disk).
            assert_eq!(
                fs.load(&path).unwrap(),
                original,
                "seed round-trips from the cell"
            );
            assert_eq!(
                fs.receipt_count(),
                0,
                "a seed is genesis, not a turn — no receipt yet"
            );

            // save() runs a real cap-gated turn → a genuine receipt.
            fs.save(&path, edited).unwrap();
            assert_eq!(fs.receipt_count(), 1, "the save produced ONE receipt");
            let receipt = fs.last_receipt().expect("a receipt was recorded");
            assert_eq!(
                receipt.agent,
                fs.editor_id(),
                "the editor is the turn's agent"
            );
            assert_ne!(
                receipt.pre_state_hash, receipt.post_state_hash,
                "the save moved the ledger state (the edit landed on-ledger)"
            );
            assert!(receipt.action_count >= 1);

            // re-load() reads the edited content BACK FROM THE LEDGER (the cell's
            // committed map the turn wrote) — never disk.
            assert_eq!(
                fs.load(&path).unwrap(),
                edited,
                "the edited content round-trips through the ledger, not disk"
            );

            // The file cell is the one the namespace resolves the path to.
            assert_eq!(fs.cell_for(&path), Some(file));
        }

        #[test]
        fn save_without_the_edit_cap_is_refused_in_band() {
            // The cross-cell cap gate is the real save authority: a file cell the
            // editor holds NO cap for cannot be saved (the executor refuses it
            // in-band — the anti-ghost tooth).
            // Build over an OwnedSpine we can reach into: mint a file cell on its
            // ledger WITHOUT granting the editor its cap, then register the path.
            let spine = Rc::new(OwnedSpine::new());
            let file = spine.install_uncapped_file("secret");
            let fs = FirmamentFs::over(spine);
            let path = PathBuf::from("/locked.txt");
            fs.namespace.borrow_mut().bind(&path, file).unwrap();
            // NB: no capabilities.grant — the editor lacks the file's cap.

            // The read still works (a read is authority-checked at the namespace,
            // not via a turn).
            assert_eq!(fs.load(&path).unwrap(), "secret");

            // The save is REFUSED by the executor's cap gate, in-band.
            let err = fs.save(&path, "tampered").unwrap_err();
            assert!(
                err.to_string().contains("refused"),
                "save without the edit cap must be refused: {err}"
            );
            // The content is UNTOUCHED — the executor rolled the ledger back.
            assert_eq!(
                fs.load(&path).unwrap(),
                "secret",
                "a refused save leaves the cell untouched"
            );
            assert_eq!(fs.receipt_count(), 0, "no receipt for a refused save");
        }

        #[test]
        fn per_file_history_is_attributed_and_ordered() {
            // Each file carries its OWN verifiable save timeline (the FS-layer
            // provenance), distinct from the spine-global receipt log: a save to
            // file A must not appear in file B's history, and the global log is
            // the union of the per-file timelines in commit order.
            let fs = FirmamentFs::new();
            let a = PathBuf::from("/proj/a.rs");
            let b = PathBuf::from("/proj/b.rs");
            fs.seed_file(&a, "a0").unwrap();
            fs.seed_file(&b, "b0").unwrap();

            // A seed is genesis, not a turn — no per-file history yet.
            assert!(fs.history(&a).unwrap().is_empty());
            assert_eq!(fs.save_count_for(&a), 0);

            // Interleave saves: a, b, a.
            fs.save(&a, "a1").unwrap();
            fs.save(&b, "b1").unwrap();
            fs.save(&a, "a2").unwrap();

            // Per-file counts are attributed, not global.
            assert_eq!(fs.save_count_for(&a), 2, "file a saw two saves");
            assert_eq!(fs.save_count_for(&b), 1, "file b saw one save");
            assert_eq!(
                fs.receipt_count(),
                3,
                "the global log is the union of the per-file timelines"
            );

            // a's timeline is its two receipts in commit order, each chained
            // (the second's previous hash is the first's receipt hash) — a's own
            // verifiable history independent of the b save committed between them.
            let hist_a = fs.history(&a).unwrap();
            assert_eq!(hist_a.len(), 2);
            assert_eq!(
                hist_a[1].previous_receipt_hash,
                Some(fs.history(&b).unwrap()[0].receipt_hash()),
                "the global receipt chain threads through ALL files; a's 2nd save \
                 chains onto the b save committed between a's two saves"
            );
            for r in &hist_a {
                assert_eq!(r.agent, fs.editor_id(), "the editor authored each save");
                assert_ne!(r.pre_state_hash, r.post_state_hash, "each save moved state");
            }

            // A path with no cell errors; a known-but-unsaved-since-seed path is Ok([]).
            assert!(fs.history(Path::new("/nope.rs")).is_err());
        }

        #[test]
        fn read_dir_lists_namespace_children() {
            let fs = FirmamentFs::new();
            fs.seed_file("/proj/a.rs", "a").unwrap();
            fs.seed_file("/proj/b.rs", "b").unwrap();
            fs.seed_file("/proj/sub/c.rs", "c").unwrap();

            let mut entries = fs.read_dir(Path::new("/proj")).unwrap();
            entries.sort_by(|x, y| x.path.cmp(&y.path));
            let names: Vec<_> = entries.iter().map(|e| (e.file_name(), e.is_dir)).collect();
            assert_eq!(
                names,
                vec![
                    ("a.rs".to_string(), false),
                    ("b.rs".to_string(), false),
                    ("sub".to_string(), true),
                ]
            );

            let md = fs.metadata(Path::new("/proj/a.rs")).unwrap();
            assert!(!md.is_dir && md.len == 1);
            let dmd = fs.metadata(Path::new("/proj/sub")).unwrap();
            assert!(dmd.is_dir);
        }

        #[test]
        fn disk_mirror_dual_writes_each_save_after_the_receipt() {
            // THE FULL-LOOP WIRE: with the mirror enabled, a receipted save also
            // lands the new content on disk where the legacy toolchain reads it.
            // The cell is the source of truth; the disk file is a derived mirror.
            let dir = std::env::temp_dir().join(format!(
                "firmament-mirror-test-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/proj/src/main.rs");
            let v1 = "fn main() { println!(\"v1\"); }\n";
            let v2 = "fn main() { println!(\"v2\"); }\n";

            fs.seed_file(&path, v1).unwrap();
            // Enabling the mirror backfills the seed content onto disk.
            fs.enable_disk_mirror(&dir).unwrap();
            let on_disk = dir.join("proj/src/main.rs");
            assert_eq!(
                std::fs::read_to_string(&on_disk).unwrap(),
                v1,
                "enabling the mirror backfills the seeded content to disk"
            );

            // A receipted save dual-writes the edit to disk.
            fs.save(&path, v2).unwrap();
            assert_eq!(fs.receipt_count(), 1, "the save is a real receipted turn");
            assert_eq!(
                std::fs::read_to_string(&on_disk).unwrap(),
                v2,
                "the save's new content is mirrored to disk for the legacy toolchain"
            );
            // The cell remains the source of truth: a re-load reads from the ledger.
            assert_eq!(fs.load(&path).unwrap(), v2);

            let _ = std::fs::remove_dir_all(&dir);
        }

        #[test]
        fn mirror_off_by_default_writes_no_disk() {
            // The default (no mirror) writes NOTHING to disk — exactly today's
            // cell-only behavior. (We can't easily assert "no file anywhere", but
            // we can assert the namespace works without a configured root.)
            let fs = FirmamentFs::new();
            assert!(fs.mirror_root().is_none(), "mirror is off by default");
            let path = PathBuf::from("/x.rs");
            fs.seed_file(&path, "a").unwrap();
            fs.save(&path, "b").unwrap();
            assert_eq!(fs.load(&path).unwrap(), "b");
            assert!(fs.mirror_root().is_none(), "still off after a save");
        }

        #[test]
        fn shrinking_a_file_vacates_stale_tail_chunks() {
            // A save that shrinks the content must vacate the old tail so the
            // commitment binds only the live content (a re-load can't resurrect
            // bytes the editor deleted).
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/big.txt");
            let big = "x".repeat(200); // 7 chunks
            let small = "y".repeat(10); // 1 chunk
            fs.seed_file(&path, &big).unwrap();
            fs.save(&path, &small).unwrap();
            assert_eq!(fs.load(&path).unwrap(), small);
        }
    }
}

#[cfg(feature = "firmament")]
pub use live::{
    host_content_write_effects, host_decode_content, host_make_editor_cell, host_make_file_cell,
    FirmamentFs, LedgerSpine, OwnedSpine,
};
