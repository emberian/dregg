//! Mount [`deos_zed::Editor`] as a [`CockpitSurface`] — the deos editor pane.
//!
//! This forwards the cockpit's [`CockpitSurface`] trait to the inherent methods
//! on [`deos_zed::cockpit_surface::EditorSurface`]. It is mounted in
//! `dock/mod.rs`; the live cockpit opens it from
//! `cockpit/panels_workspace.rs::open_editor_pane`.
//!
//! ## Backing store: FirmamentFs by DEFAULT (saves = receipted turns)
//!
//! With starbridge-v2's `firmament` feature on (it rides `dev-surfaces` →
//! `native-full`), [`EditorPane::new`] builds a **firmament-backed** pane: the
//! editor edits sovereign cells over an in-process `Ledger` + `TurnExecutor`,
//! and EVERY SAVE is a real cap-gated `SetField` turn leaving a verifiable
//! `TurnReceipt`. The `RealFs` (disk) handle the caller passes is then only the
//! file-tree root hint — the editor buffer is on-ledger, not disk. The status
//! line's `N saves · on-ledger` is the genuine ledger receipt count.
//!
//! With the feature off, [`EditorPane::new`] is the original disk pane over the
//! passed `Arc<dyn Fs>` (so a `RealFs` build still works). The default
//! cockpit build (`native-full`) carries `firmament`, so the running editor is
//! firmament-backed. See `deos-zed/FIRMAMENT-FS-SEAM.md`.

use deos_zed::cockpit_surface::EditorSurface;
use gpui::{AnyElement, App, FocusHandle, IntoElement, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// The cockpit-`World` realization of deos-zed's [`LedgerSpine`](deos_zed::fs::LedgerSpine):
/// file-cells live on the LIVE cockpit `World`, so a save is a real turn committed
/// through `World::commit_turn` and visible to the cockpit's cell inspector (which
/// reads the SAME `World::ledger()`). Mounting a [`FirmamentFs::over`](deos_zed::fs::FirmamentFs::over)
/// this spine is how the editor pane edits the ledger the cockpit inspects, not a
/// per-editor copy.
///
/// Single-threaded (`Rc<RefCell<World>>`), matching the cockpit's own ownership —
/// no second `Arc<Mutex<…>>` model. The editor cell (the save agent) is installed
/// once on the World at construction; each seeded/saved file gets its cap granted.
#[cfg(all(feature = "firmament", feature = "embedded-executor"))]
struct WorldSpine {
    world: std::rc::Rc<std::cell::RefCell<crate::world::World>>,
    /// The editor (author) cell id — installed on the World once, the agent of
    /// every save turn.
    editor: dregg_cell::CellId,
    /// A monotonic seed for new file cells (domain-tagged so they can't collide
    /// with the editor cell; offset high so it can't collide with cockpit genesis
    /// seeds either).
    next_seed: std::cell::Cell<u32>,
    /// Per-FILE receipt timeline: the receipts whose save targeted a given
    /// file cell, in commit order — what deos-zed's RECEIPT RAIL (the editor
    /// pane's ledger face) renders for the open file. Mirrors `OwnedSpine`'s
    /// `per_file`; without it this spine silently inherited the empty
    /// `LedgerSpine::file_history` default and the live-cockpit rail was
    /// blank. Only genuine commits are recorded (a refused save reaches
    /// neither arm). Single-threaded `RefCell`, same as the World itself.
    per_file: std::cell::RefCell<
        std::collections::BTreeMap<dregg_cell::CellId, Vec<dregg_turn::TurnReceipt>>,
    >,
}

#[cfg(all(feature = "firmament", feature = "embedded-executor"))]
impl WorldSpine {
    /// Mount a spine over the live cockpit `World`, installing the editor (author)
    /// cell onto it (genesis path) so saves have an agent that holds the file caps.
    fn new(world: std::rc::Rc<std::cell::RefCell<crate::world::World>>) -> Self {
        let editor_cell = deos_zed::fs::host_make_editor_cell();
        let editor = editor_cell.id();
        world.borrow_mut().genesis_install(editor_cell);
        WorldSpine {
            world,
            editor,
            // Start high so file-cell seeds don't collide with the cockpit's own
            // small genesis seeds (anchors etc.).
            next_seed: std::cell::Cell::new(0x1000_0000),
            per_file: std::cell::RefCell::new(std::collections::BTreeMap::new()),
        }
    }
}

#[cfg(all(feature = "firmament", feature = "embedded-executor"))]
impl deos_zed::fs::LedgerSpine for WorldSpine {
    fn editor_id(&self) -> dregg_cell::CellId {
        self.editor
    }

    fn cell(&self, id: &dregg_cell::CellId) -> Option<dregg_cell::Cell> {
        self.world.borrow().ledger().get(id).cloned()
    }

    fn install_file(&self, content: &str) -> anyhow::Result<dregg_cell::CellId> {
        let seed = self.next_seed.get();
        self.next_seed.set(seed.wrapping_add(1));
        // Build the file cell in EXACTLY the layout deos-zed's `load` decodes
        // (the host wire API), install it on the live World as genesis, and grant
        // the editor its per-file edit cap so a later save commits.
        let file_cell = deos_zed::fs::host_make_file_cell(seed, content);
        let file = file_cell.id();
        let mut w = self.world.borrow_mut();
        w.genesis_install(file_cell);
        w.genesis_grant_cap(&self.editor, file)
            .ok_or_else(|| anyhow::anyhow!("editor c-list full granting file edit cap"))?;
        Ok(file)
    }

    fn commit_save(
        &self,
        file: dregg_cell::CellId,
        content: &str,
    ) -> anyhow::Result<dregg_turn::TurnReceipt> {
        // Build the content `SetField` effects against the file cell's CURRENT
        // state (so the stale-tail vacate is computed) — the SAME wire shape the
        // owned spine + `seed_file` lay, so the editor's `load` decodes the save.
        let effects = {
            let w = self.world.borrow();
            let cell = w
                .ledger()
                .get(&file)
                .ok_or_else(|| anyhow::anyhow!("file cell vanished from ledger"))?;
            deos_zed::fs::host_content_write_effects(cell, content)
        };
        // THE SAVE IS A TURN through the LIVE World — `World::turn` threads the
        // editor's nonce, `commit_turn` threads the receipt chain head + records
        // the receipt + emits dynamics. A second reader of this World (the cockpit
        // inspector) now sees the new cell content + the new receipt.
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(self.editor, effects);
            w.commit_turn(turn)
        };
        match outcome {
            crate::world::CommitOutcome::Committed { receipt, .. } => {
                // Attribute the receipt to the file it saved — the per-file
                // rail the editor pane's ledger face reads (only genuine
                // commits land here; a refused save returned above).
                self.per_file
                    .borrow_mut()
                    .entry(file)
                    .or_default()
                    .push((*receipt).clone());
                Ok(*receipt)
            }
            crate::world::CommitOutcome::Rejected { reason, .. } => Err(anyhow::anyhow!(
                "save turn refused by the executor: {reason}"
            )),
            crate::world::CommitOutcome::Queued { .. } => {
                Err(anyhow::anyhow!("save turn queued (world suspended)"))
            }
        }
    }

    fn receipt_count(&self) -> usize {
        self.world.borrow().receipts().len()
    }

    fn last_receipt(&self) -> Option<dregg_turn::TurnReceipt> {
        self.world.borrow().receipts().last().cloned()
    }

    fn file_history(&self, file: dregg_cell::CellId) -> Vec<dregg_turn::TurnReceipt> {
        self.per_file
            .borrow()
            .get(&file)
            .cloned()
            .unwrap_or_default()
    }

    fn receipts(&self) -> Vec<dregg_turn::TurnReceipt> {
        // The LIVE World's global receipt log — the rail's `verify chain`
        // embeds a file's timeline into exactly this (each chip's hash is the
        // SAME hash the desktop's dynamics feed carries in TurnCommitted).
        self.world.borrow().receipts().to_vec()
    }

    fn total_balance(&self) -> i128 {
        self.world
            .borrow()
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance() as i128)
            .sum()
    }
}

/// A dock-hostable wrapper around a deos-zed editor surface.
pub struct EditorPane(EditorSurface);

/// The seed project a firmament-backed editor pane opens onto: a couple of
/// file-cells with real content so the editor opens on something editable and
/// the file tree shows a project. The FIRST entry is the file opened in the
/// buffer; saving it fires a real turn. Mirrors the showcase's seeded slice but
/// over genuine cells (not an in-memory string).
#[cfg(feature = "firmament")]
const FIRMAMENT_SEED: &[(&str, &str)] = &[
    (
        "/deos/main.rs",
        "// edit me — every save here is a RECEIPTED dregg turn on the live ledger.\n\
         fn main() {\n    println!(\"hello from a sovereign cell\");\n}\n",
    ),
    (
        "/deos/notes.md",
        "# on-ledger notes\n\nThis file is a cell. Saving it is a cap-gated turn,\n\
         not a disk write — the status line shows the real receipt count.\n",
    ),
];

impl EditorPane {
    /// Build the cockpit editor pane. With the `firmament` feature on (the
    /// default cockpit build), this is FIRMAMENT-BACKED — saves are receipted
    /// turns, `fs`/`root` only hint the file-tree root. Off, it is the disk pane
    /// over the passed `fs`.
    pub fn new(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        #[cfg(feature = "firmament")]
        {
            let _ = fs; // disk handle unused: the firmament pane is cell-backed.
            match EditorSurface::firmament(id, root.clone(), FIRMAMENT_SEED, window, cx) {
                Ok(surface) => EditorPane(surface),
                Err(e) => {
                    // Fail-soft to the disk pane so a firmament mount error can
                    // never take down the cockpit — but say so loudly.
                    eprintln!(
                        "EditorPane::new: firmament mount failed, falling back to disk: {e:#}"
                    );
                    EditorPane(EditorSurface::new(
                        id,
                        deos_zed::fs::RealFs::arc(),
                        root,
                        window,
                        cx,
                    ))
                }
            }
        }
        #[cfg(not(feature = "firmament"))]
        EditorPane(EditorSurface::new(id, fs, root, window, cx))
    }

    /// Build a firmament-backed pane explicitly (independent of the feature gate
    /// at the call site): the editor edits sovereign cells, saves are receipted
    /// turns. `files` is the seed project (first entry opened in the buffer).
    /// Exposes the typed handle so the host/test can read the live receipt log.
    #[cfg(feature = "firmament")]
    pub fn firmament(
        id: u64,
        root: std::path::PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Ok(EditorPane(EditorSurface::firmament(
            id, root, files, window, cx,
        )?))
    }

    /// **Build a firmament-backed pane OVER the live cockpit `World`** — the
    /// shared-ledger seam. The editor edits file-cells on the SAME `World` ledger
    /// the cockpit's cell inspector reads, so a save is a real turn committed
    /// through `World::commit_turn` and shows up as a new cell + receipt in the
    /// cockpit's live world (not a per-editor copy). `files` is the seed project
    /// (installed as genesis on the World; first entry opened in the buffer).
    #[cfg(all(feature = "firmament", feature = "embedded-executor"))]
    pub fn firmament_over(
        id: u64,
        world: std::rc::Rc<std::cell::RefCell<crate::world::World>>,
        root: std::path::PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        let spine: std::rc::Rc<dyn deos_zed::fs::LedgerSpine> =
            std::rc::Rc::new(WorldSpine::new(world));
        // single-threaded gpui context; the Arc is what `FirmamentFs` hands the editor API
        #[allow(clippy::arc_with_non_send_sync)]
        let firm = std::sync::Arc::new(deos_zed::fs::FirmamentFs::over(spine));
        Ok(EditorPane(EditorSurface::firmament_over(
            id, firm, root, files, window, cx,
        )?))
    }

    /// The real on-ledger receipt count (genuine `TurnReceipt`s), if this pane is
    /// firmament-backed. The honest `N saves · on-ledger` truth.
    #[cfg(feature = "firmament")]
    pub fn receipt_count(&self) -> Option<usize> {
        self.0.receipt_count()
    }

    /// The typed firmament fs handle, if firmament-backed — for host/test reads
    /// (last receipt, conservation Σδ=0, cell lookup).
    #[cfg(feature = "firmament")]
    pub fn firmament_fs(&self) -> Option<&std::sync::Arc<deos_zed::fs::FirmamentFs>> {
        self.0.firmament_fs()
    }

    /// Build a SEEDED editor pane: an in-memory buffer filled with `revisions`
    /// (the last shown; priors are on-ledger patches) under the virtual `name`
    /// (drives syntax highlighting), plus a real file tree over `fs`/`root`. What
    /// the headless showcase bake uses — disk-free highlighted code with a real
    /// `N patches · on-ledger` status.
    pub fn seeded(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        EditorPane(EditorSurface::seeded(
            id, fs, root, name, revisions, window, cx,
        ))
    }

    /// Access the underlying editor entity (host-side open/save).
    pub fn editor(&self) -> &gpui::Entity<deos_zed::editor::Editor> {
        self.0.editor()
    }

    /// Install the node-wire save hook on this pane's editor — when the cockpit is
    /// `--node`-attached the host wires the editor's OWN save path (the callback a
    /// real Cmd-S invokes) to route a client-signed turn to the live node. See
    /// [`deos_zed::editor::SaveCallback`]. The local firmament save is unchanged;
    /// the node write is additive and fail-soft.
    pub fn set_save_callback(&self, cb: deos_zed::editor::SaveCallback, cx: &mut App) {
        self.0.set_save_callback(cb, cx);
    }
}

impl CockpitSurface for EditorPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.surface_id())
    }

    fn tab_label(&self) -> SharedString {
        // CockpitSurface::tab_label takes no cx; the live title is rendered in
        // tab_content instead. This static label is the stable fallback.
        SharedString::from("editor")
    }

    fn tab_content(&self, _window: &mut Window, cx: &mut App) -> AnyElement {
        use gpui::{div, ParentElement};
        div().child(self.0.tab_label(cx)).into_any_element()
    }

    fn render_body(&mut self, window: &mut Window, cx: &mut App) -> AnyElement {
        self.0.render_body(window, cx)
    }

    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.0.focus_handle(cx)
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.0.is_dirty(cx)
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(EditorPane(self.0.clone()))
    }
}
