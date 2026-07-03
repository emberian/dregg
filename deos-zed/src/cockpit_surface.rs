//! The cockpit-surface adapter — mount the [`Editor`] as a dock pane in
//! starbridge-v2.
//!
//! starbridge-v2's dock hosts any [`CockpitSurface`] (the slim ~8-method item
//! trait in `starbridge-v2/src/dock/surface.rs`). This module gives the editor
//! everything that trait needs, as a concrete [`EditorSurface`] handle.
//!
//! ## Two-file delivery (no heavy cockpit.rs touch)
//!
//! deos-zed is its own workspace, so it can't `use` starbridge-v2's
//! `CockpitSurface` trait directly. The split is:
//!
//!   * **here** — [`EditorSurface`], a concrete handle holding the editor
//!     [`Entity`] plus a `FileTree`, exposing `tab_label` / `render_body` /
//!     `focus_handle` / `is_dirty` / `item_id` as plain inherent methods. This is
//!     the real, tested logic.
//!   * **`starbridge-v2/src/dock/editor_surface.rs`** (delivered ready-to-drop) —
//!     a ~20-line `impl CockpitSurface for EditorSurface` that forwards each
//!     trait method to the inherent method here. It lives in starbridge-v2
//!     because that is where the trait lives; mounting it is a one-line
//!     `pub mod editor_surface;` in `dock/mod.rs` (the dock module, NOT
//!     cockpit.rs) plus a `deos-zed` path dependency.
//!
//! Because both crates pin the same gpui fork, the `Entity<Editor>` here is
//! byte-identical to the one starbridge-v2 sees — the forward is a plain call,
//! no glue.

use std::path::PathBuf;
use std::sync::Arc;

use gpui::{
    div, px, AnyElement, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, Window,
};
use gpui_component::{h_flex, v_flex, ActiveTheme as _};

use dregg_doc::Author;

use crate::doc_viewer::DocViewer;
use crate::editor::Editor;
use crate::file_tree::FileTree;
use crate::fs::Fs;
use crate::receipt_rail::ReceiptRail;

/// Which face of the document the editor pane shows: the editable BUFFER, the
/// document's STRUCTURE — the blame timeline + first-class conflict objects —
/// or its LEDGER: the per-file receipt rail, each committed save as a chained
/// `TurnReceipt` chip.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViewMode {
    /// The rope-backed editable buffer (the authoring face).
    Buffer,
    /// The provenance + conflicts inspector (the [`DocViewer`]): who wrote each
    /// live span, and any two-pens-at-one-tail clash as a first-class object.
    Structure,
    /// The receipt rail (the [`ReceiptRail`]): this file's verifiable save
    /// timeline — one chip per committed turn (hash, height, pre→post morph,
    /// computrons, chain link), read off the REAL cell the file binds to.
    /// Where Structure answers "who wrote each span", Ledger answers "which
    /// receipted turns landed each save".
    Ledger,
}

impl ViewMode {
    fn tab_id(self) -> &'static str {
        match self {
            ViewMode::Buffer => "editor-mode-buffer",
            ViewMode::Structure => "editor-mode-structure",
            ViewMode::Ledger => "editor-mode-ledger",
        }
    }
    fn label(self) -> &'static str {
        match self {
            ViewMode::Buffer => "buffer",
            ViewMode::Structure => "structure · blame / conflicts",
            ViewMode::Ledger => "ledger · receipts",
        }
    }
}

/// The live, interactive editor pane: a file tree, a mode toggle, and — by mode —
/// either the editable [`Editor`] buffer or the [`DocViewer`] structure (blame +
/// conflict objects) of the SAME open document. A single gpui [`Render`] entity so
/// a toggle click re-renders the whole pane (mirrors the hermes dock's owned view).
pub struct EditorPaneView {
    editor: Entity<Editor>,
    tree: Arc<FileTree>,
    /// The provenance/conflicts inspector over the editor's live document. Snapshot
    /// is refreshed from `editor.document()` on open + on each switch to Structure.
    docviewer: Entity<DocViewer>,
    /// The receipt rail over the open file's save timeline — the LEDGER face.
    /// Snapshot is refreshed from the editor's `Fs` seam
    /// ([`Fs::receipt_facts_for`] on the open path) on open, on each switch to
    /// Ledger, and — via the editor observation below — after every save, so a
    /// Cmd-S lands its chip live.
    rail: Entity<ReceiptRail>,
    mode: ViewMode,
    focus: FocusHandle,
    /// Keeps the editor→rail observation alive: whenever the editor notifies
    /// (open, save, merge — every notify), the rail re-snapshots off the live
    /// seam. Cheap (a per-file receipt clone), so a save's new chip appears
    /// without the host re-driving anything.
    _subscriptions: Vec<Subscription>,
}

impl EditorPaneView {
    /// Build the pane over an editor + tree, seeding the structure snapshot from
    /// whatever document the editor already has open (firmament mounts open the
    /// first seed file in their constructor, so the snapshot is live immediately).
    pub fn new(
        editor: Entity<Editor>,
        tree: Arc<FileTree>,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        let docviewer = cx.new(|cx| DocViewer::new(cx));
        let rail = cx.new(|cx| ReceiptRail::new(cx));
        let focus = cx.focus_handle();
        // THE LIVE WIRE: the editor `cx.notify()`s on open/save/merge; observe
        // it so the rail re-snapshots — a save flash-lands its chip with zero
        // extra plumbing (gpui defers observer callbacks past the update, so
        // this cannot re-enter the editor borrow).
        let subs = vec![cx.observe(&editor, |this: &mut Self, _editor, cx| {
            this.refresh_rail(cx);
            cx.notify();
        })];
        let mut me = Self {
            editor,
            tree,
            docviewer,
            rail,
            mode: ViewMode::Buffer,
            focus,
            _subscriptions: subs,
        };
        me.refresh_structure(cx);
        me.refresh_rail(cx);
        me
    }

    /// The editor entity (host-side open/save).
    pub fn editor(&self) -> &Entity<Editor> {
        &self.editor
    }

    /// The structure inspector entity.
    pub fn doc_viewer(&self) -> &Entity<DocViewer> {
        &self.docviewer
    }

    /// The receipt-rail entity (the LEDGER face) — host/test reads of the
    /// per-file save timeline (chip count, latest hash, verify verdict).
    pub fn receipt_rail(&self) -> &Entity<ReceiptRail> {
        &self.rail
    }

    /// The current face shown.
    pub fn mode(&self) -> ViewMode {
        self.mode
    }

    /// Re-snapshot the structure inspector from the editor's LIVE document. Reads
    /// the open document's blame + rendered structure ONCE (owned) so no borrow on
    /// the live `RopeDoc` is held across the `docviewer` update.
    pub fn refresh_structure(&mut self, cx: &mut Context<Self>) {
        let (blame, rendered, title, patches) = {
            let ed = self.editor.read(cx);
            (ed.blame(), ed.rendered(), ed.title(), ed.patch_count())
        };
        self.docviewer.update(cx, |v, _cx| {
            v.set_snapshot(blame, rendered, title, patches);
        });
    }

    /// Re-snapshot the receipt rail from the editor's LIVE `Fs` seam: the open
    /// path's per-file receipt timeline ([`Fs::receipt_facts_for`]) + the
    /// spine's global log ([`Fs::receipt_facts`]) for the verify embedding.
    /// Reads are owned (fact clones) so no borrow spans the `rail` update. A
    /// `RealFs` (or no open file) snapshots an empty rail — the rail renders
    /// that honestly.
    pub fn refresh_rail(&mut self, cx: &mut Context<Self>) {
        let (facts, global, title) = {
            let ed = self.editor.read(cx);
            let fs = ed.fs();
            let facts = ed
                .path()
                .map(|p| fs.receipt_facts_for(p))
                .unwrap_or_default();
            (facts, fs.receipt_facts(), ed.title())
        };
        self.rail.update(cx, |r, cx| {
            r.set_snapshot(facts, global, title);
            cx.notify();
        });
    }

    /// **The merge/conflict action** — run the in-session co-author conflict
    /// demonstrator on the open document, then switch to the STRUCTURE face so the
    /// resulting first-class conflict object is front-and-centre. This is what
    /// closes the gap that a single-author session never produces a conflict (so
    /// the structure pane was blame-only): a REAL branch/merge (the pushout,
    /// `Editor::simulate_coauthor_merge`), surfaced as an object. The co-author
    /// identity is a DISTINCT author so the conflict object attributes both
    /// alternatives correctly ("who wrote which" is a fact).
    pub fn merge_coauthor_take(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let coauthor = {
            let mine = self.editor.read(cx).author().0;
            Author(if mine == 2 { 3 } else { 2 })
        };
        self.editor.update(cx, |ed, cx| {
            ed.simulate_coauthor_merge(coauthor, window, cx);
        });
        self.mode = ViewMode::Structure;
        self.refresh_structure(cx);
        cx.notify();
    }

    /// Switch the shown face; refresh the entered face's snapshot from the
    /// live editor (structure → blame/conflicts; ledger → the receipt rail).
    pub fn set_mode(&mut self, mode: ViewMode, cx: &mut Context<Self>) {
        if self.mode == mode {
            return;
        }
        self.mode = mode;
        match mode {
            ViewMode::Structure => self.refresh_structure(cx),
            ViewMode::Ledger => self.refresh_rail(cx),
            ViewMode::Buffer => {}
        }
        cx.notify();
    }

    /// One mode toggle tab (active = highlighted; click switches the face).
    fn mode_tab(&self, mode: ViewMode, cx: &mut Context<Self>) -> impl IntoElement {
        let active = self.mode == mode;
        let (bg, fg) = {
            let theme = cx.theme();
            if active {
                (theme.secondary, theme.foreground)
            } else {
                (theme.background, theme.muted_foreground)
            }
        };
        div()
            .id(mode.tab_id())
            .px_3()
            .py_1()
            .cursor_pointer()
            .bg(bg)
            .text_color(fg)
            .text_xs()
            .child(SharedString::from(mode.label()))
            .on_click(cx.listener(move |this, _ev, _window, cx| {
                this.set_mode(mode, cx);
            }))
    }

    /// The merge/conflict action button (right of the mode tabs): fork two
    /// divergent co-author takes of the open document and merge them — producing a
    /// first-class conflict object the structure pane shows. Closes the
    /// "single-author session can't make a conflict" gap with a real pushout.
    fn coauthor_button(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let (bg, fg, border) = {
            let theme = cx.theme();
            (theme.secondary, theme.foreground, theme.border)
        };
        div()
            .id("editor-merge-coauthor")
            .px_3()
            .py_1()
            .cursor_pointer()
            .bg(bg)
            .text_color(fg)
            .text_xs()
            .border_1()
            .border_color(border)
            .child(SharedString::from("⑃ merge a co-author's take"))
            .on_click(cx.listener(|this, _ev, window, cx| {
                this.merge_coauthor_take(window, cx);
            }))
    }

    /// The left file-tree column. Clicking a file opens it in the editor AND
    /// re-snapshots the structure inspector, so the structure follows the open doc.
    fn tree_column(&self, cx: &mut Context<Self>) -> AnyElement {
        let tree_el = self.tree.render(
            cx.entity(),
            move |this: &mut EditorPaneView, path, window, cx| {
                this.editor.update(cx, |ed, cx| {
                    let _ = ed.open(path, window, cx);
                });
                this.refresh_structure(cx);
            },
            cx,
        );
        div()
            .w(px(220.))
            .h_full()
            .min_h(px(0.))
            .child(tree_el)
            .into_any_element()
    }
}

impl Focusable for EditorPaneView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for EditorPaneView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let toggle = h_flex()
            .w_full()
            .gap_1()
            .px_2()
            .py_0p5()
            .bg(cx.theme().secondary)
            .border_b_1()
            .border_color(cx.theme().border)
            .child(self.mode_tab(ViewMode::Buffer, cx))
            .child(self.mode_tab(ViewMode::Structure, cx))
            .child(self.mode_tab(ViewMode::Ledger, cx))
            .child(div().flex_1())
            .child(self.coauthor_button(cx));

        // The right column is the editor buffer, the structure inspector, or
        // the receipt rail — by face.
        let right: AnyElement = match self.mode {
            ViewMode::Buffer => div()
                .flex_1()
                .h_full()
                .min_h(px(0.))
                .min_w(px(0.))
                .child(self.editor.clone())
                .into_any_element(),
            ViewMode::Structure => div()
                .flex_1()
                .h_full()
                .min_h(px(0.))
                .min_w(px(0.))
                .border_l_1()
                .border_color(cx.theme().border)
                .child(self.docviewer.clone())
                .into_any_element(),
            ViewMode::Ledger => div()
                .flex_1()
                .h_full()
                .min_h(px(0.))
                .min_w(px(0.))
                .border_l_1()
                .border_color(cx.theme().border)
                .child(self.rail.clone())
                .into_any_element(),
        };

        let body = h_flex()
            .size_full()
            .flex_1()
            .min_h(px(0.))
            .min_w(px(0.))
            .child(self.tree_column(cx))
            .child(right);

        v_flex()
            .size_full()
            .track_focus(&self.focus)
            .child(toggle)
            .child(body)
    }
}

/// A mounted editor: the editor entity + a side file tree, addressable by a
/// stable surface id. Hand this to `starbridge-v2`'s `CockpitSurface` impl.
///
/// When built firmament-backed ([`EditorSurface::firmament`]) the surface also
/// keeps the TYPED `Arc<FirmamentFs>` handle so the host can read the live
/// receipt log (the `N saves · on-ledger` chrome reflects REAL `TurnReceipt`s,
/// not a disk write). The `Arc<dyn Fs>` the editor + tree hold is the SAME
/// object — one ledger, one save path.
#[derive(Clone)]
pub struct EditorSurface {
    id: u64,
    editor: Entity<Editor>,
    /// The live interactive pane: file tree + a buffer/structure toggle. The
    /// `editor` handle above is the SAME entity this view holds (one editor, one
    /// document) — kept on the surface too so host/test open/save reach it directly.
    view: Entity<EditorPaneView>,
    /// The typed firmament handle, when this surface is firmament-backed. Lets
    /// the host surface the live receipt count (the real on-ledger save count)
    /// rather than re-deriving it from the gpui-side document patch history.
    #[cfg(feature = "firmament")]
    firmament: Option<Arc<crate::fs::FirmamentFs>>,
}

/// Build the interactive pane view over an editor + tree.
fn build_pane_view(
    editor: Entity<Editor>,
    tree: Arc<FileTree>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<EditorPaneView> {
    cx.new(|cx| EditorPaneView::new(editor, tree, window, cx))
}

impl EditorSurface {
    /// Build an editor surface over the [`Fs`] seam, rooted at `root` for the
    /// file tree. `id` is the stable surface identity within a pane (the host
    /// supplies a monotonic counter or a `Tab` discriminant).
    pub fn new(id: u64, fs: Arc<dyn Fs>, root: PathBuf, window: &mut Window, cx: &mut App) -> Self {
        let editor = cx.new(|cx| Editor::new(fs.clone(), window, cx));
        // `build_pane_view`/`EditorPaneView` hold the tree as `Arc<FileTree>`; the
        // surface is single-threaded gpui state, so the !Send/!Sync Arc is correct.
        #[allow(clippy::arc_with_non_send_sync)]
        let tree = Arc::new(FileTree::new(fs, root, cx));
        let view = build_pane_view(editor.clone(), tree, window, cx);
        Self {
            id,
            editor,
            view,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// Wrap an already-built editor entity (e.g. one the host opened a file in)
    /// with a file tree.
    pub fn from_editor(
        id: u64,
        editor: Entity<Editor>,
        tree: Arc<FileTree>,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        let view = build_pane_view(editor.clone(), tree, window, cx);
        Self {
            id,
            editor,
            view,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// **Build a FIRMAMENT-BACKED editor surface** — the cockpit-default mount:
    /// the editor edits SOVEREIGN CELLS over an in-process `Ledger` +
    /// `TurnExecutor`, and every save is a real cap-gated `SetField` turn leaving
    /// a verifiable [`TurnReceipt`](dregg_turn::TurnReceipt). No disk is touched.
    ///
    /// The mount seeds a small project of file-cells (`files`: `(path, content)`),
    /// grants the editor the per-file edit caps, opens the FIRST file THROUGH THE
    /// EDITOR's own `open()` (so the buffer the user sees is the cell's committed
    /// content, decoded from its `fields_map`), and roots the file tree at
    /// `root` over the SAME firmament fs (the left rail browses the cells, not
    /// disk). The returned surface keeps the typed `FirmamentFs` so the host can
    /// read the live receipt log.
    ///
    /// This is the PER-EDITOR mount: a firmament fs over a FRESH `OwnedSpine`
    /// (its own ledger + executor). It is the headless / test / no-live-World
    /// default. A host with a live cockpit `World` it wants edits to land on
    /// mounts [`EditorSurface::firmament_over`] instead, handing the spine that
    /// wraps the live World — then the editor edits the SAME ledger the cockpit
    /// inspects.
    // `firmament_over`/the `firmament` field type the fs as `Arc<FirmamentFs>` (it is
    // also coerced to `Arc<dyn Fs>`); single-threaded gpui state, so the !Send/!Sync Arc
    // is intentional and the type cannot become `Rc`.
    #[allow(clippy::arc_with_non_send_sync)]
    #[cfg(feature = "firmament")]
    pub fn firmament(
        id: u64,
        root: PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Self::firmament_over(
            id,
            Arc::new(crate::fs::FirmamentFs::new()),
            root,
            files,
            window,
            cx,
        )
    }

    /// **Mount a firmament-backed editor surface OVER an existing FirmamentFs** —
    /// the cockpit seam. The caller builds the [`FirmamentFs`](crate::fs::FirmamentFs)
    /// (via [`FirmamentFs::over`](crate::fs::FirmamentFs::over) the live cockpit
    /// spine, or [`FirmamentFs::new`](crate::fs::FirmamentFs::new) for a fresh
    /// one), then this seeds the `files` onto THAT fs's ledger, opens the first
    /// through the editor's real `open()`, and roots the tree over it. When `firm`
    /// is mounted over the live `World`, a save lands on the ledger the cockpit's
    /// cell inspector reads — one ledger, one save path.
    #[cfg(feature = "firmament")]
    pub fn firmament_over(
        id: u64,
        firm: Arc<crate::fs::FirmamentFs>,
        root: PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        for (path, content) in files {
            firm.seed_file(*path, content)?;
        }
        let fs: Arc<dyn Fs> = firm.clone();

        // Open the first seeded file THROUGH the editor's real `open()` path so
        // the buffer is the cell's decoded content (not a seeded in-memory
        // string) — the SAME code path the running pane uses on a tree click.
        let first = files.first().map(|(p, _)| PathBuf::from(*p));
        let editor = cx.new(|cx| {
            let mut ed = Editor::new(fs.clone(), window, cx);
            if let Some(path) = first {
                if let Err(e) = ed.open(path, window, cx) {
                    eprintln!("firmament editor: could not open seed cell: {e:#}");
                }
            }
            ed
        });
        // Single-threaded gpui state; `EditorPaneView` holds `Arc<FileTree>`.
        #[allow(clippy::arc_with_non_send_sync)]
        let tree = Arc::new(FileTree::new(fs, root, cx));
        let view = build_pane_view(editor.clone(), tree, window, cx);
        Ok(Self {
            id,
            editor,
            view,
            firmament: Some(firm),
        })
    }

    /// The typed firmament handle, if this surface is firmament-backed — lets the
    /// host read the live on-ledger save count / last receipt.
    #[cfg(feature = "firmament")]
    pub fn firmament_fs(&self) -> Option<&Arc<crate::fs::FirmamentFs>> {
        self.firmament.as_ref()
    }

    /// The number of real `TurnReceipt`s the firmament ledger has recorded (the
    /// genuine on-ledger save count), or `None` if this surface is not
    /// firmament-backed.
    #[cfg(feature = "firmament")]
    pub fn receipt_count(&self) -> Option<usize> {
        self.firmament.as_ref().map(|f| f.receipt_count())
    }

    /// Build a SEEDED editor surface: an editor whose buffer is filled in-memory
    /// with `revisions` (the last is shown; each prior one is an on-ledger patch)
    /// under the virtual `name` (drives the highlighter language), plus a real
    /// file tree over `fs`/`root`. Deterministic and disk-free for the buffer —
    /// exactly what the headless showcase bake wants (syntax-highlighted code with
    /// a real `N patches · on-ledger` status, no file to load). The tree still
    /// reflects `fs`/`root` so the left rail shows a real project.
    pub fn seeded(
        id: u64,
        fs: Arc<dyn Fs>,
        root: PathBuf,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        let editor = cx.new(|cx| {
            let mut ed = Editor::new(fs.clone(), window, cx);
            ed.seed_content(name, revisions, window, cx);
            ed
        });
        // Single-threaded gpui state; `EditorPaneView` holds `Arc<FileTree>`.
        #[allow(clippy::arc_with_non_send_sync)]
        let tree = Arc::new(FileTree::new(fs, root, cx));
        let view = build_pane_view(editor.clone(), tree, window, cx);
        Self {
            id,
            editor,
            view,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// The underlying editor entity, for host-side open/save calls.
    pub fn editor(&self) -> &Entity<Editor> {
        &self.editor
    }

    /// Install the host save hook on the mounted editor — the node wire. When the
    /// cockpit is `--node`-attached the host calls this so an in-editor save
    /// (Cmd-S) ALSO submits a client-signed turn to the live node (the editor pane's
    /// OWN save path drives the node write, not a separate direct call). See
    /// [`crate::editor::SaveCallback`].
    pub fn set_save_callback(&self, cb: crate::editor::SaveCallback, cx: &mut App) {
        self.editor
            .update(cx, |ed, _cx| ed.set_save_callback(Some(cb)));
    }

    // --- the methods the host's `CockpitSurface` impl forwards to ------------

    /// `CockpitSurface::item_id` payload.
    pub fn surface_id(&self) -> u64 {
        self.id
    }

    /// `CockpitSurface::tab_label`: the document title (filename + dirty dot).
    pub fn tab_label(&self, cx: &App) -> SharedString {
        self.editor.read(cx).title()
    }

    /// `CockpitSurface::is_dirty`: unsaved edits in the buffer.
    pub fn is_dirty(&self, cx: &App) -> bool {
        self.editor.read(cx).is_dirty()
    }

    /// `CockpitSurface::focus_handle`: the editor's focus handle.
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.editor.read(cx).focus_handle(cx)
    }

    /// `CockpitSurface::render_body`: the live interactive pane — a file tree, a
    /// buffer/structure toggle, and (by mode) the editor buffer or the document's
    /// blame + conflict-objects inspector. Renders the one owned [`EditorPaneView`]
    /// entity, so a toggle click (which `cx.notify()`s that entity) re-renders the
    /// pane without the host re-driving it. Returns an `AnyElement` so the host
    /// trait stays object-safe.
    pub fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        // `flex_1().min_h(0).min_w(0)` makes the pane claim its parent's full
        // measured height robustly whether laid out in a flex COLUMN (showcase) or
        // directly in a flex ROW (self-hosting).
        div()
            .size_full()
            .flex_1()
            .min_h(px(0.))
            .min_w(px(0.))
            .child(self.view.clone())
            .into_any_element()
    }

    /// The interactive pane view (host-side: read/set the buffer/structure mode).
    pub fn view(&self) -> &Entity<EditorPaneView> {
        &self.view
    }

    /// Switch the pane's shown face (buffer ⇄ structure) host-side — what a test or
    /// a host menu drives to surface the blame/conflicts inspector.
    pub fn set_mode(&self, mode: ViewMode, cx: &mut App) {
        self.view.update(cx, |v, cx| v.set_mode(mode, cx));
    }

    /// The face currently shown.
    pub fn mode(&self, cx: &App) -> ViewMode {
        self.view.read(cx).mode()
    }

    /// The pane's receipt-rail entity (the LEDGER face) — host/test reads of
    /// the open file's save timeline (chip count, latest hash, verify verdict).
    pub fn receipt_rail(&self, cx: &App) -> Entity<ReceiptRail> {
        self.view.read(cx).receipt_rail().clone()
    }
}
