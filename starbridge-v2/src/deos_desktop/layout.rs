//! **The spatial + content persistence layer** — the durable desktop layout: every
//! icon position, every open window's geometry and TYPE, every document cell's
//! prose, and the desktop's customization preferences. All serialized to one
//! sidecar JSON file and restored on open.

use std::path::PathBuf;

use gpui::{px, Pixels, Point};

use super::chrome::NT_DESKTOP_BG;

/// A persisted desktop position for one cell-icon (`(x, y)` on the desktop) — keyed
/// by the cell's hex id so it survives across worlds with the same cells.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct IconPos {
    pub cell: String,
    pub x: f32,
    pub y: f32,
}

/// A persisted open-window geometry for one cell (id + frame). Persisting this is
/// what makes "you arrange your world and it STAYS" true for windows too.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct WinGeom {
    pub cell: String,
    pub x: f32,
    pub y: f32,
    pub w: f32,
    pub h: f32,
    pub minimized: bool,
    /// Which window TYPE this geometry restores — inspector / document editor /
    /// links view / transcript. Defaults to the inspector for legacy layouts.
    #[serde(default)]
    pub kind: WinKindTag,
}

/// The persisted tag of a window's type (the serializable face of `WinKind`).
#[derive(
    Clone, Copy, Default, PartialEq, Eq, Hash, Debug, serde::Serialize, serde::Deserialize,
)]
pub enum WinKindTag {
    #[default]
    Inspector,
    DocEditor,
    Links,
    Transcript,
    /// The workflow-composer surface (intents + composed workflow + flow refinement).
    Workflow,
    /// **An android-cell** — a live, cap-confined Android app hosted as a window: its
    /// captured surface is the window body, and the window's pointer/key events are
    /// mapped (via [`super::android_window`]) into cap-gated `AndroidInput` driven into
    /// the confined runtime. Clicking the window TAPS the android app.
    AndroidCell,
    /// **The DOCUMENT EXPLORER** — a Pharo-moldable multi-face inspector of a
    /// document cell's patch-theoretic substance: a tabbed surface over the live
    /// `dregg_doc` faces (History time-travel scrubber · the DocGraph atoms+edges ·
    /// Blame authorship). Read-only reflection; the editing happens in `DocEditor`.
    DocExplorer,
    /// **The WORLD EXPLORER** — the "My Computer" of the verified World: a tabbed
    /// inspector over the World itself (the ledger census · the receipt-log chronicle ·
    /// the Σ-balance conservation invariant). Anchored on a sentinel cell (the user).
    WorldExplorer,
    /// **THE CONTENT-IR PANE** — a window whose body is a real `deos_view::ViewNode`
    /// (a card-as-cell) rendered through deos-view's NATIVE renderer (`AppletView`),
    /// beside the native-chrome surfaces. Proves the desktop hosts portable-IR content
    /// (the same tree a web renderer would render), not just hand-built native gpui.
    /// The rendered renderer entity lives in `viewnode_panes` (gated on `card-pane`),
    /// so this variant is a marker like `WorldExplorer`.
    ViewNodePane,
    /// **The AGENT ROOM** — the desktop face of an agent-as-inhabitant: a tabbed
    /// inspector over one resident cell's provable activity (the held mandate ·
    /// the receipted actions · the authorization boundary), built purely from the
    /// live World by [`crate::agent::AgentActivity`]. Anchored on the room's own
    /// sentinel cell; per-window state lives in `agent_rooms`, so this variant is
    /// a marker like `WorldExplorer`.
    AgentRoom,
    /// **THE APP SHELF** — the roster of pre-built starbridge-apps (the registry) as a
    /// desktop window: name · what-it-does · manifest facts per app, LAUNCH (a real
    /// `launch_on_world` — the app's cell + receipt land on the LIVE World) and the
    /// wired live fires. The shelf's state (`AppShelfState`: the registry + the
    /// installed set) lives on the desktop (gated on `app-registry`), so this variant
    /// is a marker like `WorldExplorer`. Anchored on a sentinel cell (the user).
    AppShelf,
    /// **THE EXCHANGE FLOOR** — the $DREGG agent-economy window: compute OFFERS as
    /// live cells (each carrying the compute-exchange job program) posted / taken /
    /// settled by real verified turns, the execution-lease rail metering every take,
    /// and Σδ = 0 read off the LIVE ledger at settlement. The floor's state
    /// (`ExchangeFloorState`: the order book) lives on the desktop (gated on
    /// `app-registry`), so this variant is a marker like `AppShelf`. Anchored on a
    /// sentinel cell (the user).
    ExchangeFloor,
    /// **THE MATRIX ROOM** — membrane-over-Matrix in the shipped desktop: rooms as
    /// live cells on the desktop's OWN World, every send a receipted turn decoded
    /// back off the receipt chain, and the REAL executor envelope legs (mint ·
    /// fail-closed rehydrate · receipted drive · settlement-gated stitch) riding
    /// the `deos_matrix` wire shape over the recorded/mock sync (the live
    /// homeserver a named env-gated seam). Its state lives in the desktop's
    /// `matrix_rooms` / `matrix_stack` (gated on `dev-surfaces`), so this variant
    /// is a marker like `AgentRoom`. Anchored on its own sentinel cell.
    MatrixRoom,
    /// **THE PROVENANCE WALKER** — walk the World's receipt chain hash-by-hash,
    /// every link RECOMPUTED as you walk (the state-root handoff between
    /// consecutive receipts + each agent's blocklace back-edge, both re-derived,
    /// never trusted — see `super::provenance_walker`). Per-window state (the walk
    /// cursor + the go-to landing) lives in `provenance_walkers`, so this variant
    /// is a marker like `WorldExplorer`. Anchored on its own sentinel cell.
    ProvenanceWalker,
    /// **THE ATTACH WIZARD** — the warm "send your AI to live here" onboarding: a
    /// five-breath walk (name · brain · mandate · review · hire) over the hireling
    /// rail that lands a real confined resident in the Agent Room, already stepping
    /// (see `super::attach_wizard`). Per-window state (the walk position + the
    /// choices) lives in `attach_wizards`, so this variant is a marker like
    /// `AgentRoom`. Anchored on its own sentinel cell; the render is gated on
    /// `dev-surfaces` (the hireling rail), falling back to the inspector otherwise.
    AttachWizard,
    /// **MY DREGG COMPUTERS** — the desktop face of *have a Dregg Computer*: the
    /// vats (private verified Worlds, each a content-addressed cell on a DreggNet
    /// ServerFleet) this account can reach, with CONNECT attaching one over the
    /// proven HTTP+SSE wire path and reflecting its remote cells + receipt stream
    /// live (see [`super::dregg_computers`]). Per-window state lives in
    /// `dregg_computers`; the attachment itself lives on the desktop (`vat_link`)
    /// so your computer stays attached with the window closed. Anchored on its
    /// own sentinel cell.
    DreggComputers,
    /// **THE MAIL ROOM** — the desktop face of the [`crate::letter_office`]: mail
    /// between agents as cells on the live World (inbox · outbox · mail-ledger). A
    /// letter IS a cell carrying its markdown in the heap; sending drops it in an outbox
    /// cell, delivery is a receipted turn moving it to an inbox cell. Per-window state
    /// (the compose recipient + the shown face) lives in `mail_rooms`, so this variant
    /// is a marker like `AgentRoom`. Anchored on its own sentinel cell.
    MailRoom,
}

/// A persisted document's text, keyed by the cell's hex id — the CONTENT
/// persistence that pairs with the spatial persistence. A document cell's prose is
/// durable state; the sidecar mirrors it so a reopened desktop restores the exact
/// authored text.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct DocText {
    pub cell: String,
    pub text: String,
}

/// **THE DESKTOP LAYOUT — the load-bearing spatial-persistence state.** The whole
/// arrangement of the user's world: every icon position, every open window's
/// geometry, every document's prose, and the customization prefs. Serialized to a
/// sidecar JSON file ([`DesktopLayout::default_path`]) on every change and reloaded
/// on open, so the arrangement is durable state, not ephemeral view-state.
#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct DesktopLayout {
    pub icons: Vec<IconPos>,
    pub windows: Vec<WinGeom>,
    /// Persisted document text per cell (the CONTENT persistence — pairs with the
    /// spatial persistence above so a reopened desktop restores the authored prose).
    #[serde(default)]
    pub docs: Vec<DocText>,
    /// The desktop's customization preferences (appearance / layout knobs the user
    /// sets via Properties → Preferences). Persisted like everything else.
    #[serde(default)]
    pub prefs: DesktopPrefs,
}

/// **Customization** — the desktop's persisted preferences, edited through the
/// Properties/Preferences surface. Layout-level customization (it carries no
/// authority, just appearance), so changing it is a pure persisted layout change.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct DesktopPrefs {
    /// The desktop background colour (one of a small NT-era palette).
    pub bg: u32,
    /// Whether icon captions show the grouped balance line.
    pub show_balances: bool,
    /// Whether new document windows default to word- vs line-granularity edits.
    pub word_granularity: bool,
    /// The icon auto-arrange column height (rows per column on a fresh desktop).
    pub grid_rows: u32,
    /// Whether the newcomer has already been greeted. `false` (the default, and the
    /// value a fresh/legacy layout deserializes to) means the warm WELCOME moment
    /// shows on open; dismissing it sets this `true` so the calm front door appears
    /// exactly once and the room is thereafter the bare, breathing desktop.
    #[serde(default)]
    pub welcomed: bool,
    /// Whether the GOSSAMER transclusion threads paint between windows (the cyan
    /// elbow connectors from a quoting document to each quoted surface — see
    /// `super::threads`). Defaults to `true` (fresh AND legacy layouts show the
    /// docuverse's geometry out of the box); the View-menu toggle flips + persists it.
    #[serde(default = "default_show_threads")]
    pub show_threads: bool,
    /// **The Spotter's RECENT-JUMPS trail** — the replay strings of the last 8
    /// dispatches, newest first (a jump's label, or a command's canonical verb line
    /// — see `super::spotter::replay_string`). The empty-query palette greets you
    /// with these, RE-RESOLVED against the live desktop on show (a closed window's
    /// jump quietly drops; a recalled command re-resolves its cell prefixes), so
    /// persisting plain strings is safe: nothing stale can dispatch. Persisted like
    /// every other preference; `#[serde(default)]` keeps legacy layouts loading.
    #[serde(default)]
    pub recent_jumps: Vec<String>,
}

/// The serde default for [`DesktopPrefs::show_threads`] — `true`, so a legacy layout
/// (serialized before the field existed) deserializes with the threads visible.
fn default_show_threads() -> bool {
    true
}

impl Default for DesktopPrefs {
    fn default() -> Self {
        DesktopPrefs {
            bg: NT_DESKTOP_BG,
            show_balances: true,
            word_granularity: false,
            grid_rows: 6,
            welcomed: false,
            show_threads: true,
            recent_jumps: Vec::new(),
        }
    }
}

impl DesktopLayout {
    /// The default sidecar path (under the user's data dir, falling back to a temp
    /// path). The desktop saves here on every spatial change and loads here on open.
    pub fn default_path() -> PathBuf {
        if let Some(dir) = dirs_next_data() {
            dir.join("deos-desktop-layout.json")
        } else {
            std::env::temp_dir().join("deos-desktop-layout.json")
        }
    }

    /// Load a persisted layout from `path`, or an empty layout if none exists / it
    /// is corrupt (a fresh desktop falls back to the auto-arranged grid).
    pub fn load(path: &PathBuf) -> Self {
        std::fs::read(path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_default()
    }

    /// **Persist the layout** to `path` (atomic-ish: write then rename), on the
    /// calling thread. The COLD-path write: preferences flips, the welcome
    /// dismissal, a window close, and the bake hooks (which reopen + assert
    /// immediately, so they need the write durable before they return). The HOT
    /// interaction paths — window drag/resize, icon drag-end, per-keystroke doc
    /// mirrors — go through [`LayoutSaver`] instead: this serialization covers
    /// EVERY document's full prose, and paying it synchronously on the UI thread
    /// per gesture is the jank the perf scout flagged. Errors are swallowed (a
    /// read-only FS still gives a live desktop; only persistence is lost).
    pub fn save(&self, path: &PathBuf) {
        if let Ok(json) = serde_json::to_vec_pretty(self) {
            let tmp = path.with_extension("json.tmp");
            if std::fs::write(&tmp, &json).is_ok() {
                let _ = std::fs::rename(&tmp, path);
            }
        }
    }

    pub(super) fn icon_pos(&self, cell: &str) -> Option<Point<Pixels>> {
        self.icons
            .iter()
            .find(|p| p.cell == cell)
            .map(|p| Point::new(px(p.x), px(p.y)))
    }

    pub(super) fn set_icon_pos(&mut self, cell: &str, x: f32, y: f32) {
        if let Some(p) = self.icons.iter_mut().find(|p| p.cell == cell) {
            p.x = x;
            p.y = y;
        } else {
            self.icons.push(IconPos {
                cell: cell.to_string(),
                x,
                y,
            });
        }
    }

    pub(super) fn win_geom(&self, cell: &str, kind: WinKindTag) -> Option<WinGeom> {
        self.windows
            .iter()
            .find(|w| w.cell == cell && w.kind == kind)
            .cloned()
    }

    pub(super) fn set_win_geom(&mut self, g: WinGeom) {
        if let Some(w) = self
            .windows
            .iter_mut()
            .find(|w| w.cell == g.cell && w.kind == g.kind)
        {
            *w = g;
        } else {
            self.windows.push(g);
        }
    }

    pub(super) fn drop_win(&mut self, cell: &str, kind: WinKindTag) {
        self.windows.retain(|w| !(w.cell == cell && w.kind == kind));
    }

    pub(super) fn doc_text(&self, cell: &str) -> Option<String> {
        self.docs
            .iter()
            .find(|d| d.cell == cell)
            .map(|d| d.text.clone())
    }

    pub(super) fn set_doc_text(&mut self, cell: &str, text: &str) {
        if let Some(d) = self.docs.iter_mut().find(|d| d.cell == cell) {
            d.text = text.to_string();
        } else {
            self.docs.push(DocText {
                cell: cell.to_string(),
                text: text.to_string(),
            });
        }
    }
}

/// **The coalescing background layout writer** — the HOT-path half of
/// persistence. One writer thread owns the file; the UI thread's `save` is a
/// clone + channel send (microseconds, no serialization, no IO). The writer
/// drains the channel to the NEWEST snapshot before each write, so a burst of
/// drag-move gestures costs ONE serialize+rename instead of one per event, and
/// last-sent always wins (a single writer means no stale write can land after a
/// newer one). The honest tradeoff: a snapshot sent microseconds before process
/// exit may not reach disk — which is why the cold paths (prefs, welcome, close,
/// bake hooks) still call [`DesktopLayout::save`] synchronously.
pub struct LayoutSaver {
    tx: std::sync::mpsc::Sender<DesktopLayout>,
}

impl LayoutSaver {
    /// Spawn the writer thread for `path`. The thread parks on an empty channel
    /// and exits when every sender is dropped (recv errors out).
    pub fn spawn(path: PathBuf) -> Self {
        let (tx, rx) = std::sync::mpsc::channel::<DesktopLayout>();
        std::thread::Builder::new()
            .name("deos-layout-saver".into())
            .spawn(move || {
                while let Ok(mut latest) = rx.recv() {
                    // Coalesce the burst: only the newest snapshot hits the disk.
                    while let Ok(newer) = rx.try_recv() {
                        latest = newer;
                    }
                    latest.save(&path);
                }
            })
            .ok();
        LayoutSaver { tx }
    }

    /// Queue `layout` for persistence — a clone + send; never blocks on IO. If
    /// the writer thread is gone (spawn failed / shutdown) this silently drops,
    /// mirroring `DesktopLayout::save`'s swallow-errors contract.
    pub fn save(&self, layout: &DesktopLayout) {
        let _ = self.tx.send(layout.clone());
    }
}

#[cfg(test)]
mod saver_tests {
    use super::*;

    /// A burst of queued snapshots coalesces and the LAST one is what the file
    /// holds (poll-load until the writer catches up — the channel guarantees
    /// order, the single writer guarantees no stale overwrite).
    #[test]
    fn saver_coalesces_and_last_write_wins() {
        let path = std::env::temp_dir().join(format!(
            "deos-layout-saver-test-{}.json",
            std::process::id()
        ));
        let _ = std::fs::remove_file(&path);
        let saver = LayoutSaver::spawn(path.clone());

        for rows in 1..=9u32 {
            let mut l = DesktopLayout::default();
            l.prefs.grid_rows = rows;
            saver.save(&l);
        }

        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        loop {
            let loaded = DesktopLayout::load(&path);
            if loaded.prefs.grid_rows == 9 {
                break;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "writer never landed the newest snapshot (got rows={})",
                loaded.prefs.grid_rows
            );
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        let _ = std::fs::remove_file(&path);
    }
}

/// A platform-appropriate data dir (no extra dep): `$XDG_DATA_HOME` /
/// `~/Library/Application Support` / `~/.local/share`.
fn dirs_next_data() -> Option<PathBuf> {
    if let Ok(x) = std::env::var("XDG_DATA_HOME") {
        if !x.is_empty() {
            return Some(PathBuf::from(x).join("deos"));
        }
    }
    let home = std::env::var("HOME").ok()?;
    #[cfg(target_os = "macos")]
    {
        Some(PathBuf::from(home).join("Library/Application Support/deos"))
    }
    #[cfg(not(target_os = "macos"))]
    {
        Some(PathBuf::from(home).join(".local/share/deos"))
    }
}
