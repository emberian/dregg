//! **THE deos DESKTOP** — a Windows-NT / Pharo-Smalltalk workbench over the live
//! verified World.
//!
//! This is the answer to the cockpit's three holes: NO WAY TO ACTUATE OR COMPOSE
//! the parts, ZERO METAPHORS, ZERO SPATIAL PERSISTENCE. The desktop gives the user
//! the oldest, densest, most legible metaphors there are — a **desktop of icons**,
//! **overlapping windows**, **right-click context menus**, a **menu bar**, and a
//! reflexive **inspector** — and wires every one of them to REAL substance:
//!
//!   * **Icons ARE cells.** Each icon on the desktop is one sovereign cell read off
//!     the live `World` ledger ([`crate::world::World`]): its id, its kind, its
//!     balance/nonce/lifecycle. Drag it and it MOVES; its position is SAVED.
//!   * **Spatial persistence** (the #1 missing thing). The desktop layout — every
//!     icon position, every open window's geometry — is real state, serialized to a
//!     sidecar ([`DesktopLayout`]) and RESTORED on reopen. You arrange your world
//!     and it STAYS.
//!   * **Windows.** Double-click an icon → it opens in a movable NT window (title
//!     bar, min/max/close, a dense inspector body). Windows overlap; their geometry
//!     persists too.
//!   * **Right-click context menus** — the ACTUATION. Right-click any cell-icon → a
//!     menu of EVERY action available on it (inspect, fire its affordances as
//!     verified turns, grant a cap, transfer), lit if the cap is held, dim if not.
//!     This is Smalltalk "do it": the user actually DOES things to the parts.
//!   * **Compose** — drag one cell-icon ONTO another to act across them (transfer /
//!     grant), the dropped affordance.
//!
//! REAL UNDERNEATH: a fired action commits a real `dregg_turn` through the embedded
//! verified executor ([`crate::world::World::commit_turn`]) leaving a `TurnReceipt`;
//! the inspector shows the cell's real reflected faces; the layout persists as real
//! JSON state. Built NEW, beside the cockpit — it does not touch the cockpit tree.

// ── Submodules ────────────────────────────────────────────────────────────────────
// The desktop is split into a reusable chrome kit + a persistence layer + this glue.
//   * `chrome`  — the NT widget infrastructure (palette, bevel/face primitives,
//                 id/number formatting). The reusable component layer.
//   * `layout`  — the spatial + content persistence (DesktopLayout and friends).
// The remaining surfaces (windows, menus, document editing, properties, actuation,
// rendering) live here as `impl DeosDesktop` blocks over the shared chrome/layout.
/// THE AGENT ROOM — the desktop face of an agent-as-inhabitant: one resident
/// cell's provable activity (mandate · receipted actions · authorization
/// boundary) rendered off the live World via [`crate::agent::AgentActivity`] —
/// the executor's account of the agent, never its self-report.
pub mod agent_room;
pub mod android_window;
/// THE APP SHELF — the pre-built starbridge-apps as first-class desktop citizens: a
/// shelf window listing every `crate::app_registry` app (name · what-it-does ·
/// manifest facts), per-app LAUNCH (`AppEntry::launch_on_world` — the app's cell +
/// program seed onto the LIVE World and its representative affordance COMMITS as a
/// real verified turn), desktop icons wearing the app's own face, and the wired
/// card fires as further live turns. gpui-free model + the View's listeners, split
/// clobber-safe. Gated on `app-registry` (which implies `embedded-executor`).
#[cfg(feature = "app-registry")]
pub mod app_shelf;
/// THE ATTACH WIZARD — "send your AI to live here" in five minutes: a warm desktop
/// onboarding over the hireling rail (name your resident · pick the brain — hermetic
/// on-box default or BYO key with the brain-pocket invariant explained · set an
/// attenuated mandate + a small budget by direct manipulation · HIRE) that lands a
/// real confined resident in the Agent Room already stepping. Its HIRE routes through
/// the ONE [`hireling::HirelingState::hire_with`] the room's own button delegates to
/// (no duplicated hire logic). Gated on `dev-surfaces` (the deos-hermes brain/gate
/// rail), like [`hireling`].
#[cfg(feature = "dev-surfaces")]
pub mod attach_wizard;
/// THE DISCORD-BOT SURFACE — the desktop face of the one dregg-driven bot: a card
/// that drives the bot's ops as dregg turns (`drive_on_world` on the embedded executor
/// / the `op_request` POST to the live bot's `/api/op`) and renders the bot's activity
/// feed as a portable `deos_view::ViewNode` card (the SAME shape the bot renders as a
/// Discord embed). The core (ops · drive · feed) is gpui-free; the card render is gated
/// on `card-pane` (where `deos-view` is in scope).
pub mod bot_surface;
// THE CARD FEED OF THE PULSE — attached-World `CardPane`s ride the same dynamics
// beat the AppletView panes do (wave 3's named gap): the quiet/loud pulse pair over
// the desktop's open-card registry, plus the proven foreign-turn-repaints-a-card
// bake. Gated on `card-pane` (where `CardPane`/`deos-view` are in scope).
#[cfg(feature = "card-pane")]
pub mod card_pulse;
pub mod chrome;
pub mod docgraph_view;
/// MY DREGG COMPUTERS — the desktop face of *have a Dregg Computer*: the vats
/// (private verified Worlds, each a content-addressed cell on a DreggNet
/// ServerFleet, admitted behind a funded lease, scoped by a `vat:<cell-id>`
/// capability) this account can reach. The roster reads the designed gateway
/// `GET /v1/vats` seam (fixture until it lands — named honestly on the glass);
/// CONNECT attaches one over the proven `--node <url>` HTTP+SSE wire path and
/// reflects its remote cells + receipt stream LIVE. gpui-free roster/attach
/// model + the View's listeners, split clobber-safe like `agent_room`.
pub mod dregg_computers;
/// THE EXCHANGE FLOOR — the $DREGG agent economy as a desktop window: compute
/// OFFERS as live cells (each carrying the compute-exchange job program), posted /
/// taken-under-lease / settled by REAL verified turns (the executor refuses an
/// over-budget take in-band; settlement conserves the budget Σδ=0, re-read off the
/// LIVE ledger), with the App Shelf's compute-exchange + execution-lease apps as
/// the substrate (launched if not installed). gpui-free order-book model + the
/// View's listeners, split clobber-safe. Gated on `app-registry`.
#[cfg(feature = "app-registry")]
pub mod exchange_floor;
/// THE FACE-SCROLL REGISTRY — one persistent [`gpui::ScrollHandle`] per dense
/// scrolling face (window bodies keyed by cell × kind × tab; chrome overlays by
/// name), so every surface scrolls behind a REAL NT scrollbar
/// ([`chrome::nt_scroll_face`]) and keeps its scroll position across repaints,
/// tab flips, and window reopens — position as view-state, like window geometry.
pub mod face_scroll;
/// The Pharo HALO — direct-manipulation handles floating on a selected icon/window,
/// each firing the same actuation the right-click menu does ("mold it in place").
pub mod halo;
/// THE HIRELING WELD — HIRE / STEP / FIRE a REAL confined resident from the Agent
/// Room: hire mints its cell + cap-gated gateway on the LIVE World
/// ([`crate::resident_agent::hire_resident_seeded`]), STEP drives one
/// perceive→decide→act beat whose admitted calls mirror as real verified turns
/// (THE PULSE announces them) and whose gate refusals surface as amber toasts +
/// REFUSED rows, FIRE commits a real `RevokeCapability` turn. Gated on
/// `dev-surfaces` (where the deos-hermes brain/gate rail lives).
#[cfg(feature = "dev-surfaces")]
pub mod hireling;
pub mod layout;
/// THE MAIL ROOM — the desktop face of the [`crate::letter_office`]: mail between
/// agents as cells on the live World. Inbox (letters delivered to you) · Outbox (letters
/// you sent, each Outbound one carrying a *deliver now* button that fires one ferry round
/// as a real receipted turn) · Mail-Ledger (every letter in the town). A letter IS a cell
/// carrying its markdown in the heap; the room re-scans the live ledger each paint (never
/// a cache). gpui-free faces + the View's listeners, split clobber-safe like `agent_room`.
pub mod mail_room;
/// THE MATRIX ROOM — membrane-over-Matrix in the shipped desktop: rooms as live
/// cells on the desktop's OWN World, every send a receipted `SetField` turn whose
/// timeline is decoded back off the recorded receipt chain, and the real
/// [`crate::shared_fork::MembraneFrustum`] envelope legs (mint · fail-closed
/// rehydrate · receipted drive · settlement-gated stitch) riding the exact
/// `deos_matrix` wire shape over the recorded/mock sync backend. The live
/// homeserver is a NAMED env-gated seam (`DEOS_HOMESERVER_URL`), shown honestly.
/// The sentinel/tabs/codec/seam compile everywhere; the wire-typed half is gated
/// on `dev-surfaces` (where `deos-matrix` lives), falling back to the inspector
/// body like the other gated windows.
pub mod matrix_room;
/// THE PROVENANCE WALKER — walk the World's receipt chain hash-by-hash in the
/// dark-console window: every row a committed receipt with BOTH its links
/// RE-DERIVED on the spot (the state-root handoff between consecutive receipts,
/// and each agent's blocklace back-edge recomputed with blake3 — never read,
/// never trusted), the walk cursor stepping back edge-by-edge, and a
/// root-verified go-to-that-point off [`crate::provenance_navigator::goto`].
pub mod provenance_walker;
/// THE REWIND RAIL — scrub the whole desktop through root-verified history: the
/// bottom-docked timeline over `crate::replay::History` (gpui-free projection
/// model + the rail render + the effective-ledger accessor every reader routes
/// through). The past is read-only; the LIVE chip returns you.
pub mod rewind;
pub mod spotter;
// THE GRAPHIDEOS SYSTEMUI CAP-CHROME ON THE GLASS — the gpui body that paints a focused
// `WinKind::AndroidCell` window as the phone's SystemUI (status bar + quick-settings shade
// + hand-over sheet), over the proven `crate::systemui_caps::SystemUiCapChrome` model.
// App/presentation; no new kernel effect. Gated on `android-systemui` (where `android-cell`
// + the cap-chrome model are in scope); the window falls back to the inspector body off it.
#[cfg(feature = "android-systemui")]
pub mod systemui_chrome_render;
/// GOSSAMER — the visible transclusion threads: a cyan NT elbow connector drawn
/// between a document window quoting cell X and whatever surface shows X, walkable
/// from either endpoint dot (Ted Nelson's parallel visible connections over real
/// receipted quotes). Gated on the persisted `show_threads` preference (View menu).
pub mod threads;
/// PULSE TOASTS — the World's motion arriving as small NT cards (green committed /
/// amber REFUSED), fed by the pulse, self-retiring, click-through to the Transcript.
pub mod toasts;
// THE CONTENT-IR BRIDGE — a desktop window whose body is a real `deos_view::ViewNode`
// rendered through deos-view's NATIVE renderer (the portable-IR content surface beside
// the native-chrome panes). Gated on `card-pane` (pulls deos-view + deos-js); the
// window-type registration below falls back to the inspector body when it is off.
#[cfg(feature = "card-pane")]
pub mod viewnode_pane;
pub mod virtual_face;
pub mod welcome;
pub mod workflow;
pub mod world_explorer;

pub use workflow::{IntentKind, WorkflowState, WorkflowStep};

/// The witnesses of one reflective-cockpit loop over the shipped World-Status pane (the
/// return of [`DeosDesktop::bake_agent_rewrites_viewnode_pane`]).
#[cfg(feature = "card-pane")]
pub struct ViewnodeRewrite {
    /// REFLECT-ON saw the pre-existing `World Status` header on the live surface.
    pub reflected_header: bool,
    /// REFLECT-ON counted the live surface's `bind` rows (the panel has 3).
    pub reflected_rows: usize,
    /// The surface had NO `refresh` button before the agent's rewrite.
    pub before_has_button: bool,
    /// The agent's re-folded tree carries the `refresh` button.
    pub after_has_button: bool,
    /// The LIVE entity the desktop window paints now carries the rewrite (the real
    /// window's surface IS the rewritten one).
    pub live_after_has_button: bool,
    /// How many receipted provenance turns the rewrite committed (addButton + relabel).
    pub receipt_count: usize,
    /// Whether the surface's blame attributes the rewrites to the agent (accountable).
    pub blamed_agent: bool,
}

/// The witnesses of the agent COMPOSING a brand-new cockpit surface — the World Board —
/// from an empty root, informed by the live World (the return of
/// [`DeosDesktop::bake_agent_composes_world_board`]). The deeper reflective loop: the
/// agent stops editing the cockpit and co-authors a NEW surface OF it.
#[cfg(feature = "card-pane")]
pub struct WorldBoardComposition {
    /// REFLECT-ON: the agent's authoring surface began as a bare empty root (it composed
    /// from nothing, not by tweaking a pre-existing pane).
    pub started_empty: bool,
    /// READ THE WORLD: the live cell count the agent crawled off the real ledger (which
    /// the host cross-checks against its own ledger read).
    pub crawled_cells: usize,
    /// The agent authored the board's title text from nothing.
    pub composed_title: bool,
    /// How many LIVE state-bound rows the agent composed (the board has 3).
    pub composed_bind_rows: usize,
    /// The agent composed the `refresh` affordance button.
    pub composed_button: bool,
    /// How many receipted provenance turns the composition committed (one per gesture: a
    /// title + 3 bind rows + a button = 5).
    pub receipt_count: usize,
    /// Whether the board's blame attributes the composition to the agent (accountable).
    pub blamed_agent: bool,
    /// A REAL second `viewnode_pane` desktop window now hosts the agent-composed board.
    pub mounted_window: bool,
}

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use gpui::prelude::FluentBuilder;
use gpui::{
    div, px, AnyElement, AppContext, ClickEvent, Context, Div, Entity, FocusHandle, FontWeight,
    InteractiveElement, IntoElement, KeyDownEvent, MouseButton, MouseDownEvent, MouseMoveEvent,
    MouseUpEvent, ParentElement, Pixels, Point, Render, ScrollHandle, Stateful,
    StatefulInteractiveElement, Styled, Subscription, Window,
};

use gpui_component::input::{Input, InputEvent, InputState};
use gpui_component::{v_virtual_list, VirtualListScrollHandle};

use dregg_cell::lifecycle::CellLifecycle;
use dregg_types::CellId;

use dregg_doc::{
    blame, blame_summary, content, resolutions_for, text_from_heap, Author, Doc, DocGraph,
    DocHeapCell, Granularity, PatchId, Regime, ResolutionChoice,
};

use crate::world::{grant_capability, transfer, CommitOutcome, World};

// The chrome kit + persistence types are re-exported so existing call sites
// (`deos_desktop::id_hex`, `deos_desktop::DesktopLayout`, …) keep working.
pub use android_window::{AndroidInputCmd, AndroidWindow, ANDROID_WINDOW_TITLE};
pub use chrome::{
    bevel_raised, bevel_sunken, bevel_window, face_gauge, face_row, face_row_color, face_section,
    fmt_balance, id_hex, id_short, kind_short, nt_scroll_face, nt_scrollbar, pxf, DOC_CHUNK_BYTES,
    DOC_MAX_CHUNKS, DOC_REV_SLOT, DOC_TEXT_BASE, GLYPH_CLOSE, GLYPH_GRIP, GLYPH_MAX, GLYPH_MIN,
    GLYPH_RESTORE, ICON_H, ICON_W, MENUBAR_H, NT_DESKTOP_BG, NT_DIM, NT_FACE, NT_FACE_DARK,
    NT_HILIGHT, NT_ICON_LABEL, NT_LABEL, NT_MENU_HILIGHT, NT_OK, NT_PANEL, NT_RULE, NT_SELECT,
    NT_SHADOW, NT_TEXT, NT_TITLE_ACTIVE, NT_TITLE_INACTIVE, NT_TITLE_INACTIVE_TEXT, NT_TITLE_TEXT,
    NT_WARN, WIN_MIN_H, WIN_MIN_W,
};
pub use face_scroll::{FaceScrollKey, FaceScrollRegistry};
pub use layout::{DesktopLayout, DesktopPrefs, DocText, IconPos, WinGeom, WinKindTag};
pub use virtual_face::{visible_row_range, VirtualFaceRegistry};

use halo::HaloTarget;

// ── UNCAPPED-FACE ROW RENDERERS (pure; the View owns the virtual list state) ──────
//
// The virtualized log faces (`render_transcript_body`, the receipt console) build
// each visible row through these free functions. Keeping them pure — one datum in,
// one inert row element out, no view context — is the clobber-safe split the dense
// window bodies already hold: the kit's `v_virtual_list` closure re-enters the View
// for the LIVE slice, then maps each item through a renderer that could not care
// less where the row came from. The `*_text` twins carry the exact glyphs the row
// paints so the bakes can witness "offset N shows the right receipts" as plain
// strings, with no window (see `bake_transcript_rows_at`).

/// Fixed row pitch (px) for the single-line receipt-log faces — the transcript and
/// the receipt console. One line of 11px text plus the old `.gap_1()` breathing,
/// declared uniformly so `virtual_face::visible_row_range` (and the kit) can map an
/// offset to a row window by division. Kept a touch taller than the glyph so a row
/// never clips.
const TRANSCRIPT_ROW_H: f32 = 18.0;

/// Row pitch (px) for the receipt-console flyout — same single-line log geometry.
const STATUS_ROW_H: f32 = 18.0;

/// The receipt console's ring bound — the newest `say()` lines kept, oldest out.
/// Was an implicit 64 (of which the flyout showed only the newest 24); now that
/// the console is virtualized and tail-following, it can hold a real session
/// history cheaply, so the bound is raised to a full log the operator can scroll
/// back through. Bounded still (a couple hundred KB of short strings at worst) —
/// the console is narration, not the receipt chain.
const STATUS_LOG_CAP: usize = 4096;

/// The transcript body's per-receipt line, exactly as painted: the commit index,
/// turn-hash + post-state-hash prefixes, and the acting cell. Pure over one receipt.
fn transcript_row_text(i: usize, r: &dregg_turn::turn::TurnReceipt) -> String {
    let hh: String = r.turn_hash[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let post: String = r.post_state_hash[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    format!(
        "#{i:<4} turn {hh} → post {post}  agent {}",
        id_short(&r.agent)
    )
}

/// One transcript row element — the pure renderer the virtual list maps over its
/// visible range. Fixed-height so it tiles cleanly under virtualization.
fn transcript_row(i: usize, r: &dregg_turn::turn::TurnReceipt) -> AnyElement {
    div()
        .h(px(TRANSCRIPT_ROW_H))
        .text_size(px(11.0))
        .child(transcript_row_text(i, r))
        .into_any_element()
}

/// One receipt-console row element — a single `say()` line, fixed-height for
/// virtualization. The text IS the line (the console is a raw narration log), so
/// the row is its own witness; no `*_text` twin is needed.
fn console_row(line: &str) -> AnyElement {
    div()
        .h(px(STATUS_ROW_H))
        .text_size(px(11.0))
        .child(line.to_string())
        .into_any_element()
}

/// Parse a document line back to the `CellId` it transcludes, if any. The compose
/// gesture writes `{transclude dregg://<64-hex> · <kind> · balance <b> · <life>}`
/// (see [`DeosDesktop::transclude_into`]); this reverses the `dregg://<hex>` head so
/// a transclusion becomes a STRUCTURED link the Links window can resolve to live
/// faces + invert into a backlink. Returns `None` for any non-transclusion line.
fn parse_transclusion_ref(line: &str) -> Option<CellId> {
    let after = line.split("dregg://").nth(1)?;
    // The hex id runs up to the first delimiter (space, middot, or closing brace).
    let hex: String = after
        .chars()
        .take_while(|c| c.is_ascii_hexdigit())
        .collect();
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(CellId::from_bytes(bytes))
}

/// **The pure reverse-scan core** of [`DeosDesktop::backlinks_of`] — given every
/// desktop document as a `(cell, prose)` pair, return the cells whose prose carries a
/// transclusion resolving to `here` (its BACKLINKS, in desktop order). A cell quoting
/// itself is not a backlink. Kept as a free, gpui-less function so the two-way-link
/// inversion — the truth the Links window, the halo's "← quoted by N" witness arc,
/// and [`DeosDesktop::bake_doc_links`] all read — is unit-testable headlessly (see
/// the `tests` module at the bottom of this file).
fn backlinks_in(here: CellId, docs: impl IntoIterator<Item = (CellId, String)>) -> Vec<CellId> {
    docs.into_iter()
        .filter(|(other, _)| *other != here)
        .filter(|(_, prose)| {
            prose
                .lines()
                .filter_map(parse_transclusion_ref)
                .any(|t| t == here)
        })
        .map(|(other, _)| other)
        .collect()
}

// ── A live, open inspector window over one cell ───────────────────────────────────

/// The faces an inspector window shows of a cell (read fresh off the live ledger
/// each render — a fired affordance updates them in place).
struct WindowState {
    /// The cell this window inspects (also the `HashMap` key; kept inline so a
    /// `WindowState` is self-describing when iterated).
    #[allow(dead_code)]
    cell: CellId,
    title: String,
    x: f32,
    y: f32,
    w: f32,
    h: f32,
    minimized: bool,
    z: u32,
    /// The TYPE of this window — inspector, document editor, links/backlinks, or
    /// the transcript/receipt-log. The same cell can be open in several kinds.
    kind: WinKind,
}

/// **The window-type vocabulary** — the NT/Pharo density beyond a lone inspector.
/// Each is a distinct surface over the same live cell.
#[derive(Clone)]
enum WinKind {
    /// The reflective inspector (identity + live state + affordances + properties).
    Inspector,
    /// **A real document editor.** Holds a live `dregg_doc::Doc` — typing diffs
    /// into a receipted patch (the chronicle advances) AND lands a verified turn on
    /// the cell. The document IS the cell (its prose lives in the cell's heap).
    DocEditor {
        doc: Doc,
        /// The text currently in the edit buffer (committed-on-edit / on the bake).
        buffer: String,
        /// **A forked co-author DRAFT branch** (BRANCH-AND-STITCH-PROTOCOL §1) — a
        /// clone of `doc`'s patch-history that a second author edits independently,
        /// confined until stitched. `None` until the user forks one.
        branch: Option<Doc>,
        /// **The STITCHED document** after a merge (`History::stitch` = the pushout) —
        /// it may carry first-class `dregg_doc` conflict states (an antichain of live
        /// alternatives) where both authors edited the same region. `None` until a
        /// stitch runs; rendered as the live ConflictView when it holds a conflict.
        merged: Option<Doc>,
    },
    /// A links / backlinks view — which cells this one reaches (its caps) and which
    /// reach it, plus the transclusions composed into it.
    Links,
    /// The transcript / receipt-log — the World's receipt chain, the chronicle the
    /// user's "do it"s have written.
    Transcript,
    /// **The workflow-composer surface** — intents/workflows/refinement as first-class
    /// objects. The window's editing state (steps + baseline) lives in the desktop's
    /// `workflows` map keyed by the subject cell, so this variant is a marker.
    WorkflowComposer,
    /// **The DOCUMENT EXPLORER** — the Pharo-moldable multi-face inspector of a
    /// document's patch substance (History scrubber · DocGraph · Blame). Its per-cell
    /// view state (selected tab + scrubber cursor) lives in `doc_explorers`, so this
    /// variant is a marker like `WorkflowComposer`.
    DocExplorer,
    /// **The WORLD EXPLORER** — the "My Computer" of the verified World (ledger ·
    /// chronicle · conservation). Per-window face selection lives in `world_explorers`,
    /// so this variant is a marker.
    WorldExplorer,
    /// **The AGENT ROOM** — the desktop face of an agent-as-inhabitant (mandate ·
    /// receipted actions · authorization boundary, off the live World). Per-window
    /// resident + face selection lives in `agent_rooms`, so this variant is a marker.
    AgentRoom,
    /// **THE CONTENT-IR PANE** — a window whose body is a real `deos_view::ViewNode`
    /// rendered through deos-view's NATIVE renderer (`AppletView`). The rendered
    /// renderer entity lives in `viewnode_panes`, so this variant is a marker.
    ViewNodePane,
    /// **A confined ANDROID-CELL dressed as the phone's SystemUI** — its body is the
    /// graphideOS cap-chrome (status bar + quick-settings shade + hand-over sheet) over a
    /// live [`crate::systemui_caps::SystemUiCapChrome`]. The chrome (its real `PermWorld` +
    /// executor) lives in `systemui_chromes`, so this variant is a marker.
    AndroidCell,
    /// **THE APP SHELF** — the roster of pre-built starbridge-apps, each launchable
    /// onto the LIVE World as a real verified turn. Its state (`AppShelfState`) lives
    /// in `app_shelf` (gated on `app-registry`), so this variant is a marker.
    AppShelf,
    /// **THE EXCHANGE FLOOR** — the $DREGG agent-economy window: offers as live
    /// cells, post → lease → settle as real verified turns, Σδ=0 settlement. Its
    /// state (`ExchangeFloorState`) lives in `exchange_floor` (gated on
    /// `app-registry`), so this variant is a marker.
    ExchangeFloor,
    /// **THE MATRIX ROOM** — membrane-over-Matrix in the shipped desktop: rooms as
    /// live cells, sends as receipted turns read back off the receipt chain, and
    /// the REAL executor envelope legs over the recorded/mock sync (the live
    /// homeserver a named env-gated seam). Per-window state lives in
    /// `matrix_rooms` / `matrix_stack` (gated on `dev-surfaces`), so this variant
    /// is a marker like `AgentRoom`. Anchored on its own sentinel cell.
    MatrixRoom,
    /// **THE PROVENANCE WALKER** — the receipt chain walked hash-by-hash, every
    /// link recomputed (never trusted). Its per-window state (the walk cursor +
    /// the go-to landing) lives in `provenance_walkers`, so this variant is a
    /// marker like `WorldExplorer`.
    ProvenanceWalker,
    /// **THE ATTACH WIZARD** — the warm "send your AI to live here" onboarding over
    /// the hireling rail. Its per-window walk state lives in `attach_wizards`, so
    /// this variant is a marker like `AgentRoom`.
    AttachWizard,
    /// **THE MAIL ROOM** — the desktop face of the [`crate::letter_office`]: mail
    /// between agents as cells on the live World (inbox · outbox · mail-ledger). A letter
    /// IS a cell carrying its markdown in the heap; sending drops it in an outbox cell,
    /// delivery is a receipted turn moving it to an inbox cell. Per-window state (the
    /// compose recipient + the shown face) lives in `mail_rooms`, so this variant is a
    /// marker like `AgentRoom`. Anchored on its own sentinel cell.
    MailRoom,
    /// **MY DREGG COMPUTERS** — the vats this account can reach (each a private
    /// verified World whose identity is a content-addressed cell on a DreggNet
    /// ServerFleet), the roster off the designed `GET /v1/vats` gateway seam,
    /// CONNECT attaching one over the proven HTTP+SSE wire path and reflecting
    /// its remote cells + receipt stream live. Per-window state lives in
    /// `dregg_computers` (the attachment itself in `vat_link` — it belongs to
    /// the desktop, not the window), so this variant is a marker like
    /// `AgentRoom`. Anchored on its own sentinel cell.
    DreggComputers,
}

impl WinKind {
    fn label(&self) -> &'static str {
        match self {
            WinKind::Inspector => "Inspector",
            WinKind::DocEditor { .. } => "Document",
            WinKind::Links => "Links",
            WinKind::Transcript => "Transcript",
            WinKind::WorkflowComposer => "Workflow",
            WinKind::DocExplorer => "Doc Explorer",
            WinKind::WorldExplorer => "World Explorer",
            WinKind::AgentRoom => "Agent Room",
            WinKind::ViewNodePane => "World Status",
            WinKind::AndroidCell => "Android · SystemUI",
            WinKind::AppShelf => "App Shelf",
            WinKind::ExchangeFloor => "Exchange Floor",
            WinKind::MatrixRoom => "Matrix Room",
            WinKind::ProvenanceWalker => "Provenance Walker",
            WinKind::AttachWizard => "Attach a Resident",
            WinKind::MailRoom => "Mail Room",
            WinKind::DreggComputers => "My Dregg Computers",
        }
    }
}

// ── The actuation surface: every action available on a cell ───────────────────────

/// One entry of a cell's right-click context menu — an action the user can "do it"
/// on. `held` reflects whether the user holds the cap for it (lit vs. dim).
struct MenuAction {
    label: String,
    held: bool,
    kind: ActionKind,
    /// A non-actionable divider row (groups the deep menu visually). Rendered as a
    /// thin rule; clicking does nothing.
    separator: bool,
}

impl MenuAction {
    /// An actionable menu row.
    fn new(label: impl Into<String>, held: bool, kind: ActionKind) -> MenuAction {
        MenuAction {
            label: label.into(),
            held,
            kind,
            separator: false,
        }
    }

    /// A divider row in a deep context menu.
    fn sep() -> MenuAction {
        MenuAction {
            label: String::new(),
            held: false,
            kind: ActionKind::Inspect,
            separator: true,
        }
    }
}

#[derive(Clone)]
enum ActionKind {
    /// Open the inspector window on the cell.
    Inspect,
    /// Open the cell as a DOCUMENT EDITOR (the document-as-cell surface).
    OpenDoc,
    /// Open the DOCUMENT EXPLORER — the Pharo-moldable inspector of the document's
    /// patch substance (History scrubber · DocGraph · Blame).
    OpenDocExplorer,
    /// Open the WORLD EXPLORER — the "My Computer" of the verified World (ledger ·
    /// chronicle · conservation). A World-level (desktop-background) surface.
    OpenWorldExplorer,
    /// Open the AGENT ROOM — the resident's provable activity (mandate · receipted
    /// actions · authorization boundary). A World-level (desktop-background) surface.
    OpenAgentRoom,
    /// Open the PROVENANCE WALKER — the receipt chain walked hash-by-hash, every
    /// link recomputed (never trusted). A World-level (desktop-background) surface.
    OpenProvenanceWalker,
    /// Open the MAIL ROOM — mail between agents as cells on the live World (inbox ·
    /// outbox · mail-ledger). A World-level (desktop-background) surface.
    OpenMailRoom,
    /// Open MY DREGG COMPUTERS — the vats you can reach (roster · connect ·
    /// reflect · receipts). A World-level (desktop-background) surface.
    OpenDreggComputers,
    /// Open a DOCUMENT-COLLABORATION session — the document editor with a forked
    /// co-author draft already in flight (branch · stitch · resolve), landed mold-ready.
    OpenDocCollab,
    /// Open the WORLD-STATUS BOARD — the agent-composable `deos_view::ViewNode` pane
    /// (the reflective surface a confined agent rewrites). A World-level surface.
    OpenViewNodePane,
    /// Open a confined ANDROID CELL dressed as the phone's SystemUI cap-chrome (status
    /// bar · quick-settings shade · hand-over sheet). A World-level surface.
    OpenAndroidCell,
    /// Open the APP SHELF — the pre-built starbridge-apps roster (launch one onto the
    /// LIVE World as a real verified turn). A World-level surface. Gated on
    /// `app-registry` (the feature that wires the registry + app crates in).
    #[cfg(feature = "app-registry")]
    OpenAppShelf,
    /// Open the EXCHANGE FLOOR — the $DREGG agent-economy window (offers as live
    /// cells; post → lease → settle as real verified turns; Σδ=0 settlement). A
    /// World-level surface. Gated on `app-registry` (the compute-exchange /
    /// execution-lease substrate crates ride that feature).
    #[cfg(feature = "app-registry")]
    OpenExchangeFloor,
    /// Open the MATRIX ROOM — membrane-over-Matrix in the shipped desktop (rooms
    /// as live cells; sends as receipted turns; the real envelope legs over the
    /// recorded sync; the live homeserver a named env-gated seam). A World-level
    /// surface. Gated on `dev-surfaces` (where the `deos-matrix` wire types live).
    #[cfg(feature = "dev-surfaces")]
    OpenMatrixRoom,
    /// Open the ATTACH WIZARD — the warm "send your AI to live here" onboarding: name
    /// a resident, pick its brain, set its mandate by hand, and HIRE it into the Agent
    /// Room already stepping. A World-level surface. Gated on `dev-surfaces` (the
    /// hireling rail it drives).
    #[cfg(feature = "dev-surfaces")]
    OpenAttachWizard,
    /// Open the SPOTTER command palette — fuzzy-jump to any cell / action / window.
    OpenSpotter,
    /// Open the links / backlinks view over the cell.
    OpenLinks,
    /// Open the transcript / receipt-log window (the World chronicle).
    OpenTranscript,
    /// Open the WORKFLOW-COMPOSER window over the cell — compose intents into a
    /// workflow and check flow-refinement (the real `dregg_deploy::refine` game).
    OpenWorkflow,
    /// Open the PROPERTY inspector/editor for the cell (the NT property-dialog +
    /// Pharo inspect-everything surface — view and edit the cell's properties).
    Properties,
    /// Open the WINDOW property sheet (the window's persisted layout properties) for
    /// the given window kind on the acted-on cell.
    WindowProperties { tag: WinKindTag },
    /// Fire a real verified turn: transfer `amount` from this cell to the
    /// desktop's "user" anchor (a self-contained demo of actuation).
    Transfer { amount: u64 },
    /// Grant a capability reaching `target` to this cell at the next free slot
    /// (the ocap "grant" verb) — a real `GrantCapability` turn.
    Grant { target: CellId },
    /// Bump the cell's nonce via a real `IncrementNonce` turn (the simplest
    /// always-available affordance — proves the actuation path lands a receipt).
    BumpNonce,
    /// **Set a state field via a receipted `SetField` turn** — the property-editor's
    /// write verb (editing a cell property IS a verified turn). Writes `value` into
    /// slot `index` of the cell's state.
    SetField { index: usize, value: u64 },
    /// **COMPOSE: transclude this cell into the named target document** — embed a
    /// provenanced reference to this cell's content into `into`'s document (a
    /// receipted patch + a verified turn). The genuine cross-cell compose gesture.
    TranscludeInto { into: CellId },
    /// Seal / unseal the cell (a lifecycle turn) — a window-control-ish actuation
    /// surfaced in the deep menu.
    ToggleSeal,
    /// **Cascade every open window** — re-stagger all open windows from the top-left
    /// (the NT "Cascade Windows" command). A pure layout/view actuation: it moves
    /// windows and re-persists their geometry, firing NO verified turn.
    CascadeWindows,
    /// **Tile every open window** in a grid filling the desktop (the NT "Tile" command).
    /// Pure layout actuation.
    TileWindows,
    /// **Close every open window** (the NT "Close All"). Pure layout actuation.
    CloseAllWindows,
    /// **Show / hide the GOSSAMER transclusion threads** — the cyan elbow connectors
    /// drawn between a quoting document window and each quoted surface
    /// ([`threads`]). A persisted preference flip (pure view actuation): it repaints
    /// the glass and re-saves the layout, firing NO verified turn.
    ToggleThreads,
}

// ── A floating context menu (rendered as an NT popup overlay) ─────────────────────

struct OpenMenu {
    /// The object the menu acts on. `None` = the desktop-background menu (no cell).
    cell: Option<CellId>,
    /// The menu's heading (the named object: a cell kind + id, a window title, or
    /// "Desktop").
    heading: String,
    at: Point<Pixels>,
    actions: Vec<MenuAction>,
}

/// **The property inspector/editor** — a modal NT property-dialog open over one
/// object (a cell or a window). It lists the object's properties and lets the user
/// EDIT them: a cell-property edit fires a receipted `SetField` turn; a window /
/// desktop property edit is a persisted layout change. The Pharo "inspect anything"
/// fused with the NT "Properties…" dialog.
struct PropertyDialog {
    subject: PropSubject,
    at: Point<Pixels>,
    w: f32,
    h: f32,
}

#[derive(Clone)]
enum PropSubject {
    /// A cell's properties (view + receipted edits via SetField turns).
    Cell(CellId),
    /// A window's layout properties (view + persisted layout edits) — keyed by the
    /// cell + window kind so it targets the right open window.
    Window(CellId, WinKindTag),
    /// The desktop's customization preferences.
    Desktop,
}

// ── A live drag in flight (an icon being moved, or a window being moved/resized) ───

enum Drag {
    Icon {
        cell: CellId,
        // The grab offset from the icon's top-left to the mouse.
        grab: Point<Pixels>,
    },
    WinMove {
        key: WinKey,
        grab: Point<Pixels>,
    },
    WinResize {
        key: WinKey,
        // The window's top-left at grab; we resize the bottom-right corner.
        origin: Point<Pixels>,
    },
    /// The Rewind Rail's height scrubber is in hand — each mouse-move maps
    /// x → a history step and re-plants the rewind cursor (the root-verified
    /// projection rebuilds memoized on the next render pass; see `rewind`).
    Rewind,
}

/// A window-instance key — a cell plus the window TYPE, so one cell can be open as
/// an inspector AND a document editor AND a links view at once.
type WinKey = (CellId, WinKindTag);

/// **THE deos DESKTOP** — the root `Render` view. Owns the live `World`, the icon
/// layout, the open inspector windows, the in-flight drag, the open context menu,
/// and the persisted [`DesktopLayout`]. Every spatial gesture mutates the layout and
/// re-saves it; every actuation commits a real verified turn on the World.
pub struct DeosDesktop {
    world: Rc<RefCell<World>>,
    /// The cells to show as icons (the live ledger's cells, ordered stably by id).
    cells: Vec<CellId>,
    /// The "user" anchor — the default transfer/grant counterparty for the demo
    /// actuation verbs (so a context-menu action is fully self-contained).
    user: CellId,
    layout: DesktopLayout,
    layout_path: PathBuf,
    windows: HashMap<WinKey, WindowState>,
    open_menu: Option<OpenMenu>,
    /// The open property dialog, if any (the NT Properties… surface).
    open_prop: Option<PropertyDialog>,
    drag: Option<Drag>,
    next_z: u32,
    /// The author identity stamped on document patches (the operator). A document
    /// edit's `dregg_doc::Patch` carries this; blame/provenance flow from it.
    author: Author,
    /// A short log of the last actuations (receipt height / outcome) shown in the
    /// status bar — the user sees their "do it" landed a real verified turn.
    status: String,
    /// **The per-cell workflow-composer state** — the intents/workflow being composed
    /// over each subject cell, plus the pinned refinement baseline. Read by the
    /// workflow window body; the REAL `dregg_deploy::refine` flow + decision run over
    /// it. Keyed by the subject cell so each cell has its own workflow.
    workflows: HashMap<CellId, workflow::WorkflowState>,
    /// **The real free-typing document editors** — one live `gpui-component`
    /// `InputState` (a rope-backed, multi-line text widget) per open document cell.
    /// Keystrokes flow through its `Change` event into [`Self::edit_doc`], which
    /// commits the document into the cell's committed umem-heap
    /// ([`Self::commit_doc_to_umem_heap`] → resealed `heap_root`) as a receipted
    /// patch. Created lazily on first render of the doc
    /// body (where `window`/`cx` are in hand). The `Change` subscription's lifetime
    /// is kept in `doc_subs`.
    doc_inputs: HashMap<CellId, Entity<InputState>>,
    /// The per-document `Change`-event subscription handles (kept alive so the
    /// keystroke→heap commit fires for the editor's whole lifetime).
    doc_subs: HashMap<CellId, Subscription>,
    /// **The live co-author DRAFT editors** — one `InputState` per open document that
    /// currently carries a forked branch. Typing here is a *second author*'s divergent
    /// edit on the CONFINED draft (no heap commit until stitched), so a real user can
    /// drive the divergence by hand (not only the canned "diverges" button). Created
    /// lazily when a branch exists and rendered below the main editor; dropped when the
    /// branch retires (stitched/resolved/closed). Keyed by the document cell.
    branch_inputs: HashMap<CellId, Entity<InputState>>,
    /// `Change`-event subscriptions for the live branch editors (kept alive for the
    /// draft's lifetime; the handler folds the typed text into the confined branch doc).
    branch_subs: HashMap<CellId, Subscription>,
    /// **The most recent resolution receipt** — `(document cell, choice label, the
    /// committed resolution patch id)`. A resolution is itself a receipted patch (the
    /// turn's receipt id); the conflict surface surfaces this so the user SEES the
    /// settlement landed as a real, content-addressed turn. `None` until one resolves.
    last_resolution: Option<(CellId, String, PatchId)>,
    /// Cells whose document text was changed OUTSIDE the editor widget (a transclude
    /// drop / a bake edit) and so the live `InputState` must be re-seeded from the
    /// cached buffer on the next render (those paths lack `&mut Window`, which
    /// `InputState::set_value` needs). Drained in `render_doc_body`.
    doc_resync: std::collections::HashSet<CellId>,
    /// **The per-cell DOCUMENT-EXPLORER view state** — which face (tab) is selected and
    /// where the History time-travel scrubber's cursor sits. Keyed by the subject cell;
    /// the `DocExplorer` window reads it. A pure view concern (no committed state).
    doc_explorers: HashMap<CellId, DocExplorerState>,
    /// **The per-window WORLD-EXPLORER view state** — which face (ledger/chronicle/
    /// conservation) is selected. Keyed by the anchor cell of the World Explorer window.
    world_explorers: HashMap<CellId, world_explorer::WorldExplorerState>,
    /// **The SPOTTER overlay** — the Pharo command palette (fuzzy-jump to any cell /
    /// action / window). `None` when closed; holds the live query + selection when open.
    spotter: Option<SpotterUi>,
    /// **The current halo selection** — the icon or window wearing the Pharo
    /// direct-manipulation ring (`None` when nothing is molded). Set by a left-click on
    /// an icon/window, cleared by a click on the bare desktop. Read only by the `halo`
    /// submodule's render + actuation.
    selected: Option<HaloTarget>,
    /// **The WELCOME moment** — `true` while the warm front-door card is showing. Set
    /// from `prefs.welcomed` on open (a fresh/never-greeted image shows it once), and
    /// cleared the moment the newcomer dismisses it or steps through a door (which also
    /// persists `welcomed = true`, so the calm greeting appears exactly once). The
    /// `welcome` submodule owns the gpui-free model + greeting; this View renders it.
    show_welcome: bool,
    /// **The content-IR panes** — one [`deos_view::AppletView`] (deos-view's NATIVE
    /// renderer over a portable `deos_view::ViewNode`) per open `ViewNodePane` window,
    /// created lazily on first render. The desktop hosts the entity as the window body,
    /// so the shell paints portable IR beside its native-chrome surfaces. Keyed by the
    /// window's anchor cell. Gated on `card-pane` (where `deos-view` is in scope).
    #[cfg(feature = "card-pane")]
    viewnode_panes: HashMap<CellId, Entity<deos_view::AppletView>>,
    /// **The open live CARDS on the pulse** — every mounted
    /// [`crate::card_pane::CardPane`] (an attached-World card whose binds read REAL
    /// cells of the live `World`), keyed by its substance cell. [`Self::pump_dynamics`]
    /// broadcasts each beat's world events into every card's signal registry
    /// ([`card_pulse::pulse_cards`] / [`card_pulse::pulse_cards_quiet`]) so a foreign
    /// turn repaints exactly the dirty binds — the card half of the Pulse→Signals
    /// weld (the viewnode half is `viewnode_panes`). Gated on `card-pane`.
    #[cfg(feature = "card-pane")]
    card_panes: HashMap<CellId, Entity<crate::card_pane::CardPane>>,
    /// **The per-window AGENT-ROOM view state** — which resident is watched and which
    /// face (actions/mandate/reach) is shown. Keyed by the room window's anchor cell
    /// (the room's own sentinel). A pure view concern (no committed state).
    agent_rooms: HashMap<CellId, agent_room::AgentRoomState>,
    /// **The per-window PROVENANCE-WALKER view state** — the walk cursor (which
    /// receipt is selected, keyed by recomputed hash) plus the last root-verified
    /// go-to-that-point landing. Keyed by the walker window's own sentinel cell
    /// ([`provenance_walker::walker_window_cell`]). A pure view concern — the
    /// chain itself is re-derived from the live World on every paint.
    provenance_walkers: HashMap<CellId, provenance_walker::WalkerState>,
    /// **The per-window MAIL-ROOM view state** — the compose recipient + which face
    /// (inbox/outbox/mail-ledger) is shown. Keyed by the room window's own sentinel cell
    /// ([`mail_room::mail_room_window_cell`]). A pure view concern — the mail itself is
    /// re-scanned off the live World ([`crate::letter_office`]) on every paint.
    mail_rooms: HashMap<CellId, mail_room::MailRoomState>,
    /// **The per-window MY-DREGG-COMPUTERS view state** — which face (computers/
    /// connection/receipts) is shown. Keyed by the surface's own sentinel cell
    /// ([`dregg_computers::dregg_computers_window_cell`]). A pure view concern.
    dregg_computers: HashMap<CellId, dregg_computers::DreggComputersState>,
    /// **The vat ROSTER** — the Dregg Computers this account can reach, honestly
    /// sourced (the `GET /v1/vats` fixture, or the live gateway when
    /// `DREGG_GATEWAY_URL` names one). Built once at construction; the surface
    /// reads it every paint.
    vat_directory: dregg_computers::VatDirectory,
    /// **The vat ATTACHMENT** — the one Dregg Computer this desktop is connected
    /// to (`None` until CONNECT): the wire client + the reflected snapshot + the
    /// receipt feed the pulse drains. Deliberately NOT per-window: the link is to
    /// a remote computer, not a window, so closing the window keeps you attached
    /// (your computer stays yours with the lid shut).
    vat_link: Option<dregg_computers::VatLink>,
    /// The Mail Room composer's live input widget (single-line; Enter sends the draft as a
    /// REAL letter turn — the SAME send the bake hook drives), built lazily on first render
    /// like the Spotter's.
    mail_input: Option<Entity<InputState>>,
    /// The Mail Room composer's `Change`/`PressEnter` subscription (kept alive while open).
    mail_input_sub: Option<Subscription>,
    /// The Mail Room composer's current draft (mirrored from the widget on each `Change`).
    mail_draft: String,
    /// **THE HIRELING** — the Agent Room's hired resident: the confined deos-hermes
    /// brain+gate [`crate::resident_agent::AgentHandle`] plus the step planner
    /// (see [`hireling`]). Unstaffed by default; every STEP beat mirrors real
    /// verified turns onto the live World and surfaces gate refusals in-band.
    /// Gated on `dev-surfaces` (where the deos-hermes rail is in scope).
    #[cfg(feature = "dev-surfaces")]
    hireling: hireling::HirelingState,
    /// **The per-window ATTACH-WIZARD state** — the five-breath onboarding walk (its
    /// step position + the operator's name/brain/mandate choices) that hires a real
    /// confined resident into the Agent Room (see [`attach_wizard`]). Keyed by the
    /// wizard's own sentinel cell ([`attach_wizard::wizard_window_cell`]); a pure
    /// view concern until HIRE, which routes through the shared hireling path. Gated
    /// on `dev-surfaces` (where the hireling rail is in scope).
    #[cfg(feature = "dev-surfaces")]
    attach_wizards: HashMap<CellId, attach_wizard::WizardState>,
    /// **The per-window MATRIX ROOM view state** — which room is watched and which
    /// face (timeline/envelopes/wire) is shown. Keyed by the window's own sentinel.
    /// A pure view concern. Gated on `dev-surfaces` (where the wire types live).
    #[cfg(feature = "dev-surfaces")]
    matrix_rooms: HashMap<CellId, matrix_room::MatrixRoomState>,
    /// **THE MATRIX ROOM's substance** — the live room cells + the Matrix-hand on
    /// the desktop's OWN World, the recorded-sync wire, and the envelope verdicts
    /// (see [`matrix_room::MatrixRoomStack`]). Installed lazily on first open (a
    /// real genesis-path install; the icon census refreshes at once). Gated on
    /// `dev-surfaces`.
    #[cfg(feature = "dev-surfaces")]
    matrix_stack: Option<matrix_room::MatrixRoomStack>,
    /// The Matrix composer's live input widget (single-line; Enter commits the
    /// draft as a REAL receipted turn), built lazily on first render like the
    /// Spotter's. Gated on `dev-surfaces`.
    #[cfg(feature = "dev-surfaces")]
    matrix_input: Option<Entity<InputState>>,
    /// The composer's `Change`/`PressEnter` subscription (kept alive while open).
    #[cfg(feature = "dev-surfaces")]
    matrix_input_sub: Option<Subscription>,
    /// The composer's current draft (mirrored from the widget on each `Change`).
    #[cfg(feature = "dev-surfaces")]
    matrix_draft: String,
    /// **THE PULSE CURSOR** — how far into the World's [`crate::dynamics`] stream the
    /// desktop has consumed. A background pump polls the stream (the documented pull
    /// model: `since(cursor)` per beat) and, when the World moved WITHOUT the desktop's
    /// own hand — a bot reactor, an attached agent, a live node — refreshes the icon
    /// census and repaints, so every open surface shows the ledger's truth without a
    /// refresh button. Turns by residents other than the operator are announced on the
    /// status bar (the room's heartbeat).
    pulse_cursor: usize,
    /// **The discord-bot's activity feed** the bot-surface card paints — the desktop
    /// mirror of the bot's `GET /api/apps/activity/recent` (folded into the SAME
    /// `ViewNode` card shape the bot renders as a Discord embed). Empty without a live
    /// bot (the HTTP leg is the named seam); a desktop-driven op would append here.
    /// Gated on `card-pane` (where the card render is in scope).
    #[cfg(feature = "card-pane")]
    bot_activity: Vec<bot_surface::BotActivity>,
    /// **The live SystemUI cap-chromes** — one [`crate::systemui_caps::SystemUiCapChrome`]
    /// (a confined android-cell's real `PermWorld` + the verified executor) per open
    /// `AndroidCell` window, minted lazily on first paint. The window body renders its
    /// status bar / quick-settings shade / hand-over sheet; a hand-over commits a real
    /// `Effect::GrantCapability` on this confined ledger. Keyed by the window's anchor
    /// cell. Gated on `android-systemui` (where the cap-chrome model is in scope).
    #[cfg(feature = "android-systemui")]
    systemui_chromes: HashMap<CellId, crate::systemui_caps::SystemUiCapChrome>,
    /// Which `AndroidCell` windows have their quick-settings shade pulled down (a pure
    /// view concern). Keyed by the window's anchor cell.
    #[cfg(feature = "android-systemui")]
    systemui_shades: std::collections::HashSet<CellId>,
    /// **THE APP SHELF state** — the registry of pre-built starbridge-apps plus the
    /// installed set (each a launched-on-World app whose cell + receipts live on the
    /// desktop's OWN `World` ledger). Read by the shelf window body, the app-faced
    /// desktop icons, and the Spotter's launch dispatch; mutated only by the launch
    /// flow ([`app_shelf::AppShelfState::install_on_world`] — a real verified turn).
    /// Gated on `app-registry` (which implies `embedded-executor`).
    #[cfg(feature = "app-registry")]
    app_shelf: app_shelf::AppShelfState,
    /// **THE EXCHANGE FLOOR state** — the $DREGG agent-economy order book: every
    /// floor-posted compute OFFER is a REAL cell on the desktop's own `World`
    /// carrying the compute-exchange job program; post / take / settle are real
    /// verified turns committed through its spines. Read by the Exchange window
    /// body and the offer icon faces; the App Shelf's compute-exchange +
    /// execution-lease installs are its substrate. Gated on `app-registry`.
    #[cfg(feature = "app-registry")]
    exchange_floor: exchange_floor::ExchangeFloorState,
    /// The last rendered viewport size (logical px), captured each `render`. Tile /
    /// cascade read it so they fill the ACTUAL desktop instead of a hardcoded
    /// 1600×1000 — at higher bake resolutions the windows spread the whole room.
    last_viewport: (f32, f32),
    /// **THE KEYBOARD SPINE's focus root** — the desktop root tracks this handle so
    /// one `on_key` dispatcher hears every keystroke that no focused child consumed:
    /// ⌘K/Ctrl-K summons (or dismisses) the Spotter from anywhere; while the Spotter
    /// is open, ↑/↓ move the selection and Escape closes it; otherwise Escape climbs
    /// the dismissal ladder (context menu → property dialog → halo selection).
    focus: FocusHandle,
    /// **THE RECEIPT CONSOLE's narration log** — every status-bar line the desktop
    /// ever said (`say()`), newest last, capped at 64. The status bar shows only the
    /// latest; clicking the bar's left region opens the console flyout over this log,
    /// so narration history stops evaporating. Session view-state, never persisted.
    status_log: std::collections::VecDeque<String>,
    /// Whether the receipt-console flyout is open (anchored above the status bar).
    status_flyout: bool,
    /// Narration lines said while the flyout was CLOSED since it was last opened —
    /// the "⋯ n new" unread chip on the status bar. Opening the flyout clears it.
    status_unread: usize,
    /// **The PULSE-TOAST rack** — announcement cards for the World's foreign motion
    /// (green committed / amber REFUSED), fed and aged by [`Self::pump_dynamics`],
    /// mounted bottom-right by the render tail; click-through opens the Transcript.
    toast_rack: toasts::ToastRack,
    /// **The coalescing background layout writer** — the HOT interaction paths
    /// (window drag/resize via `persist_window`, icon drag-end, the per-keystroke
    /// document sidecar mirrors) queue snapshots here instead of serializing every
    /// document's prose synchronously on the UI thread per gesture. Cold paths
    /// (prefs, welcome, close, bake hooks) still write synchronously for
    /// exit-safety. See [`layout::LayoutSaver`].
    saver: layout::LayoutSaver,
    /// **THE REWIND RAIL's cursor + memoized projection** — LIVE (`None`) by
    /// default; while scrubbed, every `cell_*` reader and the World Explorer
    /// faces read the root-verified REPLAYED ledger at the cursor instead of
    /// the live World (see [`rewind::RewindState`] — the model is gpui-free and
    /// unit-tested; a rewind is a session gesture, never persisted layout).
    rewind: rewind::RewindState,
    /// **THE FACE-SCROLL REGISTRY** — one persistent [`ScrollHandle`] per dense
    /// scrolling face ([`face_scroll::FaceScrollKey`]: window bodies by cell ×
    /// kind × tab ordinal; the Spotter/console/property overlays by name). Every
    /// face renders through [`chrome::nt_scroll_face`] with its registry handle,
    /// so it wears a REAL always-visible NT scrollbar and its scroll POSITION is
    /// desktop view-state — surviving repaints, tab flips, and window reopens
    /// (session-only, like the halo; never persisted layout).
    face_scrolls: face_scroll::FaceScrollRegistry,
    /// **THE VIRTUAL-FACE REGISTRY** — one persistent [`VirtualListScrollHandle`]
    /// (plus a tail cursor) per UNCAPPED log face ([`virtual_face`]): the World
    /// Explorer's Chronicle + Ledger, the Transcript body, and the receipt
    /// console. These faces render through `gpui_component::v_virtual_list`, so
    /// only the visible rows are ever built and the row count is unbounded — the
    /// chronicle stops being a 24-row peephole. Append-order faces (chronicle,
    /// transcript, console) `follow_tail` so a landing receipt snaps into view
    /// (`tail -f` for the World); the id-sorted Ledger keeps its place. The base
    /// handle feeds the same NT scrollbar the flat faces wear.
    virtual_faces: virtual_face::VirtualFaceRegistry,
}

/// The live state of the open Spotter command palette overlay.
struct SpotterUi {
    /// The current query text — mirrored from the live `InputState` widget on each
    /// `Change`, so ranking + render read it without touching the entity.
    query: String,
    /// The highlighted candidate index (click dispatches it; Enter dispatches the top).
    selected: usize,
    /// The live query field — a real `gpui-component` `Input` (rope-backed). Built
    /// lazily on first render of the overlay; the subscription keeps `query` in sync.
    input: Option<Entity<InputState>>,
    /// The query field's `Change`/`PressEnter` subscription (kept alive while open).
    _sub: Option<Subscription>,
}

/// The view state of a [`WinKind::DocExplorer`] window: which moldable face is shown
/// and the History scrubber's cursor (a revision index, `None` = the tip).
#[derive(Clone, Default)]
struct DocExplorerState {
    tab: DocExplorerTab,
    /// The scrubbed revision index (0-based into the patch history); `None` = tip.
    scrub: Option<usize>,
}

/// The moldable faces of the Document Explorer (the Pharo "many views of one object").
#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum DocExplorerTab {
    /// The patch-history time-travel scrubber (replay the doc at each revision).
    #[default]
    History,
    /// The per-patch diff — what each patch's ops added/deleted/connected/set.
    Patches,
    /// The DocGraph as a visual node-chain — boxes + ↓ order + ⑂ conflict forks.
    Graph,
    /// Per-line authorship blame + contributions-by-author.
    Blame,
}

impl DocExplorerTab {
    fn label(self) -> &'static str {
        match self {
            DocExplorerTab::History => "History (time-travel)",
            DocExplorerTab::Patches => "Patches (diff)",
            DocExplorerTab::Graph => "DocGraph (nodes)",
            DocExplorerTab::Blame => "Blame (authorship)",
        }
    }
    const ALL: [DocExplorerTab; 4] = [
        DocExplorerTab::History,
        DocExplorerTab::Patches,
        DocExplorerTab::Graph,
        DocExplorerTab::Blame,
    ];
}

impl DeosDesktop {
    /// Open the desktop over a live `World`, restoring the persisted layout. `user`
    /// is the default counterparty for the demo transfer/grant verbs.
    pub fn new(
        world: Rc<RefCell<World>>,
        user: CellId,
        layout_path: PathBuf,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        // The kit's scrollbars wear NT from the first paint: always-visible bars,
        // button-face thumb on a darker track (every mount — live window and
        // headless bakes — passes through here, so one call dresses them all).
        chrome::apply_nt_scrollbar_dress(cx);
        let (cells, pulse_cursor) = {
            let w = world.borrow();
            let mut v: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
            v.sort();
            // The pulse starts at the CURRENT cursor — genesis is already on the
            // glass; the pump only chases what moves from here on.
            (v, w.dynamics().cursor())
        };
        let layout = DesktopLayout::load(&layout_path);
        // A never-greeted image opens onto the warm WELCOME card (the calm default);
        // a returning one opens straight onto its arranged room.
        let show_welcome = !layout.prefs.welcomed;

        // The saver takes its own copy of the path (the struct literal moves the
        // local `layout_path` into the field above this init line evaluates).
        let saver_path = layout_path.clone();
        let mut desk = DeosDesktop {
            world,
            cells,
            user,
            layout,
            layout_path,
            windows: HashMap::new(),
            open_menu: None,
            open_prop: None,
            drag: None,
            next_z: 1,
            // A stable operator author derived from the user anchor — every document
            // patch is blamed on it.
            author: Author(u64::from_le_bytes(
                user.as_bytes()[..8].try_into().unwrap_or([0u8; 8]),
            )),
            status: "deos desktop — right-click ANYTHING for its menu · double-click to inspect · \
                     drag to arrange (persisted) · Open as Document to author"
                .to_string(),
            workflows: HashMap::new(),
            doc_inputs: HashMap::new(),
            doc_subs: HashMap::new(),
            branch_inputs: HashMap::new(),
            branch_subs: HashMap::new(),
            last_resolution: None,
            doc_resync: std::collections::HashSet::new(),
            doc_explorers: HashMap::new(),
            world_explorers: HashMap::new(),
            agent_rooms: HashMap::new(),
            provenance_walkers: HashMap::new(),
            mail_rooms: HashMap::new(),
            dregg_computers: HashMap::new(),
            vat_directory: dregg_computers::VatDirectory::discover(),
            vat_link: None,
            mail_input: None,
            mail_input_sub: None,
            mail_draft: String::new(),
            #[cfg(feature = "dev-surfaces")]
            hireling: hireling::HirelingState::default(),
            #[cfg(feature = "dev-surfaces")]
            attach_wizards: HashMap::new(),
            #[cfg(feature = "dev-surfaces")]
            matrix_rooms: HashMap::new(),
            #[cfg(feature = "dev-surfaces")]
            matrix_stack: None,
            #[cfg(feature = "dev-surfaces")]
            matrix_input: None,
            #[cfg(feature = "dev-surfaces")]
            matrix_input_sub: None,
            #[cfg(feature = "dev-surfaces")]
            matrix_draft: String::new(),
            pulse_cursor,
            spotter: None,
            selected: None,
            show_welcome,
            #[cfg(feature = "card-pane")]
            viewnode_panes: HashMap::new(),
            #[cfg(feature = "card-pane")]
            card_panes: HashMap::new(),
            #[cfg(feature = "card-pane")]
            bot_activity: Vec::new(),
            #[cfg(feature = "android-systemui")]
            systemui_chromes: HashMap::new(),
            #[cfg(feature = "android-systemui")]
            systemui_shades: std::collections::HashSet::new(),
            #[cfg(feature = "app-registry")]
            app_shelf: app_shelf::AppShelfState::new(),
            #[cfg(feature = "app-registry")]
            exchange_floor: exchange_floor::ExchangeFloorState::new(),
            last_viewport: (1600.0, 1000.0),
            focus: cx.focus_handle(),
            status_log: std::collections::VecDeque::new(),
            status_flyout: false,
            status_unread: 0,
            toast_rack: toasts::ToastRack::default(),
            saver: layout::LayoutSaver::spawn(saver_path),
            rewind: rewind::RewindState::default(),
            face_scrolls: face_scroll::FaceScrollRegistry::default(),
            virtual_faces: virtual_face::VirtualFaceRegistry::default(),
        };
        // Re-open any windows the persisted layout remembers (spatial persistence
        // for windows, not just icons — and now for window TYPE too).
        let geoms: Vec<WinGeom> = desk.layout.windows.clone();
        for g in geoms {
            if let Some(cell) = desk.cells.iter().find(|c| id_hex(c) == g.cell).copied() {
                desk.open_window_at(cell, g.kind, g.x, g.y, g.w, g.h, g.minimized);
            }
        }

        // THE PULSE — a background beat that consumes the World's dynamics stream
        // (the documented pull model) so the desktop repaints when the World moves
        // WITHOUT the desktop's own hand: a bot reactor, an attached agent, a live
        // node. Self-stopping when the view drops (the weak update fails).
        cx.spawn(async move |this, cx| loop {
            cx.background_executor()
                .timer(std::time::Duration::from_millis(250))
                .await;
            if this
                .update(cx, |desk: &mut DeosDesktop, cx| desk.pump_dynamics(cx))
                .is_err()
            {
                break;
            }
        })
        .detach();

        desk
    }

    /// **Narrate** — set the status bar's line AND append it to the receipt
    /// console's log (a [`STATUS_LOG_CAP`] ring, oldest out). Every status write in
    /// the desktop goes through here, so the console is the complete session
    /// narration — the story the bar used to overwrite one line at a time. The
    /// virtualized, tail-following flyout renders the whole ring, not a peephole.
    /// While the flyout is closed, said lines tick the unread chip.
    pub(super) fn say(&mut self, line: impl Into<String>) {
        let line = line.into();
        self.status = line.clone();
        self.status_log.push_back(line);
        if self.status_log.len() > STATUS_LOG_CAP {
            self.status_log.pop_front();
        }
        if !self.status_flyout {
            self.status_unread += 1;
        }
    }

    /// One beat of THE PULSE — consume the dynamics stream past [`Self::pulse_cursor`].
    /// If the World moved, refresh the icon census (cells born outside the desktop
    /// appear without a reopen) and repaint every open surface off the live ledger.
    /// Foreign residents' committed turns land as green toasts + the status line;
    /// REFUSALS land as amber toasts (the ocap guarantee firing deserves a card).
    /// The rack also ages one beat here — toasts retire themselves.
    fn pump_dynamics(&mut self, cx: &mut Context<Self>) {
        use crate::dynamics::WorldEvent;
        let aged = self.toast_rack.beat();
        // THE VAT TAP — drain the attached Dregg Computer's SSE receipt stream
        // (if any) into its feed each beat, so the Receipts face advances LIVE
        // while you watch (the remote half of the pulse; zero when unattached
        // or snapshot-only).
        let vat_new = self.pump_vat_stream();
        // THE PULSE→SIGNALS WELD, quiet half — every beat, even when the World did not
        // move: retire last beat's dirty-glow tint on every open content-IR pane AND
        // every open attached-World card, and catch up turns a surface's OWN backing
        // committed between beats (a button fired on the surface itself). See
        // `viewnode_pane::pulse_panes_quiet` + `card_pulse::pulse_cards_quiet`.
        #[cfg(feature = "card-pane")]
        let weld_quiet = viewnode_pane::pulse_panes_quiet(&self.viewnode_panes, cx)
            | card_pulse::pulse_cards_quiet(&self.card_panes, cx);
        #[cfg(not(feature = "card-pane"))]
        let weld_quiet = false;
        let (cursor, announce, arrivals, cells, field_sets, cell_events, receipts) = {
            let w = self.world.borrow();
            let d = w.dynamics();
            let cursor = d.cursor();
            // The dynamics log is a BOUNDED ring (CORE-AUDIT #11): once it exceeds
            // its retained cap it evicts the oldest events, advancing `base`. If our
            // pulse cursor fell BEHIND that floor between beats, `since` can only
            // hand us the retained tail — the evicted span's FieldSet/CellMutated
            // teeth are gone. Capture the floor now so the loud half can recover
            // conservatively rather than silently under-invalidate.
            let base = d.base();
            if cursor == self.pulse_cursor {
                drop(w);
                if aged || weld_quiet || vat_new > 0 {
                    cx.notify();
                }
                return;
            }
            let mut announce = None;
            let mut arrivals: Vec<(toasts::ToastKind, String)> = Vec::new();
            // The beat's `(cell, slot)` writes — projected into the exact shape the
            // signal registry invalidates on (`deos_js::signals::SourceEvent`), so the
            // weld's loud half can broadcast them to every open content-IR pane + card.
            let mut field_sets: Vec<(CellId, usize)> = Vec::new();
            // The beat's CELL-WIDE mutations (a cell named, no slot): `CellMutated`
            // (nonce bump / sovereign flip / permissions write / cap reshape) and
            // `CapabilityRevoked` — folded through the registries' conservative
            // `invalidate_cell` tooth (wave 3 left them unprojected).
            let mut cell_events: Vec<CellId> = Vec::new();
            for e in d.since(self.pulse_cursor) {
                match e {
                    WorldEvent::TurnCommitted {
                        agent,
                        height,
                        computrons,
                        ..
                    } if *agent != self.user => {
                        let line = format!(
                            "resident {} committed turn #{height} · {computrons}cu",
                            id_short(agent)
                        );
                        announce = Some(format!("⋯ {line}"));
                        arrivals.push((toasts::ToastKind::Committed, line));
                    }
                    WorldEvent::TurnRejected { agent, reason } => {
                        arrivals.push((
                            toasts::ToastKind::Refused,
                            format!("{} — {reason}", id_short(agent)),
                        ));
                    }
                    WorldEvent::FieldSet { cell, index } => field_sets.push((*cell, *index)),
                    WorldEvent::CapabilityRevoked { cell, .. } => cell_events.push(*cell),
                    WorldEvent::CellMutated { cell } => cell_events.push(*cell),
                    _ => {}
                }
            }
            let mut cells: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
            cells.sort();
            let receipts = w.receipts().len() as u64;
            // CONSERVATIVE RECOVERY across dynamics eviction (CORE-AUDIT #11). If the
            // pulse lagged MORE than the whole retained cap behind, the beat's `since`
            // slice is only the retained tail — the evicted FieldSet/CellMutated teeth
            // for the lost span never reached `field_sets`/`cell_events`, so a
            // fine-grained invalidation would UNDER-invalidate and leave stale paint
            // (violating "cache soundness = dynamics completeness"). Rather than miss
            // dirty rows, name EVERY live cell as cell-wide dirty so every open
            // pane/card re-reads its binds through the conservative `invalidate_cell`
            // tooth. Only the cosmetic activity-feed toasts for the evicted span are
            // lost (they were never a correctness invariant). In practice this branch
            // never fires — a ~250ms beat cannot emit a full retained cap of events —
            // it is the fail-safe that makes eviction SOUND, not merely cheap.
            if self.pulse_cursor < base {
                cell_events = cells.clone();
            }
            (
                cursor,
                announce,
                arrivals,
                cells,
                field_sets,
                cell_events,
                receipts,
            )
        };
        self.pulse_cursor = cursor;
        self.cells = cells;
        // THE PULSE→SIGNALS WELD, loud half — the World moved: broadcast the beat's
        // FieldSets + cell-wide mutations into every pane's AND every open card's
        // signal registry (exactly the dirty binds re-read), and mirror the moved
        // census into the World-Status panel as receipted tracking turns. The shipped
        // surfaces' binds finally track the live World.
        #[cfg(feature = "card-pane")]
        {
            let census = viewnode_pane::WorldCensus {
                cells: self.cells.len() as u64,
                receipts,
            };
            viewnode_pane::pulse_panes(&self.viewnode_panes, &field_sets, &cell_events, census, cx);
            card_pulse::pulse_cards(&self.card_panes, &field_sets, &cell_events, cx);
        }
        #[cfg(not(feature = "card-pane"))]
        let _ = (&field_sets, &cell_events, receipts);
        for (kind, line) in arrivals {
            self.toast_rack.push(kind, line);
        }
        if let Some(line) = announce {
            self.say(line);
        }
        cx.notify();
    }

    /// How many toasts the rack currently shows — a bake/test hook.
    pub fn bake_toast_count(&self) -> usize {
        self.toast_rack.toasts().len()
    }

    /// Push an announcement card directly — a bake/test hook (the pulse's feed,
    /// without needing a foreign turn).
    pub fn bake_push_toast(&mut self, refused: bool, line: &str) {
        let kind = if refused {
            toasts::ToastKind::Refused
        } else {
            toasts::ToastKind::Committed
        };
        self.toast_rack.push(kind, line);
    }

    /// The auto-arranged default grid position for a cell with no persisted slot —
    /// a left-edge column of icons (so a fresh desktop is legible before any drag).
    fn default_icon_pos(&self, idx: usize) -> Point<Pixels> {
        let rows = self.layout.prefs.grid_rows.max(1) as usize;
        let col = (idx / rows) as f32;
        let row = (idx % rows) as f32;
        Point::new(
            px(24.0 + col * (ICON_W + 16.0)),
            px(MENUBAR_H + 18.0 + row * (ICON_H + 14.0)),
        )
    }

    fn icon_pos(&self, idx: usize, cell: &CellId) -> Point<Pixels> {
        self.layout
            .icon_pos(&id_hex(cell))
            .unwrap_or_else(|| self.default_icon_pos(idx))
    }

    /// Build a fresh window-kind body for `cell` and `tag` — for the document editor
    /// this loads the cell's persisted/heap-stored prose into a live `dregg_doc::Doc`.
    fn make_kind(&self, cell: CellId, tag: WinKindTag) -> WinKind {
        match tag {
            WinKindTag::Inspector => WinKind::Inspector,
            WinKindTag::Links => WinKind::Links,
            WinKindTag::Transcript => WinKind::Transcript,
            WinKindTag::Workflow => WinKind::WorkflowComposer,
            WinKindTag::DocExplorer => WinKind::DocExplorer,
            WinKindTag::WorldExplorer => WinKind::WorldExplorer,
            WinKindTag::AgentRoom => WinKind::AgentRoom,
            WinKindTag::MailRoom => WinKind::MailRoom,
            WinKindTag::DreggComputers => WinKind::DreggComputers,
            WinKindTag::ViewNodePane => WinKind::ViewNodePane,
            WinKindTag::AndroidCell => WinKind::AndroidCell,
            WinKindTag::AppShelf => WinKind::AppShelf,
            WinKindTag::ExchangeFloor => WinKind::ExchangeFloor,
            WinKindTag::MatrixRoom => WinKind::MatrixRoom,
            WinKindTag::ProvenanceWalker => WinKind::ProvenanceWalker,
            WinKindTag::AttachWizard => WinKind::AttachWizard,
            WinKindTag::DocEditor => {
                let text = self.load_doc_text(&cell);
                let g = if self.layout.prefs.word_granularity {
                    Granularity::Word
                } else {
                    Granularity::Line
                };
                let mut doc = Doc::new(g);
                if !text.is_empty() {
                    doc.edit(self.author, &text);
                }
                WinKind::DocEditor {
                    doc,
                    buffer: text,
                    branch: None,
                    merged: None,
                }
            }
            // Other window TYPEs owned by concurrent surfaces fall back to an
            // inspector body until their own arm lands (swarm self-heal).
            #[allow(unreachable_patterns)]
            // defensive fallback for variants added by concurrent surfaces / non-default features
            _ => WinKind::Inspector,
        }
    }

    #[allow(clippy::too_many_arguments)] // window placement needs the full spatial + cell context
    fn open_window_at(
        &mut self,
        cell: CellId,
        tag: WinKindTag,
        x: f32,
        y: f32,
        w: f32,
        h: f32,
        minimized: bool,
    ) {
        let z = self.next_z;
        self.next_z += 1;
        let kind = self.make_kind(cell, tag);
        // The Agent Room anchors on its own non-ledger sentinel, so the usual
        // "{cell-kind} {id}" prefix would misread it as a zero-balance service.
        // The Provenance Walker's sentinel gets the same courtesy.
        let title = if agent_room::is_agent_room(&cell) {
            format!("the resident — {}", kind.label())
        } else if mail_room::is_mail_room(&cell) {
            // The Mail Room's sentinel gets the same courtesy — it is a post office, not
            // a zero-balance service cell.
            format!("the letter office — {}", kind.label())
        } else if matrix_room::is_matrix_room(&cell) {
            // The Matrix Room's sentinel gets the same courtesy.
            format!("membranes over the wire — {}", kind.label())
        } else if dregg_computers::is_dregg_computers(&cell) {
            // The Dregg Computers sentinel gets the same courtesy — it is your
            // fleet of vats, not a zero-balance service cell.
            format!("your vats — {}", kind.label())
        } else if provenance_walker::is_walker(&cell) {
            format!("the receipt chain — {}", kind.label())
        } else {
            format!(
                "{} {} — {}",
                self.cell_kind(&cell),
                id_short(&cell),
                kind.label()
            )
        };
        self.windows.insert(
            (cell, tag),
            WindowState {
                cell,
                title,
                x,
                y,
                w: w.max(WIN_MIN_W),
                h: h.max(WIN_MIN_H),
                minimized,
                z,
                kind,
            },
        );
    }

    /// Open (or focus) the inspector window on `cell` (the legacy double-click).
    fn open_window(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Inspector);
    }

    /// Open (or focus) the WORKFLOW-COMPOSER window on `cell` — the surface that
    /// composes intents into a workflow and decides flow-refinement.
    pub(super) fn open_workflow_window(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Workflow);
        self.say(format!(
            "Workflow composer on {} — compose intents, check refinement A ≤ᶠ B.",
            id_short(&cell)
        ));
    }

    /// The user anchor — the default counterparty for the workflow's intent steps
    /// (transfer/grant target). Exposed to the `workflow` submodule.
    pub(super) fn workflow_user(&self) -> CellId {
        self.user
    }

    /// Open (or focus) the AGENT ROOM — the resident's provable activity (mandate ·
    /// receipted actions · authorization boundary), anchored on the room's own
    /// sentinel. A fresh room watches the DEFAULT resident (the most-active cell
    /// that is not the operator) — whoever is actually doing things in the World.
    fn open_agent_room(&mut self) {
        self.open_kind(agent_room::agent_room_window_cell(), WinKindTag::AgentRoom);
        self.say(
            "Agent Room — the executor's account of the resident: receipts, \
                       mandate, and the boundary of its reach.",
        );
    }

    /// Open (or focus) the MAIL ROOM — mail between agents as cells on the live World
    /// (inbox · outbox · mail-ledger), anchored on the room's own sentinel. Opening it
    /// ensures the operator's post office exists on the World (a genesis-path install of
    /// their inbox + outbox cells + the town ferry), so a fresh room opens ready to write.
    fn open_mail_room(&mut self) {
        {
            let mut w = self.world.borrow_mut();
            crate::letter_office::ensure_office(&mut w, self.user);
            crate::letter_office::ensure_ferry(&mut w);
        }
        self.open_kind(mail_room::mail_room_window_cell(), WinKindTag::MailRoom);
        self.say(
            "Mail Room — the letter office: a letter IS a cell carrying its markdown; \
             sending drops it in your outbox, and the ferry delivers it to an inbox.",
        );
    }

    /// Open (or focus) MY DREGG COMPUTERS — the vats you can reach (the roster
    /// off the `GET /v1/vats` seam, honestly sourced), CONNECT, and the attached
    /// computer's live reflection, anchored on its own sentinel like the Agent
    /// Room.
    fn open_dregg_computers(&mut self) {
        self.open_kind(
            dregg_computers::dregg_computers_window_cell(),
            WinKindTag::DreggComputers,
        );
        self.say(format!(
            "My Dregg Computers — {}. Connect one and watch its receipts: it cannot lie to you.",
            self.vat_directory.describe()
        ));
    }

    /// **CONNECT to a Dregg Computer** — attach the vat with `cell_id` off the
    /// roster: the backend the roster's source picks (mock for the fixture; HTTP
    /// at the vat's REAL endpoint for a gateway roster — the same wire path
    /// `--node <url>` proves), then the snapshot reflection (status · remote
    /// cells · receipt tail) and, against a live endpoint, the SSE stream the
    /// pulse drains. The verdict — including an unreachable endpoint — is
    /// narrated, never swallowed.
    fn connect_vat(&mut self, cell_id: &str) {
        let Some(vat) = self.vat_directory.vat(cell_id).cloned() else {
            self.say("That computer is no longer on the roster.");
            return;
        };
        match self.vat_directory.client_for(&vat) {
            Err(refusal) => self.say(format!("Cannot connect — {refusal}")),
            Ok(client) => {
                let link = dregg_computers::VatLink::connect_with(vat, client);
                let verdict = match &link.error {
                    Some(e) => format!("Attach FAILED — {e}"),
                    None => format!(
                        "Attached to your Dregg Computer {} — {} remote cell(s), {} receipt(s){}.",
                        link.describe(),
                        link.cells.len(),
                        link.feed.receipts().len(),
                        if link.streaming() {
                            ", stream live"
                        } else {
                            ""
                        }
                    ),
                };
                self.vat_link = Some(link);
                self.say(verdict);
            }
        }
    }

    /// **DISCONNECT** from the attached Dregg Computer (drops the wire client +
    /// the SSE reader; the vat itself keeps running — detaching a screen does
    /// not power off the machine).
    fn disconnect_vat(&mut self) {
        if let Some(link) = self.vat_link.take() {
            self.say(format!(
                "Detached from {} — it keeps running without you watching.",
                link.describe()
            ));
        }
    }

    /// One pulse beat of the vat attachment: drain every receipt the SSE reader
    /// delivered since the last beat into the feed. Returns how many were NEW
    /// (each is a repaint-worthy arrival). Zero when unattached / snapshot-only.
    fn pump_vat_stream(&mut self) -> usize {
        self.vat_link.as_mut().map(|l| l.pump()).unwrap_or(0)
    }

    // ── My Dregg Computers bake/test hooks (headless drivers) ────────────────

    /// Open the My Dregg Computers window — a bake hook.
    pub fn bake_open_dregg_computers(&mut self) {
        self.open_dregg_computers();
    }

    /// The roster's card lines (the text twin of every painted vat card) plus
    /// the honest source caption — what a headless bake asserts against.
    pub fn bake_vat_roster(&self) -> Vec<String> {
        let mut v = vec![self.vat_directory.describe()];
        v.extend(
            self.vat_directory
                .vats
                .iter()
                .map(dregg_computers::vat_card_text),
        );
        v
    }

    /// CONNECT to the roster vat at `idx` (the same actuation the card button
    /// fires) and return the attachment caption — a bake hook. `None` when the
    /// index is off the roster.
    pub fn bake_connect_vat(&mut self, idx: usize) -> Option<String> {
        let cell_id = self.vat_directory.vats.get(idx)?.cell_id.clone();
        self.connect_vat(&cell_id);
        self.vat_link.as_ref().map(|l| l.describe())
    }

    /// The attached computer's reflected truths — `(remote cells, receipts,
    /// streaming)` — a bake hook. `None` when unattached.
    pub fn bake_vat_connection(&self) -> Option<(usize, usize, bool)> {
        self.vat_link
            .as_ref()
            .map(|l| (l.cells.len(), l.feed.receipts().len(), l.streaming()))
    }

    /// Open (or focus) the PROVENANCE WALKER — the receipt chain walked
    /// hash-by-hash, every link recomputed on the spot (never trusted),
    /// anchored on its own sentinel like the Agent Room.
    fn open_provenance_walker(&mut self) {
        self.open_kind(
            provenance_walker::walker_window_cell(),
            WinKindTag::ProvenanceWalker,
        );
        self.say(
            "Provenance Walker — the receipt chain, hash-by-hash: state-root \
             handoffs and blocklace back-edges re-derived as you walk.",
        );
    }

    /// Open (or focus) a window of `tag` on `cell`, restoring its persisted geometry
    /// if any, else a cascade default. The same cell can hold several window kinds.
    fn open_kind(&mut self, cell: CellId, tag: WinKindTag) {
        if let Some(ws) = self.windows.get_mut(&(cell, tag)) {
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
            return;
        }
        // Document/links/transcript windows open a touch wider than the inspector.
        let (dw, dh) = match tag {
            WinKindTag::DocEditor => (440.0, 340.0),
            WinKindTag::Transcript => (440.0, 300.0),
            WinKindTag::Links => (380.0, 300.0),
            WinKindTag::Inspector => (360.0, 300.0),
            WinKindTag::Workflow => (420.0, 460.0),
            WinKindTag::DocExplorer => (460.0, 420.0),
            WinKindTag::WorldExplorer => (480.0, 440.0),
            WinKindTag::AgentRoom => (460.0, 440.0),
            WinKindTag::ViewNodePane => (420.0, 320.0),
            // A phone-ish portrait window for the android-cell's SystemUI cap-chrome.
            WinKindTag::AndroidCell => (340.0, 520.0),
            // The App Shelf opens tall enough for the dense app roster.
            WinKindTag::AppShelf => (540.0, 460.0),
            // The Exchange Floor opens wide enough for the order book's verb rows.
            WinKindTag::ExchangeFloor => (560.0, 480.0),
            // The Matrix Room opens wide enough for the merged timeline + composer.
            WinKindTag::MatrixRoom => (560.0, 500.0),
            // The Provenance Walker opens wide for the dense hash rows + detail.
            WinKindTag::ProvenanceWalker => (560.0, 460.0),
            // The Attach Wizard opens as a calm portrait card for the five-breath walk.
            WinKindTag::AttachWizard => (420.0, 480.0),
            // The Mail Room opens tall enough for the letter cards + the compose strip.
            WinKindTag::MailRoom => (520.0, 500.0),
            // My Dregg Computers opens wide enough for the vat cards' rental truths.
            WinKindTag::DreggComputers => (560.0, 480.0),
            #[allow(unreachable_patterns)]
            // defensive fallback for variants added by concurrent surfaces / non-default features
            _ => (380.0, 320.0),
        };
        if let Some(g) = self.layout.win_geom(&id_hex(&cell), tag) {
            self.open_window_at(cell, tag, g.x, g.y, g.w, g.h, false);
        } else {
            let n = self.windows.len() as f32;
            self.open_window_at(cell, tag, 300.0 + n * 26.0, 80.0 + n * 26.0, dw, dh, false);
        }
        self.persist_window((cell, tag));
    }

    /// **Land in a surface AND leave it mold-ready** — open (or focus) the `tag` window
    /// on `cell`, then SELECT it so its Pharo halo ring floats immediately. This is the
    /// seam that makes the stranger's path ONE motion: a welcome door or a Spotter jump
    /// drops you into a live surface whose mold-in-place handles are already there — no
    /// hunting for the gesture. The unifying entry points ([`Self::welcome_dispatch`],
    /// [`Self::spotter_dispatch`]) route through here so "open" and "you can mold it"
    /// are the same arrival; it adds NO new actuation, it only welds selection to open.
    fn land_in(&mut self, cell: CellId, tag: WinKindTag) {
        self.open_kind(cell, tag);
        self.selected = Some(HaloTarget::Window((cell, tag)));
    }

    fn close_window(&mut self, key: WinKey) {
        self.windows.remove(&key);
        // Drop a halo selection that pointed at the now-closed window (no stale ring).
        if self.selected == Some(HaloTarget::Window(key)) {
            self.selected = None;
        }
        // Drop the live editor entity + its Change subscription when a document window
        // closes, so a reopen re-seeds the widget from the committed cell heap.
        if key.1 == WinKindTag::DocEditor {
            self.doc_inputs.remove(&key.0);
            self.doc_subs.remove(&key.0);
            self.doc_resync.remove(&key.0);
            self.branch_inputs.remove(&key.0);
            self.branch_subs.remove(&key.0);
        }
        if key.1 == WinKindTag::DocExplorer {
            self.doc_explorers.remove(&key.0);
        }
        if key.1 == WinKindTag::WorldExplorer {
            self.world_explorers.remove(&key.0);
        }
        if key.1 == WinKindTag::ProvenanceWalker {
            self.provenance_walkers.remove(&key.0);
        }
        // Drop the per-window view state when My Dregg Computers closes. The
        // ATTACHMENT (`vat_link`) deliberately stays: the link is to a remote
        // computer, not to a window — closing the lid does not detach the vat.
        if key.1 == WinKindTag::DreggComputers {
            self.dregg_computers.remove(&key.0);
        }
        // Drop the content-IR renderer entity when its window closes so a reopen
        // re-mints the applet + re-renders the portable tree fresh.
        #[cfg(feature = "card-pane")]
        if key.1 == WinKindTag::ViewNodePane {
            self.viewnode_panes.remove(&key.0);
        }
        // Drop the confined SystemUI cap-chrome (its PermWorld) + shade state when its
        // android-cell window closes, so a reopen re-mints a fresh confined cell.
        #[cfg(feature = "android-systemui")]
        if key.1 == WinKindTag::AndroidCell {
            self.systemui_chromes.remove(&key.0);
            self.systemui_shades.remove(&key.0);
        }
        // Drop the Matrix composer widget + per-window view state when the Matrix
        // Room closes (the STACK stays — its room cells live on the World ledger,
        // which a window close must never un-install).
        #[cfg(feature = "dev-surfaces")]
        if key.1 == WinKindTag::MatrixRoom {
            self.matrix_rooms.remove(&key.0);
            self.matrix_input = None;
            self.matrix_input_sub = None;
            self.matrix_draft.clear();
        }
        self.layout.drop_win(&id_hex(&key.0), key.1);
        self.layout.save(&self.layout_path);
    }

    fn persist_window(&mut self, key: WinKey) {
        if let Some(ws) = self.windows.get(&key) {
            self.layout.set_win_geom(WinGeom {
                cell: id_hex(&key.0),
                x: ws.x,
                y: ws.y,
                w: ws.w,
                h: ws.h,
                minimized: ws.minimized,
                kind: key.1,
            });
            self.saver.save(&self.layout);
        }
    }

    /// Whether the user holds the authority to act on a cell. The embedded World is
    /// single-custody (the operator is the authority), so every action is HELD here;
    /// a federated/cap-bounded desktop would dim the ones the held cap can't reach.
    /// We mark the issuer well (negative balance) as "system" (dim) to show the
    /// lit/dim distinction the metaphor needs.
    fn holds(&self, cell: &CellId) -> bool {
        // THE READ-ONLY PAST: while the Rewind Rail is scrubbed off LIVE the
        // desktop is a root-verified REPLAY — no verb may land a turn "in the
        // past", so every held affordance dims until the LIVE chip returns you.
        self.rewind.is_live() && self.cell_balance(cell) >= 0
    }

    // The `cell_*` readers below all route through the Rewind Rail's
    // EFFECTIVE-ledger accessor (`rewind.rs::with_effective_cell`): the live
    // World's ledger at LIVE, the root-verified replayed projection while the
    // rail is scrubbed — so the icons, the inspector bodies, and every other
    // surface built on these readers re-derive at the cursor for free.

    fn cell_balance(&self, cell: &CellId) -> i64 {
        self.with_effective_cell(cell, |c| c.state.balance())
            .unwrap_or(0)
    }

    fn cell_nonce(&self, cell: &CellId) -> u64 {
        self.with_effective_cell(cell, |c| c.state.nonce())
            .unwrap_or(0)
    }

    fn cell_lifecycle(&self, cell: &CellId) -> String {
        match self.with_effective_cell(cell, |c| c.lifecycle.clone()) {
            Some(CellLifecycle::Live) => "Live".into(),
            Some(CellLifecycle::Sealed { .. }) => "Sealed".into(),
            Some(CellLifecycle::Migrated { .. }) => "Migrated".into(),
            Some(CellLifecycle::Destroyed { .. }) => "Destroyed".into(),
            Some(CellLifecycle::Archived { .. }) => "Archived".into(),
            None => "—".into(),
        }
    }

    fn cell_cap_count(&self, cell: &CellId) -> usize {
        self.with_effective_cell(cell, |c| c.capabilities.iter().count())
            .unwrap_or(0)
    }

    /// Read state slot `index` of a cell as a u64 (the low 8 bytes of the field) —
    /// the property editor's read-back.
    fn cell_field_u64(&self, cell: &CellId, index: usize) -> u64 {
        self.with_effective_cell(cell, |c| c.state.fields.get(index).copied())
            .flatten()
            .map(|f| u64::from_le_bytes(f[..8].try_into().unwrap_or([0u8; 8])))
            .unwrap_or(0)
    }

    /// Whether the cell is currently sealed (drives the seal/unseal menu label).
    fn cell_sealed(&self, cell: &CellId) -> bool {
        matches!(
            self.with_effective_cell(cell, |c| c.lifecycle.clone()),
            Some(CellLifecycle::Sealed { .. })
        )
    }

    // ── Document text: the document-as-cell payload ──────────────────────────────
    // A document is a CELL: editing diffs into a `dregg_doc::Patch` (the chronicle
    // advances) AND lands real `SetField` turns that write the prose itself into the
    // cell's COMMITTED heap (`fields_map`, ext keys >= STATE_SLOTS, committed via
    // `fields_root`) plus a revision bump into slot 14. The committed truth is the
    // cell heap: a doc edit is a verified, receipted turn whose value reads back from
    // the committed state and survives reopen FROM THE LEDGER. The layout sidecar is
    // kept only as a fast cache / pre-heap-migration fallback.

    /// Load a document cell's prose from the COMMITTED umem-heap (`heap_map`),
    /// falling back to the layout sidecar only for cells whose prose predates the
    /// umem-heap-write path (migration) — empty for a fresh doc. The committed umem
    /// boundary is the source of truth: reopen restores from the ledger, not the
    /// sidecar.
    fn load_doc_text(&self, cell: &CellId) -> String {
        if let Some(text) = self.read_doc_from_heap(cell) {
            return text;
        }
        // Migration / cache fallback: a doc authored before the umem-heap path.
        self.layout.doc_text(&id_hex(cell)).unwrap_or_default()
    }

    /// Read a document's prose back from the cell's committed **umem-heap**
    /// (`heap_map`, collection `dregg_doc::COLL_TEXT`): key `0` holds the byte
    /// length, keys `1..` the 32-byte chunks. Returns `None` when the cell carries
    /// no umem-heap prose (length leaf absent) so the caller can fall back to the
    /// sidecar. The bytes are the verbatim values bound by the committed `heap_root`
    /// — a read off the live ledger's umem boundary.
    fn read_doc_from_heap(&self, cell: &CellId) -> Option<String> {
        let w = self.world.borrow();
        let state = &w.ledger().get(cell)?.state;
        text_from_heap(&state.heap_map)
    }

    /// The sum of all live cell balances — the conservation invariant the World keeps
    /// at zero (issuer wells are negative, accounts positive; Σδ = 0). A read-only
    /// projection over the live ledger, shown in the World-summary widget.
    fn world_balance_sum(&self) -> i64 {
        self.world
            .borrow()
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .sum()
    }

    /// The count of receipts in the World chronicle whose agent is `cell` — the
    /// cell's own turn history length, surfaced in the inspector. A read-only filter
    /// over the effective receipt log (truncated to the cursor while rewound).
    fn cell_receipt_count(&self, cell: &CellId) -> usize {
        self.effective_cell_receipt_count(cell)
    }

    /// The largest live cell balance (a denominator for the inspector's balance
    /// gauge, so a cell's value reads relative to the World's biggest holder).
    fn world_max_balance(&self) -> i64 {
        self.world
            .borrow()
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .max()
            .unwrap_or(1)
            .max(1)
    }

    /// A short kind label for a cell, derived from its balance — the icon's caption.
    fn cell_kind(&self, cell: &CellId) -> &'static str {
        let b = self.cell_balance(cell);
        if b < 0 {
            "issuer well"
        } else if b > 500_000 {
            "treasury"
        } else if b == 0 {
            "service"
        } else {
            "account"
        }
    }

    /// **The actuation surface for `cell`** — a DEEP, contextual list of everything
    /// you can do to a cell-icon (the Pharo "right-click anything and there's a menu
    /// of everything"). Open-as surfaces, verified-turn affordances, the compose
    /// gesture, lifecycle, and Properties. Lit if the cap is held, dim if not.
    fn actions_for(&self, cell: CellId) -> Vec<MenuAction> {
        use ActionKind as A;
        let held = self.holds(&cell);
        let mut v = vec![
            // ── Open-as surfaces (the window-type vocabulary) ──
            MenuAction::new("Inspect…", true, A::Inspect),
            MenuAction::new("Open as Document…", true, A::OpenDoc),
            MenuAction::new(
                "Explore Document… (history · graph · blame)",
                true,
                A::OpenDocExplorer,
            ),
            MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
            MenuAction::new("Transcript (receipt log)…", true, A::OpenTranscript),
            MenuAction::new(
                "Compose Workflow… (intents + refinement)",
                true,
                A::OpenWorkflow,
            ),
            MenuAction::sep(),
            // ── Verified-turn affordances (do it) ──
            MenuAction::new("Bump nonce  (verified turn)", held, A::BumpNonce),
        ];
        if cell != self.user {
            v.push(MenuAction::new(
                format!("Transfer 1,000 → {}", id_short(&self.user)),
                held && self.cell_balance(&cell) >= 1_000,
                A::Transfer { amount: 1_000 },
            ));
        }
        v.push(MenuAction::new(
            format!("Grant cap → {}", id_short(&self.user)),
            held,
            A::Grant { target: self.user },
        ));
        v.push(MenuAction::new(
            format!("Set field[{DOC_REV_SLOT}] += 1  (SetField turn)"),
            held,
            A::SetField {
                index: DOC_REV_SLOT,
                value: self.cell_field_u64(&cell, DOC_REV_SLOT) + 1,
            },
        ));
        v.push(MenuAction::sep());
        // ── Compose: transclude this cell into every OPEN document ──
        let mut doc_targets: Vec<CellId> = self
            .windows
            .keys()
            .filter(|(_, t)| *t == WinKindTag::DocEditor)
            .map(|(c, _)| *c)
            .collect();
        doc_targets.sort();
        doc_targets.dedup();
        if doc_targets.is_empty() {
            v.push(MenuAction::new(
                "Transclude into… (open a Document first)",
                false,
                A::OpenDoc,
            ));
        } else {
            for into in doc_targets {
                v.push(MenuAction::new(
                    format!("Transclude into doc {}", id_short(&into)),
                    true,
                    A::TranscludeInto { into },
                ));
            }
        }
        v.push(MenuAction::sep());
        // ── Lifecycle ──
        v.push(MenuAction::new(
            if self.cell_sealed(&cell) {
                "Unseal cell  (lifecycle turn)"
            } else {
                "Seal cell  (lifecycle turn)"
            },
            held,
            A::ToggleSeal,
        ));
        v.push(MenuAction::sep());
        // ── Properties (the property inspector/editor) ──
        v.push(MenuAction::new("Properties…", true, A::Properties));
        v
    }

    /// The deep right-click menu for an OPEN WINDOW (its title bar / chrome) — open
    /// the same cell in other surfaces, and the window's / cell's Properties.
    fn window_actions(&self, _cell: CellId, tag: WinKindTag) -> Vec<MenuAction> {
        use ActionKind as A;
        vec![
            MenuAction::new("Inspect this cell…", true, A::Inspect),
            MenuAction::new("Open as Document…", true, A::OpenDoc),
            MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
            MenuAction::new("Transcript…", true, A::OpenTranscript),
            MenuAction::sep(),
            MenuAction::new("Window Properties…", true, A::WindowProperties { tag }),
            MenuAction::new("Cell Properties…", true, A::Properties),
        ]
    }

    /// The right-click menu for the bare desktop background — the World transcript and
    /// desktop Preferences/customization. The Transcript/Preferences open without a
    /// cell context (handled in `actuate_desktop`).
    fn desktop_actions(&self) -> Vec<MenuAction> {
        use ActionKind as A;
        let any_win = !self.windows.is_empty();
        let mut v = vec![
            MenuAction::new(
                "World Explorer… (ledger · chronicle · Σ)",
                true,
                A::OpenWorldExplorer,
            ),
            MenuAction::new("World Transcript (receipt log)…", true, A::OpenTranscript),
            MenuAction::new(
                "Agent Room… (the resident's receipts · mandate · reach)",
                true,
                A::OpenAgentRoom,
            ),
            MenuAction::new(
                "Provenance Walker… (the receipt chain, hash-by-hash)",
                true,
                A::OpenProvenanceWalker,
            ),
            MenuAction::new(
                "Mail Room… (letters as cells · inbox · outbox · deliver)",
                true,
                A::OpenMailRoom,
            ),
            MenuAction::new(
                "My Dregg Computers… (vats you can reach · connect · receipts)",
                true,
                A::OpenDreggComputers,
            ),
            MenuAction::new("Spotter… (jump to anything)", true, A::OpenSpotter),
            MenuAction::sep(),
            // The session's woven surfaces — reachable from the bare desktop too, not only
            // the Spotter (one place, one vocabulary).
            MenuAction::new(
                "Co-author a Document… (branch · stitch · resolve)",
                true,
                A::OpenDocCollab,
            ),
        ];
        // THE APP SHELF — every pre-built starbridge-app, launchable onto the LIVE
        // World (each launch commits a real verified turn).
        #[cfg(feature = "app-registry")]
        v.push(MenuAction::new(
            "App Shelf… (pre-built apps · launch onto the World)",
            true,
            A::OpenAppShelf,
        ));
        // THE EXCHANGE FLOOR — the $DREGG agent economy: offers as live cells, every
        // verb a real verified turn, settlement Σδ=0.
        #[cfg(feature = "app-registry")]
        v.push(MenuAction::new(
            "Exchange Floor… ($DREGG economy · post → lease → settle)",
            true,
            A::OpenExchangeFloor,
        ));
        // THE MATRIX ROOM — membrane-over-Matrix: rooms as live cells, sends as
        // receipted turns, real envelope legs over the recorded sync.
        #[cfg(feature = "dev-surfaces")]
        v.push(MenuAction::new(
            "Matrix Room… (membranes over the wire · sends are receipted turns)",
            true,
            A::OpenMatrixRoom,
        ));
        // THE ATTACH WIZARD — send your AI to live here: name · brain · mandate ·
        // hire, landing a real confined resident in the Agent Room already stepping.
        #[cfg(feature = "dev-surfaces")]
        v.push(MenuAction::new(
            "Attach a resident… (send your AI to live here — name · brain · hire)",
            true,
            A::OpenAttachWizard,
        ));
        #[cfg(feature = "card-pane")]
        v.push(MenuAction::new(
            "World-Status Board… (deos.ui ViewNode · agent-composable)",
            true,
            A::OpenViewNodePane,
        ));
        #[cfg(feature = "android-systemui")]
        v.push(MenuAction::new(
            "Android Cell… (SystemUI cap-chrome · hand-over)",
            true,
            A::OpenAndroidCell,
        ));
        v.extend([
            MenuAction::sep(),
            MenuAction::new("Cascade windows", any_win, A::CascadeWindows),
            MenuAction::new("Tile windows", any_win, A::TileWindows),
            MenuAction::new("Close all windows", any_win, A::CloseAllWindows),
            MenuAction::sep(),
            MenuAction::new("Preferences & Customize…", true, A::Properties),
        ]);
        v
    }

    /// The pull-down for one menu-bar item (acts on the `user` anchor cell). Dense,
    /// per-menu vocabulary — the NT menu bar fleshed out.
    fn menubar_actions(&self, name: &str) -> Vec<MenuAction> {
        use ActionKind as A;
        let u = self.user;
        match name {
            "World" => vec![
                MenuAction::new("Transcript (receipt log)…", true, A::OpenTranscript),
                MenuAction::sep(),
                MenuAction::new("Preferences & Customize…", true, A::Properties),
            ],
            "Cell" => vec![
                MenuAction::new("Inspect user cell…", true, A::Inspect),
                MenuAction::new("Open as Document…", true, A::OpenDoc),
                MenuAction::new("Bump nonce  (verified turn)", self.holds(&u), A::BumpNonce),
                MenuAction::new("Properties…", true, A::Properties),
            ],
            "View" => {
                let mut v = vec![
                    MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
                    MenuAction::new("Transcript…", true, A::OpenTranscript),
                    MenuAction::new("Workflow Composer…", true, A::OpenWorkflow),
                    MenuAction::sep(),
                    MenuAction::new(
                        "Co-author a Document… (branch · stitch)",
                        true,
                        A::OpenDocCollab,
                    ),
                    MenuAction::sep(),
                    // The GOSSAMER toggle — the label names the flip it fires, so the
                    // menu reads as a checkbox without a glyph (font-safe in the bake).
                    MenuAction::new(
                        if self.layout.prefs.show_threads {
                            "Hide transclusion threads"
                        } else {
                            "Show transclusion threads"
                        },
                        true,
                        A::ToggleThreads,
                    ),
                ];
                #[cfg(feature = "app-registry")]
                v.push(MenuAction::new(
                    "App Shelf… (pre-built apps)",
                    true,
                    A::OpenAppShelf,
                ));
                #[cfg(feature = "app-registry")]
                v.push(MenuAction::new(
                    "Exchange Floor… (agent economy)",
                    true,
                    A::OpenExchangeFloor,
                ));
                #[cfg(feature = "card-pane")]
                v.push(MenuAction::new(
                    "World-Status Board… (agent-composable)",
                    true,
                    A::OpenViewNodePane,
                ));
                #[cfg(feature = "android-systemui")]
                v.push(MenuAction::new(
                    "Android Cell… (SystemUI cap-chrome)",
                    true,
                    A::OpenAndroidCell,
                ));
                v
            }
            "Window" => {
                let any_win = !self.windows.is_empty();
                vec![
                    MenuAction::new("New Inspector…", true, A::Inspect),
                    MenuAction::new("New Document…", true, A::OpenDoc),
                    MenuAction::new("New Transcript…", true, A::OpenTranscript),
                    MenuAction::new("New Workflow Composer…", true, A::OpenWorkflow),
                    MenuAction::sep(),
                    MenuAction::new("Cascade windows", any_win, A::CascadeWindows),
                    MenuAction::new("Tile windows", any_win, A::TileWindows),
                    MenuAction::new("Close all windows", any_win, A::CloseAllWindows),
                ]
            }
            _ => vec![MenuAction::new(
                "deos desktop — right-click anything",
                false,
                A::Inspect,
            )],
        }
    }

    /// **DO IT** — fire a real verified turn for a context-menu action, commit it on
    /// the live World, and record the outcome in the status bar. This is the ACTUATION:
    /// the user's right-click "do it" lands a real `TurnReceipt` on the cell's chain.
    fn actuate(&mut self, cell: CellId, kind: &ActionKind) {
        match kind {
            ActionKind::Inspect => {
                self.open_window(cell);
                self.say(format!(
                    "Inspecting {} ({}).",
                    id_short(&cell),
                    self.cell_kind(&cell)
                ));
            }
            ActionKind::BumpNonce => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(
                        cell,
                        vec![dregg_turn::action::Effect::IncrementNonce { cell }],
                    )
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.say(format!(
                    "Bump nonce on {} → {} (height {}).",
                    id_short(&cell),
                    Self::outcome_verdict(&outcome),
                    self.world.borrow().height()
                ));
            }
            ActionKind::Transfer { amount } => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![transfer(cell, self.user, *amount)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.say(format!(
                    "Transfer {} {} → {} → {} (height {}).",
                    amount,
                    id_short(&cell),
                    id_short(&self.user),
                    Self::outcome_verdict(&outcome),
                    self.world.borrow().height()
                ));
            }
            ActionKind::Grant { target } => {
                let slot = self.cell_cap_count(&cell) as u32 + 1;
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![grant_capability(cell, cell, *target, slot)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.say(format!(
                    "Grant cap {} → {} @{} → {} (height {}).",
                    id_short(&cell),
                    id_short(target),
                    slot,
                    Self::outcome_verdict(&outcome),
                    self.world.borrow().height()
                ));
            }
            ActionKind::OpenDoc => {
                self.open_kind(cell, WinKindTag::DocEditor);
                self.say(format!("Document editor open on {}.", id_short(&cell)));
            }
            ActionKind::OpenDocExplorer => {
                self.open_kind(cell, WinKindTag::DocExplorer);
                self.say(format!(
                    "Doc Explorer on {} — time-travel · DocGraph · blame (the patch substance).",
                    id_short(&cell)
                ));
            }
            ActionKind::OpenLinks => {
                self.open_kind(cell, WinKindTag::Links);
                self.say(format!("Links & backlinks of {}.", id_short(&cell)));
            }
            ActionKind::OpenTranscript => {
                self.open_kind(cell, WinKindTag::Transcript);
                self.say("Transcript — the World receipt log.");
            }
            ActionKind::OpenWorkflow => {
                self.open_workflow_window(cell);
            }
            ActionKind::Properties => {
                self.open_properties(PropSubject::Cell(cell));
                self.say(format!("Properties of {}.", id_short(&cell)));
            }
            ActionKind::WindowProperties { tag } => {
                self.open_properties(PropSubject::Window(cell, *tag));
                self.say(format!(
                    "Window properties of {} {:?}.",
                    id_short(&cell),
                    tag
                ));
            }
            ActionKind::SetField { index, value } => {
                let ok = self.commit_set_field(cell, *index, *value);
                self.say(format!(
                    "SetField {} field[{index}] = {value} → {} (height {}).",
                    id_short(&cell),
                    if ok { "committed" } else { "rejected" },
                    self.world.borrow().height()
                ));
            }
            ActionKind::ToggleSeal => {
                let sealed = self.cell_sealed(&cell);
                let eff = if sealed {
                    dregg_turn::action::Effect::CellUnseal { target: cell }
                } else {
                    dregg_turn::action::Effect::CellSeal {
                        target: cell,
                        reason: [0u8; 32],
                    }
                };
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![eff])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.say(format!(
                    "{} {} → {} (height {}).",
                    if sealed { "Unseal" } else { "Seal" },
                    id_short(&cell),
                    Self::outcome_verdict(&outcome),
                    self.world.borrow().height()
                ));
            }
            ActionKind::TranscludeInto { into } => {
                self.transclude_into(cell, *into);
            }
            ActionKind::CascadeWindows => self.cascade_windows(),
            ActionKind::TileWindows => self.tile_windows(),
            ActionKind::CloseAllWindows => self.close_all_windows(),
            ActionKind::ToggleThreads => self.toggle_threads(),
            // World-level surfaces (also reachable from the desktop menu) — open them
            // regardless of which cell's menu summoned them.
            ActionKind::OpenWorldExplorer => {
                self.open_kind(self.user, WinKindTag::WorldExplorer);
            }
            ActionKind::OpenAgentRoom => self.open_agent_room(),
            ActionKind::OpenProvenanceWalker => self.open_provenance_walker(),
            ActionKind::OpenMailRoom => self.open_mail_room(),
            ActionKind::OpenDreggComputers => self.open_dregg_computers(),
            ActionKind::OpenSpotter => self.open_spotter(),
            // The session's woven surfaces, reached from a cell menu too (anchored on the
            // acted-on cell): a doc-collab session, the World-Status board, an Android cell.
            ActionKind::OpenDocCollab => self.start_doc_collab(cell),
            ActionKind::OpenViewNodePane => self.land_in(cell, WinKindTag::ViewNodePane),
            ActionKind::OpenAndroidCell => self.land_in(cell, WinKindTag::AndroidCell),
            #[cfg(feature = "app-registry")]
            ActionKind::OpenAppShelf => self.open_app_shelf(),
            #[cfg(feature = "app-registry")]
            ActionKind::OpenExchangeFloor => self.open_exchange_floor(),
            #[cfg(feature = "dev-surfaces")]
            ActionKind::OpenMatrixRoom => self.open_matrix_room(),
            #[cfg(feature = "dev-surfaces")]
            ActionKind::OpenAttachWizard => self.open_attach_wizard(),
        }
    }

    /// Render a commit outcome as the status bar's verdict fragment. A committed turn
    /// reads "committed"; a REFUSAL carries its reason (and the offending action index)
    /// onto the glass — the ocap guarantee firing is a MOMENT, never a mute "rejected".
    fn outcome_verdict(outcome: &CommitOutcome) -> String {
        match outcome {
            CommitOutcome::Committed { .. } => "committed".to_string(),
            CommitOutcome::Rejected { reason, at_action } => {
                if at_action.is_empty() {
                    format!("REFUSED — {reason}")
                } else {
                    format!("REFUSED at action {at_action:?} — {reason}")
                }
            }
            CommitOutcome::Queued { .. } => "queued (world suspended)".to_string(),
        }
    }

    /// Commit a `SetField` turn writing `value` (LE u64) into `index` — the property
    /// editor's write verb. Returns whether the verified turn committed.
    fn commit_set_field(&mut self, cell: CellId, index: usize, value: u64) -> bool {
        let mut fe = [0u8; 32];
        fe[..8].copy_from_slice(&value.to_le_bytes());
        let turn = {
            let w = self.world.borrow();
            w.turn(
                cell,
                vec![dregg_turn::action::Effect::SetField {
                    cell,
                    index,
                    value: fe,
                }],
            )
        };
        self.world.borrow_mut().commit_turn(turn).is_committed()
    }

    /// **Commit a document's content INTO the cell's umem-heap** — the per-cell
    /// universal-memory boundary (`UMEM-PRIMITIVE` §8, `dregg_doc::doc_heap`). The
    /// document graph (atoms/edges/fields, with anti-forge provenance) AND its
    /// verbatim editor prose (`dregg_doc::COLL_TEXT`, recoverable on reopen) are
    /// projected into the cell's `heap_map` via [`DocHeapCell`], then `heap_root`
    /// is resealed out-of-band ([`World::set_cell_heap`] — `set_heap` /
    /// `reseal_heap_root`; NO kernel effect, the substrate already commits heap
    /// writes). The resealed `heap_root` IS the document's commitment: the boundary
    /// the inspector shows is the committed truth (not a derived witness over
    /// fields), and a reopen re-seeds the editor from it ([`Self::read_doc_from_heap`]).
    /// Returns whether the boundary was resealed.
    fn commit_doc_to_umem_heap(&mut self, cell: CellId, graph: &DocGraph, text: &str) -> bool {
        let heap = DocHeapCell::from_graph_with_text(cell.as_bytes()[0], graph.clone(), text)
            .cell()
            .state
            .heap_map
            .clone();
        self.world.borrow_mut().set_cell_heap(&cell, heap)
    }

    /// **COMPOSE — transclude a cell into a document.** Embed a provenanced reference
    /// to `src`'s content (its id, kind, balance, lifecycle) as a line into the open
    /// document on `into`. This is a genuine cross-cell compose: a receipted
    /// `dregg_doc::Patch` lands on the document AND a verified `SetField` turn bumps
    /// the document cell's revision (so the composed doc is real, receipted state).
    fn transclude_into(&mut self, src: CellId, into: CellId) {
        // The transclusion line — a live, provenanced quote of the source cell.
        let line = format!(
            "{{transclude dregg://{} · {} · balance {} · {}}}\n",
            id_hex(&src),
            self.cell_kind(&src),
            fmt_balance(self.cell_balance(&src)),
            self.cell_lifecycle(&src),
        );
        let author = self.author;
        let mut committed = false;
        let mut graph = None;
        if let Some(ws) = self.windows.get_mut(&(into, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor { doc, buffer, .. } = &mut ws.kind {
                buffer.push_str(&line);
                let new_text = buffer.clone();
                doc.edit(author, &new_text);
                graph = Some(doc.history().replay());
                committed = true;
            }
        }
        if committed {
            // Commit the composed document into the cell's umem-heap (its `heap_root`
            // boundary IS the commitment) + bump the doc cell's revision (a verified
            // turn — the receipted chronicle entry). The sidecar is kept as a cache.
            let text = self.load_doc_buffer(into);
            let graph = graph.unwrap_or_else(DocGraph::new);
            let prose_ok = self.commit_doc_to_umem_heap(into, &graph, &text);
            self.layout.set_doc_text(&id_hex(&into), &text);
            self.saver.save(&self.layout);
            let rev = self.cell_field_u64(&into, DOC_REV_SLOT) + 1;
            let ok = prose_ok && self.commit_set_field(into, DOC_REV_SLOT, rev);
            // The live editor widget must pick up the transcluded line on next render
            // (this path has no `&mut Window` to push into `InputState` directly).
            self.doc_resync.insert(into);
            self.say(format!(
                "COMPOSE: transcluded {} into doc {} → patch + umem heap_root {} (height {}).",
                id_short(&src),
                id_short(&into),
                if ok { "committed" } else { "rejected" },
                self.world.borrow().height()
            ));
        } else {
            self.say(format!(
                "COMPOSE: no open Document on {} — Open as Document first.",
                id_short(&into)
            ));
        }
    }

    /// Read the current edit buffer of an open document window (the composed prose).
    fn load_doc_buffer(&self, cell: CellId) -> String {
        match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor { buffer, .. }) => buffer.clone(),
            _ => self.load_doc_text(&cell),
        }
    }

    /// Open the property dialog over `subject`, cascading it onto the desktop.
    fn open_properties(&mut self, subject: PropSubject) {
        let n = self.windows.len() as f32;
        self.open_prop = Some(PropertyDialog {
            subject,
            at: Point::new(px(360.0 + n * 8.0), px(150.0 + n * 8.0)),
            w: 340.0,
            h: 300.0,
        });
        self.open_menu = None;
    }

    /// **Ensure the live free-typing editor exists for `cell`** — a real
    /// `gpui-component` `InputState` (rope-backed, multi-line) seeded with the cell's
    /// current committed prose, with a `Change` subscription that commits every
    /// keystroke through [`Self::edit_doc`] into the cell's heap (a receipted patch +
    /// verified revision turn). Idempotent: a second call is a no-op. Needs `window`
    /// + `cx` to build the entity, so it runs from `render_doc_body` (which threads
    ///   them) rather than the `window`-less open paths.
    fn ensure_doc_input(&mut self, cell: CellId, window: &mut Window, cx: &mut Context<Self>) {
        if self.doc_inputs.contains_key(&cell) {
            return;
        }
        let seed = self.load_doc_buffer(cell);
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .multi_line(true)
                .soft_wrap(true)
                .placeholder(
                    "Type your document — every keystroke is a receipted patch on the cell heap…",
                )
                .default_value(seed)
        });
        // The keystroke → heap seam: on every Change, fold the editor's rope into the
        // cell's committed prose (the SAME `edit_doc` the canned buttons call). The
        // editor IS the buffer; the heap commit is its side effect.
        let sub = cx.subscribe_in(
            &input,
            window,
            move |this, input, event: &InputEvent, _window, cx| {
                if matches!(event, InputEvent::Change) {
                    let text = input.read(cx).value().to_string();
                    this.edit_doc(cell, text);
                    cx.notify();
                }
            },
        );
        // Focus the editor the moment it opens — "Open as Document" lands you with a
        // live caret, ready to type (a real editor, not a click-to-focus surface). The
        // desktop is hosted under a `gpui_component::Root` (the editor widget reaches it
        // for its overlay/focus plumbing), so this is always safe.
        input.update(cx, |st, cx| st.focus(window, cx));
        self.doc_inputs.insert(cell, input);
        self.doc_subs.insert(cell, sub);
    }

    /// **The document-editor edit gesture** — replace the buffer with `new_text`,
    /// diff it into a receipted `dregg_doc::Patch` (the chronicle advances), persist
    /// the prose, and bump the document cell's revision via a real `SetField` turn.
    fn edit_doc(&mut self, cell: CellId, new_text: String) {
        let author = self.author;
        let mut patches = 0usize;
        let mut graph = None;
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor { doc, buffer, .. } = &mut ws.kind {
                *buffer = new_text.clone();
                doc.edit(author, &new_text);
                patches = doc.history().len();
                graph = Some(doc.history().replay());
            }
        }
        // Commit the document INTO the cell's umem-heap: its resealed `heap_root`
        // boundary IS the document commitment (no kernel effect — an out-of-band
        // heap write). Then bump the revision (a verified turn — the receipted
        // chronicle entry). The sidecar is kept as a fast cache; the committed
        // truth is the umem boundary, re-seeded from the ledger on reopen.
        let graph = graph.unwrap_or_else(DocGraph::new);
        let prose_ok = self.commit_doc_to_umem_heap(cell, &graph, &new_text);
        self.layout.set_doc_text(&id_hex(&cell), &new_text);
        self.saver.save(&self.layout);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT) + 1;
        let ok = prose_ok && self.commit_set_field(cell, DOC_REV_SLOT, rev);
        self.say(format!(
            "EDIT doc {} → patch #{patches} + umem heap_root {} (rev {rev}, height {}).",
            id_short(&cell),
            if ok { "committed" } else { "rejected" },
            self.world.borrow().height()
        ));
    }

    /// **The document's umem-heap boundary commitment.** A dreggverse document IS a
    /// [`dregg_doc::DocHeapCell`] — a cell whose committed `heap_root` (the
    /// sorted-Poseidon2 boundary over its umem-heap) IS the document's commitment
    /// (`UMEM-PRIMITIVE` §8, `dregg_doc::doc_heap`). Project this graph onto a fresh
    /// document cell and read its boundary root, so the surface can SHOW the document as
    /// a sovereign, content-addressed umem and watch the boundary MOVE as the document
    /// is edited, stitched, and resolved. A conflict's boundary binds BOTH live
    /// alternatives (forging or hiding one moves the root) — the anti-forge tooth, made
    /// visible. The `seed` ties the boundary to the document cell's identity.
    fn doc_umem_boundary(&self, cell: CellId, graph: &DocGraph) -> [u8; 32] {
        DocHeapCell::from_graph(cell.as_bytes()[0], graph.clone()).commitment()
    }

    /// **The document's LIVE committed umem boundary** — the cell's resealed
    /// `heap_root` straight off the ledger. After [`Self::commit_doc_to_umem_heap`]
    /// this IS the document's commitment (the projected graph + verbatim prose,
    /// bound by one sorted-Poseidon2 root), not a derived witness. `None` if the
    /// cell is absent. Distinct from [`Self::doc_umem_boundary`], which derives a
    /// hypothetical boundary from an UNcommitted graph (a confined branch or a
    /// held conflict state).
    fn live_doc_boundary(&self, cell: &CellId) -> Option<[u8; 32]> {
        Some(self.world.borrow().ledger().get(cell)?.state.heap_root)
    }

    /// A short hex of a umem boundary root (the first/last bytes), for a face-row readout.
    fn boundary_short(root: &[u8; 32]) -> String {
        format!(
            "{:02x}{:02x}{:02x}{:02x}…{:02x}{:02x}",
            root[0], root[1], root[2], root[3], root[30], root[31]
        )
    }

    /// Attribute an [`Author`] relative to the seated user: the seated author is *you*,
    /// `author ^ 1` is the *co-author* (the draft's second identity), anything else is a
    /// bare `@id`. Provenance is a FACT carried by the commitment — never a guess.
    fn author_label(&self, author: Author) -> String {
        if author == self.author {
            format!("you (@{})", self.author.0 & 0xffff)
        } else if author.0 == self.author.0 ^ 1 {
            format!("co-author (@{})", author.0 & 0xffff)
        } else {
            format!("@{}", author.0 & 0xffff)
        }
    }

    /// Ensure a live co-author DRAFT editor exists for `cell`'s forked branch — a real
    /// editable `InputState` seeded with the current draft text. Typing folds into the
    /// CONFINED branch doc as the co-author (`author ^ 1`), so a user can drive the
    /// divergence by hand. Created without stealing focus (the main editor keeps it).
    fn ensure_branch_input(&mut self, cell: CellId, window: &mut Window, cx: &mut Context<Self>) {
        if self.branch_inputs.contains_key(&cell) {
            return;
        }
        let seed = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor {
                branch: Some(b), ..
            }) => b.text(),
            _ => return, // no branch — nothing to edit
        };
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .multi_line(true)
                .soft_wrap(true)
                .placeholder("The co-author's confined draft — type a divergent edit…")
                .default_value(seed)
        });
        let sub = cx.subscribe_in(
            &input,
            window,
            move |this, input, event: &InputEvent, _window, cx| {
                if matches!(event, InputEvent::Change) {
                    let text = input.read(cx).value().to_string();
                    this.set_branch_text(cell, &text);
                    cx.notify();
                }
            },
        );
        self.branch_inputs.insert(cell, input);
        self.branch_subs.insert(cell, sub);
    }

    /// Replace the confined draft's whole text with `text`, authored as the co-author
    /// (`author ^ 1`). The branch is confined — this commits NOTHING to the heap; it
    /// only advances the draft's own patch-history, ready to stitch.
    fn set_branch_text(&mut self, cell: CellId, text: &str) {
        let coauthor = Author(self.author.0 ^ 1);
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor {
                branch: Some(b), ..
            } = &mut ws.kind
            {
                b.edit(coauthor, text);
            }
        }
    }

    /// Drop the live branch editor + its subscription (the draft retired — stitched,
    /// resolved, or refolded), so a future fork re-seeds a fresh draft editor.
    fn retire_branch_input(&mut self, cell: CellId) {
        self.branch_inputs.remove(&cell);
        self.branch_subs.remove(&cell);
    }

    /// **Fork a co-author DRAFT branch** (BRANCH-AND-STITCH-PROTOCOL §1) — clone the
    /// document's patch-history into a parallel `dregg_doc::Doc` a *second* author
    /// edits independently. The branch is confined (no heap commit) until stitched; a
    /// branch edit cannot leak into the published document. This is the live realization
    /// of "an author's draft is a branch."
    fn fork_doc_branch(&mut self, cell: CellId) {
        // A fresh fork retires any stale draft editor so the live widget re-seeds.
        self.retire_branch_input(cell);
        let g = if self.layout.prefs.word_granularity {
            Granularity::Word
        } else {
            Granularity::Line
        };
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor {
                doc,
                branch,
                merged,
                ..
            } = &mut ws.kind
            {
                *branch = Some(Doc::from_history(doc.history().branch(), g));
                *merged = None;
            }
        }
        self.say(format!(
            "BRANCH: forked a confined co-author draft of doc {} — edit it, then Stitch \
             (a divergent region becomes a first-class conflict, not a rejected merge).",
            id_short(&cell)
        ));
    }

    /// **Land in a live DOCUMENT-COLLABORATION session** — open (mold-ready) the document
    /// editor on `cell` AND fork a confined co-author draft in the same gesture, so the
    /// branch-and-stitch flow (diverge · Stitch · the first-class conflict · resolve) is
    /// present and discoverable the instant you arrive — not a button buried inside an
    /// editor you must first find. This is the seam that makes "co-author a document" ONE
    /// reachable place from the unifying Spotter (and the desktop menu). It adds no new
    /// actuation: it composes the two gestures the doc surface already performs.
    fn start_doc_collab(&mut self, cell: CellId) {
        self.land_in(cell, WinKindTag::DocEditor);
        self.fork_doc_branch(cell);
        self.say(format!(
            "Document collaboration on {} — a confined co-author draft is open. Type a \
             divergent line, then Stitch: a clashing region becomes a first-class conflict \
             you resolve (never a rejected merge).",
            id_short(&cell)
        ));
    }

    /// **A divergent edit on the draft branch** — author the branch as a *second*
    /// author (`author ^ 1`, a distinct identity) so a stitch that touches the same
    /// region yields a genuine prose antichain (two live, mutually-unordered
    /// alternatives), each carrying its author's provenance. Confined: no heap commit.
    fn diverge_branch(&mut self, cell: CellId, append: &str) {
        let coauthor = Author(self.author.0 ^ 1);
        let mut new_text = None;
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor {
                branch: Some(b), ..
            } = &mut ws.kind
            {
                let t = format!("{}{append}", b.text());
                b.edit(coauthor, &t);
                new_text = Some(t);
            }
        }
        self.say(match new_text {
            Some(t) => format!(
                "BRANCH: co-author @{} diverged the draft of doc {} ({} chars) — confined; \
                 Stitch to merge.",
                coauthor.0 & 0xffff,
                id_short(&cell),
                t.len()
            ),
            None => format!(
                "BRANCH: no draft on doc {} — Fork a draft first.",
                id_short(&cell)
            ),
        });
    }

    /// **Stitch the draft branch into the document** (BRANCH-AND-STITCH-PROTOCOL §3 —
    /// the pushout). `History::stitch` folds both branches' patches; the result is a
    /// merged `dregg_doc::Doc` that may carry FIRST-CLASS CONFLICT STATES (an antichain
    /// of live alternatives) where both authors edited one region. A clean stitch folds
    /// straight into the document + heap; a conflicted stitch is held in `merged` and
    /// surfaced as the live ConflictView (resolved by a later patch — never rejected).
    fn stitch_branch(&mut self, cell: CellId) {
        let g = if self.layout.prefs.word_granularity {
            Granularity::Word
        } else {
            Granularity::Line
        };
        let mut outcome: Option<(bool, String)> = None; // (conflicted, clean_text)
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor {
                doc,
                branch: Some(b),
                merged,
                ..
            } = &mut ws.kind
            {
                let mut stitched = doc.history().branch();
                stitched.stitch(b.history());
                let graph = stitched.replay();
                let rendered = content(&graph);
                let stitched_doc = Doc::from_history(stitched, g);
                if rendered.has_conflict() {
                    *merged = Some(stitched_doc);
                    outcome = Some((true, String::new()));
                } else {
                    // Clean stitch — adopt the merged history as the document's own.
                    let text = stitched_doc.text();
                    *doc = stitched_doc;
                    *merged = None;
                    outcome = Some((false, text));
                }
            }
        }
        match outcome {
            Some((true, _)) => {
                let n = self
                    .doc_merged_conflict_count(cell)
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "?".into());
                self.say(format!(
                    "STITCH doc {} → {n} first-class CONFLICT(s): both authors edited a \
                     region. Resolve below (a resolution is itself a receipted patch).",
                    id_short(&cell)
                ));
            }
            Some((false, text)) => {
                // A clean merge folds into the committed heap as a real revision turn.
                self.edit_doc(cell, text);
                if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
                    if let WinKind::DocEditor { branch, .. } = &mut ws.kind {
                        *branch = None;
                    }
                }
                self.retire_branch_input(cell);
                self.say(format!(
                    "STITCH doc {} → clean merge (disjoint edits union) committed to heap.",
                    id_short(&cell)
                ));
            }
            None => {
                self.say(format!(
                    "STITCH: no draft on doc {} — Fork a draft first.",
                    id_short(&cell)
                ));
            }
        }
    }

    /// How many unresolved conflict regions the stitched (merged) document carries, if
    /// any. `None` when there is no merged document open on the cell.
    fn doc_merged_conflict_count(&self, cell: CellId) -> Option<usize> {
        match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor {
                merged: Some(m), ..
            }) => Some(content(&m.history().replay()).conflicts().count()),
            _ => None,
        }
    }

    /// **Resolve one conflict region with one choice** — apply the ready
    /// `ResolutionChoice` patch (keep-this / order-both / choose-value) to the merged
    /// document's history. A resolution is *just another additive authored patch*
    /// (`dregg_doc` resolve.rs); after it the antichain collapses. When the merged
    /// document is fully conflict-free, it FOLDS into the document + a real verified
    /// heap-commit turn, and the draft branch retires — the merge is published.
    fn resolve_conflict(&mut self, cell: CellId, region_idx: usize, choice_idx: usize) {
        let author = self.author;
        // Build the resolving patch off the live merged graph + chosen region/choice.
        let choice: Option<ResolutionChoice> = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor {
                merged: Some(m), ..
            }) => {
                let graph = m.history().replay();
                // Clone the chosen region out so the `rendered` borrow ends here,
                // then build its resolution menu against the (still-live) graph.
                let region = content(&graph).conflicts().nth(region_idx).cloned();
                region.and_then(|region| {
                    resolutions_for(&graph, &region, author)
                        .into_iter()
                        .nth(choice_idx)
                })
            }
            _ => None,
        };
        let Some(choice) = choice else {
            self.say("RESOLVE: that conflict/choice is gone (already resolved?).");
            return;
        };
        // Apply the resolution patch onto the merged history; re-render.
        let mut published: Option<(Doc, bool)> = None; // (doc, fully_clean)
        let mut receipt_out: Option<PatchId> = None;
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor {
                merged: Some(m), ..
            } = &mut ws.kind
            {
                let mut h = m.history().branch();
                receipt_out = Some(h.commit(choice.patch.clone()));
                let still_conflicted = content(&h.replay()).has_conflict();
                let g = if self.layout.prefs.word_granularity {
                    Granularity::Word
                } else {
                    Granularity::Line
                };
                let resolved = Doc::from_history(h, g);
                published = Some((resolved, !still_conflicted));
            }
        }
        // The resolution patch's id IS the turn's receipt — surface it.
        if let Some(receipt) = receipt_out {
            self.last_resolution = Some((cell, choice.label.clone(), receipt));
        }
        let Some((resolved, clean)) = published else {
            return;
        };
        if clean {
            // The conflict is fully resolved — publish: adopt the merged history as the
            // document's own, retire the branch, and commit the resolved prose to heap.
            let text = resolved.text();
            if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
                if let WinKind::DocEditor {
                    doc,
                    branch,
                    merged,
                    ..
                } = &mut ws.kind
                {
                    *doc = resolved;
                    *branch = None;
                    *merged = None;
                }
            }
            self.retire_branch_input(cell);
            self.edit_doc(cell, text);
            self.say(format!(
                "RESOLVE doc {} → '{}' — conflict collapsed, merge PUBLISHED to heap \
                 (the resolution is itself a receipted patch).",
                id_short(&cell),
                choice.label
            ));
        } else {
            // Still conflicted (more regions / concurrent resolutions) — hold the merged
            // doc with the resolution folded in; the remaining conflicts stay live.
            if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
                if let WinKind::DocEditor { merged, .. } = &mut ws.kind {
                    *merged = Some(resolved);
                }
            }
            self.say(format!(
                "RESOLVE doc {} → '{}' applied; further conflict(s) remain (resolution is \
                 closed under its own conflicts).",
                id_short(&cell),
                choice.label
            ));
        }
    }

    // ── THE SPOTTER — the Pharo command palette (fuzzy-jump to anything) ──

    /// Open the Spotter overlay (empty query, top candidate selected).
    fn open_spotter(&mut self) {
        self.spotter = Some(SpotterUi {
            query: String::new(),
            selected: 0,
            input: None,
            _sub: None,
        });
        self.open_menu = None;
        self.say("Spotter — type to jump to any cell, action, or surface.");
    }

    /// **THE KEYBOARD SPINE's dispatcher** — the gpui-free model half (the root's
    /// `on_key_down` listener wraps it; the bake drives it directly). Returns whether
    /// the keystroke changed anything (the caller notifies).
    ///
    ///   * `⌘K` / `Ctrl-K` — summon the Spotter from anywhere; press again to dismiss.
    ///   * Spotter open: `↑`/`↓` move the selection (clamped to the ranked list),
    ///     `Escape` closes. (`Enter` dispatches via the query field's `PressEnter`.)
    ///   * Otherwise `Escape` climbs the dismissal ladder one rung per press:
    ///     context menu → property dialog → halo selection.
    fn on_key_model(&mut self, key: &str, cmd: bool) -> bool {
        if cmd && key == "k" {
            if self.spotter.is_some() {
                self.spotter = None;
            } else {
                self.open_spotter();
            }
            return true;
        }
        if self.spotter.is_some() {
            return match key {
                "escape" => {
                    self.spotter = None;
                    true
                }
                "down" | "up" => {
                    let max = self.spotter_ranked().len().saturating_sub(1);
                    if let Some(ui) = self.spotter.as_mut() {
                        ui.selected = if key == "down" {
                            (ui.selected + 1).min(max)
                        } else {
                            ui.selected.saturating_sub(1)
                        };
                    }
                    true
                }
                _ => false,
            };
        }
        // THE ATTACH WIZARD's name field — while it is capturing, printable keys and
        // Backspace type into the resident's name (Escape/Enter release capture). It
        // sits below ⌘K + the Spotter (they still win) and above the Escape ladder.
        #[cfg(feature = "dev-surfaces")]
        if self.wizard_type_key(key, cmd) {
            return true;
        }
        if key == "escape" {
            if self.open_menu.take().is_some() {
                return true;
            }
            if self.open_prop.take().is_some() {
                return true;
            }
            if self.selected.take().is_some() {
                return true;
            }
        }
        false
    }

    /// Drive one keystroke through the spine — a bake/test hook (the same model fn
    /// the root listener runs; `cmd` = platform/control held).
    pub fn bake_key(&mut self, key: &str, cmd: bool) -> bool {
        self.on_key_model(key, cmd)
    }

    /// The receipt console's log length — a bake/test hook (every `say()` lands).
    pub fn bake_status_log_len(&self) -> usize {
        self.status_log.len()
    }

    /// The unread-narration count — a bake/test hook (ticks while the flyout is
    /// closed; opening clears it).
    pub fn bake_status_unread(&self) -> usize {
        self.status_unread
    }

    /// Toggle the receipt-console flyout — a bake/test hook (the status bar click).
    pub fn bake_toggle_status_console(&mut self) -> bool {
        self.status_flyout = !self.status_flyout;
        if self.status_flyout {
            self.status_unread = 0;
        }
        self.status_flyout
    }

    /// BAKE: read a dense face's scroll offset (y px — `0.0` at the top, growing
    /// NEGATIVE as the face scrolls down) straight off its persistent handle in
    /// the face-scroll registry. The witness that scroll POSITION is desktop
    /// view-state (it survives repaints and window reopens), not per-frame
    /// element state. Ensures the handle, so a bake can probe a face pre-render.
    pub fn bake_scroll_offset_y(&mut self, key: FaceScrollKey) -> f32 {
        f32::from(self.face_scrolls.ensure(key).offset().y)
    }

    /// BAKE: drive a face's scroll position (the headless stand-in for a wheel /
    /// thumb drag) through the SAME persistent handle the rendered face tracks.
    pub fn bake_scroll_to(&mut self, key: FaceScrollKey, y: f32) {
        self.face_scrolls
            .ensure(key)
            .set_offset(gpui::point(px(0.0), px(y)));
    }

    // ── UNCAP WITNESSES: what a virtualized face paints at an offset ──────────────
    //
    // The uncapped faces render only their *visible* rows through `v_virtual_list`,
    // so "the chronicle is no longer a 24-row peephole" cannot be witnessed by
    // counting eager children (there are none off-screen). These bakes stand in for
    // the kit's window-bound prepaint headlessly: the SAME uniform-height range math
    // (`virtual_face::visible_row_range`) the kit runs, over the SAME pure row
    // renderers the live face maps, over the live World — so a 10k-row bake proves
    // "offset N shows exactly these receipts" and "parked on the tail, the newest
    // receipt is in view" without standing up a window.

    /// BAKE: the row TEXTS the virtualized **Chronicle** paints at scroll
    /// `offset_y` in a `viewport_h`-tall viewport, over the live receipt log.
    pub fn bake_chronicle_rows_at(&self, offset_y: f32, viewport_h: f32) -> Vec<String> {
        let w = self.world.borrow();
        let receipts = w.receipts();
        virtual_face::visible_row_range(
            receipts.len(),
            world_explorer::CHRONICLE_ROW_H,
            viewport_h,
            offset_y,
        )
        .filter_map(|i| {
            receipts
                .get(i)
                .map(|r| world_explorer::chronicle_row_text(i, r))
        })
        .collect()
    }

    /// BAKE: the row TEXTS the virtualized **Transcript** paints at scroll
    /// `offset_y` in a `viewport_h`-tall viewport, over the live receipt log.
    pub fn bake_transcript_rows_at(&self, offset_y: f32, viewport_h: f32) -> Vec<String> {
        let w = self.world.borrow();
        let receipts = w.receipts();
        virtual_face::visible_row_range(receipts.len(), TRANSCRIPT_ROW_H, viewport_h, offset_y)
            .filter_map(|i| receipts.get(i).map(|r| transcript_row_text(i, r)))
            .collect()
    }

    /// BAKE: parked on the tail, the Transcript's NEWEST receipt is in the painted
    /// window — the visible end of `tail -f`. Returns that newest row's text, or
    /// `None` if the newest row is somehow not in view (a failed tail) or the log
    /// is empty.
    pub fn bake_transcript_tail_row(&self, viewport_h: f32) -> Option<String> {
        let w = self.world.borrow();
        let receipts = w.receipts();
        let n = receipts.len();
        if n == 0 {
            return None;
        }
        let off = virtual_face::tail_offset(n, TRANSCRIPT_ROW_H, viewport_h);
        virtual_face::visible_row_range(n, TRANSCRIPT_ROW_H, viewport_h, off)
            .contains(&(n - 1))
            .then(|| transcript_row_text(n - 1, &receipts[n - 1]))
    }

    /// BAKE: the row TEXTS the virtualized **receipt console** paints at scroll
    /// `offset_y` — over the WHOLE `say()` ring, not the old newest-24 peephole.
    pub fn bake_status_console_rows_at(&self, offset_y: f32, viewport_h: f32) -> Vec<String> {
        virtual_face::visible_row_range(self.status_log.len(), STATUS_ROW_H, viewport_h, offset_y)
            .filter_map(|i| self.status_log.get(i).cloned())
            .collect()
    }

    /// Build the Spotter candidate set over the World's cells (each cell + its action
    /// verbs), reading live faces off the ledger. Delegates the entry shapes to
    /// [`spotter::candidates_for_cells`].
    fn spotter_candidates(&self) -> Vec<spotter::SpotterEntry> {
        // The OPEN WINDOWS come first of all (front-most first): a jump to a place
        // already on the glass is the cheapest move there is, and `rank`'s stable
        // sort keeps input order on ties, so windows outrank only at EQUAL match
        // quality — a strictly stronger fuzzy match elsewhere still wins.
        let mut out = spotter::window_candidates(&self.spotter_window_rows());
        // Then the GLOBAL surfaces (World Explorer · Transcript · the Portable-IR
        // card…), so the unifying entry opens onto the whole rooms of the desktop
        // before the per-cell vocabulary — one entry to every surface + every cell.
        out.extend(spotter::surface_candidates());
        // THE APP SHELF vocabulary — the shelf surface + one "Launch <name> · app"
        // per registry app, so the one-keystroke entry reaches every pre-built app.
        #[cfg(feature = "app-registry")]
        out.extend(app_shelf::app_spotter_candidates());
        // THE EXCHANGE FLOOR — the one entry to the agent-economy room (offers ride
        // the per-cell candidates below; an offer IS a cell).
        #[cfg(feature = "app-registry")]
        out.extend(exchange_floor::exchange_spotter_candidates());
        out.extend(spotter::candidates_for_cells(&self.cells, |c| {
            (
                self.cell_kind(c).to_string(),
                format!(
                    "balance {} · {}",
                    fmt_balance(self.cell_balance(c)),
                    self.cell_lifecycle(c)
                ),
            )
        }));
        out
    }

    /// The open windows as `(title, cell, kind)` rows for the Spotter's
    /// jump-to-window candidates — front-most (highest z) first, so the window you
    /// touched last is the first row a bare query greets.
    fn spotter_window_rows(&self) -> Vec<(String, CellId, WinKindTag)> {
        let mut rows: Vec<(&WinKey, &WindowState)> = self.windows.iter().collect();
        rows.sort_by_key(|(_, ws)| std::cmp::Reverse(ws.z));
        rows.into_iter()
            .map(|(key, ws)| (ws.title.clone(), key.0, key.1))
            .collect()
    }

    /// The ranked candidates for the live query — three layers, in rank order:
    ///
    ///   1. **COMMANDS** — when the verb prefix parses ([`spotter::parse_command`]),
    ///      the synthesized ready-to-commit entries sit ABOVE every fuzzy match, and
    ///      ONLY then (any other query never sees them — the fuzzy jump is intact).
    ///   2. **RECENTS** — on an empty query only, the last 8 dispatches greet you.
    ///   3. The fuzzy-ranked candidate set (empty query = the full list, in order).
    fn spotter_ranked(&self) -> Vec<spotter::SpotterEntry> {
        let q = self
            .spotter
            .as_ref()
            .map(|s| s.query.as_str())
            .unwrap_or("");
        let mut out = self.spotter_command_entries(q);
        if q.trim().is_empty() {
            out.extend(self.spotter_recent_entries());
        }
        out.extend(spotter::rank(q, &self.spotter_candidates()));
        out
    }

    /// Every live cell whose full hex id starts with `prefix` (already lowercased by
    /// the parser) — the command line's argument resolution against the LIVE ledger.
    /// One hit = a ready command; several = the entries fan out, one per completion
    /// (pick the one you meant); none = the query falls back to the plain fuzzy jump.
    fn resolve_prefix(&self, prefix: &str) -> Vec<CellId> {
        self.cells
            .iter()
            .filter(|c| id_hex(c).starts_with(prefix))
            .copied()
            .collect()
    }

    /// Synthesize the COMMAND entries for `query` — the Spotter-as-command-line
    /// half. The pure grammar ([`spotter::parse_command`]) reads the verb; this
    /// resolves each cell prefix via [`Self::resolve_prefix`] and emits one entry
    /// per resolution (capped at 6 so an ambiguous fan-out stays a list, not a
    /// flood). The targets carry RESOLVED `CellId`s; dispatch routes them through
    /// the SAME verified-turn actuations the context menu fires. An omitted source
    /// (`transfer 500 to 87a5` · `grant ccfc9955`) is the operator's own cell.
    fn spotter_command_entries(&self, query: &str) -> Vec<spotter::SpotterEntry> {
        use spotter::{SpotterCommand as C, SpotterEntry, SpotterTarget as Tg};
        let Some(cmd) = spotter::parse_command(query) else {
            return Vec::new();
        };
        let sub = "command · a verified turn on the live World · Enter to commit";
        let name = |c: &CellId| format!("{} {}", self.cell_kind(c), id_short(c));
        let mut out = Vec::new();
        match cmd {
            C::Transfer { amount, src, dst } => {
                let srcs = src
                    .map(|p| self.resolve_prefix(&p))
                    .unwrap_or_else(|| vec![self.user]);
                let dsts = self.resolve_prefix(&dst);
                for s in &srcs {
                    for d in &dsts {
                        if s == d {
                            continue; // a self-transfer is no move at all
                        }
                        out.push(SpotterEntry {
                            label: format!(
                                "Transfer {}  {} → {}",
                                chrome::group(amount),
                                name(s),
                                name(d)
                            ),
                            sublabel: sub.to_string(),
                            target: Tg::CmdTransfer {
                                src: *s,
                                dst: *d,
                                amount,
                            },
                            score: 0,
                        });
                    }
                }
            }
            C::Grant { src, dst } => {
                let srcs = src
                    .map(|p| self.resolve_prefix(&p))
                    .unwrap_or_else(|| vec![self.user]);
                let dsts = self.resolve_prefix(&dst);
                for s in &srcs {
                    for d in &dsts {
                        out.push(SpotterEntry {
                            label: format!("Grant cap  {} → {}", name(s), name(d)),
                            sublabel: sub.to_string(),
                            target: Tg::CmdGrant { src: *s, dst: *d },
                            score: 0,
                        });
                    }
                }
            }
            C::Bump { target } => {
                for c in self.resolve_prefix(&target) {
                    out.push(SpotterEntry {
                        label: format!("Bump nonce  {}", name(&c)),
                        sublabel: sub.to_string(),
                        target: Tg::CmdBump(c),
                        score: 0,
                    });
                }
            }
            C::Seal { target } => {
                for c in self.resolve_prefix(&target) {
                    let verb = if self.cell_sealed(&c) {
                        "Unseal"
                    } else {
                        "Seal"
                    };
                    out.push(SpotterEntry {
                        label: format!("{verb}  {}", name(&c)),
                        sublabel: sub.to_string(),
                        target: Tg::CmdSeal(c),
                        score: 0,
                    });
                }
            }
        }
        out.truncate(6);
        out
    }

    /// The RECENT-JUMPS rows the empty-query palette greets you with — the last 8
    /// dispatches, newest first, each RE-RESOLVED against the live desktop rather
    /// than replayed blind: a recent command re-parses + re-resolves its prefixes
    /// (it fires on today's ledger), a recent jump matches its label back into the
    /// current candidate set (a closed window / vanished cell quietly drops out).
    fn spotter_recent_entries(&self) -> Vec<spotter::SpotterEntry> {
        if self.layout.prefs.recent_jumps.is_empty() {
            return Vec::new();
        }
        let full = self.spotter_candidates();
        self.layout
            .prefs
            .recent_jumps
            .iter()
            .filter_map(|r| {
                let hit = self
                    .spotter_command_entries(r)
                    .into_iter()
                    .next()
                    .or_else(|| full.iter().find(|e| e.label == *r).cloned())?;
                Some(spotter::SpotterEntry {
                    sublabel: format!("recent · {}", hit.sublabel),
                    ..hit
                })
            })
            .collect()
    }

    /// Remember a Spotter dispatch on the RECENT-JUMPS trail (newest first, deduped,
    /// capped at 8) and persist it with the layout prefs — the same cold-path sync
    /// save the welcome dismissal uses, so the trail survives reopen. `replay` is
    /// the entry's replay string ([`spotter::replay_string`]): a jump's label, or a
    /// command's canonical verb line (re-parsed + re-resolved when shown again).
    fn note_recent_jump(&mut self, replay: String) {
        let recents = &mut self.layout.prefs.recent_jumps;
        recents.retain(|r| *r != replay);
        recents.insert(0, replay);
        recents.truncate(8);
        self.layout.save(&self.layout_path);
    }

    /// Dispatch the Spotter's selected (or `idx`-th) candidate: open the corresponding
    /// surface / fire the gesture, then close the overlay. The single keystroke that
    /// ties every surface together.
    fn spotter_dispatch(&mut self, idx: Option<usize>) {
        use spotter::SpotterTarget as Tg;
        let ranked = self.spotter_ranked();
        let i = idx.unwrap_or_else(|| self.spotter.as_ref().map(|s| s.selected).unwrap_or(0));
        let Some(entry) = ranked.get(i) else {
            self.spotter = None;
            return;
        };
        // THE RECENT-JUMPS TRAIL — every dispatch is remembered (newest first,
        // deduped, capped at 8, persisted with the prefs) so the next empty-query
        // palette greets you with your own trail. Recorded BEFORE the match so the
        // early-returning arms (commands, app launches) land on it too.
        self.note_recent_jump(spotter::replay_string(entry));
        // Every jump LANDS MOLD-READY: the opened surface is selected so its halo ring
        // is already floating when you arrive (the unifying entry hands you straight to
        // the mold-in-place gesture). Global surfaces anchor on the user sentinel.
        match entry.target.clone() {
            Tg::Cell(c) | Tg::Inspect(c) => self.land_in(c, WinKindTag::Inspector),
            Tg::OpenDoc(c) => self.land_in(c, WinKindTag::DocEditor),
            Tg::Explore(c) => self.land_in(c, WinKindTag::DocExplorer),
            Tg::Links(c) => self.land_in(c, WinKindTag::Links),
            Tg::Transcript(c) => self.land_in(c, WinKindTag::Transcript),
            Tg::Workflow(c) => {
                self.open_workflow_window(c);
                self.selected = Some(HaloTarget::Window((c, WinKindTag::Workflow)));
            }
            Tg::WorldExplorer => self.land_in(self.user, WinKindTag::WorldExplorer),
            Tg::AgentRoom => {
                self.land_in(agent_room::agent_room_window_cell(), WinKindTag::AgentRoom)
            }
            Tg::ProvenanceWalker => self.land_in(
                provenance_walker::walker_window_cell(),
                WinKindTag::ProvenanceWalker,
            ),
            // The Mail Room's opener ensures the operator's office (a genesis-path install
            // when missing) and lands mold-ready like every other global surface.
            Tg::MailRoom => {
                self.open_mail_room();
                self.selected = Some(HaloTarget::Window((
                    mail_room::mail_room_window_cell(),
                    WinKindTag::MailRoom,
                )));
            }
            // My Dregg Computers' opener narrates the roster source (fixture vs
            // live gateway) and lands mold-ready like every other global surface.
            Tg::DreggComputers => {
                self.open_dregg_computers();
                self.selected = Some(HaloTarget::Window((
                    dregg_computers::dregg_computers_window_cell(),
                    WinKindTag::DreggComputers,
                )));
            }
            Tg::WorldTranscript => self.land_in(self.user, WinKindTag::Transcript),
            Tg::DocCollab => self.start_doc_collab(self.user),
            #[cfg(feature = "card-pane")]
            Tg::PortableCard => self.land_in(self.user, WinKindTag::ViewNodePane),
            #[cfg(feature = "card-pane")]
            Tg::BotSurface => self.land_in(
                bot_surface::bot_surface_window_cell(),
                WinKindTag::ViewNodePane,
            ),
            #[cfg(feature = "android-systemui")]
            Tg::AndroidCell => self.land_in(self.user, WinKindTag::AndroidCell),
            #[cfg(feature = "app-registry")]
            Tg::AppShelf => self.land_in(self.user, WinKindTag::AppShelf),
            // The floor's opener ensures the substrate (a real launch when missing)
            // and lands mold-ready like every other global surface.
            #[cfg(feature = "app-registry")]
            Tg::ExchangeFloor => self.open_exchange_floor(),
            // The Matrix Room's opener installs the room cells + the Matrix-hand
            // onto the LIVE World on first open, then lands mold-ready.
            #[cfg(feature = "dev-surfaces")]
            Tg::MatrixRoom => self.open_matrix_room(),
            // The Attach Wizard's opener starts a FRESH five-breath walk and lands
            // mold-ready like every other global surface.
            #[cfg(feature = "dev-surfaces")]
            Tg::AttachWizard => self.open_attach_wizard(),
            // Launching an app writes its OWN rich status line (the receipt landmark),
            // so this arm returns early rather than letting the generic "Spotter → …"
            // overwrite the committed-turn verdict.
            #[cfg(feature = "app-registry")]
            Tg::LaunchApp(id) => {
                self.spotter = None;
                self.launch_shelf_app(id);
                return;
            }
            // Jump to an ALREADY-OPEN window: raise + un-minimize + land mold-ready
            // (the same halo-selected arrival every other jump makes).
            Tg::FocusWindow(c, tag) => {
                self.focus_window((c, tag));
                self.selected = Some(HaloTarget::Window((c, tag)));
            }
            // ── THE COMMAND LINE's verbs — receipted turns with their own verdict
            // narration. Each routes through the SAME actuation the context menu
            // fires and returns early: the receipt line (committed / REFUSED, with
            // the chronicle height) IS the story; the generic "Spotter → …" jump
            // line must not clobber it — the LaunchApp precedent, held to.
            Tg::CmdTransfer { src, dst, amount } => {
                self.spotter = None;
                let outcome = self.commit_transfer(src, dst, amount);
                self.say(format!(
                    "Spotter command: transfer {} {} → {} → {} (height {}).",
                    chrome::group(amount),
                    id_short(&src),
                    id_short(&dst),
                    Self::outcome_verdict(&outcome),
                    self.world.borrow().height()
                ));
                return;
            }
            Tg::CmdGrant { src, dst } => {
                self.spotter = None;
                self.actuate(src, &ActionKind::Grant { target: dst });
                return;
            }
            Tg::CmdBump(c) => {
                self.spotter = None;
                self.actuate(c, &ActionKind::BumpNonce);
                return;
            }
            Tg::CmdSeal(c) => {
                self.spotter = None;
                self.actuate(c, &ActionKind::ToggleSeal);
                return;
            }
        }
        self.say(format!("Spotter → {}", entry.label));
        self.spotter = None;
    }

    /// Dismiss the warm WELCOME card and remember the newcomer has been greeted (so the
    /// calm front door shows exactly once — thereafter the room opens bare). Persisting
    /// `welcomed` is a pure layout change, like any other preference.
    fn dismiss_welcome(&mut self) {
        self.show_welcome = false;
        self.layout.prefs.welcomed = true;
        self.layout.save(&self.layout_path);
    }

    /// Step through one of the welcome card's warm doors. Each maps to a real desktop
    /// gesture the adept fires too — the welcome only *names the first move* in plain
    /// words; it invents no beginner-only machinery. Dismisses the card in the same
    /// breath (you have begun; the front door steps aside).
    fn welcome_dispatch(&mut self, action: welcome::WelcomeAction) {
        use welcome::WelcomeAction as A;
        self.dismiss_welcome();
        match action {
            A::LookAround => {
                // The gentlest door still teaches the ONE gesture: select the user's own
                // cell so its halo ring floats — the handles say "you can touch me" before
                // the newcomer reads a word. (Selecting an icon fires nothing; it only
                // invites.) A bare-desktop click clears it again whenever they like.
                self.selected = Some(HaloTarget::Icon(self.user));
                self.say(
                    "Look around — that ring of handles molds a cell in place; hover any cell \
                     for its menu, double-click to open it.",
                );
            }
            A::FindAnything => self.open_spotter(),
            A::WriteSomething => {
                // Open the user's own cell as a fresh page — the newcomer's first
                // document, on the cell that is *them* — and land mold-ready (its halo
                // floats so the next gesture, "mold it", is already in reach).
                self.land_in(self.user, WinKindTag::DocEditor);
                self.say(
                    "Write something — type, and every keystroke is kept. The ring of handles \
                     molds this surface in place.",
                );
            }
            A::SeeTheWorld => {
                self.land_in(self.user, WinKindTag::WorldExplorer);
                self.say("The whole world — every cell, every receipt, balance summing to zero.");
            }
        }
    }

    /// Actuate a desktop-background menu action (no cell context).
    fn actuate_desktop(&mut self, kind: &ActionKind) {
        match kind {
            ActionKind::OpenTranscript => {
                // The transcript over the World — anchor it on the user cell's window.
                self.open_kind(self.user, WinKindTag::Transcript);
                self.say("World Transcript — the receipt log of every turn.");
            }
            ActionKind::OpenWorldExplorer => {
                // The World Explorer anchors on the user cell (a stable sentinel).
                self.open_kind(self.user, WinKindTag::WorldExplorer);
                self.say("World Explorer — the ledger census · the chronicle · Σ balance = 0.");
            }
            ActionKind::OpenAgentRoom => self.open_agent_room(),
            ActionKind::OpenProvenanceWalker => self.open_provenance_walker(),
            ActionKind::OpenMailRoom => self.open_mail_room(),
            ActionKind::OpenDreggComputers => self.open_dregg_computers(),
            ActionKind::OpenSpotter => self.open_spotter(),
            ActionKind::OpenDocCollab => self.start_doc_collab(self.user),
            ActionKind::OpenViewNodePane => {
                self.land_in(self.user, WinKindTag::ViewNodePane);
                self.say(
                    "World-Status Board — the agent-composable ViewNode surface (reflect-on \
                     + rewrite). Mold it in place with its halo handles.",
                );
            }
            ActionKind::OpenAndroidCell => {
                self.land_in(self.user, WinKindTag::AndroidCell);
                self.say(
                    "Android Cell — a confined app's caps on the glass; pull the shade to see \
                     every authority, tap the hand-over sheet to grant a real cap.",
                );
            }
            #[cfg(feature = "app-registry")]
            ActionKind::OpenAppShelf => self.open_app_shelf(),
            #[cfg(feature = "app-registry")]
            ActionKind::OpenExchangeFloor => self.open_exchange_floor(),
            #[cfg(feature = "dev-surfaces")]
            ActionKind::OpenMatrixRoom => self.open_matrix_room(),
            #[cfg(feature = "dev-surfaces")]
            ActionKind::OpenAttachWizard => self.open_attach_wizard(),
            ActionKind::Properties => {
                self.open_properties(PropSubject::Desktop);
                self.say("Desktop Preferences & customization.");
            }
            ActionKind::CascadeWindows => self.cascade_windows(),
            ActionKind::TileWindows => self.tile_windows(),
            ActionKind::CloseAllWindows => self.close_all_windows(),
            _ => {}
        }
    }

    /// **Commit ONE transfer turn** `src → dst` for `amount` — the single
    /// verified-turn body behind both the spatial compose-drop gesture and the
    /// Spotter's `transfer` command, factored so the palette's typed verb and the
    /// drag gesture are provably the SAME actuation. Returns the executor's
    /// verdict; the narration is each caller's own (a drop says COMPOSE, the
    /// command line says its receipt).
    fn commit_transfer(&mut self, src: CellId, dst: CellId, amount: u64) -> CommitOutcome {
        let turn = {
            let w = self.world.borrow();
            w.turn(src, vec![transfer(src, dst, amount)])
        };
        self.world.borrow_mut().commit_turn(turn)
    }

    /// **COMPOSE** — drop cell `src` ONTO cell `dst`: act across them with the
    /// dropped affordance. A transfer when `src` has balance, else a cap grant. This
    /// is the spatial compose gesture (drag one icon onto another).
    fn compose_drop(&mut self, src: CellId, dst: CellId) {
        if src == dst {
            return;
        }
        let bal = self.cell_balance(&src);
        if bal >= 1_000 {
            let outcome = self.commit_transfer(src, dst, 1_000);
            self.say(format!(
                "COMPOSE: dropped {} → {}: transfer 1,000 {} (height {}).",
                id_short(&src),
                id_short(&dst),
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            ));
        } else {
            let slot = self.cell_cap_count(&src) as u32 + 1;
            let turn = {
                let w = self.world.borrow();
                w.turn(src, vec![grant_capability(src, src, dst, slot)])
            };
            let outcome = self.world.borrow_mut().commit_turn(turn);
            self.say(format!(
                "COMPOSE: dropped {} → {}: grant cap @{} {} (height {}).",
                id_short(&src),
                id_short(&dst),
                slot,
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            ));
        }
    }

    // ── Window arrangement (pure layout actuation — NO verified turn) ────────────
    // The NT "Window" menu's Cascade / Tile / Close-All commands. Each only moves or
    // drops open windows and re-persists their geometry to the sidecar — view-state
    // only, the same persistence path a manual drag uses.

    /// **Cascade** every open (non-minimized) window from the top-left, staggered, and
    /// re-persist their geometry. Restores minimized windows so the cascade is whole.
    fn cascade_windows(&mut self) {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| self.windows[k].z);
        for (i, key) in keys.iter().enumerate() {
            let off = i as f32 * 28.0;
            if let Some(ws) = self.windows.get_mut(key) {
                ws.x = 300.0 + off;
                ws.y = MENUBAR_H + 12.0 + off;
                ws.minimized = false;
                ws.z = self.next_z;
                self.next_z += 1;
            }
            self.persist_window(*key);
        }
        self.say(format!("Cascaded {} window(s).", keys.len()));
    }

    /// **Tile** every open window into a near-square grid filling the desktop below
    /// the menu bar, and re-persist. A pure layout actuation.
    fn tile_windows(&mut self) {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| self.windows[k].z);
        let n = keys.len().max(1);
        let cols = (n as f32).sqrt().ceil() as usize;
        let rows = n.div_ceil(cols);
        // Tile across the room, reserving the left icon column (~232px) and the
        // top-right World-summary widget (~300px), and the chrome margins — below the
        // menu bar, above the taskbar + status bar (46px) — so no window tucks under
        // the system chrome. Sized to the ACTUAL viewport (captured each render) so a
        // high-res bake fills the whole frame, not a hardcoded 1600×1000 corner.
        let (vw, vh) = self.last_viewport;
        let gap = 10.0;
        let area_x = 232.0;
        let area_y = MENUBAR_H + gap;
        let right_reserve = 300.0;
        let area_w = (vw - area_x - right_reserve - gap).max(WIN_MIN_W);
        let area_h = (vh - area_y - 46.0 - gap).max(WIN_MIN_H);
        let cw = (area_w / cols as f32).max(WIN_MIN_W);
        let ch = (area_h / rows as f32).max(WIN_MIN_H);
        for (i, key) in keys.iter().enumerate() {
            let col = (i % cols) as f32;
            let row = (i / cols) as f32;
            if let Some(ws) = self.windows.get_mut(key) {
                ws.x = area_x + col * cw;
                ws.y = area_y + row * ch;
                ws.w = (cw - gap).max(WIN_MIN_W);
                ws.h = (ch - gap).max(WIN_MIN_H);
                ws.minimized = false;
            }
            self.persist_window(*key);
        }
        self.say(format!("Tiled {n} window(s) in a {cols}×{rows} grid."));
    }

    /// **Close all** open windows (and drop their persisted geometry).
    fn close_all_windows(&mut self) {
        let keys: Vec<WinKey> = self.windows.keys().copied().collect();
        let n = keys.len();
        for key in keys {
            self.close_window(key);
        }
        self.say(format!("Closed {n} window(s)."));
    }

    /// Focus (raise + un-minimize) a window — what a taskbar-stub click does.
    fn focus_window(&mut self, key: WinKey) {
        if let Some(ws) = self.windows.get_mut(&key) {
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
            self.persist_window(key);
        }
    }

    // ── Global mouse handling for the in-flight drag ─────────────────────────────

    fn on_mouse_move(&mut self, ev: &MouseMoveEvent, cx: &mut Context<Self>) {
        let Some(drag) = &self.drag else { return };
        match drag {
            Drag::Icon { cell, grab } => {
                let cell = *cell;
                let nx = pxf(ev.position.x - grab.x).max(0.0);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                self.layout.set_icon_pos(&id_hex(&cell), nx, ny);
                cx.notify();
            }
            Drag::WinMove { key, grab } => {
                let key = *key;
                let nx = pxf(ev.position.x - grab.x);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                if let Some(ws) = self.windows.get_mut(&key) {
                    ws.x = nx;
                    ws.y = ny;
                }
                cx.notify();
            }
            Drag::WinResize { key, origin } => {
                let key = *key;
                let nw = pxf(ev.position.x - origin.x).max(WIN_MIN_W);
                let nh = pxf(ev.position.y - origin.y).max(WIN_MIN_H);
                if let Some(ws) = self.windows.get_mut(&key) {
                    ws.w = nw;
                    ws.h = nh;
                }
                cx.notify();
            }
            Drag::Rewind => {
                // Scrub the Rewind Rail: map x → a history step and re-plant the
                // cursor; the root-verified projection rebuilds (memoized) at the
                // top of the next render pass (`rewind_refresh`).
                self.rewind.cursor = Some(rewind::step_at_x(
                    pxf(ev.position.x),
                    self.last_viewport.0,
                    self.world.borrow().recorded_turns().len(),
                ));
                cx.notify();
            }
        }
    }

    fn on_mouse_up(&mut self, ev: &MouseUpEvent, cx: &mut Context<Self>) {
        let Some(drag) = self.drag.take() else { return };
        match drag {
            Drag::Icon { cell, .. } => {
                // Persist the new icon position (the spatial-persistence write).
                self.saver.save(&self.layout);
                // COMPOSE: if released over an OPEN DOCUMENT window, transclude the
                // cell into it. Else if over ANOTHER cell-icon, act across them.
                if let Some(into) = self.doc_window_under(ev.position) {
                    if into != cell {
                        self.transclude_into(cell, into);
                    }
                } else if let Some(dst) = self.icon_under(ev.position, Some(cell)) {
                    self.compose_drop(cell, dst);
                }
            }
            Drag::WinMove { key, .. } | Drag::WinResize { key, .. } => {
                self.persist_window(key);
            }
            // Releasing the rail scrubber plants the cursor where it sits —
            // nothing to persist (a rewind is a session gesture, not layout).
            Drag::Rewind => {}
        }
        cx.notify();
    }

    /// Which OPEN document window (if any) sits under `p` — the drop target for the
    /// drag-to-transclude compose gesture.
    fn doc_window_under(&self, p: Point<Pixels>) -> Option<CellId> {
        let mut best: Option<(u32, CellId)> = None;
        for ((cell, tag), ws) in self.windows.iter() {
            if *tag != WinKindTag::DocEditor || ws.minimized {
                continue;
            }
            let within = p.x >= px(ws.x)
                && p.x <= px(ws.x + ws.w)
                && p.y >= px(ws.y)
                && p.y <= px(ws.y + ws.h);
            if within && best.map(|(z, _)| ws.z > z).unwrap_or(true) {
                best = Some((ws.z, *cell));
            }
        }
        best.map(|(_, c)| c)
    }

    /// Which cell-icon (other than `exclude`) sits under `p` — used by the compose
    /// drop to find the drop target.
    fn icon_under(&self, p: Point<Pixels>, exclude: Option<CellId>) -> Option<CellId> {
        for (idx, cell) in self.cells.iter().enumerate() {
            if Some(*cell) == exclude {
                continue;
            }
            let pos = self.icon_pos(idx, cell);
            let within_x = p.x >= pos.x && p.x <= pos.x + px(ICON_W);
            let within_y = p.y >= pos.y && p.y <= pos.y + px(ICON_H);
            if within_x && within_y {
                return Some(*cell);
            }
        }
        None
    }

    // ── Bake / test hooks (drive the live gestures headlessly) ───────────────────
    // These mirror exactly what the interactive mouse handlers do, so a headless
    // bake (or a test) can open windows, fire an actuation, and persist a drag —
    // and assert the real verified turn landed and the layout saved.

    /// Open an inspector window on `cell` (what a double-click does).
    pub fn bake_open_window(&mut self, cell: CellId) {
        self.open_window(cell);
    }

    /// Fire a transfer actuation `src → dst` of `amount` (what the right-click
    /// "Transfer" menu action does) — a REAL verified turn on the live World.
    pub fn bake_actuate_transfer(&mut self, src: CellId, _dst: CellId, amount: u64) {
        self.actuate(src, &ActionKind::Transfer { amount });
    }

    /// Move `cell`'s icon to `(x, y)` and persist the layout (what a drag-end does).
    pub fn bake_drag_icon(&mut self, cell: CellId, x: f32, y: f32) {
        self.layout.set_icon_pos(&id_hex(&cell), x, y);
        self.layout.save(&self.layout_path);
    }

    /// Open the right-click context menu on `cell` at `(x, y)` (the ACTUATION
    /// surface) so it is visible in a bake.
    pub fn bake_open_menu(&mut self, cell: CellId, x: f32, y: f32) {
        self.open_menu = Some(OpenMenu {
            cell: Some(cell),
            heading: format!("{} · {}", self.cell_kind(&cell), id_short(&cell)),
            at: Point::new(px(x), px(y)),
            actions: self.actions_for(cell),
        });
    }

    /// Open a DOCUMENT EDITOR window on `cell` (what "Open as Document" does).
    pub fn bake_open_doc(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::DocEditor);
    }

    /// Close `cell`'s document editor window (what the titlebar ✕ does) — drops the
    /// live `InputState` entity + its `Change` subscription, so a reopen re-seeds the
    /// widget FROM THE COMMITTED CELL HEAP (not a stale in-memory buffer). A bake/test
    /// hook over `close_window`, for proving the document IS the cell.
    pub fn bake_close_doc(&mut self, cell: CellId) {
        self.close_window((cell, WinKindTag::DocEditor));
    }

    /// Type `text` into `cell`'s document editor — a receipted patch + a verified
    /// SetField revision turn (what the live editor's keystrokes do).
    pub fn bake_edit_doc(&mut self, cell: CellId, text: &str) {
        if !self.windows.contains_key(&(cell, WinKindTag::DocEditor)) {
            self.open_kind(cell, WinKindTag::DocEditor);
        }
        self.edit_doc(cell, text.to_string());
        // The live editor widget re-seeds from the buffer on next render (this bake
        // hook has no `&mut Window` to push into `InputState` directly).
        self.doc_resync.insert(cell);
    }

    /// COMPOSE: transclude `src` into the open document on `into` (a receipted patch
    /// + verified turn) — what dragging a cell-icon onto a document does.
    pub fn bake_transclude(&mut self, src: CellId, into: CellId) {
        self.transclude_into(src, into);
    }

    /// Open the LINKS / BACKLINKS window on `cell` (what "Links & Backlinks" does).
    pub fn bake_open_links(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Links);
    }

    /// Open the TRANSCRIPT / receipt-log window (what "Transcript" does).
    pub fn bake_open_transcript(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Transcript);
    }

    /// Open the PROPERTY inspector/editor over `cell` (what "Properties…" does).
    pub fn bake_open_properties(&mut self, cell: CellId) {
        self.open_properties(PropSubject::Cell(cell));
    }

    /// How many windows of `tag` are open (a bake/test assertion hook).
    pub fn bake_window_count(&self, kind_is_doc: bool) -> usize {
        let want = if kind_is_doc {
            WinKindTag::DocEditor
        } else {
            WinKindTag::Inspector
        };
        self.windows.keys().filter(|(_, t)| *t == want).count()
    }

    /// The current edit-buffer text of `cell`'s open document (a bake/test hook).
    pub fn bake_doc_text(&self, cell: CellId) -> String {
        self.load_doc_buffer(cell)
    }

    // ── Branch / stitch / conflict bake+test hooks (the document-language surface) ──

    /// Fork a confined co-author draft branch of `cell`'s document (the Fork button).
    pub fn bake_fork_branch(&mut self, cell: CellId) {
        self.fork_doc_branch(cell);
    }

    /// Author a divergent edit on `cell`'s draft branch (the Diverge button), so a
    /// stitch yields a genuine prose conflict at the shared region.
    pub fn bake_diverge_branch(&mut self, cell: CellId, append: &str) {
        self.diverge_branch(cell, append);
    }

    /// Set the WHOLE text of `cell`'s confined draft as the co-author (the live branch
    /// editor's typing path), so a bake can drive the divergence by content (not the
    /// canned append). The branch is confined — nothing commits to the heap.
    pub fn bake_set_branch_text(&mut self, cell: CellId, text: &str) {
        self.set_branch_text(cell, text);
    }

    /// The document's LIVE committed umem-heap boundary commitment (the cell's
    /// resealed `heap_root` off the ledger) — the sorted-Poseidon2 boundary a light
    /// client trusts, which IS the document's commitment. A bake/test hook to assert
    /// the committed boundary MOVES as the document is edited/resolved and survives
    /// reopen (it reads the cell, not the window, so it holds after the editor closes).
    pub fn bake_doc_umem_boundary(&self, cell: CellId) -> Option<[u8; 32]> {
        self.live_doc_boundary(&cell)
    }

    /// The most recent resolution receipt for `cell` (the committed resolution patch's
    /// content-addressed id), if any — a bake/test hook proving a resolution lands a
    /// real, identified turn.
    pub fn bake_last_resolution_receipt(&self, cell: CellId) -> Option<u128> {
        self.last_resolution
            .as_ref()
            .filter(|(c, _, _)| *c == cell)
            .map(|(_, _, pid)| pid.0)
    }

    /// Place + size `cell`'s document-editor window (a bake-layout hook) so the focused
    /// document-collaboration shot renders the whole surface un-clipped.
    pub fn bake_place_doc_window(&mut self, cell: CellId, x: f32, y: f32, w: f32, h: f32) {
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            ws.x = x;
            ws.y = y;
            ws.w = w;
            ws.h = h;
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
        }
    }

    /// Stitch `cell`'s draft branch into the document (the pushout) — a clean merge
    /// folds to heap; a contested region becomes a first-class conflict state.
    pub fn bake_stitch_branch(&mut self, cell: CellId) {
        self.stitch_branch(cell);
    }

    /// How many unresolved first-class CONFLICT regions `cell`'s stitched document
    /// currently carries (`None` if no stitch is pending). A bake/test assertion hook.
    pub fn bake_conflict_count(&self, cell: CellId) -> Option<usize> {
        self.doc_merged_conflict_count(cell)
    }

    /// Resolve conflict region `region_idx` of `cell`'s stitched document with choice
    /// `choice_idx` (a one-click `ResolutionChoice` patch). A bake/test hook.
    pub fn bake_resolve_conflict(&mut self, cell: CellId, region_idx: usize, choice_idx: usize) {
        self.resolve_conflict(cell, region_idx, choice_idx);
        self.doc_resync.insert(cell);
    }

    // ── Document Explorer bake+test hooks (the Pharo-moldable patch inspector) ──

    /// Open the Document Explorer window on `cell` (the Explore Document… action).
    pub fn bake_open_doc_explorer(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::DocExplorer);
    }

    /// Select the explorer's face (0=History, 1=Graph, 2=Blame) — the tab gesture.
    pub fn bake_doc_explorer_tab(&mut self, cell: CellId, tab: usize) {
        let t = match tab {
            1 => DocExplorerTab::Patches,
            2 => DocExplorerTab::Graph,
            3 => DocExplorerTab::Blame,
            _ => DocExplorerTab::History,
        };
        self.doc_explorers.entry(cell).or_default().tab = t;
    }

    /// Scrub the History face to revision `rev` (`None` = tip) — the time-travel cursor.
    pub fn bake_doc_explorer_scrub(&mut self, cell: CellId, rev: Option<usize>) {
        self.doc_explorers.entry(cell).or_default().scrub = rev;
    }

    /// The document AT the scrubbed revision (replayed via `replay_to`), or the tip's
    /// text. A bake/test hook proving the time-travel scrubber reads real history.
    pub fn bake_doc_explorer_at(&self, cell: CellId, rev: Option<usize>) -> Option<String> {
        let doc = self.doc_for_explorer(cell)?;
        let patches = doc.history().patches();
        Some(match rev {
            Some(i) if i < patches.len() => {
                content(&doc.history().replay_to(patches[i].id())).to_marked_string()
            }
            _ => doc.text(),
        })
    }

    /// How many atoms / how many distinct authors `cell`'s document graph carries — a
    /// bake/test assertion hook over the live DocGraph + blame faces.
    pub fn bake_doc_explorer_stats(&self, cell: CellId) -> Option<(usize, usize)> {
        let doc = self.doc_for_explorer(cell)?;
        let graph = doc.history().replay();
        let atoms = graph.atoms().count();
        let authors = blame_summary(&graph).len();
        Some((atoms, authors))
    }

    // ── World Explorer + Spotter bake/test hooks ──

    /// Open the World Explorer window (anchored on the user cell). A bake/test hook.
    pub fn bake_open_world_explorer(&mut self) {
        self.open_kind(self.user, WinKindTag::WorldExplorer);
    }

    /// Select the World Explorer face (0=Ledger, 1=Chronicle, 2=Conservation).
    pub fn bake_world_explorer_tab(&mut self, tab: usize) {
        use world_explorer::WorldExplorerTab as T;
        let t = match tab {
            1 => T::Chronicle,
            2 => T::Conservation,
            _ => T::Ledger,
        };
        self.world_explorers.entry(self.user).or_default().tab = t;
    }

    /// Open the AGENT ROOM window (anchored on its own sentinel) — a bake/test hook.
    pub fn bake_open_agent_room(&mut self) {
        self.open_agent_room();
    }

    /// The resident the open Agent Room is watching (the pinned one, else the
    /// default-resident projection) — a bake/test hook.
    pub fn bake_agent_room_resident(&self) -> CellId {
        let key = agent_room::agent_room_window_cell();
        self.agent_rooms
            .get(&key)
            .and_then(|s| s.resident)
            .unwrap_or_else(|| agent_room::default_resident(&self.world.borrow(), self.user))
    }

    /// How many receipted actions the watched resident's activity carries — a
    /// bake/test hook (the room's Actions face row count, before capping).
    pub fn bake_agent_room_action_count(&self) -> usize {
        let resident = self.bake_agent_room_resident();
        crate::agent::AgentActivity::build(&self.world.borrow(), resident, 24)
            .actions
            .len()
    }

    // ── Mail Room bake/test hooks ──

    /// Open the MAIL ROOM window (anchored on its own sentinel; ensures the operator's
    /// office + the town ferry) — a bake/test hook.
    pub fn bake_open_mail_room(&mut self) {
        self.open_mail_room();
    }

    /// **Post a letter** from the operator to `to` as a real send turn — a bake/test hook
    /// (the SAME [`crate::letter_office::send_letter`] the compose strip drives). Returns
    /// the born letter cell id on success.
    pub fn bake_mail_send(&mut self, to: CellId, subject: &str, body: &str) -> Option<CellId> {
        let from = self.user;
        let mut w = self.world.borrow_mut();
        crate::letter_office::send_letter(&mut w, from, to, subject, body)
            .ok()
            .map(|r| r.letter)
    }

    /// **Deliver a letter now** as a real ferry turn — a bake/test hook (the SAME
    /// [`crate::letter_office::deliver_now`] the *deliver now* button drives). Returns
    /// whether the delivery committed.
    pub fn bake_mail_deliver(&mut self, letter: CellId) -> bool {
        let mut w = self.world.borrow_mut();
        crate::letter_office::deliver_now(&mut w, letter).is_ok()
    }

    /// How many letters have landed in `owner`'s inbox on the live World — a bake/test
    /// hook (the Inbox face's row count).
    pub fn bake_mail_inbox_count(&self, owner: CellId) -> usize {
        crate::letter_office::mailbox_of(&self.world.borrow(), owner)
            .inbox
            .len()
    }

    /// How many letters exist town-wide (every letter is a cell) — a bake/test hook (the
    /// Mail-Ledger face's row count).
    pub fn bake_mail_town_count(&self) -> usize {
        crate::letter_office::town_letters(&self.world.borrow()).len()
    }

    // ── Provenance Walker bake/test hooks ──

    /// Open the PROVENANCE WALKER window (anchored on its own sentinel) — a
    /// bake/test hook.
    pub fn bake_open_provenance_walker(&mut self) {
        self.open_provenance_walker();
    }

    /// **Does the receipt chain VERIFY to depth `n`?** Re-derives every link of
    /// the live World's receipt log ([`provenance_walker::walk_rows`]: the
    /// state-root handoff between consecutive receipts + each agent's blocklace
    /// back-edge, blake3-recomputed) and demands the newest `n` receipts' links
    /// all check out ([`provenance_walker::chain_verifies_to_depth`]) — with
    /// out-of-band genesis boundaries named off the recorded History
    /// ([`provenance_walker::reseeded_flags`]), exactly as the window paints
    /// them. The bake's tooth on "the chain on screen is a chain, not a list".
    pub fn bake_walk_verify(&self, n: usize) -> bool {
        let w = self.world.borrow();
        let flags = provenance_walker::reseeded_flags(w.recorded_turns());
        provenance_walker::chain_verifies_to_depth(w.receipts(), &flags, n)
    }

    /// **Walk one back-edge** — step the open walker's cursor from the selected
    /// receipt (the chain head when none is pinned) to its author's previous
    /// receipt, exactly as the window's "← walk to prev" verb does. Returns the
    /// landing receipt's full hex, or `None` at a chain head (nothing before
    /// it). A bake/test hook: drives the WALK headlessly.
    pub fn bake_walker_walk_back(&mut self) -> Option<String> {
        let cell = provenance_walker::walker_window_cell();
        let prev = {
            let w = self.world.borrow();
            let cur = self
                .provenance_walkers
                .get(&cell)
                .and_then(|s| s.selected)
                .or_else(|| w.receipts().last().map(|r| r.receipt_hash()))?;
            crate::provenance_navigator::turn_detail(&w, &cur)?.previous_receipt?
        };
        let st = self.provenance_walkers.entry(cell).or_default();
        st.selected = Some(prev);
        st.landed = None;
        Some(prev.iter().map(|b| format!("{b:02x}")).collect())
    }

    /// The open walker's selected receipt (the walk cursor), as full hex — the
    /// chain head when none is pinned yet. `None` on an empty chronicle. A
    /// bake/test hook (pairs with [`Self::bake_walker_walk_back`]).
    pub fn bake_walker_selected(&self) -> Option<String> {
        let cell = provenance_walker::walker_window_cell();
        let w = self.world.borrow();
        let cur = self
            .provenance_walkers
            .get(&cell)
            .and_then(|s| s.selected)
            .or_else(|| w.receipts().last().map(|r| r.receipt_hash()))?;
        Some(cur.iter().map(|b| format!("{b:02x}")).collect())
    }

    // ── Content-IR pane bake/test hooks (gated on `card-pane`) ──

    /// Open the content-IR pane window (anchored on the user cell) — a desktop window
    /// whose body is a real `deos_view::ViewNode` rendered through deos-view's native
    /// renderer. A bake/test hook. The renderer entity is minted on the next render.
    #[cfg(feature = "card-pane")]
    pub fn bake_open_viewnode_pane(&mut self) {
        self.open_kind(self.user, WinKindTag::ViewNodePane);
    }

    /// Whether the content-IR renderer entity has been minted for the user's pane —
    /// i.e. the desktop window's body IS a rendered portable `ViewNode`. True only
    /// after the window has rendered at least once (the entity is created lazily).
    #[cfg(feature = "card-pane")]
    pub fn bake_viewnode_has_pane(&self) -> bool {
        self.viewnode_panes.contains_key(&self.user)
    }

    /// Place + raise the World-Status pane window in a clear area (a bake hook) so its
    /// body is visible + unoccluded when the bake captures the before/after frames.
    #[cfg(feature = "card-pane")]
    pub fn bake_place_viewnode_window(&mut self, x: f32, y: f32, w: f32, h: f32) {
        let key = (self.user, WinKindTag::ViewNodePane);
        if let Some(ws) = self.windows.get_mut(&key) {
            ws.x = x;
            ws.y = y;
            ws.w = w;
            ws.h = h;
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
        }
    }

    /// Place + raise the `ViewNodePane` window keyed on `cell` in a clear area (a bake
    /// hook) — the cell-addressed sibling of [`Self::bake_place_viewnode_window`], used to
    /// surface the agent-composed World Board window for the after-capture.
    #[cfg(feature = "card-pane")]
    pub fn bake_place_window(&mut self, cell: CellId, x: f32, y: f32, w: f32, h: f32) {
        let key = (cell, WinKindTag::ViewNodePane);
        if let Some(ws) = self.windows.get_mut(&key) {
            ws.x = x;
            ws.y = y;
            ws.w = w;
            ws.h = h;
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
        }
    }

    /// **THE REFLECTIVE-COCKPIT LOOP, IN THE SHIPPED DESKTOP** — a confined agent
    /// reflects-on then rewrites the World-Status pane in the REAL desktop window.
    ///
    /// The next rung of `0c3e567b` (which proved the loop over a headless deos-view
    /// render): here it runs against the SHIPPED `viewnode_pane` window. We (1) ensure
    /// the live [`deos_view::AppletView`] entity exists, (2) REFLECT-ON its current
    /// view-tree (the host read; the agent's JS reads the same tree via
    /// `deos.editor.view()`), (3) run the agent's reflect-then-rewrite JS through the
    /// proven `CardEditor` machinery (receipted patches, blamed on the agent, cap-toothed),
    /// and (4) SWAP the re-folded tree into the SAME live entity ([`AppletView::set_tree`])
    /// + `notify` — so the real desktop window repaints the agent's rewrite on the next
    ///   frame (a `refresh` button + the `World Status (live)` relabel reach the glass).
    ///
    /// Returns the loop's witnesses (reflect counts, receipt count, blame, before/after
    /// button presence) so a bake can assert the agent rewrote a real cockpit surface.
    #[cfg(feature = "card-pane")]
    pub fn bake_agent_rewrites_viewnode_pane(
        &mut self,
        rt: &mut deos_js::JsRuntime,
        cx: &mut Context<Self>,
    ) -> Result<ViewnodeRewrite, String> {
        let cell = self.user;

        // (1) Ensure the live renderer entity exists (created lazily on render; mint it
        //     here so the bake can reflect-on it before the next paint).
        let entity = match self.viewnode_panes.get(&cell).cloned() {
            Some(e) => e,
            None => {
                let e = viewnode_pane::build_viewnode_view(cx);
                self.viewnode_panes.insert(cell, e.clone());
                e
            }
        };

        // (2) REFLECT-ON — read the live surface's OWN view-tree off the entity the
        //     desktop window paints (the host read; the agent's JS reads the same tree).
        let before_tree = entity.read(cx).tree().clone();
        let (reflected_header, reflected_rows) = viewnode_pane::reflect_status(&before_tree);
        let before_has_button = viewnode_pane::tree_has_refresh_button(&before_tree);

        // (3) REWRITE — run the agent's reflect-then-rewrite JS through the proven
        //     `CardEditor` machinery (receipted, blamed, cap-toothed).
        let rw = viewnode_pane::agent_rewrite_status_panel(rt)?;

        // (4) THE LIVE SURFACE RE-RENDERS — swap the re-folded tree into the SAME entity
        //     the desktop window hosts, and notify so the real window repaints it.
        let after_tree = rw.after_tree.clone();
        entity.update(cx, |view, cx| {
            view.set_tree(after_tree);
            cx.notify();
        });
        // The LIVE entity's tree now carries the agent's rewrite (the surface in the real
        // window IS the rewritten one).
        let live_after_has_button = viewnode_pane::tree_has_refresh_button(entity.read(cx).tree());

        Ok(ViewnodeRewrite {
            reflected_header,
            reflected_rows,
            before_has_button,
            after_has_button: rw.after_has_button,
            live_after_has_button,
            receipt_count: rw.receipt_count,
            blamed_agent: rw.blamed_agent,
        })
    }

    /// **THE AGENT AS CO-AUTHOR — compose a brand-new cockpit surface from scratch.**
    ///
    /// The deeper rung past [`Self::bake_agent_rewrites_viewnode_pane`] (which rewrites one
    /// pre-existing surface): here a confined agent COMPOSES a NEW surface — a World Board —
    /// from an EMPTY root, informed by reading the live World, and the board is mounted as a
    /// REAL second `viewnode_pane` window in the shipped desktop. The agent stops being an
    /// editor of the cockpit and becomes a co-author OF it:
    ///
    ///   1. The host reads its live World (cell count · receipts · conservation Σ) and
    ///      seeds a fresh, EMPTY board card with those stats (its `bind` rows surface them).
    ///   2. The agent's JS runs through the proven `CardEditor` machinery WITH a live-World
    ///      crawl target attached: it REFLECTS-ON its own empty surface, CRAWLS the real
    ///      ledger (`deos.world.cells()`) to decide what to surface, then COMPOSES from the
    ///      empty root — a title + 3 live state-bound rows (`addBind`) + a `refresh` button —
    ///      each a receipted patch blamed on the agent, cap-toothed.
    ///   3. The composed tree is painted by the SAME native renderer into a NEW desktop
    ///      window (a distinct `ViewNodePane`): the agent ADDED a cockpit surface.
    ///
    /// Returns the loop's witnesses (started-empty · crawled cell count · composed nodes ·
    /// receipts · blame · the mounted window) so a bake can assert the agent co-authored a
    /// real new cockpit surface.
    #[cfg(feature = "card-pane")]
    pub fn bake_agent_composes_world_board(
        &mut self,
        rt: &mut deos_js::JsRuntime,
        cx: &mut Context<Self>,
    ) -> Result<WorldBoardComposition, String> {
        use crate::agent_attach::{attach_agent, WorldSinkAdapter};

        // (1) READ THE LIVE WORLD (host side) — the real stats the board will surface. The
        //     ledger count is what the agent's crawl will independently report.
        let cells = self.world.borrow().ledger().iter().count() as u64;
        let receipts = self.world.borrow().receipts().len() as u64;
        let sum = self.world_balance_sum().max(0) as u64;

        // (2) A fresh, EMPTY board card seeded with those live stats (the agent composes
        //     every node; its `bind` rows re-read these slots). Confirm it begins bare —
        //     the agent composes from nothing, not by tweaking a pre-existing pane.
        let editor = viewnode_pane::world_board_editor(cells, receipts, sum);
        let started_empty = editor
            .view_tree()
            .map(|t| t.children().is_empty())
            .unwrap_or(false);

        // (3) The agent ALSO crawls the live World directly — attach a witnessed-read crawl
        //     target over the live ledger under the user cell's Signature (a read confers
        //     no authority; the empty affordance surface means it cannot mutate via it).
        let sink = WorldSinkAdapter::live(self.world.clone());
        let applet = attach_agent(sink, self.user, dregg_cell::AuthRequired::Signature, vec![]);
        let target = deos_js::JsTarget::Attached(applet);

        // (4) COMPOSE — run the agent's reflect→read→compose JS through the proven machinery
        //     on the shared process-global runtime (the same `rt` that drove the rewrite).
        let (result, editor, _target) =
            rt.run_authoring_with_crawl(editor, target, viewnode_pane::WORLD_BOARD_COMPOSE_JS)?;
        let crawled = result.unwrap_or(0);
        if crawled < 1 {
            return Err(format!(
                "the agent's compose-from-scratch run did not complete (returned {result:?})"
            ));
        }

        let after_source = editor.view_source();
        let after_tree = deos_view::parse_view_tree(&after_source)?;
        let composed_title = viewnode_pane::tree_has_board_title(&after_tree);
        let composed_bind_rows = viewnode_pane::count_bind_rows(&after_tree);
        let composed_button = viewnode_pane::tree_has_refresh_button(&after_tree);
        let receipt_count = editor.card().receipt_count();
        let blamed_agent = editor
            .view_blame()
            .iter()
            .any(|l| l.author == viewnode_pane::AGENT_AUTHOR);

        // (5) MOUNT — paint the agent's composed tree into a NEW desktop window (a distinct
        //     ViewNodePane keyed on the board cell). Pre-insert the entity so the window's
        //     render hosts the agent's board (not the default World-Status panel).
        let board_cell = viewnode_pane::world_board_window_cell();
        let entity = viewnode_pane::build_board_view(cx, cells, receipts, sum, after_tree.clone());
        self.viewnode_panes.insert(board_cell, entity);
        self.open_kind(board_cell, WinKindTag::ViewNodePane);
        if let Some(ws) = self
            .windows
            .get_mut(&(board_cell, WinKindTag::ViewNodePane))
        {
            ws.title = "World Board — composed by the agent · deos_view::ViewNode".to_string();
        }
        let mounted_window = self
            .windows
            .contains_key(&(board_cell, WinKindTag::ViewNodePane))
            && self.viewnode_panes.contains_key(&board_cell);

        self.say(format!(
            "The agent COMPOSED a new cockpit surface — a World Board (cells {cells} · \
             receipts {receipts}) — from scratch, mounted as a live window."
        ));

        Ok(WorldBoardComposition {
            started_empty,
            crawled_cells: crawled as usize,
            composed_title,
            composed_bind_rows,
            composed_button,
            receipt_count,
            blamed_agent,
            mounted_window,
        })
    }

    /// **THE PULSE→SIGNALS WELD, PROVEN** — a FOREIGN turn (committed on the live
    /// World: outside the pane, not one of its own affordances) repaints EXACTLY the
    /// shipped World-Status pane's receipts bind, through a receipted tracking turn,
    /// with the one-beat dirty glow lit.
    ///
    /// The loop: (1) ensure the live pane entity exists; (2) CONVERGE — drive a loud
    /// pulse beat so the pane's committed readings catch the live census (the frozen
    /// 3/12 seeds stop lying; in the shipped desktop the first 250ms beat after open
    /// does this); (3) THE FOREIGN TURN — commit a real verified `SetField` turn on
    /// the live World: the receipts census moves by exactly one, the cells census does
    /// not, and the turn's `FieldSet` event rides the next beat's broadcast (proving a
    /// foreign write never over-invalidates a pane whose binds don't read it);
    /// (4) THE PROOF BEAT — one more [`Self::pump_dynamics`] beat: the pane fires ONE
    /// receipted `set_receipts` tracking turn, its dirty set is EXACTLY the receipts
    /// bind (cells + refreshes rows stay clean), the glow is lit, and the bind's
    /// committed value equals the live census. A capture before/after this call
    /// differs — the repainted value + the accent glow reach pixels.
    #[cfg(feature = "card-pane")]
    pub fn bake_foreign_turn_repaints_viewnode_binds(
        &mut self,
        cx: &mut Context<Self>,
    ) -> Result<viewnode_pane::PulseWeldWitness, String> {
        let cell = self.user;

        // (1) The live renderer entity (created lazily on render; mint it here so the
        //     weld can drive it even before the window's next paint).
        let entity = match self.viewnode_panes.get(&cell).cloned() {
            Some(e) => e,
            None => {
                let e = viewnode_pane::build_viewnode_view(cx);
                self.viewnode_panes.insert(cell, e.clone());
                e
            }
        };
        let applet = entity.read(cx).applet();

        // (2) CONVERGE — drive one beat; if the dynamics stream was already drained
        //     (the beat stays quiet and the census weld never ran), nudge the World
        //     with one real turn so the next beat is loud, and converge on that.
        self.pump_dynamics(cx);
        {
            let live = self.world.borrow().receipts().len() as u64;
            let shown = applet.borrow().get_u64(viewnode_pane::STATUS_SLOT_RECEIPTS);
            if shown != live && !self.commit_set_field(cell, 9, 7) {
                return Err("the convergence nudge turn did not commit".into());
            }
        }
        self.pump_dynamics(cx);
        let receipts_before = applet.borrow().get_u64(viewnode_pane::STATUS_SLOT_RECEIPTS);
        {
            let live = self.world.borrow().receipts().len() as u64;
            if receipts_before != live {
                return Err(format!(
                    "the convergence beat did not land: the pane's committed receipts \
                     reading is {receipts_before}, the live census {live}"
                ));
            }
        }
        let pane_tape_before = applet.borrow().receipt_count();

        // (3) THE FOREIGN TURN — a real verified `SetField` on the live World. The
        //     receipts census moves by one; the cells census does not.
        if !self.commit_set_field(cell, 9, 42) {
            return Err("the foreign SetField turn did not commit".into());
        }
        let live_receipts = self.world.borrow().receipts().len() as u64;

        // (4) THE PROOF BEAT — the pulse mirrors the moved receipts census into the
        //     pane as ONE receipted tracking turn and invalidates EXACTLY its bind.
        self.pump_dynamics(cx);

        let view = entity.read(cx);
        let receipts_after = applet.borrow().get_u64(viewnode_pane::STATUS_SLOT_RECEIPTS);
        let dirty = viewnode_pane::raw_ids(&view.last_dirty());
        let glowing = viewnode_pane::raw_ids(&view.glowing());
        let expected = viewnode_pane::bindings_reading(view, viewnode_pane::STATUS_SLOT_RECEIPTS);
        let dirty_is_exactly_receipts_bind =
            !expected.is_empty() && dirty == expected && glowing == expected;
        let weld_receipts_committed = applet
            .borrow()
            .receipt_count()
            .saturating_sub(pane_tape_before);

        self.say(format!(
            "THE PULSE→SIGNALS WELD — a foreign turn moved the World's receipts census \
             to {live_receipts}; the World-Status pane repainted exactly its receipts \
             bind (a receipted tracking turn; dirty glow lit)."
        ));

        Ok(viewnode_pane::PulseWeldWitness {
            receipts_before,
            receipts_after,
            live_receipts,
            dirty,
            glowing,
            dirty_is_exactly_receipts_bind,
            weld_receipts_committed,
        })
    }

    /// Open the Spotter overlay with a query — a bake/test hook driving the palette.
    pub fn bake_open_spotter(&mut self, query: &str) {
        self.open_spotter();
        if let Some(ui) = self.spotter.as_mut() {
            ui.query = query.to_string();
        }
    }

    /// How many Spotter candidates the current query ranks (a bake/test hook proving
    /// the fuzzy match runs over the live cells). `None` when the Spotter is closed.
    pub fn bake_spotter_match_count(&self) -> Option<usize> {
        self.spotter.as_ref()?;
        Some(self.spotter_ranked().len())
    }

    /// The label of the Spotter's top-ranked candidate for the live query — a bake/test
    /// hook proving the ranking surfaces a sensible best match.
    pub fn bake_spotter_top_label(&self) -> Option<String> {
        self.spotter.as_ref()?;
        self.spotter_ranked().first().map(|e| e.label.clone())
    }

    /// Dispatch the Spotter's top candidate (what Enter does) — a bake/test hook.
    pub fn bake_spotter_dispatch_top(&mut self) {
        self.spotter_dispatch(Some(0));
    }

    /// Drive one Spotter COMMAND end-to-end — a bake/test hook: open the palette
    /// with `query`, and dispatch the top entry (what typing the sentence + Enter
    /// does). Returns whether the top entry WAS a command (the verb prefix parsed
    /// and its cells resolved); `false` means the query stayed a plain fuzzy jump
    /// — so a bake can assert both that `transfer 500 <hex> <hex>` commits a real
    /// verified turn (the height advances; the status line carries the verdict)
    /// AND that a non-verb query never grows a command on top.
    pub fn bake_spotter_run_command(&mut self, query: &str) -> bool {
        use spotter::SpotterTarget as Tg;
        self.bake_open_spotter(query);
        let was_command = matches!(
            self.spotter_ranked().first().map(|e| e.target.clone()),
            Some(Tg::CmdTransfer { .. } | Tg::CmdGrant { .. } | Tg::CmdBump(_) | Tg::CmdSeal(_))
        );
        self.spotter_dispatch(Some(0));
        was_command
    }

    /// The persisted RECENT-JUMPS trail (newest first, capped at 8) — a bake/test
    /// hook proving dispatches land on it, dedupe, and greet the empty query.
    pub fn bake_spotter_recent_jumps(&self) -> Vec<String> {
        self.layout.prefs.recent_jumps.clone()
    }

    /// The status bar's current line — a bake/test hook (a committed Spotter
    /// command's receipt narration, verdict + height, lands here via `say()`).
    pub fn bake_status_line(&self) -> String {
        self.status.clone()
    }

    /// The World's chronicle height — a bake/test hook (a committed command
    /// advances it; a refused one leaves it be).
    pub fn bake_world_height(&self) -> u64 {
        self.world.borrow().height()
    }

    /// Whether the warm WELCOME card is currently showing (a bake/test hook).
    pub fn bake_welcome_is_shown(&self) -> bool {
        self.show_welcome
    }

    /// Dismiss the warm WELCOME card without stepping through a door — for a focused bake
    /// that wants the bare workbench (e.g. the document-collaboration shot).
    pub fn bake_dismiss_welcome(&mut self) {
        self.dismiss_welcome();
    }

    /// The live, jargon-free welcome greeting for the current world (a bake/test hook) —
    /// the exact sentence the card renders, so a bake can assert it names the real image.
    pub fn bake_welcome_greeting(&self) -> String {
        welcome::greeting(self.cells.len(), self.world.borrow().height())
    }

    /// Step through the welcome card's `n`-th door (0-based: look · find · make · survey)
    /// — a bake/test hook proving a door dispatches its real gesture and dismisses the
    /// card. Returns whether the card is still shown afterward (always `false`).
    pub fn bake_welcome_door(&mut self, n: usize) -> bool {
        if let Some(tile) = welcome::welcome_tiles().get(n) {
            self.welcome_dispatch(tile.action);
        }
        self.show_welcome
    }

    /// The live `InputState` editor entity for `cell`'s open document, if the doc body
    /// has rendered at least once (so `ensure_doc_input` built it). A test hook: lets a
    /// headless test TYPE into the REAL widget (`insert`/`set_value`) and assert the
    /// keystroke→heap seam fires, exercising the genuine `Change` subscription rather
    /// than a bypass.
    pub fn bake_doc_input(&self, cell: CellId) -> Option<Entity<InputState>> {
        self.doc_inputs.get(&cell).cloned()
    }

    /// **Structured link assertion (a bake/test hook)** — does `doc`'s document carry
    /// a transclusion that resolves to `target` (an OUTBOUND link), and does `target`'s
    /// Links view see `doc` as a BACKLINK (← mentions this)? Returns `(outbound, back)`.
    /// Reuses the exact `parse_transclusion_ref` + `Self::backlinks_of` the Links
    /// window renders with, so the assertion tracks the real surface. (The back leg
    /// previously re-parsed the SAME doc's prose — the outbound scan twice under
    /// another name — so the genuine reverse scan was never exercised; it now asks
    /// the observer's question: is `doc` among `target`'s backlinks?)
    pub fn bake_doc_links(&self, doc: CellId, target: CellId) -> (bool, bool) {
        let outbound = self
            .load_doc_buffer(doc)
            .lines()
            .filter_map(parse_transclusion_ref)
            .any(|t| t == target);
        let back = self.backlinks_of(target).contains(&doc);
        (outbound, back)
    }

    /// **Cascade** all open windows (the Window→Cascade command) — a bake/test hook.
    /// Pure layout; fires NO verified turn. Returns the open-window count moved.
    pub fn bake_cascade_windows(&mut self) -> usize {
        let n = self.windows.len();
        self.cascade_windows();
        n
    }

    /// **Tile** all open windows (the Window→Tile command) — a bake/test hook.
    pub fn bake_tile_windows(&mut self) -> usize {
        let n = self.windows.len();
        self.tile_windows();
        n
    }

    /// The total open-window count across ALL kinds (a bake/test assertion hook).
    pub fn bake_total_window_count(&self) -> usize {
        self.windows.len()
    }

    /// The kind-label of the surface the halo selection currently points at (the window
    /// kind's reader-legible name, e.g. "Document", "Android · SystemUI", "World Status").
    /// `None` when nothing or a bare icon is selected. A bake/test hook: proves a Spotter
    /// jump LANDED in the RIGHT surface (not merely that some window opened), and that it
    /// arrived mold-ready (the selection IS the landed window).
    pub fn bake_selected_window_label(&self) -> Option<&'static str> {
        match self.selected {
            Some(HaloTarget::Window(key)) => self.windows.get(&key).map(|ws| ws.kind.label()),
            _ => None,
        }
    }

    /// Whether the open document on `cell` currently carries a forked co-author draft
    /// branch (the live doc-collaboration session). A bake/test hook proving the Spotter's
    /// "Co-author a Document" surface landed a real branch-and-stitch session, not a bare
    /// editor.
    pub fn bake_doc_has_branch(&self, cell: CellId) -> bool {
        matches!(
            self.windows
                .get(&(cell, WinKindTag::DocEditor))
                .map(|ws| &ws.kind),
            Some(WinKind::DocEditor {
                branch: Some(_),
                ..
            })
        )
    }

    /// The World's conservation sum (Σ balance) — a bake/test hook over the live
    /// ledger (the desktop's World-summary widget reflects it; it must read 0).
    pub fn bake_world_balance_sum(&self) -> i64 {
        self.world_balance_sum()
    }
}

// ── Rendering ─────────────────────────────────────────────────────────────────────
// (The `bevel_raised` / `face_section` / `face_row` chrome primitives live in
// `chrome.rs` and are imported above.)

impl Render for DeosDesktop {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Remember the real desktop size so Tile/Cascade fill the ACTUAL room (a
        // high-res bake spreads windows over the whole frame, not a 1600×1000 corner).
        {
            let vp = window.viewport_size();
            self.last_viewport = (f32::from(vp.width), f32::from(vp.height));
        }
        // THE REWIND RAIL's projection refresh — keep the memoized root-verified
        // replay in step with the cursor + the live history BEFORE any surface
        // reads through `with_effective_ledger` this frame (live turns landing
        // while the cursor sits in the past re-diff the glow + lengthen the rail).
        self.rewind_refresh();
        let mut root = div()
            .id("deos-desktop-root")
            .key_context("DeosDesktop")
            .track_focus(&self.focus)
            // THE KEYBOARD SPINE — one dispatcher for every keystroke no focused
            // child consumed (⌘K Spotter · ↑/↓ selection · the Escape ladder).
            .on_key_down(cx.listener(|this, ev: &KeyDownEvent, _w, cx| {
                if this.on_key_model(&ev.keystroke.key, {
                    let m = &ev.keystroke.modifiers;
                    m.platform || m.control
                }) {
                    cx.notify();
                }
            }))
            .size_full()
            .bg(gpui::rgb(self.layout.prefs.bg))
            .text_color(gpui::rgb(NT_TEXT))
            .font_family("Lilex")
            .text_size(px(12.0))
            // Global drag handling (move/up anywhere on the desktop drive the
            // in-flight icon/window drag).
            .on_mouse_move(
                cx.listener(|this, ev: &MouseMoveEvent, _w, cx| this.on_mouse_move(ev, cx)),
            )
            .on_mouse_up(
                MouseButton::Left,
                cx.listener(|this, ev: &MouseUpEvent, _w, cx| this.on_mouse_up(ev, cx)),
            )
            // A left-click on the bare desktop dismisses an open menu/dialog AND
            // clears the halo selection. This parent handler runs BEFORE a child
            // icon/window's own mouse-down (which re-sets the selection), so a click
            // that lands ON a surface still selects it; only a bare-desktop click
            // deselects. (gpui dispatches ancestor handlers first, child last.)
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                    // NOT the spotter: this ancestor handler fires before a spotter
                    // row's own mouse-down, so closing it here would clear the query
                    // state the row's dispatch is about to read. Escape (the keyboard
                    // spine) is the spotter's dismissal.
                    let dirty = this.open_menu.take().is_some() | this.selected.take().is_some();
                    if dirty {
                        cx.notify();
                    }
                }),
            )
            // A right-click on the bare desktop opens the DESKTOP context menu.
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(|this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: None,
                        heading: "Desktop".into(),
                        at: ev.position,
                        actions: this.desktop_actions(),
                    });
                    cx.notify();
                }),
            );

        // ── The menu bar (NT-style) ──────────────────────────────────────────────
        root = root.child(self.render_menubar(cx));

        // ── The desktop icons (cells) ────────────────────────────────────────────
        let cells = self.cells.clone();
        for (idx, cell) in cells.iter().enumerate() {
            // While the Rewind Rail is scrubbed, a cell that does not exist yet
            // at the cursor's height has no icon — the past census is the truth.
            if !self.rewind_cell_present(cell) {
                continue;
            }
            root = root.child(self.render_icon(idx, *cell, cx));
        }

        // ── The World-summary widget (pinned top-right, fills the empty margin) ───
        root = root.child(self.render_world_widget());

        // ── The open windows (z-ordered) ─────────────────────────────────────────
        // The top-z, non-minimized window is the FOCUSED one — it alone wears the
        // active navy title bar (the NT "one focused thing" cue); the rest read
        // inactive-gray so the eye lands on the live surface, not a wall of navy.
        let mut wins: Vec<WinKey> = self.windows.keys().copied().collect();
        wins.sort_by_key(|k| self.windows[k].z);
        let focused: Option<WinKey> = wins
            .iter()
            .filter(|k| !self.windows[*k].minimized)
            .max_by_key(|k| self.windows[*k].z)
            .copied();
        for key in wins {
            let active = Some(key) == focused;
            root = root.child(self.render_window(key, active, window, cx));
        }

        // ── GOSSAMER — the visible transclusion threads (the docuverse's geometry) ─
        // A cyan NT elbow runs from every surface showing a quoted cell into the
        // document window quoting it — drawn with the same absolutely-positioned
        // overlay idiom as the halo, walkable from either endpoint dot. Painted over
        // the windows but under the halo/menus, gated on the persisted Show-threads
        // preference (the View-menu toggle).
        if self.layout.prefs.show_threads {
            for el in self.render_threads(cx) {
                root = root.child(el);
            }
        }

        // ── The Pharo HALO — direct-manipulation handles on the selected surface ──
        // A ring of round handles floating around the molded icon/window; each fires
        // the SAME actuation the right-click menu does. Painted above the windows so
        // the ring sits on the live surface; the context menu still draws over it.
        if self.selected.is_some() {
            for el in self.render_halo(cx) {
                root = root.child(el);
            }
        }

        // ── The context menu overlay (the ACTUATION) ─────────────────────────────
        if self.open_menu.is_some() {
            root = root.child(self.render_context_menu(cx));
        }

        // ── The property dialog overlay (the PROPERTY inspector/editor) ───────────
        if self.open_prop.is_some() {
            root = root.child(self.render_property_dialog(cx));
        }

        // ── The Spotter command-palette overlay (the Pharo fuzzy-jump) ────────────
        if self.spotter.is_some() {
            root = root.child(self.render_spotter_overlay(window, cx));
        }

        // ── The taskbar (open-window stubs) + the status bar ─────────────────────
        root = root.child(self.render_taskbar(cx));
        root = root.child(self.render_statusbar(cx));
        if self.status_flyout {
            root = root.child(self.render_status_console(cx));
        }

        // ── PULSE TOASTS — the World's foreign motion, arriving bottom-right ──────
        // Green committed / amber REFUSED cards fed by the pulse; click-through
        // opens the World Transcript (the narration lands you on the receipt log)
        // and clears the rack.
        if !self.toast_rack.toasts().is_empty() {
            let mut stack = div()
                .id("pulse-toast-rack")
                .absolute()
                .right(px(12.0))
                .bottom(px(52.0))
                .flex()
                .flex_col()
                .gap_1()
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                        this.toast_rack.clear();
                        this.land_in(this.user, WinKindTag::Transcript);
                        cx.notify();
                    }),
                );
            for card in toasts::render_toast_rack(&self.toast_rack) {
                stack = stack.child(card);
            }
            root = root.child(stack);
        }

        // ── THE REWIND RAIL — scrub verified history (docked above the taskbar,
        //    painted over the windows) + the amber ≠-NOW rings while in the past ──
        for el in self.render_rewind_layer(cx) {
            root = root.child(el);
        }

        // ── The gentle "type anything" entry pill (the calm Spotter door) ─────────
        // A small, always-present invitation pinned top-center. It is the wonder-first
        // face of the Spotter: a newcomer who learns nothing else learns that they can
        // type a word here and arrive. Hidden while the Spotter or the welcome card is
        // already open (one calm thing at a time).
        if self.spotter.is_none() && !self.show_welcome {
            root = root.child(self.render_spotter_pill(cx));
        }

        // ── The warm WELCOME card (the calm front door — first run only) ──────────
        // Painted LAST so it rests over the whole room: a stranger's first breath.
        if self.show_welcome {
            root = root.child(self.render_welcome_overlay(cx));
        }

        root
    }
}

impl DeosDesktop {
    fn render_menubar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menus = ["World", "Cell", "View", "Window", "Help"];
        let user = self.user;
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .top(px(0.0))
            .w_full()
            .h(px(MENUBAR_H))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(NT_FACE))
            .border_b_1()
            .border_color(gpui::rgb(NT_SHADOW));
        // The deos mark on the far left (the "Start"-equivalent system menu).
        bar = bar.child(
            div()
                .px_2()
                .h_full()
                .flex()
                .items_center()
                .bg(gpui::rgb(NT_FACE_DARK))
                .child(div().font_weight(FontWeight::BOLD).child("deos")),
        );
        for (i, name) in menus.iter().enumerate() {
            let name = *name;
            let at_x = 64.0 + i as f32 * 56.0;
            bar = bar.child(
                div()
                    .id(gpui::SharedString::from(format!("menu-{name}")))
                    .px_3()
                    .h_full()
                    .flex()
                    .items_center()
                    .hover(|s| {
                        s.bg(gpui::rgb(NT_MENU_HILIGHT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    // Clicking a menu-bar item drops its menu (the NT pull-down).
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            let actions = this.menubar_actions(name);
                            this.open_menu = Some(OpenMenu {
                                cell: Some(user),
                                heading: name.to_string(),
                                at: Point::new(px(at_x), px(MENUBAR_H)),
                                actions,
                            });
                            cx.notify();
                        }),
                    )
                    .child(name.to_string()),
            );
        }
        // A live height/cell-count readout on the far right (the World face).
        let h = self.world.borrow().height();
        let n = self.cells.len();
        bar = bar.child(
            div()
                .ml_auto()
                .px_3()
                .h_full()
                .flex()
                .items_center()
                .text_color(gpui::rgb(NT_DIM))
                .child(format!("World · {n} cells · height {h}")),
        );
        let _ = cx;
        bar
    }

    fn render_icon(&self, idx: usize, cell: CellId, cx: &mut Context<Self>) -> impl IntoElement {
        let pos = self.icon_pos(idx, &cell);
        let kind = self.cell_kind(&cell);
        let bal = self.cell_balance(&cell);
        let held = self.holds(&cell);
        // A font-safe single-letter kind badge (the geometric/dingbat icon glyphs are
        // tofu in the bake font, so a dense letter stands in: T/W/S/A).
        let glyph = match kind {
            "treasury" => "T",
            "issuer well" => "W",
            "service" => "S",
            _ => "A",
        };
        // An INSTALLED APP's cell wears the app's OWN face — its display name as the
        // caption kind and its initial as the tile glyph — so a launched shelf app
        // reads as an APP on the desktop, not a balance-classified account. (The
        // registry exposes this for free off the installed set; every other cell
        // keeps its kind face.)
        #[cfg(feature = "app-registry")]
        let (kind, glyph) = self.app_shelf.icon_face(&cell).unwrap_or((kind, glyph));
        // A floor-posted OFFER's cell wears the economy face ("compute offer" · $) —
        // the order book's substance reads as itself on the desktop.
        #[cfg(feature = "app-registry")]
        let (kind, glyph) = self
            .exchange_floor
            .icon_face(&cell)
            .unwrap_or((kind, glyph));
        let label = if self.layout.prefs.show_balances {
            format!("{}\n{}\n{}", kind, id_short(&cell), fmt_balance(bal))
        } else {
            format!("{}\n{}", kind, id_short(&cell))
        };

        div()
            .id(gpui::SharedString::from(format!("icon-{}", id_hex(&cell))))
            .absolute()
            .left(pos.x)
            .top(pos.y)
            .w(px(ICON_W))
            .h(px(ICON_H))
            .flex()
            .flex_col()
            .items_center()
            .justify_start()
            .pt_1()
            // Drag to move; the mouse-down records the grab offset and starts a drag.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = None;
                    // Select the icon → its halo ring floats (the Pharo "mold it").
                    this.selected = Some(HaloTarget::Icon(cell));
                    let idx = this.cells.iter().position(|c| *c == cell).unwrap_or(0);
                    let p = this.icon_pos(idx, &cell);
                    this.drag = Some(Drag::Icon {
                        cell,
                        grab: Point::new(ev.position.x - p.x, ev.position.y - p.y),
                    });
                    cx.notify();
                }),
            )
            // Double-click opens the inspector window.
            .on_click(cx.listener(move |this, ev: &ClickEvent, _w, cx| {
                if ev.click_count() >= 2 {
                    this.open_window(cell);
                    cx.notify();
                }
            }))
            // Right-click opens the context menu (the ACTUATION surface).
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: Some(cell),
                        heading: format!("{} · {}", this.cell_kind(&cell), id_short(&cell)),
                        at: ev.position,
                        actions: this.actions_for(cell),
                    });
                    cx.notify();
                }),
            )
            .child(
                // The 40x40 glyph tile. A HELD/live cell wears its kind-tinted glow
                // (the glowing-room warmth — see `bevel_raised_glow`); a quiet cell
                // keeps the plain raised face, dimmed.
                {
                    // Every cell is a glowing thing in the room (the 1999-AOL warmth):
                    // its kind-tinted halo + colored glyph. A cell the viewer HOLDS burns
                    // full; one they don't is the same glow, just a touch quieter — alive,
                    // never washed-out.
                    let glow = crate::deos_desktop::chrome::kind_glow(kind);
                    crate::deos_desktop::chrome::bevel_raised_glow(div(), glow)
                        .when(!held, |d| d.opacity(0.82))
                        .text_color(gpui::rgb(glow))
                        .w(px(40.0))
                        .h(px(40.0))
                        .flex()
                        .items_center()
                        .justify_center()
                        .text_size(px(22.0))
                        .font_weight(gpui::FontWeight::BOLD)
                        .child(glyph)
                },
            )
            .child(
                div()
                    .mt_1()
                    .px_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_ICON_LABEL))
                    .text_center()
                    .child(label),
            )
    }

    fn render_window(
        &mut self,
        key: WinKey,
        active: bool,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let (cell, tag) = key;
        let (x, y, w, h, title, minimized) = {
            let ws = &self.windows[&key];
            (ws.x, ws.y, ws.w, ws.h, ws.title.clone(), ws.minimized)
        };

        if minimized {
            // A minimized window collapses to a title-bar stub at its origin.
            return div()
                .id(gpui::SharedString::from(format!(
                    "winmin-{}-{:?}",
                    id_hex(&cell),
                    tag as u8
                )))
                .absolute()
                .left(px(x))
                .top(px(y))
                .w(px(180.0))
                .child(self.render_titlebar(key, &title, active, true, cx))
                .into_any_element();
        }

        // The body varies by window TYPE — the NT/Pharo density. Every body
        // scrolls behind a REAL NT scrollbar off one persistent handle per
        // window face (`face_scrolls`); the tabbed bodies (World Explorer /
        // Agent Room) ensure their OWN per-tab handles inside their renderers,
        // so each tab keeps its own place.
        let sc = self
            .face_scrolls
            .ensure(FaceScrollKey::Window(cell, tag, 0));
        let body = match tag {
            WinKindTag::Inspector => self.render_inspector_body(cell, &sc, cx),
            WinKindTag::DocEditor => self.render_doc_body(cell, &sc, window, cx),
            WinKindTag::Links => self.render_links_body(cell, &sc),
            WinKindTag::Transcript => self.render_transcript_body(cell, cx),
            WinKindTag::Workflow => self.render_workflow_body(cell, &sc, cx),
            WinKindTag::DocExplorer => self.render_doc_explorer_body(cell, &sc, cx),
            WinKindTag::WorldExplorer => self.render_world_explorer_window(cell, cx),
            WinKindTag::AgentRoom => self.render_agent_room_window(cell, cx),
            WinKindTag::MailRoom => self.render_mail_room_window(cell, window, cx),
            WinKindTag::DreggComputers => self.render_dregg_computers_window(cell, cx),
            WinKindTag::ProvenanceWalker => self.render_provenance_walker_window(cell, cx),
            #[cfg(feature = "card-pane")]
            WinKindTag::ViewNodePane => self.render_viewnode_body(cell, &sc, window, cx),
            #[cfg(feature = "android-systemui")]
            WinKindTag::AndroidCell => self.render_android_systemui_body(cell, &sc, cx),
            #[cfg(feature = "app-registry")]
            WinKindTag::AppShelf => self.render_app_shelf_body(&sc, cx),
            #[cfg(feature = "app-registry")]
            WinKindTag::ExchangeFloor => self.render_exchange_floor_body(&sc, cx),
            #[cfg(feature = "dev-surfaces")]
            WinKindTag::MatrixRoom => self.render_matrix_room_window(cell, window, cx),
            #[cfg(feature = "dev-surfaces")]
            WinKindTag::AttachWizard => self.render_attach_wizard_window(cell, cx),
            #[allow(unreachable_patterns)]
            // needed when card-pane / android-systemui features are off
            _ => self.render_inspector_body(cell, &sc, cx),
        };

        let resize_grip = div()
            .id(gpui::SharedString::from(format!(
                "resize-{}-{:?}",
                id_hex(&cell),
                tag as u8
            )))
            .absolute()
            .right(px(0.0))
            .bottom(px(0.0))
            .w(px(14.0))
            .h(px(14.0))
            .bg(gpui::rgb(NT_FACE_DARK))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&key) {
                        this.drag = Some(Drag::WinResize {
                            key,
                            origin: Point::new(px(ws.x), px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            .text_size(px(8.0))
            .flex()
            .items_center()
            .justify_center()
            .child(GLYPH_GRIP);

        bevel_window(
            div()
                .id(gpui::SharedString::from(format!(
                    "win-{}-{:?}",
                    id_hex(&cell),
                    tag as u8
                )))
                .absolute()
                .left(px(x))
                .top(px(y))
                .w(px(w))
                .h(px(h))
                .flex()
                .flex_col()
                .p_px(),
        )
        // Clicking anywhere in the window raises it AND selects it (its halo ring).
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.selected = Some(HaloTarget::Window(key));
                if let Some(ws) = this.windows.get_mut(&key) {
                    ws.z = this.next_z;
                    this.next_z += 1;
                }
                cx.notify();
            }),
        )
        // Right-click anywhere on the window chrome opens the WINDOW menu.
        .on_mouse_down(MouseButton::Right, {
            let title_for_menu = title.clone();
            cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                this.open_menu = Some(OpenMenu {
                    cell: Some(cell),
                    heading: title_for_menu.clone(),
                    at: ev.position,
                    actions: this.window_actions(cell, tag),
                });
                cx.notify();
            })
        })
        .child(self.render_titlebar(key, &title, active, false, cx))
        .child(body)
        .child(resize_grip)
        .into_any_element()
    }

    /// The classic reflective inspector body (identity + live state + affordances +
    /// a Properties button).
    fn render_inspector_body(
        &self,
        cell: CellId,
        scroll: &ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let bal = self.cell_balance(&cell);
        let nonce = self.cell_nonce(&cell);
        let lifecycle = self.cell_lifecycle(&cell);
        let caps = self.cell_cap_count(&cell);
        let kind = self.cell_kind(&cell);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let held = self.holds(&cell);
        let receipts = self.cell_receipt_count(&cell);
        // The balance gauge denominator — the World's largest holder.
        let gauge = (bal.max(0) as f32) / (self.world_max_balance() as f32);
        // The lifecycle reads green when Live, amber otherwise (a sealed/migrated cell).
        let life_color = if lifecycle == "Live" { NT_OK } else { NT_WARN };

        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "winbody-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Identity"))
            .child(face_row("id", &id_hex(&cell)))
            .child(face_row("kind", kind))
            .child(face_row_color(
                "authority",
                if held { "held (lit)" } else { "system (dim)" },
                if held { NT_OK } else { NT_DIM },
            ))
            .child(face_section("State (live)"))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_gauge(gauge))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row_color("lifecycle", &lifecycle, life_color))
            .child(face_row("capabilities", &caps.to_string()))
            .child(face_row("doc revision", &rev.to_string()))
            .child(face_row("turns by cell", &receipts.to_string()));

        // ── State slots (the raw committed fields — Pharo "inspect everything") ──
        col = col.child(face_section("State slots (committed fields)"));
        for slot in 0..8usize {
            let v = self.cell_field_u64(&cell, slot);
            // Only show non-zero slots plus slot 0 (keeps the dense view legible).
            if v != 0 || slot == 0 {
                col = col.child(face_row(&format!("field[{slot}]"), &v.to_string()));
            }
        }

        // ── The committed document, if this cell carries one (the inspector REFLECTS
        //    the document that IS the cell — a prose preview off the committed heap) ──
        if let Some(prose) = self.read_doc_from_heap(&cell) {
            col = col.child(face_section("Document (committed prose)"));
            let bytes = prose.len();
            let lines = prose
                .lines()
                .count()
                .max(if prose.is_empty() { 0 } else { 1 });
            col = col.child(face_row("bytes on heap", &bytes.to_string()));
            col = col.child(face_row("lines", &lines.to_string()));
            let preview: String = prose.chars().take(140).collect();
            let preview = if prose.chars().count() > 140 {
                format!("{preview}…")
            } else {
                preview
            };
            col = col.child(
                div()
                    .my_1()
                    .p_1()
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_size(px(10.0))
                    .child(if preview.is_empty() {
                        "(empty document)".to_string()
                    } else {
                        preview
                    }),
            );
        }

        // ── Recent turns whose agent IS this cell (the cell's own chronicle) ──
        col = col.child(face_section("Recent turns (this cell)"));
        let cell_receipts: Vec<String> = {
            let w = self.world.borrow();
            w.receipts()
                .iter()
                .filter(|r| r.agent == cell)
                .rev()
                .take(5)
                .map(|r| {
                    let hh: String = r.turn_hash[..3]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    let post: String = r.post_state_hash[..3]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    format!("turn {hh} → post {post}")
                })
                .collect()
        };
        if cell_receipts.is_empty() {
            col = col.child(face_row("(none)", "actuate to write a receipt"));
        } else {
            for (i, line) in cell_receipts.iter().enumerate() {
                col = col.child(face_row(&format!("[{i}]"), line));
            }
        }

        let col = col
            .child(face_section("Affordances (do it)"))
            .child(self.affordance_button(cell, "Bump nonce", ActionKind::BumpNonce, cx))
            .child(self.affordance_button(
                cell,
                &format!("Transfer 1,000 → {}", id_short(&self.user)),
                ActionKind::Transfer { amount: 1_000 },
                cx,
            ))
            .child(self.affordance_button(
                cell,
                &format!("Grant cap → {}", id_short(&self.user)),
                ActionKind::Grant { target: self.user },
                cx,
            ))
            .child(self.affordance_button(cell, "Open as Document…", ActionKind::OpenDoc, cx))
            .child(self.affordance_button(cell, "Properties…", ActionKind::Properties, cx));
        nt_scroll_face(scroll, col).into_any_element()
    }

    /// **The document-editor body** — the cell's prose, the live chronicle (patch
    /// count), and the receipted-edit controls. Typing here is a `dregg_doc::Patch`
    /// plus a verified revision turn (the document IS the cell).
    fn render_doc_body(
        &mut self,
        cell: CellId,
        scroll: &ScrollHandle,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        // Build the live free-typing editor on first render of this doc body (it needs
        // `window`/`cx`). Keystrokes flow Change → `edit_doc` → committed heap.
        self.ensure_doc_input(cell, window, cx);
        // Apply a pending external edit (transclude / bake) into the live widget — the
        // editing paths that lack `&mut Window` deferred the `set_value` to here.
        if self.doc_resync.remove(&cell) {
            let text = self.load_doc_buffer(cell);
            if let Some(input) = self.doc_inputs.get(&cell).cloned() {
                input.update(cx, |st, cx| st.set_value(&text, window, cx));
            }
        }

        let patches = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor { doc, .. }) => doc.history().len(),
            _ => 0,
        };
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let input = self.doc_inputs.get(&cell).cloned();
        let face = div()
            .id(gpui::SharedString::from(format!(
                "docbody-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(
                "Document (free-typing — every keystroke is a receipted patch)",
            ))
            .child(
                // THE PROSE SURFACE — a REAL editable text field (gpui-component's
                // rope-backed multi-line `Input`). Click in and type; each keystroke
                // commits into the cell's heap. Drag a cell-icon here to transclude it.
                div()
                    .id(gpui::SharedString::from(format!(
                        "docprose-{}",
                        id_hex(&cell)
                    )))
                    .flex_1()
                    .min_h(px(120.0))
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_size(px(12.0))
                    .when_some(input, |this, input| this.child(Input::new(&input).h_full())),
            )
            .child(face_section("Chronicle"))
            .child(face_row("patches", &patches.to_string()))
            .child(face_row("cell revision", &rev.to_string()))
            .child(face_row("author", &format!("{}", self.author.0 & 0xffff)))
            .child(self.render_doc_collab(cell, window, cx));
        nt_scroll_face(scroll, face).into_any_element()
    }

    /// **The branch / stitch / CONFLICT surface** — the live realization of
    /// conflicts-as-first-class-states (DOCUMENT-LANGUAGE §2.3, the `dregg_doc` patch
    /// core). It shows: Fork-a-draft / diverge / Stitch controls; and when a stitch
    /// produced a conflict, the ConflictView — each antichain region's live
    /// alternatives side-by-side WITH author provenance, and one-click resolution
    /// buttons (`resolutions_for`) that each commit a real resolution patch.
    fn render_doc_collab(
        &mut self,
        cell: CellId,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        // A live co-author draft editor exists exactly while a branch is forked.
        self.ensure_branch_input(cell, window, cx);

        let (has_branch, branch_graph, doc_graph, merged) = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor {
                doc,
                branch,
                merged,
                ..
            }) => (
                branch.is_some(),
                branch.as_ref().map(|b| b.history().replay()),
                Some(doc.history().replay()),
                merged.clone(),
            ),
            _ => (false, None, None, None),
        };
        let branch_input = self.branch_inputs.get(&cell).cloned();

        let mut col = div().flex().flex_col().gap_1().child(face_section(
            "Collaborate (branch · stitch · conflict-as-state)",
        ));

        // ── THE UMEM-HEAP BOUNDARY — the document IS a cell; its commitment IS the
        //    sorted-Poseidon2 boundary over its umem-heap. Watch it MOVE as the document
        //    is edited, diverged, and resolved (the dregg-doc-on-umem ride made visible).
        if let Some(g) = &doc_graph {
            // The LIVE committed boundary off the ledger (the document IS this
            // resealed `heap_root`), falling back to the derived projection only if
            // the cell is somehow absent.
            let root = self
                .live_doc_boundary(&cell)
                .unwrap_or_else(|| self.doc_umem_boundary(cell, g));
            col = col.child(face_row("umem heap_root", &Self::boundary_short(&root)));
        }

        // The branch/stitch controls.
        if !has_branch && merged.is_none() {
            col = col.child(self.doc_collab_button(
                cell,
                "Fork a co-author draft branch",
                DocCollabAct::Fork,
                cx,
            ));
        }
        if has_branch {
            // The branch's OWN umem boundary diverges from the document's the moment the
            // co-author edits — two sovereign boundaries, reconciled only by a stitch.
            let branch_root =
                self.doc_umem_boundary(cell, branch_graph.as_ref().unwrap_or(&DocGraph::new()));
            col = col
                .child(face_row(
                    "draft branch",
                    "confined (no heap commit until stitch)",
                ))
                .child(face_row(
                    "branch heap_root",
                    &Self::boundary_short(&branch_root),
                ))
                .child(face_section(
                    "Co-author's confined draft (type to diverge — a second author)",
                ))
                .when_some(branch_input, |this, input| {
                    this.child(
                        div()
                            .id(gpui::SharedString::from(format!(
                                "branchprose-{}",
                                id_hex(&cell)
                            )))
                            .min_h(px(56.0))
                            .bg(gpui::rgb(0xfbf7ff))
                            .border_1()
                            .border_color(gpui::rgb(0x9070b0))
                            .text_size(px(11.0))
                            .child(Input::new(&input).h_full()),
                    )
                })
                .child(self.doc_collab_button(
                    cell,
                    "Co-author diverges (canned demo edit)",
                    DocCollabAct::Diverge,
                    cx,
                ))
                .child(self.doc_collab_button(
                    cell,
                    "Stitch draft → document (the pushout)",
                    DocCollabAct::Stitch,
                    cx,
                ));
        }

        // ── THE CONFLICT VIEW — first-class conflict states, side-by-side. ──
        if let Some(m) = &merged {
            let graph = m.history().replay();
            let rendered = content(&graph);
            let conflicts: Vec<_> = rendered.conflicts().cloned().collect();
            // The conflict's umem boundary BINDS BOTH live alternatives (forging or
            // hiding one moves the root — the anti-forge tooth, in the committed heap).
            let conflict_root = self.doc_umem_boundary(cell, &graph);
            col = col
                .child(face_section(&format!(
                    "CONFLICT ({} region{}, first-class state · held, NOT committed)",
                    conflicts.len(),
                    if conflicts.len() == 1 { "" } else { "s" }
                )))
                .child(face_row(
                    "binds both alts",
                    &Self::boundary_short(&conflict_root),
                ));
            for (ri, region) in conflicts.iter().enumerate() {
                let regime_lbl = match region.regime {
                    Regime::Prose => "prose · always-resolvable",
                    Regime::Field => "field · needs consensus",
                };
                let head = if let Some(f) = &region.field {
                    format!("region {ri}  ·  field '{f}'  ·  {regime_lbl}")
                } else {
                    format!("region {ri}  ·  {regime_lbl}")
                };
                col = col.child(
                    div()
                        .my_1()
                        .px_1()
                        .text_size(px(10.0))
                        .font_weight(FontWeight::BOLD)
                        .text_color(gpui::rgb(0xa02020))
                        .child(head),
                );
                // Each live alternative, attributed to WHO wrote it — you vs co-author
                // (a FACT carried by the commitment; the loser is provenanced, not lost).
                for alt in &region.alternatives {
                    let txt: String = alt.text.chars().take(80).collect();
                    col = col.child(
                        div()
                            .ml_2()
                            .px_1()
                            .py_1()
                            .bg(gpui::rgb(0xfff4f4))
                            .border_1()
                            .border_color(gpui::rgb(0xd0a0a0))
                            .text_size(px(10.0))
                            .child(format!(
                                "{}: {}",
                                self.author_label(alt.provenance.author),
                                if txt.trim().is_empty() {
                                    "(empty)"
                                } else {
                                    txt.trim()
                                }
                            )),
                    );
                }
                // One-click resolution choices — each a ready, authored patch (its commit
                // is the resolution turn's receipt).
                let choices = resolutions_for(&graph, region, self.author);
                for (ci, choice) in choices.iter().enumerate() {
                    col = col.child(self.doc_resolve_button(cell, ri, ci, &choice.label, cx));
                }
            }
        }

        // ── THE RECEIPT — the most recent resolution, as a content-addressed turn id.
        if let Some((rc, label, pid)) = &self.last_resolution {
            if *rc == cell {
                col = col.child(
                    div()
                        .my_1()
                        .px_1()
                        .py_1()
                        .bg(gpui::rgb(0xe8f0e8))
                        .border_1()
                        .border_color(gpui::rgb(0x70a070))
                        .text_size(px(10.0))
                        .child(format!(
                            "RESOLVED '{}' → receipt patch #{} (published to the umem-heap)",
                            label, pid.0
                        )),
                );
            }
        }

        col.into_any_element()
    }

    /// A branch/stitch action button — fires the corresponding collaboration gesture.
    fn doc_collab_button(
        &self,
        cell: CellId,
        label: &str,
        act: DocCollabAct,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "doccollab-{}-{}",
                    id_hex(&cell),
                    label
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                match act {
                    DocCollabAct::Fork => this.fork_doc_branch(cell),
                    DocCollabAct::Diverge => {
                        this.diverge_branch(cell, "\nThe co-author's alternative line.\n")
                    }
                    DocCollabAct::Stitch => this.stitch_branch(cell),
                }
                cx.notify();
            }),
        )
        .child(label.to_string())
    }

    /// A one-click conflict-resolution button — commits exactly the chosen
    /// `ResolutionChoice`'s ready patch onto the merged document.
    fn doc_resolve_button(
        &self,
        cell: CellId,
        region_idx: usize,
        choice_idx: usize,
        label: &str,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "docresolve-{}-{region_idx}-{choice_idx}",
                    id_hex(&cell)
                )))
                .ml_2()
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(10.0))
                .bg(gpui::rgb(0xe8f0e8)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.resolve_conflict(cell, region_idx, choice_idx);
                cx.notify();
            }),
        )
        .child(format!("resolve: {label}"))
    }

    // ── THE DOCUMENT EXPLORER — the Pharo-moldable inspector of a doc's patch substance ──

    /// Obtain a live `dregg_doc::Doc` to explore for `cell`: the open editor's own doc
    /// (its full patch-history) if one is open, else a doc reconstructed from the cell's
    /// committed heap prose. `None` for a cell that carries no document at all.
    fn doc_for_explorer(&self, cell: CellId) -> Option<Doc> {
        if let Some(WinKind::DocEditor { doc, .. }) = self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            return Some(doc.clone());
        }
        let text = self.read_doc_from_heap(&cell)?;
        let g = if self.layout.prefs.word_granularity {
            Granularity::Word
        } else {
            Granularity::Line
        };
        let mut doc = Doc::new(g);
        if !text.is_empty() {
            doc.edit(self.author, &text);
        }
        Some(doc)
    }

    /// **The World Explorer window** — the NT tab strip + the [`world_explorer`] body
    /// (ledger · chronicle · conservation). The "My Computer" of the verified World.
    /// (`&mut self` for the face-scroll registry: each tab's face keeps its OWN
    /// persistent scroll handle, keyed by the tab ordinal.)
    fn render_world_explorer_window(&mut self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        use world_explorer::WorldExplorerTab as T;
        let tab = self
            .world_explorers
            .get(&cell)
            .map(|s| s.tab)
            .unwrap_or_default();

        let mut tabs = div().flex().flex_row().gap_1().my_1();
        for t in T::ALL {
            let selected = t == tab;
            tabs = tabs.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "wldtab-{}-{}",
                            id_hex(&cell),
                            t.label()
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.world_explorers.entry(cell).or_default().tab = t;
                        cx.notify();
                    }),
                )
                .child(t.label()),
            );
        }

        // The faces read through the Rewind Rail's effective lens: the live World
        // at LIVE, the root-verified replayed projection (with its amber REPLAYED
        // banner) while the rail is scrubbed. Chronicle + Ledger are UNCAPPED here
        // (View-owned `v_virtual_list`); Conservation stays the flat pure body.
        let body = self.render_world_explorer_body_effective(tab, cell, cx);
        div()
            .id(gpui::SharedString::from(format!(
                "wldbody-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .child(tabs)
            .child(body)
            .into_any_element()
    }

    /// **The Agent Room window body** — the resident picker strip + the face tabs +
    /// the room header + the selected face, all over a fresh [`agent::AgentActivity`]
    /// built from the live World each frame (the ledger's truth, never a cache).
    fn render_agent_room_window(&mut self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        use agent_room::AgentRoomTab as T;
        let state = self.agent_rooms.entry(cell).or_default().clone();
        // Each face keeps its OWN persistent scroll handle (tab ordinal in the key).
        let sc = self.face_scrolls.ensure(FaceScrollKey::Window(
            cell,
            WinKindTag::AgentRoom,
            state.tab as u8,
        ));
        let world = self.world.borrow();
        let resident = state
            .resident
            .unwrap_or_else(|| agent_room::default_resident(&world, self.user));
        let activity = crate::agent::AgentActivity::build(&world, resident, 24);
        let ranked = agent_room::residents(&world);
        drop(world);

        // THE HIRELING's session-side gate refusals — REAL gate verdicts merged into
        // the Actions face as REFUSED rows (surfaced, never fabricated World turns;
        // see `hireling`'s two-truths line). Only when the room watches the hired
        // resident itself.
        #[cfg(feature = "dev-surfaces")]
        let activity = {
            let mut activity = activity;
            self.hireling.merge_refusals_into(resident, &mut activity);
            activity
        };

        // The resident picker — the top-ranked cells by committed-turn count, the
        // watched one selected. Clicking pins the room to that resident.
        let mut picker = div().flex().flex_row().flex_wrap().gap_1().my_1();
        for (rid, nonce) in ranked.iter().take(6) {
            let rid = *rid;
            let selected = rid == resident;
            let is_user = rid == self.user;
            let caption = format!(
                "{}{} n{}",
                id_short(&rid),
                if is_user { " (you)" } else { "" },
                nonce
            );
            picker = picker.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "agentroom-pick-{}",
                            id_hex(&rid)
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.agent_rooms.entry(cell).or_default().resident = Some(rid);
                        cx.notify();
                    }),
                )
                .child(caption),
            );
        }

        // The face tabs — actions / mandate / reach.
        let mut tabs = div().flex().flex_row().gap_1().my_1();
        for t in T::ALL {
            let selected = t == state.tab;
            tabs = tabs.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "agentroom-tab-{}",
                            t.label()
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.agent_rooms.entry(cell).or_default().tab = t;
                        cx.notify();
                    }),
                )
                .child(t.label()),
            );
        }

        // THE HIRELING STRIP — hire/step/fire the room's real confined resident
        // (`dev-surfaces`: the deos-hermes brain/gate rail). A build without that
        // rail simply mounts no strip — the room stays the pure observer it was.
        #[cfg(feature = "dev-surfaces")]
        let hire_strip = Some(self.render_hireling_strip(cell, cx));
        #[cfg(not(feature = "dev-surfaces"))]
        let hire_strip: Option<AnyElement> = None;

        let header = agent_room::render_room_header(&activity);
        let body = agent_room::render_agent_room_body(&activity, state.tab, &sc);
        div()
            .id(gpui::SharedString::from(format!(
                "agentroom-body-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .child(picker)
            .children(hire_strip)
            .child(header)
            .child(tabs)
            .child(body)
            .into_any_element()
    }

    /// Build the Mail Room composer's live input on first render — single-line, Enter
    /// posts the draft as a REAL send turn (the SAME send the bake hook drives). Mirrors
    /// the Matrix composer / Spotter input plumbing exactly.
    fn ensure_mail_input(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if self.mail_input.is_some() {
            return;
        }
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .placeholder("Write a letter — Enter posts it to your outbox…")
        });
        let sub = cx.subscribe_in(
            &input,
            window,
            |this, input, ev: &InputEvent, window, cx| match ev {
                InputEvent::Change => {
                    this.mail_draft = input.read(cx).value().to_string();
                }
                InputEvent::PressEnter { .. } => {
                    this.mail_send_draft(mail_room::mail_room_window_cell());
                    input.update(cx, |st, cx| st.set_value("", window, cx));
                    cx.notify();
                }
                _ => {}
            },
        );
        self.mail_input = Some(input);
        self.mail_input_sub = Some(sub);
    }

    /// **POST the composer draft as a letter** — one real [`crate::letter_office::send_letter`]
    /// turn from the operator to the chosen correspondent: the letter is born as a cell
    /// (its markdown in the heap), then dropped in the operator's outbox with a receipted
    /// turn. The subject is the first non-empty markdown line; the verdict is narrated.
    fn mail_send_draft(&mut self, cell: CellId) {
        let body = std::mem::take(&mut self.mail_draft);
        let body = body.trim().to_string();
        if body.is_empty() {
            return;
        }
        let recipient = {
            let w = self.world.borrow();
            self.mail_rooms
                .get(&cell)
                .and_then(|s| s.recipient)
                .or_else(|| mail_room::default_recipient(&w, self.user))
        };
        let Some(to) = recipient else {
            self.say("No one to write to yet — a resident must exist to receive a letter.");
            return;
        };
        // The subject is the first non-empty line (heading marks trimmed), capped legibly.
        let subject: String = body
            .lines()
            .map(|l| l.trim_start_matches('#').trim())
            .find(|l| !l.is_empty())
            .unwrap_or("(no subject)")
            .chars()
            .take(64)
            .collect();
        let from = self.user;
        let outcome = {
            let mut w = self.world.borrow_mut();
            crate::letter_office::send_letter(&mut w, from, to, &subject, &body)
        };
        match outcome {
            Ok(r) => self.say(format!(
                "Letter posted to {} — it sits in your outbox awaiting the ferry (receipt {}).",
                id_short(&to),
                r.receipt[..4]
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
            )),
            Err(e) => self.say(format!("Letter REFUSED — {e}")),
        }
    }

    /// **DELIVER a letter NOW** — the ferry's round, fired by hand from the Outbox face:
    /// one [`crate::letter_office::deliver_now`] turn moves the Outbound letter to its
    /// recipient's inbox (the twice-daily mailman a named seam). The verdict is narrated.
    fn mail_deliver(&mut self, letter: CellId) {
        let outcome = {
            let mut w = self.world.borrow_mut();
            crate::letter_office::deliver_now(&mut w, letter)
        };
        match outcome {
            Ok(r) => self.say(format!(
                "Delivered — the ferry moved the letter to its inbox (receipt {}).",
                r.receipt[..4]
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
            )),
            Err(e) => self.say(format!("Delivery REFUSED — {e}")),
        }
    }

    /// **The Mail Room window body** — the letter office on the live World: the recipient
    /// picker, the Inbox / Outbox / Mail-Ledger tabs, the office header, the selected face
    /// (each letter a real cell, re-scanned off the ledger every paint), and the compose
    /// strip that posts a new letter as a real send turn. The Outbox face welds a *deliver
    /// now* button onto every Outbound letter — one click IS one ferry round, committing
    /// the delivery turn locally.
    fn render_mail_room_window(
        &mut self,
        cell: CellId,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        use mail_room::MailRoomTab as T;
        self.ensure_mail_input(window, cx);
        let state = self.mail_rooms.entry(cell).or_default().clone();
        // Each face keeps its OWN persistent scroll handle (tab ordinal in the key).
        let sc = self.face_scrolls.ensure(FaceScrollKey::Window(
            cell,
            WinKindTag::MailRoom,
            state.tab as u8,
        ));
        let world = self.world.borrow();
        let mb = crate::letter_office::mailbox_of(&world, self.user);
        let town = crate::letter_office::town_letters(&world);
        let cands = mail_room::recipient_candidates(&world, self.user);
        let recipient = state
            .recipient
            .or_else(|| mail_room::default_recipient(&world, self.user));
        drop(world);

        // The recipient picker — other residents by activity; clicking sets who the
        // compose strip writes to.
        let mut picker = div().flex().flex_row().flex_wrap().gap_1().my_1();
        for (rid, nonce) in cands.iter().take(6) {
            let rid = *rid;
            let selected = Some(rid) == recipient;
            let caption = format!("{} n{}", id_short(&rid), nonce);
            picker = picker.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "mailroom-to-{}",
                            id_hex(&rid)
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.mail_rooms.entry(cell).or_default().recipient = Some(rid);
                        cx.notify();
                    }),
                )
                .child(caption),
            );
        }
        if cands.is_empty() {
            picker = picker.child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child("(no other residents yet — no one to write to)"),
            );
        }

        // The face tabs — inbox / outbox / mail-ledger.
        let mut tabs = div().flex().flex_row().gap_1().my_1();
        for t in T::ALL {
            let selected = t == state.tab;
            tabs = tabs.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "mailroom-tab-{}",
                            t.label()
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.mail_rooms.entry(cell).or_default().tab = t;
                        cx.notify();
                    }),
                )
                .child(t.label()),
            );
        }

        let header = mail_room::render_mailbox_header(&mb);

        // The selected face. Inbox + Ledger are pure; the Outbox welds deliver buttons.
        let body = match state.tab {
            T::Inbox => mail_room::render_inbox_face(&mb, &sc),
            T::Ledger => mail_room::render_ledger_face(&town, &sc),
            T::Outbox => {
                let mut col = div()
                    .id("mailroom-outbox")
                    .bg(gpui::rgb(NT_PANEL))
                    .p_2()
                    .flex()
                    .flex_col()
                    .gap_2()
                    .child(face_section(&format!(
                        "Outbox · {} sent · {} awaiting the ferry",
                        mb.sent, mb.pending
                    )));
                if mb.outbox.is_empty() {
                    col = col.child(face_row("(empty)", "no letters sent yet — write one below"));
                } else {
                    for l in &mb.outbox {
                        let card = mail_room::letter_card(l);
                        let card = if l.status == crate::letter_office::LetterStatus::Outbound {
                            let lc = l.cell;
                            card.child(
                                div().flex().flex_row().justify_end().child(
                                    bevel_raised(
                                        div()
                                            .id(gpui::SharedString::from(format!(
                                                "mail-deliver-{}",
                                                id_hex(&lc)
                                            )))
                                            .px_2()
                                            .py_1()
                                            .text_size(px(10.0))
                                            .font_weight(FontWeight::BOLD)
                                            .bg(gpui::rgb(NT_WARN))
                                            .text_color(gpui::rgb(0xffffff)),
                                    )
                                    .on_mouse_down(
                                        MouseButton::Left,
                                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                            this.mail_deliver(lc);
                                            cx.notify();
                                        }),
                                    )
                                    .child("deliver now  ⟶"),
                                ),
                            )
                        } else {
                            card
                        };
                        col = col.child(card);
                    }
                }
                nt_scroll_face(&sc, col).into_any_element()
            }
        };

        // The compose strip — write a letter to the chosen recipient (Enter or Send posts
        // it to the outbox as a real send turn). Rides under every face.
        let to_label = match recipient {
            Some(r) => format!("To: {}", id_short(&r)),
            None => "To: (pick a recipient above)".to_string(),
        };
        let input = self.mail_input.clone();
        let composer = div()
            .flex()
            .flex_col()
            .gap_1()
            .my_1()
            .child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(to_label),
            )
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .items_center()
                    .child(
                        div()
                            .flex_1()
                            .h(px(26.0))
                            .bg(gpui::rgb(0xffffff))
                            .when_some(input, |d, input| d.child(Input::new(&input).h_full())),
                    )
                    .child(
                        bevel_raised(
                            div()
                                .id("mail-send")
                                .px_2()
                                .py_1()
                                .text_size(px(10.0))
                                .font_weight(FontWeight::BOLD),
                        )
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.mail_send_draft(cell);
                                cx.notify();
                            }),
                        )
                        .child("Send ✉"),
                    ),
            );

        div()
            .id(gpui::SharedString::from(format!(
                "mailroom-body-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .child(picker)
            .child(header)
            .child(tabs)
            .child(body)
            .child(composer)
            .into_any_element()
    }

    /// **The My Dregg Computers window body** — your vats on the glass: the
    /// roster header (its source named — fixture vs live gateway), the
    /// Computers / Connection / Receipts tabs, and the selected face. The
    /// Computers face welds a CONNECT (or disconnect) button onto every vat
    /// card — one click attaches the computer over the proven wire path; the
    /// Connection and Receipts faces are the pure `dregg_computers` renders
    /// over the live [`dregg_computers::VatLink`] (the clobber-safe split, as
    /// the Agent Room / Mail Room hold it).
    fn render_dregg_computers_window(
        &mut self,
        cell: CellId,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        use dregg_computers::DreggComputersTab as T;
        let state = self.dregg_computers.entry(cell).or_default().clone();
        // Each face keeps its OWN persistent scroll handle (tab ordinal in the key).
        let sc = self.face_scrolls.ensure(FaceScrollKey::Window(
            cell,
            WinKindTag::DreggComputers,
            state.tab as u8,
        ));

        // The face tabs — computers / connection / receipts.
        let mut tabs = div().flex().flex_row().gap_1().my_1();
        for t in T::ALL {
            let selected = t == state.tab;
            tabs = tabs.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "dregg-computers-tab-{}",
                            t.label()
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.dregg_computers.entry(cell).or_default().tab = t;
                        cx.notify();
                    }),
                )
                .child(t.label()),
            );
        }

        let header =
            dregg_computers::render_directory_header(&self.vat_directory, self.vat_link.as_ref());

        let body = match state.tab {
            T::Connection => dregg_computers::render_connection_face(self.vat_link.as_ref(), &sc),
            T::Receipts => dregg_computers::render_receipts_face(self.vat_link.as_ref(), &sc),
            T::Computers => {
                // The roster face — every vat card, CONNECT welded on by this View
                // (the pure module renders the card; the listener needs `Context`).
                let mut col = div()
                    .id("dregg-computers-roster")
                    .bg(gpui::rgb(NT_PANEL))
                    .p_2()
                    .flex()
                    .flex_col()
                    .gap_2()
                    .child(face_section(&format!(
                        "Computers you can reach · {}",
                        self.vat_directory.vats.len()
                    )));
                if let Some(err) = &self.vat_directory.error {
                    col = col.child(face_row_color("gateway", err, NT_WARN));
                }
                if self.vat_directory.vats.is_empty() && self.vat_directory.error.is_none() {
                    col = col.child(face_row(
                        "(none)",
                        "no vats yet — `dregg-cloud vat create --name mybox` mints one",
                    ));
                }
                for v in self.vat_directory.vats.clone() {
                    let attached = self
                        .vat_link
                        .as_ref()
                        .is_some_and(|l| l.vat.cell_id == v.cell_id);
                    let vid = v.cell_id.clone();
                    let button = bevel_raised(
                        div()
                            .id(gpui::SharedString::from(format!("vat-connect-{vid}")))
                            .px_2()
                            .py_1()
                            .text_size(px(10.0))
                            .font_weight(FontWeight::BOLD)
                            .bg(gpui::rgb(if attached { NT_DIM } else { NT_SELECT }))
                            .text_color(gpui::rgb(0xffffff)),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            if attached {
                                this.disconnect_vat();
                            } else {
                                this.connect_vat(&vid);
                            }
                            cx.notify();
                        }),
                    )
                    .child(if attached {
                        "disconnect"
                    } else {
                        "connect  ⟶"
                    });
                    col = col.child(
                        dregg_computers::vat_card(&v, attached)
                            .child(div().flex().flex_row().justify_end().child(button)),
                    );
                }
                nt_scroll_face(&sc, col).into_any_element()
            }
        };

        div()
            .id(gpui::SharedString::from(format!(
                "dregg-computers-body-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .child(header)
            .child(tabs)
            .child(body)
            .into_any_element()
    }

    /// **The Provenance Walker window body** — the dark-console chain walk: the
    /// links-verified header, one CLICKABLE row per committed receipt (both links
    /// re-derived by [`provenance_walker::walk_rows`] on every paint — the live
    /// World's truth, never a cache), and the selected receipt's detail face with
    /// the walk verbs: WALK the back-edge, click through to the agent cell's
    /// inspector, GO TO THAT POINT by root-verified replay. This View owns every
    /// listener; the `provenance_walker` module renders only inert facts (the
    /// clobber-safe split, exactly as the Agent Room / World Explorer hold it).
    fn render_provenance_walker_window(
        &mut self,
        cell: CellId,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        use provenance_walker as pw;
        let state = self.provenance_walkers.entry(cell).or_default().clone();
        // The rows and the detail each keep their OWN persistent scroll handle
        // (ordinal-keyed, the tabbed-window discipline).
        let sc_rows =
            self.face_scrolls
                .ensure(FaceScrollKey::Window(cell, WinKindTag::ProvenanceWalker, 0));
        let sc_detail =
            self.face_scrolls
                .ensure(FaceScrollKey::Window(cell, WinKindTag::ProvenanceWalker, 1));

        let w = self.world.borrow();
        // The effects column reads the RECORDED turns (the same call-forest walk
        // the navigator's lineage does) — one summary line per committed receipt,
        // in log order. A receipt with no recorded turn (a symbolic-mode commit
        // the tape skipped) falls back to its action count inside `walk_rows`.
        let effects: Vec<String> = {
            use crate::replay::RecordedStep;
            w.recorded_turns()
                .steps()
                .iter()
                .filter_map(|s| match s {
                    RecordedStep::Committed { turn, .. } => {
                        Some(crate::provenance_navigator::effect_kinds(turn).join(" · "))
                    }
                    _ => None,
                })
                .collect()
        };
        // Genesis-install boundaries (a hire's mid-session seed) are named off
        // the recorded History so a lawful out-of-band root move never paints
        // as a broken chain.
        let reseeded = pw::reseeded_flags(w.recorded_turns());
        let rows = pw::walk_rows(w.receipts(), &effects, &reseeded);
        let height = w.height();

        // The walk cursor: the pinned receipt, else the chain head (the natural
        // start of a walk toward genesis).
        let selected_hash = state
            .selected
            .or_else(|| rows.last().map(|r| r.receipt_hash));
        let selected_row = rows
            .iter()
            .find(|r| Some(r.receipt_hash) == selected_hash)
            .cloned();
        let detail = selected_hash.and_then(|h| crate::provenance_navigator::turn_detail(&w, &h));
        drop(w);

        // ── the row list (the last ~48, newest last — the console-log idiom);
        //    each inert row from the pure module is wrapped in this View's own
        //    listener: click pins the walk cursor there.
        let shown = 48usize;
        let start = rows.len().saturating_sub(shown);
        let mut rows_col = div()
            .id(gpui::SharedString::from(format!(
                "provwalk-rows-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(pw::CONSOLE_BG))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(pw::render_walker_header(&rows, height));
        if start > 0 {
            rows_col = rows_col.child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(pw::CONSOLE_DIM))
                    .child(format!("… {start} earlier receipts above")),
            );
        }
        for row in rows.iter().skip(start) {
            let is_sel = Some(row.receipt_hash) == selected_hash;
            let hash = row.receipt_hash;
            rows_col = rows_col.child(
                div()
                    .id(gpui::SharedString::from(format!(
                        "provwalk-row-{}",
                        row.index
                    )))
                    .px_1()
                    .when(is_sel, |d| d.bg(gpui::rgb(pw::CONSOLE_SEL)))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            let st = this.provenance_walkers.entry(cell).or_default();
                            st.selected = Some(hash);
                            st.landed = None;
                            cx.notify();
                        }),
                    )
                    .child(pw::render_walk_row(row, is_sel)),
            );
        }

        // ── the walk verbs over the selected receipt (this View's listeners).
        let mut verbs = div()
            .flex()
            .flex_row()
            .flex_wrap()
            .gap_1()
            .text_color(gpui::rgb(NT_TEXT));
        if let Some(d) = &detail {
            // WALK — step the cursor one back-edge toward genesis. The landing
            // row re-derives BOTH its links on the repaint: the walk verifies.
            if let Some(prev) = d.previous_receipt {
                verbs = verbs.child(
                    bevel_raised(div().id("provwalk-back").px_2().py_1().text_size(px(10.0)))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                let st = this.provenance_walkers.entry(cell).or_default();
                                st.selected = Some(prev);
                                st.landed = None;
                                this.say(format!(
                                    "Walked the back-edge to receipt {} — its links recompute \
                                     on this very paint.",
                                    pw::hash4(&prev)
                                ));
                                cx.notify();
                            }),
                        )
                        .child(format!("← walk to prev {}", pw::hash4(&prev))),
                );
            }
            // CLICK-THROUGH — the receipt's authoring cell, in its inspector.
            let agent = d.author;
            verbs = verbs.child(
                bevel_raised(
                    div()
                        .id("provwalk-inspect")
                        .px_2()
                        .py_1()
                        .text_size(px(10.0)),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.land_in(agent, WinKindTag::Inspector);
                        this.say(format!(
                            "Inspecting {} — the receipt's authoring cell.",
                            id_short(&agent)
                        ));
                        cx.notify();
                    }),
                )
                .child(format!("inspect agent {}", id_short(&agent))),
            );
            // GO TO THAT POINT — root-verified replay to the receipt's landing.
            let hash = d.receipt_hash;
            verbs = verbs.child(
                bevel_raised(div().id("provwalk-goto").px_2().py_1().text_size(px(10.0)))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.walker_goto(cell, hash);
                            cx.notify();
                        }),
                    )
                    .child("go to that point (root-verified)"),
            );
        }

        // ── the detail face under the rows (its own scroll handle).
        let detail_col = div()
            .id(gpui::SharedString::from(format!(
                "provwalk-detail-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(pw::CONSOLE_BG))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .when_some(
                detail.as_ref().zip(selected_row.as_ref()),
                |d, (det, row)| d.child(pw::render_detail_face(det, row, state.landed.as_ref())),
            );

        div()
            .id(gpui::SharedString::from(format!(
                "provwalk-body-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_FACE_DARK))
            .p_1()
            .child(nt_scroll_face(&sc_rows, rows_col))
            .child(verbs)
            .child(
                div()
                    .h(px(150.0))
                    .flex_none()
                    .flex()
                    .flex_col()
                    .child(nt_scroll_face(&sc_detail, detail_col)),
            )
            .into_any_element()
    }

    /// **GO TO THAT POINT** — run the navigator's root-verified replay to the
    /// receipt's landing ([`crate::provenance_navigator::goto`]) and pin the
    /// verdict on the walker's state for the detail face: the recorded root
    /// tooth, VERIFIED ✓/✗, live-vs-replayed, and the author's then-balance.
    /// Narrated on the receipt console like every other landmark.
    fn walker_goto(&mut self, cell: CellId, hash: [u8; 32]) {
        let note = {
            let w = self.world.borrow();
            crate::provenance_navigator::goto(&w, &hash).map(|g| {
                let author = crate::provenance_navigator::turn_detail(&w, &hash).map(|d| d.author);
                provenance_walker::GotoNote {
                    step: g.step,
                    root: g.root,
                    verified: g.verified,
                    live: g.liveness == crate::ui_snapshot::Liveness::Live,
                    balance_then: author.and_then(|a| g.balance_of(&a)),
                }
            })
        };
        match note {
            Some(n) => {
                self.say(format!(
                    "Went to receipt {} — step {}, root {}, {}.",
                    provenance_walker::hash4(&hash),
                    n.step,
                    provenance_walker::hash4(&n.root),
                    if n.verified {
                        "reconstruction VERIFIED against the recorded tooth"
                    } else {
                        "reconstruction FAILED to verify"
                    }
                ));
                self.provenance_walkers.entry(cell).or_default().landed = Some(n);
            }
            None => self.say("That receipt is not in the recorded history — nothing to go to."),
        }
    }

    /// **The content-IR pane body** — host a real `deos_view::ViewNode` rendered
    /// through deos-view's NATIVE renderer ([`viewnode_pane`] → `deos_view::AppletView`)
    /// as this window's body, BESIDE the native-chrome surfaces. The renderer entity is
    /// created lazily on first render (it needs `cx`) and cached in `viewnode_panes`;
    /// the desktop paints it as a child entity. This is the proof that the native shell
    /// hosts portable-IR content (the same tree a web renderer would render), not just
    /// hand-built native gpui.
    #[cfg(feature = "card-pane")]
    fn render_viewnode_body(
        &mut self,
        cell: CellId,
        scroll: &ScrollHandle,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        // Lazily mint the `AppletView` (deos-view's native renderer) over the static
        // portable card on first render of this window; cache it so reads/turns persist.
        let entity = match self.viewnode_panes.get(&cell).cloned() {
            Some(e) => e,
            None => {
                // The discord-bot surface paints the bot's activity feed as the card
                // (the SAME `ViewNode` shape the bot renders as a Discord embed); every
                // other ViewNodePane is the World-Status panel. Without a live bot the
                // feed is empty (the HTTP `/api/apps/activity/recent` leg is the seam),
                // so the card renders its chrome + "no activity yet".
                let e = if bot_surface::is_bot_surface(&cell) {
                    bot_surface::build_bot_surface_view(cx, &self.bot_activity)
                } else {
                    viewnode_pane::build_viewnode_view(cx)
                };
                self.viewnode_panes.insert(cell, e.clone());
                e
            }
        };
        let face = div()
            .id(gpui::SharedString::from(format!("irbody-{}", id_hex(&cell))))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(if bot_surface::is_bot_surface(&cell) {
                "discord-bot · activity (deos_view::ViewNode -> AppletView · the bot's feed as a desktop card — the SAME card the bot renders as a Discord embed; two faces of one dregg-driven bot)"
            } else if viewnode_pane::is_world_board(&cell) {
                "World Board (deos_view::ViewNode -> AppletView · the confined agent COMPOSED this surface from scratch, reading the live World)"
            } else {
                "World-Status panel (deos_view::ViewNode -> AppletView · a confined agent reflects-on + rewrites it live)"
            }))
            .child(
                // THE IR-RENDERED SURFACE — deos-view's native renderer walks the
                // portable `ViewNode` into real gpui-component widgets (the `bind` reads
                // a live cell slot; the `+1` button fires a verified turn on the embedded
                // ledger). A white panel so the rendered card reads against the NT chrome.
                div()
                    .id(gpui::SharedString::from(format!(
                        "irsurface-{}",
                        id_hex(&cell)
                    )))
                    .flex_1()
                    .min_h(px(120.0))
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .child(entity),
            );
        nt_scroll_face(scroll, face).into_any_element()
    }

    /// Build the Spotter's live query input on first render (a real `gpui-component`
    /// `Input`, focused), with a `Change` subscription that mirrors the text into
    /// `query` + re-ranks, and `PressEnter` that dispatches the top candidate.
    fn ensure_spotter_input(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if self
            .spotter
            .as_ref()
            .map(|s| s.input.is_some())
            .unwrap_or(true)
        {
            return;
        }
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .placeholder("Jump anywhere — or command: transfer 500 to <id> · grant · bump…")
        });
        let sub = cx.subscribe_in(
            &input,
            window,
            |this, input, ev: &InputEvent, _w, cx| match ev {
                InputEvent::Change => {
                    let q = input.read(cx).value().to_string();
                    if let Some(ui) = this.spotter.as_mut() {
                        ui.query = q;
                        ui.selected = 0;
                    }
                    cx.notify();
                }
                InputEvent::PressEnter { .. } => {
                    this.spotter_dispatch(None);
                    cx.notify();
                }
                _ => {}
            },
        );
        input.update(cx, |st, cx| st.focus(window, cx));
        if let Some(ui) = self.spotter.as_mut() {
            ui.input = Some(input);
            ui._sub = Some(sub);
        }
    }

    /// **The Spotter overlay** — a centered NT palette: the live query field over a
    /// ranked candidate list (click a row to jump; Enter takes the top). The single
    /// keystroke that ties every surface together.
    fn render_spotter_overlay(
        &mut self,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        self.ensure_spotter_input(window, cx);
        // The result list scrolls behind a real NT scrollbar; the persistent
        // handle keeps the place while the operator arrows through candidates.
        let sc = self.face_scrolls.ensure(FaceScrollKey::Chrome("spotter"));
        let (input, selected) = match self.spotter.as_ref() {
            Some(ui) => (ui.input.clone(), ui.selected),
            None => (None, 0),
        };
        let ranked = self.spotter_ranked();
        let shown = ranked.len().min(12);
        let rows = spotter::render_spotter_rows(&ranked[..shown], selected);

        let mut list = div().flex().flex_col().gap_1().mt_1();
        for (i, row) in rows.into_iter().enumerate() {
            list = list.child(
                div()
                    .id(gpui::SharedString::from(format!("spotrow-{i}")))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.spotter_dispatch(Some(i));
                            cx.notify();
                        }),
                    )
                    .child(row),
            );
        }

        // The palette panel, centered near the top (the NT/Spotlight position).
        // The panel clamps at 440px; the INNER face (min_h 0 + tracked scroll)
        // scrolls behind the kit scrollbar when the candidate list outgrows it —
        // the same sibling arrangement as `nt_scroll_face`, on the overlay's own
        // max-height geometry.
        div()
            .id("spotter-overlay")
            .absolute()
            .top(px(90.0))
            .left(px(0.0))
            .right(px(0.0))
            .flex()
            .flex_col()
            .items_center()
            .child(
                bevel_window(
                    div()
                        .id("spotter-panel")
                        .w(px(520.0))
                        .max_h(px(440.0))
                        .relative()
                        .flex()
                        .flex_col(),
                )
                .child(
                    div()
                        .id("spotter-scroll")
                        .min_h(px(0.0))
                        .overflow_y_scroll()
                        .track_scroll(&sc)
                        .p_2()
                        .flex()
                        .flex_col()
                        .child(face_section(&format!(
                            "Spotter — {} match(es)",
                            ranked.len()
                        )))
                        .when_some(input, |this, input| {
                            this.child(
                                div()
                                    .my_1()
                                    .h(px(26.0))
                                    .bg(gpui::rgb(0xffffff))
                                    .border_1()
                                    .border_color(gpui::rgb(NT_FACE_DARK))
                                    .child(Input::new(&input).h_full()),
                            )
                        })
                        .child(list),
                )
                .child(nt_scrollbar(&sc)),
            )
            .into_any_element()
    }

    /// **The gentle "type anything" pill** — the calm, always-present face of the
    /// Spotter, pinned just under the menu bar, centered. A newcomer who learns nothing
    /// else learns that words go here and carry them somewhere. Clicking it opens the
    /// full Spotter overlay (the same `open_spotter` the menu/keystroke fire). Pure
    /// presentation + one click listener; it holds no state of its own.
    fn render_spotter_pill(&self, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .absolute()
            .top(px(MENUBAR_H + 12.0))
            .left(px(0.0))
            .right(px(0.0))
            .flex()
            .flex_row()
            .justify_center()
            .child(
                bevel_sunken(
                    div()
                        .id("spotter-pill")
                        .w(px(340.0))
                        .h(px(26.0))
                        .px_3()
                        .flex()
                        .flex_row()
                        .items_center()
                        .gap_2()
                        .bg(gpui::rgb(0xffffff)),
                )
                .hover(|s| s.bg(gpui::rgb(NT_PANEL)))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                        this.open_spotter();
                        cx.notify();
                    }),
                )
                // A font-safe magnifier stand-in (the search affordance), then the warm
                // prompt — never "query", never "command palette".
                .child(
                    div()
                        .text_size(px(12.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child("o-"),
                )
                .child(
                    div()
                        .flex_1()
                        .text_size(px(12.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child("Type anything — jump to a cell, an action, a place"),
                ),
            )
    }

    /// **The warm WELCOME card** — the calm front door over the live image. Shown once
    /// to a never-greeted newcomer: a plain greeting drawn from the REAL world (its cell
    /// count + history height) over a small set of inviting doors (look · find · make ·
    /// survey), each a real desktop gesture in warm words. The model + greeting are the
    /// gpui-free `welcome` submodule; this method renders + wires the click dispatch.
    fn render_welcome_overlay(&self, cx: &mut Context<Self>) -> AnyElement {
        let (cells, height) = {
            let w = self.world.borrow();
            (self.cells.len(), w.height())
        };
        let greeting = welcome::greeting(cells, height);

        // The doors — each a beveled tile with a digit step badge, a warm title, and one
        // plain sentence, wired to dispatch its `WelcomeAction`.
        let mut doors = div().flex().flex_col().gap_2().mt_2();
        for tile in welcome::welcome_tiles() {
            let action = tile.action;
            doors = doors.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "welcome-door-{}",
                            tile.step
                        )))
                        .px_3()
                        .py_2()
                        .flex()
                        .flex_row()
                        .items_center()
                        .gap_3(),
                )
                .hover(|s| s.bg(gpui::rgb(NT_PANEL)))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.welcome_dispatch(action);
                        cx.notify();
                    }),
                )
                // The step badge — a calm navy chip a five-year-old can follow.
                .child(
                    div()
                        .flex_none()
                        .w(px(26.0))
                        .h(px(26.0))
                        .flex()
                        .items_center()
                        .justify_center()
                        .bg(gpui::rgb(NT_TITLE_ACTIVE))
                        .text_color(gpui::rgb(NT_TITLE_TEXT))
                        .text_size(px(14.0))
                        .font_weight(FontWeight::BOLD)
                        .child(tile.step),
                )
                .child(
                    div()
                        .flex_1()
                        .flex()
                        .flex_col()
                        .child(
                            div()
                                .text_size(px(14.0))
                                .font_weight(FontWeight::BOLD)
                                .text_color(gpui::rgb(NT_TEXT))
                                .child(tile.title),
                        )
                        .child(
                            div()
                                .text_size(px(11.0))
                                .text_color(gpui::rgb(NT_LABEL))
                                .child(tile.blurb),
                        ),
                ),
            );
        }

        // The card itself — centered, with breathing room, over a soft scrim that dims
        // (but does not hide) the room behind it.
        div()
            .id("welcome-overlay")
            .absolute()
            .inset_0()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            // A soft scrim — the room is still visible, just resting behind the door.
            .bg(gpui::rgba(0x0a3a4a99))
            .child(
                bevel_window(
                    div()
                        .id("welcome-card")
                        .w(px(560.0))
                        .p_4()
                        .flex()
                        .flex_col()
                        .gap_2(),
                )
                // The title bar — warm, not a system caption.
                .child(
                    div()
                        .flex()
                        .flex_row()
                        .items_center()
                        .child(
                            div()
                                .flex_1()
                                .text_size(px(20.0))
                                .font_weight(FontWeight::BOLD)
                                .text_color(gpui::rgb(NT_TITLE_ACTIVE))
                                .child("Welcome to deos"),
                        )
                        // A quiet close (×) — the same dismiss the footer offers.
                        .child(
                            bevel_raised(
                                div()
                                    .id("welcome-close")
                                    .w(px(22.0))
                                    .h(px(20.0))
                                    .flex()
                                    .items_center()
                                    .justify_center()
                                    .text_size(px(13.0)),
                            )
                            .hover(|s| s.bg(gpui::rgb(NT_PANEL)))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                                    this.dismiss_welcome();
                                    cx.notify();
                                }),
                            )
                            .child(GLYPH_CLOSE),
                        ),
                )
                // The greeting — the live, jargon-free sentence.
                .child(
                    div()
                        .mt_1()
                        .text_size(px(13.0))
                        .text_color(gpui::rgb(NT_TEXT))
                        .child(greeting),
                )
                .child(face_section("Where would you like to begin?"))
                .child(doors)
                // The closing reassurance + the "just let me look" door.
                .child(
                    div()
                        .mt_3()
                        .flex()
                        .flex_row()
                        .items_center()
                        .gap_3()
                        .child(
                            div()
                                .flex_1()
                                .text_size(px(11.0))
                                .text_color(gpui::rgb(NT_DIM))
                                .child(welcome::WELCOME_FOOTER),
                        )
                        .child(
                            bevel_raised(
                                div()
                                    .id("welcome-begin")
                                    .px_3()
                                    .py_1()
                                    .text_size(px(12.0))
                                    .font_weight(FontWeight::BOLD),
                            )
                            .hover(|s| s.bg(gpui::rgb(NT_PANEL)))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                                    this.welcome_dispatch(welcome::WelcomeAction::LookAround);
                                    cx.notify();
                                }),
                            )
                            .child("Just let me look around"),
                        ),
                ),
            )
            .into_any_element()
    }

    /// **The Document Explorer body** — a tabbed Pharo-moldable inspector over a
    /// document's `dregg_doc` faces: the History time-travel scrubber, the DocGraph
    /// atoms+edges, and Blame. Read-only reflection over the live patch substance.
    fn render_doc_explorer_body(
        &self,
        cell: CellId,
        scroll: &ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let state = self.doc_explorers.get(&cell).cloned().unwrap_or_default();
        let doc = self.doc_for_explorer(cell);

        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "docxbody-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1();

        // The tab strip (the NT/Pharo "many faces of one object" selector).
        let mut tabs = div().flex().flex_row().gap_1().my_1();
        for t in DocExplorerTab::ALL {
            let selected = t == state.tab;
            tabs = tabs.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "docxtab-{}-{}",
                            id_hex(&cell),
                            t.label()
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(NT_SELECT)).text_color(gpui::rgb(0xffffff))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.doc_explorers.entry(cell).or_default().tab = t;
                        cx.notify();
                    }),
                )
                .child(t.label()),
            );
        }
        col = col.child(tabs);

        let Some(doc) = doc else {
            return nt_scroll_face(
                scroll,
                col.child(face_row(
                    "(no document)",
                    "Open as Document and type to explore it",
                )),
            )
            .into_any_element();
        };

        let body = match state.tab {
            DocExplorerTab::History => self.render_docx_history(cell, &doc, state.scrub, cx),
            DocExplorerTab::Patches => docgraph_view::render_patch_diff(&doc),
            // The richer node-chain view (boxes + ↓ order + ⑂ forks) supersedes the flat
            // atom list; `render_docx_graph` is retained as the dense fallback.
            DocExplorerTab::Graph => docgraph_view::render_docgraph_nodes(&doc),
            DocExplorerTab::Blame => self.render_docx_blame(&doc),
        };
        nt_scroll_face(scroll, col.child(body)).into_any_element()
    }

    /// The History FACE — the patch-history time-travel scrubber. Each revision is a
    /// clickable row; selecting one replays the document AT that point (`replay_to`),
    /// so you scrub the document's whole evolution. The tip is the live document.
    fn render_docx_history(
        &self,
        cell: CellId,
        doc: &Doc,
        scrub: Option<usize>,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let patches = doc.history().patches();
        let n = patches.len();
        let mut col = div().flex().flex_col().gap_1().child(face_section(&format!(
            "History — {n} patch(es), time-travel"
        )));

        // The revision rows: genesis(0) … tip(n). Clicking sets the scrub cursor.
        let cursor = scrub.unwrap_or(n);
        // 0..=n runs one past `patches` on purpose: i==n is the synthetic "tip" row.
        #[allow(clippy::needless_range_loop)]
        for i in 0..=n {
            let is_tip = i == n;
            let selected = i == cursor;
            let label = if is_tip {
                "● tip (live)".to_string()
            } else {
                let author = patches[i].author.0 & 0xffff;
                format!("rev {i}  ·  @{author}")
            };
            col = col.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "docxrev-{}-{i}",
                            id_hex(&cell)
                        )))
                        .px_2()
                        .py_1()
                        .text_size(px(10.0))
                        .when(selected, |d| {
                            d.bg(gpui::rgb(0xd8d0f0)).font_weight(FontWeight::BOLD)
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        let s = this.doc_explorers.entry(cell).or_default();
                        s.scrub = if is_tip { None } else { Some(i) };
                        cx.notify();
                    }),
                )
                .child(label),
            );
        }

        // The replayed document AT the scrubbed revision (the time-travel payoff).
        let at_text = if cursor >= n {
            doc.text()
        } else {
            let pid = patches[cursor].id();
            let g = content(&doc.history().replay_to(pid));
            g.to_marked_string()
        };
        let preview: String = at_text.chars().take(400).collect();
        col = col.child(face_section(if cursor >= n {
            "Document at tip (live)"
        } else {
            "Document at this revision (replayed)"
        }));
        col.child(
            div()
                .my_1()
                .p_1()
                .min_h(px(60.0))
                .bg(gpui::rgb(0xffffff))
                .border_1()
                .border_color(gpui::rgb(NT_FACE_DARK))
                .text_size(px(10.0))
                .child(if preview.trim().is_empty() {
                    "(empty at this revision)".to_string()
                } else {
                    preview
                }),
        )
        .into_any_element()
    }

    /// The DocGraph FACE — the Pijul graph laid bare: every atom (its id, alive/dead
    /// status, author, content) and the order-edges. Pure structural reflection (the
    /// "inspect the object's guts" Pharo bar) over the document's content-addressed atoms.
    #[allow(dead_code)] // the dense flat-list view, superseded by docgraph_view nodes
    fn render_docx_graph(&self, doc: &Doc) -> AnyElement {
        let graph = doc.history().replay();
        let mut atoms: Vec<_> = graph.atoms().collect();
        atoms.sort_by_key(|a| a.id.0);
        let alive = atoms.iter().filter(|a| a.is_alive()).count();
        let mut col = div().flex().flex_col().gap_1().child(face_section(&format!(
            "DocGraph — {} atom(s), {alive} alive",
            atoms.len()
        )));
        for a in &atoms {
            // ROOT is the sentinel; show it dimmed as the anchor.
            let is_root = a.id.0 == 0;
            let status = if a.is_alive() {
                "alive"
            } else {
                "dead·tombstone"
            };
            let content_preview: String = a.content.chars().take(36).collect();
            let label = if is_root {
                "ROOT (anchor)".to_string()
            } else {
                format!("@{} · {status}", a.provenance.author.0 & 0xffff)
            };
            let succ: Vec<_> = graph.successors(a.id).collect();
            let edge = if succ.is_empty() {
                String::new()
            } else {
                format!("  →{}", succ.len())
            };
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .px_1()
                    .text_size(px(10.0))
                    .when(!a.is_alive(), |d| d.text_color(gpui::rgb(NT_DIM)))
                    .child(
                        div()
                            .w(px(150.0))
                            .child(format!("a{:x}{edge}", (a.id.0 as u64) & 0xffff)),
                    )
                    .child(div().w(px(120.0)).child(label))
                    .child(div().flex_1().child(if content_preview.trim().is_empty() {
                        "·".to_string()
                    } else {
                        content_preview.replace('\n', "⏎")
                    })),
            );
        }
        col.into_any_element()
    }

    /// The Blame FACE — per-line authorship (each live atom attributed to its author +
    /// the patch that introduced it, content-addressed so attribution rides the content),
    /// plus a contributions-by-author tally.
    fn render_docx_blame(&self, doc: &Doc) -> AnyElement {
        let graph = doc.history().replay();
        let lines = blame(&graph);
        let summary = blame_summary(&graph);
        let mut col = div()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(&format!("Blame — {} line(s)", lines.len())));
        for bl in &lines {
            let text: String = bl.content.chars().take(44).collect();
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .px_1()
                    .text_size(px(10.0))
                    .child(
                        div()
                            .w(px(70.0))
                            .text_color(gpui::rgb(0x4040a0))
                            .child(format!("@{}", bl.author.0 & 0xffff)),
                    )
                    .child(div().flex_1().child(if text.trim().is_empty() {
                        "·".to_string()
                    } else {
                        text.replace('\n', "⏎")
                    })),
            );
        }
        col = col.child(face_section("Contributions (by author)"));
        let mut tally: Vec<_> = summary.into_iter().collect();
        tally.sort_by_key(|b| std::cmp::Reverse(b.1));
        if tally.is_empty() {
            col = col.child(face_row(
                "(none)",
                "type into the document to attribute atoms",
            ));
        }
        for (author, count) in tally {
            col = col.child(face_row(
                &format!("@{}", author.0 & 0xffff),
                &format!("{count} atom(s)"),
            ));
        }
        col.into_any_element()
    }

    /// **Backlinks — which cells' documents transclude `cell`.** The reverse scan
    /// over every committed document on the desktop: each cell's umem-heap prose
    /// (falling back to an open editor's live buffer) is parsed line-by-line through
    /// [`parse_transclusion_ref`] and matched against `cell`. This is the ONE source
    /// of two-way-link truth — the Links window's "Backlinks" section, the halo's
    /// "← quoted by N" witness arc ([`Self::render_halo`]), and the
    /// [`Self::bake_doc_links`] back-leg all call it, so the surfaces cannot drift.
    fn backlinks_of(&self, cell: CellId) -> Vec<CellId> {
        backlinks_in(
            cell,
            self.cells.iter().map(|other| {
                let prose = self
                    .read_doc_from_heap(other)
                    .or_else(|| {
                        self.windows
                            .get(&(*other, WinKindTag::DocEditor))
                            .and_then(|w| match &w.kind {
                                WinKind::DocEditor { buffer, .. } => Some(buffer.clone()),
                                _ => None,
                            })
                    })
                    .unwrap_or_default();
                (*other, prose)
            }),
        )
    }

    /// **The links / backlinks body** — which cells this one reaches (its caps),
    /// which transclusions are composed into it, and the World's reach.
    fn render_links_body(&self, cell: CellId, scroll: &ScrollHandle) -> AnyElement {
        let caps = self.cell_cap_count(&cell);
        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "linksbody-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Outbound (capabilities)"))
            .child(face_row("cap count", &caps.to_string()));
        // ── Composed-in: transclusions this cell's document reaches. Each line is
        //    parsed back to a STRUCTURED reference and the referenced cell's LIVE faces
        //    (kind · balance · lifecycle) are re-read off the ledger — so a backlink
        //    reflects the target's current state, not the stale text snapshot. ──
        let doc = self.load_doc_buffer(cell);
        let outbound: Vec<CellId> = doc.lines().filter_map(parse_transclusion_ref).collect();
        col = col.child(face_section("Composed-in (transclusions →)"));
        if outbound.is_empty() {
            col = col.child(face_row(
                "transclusions",
                "(none — drag a cell onto its doc)",
            ));
        } else {
            for tgt in &outbound {
                if self.world.borrow().ledger().get(tgt).is_some() {
                    col = col.child(face_row(
                        &format!("→ {}", id_short(tgt)),
                        &format!(
                            "{} · {} · {}",
                            self.cell_kind(tgt),
                            fmt_balance(self.cell_balance(tgt)),
                            self.cell_lifecycle(tgt),
                        ),
                    ));
                } else {
                    col = col.child(face_row(&format!("→ {}", id_short(tgt)), "(no such cell)"));
                }
            }
        }

        // ── Backlinks: which OTHER cells' documents transclude THIS one — the SAME
        //    `backlinks_of` reverse scan the halo's "← quoted by N" witness arc reads
        //    (one truth, two surfaces) — "what points here". ──
        let backlinks = self.backlinks_of(cell);
        col = col.child(face_section("Backlinks (← mentions this)"));
        if backlinks.is_empty() {
            col = col.child(face_row("backlinks", "(none point here yet)"));
        } else {
            for src in &backlinks {
                col = col.child(face_row(
                    &format!("← {}", id_short(src)),
                    &format!("{} mentions this", self.cell_kind(src)),
                ));
            }
        }

        col = col
            .child(face_section("World"))
            .child(face_row("cells", &self.cells.len().to_string()))
            .child(face_row(
                "height",
                &self.world.borrow().height().to_string(),
            ));
        nt_scroll_face(scroll, col).into_any_element()
    }

    /// **The transcript / receipt-log body** — the World's receipt chain, the
    /// chronicle the user's "do it"s have written, UNCAPPED and tail-following.
    ///
    /// Was a hard-capped tail (the last ~24 receipts eagerly built into the tree);
    /// now the WHOLE log rides `gpui_component::v_virtual_list` so only the visible
    /// rows are ever built and the log is unbounded. The View owns the list state
    /// (the persistent [`VirtualListScrollHandle`] in `virtual_faces`, keyed like
    /// the flat transcript face was); the row renderer stays a pure free function
    /// ([`transcript_row`]) the closure calls over the LIVE receipt slice at paint
    /// time — the live World's truth, never a snapshot. `follow_tail` keeps the
    /// freshest receipt in view as the pulse lands turns (`tail -f`).
    ///
    /// (`&mut self` for the virtual-face registry; `cx` for `cx.entity()`, the
    /// view handle `v_virtual_list` re-enters to build the visible range. `cell`
    /// keys the window's own list state + element id, so two transcript windows
    /// scroll and tail-follow independently.)
    fn render_transcript_body(&mut self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        let (n, height) = {
            let w = self.world.borrow();
            (w.receipts().len(), w.height())
        };
        let key = FaceScrollKey::Window(cell, WinKindTag::Transcript, 0);
        let list_id = gpui::SharedString::from(format!("transcript-list-{}", id_hex(&cell)));
        let header = div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
            "── World receipt log · {n} turns · height {height} "
        ));
        let body = if n == 0 {
            div()
                .child("(no turns yet — actuate a cell)")
                .into_any_element()
        } else {
            self.nt_virtual_face(
                key,
                list_id,
                n,
                TRANSCRIPT_ROW_H,
                true,
                cx,
                |this, range, _w, _cx| {
                    let w = this.world.borrow();
                    let receipts = w.receipts();
                    range
                        .filter_map(|i| receipts.get(i).map(|r| transcript_row(i, r)))
                        .collect()
                },
            )
        };
        div()
            .id("transcript-body")
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(0x101820))
            .text_color(gpui::rgb(0x9fe0a0))
            .p_2()
            .child(header)
            .child(body)
            .into_any_element()
    }

    /// **The UNCAP primitive** — assemble one virtualized, NT-chromed log face.
    ///
    /// This is the shared spine every uncapped face rides: it mounts a
    /// `gpui_component::v_virtual_list` over `count` uniform `row_h`-tall rows —
    /// so only the visible window is ever built, and `count` is unbounded — and
    /// pairs it with the desktop's always-visible NT scrollbar
    /// ([`chrome::nt_scrollbar`]) tracking the SAME handle's `base_handle()`, so a
    /// virtualized face wears exactly the chrome the flat faces did (the kit sizes
    /// the thumb off the whole virtual content, not the rendered slice).
    ///
    /// The list STATE is the View's: the persistent [`VirtualListScrollHandle`]
    /// lives in `virtual_faces` keyed by `key`, so scroll position (and, for
    /// `follow`-ing faces, the tail cursor) survives repaints and reopens exactly
    /// like the flat faces' positions did. The ROW renderer stays pure: `build`
    /// is a `'static` closure the kit re-enters with `&mut self` and the visible
    /// `range`, pulling live rows for just those indices (live-World truth, never
    /// a snapshot). When `follow` is set, a grown `count` defers a scroll to the
    /// new tail (`tail -f`); an id-sorted census passes `follow = false` and keeps
    /// its place.
    ///
    /// The returned wrapper is the flexing body slot (`flex_1` / `min_h(0)`) — mount
    /// it under a face's pinned header, the way [`render_transcript_body`] does.
    fn nt_virtual_face<F>(
        &mut self,
        key: FaceScrollKey,
        list_id: impl Into<gpui::ElementId>,
        count: usize,
        row_h: f32,
        follow: bool,
        cx: &mut Context<Self>,
        build: F,
    ) -> AnyElement
    where
        F: 'static
            + Fn(
                &mut Self,
                std::ops::Range<usize>,
                &mut Window,
                &mut Context<Self>,
            ) -> Vec<AnyElement>,
    {
        let handle: VirtualListScrollHandle = self.virtual_faces.ensure(key);
        if follow {
            // tail -f: a landing receipt (a grown count) snaps the viewport to the
            // fresh tail; an unchanged count leaves the operator's scroll alone.
            self.virtual_faces.follow_tail(key, count);
        }
        // One uniform-height entry per row — the kit's per-item size table. Cheap
        // O(count) scalars vs. the O(count) ELEMENTS the flat face used to build.
        let sizes = Rc::new(vec![gpui::size(px(0.0), px(row_h)); count]);
        let list = v_virtual_list(cx.entity(), list_id, sizes, build)
            .track_scroll(&handle)
            .size_full();
        div()
            .relative()
            .flex_1()
            .min_h(px(0.0))
            .child(list)
            .child(nt_scrollbar(handle.base_handle()))
            .into_any_element()
    }

    fn render_titlebar(
        &self,
        key: WinKey,
        title: &str,
        active: bool,
        minimized: bool,
        cx: &mut Context<Self>,
    ) -> Stateful<Div> {
        let (cell, tag) = key;
        // A font-safe 3-letter kind badge (the geometric window glyphs render as tofu
        // in the bake font, so the dense legible tag stands in for them).
        let glyph = kind_short(tag);
        // The FOCUSED window wears the navy active bar; the rest read inactive-gray
        // (the NT focus cue — one window is "the one you're working in").
        let (bar_bg, bar_text) = if active {
            (NT_TITLE_ACTIVE, NT_TITLE_TEXT)
        } else {
            (NT_TITLE_INACTIVE, NT_TITLE_INACTIVE_TEXT)
        };
        // NT title bar with min/max/close glyph buttons. The bar grabs a window-move
        // drag on mouse-down; the buttons fire close/minimize.
        div()
            .id(gpui::SharedString::from(format!(
                "title-{}-{:?}",
                id_hex(&cell),
                tag as u8
            )))
            .h(px(22.0))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(bar_bg))
            .text_color(gpui::rgb(bar_text))
            .px_1()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&key) {
                        this.drag = Some(Drag::WinMove {
                            key,
                            grab: Point::new(ev.position.x - px(ws.x), ev.position.y - px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            // Right-click the title bar → the deep WINDOW menu.
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: Some(cell),
                        heading: format!("{} {}", glyph, id_short(&cell)),
                        at: ev.position,
                        actions: this.window_actions(cell, tag),
                    });
                    cx.notify();
                }),
            )
            .child(
                div()
                    .mx_1()
                    .px_1()
                    .text_size(px(9.0))
                    .bg(gpui::rgb(0x000050))
                    .text_color(gpui::rgb(0xc0d0ff))
                    .child(glyph),
            )
            .child(
                div()
                    .flex_1()
                    .px_1()
                    .text_size(px(11.0))
                    .font_weight(FontWeight::BOLD)
                    .child(title.to_string()),
            )
            // A live status badge for document windows — the receipt landing in the
            // title bar as you type (rev · patches · saved✓), read off committed state.
            .when(tag == WinKindTag::DocEditor, |row| {
                let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
                let patches = match self
                    .windows
                    .get(&(cell, WinKindTag::DocEditor))
                    .map(|w| &w.kind)
                {
                    Some(WinKind::DocEditor { doc, .. }) => doc.history().len(),
                    _ => 0,
                };
                row.child(
                    div()
                        .mx_1()
                        .px_1()
                        .text_size(px(9.0))
                        .bg(gpui::rgb(0x0a3a14))
                        .text_color(gpui::rgb(0x9fe0a8))
                        .child(format!("rev {rev} · {patches}¶ · heap✓")),
                )
            })
            .child(self.title_btn(key, GLYPH_MIN, TitleBtn::Minimize, cx))
            .child(self.title_btn(
                key,
                if minimized { GLYPH_RESTORE } else { GLYPH_MAX },
                TitleBtn::Maximize,
                cx,
            ))
            .child(self.title_btn(key, GLYPH_CLOSE, TitleBtn::Close, cx))
    }

    fn title_btn(
        &self,
        key: WinKey,
        glyph: &str,
        which: TitleBtn,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let (cell, tag) = key;
        let glyph = glyph.to_string();
        div()
            .id(gpui::SharedString::from(format!(
                "titlebtn-{}-{:?}-{glyph}",
                id_hex(&cell),
                tag as u8
            )))
            .ml_1()
            .w(px(16.0))
            .h(px(14.0))
            .flex()
            .items_center()
            .justify_center()
            .bg(gpui::rgb(NT_FACE))
            .text_color(gpui::rgb(NT_TEXT))
            .text_size(px(9.0))
            .border_1()
            .border_color(gpui::rgb(NT_SHADOW))
            .hover(|s| s.bg(gpui::rgb(NT_FACE_DARK)))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    // Swallow the title-drag the parent bar would otherwise start, and
                    // perform the window-control action.
                    this.drag = None;
                    match which {
                        TitleBtn::Close => this.close_window(key),
                        TitleBtn::Minimize => {
                            if let Some(ws) = this.windows.get_mut(&key) {
                                ws.minimized = true;
                            }
                            this.persist_window(key);
                        }
                        TitleBtn::Maximize => {
                            if let Some(ws) = this.windows.get_mut(&key) {
                                ws.minimized = false;
                            }
                            this.persist_window(key);
                        }
                    }
                    cx.notify();
                }),
            )
            .child(glyph)
    }

    /// A title-bar action wired through the desktop (close/min uses a click handler
    /// on the wrapping element; broken out so the drag handler can sit on the bar).
    fn affordance_button(
        &self,
        cell: CellId,
        label: &str,
        kind: ActionKind,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let held = match &kind {
            ActionKind::Transfer { amount } => {
                self.holds(&cell) && self.cell_balance(&cell) >= *amount as i64
            }
            _ => self.holds(&cell),
        };
        let kind2 = kind.clone();
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "aff-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .when(!held, |d| d.opacity(0.5).text_color(gpui::rgb(NT_DIM)))
        .when(held, |d| {
            d.on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.actuate(cell, &kind2);
                    cx.notify();
                }),
            )
        })
        .child(label.to_string())
    }

    fn render_context_menu(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menu = self.open_menu.as_ref().unwrap();
        let cell = menu.cell;
        let heading = menu.heading.clone();
        let key_base = cell.map(|c| id_hex(&c)).unwrap_or_else(|| "desktop".into());
        let mut m = bevel_window(
            div()
                .absolute()
                .left(menu.at.x)
                .top(menu.at.y)
                .w(px(268.0))
                .py_1()
                .flex()
                .flex_col(),
        );
        // A header naming the object the menu acts on.
        m = m.child(
            div()
                .px_2()
                .py_1()
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(NT_TITLE_ACTIVE))
                .border_b_1()
                .border_color(gpui::rgb(NT_FACE_DARK))
                .child(heading),
        );
        for (i, action) in menu.actions.iter().enumerate() {
            if action.separator {
                m = m.child(div().mx_2().my_1().h(px(1.0)).bg(gpui::rgb(NT_FACE_DARK)));
                continue;
            }
            let kind = action.kind.clone();
            let held = action.held;
            let row = div()
                .id(gpui::SharedString::from(format!("ctx-{key_base}-{i}")))
                .px_3()
                .py_1()
                .text_size(px(12.0))
                .when(!held, |d| d.opacity(0.45).text_color(gpui::rgb(NT_DIM)))
                .when(held, |d| {
                    d.hover(|s| {
                        s.bg(gpui::rgb(NT_SELECT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            match cell {
                                Some(c) => this.actuate(c, &kind),
                                None => this.actuate_desktop(&kind),
                            }
                            this.open_menu = None;
                            cx.notify();
                        }),
                    )
                })
                .child(action.label.clone());
            m = m.child(row);
        }
        m
    }

    /// **The property inspector/editor dialog** — an NT property sheet over a cell, a
    /// window, or the desktop. Cell properties are EDITABLE via receipted `SetField`
    /// turns; window/desktop properties are persisted layout changes.
    fn render_property_dialog(&mut self, cx: &mut Context<Self>) -> AnyElement {
        // (`&mut self` for the face-scroll registry: the scrolling dialog bodies
        // keep persistent handles keyed per subject.)
        let (x, y, w, h, subject) = {
            let dlg = self.open_prop.as_ref().unwrap();
            (dlg.at.x, dlg.at.y, dlg.w, dlg.h, dlg.subject.clone())
        };
        let (heading, body) = match subject {
            PropSubject::Cell(cell) => {
                let sc = self
                    .face_scrolls
                    .ensure(FaceScrollKey::CellChrome("props-cell", cell));
                (
                    format!("Properties — {} {}", self.cell_kind(&cell), id_short(&cell)),
                    self.prop_body_cell(cell, &sc, cx),
                )
            }
            PropSubject::Window(cell, tag) => (
                format!("Window Properties — {}", id_short(&cell)),
                self.prop_body_window(cell, tag, cx),
            ),
            PropSubject::Desktop => {
                let sc = self
                    .face_scrolls
                    .ensure(FaceScrollKey::Chrome("props-desktop"));
                (
                    "Desktop Preferences & Customize".to_string(),
                    self.prop_body_desktop(&sc, cx),
                )
            }
        };
        bevel_window(
            div()
                .id("prop-dialog")
                .absolute()
                .left(x)
                .top(y)
                .w(px(w))
                .h(px(h))
                .flex()
                .flex_col()
                .p_px(),
        )
        .child(
            // The dialog title bar (with a close X).
            div()
                .h(px(22.0))
                .flex()
                .flex_row()
                .items_center()
                .bg(gpui::rgb(NT_TITLE_ACTIVE))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
                .px_1()
                .child(
                    div()
                        .mx_1()
                        .px_1()
                        .text_size(px(9.0))
                        .bg(gpui::rgb(0x000050))
                        .text_color(gpui::rgb(0xc0d0ff))
                        .child("CFG"),
                )
                .child(
                    div()
                        .flex_1()
                        .px_1()
                        .text_size(px(11.0))
                        .font_weight(FontWeight::BOLD)
                        .child(heading),
                )
                .child(
                    div()
                        .id("prop-close")
                        .w(px(16.0))
                        .h(px(14.0))
                        .flex()
                        .items_center()
                        .justify_center()
                        .bg(gpui::rgb(NT_FACE))
                        .text_color(gpui::rgb(NT_TEXT))
                        .text_size(px(9.0))
                        .border_1()
                        .border_color(gpui::rgb(NT_SHADOW))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                                this.open_prop = None;
                                cx.notify();
                            }),
                        )
                        .child(GLYPH_CLOSE),
                ),
        )
        .child(body)
        .into_any_element()
    }

    fn prop_body_cell(
        &self,
        cell: CellId,
        scroll: &ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let bal = self.cell_balance(&cell);
        let nonce = self.cell_nonce(&cell);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let face = div()
            .id(gpui::SharedString::from(format!(
                "propcell-{}",
                id_hex(&cell)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Read-only"))
            .child(face_row("id", &id_hex(&cell)))
            .child(face_row("kind", self.cell_kind(&cell)))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row("lifecycle", &self.cell_lifecycle(&cell)))
            .child(face_section("Editable (receipted SetField turn)"))
            .child(face_row("field[14] revision", &rev.to_string()))
            // The property-edit controls: each is a verified turn.
            .child(self.prop_setfield_button(cell, "revision +1", DOC_REV_SLOT, rev + 1, cx))
            .child(self.prop_setfield_button(cell, "revision =0", DOC_REV_SLOT, 0, cx))
            .child(self.prop_setfield_button(cell, "field[13] =42", 13, 42, cx));
        nt_scroll_face(scroll, face).into_any_element()
    }

    fn prop_setfield_button(
        &self,
        cell: CellId,
        label: &str,
        index: usize,
        value: u64,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let held = self.holds(&cell);
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "propset-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .when(!held, |d| d.opacity(0.5).text_color(gpui::rgb(NT_DIM)))
        .when(held, |d| {
            d.on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.actuate(cell, &ActionKind::SetField { index, value });
                    cx.notify();
                }),
            )
        })
        .child(label.to_string())
    }

    fn prop_body_window(
        &self,
        cell: CellId,
        tag: WinKindTag,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let geom = self
            .windows
            .get(&(cell, tag))
            .map(|w| (w.x, w.y, w.w, w.h))
            .unwrap_or((0.0, 0.0, 0.0, 0.0));
        let _ = cx;
        div()
            .flex_1()
            .min_h(px(0.0))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Window (persisted layout)"))
            .child(face_row("x", &format!("{:.0}", geom.0)))
            .child(face_row("y", &format!("{:.0}", geom.1)))
            .child(face_row("w", &format!("{:.0}", geom.2)))
            .child(face_row("h", &format!("{:.0}", geom.3)))
            .into_any_element()
    }

    /// **The desktop Preferences body — customization.** Toggling these persists to
    /// the layout sidecar (a pure layout change: appearance/behaviour, no authority).
    fn prop_body_desktop(&self, scroll: &ScrollHandle, cx: &mut Context<Self>) -> AnyElement {
        let p = &self.layout.prefs;
        let face = div()
            .id("propdesktop")
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Appearance"))
            .child(face_row("background", &format!("#{:06x}", p.bg)))
            // The background palette — clicking a swatch persists it.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .my_1()
                    .child(self.pref_swatch(NT_DESKTOP_BG, cx))
                    .child(self.pref_swatch(0x202830, cx))
                    .child(self.pref_swatch(0x2a1a3a, cx))
                    .child(self.pref_swatch(0x103020, cx)),
            )
            .child(face_section("Behaviour"))
            .child(self.pref_toggle(
                "Show icon balances",
                p.show_balances,
                PrefToggle::Balances,
                cx,
            ))
            .child(self.pref_toggle(
                "Word-granularity doc edits",
                p.word_granularity,
                PrefToggle::WordGran,
                cx,
            ))
            .child(face_row("grid rows", &p.grid_rows.to_string()))
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .my_1()
                    .child(self.pref_rows_button(4, cx))
                    .child(self.pref_rows_button(6, cx))
                    .child(self.pref_rows_button(8, cx)),
            );
        nt_scroll_face(scroll, face).into_any_element()
    }

    fn pref_swatch(&self, color: u32, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = self.layout.prefs.bg == color;
        div()
            .id(gpui::SharedString::from(format!("swatch-{color:06x}")))
            .w(px(28.0))
            .h(px(20.0))
            .bg(gpui::rgb(color))
            .border_2()
            .border_color(gpui::rgb(if selected { NT_HILIGHT } else { NT_SHADOW }))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.layout.prefs.bg = color;
                    this.layout.save(&this.layout_path);
                    this.status = format!("Desktop background → #{color:06x} (persisted).");
                    cx.notify();
                }),
            )
    }

    fn pref_toggle(
        &self,
        label: &str,
        on: bool,
        which: PrefToggle,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!("pref-{label}")))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                match which {
                    PrefToggle::Balances => {
                        this.layout.prefs.show_balances = !this.layout.prefs.show_balances
                    }
                    PrefToggle::WordGran => {
                        this.layout.prefs.word_granularity = !this.layout.prefs.word_granularity
                    }
                }
                this.layout.save(&this.layout_path);
                cx.notify();
            }),
        )
        .child(format!("[{}] {label}", if on { "✓" } else { " " }))
    }

    fn pref_rows_button(&self, rows: u32, cx: &mut Context<Self>) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!("rows-{rows}")))
                .px_2()
                .py_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.layout.prefs.grid_rows = rows;
                this.layout.save(&this.layout_path);
                cx.notify();
            }),
        )
        .child(format!("{rows} rows"))
    }

    fn render_statusbar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let h = self.world.borrow().height();
        let unread = self.status_unread;
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .bottom(px(0.0))
            .w_full()
            .h(px(22.0))
            .flex()
            .flex_row()
            .items_center()
            .px_2()
            .bg(gpui::rgb(NT_FACE))
            .border_t_2()
            .border_color(gpui::rgb(NT_HILIGHT))
            .text_size(px(11.0))
            .text_color(gpui::rgb(NT_TEXT))
            // The narration line — click to open/close the RECEIPT CONSOLE flyout
            // (the session's full `say()` log; the bar shows only the latest line).
            .child(
                div()
                    .id("statusbar-narration")
                    .flex_1()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                            this.status_flyout = !this.status_flyout;
                            if this.status_flyout {
                                this.status_unread = 0;
                            }
                            cx.notify();
                        }),
                    )
                    .child(self.status.clone()),
            );
        // The unread chip — narration said while the console was closed.
        if unread > 0 && !self.status_flyout {
            bar = bar.child(
                div()
                    .px_2()
                    .text_color(gpui::rgb(NT_WARN))
                    .child(format!("⋯ {unread} new")),
            );
        }
        // The height "tray" (the NT clock corner) — click lands in the World
        // Transcript: the receipts are one click from anywhere, always.
        bar.child(
            div()
                .id("statusbar-height-chip")
                .px_2()
                .border_l_1()
                .border_color(gpui::rgb(NT_FACE_DARK))
                .text_color(gpui::rgb(0x303030))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                        this.land_in(this.user, WinKindTag::Transcript);
                        cx.notify();
                    }),
                )
                .child(format!("World height {h}")),
        )
    }

    /// **The RECEIPT CONSOLE flyout** — the session's FULL narration log (every
    /// `say()` line, newest last), anchored above the status bar in the
    /// transcript's dense dark-console style. The bar's one line stops being the
    /// only witness; the story scrolls.
    ///
    /// Was the newest-24-of-64 peephole (only the last 24 lines built, the ring
    /// itself bounded at 64). Now the WHOLE [`STATUS_LOG_CAP`] ring rides
    /// `v_virtual_list` through [`nt_virtual_face`], so every retained line is
    /// reachable behind the same NT scrollbar, and the console `follow_tail`s —
    /// a fresh `say()` snaps the newest line into view. The flyout height tracks
    /// the log (one row each) up to a cap so a short session shrinks to fit and a
    /// long one scrolls; `follow = true` keeps the tail live either way.
    ///
    /// (`&mut self`/`cx`: the virtual list is View-owned, like every uncapped
    /// face — see [`nt_virtual_face`].)
    fn render_status_console(&mut self, cx: &mut Context<Self>) -> impl IntoElement {
        let n = self.status_log.len();
        let key = FaceScrollKey::Chrome("status-console");
        let header = div()
            .px_2()
            .pt_2()
            .pb_1()
            .text_color(gpui::rgb(0x6fc0ff))
            .child(format!(
                "── receipt console · {n} line(s) · click the bar to close "
            ));
        // The list area grows one row per line up to a ceiling, so a short session
        // shrinks to fit and a long one scrolls; the flyout is header + that area.
        let list_h = (n as f32 * STATUS_ROW_H).clamp(STATUS_ROW_H, 260.0);
        let body = if n == 0 {
            div()
                .p_2()
                .child("(nothing said yet — the console is quiet)")
                .into_any_element()
        } else {
            self.nt_virtual_face(
                key,
                "status-console-list",
                n,
                STATUS_ROW_H,
                true,
                cx,
                |this, range, _w, _cx| {
                    range
                        .filter_map(|i| this.status_log.get(i).map(|line| console_row(line)))
                        .collect()
                },
            )
        };
        div()
            .absolute()
            .left(px(8.0))
            .bottom(px(50.0))
            .w(px(560.0))
            .h(px(list_h + 34.0))
            .bg(gpui::rgb(0x101820))
            .text_color(gpui::rgb(0x9fe0a0))
            .border_2()
            .border_color(gpui::rgb(NT_FACE_DARK))
            .flex()
            .flex_col()
            .child(header)
            .child(body)
    }

    /// **The taskbar** — a row of stubs for every open window, just above the status
    /// bar (the NT taskbar). Each stub names the window and click-focuses it; a
    /// minimized window's stub reads dimmed. Pure view-state over `self.windows`.
    fn render_taskbar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| (self.windows[k].minimized, self.windows[k].z));
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .bottom(px(22.0))
            .w_full()
            .h(px(24.0))
            .flex()
            .flex_row()
            .items_center()
            .gap_1()
            .px_1()
            .bg(gpui::rgb(NT_FACE))
            .border_t_1()
            .border_color(gpui::rgb(NT_FACE_DARK));
        // A leading "Windows" caption (the taskbar's system corner).
        bar = bar.child(
            div()
                .px_2()
                .h(px(20.0))
                .flex()
                .items_center()
                .bg(gpui::rgb(NT_FACE_DARK))
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .child(format!("{} open", keys.len())),
        );
        for key in keys {
            let (cell, tag) = key;
            let ws = &self.windows[&key];
            let min = ws.minimized;
            // Font-safe label: the cell id + the 3-letter kind tag (no tofu glyph).
            let label = format!("{} · {}", id_short(&cell), kind_short(tag));
            bar = bar.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "task-{}-{:?}",
                            id_hex(&cell),
                            tag as u8
                        )))
                        .h(px(20.0))
                        .px_2()
                        .flex()
                        .items_center()
                        .text_size(px(10.0)),
                )
                .when(min, |d| d.opacity(0.55))
                .hover(|s| s.bg(gpui::rgb(NT_FACE_DARK)))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.focus_window(key);
                        cx.notify();
                    }),
                )
                .child(label),
            );
        }
        bar
    }

    /// **The World-summary widget** — a small NT info panel pinned to the desktop's
    /// top-right, reflecting the live World invariants: height, cell count, total
    /// receipts, and the conservation sum (Σ balance, the net of issuer wells vs.
    /// accounts). Read-only over the live ledger; it fills the empty right margin and
    /// teaches the invariant at a glance. The sum is INVARIANT under value-conserving
    /// turns (transfers move value, they do not create it), so the widget's headline
    /// is its stability, shown as the constant net.
    fn render_world_widget(&self) -> impl IntoElement {
        let (h, n, receipts) = {
            let w = self.world.borrow();
            (w.height(), self.cells.len(), w.receipts().len())
        };
        let sum = self.world_balance_sum();
        bevel_window(
            div()
                .absolute()
                .right(px(16.0))
                .top(px(MENUBAR_H + 12.0))
                .w(px(216.0))
                .flex()
                .flex_col(),
        )
        .child(
            div()
                .h(px(20.0))
                .flex()
                .items_center()
                .px_2()
                .bg(gpui::rgb(NT_TITLE_ACTIVE))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
                .text_size(px(11.0))
                .font_weight(FontWeight::BOLD)
                .child("World"),
        )
        .child(
            div()
                .p_2()
                .flex()
                .flex_col()
                .gap_1()
                .child(face_row("height", &h.to_string()))
                .child(face_row("cells", &n.to_string()))
                .child(face_row("receipts", &receipts.to_string()))
                .child(face_row_color("Σ balance", &fmt_balance(sum), 0x0a4a7a))
                .child(
                    div()
                        .mt_1()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child("net of wells vs accounts — invariant under transfers"),
                ),
        )
    }
}

// (`kind_short` — the 3-letter window-kind tag the taskbar stubs and the Spotter's
// row badges share — moved into `chrome.rs` beside `kind_glow`, re-exported above.)

#[derive(Clone, Copy)]
enum TitleBtn {
    Minimize,
    Maximize,
    Close,
}

/// A document COLLABORATION gesture (the branch/stitch surface of the doc editor).
#[derive(Clone, Copy)]
enum DocCollabAct {
    /// Fork a confined co-author draft branch of the document.
    Fork,
    /// Author a divergent edit on the draft branch (as a second author).
    Diverge,
    /// Stitch the draft branch into the document (the pushout) — may conflict.
    Stitch,
}

/// Which boolean preference a desktop-Preferences toggle flips.
#[derive(Clone, Copy)]
enum PrefToggle {
    Balances,
    WordGran,
}

// (Small render helpers — `face_section` / `face_row` / `fmt_balance` / `group` —
// live in `chrome.rs` and are imported at the top of this module.)

// ── Unit tests for the pure two-way-link core (gpui-free) ──────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// The exact line shape `transclude_into` composes (id · kind · balance · life).
    fn quote_line(target: &CellId) -> String {
        format!(
            "{{transclude dregg://{} · token · balance 500 · Live}}",
            id_hex(target)
        )
    }

    #[test]
    fn parse_transclusion_ref_roundtrips_the_compose_line() {
        let target = cid(7);
        assert_eq!(
            parse_transclusion_ref(&quote_line(&target)),
            Some(target),
            "the compose line parses back to the STRUCTURED reference it quotes"
        );
        // Plain prose — and a truncated (non-64-hex) dregg:// id — parse to nothing.
        assert_eq!(parse_transclusion_ref("plain prose line"), None);
        assert_eq!(
            parse_transclusion_ref("{transclude dregg://abcd · token}"),
            None
        );
    }

    #[test]
    fn backlinks_in_inverts_the_quote() {
        let here = cid(1);
        let quoter = cid(2);
        let silent = cid(3);
        let docs = vec![
            (
                quoter,
                format!("prose above\n{}\nprose below", quote_line(&here)),
            ),
            (silent, "no transclusions at all".to_string()),
            // A cell quoting ITSELF is not a backlink (the Links window skips it too).
            (here, quote_line(&here)),
        ];
        assert_eq!(
            backlinks_in(here, docs),
            vec![quoter],
            "only the OTHER document that quotes `here` comes back"
        );
    }

    #[test]
    fn backlinks_in_finds_every_quoter_in_desktop_order() {
        let here = cid(9);
        let a = cid(10);
        let b = cid(11);
        let docs = vec![
            (a, quote_line(&here)),
            // A document quoting several cells still backlinks each exactly once.
            (
                b,
                format!("{}\n{}", quote_line(&cid(12)), quote_line(&here)),
            ),
        ];
        assert_eq!(backlinks_in(here, docs), vec![a, b]);
        assert!(
            backlinks_in(cid(13), vec![(a, quote_line(&here))]).is_empty(),
            "a cell nobody quotes has no backlinks"
        );
    }

    /// A synthetic receipt whose glyphs encode its index — so a row's text
    /// witnesses WHICH receipt it drew.
    fn receipt(i: u32) -> dregg_turn::turn::TurnReceipt {
        dregg_turn::turn::TurnReceipt {
            turn_hash: [i as u8; 32],
            post_state_hash: [(i >> 8) as u8; 32],
            agent: cid((i % 200) as u8),
            computrons_used: i as u64,
            ..Default::default()
        }
    }

    /// **THE UNCAP, witnessed at 10k.** The flat Chronicle hard-stopped at 24
    /// rows; the virtualized face pairs `virtual_face::visible_row_range` (the kit's
    /// uniform-height scan) with the pure `world_explorer::chronicle_row_text`, so
    /// over a 10k-receipt log it (a) builds only the visible window — never the
    /// whole log — and (b) draws the CORRECT receipts at any offset, including the
    /// tail. This is the bake hook: correct rows at offset N with 10k receipts.
    #[test]
    fn virtualized_chronicle_shows_correct_rows_at_offset_over_10k() {
        let receipts: Vec<dregg_turn::turn::TurnReceipt> = (0u32..10_000).map(receipt).collect();
        let row_h = world_explorer::CHRONICLE_ROW_H;
        let viewport = 360.0;
        let n = receipts.len();

        // Parked at the TOP: only the head window is built (virtual, not eager),
        // and it starts at row 0.
        let top = virtual_face::visible_row_range(n, row_h, viewport, 0.0);
        assert_eq!(top.start, 0);
        assert!(
            top.len() < 30,
            "top window is virtualized: {} rows",
            top.len()
        );
        assert!(world_explorer::chronicle_row_text(0, &receipts[0]).contains("#0"));

        // Scroll so row 5000 tops the viewport — the window is the rows AT that
        // offset (local, not the head, not the whole log), and each reads its OWN
        // receipt.
        let off = -(5000.0 * row_h);
        let mid = virtual_face::visible_row_range(n, row_h, viewport, off);
        assert_eq!(mid.start, 5000, "first visible is the row at the offset");
        let row = world_explorer::chronicle_row_text(mid.start, &receipts[mid.start]);
        assert!(
            row.contains("#5000") && row.contains("5000cu"),
            "row 5000 drew receipt 5000: {row:?}"
        );
        assert!(
            !mid.contains(&0) && !mid.contains(&9999),
            "the window is local to the offset: {mid:?}"
        );

        // Parked on the TAIL: the newest receipt (row 9999) is in view — the visible
        // end of tail -f — while the head is still NOT built.
        let tail_off = virtual_face::tail_offset(n, row_h, viewport);
        let tail = virtual_face::visible_row_range(n, row_h, viewport, tail_off);
        assert!(tail.contains(&9999), "tail row present: {tail:?}");
        assert!(
            !tail.contains(&0),
            "still virtualized at the tail: {tail:?}"
        );
        assert!(world_explorer::chronicle_row_text(9999, &receipts[9999]).contains("9999cu"));
    }

    /// The Transcript's pure row renderer draws its receipt's index + hashes +
    /// agent — the datum the virtualized Transcript body maps over its visible
    /// range (and the bakes read as text).
    #[test]
    fn transcript_row_text_draws_its_receipt() {
        let r = receipt(42);
        let text = transcript_row_text(42, &r);
        assert!(text.contains("#42"), "carries the index: {text:?}");
        assert!(
            text.contains(&id_short(&r.agent)),
            "carries the agent: {text:?}"
        );
        // 0x2a = 42 → the turn-hash prefix is the repeated index byte.
        assert!(
            text.contains("2a2a2a2a"),
            "carries the turn-hash prefix: {text:?}"
        );
    }
}
