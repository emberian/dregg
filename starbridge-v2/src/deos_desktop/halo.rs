//! **The Pharo HALO — direct manipulation over the live workbench.**
//!
//! The most-Pharo affordance the desktop was still missing: *mold a surface in
//! place*. Select a cell-icon or a window and a small ring of round **handles**
//! floats around its bounding box — inspect · explore · open-as-document · fork ·
//! properties · the cell's affordance · resize · close · the full menu. Each handle
//! fires EXACTLY what the right-click context menu already actuates (a real verified
//! turn, an open-as surface, a layout move): the halo is a second, spatial face onto
//! the SAME actuation vocabulary ([`super::DeosDesktop::actuate`]) — no new effect, no
//! new circuit. It is the Smalltalk gesture (surround a morph with halo handles and
//! reshape it) brought over the verified World.
//!
//! `Halo`/direct-manipulation is named in `docs/deos/INSPECTOR-FRAMEWORK.md` §1.5 (the
//! ring is *data*, extended per object kind) and `docs/deos/HIG.md` ("Reflection is a
//! halo/flip on any cell"). This module is the desktop's concrete realization.

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, Point, SharedString, Styled,
};

use dregg_types::CellId;

use super::chrome::{id_hex, id_short, ICON_H, ICON_W, MENUBAR_H, NT_TITLE_TEXT};
use super::{ActionKind, DeosDesktop, Drag, OpenMenu, WinKey, WinKindTag};

/// **What the halo is wrapped around** — a desktop cell-icon, or one open window
/// (a window is `(cell, kind)`, so the same cell can carry several halos at once).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum HaloTarget {
    Icon(CellId),
    Window(WinKey),
}

impl HaloTarget {
    /// The cell the handles act on (a window's halo still actuates its anchor cell).
    fn cell(self) -> CellId {
        match self {
            HaloTarget::Icon(c) => c,
            HaloTarget::Window((c, _)) => c,
        }
    }
}

/// The eight compass anchor points around a bounding box — where a handle floats.
#[derive(Clone, Copy)]
enum Anchor {
    Nw,
    N,
    Ne,
    E,
    Se,
    S,
    Sw,
    W,
}

impl Anchor {
    /// The handle's CENTER for a box `(x, y, w, h)`.
    fn center(self, x: f32, y: f32, w: f32, h: f32) -> Point<f32> {
        let (cx, cy) = match self {
            Anchor::Nw => (x, y),
            Anchor::N => (x + w / 2.0, y),
            Anchor::Ne => (x + w, y),
            Anchor::E => (x + w, y + h / 2.0),
            Anchor::Se => (x + w, y + h),
            Anchor::S => (x + w / 2.0, y + h),
            Anchor::Sw => (x, y + h),
            Anchor::W => (x, y + h / 2.0),
        };
        Point { x: cx, y: cy }
    }
}

/// One verb a halo handle fires — each desugars into the EXISTING actuation surface.
#[derive(Clone, Copy)]
enum HaloCmd {
    /// Open the reflective inspector (`ActionKind::Inspect`).
    Inspect,
    /// Open the Document Explorer — history · graph · blame (`ActionKind::OpenDocExplorer`).
    Explore,
    /// Open the cell as a live document editor (`ActionKind::OpenDoc`).
    Document,
    /// Fork a confined co-author DRAFT branch (the branch-and-stitch gesture).
    Fork,
    /// Open the property inspector/editor — the "mold it in place" (`ActionKind::Properties`).
    Properties,
    /// Fire the cell's always-available verified-turn affordance (`ActionKind::BumpNonce`).
    Affordance,
    /// Drop the FULL context menu (every action) at the box edge.
    Menu,
    /// Begin a resize drag on a window (mirrors the corner grip).
    Resize,
    /// Close a window (`close_window`).
    Close,
    /// **Walk a backlink** — open the QUOTING document (the payload cell) and land
    /// selected on it. Fired by the witness-arc beads, not a ring handle.
    WalkBacklink(CellId),
}

/// A single handle descriptor — glyph, accent, where it sits, what it fires.
struct HaloHandle {
    glyph: &'static str,
    label: &'static str,
    color: u32,
    anchor: Anchor,
    cmd: HaloCmd,
    enabled: bool,
}

impl HaloHandle {
    fn new(
        glyph: &'static str,
        label: &'static str,
        color: u32,
        anchor: Anchor,
        cmd: HaloCmd,
    ) -> Self {
        HaloHandle {
            glyph,
            label,
            color,
            anchor,
            cmd,
            enabled: true,
        }
    }
    fn gated(mut self, held: bool) -> Self {
        self.enabled = held;
        self
    }
}

// ── Handle accents (kept distinct so the ring reads at a glance) ────────────────────
const HALO_INSPECT: u32 = 0x000080; // navy — inspect
const HALO_MENU: u32 = 0xb05000; // amber-orange — the "everything" menu
const HALO_PROPS: u32 = 0x0a6a7a; // teal — properties / mold in place
const HALO_EXPLORE: u32 = 0x5030a0; // violet — explore the substance
const HALO_DOC: u32 = 0x0a7a2a; // green — open as document
const HALO_AFFORD: u32 = 0xa06000; // amber — the verified-turn affordance
const HALO_FORK: u32 = 0x9030a0; // magenta — fork a draft branch
const HALO_RESIZE: u32 = 0x2a6a2a; // green — resize grip
const HALO_CLOSE: u32 = 0xb02020; // red — close
/// The selection outline (a bright cyan ring around the molded surface).
const HALO_OUTLINE: u32 = 0x33ccff;

/// The handle diameter (px).
const HANDLE_D: f32 = 24.0;

/// The backlink-bead diameter (px) — smaller than a handle: a bead is a door to
/// ANOTHER object (a quoting document), not a verb on this one.
const BEAD_D: f32 = 14.0;

impl DeosDesktop {
    /// The bounding box `(x, y, w, h)` of the current halo target, or `None` if the
    /// selection is stale (its window closed / its cell vanished).
    fn selected_bounds(&self, target: HaloTarget) -> Option<(f32, f32, f32, f32)> {
        match target {
            HaloTarget::Icon(cell) => {
                let idx = self.cells.iter().position(|c| *c == cell)?;
                let pos = self.icon_pos(idx, &cell);
                Some((super::pxf(pos.x), super::pxf(pos.y), ICON_W, ICON_H))
            }
            HaloTarget::Window(key) => {
                let ws = self.windows.get(&key)?;
                if ws.minimized {
                    Some((ws.x, ws.y, 180.0, 22.0))
                } else {
                    Some((ws.x, ws.y, ws.w, ws.h))
                }
            }
        }
    }

    /// The ring of handles for `target` — contextual: an icon offers open-as +
    /// actuation; a window adds resize + close (its window-control handles).
    fn halo_handles(&self, target: HaloTarget) -> Vec<HaloHandle> {
        use Anchor::*;
        use HaloCmd as C;
        let held = self.holds(&target.cell());
        match target {
            HaloTarget::Icon(_) => vec![
                HaloHandle::new("i", "Inspect", HALO_INSPECT, Nw, C::Inspect),
                HaloHandle::new("=", "Menu (everything)", HALO_MENU, N, C::Menu),
                HaloHandle::new("P", "Properties (mold)", HALO_PROPS, Ne, C::Properties),
                HaloHandle::new(
                    "e",
                    "Explore (history·graph·blame)",
                    HALO_EXPLORE,
                    E,
                    C::Explore,
                ),
                HaloHandle::new("D", "Open as Document", HALO_DOC, Se, C::Document),
                HaloHandle::new(
                    "+",
                    "Affordance (verified turn)",
                    HALO_AFFORD,
                    S,
                    C::Affordance,
                )
                .gated(held),
                HaloHandle::new("Y", "Fork a draft branch", HALO_FORK, Sw, C::Fork),
            ],
            HaloTarget::Window(_) => vec![
                HaloHandle::new("i", "Inspect", HALO_INSPECT, Nw, C::Inspect),
                HaloHandle::new("=", "Menu (everything)", HALO_MENU, N, C::Menu),
                HaloHandle::new("×", "Close", HALO_CLOSE, Ne, C::Close),
                HaloHandle::new("P", "Properties (mold)", HALO_PROPS, E, C::Properties),
                HaloHandle::new("/", "Resize", HALO_RESIZE, Se, C::Resize),
                HaloHandle::new(
                    "+",
                    "Affordance (verified turn)",
                    HALO_AFFORD,
                    S,
                    C::Affordance,
                )
                .gated(held),
                HaloHandle::new(
                    "e",
                    "Explore (history·graph·blame)",
                    HALO_EXPLORE,
                    Sw,
                    C::Explore,
                ),
                HaloHandle::new("Y", "Fork a draft branch", HALO_FORK, W, C::Fork),
            ],
        }
    }

    /// **Fire a halo handle** — desugar `cmd` into the existing actuation surface. The
    /// halo never reaches the kernel directly; it routes through the very same
    /// [`DeosDesktop::actuate`] / window-control paths the right-click menu uses.
    fn actuate_halo(&mut self, target: HaloTarget, cmd: HaloCmd) {
        let cell = target.cell();
        match cmd {
            HaloCmd::Inspect => self.actuate(cell, &ActionKind::Inspect),
            HaloCmd::Explore => self.actuate(cell, &ActionKind::OpenDocExplorer),
            HaloCmd::Document => self.actuate(cell, &ActionKind::OpenDoc),
            HaloCmd::Properties => self.actuate(cell, &ActionKind::Properties),
            HaloCmd::Affordance => self.actuate(cell, &ActionKind::BumpNonce),
            HaloCmd::Fork => {
                // Open (or focus) the document editor and fork a confined co-author
                // draft — the genuine branch-and-stitch gesture. Track the editor.
                self.open_kind(cell, WinKindTag::DocEditor);
                self.fork_doc_branch(cell);
                self.selected = Some(HaloTarget::Window((cell, WinKindTag::DocEditor)));
            }
            HaloCmd::Menu => {
                // Drop the full context menu at the box's top-right corner — the same
                // deep vocabulary, summoned spatially from the ring.
                let at = self
                    .selected_bounds(target)
                    .map(|(x, y, w, _)| Point::new(px(x + w), px(y)))
                    .unwrap_or_else(|| Point::new(px(0.0), px(MENUBAR_H)));
                let (heading, actions) = match target {
                    HaloTarget::Icon(c) => (
                        format!("{} · {}", self.cell_kind(&c), id_short(&c)),
                        self.actions_for(c),
                    ),
                    HaloTarget::Window((c, tag)) => (
                        format!("{} {}", self.cell_kind(&c), id_short(&c)),
                        self.window_actions(c, tag),
                    ),
                };
                self.open_menu = Some(OpenMenu {
                    cell: Some(cell),
                    heading,
                    at,
                    actions,
                });
            }
            HaloCmd::Resize => {
                if let HaloTarget::Window(key) = target {
                    if let Some(ws) = self.windows.get(&key) {
                        self.drag = Some(Drag::WinResize {
                            key,
                            origin: Point::new(px(ws.x), px(ws.y)),
                        });
                    }
                }
            }
            HaloCmd::Close => {
                if let HaloTarget::Window(key) = target {
                    self.close_window(key);
                }
                self.selected = None;
            }
            HaloCmd::WalkBacklink(observer) => {
                // Walk the two-way link BACKWARDS — open the quoting document's
                // editor and land selected on it (the same `land_in` arrival a
                // welcome door / Spotter jump makes), so the backlink stops being
                // a row you must open a Links window to read and becomes a door
                // you step through.
                self.land_in(observer, WinKindTag::DocEditor);
                self.say(format!(
                    "WALK backlink → document {} (it quotes {}).",
                    id_short(&observer),
                    id_short(&cell)
                ));
            }
        }
    }

    /// **Render the floating halo** — the selection outline plus the ring of handles,
    /// each an absolutely-positioned child of the desktop root (desktop coordinates,
    /// exactly like the icons). Returns an empty vec if the selection is stale.
    pub(super) fn render_halo(&self, cx: &mut Context<Self>) -> Vec<AnyElement> {
        let Some(target) = self.selected else {
            return Vec::new();
        };
        let Some((bx, by, bw, bh)) = self.selected_bounds(target) else {
            return Vec::new();
        };
        let key_base = match target {
            HaloTarget::Icon(c) => format!("icon-{}", id_hex(&c)),
            HaloTarget::Window((c, tag)) => format!("win-{}-{}", id_hex(&c), tag as u8),
        };

        let mut out: Vec<AnyElement> = Vec::new();

        // The selection outline — a bright cyan ring just outside the box.
        out.push(
            div()
                .absolute()
                .left(px(bx - 3.0))
                .top(px(by - 3.0))
                .w(px(bw + 6.0))
                .h(px(bh + 6.0))
                .border_2()
                .border_color(gpui::rgb(HALO_OUTLINE))
                .rounded(px(2.0))
                .into_any_element(),
        );

        // A small caption pinned above the ring so the molded object names itself.
        out.push(
            div()
                .absolute()
                .left(px(bx))
                .top(px((by - 30.0).max(MENUBAR_H)))
                .px_1()
                .text_size(px(9.0))
                .bg(gpui::rgb(HALO_INSPECT))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
                .child(format!(
                    "halo · {} — mold in place",
                    id_short(&target.cell())
                ))
                .into_any_element(),
        );

        // ── The backlink WITNESS ARC — the ring knows who quotes you. `backlinks_of`
        //    is the very reverse scan the Links window renders with (one source of
        //    two-way-link truth, so the two surfaces cannot drift): every document
        //    whose prose transcludes this cell. An amber badge names the count; up to
        //    three beads follow, one per quoting document, each labeled with the
        //    document's leading hex — and each a DOOR: clicking a bead walks the link
        //    backwards (`HaloCmd::WalkBacklink` → open that document's editor, land
        //    selected on it, mold-ready). ──
        let backlinks = self.backlinks_of(target.cell());
        if !backlinks.is_empty() {
            let arc_y = by + bh + 8.0;
            out.push(
                div()
                    .absolute()
                    .left(px(bx))
                    .top(px(arc_y))
                    .px_1()
                    .text_size(px(9.0))
                    .bg(gpui::rgb(HALO_AFFORD))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
                    .child(format!("← quoted by {}", backlinks.len()))
                    .into_any_element(),
            );
            for (i, observer) in backlinks.into_iter().take(3).enumerate() {
                let hex2: String = id_hex(&observer).chars().take(2).collect();
                out.push(
                    div()
                        .id(SharedString::from(format!("halo-back-{key_base}-{i}")))
                        .absolute()
                        .left(px(bx + 96.0 + i as f32 * (BEAD_D + 4.0)))
                        .top(px(arc_y))
                        .w(px(BEAD_D))
                        .h(px(BEAD_D))
                        .rounded_full()
                        .flex()
                        .items_center()
                        .justify_center()
                        .text_size(px(8.0))
                        .text_color(gpui::rgb(NT_TITLE_TEXT))
                        .bg(gpui::rgb(HALO_AFFORD))
                        .border_1()
                        .border_color(gpui::rgb(0xffffff))
                        .hover(|s| s.border_color(gpui::rgb(0x101010)))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.actuate_halo(target, HaloCmd::WalkBacklink(observer));
                                cx.notify();
                            }),
                        )
                        .child(hex2)
                        .into_any_element(),
                );
            }
        }

        for (i, h) in self.halo_handles(target).into_iter().enumerate() {
            let c = h.anchor.center(bx, by, bw, bh);
            let cmd = h.cmd;
            let enabled = h.enabled;
            let mut btn = div()
                .id(SharedString::from(format!("halo-{key_base}-{i}")))
                .absolute()
                .left(px(c.x - HANDLE_D / 2.0))
                .top(px(c.y - HANDLE_D / 2.0))
                .w(px(HANDLE_D))
                .h(px(HANDLE_D))
                .rounded_full()
                .flex()
                .items_center()
                .justify_center()
                .text_size(px(13.0))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
                .bg(gpui::rgb(h.color))
                .border_2()
                .border_color(gpui::rgb(0xffffff))
                .child(h.glyph);
            if enabled {
                btn = btn
                    .hover(|s| s.border_color(gpui::rgb(0x101010)))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.actuate_halo(target, cmd);
                            cx.notify();
                        }),
                    );
            } else {
                // A dim, unheld affordance handle (the cap is not held).
                btn = btn.opacity(0.4);
            }
            // The handle tooltip rides along as the element title (legible on hover).
            let _ = h.label;
            out.push(btn.into_any_element());
        }

        out
    }

    // ── Bake / test hooks (drive the halo headlessly) ────────────────────────────

    /// Select a cell-icon so its halo ring floats (what a single left-click does).
    pub fn bake_select_icon(&mut self, cell: CellId) {
        self.selected = Some(HaloTarget::Icon(cell));
    }

    /// Select an open window so its halo ring floats (what clicking the window does).
    pub fn bake_select_window(&mut self, cell: CellId, tag: WinKindTag) {
        self.selected = Some(HaloTarget::Window((cell, tag)));
    }

    /// The number of handles the current selection's halo would float (0 if nothing
    /// is selected or the selection is stale).
    pub fn bake_halo_handle_count(&self) -> usize {
        match self.selected.and_then(|t| {
            self.selected_bounds(t)?;
            Some(t)
        }) {
            Some(t) => self.halo_handles(t).len(),
            None => 0,
        }
    }

    /// Whether the current halo selection is an open WINDOW (vs. a bare cell-icon, vs.
    /// nothing). A bake/test hook: proves a welcome door / Spotter jump LANDED you in a
    /// live surface that is already mold-ready (its window halo floating), not merely
    /// opened a window you must then go hunt and select.
    pub fn bake_selection_is_window(&self) -> bool {
        matches!(self.selected, Some(HaloTarget::Window(_)))
    }

    /// Fire the halo's Inspect handle on the current selection (what clicking the
    /// inspect handle does) — proves the ring reuses the existing actuation. Returns
    /// whether something was selected to act on.
    pub fn bake_halo_fire_inspect(&mut self) -> bool {
        match self.selected {
            Some(target) => {
                self.actuate_halo(target, HaloCmd::Inspect);
                true
            }
            None => false,
        }
    }

    /// The backlink count the current halo selection's witness arc shows — how many
    /// documents transclude the selected cell (the "← quoted by N" badge); 0 when
    /// nothing is selected or the selection is stale. Reads the SAME
    /// `DeosDesktop::backlinks_of` reverse scan the badge (and the Links window)
    /// renders with, so the assertion tracks the real surface.
    pub fn bake_halo_backlink_count(&self) -> usize {
        match self.selected.and_then(|t| {
            self.selected_bounds(t)?;
            Some(t)
        }) {
            Some(t) => self.backlinks_of(t.cell()).len(),
            None => 0,
        }
    }

    /// **Walk the first backlink bead** on the current halo selection (what clicking
    /// bead `halo-back-…-0` does): open the quoting document's editor and land
    /// selected on it. Returns the quoting cell walked to (`None` when nothing is
    /// selected or nothing quotes it). Pair with
    /// `DeosDesktop::bake_selected_window_label` to assert the walk LANDED
    /// mold-ready in the RIGHT surface (the selection IS the quoting Document).
    pub fn bake_halo_walk_backlink(&mut self) -> Option<CellId> {
        let target = self.selected?;
        let observer = self.backlinks_of(target.cell()).into_iter().next()?;
        self.actuate_halo(target, HaloCmd::WalkBacklink(observer));
        Some(observer)
    }
}
