//! **GOSSAMER — the visible transclusion threads between windows.**
//!
//! The docuverse stops being rows in a list and becomes GEOMETRY you can see: when a
//! document window quoting cell X and any surface showing X are both on screen, a
//! literal cyan thread (an NT elbow connector) runs between them. Drag an icon onto
//! an open Document and the thread SNAPS into existence on the drop — the compose
//! gesture ([`DeosDesktop::transclude_into`]) writes the quote line into the buffer,
//! and the very next paint parses it back out ([`super::parse_transclusion_ref`])
//! into a drawn connection. Open the quoted cell's inspector and the thread re-roots
//! from its icon to the window. This is Ted Nelson's parallel-visible-connection
//! drawing — the single most photographed Xanadu mockup — running over real,
//! receipted quotes.
//!
//! ## The clobber-safe split
//!
//! This module owns the PURE elbow geometry ([`elbow_path`] — the load-bearing,
//! unit-testable core: facing-edge anchors, the three 2px strokes, the per-lane fan
//! offset) plus the desktop-side model (`quote_edges` / `visible_threads`) and the
//! [`DeosDesktop::render_threads`] presentation (the same absolutely-positioned-div
//! overlay idiom as [`super::halo`]). The desktop View owns only two seams: the
//! render() tail pushes the thread elements (gated on the persisted `show_threads`
//! preference), and the View menu carries the toggle. The geometry is gpui-value-free
//! `f32` math, so it compiles and tests without a renderer.
//!
//! ## Walkable, both ways
//!
//! Each thread ends in a clickable endpoint dot. Clicking the dot on the quoted
//! surface walks you INTO the quoting document (focus + halo-select); clicking the
//! dot on the document walks you back OUT to the quoted source (its top-z window if
//! one is open, else its icon, halo-selected). The link is a place you can travel,
//! not just a line you look at. No new actuation vocabulary: the walk desugars into
//! the existing focus/selection surface, exactly as the halo handles do.

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, SharedString, Styled,
};

use dregg_types::CellId;

use super::chrome::{bevel_raised, id_hex, id_short, ICON_H, ICON_W, NT_TEXT};
use super::halo::HaloTarget;
use super::{ActionKind, DeosDesktop, WinKindTag};

/// A desktop-coordinate rectangle `(x, y, w, h)` — the shared currency between the
/// anchor resolution (window frames, icon tiles, minimized stubs) and the elbow
/// strokes (each stroke IS one of these, painted as an absolutely-positioned div).
pub type Rect4 = (f32, f32, f32, f32);

/// The thread's stroke thickness (px) — thin enough to read as gossamer, thick
/// enough to survive the bake's downscale.
pub const THREAD_W: f32 = 2.0;
/// How far parallel threads fan apart (px per lane) so a bundle stays legible.
pub const LANE_STEP: f32 = 6.0;
/// The clickable endpoint-dot diameter (px).
pub const DOT_D: f32 = 8.0;
/// How far below a surface's top edge the thread anchors — just under the title
/// bar, so the line reads as tied to the WINDOW, not floating over its body.
pub const ANCHOR_DROP: f32 = 18.0;
/// The thread accent — the same bright cyan as the halo's selection outline
/// (`halo::HALO_OUTLINE`), so "selected" and "connected" share one voice.
const THREAD_CYAN: u32 = 0x33ccff;

/// **One resolved thread on the glass** — a quote edge whose two ends both landed on
/// visible geometry: the document window quoting `src`, and whatever surface
/// currently shows `src` (a window of any kind, or the bare icon).
pub(super) struct Thread {
    /// The QUOTED cell (the thread roots on its surface / icon).
    pub(super) src: CellId,
    /// The QUOTING document cell (the thread lands on its editor window).
    pub(super) doc: CellId,
    /// The source-side anchor box (window frame · minimized stub · icon tile).
    pub(super) from: Rect4,
    /// The document editor window's frame (or its minimized stub).
    pub(super) to: Rect4,
    /// Which parallel lane this thread rides (0 = the first thread touching either
    /// of its surfaces; each later sibling fans one [`LANE_STEP`] further out).
    pub(super) lane: usize,
}

/// **The elbow, resolved** — the two endpoints (each the center of a clickable dot)
/// plus the three axis-aligned strokes that join them: out of the source's facing
/// edge, down/up the vertical spine, into the document's facing edge.
pub struct ElbowPath {
    /// The source-side endpoint (on the quoted surface's facing edge).
    pub a: (f32, f32),
    /// The document-side endpoint (on the quoting window's facing edge).
    pub b: (f32, f32),
    /// The three strokes — `[horizontal out of a, the vertical spine, horizontal
    /// into b]` — each an absolutely-positionable `(x, y, w, h)`.
    pub segs: [Rect4; 3],
}

/// **The pure elbow geometry** — where a thread from box `from` to box `to` on lane
/// `lane` actually runs. Endpoints leave the FACING edges (the source's right edge
/// when the document sits to its right, else mirrored) at [`ANCHOR_DROP`] below the
/// top (clamped to the box's vertical middle, so a 22px minimized stub still anchors
/// inside itself). The vertical spine sits halfway between the endpoints, nudged one
/// [`LANE_STEP`] per lane so parallel threads fan instead of stacking.
pub fn elbow_path(from: Rect4, to: Rect4, lane: usize) -> ElbowPath {
    let (fx, fy, fw, fh) = from;
    let (tx, ty, tw, th) = to;
    let rightward = tx + tw / 2.0 >= fx + fw / 2.0;
    let a = if rightward {
        (fx + fw, fy + ANCHOR_DROP.min(fh / 2.0))
    } else {
        (fx, fy + ANCHOR_DROP.min(fh / 2.0))
    };
    let b = if rightward {
        (tx, ty + ANCHOR_DROP.min(th / 2.0))
    } else {
        (tx + tw, ty + ANCHOR_DROP.min(th / 2.0))
    };
    let mid_x = (a.0 + b.0) / 2.0 + lane as f32 * LANE_STEP;
    ElbowPath {
        a,
        b,
        segs: [
            hseg(a.0, mid_x, a.1),
            vseg(mid_x, a.1, b.1),
            hseg(mid_x, b.0, b.1),
        ],
    }
}

/// A horizontal stroke from `x0` to `x1` centered on `y` (normalized so `w ≥ 0`,
/// with a [`THREAD_W`] floor so a zero-length run still paints a joint).
fn hseg(x0: f32, x1: f32, y: f32) -> Rect4 {
    let (lo, hi) = if x0 <= x1 { (x0, x1) } else { (x1, x0) };
    (lo, y - THREAD_W / 2.0, (hi - lo).max(THREAD_W), THREAD_W)
}

/// A vertical stroke from `y0` to `y1` centered on `x` (same normalization).
fn vseg(x: f32, y0: f32, y1: f32) -> Rect4 {
    let (lo, hi) = if y0 <= y1 { (y0, y1) } else { (y1, y0) };
    (x - THREAD_W / 2.0, lo, THREAD_W, (hi - lo).max(THREAD_W))
}

impl DeosDesktop {
    /// **Every live quote edge `(doc, src)`** — for each open document-editor window,
    /// parse its buffer back through the same [`super::parse_transclusion_ref`] the
    /// Links window uses, so the drawn threads and the listed links can never drift.
    /// Deduped (one thread per pair however many times the doc quotes the cell) and
    /// self-quotes skipped. Doc order is sorted so lanes are stable across paints
    /// (the windows map is a `HashMap`; iteration order must not make threads flicker).
    fn quote_edges(&self) -> Vec<(CellId, CellId)> {
        let mut docs: Vec<CellId> = self
            .windows
            .keys()
            .filter(|(_, tag)| *tag == WinKindTag::DocEditor)
            .map(|(c, _)| *c)
            .collect();
        docs.sort();
        let mut edges: Vec<(CellId, CellId)> = Vec::new();
        for doc in docs {
            for src in self
                .load_doc_buffer(doc)
                .lines()
                .filter_map(super::parse_transclusion_ref)
            {
                if src != doc && !edges.contains(&(doc, src)) {
                    edges.push((doc, src));
                }
            }
        }
        edges
    }

    /// **Where a quoted cell shows on the glass** — the source-side anchor box,
    /// mirroring the halo's bounds resolution: prefer the top-z NON-MINIMIZED window
    /// of any kind on the cell (open the source's inspector and the thread re-roots
    /// from icon to window), then a minimized window's collapsed title stub, else the
    /// cell's desktop icon tile. `None` only for a quote of a vanished cell.
    fn thread_anchor(&self, cell: CellId) -> Option<Rect4> {
        let win = self
            .windows
            .iter()
            .filter(|((c, _), _)| *c == cell)
            .max_by_key(|(_, ws)| (!ws.minimized, ws.z));
        if let Some((_, ws)) = win {
            return Some(if ws.minimized {
                (ws.x, ws.y, 180.0, 22.0)
            } else {
                (ws.x, ws.y, ws.w, ws.h)
            });
        }
        let idx = self.cells.iter().position(|c| *c == cell)?;
        let pos = self.icon_pos(idx, &cell);
        Some((super::pxf(pos.x), super::pxf(pos.y), ICON_W, ICON_H))
    }

    /// The document-side anchor — the quoting DocEditor window's frame (its collapsed
    /// stub when minimized). `None` retires the thread the moment the doc closes.
    fn doc_anchor(&self, doc: CellId) -> Option<Rect4> {
        let ws = self.windows.get(&(doc, WinKindTag::DocEditor))?;
        Some(if ws.minimized {
            (ws.x, ws.y, 180.0, 22.0)
        } else {
            (ws.x, ws.y, ws.w, ws.h)
        })
    }

    /// **The threads on screen right now** — every quote edge whose two ends both
    /// resolve to visible geometry, each assigned the next free lane among the
    /// threads already touching one of its surfaces (so a fan of quotes into one
    /// document spreads one [`LANE_STEP`] apiece instead of stacking into one line).
    pub(super) fn visible_threads(&self) -> Vec<Thread> {
        let mut out: Vec<Thread> = Vec::new();
        for (doc, src) in self.quote_edges() {
            let Some(to) = self.doc_anchor(doc) else {
                continue;
            };
            let Some(from) = self.thread_anchor(src) else {
                continue;
            };
            let lane = out.iter().filter(|t| t.src == src || t.doc == doc).count();
            out.push(Thread {
                src,
                doc,
                from,
                to,
                lane,
            });
        }
        out
    }

    /// **Walk a thread to its `cell` end** — what clicking an endpoint dot does.
    /// Focus (raise + un-minimize) the top-z window open on the cell and leave it
    /// halo-selected; with nothing open, select the cell's icon so the ring names the
    /// landing. No new actuation: the walk desugars into the existing focus/selection
    /// surface, exactly like a halo handle or a Spotter jump.
    pub(super) fn walk_thread_end(&mut self, cell: CellId) {
        let key = self
            .windows
            .keys()
            .filter(|(c, _)| *c == cell)
            .copied()
            .max_by_key(|k| (!self.windows[k].minimized, self.windows[k].z));
        match key {
            Some(key) => {
                self.focus_window(key);
                self.selected = Some(HaloTarget::Window(key));
            }
            None => {
                self.selected = Some(HaloTarget::Icon(cell));
            }
        }
        self.say(format!(
            "Thread → walked to {} ({}).",
            id_short(&cell),
            self.cell_kind(&cell)
        ));
    }

    /// Flip the persisted Show-threads preference (the View-menu toggle). A pure
    /// persisted layout change, like every other preference — NO verified turn.
    pub(super) fn toggle_threads(&mut self) {
        self.layout.prefs.show_threads = !self.layout.prefs.show_threads;
        self.layout.save(&self.layout_path);
        self.say(if self.layout.prefs.show_threads {
            "Transclusion threads ON — quotes draw their geometry between windows."
        } else {
            "Transclusion threads hidden (View menu shows them again)."
        });
    }

    /// **Render the gossamer** — every visible thread as a 3-stroke cyan elbow of
    /// absolutely-positioned divs (the exact overlay idiom of
    /// [`DeosDesktop::render_halo`]), two clickable endpoint dots that walk the link
    /// in either direction, and a tiny mid-spine chip naming the quoted cell. Painted
    /// by the render() tail between the windows and the halo, so threads run OVER the
    /// surfaces they join but never over the ring, menus, or dialogs.
    pub(super) fn render_threads(&self, cx: &mut Context<Self>) -> Vec<AnyElement> {
        let mut out: Vec<AnyElement> = Vec::new();
        for t in self.visible_threads() {
            let path = elbow_path(t.from, t.to, t.lane);
            let key_base = format!("thread-{}-{}", id_hex(&t.src), id_hex(&t.doc));
            // The three strokes of the elbow.
            for (x, y, w, h) in path.segs {
                out.push(
                    div()
                        .absolute()
                        .left(px(x))
                        .top(px(y))
                        .w(px(w))
                        .h(px(h))
                        .bg(gpui::rgb(THREAD_CYAN))
                        .opacity(0.8)
                        .into_any_element(),
                );
            }
            // The endpoint dots — each walks to the OTHER end of the thread.
            let (src, doc) = (t.src, t.doc);
            for (i, (cx0, cy0), dest) in [(0usize, path.a, doc), (1usize, path.b, src)] {
                out.push(
                    div()
                        .id(SharedString::from(format!("{key_base}-{i}")))
                        .absolute()
                        .left(px(cx0 - DOT_D / 2.0))
                        .top(px(cy0 - DOT_D / 2.0))
                        .w(px(DOT_D))
                        .h(px(DOT_D))
                        .rounded_full()
                        .bg(gpui::rgb(THREAD_CYAN))
                        .border_1()
                        .border_color(gpui::rgb(0xffffff))
                        .hover(|s| s.border_color(gpui::rgb(0x101010)))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.walk_thread_end(dest);
                                cx.notify();
                            }),
                        )
                        .into_any_element(),
                );
            }
            // The mid-spine chip — the thread names what it quotes.
            let spine_x = path.segs[1].0 + THREAD_W / 2.0;
            let mid_y = (path.a.1 + path.b.1) / 2.0;
            out.push(
                bevel_raised(
                    div()
                        .absolute()
                        .left(px(spine_x + 4.0))
                        .top(px(mid_y - 7.0))
                        .px_1()
                        .text_size(px(8.0))
                        .text_color(gpui::rgb(NT_TEXT))
                        .child(format!("⊂ {}", id_short(&t.src))),
                )
                .into_any_element(),
            );
        }
        out
    }

    // ── Bake / test hooks (drive the threads headlessly) ────────────────────────

    /// How many threads the desktop would paint RIGHT NOW — the pref-gated count of
    /// quote edges whose two ends both resolve to on-screen geometry. The
    /// drag-to-transclude bake ([`DeosDesktop::bake_transclude`]) grows this by one;
    /// closing the quoting document ([`DeosDesktop::bake_close_doc`]) retires it.
    pub fn bake_thread_count(&self) -> usize {
        if !self.layout.prefs.show_threads {
            return 0;
        }
        self.visible_threads().len()
    }

    /// Whether a thread runs from the surface showing `src` into the open document
    /// window on `doc` (the one-named-connection assertion hook).
    pub fn bake_thread_between(&self, src: CellId, doc: CellId) -> bool {
        self.layout.prefs.show_threads
            && self
                .visible_threads()
                .iter()
                .any(|t| t.src == src && t.doc == doc)
    }

    /// Flip the View-menu Show-threads toggle through the SAME actuation path the
    /// menu row fires (persisted like every preference). Returns the new pref value.
    pub fn bake_toggle_threads(&mut self) -> bool {
        self.actuate(self.user, &ActionKind::ToggleThreads);
        self.layout.prefs.show_threads
    }

    /// Click a thread's endpoint dot — walk to the `cell` end (focus + halo-select
    /// its top-z surface, or select its bare icon when nothing is open). Returns
    /// whether the walk landed on an open WINDOW (vs. the icon).
    pub fn bake_walk_thread(&mut self, cell: CellId) -> bool {
        self.walk_thread_end(cell);
        matches!(self.selected, Some(HaloTarget::Window(_)))
    }
}

// ── Unit tests for the pure elbow geometry (gpui-free) ────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// A source at the origin and a document down-right of it.
    const FROM: Rect4 = (0.0, 0.0, 100.0, 50.0);
    const TO: Rect4 = (300.0, 200.0, 120.0, 60.0);

    #[test]
    fn endpoints_leave_the_facing_edges() {
        let p = elbow_path(FROM, TO, 0);
        assert_eq!(
            p.a,
            (100.0, 18.0),
            "the thread leaves the source's RIGHT edge, just under the title bar"
        );
        assert_eq!(
            p.b,
            (300.0, 218.0),
            "and enters the document's LEFT edge at the same drop"
        );
        // Mirrored when the document sits to the LEFT of the source.
        let m = elbow_path(TO, FROM, 0);
        assert_eq!(m.a, (300.0, 218.0), "leftward threads leave the left edge");
        assert_eq!(m.b, (100.0, 18.0), "and enter the target's right edge");
    }

    #[test]
    fn anchor_drop_clamps_inside_a_minimized_stub() {
        // A collapsed 22px title stub anchors at its vertical middle, not 18px below
        // its top (which would hang the endpoint outside the stub).
        let stub: Rect4 = (10.0, 400.0, 180.0, 22.0);
        let p = elbow_path(stub, TO, 0);
        assert_eq!(p.a.1, 411.0, "the drop clamps to h/2 for short boxes");
    }

    #[test]
    fn lanes_fan_the_spine_one_step_apiece() {
        let p0 = elbow_path(FROM, TO, 0);
        let p2 = elbow_path(FROM, TO, 2);
        let spine0 = p0.segs[1].0;
        let spine2 = p2.segs[1].0;
        assert_eq!(
            spine2 - spine0,
            2.0 * LANE_STEP,
            "each lane nudges the vertical spine one LANE_STEP further"
        );
        // The endpoints do NOT move with the lane — only the spine fans.
        assert_eq!(p0.a, p2.a);
        assert_eq!(p0.b, p2.b);
    }

    #[test]
    fn strokes_join_into_one_connected_elbow() {
        let p = elbow_path(FROM, TO, 1);
        let [h1, v, h2] = p.segs;
        let spine_x = v.0 + THREAD_W / 2.0;
        // The first horizontal runs from the source endpoint to the spine at a.y.
        assert_eq!(h1.1 + THREAD_W / 2.0, p.a.1);
        assert!((h1.0 - p.a.0.min(spine_x)).abs() < f32::EPSILON);
        assert!((h1.0 + h1.2 - p.a.0.max(spine_x)).abs() < f32::EPSILON);
        // The spine spans the two endpoint heights.
        assert!((v.1 - p.a.1.min(p.b.1)).abs() < f32::EPSILON);
        assert!((v.1 + v.3 - p.a.1.max(p.b.1)).abs() < f32::EPSILON);
        // The second horizontal runs from the spine into the document endpoint.
        assert_eq!(h2.1 + THREAD_W / 2.0, p.b.1);
        assert!((h2.0 - p.b.0.min(spine_x)).abs() < f32::EPSILON);
        assert!((h2.0 + h2.2 - p.b.0.max(spine_x)).abs() < f32::EPSILON);
        // Every stroke keeps the gossamer thickness (and its zero-length floor).
        for (_, _, w, h) in p.segs {
            assert!(w >= THREAD_W && h >= THREAD_W);
            assert!(w == THREAD_W || h == THREAD_W, "strokes are 2px bars");
        }
    }
}
