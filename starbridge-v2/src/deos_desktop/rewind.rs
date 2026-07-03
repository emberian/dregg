//! **THE REWIND RAIL — scrub the entire desktop through root-verified history.**
//!
//! The event-sourced OS made *felt*: the desktop IS a fold over the receipt
//! chain, and this module puts the fold in the operator's hand. A thin NT rail
//! docked above the taskbar carries one tick per recorded [`History`] step;
//! drag its scrubber and the WHOLE desktop — icons, inspector bodies, the World
//! Explorer's census/chronicle/conservation faces — re-derives at that point in
//! history by VERIFIED replay ([`History::reify_to`], the umem-boundary restore
//! with genesis-replay fallback, fail-closed against the recorded root tooth).
//! A prominent **LIVE** chip snaps you back; live turns landing while the
//! cursor sits in the past visibly lengthen the rail.
//!
//! Three layers, clobber-safe:
//!
//!   * **The gpui-free model** — [`RewindProjection`] (one verified replay of
//!     the world at step `k`: ledger + root + the receipt stamp + the diff vs
//!     live) built by the pure [`project`], and [`RewindState`] (the cursor +
//!     the memoized projection; rebuilt only when the cursor moves or live
//!     history grows — never per-frame). Unit-tested below without a window.
//!   * **The effective-ledger accessor** — [`DeosDesktop::with_effective_ledger`]
//!     / [`DeosDesktop::with_effective_cell`]: every `cell_*` reader in the hub
//!     routes through it, so any surface that reads the World reads the
//!     replayed projection while scrubbing and the live ledger at LIVE. THE
//!     WELD POINT for new surfaces: read through these accessors (or accept a
//!     [`super::world_explorer::WorldLens`]) and rewind coverage is free.
//!   * **Pure presentation + the View** — the rail render (NT chrome: sunken
//!     track, raised knob, the scrubbed root/receipt stamp, the LIVE chip) and
//!     the amber "differs from NOW" rings around changed icons. The `View` owns
//!     the listeners (the halo.rs discipline); the drag itself is a
//!     [`Drag::Rewind`] driven by the desktop root's global mouse-move.
//!
//! NEVER MUTATES THE LIVE WORLD: a projection is a read-only reconstruction
//! (its own [`Ledger`] rebuilt from the recorded steps), and while the cursor
//! is off LIVE every verified-turn verb dims (`DeosDesktop::holds` gates on
//! [`RewindState::is_live`]) — the past is read-only, the substrate cannot be
//! asked to lie about it.
//!
//! TODO(weld — tonight's newest commits, not in this base): (1) the keyboard
//! spine should bind Left/Right to step the cursor ±1 and Esc to
//! `rewind_go_live`; (2) the transcript body + `pump_dynamics` REFUSED rows
//! (the outcome_verdict lane) still read the live World while scrubbing — weld
//! them through `with_effective_ledger`/`RewindProjection::receipts` when the
//! trees merge; (3) `describe_outcome` (refusal-surfacing lane) should stamp
//! the rail's status line once it lands.

use std::collections::HashSet;

use gpui::{
    div, px, AnyElement, Context, FontWeight, InteractiveElement, IntoElement, MouseButton,
    MouseDownEvent, ParentElement, Styled,
};

use dregg_cell::{Cell, Ledger};
use dregg_turn::turn::TurnReceipt;
use dregg_types::CellId;

use crate::replay::{diff_ledgers, History, RecordedStep, ScrubSource};
use crate::world::World;

use super::chrome::{
    bevel_raised, bevel_sunken, id_short, pxf, ICON_H, ICON_W, NT_DIM, NT_FACE, NT_FACE_DARK,
    NT_OK, NT_PANEL, NT_SHADOW, NT_TEXT, NT_TITLE_ACTIVE, NT_TITLE_TEXT, NT_WARN,
};
use super::world_explorer as we;
use super::world_explorer::{render_world_explorer_body, WorldExplorerTab, WorldLens};
use super::{DeosDesktop, Drag, FaceScrollKey, WinKindTag};

// ── Rail geometry (fixed, so x → step mapping is one pure function) ───────────────

/// The rail strip's height (px) — a thin dock between the windows and the taskbar.
pub const RAIL_H: f32 = 22.0;
/// The rail's bottom offset: statusbar (22) + taskbar (24).
pub const RAIL_BOTTOM: f32 = 46.0;
/// Where the scrub track starts (left zone carries the REWIND caption).
pub const RAIL_TRACK_LEFT: f32 = 148.0;
/// Reserved right zone: the root/receipt stamp readout + the LIVE chip.
pub const RAIL_TRACK_RIGHT: f32 = 360.0;
/// The scrubber knob width.
const KNOB_W: f32 = 9.0;

// ===========================================================================
// The gpui-free model
// ===========================================================================

/// The receipt stamped at (or nearest below) the scrubbed step — the rail's
/// "when/what" readout: the RECOMPUTED receipt hash + the deterministic
/// executor timestamp of the last committed turn at-or-before the cursor.
#[derive(Clone)]
pub struct StepStamp {
    /// `TurnReceipt::receipt_hash()` — recomputed BLAKE3, never trusted bytes.
    pub receipt_hash: [u8; 32],
    /// The receipt's (replay-deterministic) executor timestamp.
    pub timestamp: i64,
    /// The turn's agent cell.
    pub agent: CellId,
}

/// **One verified replay of the World at history step `k`** — the read-only
/// projection every desktop surface reads while the Rewind Rail is scrubbed.
/// Built by [`project`]; owns its own reconstructed [`Ledger`] (the live World
/// is NEVER touched). Fail-closed: if the re-derived root does not match the
/// recorded tooth, `verified` is false and the ledger is EMPTY — the desktop
/// shows nothing rather than an unverifiable past.
pub struct RewindProjection {
    /// The replayed step (`0` = pre-genesis void … `total` = the head).
    pub step: usize,
    /// `History::len()` at build time — the rail's denominator AND the memo
    /// key that catches live turns landing while the cursor sits in the past.
    pub total: usize,
    /// The reconstructed ledger at `step` (root-verified, or empty on refusal).
    pub ledger: Ledger,
    /// The recorded canonical root tooth at `step` (`History::root_at`).
    pub root: [u8; 32],
    /// Whether the reconstruction reproduced the recorded tooth (fail-closed).
    pub verified: bool,
    /// `true` when the umem-boundary fast path restored it; `false` when the
    /// genesis-replay safety net (or a refusal) fired. Pure honesty readout.
    pub via_boundary: bool,
    /// Cells whose observable state at `step` DIFFERS from the live head —
    /// these icons wear the amber "≠ NOW" ring (`diff_ledgers`, both created
    /// and changed and since-destroyed ids).
    pub changed: HashSet<CellId>,
    /// The receipts of every committed turn among steps `0..step`, in order —
    /// the Chronicle face's past log + the per-cell "turns by cell" reader.
    pub receipts: Vec<TurnReceipt>,
    /// The stamp of the newest committed turn at-or-before `step` (`None`
    /// while the cursor sits in the genesis installs — no receipt exists yet).
    pub stamp: Option<StepStamp>,
}

/// **The pure replay projection** — reconstruct the world at `step` from the
/// canonical recorded history and verify it against the recorded root tooth.
///
/// Read-only over both inputs: the reconstruction is a fresh [`Ledger`]
/// ([`History::reify_to`] — the umem-boundary inverse fold, falling back to
/// root-verified genesis replay for cells outside the faithful class); the
/// `live` ledger is consulted only to diff "what differs from NOW". A `step`
/// beyond the head clamps to the head. The anti-substitution tooth is
/// delegated to `reify_to`/`replay_to` (tamper tests live in `replay.rs`); a
/// refused reconstruction yields `verified == false` + an EMPTY ledger.
pub fn project(history: &History, live: &Ledger, step: usize) -> RewindProjection {
    let total = history.len();
    let step = step.min(total);
    let (ledger, verified, via_boundary) = match history.reify_to(step) {
        Ok((l, src)) => (l, true, src == ScrubSource::UmemBoundary),
        // Fail-closed: an unverifiable past renders as NOTHING, not a guess.
        Err(_) => (Ledger::new(), false, false),
    };
    let root = history.root_at(step);
    let changed: HashSet<CellId> = if verified {
        diff_ledgers(&ledger, live)
            .changed_ids()
            .into_iter()
            .collect()
    } else {
        HashSet::new()
    };
    let mut receipts: Vec<TurnReceipt> = Vec::new();
    for s in &history.steps()[..step] {
        if let RecordedStep::Committed { receipt, .. } = s {
            receipts.push((**receipt).clone());
        }
    }
    let stamp = receipts.last().map(|r| StepStamp {
        receipt_hash: r.receipt_hash(),
        timestamp: r.timestamp,
        agent: r.agent,
    });
    RewindProjection {
        step,
        total,
        ledger,
        root,
        verified,
        via_boundary,
        changed,
        receipts,
        stamp,
    }
}

/// **The Rewind Rail's view-model** — the scrub cursor plus the memoized
/// verified projection at it. Owned by `DeosDesktop`; a pure view concern
/// (nothing here is committed state — reopening the desktop opens LIVE).
#[derive(Default)]
pub struct RewindState {
    /// `None` = LIVE (every reader hits the live World); `Some(k)` = the
    /// desktop reads the root-verified replay at history step `k`. Written by
    /// the rail's listeners and the `Drag::Rewind` mouse-move arm.
    pub(super) cursor: Option<u64>,
    /// The memoized projection at `cursor` — rebuilt by [`Self::ensure`] only
    /// when the cursor lands on a new step or live history grows underneath
    /// it, NEVER per-frame (a replay per repaint would be dishonest cost).
    projection: Option<RewindProjection>,
}

impl RewindState {
    /// Whether the desktop reads the live World (no scrub in progress).
    pub fn is_live(&self) -> bool {
        self.cursor.is_none()
    }

    /// The current verified projection — `Some` only while scrubbing (after an
    /// [`Self::ensure`] pass; the render path refreshes before any reader).
    pub fn projection(&self) -> Option<&RewindProjection> {
        match self.cursor {
            Some(_) => self.projection.as_ref(),
            None => None,
        }
    }

    /// Snap back to LIVE — drop the cursor AND the projection (the next reader
    /// hits the live World immediately).
    pub fn go_live(&mut self) {
        self.cursor = None;
        self.projection = None;
    }

    /// Keep the memoized projection IN STEP with the cursor + the live
    /// history: rebuild iff the cursor moved or `History::len()` grew (a live
    /// turn landed while the cursor sat in the past — the rail lengthens and
    /// the "differs from NOW" diff re-derives). Clamps the cursor to the head.
    pub fn ensure(&mut self, world: &World) {
        let Some(k) = self.cursor else {
            self.projection = None;
            return;
        };
        let history = world.recorded_turns();
        let step = (k as usize).min(history.len());
        let fresh = matches!(
            &self.projection,
            Some(p) if p.step == step && p.total == history.len()
        );
        if !fresh {
            self.projection = Some(project(history, world.ledger(), step));
        }
        self.cursor = Some(step as u64);
    }
}

// ── Pure presentation helpers (string projections; unit-tested) ───────────────────

/// First 4 bytes as 8 hex chars — the rail's dense root/receipt rendering.
pub fn hex8(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

/// The rail's replay banner: liveness (the `ui_snapshot` honesty vocabulary —
/// a replay is DETERMINISTIC, never claimed live), the cursor, and the
/// re-derived root's verdict against the recorded tooth.
pub fn rail_caption(p: &RewindProjection) -> String {
    format!(
        "REPLAYED (deterministic) · step {}/{} · root {} {}",
        p.step,
        p.total,
        hex8(&p.root),
        if p.verified {
            "✓"
        } else {
            "!! ROOT MISMATCH"
        }
    )
}

/// The scrubbed step's receipt stamp — the RECOMPUTED receipt hash + the
/// deterministic timestamp, or the honest "no receipt yet" while the cursor
/// sits in the genesis installs.
pub fn stamp_caption(p: &RewindProjection) -> String {
    match &p.stamp {
        Some(s) => format!(
            "receipt {} · t{} · agent {}",
            hex8(&s.receipt_hash),
            s.timestamp,
            id_short(&s.agent)
        ),
        None => "genesis — no receipt yet".into(),
    }
}

/// Map a desktop-window x coordinate onto a history step — the ONE mapping the
/// track click, the [`Drag::Rewind`] mouse-move, and the knob placement all
/// share (fixed track bounds, so the inverse is exact).
pub(super) fn step_at_x(x: f32, viewport_w: f32, total: usize) -> u64 {
    if total == 0 {
        return 0;
    }
    let track_w = (viewport_w - RAIL_TRACK_LEFT - RAIL_TRACK_RIGHT).max(48.0);
    let frac = ((x - RAIL_TRACK_LEFT) / track_w).clamp(0.0, 1.0);
    (frac * total as f32).round() as u64
}

// ===========================================================================
// The View half — accessors, actuation, and the rail render (owns listeners)
// ===========================================================================

impl DeosDesktop {
    /// Keep the rewind projection fresh — called ONCE at the top of `render`
    /// (before any surface reads through the effective accessors this frame)
    /// and after every cursor write. Memoized inside [`RewindState::ensure`].
    pub(super) fn rewind_refresh(&mut self) {
        let w = self.world.borrow();
        self.rewind.ensure(&w);
    }

    /// **THE EFFECTIVE LEDGER** — the one read-surface switch of the Rewind
    /// Rail: the replayed projection's ledger while scrubbing, the live
    /// World's otherwise. Every `cell_*` reader in the hub routes through
    /// here; a new surface that reads through this accessor (rather than
    /// `self.world.borrow().ledger()` directly) gets rewind coverage free.
    pub(super) fn with_effective_ledger<R>(&self, f: impl FnOnce(&Ledger) -> R) -> R {
        match self.rewind.projection() {
            Some(p) => f(&p.ledger),
            None => f(self.world.borrow().ledger()),
        }
    }

    /// Read one cell off the effective ledger. `None` when the cell does not
    /// exist THERE — at a scrubbed cursor that is the truthful past absence
    /// (a cell born later has no state at this height), never a live fallback.
    pub(super) fn with_effective_cell<R>(
        &self,
        cell: &CellId,
        f: impl FnOnce(&Cell) -> R,
    ) -> Option<R> {
        self.with_effective_ledger(|l| l.get(cell).map(f))
    }

    /// Whether `cell` exists at the current view of the world — gates the icon
    /// census while scrubbing (a not-yet-born cell has no icon in the past).
    pub(super) fn rewind_cell_present(&self, cell: &CellId) -> bool {
        match self.rewind.projection() {
            Some(p) => p.ledger.get(cell).is_some(),
            None => true,
        }
    }

    /// The cell's turn count at the current view — the projection's receipt
    /// log while scrubbing (receipts that existed AT the cursor), live else.
    pub(super) fn effective_cell_receipt_count(&self, cell: &CellId) -> usize {
        match self.rewind.projection() {
            Some(p) => p.receipts.iter().filter(|r| &r.agent == cell).count(),
            None => self
                .world
                .borrow()
                .receipts()
                .iter()
                .filter(|r| &r.agent == cell)
                .count(),
        }
    }

    /// Plant the cursor at `step` and rebuild the projection — what a track
    /// click / a rail drag / `bake_rewind_to` does. The status bar narrates
    /// the landing (root verdict + receipt stamp) so the scrub is legible.
    pub(super) fn rewind_scrub_to(&mut self, step: u64) {
        self.rewind.cursor = Some(step);
        self.rewind_refresh();
        if let Some(p) = self.rewind.projection() {
            self.say(format!(
                "REWIND · {} · {} — the past is read-only; LIVE returns you.",
                rail_caption(p),
                stamp_caption(p)
            ));
        }
    }

    /// Snap back to LIVE — what the rail's LIVE chip / `bake_rewind_live` does.
    pub(super) fn rewind_go_live(&mut self) {
        self.rewind.go_live();
        self.say(format!(
            "LIVE — the desktop reads the live World again (height {}).",
            self.world.borrow().height()
        ));
    }

    /// The World Explorer body over the EFFECTIVE world — the replayed lens
    /// (with its amber REPLAYED banner) while scrubbing, the live lens else.
    ///
    /// The two dense log/census faces — **Chronicle** and **Ledger** — are
    /// UNCAPPED here: they ride the View's `v_virtual_list` (see
    /// [`DeosDesktop::nt_virtual_face`]) over the effective receipts/ledger, so
    /// only the visible rows are ever built and the whole history is reachable —
    /// no more 24-row peephole at 100k turns. The row renderers stay the pure
    /// `world_explorer::{chronicle_row, ledger_row}` functions the flat faces
    /// share; the closure re-resolves the effective lens (replayed while
    /// scrubbing, live else) each paint, so the census is always the World's
    /// truth at the cursor. The Chronicle `follow_tail`s (a landing receipt snaps
    /// the tail into view); the id-sorted Ledger keeps its scroll place.
    ///
    /// **Conservation** stays the flat pure path — its per-cell gauge rows are
    /// two-element and not uniform-height, so it does not fit uniform
    /// virtualization; it keeps the caller-style persistent `face_scrolls` handle
    /// (ensured here now that this owns `&mut self`).
    ///
    /// (`&mut self` for the virtual/flat scroll registries; `cx` for the
    /// `v_virtual_list` view handle. `cell` keys the per-window/per-tab face.)
    pub(super) fn render_world_explorer_body_effective(
        &mut self,
        tab: WorldExplorerTab,
        cell: CellId,
        cx: &mut gpui::Context<Self>,
    ) -> AnyElement {
        let key = FaceScrollKey::Window(cell, WinKindTag::WorldExplorer, tab as u8);
        match tab {
            // The uniform-height gauge rows do not virtualize cleanly; keep the
            // flat pure body over its persistent face-scroll handle.
            WorldExplorerTab::Conservation => {
                let scroll = self.face_scrolls.ensure(key);
                match self.rewind.projection() {
                    Some(p) => render_world_explorer_body(
                        &WorldLens {
                            ledger: &p.ledger,
                            receipts: &p.receipts,
                            height: p.receipts.len() as u64,
                            cell_count: p.ledger.len(),
                            banner: Some(rail_caption(p)),
                        },
                        tab,
                        &scroll,
                    ),
                    None => {
                        let w = self.world.borrow();
                        render_world_explorer_body(&WorldLens::live(&w), tab, &scroll)
                    }
                }
            }

            WorldExplorerTab::Chronicle => {
                let (count, height, banner) = match self.rewind.projection() {
                    Some(p) => (
                        p.receipts.len(),
                        p.receipts.len() as u64,
                        Some(rail_caption(p)),
                    ),
                    None => {
                        let w = self.world.borrow();
                        (w.receipts().len(), w.height(), None)
                    }
                };
                let list_id =
                    gpui::SharedString::from(format!("wld-chron-{}", super::id_hex(&cell)));
                let list = if count == 0 {
                    div()
                        .child("(no turns yet — actuate a cell)")
                        .into_any_element()
                } else {
                    self.nt_virtual_face(
                        key,
                        list_id,
                        count,
                        we::CHRONICLE_ROW_H,
                        true,
                        cx,
                        |this, range, _w, _cx| {
                            if let Some(p) = this.rewind.projection() {
                                range
                                    .filter_map(|i| {
                                        p.receipts.get(i).map(|r| we::chronicle_row(i, r))
                                    })
                                    .collect()
                            } else {
                                let w = this.world.borrow();
                                let receipts = w.receipts();
                                range
                                    .filter_map(|i| {
                                        receipts.get(i).map(|r| we::chronicle_row(i, r))
                                    })
                                    .collect()
                            }
                        },
                    )
                };
                let face = div()
                    .flex_1()
                    .min_h(px(0.0))
                    .flex()
                    .flex_col()
                    .bg(gpui::rgb(0x101820))
                    .text_color(gpui::rgb(0x9fe0a0))
                    .p_2()
                    .gap_1()
                    .child(we::chronicle_header(count, height))
                    .child(list)
                    .into_any_element();
                we::with_replay_banner(banner, face)
            }

            WorldExplorerTab::Ledger => {
                let (count, banner) = match self.rewind.projection() {
                    Some(p) => (p.ledger.len(), Some(rail_caption(p))),
                    None => (self.world.borrow().ledger().len(), None),
                };
                let list_id =
                    gpui::SharedString::from(format!("wld-ledger-{}", super::id_hex(&cell)));
                let list = if count == 0 {
                    div()
                        .child("(empty) · no cells — seed genesis")
                        .into_any_element()
                } else {
                    // follow = false: an id-sorted census keeps the operator's
                    // place, it does not chase a tail. The closure materializes the
                    // canonical id order and indexes the visible window; the sort
                    // is the residual O(N log N)/frame (the *render*, not the sort,
                    // was the cap — that is what virtualization lifts).
                    self.nt_virtual_face(
                        key,
                        list_id,
                        count,
                        we::LEDGER_ROW_H,
                        false,
                        cx,
                        |this, range, _w, _cx| {
                            if let Some(p) = this.rewind.projection() {
                                let mut cells: Vec<(&CellId, &Cell)> = p.ledger.iter().collect();
                                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                                range
                                    .filter_map(|i| {
                                        cells.get(i).map(|pair| we::ledger_row(pair.0, pair.1))
                                    })
                                    .collect()
                            } else {
                                let w = this.world.borrow();
                                let mut cells: Vec<(&CellId, &Cell)> = w.ledger().iter().collect();
                                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                                range
                                    .filter_map(|i| {
                                        cells.get(i).map(|pair| we::ledger_row(pair.0, pair.1))
                                    })
                                    .collect()
                            }
                        },
                    )
                };
                let face = div()
                    .flex_1()
                    .min_h(px(0.0))
                    .flex()
                    .flex_col()
                    .bg(gpui::rgb(NT_PANEL))
                    .p_2()
                    .gap_1()
                    .child(we::ledger_header(count))
                    .child(list)
                    .into_any_element();
                we::with_replay_banner(banner, face)
            }
        }
    }

    /// **Render the Rewind Rail layer** — the amber "≠ NOW" rings around icons
    /// whose state at the cursor differs from live, then the rail itself
    /// (docked above the taskbar, painted over the windows so the timeline is
    /// always in hand). The projection was refreshed at the top of `render`.
    pub(super) fn render_rewind_layer(&self, cx: &mut Context<Self>) -> Vec<AnyElement> {
        let mut out: Vec<AnyElement> = Vec::new();

        // ── The changed-cell rings (only while scrubbing) ────────────────────
        if let Some(p) = self.rewind.projection() {
            for (idx, cell) in self.cells.iter().enumerate() {
                if !p.changed.contains(cell) || p.ledger.get(cell).is_none() {
                    continue;
                }
                let pos = self.icon_pos(idx, cell);
                out.push(
                    div()
                        .absolute()
                        .left(px(pxf(pos.x) - 3.0))
                        .top(px(pxf(pos.y) - 3.0))
                        .w(px(ICON_W + 6.0))
                        .h(px(ICON_H + 6.0))
                        .border_2()
                        .border_color(gpui::rgb(NT_WARN))
                        .rounded(px(3.0))
                        .into_any_element(),
                );
            }
        }

        // ── The rail ─────────────────────────────────────────────────────────
        let (total, live_height, live_root) = {
            let w = self.world.borrow();
            let h = w.recorded_turns();
            (h.len(), w.height(), h.root_at(h.len()))
        };
        let scrub = self.rewind.projection();
        let scrubbing = scrub.is_some();
        let vw = self.last_viewport.0;
        let track_w = (vw - RAIL_TRACK_LEFT - RAIL_TRACK_RIGHT).max(48.0);
        let cursor_step = scrub.map(|p| p.step).unwrap_or(total);
        let frac = if total == 0 {
            1.0
        } else {
            cursor_step as f32 / total as f32
        };

        let mut rail = div()
            .id("rewind-rail")
            .absolute()
            .left(px(0.0))
            .bottom(px(RAIL_BOTTOM))
            .w_full()
            .h(px(RAIL_H))
            .bg(gpui::rgb(NT_FACE))
            .border_t_1()
            .border_color(gpui::rgb(if scrubbing { NT_WARN } else { NT_FACE_DARK }));

        // The left caption — the rail names itself + its length (or its mode).
        rail = rail.child(
            div()
                .absolute()
                .left(px(6.0))
                .top(px(5.0))
                .text_size(px(9.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(if scrubbing { NT_WARN } else { NT_TEXT }))
                .child(if scrubbing {
                    "REWIND · REPLAYED".to_string()
                } else {
                    format!("REWIND · {total} steps")
                }),
        );

        // The scrub track — sunken NT well; click/drag maps x → step. The knob
        // and ticks are inert children (gpui bubbles their clicks up here).
        let mut track = bevel_sunken(
            div()
                .id("rewind-track")
                .absolute()
                .left(px(RAIL_TRACK_LEFT))
                .top(px(4.0))
                .w(px(track_w))
                .h(px(14.0))
                .bg(gpui::rgb(NT_FACE_DARK)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(|this, ev: &MouseDownEvent, _w, cx| {
                let total = this.world.borrow().recorded_turns().len();
                let step = step_at_x(pxf(ev.position.x), this.last_viewport.0, total);
                this.drag = Some(Drag::Rewind);
                this.rewind_scrub_to(step);
                cx.notify();
            }),
        );
        // The 0..cursor progress fill — navy at LIVE (full), amber in the past.
        track = track.child(
            div()
                .absolute()
                .left(px(0.0))
                .top(px(0.0))
                .h_full()
                .w(px(track_w * frac))
                .bg(gpui::rgb(if scrubbing { NT_WARN } else { NT_TITLE_ACTIVE }))
                .opacity(0.45),
        );
        // One tick per step (thinned past ~48 so a long history stays legible).
        if total > 0 {
            let every = (total / 48).max(1);
            for s in (0..=total).step_by(every) {
                let x = (track_w * (s as f32 / total as f32)).min(track_w - 1.0);
                track = track.child(
                    div()
                        .absolute()
                        .left(px(x))
                        .top(px(0.0))
                        .w(px(1.0))
                        .h_full()
                        .bg(gpui::rgb(NT_SHADOW))
                        .opacity(0.4),
                );
            }
        }
        // The knob — a raised NT thumb at the cursor.
        let knob_x = (track_w * frac - KNOB_W / 2.0).clamp(0.0, (track_w - KNOB_W).max(0.0));
        track = track.child(bevel_raised(
            div()
                .absolute()
                .left(px(knob_x))
                .top(px(1.0))
                .w(px(KNOB_W))
                .h(px(12.0)),
        ));
        rail = rail.child(track);

        // The stamp readout — the scrubbed root verdict + receipt/timestamp,
        // or the live head root. Dense, right of the track.
        let stamp_text = match scrub {
            Some(p) => format!(
                "root {} {} · {}",
                hex8(&p.root),
                if p.verified {
                    "✓"
                } else {
                    "!! ROOT MISMATCH"
                },
                stamp_caption(p)
            ),
            None => format!(
                "LIVE · height {live_height} · head root {}",
                hex8(&live_root)
            ),
        };
        rail = rail.child(
            div()
                .absolute()
                .right(px(88.0))
                .top(px(6.0))
                .w(px(264.0))
                .text_size(px(9.0))
                .text_color(gpui::rgb(if scrubbing { NT_WARN } else { NT_DIM }))
                .child(stamp_text),
        );

        // The LIVE chip — the prominent return. Amber + clickable in the past;
        // a calm pressed-in "LIVE" verdict at the head.
        let chip = div()
            .id("rewind-live-chip")
            .absolute()
            .right(px(6.0))
            .top(px(3.0))
            .w(px(74.0))
            .h(px(16.0))
            .flex()
            .items_center()
            .justify_center()
            .text_size(px(10.0))
            .font_weight(FontWeight::BOLD);
        let chip = if scrubbing {
            bevel_raised(chip)
                .bg(gpui::rgb(NT_WARN))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
                .hover(|s| s.bg(gpui::rgb(NT_TITLE_ACTIVE)))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                        this.rewind_go_live();
                        cx.notify();
                    }),
                )
                .child("> LIVE")
        } else {
            bevel_sunken(chip)
                .text_color(gpui::rgb(NT_OK))
                .child("LIVE")
        };
        rail = rail.child(chip);

        out.push(rail.into_any_element());
        out
    }

    // ── Bake / test hooks (drive the rail headlessly) ────────────────────────────

    /// Scrub the desktop to history step `h` (what dragging the rail there does).
    pub fn bake_rewind_to(&mut self, h: u64) {
        self.rewind_scrub_to(h);
    }

    /// Snap back to LIVE (what clicking the rail's LIVE chip does).
    pub fn bake_rewind_live(&mut self) {
        self.rewind_go_live();
    }

    /// The EFFECTIVE census length — how many cells the desktop currently reads
    /// truth from: the replayed ledger's census while scrubbing, the live one at
    /// LIVE. A bake asserts the census at an early height DIFFERS from live.
    pub fn bake_rewind_census_len(&self) -> usize {
        self.with_effective_ledger(|l| l.len())
    }

    /// Whether the scrubbed reconstruction reproduced the recorded root tooth
    /// (`None` at LIVE — there is nothing replayed to verify).
    pub fn bake_rewind_root_verified(&self) -> Option<bool> {
        self.rewind.projection().map(|p| p.verified)
    }

    /// The rail's receipt stamp at the cursor (`None` at LIVE) — hash +
    /// timestamp, for bakes that assert the readout names the real receipt.
    pub fn bake_rewind_stamp(&self) -> Option<String> {
        self.rewind.projection().map(stamp_caption)
    }

    /// A cell's balance through the effective read path — while scrubbed this
    /// is the PAST balance (the same value the icon/inspector shows).
    pub fn bake_rewind_balance(&self, cell: CellId) -> i64 {
        self.cell_balance(&cell)
    }
}

// ===========================================================================
// Tests — the pure replay projection (no gpui, no window)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// Two genesis cells + two committed transfers — 4 recorded steps, live
    /// balances a=850 / b=150 (mirrors the `replay.rs` fixture, but through a
    /// real `World` so the desktop's own recording path is what's under test).
    fn seeded_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let t = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t).is_committed());
        let t = w.turn(a, vec![transfer(a, b, 50)]);
        assert!(w.commit_turn(t).is_committed());
        (w, a, b)
    }

    #[test]
    fn census_at_an_early_height_differs_from_live() {
        let (w, _a, _b) = seeded_world();
        let h = w.recorded_turns();
        assert_eq!(h.len(), 4, "2 genesis + 2 turns");
        // Step 1: only the first genesis cell exists — the past census is
        // smaller than the live one (the bake_rewind_census_len assertion).
        let p = project(h, w.ledger(), 1);
        assert!(p.verified, "the reconstruction must reproduce the tooth");
        assert_eq!(p.ledger.len(), 1);
        assert_ne!(p.ledger.len(), w.ledger().len(), "live census is 2");
        // Step 0 is the pre-genesis void: no cells, no receipts, no stamp.
        let p0 = project(h, w.ledger(), 0);
        assert!(p0.verified);
        assert_eq!(p0.ledger.len(), 0);
        assert!(p0.stamp.is_none());
        assert!(p0.receipts.is_empty());
    }

    #[test]
    fn replayed_balances_root_tooth_and_receipt_stamp() {
        let (w, a, b) = seeded_world();
        let h = w.recorded_turns();
        // Step 2: both genesis installs, no transfers yet.
        let p = project(h, w.ledger(), 2);
        assert!(p.verified);
        assert_eq!(p.root, h.root_at(2), "the projection carries the tooth");
        assert_eq!(p.ledger.get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(p.ledger.get(&b).unwrap().state.balance(), 0);
        // The diff vs live names exactly the cells the later transfers moved.
        assert!(p.changed.contains(&a) && p.changed.contains(&b));
        // Step 3: after the first transfer — one receipt, and the stamp IS it
        // (recomputed hash + the deterministic executor timestamp).
        let p3 = project(h, w.ledger(), 3);
        assert_eq!(p3.ledger.get(&a).unwrap().state.balance(), 900);
        assert_eq!(p3.ledger.get(&b).unwrap().state.balance(), 100);
        assert_eq!(p3.receipts.len(), 1);
        let s = p3.stamp.as_ref().expect("a committed step has a stamp");
        assert_eq!(s.receipt_hash, p3.receipts[0].receipt_hash());
        assert_eq!(s.timestamp, p3.receipts[0].timestamp);
        assert_eq!(s.agent, a);
        // The captions surface the same truth (the rail's readouts).
        assert!(rail_caption(&p3).contains("step 3/4"));
        assert!(rail_caption(&p3).contains(&hex8(&p3.root)));
        assert!(rail_caption(&p3).contains('✓'));
        assert!(stamp_caption(&p3).contains(&hex8(&s.receipt_hash)));
    }

    #[test]
    fn head_projection_matches_live_and_out_of_range_clamps() {
        let (w, _a, _b) = seeded_world();
        let h = w.recorded_turns();
        let p = project(h, w.ledger(), h.len());
        assert!(p.verified);
        assert!(p.changed.is_empty(), "the head replay diffs empty vs live");
        assert_eq!(p.ledger.len(), w.ledger().len());
        assert_eq!(p.receipts.len(), 2);
        // A cursor past the head clamps to the head (the drag can overshoot).
        let p_over = project(h, w.ledger(), 999);
        assert_eq!(p_over.step, h.len());
        assert_eq!(p_over.root, p.root);
    }

    #[test]
    fn ensure_memoizes_and_live_turns_lengthen_the_rail() {
        let (mut w, a, b) = seeded_world();
        let mut rs = RewindState::default();
        assert!(rs.is_live() && rs.projection().is_none());
        rs.cursor = Some(2);
        rs.ensure(&w);
        let (step0, total0) = {
            let p = rs.projection().expect("scrubbed → projection");
            (p.step, p.total)
        };
        assert_eq!((step0, total0), (2, 4));
        // Same cursor, no new history → the memo holds (same step/total).
        rs.ensure(&w);
        let p = rs.projection().unwrap();
        assert_eq!((p.step, p.total), (2, 4));
        // A LIVE turn lands while the cursor sits in the past → the rail
        // lengthens (total grows) and the cursor stays planted at its step.
        let t = w.turn(b, vec![transfer(b, a, 10)]);
        assert!(w.commit_turn(t).is_committed());
        rs.ensure(&w);
        let p = rs.projection().unwrap();
        assert_eq!((p.step, p.total), (2, 5));
        // The planted past still reads its own truth, not the new head's.
        assert_eq!(p.ledger.get(&a).unwrap().state.balance(), 1_000);
        // GO LIVE drops both cursor and projection.
        rs.go_live();
        assert!(rs.is_live() && rs.projection().is_none());
    }

    #[test]
    fn step_at_x_maps_the_track_ends_and_midpoint() {
        // Left of the track → step 0; far right → the head; the middle → N/2.
        assert_eq!(step_at_x(0.0, 1600.0, 10), 0);
        assert_eq!(step_at_x(10_000.0, 1600.0, 10), 10);
        let mid = RAIL_TRACK_LEFT + (1600.0 - RAIL_TRACK_LEFT - RAIL_TRACK_RIGHT) / 2.0;
        assert_eq!(step_at_x(mid, 1600.0, 10), 5);
        // An empty history always maps to step 0 (nothing to scrub).
        assert_eq!(step_at_x(500.0, 1600.0, 0), 0);
    }
}
