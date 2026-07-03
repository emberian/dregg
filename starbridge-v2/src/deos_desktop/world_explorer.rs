//! **The World Explorer** — the "My Computer" of the verified World.
//!
//! A tabbed, read-only Pharo-moldable inspector over the live dregg [`World`]
//! ITSELF (not a single cell): the dense Windows-NT census of every sovereign
//! cell, the World's witnessed receipt history, and the Σ-balance conservation
//! invariant the operator can SEE hold at zero.
//!
//! This surface is pure presentation: each face is a scrolling `div()` element
//! tree built from a [`WorldLens`] — one read-only view of A world state
//! (ledger + receipts + height), either the LIVE `World` ([`WorldLens::live`])
//! or the Rewind Rail's root-verified REPLAYED projection at a scrubbed step
//! (built in [`super::rewind`]; it arrives wearing an amber `banner` so the
//! face names its own liveness). The file carries no view context
//! (`Context<DeosDesktop>`) and no interactivity inside the faces. The
//! clickable tab strip is owned by the window-dispatch caller (which holds the
//! view context); this module supplies the tab vocabulary
//! ([`WorldExplorerTab`]) + the per-tab body renderer
//! ([`render_world_explorer_body`]).

use gpui::{
    div, px, AnyElement, FontWeight, InteractiveElement, IntoElement, ParentElement,
    StatefulInteractiveElement, Styled,
};

use dregg_cell::{lifecycle::CellLifecycle, Cell, Ledger};
use dregg_turn::turn::TurnReceipt;
use dregg_types::CellId;

use crate::deos_desktop::chrome::{
    face_gauge, face_row, face_row_color, face_section, fmt_balance, id_short, NT_DIM, NT_OK,
    NT_PANEL, NT_TITLE_TEXT, NT_WARN,
};
use crate::world::World;

/// **One read-only view of a world state** — the faces' single input, so the
/// SAME pure render draws the live World and the Rewind Rail's replayed past.
/// Borrowed, never owning: the live lens borrows straight off [`World`]; the
/// replayed lens borrows the projection's reconstructed ledger + the receipts
/// that existed AT the scrubbed step.
pub struct WorldLens<'a> {
    /// The census to render (live ledger, or the root-verified reconstruction).
    pub ledger: &'a Ledger,
    /// The receipt log AT this view (truncated to the cursor while replaying).
    pub receipts: &'a [TurnReceipt],
    /// The world height at this view (committed-turn count).
    pub height: u64,
    /// The census size (kept explicit so the header agrees with `ledger`).
    pub cell_count: usize,
    /// `Some(caption)` when this lens is a REPLAYED past projection — each face
    /// paints it as an amber banner row so the surface names its own liveness
    /// (`ui_snapshot`'s honesty discipline). `None` = the live World.
    pub banner: Option<String>,
}

impl<'a> WorldLens<'a> {
    /// The live World's lens — what every face read before the Rewind Rail.
    pub fn live(world: &'a World) -> Self {
        WorldLens {
            ledger: world.ledger(),
            receipts: world.receipts(),
            height: world.height(),
            cell_count: world.cell_count(),
            banner: None,
        }
    }
}

/// The three faces of the World Explorer — the moldable multiplicity over the
/// World as a whole. Each is a read-only projection the operator browses.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub enum WorldExplorerTab {
    /// The dense NT census of every cell — id, kind, balance, lifecycle, nonce.
    #[default]
    Ledger,
    /// The receipt log — the World's witnessed history, newest last.
    Chronicle,
    /// The Σ-balance invariant face — total balance (reads 0), counts, and the
    /// per-cell breakdown so Σδ = 0 is visible.
    Conservation,
}

impl WorldExplorerTab {
    /// The tab caption the caller draws on the clickable strip.
    pub fn label(self) -> &'static str {
        match self {
            WorldExplorerTab::Ledger => "Ledger",
            WorldExplorerTab::Chronicle => "Chronicle",
            WorldExplorerTab::Conservation => "Conservation",
        }
    }

    /// Every tab, in display order — the caller iterates this to build the strip.
    pub const ALL: [WorldExplorerTab; 3] = [
        WorldExplorerTab::Ledger,
        WorldExplorerTab::Chronicle,
        WorldExplorerTab::Conservation,
    ];
}

/// The per-window view state of a World Explorer surface — which face is shown.
/// The caller holds this keyed by a sentinel cell and flips `tab` on a tab click.
#[derive(Clone, Default)]
pub struct WorldExplorerState {
    pub tab: WorldExplorerTab,
}

/// Render the BODY for the selected tab as a pure gpui element tree.
///
/// The faces are read-only lists over the `lens` (the live World, or the
/// Rewind Rail's replayed projection — same render either way); the clickable
/// tab strip above this body is built by the caller (it owns the view context
/// the tab listeners need). Long lists are capped (~24 rows) to keep the dense
/// view legible, the way the transcript surface does. A replayed lens gets its
/// amber banner stacked above the face so the past never masquerades as live.
pub fn render_world_explorer_body(lens: &WorldLens, tab: WorldExplorerTab) -> AnyElement {
    let face = match tab {
        WorldExplorerTab::Ledger => render_ledger_face(lens),
        WorldExplorerTab::Chronicle => render_chronicle_face(lens),
        WorldExplorerTab::Conservation => render_conservation_face(lens),
    };
    match &lens.banner {
        None => face,
        Some(caption) => div()
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .child(
                div()
                    .px_2()
                    .py_1()
                    .bg(gpui::rgb(NT_WARN))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
                    .text_size(px(10.0))
                    .font_weight(FontWeight::BOLD)
                    .child(caption.clone()),
            )
            .child(face)
            .into_any_element(),
    }
}

/// Classify a cell by its balance — replicated from `DeosDesktop::cell_kind`
/// (an issuer well carries −supply, a treasury a large positive balance, a
/// zero-balance cell is a service, everything else an account). Kept byte-for-byte
/// with the inspector's classifier so the two surfaces agree on a cell's kind.
fn cell_kind(cell: &Cell) -> &'static str {
    let b = cell.state.balance();
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

/// The cell's lifecycle as a short label — replicated from
/// `DeosDesktop::cell_lifecycle` (off the cell's `lifecycle` field directly).
fn cell_lifecycle(cell: &Cell) -> &'static str {
    match cell.lifecycle {
        CellLifecycle::Live => "Live",
        CellLifecycle::Sealed { .. } => "Sealed",
        CellLifecycle::Migrated { .. } => "Migrated",
        CellLifecycle::Destroyed { .. } => "Destroyed",
        CellLifecycle::Archived { .. } => "Archived",
    }
}

// ── LEDGER: the dense NT census of every cell ───────────────────────────────────

/// The LEDGER face — a browsable list of every cell, sorted by id, each showing
/// its short id, kind, balance, lifecycle, and nonce. The My-Computer census.
/// Over a replayed lens this is the census AS IT WAS — since-destroyed cells
/// reappear, not-yet-born ones are absent.
fn render_ledger_face(lens: &WorldLens) -> AnyElement {
    let ledger = lens.ledger;
    // Sort by id for a stable, browsable census (the same canonical order the
    // image root folds over).
    let mut cells: Vec<(&CellId, &Cell)> = ledger.iter().collect();
    cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    let n = cells.len();

    let mut col = div()
        .id("world-explorer-ledger")
        .flex_1()
        .min_h(px(0.0))
        .overflow_y_scroll()
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section(&format!("World cells · {n} cells")));

    if n == 0 {
        return col
            .child(face_row("(empty)", "no cells — seed genesis"))
            .into_any_element();
    }

    // Cap the dense census so a large World stays legible (newest ids are no more
    // salient than oldest here, so we show the first ~24 in id order).
    let cap = 24usize;
    for (id, cell) in cells.iter().take(cap) {
        let bal = cell.state.balance();
        let kind = cell_kind(cell);
        let life = cell_lifecycle(cell);
        let nonce = cell.state.nonce();
        // An issuer well (negative) reads amber, a Live account reads neutral.
        let bal_color = if bal < 0 { NT_WARN } else { 0x101010 };
        col = col.child(
            div()
                .flex()
                .flex_row()
                .gap_1()
                .text_size(px(11.0))
                .child(
                    div()
                        .w(px(72.0))
                        .text_color(gpui::rgb(0x000080))
                        .font_weight(FontWeight::BOLD)
                        .child(id_short(id)),
                )
                .child(div().w(px(76.0)).text_color(gpui::rgb(NT_DIM)).child(kind))
                .child(
                    div()
                        .flex_1()
                        .text_color(gpui::rgb(bal_color))
                        .child(fmt_balance(bal)),
                )
                .child(div().w(px(64.0)).child(life))
                .child(
                    div()
                        .w(px(56.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("n{nonce}")),
                ),
        );
    }
    if n > cap {
        col = col.child(face_row("…", &format!("{} more cells", n - cap)));
    }
    col.into_any_element()
}

// ── CHRONICLE: the World's witnessed receipt history ────────────────────────────

/// The CHRONICLE face — the last ~24 receipts, each showing the commit index,
/// turn-hash (first 4 bytes), post-state-hash (first 4 bytes), the agent cell,
/// and the computrons it spent. The World's navigable history.
fn render_chronicle_face(lens: &WorldLens) -> AnyElement {
    let receipts = lens.receipts;
    let n = receipts.len();

    let mut col = div()
        .id("world-explorer-chronicle")
        .flex_1()
        .min_h(px(0.0))
        .overflow_y_scroll()
        .bg(gpui::rgb(0x101820))
        .text_color(gpui::rgb(0x9fe0a0))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
            "── World chronicle · {n} turns · height {} ",
            lens.height
        )));

    if n == 0 {
        return col
            .child(div().child("(no turns yet — actuate a cell)"))
            .into_any_element();
    }

    // The last ~24 receipts, newest last (the dense scrolling log).
    let start = n.saturating_sub(24);
    for (i, r) in receipts.iter().enumerate().skip(start) {
        let hh: String = r.turn_hash[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let post: String = r.post_state_hash[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        col = col.child(div().text_size(px(11.0)).child(format!(
            "#{i:<4} turn {hh} → post {post}  agent {}  · {}cu",
            id_short(&r.agent),
            r.computrons_used
        )));
    }
    col.into_any_element()
}

// ── CONSERVATION: the Σδ = 0 invariant, made visible ────────────────────────────

/// The CONSERVATION face — the Σ-balance invariant the World keeps at zero
/// (issuer wells negative, accounts positive). Shows the total balance (which
/// MUST read 0), the cell/height/receipt counts, and the per-cell breakdown so
/// the operator SEES Σδ = 0 hold across the live ledger.
fn render_conservation_face(lens: &WorldLens) -> AnyElement {
    let ledger = lens.ledger;
    let mut cells: Vec<(&CellId, &Cell)> = ledger.iter().collect();
    cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

    let sum: i64 = cells.iter().map(|(_, c)| c.state.balance()).sum();
    let cell_count = lens.cell_count;
    let height = lens.height;
    let receipts = lens.receipts.len();
    // Σ reads green at the invariant (0), amber if it ever drifts — the operator's
    // at-a-glance conservation verdict.
    let sum_color = if sum == 0 { NT_OK } else { NT_WARN };

    let mut col = div()
        .id("world-explorer-conservation")
        .flex_1()
        .min_h(px(0.0))
        .overflow_y_scroll()
        .bg(gpui::rgb(NT_PANEL))
        .p_2()
        .flex()
        .flex_col()
        .gap_1()
        .child(face_section("Conservation (Σδ = 0)"))
        .child(face_row_color("Σ balance", &fmt_balance(sum), sum_color))
        .child(face_row_color(
            "invariant",
            if sum == 0 {
                "holds (Σ = 0)"
            } else {
                "DRIFTED"
            },
            sum_color,
        ))
        .child(face_section("World census"))
        .child(face_row("cells", &cell_count.to_string()))
        .child(face_row("height", &height.to_string()))
        .child(face_row("receipts", &receipts.to_string()))
        .child(face_section("Per-cell balance breakdown"));

    if cells.is_empty() {
        return col
            .child(face_row("(empty)", "no cells — seed genesis"))
            .into_any_element();
    }

    // The largest magnitude balance — the gauge denominator so each cell's bar is
    // legible relative to the World's biggest holder/well.
    let max_mag = cells
        .iter()
        .map(|(_, c)| c.state.balance().unsigned_abs())
        .max()
        .unwrap_or(1)
        .max(1);

    // Issuer wells (negative) read amber; accounts (positive) read green; a
    // zero-balance service reads dim. The signed rows make Σδ = 0 visible: the
    // amber wells and green accounts cancel.
    let cap = 24usize;
    for (id, cell) in cells.iter().take(cap) {
        let bal = cell.state.balance();
        let color = if bal < 0 {
            NT_WARN
        } else if bal > 0 {
            NT_OK
        } else {
            NT_DIM
        };
        let ratio = (bal.unsigned_abs() as f32) / (max_mag as f32);
        col = col
            .child(face_row_color(&id_short(id), &fmt_balance(bal), color))
            .child(face_gauge(ratio));
    }
    if cells.len() > cap {
        col = col.child(face_row("…", &format!("{} more cells", cells.len() - cap)));
    }
    col.into_any_element()
}
