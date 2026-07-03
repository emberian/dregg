//! **THE REFLECTIVE-COCKPIT PANE** — a desktop window whose body IS a real
//! [`deos_view::ViewNode`] (a card-as-cell), rendered through deos-view's NATIVE
//! renderer, AND the surface a confined agent reflects-on then rewrites LIVE.
//!
//! Every other desktop window is raw native gpui chrome (the NT inspector, the
//! World Explorer, the Document Explorer): the shell paints those directly. THIS
//! window proves the shell can ALSO host PORTABLE-IR content — a view-tree authored
//! as backend-independent DATA ([`deos_view::ViewNode`], the Rust mirror of the
//! `deos.ui.*` element-tree) and walked into pixels by the SAME renderer
//! ([`deos_view::AppletView`]) the card-pane / cockpit use, the SAME tree a web
//! renderer would walk into HTML ([`deos_view::web`]). One IR, two backends; the
//! native desktop is one of them.
//!
//! ## The reflective surface — a World-Status panel
//!
//! The surface hosted here is the canonical **World-Status panel** the reflective-
//! cockpit loop (`deos-view/tests/agent_reflects_and_rewrites_a_surface_live.rs`,
//! `0c3e567b`) proved over a headless render: a titled header over three live `bind`
//! rows (cells · receipts · refreshes) with a `refresh` affordance. That test proved
//! the loop over a deos-view render in isolation; THIS lifts the SAME panel source up
//! into the SHIPPED desktop window, so the loop runs against a real cockpit pane:
//!
//!   1. REFLECT-ON — the host reads the live surface's own view-tree
//!      ([`AppletView::tree`]); a confined agent's JS reads the same tree through
//!      `deos.editor.view()`. A pure read — no patch, no turn.
//!   2. REWRITE — the agent's JS adds a `refresh` button + relabels the header
//!      (`World Status` → `World Status (live)`) through `deos.editor.editView`. Each
//!      gesture is a RECEIPTED patch blamed on the agent (the proven `CardEditor`
//!      machinery), bounded by the authoring cap tooth.
//!   3. THE LIVE SURFACE RE-RENDERS — the re-folded tree is swapped into the SAME live
//!      [`AppletView`] entity the desktop window hosts ([`AppletView::set_tree`]), so
//!      the real desktop window repaints the agent's rewrite (before/after differ).
//!
//! ## Light by construction
//!
//! The static panel ([`status_panel_tree`] / [`status_panel_applet`]) needs NO mozjs:
//! it parses a fixed [`status_panel_source`] and mints an embedded verified cell. Only
//! the agent REWRITE ([`agent_rewrite_status_panel`]) reaches the SpiderMonkey
//! authoring path — and only when the loop is driven.
//!
//! ## Live by the pulse — THE PULSE→SIGNALS WELD
//!
//! The panel's `bind` rows are not frozen seeds: every desktop pulse beat where the
//! LIVE World's census moved, [`pulse_panes`] fires the panel's census-tracking
//! affordances ([`STATUS_AFF_SET_CELLS`]/[`STATUS_AFF_SET_RECEIPTS`], each ONE real
//! receipted verified turn on the panel's embedded executor) and folds exactly the
//! touched slots through the renderer's signal registry
//! ([`deos_view::AppletView::on_world_events`]) — so a foreign turn anywhere on the
//! World repaints exactly the dirty rows, wearing a one-beat dirty glow.
//!
//! Gated on `card-pane` (which pulls `deos-view` + `deos-js` via `agent-js`); the
//! desktop's window-type registration falls back to the inspector body when the
//! feature is off, so the gpui-free / headless builds still compile.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use gpui::{App, AppContext, Entity};

use deos_js::applet::Slot;
use deos_js::card_editor::{Author, BindProps, CardEditor, TextProps, ViewTree as EditorViewTree};
use deos_js::portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
use deos_js::signals::BindingId;
use deos_js::{Applet, JsRuntime};
use deos_view::{parse_view_tree, AppletView, SharedApplet, ViewNode};
use dregg_cell::AuthRequired;
use dregg_types::CellId;

/// The status panel's model slots — the live values its `bind` rows re-read off the
/// ledger (a status face is a function of state). `refreshes` is what the panel's
/// `refresh` affordance bumps (the affordance the agent's rewrite adds a button for).
pub const STATUS_SLOT_CELLS: Slot = 0;
pub const STATUS_SLOT_RECEIPTS: Slot = 1;
pub const STATUS_SLOT_REFRESHES: Slot = 2;

/// **The census-tracking affordances — THE PULSE→SIGNALS WELD's write verbs.** Each
/// pulse beat where the LIVE World's census moved, the desktop fires these on the
/// panel's embedded applet with `arg = the new reading` (`ApplyOp::SetSlotFromArg`):
/// a REAL receipted verified turn per moved reading, so the panel's `bind` rows
/// re-read COMMITTED state — the mirroring itself is on the audit tape, never a
/// side-channel poke into the model.
pub const STATUS_AFF_SET_CELLS: &str = "set_cells";
pub const STATUS_AFF_SET_RECEIPTS: &str = "set_receipts";

/// The witnessed values seeded into the panel's rows — so the `bind`s paint real values
/// on first paint (before any turn fires).
pub const STATUS_SEED_CELLS: u64 = 3;
pub const STATUS_SEED_RECEIPTS: u64 = 12;
pub const STATUS_SEED_REFRESHES: u64 = 0;

/// The window title shown above the IR-rendered body (the surface chrome).
pub const STATUS_PANEL_TITLE: &str = "World Status · deos_view::ViewNode";

/// The agent's blame identity — every patch the agent's rewrite lands is attributed to
/// it (the accountable-patch face: the surface rewrites are blamed on the AGENT).
pub const AGENT_AUTHOR: Author = Author(99);

/// **The reflect-then-rewrite script a confined agent runs against the live surface.**
/// (0) REFLECT-ON — read the surface's own view-tree (`deos.editor.view()`) and confirm
/// it carries the header + three status rows IT DID NOT AUTHOR; (1) REWRITE — add a
/// `refresh` button (fires the panel's real `refresh` affordance) and (2) relabel the
/// header. Returns 1 only if the reflect saw the pre-existing surface AND both rewrites
/// landed in the re-folded tree. This is the SAME script the `0c3e567b` loop proved.
pub const AGENT_REWRITE_JS: &str = r#"
    // (0) REFLECT-ON — read the live surface's OWN view-tree before touching it.
    // The agent did NOT build this surface; it is reading a real cockpit panel.
    var surface = deos.editor.view();
    var sawHeader = false, statusRows = 0;
    (function walk(n) {
        if (!n) return;
        if (n.kind === "text" && n.props && n.props.text === "World Status") sawHeader = true;
        if (n.kind === "bind") statusRows += 1;
        var kids = n.children || [];
        for (var i = 0; i < kids.length; i++) walk(kids[i]);
    })(surface);
    var reflected = sawHeader && (statusRows === 3);

    // (1) REWRITE — add a `refresh` button (fires the panel's real `refresh` affordance).
    var card = deos.editor.card();
    deos.editor.editView(card, {
        op: "addButton", label: "refresh", affordance: "refresh", arg: 1
    });
    // (2) relabel the header "World Status" -> "World Status (live)".
    var tree = deos.editor.editView(card, {
        op: "relabel", target: "World Status", text: "World Status (live)"
    });

    var hasButton = false, relabelled = false;
    (function walk(n) {
        if (!n) return;
        if (n.kind === "button" && n.props && n.props.on_click &&
            n.props.on_click.turn === "refresh") hasButton = true;
        if (n.kind === "text" && n.props && n.props.text === "World Status (live)")
            relabelled = true;
        var kids = n.children || [];
        for (var i = 0; i < kids.length; i++) walk(kids[i]);
    })(tree);
    (reflected && hasButton && relabelled) ? 1 : 0;
"#;

/// **The World-Status panel AS structured view-source** — a titled header over three
/// live `bind` rows. The exact `{kind, props, children}` JSON the renderer's
/// [`parse_view_tree`] consumes AND the card-editor's `ViewTree` authors (so the
/// agent's rewrite splices it as patches). Built via the card-editor's `ViewTree` so the
/// shipped pane and the authoring path share ONE source shape.
pub fn status_panel_source() -> String {
    let view = EditorViewTree::VStack {
        children: vec![
            EditorViewTree::Text {
                props: TextProps {
                    text: "World Status".into(),
                },
            },
            EditorViewTree::Bind {
                props: BindProps {
                    slot: STATUS_SLOT_CELLS,
                    label: "cells: ".into(),
                },
            },
            EditorViewTree::Bind {
                props: BindProps {
                    slot: STATUS_SLOT_RECEIPTS,
                    label: "receipts: ".into(),
                },
            },
            EditorViewTree::Bind {
                props: BindProps {
                    slot: STATUS_SLOT_REFRESHES,
                    label: "refreshes: ".into(),
                },
            },
        ],
    };
    view.to_json()
}

/// The panel's portable manifest — its program (seed fields + the `refresh` affordance +
/// the census-tracking verbs [`STATUS_AFF_SET_CELLS`]/[`STATUS_AFF_SET_RECEIPTS`] the
/// pulse weld fires + the structured view source). The SAME manifest the static pane
/// mints from and the agent's `CardEditor` adopts (so the live surface and the authored
/// surface agree).
pub fn status_panel_manifest() -> AppletManifest {
    AppletManifest {
        seed_fields: vec![
            (STATUS_SLOT_CELLS, STATUS_SEED_CELLS),
            (STATUS_SLOT_RECEIPTS, STATUS_SEED_RECEIPTS),
            (STATUS_SLOT_REFRESHES, STATUS_SEED_REFRESHES),
        ],
        affordances: vec![
            AffordanceSpec {
                name: "refresh".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot {
                    slot: STATUS_SLOT_REFRESHES,
                },
            },
            // The Pulse→Signals weld's tracking verbs: `slot := max(arg, 0)` — the
            // desktop mirrors the LIVE World census into the panel's committed model
            // as receipted turns (see `pulse_panes`), so the shipped pane's binds
            // finally track the World instead of painting the frozen seeds forever.
            AffordanceSpec {
                name: STATUS_AFF_SET_CELLS.into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SetSlotFromArg {
                    slot: STATUS_SLOT_CELLS,
                },
            },
            AffordanceSpec {
                name: STATUS_AFF_SET_RECEIPTS.into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SetSlotFromArg {
                    slot: STATUS_SLOT_RECEIPTS,
                },
            },
        ],
        held: AuthRequired::Signature,
        view_source: status_panel_source(),
    }
}

/// Parse the panel's view-source into the typed [`ViewNode`] the NATIVE renderer
/// ([`AppletView`]) and the WEB renderer ([`deos_view::web`]) BOTH consume.
pub fn status_panel_tree() -> ViewNode {
    parse_view_tree(&status_panel_source()).expect("the World-Status panel source must parse")
}

/// Mint the panel's backing applet on a fresh EMBEDDED verified executor (no mozjs): one
/// sovereign cell seeded with the witnessed status values, carrying the `refresh`
/// affordance. A rendered `bind` reads a slot off this cell (a witnessed read); the
/// agent-added `refresh` button fires `refresh` = ONE cap-gated verified turn that bumps
/// the `refreshes` slot.
pub fn status_panel_applet() -> Applet {
    // A deterministic identity for the desktop's World-Status panel cell.
    let public_key = [0x57u8; 32]; // 'W' — World-Status
    let token_id = [0x1du8; 32];
    PortableApplet::mint(public_key, token_id, &status_panel_manifest())
}

/// **Build the World-Status pane** — a [`deos_view::AppletView`] gpui entity over the
/// panel's [`ViewNode`] backed by the embedded [`status_panel_applet`]. This IS
/// deos-view's native renderer; the desktop hosts the returned entity as a window body
/// (exactly as `dock::card_surface` hosts a `CardPane`), so a desktop window's body
/// becomes the reflective World-Status surface.
pub fn build_viewnode_view(cx: &mut App) -> Entity<AppletView> {
    let applet: SharedApplet = Rc::new(RefCell::new(status_panel_applet()));
    let tree = status_panel_tree();
    cx.new(|_cx| AppletView::new(applet, tree))
}

/// Render the SAME panel tree through the WEB renderer (HTML) — the renderer-
/// independence proof the bake asserts beside the live native pane. The web renderer
/// walks the IDENTICAL [`ViewNode`] [`build_viewnode_view`] hands the native renderer.
pub fn status_panel_html() -> String {
    let tree = status_panel_tree();
    deos_view::web::render_card_document(
        STATUS_PANEL_TITLE,
        &tree,
        &[
            STATUS_SEED_CELLS,
            STATUS_SEED_RECEIPTS,
            STATUS_SEED_REFRESHES,
        ],
    )
}

/// REFLECT-ON (host side) — walk a rendered [`ViewNode`] and report whether it carries
/// the `World Status` header and how many `bind` rows it has. The bake reads this off the
/// LIVE pane entity to prove the surface the agent reflects-on is the real one.
pub fn reflect_status(tree: &ViewNode) -> (bool, usize) {
    fn walk(n: &ViewNode, saw_header: &mut bool, rows: &mut usize) {
        match n {
            ViewNode::Text(s) if s == "World Status" => *saw_header = true,
            ViewNode::Bind { .. } => *rows += 1,
            ViewNode::VStack(kids)
            | ViewNode::Row(kids)
            | ViewNode::List(kids)
            | ViewNode::Table(kids) => {
                for k in kids {
                    walk(k, saw_header, rows);
                }
            }
            _ => {}
        }
    }
    let mut saw_header = false;
    let mut rows = 0;
    walk(tree, &mut saw_header, &mut rows);
    (saw_header, rows)
}

/// Walk a rendered [`ViewNode`] looking for the agent's `refresh` button.
pub fn tree_has_refresh_button(tree: &ViewNode) -> bool {
    match tree {
        ViewNode::Button { turn, .. } => turn == "refresh",
        ViewNode::VStack(kids)
        | ViewNode::Row(kids)
        | ViewNode::List(kids)
        | ViewNode::Table(kids) => kids.iter().any(tree_has_refresh_button),
        _ => false,
    }
}

/// The outcome of a confined agent reflecting-on + rewriting the World-Status surface.
pub struct RewriteResult {
    /// The agent's re-folded view-tree (a renderer re-paints it).
    pub after_tree: ViewNode,
    /// How many receipted provenance turns the rewrite gestures committed (addButton +
    /// relabel = 2).
    pub receipt_count: usize,
    /// Whether the surface's blame attributes the rewrites to the AGENT (accountable).
    pub blamed_agent: bool,
    /// Whether the re-folded tree carries the agent's `refresh` button.
    pub after_has_button: bool,
}

/// **Run the confined agent's reflect-then-rewrite loop over the World-Status panel** —
/// the proven `0c3e567b` machinery. Adopt the panel's manifest into a [`CardEditor`]
/// (held `None`, the panel's authoring needs `Signature` — but the panel is mounted as a
/// single-custody surface here, so authoring is admitted; the cap tooth still runs), run
/// [`AGENT_REWRITE_JS`] in real SpiderMonkey against it (the agent reads the surface, then
/// rewrites it as receipted patches), and hand back the re-folded tree + accountability.
///
/// SpiderMonkey is a process-global thread-bound singleton (its engine is one-shot per
/// process), so the runtime is created ONCE by the caller and threaded in — the same
/// `rt` drives the rewrite AND the [`world_board_editor`] compose loop.
pub fn agent_rewrite_status_panel(rt: &mut JsRuntime) -> Result<RewriteResult, String> {
    let manifest = status_panel_manifest();
    let card = status_panel_applet();
    // The editor holds `Signature`, which satisfies the panel's authoring authority
    // (`Signature`) — the cap tooth still runs before each gesture (an over-reach is
    // refused in-band; the `0c3e567b` test proves the refusal arm).
    let editor = CardEditor::adopt(
        card,
        manifest,
        AGENT_AUTHOR,
        AuthRequired::Signature,
        AuthRequired::Signature,
    );

    let (result, editor) = rt.run_authoring(editor, AGENT_REWRITE_JS)?;
    if result != Some(1) {
        return Err(format!(
            "the agent's reflect-then-rewrite run did not complete (returned {result:?})"
        ));
    }

    let after_source = editor.view_source();
    let after_tree = parse_view_tree(&after_source)?;
    let receipt_count = editor.card().receipt_count();
    let blamed_agent = editor.view_blame().iter().any(|l| l.author == AGENT_AUTHOR);
    let after_has_button = tree_has_refresh_button(&after_tree);

    Ok(RewriteResult {
        after_tree,
        receipt_count,
        blamed_agent,
        after_has_button,
    })
}

// ══════════════════════════════════════════════════════════════════════════════════
//  THE PULSE→SIGNALS WELD — every open card ticks when anyone moves the World
// ══════════════════════════════════════════════════════════════════════════════════
//
// The fine-grained invalidation machinery (deos-js's `BindingRegistry` + deos-view's
// `AppletView::on_world_events`) was only ever driven from tests: the shipped pane's
// `bind` rows painted from a never-invalidated cache, so the World-Status panel showed
// the frozen seeds 3/12/0 forever while the World moved underneath it. These functions
// are the desktop half of the weld — called from `pump_dynamics` (THE PULSE, the
// documented 250ms pull beat) over every open content-IR pane:
//
//   - QUIET half (every beat): retire last beat's dirty-glow tint; catch up turns the
//     pane's OWN embedded executor committed between beats (a button fired on the
//     surface itself — no dynamics stream names its slots).
//   - LOUD half (a beat where the World moved): broadcast the beat's
//     `WorldEvent::FieldSet`s into every pane's signal registry (an attached-cell card
//     bound to a touched `(cell, slot)` repaints EXACTLY its dirty binds), broadcast
//     the beat's CELL-WIDE `CellMutated`/`CapabilityRevoked` events through the
//     registry's conservative `invalidate_cell` tooth (`on_world_cells`), and mirror
//     the moved World census into the World-Status panel as RECEIPTED tracking turns
//     (`set_cells` / `set_receipts`, `ApplyOp::SetSlotFromArg`) — then fold exactly
//     those slots through the registry so the pane's binds re-read committed state.
//
//     (The SAME two broadcasts also feed every open attached-World CARD — see
//     `super::card_pulse`, the card half of this weld.)

/// The live World's census — the two readings the World-Status panel's first two
/// `bind` rows surface. The desktop reads it off the LIVE ledger each pulse beat and
/// the weld mirrors it into the panel's committed model when it moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorldCensus {
    /// How many cells the live ledger carries.
    pub cells: u64,
    /// How many verified turns have committed on the live World (the receipt tape).
    pub receipts: u64,
}

/// **The pure census-drive plan** — given the panel's CURRENT committed readings and
/// the live census, the `(affordance, slot, arg)` fires that bring the panel's model
/// up to date. Empty when the census did not move (the common, free beat). A pure
/// function so the weld's decision logic is unit-testable without gpui (see the
/// `tests` module).
pub fn census_plan(
    current_cells: u64,
    current_receipts: u64,
    census: WorldCensus,
) -> Vec<(&'static str, Slot, i64)> {
    let mut plan = Vec::new();
    if current_cells != census.cells {
        plan.push((STATUS_AFF_SET_CELLS, STATUS_SLOT_CELLS, census.cells as i64));
    }
    if current_receipts != census.receipts {
        plan.push((
            STATUS_AFF_SET_RECEIPTS,
            STATUS_SLOT_RECEIPTS,
            census.receipts as i64,
        ));
    }
    plan
}

/// **The QUIET half of one pulse beat** over every open content-IR pane — runs every
/// beat, even when the World did not move: (a) retire last beat's dirty-glow tint
/// ([`AppletView::fade_glow`] — a glow lasts exactly one beat), (b) catch up turns the
/// pane's OWN embedded executor committed between beats ([`AppletView::catch_up_own_turns`]
/// — a rendered button's fire names its slots in no dynamics stream, so the watermark
/// tooth re-reads the cell's binds; the pane's `refreshes` row finally ticks when its
/// own `refresh` button is pressed). Returns whether ANY pane needs a repaint.
pub fn pulse_panes_quiet(panes: &HashMap<CellId, Entity<AppletView>>, cx: &mut App) -> bool {
    let mut any = false;
    for entity in panes.values() {
        let changed = entity.update(cx, |view, cx| {
            let faded = view.fade_glow();
            let caught = !view.catch_up_own_turns().is_empty();
            if faded || caught {
                cx.notify();
            }
            faded || caught
        });
        any |= changed;
    }
    any
}

/// **The LOUD half of one pulse beat** — the World moved past the pulse cursor:
///
///   1. Broadcast the beat's projected `WorldEvent::FieldSet`s (`field_sets`, each a
///      `(cell, slot)` write on the LIVE World) into every pane's signal registry via
///      [`AppletView::on_world_events`]. The registry is keyed `(cell, slot)`, so a
///      pane whose binds never read a touched source stays perfectly still — and a
///      pane over an ATTACHED World cell repaints exactly its dirty binds.
///   1b. Broadcast the beat's CELL-WIDE events (`cell_events` — each a
///      `WorldEvent::CellMutated` / `CapabilityRevoked`, naming a cell but no slot;
///      wave 3 left them unprojected) through the registry's conservative
///      `invalidate_cell` tooth ([`AppletView::on_world_cells`]): every binding of a
///      touched cell re-reads (never under-invalidating), a cell no bind reads
///      dirties nothing.
///   2. For panes carrying the census-tracking verbs (the World-Status panel): fire
///      the [`census_plan`]'s `set_cells`/`set_receipts` affordances — one REAL
///      receipted verified turn per moved reading — then fold exactly those slots
///      through the registry so the binds re-read the committed values (and glow).
///
/// Returns whether ANY pane invalidated (its repaint was `notify`d here).
pub fn pulse_panes(
    panes: &HashMap<CellId, Entity<AppletView>>,
    field_sets: &[(CellId, Slot)],
    cell_events: &[CellId],
    census: WorldCensus,
    cx: &mut App,
) -> bool {
    let mut any = false;
    for entity in panes.values() {
        let changed = entity.update(cx, |view, cx| {
            let mut dirty = 0usize;

            // (1) The beat's World events, broadcast — only binds on a matching
            //     (cell, slot) source re-read (a foreign write never over-invalidates).
            if !field_sets.is_empty() {
                dirty += view.on_world_events(field_sets).len();
            }

            // (1b) The beat's cell-wide events — the conservative invalidate_cell
            //      tooth: a nonce bump / permissions write / cap revoke on a cell a
            //      bind reads re-reads that cell's bindings; foreign cells stay still.
            if !cell_events.is_empty() {
                dirty += view.on_world_cells(cell_events).len();
            }

            // (2) The census weld — only panes whose applet carries the tracking
            //     verbs (the World-Status panel; the board card does not) AND whose
            //     view actually SURFACES a census slot with a `bind` (the bot card
            //     borrows the panel applet as a bind-less placeholder backing — no
            //     row reads the census, so no tracking turn is spent on it).
            let surfaces_census = !view.bindings_reading(STATUS_SLOT_CELLS).is_empty()
                || !view.bindings_reading(STATUS_SLOT_RECEIPTS).is_empty();
            let applet = view.applet();
            let (own_cell, cur_cells, cur_receipts, tracks) = {
                let a = applet.borrow();
                (
                    a.cell(),
                    a.get_u64(STATUS_SLOT_CELLS),
                    a.get_u64(STATUS_SLOT_RECEIPTS),
                    a.affordance_specs()
                        .iter()
                        .any(|(n, _)| n == STATUS_AFF_SET_CELLS),
                )
            };
            if tracks && surfaces_census {
                let plan = census_plan(cur_cells, cur_receipts, census);
                if !plan.is_empty() {
                    let mut touched: Vec<(CellId, Slot)> = Vec::new();
                    for (aff, slot, arg) in plan {
                        // A REAL cap-gated verified turn on the pane's embedded
                        // executor — the mirrored reading is committed, receipted
                        // state. A refusal mirrors nothing (the pane stays honest).
                        match applet.borrow_mut().fire(aff, arg) {
                            Ok(_receipt) => touched.push((own_cell, slot)),
                            Err(e) => {
                                eprintln!("deos: census weld '{aff}' did not commit: {e}")
                            }
                        }
                    }
                    dirty += view.on_world_events(&touched).len();
                    // Our fires were exactly folded above — don't let the next quiet
                    // beat's watermark re-invalidate the whole cell for them.
                    view.mark_own_turns_seen();
                }
            }

            if dirty > 0 {
                cx.notify();
            }
            dirty > 0
        });
        any |= changed;
    }
    any
}

/// The witnesses of one PROVEN Pulse→Signals beat (the return of
/// `DeosDesktop::bake_foreign_turn_repaints_viewnode_binds`): a FOREIGN turn committed
/// on the live World — outside the pane, outside the desktop's own hand — moved the
/// receipts census, and the shipped World-Status pane repainted EXACTLY its receipts
/// bind, through a receipted tracking turn, with the one-beat dirty glow lit.
pub struct PulseWeldWitness {
    /// The pane's committed receipts reading after the CONVERGENCE beat — equal to the
    /// live World's receipts census right before the foreign turn.
    pub receipts_before: u64,
    /// The pane's committed receipts reading after the PROOF beat (what the bind now
    /// paints, re-read off the pane's ledger).
    pub receipts_after: u64,
    /// The live World's receipts census after the foreign turn — the truth the pane
    /// must now show (`receipts_after == live_receipts`).
    pub live_receipts: u64,
    /// The proof beat's dirty set (raw `BindingId` indices, driver-friendly).
    pub dirty: Vec<u64>,
    /// The glow set right after the proof beat — the accent tint on the glass.
    pub glowing: Vec<u64>,
    /// Whether the dirty set is EXACTLY the pane's receipts bind — the fine-grained
    /// bar (one foreign turn lit one row), pre-checked against the pane's own bind
    /// plan so the bake driver needs no deos-js types.
    pub dirty_is_exactly_receipts_bind: bool,
    /// How many receipted turns the PROOF beat committed on the pane's applet — the
    /// tracking write was a real verified turn (exactly 1: one `set_receipts` fire).
    pub weld_receipts_committed: usize,
}

/// The raw ids of the bindings in a pane's plan that read `slot` — the expected dirty
/// set for a census move on that slot (bake instrumentation).
pub fn bindings_reading(view: &AppletView, slot: Slot) -> Vec<u64> {
    view.bindings_reading(slot).iter().map(|b| b.0).collect()
}

/// Lower a `BindingId` dirty set to raw ids (bake instrumentation).
pub fn raw_ids(bindings: &[BindingId]) -> Vec<u64> {
    bindings.iter().map(|b| b.0).collect()
}

// ══════════════════════════════════════════════════════════════════════════════════
//  THE WORLD BOARD — the agent as a CO-AUTHOR of the live cockpit
// ══════════════════════════════════════════════════════════════════════════════════
//
// The `0c3e567b`/`b18447aa` loop proved the agent can REWRITE one pre-existing surface
// (the World-Status panel). This goes deeper: the agent COMPOSES a BRAND-NEW cockpit
// surface — a "World Board" — FROM AN EMPTY ROOT, informed by reading the live World,
// and the board is mounted as a REAL second `viewnode_pane` desktop window. The agent
// stops being an editor of the cockpit and becomes a co-author OF it:
//
//   1. REFLECT-ON  — the agent reads its OWN surface (`deos.editor.view()`) and finds a
//      bare, empty root: it is about to compose from nothing, not tweak an existing pane.
//   2. READ THE WORLD — it crawls the live ledger (`deos.world.cells()`) to DECIDE what
//      to surface (a witnessed read; confers no authority).
//   3. COMPOSE — from the empty root it authors every node: a title, three LIVE
//      state-bound rows (`addBind` — the new authoring primitive), and a `refresh`
//      button. Each gesture is a receipted patch blamed on the agent, cap-toothed.
//   4. MOUNT — the composed tree is painted by the SAME native renderer into a new
//      desktop window (a distinct `ViewNodePane`): the agent ADDED a cockpit surface.

/// The board card's model slots — the live values its `bind` rows surface (a status
/// face is a function of state). The host seeds these from its live-World read.
pub const BOARD_SLOT_CELLS: Slot = 0;
pub const BOARD_SLOT_RECEIPTS: Slot = 1;
pub const BOARD_SLOT_SUM: Slot = 2;
/// What the board's `refresh` affordance bumps (kept off the surfaced stat slots).
pub const BOARD_SLOT_REFRESHES: Slot = 3;

/// The window key the desktop hosts the agent-composed board under — a deterministic,
/// distinct cell so the board opens as its OWN `ViewNodePane` window (beside the
/// World-Status pane keyed on the user cell). Not the board applet's internal cell; it
/// is the window/HashMap key + the marker [`is_world_board`] reads.
pub fn world_board_window_cell() -> CellId {
    CellId::from_bytes([0x42u8; 32])
}

/// Whether `cell` keys the agent-composed World Board window (drives the pane header).
pub fn is_world_board(cell: &CellId) -> bool {
    cell == &world_board_window_cell()
}

/// **The agent's compose-from-scratch script.** (0) REFLECT-ON — read the agent's own
/// surface and confirm it is a bare EMPTY root (composing from nothing); (1) READ THE
/// WORLD — crawl the live ledger's real cells; (2) COMPOSE — from the empty root, author
/// a title + three live state-bound rows (`addBind`) + a `refresh` button. Returns the
/// crawled live-cell count on full success (a positive witness the host cross-checks
/// against its own ledger read), else 0. Each `editView` is a receipted, blamed,
/// cap-toothed patch — the SAME proven `CardEditor` machinery, now building a new surface.
pub const WORLD_BOARD_COMPOSE_JS: &str = r#"
    // (0) REFLECT-ON — the agent reads its OWN surface first: a bare, EMPTY root.
    var surface = deos.editor.view();
    var startedEmpty = surface && surface.kind === "vstack" &&
        (!surface.children || surface.children.length === 0);

    // (1) READ THE LIVE WORLD — crawl the REAL ledger to DECIDE what to surface.
    var n = deos.world.cells().length;

    // (2) COMPOSE A FRESH SURFACE FROM THE EMPTY ROOT — the agent authors every row of
    //     its OWN cockpit board: a title, three live state-bound rows, a refresh button.
    var card = deos.editor.card();
    deos.editor.editView(card, { op: "addText", text: "World Board" });
    deos.editor.editView(card, { op: "addBind", slot: 0, label: "live cells: " });
    deos.editor.editView(card, { op: "addBind", slot: 1, label: "receipts: " });
    deos.editor.editView(card, { op: "addBind", slot: 2, label: "conservation Σ: " });
    var tree = deos.editor.editView(card, {
        op: "addButton", label: "refresh", affordance: "refresh", arg: 1
    });

    // (3) WITNESS — the empty surface now carries the agent's composed board.
    var titled = false, binds = 0, hasButton = false;
    (function walk(node) {
        if (!node) return;
        if (node.kind === "text" && node.props && node.props.text === "World Board") titled = true;
        if (node.kind === "bind") binds += 1;
        if (node.kind === "button" && node.props && node.props.on_click &&
            node.props.on_click.turn === "refresh") hasButton = true;
        var kids = node.children || [];
        for (var i = 0; i < kids.length; i++) walk(kids[i]);
    })(tree);

    (startedEmpty && n >= 1 && titled && binds === 3 && hasButton) ? n : 0;
"#;

/// The board card's portable manifest — an **EMPTY root view** (the agent composes every
/// node from scratch), its three stat slots seeded from the host's live-World read, and a
/// `refresh` affordance the agent's composed button fires.
pub fn world_board_manifest(cells: u64, receipts: u64, sum: u64) -> AppletManifest {
    AppletManifest {
        seed_fields: vec![
            (BOARD_SLOT_CELLS, cells),
            (BOARD_SLOT_RECEIPTS, receipts),
            (BOARD_SLOT_SUM, sum),
            (BOARD_SLOT_REFRESHES, 0),
        ],
        affordances: vec![
            AffordanceSpec {
                name: "refresh".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot {
                    slot: BOARD_SLOT_REFRESHES,
                },
            },
            // The board shares the panel's census slots (0/1), so the SAME pulse weld
            // keeps the agent-composed board's `live cells:`/`receipts:` rows tracking
            // the live World once it is mounted as a pane (see `pulse_panes`).
            AffordanceSpec {
                name: STATUS_AFF_SET_CELLS.into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SetSlotFromArg {
                    slot: BOARD_SLOT_CELLS,
                },
            },
            AffordanceSpec {
                name: STATUS_AFF_SET_RECEIPTS.into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SetSlotFromArg {
                    slot: BOARD_SLOT_RECEIPTS,
                },
            },
        ],
        held: AuthRequired::Signature,
        // The agent composes the whole tree — the surface starts as a bare vstack.
        view_source: EditorViewTree::root().to_json(),
    }
}

/// Mint the board's backing applet on a fresh embedded verified executor, seeded with the
/// live-World stats its `bind` rows surface.
pub fn world_board_applet(cells: u64, receipts: u64, sum: u64) -> Applet {
    let public_key = [0x42u8; 32]; // 'B' — the World Board
    let token_id = [0x0bu8; 32];
    PortableApplet::mint(
        public_key,
        token_id,
        &world_board_manifest(cells, receipts, sum),
    )
}

/// Adopt a fresh, empty board card for authoring under the agent's identity (held
/// `Signature`, the cap tooth runs before each compose gesture).
pub fn world_board_editor(cells: u64, receipts: u64, sum: u64) -> CardEditor {
    let manifest = world_board_manifest(cells, receipts, sum);
    let card = world_board_applet(cells, receipts, sum);
    CardEditor::adopt(
        card,
        manifest,
        AGENT_AUTHOR,
        AuthRequired::Signature,
        AuthRequired::Signature,
    )
}

/// Count the live `bind` rows in a rendered board tree (the agent's composed state rows).
pub fn count_bind_rows(tree: &ViewNode) -> usize {
    fn walk(n: &ViewNode, rows: &mut usize) {
        if let ViewNode::Bind { .. } = n {
            *rows += 1;
        }
        match n {
            ViewNode::VStack(kids)
            | ViewNode::Row(kids)
            | ViewNode::List(kids)
            | ViewNode::Table(kids) => {
                for k in kids {
                    walk(k, rows);
                }
            }
            _ => {}
        }
    }
    let mut rows = 0;
    walk(tree, &mut rows);
    rows
}

/// Whether a rendered board tree carries the agent's `World Board` title text.
pub fn tree_has_board_title(tree: &ViewNode) -> bool {
    fn walk(n: &ViewNode) -> bool {
        match n {
            ViewNode::Text(s) => s == "World Board",
            ViewNode::VStack(kids)
            | ViewNode::Row(kids)
            | ViewNode::List(kids)
            | ViewNode::Table(kids) => kids.iter().any(walk),
            _ => false,
        }
    }
    walk(tree)
}

/// **Build the agent-composed World Board pane** — a [`deos_view::AppletView`] gpui entity
/// over the agent's composed `tree`, backed by a board applet seeded with the live-World
/// stats the `bind` rows surface. The desktop hosts the returned entity as a new window
/// body (a distinct `ViewNodePane`), so the agent's from-scratch composition reaches the
/// glass through the SAME native renderer the World-Status pane uses.
pub fn build_board_view(
    cx: &mut App,
    cells: u64,
    receipts: u64,
    sum: u64,
    tree: ViewNode,
) -> Entity<AppletView> {
    let applet: SharedApplet = Rc::new(RefCell::new(world_board_applet(cells, receipts, sum)));
    cx.new(|_cx| AppletView::new(applet, tree))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn board_manifest_starts_empty_and_seeds_live_stats() {
        // The board's authoring surface begins as a bare empty root — the agent composes
        // every node — and its model carries the host's live-World read.
        let tree = parse_view_tree(&world_board_manifest(7, 21, 0).view_source)
            .expect("the board's empty-root view-source parses");
        assert!(
            matches!(&tree, ViewNode::VStack(kids) if kids.is_empty()),
            "a fresh board is a bare empty vstack (nothing authored yet)"
        );
        let mut applet = world_board_applet(7, 21, 0);
        assert_eq!(applet.get_u64(BOARD_SLOT_CELLS), 7);
        assert_eq!(applet.get_u64(BOARD_SLOT_RECEIPTS), 21);
        // The `refresh` affordance the agent's composed button fires is a cap-gated turn.
        applet.fire("refresh", 1).expect("refresh commits");
        assert_eq!(applet.get_u64(BOARD_SLOT_REFRESHES), 1);
    }

    #[test]
    fn add_bind_composes_a_live_row_from_scratch() {
        // The new `AddBind` authoring primitive: from an empty editor, an agent can
        // compose a state-bound row (not just a frozen text snapshot).
        use deos_js::card_editor::ViewPatch;
        let mut editor = world_board_editor(3, 12, 0);
        editor
            .edit_view(ViewPatch::AddText {
                text: "World Board".into(),
            })
            .expect("compose the title");
        editor
            .edit_view(ViewPatch::AddBind {
                slot: BOARD_SLOT_CELLS,
                label: "live cells: ".into(),
            })
            .expect("compose a live bind row");
        let tree = parse_view_tree(&editor.view_source()).expect("composed source parses");
        assert!(tree_has_board_title(&tree), "the title was composed");
        assert_eq!(
            count_bind_rows(&tree),
            1,
            "one live state-bound row composed"
        );
    }

    #[test]
    fn panel_source_parses_to_the_expected_shape() {
        // The panel's view-source parses to a vstack: a header text over 3 bind rows.
        match status_panel_tree() {
            ViewNode::VStack(children) => {
                assert_eq!(children.len(), 4, "header + 3 status rows");
                assert!(matches!(&children[0], ViewNode::Text(t) if t == "World Status"));
                let (saw_header, rows) = reflect_status(&status_panel_tree());
                assert!(
                    saw_header && rows == 3,
                    "the reflective surface: header + 3 binds"
                );
            }
            other => panic!("expected a vstack root, got {other:?}"),
        }
    }

    #[test]
    fn backing_applet_reads_seeds_and_fires_the_refresh_turn() {
        let mut applet = status_panel_applet();
        assert_eq!(applet.get_u64(STATUS_SLOT_CELLS), STATUS_SEED_CELLS);
        assert_eq!(applet.get_u64(STATUS_SLOT_RECEIPTS), STATUS_SEED_RECEIPTS);
        // The `refresh` affordance the agent's button fires = one cap-gated verified turn.
        applet
            .fire("refresh", 1)
            .expect("the refresh affordance must commit");
        assert_eq!(
            applet.get_u64(STATUS_SLOT_REFRESHES),
            STATUS_SEED_REFRESHES + 1
        );
    }

    #[test]
    fn the_web_renderer_renders_the_same_panel() {
        let html = status_panel_html();
        assert!(html.contains("World Status"));
        assert!(
            html.contains("receipts: 12"),
            "the seeded status rows paint their witnessed values"
        );
    }

    #[test]
    fn census_plan_fires_only_the_moved_readings() {
        let census = WorldCensus {
            cells: 6,
            receipts: 41,
        };
        // Nothing moved → the free beat (no fires, no receipts, no repaint).
        assert!(census_plan(6, 41, census).is_empty());
        // Only receipts moved → EXACTLY the set_receipts fire (the fine-grained bar
        // starts at the plan: one moved reading, one tracking turn).
        assert_eq!(
            census_plan(6, 40, census),
            vec![(STATUS_AFF_SET_RECEIPTS, STATUS_SLOT_RECEIPTS, 41)]
        );
        // Both moved (the first convergence beat off the 3/12 seeds) → both fires.
        assert_eq!(
            census_plan(3, 12, census),
            vec![
                (STATUS_AFF_SET_CELLS, STATUS_SLOT_CELLS, 6),
                (STATUS_AFF_SET_RECEIPTS, STATUS_SLOT_RECEIPTS, 41),
            ]
        );
    }

    #[test]
    fn the_tracking_affordances_commit_receipted_setslot_turns() {
        // The weld's write verbs are REAL cap-gated verified turns on the panel's
        // embedded executor: firing `set_receipts` with `arg = the live census`
        // commits a receipt and the bind's slot now reads the mirrored value.
        let mut applet = status_panel_applet();
        assert_eq!(applet.get_u64(STATUS_SLOT_RECEIPTS), STATUS_SEED_RECEIPTS);
        let before = applet.receipt_count();
        applet
            .fire(STATUS_AFF_SET_RECEIPTS, 41)
            .expect("the tracking turn commits");
        applet
            .fire(STATUS_AFF_SET_CELLS, 6)
            .expect("the tracking turn commits");
        assert_eq!(applet.get_u64(STATUS_SLOT_RECEIPTS), 41);
        assert_eq!(applet.get_u64(STATUS_SLOT_CELLS), 6);
        assert_eq!(
            applet.receipt_count(),
            before + 2,
            "each mirrored reading is a receipted verified turn on the audit tape"
        );
        // A negative arg clamps to 0 (`slot := max(arg, 0)`) — never a wild write.
        applet
            .fire(STATUS_AFF_SET_CELLS, -5)
            .expect("the clamped tracking turn commits");
        assert_eq!(applet.get_u64(STATUS_SLOT_CELLS), 0);
    }
}
