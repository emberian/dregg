//! **THE APP SHELF** — the pre-built starbridge-apps as FIRST-CLASS DESKTOP CITIZENS.
//!
//! The app ecosystem below the glass is startlingly complete — ~20 fully-built apps
//! (cells × cap-gated affordances × manifest × tests) sit in `starbridge-apps/`, and
//! [`crate::app_registry::AppRegistry`] already launches any of them onto a live
//! `World` via [`crate::app_worldspine::AppWorldSpine`] — yet the flagship desktop
//! consumed NONE of it (zero references; only the older cockpit had a launcher
//! panel). THIS module is the missing weld: a desktop **App Shelf** window that
//! lists every registry app with its facts, and a per-app LAUNCH that seeds the
//! app's cell + program onto the desktop's LIVE `World` and commits its
//! representative affordance as a **REAL verified turn** — the cell then stands on
//! the desktop as an icon wearing the app's own face, its receipt is in the
//! Transcript, and its live state is one double-click away in the inspector.
//!
//! ## The clobber-safe split
//!
//! * **gpui-free model** — [`AppShelfState`] (the registry + the installed set),
//!   [`InstalledApp`] (one launched-on-World app: its cell, its live-fire
//!   [`AppCardSubstance`], its cells/affordances census), the pure
//!   [`shelf_rows`] projection the window body renders from, and
//!   [`app_spotter_candidates`] (the Spotter's "app · <name>" vocabulary). All of
//!   it compiles and `cargo test`s without a renderer.
//! * **presentation + actuation** — an `impl DeosDesktop` block (the house pattern
//!   `halo.rs`/`workflow.rs` use): the View owns the `cx.listener` wiring, the
//!   NT-chrome shelf body, and the launch/fire/open dispatch. Every actuation is a
//!   real committed turn on the shared `World`; every read is the LIVE ledger.
//!
//! ## Honest scope (the named seams)
//!
//! * **One instance per app id.** A shelf install is `launch_on_world` once; the
//!   RECEIPTED INSTALL CEREMONY (install/uninstall as first-class receipted turns,
//!   re-install as a fresh instance, persistence of the installed set in
//!   [`super::DesktopLayout`] so a reopened desktop re-seeds its apps) is future
//!   work — the seam is [`AppShelfState::install_on_world`]'s already-installed
//!   refusal.
//! * **Live-fire coverage follows the wired cards.** The four apps with wired
//!   cards (gallery / bounty-board / sealed-auction / execution-lease) expose their
//!   representative method as a shelf FIRE button — the SAME
//!   [`crate::app_registry::CardFireFn`] dispatch the card surface uses. The other
//!   apps launch (their representative affordance commits at install) and then
//!   surface an honest refusal naming the whole-lifecycle-cards seam.
//! * **The app's bespoke deos-view CARD** (`app_card(id).json` →
//!   `deos_view::parse_view_tree` → an `AppletView` window) is the richer "open"
//!   this shelf's inspector-open should graduate to once the card-pane mount for
//!   `AppCardSubstance` lands on the desktop side.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, Styled,
};

use dregg_app_framework::{DeosApp, TurnReceipt};
use dregg_types::CellId;

use crate::app_registry::{app_card, AppCardSubstance, AppEntry, AppRegistry, CardFireFn};
use crate::app_worldspine::{AppWorldSpine, WorldFireError};
use crate::world::World;

use super::chrome::{
    bevel_raised, face_row, face_section, fmt_balance, id_short, NT_DIM, NT_OK, NT_PANEL,
    NT_SELECT, NT_TITLE_TEXT, NT_WARN,
};
use super::spotter::{SpotterEntry, SpotterTarget};
use super::{DeosDesktop, WinKindTag};

/// The federation the shelf births app identities into — the SAME constant the
/// cockpit's launcher panel uses (`cockpit/panels_app_launcher.rs`), so an app
/// launched from either surface lives in one federation. Each launch mints a fresh
/// random app cipherclerk, so the derived app cell never collides across launches.
pub const SHELF_FEDERATION: [u8; 32] = [0x5Eu8; 32];

// ── The gpui-free model ─────────────────────────────────────────────────────────

/// One **installed app** — a registry entry launched onto the desktop's LIVE
/// `World`: its primary cell is on `World::ledger()` (the icon + inspector read it),
/// its install receipt is in `World::receipts()` (the Transcript shows it), and its
/// [`AppCardSubstance`] fires further methods as real verified turns.
pub struct InstalledApp {
    /// The registry id (`"gallery"`, `"bounty-board"`, …) — the launch key.
    pub id: &'static str,
    /// The display name (the icon caption + shelf heading).
    pub name: &'static str,
    /// The app's primary cell on the LIVE World ledger (the inspector's pointer).
    pub cell: CellId,
    /// The live-fire substance — the seeded [`AppWorldSpine`] + the app's card fire
    /// dispatch ([`CardFireFn`]; a surfaced-refusal fallback for unwired apps). A
    /// fire through it is a REAL cap∧state-gated verified turn on the shared World.
    pub substance: AppCardSubstance,
    /// How many `DeosCell`s the composed app declares (the manifest's cell census).
    pub cells: usize,
    /// Every affordance name the app declares (plain + gated) — the method
    /// vocabulary its shelf fire buttons offer. Empty for a PROGRAM entry (polis),
    /// whose affordances live in its charter programs, not a composed `DeosApp`.
    pub affordances: Vec<String>,
    /// Whether the app ships a WIRED card fire ([`app_card`] is `Some`) — only then
    /// do the shelf's fire buttons drive real turns; otherwise they surface the
    /// whole-lifecycle-cards seam as an honest refusal.
    pub wired_card: bool,
    /// The World height right after the install committed (the receipt's landmark).
    pub installed_height: u64,
}

/// **The shelf's whole state** — the standard registry (WHAT can be launched) plus
/// the installed set (WHAT HAS BEEN, each a live cell on the World). Owned by
/// [`DeosDesktop`]; gpui-free, so the install/fire flow is `cargo test`-able.
pub struct AppShelfState {
    registry: AppRegistry,
    installed: Vec<InstalledApp>,
}

impl Default for AppShelfState {
    fn default() -> Self {
        Self::new()
    }
}

impl AppShelfState {
    /// A fresh shelf over the standard registry, nothing installed yet.
    pub fn new() -> Self {
        AppShelfState {
            registry: AppRegistry::standard(),
            installed: Vec::new(),
        }
    }

    /// Every launchable registry entry, in registry order (the shelf's row order).
    pub fn entries(&self) -> &[AppEntry] {
        self.registry.entries()
    }

    /// How many apps the registry offers (the shelf's roster size).
    pub fn total(&self) -> usize {
        self.registry.entries().len()
    }

    /// The installed set, in install order.
    pub fn installed(&self) -> &[InstalledApp] {
        &self.installed
    }

    /// The installed app with registry id `id`, if any.
    pub fn find(&self, id: &str) -> Option<&InstalledApp> {
        self.installed.iter().find(|a| a.id == id)
    }

    /// The desktop-icon face for an INSTALLED app's cell — `(display name, initial
    /// glyph)` — so a launched app reads as an APP on the desktop (its own name +
    /// initial), not a balance-classified "account". `None` for every other cell
    /// (the icon keeps its kind face). Cheap: a linear scan of the installed set.
    pub fn icon_face(&self, cell: &CellId) -> Option<(&'static str, &'static str)> {
        self.installed
            .iter()
            .find(|a| &a.cell == cell)
            .map(|a| (a.name, initial_glyph(a.name)))
    }

    /// **Install `id` onto the live `World`** — the launch flow's gpui-free core.
    ///
    /// Resolves the registry entry and runs its REAL
    /// [`AppEntry::launch_on_world`]: the app's primary cell + program + genesis
    /// state are seeded onto `world` and its representative affordance COMMITS as a
    /// verified turn (the receipt lands in `World::receipts()`). The launched spine
    /// is wrapped in an [`AppCardSubstance`] with the app's wired card fire (or the
    /// surfaced-refusal fallback), and the install is recorded with its
    /// cells/affordances census. Returns the app's live cell id.
    ///
    /// Refusals are surfaced strings, never panics: an unknown id, an
    /// already-installed id (the receipted install-ceremony seam), or the
    /// executor's own launch rejection.
    pub fn install_on_world(
        &mut self,
        id: &str,
        world: Rc<RefCell<World>>,
    ) -> Result<CellId, String> {
        if self.find(id).is_some() {
            return Err(format!(
                "'{id}' is already installed — one instance per shelf tonight (the \
                 receipted install/uninstall ceremony is the named future seam)"
            ));
        }
        let entry = *self
            .registry
            .get(id)
            .ok_or_else(|| format!("no app '{id}' in the registry"))?;
        let launched = entry
            .launch_on_world(SHELF_FEDERATION, Rc::clone(&world))
            .map_err(|e| e.to_string())?;
        let cell = launched.primary_cell();
        // The manifest facts: the composed app's cell census + affordance vocabulary.
        // A PROGRAM entry (polis) has no composed `DeosApp` — one charter cell, and
        // its affordances live in the charter programs (the honest fallback).
        let (cells, affordances) = launched
            .app
            .as_ref()
            .map(app_census)
            .unwrap_or((1, Vec::new()));
        // The app's wired card fire when it ships one (the SAME dispatch its card
        // surface uses), else the surfaced-refusal fallback naming the seam.
        let card = app_card(entry.id);
        let wired_card = card.is_some();
        let fire: CardFireFn = card.map(|c| c.fire).unwrap_or(unwired_card_fire);
        let installed_height = world.borrow().height();
        self.installed.push(InstalledApp {
            id: entry.id,
            name: entry.name,
            cell,
            substance: AppCardSubstance::new(launched.spine, fire),
            cells,
            affordances,
            wired_card,
            installed_height,
        });
        Ok(cell)
    }

    /// **Fire `method` on the installed app `id`** — a real verified turn through
    /// the app's [`AppCardSubstance`] (the SAME dispatch its card surface uses).
    /// `None` if the app is not installed; `Some(Err(_))` is the executor's / the
    /// gate's own surfaced refusal (out-of-phase, unwired card, …).
    pub fn fire(
        &self,
        id: &str,
        method: &str,
        arg: i64,
    ) -> Option<Result<TurnReceipt, WorldFireError>> {
        self.find(id).map(|a| a.substance.fire(method, arg))
    }
}

/// The manifest census of a composed [`DeosApp`]: how many cells it declares, and
/// every affordance name across them (plain surface + cap∧state-gated surface) —
/// the method vocabulary the shelf's fire buttons and facts line read.
fn app_census(app: &DeosApp) -> (usize, Vec<String>) {
    let mut names: Vec<String> = Vec::new();
    for cell in app.cells() {
        for a in &cell.surface().affordances {
            names.push(a.name.clone());
        }
        for g in &cell.gated_surface().affordances {
            names.push(g.affordance.name.clone());
        }
    }
    (app.cells().len(), names)
}

/// The fire fallback for an app WITHOUT a wired card: an in-band surfaced refusal
/// naming the whole-lifecycle-cards seam. Commits NOTHING (anti-ghost) — the app's
/// representative affordance already committed at install; further methods need the
/// per-app effect-builder wiring (`app_registry::app_card`) this refusal names.
fn unwired_card_fire(
    _spine: &AppWorldSpine,
    method: &str,
    _arg: i64,
) -> Result<TurnReceipt, WorldFireError> {
    Err(WorldFireError::World {
        reason: format!(
            "'{method}' has no wired card fire — this app's representative affordance \
             committed at install; whole-lifecycle card fires are the named future seam \
             (wire it in app_registry::app_card)"
        ),
    })
}

/// The first character of an app's display name as its icon glyph — `&'static`
/// because the registry names are `&'static` (the icon tile borrows it for free).
fn initial_glyph(name: &'static str) -> &'static str {
    name.get(..1).unwrap_or("A")
}

/// Truncate `s` to at most `max` chars with a trailing ellipsis — the shelf's dense
/// one-line description clamp (char-boundary safe; a short string passes through).
fn truncate_ellipsis(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let head: String = s.chars().take(max.saturating_sub(1)).collect();
    format!("{}…", head.trim_end())
}

// ── The pure row projection (what the window body renders from) ──────────────────

/// One shelf row's render-ready facts — the registry entry plus, when installed,
/// the live install facts. Pure data: the body maps these to elements.
pub struct ShelfRowFacts {
    pub id: &'static str,
    pub name: &'static str,
    pub description: &'static str,
    /// `Some` when this app is installed on the live World.
    pub installed: Option<InstalledRowFacts>,
}

/// The installed half of a shelf row — the app's live cell + census + the dense
/// LIVE detail line (`live`) the caller reads off the ledger.
pub struct InstalledRowFacts {
    pub cell: CellId,
    pub cells: usize,
    pub affordances: Vec<String>,
    pub wired_card: bool,
    pub installed_height: u64,
    /// The dense live-ledger line for the app cell (balance · nonce · receipts ·
    /// lifecycle), supplied by the caller so this projection stays ledger-free.
    pub live: String,
}

/// Project the shelf state into render-ready rows, one per registry entry in
/// registry order. `live` reads the dense live-ledger detail line for an installed
/// app's cell (the desktop passes its own ledger readers in, keeping this pure and
/// testable — the same inversion [`super::spotter::candidates_for_cells`] uses).
pub fn shelf_rows(state: &AppShelfState, live: impl Fn(&CellId) -> String) -> Vec<ShelfRowFacts> {
    state
        .entries()
        .iter()
        .map(|e| ShelfRowFacts {
            id: e.id,
            name: e.name,
            description: e.description,
            installed: state.find(e.id).map(|a| InstalledRowFacts {
                cell: a.cell,
                cells: a.cells,
                affordances: a.affordances.clone(),
                wired_card: a.wired_card,
                installed_height: a.installed_height,
                live: live(&a.cell),
            }),
        })
        .collect()
}

/// The shelf window's summary line — roster size vs. installed count.
pub fn shelf_summary(installed: usize, total: usize) -> String {
    format!("{total} pre-built apps · {installed} installed on this World")
}

// ── The Spotter vocabulary ────────────────────────────────────────────────────────

/// The Spotter's app-ecosystem candidates: the App Shelf surface itself, plus one
/// "Launch <name>" entry per registry app (sublabel `app · <name> · <what it does>`)
/// — so the ONE entry to every surface reaches every pre-built app too. Appended to
/// [`super::spotter::surface_candidates`] by the desktop's candidate builder.
pub fn app_spotter_candidates() -> Vec<SpotterEntry> {
    let reg = AppRegistry::standard();
    let mut out = Vec::with_capacity(reg.entries().len() + 1);
    out.push(SpotterEntry {
        label: format!(
            "App Shelf  ({} pre-built apps · launch onto the World)",
            reg.entries().len()
        ),
        sublabel: "surface · the starbridge-apps as first-class desktop citizens".to_string(),
        target: SpotterTarget::AppShelf,
        score: 0,
    });
    for e in reg.entries() {
        out.push(SpotterEntry {
            label: format!("Launch {}  (app)", e.name),
            sublabel: format!(
                "app · {} · {}",
                e.name,
                truncate_ellipsis(e.description, 72)
            ),
            target: SpotterTarget::LaunchApp(e.id),
            score: 0,
        });
    }
    out
}

// ── The View half: actuation + the NT shelf body (the View owns the listeners) ────

impl DeosDesktop {
    /// Open (or focus) the APP SHELF window — anchored on the user sentinel like the
    /// World Explorer, and landed mold-ready (its halo ring floats on arrival).
    pub(super) fn open_app_shelf(&mut self) {
        self.land_in(self.user, WinKindTag::AppShelf);
        self.say(format!(
            "App Shelf — {} pre-built apps; LAUNCH seeds an app's cell + program onto \
             the LIVE World and commits its representative affordance as a real \
             verified turn.",
            self.app_shelf.total()
        ));
    }

    /// **LAUNCH an app from the shelf** (or focus it if already installed) — the
    /// desktop half of [`AppShelfState::install_on_world`]: install, refresh the
    /// icon census (the new app cell stands on the desktop), and land in the app
    /// cell's primary surface as a desktop window, mold-ready. Returns whether the
    /// app is installed after the call (an already-installed id counts).
    pub(super) fn launch_shelf_app(&mut self, id: &str) -> bool {
        if let Some((cell, name)) = self.app_shelf.find(id).map(|a| (a.cell, a.name)) {
            self.land_in(cell, WinKindTag::Inspector);
            self.say(format!(
                "{name} is already installed — opened its live cell {} (re-install is \
                 the receipted install-ceremony seam).",
                id_short(&cell)
            ));
            return true;
        }
        let world = Rc::clone(&self.world);
        match self.app_shelf.install_on_world(id, world) {
            Ok(cell) => {
                self.refresh_cells_from_ledger();
                // The app's PRIMARY SURFACE as a desktop window: the reflective
                // inspector over its live cell (state slots + affordances + receipts).
                // The bespoke deos-view card mount is the named richer follow-up.
                self.land_in(cell, WinKindTag::Inspector);
                self.say(format!(
                    "LAUNCHED '{id}' onto the LIVE World — cell {} seeded + its \
                     representative affordance committed (height {}).",
                    id_short(&cell),
                    self.world.borrow().height()
                ));
                true
            }
            Err(reason) => {
                self.say(format!("LAUNCH '{id}' refused: {reason}"));
                false
            }
        }
    }

    /// **FIRE a method on an installed app** — a real verified turn through the
    /// app's substance (the SAME dispatch its card surface uses); the outcome (the
    /// executor's receipt, or its own surfaced refusal) lands in the status bar.
    /// Returns whether the turn COMMITTED.
    pub(super) fn fire_shelf_app(&mut self, id: &str, method: &str) -> bool {
        match self.app_shelf.fire(id, method, 1) {
            Some(Ok(receipt)) => {
                self.say(format!(
                    "App '{id}' · '{method}' COMMITTED — a real verified turn by {} \
                     (height {}).",
                    id_short(&receipt.agent),
                    self.world.borrow().height()
                ));
                true
            }
            Some(Err(e)) => {
                self.say(format!("App '{id}' · '{method}' REFUSED: {e}"));
                false
            }
            None => {
                self.say(format!(
                    "App '{id}' is not installed — launch it from the App Shelf first."
                ));
                false
            }
        }
    }

    /// Re-read the icon census off the LIVE ledger — a launched app's fresh cell
    /// becomes a desktop icon immediately (the same read [`DeosDesktop::new`] makes).
    // TODO(pump_dynamics): tonight's THE-PULSE commit (`pump_dynamics`, on a newer
    // base than this lane's) re-reads the ledger every beat, which subsumes this
    // manual refresh — when merging onto that base, the launch path can drop this
    // call and let the pulse grow the icon.
    pub(super) fn refresh_cells_from_ledger(&mut self) {
        let mut v: Vec<CellId> = {
            let w = self.world.borrow();
            w.ledger().iter().map(|(id, _)| *id).collect()
        };
        v.sort();
        self.cells = v;
    }

    // ── Bake / test hooks (drive the shelf headlessly) ────────────────────────────

    /// Open the App Shelf window (what the desktop menu's "App Shelf…" does).
    pub fn bake_open_app_shelf(&mut self) {
        self.open_app_shelf();
    }

    /// How many pre-built apps the registry offers the shelf (a bake assertion).
    pub fn bake_app_count(&self) -> usize {
        self.app_shelf.total()
    }

    /// How many apps are INSTALLED on the live World (a bake assertion).
    pub fn bake_installed_app_count(&self) -> usize {
        self.app_shelf.installed().len()
    }

    /// LAUNCH `id` from the shelf (what the row's "Install & Launch" button does) —
    /// a real `launch_on_world` whose receipt lands on the live World. Returns
    /// whether the app is installed after the call.
    pub fn bake_launch_app(&mut self, id: &str) -> bool {
        self.launch_shelf_app(id)
    }

    /// FIRE `method` on the installed `id` (what a row's fire button does) and
    /// report whether the verified turn COMMITTED.
    pub fn bake_fire_app(&mut self, id: &str, method: &str) -> bool {
        self.fire_shelf_app(id, method)
    }

    // ── The NT shelf body ─────────────────────────────────────────────────────────

    /// **The App Shelf window body** — the dense NT roster of every registry app:
    /// name · what-it-does · manifest facts, an "Install & Launch" button per
    /// uninstalled app, and per installed apps the live-ledger line, an "Open"
    /// button (its cell's inspector), and the wired fire buttons (each a real
    /// verified turn). The rows come from the pure [`shelf_rows`] projection; this
    /// method owns only the listeners (the clobber-safe split).
    pub(super) fn render_app_shelf_body(
        &self,
        scroll: &gpui::ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let rows = shelf_rows(&self.app_shelf, |cell| {
            format!(
                "balance {} · nonce {} · {} receipt(s) · {}",
                fmt_balance(self.cell_balance(cell)),
                self.cell_nonce(cell),
                self.cell_receipt_count(cell),
                self.cell_lifecycle(cell)
            )
        });
        let summary = shelf_summary(self.app_shelf.installed().len(), self.app_shelf.total());

        let mut col = div()
            .id("app-shelf-body")
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(&format!("App Shelf · {summary}")))
            .child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child(
                        "Each row is a fully-built deos app (cells × cap-gated affordances). \
                     LAUNCH seeds its cell + program onto YOUR live World and commits its \
                     representative affordance as a REAL verified turn — the cell becomes a \
                     desktop icon, the receipt lands in the Transcript.",
                    ),
            );

        for row in rows {
            col = col.child(self.render_shelf_row(row, cx));
        }
        // The roster scrolls behind a REAL NT scrollbar — a long shelf reads as
        // depth, not truncation, and the persistent handle keeps the place.
        super::chrome::nt_scroll_face(scroll, col).into_any_element()
    }

    /// One shelf row: the app's heading + description + facts, then its action
    /// buttons (launch / open / wired fires).
    fn render_shelf_row(&self, row: ShelfRowFacts, cx: &mut Context<Self>) -> AnyElement {
        let id = row.id;
        let mut card = bevel_raised(
            div()
                .id(gpui::SharedString::from(format!("shelf-row-{id}")))
                .p_2()
                .flex()
                .flex_col()
                .gap_1(),
        );

        // Heading: the display name bold, the registry id dim beside it, and the
        // installed verdict on the right.
        card = card.child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .items_center()
                .child(
                    div()
                        .text_size(px(12.0))
                        .font_weight(gpui::FontWeight::BOLD)
                        .child(row.name),
                )
                .child(
                    div()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("app · {id}")),
                )
                .child(
                    div()
                        .ml_auto()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(if row.installed.is_some() {
                            NT_OK
                        } else {
                            NT_DIM
                        }))
                        .child(if row.installed.is_some() {
                            "INSTALLED"
                        } else {
                            "not installed"
                        }),
                ),
        );
        // What it does (the registry's one-liner, clamped dense).
        card = card.child(
            div()
                .text_size(px(10.0))
                .text_color(gpui::rgb(NT_DIM))
                .child(truncate_ellipsis(row.description, 140)),
        );

        match row.installed {
            None => {
                // The launch affordance — a real `launch_on_world` on click.
                card = card.child(
                    shelf_button_chrome(format!("shelf-launch-{id}"))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.launch_shelf_app(id);
                                cx.notify();
                            }),
                        )
                        .child("Install & Launch  (verified turn)"),
                );
            }
            Some(inst) => {
                // The manifest + live facts of the installed instance.
                card = card
                    .child(face_row(
                        "manifest",
                        &format!(
                            "{} cell(s) · {} affordance(s){}",
                            inst.cells,
                            inst.affordances.len(),
                            if inst.wired_card {
                                " · wired card"
                            } else {
                                " · card seam unwired"
                            }
                        ),
                    ))
                    .child(face_row("cell", &id_short(&inst.cell)))
                    .child(face_row("live", &inst.live))
                    .child(face_row(
                        "installed",
                        &format!("at height {}", inst.installed_height),
                    ));

                let mut buttons = div().flex().flex_row().flex_wrap().gap_1();
                let cell = inst.cell;
                buttons = buttons.child(
                    shelf_button_chrome(format!("shelf-open-{id}"))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                // The app's primary surface as a window, mold-ready.
                                this.land_in(cell, WinKindTag::Inspector);
                                this.status = format!(
                                    "Inspecting app '{id}' — its live cell {} on the World ledger.",
                                    id_short(&cell)
                                );
                                cx.notify();
                            }),
                        )
                        .child("Open  (live cell inspector)"),
                );
                if inst.wired_card {
                    // One fire button per declared affordance — each routed through
                    // the app's wired CardFireFn (a real verified turn, or the
                    // executor's own surfaced refusal when the phase forbids it).
                    for name in inst.affordances.iter().take(6) {
                        let method = name.clone();
                        let label = format!("fire '{name}'");
                        buttons = buttons.child(
                            shelf_button_chrome(format!("shelf-fire-{id}-{name}"))
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                        this.fire_shelf_app(id, &method);
                                        cx.notify();
                                    }),
                                )
                                .child(label),
                        );
                    }
                } else {
                    buttons = buttons.child(
                        div()
                            .text_size(px(10.0))
                            .text_color(gpui::rgb(NT_WARN))
                            .child(
                                "launch fired its representative affordance — further \
                                 fires await the whole-lifecycle card wiring",
                            ),
                    );
                }
                card = card.child(buttons);
            }
        }
        card.into_any_element()
    }
}

/// The raised NT chrome of one shelf button (id + dense padding + navy hover). The
/// CALLER chains its own `.on_mouse_down(…, cx.listener(…))` + `.child(label)` —
/// the View owns the listeners (the clobber-safe split); this is dumb chrome.
fn shelf_button_chrome(elem_id: String) -> gpui::Stateful<gpui::Div> {
    bevel_raised(
        div()
            .id(gpui::SharedString::from(elem_id))
            .px_2()
            .py_1()
            .text_size(px(10.0))
            .hover(|s| {
                s.bg(gpui::rgb(NT_SELECT))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
            }),
    )
}

// ── Unit tests for the gpui-free core (registry → World, real verified turns) ─────

#[cfg(test)]
mod tests {
    use super::*;

    /// The shelf installs a registry app onto a LIVE `World` (the launch commits its
    /// representative affordance), a wired fire drives ANOTHER real verified turn,
    /// an out-of-phase fire is a surfaced refusal that commits NOTHING, and a second
    /// install of the same id is refused (the named install-ceremony seam).
    #[test]
    fn install_and_fire_land_real_verified_turns_on_the_live_world() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut shelf = AppShelfState::new();
        assert!(shelf.total() >= 19, "the standard registry is the roster");
        let receipts_before = world.borrow().receipts().len();

        let cell = shelf
            .install_on_world("gallery", Rc::clone(&world))
            .expect("gallery installs onto the live World");

        // The app cell is LIVE on World's ledger — the SAME read the desktop icons
        // + inspector make.
        assert!(
            world.borrow().ledger().get(&cell).is_some(),
            "the installed app's cell is on the live ledger"
        );
        // The launch itself committed the representative affordance (one receipt).
        assert_eq!(world.borrow().receipts().len(), receipts_before + 1);

        // The install record carries the manifest census (gallery: 1 cell; its
        // affordance vocabulary includes the submit method the card fires).
        let inst = shelf.find("gallery").expect("recorded as installed");
        assert_eq!(inst.cells, 1);
        assert!(inst.wired_card, "gallery ships a wired card fire");
        assert!(
            inst.affordances.iter().any(|a| a == "submit"),
            "the census names the submit affordance"
        );

        // A wired fire is ANOTHER real verified turn (submit → the next free
        // WriteOnce slot, read off World's LIVE state).
        let receipt = shelf
            .fire("gallery", "submit", 1)
            .expect("installed")
            .expect("submit commits from the seeded SUBMISSION phase");
        assert_eq!(receipt.agent, cell, "the app cell authored the turn");
        assert_eq!(world.borrow().receipts().len(), receipts_before + 2);

        // An out-of-phase method is a SURFACED refusal — and commits nothing.
        let refused = shelf.fire("gallery", "reveal", 1).expect("installed");
        assert!(
            refused.is_err(),
            "reveal is not live-fireable from SUBMISSION"
        );
        assert_eq!(
            world.borrow().receipts().len(),
            receipts_before + 2,
            "a refusal commits NOTHING (anti-ghost)"
        );

        // One instance per id tonight — the receipted install ceremony is the seam.
        assert!(shelf
            .install_on_world("gallery", Rc::clone(&world))
            .is_err());
        assert_eq!(shelf.installed().len(), 1);
    }

    /// A PROGRAM entry (polis) installs through the same seam — its charter cell
    /// lands live — and its unwired fires surface the named refusal.
    #[test]
    fn a_program_entry_installs_and_unwired_fires_surface_the_seam() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut shelf = AppShelfState::new();
        let cell = shelf
            .install_on_world("polis", Rc::clone(&world))
            .expect("polis installs (the program backend)");
        assert!(world.borrow().ledger().get(&cell).is_some());
        let inst = shelf.find("polis").expect("recorded");
        assert!(!inst.wired_card, "polis ships no wired card");
        let refused = shelf.fire("polis", "anything", 1).expect("installed");
        match refused {
            Err(WorldFireError::World { reason }) => {
                assert!(
                    reason.contains("named future seam"),
                    "the refusal names the whole-lifecycle-cards seam: {reason}"
                );
            }
            other => panic!("expected the unwired-card refusal, got {other:?}"),
        }
    }

    /// The pure row projection: one row per registry entry in registry order; an
    /// installed app's row carries the live detail the caller supplies; icon_face
    /// answers only for installed cells.
    #[test]
    fn shelf_rows_project_the_registry_and_the_installed_facts() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut shelf = AppShelfState::new();
        let rows = shelf_rows(&shelf, |_| unreachable!("nothing installed yet"));
        assert_eq!(rows.len(), shelf.total());
        assert!(rows.iter().all(|r| r.installed.is_none()));

        let cell = shelf
            .install_on_world("bounty-board", Rc::clone(&world))
            .expect("bounty-board installs");
        let rows = shelf_rows(&shelf, |c| format!("live {}", id_short(c)));
        let bb = rows
            .iter()
            .find(|r| r.id == "bounty-board")
            .expect("bounty row");
        let inst = bb.installed.as_ref().expect("installed facts");
        assert_eq!(inst.cell, cell);
        assert_eq!(inst.live, format!("live {}", id_short(&cell)));
        // Registry order is preserved (gallery is the registry's first entry).
        assert_eq!(rows[0].id, "gallery");

        // The desktop-icon face: the app's own name + initial for ITS cell only.
        assert_eq!(shelf.icon_face(&cell), Some(("Bounty Board", "B")));
        assert_eq!(shelf.icon_face(&CellId::from_bytes([0u8; 32])), None);
    }

    /// The Spotter vocabulary: the shelf surface entry plus one "app · <name>"
    /// launch entry per registry app.
    #[test]
    fn spotter_candidates_cover_every_registry_app() {
        let cands = app_spotter_candidates();
        let reg = AppRegistry::standard();
        assert_eq!(cands.len(), reg.entries().len() + 1);
        assert!(matches!(cands[0].target, SpotterTarget::AppShelf));
        for e in reg.entries() {
            assert!(
                cands.iter().any(|c| {
                    matches!(c.target, SpotterTarget::LaunchApp(id) if id == e.id)
                        && c.sublabel.starts_with("app · ")
                        && c.label.contains(e.name)
                }),
                "a launch candidate exists for '{}'",
                e.id
            );
        }
    }

    /// The dense clamp is char-boundary safe and passes short strings through.
    #[test]
    fn truncate_ellipsis_is_char_safe() {
        assert_eq!(truncate_ellipsis("short", 10), "short");
        assert_eq!(truncate_ellipsis("exactly-ten", 11), "exactly-ten");
        let clamped = truncate_ellipsis("a sealed (commit–reveal) auction over Σ", 12);
        assert!(clamped.ends_with('…'));
        assert!(clamped.chars().count() <= 12);
        // Multi-byte boundaries never split (the middot/Σ are multi-byte).
        assert_eq!(truncate_ellipsis("ΣΣΣΣ", 3), "ΣΣ…");
    }

    /// The summary line reads roster vs. installed.
    #[test]
    fn shelf_summary_reads_the_counts() {
        assert_eq!(
            shelf_summary(2, 20),
            "20 pre-built apps · 2 installed on this World"
        );
    }
}
