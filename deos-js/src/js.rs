//! The **JS engine binding** — real SpiderMonkey (`mozjs`) driving deos substance.
//!
//! [`JsRuntime`] wraps a genuine `JSContext`/`Runtime` (the same minimal embedding the
//! `mozjs` `eval`/`callback` examples prove). It installs native Rust functions onto a
//! fresh global; a JS prelude builds the ergonomic `deos.applet({...})` / `app.fire` /
//! `app.get` / `app.view` surface on top of them. The natives bridge into a
//! thread-local [`Applet`] (the embedded verified executor) so:
//!
//!   - `app.fire("inc", n)` → a REAL cap-gated verified turn (a `TurnReceipt`);
//!   - `app.get(slot)` → a witnessed read off the live ledger;
//!   - `app.view.set(k, v)` → a plain in-memory change (NO turn, NO receipt).
//!
//! SpiderMonkey rooting/GC is observed via the `rooted!` macro and `CallArgs`, exactly
//! as the upstream `callback.rs` test does. This is the genuine engine, not a stub.

use std::cell::RefCell;
use std::ffi::CStr;
use std::ptr;
use std::ptr::NonNull;
use std::str;

use mozjs::context::{JSContext as SmContext, RawJSContext};
use mozjs::jsapi::{CallArgs, OnNewGlobalHookOption, Value};
use mozjs::jsval::{Int32Value, StringValue, UndefinedValue};
use mozjs::realm::AutoRealm;
use mozjs::rooted;
use mozjs::rust::wrappers2::{
    EncodeStringToUTF8, JS_DefineFunction, JS_NewGlobalObject, JS_NewStringCopyN,
};
use mozjs::rust::{
    evaluate_script, CompileOptionsWrapper, JSEngine, RealmOptions, Runtime, SIMPLE_GLOBAL_CLASS,
};

use crate::applet::{Applet, FireError};
use crate::attach::{AttachedApplet, AttachedComposer, ComposeError, ComposeStep};
use crate::card_editor::{CardEditor, EditError, ViewPatch};
use crate::portable::{AffordanceSpec, ApplyOp};
use crate::reflect_binding;

/// The substance the native functions drive: EITHER deos-js's own embedded engine
/// ([`Applet`]) or a PROVIDED live World ([`AttachedApplet`] — the attach path). The
/// natives call the SAME surface on both (crawl `ledger()`, fire, read, view-state),
/// so one set of bindings serves both the embedded spike and the live cockpit.
pub enum JsTarget {
    /// deos-js's own fresh embedded engine — a private single-cell world.
    /// Boxed: `Applet` is far larger than `AttachedApplet` (large_enum_variant).
    Embedded(Box<Applet>),
    /// A provided live World (the cockpit's real ledger, or a fork) — the attach path.
    Attached(AttachedApplet),
}

impl JsTarget {
    /// Read the live ledger the reflective crawl walks (the REAL cells of whichever
    /// world is attached) by running `f` over it — closure-passing so the attach
    /// path can borrow a World held behind an `Rc<RefCell<World>>` for the read's
    /// duration. The crawl natives produce their JSON inside `f`.
    pub fn with_ledger(&self, f: &mut dyn FnMut(&dregg_cell::Ledger)) {
        match self {
            JsTarget::Embedded(a) => f(a.ledger()),
            JsTarget::Attached(a) => a.with_ledger(f),
        }
    }
    /// Fire an affordance — ONE cap-gated verified turn (on the embedded engine, or
    /// the live World). Returns the receipt hash on commit.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<[u8; 32], FireError> {
        match self {
            JsTarget::Embedded(a) => a.fire(affordance, arg).map(|r| r.receipt_hash()),
            JsTarget::Attached(a) => a.fire(affordance, arg),
        }
    }
    /// Fire RAW effects (the GM-superpower path) — only the attach path supports it
    /// (the embedded engine has no live World to commit arbitrary cross-cell effects on).
    pub fn fire_raw_effects(
        &mut self,
        method: &str,
        effects: Vec<dregg_turn::action::Effect>,
    ) -> Result<[u8; 32], FireError> {
        match self {
            JsTarget::Attached(a) => a.fire_raw_effects(method, effects),
            JsTarget::Embedded(_) => Err(FireError::Executor(
                "raw-effect fire requires an attached live World".into(),
            )),
        }
    }
    /// Fire RAW effects under an explicit `actor` (the GM superpower of acting as a cell
    /// it governs — e.g. a self-grant from a spawned door cell).
    pub fn fire_raw_effects_as(
        &mut self,
        actor: dregg_types::CellId,
        method: &str,
        effects: Vec<dregg_turn::action::Effect>,
    ) -> Result<[u8; 32], FireError> {
        match self {
            JsTarget::Attached(a) => a.fire_raw_effects_as(actor, method, effects),
            JsTarget::Embedded(_) => Err(FireError::Executor(
                "raw-effect fire requires an attached live World".into(),
            )),
        }
    }
    /// Mint an OPEN, funded world cell through the host (the GM superpower) — only the
    /// attach path has a host ledger to mint into.
    pub fn mint_open_cell(
        &mut self,
        seed: &str,
        funding: u64,
    ) -> Result<dregg_types::CellId, FireError> {
        match self {
            JsTarget::Attached(a) => a.mint_open_cell(seed, funding),
            JsTarget::Embedded(_) => Err(FireError::Executor(
                "mint_open_cell requires an attached live World".into(),
            )),
        }
    }
    /// The agent cell driving this target (the actor of every committed turn).
    pub fn agent_cell(&self) -> dregg_types::CellId {
        self.cell()
    }
    /// Witnessed read of one model field as a u64.
    pub fn get_u64(&self, slot: usize) -> u64 {
        match self {
            JsTarget::Embedded(a) => a.get_u64(slot),
            JsTarget::Attached(a) => a.get_u64(slot),
        }
    }
    /// The agent/applet cell (the affordance projection's subject).
    pub fn cell(&self) -> dregg_types::CellId {
        match self {
            JsTarget::Embedded(a) => a.cell(),
            JsTarget::Attached(a) => a.cell(),
        }
    }
    /// The registered affordance specs (name + required authority).
    pub fn affordance_specs(&self) -> Vec<(String, dregg_cell::AuthRequired)> {
        match self {
            JsTarget::Embedded(a) => a.affordance_specs(),
            JsTarget::Attached(a) => a.affordance_specs(),
        }
    }
    /// The committed receipt count (the audit tape length).
    pub fn receipt_count(&self) -> usize {
        match self {
            JsTarget::Embedded(a) => a.receipt_count(),
            JsTarget::Attached(a) => a.receipt_count(),
        }
    }
    /// The committed receipt-hash tape (the rewindable lineage).
    pub fn receipts(&self) -> Vec<[u8; 32]> {
        match self {
            JsTarget::Embedded(a) => a.receipts().to_vec(),
            JsTarget::Attached(a) => a.receipts().to_vec(),
        }
    }
    fn set_view(&mut self, key: &str, value: &str) {
        match self {
            JsTarget::Embedded(a) => a.set_view(key, value),
            JsTarget::Attached(a) => a.set_view(key, value),
        }
    }
    fn get_view(&self, key: &str) -> Option<String> {
        match self {
            JsTarget::Embedded(a) => a.get_view(key).map(|s| s.to_string()),
            JsTarget::Attached(a) => a.get_view(key).map(|s| s.to_string()),
        }
    }
    /// Run `f` over the full committed receipts by BORROW — no `to_vec` clone of the
    /// whole tape. `present()` reads the lineage per call without copying it; the
    /// attach path has no in-JS full tape, so `f` sees an empty slice. (The Provenance
    /// face's lineage; empty for the attach path, whose live World owns the full log.)
    fn with_full_receipts<R>(&self, f: impl FnOnce(&[dregg_turn::turn::TurnReceipt]) -> R) -> R {
        match self {
            JsTarget::Embedded(a) => f(a.full_receipts()),
            JsTarget::Attached(_) => f(&[]),
        }
    }
    /// Snapshot the substance for cheap rewind — only the embedded engine supports
    /// it (a fork is the live World's own rewind primitive). `None` for attach.
    fn snapshot(&self) -> Option<(Vec<u8>, usize)> {
        match self {
            JsTarget::Embedded(a) => Some((a.snapshot(), a.receipt_count())),
            JsTarget::Attached(_) => None,
        }
    }
    /// Restore the embedded substance to a snapshot. The attach path cannot rewind
    /// here (the live World rewinds itself).
    fn restore(&mut self, bytes: &[u8], keep: usize) -> Result<(), String> {
        match self {
            JsTarget::Embedded(a) => a.restore(bytes, keep),
            JsTarget::Attached(_) => Err("attach path cannot rewind in-JS".into()),
        }
    }
}

thread_local! {
    /// The substance the native functions drive. ONE target per runtime for the spike
    /// (the polynomial-functor interface of a single sovereign cell, embedded OR live).
    /// A real multi-app surface would key by an integer handle returned from
    /// `deos.applet`.
    static CURRENT_APPLET: RefCell<Option<JsTarget>> = const { RefCell::new(None) };
    /// The last error message a native produced (surfaced to the test).
    static LAST_NATIVE_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };
    /// A scratch string for the UTF-8-encode callback to deposit into.
    static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
    /// Snapshot store for `deos.world.snapshot()`/`.rewind(token)`: token → (bytes,
    /// receipt-count-at-snapshot). A snapshot is the integrity-hashed ledger state.
    static SNAPSHOTS: RefCell<Vec<(Vec<u8>, usize)>> = const { RefCell::new(Vec::new()) };
    /// THE CARD EDITOR the `deos.editor.*` natives drive — the card being authored from
    /// within deos (its view/field/affordance). Mounted under the editor's own `held`
    /// (the authoring cap tooth). Installed by the host alongside (and independent of)
    /// the crawl/drive target, so `deos.editor.*` is reachable in BOTH the embedded run
    /// and an attached-live-World run: the card is a portable cell either way.
    static CURRENT_EDITOR: RefCell<Option<CardEditor>> = const { RefCell::new(None) };
    /// THE SERVER REGISTRY the `deos.server.*` natives publish into — the affordances a
    /// hosted "private server" program registers at boot (`defineAffordance`). The host
    /// (e.g. the dregg node's `deos-host`) drains this AFTER running the program's setup
    /// to publish the surface clients discover + fire. Each entry carries a real
    /// `Vec<Effect>` (the generalized affordance shape, not a hardcoded counter-bump).
    static SERVER_REGISTRY: RefCell<Vec<ServerAffordanceDef>> = const { RefCell::new(Vec::new()) };
    /// THE FORK REGISTRY — the forked INSTANCES a server program stood up via
    /// `deos.server.fork(seed)`. Each is a fresh OPEN cell minted on the live ledger (a
    /// cap-bounded fork of the server's world for a party/session); the host drains this
    /// after setup and publishes each as its OWN discoverable surface keyed by the
    /// instance cell, carrying exactly the affordances scoped to it.
    static FORK_REGISTRY: RefCell<Vec<ServerFork>> = const { RefCell::new(Vec::new()) };
    /// THE BOUNDED MULTI-CELL COMPOSER the `deos.compose(...)` native drives — the agent's
    /// brain composing a story spanning MULTIPLE cells (mint a card + seed it + grant a peer
    /// a cap) on the live World as ONE all-or-nothing bounded gesture. Mounted under the
    /// agent's ATTENUATED `held` (the cap tooth), independent of the crawl/drive target, so
    /// `deos.compose` is reachable in an attached-live-World run. The host installs it before
    /// the run and reads back the receipts + the refusal (if any) after.
    static CURRENT_COMPOSER: RefCell<Option<AttachedComposer>> = const { RefCell::new(None) };
    /// The outcome of the last `deos.compose(...)` the JS ran: the committed receipts +
    /// minted cells on success, or the in-band OVER-REACH reason (with nothing committed) on
    /// refusal. The host reads this back after the run (the composer commits step-wise, so
    /// the receipts ALSO land on the live ledger directly).
    static LAST_COMPOSE: RefCell<Option<ComposeOutcome>> = const { RefCell::new(None) };
}

/// The JS-visible outcome of a `deos.compose(...)` call: what the agent's multi-cell story
/// did on the live World. The host reads this back after the run.
#[derive(Clone, Debug, Default)]
pub struct ComposeOutcome {
    /// The committed receipt hashes, in leg order (empty on an over-reach — nothing committed).
    pub receipts: Vec<[u8; 32]>,
    /// The cell ids minted by `mintCard` legs, in order.
    pub minted: Vec<dregg_types::CellId>,
    /// The number of legs that committed (= `receipts.len()`).
    pub committed: usize,
    /// The in-band OVER-REACH / executor refusal reason, iff the story was refused. On an
    /// over-reach `committed == 0` (the atomic pre-screen aborted before any turn).
    pub refusal: Option<String>,
}

impl ComposeOutcome {
    /// Whether the whole story committed (no refusal).
    pub fn ok(&self) -> bool {
        self.refusal.is_none()
    }
}

/// One affordance a hosted server program registered via `deos.server.defineAffordance`:
/// a name, the authority a player must hold to fire it, the real effects the fire
/// commits, and an OPTIONAL instance cell it is scoped to (a fork — see [`ServerFork`]).
/// `instance == None` ⇒ the root server surface; `Some(cell)` ⇒ the affordance belongs
/// to that forked instance's own published surface. The host publishes the root + each
/// fork as a distinct discoverable surface so a client connects to a specific
/// party/session instance.
#[derive(Clone, Debug)]
pub struct ServerAffordanceDef {
    pub name: String,
    pub required: dregg_cell::AuthRequired,
    pub effects: Vec<dregg_turn::action::Effect>,
    /// The forked instance this affordance is scoped to (`None` ⇒ the root surface).
    pub instance: Option<dregg_types::CellId>,
}

/// A FORKED INSTANCE the server stood up via `deos.server.fork(seed)` — a cap-bounded
/// fork of the server's world for a party/session (the membrane-fork). Each fork is a
/// fresh OPEN cell minted on the live ledger; affordances scoped to it
/// (`defineAffordance({…, instance})`) publish as the fork's OWN discoverable surface,
/// so a client connects + fires into THAT instance, isolated from the root + siblings.
#[derive(Clone, Debug)]
pub struct ServerFork {
    /// The seed label the fork was derived from (the instance's name).
    pub seed: String,
    /// The minted instance cell (the discovery key + the surface root).
    pub cell: dregg_types::CellId,
}

/// Reset the server registry (affordances + forks) before running a program's setup (so
/// a fresh boot starts from an empty published surface).
pub fn reset_server_registry() {
    SERVER_REGISTRY.with(|r| r.borrow_mut().clear());
    FORK_REGISTRY.with(|r| r.borrow_mut().clear());
}

/// Drain the affordances a hosted server program registered (after its setup ran).
pub fn take_server_registry() -> Vec<ServerAffordanceDef> {
    SERVER_REGISTRY.with(|r| std::mem::take(&mut *r.borrow_mut()))
}

/// Drain the forked instances a hosted server program stood up (after its setup ran).
/// The host publishes each as its own discoverable surface keyed by the instance cell.
pub fn take_fork_registry() -> Vec<ServerFork> {
    FORK_REGISTRY.with(|r| std::mem::take(&mut *r.borrow_mut()))
}

/// Install the [`CardEditor`] the `deos.editor.*` natives author through. The editor is
/// mounted under its own `held`; `deos.editor.editView/setField/addAffordance(cardId,…)`
/// drive it, refusing in-band when `held` does not satisfy the card's `edit_authority`
/// OR when `cardId` is not the editor's card (an author-the-wrong-card over-reach).
pub fn set_current_editor(editor: CardEditor) {
    CURRENT_EDITOR.with(|c| *c.borrow_mut() = Some(editor));
}

/// Take the editor back out — to read the authored card (its re-folded view, blame,
/// receipts, the re-mintable manifest) after a JS authoring run.
pub fn take_current_editor() -> Option<CardEditor> {
    CURRENT_EDITOR.with(|c| c.borrow_mut().take())
}

/// Install the [`AttachedComposer`] the `deos.compose(...)` native drives — the agent's
/// bounded multi-cell composer over the live World, mounted under its `held`. Independent
/// of the crawl/drive target, so `deos.compose` composes against the live ledger in an
/// attached run. Clears any stale compose outcome.
pub fn set_current_composer(composer: AttachedComposer) {
    LAST_COMPOSE.with(|c| *c.borrow_mut() = None);
    CURRENT_COMPOSER.with(|c| *c.borrow_mut() = Some(composer));
}

/// Take the composer back out — to inspect its receipt tape + scope after a JS run.
pub fn take_current_composer() -> Option<AttachedComposer> {
    CURRENT_COMPOSER.with(|c| c.borrow_mut().take())
}

/// Read back the outcome of the last `deos.compose(...)` the JS ran (the committed receipts
/// + minted cells, or the in-band over-reach refusal). `None` if no compose ran.
pub fn take_last_compose() -> Option<ComposeOutcome> {
    LAST_COMPOSE.with(|c| c.borrow_mut().take())
}

/// Install the embedded applet the native functions drive (deos-js's own engine).
pub fn set_current_applet(applet: Applet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(JsTarget::Embedded(Box::new(applet))));
}

/// Install an ATTACHED applet — the runtime bound to a PROVIDED live World (the
/// cockpit's real ledger, or a fork). The crawl + fire then drive that World.
pub fn set_current_attached(applet: AttachedApplet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(JsTarget::Attached(applet)));
}

/// Install a fully-formed [`JsTarget`] (embedded or attached) directly.
pub fn set_current_target(target: JsTarget) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(target));
}

/// Take the target back out (to inspect its ledger/receipts after a JS run).
pub fn take_current_target() -> Option<JsTarget> {
    CURRENT_APPLET.with(|c| c.borrow_mut().take())
}

/// Take the EMBEDDED applet back out, if the current target is embedded (else `None`).
/// Preserves the existing `take_current_applet()` shape for the embedded callers.
pub fn take_current_applet() -> Option<Applet> {
    match CURRENT_APPLET.with(|c| c.borrow_mut().take()) {
        Some(JsTarget::Embedded(a)) => Some(*a),
        other => {
            // Not embedded — put it back so an attached caller can take it.
            if let Some(t) = other {
                CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(t));
            }
            None
        }
    }
}

/// The last native-function error, if any.
pub fn last_native_error() -> Option<String> {
    LAST_NATIVE_ERROR.with(|e| e.borrow().clone())
}

fn record_error(msg: String) {
    LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = Some(msg));
}

/// The JS prelude — builds `deos.applet`/`app.fire`/`app.get`/`app.view` atop the
/// `__deos_*` natives. `app.view.set/get` route to the EPHEMERAL natives (in-memory;
/// never a turn). `deos.applet(spec)` turns each declared affordance name into a
/// method that fires the corresponding verified turn.
const PRELUDE: &str = r#"
    var deos = {
        applet: function(spec) {
            var handle = {
                fire: function(name, arg) { return __deos_fire(String(name), arg | 0); },
                get: function(slot) { return __deos_get(slot | 0); },
                view: {
                    set: function(k, v) { __deos_view_set(String(k), String(v)); },
                    get: function(k) { return __deos_view_get(String(k)); }
                }
            };
            var names = (spec && spec.affordances) || [];
            for (var i = 0; i < names.length; i++) {
                (function(n) {
                    handle[n] = function(arg) { return handle.fire(n, arg | 0); };
                })(names[i]);
            }
            return handle;
        },
        // ── THE REFLECTIVE CRAWL (slice 2) — JS objects crawl the live image ──────
        // Reflection is a cap-bounded, attested READ (confers no authority), distinct
        // from driving (a turn). Every accessor parses JSON from a `__deos_reflect_*`
        // native that projects the live ledger through `deos-reflect`.
        world: {
            // every cell id on the ledger (the unbounded crawl root)
            cells: function() { return JSON.parse(__deos_world_cells()); },
            cellCount: function() { return this.cells().length; },
            // the capability web (nodes + edges)
            ocap: function() { return JSON.parse(__deos_world_ocap()); },
            // cheap fork-based time-travel: snapshot returns a token; rewind(token)
            // restores the ledger to it (a READ-restore — receipts truncate to match).
            snapshot: function() { return __deos_snapshot() | 0; },
            rewind: function(token) { return __deos_rewind(token | 0) | 0; }
        },
        // fuzzy spotter over every cell's faces → [{cell, score, snippet}], best-first.
        search: function(q) { return JSON.parse(__deos_search(String(q))); },
        // ── THE VIEW LANGUAGE (slice 3) — a serializable element-tree (data, NOT gpui) ─
        // `deos.ui.*` build a view-tree describing gpui-component widgets; a button's
        // onClick is `{turn:"<affordance>", arg:N}` (a real turn when rendered+fired);
        // a `bind(() => expr)` node re-reads its value on demand (fine-grained signal).
        // deos-js stays GPUI-FREE: this produces DATA; a separate renderer draws it.
        ui: (function() {
            function node(kind, props, children) {
                var n = { kind: kind, props: props || {} };
                if (children !== undefined) n.children = children;
                return n;
            }
            return {
                vstack: function() { return node("vstack", {}, Array.prototype.slice.call(arguments)); },
                row:    function() { return node("row", {}, Array.prototype.slice.call(arguments)); },
                text:   function(s) { return node("text", { text: String(s) }); },
                // a bound value node: re-evaluates `fn()` each read (signal binding).
                bind:   function(fn) { var n = node("bind", {}); n.read = fn; return n; },
                // a button whose onClick fires affordance `aff` with `arg` — a real turn.
                button: function(label, aff, arg) {
                    return node("button", { label: String(label), onClick: { turn: String(aff), arg: (arg | 0) } });
                },
                // input(viewKey) — an ephemeral draft field. The 2-arg form
                // input(viewKey, {fireTurn, submitLabel}) EXTENDS it: the submitted draft
                // becomes the `arg` of `fireTurn` (input → a real verified turn).
                input:  function(viewKey, opts) {
                    var p = { bindView: String(viewKey) };
                    if (opts && opts.fireTurn) { p.fireTurn = String(opts.fireTurn); p.submitLabel = String(opts.submitLabel || "submit"); }
                    return node("input", p);
                },
                list:   function(items) { return node("list", {}, items || []); },
                table:  function(rows) { return node("table", {}, rows || []); },
                // ── The RICHNESS EXPANSION — the rest of the §1 vocabulary, authorable here so a
                //    card author (or an agent via run_js) emits the rich nodes the renderers paint.
                // section(title, ...children) — a titled, bordered container; tag accents it.
                section: function(title) {
                    return node("section", { title: String(title || ""), tag: "" }, Array.prototype.slice.call(arguments, 1));
                },
                // sectionTagged(title, tag, ...children) — a section with a styling/disclosure tag.
                sectionTagged: function(title, tag) {
                    return node("section", { title: String(title || ""), tag: String(tag || "") }, Array.prototype.slice.call(arguments, 2));
                },
                // tabs({tabs, selectedSlot, selectTurn}, ...panels) — a stateful tab-strip (a tab
                // switch is a real verified turn writing selectedSlot).
                tabs: function(spec) {
                    spec = spec || {};
                    return node("tabs", { tabs: spec.tabs || [], selectedSlot: (spec.selectedSlot | 0), selectTurn: String(spec.selectTurn || "") }, Array.prototype.slice.call(arguments, 1));
                },
                // grid({cols}, ...children) — a wrapping spatial cell field (Wonder / icon field).
                grid: function(spec) {
                    spec = spec || {};
                    return node("grid", { cols: (spec.cols | 0) }, Array.prototype.slice.call(arguments, 1));
                },
                divider: function() { return node("divider", {}); },
                // breadcrumb([{label, turn?, arg?}, ...]) — a navigation path (clickable crumbs).
                breadcrumb: function(items) { return node("breadcrumb", { items: items || [] }); },
                // gauge({slot, max, label}) — a BOUND progress/balance bar (live slot fill).
                gauge: function(spec) { spec = spec || {}; return node("gauge", { slot: (spec.slot | 0), max: (spec.max | 0), label: String(spec.label || "") }); },
                // progress({value, max, label}) — a STATIC (literal) progress bar.
                progress: function(spec) { spec = spec || {}; return node("progress", { value: (spec.value | 0), max: (spec.max | 0), label: String(spec.label || "") }); },
                // pill(text, tag) — a colored status badge (good/warn/bad/accent/muted).
                pill: function(text, tag) { return node("pill", { text: String(text), tag: String(tag || "") }); },
                // icon(glyph, tag) — a tinted glyph indicator.
                icon: function(glyph, tag) { return node("icon", { glyph: String(glyph), tag: String(tag || "") }); },
                // menu([{label, turn, arg, enabled?}, ...]) — a context actuation menu.
                menu: function(items) { return node("menu", { items: items || [] }); },
                // halo({targetSlot?}, [{glyph, turn, arg, enabled?}, ...]) — the Pharo handle-ring.
                halo: function(spec, handles) { spec = spec || {}; return node("halo", { targetSlot: (spec.targetSlot | 0), handles: handles || [] }); },
                // slider({slot, min, max, turn}) — a bound draggable value → seek turn.
                slider: function(spec) { spec = spec || {}; return node("slider", { slot: (spec.slot | 0), min: (spec.min | 0), max: (spec.max | 0), turn: String(spec.turn || "") }); },
                // toggle({slot, onTurn, offTurn, glyphOn?, glyphOff?, label?}) — an affordance checkbox.
                toggle: function(spec) {
                    spec = spec || {};
                    var p = { slot: (spec.slot | 0), onTurn: String(spec.onTurn || ""), offTurn: String(spec.offTurn || ""), label: String(spec.label || "") };
                    if (spec.glyphOn) p.glyphOn = String(spec.glyphOn);
                    if (spec.glyphOff) p.glyphOff = String(spec.glyphOff);
                    return node("toggle", p);
                },
                // tile({handle, w, h}) — a card-referenced host-painted region (the Servo tile).
                tile: function(spec) { spec = spec || {}; return node("tile", { handle: String(spec.handle || ""), w: (spec.w | 0), h: (spec.h | 0) }); }
            };
        })(),
        // a reflective handle on ONE cell: its substances · faces · affordances · frustum.
        cell: function(id) {
            var cid = String(id);
            return {
                id: cid,
                // the four substances (value/authority/state/evidence) as a field tree
                reflect: function() {
                    var j = __deos_cell(cid);
                    return j === "null" ? null : JSON.parse(j);
                },
                // a quick read of a named substance field's value
                field: function(key) {
                    var r = this.reflect();
                    if (!r) return null;
                    for (var i = 0; i < r.fields.length; i++)
                        if (r.fields[i].key === key) return r.fields[i].value;
                    return null;
                },
                // the moldable faces (RawFields · Graph · DomainVisual · Provenance) —
                // each a distinct obs-projection of the SAME cell.
                present: function() {
                    var j = __deos_present(cid);
                    return j === "null" ? null : JSON.parse(j);
                },
                // the cap-gated message list a holder of `viewer`'s authority may fire.
                // `viewer` is an authority label: "none"/"signature"/"proof"/"either".
                affordances: function(viewer) {
                    return JSON.parse(__deos_affordances(String(viewer || "none")));
                },
                // .as(viewer) → the cap-bounded view: which cells `viewer` may crawl,
                // and a reflect() that yields null for an unobservable target.
                as: function(viewer) {
                    var v = String(viewer);
                    return {
                        frustum: function() { return JSON.parse(__deos_frustum(v)); },
                        canObserve: function(target) {
                            var f = this.frustum();
                            return f.visible.indexOf(String(target)) >= 0;
                        },
                        reflect: function(target) {
                            var j = __deos_frustum_reflect(v, String(target));
                            return j === "null" ? null : JSON.parse(j);
                        }
                    };
                }
            };
        },
        // ── THE CARD EDITOR (the authoring surface) — `deos.editor.*` ──────────────
        // A user OR an agent (via run_js) authors a card LIVE from inside the image:
        // edit its view (a receipted structural patch + blame), set a field (a real
        // verified turn), weld a fireable affordance. Every gesture is bounded by the
        // editor's `held` (the cap tooth) AND by `cardId` (you may only author the
        // editor's own card) — an over-reach returns -1/null, NO patch, NO turn.
        //
        // `card()` names the editor's current card (the id editView/setField target).
        editor: {
            card: function() { var c = __deos_editor_card(); return c === "" ? null : c; },
            // view() — the editor card's CURRENT view-tree (the {kind,props,children}
            // JSON deos-view consumes), parsed to an object. The READ half of the
            // reflective loop: an agent reads the live surface's own shape (reflect-on)
            // before rewriting it. A pure read — NO patch, NO turn. null if no editor.
            view: function() {
                var j = __deos_editor_view();
                return j === "null" ? null : JSON.parse(j);
            },
            // editView(cardId, patchSpec) — apply a structural view-patch, re-fold the
            // view-source, leave a receipted patch + blame. patchSpec is a small object:
            //   {op:"addButton", label, affordance, arg}  — append a button (a turn);
            //   {op:"addText",   text}                     — append a text node;
            //   {op:"addBind",   slot, label}             — append a live state-bound row;
            //   {op:"relabel",   target, text}            — relabel a text node.
            // Returns the re-folded view-tree (the {kind,props,children} JSON deos-view
            // consumes), or null on refusal (unauthorized / wrong card / no-op).
            editView: function(cardId, patchSpec) {
                var j = __deos_editor_edit_view(String(cardId), JSON.stringify(patchSpec || {}));
                return j === "null" ? null : JSON.parse(j);
            },
            // setField(cardId, slot, value) — a real SetField verified turn on the card's
            // state. Returns 1 on commit (a re-read reflects it), -1 on refusal.
            setField: function(cardId, slot, value) {
                return __deos_editor_set_field(String(cardId), slot | 0, value | 0) | 0;
            },
            // addAffordance(cardId, spec) — weld a fireable affordance into the card's
            // program. spec: {name, required:"none"/"signature"/"proof"/"either",
            //   op:"add"/"sub"/"set"/"track", slot, value}. ("track": slot := max(arg,0)
            //   — the fire's arg IS the new value, the census-mirroring write verb.)
            // Returns 1 on commit, -1 on refusal.
            addAffordance: function(cardId, spec) {
                return __deos_editor_add_affordance(String(cardId), JSON.stringify(spec || {})) | 0;
            }
        },
        // ── THE PRIVATE SERVER SURFACE — `deos.server.*` ───────────────────────────
        // A hosted userspace program (run headless INSIDE a dregg node) holds state +
        // offers cap-gated affordances players connect to + fire. The program's setup
        // registers its surface here; the HOST publishes it for client discovery.
        //
        //   defineAffordance({name, required, effects:[...], instance:<hex>?})  — register
        //     a cap-gated affordance carrying ARBITRARY effects (the keystone). `required`
        //     is an authority label ("none"/"signature"/"proof"/"either"). Each effect is
        //     a small object the host decodes into a real `Effect`:
        //       {type:"setField", cell:<hex>, index:N, value:N}
        //       {type:"incrementNonce", cell:<hex>}
        //     `instance` (optional) scopes the affordance to a forked instance (a cell hex
        //     returned by `fork()`); omit it to register on the root server surface.
        //     Returns 1 on register, -1 on a malformed spec.
        //   fork(seedLabel) — INSTANCE the server's world: mint a fresh OPEN instance cell
        //     (a real verified turn through the host) — a cap-bounded fork for a party or
        //     session (the membrane-fork). Returns the instance cell id hex (the discovery
        //     key clients connect to), or "" on refusal. Scope affordances to it by passing
        //     its hex as `defineAffordance`'s `instance`.
        //   spawnCell(seedHex, perms) — GM superpower: mint a fresh cell (a real
        //     CreateCell turn through the host) under the server's authority. Returns
        //     the new cell id hex, or "" on refusal. `perms` is "open" (default) for a
        //     fully-open cell.
        //   grant(toCellHex, onCellHex, required) — GM superpower: grant a capability
        //     over `onCell` to `toCell` (a real GrantCapability turn). Returns 1/-1.
        //   setField(cellHex, index, value) — GM superpower: commit a `SetField` NOW on
        //     any cell the GM governs (a real verified turn through the host). The GM
        //     uses this to stamp a freshly-spawned cell's stats (level/xp/room), to fire
        //     an NPC reaction, and to apply a LEVEL-UP after observing XP cross a
        //     threshold. Returns 1 on commit, -1 on refusal. (Players can't reach this —
        //     it is a server-side native; a player drives the world only via signed
        //     turns over the caps the GM granted them.)
        //   getField(cellHex, index) — read a u64 field off the live ledger (the GM
        //     observing a player's character, e.g. its XP). Returns the value, or -1 if
        //     the cell/field is absent.
        server: {
            defineAffordance: function(spec) {
                return __deos_server_define_affordance(JSON.stringify(spec || {})) | 0;
            },
            fork: function(seedLabel) {
                var c = __deos_server_fork(String(seedLabel || ""));
                return c === "" ? null : c;
            },
            spawnCell: function(seedHex, perms) {
                var c = __deos_server_spawn_cell(String(seedHex || ""), String(perms || "open"));
                return c === "" ? null : c;
            },
            grant: function(toCellHex, onCellHex, required) {
                return __deos_server_grant(String(toCellHex), String(onCellHex), String(required || "signature")) | 0;
            },
            setField: function(cellHex, index, value) {
                return __deos_server_set_field(String(cellHex), index | 0, value | 0) | 0;
            },
            getField: function(cellHex, index) {
                return __deos_server_get_field(String(cellHex), index | 0) | 0;
            }
        },
        // ── THE BOUNDED MULTI-CELL COMPOSE — `deos.compose([...])` ──────────────────
        // The agent's brain decides-and-executes a genuinely useful MULTI-CELL task as ONE
        // all-or-nothing BOUNDED gesture on the live World: e.g. stand up a shared notebook
        // for a collaborator = mint the cell + seed its title + grant the collaborator a cap.
        // Unlike `deos.server.*` (the UNBOUNDED GM superpowers), every leg is checked against
        // the agent's mandate `held` (the cap tooth) and its scope (a leg may only touch a
        // held cell) BEFORE any turn commits — an over-reach aborts the WHOLE story in-band
        // with NOTHING committed (no partial leg). Each leg is one cap-gated verified turn.
        //
        //   deos.compose(steps) — `steps` is an array of leg objects:
        //     { op:"mintCard", seed:<label>, fields:[[slot,value],...], funding:N?, required:<auth>? }
        //         — stand up a fresh OPEN cell (id = hash(seed)); it joins scope for later
        //           legs. `fields` seed its genesis model. Returns its id hex in `.minted`.
        //     { op:"setField", cell:<hex>, slot:N, value:N, required:<auth>? }
        //         — write a field on a HELD cell (a foreign cell is the scope over-reach).
        //     { op:"grant", from:<hex>, to:<hex>, granted:<auth>?, required:<auth>? }
        //         — grant a cap over a HELD `from` cell to peer `to` (granted ⊑ held).
        //   `required`/`granted`/`auth` are labels: "none"/"signature"/"proof"/"either".
        //   Returns an object:
        //     { ok:bool, committed:N, receipts:[hex,...], minted:[hex,...], refusal:str? }
        //   on an over-reach `ok:false, committed:0` and `refusal` names the failed leg.
        compose: function(steps) {
            var json = JSON.stringify(steps || []);
            var out = __deos_compose(json);
            return JSON.parse(out);
        }
    };
"#;

/// A real SpiderMonkey runtime with the `deos` binding available.
pub struct JsRuntime {
    rt: Runtime,
    // The engine handle must stay alive for the runtime's lifetime.
    _engine: JSEngine,
}

impl JsRuntime {
    /// Boot a genuine SpiderMonkey runtime. The `deos` binding + prelude are installed
    /// per-[`Self::eval`] (on a fresh global) so a single test script sees them.
    pub fn new() -> Result<Self, String> {
        let engine = JSEngine::init().map_err(|e| format!("JSEngine::init: {e:?}"))?;
        let rt = Runtime::new(engine.handle());
        Ok(JsRuntime {
            rt,
            _engine: engine,
        })
    }

    /// Evaluate a JS program against a fresh global that has the `deos` binding. The
    /// program drives the thread-local applet. Returns the script's result as an i32
    /// if it produced one (else `None`).
    pub fn eval(&mut self, source: &str) -> Result<Option<i32>, String> {
        LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = None);

        let cx = self.rt.cx();
        let realm_opts = RealmOptions::default();
        unsafe {
            rooted!(&in(cx) let global = JS_NewGlobalObject(
                cx,
                &SIMPLE_GLOBAL_CLASS,
                ptr::null_mut(),
                OnNewGlobalHookOption::FireOnNewGlobalHook,
                &*realm_opts,
            ));

            // ENTER THE REALM before defining the natives / running scripts — the
            // proven upstream pattern (callback.rs). Defining a function on, or
            // converting a string within, a global that is NOT the active realm
            // segfaults. `global_and_reborrow` yields the realm-bound global handle +
            // the realm context to use for everything below.
            let mut realm = AutoRealm::new_from_handle(cx, global.handle());
            let (g, realm_cx) = realm.global_and_reborrow();

            // Install the native bridge functions on the realm's global.
            for (name, f, nargs) in [
                // drive (slice 1)
                (c"__deos_fire", native_fire as RawNative, 2u32),
                (c"__deos_get", native_get as RawNative, 1),
                (c"__deos_view_set", native_view_set as RawNative, 2),
                (c"__deos_view_get", native_view_get as RawNative, 1),
                // crawl (slice 2) — the reflective natives (return JSON strings)
                (c"__deos_world_cells", native_world_cells as RawNative, 0),
                (c"__deos_world_ocap", native_world_ocap as RawNative, 0),
                (c"__deos_cell", native_cell as RawNative, 1),
                (c"__deos_frustum", native_frustum as RawNative, 1),
                (
                    c"__deos_frustum_reflect",
                    native_frustum_reflect as RawNative,
                    2,
                ),
                // fan-out — present faces · affordances · snapshot/rewind · spotter
                (c"__deos_present", native_present as RawNative, 1),
                (c"__deos_affordances", native_affordances as RawNative, 1),
                (c"__deos_snapshot", native_snapshot as RawNative, 0),
                (c"__deos_rewind", native_rewind as RawNative, 1),
                (c"__deos_search", native_search as RawNative, 1),
                // author (the card editor) — view/field/affordance, cap-gated
                (c"__deos_editor_card", native_editor_card as RawNative, 0),
                (c"__deos_editor_view", native_editor_view as RawNative, 0),
                (
                    c"__deos_editor_edit_view",
                    native_editor_edit_view as RawNative,
                    2,
                ),
                (
                    c"__deos_editor_set_field",
                    native_editor_set_field as RawNative,
                    3,
                ),
                (
                    c"__deos_editor_add_affordance",
                    native_editor_add_affordance as RawNative,
                    2,
                ),
                // private server (the deos-host surface) — define / spawn / grant
                (
                    c"__deos_server_define_affordance",
                    native_server_define_affordance as RawNative,
                    1,
                ),
                (c"__deos_server_fork", native_server_fork as RawNative, 1),
                (
                    c"__deos_server_spawn_cell",
                    native_server_spawn_cell as RawNative,
                    2,
                ),
                (c"__deos_server_grant", native_server_grant as RawNative, 3),
                (
                    c"__deos_server_set_field",
                    native_server_set_field as RawNative,
                    3,
                ),
                (
                    c"__deos_server_get_field",
                    native_server_get_field as RawNative,
                    2,
                ),
                // bounded multi-cell compose (the agent's useful, atomic, held-bounded story)
                (c"__deos_compose", native_compose as RawNative, 1),
            ] {
                let defined = JS_DefineFunction(realm_cx, g, name.as_ptr(), Some(f), nargs, 0);
                if defined.is_null() {
                    return Err(format!("JS_DefineFunction failed for {name:?}"));
                }
            }

            // (1) install the prelude on this global; (2) run the user's source.
            eval_on(realm_cx, g, PRELUDE)?;
            let r = eval_on(realm_cx, g, source)?;

            if let Some(err) = last_native_error() {
                return Err(format!("native error during eval: {err}"));
            }
            Ok(r)
        }
    }

    /// THE ATTACH RUN — install an [`AttachedApplet`] (bound to a PROVIDED live World)
    /// as the runtime's target, eval `source` against it, then take the target back
    /// out so the caller can read the committed-fire tape. The crawl + fires inside
    /// `source` drive the ATTACHED World's real cells (a receipt landing on the live
    /// ledger), with the cap tooth mounted under the agent's `held`.
    ///
    /// Returns `(script_result, committed_receipt_hashes, the_target_back)`. The
    /// caller keeps the [`AttachedApplet`] (and through it the `WorldSink`) to inspect
    /// the live ledger after the run.
    pub fn run_attached(
        &mut self,
        applet: AttachedApplet,
        source: &str,
    ) -> Result<AttachRunOutcome, String> {
        set_current_attached(applet);
        let eval = self.eval(source);
        let target = take_current_target();
        let attached = match target {
            Some(JsTarget::Attached(a)) => a,
            _ => return Err("attached target vanished during run".into()),
        };
        match eval {
            Ok(result) => Ok(AttachRunOutcome {
                result,
                receipts: attached.receipts().to_vec(),
                fires_committed: attached.receipt_count(),
                applet: attached,
            }),
            Err(e) => Err(e),
        }
    }

    /// THE AUTHORING RUN — install a [`CardEditor`] as the `deos.editor.*` target, eval
    /// `source` (which authors the card via `deos.editor.editView/setField/addAffordance`),
    /// then take the editor back out so the caller can read the authored card (its
    /// re-folded view, blame, receipts, the re-mintable manifest).
    ///
    /// The editor is INDEPENDENT of the crawl/drive target, so this composes with the
    /// embedded engine (install both `set_current_applet` + the editor) or an attached
    /// live World (`set_current_attached` + the editor) — the authoring surface is
    /// reachable in either run, and the authored card is a portable cell either way.
    ///
    /// Returns `(script_result, the_editor_back)`.
    pub fn run_authoring(
        &mut self,
        editor: CardEditor,
        source: &str,
    ) -> Result<(Option<i32>, CardEditor), String> {
        set_current_editor(editor);
        let eval = self.eval(source);
        let editor =
            take_current_editor().ok_or_else(|| "card editor vanished during run".to_string())?;
        match eval {
            Ok(result) => Ok((result, editor)),
            Err(e) => Err(e),
        }
    }

    /// THE AUTHORING-WITH-CRAWL RUN — like [`Self::run_authoring`], but ALSO installs a
    /// crawl/drive [`JsTarget`] (embedded or a live-World attach) so the authoring script
    /// can READ the live image (`deos.world.*`, `deos.cell(id)`) *while* it composes. The
    /// reflective-cockpit loop deepened from rewriting one surface to **composing a fresh
    /// surface from the live world-state**: the agent reads the real ledger, decides a
    /// layout, and authors it. The crawl read confers no authority (it is a witnessed
    /// read); authoring stays bounded by the editor's `held` (the cap tooth).
    ///
    /// Returns `(script_result, the_editor_back, the_crawl_target_back)`.
    pub fn run_authoring_with_crawl(
        &mut self,
        editor: CardEditor,
        target: JsTarget,
        source: &str,
    ) -> Result<(Option<i32>, CardEditor, JsTarget), String> {
        set_current_target(target);
        set_current_editor(editor);
        let eval = self.eval(source);
        let editor =
            take_current_editor().ok_or_else(|| "card editor vanished during run".to_string())?;
        let target =
            take_current_target().ok_or_else(|| "crawl target vanished during run".to_string())?;
        match eval {
            Ok(result) => Ok((result, editor, target)),
            Err(e) => Err(e),
        }
    }

    /// THE COMPOSE RUN — install an [`AttachedComposer`] (bound to a PROVIDED live World,
    /// mounted under the agent's `held`) as the `deos.compose(...)` target, eval `source`
    /// (which composes one or more bounded multi-cell stories via `deos.compose([...])`),
    /// then take the composer + the last compose outcome back out.
    ///
    /// The composer is INDEPENDENT of the crawl/drive target, so `deos.compose` composes
    /// against the live ledger here while `deos.world.cells()` still crawls it (the host may
    /// install BOTH an attached crawl target and the composer). Each composed leg is a
    /// cap-gated verified turn on the live World; an over-reach is refused in-band with
    /// nothing committed.
    ///
    /// Returns `(script_result, the_composer_back, the_compose_outcome)`.
    pub fn run_compose(
        &mut self,
        composer: AttachedComposer,
        source: &str,
    ) -> Result<ComposeRunOutcome, String> {
        set_current_composer(composer);
        let eval = self.eval(source);
        let composer =
            take_current_composer().ok_or_else(|| "composer vanished during run".to_string())?;
        let compose = take_last_compose();
        match eval {
            Ok(result) => Ok(ComposeRunOutcome {
                result,
                compose,
                composer,
            }),
            Err(e) => Err(e),
        }
    }
}

/// The outcome of a [`JsRuntime::run_compose`]: what the agent's multi-cell story did on the
/// live World.
pub struct ComposeRunOutcome {
    /// The script's i32 completion value, if any.
    pub result: Option<i32>,
    /// The outcome of the `deos.compose(...)` the JS ran (committed receipts + minted cells,
    /// or the in-band over-reach refusal). `None` if the script ran no compose.
    pub compose: Option<ComposeOutcome>,
    /// The composer handed back (its `WorldSink` reads the live ledger; its receipt tape +
    /// scope reflect what the story committed).
    pub composer: AttachedComposer,
}

/// The outcome of a [`JsRuntime::run_attached`]: what the JS did on the live World.
pub struct AttachRunOutcome {
    /// The script's i32 completion value, if any.
    pub result: Option<i32>,
    /// The receipt hashes the JS committed on the live World, in order.
    pub receipts: Vec<[u8; 32]>,
    /// How many verified turns committed (the audit-tape length).
    pub fires_committed: usize,
    /// The attached applet handed back (its `WorldSink` reads the live ledger).
    pub applet: AttachedApplet,
}

type RawNative = unsafe extern "C" fn(*mut RawJSContext, u32, *mut Value) -> bool;

/// Evaluate `source` against `global`, returning an i32 result if produced. The
/// rooted `rval` receives the script's completion value. `cx` must be the active
/// realm's context.
fn eval_on(
    cx: &mut SmContext,
    global: mozjs::rust::HandleObject,
    source: &str,
) -> Result<Option<i32>, String> {
    rooted!(&in(cx) let mut rval = UndefinedValue());
    let options = CompileOptionsWrapper::new(cx, c"deos.js".to_owned(), 1);
    match evaluate_script(cx, global, source, rval.handle_mut(), options) {
        Ok(()) => {
            let v = rval.get();
            if v.is_int32() {
                Ok(Some(v.to_int32()))
            } else {
                Ok(None)
            }
        }
        Err(()) => Err("evaluate_script returned an error".to_string()),
    }
}

/// Pull a UTF-8 String out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_string(cx: &mut SmContext, raw: mozjs::jsapi::HandleValue) -> String {
    let handle = mozjs::rust::Handle::from_raw(raw);
    let js = mozjs::rust::ToString(cx.raw_cx(), handle);
    rooted!(&in(cx) let rooted_str = js);
    unsafe extern "C" fn cb(message: *const core::ffi::c_char) {
        let m = CStr::from_ptr(message);
        let s = str::from_utf8(m.to_bytes()).unwrap_or("").to_string();
        SCRATCH.with(|sc| *sc.borrow_mut() = s);
    }
    EncodeStringToUTF8(cx, rooted_str.handle(), cb);
    // `mem::take` the scratch String out (leaving an empty one behind) rather than
    // cloning it — the value is consumed by the caller, so the clone was pure waste.
    SCRATCH.with(|sc| std::mem::take(&mut *sc.borrow_mut()))
}

/// Pull an i32 out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_i32(raw: mozjs::jsapi::HandleValue) -> i32 {
    let v = mozjs::rust::Handle::from_raw(raw).get();
    if v.is_int32() {
        v.to_int32()
    } else if v.is_double() {
        v.to_double() as i32
    } else {
        0
    }
}

// ── The native bridge functions ───────────────────────────────────────────────────

/// `__deos_fire(name, arg)` — fire an affordance = ONE cap-gated verified turn.
/// Returns the model's value at slot 0 after the turn (for the counter shape), or -1
/// on refusal (the cap tooth) / executor rejection.
unsafe extern "C" fn native_fire(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 1 {
        record_error("__deos_fire requires (name, arg)".into());
        args.rval().set(Int32Value(-1));
        return true;
    }
    let name = arg_string(&mut cx, args.get(0));
    let arg = if args.argc_ >= 2 {
        arg_i32(args.get(1)) as i64
    } else {
        0
    };

    // A cap-gate REFUSAL is an EXPECTED, JS-observable outcome (returns -1 with NO
    // receipt) — NOT a fatal eval error. Only a genuine fault (no applet, or the
    // executor rejecting an AUTHORIZED turn) poisons the eval.
    let outcome = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        match guard.as_mut() {
            Some(target) => match target.fire(&name, arg) {
                Ok(_receipt_hash) => FireOutcome::Committed(target.get_u64(0) as i32),
                Err(crate::applet::FireError::Unauthorized { .. }) => FireOutcome::Refused,
                Err(crate::applet::FireError::UnknownAffordance(n)) => {
                    FireOutcome::Fatal(format!("unknown affordance '{n}'"))
                }
                Err(crate::applet::FireError::Executor(r)) => {
                    FireOutcome::Fatal(format!("executor rejected authorized turn: {r}"))
                }
            },
            None => FireOutcome::Fatal("no applet installed".into()),
        }
    });

    match outcome {
        FireOutcome::Committed(v) => args.rval().set(Int32Value(v)),
        FireOutcome::Refused => args.rval().set(Int32Value(-1)),
        FireOutcome::Fatal(e) => {
            record_error(e);
            args.rval().set(Int32Value(-1));
        }
    }
    true
}

/// The three faces of a fire from JS: committed (a verified turn), refused (the cap
/// gate said no — expected, JS sees -1), or fatal (a real fault that poisons eval).
enum FireOutcome {
    Committed(i32),
    Refused,
    Fatal(String),
}

/// `__deos_get(slot)` — a witnessed read off the live ledger.
unsafe extern "C" fn native_get(_context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let args = CallArgs::from_vp(vp, argc);
    let slot = if args.argc_ >= 1 {
        arg_i32(args.get(0)) as usize
    } else {
        0
    };
    let v = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_u64(slot) as i32)
            .unwrap_or(-1)
    });
    args.rval().set(Int32Value(v));
    true
}

/// `__deos_view_set(key, value)` — ephemeral view-state. NO turn, NO receipt.
unsafe extern "C" fn native_view_set(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 2 {
        record_error("__deos_view_set requires (key, value)".into());
        args.rval().set(UndefinedValue());
        return true;
    }
    let key = arg_string(&mut cx, args.get(0));
    let val = arg_string(&mut cx, args.get(1));
    CURRENT_APPLET.with(|c| {
        if let Some(a) = c.borrow_mut().as_mut() {
            a.set_view(&key, &val);
        }
    });
    args.rval().set(UndefinedValue());
    true
}

/// `__deos_view_get(key)` — read ephemeral view-state. Returns 1 if present else 0.
unsafe extern "C" fn native_view_get(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let key = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let present = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_view(&key).is_some())
            .unwrap_or(false)
    });
    args.rval().set(Int32Value(if present { 1 } else { 0 }));
    true
}

// ── THE REFLECTIVE CRAWL natives (slice 2) — each returns a JSON STRING ────────────

/// Set the rval of a native call to a freshly-allocated JS string. Returns false (the
/// native should return false) only on allocation failure.
unsafe fn return_string(cx: &mut SmContext, args: &CallArgs, s: &str) -> bool {
    let js_str = JS_NewStringCopyN(cx, s.as_ptr() as *const core::ffi::c_char, s.len());
    if js_str.is_null() {
        record_error("JS_NewStringCopyN failed".into());
        args.rval().set(UndefinedValue());
        return false;
    }
    args.rval().set(StringValue(&*js_str));
    true
}

/// `__deos_world_cells()` → JSON array of every cell id on the applet's ledger.
unsafe extern "C" fn native_world_cells(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "[]".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::world_cells_json(l));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_world_ocap()` → JSON of the capability web (nodes + edges).
unsafe extern "C" fn native_world_ocap(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "{\"nodes\":[],\"edges\":[]}".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::world_ocap_json(l));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_cell(id)` → JSON of the cell's four substances (or `"null"` if absent).
unsafe extern "C" fn native_cell(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match reflect_binding::parse_cell_id(&id_hex) {
            Some(id) => {
                let mut out = "null".to_string();
                applet.with_ledger(&mut |l| {
                    out = reflect_binding::cell_json(l, &id).unwrap_or_else(|| "null".to_string())
                });
                out
            }
            None => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum(viewer)` → JSON of the cap-bounded view (which cells viewer crawls).
unsafe extern "C" fn native_frustum(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        };
        match reflect_binding::parse_cell_id(&viewer_hex) {
            Some(viewer) => {
                let mut out = "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string();
                applet.with_ledger(&mut |l| out = reflect_binding::frustum_json(l, &viewer));
                out
            }
            None => "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum_reflect(viewer, target)` → the cell JSON if `viewer` may observe
/// `target`, else `"null"` (the attested read: an unreachable cell is absent).
unsafe extern "C" fn native_frustum_reflect(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let target_hex = if args.argc_ >= 2 {
        arg_string(&mut cx, args.get(1))
    } else {
        String::new()
    };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match (
            reflect_binding::parse_cell_id(&viewer_hex),
            reflect_binding::parse_cell_id(&target_hex),
        ) {
            (Some(viewer), Some(target)) => {
                let mut out = "null".to_string();
                applet.with_ledger(&mut |l| {
                    out = reflect_binding::frustum_reflect_json(l, &viewer, &target)
                });
                out
            }
            _ => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

// ── THE FAN-OUT natives (present · affordances · snapshot/rewind · spotter) ────────

/// `__deos_present(id)` → the moldable faces JSON (RawFields/Graph/DomainVisual/
/// Provenance), or `"null"` if the cell is absent.
unsafe extern "C" fn native_present(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match reflect_binding::parse_cell_id(&id_hex) {
            Some(id) => {
                // Borrow the full receipt tape (no `to_vec` clone of the whole lineage
                // per present()); the ledger read nests inside that borrow.
                applet.with_full_receipts(|receipts| {
                    let mut out = "null".to_string();
                    applet.with_ledger(&mut |l| {
                        out = reflect_binding::cell_present_json(l, &id, receipts)
                            .unwrap_or_else(|| "null".to_string())
                    });
                    out
                })
            }
            None => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_affordances(viewerAuthLabel)` → the cap-gated message list the holder of
/// that authority may fire, as JSON. The label is "none"/"signature"/"proof"/"either".
unsafe extern "C" fn native_affordances(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let label = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        "none".into()
    };
    let held = parse_auth_label(&label);
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        match guard.as_ref() {
            Some(a) => {
                reflect_binding::cell_affordances_json(&a.cell(), &a.affordance_specs(), &held)
            }
            None => "[]".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_snapshot()` → an integer token denoting the saved ledger state (for rewind).
unsafe extern "C" fn native_snapshot(
    _context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let args = CallArgs::from_vp(vp, argc);
    let token = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        match guard.as_ref().and_then(|a| a.snapshot()) {
            Some((bytes, count)) => SNAPSHOTS.with(|s| {
                let mut v = s.borrow_mut();
                v.push((bytes, count));
                (v.len() - 1) as i32
            }),
            None => -1,
        }
    });
    args.rval().set(Int32Value(token));
    true
}

/// `__deos_rewind(token)` → restore the ledger to snapshot `token`. Returns 1 on
/// success, -1 on a bad token or restore failure. The audit tape truncates to match —
/// time-travel that leaves no phantom receipts.
unsafe extern "C" fn native_rewind(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let _cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let token = if args.argc_ >= 1 {
        arg_i32(args.get(0))
    } else {
        -1
    };
    let ok = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        let applet = match guard.as_mut() {
            Some(a) => a,
            None => return false,
        };
        let snap = SNAPSHOTS.with(|s| s.borrow().get(token as usize).cloned());
        match snap {
            Some((bytes, count)) => applet.restore(&bytes, count).is_ok(),
            None => false,
        }
    });
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// `__deos_search(q)` → the spotter hits JSON (fuzzy over every cell's faces).
unsafe extern "C" fn native_search(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let q = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "[]".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::spotter_json(l, &q));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// Parse an authority label from JS into an `AuthRequired` (the held authority for
/// affordance projection). Unknown → `None` (the broadest — sees everything).
fn parse_auth_label(label: &str) -> dregg_cell::AuthRequired {
    use dregg_cell::AuthRequired;
    match label.to_lowercase().as_str() {
        "signature" | "sig" => AuthRequired::Signature,
        "proof" => AuthRequired::Proof,
        "either" => AuthRequired::Either,
        "impossible" => AuthRequired::Impossible,
        _ => AuthRequired::None,
    }
}

// ── THE CARD EDITOR natives (the authoring surface) — `deos.editor.*` ──────────────
//
// Each authors the thread-local [`CardEditor`] (installed by the host under its own
// `held`). The bound the agent cannot exceed is TWO-FOLD: (1) the cap tooth in
// `CardEditor` (`held` must satisfy the card's `edit_authority`) and (2) `cardId` must
// be the editor's OWN card — authoring a card outside the editor's reach is refused
// in-band (no patch, no turn), exactly the run_js confinement bar.

/// `cardId` matches the installed editor's card iff equal (case-insensitive hex). A
/// mismatch is the "author the wrong card" over-reach the JS layer refuses.
fn editor_card_matches(editor: &CardEditor, card_id_hex: &str) -> bool {
    reflect_binding::id_hex(&editor.card().cell()).eq_ignore_ascii_case(card_id_hex.trim())
}

/// `__deos_editor_card()` → the editor's card id hex, or `""` if no editor installed.
unsafe extern "C" fn native_editor_card(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id = CURRENT_EDITOR.with(|c| {
        c.borrow()
            .as_ref()
            .map(|e| reflect_binding::id_hex(&e.card().cell()))
            .unwrap_or_default()
    });
    return_string(&mut cx, &args, &id)
}

/// `__deos_editor_view()` → the editor card's CURRENT view-tree JSON (the
/// `{kind,props,children}` shape `deos-view`'s `parse_view_tree` consumes), or `"null"`
/// if no editor is installed. This is the READ half of the reflective loop: an agent
/// reads the live surface's own tree (reflect-on) BEFORE it rewrites it — no patch, no
/// turn, a pure cap-free read of the surface's current shape.
unsafe extern "C" fn native_editor_view(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_EDITOR.with(|c| {
        c.borrow()
            .as_ref()
            .map(|e| e.view_source())
            .unwrap_or_else(|| "null".to_string())
    });
    return_string(&mut cx, &args, &json)
}

/// Build a [`ViewPatch`] from the JS `patchSpec` JSON (`{op, ...}`). Returns the parse
/// error string on a malformed/unknown spec.
fn parse_view_patch(spec_json: &str) -> Result<ViewPatch, String> {
    let v: serde_json::Value =
        serde_json::from_str(spec_json).map_err(|e| format!("patchSpec JSON: {e}"))?;
    let op = v.get("op").and_then(|o| o.as_str()).unwrap_or("");
    let s = |k: &str| v.get(k).and_then(|x| x.as_str()).unwrap_or("").to_string();
    let i = |k: &str| v.get(k).and_then(|x| x.as_i64()).unwrap_or(0);
    match op {
        "addButton" => Ok(ViewPatch::AddButton {
            label: s("label"),
            turn: s("affordance"),
            arg: i("arg"),
        }),
        "addText" => Ok(ViewPatch::AddText { text: s("text") }),
        "addBind" => Ok(ViewPatch::AddBind {
            slot: i("slot").max(0) as usize,
            label: s("label"),
        }),
        "relabel" => Ok(ViewPatch::Relabel {
            from: s("target"),
            to: s("text"),
        }),
        other => Err(format!("unknown view-patch op '{other}'")),
    }
}

/// `__deos_editor_edit_view(cardId, patchSpec)` → the re-folded view-tree JSON on a
/// committed patch, else `"null"` (refused: unauthorized / wrong card / no-op / bad
/// spec). A view-patch leaves a receipted patch + blame on the card's chain.
unsafe extern "C" fn native_editor_edit_view(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let card_id = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let spec_json = if args.argc_ >= 2 {
        arg_string(&mut cx, args.get(1))
    } else {
        String::new()
    };
    let json = CURRENT_EDITOR.with(|c| {
        let mut guard = c.borrow_mut();
        let editor = match guard.as_mut() {
            Some(e) => e,
            None => return "null".to_string(),
        };
        // (1) cardId must be the editor's own card (the wrong-card over-reach).
        if !editor_card_matches(editor, &card_id) {
            return "null".to_string();
        }
        // (2) the structural patch (the cap tooth runs inside `edit_view`).
        let patch = match parse_view_patch(&spec_json) {
            Ok(p) => p,
            Err(_) => return "null".to_string(),
        };
        match editor.edit_view(patch) {
            Ok(edit) => edit.tree.to_json(),
            // Unauthorized / no-op / fire fault → no patch, refused in-band.
            Err(EditError::Unauthorized) | Err(EditError::NoOp) => "null".to_string(),
            Err(e) => {
                record_error(format!("editor.editView: {e}"));
                "null".to_string()
            }
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_editor_set_field(cardId, slot, value)` → 1 on a committed `SetField` turn,
/// -1 on refusal (unauthorized / wrong card). A re-read reflects the new value.
unsafe extern "C" fn native_editor_set_field(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let card_id = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let slot = if args.argc_ >= 2 {
        arg_i32(args.get(1)).max(0) as usize
    } else {
        0
    };
    let value = if args.argc_ >= 3 {
        arg_i32(args.get(2)).max(0) as u64
    } else {
        0
    };
    let ok = CURRENT_EDITOR.with(|c| {
        let mut guard = c.borrow_mut();
        let editor = match guard.as_mut() {
            Some(e) => e,
            None => return false,
        };
        if !editor_card_matches(editor, &card_id) {
            return false;
        }
        match editor.set_field(slot, value) {
            Ok(_receipt) => true,
            Err(EditError::Unauthorized) => false,
            Err(e) => {
                record_error(format!("editor.setField: {e}"));
                false
            }
        }
    });
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// Build an [`AffordanceSpec`] from the JS spec JSON (`{name, required, op, slot, value}`).
fn parse_affordance_spec(spec_json: &str) -> Result<AffordanceSpec, String> {
    let v: serde_json::Value =
        serde_json::from_str(spec_json).map_err(|e| format!("affordance spec JSON: {e}"))?;
    let name = v
        .get("name")
        .and_then(|x| x.as_str())
        .unwrap_or("")
        .to_string();
    if name.is_empty() {
        return Err("affordance spec needs a name".into());
    }
    let required = parse_auth_label(v.get("required").and_then(|x| x.as_str()).unwrap_or("none"));
    let slot = v.get("slot").and_then(|x| x.as_u64()).unwrap_or(0) as usize;
    let value = v.get("value").and_then(|x| x.as_u64()).unwrap_or(0);
    let op = match v.get("op").and_then(|x| x.as_str()).unwrap_or("add") {
        "add" | "inc" => ApplyOp::AddToSlot { slot },
        "sub" | "dec" => ApplyOp::SubFromSlot { slot },
        "set" => ApplyOp::SetSlot { slot, value },
        // `slot := max(arg, 0)` — the fire's arg IS the new value (the tracking write
        // verb the Pulse→Signals weld fires to mirror a live World reading into a card).
        "track" | "setFromArg" => ApplyOp::SetSlotFromArg { slot },
        other => return Err(format!("unknown affordance op '{other}'")),
    };
    Ok(AffordanceSpec { name, required, op })
}

/// `__deos_editor_add_affordance(cardId, spec)` → 1 on a committed weld (the card gains
/// a new fireable affordance + a provenance receipt), -1 on refusal.
unsafe extern "C" fn native_editor_add_affordance(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let card_id = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let spec_json = if args.argc_ >= 2 {
        arg_string(&mut cx, args.get(1))
    } else {
        String::new()
    };
    let ok = CURRENT_EDITOR.with(|c| {
        let mut guard = c.borrow_mut();
        let editor = match guard.as_mut() {
            Some(e) => e,
            None => return false,
        };
        if !editor_card_matches(editor, &card_id) {
            return false;
        }
        let spec = match parse_affordance_spec(&spec_json) {
            Ok(s) => s,
            Err(_) => return false,
        };
        match editor.add_affordance(spec) {
            Ok(_receipt) => true,
            Err(EditError::Unauthorized) => false,
            Err(e) => {
                record_error(format!("editor.addAffordance: {e}"));
                false
            }
        }
    });
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

// ── THE PRIVATE-SERVER natives (`deos.server.*`) — the deos-host surface ────────────
//
// A hosted userspace program registers cap-gated affordances (carrying ARBITRARY
// effects) into the thread-local SERVER_REGISTRY (the host drains it after setup), and
// wields the GM superpowers (`spawnCell` / `grant`) as real verified turns committed
// through the attached live World.

/// Decode one effect descriptor (`{type, ...}`) from the `defineAffordance` spec into a
/// real [`Effect`]. Supports the spike's shapes: `setField` and `incrementNonce`.
fn parse_effect_descriptor(v: &serde_json::Value) -> Result<dregg_turn::action::Effect, String> {
    use dregg_turn::action::Effect;
    let ty = v.get("type").and_then(|x| x.as_str()).unwrap_or("");
    let cell_hex = v.get("cell").and_then(|x| x.as_str()).unwrap_or("");
    let cell = reflect_binding::parse_cell_id(cell_hex)
        .ok_or_else(|| format!("effect '{ty}': bad cell id '{cell_hex}'"))?;
    match ty {
        "setField" => {
            let index = v.get("index").and_then(|x| x.as_u64()).unwrap_or(0) as usize;
            let value = v.get("value").and_then(|x| x.as_u64()).unwrap_or(0);
            Ok(Effect::SetField {
                cell,
                index,
                value: crate::applet::pack_u64(value),
            })
        }
        "incrementNonce" => Ok(Effect::IncrementNonce { cell }),
        other => Err(format!("unknown effect type '{other}'")),
    }
}

/// `__deos_server_define_affordance(specJson)` — register a cap-gated affordance carrying
/// arbitrary effects into the server registry. Returns 1 on register, -1 on a bad spec.
unsafe extern "C" fn native_server_define_affordance(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let spec_json = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let parsed = (|| -> Result<ServerAffordanceDef, String> {
        let v: serde_json::Value =
            serde_json::from_str(&spec_json).map_err(|e| format!("defineAffordance JSON: {e}"))?;
        let name = v
            .get("name")
            .and_then(|x| x.as_str())
            .unwrap_or("")
            .to_string();
        if name.is_empty() {
            return Err("defineAffordance needs a name".into());
        }
        let required =
            parse_auth_label(v.get("required").and_then(|x| x.as_str()).unwrap_or("none"));
        let effects = match v.get("effects").and_then(|x| x.as_array()) {
            Some(arr) => arr
                .iter()
                .map(parse_effect_descriptor)
                .collect::<Result<Vec<_>, _>>()?,
            None => Vec::new(),
        };
        // Optional `instance`: scope this affordance to a forked instance (a cell hex
        // `fork()` returned). A present-but-malformed instance hex is a hard error (the
        // program meant to scope it but named no valid cell).
        let instance = match v.get("instance").and_then(|x| x.as_str()) {
            Some(hex) if !hex.trim().is_empty() => Some(
                reflect_binding::parse_cell_id(hex)
                    .ok_or_else(|| format!("defineAffordance: bad instance cell '{hex}'"))?,
            ),
            _ => None,
        };
        Ok(ServerAffordanceDef {
            name,
            required,
            effects,
            instance,
        })
    })();
    let ok = match parsed {
        Ok(def) => {
            SERVER_REGISTRY.with(|r| r.borrow_mut().push(def));
            true
        }
        Err(e) => {
            record_error(format!("server.defineAffordance: {e}"));
            false
        }
    };
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// `__deos_server_fork(seedLabel)` — INSTANCE the server's world: mint a fresh OPEN
/// instance cell through the attached host (the SAME open-perms mint `spawnCell` uses)
/// and record it in the fork registry. Returns the instance cell id hex (the discovery
/// key clients connect to), or `""` on refusal. A cap-bounded fork for a party/session
/// (the membrane-fork): affordances scoped to it (`defineAffordance({…, instance})`)
/// publish as the fork's OWN surface, isolated from the root + sibling instances.
unsafe extern "C" fn native_server_fork(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let seed = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    if seed.trim().is_empty() {
        record_error("server.fork: a seed label is required".into());
        return return_string(&mut cx, &args, "");
    }

    // A funding stipend so the instance can pay its own self-stamp turns' computron fees
    // (the same sizing `spawnCell`'s OPEN path uses).
    const FORK_FUNDING: u64 = 100_000;

    let id_hex = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        let target = match guard.as_mut() {
            Some(t) => t,
            None => {
                record_error("server.fork: no attached World".into());
                return String::new();
            }
        };
        match target.mint_open_cell(&seed, FORK_FUNDING) {
            Ok(id) => {
                FORK_REGISTRY.with(|r| {
                    r.borrow_mut().push(ServerFork {
                        seed: seed.clone(),
                        cell: id,
                    })
                });
                reflect_binding::id_hex(&id)
            }
            Err(e) => {
                record_error(format!("server.fork: {e}"));
                String::new()
            }
        }
    });
    return_string(&mut cx, &args, &id_hex)
}

/// `__deos_server_spawn_cell(seedHex, perms)` — GM superpower: mint a fresh cell via a
/// real `CreateCell` verified turn through the attached World. Returns the new cell id
/// hex (its deterministic derivation), or `""` on refusal.
///
/// When `perms == "open"` (the default), the cell is minted OPEN + funded directly on the
/// host ledger (the GM superpower [`WorldSink::mint_open_cell`]): every action
/// `AuthRequired::None`, with a funding stipend. An open, funded cell can then (a) be
/// self-stamped by the GM's `setField` superpower and (b) be written cross-cell by a
/// player holding a granted cap — the two motions the living world needs (OPEN is
/// load-bearing: the cell's pubkey is `hash(seed)`, not a signable Ed25519 key, so any
/// signature-gated write would be unreachable). A non-"open" spawn instead commits a bare
/// `CreateCell` verified turn, leaving the cell at the default user permissions
/// (unreachable by a player without further grants).
unsafe extern "C" fn native_server_spawn_cell(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let seed_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let perms = if args.argc_ >= 2 {
        arg_string(&mut cx, args.get(1))
    } else {
        "open".into()
    };
    let open = perms.trim() == "open" || perms.trim().is_empty();

    let mut public_key = [0u8; 32];
    if !hex_decode_into(&seed_hex, &mut public_key) {
        public_key = *blake3::hash(seed_hex.as_bytes()).as_bytes();
    }
    let token_id = *blake3::hash(b"default").as_bytes();
    let new_id = dregg_types::CellId::derive_raw(&public_key, &token_id);

    // A funding stipend so an OPEN spawned cell can pay its own self-stamp turns'
    // computron fees. Sized to comfortably cover a handful of single-effect turns.
    const SPAWN_FUNDING: u64 = 100_000;

    let id_hex = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        let target = match guard.as_mut() {
            Some(t) => t,
            None => {
                record_error("server.spawnCell: no attached World".into());
                return String::new();
            }
        };
        if open {
            // OPEN spawn: the GM superpower — mint an open, funded world vessel through
            // the host. OPEN is required: the cell's pubkey (hash(seed)) is not a signable
            // Ed25519 key, so the GM's later self-stamps + a player's cap-bounded writes
            // can only authorize if the cell needs NO signature (`set_state: None`).
            match target.mint_open_cell(&seed_hex, SPAWN_FUNDING) {
                Ok(id) => reflect_binding::id_hex(&id),
                Err(e) => {
                    record_error(format!("server.spawnCell: {e}"));
                    String::new()
                }
            }
        } else {
            // Non-open spawn: a bare `CreateCell` verified turn as the GM agent (the cell
            // keeps default user permissions — unreachable by a player without grants).
            let create = dregg_turn::action::Effect::CreateCell {
                public_key,
                token_id,
                balance: 0,
            };
            match target.fire_raw_effects("spawnCell", vec![create]) {
                Ok(_rh) => reflect_binding::id_hex(&new_id),
                Err(e) => {
                    record_error(format!("server.spawnCell: {e}"));
                    String::new()
                }
            }
        }
    });
    return_string(&mut cx, &args, &id_hex)
}

/// `__deos_server_grant(toHex, onHex, required)` — GM superpower: grant a capability over
/// `on` to `to` via a real `GrantCapability` verified turn. Returns 1 on commit, -1 on
/// refusal.
unsafe extern "C" fn native_server_grant(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let to_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let on_hex = if args.argc_ >= 2 {
        arg_string(&mut cx, args.get(1))
    } else {
        String::new()
    };
    let req_label = if args.argc_ >= 3 {
        arg_string(&mut cx, args.get(2))
    } else {
        "signature".into()
    };
    let ok = (|| -> bool {
        let to = match reflect_binding::parse_cell_id(&to_hex) {
            Some(c) => c,
            None => return false,
        };
        let on = match reflect_binding::parse_cell_id(&on_hex) {
            Some(c) => c,
            None => return false,
        };
        let cap = dregg_cell::CapabilityRef {
            target: on,
            slot: 0,
            permissions: parse_auth_label(&req_label),
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let effect = dregg_turn::action::Effect::GrantCapability { from: on, to, cap };
        CURRENT_APPLET.with(|c| {
            let mut guard = c.borrow_mut();
            match guard.as_mut() {
                // Commit the grant AS the `on` cell — a SELF-grant (from == actor ==
                // action target). GrantCapability's authority is checked against `on`'s
                // `delegate` permission; for an OPEN world cell (`delegate: None`) the
                // self-grant authorizes with no signature, which is essential because the
                // spawned cell's pubkey is not a signable Ed25519 key. (This mirrors the
                // deos-host spike's door self-grant.)
                Some(target) => match target.fire_raw_effects_as(on, "grant", vec![effect]) {
                    Ok(_rh) => true,
                    Err(e) => {
                        record_error(format!("server.grant: {e}"));
                        false
                    }
                },
                None => false,
            }
        })
    })();
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// `__deos_server_set_field(cellHex, index, value)` — GM superpower: commit a `SetField`
/// NOW on a cell the GM governs (a real verified turn committed AS that cell through the
/// attached World). The GM uses this to stamp spawned cells' stats, fire NPC reactions,
/// and apply LEVEL-UPs. Returns 1 on commit, -1 on refusal.
unsafe extern "C" fn native_server_set_field(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let cell_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let index = if args.argc_ >= 2 {
        arg_i32(args.get(1)).max(0) as usize
    } else {
        0
    };
    let value = if args.argc_ >= 3 {
        arg_i32(args.get(2)).max(0) as u64
    } else {
        0
    };
    let ok = (|| -> bool {
        let cell = match reflect_binding::parse_cell_id(&cell_hex) {
            Some(c) => c,
            None => return false,
        };
        let effect = dregg_turn::action::Effect::SetField {
            cell,
            index,
            value: crate::applet::pack_u64(value),
        };
        // Commit AS the governed cell (the GM acting on a cell of its own world — the
        // executor's authority gate is the binding check; the open-perms cells the GM
        // spawned admit the self-write).
        CURRENT_APPLET.with(|c| {
            let mut guard = c.borrow_mut();
            match guard.as_mut() {
                Some(target) => match target.fire_raw_effects_as(cell, "setField", vec![effect]) {
                    Ok(_rh) => true,
                    Err(e) => {
                        record_error(format!("server.setField: {e}"));
                        false
                    }
                },
                None => false,
            }
        })
    })();
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// `__deos_server_get_field(cellHex, index)` — read a u64 field off the live ledger (the
/// GM observing a player's character — e.g. its XP). Returns the value as an i32, or -1 if
/// the cell/field is absent.
unsafe extern "C" fn native_server_get_field(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let cell_hex = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let index = if args.argc_ >= 2 {
        arg_i32(args.get(1)).max(0) as usize
    } else {
        0
    };
    let v = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return -1i32,
        };
        let cell = match reflect_binding::parse_cell_id(&cell_hex) {
            Some(c) => c,
            None => return -1i32,
        };
        let mut out = -1i32;
        applet.with_ledger(&mut |l| {
            if let Some(cell_ref) = l.get(&cell) {
                if let Some(fe) = cell_ref.state.get_field(index) {
                    let mut b = [0u8; 8];
                    b.copy_from_slice(&fe[..8]);
                    out = u64::from_le_bytes(b) as i32;
                }
            }
        });
        out
    });
    args.rval().set(Int32Value(v));
    true
}

// ── THE BOUNDED MULTI-CELL COMPOSE native (`deos.compose`) ──────────────────────────
//
// The agent's brain composes a story spanning MULTIPLE cells (mint + setField + grant) as
// ONE all-or-nothing bounded gesture on the live World. The cap tooth (`held`) + scope
// tooth + atomic pre-screen live in `AttachedComposer::compose` (the lifted
// `multi_cell::MultiCellAuthor` semantics); this native is the JSON↔composer bridge.

/// Decode one compose leg (`{op, ...}`) from the brain's JSON into a [`ComposeStep`].
fn parse_compose_step(v: &serde_json::Value) -> Result<ComposeStep, String> {
    let op = v.get("op").and_then(|x| x.as_str()).unwrap_or("");
    let required = parse_auth_label(
        v.get("required")
            .and_then(|x| x.as_str())
            .unwrap_or("signature"),
    );
    match op {
        "mintCard" => {
            let seed = v
                .get("seed")
                .and_then(|x| x.as_str())
                .ok_or("mintCard needs a 'seed' label")?
                .to_string();
            let funding = v.get("funding").and_then(|x| x.as_u64()).unwrap_or(100_000);
            let seed_fields = match v.get("fields").and_then(|x| x.as_array()) {
                Some(arr) => arr
                    .iter()
                    .map(|pair| {
                        let p = pair
                            .as_array()
                            .ok_or("mintCard field must be a [slot, value] pair")?;
                        let slot = p.first().and_then(|x| x.as_u64()).unwrap_or(0) as usize;
                        let value = p.get(1).and_then(|x| x.as_u64()).unwrap_or(0);
                        Ok::<_, String>((slot, crate::applet::pack_u64(value)))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                None => Vec::new(),
            };
            Ok(ComposeStep::MintCard {
                seed,
                seed_fields,
                funding,
                required,
            })
        }
        "setField" => {
            let cell_hex = v.get("cell").and_then(|x| x.as_str()).unwrap_or("");
            let cell = reflect_binding::parse_cell_id(cell_hex)
                .ok_or_else(|| format!("setField: bad cell id '{cell_hex}'"))?;
            let slot = v.get("slot").and_then(|x| x.as_u64()).unwrap_or(0) as usize;
            let value = v.get("value").and_then(|x| x.as_u64()).unwrap_or(0);
            Ok(ComposeStep::SetField {
                cell,
                slot,
                value,
                required,
            })
        }
        "grant" => {
            let from_hex = v.get("from").and_then(|x| x.as_str()).unwrap_or("");
            let from = reflect_binding::parse_cell_id(from_hex)
                .ok_or_else(|| format!("grant: bad 'from' cell id '{from_hex}'"))?;
            let to_hex = v.get("to").and_then(|x| x.as_str()).unwrap_or("");
            let to = reflect_binding::parse_cell_id(to_hex)
                .ok_or_else(|| format!("grant: bad 'to' cell id '{to_hex}'"))?;
            let granted = parse_auth_label(
                v.get("granted")
                    .and_then(|x| x.as_str())
                    .unwrap_or("signature"),
            );
            Ok(ComposeStep::GrantCap {
                from,
                to,
                granted,
                required,
            })
        }
        other => Err(format!("unknown compose op '{other}'")),
    }
}

/// Serialize a [`ComposeOutcome`] into the JSON shape `deos.compose` hands back to JS:
/// `{ ok, committed, receipts:[hex], minted:[hex], refusal? }`.
fn compose_outcome_json(out: &ComposeOutcome) -> String {
    let receipts: Vec<String> = out
        .receipts
        .iter()
        .map(|h| deos_reflect::substance::hex_encode(h))
        .collect();
    let minted: Vec<String> = out.minted.iter().map(reflect_binding::id_hex).collect();
    serde_json::json!({
        "ok": out.ok(),
        "committed": out.committed,
        "receipts": receipts,
        "minted": minted,
        "refusal": out.refusal,
    })
    .to_string()
}

/// `__deos_compose(stepsJson)` — run the agent's bounded multi-cell story on the live World.
/// Drives the installed [`AttachedComposer`] (mounted under the agent's `held`): the atomic
/// pre-screen refuses any over-reach IN-BAND (nothing committed); a fully-authorized story
/// commits each leg as a verified turn on the live ledger. Returns the outcome JSON string;
/// also stashed in `LAST_COMPOSE` for the host. A malformed steps blob is a refusal.
unsafe extern "C" fn native_compose(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let steps_json = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        "[]".into()
    };

    let outcome = CURRENT_COMPOSER.with(|c| {
        let mut guard = c.borrow_mut();
        let composer = match guard.as_mut() {
            Some(c) => c,
            None => {
                return ComposeOutcome {
                    refusal: Some("no composer attached (deos.compose needs a live World)".into()),
                    ..Default::default()
                };
            }
        };
        // Parse the legs. A malformed leg (bad op/cell/shape) is a hard refusal BEFORE any
        // turn — the brain produced an ill-formed story.
        let parsed: Result<Vec<ComposeStep>, String> = (|| {
            let v: serde_json::Value =
                serde_json::from_str(&steps_json).map_err(|e| format!("compose JSON: {e}"))?;
            let arr = v.as_array().ok_or("compose expects an array of legs")?;
            arr.iter().map(parse_compose_step).collect()
        })();
        let steps = match parsed {
            Ok(s) => s,
            Err(e) => {
                return ComposeOutcome {
                    refusal: Some(e),
                    ..Default::default()
                };
            }
        };
        match composer.compose(steps) {
            Ok(comp) => ComposeOutcome {
                receipts: comp.receipts.clone(),
                minted: comp.minted.clone(),
                committed: comp.receipts.len(),
                refusal: None,
            },
            Err(ComposeError::OverReach { reason, .. }) => ComposeOutcome {
                // The atomic pre-screen aborted — NOTHING committed (no partial leg).
                refusal: Some(format!("over-reach: {reason}")),
                ..Default::default()
            },
            Err(ComposeError::Executor { step, reason }) => {
                // Legs BEFORE this one committed on the live ledger (step-wise commit).
                let committed = composer.receipt_count();
                ComposeOutcome {
                    receipts: composer.receipts().to_vec(),
                    committed,
                    refusal: Some(format!("executor refused leg {step}: {reason}")),
                    ..Default::default()
                }
            }
        }
    });

    let json = compose_outcome_json(&outcome);
    LAST_COMPOSE.with(|c| *c.borrow_mut() = Some(outcome));
    return_string(&mut cx, &args, &json)
}

/// Decode 64-char hex into `out` (exact-length match required). Returns false on any
/// non-hex char or a length mismatch.
fn hex_decode_into(s: &str, out: &mut [u8; 32]) -> bool {
    let s = s.trim();
    if s.len() != 64 {
        return false;
    }
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = match u8::from_str_radix(&s[i * 2..i * 2 + 1], 16) {
            Ok(v) => v,
            Err(_) => return false,
        };
        let lo = match u8::from_str_radix(&s[i * 2 + 1..i * 2 + 2], 16) {
            Ok(v) => v,
            Err(_) => return false,
        };
        *byte = (hi << 4) | lo;
    }
    true
}
