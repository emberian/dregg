//! The **renderer** — walk a deos-js view-tree into REAL gpui-component widgets.
//!
//! The vocabulary is gpui-component (the longbridge widget fork the cockpit uses):
//!
//!   - `vstack` → [`gpui_component::v_flex`]   `row` → [`gpui_component::h_flex`]
//!   - `text`   → [`gpui_component::label::Label`]
//!   - `bind`   → a [`Label`] re-read off the live applet ledger (the signal binding)
//!   - `button` → [`gpui_component::button::Button`] whose `on_click` fires the
//!     applet's affordance = a REAL cap-gated verified turn (a `TurnReceipt`)
//!   - `input`  → a bordered field showing the ephemeral view-state value (see the
//!     NATIVE/WEB PARITY note below — display-only on native, editable `<input>` on web)
//!   - `list` / `table` → a `v_flex` of the child nodes
//!
//! The same vocabulary renders the moldable `present()` faces ([`crate::faces`]) — the
//! §7 unification (the inspector and the custom view share widgets).
//!
//! NATIVE/WEB PARITY — one honest exception. The view-tree is renderer-independent
//! DATA and every node paints on both faces, but `input` is not yet INTERACTIVE on
//! native: there is NO text-entry widget in this crate, so a native `input` renders a
//! READ-ONLY [`Label`] (a user cannot type), while the `web` renderer emits a real
//! editable `<input>` read live on submit. A native `input` therefore reflects only
//! draft text a JS/agent path seeded via `set_view`, and an unseeded submit fires
//! `arg = 0`. Wiring gpui's `InputState`/`TextInput` (persistent per-field state +
//! focus) closes it; until then treat native `input` as display/agent-driven, not
//! user-editable. (Audit finding #17 — the honest boundary, stated at the node.)
//!
//! INVALIDATION — the **fine-grained signal hook** (the SolidJS-shaped re-render).
//!
//! The renderer welds [`deos_js::signals::BindingRegistry`] into the render path:
//!
//!   - At construction the tree is walked ONCE ([`bind_plan`]) and every `bind` node is
//!     assigned a monotonic [`BindingId`] + `register`ed on its `(cell, slot)` source in
//!     the registry. (The applet's cell is the sovereignty boundary, so every bind reads
//!     `(applet.cell(), slot)`.)
//!   - Each bind's live value is held in a small per-binding **value cache**. A `bind`
//!     node renders out of the cache — NOT a fresh `get_u64` every paint.
//!   - On a committed turn the caller folds the turn's touched `(cell, slot)`s through
//!     [`AppletView::on_committed_turn`] (the self-cell sugar) or the general
//!     [`AppletView::on_world_events`] (events naming ANY cell — THE PULSE→SIGNALS WELD:
//!     the cockpit's dynamics pump projects each `WorldEvent::FieldSet { cell, index }`
//!     straight into the registry): [`BindingRegistry::invalidate_all`] returns EXACTLY
//!     the dirty bindings, and only those re-read the live ledger into the cache. Clean
//!     bindings keep their cached value untouched — a turn on slot A re-evaluates
//!     binding A and leaves binding B alone (the fine-grained win). An event naming a
//!     cell no bind reads dirties nothing (a foreign World write never over-invalidates).
//!   - Events that name a CELL but no slot (`WorldEvent::CellMutated` — the generic
//!     "this cell changed" tooth — and `WorldEvent::CapabilityRevoked`) fold through
//!     [`AppletView::on_world_cells`]: the registry's conservative `invalidate_cell`
//!     re-reads every binding of the touched cell (never under-invalidating), and a
//!     cell no bind reads still dirties nothing.
//!
//! The first paint is still immediate-mode (the cache fills lazily from the live ledger
//! the first time each bind renders), so an un-driven view is always correct; the
//! felt-liveness is the INCREMENTAL update path the committed turn drives. A bind whose
//! value did not change re-reads nothing; the [`AppletView::last_dirty`] instrumentation
//! exposes exactly which bindings the last turn re-evaluated (the test bar).
//!
//! THE DIRTY GLOW — liveness FELT, not just correct: every binding an invalidation
//! re-evaluates joins a per-beat glow set ([`AppletView::glowing`]) and its label paints
//! in the accent tint until the host's next pulse beat [`AppletView::fade_glow`]s it —
//! a foreign turn visibly *touches* exactly the rows it moved.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use deos_js::applet::Applet;
use deos_js::signals::{BindingId, BindingRegistry, Slot, SourceEvent};
use dregg_types::CellId;
use gpui::{
    div, px, rgb, App, ClickEvent, Context, FontWeight, InteractiveElement, IntoElement,
    MouseButton, ParentElement, Render, SharedString, Styled, Window,
};
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};

use crate::tree::ViewNode;

/// A shared, interior-mutable handle on the live applet. The renderer reads the model
/// through it (the `bind` re-read) and a button's `on_click` fires a turn through it
/// (a real verified turn). One handle, shared by every widget — the single sovereign
/// cell behind the whole applet view.
pub type SharedApplet = Rc<RefCell<Applet>>;

/// The slot a `bind` node reads, in tree-walk (pre-order) appearance — the renderer
/// mints one [`BindingId`] per `bind` node monotonically, paired with the model `Slot`
/// the node re-reads. The cell is constant (the applet's sovereign cell), so the source
/// each binding registers is `(applet.cell(), slot)`.
fn bind_plan(tree: &ViewNode, out: &mut Vec<Slot>) {
    match tree {
        ViewNode::Bind { slot, .. } => out.push(*slot),
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                bind_plan(c, out);
            }
        }
        // The richness-expansion containers recurse their children in declaration order so
        // the Nth `Bind` stays `BindingId(n)`. `tabs` registers EVERY panel's binds (render
        // walks all panels too, displaying only the selected one) so the cursor never
        // desyncs on a tab switch.
        ViewNode::Section { children, .. } => {
            for c in children {
                bind_plan(c, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                bind_plan(p, out);
            }
        }
        // `grid` recurses its children in declaration order (same as the other containers).
        ViewNode::Grid { children, .. } => {
            for c in children {
                bind_plan(c, out);
            }
        }
        // The adept-only wrapper is transparent to the bind cursor — recurse the wrapped node.
        // (A tree handed to a renderer has usually been `disclose`d, which removes the marker;
        // an un-disclosed tree still registers the inner node's binds here.)
        ViewNode::Adept(inner) => bind_plan(inner, out),
        // A `host`'s resolved hosted subtree is recursed at the host's position so the bind
        // cursor stays aligned across all renderers; an unresolved host (`view: None`)
        // consumes no cursor positions (so it can't desync them).
        ViewNode::Host { view, .. } => {
            if let Some(v) = view {
                bind_plan(v, out);
            }
        }
        // Leaves that hold no bind source. The bound batch-2 nodes (`slider`/`toggle`/`gauge`)
        // read their slot immediate-mode (NOT via the bind cursor), so they register nothing.
        ViewNode::Text(_)
        | ViewNode::Button { .. }
        | ViewNode::Input { .. }
        | ViewNode::Gauge { .. }
        | ViewNode::Divider
        | ViewNode::Breadcrumb { .. }
        | ViewNode::Progress { .. }
        | ViewNode::Pill { .. }
        | ViewNode::Icon { .. }
        | ViewNode::Menu { .. }
        | ViewNode::Halo { .. }
        | ViewNode::Slider { .. }
        | ViewNode::Toggle { .. }
        | ViewNode::Tile { .. } => {}
    }
}

/// The gpui view that renders a deos-js applet's view-tree. A real gpui `Render`
/// entity — open it in a (headless or windowed) window and it paints the widgets.
///
/// FINE-GRAINED LIVENESS: the view owns a [`BindingRegistry`] (deos-js's reverse index
/// `(cell, slot) → bindings`) and a per-binding **value cache**. A `bind` renders out of
/// the cache; a committed turn invalidates ONLY the touched `(cell, slot)`'s bindings
/// (via [`AppletView::on_committed_turn`]) and re-reads only those into the cache.
pub struct AppletView {
    /// The live applet (shared so button handlers can fire turns + binds can re-read).
    applet: SharedApplet,
    /// The extracted view-tree (the real `deos.ui.*` element-tree).
    tree: ViewNode,
    /// The applet's sovereign cell — the constant cell every bind reads a slot of.
    cell: CellId,
    /// The reverse index `(cell, slot) → bindings`. Built once at construction by
    /// registering each `bind` node (in tree-walk order) on its source. OWNED here; the
    /// model lives in deos-js (`signals.rs`) — this is the renderer consuming it.
    registry: BindingRegistry,
    /// The Nth `bind` node (tree-walk order) is `BindingId(n)` reading slot `bind_slots[n]`.
    /// Render walks the tree in the same order and consumes ids from a counter so each
    /// `bind` paints out of `cache[BindingId(n)]`.
    bind_slots: Vec<Slot>,
    /// The fine-grained value cache: `binding → last-read live value`. A `bind` paints
    /// from here; only `invalidate`d bindings re-read (the rest keep their cached value).
    /// `RefCell` because `render`/`node` take `&self` but lazily fill the cache on first
    /// paint of each binding.
    cache: RefCell<BTreeMap<BindingId, u64>>,
    /// The id-counter render uses to map the Nth painted `bind` node to `BindingId(n)`.
    /// Reset at the top of each `render`. `Cell` for the same `&self`-walk reason.
    render_cursor: Cell<u64>,
    /// Instrumentation: the bindings the LAST invalidation call re-evaluated (the
    /// dirty set). Empty until a turn drives the view. The test bar reads this to prove
    /// a turn on slot A dirtied ONLY binding A.
    last_dirty: RefCell<Vec<BindingId>>,
    /// THE DIRTY GLOW — the bindings invalidated since the host's last pulse beat.
    /// Unlike `last_dirty` (replaced per call, the per-turn test bar) this is the
    /// per-BEAT union: every invalidation inserts, and only [`Self::fade_glow`]
    /// (called at the top of the host's next beat) clears. A glowing bind's label
    /// paints in the accent tint, so a foreign turn is FELT on exactly the rows it
    /// moved for one beat.
    glow: RefCell<BTreeSet<BindingId>>,
    /// The applet's audit-tape watermark — how many of the applet's OWN committed
    /// receipts the view has accounted for. A turn fired on this very surface (a
    /// rendered button's `on_click`) commits on the applet's EMBEDDED executor, whose
    /// receipts are NOT projected into any dynamics stream — so the host's pulse calls
    /// [`Self::catch_up_own_turns`] each beat, which compares the live tape length
    /// against this watermark and (conservatively) invalidates the whole cell's
    /// bindings when it moved.
    receipts_seen: Cell<usize>,
}

impl AppletView {
    /// Build a view from a shared applet + its view-tree, registering every `bind` node
    /// on its `(cell, slot)` source in the signal registry (the fine-grained index).
    pub fn new(applet: SharedApplet, tree: ViewNode) -> Self {
        let (cell, receipts_seen) = {
            let a = applet.borrow();
            (a.cell(), a.receipt_count())
        };
        let mut bind_slots = Vec::new();
        bind_plan(&tree, &mut bind_slots);

        let mut registry = BindingRegistry::new();
        for (n, slot) in bind_slots.iter().enumerate() {
            registry.register(BindingId(n as u64), cell, *slot);
        }

        Self {
            applet,
            tree,
            cell,
            registry,
            bind_slots,
            cache: RefCell::new(BTreeMap::new()),
            render_cursor: Cell::new(0),
            last_dirty: RefCell::new(Vec::new()),
            glow: RefCell::new(BTreeSet::new()),
            receipts_seen: Cell::new(receipts_seen),
        }
    }

    /// The shared applet handle (for the caller to inspect receipts after a turn).
    pub fn applet(&self) -> SharedApplet {
        self.applet.clone()
    }

    /// The view-tree this surface currently paints (read-only) — the REFLECT-ON half:
    /// a host (or a confined agent reading through it) reads the live surface's own
    /// view-tree before rewriting it.
    pub fn tree(&self) -> &ViewNode {
        &self.tree
    }

    /// **Swap the painted view-tree — the REWRITE half (the view is data, not code).**
    /// After an authoring gesture re-folds the card's view-source (e.g. a
    /// [`deos-js` `CardEditor`] view-patch), the host hands the re-parsed [`ViewNode`]
    /// here and the next paint draws the reshaped surface. The binding plan is rebuilt
    /// from the new tree (so a `bind` added/removed by the rewrite re-registers) and the
    /// value cache is cleared (each `bind` re-reads its live slot on the next paint). The
    /// live applet — the substance binds read and buttons fire against — is untouched;
    /// only the view changed.
    pub fn set_tree(&mut self, tree: ViewNode) {
        let mut bind_slots = Vec::new();
        bind_plan(&tree, &mut bind_slots);

        let mut registry = BindingRegistry::new();
        for (n, slot) in bind_slots.iter().enumerate() {
            registry.register(BindingId(n as u64), self.cell, *slot);
        }

        self.tree = tree;
        self.registry = registry;
        self.bind_slots = bind_slots;
        self.cache = RefCell::new(BTreeMap::new());
        self.render_cursor = Cell::new(0);
        self.last_dirty = RefCell::new(Vec::new());
        self.glow = RefCell::new(BTreeSet::new());
        // The receipts watermark survives a tree swap — the applet (and its audit tape)
        // is untouched by a rewrite; only the view changed.
    }

    /// **THE GENERAL FINE-GRAINED HOOK — the Pulse→Signals weld's entry point.** Fold
    /// world events (each a `(cell, slot)` write, ANY cell) through the registry and
    /// re-read ONLY the dirty bindings into the cache.
    ///
    /// `touched` is what the cockpit's dynamics pump projects each
    /// `WorldEvent::FieldSet { cell, index }` into (the [`SourceEvent`] shape, see
    /// `deos_js::signals`). The registry is keyed `(cell, slot)`, so an event naming a
    /// FOREIGN cell (one this view's binds never read) dirties nothing — the pump can
    /// broadcast one beat's events to every open card and only the cards actually bound
    /// to the touched sources repaint. Returns the dirty set — exactly the bindings
    /// whose painted value may have changed; those also join the [`Self::glowing`] set
    /// until the host's next [`Self::fade_glow`] beat.
    pub fn on_world_events(&self, touched: &[(CellId, Slot)]) -> Vec<BindingId> {
        let dirty = self
            .registry
            .invalidate_all(touched.iter().map(|(c, s)| SourceEvent::new(*c, *s)));
        self.reread_dirty(&dirty);
        dirty
    }

    /// THE FINE-GRAINED HOOK, single-cell sugar — fold a committed turn's touched slots
    /// (of the applet's OWN sovereign cell) through the registry. Exactly
    /// [`Self::on_world_events`] with every event on `self.cell`; kept because the
    /// embedded single-custody applet's turns only ever write its own cell.
    pub fn on_committed_turn(&self, touched_slots: &[Slot]) -> Vec<BindingId> {
        let touched: Vec<(CellId, Slot)> = touched_slots.iter().map(|s| (self.cell, *s)).collect();
        self.on_world_events(&touched)
    }

    /// **THE CELL-WIDE INVALIDATION HOOK — the `CellMutated`/`CapabilityRevoked` feed.**
    /// Fold world events that name a whole CELL but no slot through the registry.
    ///
    /// A `WorldEvent::CellMutated` (nonce bump / sovereign flip / permissions or
    /// verification-key write / cap reshape — the generic "this cell changed" tooth)
    /// and a `WorldEvent::CapabilityRevoked` carry no `(cell, slot)` pair to
    /// invalidate on, so the registry's conservative
    /// [`BindingRegistry::invalidate_cell`] is the right tooth: EVERY binding reading
    /// ANY slot of a touched cell re-reads its live value (never under-invalidating —
    /// cache soundness = dynamics completeness), while a cell no bind of this view
    /// reads dirties nothing (a foreign mutation never over-invalidates — the pump can
    /// broadcast the beat's cell events to every open card, same as the FieldSet
    /// feed). Returns the dirty set; those bindings also join the glow until the
    /// host's next [`Self::fade_glow`] beat.
    pub fn on_world_cells(&self, cells: &[CellId]) -> Vec<BindingId> {
        let mut dirty: BTreeSet<BindingId> = BTreeSet::new();
        for c in cells {
            dirty.extend(self.registry.invalidate_cell(*c));
        }
        let dirty: Vec<BindingId> = dirty.into_iter().collect();
        self.reread_dirty(&dirty);
        dirty
    }

    /// **Catch up turns committed on the applet's OWN embedded executor** — the pulse's
    /// quiet-beat tooth. A button rendered by this very view fires [`Applet::fire`]
    /// directly (no dynamics stream names the touched slots), so the host's pulse calls
    /// this each beat: if the applet's audit tape grew past the watermark, every binding
    /// of the applet's cell is (conservatively) invalidated and re-read — the
    /// `CellMutated`-shaped tooth from `deos_js::signals`, never under-invalidating.
    /// Returns the dirty set (empty on a still tape — the common, free case).
    pub fn catch_up_own_turns(&self) -> Vec<BindingId> {
        let n = self.applet.borrow().receipt_count();
        if n == self.receipts_seen.replace(n) {
            return Vec::new();
        }
        let dirty = self.registry.invalidate_cell(self.cell);
        self.reread_dirty(&dirty);
        dirty
    }

    /// Mark the applet's current audit tape as accounted for WITHOUT invalidating —
    /// for a caller that just fired turns itself and already folded their exact
    /// touched slots through [`Self::on_world_events`] (the census weld does this),
    /// so the next [`Self::catch_up_own_turns`] doesn't re-invalidate the whole cell.
    pub fn mark_own_turns_seen(&self) {
        self.receipts_seen.set(self.applet.borrow().receipt_count());
    }

    /// Re-read ONLY the dirty bindings off the live ledger into the cache (the
    /// witnessed read the `bind` closure made) — clean bindings are untouched — then
    /// record them as the last dirty set and light their glow.
    fn reread_dirty(&self, dirty: &[BindingId]) {
        {
            let app = self.applet.borrow();
            let mut cache = self.cache.borrow_mut();
            for b in dirty {
                if let Some(v) = self.registry.reread(*b, |_cell, slot| app.get_u64(slot)) {
                    cache.insert(*b, v);
                }
            }
        }
        *self.last_dirty.borrow_mut() = dirty.to_vec();
        self.glow.borrow_mut().extend(dirty.iter().copied());
    }

    /// The bindings the last invalidation call ([`Self::on_committed_turn`] /
    /// [`Self::on_world_events`] / [`Self::catch_up_own_turns`]) re-evaluated
    /// (instrumentation / the test bar). Empty before any turn drove the view.
    pub fn last_dirty(&self) -> Vec<BindingId> {
        self.last_dirty.borrow().clone()
    }

    /// The bindings still wearing the dirty glow — the per-BEAT union of every dirty
    /// set since the last [`Self::fade_glow`], id-sorted. The bake bar reads this to
    /// prove ONE foreign turn lit EXACTLY one row.
    pub fn glowing(&self) -> Vec<BindingId> {
        self.glow.borrow().iter().copied().collect()
    }

    /// Retire the dirty glow (the host's pulse calls this at the top of each beat, so a
    /// glow lasts exactly one beat). Returns whether anything was glowing — the caller's
    /// cue that a repaint is needed to un-tint the rows.
    pub fn fade_glow(&self) -> bool {
        let mut g = self.glow.borrow_mut();
        let had = !g.is_empty();
        g.clear();
        had
    }

    /// The cached live value of a binding, if it has been read (lazily on first paint or
    /// by a committed-turn re-read). For tests / instrumentation.
    pub fn cached(&self, binding: BindingId) -> Option<u64> {
        self.cache.borrow().get(&binding).copied()
    }

    /// How many `bind` nodes the view registered (one [`BindingId`] each).
    pub fn binding_count(&self) -> usize {
        self.bind_slots.len()
    }

    /// The bindings whose registered source is `slot` of the applet's own cell — the
    /// EXPECTED dirty set for a write to that slot (instrumentation / the bake bar:
    /// "one foreign turn lit exactly this row" is checked against this).
    pub fn bindings_reading(&self, slot: Slot) -> Vec<BindingId> {
        self.bind_slots
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == slot)
            .map(|(n, _)| BindingId(n as u64))
            .collect()
    }

    /// The identity + value the next-painted `bind` node should show: its cached value,
    /// filling the cache lazily off the live ledger on first paint. Advances the render
    /// cursor so the Nth `bind` node maps to `BindingId(n)`. The id comes back too so
    /// the paint can check the dirty-glow set for this exact binding.
    fn next_bind_value(&self, slot: Slot) -> (BindingId, u64) {
        let n = self.render_cursor.get();
        self.render_cursor.set(n + 1);
        let id = BindingId(n);
        let mut cache = self.cache.borrow_mut();
        let value = *cache
            .entry(id)
            .or_insert_with(|| self.applet.borrow().get_u64(slot));
        (id, value)
    }

    /// Render one node into a gpui element. Recursive: containers render their
    /// children with the same vocabulary.
    fn node(&self, node: &ViewNode, _window: &mut Window, cx: &mut App) -> gpui::AnyElement {
        let theme_fg = cx.theme().foreground;
        match node {
            ViewNode::VStack(children) => {
                let mut col = v_flex().gap_2().p_3();
                for c in children {
                    col = col.child(self.node(c, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Row(children) => {
                let mut row = h_flex().gap_2().items_center();
                for c in children {
                    row = row.child(self.node(c, _window, cx));
                }
                row.into_any_element()
            }
            ViewNode::Text(s) => Label::new(s.clone())
                .text_color(theme_fg)
                .into_any_element(),
            ViewNode::Bind { slot, label, fmt } => {
                // THE SIGNAL BINDING — paint out of the fine-grained value CACHE. The
                // cache fills lazily off the live ledger on first paint (the same
                // witnessed read the JS closure made), then is updated ONLY for the
                // bindings a committed turn `invalidate`s (see `on_committed_turn`). A
                // clean binding repaints its cached value without re-reading the ledger —
                // the SolidJS-shaped fine-grained re-render.
                let (id, value) = self.next_bind_value(*slot);
                // CONSUMER-DELIGHT: an opaque key/hash paints SHORT + friendly (`🦊 swift-fox` /
                // `0x8bf3…a3d8` / `1,234,567`) instead of a 20-digit decimal; the default keeps
                // the plain decimal so a counter is unchanged. Identical across all renderers.
                let shown = crate::fmt::format_value(value, *fmt);
                let text = if label.is_empty() {
                    shown
                } else {
                    format!("{label}{shown}")
                };
                // THE DIRTY GLOW — a binding freshly invalidated this beat paints in the
                // accent tint (the same accent `tag_color` falls back to) until the
                // host's next pulse `fade_glow`s it: a foreign turn is FELT on exactly
                // the rows it moved, for exactly one beat.
                let color = if self.glow.borrow().contains(&id) {
                    tag_color("accent")
                } else {
                    theme_fg
                };
                Label::new(text)
                    .font_weight(FontWeight::BOLD)
                    .text_color(color)
                    .into_any_element()
            }
            ViewNode::Button { label, turn, arg } => {
                // THE REAL TURN — a button's onClick fires the applet's affordance =
                // ONE cap-gated verified turn (a `TurnReceipt`). The handler captures
                // the shared applet + the (turn, arg) from the view-tree.
                let applet = self.applet.clone();
                let turn = turn.clone();
                let arg = *arg;
                Button::new(("deos-aff", label_hash(label)))
                    .primary()
                    .label(label.clone())
                    .on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Fire the verified turn. A cap refusal / executor reject is
                        // surfaced to stderr (the screenshot stays honest); the model
                        // simply does not advance.
                        if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                            eprintln!("deos-view: affordance '{turn}' did not commit: {e}");
                        }
                    })
                    .into_any_element()
            }
            ViewNode::Input {
                bind_view,
                fire_turn,
                submit_label,
            } => {
                // The ephemeral view-state value (draft text) — NOT cell state. When `fire_turn`
                // is set, a paired submit button parses the draft into the turn's `arg` and fires
                // a REAL cap-gated verified turn (input → verified turn).
                //
                // NATIVE/WEB PARITY GAP (honest boundary): on NATIVE this renders a READ-ONLY
                // `Label` — there is no text-entry widget anywhere in deos-view, so a user cannot
                // type into it. `get_view(bind_view)` returns only whatever a JS/agent path wrote
                // via `set_view` (empty if nothing did), and on submit the arg is parsed from that
                // draft at RENDER time (`draft.trim().parse().unwrap_or(0)` below), so an unseeded
                // field fires `arg = 0`. On WEB the same node renders a real editable `<input>`
                // whose value is read LIVE on submit. So an authored transfer/URL/amount form is
                // user-interactive on web but display/agent-driven on native until a native
                // editable field (gpui `InputState`/`TextInput`) is wired. See the module doc.
                let draft = self
                    .applet
                    .borrow()
                    .get_view(bind_view)
                    .unwrap_or("")
                    .to_string();
                let field = h_flex()
                    .px_2()
                    .py_1()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .child(Label::new(if draft.is_empty() {
                        format!("‹{bind_view}›")
                    } else {
                        draft.clone()
                    }));
                if fire_turn.is_empty() {
                    return field.into_any_element();
                }
                // The submit affordance: parse the draft as the turn's arg (non-numeric → 0).
                let applet = self.applet.clone();
                let turn = fire_turn.clone();
                let draft_arg = draft.trim().parse::<i64>().unwrap_or(0);
                let label = if submit_label.is_empty() {
                    "submit".to_string()
                } else {
                    submit_label.clone()
                };
                h_flex()
                    .gap_1()
                    .items_center()
                    .child(field)
                    .child(
                        Button::new((
                            "deos-input-submit",
                            label_hash(&format!("{fire_turn}:{label}")),
                        ))
                        .primary()
                        .label(label)
                        .on_click(
                            move |_ev: &ClickEvent, _window, _cx| {
                                if let Err(e) = applet.borrow_mut().fire(&turn, draft_arg) {
                                    eprintln!(
                                        "deos-view: input submit '{turn}' did not commit: {e}"
                                    );
                                }
                            },
                        ),
                    )
                    .into_any_element()
            }
            ViewNode::List(items) => {
                let mut col = v_flex().gap_1();
                for it in items {
                    col = col.child(self.node(it, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Table(rows) => {
                let mut col = v_flex().gap_1().border_1().border_color(cx.theme().border);
                for r in rows {
                    col = col.child(self.node(r, _window, cx));
                }
                col.into_any_element()
            }

            // ── The RICHNESS EXPANSION (batch 1) ──────────────────────────────────────────
            ViewNode::Section {
                title,
                tag,
                children,
            } => {
                // A titled, bordered container — the uniform "styled section". `tag=="genuine"`
                // accents the border (the existing `props.tag` styling convention). Polished
                // toward a calmer, finished look: rounded corners + a touch more breathing room.
                let accent = if tag == "genuine" {
                    theme_fg
                } else {
                    cx.theme().border
                };
                let mut card = v_flex()
                    .gap_2()
                    .p_3()
                    .rounded(px(8.))
                    .border_1()
                    .border_color(accent);
                if !title.is_empty() {
                    // A quiet, slightly-muted header so it reads as a label, not a shout.
                    card = card.child(
                        Label::new(title.clone())
                            .font_weight(FontWeight::SEMIBOLD)
                            .text_color(cx.theme().muted_foreground),
                    );
                }
                for c in children {
                    card = card.child(self.node(c, _window, cx));
                }
                card.into_any_element()
            }
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                panels,
            } => {
                // The active tab index lives in a MODEL SLOT (read live), so a tab switch is a
                // verified turn — reflective + replayable, surviving an agent rewrite.
                let active = self.applet.borrow().get_u64(*selected_slot) as usize;
                // The tab strip: one Button per label, the active one `.primary()`; each fires
                // `select_turn` with `arg = its index` (a REAL cap-gated verified turn).
                let mut strip = h_flex().gap_1();
                for (i, label) in tabs.iter().enumerate() {
                    let applet = self.applet.clone();
                    let turn = select_turn.clone();
                    let idx = i as i64;
                    let mut b =
                        Button::new(("deos-tab", label_hash(&format!("{select_turn}:{i}"))))
                            .label(label.clone());
                    if i == active {
                        b = b.primary();
                    }
                    strip = strip.child(b.on_click(move |_ev: &ClickEvent, _window, _cx| {
                        if let Err(e) = applet.borrow_mut().fire(&turn, idx) {
                            eprintln!("deos-view: tab select '{turn}' did not commit: {e}");
                        }
                    }));
                }
                // Walk ALL panels (advancing the bind cursor in registration order) but keep
                // only the selected one's element — so a tab switch never desyncs the cursor.
                let shown = if active < panels.len() { active } else { 0 };
                let mut body = None;
                for (i, panel) in panels.iter().enumerate() {
                    let el = self.node(panel, _window, cx);
                    if i == shown {
                        body = Some(el);
                    }
                }
                let mut col = v_flex().gap_2().child(strip);
                if let Some(el) = body {
                    col = col.child(el);
                }
                col.into_any_element()
            }
            ViewNode::Gauge { slot, max, label } => {
                // A bound progress / balance bar — reads its slot IMMEDIATE-MODE (not the bind
                // cursor). The fill width is `value / max`, clamped to `[0,1]`.
                let value = self.applet.borrow().get_u64(*slot);
                let ratio = if *max == 0 {
                    0.0
                } else {
                    (value as f64 / *max as f64).clamp(0.0, 1.0)
                };
                let track_w = 140.0_f32;
                let fill_w = (track_w as f64 * ratio) as f32;
                let text = if label.is_empty() {
                    format!("{value}/{max}")
                } else {
                    format!("{label}{value}/{max}")
                };
                v_flex()
                    .gap_1()
                    .child(Label::new(text).text_color(theme_fg))
                    .child(
                        div()
                            .w(px(track_w))
                            .h(px(8.))
                            .rounded(px(4.))
                            .bg(cx.theme().border)
                            .child(
                                div()
                                    .w(px(fill_w.max(0.0)))
                                    .h(px(8.))
                                    .rounded(px(4.))
                                    .bg(theme_fg),
                            ),
                    )
                    .into_any_element()
            }
            ViewNode::Divider => div()
                .h(px(1.))
                .w_full()
                .bg(cx.theme().border)
                .into_any_element(),

            // ── The RICHNESS EXPANSION batch 2 — the actuation crown + the rest of §1 ─────────
            ViewNode::Grid { cols, children } => {
                // A wrapping spatial cell field (the Wonder grid / icon field / app tiles). A
                // flex with wrap; `cols` caps cell width so a row holds at most `cols` cells.
                let mut grid = div().flex().flex_wrap().gap_2();
                let max_w = if *cols > 0 {
                    Some(px(((520.0 / *cols as f32) - 12.0).max(48.0)))
                } else {
                    None
                };
                for c in children {
                    let mut cell = div().child(self.node(c, _window, cx));
                    if let Some(w) = max_w {
                        cell = cell.max_w(w);
                    }
                    grid = grid.child(cell);
                }
                grid.into_any_element()
            }
            ViewNode::Breadcrumb { items } => {
                // A navigation path joined by `→`; a crumb with a non-empty `turn` is clickable
                // (fires a verified turn). Mirrors Time's metastack breadcrumb.
                let mut row = h_flex().gap_1().items_center();
                for (i, crumb) in items.iter().enumerate() {
                    if i > 0 {
                        row = row.child(Label::new("→").text_color(cx.theme().muted_foreground));
                    }
                    if crumb.turn.is_empty() {
                        row = row.child(Label::new(crumb.label.clone()).text_color(theme_fg));
                    } else {
                        let applet = self.applet.clone();
                        let turn = crumb.turn.clone();
                        let arg = crumb.arg;
                        row = row.child(
                            Button::new((
                                "deos-crumb",
                                label_hash(&format!("{}:{}", crumb.turn, i)),
                            ))
                            .label(crumb.label.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                        eprintln!(
                                            "deos-view: breadcrumb '{turn}' did not commit: {e}"
                                        );
                                    }
                                },
                            ),
                        );
                    }
                }
                row.into_any_element()
            }
            ViewNode::Progress { value, max, label } => {
                // A STATIC (literal-valued) progress bar — same paint as `gauge` with a literal
                // value instead of a slot.
                let ratio = if *max == 0 {
                    0.0
                } else {
                    (*value as f64 / *max as f64).clamp(0.0, 1.0)
                };
                let track_w = 140.0_f32;
                let fill_w = (track_w as f64 * ratio) as f32;
                let text = if label.is_empty() {
                    format!("{value}/{max}")
                } else {
                    format!("{label}{value}/{max}")
                };
                v_flex()
                    .gap_1()
                    .child(Label::new(text).text_color(theme_fg))
                    .child(
                        div()
                            .w(px(track_w))
                            .h(px(8.))
                            .rounded(px(4.))
                            .bg(cx.theme().border)
                            .child(
                                div()
                                    .w(px(fill_w.max(0.0)))
                                    .h(px(8.))
                                    .rounded(px(4.))
                                    .bg(theme_fg),
                            ),
                    )
                    .into_any_element()
            }
            ViewNode::Pill {
                text,
                tag,
                slot,
                cases,
            } => {
                // A colored status badge. LIVE variant: when bound to a `slot` with `cases`, read
                // the slot IMMEDIATE-MODE and map the live value to its word + color (a phase slot
                // → COMMIT/REVEAL/RESOLVED) — the status pill READS the cell, not a frozen label.
                let (shown_text, shown_tag) = if let Some(s) = slot {
                    if cases.is_empty() {
                        (text.as_str(), tag.as_str())
                    } else {
                        let value = self.applet.borrow().get_u64(*s);
                        crate::tree::pill_display(text, tag, cases, value)
                    }
                } else {
                    (text.as_str(), tag.as_str())
                };
                div()
                    .px_2()
                    .py_0p5()
                    .rounded(px(999.))
                    .bg(tag_color(shown_tag))
                    .child(Label::new(shown_text.to_string()).text_color(rgb(0xffffff)))
                    .into_any_element()
            }
            ViewNode::Icon { glyph, tag } => {
                let color = if tag.is_empty() {
                    theme_fg
                } else {
                    tag_color(tag)
                };
                Label::new(glyph.clone())
                    .text_color(color)
                    .into_any_element()
            }
            ViewNode::Menu { items } => {
                // A right-click / context actuation menu — a column of rows; an enabled row is a
                // Button firing `{turn, arg}`, a disabled row a dimmed Label (the cap tooth shown).
                let mut col = v_flex()
                    .gap_0p5()
                    .p_1()
                    .border_1()
                    .border_color(cx.theme().border);
                for (i, item) in items.iter().enumerate() {
                    if item.enabled {
                        let applet = self.applet.clone();
                        let turn = item.turn.clone();
                        let arg = item.arg;
                        col = col.child(
                            Button::new(("deos-menu", label_hash(&format!("{}:{}", item.turn, i))))
                                .label(item.label.clone())
                                .on_click(move |_ev: &ClickEvent, _window, _cx| {
                                    if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                        eprintln!("deos-view: menu '{turn}' did not commit: {e}");
                                    }
                                }),
                        );
                    } else {
                        col = col.child(
                            div()
                                .opacity(0.4)
                                .child(Label::new(item.label.clone()).text_color(theme_fg)),
                        );
                    }
                }
                col.into_any_element()
            }
            ViewNode::Halo {
                target_slot: _,
                handles,
            } => {
                // The Pharo handle-ring — each handle is a rounded affordance firing the same
                // `{turn, arg}` a menu would; a `!enabled` handle is dimmed (cap-refused). The
                // compass-anchor geometry is renderer layout; here the handles ring in a wrap.
                let mut ring = div().flex().flex_wrap().gap_1().items_center();
                for (i, h) in handles.iter().enumerate() {
                    if h.enabled {
                        let applet = self.applet.clone();
                        let turn = h.turn.clone();
                        let arg = h.arg;
                        ring = ring.child(
                            Button::new(("deos-halo", label_hash(&format!("{}:{}", h.turn, i))))
                                .label(h.glyph.clone())
                                .on_click(move |_ev: &ClickEvent, _window, _cx| {
                                    if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                        eprintln!(
                                            "deos-view: halo handle '{turn}' did not commit: {e}"
                                        );
                                    }
                                }),
                        );
                    } else {
                        ring = ring.child(
                            div()
                                .opacity(0.4)
                                .size(px(24.))
                                .rounded_full()
                                .bg(cx.theme().border)
                                .child(Label::new(h.glyph.clone()).text_color(theme_fg)),
                        );
                    }
                }
                ring.into_any_element()
            }
            ViewNode::Slider {
                slot,
                min,
                max,
                turn,
            } => {
                // A bound scrubber: the thumb sits at the live slot value (read immediate-mode); a
                // click on a tick seeks — firing `turn` with `arg = that tick's value` (a REAL
                // verified turn), the same discrete-tick actuation the native Time scrubber uses.
                let value = self.applet.borrow().get_u64(*slot);
                let lo = *min;
                let hi = (*max).max(lo + 1);
                let span = hi - lo;
                let n_ticks = span.clamp(1, 20) as usize;
                let mut track = h_flex().gap_0p5().items_center();
                for k in 0..=n_ticks {
                    let tick_val = lo + (span * k as u64) / n_ticks as u64;
                    let filled = tick_val <= value;
                    let applet = self.applet.clone();
                    let turn_s = turn.clone();
                    let seek = tick_val as i64;
                    track = track.child(
                        div()
                            .id(SharedString::from(format!("deos-slider-{slot}-{k}")))
                            .w(px(10.))
                            .h(px(16.))
                            .rounded(px(2.))
                            .bg(if filled { theme_fg } else { cx.theme().border })
                            .cursor_pointer()
                            .on_mouse_down(MouseButton::Left, move |_ev, _window, _cx| {
                                if let Err(e) = applet.borrow_mut().fire(&turn_s, seek) {
                                    eprintln!(
                                        "deos-view: slider seek '{turn_s}' did not commit: {e}"
                                    );
                                }
                            }),
                    );
                }
                v_flex()
                    .gap_1()
                    .child(Label::new(format!("{lo} ≤ {value} ≤ {hi}")).text_color(theme_fg))
                    .child(track)
                    .into_any_element()
            }
            ViewNode::Toggle {
                slot,
                on_turn,
                off_turn,
                glyph_on,
                glyph_off,
                label,
            } => {
                // An affordance checkbox: the glyph reflects the live slot; a click fires `off_turn`
                // when currently on, else `on_turn` (a REAL verified turn flipping the boolean).
                let on = self.applet.borrow().get_u64(*slot) != 0;
                let glyph = if on {
                    glyph_on.clone()
                } else {
                    glyph_off.clone()
                };
                let applet = self.applet.clone();
                let fire = if on {
                    off_turn.clone()
                } else {
                    on_turn.clone()
                };
                let text = format!("{glyph} {label}");
                Button::new((
                    "deos-toggle",
                    label_hash(&format!("{on_turn}:{off_turn}:{slot}")),
                ))
                .label(text)
                .on_click(move |_ev: &ClickEvent, _window, _cx| {
                    if !fire.is_empty() {
                        if let Err(e) = applet.borrow_mut().fire(&fire, 0) {
                            eprintln!("deos-view: toggle '{fire}' did not commit: {e}");
                        }
                    }
                })
                .into_any_element()
            }
            ViewNode::Tile { handle, w, h } => {
                // The genuine ceiling — a card-referenced native paint region. The card does NOT
                // carry pixels; native shows a sized placeholder framing the host-resolved handle
                // (a Servo render, a video) until the host paints into it.
                let tw = if *w == 0 {
                    320.0
                } else {
                    (*w as f32).min(960.0)
                };
                let th = if *h == 0 {
                    200.0
                } else {
                    (*h as f32).min(720.0)
                };
                v_flex()
                    .w(px(tw))
                    .h(px(th))
                    .gap_1()
                    .items_center()
                    .justify_center()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .bg(cx.theme().background)
                    .child(Label::new("▦").text_color(cx.theme().muted_foreground))
                    .child(
                        Label::new(format!("‹tile {handle}: host-painted region {w}×{h}›"))
                            .text_color(cx.theme().muted_foreground),
                    )
                    .into_any_element()
            }

            // The adept-only wrapper renders its inner node transparently (the disclosure filter,
            // when applied, removes the marker before paint; an un-filtered tree shows the bones).
            ViewNode::Adept(inner) => self.node(inner, _window, cx),

            // ── The COMPOSITION KEYSTONE — mount a cell's WHOLE hosted view-tree as a
            //    subtree (the cell is a component, not a leaf). A bordered frame with a muted
            //    `⌂ <cell>` header wrapping the hosted subtree; an UNRESOLVED host paints an
            //    honest placeholder (it has no tree to mount yet).
            ViewNode::Host { cell, view } => {
                let head = format!("⌂ {}", short_cell(cell));
                let mut frame = v_flex()
                    .gap_1()
                    .p_2()
                    .border_1()
                    .border_color(cx.theme().border)
                    .child(
                        Label::new(head)
                            .text_color(cx.theme().muted_foreground)
                            .into_any_element(),
                    );
                match view {
                    Some(v) => frame = frame.child(self.node(v, _window, cx)),
                    None => {
                        frame = frame.child(
                            Label::new(format!("‹mount cell {}: unresolved›", short_cell(cell)))
                                .text_color(cx.theme().muted_foreground),
                        )
                    }
                }
                frame.into_any_element()
            }
        }
    }
}

/// The semantic-tag palette — a `pill`/`icon` tag (`good`/`warn`/`bad`/`accent`/`muted`/…)
/// maps to a tint. The cockpit's `pill(text, color)` idiom expressed as data: the SAME small
/// set of statuses, here keyed by the `props.tag` channel. An unknown tag falls back to accent.
fn tag_color(tag: &str) -> gpui::Hsla {
    let c = match tag {
        "good" | "genuine" | "live" => 0x3fb950,
        "warn" | "pending" => 0xd29922,
        "bad" | "refusal" | "revoked" => 0xf85149,
        "muted" => 0x9aa0aa,
        _ => 0x5b8cff, // accent
    };
    rgb(c).into()
}

/// A short, human prefix of a (hex) cell id for a host frame header. Long ids elide; short
/// ones (the test labels) show whole.
fn short_cell(cell: &str) -> String {
    if cell.len() > 12 {
        format!("{}…", &cell[..12])
    } else {
        cell.to_string()
    }
}

impl Render for AppletView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Reset the bind-id cursor so the Nth `bind` node painted this frame maps to
        // `BindingId(n)` (the same order `bind_plan` registered them in).
        self.render_cursor.set(0);
        // `Context<Self>` derefs to `App`; the node walker reads the theme + applet
        // through `&mut App`.
        let app: &mut App = cx;
        let background = app.theme().background;
        let foreground = app.theme().foreground;
        // Walk the view-tree by BORROW (`&self.tree`) instead of deep-cloning the whole
        // `ViewNode` every paint — `node` only reads it. `self` is borrowed immutably,
        // `app` is `cx` (a distinct object), so the borrows don't conflict.
        let body = self.node(&self.tree, window, app);
        div()
            .size_full()
            .bg(background)
            .text_color(foreground)
            .child(body)
    }
}

/// A stable id salt for a button from its label (so two buttons in one tree differ).
fn label_hash(label: &str) -> u64 {
    let mut h: u64 = 1469598103934665603; // FNV-1a offset
    for b in label.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    h
}
