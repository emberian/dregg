//! CARD PANE — mount a hyperdreggmedia CARD (a deos-js applet's view-tree) as a LIVE
//! cockpit surface, backed by the cockpit's REAL `World`.
//!
//! This is the visible counterpart to [`crate::agent_attach`]. Where `agent_attach`
//! proves the AGENT'S HANDS drive the live ledger headlessly, this proves the CARD —
//! the operator-facing applet view — renders as real gpui-component pixels IN the
//! cockpit, and its button fires a real verified turn on the SAME live `World` the
//! cockpit inspector reads.
//!
//! ## The seam it closes
//!
//! `deos-view` ([`deos_view::AppletView`]) already renders a deos-js applet's view-tree
//! to real gpui-component widgets — but over the EMBEDDED [`deos_js::Applet`] (which
//! mints its own throwaway single-cell world). The cockpit's live substance is the
//! ATTACHED applet ([`deos_js::AttachedApplet`]), whose `fire` commits THROUGH
//! [`crate::agent_attach::WorldSinkAdapter::live`] onto the operator's real cells.
//!
//! [`CardPane`] is the small weld: it walks the SAME `deos.ui.*` view-tree
//! ([`deos_view::ViewNode`], parsed by [`deos_view::parse_view_tree`] from the REAL
//! engine-produced JSON) into the SAME gpui-component vocabulary, but binds + fires
//! against the live `AttachedApplet`:
//!
//!   * a `bind` node re-reads the bound model slot off the LIVE ledger
//!     (`AttachedApplet::get_u64` → a witnessed read of the operator's real cell); and
//!   * a `button`'s `on_click` calls `AttachedApplet::fire` = ONE cap-gated verified
//!     turn committed through `World::commit_turn` onto the live ledger (a receipt that
//!     lands on the cockpit's own provenance log).
//!
//! The view-tree is AUTHORED gpui-free (the JS builds `deos.ui.*` data + `JSON.stringify`s
//! it into the applet's ephemeral view-state — NO turn), so a throwaway embedded engine
//! authors the tree, and the LIVE `AttachedApplet` is the substance the rendered widgets
//! drive. (The cap tooth still runs in deos-js before every committed fire.)
//!
//! ## CARDPANE RIDES THE PULSE — the Pulse→Signals weld's card half
//!
//! The card owns the SAME fine-grained signal machinery [`deos_view::AppletView`]
//! grew (wave 3 welded it into the AppletView-backed panes only — this closes that
//! named gap for the attached-World cards):
//!
//!   * every `bind` node registers on its `(cell, slot)` source in a
//!     [`deos_js::signals::BindingRegistry`] and paints out of a per-binding value
//!     CACHE (not a fresh ledger read every paint);
//!   * the desktop's dynamics pump broadcasts each beat's `WorldEvent::FieldSet`s into
//!     every open card ([`CardPane::on_world_events`]) and the cell-wide
//!     `CellMutated`/`CapabilityRevoked` events through the registry's conservative
//!     `invalidate_cell` tooth ([`CardPane::on_world_cells`]) — only the dirty binds
//!     re-read, and a card bound to none of the touched sources stays perfectly still;
//!   * a dirty bind wears the one-beat accent GLOW until the pulse's next
//!     [`CardPane::fade_glow`]; and
//!   * turns fired directly on the card's OWN substance (a rendered button on an
//!     embedded backing — named in no dynamics stream) are caught by the audit-tape
//!     watermark ([`CardPane::catch_up_own_turns`]) each quiet beat.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use gpui::{
    div, px, rgb, App, ClickEvent, Context, FontWeight, InteractiveElement, IntoElement,
    MouseButton, ParentElement, Render, SharedString, Styled, Window,
};
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};

use deos_js::signals::{BindingId, BindingRegistry, Slot, SourceEvent};
use deos_js::AttachedApplet;
use deos_view::{disclose, parse_view_tree, pill_display, Disclosure, ViewNode};
use dregg_types::CellId;

/// A shared, interior-mutable handle on the LIVE attached applet. The card reads the
/// model through it (a `bind` re-read off the live ledger) and a button's `on_click`
/// fires a verified turn through it (a real turn on the cockpit's World). One handle,
/// shared by every widget — the single sovereign cell behind the whole card.
pub type SharedAttached = Rc<RefCell<AttachedApplet>>;

/// **The read+fire SUBSTANCE a [`CardPane`] renders over** — the three operations the
/// renderer needs from a live card backing: read a bound model slot, read ephemeral
/// view-state, and fire an affordance as a real verified turn. Abstracting it lets ONE
/// exhaustive renderer ([`CardPane::node`]) drive two backings: the deos-js
/// [`AttachedApplet`] (the operator/agent + inspector cards) and the app-framework
/// [`crate::app_registry::AppCardSubstance`] (a launched starbridge-app's BESPOKE card,
/// whose buttons fire the app's real cap-gated verified turns through its
/// [`crate::app_worldspine::AppWorldSpine`]).
pub trait CardSubstance {
    /// The sovereign cell this card's binds read slots of — constant for the card's
    /// lifetime. Every `bind` node registers on `(cell(), slot)` in the pane's signal
    /// registry, so THE PULSE's broadcast (`WorldEvent::FieldSet` / `CellMutated` /
    /// `CapabilityRevoked` naming this cell) dirties exactly this card's bindings.
    fn cell(&self) -> CellId;
    /// How many verified turns THIS substance committed on its OWN tape — the pulse's
    /// own-turn watermark source ([`CardPane::catch_up_own_turns`]). A backing whose
    /// fires are already named in the World's dynamics stream (every touched slot
    /// rides the pulse broadcast) may report a constant still tape.
    fn receipt_count(&self) -> usize;
    /// Read the bound model slot off the live ledger (a `bind`/`gauge`/`slider`/… read).
    fn get_u64(&self, slot: usize) -> u64;
    /// Read an ephemeral view-state draft (an `input` field), if the backing keeps one.
    fn get_view(&self, key: &str) -> Option<String>;
    /// Fire an affordance as ONE real verified turn (a button's `{turn, arg}`). A cap
    /// refusal / executor reject is surfaced as the `Err` string (the live model simply
    /// does not advance).
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String>;
}

/// A shared, interior-mutable [`CardSubstance`] — what a [`CardPane`] holds and every
/// widget closure clones. One handle, shared by the whole card.
pub type CardSubstanceRef = Rc<RefCell<dyn CardSubstance>>;

impl CardSubstance for AttachedApplet {
    fn cell(&self) -> CellId {
        AttachedApplet::cell(self)
    }
    fn receipt_count(&self) -> usize {
        // The attached applet's own audit tape — turns a rendered button committed
        // THROUGH this applet (the watermark tooth's catch-up source).
        AttachedApplet::receipt_count(self)
    }
    fn get_u64(&self, slot: usize) -> u64 {
        AttachedApplet::get_u64(self, slot)
    }
    fn get_view(&self, key: &str) -> Option<String> {
        AttachedApplet::get_view(self, key).map(str::to_string)
    }
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String> {
        AttachedApplet::fire(self, method, arg)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// A launched starbridge-app's card backing fires through its [`AppWorldSpine`] (the
/// app-framework→World bridge), reads bound slots off the live World ledger, and keeps
/// no ephemeral view-state (its cards are pure server-state views).
#[cfg(feature = "app-registry")]
impl CardSubstance for crate::app_registry::AppCardSubstance {
    fn cell(&self) -> CellId {
        crate::app_registry::AppCardSubstance::app_cell(self)
    }
    fn receipt_count(&self) -> usize {
        // The app cell's live NONCE — bumps once per verified turn committed on the
        // cell, so it is an honest audit-tape watermark: a fire through this spine
        // moves it, and so does a foreign turn on the app cell (both conservatively
        // caught up; never under-invalidating). The spine keeps no local receipt
        // tape (its receipts land on `World::receipts()`), so the cell's own turn
        // counter is the watermark. Absent cell → a still tape (fail-soft).
        crate::app_registry::AppCardSubstance::spine(self)
            .live_state()
            .map(|s| s.nonce() as usize)
            .unwrap_or(0)
    }
    fn get_u64(&self, slot: usize) -> u64 {
        crate::app_registry::AppCardSubstance::get_u64(self, slot)
    }
    fn get_view(&self, _key: &str) -> Option<String> {
        None
    }
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String> {
        crate::app_registry::AppCardSubstance::fire(self, method, arg)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// The EMBEDDED single-custody applet is ALSO a card substance — the throwaway
/// authoring engine / a bake's self-contained backing. Its fires commit on its OWN
/// embedded verified executor (real cap-gated turns, a real receipt tape), which NO
/// dynamics stream names — exactly the backing the pulse's own-turn watermark
/// ([`CardPane::catch_up_own_turns`]) exists for.
impl CardSubstance for deos_js::Applet {
    fn cell(&self) -> CellId {
        deos_js::Applet::cell(self)
    }
    fn receipt_count(&self) -> usize {
        deos_js::Applet::receipt_count(self)
    }
    fn get_u64(&self, slot: usize) -> u64 {
        deos_js::Applet::get_u64(self, slot)
    }
    fn get_view(&self, key: &str) -> Option<String> {
        deos_js::Applet::get_view(self, key).map(str::to_string)
    }
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String> {
        deos_js::Applet::fire(self, method, arg)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// The slot each `bind` node reads, in tree-walk (pre-order) appearance — the card
/// mints one [`BindingId`] per `bind` node monotonically, paired with the model `Slot`
/// it re-reads. The cell is constant (the substance's sovereign cell), so the source
/// each binding registers is `(substance.cell(), slot)`. MIRRORS `deos_view::render`'s
/// private `bind_plan` exactly (the two renderers walk the same recursion order, so a
/// tree's Nth `bind` is `BindingId(n)` in both).
fn bind_plan(tree: &ViewNode, out: &mut Vec<Slot>) {
    match tree {
        ViewNode::Bind { slot, .. } => out.push(*slot),
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                bind_plan(c, out);
            }
        }
        // Containers recurse their children in declaration order so the Nth `Bind`
        // stays `BindingId(n)`. `tabs` registers EVERY panel's binds (render walks all
        // panels too, displaying only the selected one) so the cursor never desyncs on
        // a tab switch.
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
        ViewNode::Grid { children, .. } => {
            for c in children {
                bind_plan(c, out);
            }
        }
        // The adept-only wrapper is transparent to the bind cursor (the pane mounts a
        // `simple`-disclosed tree, which drops these — but an un-disclosed tree still
        // registers the inner node's binds here).
        ViewNode::Adept(inner) => bind_plan(inner, out),
        // A `host`'s resolved hosted subtree is recursed at the host's position; an
        // unresolved host (`view: None`) consumes no cursor positions.
        ViewNode::Host { view, .. } => {
            if let Some(v) = view {
                bind_plan(v, out);
            }
        }
        // Leaves that hold no bind source. The bound batch-2 nodes (`slider`/`toggle`/
        // `gauge`/live `pill`) read their slot immediate-mode (NOT via the bind
        // cursor), so they register nothing.
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

/// The cockpit surface that renders a deos-js CARD over the LIVE `World`. A real gpui
/// `Render` entity: open it in a (headless or windowed) window and it paints the card's
/// widgets, and a button fires a real verified turn on the live ledger.
///
/// **CARDPANE RIDES THE PULSE** — the card owns the SAME fine-grained signal machinery
/// [`deos_view::AppletView`] does (a [`BindingRegistry`] + a per-binding value cache +
/// the one-beat dirty glow + the own-turn watermark), so the desktop's dynamics pump
/// can broadcast each beat's `WorldEvent`s into every open card
/// ([`Self::on_world_events`] / [`Self::on_world_cells`]) and an attached-World card
/// bound to a touched `(cell, slot)` repaints exactly its dirty binds — instead of
/// painting stale cached-nothing (the pre-weld card re-read every bind every paint,
/// but nothing ever *told* it to repaint when the World moved under it).
pub struct CardPane {
    /// The live card substance (shared so button handlers fire live turns + binds
    /// re-read the live ledger) — a deos-js applet or a launched app's spine.
    applet: CardSubstanceRef,
    /// The extracted view-tree (the real `deos.ui.*` element-tree the JS authored).
    tree: ViewNode,
    /// A short title shown above the card (the surface chrome).
    title: String,
    /// The substance's sovereign cell — the constant cell every bind reads a slot of.
    cell: CellId,
    /// The reverse index `(cell, slot) → bindings` (deos-js's signal registry). Built
    /// once per mounted tree by registering each `bind` node in tree-walk order.
    registry: BindingRegistry,
    /// The Nth `bind` node (tree-walk order) is `BindingId(n)` reading `bind_slots[n]`.
    /// Render walks the tree in the same order and consumes ids from a counter so each
    /// `bind` paints out of `cache[BindingId(n)]`.
    bind_slots: Vec<Slot>,
    /// The fine-grained value cache: `binding → last-read live value`. A `bind` paints
    /// from here; only `invalidate`d bindings re-read (the rest keep their cached
    /// value). `RefCell` because `render`/`node` take `&self` but lazily fill the
    /// cache on first paint of each binding.
    cache: RefCell<BTreeMap<BindingId, u64>>,
    /// The id-counter render uses to map the Nth painted `bind` node to `BindingId(n)`.
    /// Reset at the top of each `render`. `Cell` for the same `&self`-walk reason.
    render_cursor: Cell<u64>,
    /// Instrumentation: the bindings the LAST invalidation call re-evaluated (the
    /// per-call test bar — a turn on slot A dirtied ONLY binding A).
    last_dirty: RefCell<Vec<BindingId>>,
    /// THE DIRTY GLOW — the bindings invalidated since the host's last pulse beat
    /// (the per-BEAT union; only [`Self::fade_glow`] clears). A glowing bind's label
    /// paints in the accent tint for exactly one beat.
    glow: RefCell<BTreeSet<BindingId>>,
    /// The substance's audit-tape watermark — how many of its OWN committed receipts
    /// the card has accounted for. A turn fired on this very surface (a rendered
    /// button's `on_click` on an EMBEDDED backing) is named in no dynamics stream, so
    /// the host's pulse calls [`Self::catch_up_own_turns`] each beat.
    receipts_seen: Cell<usize>,
}

impl CardPane {
    /// Build a card pane from a shared live applet + its view-tree + a title. The
    /// [`SharedAttached`] coerces into the [`CardSubstanceRef`] the pane holds (a deos-js
    /// applet IS a [`CardSubstance`]).
    pub fn new(applet: SharedAttached, tree: ViewNode, title: impl Into<String>) -> Self {
        let applet: CardSubstanceRef = applet;
        Self::build(applet, tree, title.into())
    }

    /// Build a card pane over an arbitrary [`CardSubstance`] — the generalization of
    /// [`Self::new`] used to mount a launched starbridge-app's BESPOKE card (over a
    /// [`crate::app_registry::AppCardSubstance`]), so its buttons fire the app's real
    /// verified turns through its spine.
    pub fn new_substance(
        substance: CardSubstanceRef,
        tree: ViewNode,
        title: impl Into<String>,
    ) -> Self {
        Self::build(substance, tree, title.into())
    }

    /// The shared constructor body: mount the CLEAN newcomer projection (progressive
    /// disclosure — drop the `props.adept` "see the bones" detail; an `adept` host can
    /// opt up by mounting the raw tree), then register every `bind` node of the
    /// DISCLOSED tree (the tree render actually walks) on its `(cell, slot)` source in
    /// the signal registry — the pulse-feed index.
    fn build(applet: CardSubstanceRef, tree: ViewNode, title: String) -> Self {
        let disclosed = disclose(&tree, Disclosure::Simple);
        let (cell, receipts_seen) = {
            let a = applet.borrow();
            (a.cell(), a.receipt_count())
        };
        let mut bind_slots = Vec::new();
        bind_plan(&disclosed, &mut bind_slots);

        let mut registry = BindingRegistry::new();
        for (n, slot) in bind_slots.iter().enumerate() {
            registry.register(BindingId(n as u64), cell, *slot);
        }

        Self {
            applet,
            tree: disclosed,
            title,
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

    /// The shared live substance handle (for the caller to inspect receipts / the live
    /// ledger after a turn fires — the SAME backing the widgets drive).
    pub fn substance(&self) -> CardSubstanceRef {
        self.applet.clone()
    }

    /// **Replace the rendered view-tree** — the edit-from-within hook. After a
    /// [`deos_js::card_editor::ViewPatch`] re-folds the card's view document, the
    /// caller bridges the new tree to a [`ViewNode`] and swaps it in here, so the next
    /// paint draws the reshaped surface. The live applet (the substance binds/fires
    /// drive) is untouched — only the view changed (the view is data, not code). The
    /// binding plan is rebuilt from the new (disclosed) tree and the value cache is
    /// cleared, so each `bind` re-reads its live slot on the next paint; the receipts
    /// watermark survives (the substance's audit tape is untouched by a rewrite).
    pub fn set_tree(&mut self, tree: ViewNode) {
        // Keep the same clean newcomer projection the constructors mount.
        let disclosed = disclose(&tree, Disclosure::Simple);
        let mut bind_slots = Vec::new();
        bind_plan(&disclosed, &mut bind_slots);

        let mut registry = BindingRegistry::new();
        for (n, slot) in bind_slots.iter().enumerate() {
            registry.register(BindingId(n as u64), self.cell, *slot);
        }

        self.tree = disclosed;
        self.registry = registry;
        self.bind_slots = bind_slots;
        self.cache = RefCell::new(BTreeMap::new());
        self.render_cursor = Cell::new(0);
        self.last_dirty = RefCell::new(Vec::new());
        self.glow = RefCell::new(BTreeSet::new());
    }

    /// The card's current rendered view-tree (read-only) — so a mount can re-derive
    /// the surface or assert its shape after a reshape.
    pub fn tree(&self) -> &ViewNode {
        &self.tree
    }

    // ── THE PULSE FEED — the same fine-grained hooks `deos_view::AppletView` wears,
    //    so the desktop's dynamics pump drives attached-World cards too. ─────────────

    /// **THE GENERAL FINE-GRAINED HOOK — the Pulse→Signals weld's card entry point.**
    /// Fold world events (each a `(cell, slot)` write, ANY cell) through the registry
    /// and re-read ONLY the dirty bindings into the cache.
    ///
    /// `touched` is what the desktop's dynamics pump projects each
    /// `WorldEvent::FieldSet { cell, index }` into. The registry is keyed
    /// `(cell, slot)`, so an event naming a FOREIGN cell (one this card's binds never
    /// read) dirties nothing — the pump broadcasts one beat's events to every open
    /// card and only the cards actually bound to the touched sources repaint. Returns
    /// the dirty set; those bindings also join [`Self::glowing`] until the host's next
    /// [`Self::fade_glow`] beat.
    pub fn on_world_events(&self, touched: &[(CellId, Slot)]) -> Vec<BindingId> {
        let dirty = self
            .registry
            .invalidate_all(touched.iter().map(|(c, s)| SourceEvent::new(*c, *s)));
        self.reread_dirty(&dirty);
        dirty
    }

    /// THE FINE-GRAINED HOOK, single-cell sugar — fold a committed turn's touched
    /// slots (of the substance's OWN sovereign cell) through the registry. Exactly
    /// [`Self::on_world_events`] with every event on `self.cell`.
    pub fn on_committed_turn(&self, touched_slots: &[Slot]) -> Vec<BindingId> {
        let touched: Vec<(CellId, Slot)> = touched_slots.iter().map(|s| (self.cell, *s)).collect();
        self.on_world_events(&touched)
    }

    /// **THE CELL-WIDE INVALIDATION HOOK — the `CellMutated`/`CapabilityRevoked`
    /// feed.** Fold world events that name a whole CELL but no slot through the
    /// registry via its conservative `invalidate_cell` tooth: EVERY binding reading
    /// ANY slot of a touched cell re-reads (never under-invalidating), while a cell no
    /// bind of this card reads dirties nothing (a foreign mutation never
    /// over-invalidates — the pump broadcasts the beat's cell events to every open
    /// card, same as the FieldSet feed). Returns the dirty set (glowing, like every
    /// other feed).
    pub fn on_world_cells(&self, cells: &[CellId]) -> Vec<BindingId> {
        let mut dirty: BTreeSet<BindingId> = BTreeSet::new();
        for c in cells {
            dirty.extend(self.registry.invalidate_cell(*c));
        }
        let dirty: Vec<BindingId> = dirty.into_iter().collect();
        self.reread_dirty(&dirty);
        dirty
    }

    /// **Catch up turns committed on the substance's OWN tape** — the pulse's
    /// quiet-beat tooth. A button rendered by this very card fires the substance
    /// directly; on an EMBEDDED backing no dynamics stream names the touched slots,
    /// so the host's pulse calls this each beat: if the substance's audit tape grew
    /// past the watermark, every binding of the card's cell is (conservatively)
    /// invalidated and re-read. Returns the dirty set (empty on a still tape — the
    /// common, free case). A spine-backed substance watermarks on its app cell's
    /// live NONCE, so a turn on that cell is caught here at the latest even though
    /// its `FieldSet`s also ride the World's dynamics broadcast.
    pub fn catch_up_own_turns(&self) -> Vec<BindingId> {
        let n = self.applet.borrow().receipt_count();
        if n == self.receipts_seen.replace(n) {
            return Vec::new();
        }
        let dirty = self.registry.invalidate_cell(self.cell);
        self.reread_dirty(&dirty);
        dirty
    }

    /// Mark the substance's current audit tape as accounted for WITHOUT invalidating —
    /// for a caller that just fired turns itself and already folded their exact
    /// touched slots through [`Self::on_world_events`], so the next
    /// [`Self::catch_up_own_turns`] doesn't re-invalidate the whole cell.
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

    /// The bindings the last invalidation call re-evaluated (instrumentation / the
    /// test bar). Empty before any turn drove the card.
    pub fn last_dirty(&self) -> Vec<BindingId> {
        self.last_dirty.borrow().clone()
    }

    /// The bindings still wearing the dirty glow — the per-BEAT union of every dirty
    /// set since the last [`Self::fade_glow`], id-sorted.
    pub fn glowing(&self) -> Vec<BindingId> {
        self.glow.borrow().iter().copied().collect()
    }

    /// Retire the dirty glow (the host's pulse calls this at the top of each beat, so
    /// a glow lasts exactly one beat). Returns whether anything was glowing — the
    /// caller's cue that a repaint is needed to un-tint the rows.
    pub fn fade_glow(&self) -> bool {
        let mut g = self.glow.borrow_mut();
        let had = !g.is_empty();
        g.clear();
        had
    }

    /// The cached live value of a binding, if it has been read (lazily on first paint
    /// or by an invalidation re-read). For tests / instrumentation.
    pub fn cached(&self, binding: BindingId) -> Option<u64> {
        self.cache.borrow().get(&binding).copied()
    }

    /// How many `bind` nodes the card registered (one [`BindingId`] each).
    pub fn binding_count(&self) -> usize {
        self.bind_slots.len()
    }

    /// The bindings whose registered source is `slot` of the card's own cell — the
    /// EXPECTED dirty set for a write to that slot (instrumentation / the bake bar).
    pub fn bindings_reading(&self, slot: Slot) -> Vec<BindingId> {
        self.bind_slots
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == slot)
            .map(|(n, _)| BindingId(n as u64))
            .collect()
    }

    /// The identity + value the next-painted `bind` node should show: its cached
    /// value, filling the cache lazily off the live ledger on first paint. Advances
    /// the render cursor so the Nth `bind` node maps to `BindingId(n)`. The id comes
    /// back too so the paint can check the dirty-glow set for this exact binding.
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

    /// Render one view-tree node into a gpui element. Recursive: containers render
    /// their children with the same vocabulary `deos_view::AppletView` uses, but a
    /// `bind` re-reads the LIVE ledger and a `button` fires a LIVE turn.
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
                // Never let a constrained column squeeze a text row to zero height
                // (which overlaps the next line) — a label keeps its own line height.
                .flex_shrink_0()
                .into_any_element(),
            ViewNode::Bind { slot, label, fmt } => {
                // THE SIGNAL BINDING over the LIVE ledger — paint out of the
                // fine-grained value CACHE. The cache fills lazily off the live ledger
                // on first paint (the same witnessed read the JS closure made, through
                // the substance), then is updated ONLY for the bindings THE PULSE
                // invalidates (`on_world_events` / `on_world_cells` /
                // `catch_up_own_turns`). A clean binding repaints its cached value
                // without re-reading the ledger — the same SolidJS-shaped fine-grained
                // re-render `deos_view::AppletView` does.
                let (id, value) = self.next_bind_value(*slot);
                // CONSUMER-DELIGHT: an opaque key/hash paints SHORT + friendly
                // (`🦊 swift-fox` / `0x8bf3…a3d8` / `1,234,567`) instead of a 20-digit
                // decimal; `raw` keeps the plain decimal so a counter is unchanged. The
                // SAME `deos_view::fmt` formatter the native/web/discord renderers call.
                let shown = deos_view::fmt::format_value(value, *fmt);
                let text = if label.is_empty() {
                    shown
                } else {
                    format!("{label}{shown}")
                };
                // THE DIRTY GLOW — a binding freshly invalidated this beat paints in
                // the accent tint until the host's next pulse `fade_glow`s it: a
                // foreign turn is FELT on exactly the rows it moved, for one beat.
                let color = if self.glow.borrow().contains(&id) {
                    tag_color("accent")
                } else {
                    theme_fg
                };
                Label::new(text)
                    .font_weight(FontWeight::BOLD)
                    .text_color(color)
                    .flex_shrink_0()
                    .into_any_element()
            }
            ViewNode::Button { label, turn, arg } => {
                // THE REAL LIVE TURN — a button's onClick fires the applet's affordance =
                // ONE cap-gated verified turn committed THROUGH `World::commit_turn` onto
                // the live ledger. The handler captures the shared live applet + the
                // (turn, arg) from the view-tree.
                let applet = self.applet.clone();
                let turn = turn.clone();
                let arg = *arg;
                Button::new(("deos-card-aff", label_hash(label)))
                    .primary()
                    .label(label.clone())
                    .on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Fire the verified turn on the live World. A cap refusal /
                        // executor reject is surfaced to stderr (the screenshot stays
                        // honest); the live model simply does not advance.
                        //
                        // GUARDED at the event boundary: gpui dispatches this click from a
                        // `nounwind` Obj-C callback, so a panic crossing it would
                        // `process::abort` the whole cockpit. The `fire` is Result-typed,
                        // but `applet.borrow_mut()` would PANIC if the shared applet were
                        // already borrowed (e.g. a re-entrant fire), so contain any panic
                        // as a logged no-op rather than abort the process.
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                eprintln!(
                                    "card-pane: live affordance '{turn}' did not commit: {e}"
                                );
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: live affordance '{turn}' PANICKED — contained \
                                 (no-op) instead of aborting (the gpui event boundary is \
                                 nounwind)."
                            );
                        });
                    })
                    .into_any_element()
            }
            ViewNode::Input {
                bind_view,
                fire_turn,
                submit_label,
            } => {
                // Ephemeral view-state (draft text) — NOT cell state. When `fire_turn` is set a
                // paired submit button parses the draft into the turn's `arg` and fires a REAL
                // verified turn on the live World (input → verified turn).
                let draft = self.applet.borrow().get_view(bind_view).unwrap_or_default();
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
                            "deos-card-input-submit",
                            label_hash(&format!("{fire_turn}:{label}")),
                        ))
                        .primary()
                        .label(label)
                        .on_click(
                            move |_ev: &ClickEvent, _window, _cx| {
                                guarded_fire(&applet, &turn, draft_arg);
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

            // ── The RICHNESS EXPANSION (batch 1) — mirror `deos_view::render`'s arms, but
            //    bound + fired against the LIVE attached applet. ──────────────────────────
            ViewNode::Section {
                title,
                tag,
                children,
            } => {
                // A titled, bordered container — the uniform "styled section". `tag=="genuine"`
                // accents the border (the existing `props.tag` styling convention).
                let accent = if tag == "genuine" {
                    theme_fg
                } else {
                    cx.theme().border
                };
                let mut card = v_flex().gap_1().p_2().border_1().border_color(accent);
                if !title.is_empty() {
                    card = card.child(
                        Label::new(title.clone())
                            .font_weight(FontWeight::BOLD)
                            .text_color(theme_fg),
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
                // The active tab index lives in a MODEL SLOT (read live off the ledger), so a
                // tab switch is a REAL cap-gated verified turn — reflective + replayable.
                let active = self.applet.borrow().get_u64(*selected_slot) as usize;
                // The tab strip: one Button per label, the active one `.primary()`; each fires
                // `select_turn` with `arg = its index` (a verified turn through the live applet).
                let mut strip = h_flex().gap_1();
                for (i, label) in tabs.iter().enumerate() {
                    let applet = self.applet.clone();
                    let turn = select_turn.clone();
                    let idx = i as i64;
                    let mut b =
                        Button::new(("deos-card-tab", label_hash(&format!("{select_turn}:{i}"))))
                            .label(label.clone());
                    if i == active {
                        b = b.primary();
                    }
                    strip = strip.child(b.on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Same nounwind-boundary guard as a `button` fire (the gpui Obj-C
                        // callback is `nounwind`; contain a re-entrant-borrow panic as a no-op).
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, idx) {
                                eprintln!("card-pane: tab select '{turn}' did not commit: {e}");
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: tab select '{turn}' PANICKED — contained (no-op)."
                            );
                        });
                    }));
                }
                // Walk ALL panels (advancing the bind cursor in registration order) but
                // keep only the selected one's element — so a tab switch never desyncs
                // the cursor (the same discipline `deos_view::render` uses; the plan
                // registered every panel's binds). Out-of-range falls back to the first.
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
                // A bound progress / balance bar — reads its slot IMMEDIATE-MODE off the live
                // ledger. The fill width is `value / max`, clamped to `[0,1]`.
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

            // ── The RICHNESS EXPANSION batch 2 — mirror `deos_view::render`'s arms, but bound +
            //    fired against the LIVE attached applet (every fire guarded at the gpui boundary). ─
            ViewNode::Grid { cols, children } => {
                // Each tile is a DEFINITE-width box that clips its own overflow, so a
                // long unbreakable token (a short cell-id like `0ce097…9b3`, which has
                // no break opportunity to wrap on) is contained instead of bleeding
                // sideways into the neighbouring tile. `flex_wrap` then packs as many
                // uniform tiles per row as the real pane width allows.
                let mut grid = div().flex().flex_wrap().gap_3();
                let cell_w = if *cols > 0 {
                    px(((640.0 / *cols as f32) - 14.0).max(120.0))
                } else {
                    px(160.0)
                };
                for c in children {
                    grid = grid.child(
                        div()
                            .w(cell_w)
                            .flex_none()
                            .overflow_hidden()
                            .child(self.node(c, _window, cx)),
                    );
                }
                grid.into_any_element()
            }
            ViewNode::Breadcrumb { items } => {
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
                                "deos-card-crumb",
                                label_hash(&format!("{}:{}", crumb.turn, i)),
                            ))
                            .label(crumb.label.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
                        );
                    }
                }
                row.into_any_element()
            }
            ViewNode::Progress { value, max, label } => {
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
                // A colored status badge. LIVE variant (the static-phase-word cure): when bound
                // to a `slot` with `cases`, read the slot IMMEDIATE-MODE off the live ledger and
                // map the value to its word + color (a phase slot → COMMIT/REVEAL/RESOLVED), via
                // the SAME `pill_display` resolver every renderer calls. No slot/cases → static.
                let (shown_text, shown_tag) = match slot {
                    Some(s) if !cases.is_empty() => {
                        let value = self.applet.borrow().get_u64(*s);
                        pill_display(text, tag, cases, value)
                    }
                    _ => (text.as_str(), tag.as_str()),
                };
                div()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
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
                            Button::new((
                                "deos-card-menu",
                                label_hash(&format!("{}:{}", item.turn, i)),
                            ))
                            .label(item.label.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
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
                let mut ring = div().flex().flex_wrap().gap_1().items_center();
                for (i, h) in handles.iter().enumerate() {
                    if h.enabled {
                        let applet = self.applet.clone();
                        let turn = h.turn.clone();
                        let arg = h.arg;
                        ring = ring.child(
                            Button::new((
                                "deos-card-halo",
                                label_hash(&format!("{}:{}", h.turn, i)),
                            ))
                            .label(h.glyph.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
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
                // A bound scrubber over the LIVE ledger: discrete clickable ticks (the same
                // actuation the native Time scrubber uses), each seeking `arg = its value`.
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
                            .id(SharedString::from(format!("deos-card-slider-{slot}-{k}")))
                            .w(px(10.))
                            .h(px(16.))
                            .rounded(px(2.))
                            .bg(if filled { theme_fg } else { cx.theme().border })
                            .cursor_pointer()
                            .on_mouse_down(MouseButton::Left, move |_ev, _window, _cx| {
                                guarded_fire(&applet, &turn_s, seek);
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
                    "deos-card-toggle",
                    label_hash(&format!("{on_turn}:{off_turn}:{slot}")),
                ))
                .label(text)
                .on_click(move |_ev: &ClickEvent, _window, _cx| {
                    if !fire.is_empty() {
                        guarded_fire(&applet, &fire, 0);
                    }
                })
                .into_any_element()
            }
            ViewNode::Tile { handle, w, h } => {
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
            ViewNode::Host { cell, view } => {
                // The COMPOSITION KEYSTONE — mount a cell's WHOLE hosted view-tree as a
                // subtree. A bordered frame with a muted `⌂ <cell>` header; an UNRESOLVED host
                // paints an honest placeholder (it has no tree to mount yet).
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
            ViewNode::Adept(inner) => {
                // The progressive-disclosure marker. A `simple`-disclosed tree (the clean
                // newcomer default this pane mounts) drops these before they reach `node`, so
                // this arm only fires if an un-disclosed tree is rendered directly — then it is
                // TRANSPARENT (render the wrapped node) so the adept detail still paints.
                self.node(inner, _window, cx)
            }
        }
    }
}

/// Fire a live affordance through the attached applet, GUARDED at the gpui event boundary (the
/// Obj-C callback is `nounwind`, so a re-entrant-borrow panic would `process::abort` the whole
/// cockpit — contain it as a logged no-op instead). The shared weld every batch-2 actuating node
/// (menu / halo / slider / toggle / breadcrumb / input-submit) routes its click through.
fn guarded_fire(applet: &CardSubstanceRef, turn: &str, arg: i64) {
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if let Err(e) = applet.borrow_mut().fire(turn, arg) {
            eprintln!("card-pane: live affordance '{turn}' did not commit: {e}");
        }
    }))
    .map_err(|_| {
        eprintln!("card-pane: live affordance '{turn}' PANICKED — contained (no-op).");
    });
}

/// The semantic-tag palette (mirrors `deos_view::render::tag_color`) — a `pill`/`icon` tag maps
/// to a tint (the cockpit's `pill(text, color)` idiom expressed as data).
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

/// Truncate a hex cell-id for a compact host header (mirrors `deos_view::render::short_cell`).
fn short_cell(cell: &str) -> String {
    if cell.len() > 12 {
        format!("{}…", &cell[..12])
    } else {
        cell.to_string()
    }
}

impl Render for CardPane {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // SELF-CATCH-UP AT THE PAINT — binds paint from the value cache, so a turn
        // fired on this very surface between paints (a rendered button's on_click)
        // must be caught up BEFORE the walk or a pulse-less host (the dock cockpit,
        // a headless bake capture) would paint the pre-fire value forever. Free on a
        // still tape (one watermark compare); on the desktop, THE PULSE additionally
        // runs this each beat and fades the glow — a pulse-less host simply keeps
        // the accent tint on the last-moved rows (an honest mark, never a stale
        // value).
        self.catch_up_own_turns();
        // Reset the bind-id cursor so the Nth `bind` node painted this frame maps to
        // `BindingId(n)` (the same order `bind_plan` registered them in).
        self.render_cursor.set(0);
        let title = self.title.clone();
        let app: &mut App = cx;
        let header_fg = app.theme().muted_foreground;
        let border = app.theme().border;
        let background = app.theme().background;
        let foreground = app.theme().foreground;
        // Walk the view-tree by BORROW (`&self.tree`) — it can be a large `ViewNode`,
        // and a deep clone every paint is pure waste; `node` only reads it. `self` is
        // borrowed immutably here, `app` is `cx` (a distinct object), so the two
        // borrows don't conflict.
        let body = self.node(&self.tree, window, app);
        // SIZE TO CONTENT, NOT THE COLUMN. The card is a content-sized object: it
        // hugs its view-tree vertically (`w_full`, no `h_full`) so a host never sees
        // it stretch to fill the whole pane and leave a dead canvas below the content,
        // and so its flex children are never squeezed against an over-tall parent
        // (which collapsed line heights into overlapping text). The HOST decides the
        // frame; the card draws exactly as tall as it is.
        div().w_full().bg(background).text_color(foreground).child(
            // The surface chrome — a titled card frame so it reads as a cockpit pane.
            v_flex()
                .w_full()
                .child(
                    div().px_3().py_2().border_b_1().border_color(border).child(
                        Label::new(title)
                            .font_weight(FontWeight::BOLD)
                            .text_color(header_fg),
                    ),
                )
                .child(body),
        )
    }
}

/// Author a card's view-tree by running `applet_js` in real SpiderMonkey against the
/// LIVE attached applet, then extract the engine-produced `deos.ui.*` tree.
///
/// The JS MUST build a `deos.ui.*` tree and stash it under [`deos_view::view_tree_key`]
/// via `app.view.set(...)` (ephemeral view-state — NO turn). The view-tree build commits
/// NOTHING; only a button's later `fire` does. The driven [`AttachedApplet`] is handed
/// back (its `WorldSink` reads + commits onto the live World) paired with the parsed
/// [`ViewNode`] — ready for [`CardPane::new`].
///
/// SpiderMonkey's engine is a process-global, thread-bound singleton, so `rt` is passed
/// in (the caller boots it once for the whole bake).
pub fn build_card_over_live(
    rt: &mut deos_js::JsRuntime,
    applet: AttachedApplet,
    applet_js: &str,
) -> Result<(AttachedApplet, ViewNode), String> {
    let outcome = rt
        .run_attached(applet, applet_js)
        .map_err(|e| format!("card view-tree authoring on the live World: {e}"))?;
    // The authoring JS stashes the stringified tree into the attached applet's ephemeral
    // view-state (NO turn) — and must commit no fires.
    if outcome.fires_committed != 0 {
        return Err(format!(
            "card view-tree authoring committed {} turn(s) — it must only build data",
            outcome.fires_committed
        ));
    }
    let attached = outcome.applet;
    let key = deos_view::view_tree_key();
    let json = attached
        .get_view(key)
        .ok_or_else(|| format!("card JS did not stash a view-tree under view-state '{key}'"))?
        .to_string();
    let tree = parse_view_tree(&json)?;
    Ok((attached, tree))
}

/// The ephemeral view-state key the card's authoring JS stashes its stringified
/// view-tree under (the SAME key [`build_card_over_live`] reads it back from). Exposed
/// so a bake's JS can name it consistently without depending on `deos-view` directly.
pub fn view_tree_key_for_card() -> &'static str {
    deos_view::view_tree_key()
}

/// A stable id salt for a button from its label (so two buttons in one card differ).
fn label_hash(label: &str) -> u64 {
    let mut h: u64 = 1469598103934665603; // FNV-1a offset
    for b in label.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    h
}

// ═══════════════════════════════════════════════════════════════════════════════════
//  THE PULSE-WELD BAR, card half — mirrors `deos-view/tests/world_events_weld.rs`
//  shape-for-shape over `CardPane` (the card constructs without a window; only
//  `render` paints), plus the cell-wide `on_world_cells` tooth wave 3 left
//  unprojected. The substance is a REAL embedded verified applet (every fire is a
//  cap-gated verified turn on a real receipt tape), not a hand-rolled stub.
// ═══════════════════════════════════════════════════════════════════════════════════
#[cfg(test)]
mod tests {
    use super::*;
    use deos_js::applet::{pack_u64, Affordance, Applet};
    use dregg_cell::AuthRequired;

    /// A two-slot applet: slot 0 = "a" (seed 10), slot 1 = "b" (seed 20). `incA` adds
    /// `arg` to slot 0 only — the SAME fixture shape `world_events_weld.rs` proves the
    /// AppletView path over.
    fn two_slot_applet(seed: u8) -> Applet {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let inc_a = Affordance {
            name: "incA".into(),
            required: AuthRequired::Signature,
            apply: Box::new(|model, arg| {
                let cur = model.field_u64(0);
                vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
            }),
        };
        Applet::mint(
            pk,
            [0u8; 32],
            &[(0usize, pack_u64(10)), (1usize, pack_u64(20))],
            vec![inc_a],
            AuthRequired::Signature,
        )
    }

    /// Two binds — binding 0 reads slot 0, binding 1 reads slot 1.
    fn two_bind_tree() -> ViewNode {
        ViewNode::VStack(vec![
            ViewNode::Bind {
                slot: 0,
                label: "a: ".into(),
                fmt: deos_view::BindFmt::Raw,
            },
            ViewNode::Bind {
                slot: 1,
                label: "b: ".into(),
                fmt: deos_view::BindFmt::Raw,
            },
        ])
    }

    /// A distinct, deterministic FOREIGN cell id (one the card's binds never read).
    fn foreign_cell() -> CellId {
        CellId::from_bytes([0xF0u8; 32])
    }

    /// A card over a shared embedded applet (the substance handle comes back so a
    /// test can fire turns directly on it — the rendered-button path).
    fn card_over(seed: u8) -> (Rc<RefCell<Applet>>, CardPane) {
        let shared = Rc::new(RefCell::new(two_slot_applet(seed)));
        let substance: CardSubstanceRef = shared.clone();
        let pane = CardPane::new_substance(substance, two_bind_tree(), "pulse-weld card");
        (shared, pane)
    }

    #[test]
    fn own_cell_world_event_matches_the_committed_turn_sugar() {
        let (shared, card) = card_over(0x61);
        let own = shared.borrow().cell();

        // The general entry point with the card's own cell = the sugar's dirty set.
        let dirty = card.on_world_events(&[(own, 0)]);
        assert_eq!(
            dirty,
            vec![BindingId(0)],
            "an own-cell world event dirties exactly the slot-0 binding"
        );
        assert_eq!(card.last_dirty(), vec![BindingId(0)]);
        assert_eq!(
            card.cached(BindingId(0)),
            Some(10),
            "the dirty binding re-read its live value into the cache"
        );
    }

    #[test]
    fn a_foreign_cell_event_dirties_nothing() {
        let (_shared, card) = card_over(0x62);

        // Prime both bindings (what a first paint does lazily).
        card.on_committed_turn(&[0, 1]);
        card.fade_glow();

        // THE BROADCAST GUARANTEE: the pump hands EVERY open card the beat's events;
        // a FieldSet on a cell this card's binds never read must invalidate nothing.
        let dirty = card.on_world_events(&[(foreign_cell(), 0), (foreign_cell(), 1)]);
        assert!(
            dirty.is_empty(),
            "a foreign cell's FieldSet must not over-invalidate this card"
        );
        assert!(
            card.glowing().is_empty(),
            "nothing glows on a foreign event"
        );
        assert_eq!(card.cached(BindingId(0)), Some(10), "cache untouched");
        assert_eq!(card.cached(BindingId(1)), Some(20), "cache untouched");
    }

    #[test]
    fn glow_is_the_per_beat_union_and_fades_once() {
        let (shared, card) = card_over(0x63);
        let own = shared.borrow().cell();

        // Two invalidation calls in ONE beat: the glow is their UNION; `last_dirty`
        // stays the LAST call's set.
        card.on_world_events(&[(own, 0)]);
        card.on_world_events(&[(own, 1)]);
        assert_eq!(
            card.glowing(),
            vec![BindingId(0), BindingId(1)],
            "the glow unions every dirty set since the last fade"
        );
        assert_eq!(
            card.last_dirty(),
            vec![BindingId(1)],
            "last_dirty is the per-call bar (the last call's set)"
        );

        // The host's next beat fades exactly once.
        assert!(
            card.fade_glow(),
            "something was glowing — repaint to un-tint"
        );
        assert!(card.glowing().is_empty(), "the glow retired");
        assert!(!card.fade_glow(), "a second fade on a quiet beat is free");
    }

    #[test]
    fn catch_up_own_turns_notices_a_directly_fired_turn_once() {
        let (shared, card) = card_over(0x64);

        // A still audit tape catches up to nothing (the common, free beat).
        assert!(card.catch_up_own_turns().is_empty(), "still tape → clean");

        // A rendered button's path: fire the affordance DIRECTLY on the shared
        // substance — one real cap-gated verified turn, named in no dynamics stream.
        shared
            .borrow_mut()
            .fire("incA", 5)
            .expect("incA commits a verified turn");

        // The catch-up sees the tape moved and (conservatively) invalidates the
        // cell's bindings — both re-read; the fresh slot-0 value lands in the cache.
        let dirty = card.catch_up_own_turns();
        assert_eq!(
            dirty,
            vec![BindingId(0), BindingId(1)],
            "the CellMutated-shaped tooth invalidates every binding of the card's cell"
        );
        assert_eq!(
            card.cached(BindingId(0)),
            Some(15),
            "slot 0 re-read 10 → 15"
        );
        assert_eq!(
            card.cached(BindingId(1)),
            Some(20),
            "slot 1 re-read (unchanged)"
        );
        assert_eq!(card.glowing(), vec![BindingId(0), BindingId(1)]);

        // The watermark advanced: the NEXT beat is clean again.
        assert!(
            card.catch_up_own_turns().is_empty(),
            "the same turn is never re-invalidated"
        );
    }

    #[test]
    fn mark_own_turns_seen_suppresses_the_conservative_catch_up() {
        let (shared, card) = card_over(0x65);
        let own = shared.borrow().cell();

        // The exact-fold path: the host fires the turn itself, folds the EXACT touched
        // slot through on_world_events, then marks the tape seen…
        shared
            .borrow_mut()
            .fire("incA", 3)
            .expect("incA commits a verified turn");
        let dirty = card.on_world_events(&[(own, 0)]);
        assert_eq!(
            dirty,
            vec![BindingId(0)],
            "exact invalidation, not cell-wide"
        );
        card.mark_own_turns_seen();

        // …so the next quiet beat does NOT re-invalidate the whole cell for it.
        assert!(
            card.catch_up_own_turns().is_empty(),
            "an exactly-folded own turn is not double-counted by the watermark"
        );
    }

    #[test]
    fn cell_wide_events_invalidate_conservatively_and_foreign_cells_stay_still() {
        // THE `CellMutated`/`CapabilityRevoked` FOLD — wave 3 left these events
        // unprojected; the registry's `invalidate_cell` tooth carries them now.
        let (shared, card) = card_over(0x66);
        let own = shared.borrow().cell();

        // Prime + settle (first-paint fill, then retire the glow).
        card.on_committed_turn(&[0, 1]);
        card.fade_glow();

        // A cell-wide event on a FOREIGN cell dirties nothing (the broadcast
        // guarantee holds for the conservative tooth too).
        assert!(
            card.on_world_cells(&[foreign_cell()]).is_empty(),
            "a foreign CellMutated must not over-invalidate this card"
        );
        assert!(card.glowing().is_empty());

        // Move slot 0 behind the cache's back (a real verified turn), then fold a
        // cell-wide event naming the card's OWN cell: EVERY binding of the cell
        // re-reads (never under-invalidating) and the fresh value lands.
        shared
            .borrow_mut()
            .fire("incA", 7)
            .expect("incA commits a verified turn");
        let dirty = card.on_world_cells(&[own]);
        assert_eq!(
            dirty,
            vec![BindingId(0), BindingId(1)],
            "an own-cell CellMutated invalidates every binding of the cell"
        );
        assert_eq!(
            card.cached(BindingId(0)),
            Some(17),
            "slot 0 re-read 10 → 17"
        );
        assert_eq!(
            card.glowing(),
            vec![BindingId(0), BindingId(1)],
            "the glow lit"
        );
    }

    #[test]
    fn the_bind_plan_registers_every_tabs_panel_in_declaration_order() {
        // The cursor-alignment bar: `tabs` registers EVERY panel's binds (render walks
        // all panels too, keeping only the selected element), so the Nth `bind` node
        // is `BindingId(n)` regardless of which tab is selected.
        let tree = ViewNode::VStack(vec![
            ViewNode::Bind {
                slot: 0,
                label: "before: ".into(),
                fmt: deos_view::BindFmt::Raw,
            },
            ViewNode::Tabs {
                tabs: vec!["one".into(), "two".into()],
                selected_slot: 5,
                select_turn: "select".into(),
                panels: vec![
                    ViewNode::Bind {
                        slot: 1,
                        label: "panel one: ".into(),
                        fmt: deos_view::BindFmt::Raw,
                    },
                    ViewNode::Bind {
                        slot: 2,
                        label: "panel two: ".into(),
                        fmt: deos_view::BindFmt::Raw,
                    },
                ],
            },
        ]);
        let mut slots = Vec::new();
        bind_plan(&tree, &mut slots);
        assert_eq!(
            slots,
            vec![0, 1, 2],
            "every panel's binds register, in declaration order"
        );
    }
}
