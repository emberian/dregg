//! The **view-tree model** — the Rust shape of the deos-js `deos.ui.*` element-tree.
//!
//! `deos-js` builds a *serializable* element-tree (data, NOT gpui) in real
//! SpiderMonkey: `deos.ui.{vstack,row,text,bind,button,input,list,table}`. A button's
//! `onClick` is `{turn, arg}`; a `bind(()=>expr)` is a fine-grained signal binding.
//! That JS object is `JSON.stringify`-ed by the engine and read back into Rust (see
//! [`crate::bridge`]); this module is the Rust mirror it parses into. The renderer
//! ([`crate::render`]) walks this tree into real gpui-component widgets.
//!
//! NOTE on `bind`: `JSON.stringify` drops the closure (`node.read` is a function), so
//! a serialized `bind` node carries only `kind:"bind"`. The renderer re-reads the
//! bound value off the live applet ledger directly (the binding IS `app.get(slot)`),
//! which is the same witnessed read the JS closure made — see [`ViewNode::Bind`].

use serde::Deserialize;

use crate::fmt::BindFmt;

/// A node of the view-tree, mirroring the JS `deos.ui.*` shape exactly.
///
/// The JS shape is `{ kind, props, children? , read? }`. We deserialize via the raw
/// [`RawNode`] (a faithful JSON mirror) and lift it into this typed enum so the
/// renderer matches on real variants.
#[derive(Debug, Clone)]
pub enum ViewNode {
    /// `vstack(...children)` → a vertical column (`v_flex`).
    VStack(Vec<ViewNode>),
    /// `row(...children)` → a horizontal row (`h_flex`).
    Row(Vec<ViewNode>),
    /// `text(s)` → a `Label`.
    Text(String),
    /// `bind(() => expr)` → a signal binding. The closure does not survive
    /// serialization; the renderer re-reads the bound value off the live ledger
    /// (the model slot the JS closure read). `slot` is the model slot to re-read
    /// (the counter shape binds slot 0); `label` is an optional prefix. `fmt` (the
    /// consumer-delight knob, `props.fmt`) chooses how the bound integer paints: the
    /// default [`BindFmt::Raw`] is the plain decimal (a counter stays `count: 1`), while
    /// `id`/`hash`/`amount` turn an opaque 20-digit key into a short friendly handle /
    /// truncated hex / grouped digits (see [`crate::fmt`]). Identical across all renderers.
    Bind {
        slot: usize,
        label: String,
        fmt: BindFmt,
    },
    /// `button(label, aff, arg)` → a `Button` whose onClick fires affordance `turn`
    /// with `arg` (a REAL cap-gated verified turn through the applet).
    Button {
        label: String,
        turn: String,
        arg: i64,
    },
    /// `input(viewKey)` → a text input bound to ephemeral view-state `bind_view`.
    ///
    /// EXTENDED (the richness expansion): the draft can feed a turn arg. When `fire_turn`
    /// is non-empty the field's committed draft is parsed into the `arg` of `fire_turn` on
    /// submit (Enter / a paired submit button); `submit_label` labels that button. An empty
    /// `fire_turn` keeps the legacy ephemeral-draft-only behaviour. Unlocks the
    /// `ServiceExplorer` arg rows, the `WebShell` URL bar, the predicate composer (input →
    /// verified turn).
    ///
    /// NATIVE/WEB PARITY: the editable field is live on the WEB renderer (a real
    /// `<input>` read on submit); the NATIVE renderer currently paints this
    /// display-only (a read-only label — no text-entry widget), so those unlocked
    /// surfaces are user-interactive on web but display/agent-driven on native until a
    /// native editable field lands. See `deos-view`'s `render` module doc (finding #17).
    Input {
        bind_view: String,
        /// The affordance the submitted draft fires (its `arg` is the parsed draft). Empty →
        /// a plain ephemeral draft field (no turn).
        fire_turn: String,
        /// The submit button's label (when `fire_turn` is set). Empty → a sensible default.
        submit_label: String,
    },
    /// `list(items)` → a vertical list of child nodes.
    List(Vec<ViewNode>),
    /// `table(rows)` → a table; each row is itself a node (a `row` of cells).
    Table(Vec<ViewNode>),

    // ── The RICHNESS EXPANSION (docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md) — growing the
    //    vocabulary toward native-cockpit parity so liberating a surface into a card is
    //    LOSSLESS. Batch 1: a container, an actuation+selection node, a bound visual, a leaf.
    /// `section(title, ...children)` → a titled, bordered container (the uniform "styled
    /// section"). `tag` selects a styling accent (the existing `props.tag` convention —
    /// `genuine`/`refusal`/…). Unlocks Organs, the Trust/Devtools blocks, every panel's
    /// `section_title` + bordered-box idiom.
    Section {
        title: String,
        tag: String,
        children: Vec<ViewNode>,
    },
    /// `tabs({tabs, selectedSlot, selectTurn}, ...panels)` → a tab-strip whose visible panel
    /// is bound to model slot `selected_slot`. A tab click fires `select_turn` with `arg =
    /// the tab index` (a REAL verified turn that writes the slot). Unlocks Lanes, Devtools,
    /// Moldable. The renderer walks ALL panels (keeping the bind cursor aligned) and displays
    /// only the selected one.
    Tabs {
        /// The tab labels, one per panel (in `panels` order).
        tabs: Vec<String>,
        /// The model slot holding the active tab index (read live each paint).
        selected_slot: usize,
        /// The affordance a tab click fires (`arg` is the clicked tab's index).
        select_turn: String,
        /// The tab bodies — one per label; only the selected one is displayed.
        panels: Vec<ViewNode>,
    },
    /// `gauge({slot, max, label})` → a bound progress / balance bar. The fill is
    /// `get_u64(slot) / max`, clamped to `[0,1]`. Reads its slot IMMEDIATE-MODE (it does not
    /// consume the tree-walk bind cursor — it is not a `Bind`). Unlocks `face_gauge`, the
    /// Time liveness bar, any "glow = activity" indicator.
    Gauge {
        slot: usize,
        max: u64,
        label: String,
    },
    /// `divider()` → a thin full-width horizontal rule (a groove / separator). A pure leaf.
    Divider,

    // ── The COMPOSITION KEYSTONE (docs/deos/CELL-HOSTED-VIEWTREE.md) — a cell is a
    //    first-class hostable COMPONENT whose committed heap stores its own evolving
    //    view-tree; `host` MOUNTS that whole tree here as a subtree. This is distinct from
    //    `bind` (reads ONE scalar value off `(cell, slot)`) and from value-transclusion (a
    //    value snapshot from another cell): `host` mounts an ENTIRE view-tree sourced from the
    //    hosted cell's committed heap. Hosted trees contain `host` nodes for OTHER cells →
    //    fractal recursion (cells-host-cells-host-view-trees, to arbitrary depth). ──
    /// `host(cellId)` → mount the hosted cell's WHOLE view-tree here, as a subtree.
    ///
    /// `cell` is the hosted cell's id (hex). `view` is the RESOLVED hosted view-tree:
    /// - `None` — an UNRESOLVED mount (a bare reference). The renderer paints an honest
    ///   `‹mount cell …: unresolved›` placeholder until [`resolve_mounts`] fills it from the
    ///   cell's committed heap (the cell-heap-as-view-source — see [`crate::mount`]).
    /// - `Some(tree)` — the resolved/provided subtree, mounted whole. A resolver emits this;
    ///   an author may also carry a pre-baked subtree inline (the first-cut provided source).
    ///
    /// `host` stays PURE DATA (a cell-id string + an optional resolved subtree, NO live
    /// `Applet`/`Ledger` handle) so the gpui-free + deos-js-free `web`/`discord` renderers
    /// walk the IDENTICAL resolved tree — the heap read happens OUTSIDE the IR, at the
    /// boundary, and the result is spliced back in. The hosted subtree participates in the
    /// SAME pre-order bind cursor (every renderer recurses `view` at the host's position).
    Host {
        cell: String,
        view: Option<Box<ViewNode>>,
    },

    // ── The RICHNESS EXPANSION batch 2 — the actuation crown + the rest of the §1 vocabulary
    //    (docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md). Each node carries its affordance(s) in the
    //    `{turn, arg}` shape so the cap-gated-verified-turn routing is reused unchanged; bound
    //    nodes name their `slot` and read it immediate-mode (no bind cursor). ──────────────────
    /// `grid({cols}, ...children)` → a wrapping spatial cell field. `cols` caps how many cells
    /// sit per row (0 → free wrap). Unlocks Wonder's glowing-cell grid, the desktop icon field,
    /// the Powerbox app tiles. Recurses children in declaration order (the bind cursor stays
    /// aligned).
    Grid {
        cols: usize,
        children: Vec<ViewNode>,
    },
    /// `breadcrumb({items})` → a navigation path joined by `→`. A crumb carrying a non-empty
    /// `turn` is clickable (fires a verified turn). Unlocks Time's metastack breadcrumb, the
    /// Docs transclusion path.
    Breadcrumb { items: Vec<Crumb> },
    /// `progress({value, max, label})` → a STATIC (literal-valued) progress bar — the non-bound
    /// gauge. Unlocks a swarm-member completion bar, a download tile.
    Progress { value: u64, max: u64, label: String },
    /// `pill({text, tag})` → a colored status badge (leaf). `tag` selects the semantic palette
    /// (`good`/`warn`/`bad`/`accent`/`muted`). Unlocks the cockpit's ubiquitous `pill(text,
    /// color)` — authority badges, LIVE/REVOKED chips, kind/lifecycle badges.
    ///
    /// LIVE variant (the static-pill cure): when `slot` is `Some` and `cases` is non-empty the
    /// pill reads its bound slot IMMEDIATE-MODE (like `gauge`, NOT a `Bind` — it consumes no
    /// bind cursor) and maps the live value to the matching case's `{label, tag}` — e.g. a
    /// phase slot → `0:"COMMIT"(warn) 1:"REVEAL"(accent) 2:"RESOLVED"(good)`. No case matches
    /// (or no slot) → the static `text`/`tag` fallback. So a status pill READS the cell instead
    /// of being a hard-coded word.
    Pill {
        text: String,
        tag: String,
        /// The model slot the live pill reads (immediate-mode); `None` → a static pill.
        slot: Option<usize>,
        /// The value→`{label, tag}` cases; the first whose `value` equals the live slot wins.
        cases: Vec<PillCase>,
    },
    /// `icon({glyph, tag})` → a glyph indicator (leaf), tinted by `tag`. Unlocks the Wonder ✦/○
    /// glow glyphs, the scrubber markers, the toggle ✓/○.
    Icon { glyph: String, tag: String },
    /// `menu({items})` → a right-click / context actuation menu — a list of `{label, turn, arg,
    /// enabled}` rows. A `!enabled` row is the cap tooth shown rather than hidden (a dimmed,
    /// non-firing row). Unlocks the `deos_desktop` right-click actuation list.
    Menu { items: Vec<MenuItem> },
    /// `halo({targetSlot, handles})` → the Pharo direct-manipulation handle-ring: a node carrying
    /// its handles, each a `{glyph, turn, arg, enabled}` affordance the renderer rings around the
    /// target (the compass-anchor geometry is renderer-side layout, not card data). A `!enabled`
    /// handle is cap-refused, shown dimmed. Unlocks `deos_desktop/halo.rs`.
    Halo {
        /// The slot whose object the ring floats on (informational; the geometry is the
        /// renderer's). 0 if unbound.
        target_slot: usize,
        handles: Vec<HaloHandle>,
    },
    /// `slider({slot, min, max, turn})` → a bound draggable value → seek turn. The thumb sits at
    /// `get_u64(slot)` (read immediate-mode); a drag fires `turn` with `arg = the chosen value`.
    /// Unlocks Time's rewind scrubber, Replay.
    Slider {
        slot: usize,
        min: u64,
        max: u64,
        turn: String,
    },
    /// `toggle({slot, onTurn, offTurn, glyphOn, glyphOff, label})` → an affordance checkbox. The
    /// glyph is `glyph_on` when `get_u64(slot) != 0` else `glyph_off`; a click fires `on_turn`
    /// when currently off, `off_turn` when currently on. Unlocks Share's cull toggles, any
    /// boolean affordance.
    Toggle {
        slot: usize,
        on_turn: String,
        off_turn: String,
        glyph_on: String,
        glyph_off: String,
        label: String,
    },
    /// `tile({handle, w, h})` → a card-referenced native paint region (the genuine ceiling). The
    /// card does NOT carry the pixels; it references an opaque host-resolved region (a Servo
    /// render, a video, a map). An unresolvable handle paints a labelled placeholder. Unlocks
    /// `WebShell`'s Servo render tile, any embedded native surface.
    Tile { handle: String, w: u32, h: u32 },

    /// **An ADEPT-ONLY wrapper (progressive disclosure).** Any node tagged `props.adept:true`
    /// lifts wrapped in this transparent marker — the "see the bones" detail (raw hashes, slot
    /// indices, internal fields) a newcomer should NOT see. [`disclose`] with [`Disclosure::Simple`]
    /// DROPS these (the clean 1990-delight projection); [`Disclosure::Adept`] UNWRAPS them (the
    /// Pharo moldable projection). A renderer handed an un-disclosed tree paints the inner node
    /// transparently, so the marker is invisible unless the disclosure filter acts on it. Two
    /// projections of ONE card — never two cards.
    Adept(Box<ViewNode>),
}

/// A `pill` value→word case — the live pill maps its bound slot value to this `{label, tag}`
/// (the first case whose `value` equals the slot wins). The cure for the static phase-word pill.
#[derive(Debug, Clone)]
pub struct PillCase {
    /// The slot value this case matches.
    pub value: u64,
    /// The word the pill shows when the live value matches (`COMMIT`/`REVEAL`/`RESOLVED`).
    pub label: String,
    /// The semantic palette tag for the matched word (`warn`/`accent`/`good`/…).
    pub tag: String,
}

/// **The disclosure projection of a card** — `simple` (the newcomer's clean view: friendly
/// labels, gauges, pills, breadcrumbs; raw hashes/slot-indices/internal fields HIDDEN) vs
/// `adept` (the Pharo "see the bones" view: everything shown). One card, two projections.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Disclosure {
    /// Hide [`ViewNode::Adept`]-marked detail — the clean, delightful default.
    #[default]
    Simple,
    /// Reveal everything — unwrap the adept-marked detail.
    Adept,
}

impl Disclosure {
    /// Lift a card/section `props.disclosure` string into a [`Disclosure`]. Unknown / absent →
    /// [`Disclosure::Simple`] (the clean default).
    pub fn from_prop(s: Option<&str>) -> Self {
        match s.unwrap_or("") {
            "adept" => Disclosure::Adept,
            _ => Disclosure::Simple,
        }
    }
}

/// **Apply progressive disclosure** — a pure pre-walk producing the projection of `tree` at
/// `level`, run BEFORE any renderer walk (and before `bind_plan`'s cursor walk), so the simple
/// and adept projections each have a self-consistent bind cursor (a dropped adept `bind` is
/// dropped in ALL renderers identically — the renderer-independence + bind-cursor invariants
/// hold). At [`Disclosure::Simple`] an [`ViewNode::Adept`] node (and its whole subtree) is
/// DROPPED; at [`Disclosure::Adept`] it is UNWRAPPED (the inner node kept). Either way the
/// result contains no `Adept` markers, so the renderers paint a clean tree.
pub fn disclose(tree: &ViewNode, level: Disclosure) -> ViewNode {
    // `None` ⇒ this node is dropped entirely (an adept node in the simple projection).
    fn rec(node: &ViewNode, level: Disclosure) -> Option<ViewNode> {
        match node {
            ViewNode::Adept(inner) => match level {
                Disclosure::Simple => None,
                Disclosure::Adept => rec(inner, level),
            },
            ViewNode::VStack(cs) => Some(ViewNode::VStack(kids(cs, level))),
            ViewNode::Row(cs) => Some(ViewNode::Row(kids(cs, level))),
            ViewNode::List(cs) => Some(ViewNode::List(kids(cs, level))),
            ViewNode::Table(cs) => Some(ViewNode::Table(kids(cs, level))),
            ViewNode::Section {
                title,
                tag,
                children,
            } => Some(ViewNode::Section {
                title: title.clone(),
                tag: tag.clone(),
                children: kids(children, level),
            }),
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                panels,
            } => Some(ViewNode::Tabs {
                tabs: tabs.clone(),
                selected_slot: *selected_slot,
                select_turn: select_turn.clone(),
                panels: kids(panels, level),
            }),
            ViewNode::Grid { cols, children } => Some(ViewNode::Grid {
                cols: *cols,
                children: kids(children, level),
            }),
            ViewNode::Host { cell, view } => Some(ViewNode::Host {
                cell: cell.clone(),
                view: view.as_ref().and_then(|v| rec(v, level)).map(Box::new),
            }),
            // Leaves: cloned through (no adept marker can hide inside — they hold DATA, not
            // `ViewNode` children).
            other => Some(other.clone()),
        }
    }
    fn kids(children: &[ViewNode], level: Disclosure) -> Vec<ViewNode> {
        children.iter().filter_map(|c| rec(c, level)).collect()
    }
    rec(tree, level).unwrap_or(ViewNode::VStack(Vec::new()))
}

/// A `breadcrumb` crumb — a path segment, optionally clickable (a non-empty `turn` fires a
/// verified turn carrying `arg`).
#[derive(Debug, Clone)]
pub struct Crumb {
    pub label: String,
    pub turn: String,
    pub arg: i64,
}

/// A `menu` row — a `{label, turn, arg}` actuation with a cap-tooth `enabled` flag (a disabled
/// row is shown dimmed, never hidden — the in-band refusal).
#[derive(Debug, Clone)]
pub struct MenuItem {
    pub label: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
}

/// A `halo` handle — a `{glyph, turn, arg}` affordance the renderer rings around the target,
/// with a cap-tooth `enabled` flag (a disabled handle is shown dimmed).
#[derive(Debug, Clone)]
pub struct HaloHandle {
    pub glyph: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
}

/// The raw JSON mirror of a `deos.ui.*` node (`{ kind, props, children }`). The
/// engine's `JSON.stringify(tree)` produces exactly this; we then [`RawNode::lift`]
/// it into the typed [`ViewNode`].
#[derive(Debug, Clone, Deserialize)]
pub struct RawNode {
    pub kind: String,
    #[serde(default)]
    pub props: RawProps,
    #[serde(default)]
    pub children: Vec<RawNode>,
}

/// The raw `props` bag — every field optional (a node uses only the ones for its kind).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct RawProps {
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    // The JS prelude (`deos.ui.button`) emits the camelCase key `onClick`; deserialize it
    // by that name (with the snake_case alias kept) so the affordance `{turn, arg}` the
    // engine produced survives the parse into BOTH renderers — the native `Button`'s
    // on_click AND the web `<button data-turn data-arg>`. Without the rename the engine's
    // `onClick` silently dropped to a `{turn:"", arg:0}` default.
    #[serde(default, rename = "onClick", alias = "on_click")]
    pub on_click: Option<RawOnClick>,
    #[serde(default, rename = "bindView", alias = "bind_view")]
    pub bind_view: Option<String>,
    /// For a `bind` node the renderer needs to know WHICH model slot to re-read.
    /// The JS closure isn't serializable, so the applet author tags the bind node's
    /// props with `slot` (the counter shape uses slot 0). Absent → slot 0. Also the
    /// model slot a `gauge` reads its fill ratio from.
    #[serde(default)]
    pub slot: Option<usize>,

    // ── The richness-expansion props (batch 1: section / tabs / gauge). Every field
    //    optional; a node reads only the ones for its kind (the raw `props` bag idiom). ──
    /// A `section`'s header title.
    #[serde(default)]
    pub title: Option<String>,
    /// A styling accent / disclosure tag (`section`, `pill`, …): the existing `props.tag`
    /// convention (`genuine`/`refusal`/…), reused by the disclosure filter.
    #[serde(default)]
    pub tag: Option<String>,
    /// A `gauge`'s denominator (the fill is `slot_value / max`, clamped to `[0,1]`).
    #[serde(default)]
    pub max: Option<u64>,
    /// A `tabs` node's tab labels, one per panel (camelCase `tabs`, snake alias).
    #[serde(default, alias = "tab_labels")]
    pub tabs: Option<Vec<String>>,
    /// A `tabs` node's model slot holding the active tab index (camelCase `selectedSlot`).
    #[serde(default, rename = "selectedSlot", alias = "selected_slot")]
    pub selected_slot: Option<usize>,
    /// A `tabs` node's select affordance (`arg` is the clicked tab index; camelCase).
    #[serde(default, rename = "selectTurn", alias = "select_turn")]
    pub select_turn: Option<String>,
    /// A `host` node's hosted cell id (hex) — the mount reference. The hosted cell's WHOLE
    /// view-tree is read from its committed heap and mounted here (see [`ViewNode::Host`]).
    #[serde(default, alias = "cellId")]
    pub cell: Option<String>,

    // ── batch-2 props (the actuation crown + the rest of §1). Every field optional; a node
    //    reads only the ones for its kind. ────────────────────────────────────────────────
    /// A `grid`'s column cap (cells per row; 0 → free wrap).
    #[serde(default)]
    pub cols: Option<usize>,
    /// A `menu`/`breadcrumb`'s rows (the `{label, turn, arg, enabled}` list).
    #[serde(default)]
    pub items: Option<Vec<RawItem>>,
    /// A `halo`'s handles (the `{glyph, turn, arg, enabled}` ring).
    #[serde(default)]
    pub handles: Option<Vec<RawItem>>,
    /// A `halo`'s target slot (the object the ring floats on; camelCase `targetSlot`).
    #[serde(default, rename = "targetSlot", alias = "target_slot")]
    pub target_slot: Option<usize>,
    /// A `progress`'s literal value (the non-bound gauge's fill numerator).
    #[serde(default)]
    pub value: Option<u64>,
    /// A `slider`'s minimum (the low end of the draggable range).
    #[serde(default)]
    pub min: Option<u64>,
    /// A single affordance `turn` (a `slider` seek; the `arg` is the chosen value).
    #[serde(default)]
    pub turn: Option<String>,
    /// A `toggle`'s on/off affordances (camelCase `onTurn`/`offTurn`).
    #[serde(default, rename = "onTurn", alias = "on_turn")]
    pub on_turn: Option<String>,
    #[serde(default, rename = "offTurn", alias = "off_turn")]
    pub off_turn: Option<String>,
    /// An `icon`'s glyph; a `toggle`'s on/off glyphs (camelCase `glyphOn`/`glyphOff`).
    #[serde(default)]
    pub glyph: Option<String>,
    #[serde(default, rename = "glyphOn", alias = "glyph_on")]
    pub glyph_on: Option<String>,
    #[serde(default, rename = "glyphOff", alias = "glyph_off")]
    pub glyph_off: Option<String>,
    /// An extended `input`'s submit affordance + button label (camelCase `fireTurn`/`submitLabel`).
    #[serde(default, rename = "fireTurn", alias = "fire_turn")]
    pub fire_turn: Option<String>,
    #[serde(default, rename = "submitLabel", alias = "submit_label")]
    pub submit_label: Option<String>,
    /// A `tile`'s host-side render-source handle + its pixel size.
    #[serde(default)]
    pub handle: Option<String>,
    #[serde(default)]
    pub w: Option<u32>,
    #[serde(default)]
    pub h: Option<u32>,

    // ── The CONSUMER-DELIGHT props (short-hash/avatar · value→word pill · disclosure). Every
    //    field optional; default behaviour is unchanged so existing cards are untouched. ──────
    /// A `bind`'s display format (`"id"|"key"|"hash"|"hex"|"amount"|"raw"`) — turns an opaque
    /// integer into a short friendly handle / hex / grouped digits. Absent → the plain decimal.
    #[serde(default)]
    pub fmt: Option<String>,
    /// A live `pill`'s value→`{label, tag}` cases (the first matching the bound `slot` wins).
    #[serde(default)]
    pub cases: Option<Vec<RawPillCase>>,
    /// `props.adept:true` tags a node (+ its subtree) as adept-only — hidden in the `simple`
    /// disclosure projection, revealed in `adept`. Absent/false → always shown.
    #[serde(default)]
    pub adept: Option<bool>,
    /// A card/section `props.disclosure` (`"simple"|"adept"`) — the projection hint a host reads
    /// via [`Disclosure::from_prop`] to choose which level to [`disclose`] before rendering.
    #[serde(default)]
    pub disclosure: Option<String>,
}

/// The raw `{value, label, tag}` mirror of a live `pill`'s case (the value→word mapping).
#[derive(Debug, Clone, Deserialize)]
pub struct RawPillCase {
    #[serde(default)]
    pub value: u64,
    #[serde(default)]
    pub label: String,
    #[serde(default)]
    pub tag: String,
}

/// A raw `{label?, glyph?, turn?, arg?, enabled?}` row — the JSON mirror of a `menu` item, a
/// `halo` handle, or a `breadcrumb` crumb (each node lifts only the fields it needs). `enabled`
/// defaults to `true` (a row is fireable unless the author/cap explicitly dims it).
#[derive(Debug, Clone, Deserialize)]
pub struct RawItem {
    #[serde(default)]
    pub label: String,
    #[serde(default)]
    pub glyph: String,
    #[serde(default)]
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
    #[serde(default = "raw_item_enabled_default")]
    pub enabled: bool,
}

/// A `RawItem`'s `enabled` defaults to `true` (a row fires unless explicitly dimmed by the cap).
fn raw_item_enabled_default() -> bool {
    true
}

/// `onClick = { turn, arg }` — the affordance a button fires.
#[derive(Debug, Clone, Deserialize)]
pub struct RawOnClick {
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
}

impl RawNode {
    /// Lift a raw JSON node into the typed [`ViewNode`]. An unknown kind renders as a
    /// labelled placeholder text (honest: the renderer shows what it could not map).
    pub fn lift(&self) -> ViewNode {
        let node = self.lift_inner();
        // Progressive disclosure: a `props.adept:true` node lifts wrapped in the transparent
        // [`ViewNode::Adept`] marker so [`disclose`] can drop/reveal it. Default (absent/false)
        // → the node is shown directly (no wrapper).
        if self.props.adept == Some(true) {
            ViewNode::Adept(Box::new(node))
        } else {
            node
        }
    }

    /// The kind-dispatch half of [`lift`] (before the adept wrapper is applied).
    fn lift_inner(&self) -> ViewNode {
        let kids = || self.children.iter().map(|c| c.lift()).collect::<Vec<_>>();
        match self.kind.as_str() {
            "vstack" => ViewNode::VStack(kids()),
            "row" => ViewNode::Row(kids()),
            "text" => ViewNode::Text(self.props.text.clone().unwrap_or_default()),
            "bind" => ViewNode::Bind {
                slot: self.props.slot.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
                fmt: BindFmt::from_prop(self.props.fmt.as_deref()),
            },
            "button" => {
                let oc = self.props.on_click.clone().unwrap_or(RawOnClick {
                    turn: String::new(),
                    arg: 0,
                });
                ViewNode::Button {
                    label: self.props.label.clone().unwrap_or_default(),
                    turn: oc.turn,
                    arg: oc.arg,
                }
            }
            "input" => ViewNode::Input {
                bind_view: self.props.bind_view.clone().unwrap_or_default(),
                fire_turn: self.props.fire_turn.clone().unwrap_or_default(),
                submit_label: self.props.submit_label.clone().unwrap_or_default(),
            },
            "list" => ViewNode::List(kids()),
            "table" => ViewNode::Table(kids()),
            "section" => ViewNode::Section {
                title: self.props.title.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
                children: kids(),
            },
            "tabs" => ViewNode::Tabs {
                tabs: self.props.tabs.clone().unwrap_or_default(),
                selected_slot: self.props.selected_slot.unwrap_or(0),
                select_turn: self.props.select_turn.clone().unwrap_or_default(),
                panels: kids(),
            },
            "gauge" => ViewNode::Gauge {
                slot: self.props.slot.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "divider" => ViewNode::Divider,
            "grid" => ViewNode::Grid {
                cols: self.props.cols.unwrap_or(0),
                children: kids(),
            },
            "breadcrumb" => ViewNode::Breadcrumb {
                items: self
                    .props
                    .items
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|i| Crumb {
                        label: i.label,
                        turn: i.turn,
                        arg: i.arg,
                    })
                    .collect(),
            },
            "progress" => ViewNode::Progress {
                value: self.props.value.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "pill" => ViewNode::Pill {
                text: self.props.text.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
                slot: self.props.slot,
                cases: self
                    .props
                    .cases
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|c| PillCase {
                        value: c.value,
                        label: c.label,
                        tag: c.tag,
                    })
                    .collect(),
            },
            "icon" => ViewNode::Icon {
                glyph: self.props.glyph.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
            },
            "menu" => ViewNode::Menu {
                items: self
                    .props
                    .items
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|i| MenuItem {
                        label: i.label,
                        turn: i.turn,
                        arg: i.arg,
                        enabled: i.enabled,
                    })
                    .collect(),
            },
            "halo" => ViewNode::Halo {
                target_slot: self.props.target_slot.unwrap_or(0),
                handles: self
                    .props
                    .handles
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|h| HaloHandle {
                        glyph: h.glyph,
                        turn: h.turn,
                        arg: h.arg,
                        enabled: h.enabled,
                    })
                    .collect(),
            },
            "slider" => ViewNode::Slider {
                slot: self.props.slot.unwrap_or(0),
                min: self.props.min.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                turn: self.props.turn.clone().unwrap_or_default(),
            },
            "toggle" => ViewNode::Toggle {
                slot: self.props.slot.unwrap_or(0),
                on_turn: self.props.on_turn.clone().unwrap_or_default(),
                off_turn: self.props.off_turn.clone().unwrap_or_default(),
                glyph_on: self.props.glyph_on.clone().unwrap_or_else(|| "✓".into()),
                glyph_off: self.props.glyph_off.clone().unwrap_or_else(|| "○".into()),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "tile" => ViewNode::Tile {
                handle: self.props.handle.clone().unwrap_or_default(),
                w: self.props.w.unwrap_or(0),
                h: self.props.h.unwrap_or(0),
            },
            // `host(cellId)` — a child (if present) is the provided/pre-baked hosted subtree;
            // no child = an UNRESOLVED mount (filled later from the cell heap by
            // [`resolve_mounts`]). At most one hosted subtree (a host mounts ONE cell's tree).
            "host" => ViewNode::Host {
                cell: self.props.cell.clone().unwrap_or_default(),
                view: self.children.first().map(|c| Box::new(c.lift())),
            },
            other => ViewNode::Text(format!("‹unmapped node: {other}›")),
        }
    }
}

/// A source of cells' hosted view-trees — the cell-heap-as-view-source seen abstractly. A
/// [`resolve_mounts`] walk asks it for the hosted view-tree of each [`ViewNode::Host`]'s
/// cell. The native [`crate::mount`] impl reads the tree out of the cell's committed heap;
/// tests / provided sources use an in-memory [`MapMountSource`]. Any
/// `Fn(&str) -> Option<ViewNode>` is a `MountSource` (the blanket impl below).
pub trait MountSource {
    /// The hosted view-tree of `cell` (hex id), or `None` if the cell hosts no tree (the
    /// host then stays an unresolved placeholder — honest, never a crash).
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode>;
}

impl<F: Fn(&str) -> Option<ViewNode>> MountSource for F {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self(cell)
    }
}

/// An in-memory `cell-id → hosted view-tree` source (a provided source / the test source).
#[derive(Debug, Default, Clone)]
pub struct MapMountSource(pub std::collections::BTreeMap<String, ViewNode>);

impl MapMountSource {
    /// Insert a cell's hosted view-tree (builder-style).
    pub fn with(mut self, cell: impl Into<String>, tree: ViewNode) -> Self {
        self.0.insert(cell.into(), tree);
        self
    }
}

impl MountSource for MapMountSource {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self.0.get(cell).cloned()
    }
}

/// Resolve a live `pill`'s display `(label, tag)` from its bound slot `value`: the first
/// [`PillCase`] whose `value` matches wins, else the static `(text, tag)` fallback. The one
/// helper every renderer calls so the value→word mapping is identical across them.
pub fn pill_display<'a>(
    text: &'a str,
    tag: &'a str,
    cases: &'a [PillCase],
    value: u64,
) -> (&'a str, &'a str) {
    for c in cases {
        if c.value == value {
            return (c.label.as_str(), c.tag.as_str());
        }
    }
    (text, tag)
}

/// The maximum mount DEPTH (`host` nesting) the resolver unfolds before fail-safing. Bounds
/// a huge-but-acyclic mount tree so it can never blow the stack (cycles are caught separately
/// by the visited-path check). 16 levels of cells-host-cells is far past any real surface.
///
/// DEPTH is only ONE amplification axis. A shallow-but-WIDE fan-out (a cell hosting `k` copies
/// of a child that itself hosts `k` grandchildren …) stays under this cap on every root-to-leaf
/// path yet unfolds `k^depth` mounts in total — the WIDTH×DEPTH work axis. That axis is bounded
/// separately by [`MAX_MOUNT_NODES`]; this constant alone is NOT a total-work fail-safe.
pub const MAX_MOUNT_DEPTH: usize = 16;

/// The maximum TOTAL number of `host` mounts the resolver unfolds in a single pass — the
/// WIDTH×DEPTH work budget that [`MAX_MOUNT_DEPTH`] (a per-descent, one-chain cap) cannot give.
///
/// [`MAX_MOUNT_DEPTH`] bounds a single root-to-leaf chain, and the visited-path check bounds
/// cycles — but neither bounds an *acyclic fan-out* graph. Craft distinct cells `c0..c15`
/// (never repeating on any path, so the cycle guard never fires; only 16 deep, so the depth
/// guard never fires) where each `ci` hosts a `vstack` of `k` `host(c{i+1})` nodes. Every
/// path is short and acyclic, yet the resolver unfolds `k + k² + … + k¹⁵ ≈ k¹⁵` mounts total
/// (`k = 8` → ~3.5e13), each cloning a subtree and — under the ledger source — re-reading and
/// re-parsing a cell blob: a render-time OOM/hang DoS from a victim card that host-mounts one
/// attacker-controlled cell.
///
/// This is the second, INDEPENDENT fail-safe: a single tally of host mounts unfolded across
/// the WHOLE pass (not per-chain), threaded through the recursion. Once the pass has spent its
/// whole budget every further `host` fail-safes to a `‹mount budget exceeded›` body — the
/// truncated subtree is still SHOWN (labelled, honest), never unfolded, never a hang. 4096 is
/// thousands of real cells past any authored surface yet forecloses the amplification cold.
pub const MAX_MOUNT_NODES: usize = 4096;

/// **Resolve every `host` mount against a [`MountSource`]** — the cell-hosted-view-tree
/// composition keystone. Walks `tree`, and for each [`ViewNode::Host`] fills its `view` from
/// the source's hosted tree for that cell (recursing into it so nested `host`s — fractal
/// cells-host-cells — resolve too). Returns a fully-resolved tree every renderer walks
/// identically.
///
/// FAIL-SAFE BY CONSTRUCTION (the recursion contract) — three independent bounds cover the
/// three amplification axes (self-reference, chain DEPTH, and total WIDTH×DEPTH work):
/// - **cycle** — a `host{cell}` naming a cell already on the mount path (self-host, or an
///   a→b→a cycle) resolves to a `‹mount cycle: …›` body inside the host frame (the cell is
///   still shown; only the self-reference is cut). Never an infinite unfold.
/// - **depth** — at [`MAX_MOUNT_DEPTH`] the resolver stops with a `‹mount depth exceeded›`
///   body (a huge acyclic *chain* can't blow the stack).
/// - **budget** — across the WHOLE pass at most [`MAX_MOUNT_NODES`] `host` mounts are unfolded;
///   past that every further mount stops with a `‹mount budget exceeded›` body. This is what
///   bounds an acyclic *fan-out* graph (short, non-cyclic paths that nonetheless unfold `kᵈ`
///   mounts) — the axis neither the cycle nor the depth guard can see. A huge fan-out truncates
///   (visibly, cheaply) rather than OOM/hanging the renderer.
/// - **source miss** — a cell the source can't supply stays `view: None` (the unresolved
///   placeholder). A `host` already carrying a `view` (provided/pre-baked) is recursed for
///   nested hosts but otherwise kept.
pub fn resolve_mounts(tree: &ViewNode, source: &dyn MountSource) -> ViewNode {
    let mut path: Vec<String> = Vec::new();
    // `budget` is the REMAINING total-work allowance for this pass — the shared tally of host
    // mounts still permitted to unfold, threaded (like `path`) through the whole recursion so a
    // fan-out reached via many sibling hosts draws down ONE global budget, not a fresh per-chain
    // one. Depleted → the width×depth amplification fail-safes to `‹mount budget exceeded›`.
    let mut budget: usize = MAX_MOUNT_NODES;
    resolve_rec(tree, source, &mut path, 0, &mut budget)
}

fn resolve_rec(
    node: &ViewNode,
    source: &dyn MountSource,
    path: &mut Vec<String>,
    depth: usize,
    budget: &mut usize,
) -> ViewNode {
    let recur =
        |children: &[ViewNode], path: &mut Vec<String>, budget: &mut usize| -> Vec<ViewNode> {
            children
                .iter()
                .map(|c| resolve_rec(c, source, path, depth, budget))
                .collect()
        };
    match node {
        ViewNode::Host { cell, view } => {
            // Cycle: this cell is already being mounted on the current path.
            if path.iter().any(|c| c == cell) {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text(format!("‹mount cycle: {cell}›")))),
                };
            }
            // Depth: a huge (acyclic) mount chain fail-safes rather than blowing the stack.
            if depth >= MAX_MOUNT_DEPTH {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text("‹mount depth exceeded›".into()))),
                };
            }
            // Budget: the WIDTH×DEPTH fail-safe. Cycle+depth bound one chain; this bounds the
            // TOTAL mounts unfolded across the whole pass, so an acyclic fan-out (short, cycle-
            // free paths that still amplify k^depth) truncates here instead of OOM/hanging. Each
            // mount that gets past cycle+depth spends one unit; at zero, stop (labelled, cheap).
            if *budget == 0 {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text("‹mount budget exceeded›".into()))),
                };
            }
            *budget -= 1;
            // The hosted subtree: the provided/pre-baked `view`, else the source's tree for
            // this cell. A miss leaves it unresolved (the honest placeholder).
            let hosted = match view {
                Some(v) => Some((**v).clone()),
                None => source.hosted_tree(cell),
            };
            let resolved = hosted.map(|h| {
                path.push(cell.clone());
                let r = resolve_rec(&h, source, path, depth + 1, budget);
                path.pop();
                Box::new(r)
            });
            ViewNode::Host {
                cell: cell.clone(),
                view: resolved,
            }
        }
        ViewNode::VStack(cs) => ViewNode::VStack(recur(cs, path, budget)),
        ViewNode::Row(cs) => ViewNode::Row(recur(cs, path, budget)),
        ViewNode::List(cs) => ViewNode::List(recur(cs, path, budget)),
        ViewNode::Table(cs) => ViewNode::Table(recur(cs, path, budget)),
        ViewNode::Section {
            title,
            tag,
            children,
        } => ViewNode::Section {
            title: title.clone(),
            tag: tag.clone(),
            children: recur(children, path, budget),
        },
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            panels,
        } => ViewNode::Tabs {
            tabs: tabs.clone(),
            selected_slot: *selected_slot,
            select_turn: select_turn.clone(),
            panels: recur(panels, path, budget),
        },
        // The `grid` container recurses its children (a child may host a cell), like the other
        // containers.
        ViewNode::Grid { cols, children } => ViewNode::Grid {
            cols: *cols,
            children: recur(children, path, budget),
        },
        // The adept-only wrapper is transparent to mount resolution — recurse the wrapped node
        // (it may host a cell) and keep the marker (disclosure runs separately).
        ViewNode::Adept(inner) => {
            ViewNode::Adept(Box::new(resolve_rec(inner, source, path, depth, budget)))
        }
        // Leaves carry no mounts — cloned through unchanged. (The actuation/indicator nodes hold
        // affordance/value DATA, not `ViewNode` children, so no mount can hide inside them.)
        ViewNode::Text(_)
        | ViewNode::Bind { .. }
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
        | ViewNode::Tile { .. } => node.clone(),
    }
}

/// Parse the engine's `JSON.stringify(viewTree)` string into a typed [`ViewNode`].
pub fn parse_view_tree(json: &str) -> Result<ViewNode, String> {
    let raw: RawNode = serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))?;
    Ok(raw.lift())
}

#[cfg(test)]
mod mount_tests {
    use super::*;

    /// A `host(cell)` with no child lifts to an UNRESOLVED mount (`view: None`).
    #[test]
    fn host_lifts_unresolved_from_bare_reference() {
        let tree =
            parse_view_tree(r#"{ "kind":"host", "props":{ "cell":"abcd" } }"#).expect("parse host");
        match tree {
            ViewNode::Host { cell, view } => {
                assert_eq!(cell, "abcd", "the host carries the cell ref");
                assert!(view.is_none(), "a bare host reference is unresolved");
            }
            _ => panic!("root is a host node"),
        }
    }

    /// `resolve_mounts` fills a host's `view` from the source — and recurses, so a FRACTAL
    /// 2-level nest (parent hosts child, child hosts grandchild) resolves end-to-end.
    #[test]
    fn resolve_mounts_unfolds_a_fractal_two_level_nest() {
        let grandchild = ViewNode::Section {
            title: "G".into(),
            tag: String::new(),
            children: vec![ViewNode::Text("grandchild leaf".into())],
        };
        // The child hosts the grandchild (a host node inside the child's own tree).
        let child = ViewNode::Section {
            title: "C".into(),
            tag: String::new(),
            children: vec![
                ViewNode::Text("child body".into()),
                ViewNode::Host {
                    cell: "gc".into(),
                    view: None,
                },
            ],
        };
        let source = MapMountSource::default()
            .with("child", child)
            .with("gc", grandchild);
        let parent = ViewNode::VStack(vec![
            ViewNode::Text("parent".into()),
            ViewNode::Host {
                cell: "child".into(),
                view: None,
            },
        ]);

        let resolved = resolve_mounts(&parent, &source);
        // Walk down: parent → host(child) → child Section → host(gc) → grandchild Section.
        let ViewNode::VStack(top) = &resolved else {
            panic!("root vstack")
        };
        let ViewNode::Host {
            view: Some(child_v),
            ..
        } = &top[1]
        else {
            panic!("host(child) resolved")
        };
        let ViewNode::Section {
            children: child_kids,
            ..
        } = &**child_v
        else {
            panic!("child is a section")
        };
        let ViewNode::Host {
            view: Some(gc_v), ..
        } = &child_kids[1]
        else {
            panic!("host(gc) resolved INSIDE the child — the fractal nest")
        };
        let ViewNode::Section {
            title: gc_title, ..
        } = &**gc_v
        else {
            panic!("grandchild is a section")
        };
        assert_eq!(gc_title, "G", "the grandchild tree mounted two levels deep");
    }

    /// A cell hosting ITSELF is caught — the resolver fail-safes to a cycle placeholder
    /// rather than unfolding forever.
    #[test]
    fn resolve_mounts_breaks_a_self_cycle() {
        // `loop` hosts a tree that hosts `loop` again.
        let looping = ViewNode::Host {
            cell: "loop".into(),
            view: None,
        };
        let source = MapMountSource::default().with("loop", looping.clone());
        let resolved = resolve_mounts(&looping, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("the outer host resolved once")
        };
        // Its body is the inner host(loop), which is a CYCLE — its body is the placeholder.
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("inner host present")
        };
        match &**inner {
            ViewNode::Text(t) => assert!(t.contains("mount cycle"), "self-cycle is cut: {t}"),
            _ => panic!("the self-cycle resolves to the cycle placeholder"),
        }
    }

    /// A mutual a→b→a cycle is caught the same way (the visited PATH, not just self).
    #[test]
    fn resolve_mounts_breaks_a_mutual_cycle() {
        let a = ViewNode::Host {
            cell: "b".into(),
            view: None,
        };
        let b = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        let source = MapMountSource::default().with("a", a).with("b", b);
        let root = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        // Just terminating (no stack overflow / hang) + producing a tree is the property.
        let resolved = resolve_mounts(&root, &source);
        let rendered = format!("{resolved:?}");
        assert!(
            rendered.contains("mount cycle"),
            "the mutual cycle is cut with a placeholder"
        );
    }

    /// A pre-baked (provided) `view` is kept AND recursed for nested hosts.
    #[test]
    fn resolve_mounts_keeps_and_recurses_a_provided_subtree() {
        let provided = ViewNode::Host {
            cell: "outer".into(),
            view: Some(Box::new(ViewNode::Host {
                cell: "inner".into(),
                view: None,
            })),
        };
        let source =
            MapMountSource::default().with("inner", ViewNode::Text("inner resolved".into()));
        let resolved = resolve_mounts(&provided, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("outer kept its provided view")
        };
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("the nested host inside the provided subtree was visited")
        };
        assert!(
            matches!(&**inner, ViewNode::Text(t) if t == "inner resolved"),
            "the nested host inside a provided subtree resolved from the source"
        );
    }

    /// Walk a resolved tree and tally, at each `host`, which of the three fail-safe placeholders
    /// (or a genuine unfold) it landed on. `unfolded` counts hosts whose body is real resolved
    /// content — i.e. one drawn-down unit of the [`MAX_MOUNT_NODES`] budget.
    #[derive(Default)]
    struct MountTally {
        unfolded: usize,
        budget_markers: usize,
        depth_markers: usize,
        cycle_markers: usize,
    }

    fn tally_mounts(node: &ViewNode, t: &mut MountTally) {
        match node {
            ViewNode::Host { view: Some(v), .. } => {
                match &**v {
                    ViewNode::Text(s) if s.contains("mount budget exceeded") => {
                        t.budget_markers += 1
                    }
                    ViewNode::Text(s) if s.contains("mount depth exceeded") => t.depth_markers += 1,
                    ViewNode::Text(s) if s.contains("mount cycle") => t.cycle_markers += 1,
                    // A genuine unfold (any real resolved body, incl. a non-marker leaf).
                    other => {
                        t.unfolded += 1;
                        tally_mounts(other, t);
                    }
                }
            }
            ViewNode::Host { view: None, .. } => {}
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                cs.iter().for_each(|c| tally_mounts(c, t))
            }
            ViewNode::Section { children, .. } => children.iter().for_each(|c| tally_mounts(c, t)),
            ViewNode::Tabs { panels, .. } => panels.iter().for_each(|c| tally_mounts(c, t)),
            ViewNode::Grid { children, .. } => children.iter().for_each(|c| tally_mounts(c, t)),
            ViewNode::Adept(inner) => tally_mounts(inner, t),
            _ => {}
        }
    }

    /// **The SCALING fail-safe (CORE-AUDIT #8).** An *acyclic fan-out* mount graph — distinct
    /// cells `c0..c{N}` where each hosts a `vstack` of `k` `host(c{i+1})` — trips NEITHER the
    /// cycle guard (no cell repeats on any path) NOR the depth guard (every path is well under
    /// [`MAX_MOUNT_DEPTH`]), yet without a total-work budget it would unfold `k + k² + … ≈ kᴺ`
    /// mounts (`k = 8`, N = 12 → ~6.9e10) and OOM/hang the renderer. [`MAX_MOUNT_NODES`] bounds
    /// the TOTAL unfolds: the pass terminates promptly, the work is capped at the budget, and the
    /// truncated subtrees carry a VISIBLE `‹mount budget exceeded›` marker — while the pre-existing
    /// depth marker never fires, proving it is the NEW width×depth axis that bounded this.
    #[test]
    fn resolve_mounts_bounds_an_acyclic_fan_out_to_the_node_budget() {
        // `k` well above 1 and `levels` well below MAX_MOUNT_DEPTH: the graph is short and
        // cycle-free on every path, so only the node budget can bound it.
        let k = 8usize;
        let levels = 12usize;
        assert!(
            levels < MAX_MOUNT_DEPTH,
            "stays under the depth cap on every path"
        );

        // Cell `c{i}` hosts a vstack of `k` `host(c{i+1})`; the leaf cell hosts a plain text so a
        // fully-unfolded path has an honest terminus. No cell id repeats on any root-to-leaf path.
        let mut source = MapMountSource::default();
        for i in 0..levels {
            let child = format!("c{}", i + 1);
            let fan = ViewNode::VStack(
                (0..k)
                    .map(|_| ViewNode::Host {
                        cell: child.clone(),
                        view: None,
                    })
                    .collect(),
            );
            source = source.with(format!("c{i}"), fan);
        }
        source = source.with(format!("c{levels}"), ViewNode::Text("leaf".into()));

        // A victim card that host-mounts ONE attacker-controlled cell. Without the budget this
        // resolve would attempt ~kᴺ unfolds; with it, it returns promptly.
        let root = ViewNode::Host {
            cell: "c0".into(),
            view: None,
        };
        let resolved = resolve_mounts(&root, &source);

        let mut t = MountTally::default();
        tally_mounts(&resolved, &mut t);

        // Bounded to the budget — the total-WORK cap the depth guard alone cannot give.
        assert!(
            t.unfolded <= MAX_MOUNT_NODES,
            "unfolds ({}) bounded by the node budget ({MAX_MOUNT_NODES})",
            t.unfolded,
        );
        // The cap actually ENGAGED (this graph vastly exceeds it) and the budget was fully spent.
        assert_eq!(
            t.unfolded, MAX_MOUNT_NODES,
            "the fan-out is huge, so exactly the whole budget is spent before truncation",
        );
        // The truncation is VISIBLE — the honest labelled placeholder, never a silent hang.
        assert!(
            t.budget_markers > 0,
            "the truncated subtrees carry a visible ‹mount budget exceeded› marker",
        );
        // It is the WIDTH×DEPTH axis (the new guard) that bounded this, NOT the pre-existing
        // depth cap: every path is shallow, so no depth marker is ever emitted.
        assert_eq!(
            t.depth_markers, 0,
            "the depth guard never fires — the node budget is what bounded the fan-out",
        );
        assert_eq!(t.cycle_markers, 0, "an acyclic graph trips no cycle guard");
    }

    /// A single ultra-WIDE level (one cell hosting `MAX_MOUNT_NODES + spill` sibling mounts)
    /// exercises the budget on the width axis exactly: the first `MAX_MOUNT_NODES` mounts unfold
    /// (the root host + its children), and every sibling past the budget is truncated — an exact,
    /// off-by-one-proof witness that the tally is a hard cap, not a soft heuristic.
    #[test]
    fn resolve_mounts_budget_caps_a_single_wide_level_exactly() {
        let spill = 64usize;
        let width = MAX_MOUNT_NODES + spill;
        // `wide` hosts `width` copies of `host(leaf)`; `leaf` hosts a plain text.
        let fan = ViewNode::VStack(
            (0..width)
                .map(|_| ViewNode::Host {
                    cell: "leaf".into(),
                    view: None,
                })
                .collect(),
        );
        let source = MapMountSource::default()
            .with("wide", fan)
            .with("leaf", ViewNode::Text("leaf".into()));
        let root = ViewNode::Host {
            cell: "wide".into(),
            view: None,
        };
        let resolved = resolve_mounts(&root, &source);

        let mut t = MountTally::default();
        tally_mounts(&resolved, &mut t);
        // `wide` (1 unfold) + the first (MAX_MOUNT_NODES - 1) leaf mounts = MAX_MOUNT_NODES unfolds.
        assert_eq!(
            t.unfolded, MAX_MOUNT_NODES,
            "exactly the budget's worth unfold"
        );
        // The `spill + 1` siblings beyond the budget are all truncated with the visible marker.
        assert_eq!(
            t.budget_markers,
            width - (MAX_MOUNT_NODES - 1),
            "every sibling past the budget carries the truncation marker",
        );
    }
}

#[cfg(test)]
mod batch2_lift_tests {
    //! The richness-expansion batch-2 nodes lift from their `{kind, props, children}` wire shape
    //! into the typed [`ViewNode`] (the serde round-trip on the new `RawProps` fields), and a
    //! `grid` recurses through [`resolve_mounts`] so a hosted cell nested in a grid still mounts.
    use super::*;

    #[test]
    fn the_actuation_and_indicator_nodes_lift_from_the_wire() {
        // menu — a list of {label, turn, arg, enabled} rows; `enabled` defaults to true.
        let menu = parse_view_tree(
            r#"{ "kind":"menu", "props":{ "items":[
                 { "label":"Open", "turn":"open", "arg":1 },
                 { "label":"Delete", "turn":"del", "arg":2, "enabled":false } ] } }"#,
        )
        .expect("parse menu");
        let ViewNode::Menu { items } = &menu else {
            panic!("root is a menu")
        };
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].turn, "open");
        assert!(items[0].enabled, "absent enabled defaults true");
        assert!(!items[1].enabled, "an explicit enabled:false dims the row");

        // halo — a ring of {glyph, turn, arg} handles around a target slot.
        let halo = parse_view_tree(
            r#"{ "kind":"halo", "props":{ "targetSlot":3, "handles":[
                 { "glyph":"✕", "turn":"close", "arg":0 },
                 { "glyph":"⤢", "turn":"resize", "arg":0, "enabled":false } ] } }"#,
        )
        .expect("parse halo");
        let ViewNode::Halo {
            target_slot,
            handles,
        } = &halo
        else {
            panic!("root is a halo")
        };
        assert_eq!(*target_slot, 3);
        assert_eq!(handles.len(), 2);
        assert_eq!(handles[0].glyph, "✕");
        assert!(!handles[1].enabled);

        // slider — a bound draggable value firing `turn` with `arg = value`.
        let slider = parse_view_tree(
            r#"{ "kind":"slider", "props":{ "slot":2, "min":0, "max":99, "turn":"seek" } }"#,
        )
        .expect("parse slider");
        assert!(matches!(
            slider,
            ViewNode::Slider { slot: 2, min: 0, max: 99, ref turn } if turn == "seek"
        ));

        // toggle — defaults the glyphs to ✓/○ when absent.
        let toggle = parse_view_tree(
            r#"{ "kind":"toggle", "props":{ "slot":4, "onTurn":"on", "offTurn":"off", "label":"cull " } }"#,
        )
        .expect("parse toggle");
        let ViewNode::Toggle {
            slot,
            on_turn,
            off_turn,
            glyph_on,
            glyph_off,
            label,
        } = &toggle
        else {
            panic!("root is a toggle")
        };
        assert_eq!(
            (*slot, on_turn.as_str(), off_turn.as_str()),
            (4, "on", "off")
        );
        assert_eq!((glyph_on.as_str(), glyph_off.as_str()), ("✓", "○"));
        assert_eq!(label, "cull ");

        // breadcrumb / progress / pill / icon / tile + the extended input.
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"progress", "props":{ "value":3, "max":4, "label":"build " } }"#).unwrap(),
            ViewNode::Progress { value: 3, max: 4, ref label } if label == "build "
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"pill", "props":{ "text":"LIVE", "tag":"good" } }"#).unwrap(),
            ViewNode::Pill { ref text, ref tag, .. } if text == "LIVE" && tag == "good"
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"icon", "props":{ "glyph":"✦", "tag":"accent" } }"#).unwrap(),
            ViewNode::Icon { ref glyph, ref tag } if glyph == "✦" && tag == "accent"
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"tile", "props":{ "handle":"servo:webview-1", "w":640, "h":480 } }"#).unwrap(),
            ViewNode::Tile { ref handle, w: 640, h: 480 } if handle == "servo:webview-1"
        ));
        let bc = parse_view_tree(
            r#"{ "kind":"breadcrumb", "props":{ "items":[
                 { "label":"BASE", "turn":"seek", "arg":0 }, { "label":"now" } ] } }"#,
        )
        .unwrap();
        let ViewNode::Breadcrumb { items } = &bc else {
            panic!("root is a breadcrumb")
        };
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].turn, "seek");
        assert!(items[1].turn.is_empty(), "a plain crumb has no turn");

        // the extended input carries its submit affordance.
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"input", "props":{ "bindView":"url", "fireTurn":"navigate", "submitLabel":"Go" } }"#).unwrap(),
            ViewNode::Input { ref bind_view, ref fire_turn, ref submit_label }
                if bind_view == "url" && fire_turn == "navigate" && submit_label == "Go"
        ));
        // a plain input keeps the legacy ephemeral-draft shape (empty fire_turn).
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"input", "props":{ "bindView":"draft" } }"#).unwrap(),
            ViewNode::Input { ref fire_turn, .. } if fire_turn.is_empty()
        ));
    }

    #[test]
    fn a_section_lifts_from_the_authoring_mirror_wire_shape() {
        // The EXACT shape a deos-js `card_editor::ViewTree::Section` serializes to (a
        // `{kind:"section", props:{title,tag}, children:[…]}`), as the proofs/organs/home
        // cards emit — proving the authoring-mirror extension bridges losslessly into the
        // renderer's `ViewNode::Section`.
        let tree = parse_view_tree(
            r#"{ "kind":"section", "props":{ "title":"TRUSTLINES (live)", "tag":"good" },
                 "children":[ { "kind":"text", "props":{ "text":"⬡ ab12" } },
                              { "kind":"pill", "props":{ "text":"LIVE", "tag":"good" } } ] }"#,
        )
        .expect("parse section");
        let ViewNode::Section {
            title,
            tag,
            children,
        } = &tree
        else {
            panic!("root is a section")
        };
        assert_eq!(title, "TRUSTLINES (live)");
        assert_eq!(tag, "good");
        assert_eq!(children.len(), 2, "the section carries its children");
        assert!(matches!(&children[1], ViewNode::Pill { text, .. } if text == "LIVE"));
    }

    #[test]
    fn a_grid_recurses_a_hosted_cell_through_resolve_mounts() {
        let grid = ViewNode::Grid {
            cols: 3,
            children: vec![
                ViewNode::Icon {
                    glyph: "✦".into(),
                    tag: String::new(),
                },
                ViewNode::Host {
                    cell: "tile".into(),
                    view: None,
                },
            ],
        };
        let source =
            MapMountSource::default().with("tile", ViewNode::Text("mounted in a grid".into()));
        let resolved = resolve_mounts(&grid, &source);
        let ViewNode::Grid { cols, children } = &resolved else {
            panic!("root is a grid")
        };
        assert_eq!(*cols, 3);
        let ViewNode::Host { view: Some(v), .. } = &children[1] else {
            panic!("the grid's host child resolved")
        };
        assert!(matches!(&**v, ViewNode::Text(t) if t == "mounted in a grid"));
    }
}

#[cfg(test)]
mod delight_tests {
    //! The CONSUMER-DELIGHT layer: a `bind`'s `fmt`, a LIVE value→word `pill`, and progressive
    //! disclosure — all lifting from the wire shape and behaving at the IR level (renderer-
    //! independent, so every renderer inherits them).
    use super::*;

    #[test]
    fn a_bind_lifts_its_display_fmt() {
        // The identity key shows a friendly avatar instead of a 20-digit decimal.
        let id = parse_view_tree(
            r#"{ "kind":"bind", "props":{ "slot":3, "label":"seller · ", "fmt":"id" } }"#,
        )
        .expect("parse id bind");
        assert!(matches!(
            id,
            ViewNode::Bind {
                slot: 3,
                fmt: BindFmt::Id,
                ..
            }
        ));
        // The aliases all map; an absent fmt stays Raw (the unchanged default).
        for (p, want) in [
            ("\"hash\"", BindFmt::Hex),
            ("\"hex\"", BindFmt::Hex),
            ("\"key\"", BindFmt::Id),
            ("\"amount\"", BindFmt::Amount),
        ] {
            let j = format!(r#"{{ "kind":"bind", "props":{{ "slot":0, "fmt":{p} }} }}"#);
            let ViewNode::Bind { fmt, .. } = parse_view_tree(&j).unwrap() else {
                panic!("a bind")
            };
            assert_eq!(fmt, want, "fmt {p}");
        }
        let plain = parse_view_tree(r#"{ "kind":"bind", "props":{ "slot":0 } }"#).unwrap();
        assert!(
            matches!(
                plain,
                ViewNode::Bind {
                    fmt: BindFmt::Raw,
                    ..
                }
            ),
            "default stays raw"
        );
    }

    #[test]
    fn a_live_pill_lifts_slot_and_maps_the_value_to_a_word() {
        let pill = parse_view_tree(
            r#"{ "kind":"pill", "props":{ "text":"…", "tag":"muted", "slot":7, "cases":[
                 { "value":0, "label":"COMMIT", "tag":"warn" },
                 { "value":1, "label":"REVEAL", "tag":"accent" },
                 { "value":2, "label":"RESOLVED", "tag":"good" } ] } }"#,
        )
        .expect("parse live pill");
        let ViewNode::Pill {
            text,
            tag,
            slot,
            cases,
        } = &pill
        else {
            panic!("a pill")
        };
        assert_eq!(*slot, Some(7));
        assert_eq!(cases.len(), 3);
        // The live value picks the word + color — NOT a frozen label.
        assert_eq!(pill_display(text, tag, cases, 0), ("COMMIT", "warn"));
        assert_eq!(pill_display(text, tag, cases, 1), ("REVEAL", "accent"));
        assert_eq!(pill_display(text, tag, cases, 2), ("RESOLVED", "good"));
        // An out-of-range value falls back to the static text/tag (honest, never a crash).
        assert_eq!(pill_display(text, tag, cases, 9), ("…", "muted"));
    }

    #[test]
    fn a_static_pill_is_unchanged() {
        let pill = parse_view_tree(r#"{ "kind":"pill", "props":{ "text":"LIVE", "tag":"good" } }"#)
            .unwrap();
        assert!(matches!(&pill, ViewNode::Pill { slot: None, .. }));
        let ViewNode::Pill {
            text, tag, cases, ..
        } = &pill
        else {
            panic!()
        };
        assert!(cases.is_empty());
        assert_eq!(pill_display(text, tag, cases, 42), ("LIVE", "good"));
    }

    #[test]
    fn an_adept_node_lifts_wrapped() {
        let n = parse_view_tree(
            r#"{ "kind":"bind", "props":{ "slot":1, "label":"raw hash · ", "fmt":"hash", "adept":true } }"#,
        )
        .unwrap();
        let ViewNode::Adept(inner) = &n else {
            panic!("adept-tagged node wraps")
        };
        assert!(matches!(&**inner, ViewNode::Bind { slot: 1, .. }));
    }

    #[test]
    fn disclosure_simple_hides_adept_detail_and_adept_reveals_it() {
        // A header bind (friendly) + an adept-only raw-hash bind. Simple shows ONE; adept shows BOTH.
        let card = parse_view_tree(
            r#"{ "kind":"vstack", "props":{}, "children":[
                 { "kind":"bind", "props":{ "slot":0, "label":"seller · ", "fmt":"id" } },
                 { "kind":"bind", "props":{ "slot":0, "label":"raw · ", "adept":true } } ] }"#,
        )
        .unwrap();

        let simple = disclose(&card, Disclosure::Simple);
        let ViewNode::VStack(s) = &simple else {
            panic!("vstack")
        };
        assert_eq!(s.len(), 1, "simple drops the adept bind");
        assert!(
            !format!("{simple:?}").contains("Adept"),
            "no markers leak into the rendered tree"
        );

        let adept = disclose(&card, Disclosure::Adept);
        let ViewNode::VStack(a) = &adept else {
            panic!("vstack")
        };
        assert_eq!(a.len(), 2, "adept reveals both binds");
        assert!(
            !format!("{adept:?}").contains("Adept"),
            "adept unwraps the marker"
        );
    }

    #[test]
    fn disclosure_keeps_a_self_consistent_bind_cursor() {
        // Dropping an adept `bind` shifts the surviving binds' positions identically in every
        // renderer (the filter runs before the cursor walk), so the projection is coherent.
        let card = parse_view_tree(
            r#"{ "kind":"vstack", "props":{}, "children":[
                 { "kind":"bind", "props":{ "slot":5 } },
                 { "kind":"bind", "props":{ "slot":6, "adept":true } },
                 { "kind":"bind", "props":{ "slot":7 } } ] }"#,
        )
        .unwrap();
        fn slots(n: &ViewNode, out: &mut Vec<usize>) {
            match n {
                ViewNode::Bind { slot, .. } => out.push(*slot),
                ViewNode::VStack(cs) => cs.iter().for_each(|c| slots(c, out)),
                ViewNode::Adept(i) => slots(i, out),
                _ => {}
            }
        }
        let mut simple = Vec::new();
        slots(&disclose(&card, Disclosure::Simple), &mut simple);
        assert_eq!(
            simple,
            vec![5, 7],
            "simple binds in pre-order, adept slot 6 dropped"
        );
        let mut adept = Vec::new();
        slots(&disclose(&card, Disclosure::Adept), &mut adept);
        assert_eq!(adept, vec![5, 6, 7], "adept keeps all three in pre-order");
    }
}
