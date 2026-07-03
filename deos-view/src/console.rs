//! **THE DREGG COMPUTER DASHBOARD** — "My Dregg Computer" through the deos-view
//! `ViewNode` IR: one dashboard model, many faces (native gpui · web · the graphideOS
//! phone). This is NOT a terminal (that is alacritty, in the zed bundle) — it is the
//! "my stuff" home: your Dregg Computers, your hermeses, spend, and verify.
//!
//! ## Why an IR dashboard (not HTML strings, not a terminal)
//!
//! A dashboard rendered as server-side HTML strings is web-only by construction: the
//! markup IS the surface, so there is no native face, no phone face, and no way for the
//! cockpit to mount "my computers" as a card. THIS dashboard is a pure, serializable
//! [`ViewNode`] tree — the identical IR the native gpui renderer (`crate::render`,
//! feature `native`), the web renderer (`crate::web`), and the discord renderer
//! (`crate::discord`) already walk. Build the card once, and the graphideOS phone (dregg
//! as the upper half of userspace) gets the dashboard for free: it is just a fourth
//! walker over the same tree. One model, four faces.
//!
//! ## The source of truth is OUR cells
//!
//! The view models here ([`VatView`], [`HermesView`], …) are dregg-native — their source
//! of truth is the live World, not any external service:
//!
//! | view model                    | native source of truth                                          |
//! |-------------------------------|-----------------------------------------------------------------|
//! | [`VatView`]                   | the vat cell — `cell_id` (content-addressed from you+app+name), lifecycle = checkpoint/wake, `endpoint` + `witness` = the vat's own lease terms (DREGG-COMPUTER.md) |
//! | [`VatView::settled_units`] / [`VatView::headroom_units`] | the vat's `execution-lease` StandingObligation (periods × per-period; budget − settled, floored) |
//! | [`HermesView`]                | a living resident: `starbridge-v2/src/hireling.rs` (the hire weld) + `agent_memory.rs` (checkpoint/resume) — a persistent/resumable hermes, not a one-shot deploy report |
//! | [`HermesView::mandate`]       | `starbridge-v2/src/agent.rs` mandate edges + the CAN/CANNOT boundary (read off the live World, never self-report) |
//! | [`SpendLine`] / [`LedgerView`]| the $DREGG cells (balance + spend, conserving) |
//! | [`ConsoleModel::scoped_to`]   | a resource is shown iff its owner-cap subject == the viewer (the capability the viewer holds) |
//!
//! (Historical note: this dashboard's shape was strip-mined from the retired DreggNet
//! `console/` before that repo was abandoned — the LOGIC was ported, made dregg-native,
//! and re-anchored on cells. There is no dependency on, and no future weld back to, that
//! repo; it is gone. Units are clamped to `u64` here — a negative meter reading is a bug,
//! not a renderable quantity.)
//!
//! ## LIVE-BIND DISCIPLINE (how one static model becomes a live card)
//!
//! Three node kinds read the model at paint time, two disciplines:
//!
//! * [`ViewNode::Bind`] consumes the pre-order BIND CURSOR — [`console_bind_values`]
//!   returns the values in exactly that order (the web renderer's `BindValues` contract;
//!   the native renderer re-reads the same slots off the live applet ledger).
//! * [`ViewNode::Gauge`] and the live [`ViewNode::Pill`] read their `slot`
//!   IMMEDIATE-MODE (no cursor). [`console_slot_seeds`] lists every `(slot, value)` a
//!   live executor must seed so the live card agrees with the snapshot.
//!
//! **The `0 = as-baked` pill convention:** a live pill's case list here NEVER maps the
//! value `0`. An un-driven surface (a static web bake; an unseeded native applet) reads
//! `0`, matches no case, and falls back to the pill's static `text`/`tag` — which this
//! builder sets to the SNAPSHOT truth. So a static bake can never show a sleeping vat
//! as RUNNING: live values start at 1 ([`VatState::live_value`]), and going live only
//! ever upgrades the word from snapshot-truth to now-truth.
//!
//! ## Progressive disclosure
//!
//! Raw cell ids ride in [`ViewNode::Adept`] wrappers (full hex is adept-only; the simple
//! projection shows the short handle). Adept wrappers here NEVER contain `Bind` nodes,
//! so [`console_bind_values`] is valid for BOTH disclosure projections (the dropped
//! subtree consumes no bind cursor — the invariant `disclose` documents).

use serde::{Deserialize, Serialize};

use crate::fmt::{format_value, BindFmt};
use crate::tree::{Crumb, MenuItem, PillCase, ViewNode};

// ─────────────────────────────────────────────────────────────────────────────
// THE DASHBOARD VIEW MODELS — dregg-native, anchored on live-World cells
// ─────────────────────────────────────────────────────────────────────────────

/// A vat's lifecycle state — the `ServerView.state` string (`"running"` / `"stopped"` /
/// `"reaped"`, DreggNet model.rs:63) lifted into the VAT framing: a stopped server is a
/// SLEEPING computer (its whole state checkpointed to a committed root,
/// `ServerRecord.checkpoint_root`, control/src/server.rs:65 — wake restores it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VatState {
    /// Held up and metered per uptime period.
    Running,
    /// Checkpointed to its committed root — wake restores exactly this computer.
    Sleeping,
    /// Reclaimed (lapsed lease / explicit reap). Its receipts remain verifiable.
    Reaped,
}

impl VatState {
    /// Lift the `ServerView.state` record word (model.rs:63). Unknown → `Reaped` is the
    /// WRONG default (it would show a live computer as dead); unknown → `Sleeping` is the
    /// conservative one: the computer exists, we do not claim it is serving.
    pub fn from_record(word: &str) -> Self {
        match word {
            "running" => VatState::Running,
            "stopped" | "sleeping" => VatState::Sleeping,
            "reaped" => VatState::Reaped,
            _ => VatState::Sleeping,
        }
    }

    /// The pill word for this state.
    pub fn word(self) -> &'static str {
        match self {
            VatState::Running => "RUNNING",
            VatState::Sleeping => "SLEEPING",
            VatState::Reaped => "REAPED",
        }
    }

    /// The semantic pill tag (the `crate::web` palette: `live`=green, `muted`=grey,
    /// `bad`=red).
    pub fn tag(self) -> &'static str {
        match self {
            VatState::Running => "live",
            VatState::Sleeping => "muted",
            VatState::Reaped => "bad",
        }
    }

    /// The live slot value for this state — the `0 = as-baked` convention: values start
    /// at 1 so an un-driven slot (0) falls back to the snapshot-truth static pill.
    pub fn live_value(self) -> u64 {
        match self {
            VatState::Running => 1,
            VatState::Sleeping => 2,
            VatState::Reaped => 3,
        }
    }

    /// The live-pill case list every vat status pill carries (values 1..=3; NO case for
    /// 0 — see the module-doc pill convention).
    pub fn pill_cases() -> Vec<PillCase> {
        [VatState::Running, VatState::Sleeping, VatState::Reaped]
            .into_iter()
            .map(|s| PillCase {
                value: s.live_value(),
                label: s.word().to_string(),
                tag: s.tag().to_string(),
            })
            .collect()
    }
}

/// The renter's witness stance for a vat — mirrors `WitnessMode`
/// (deos turn/src/collapse.rs:98: `Full` = every commit materializes the per-turn Merkle
/// witness; `Symbolic` = the state transition fully applies but the witness defers, and
/// a later `collapse` re-derives the real one FAIL-CLOSED, world.rs:1390).
///
/// HONEST GAP (DREGG-COMPUTER.md): `witness_mode` is not yet a field of the DreggNet
/// lease — a renter cannot pick this at provision time. The console carries it anyway
/// because the card is the surface where that choice will live; the fixture data marks
/// which stance each demo vat runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessStance {
    /// Proof-as-you-go: every receipt immediately publishable.
    Full,
    /// Cheap now, verify later: witnesses deferred until a collapse.
    Symbolic,
}

impl WitnessStance {
    /// The pill word — names the guarantee, not the enum.
    pub fn word(self) -> &'static str {
        match self {
            WitnessStance::Full => "FULL · PROOF-AS-YOU-GO",
            WitnessStance::Symbolic => "SYMBOLIC · VERIFY LATER",
        }
    }

    /// `good` for full (green: publishable now), `warn` for symbolic (amber: a
    /// commitment deferred is a commitment not yet checkable — never paint it green).
    pub fn tag(self) -> &'static str {
        match self {
            WitnessStance::Full => "good",
            WitnessStance::Symbolic => "warn",
        }
    }
}

/// **A Dregg Computer** — one vat. Mirrors `ServerView` (DreggNet model.rs:56) plus the
/// vat-identity fields the design adds: the content-addressed `cell_id` the whole
/// computer IS (control/src/server.rs:56), the reachable `endpoint` (the v0 build-order
/// field — `None` until the weld lands, and the card says so honestly), and the
/// [`WitnessStance`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VatView {
    /// The lessee renting this computer — the owning subject (`dregg:<16 hex>`,
    /// `ServerView.lessee`, model.rs:58).
    pub owner: String,
    /// The vat's cell id (hex) — the computer's content-addressed identity
    /// (`ServerRecord.cell_id`, server.rs:56). Full hex is adept-only on the card.
    pub cell_id: String,
    /// A human name (`ServerView.name`).
    pub name: String,
    /// Lifecycle state (`ServerView.state` lifted — [`VatState::from_record`]).
    pub state: VatState,
    /// Placement region (`ServerView.region`).
    pub region: String,
    /// Compute size (`ServerView.size` — `small`/`medium`/`large`).
    pub size: String,
    /// Total uptime budget, meter units — the hard ceiling (`budget_units`).
    pub budget_units: u64,
    /// Cost per uptime period (`per_period_units`).
    pub per_period_units: u64,
    /// Uptime periods metered + settled so far — the durable cursor
    /// (`periods_metered`; settle is exactly-once per period, server.rs:1108).
    pub periods_metered: u64,
    /// The renter's witness stance (see [`WitnessStance`] — a named DreggNet gap).
    pub witness: WitnessStance,
    /// The reachable endpoint, once the v0 `ServerRecord.endpoint` weld lands.
    /// `None` → the card shows the gap instead of faking a URL.
    pub endpoint: Option<String>,
}

impl VatView {
    /// Total uptime units settled so far — mirrors `ServerView::settled_units`
    /// (model.rs:79): `periods_metered × per_period_units`, saturating.
    pub fn settled_units(&self) -> u64 {
        self.periods_metered.saturating_mul(self.per_period_units)
    }

    /// Remaining uptime headroom — mirrors `ServerView::headroom_units` (model.rs:83):
    /// `budget − settled`, floored at zero.
    pub fn headroom_units(&self) -> u64 {
        self.budget_units.saturating_sub(self.settled_units())
    }
}

/// One mandate edge of a hermes — a verb it CAN or CANNOT perform, read off the live
/// World's authorization boundary (`starbridge-v2/src/agent.rs:305`), never
/// self-reported. A CANNOT edge is SHOWN (the in-band refusal), not hidden.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MandateEdge {
    /// The capability verb (`invoke:run_tests`, `cell-write:/deploy`, …).
    pub verb: String,
    /// Whether the mandate grants it.
    pub allowed: bool,
}

/// One receipted action row of a hermes — the console's explore surface leads with the
/// truth trail (`AgentActivity::build_actions` interleaves refusals in true order,
/// agent.rs:209; the fixture rows mirror `AgentRunReport::tool_results`, model.rs:138).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptRow {
    /// What the action was (`verify_deploy`, `run_tests`, a cell write, …).
    pub action: String,
    /// Whether it was admitted + passed (`false` → REFUSED/failed, painted red).
    pub ok: bool,
    /// The sealed one-line summary (`"tests: 34 passed, 0 failed"`).
    pub note: String,
}

/// A hermes' living status — the resident-agent lifecycle the F4 design names
/// (hire → step → sleep=checkpoint → resume / fork). Values start at 1 for the live
/// slot (the `0 = as-baked` convention, like [`VatState::live_value`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HermesStatus {
    /// Hired and idle in its room — ready to step.
    Resident,
    /// Mid-beat: committing receipted turns right now.
    Stepping,
    /// Checkpointed (`AgentMemoryCheckpoint::capture`, agent_memory.rs:121) — resume
    /// reifies it back fail-closed (`:170`).
    Sleeping,
    /// Running in a forked World (`World::fork`) — stitch or discard later.
    Forked,
}

impl HermesStatus {
    /// The pill word.
    pub fn word(self) -> &'static str {
        match self {
            HermesStatus::Resident => "RESIDENT",
            HermesStatus::Stepping => "STEPPING",
            HermesStatus::Sleeping => "SLEEPING",
            HermesStatus::Forked => "FORKED",
        }
    }

    /// The semantic pill tag.
    pub fn tag(self) -> &'static str {
        match self {
            HermesStatus::Resident => "live",
            HermesStatus::Stepping => "accent",
            HermesStatus::Sleeping => "muted",
            HermesStatus::Forked => "pending",
        }
    }

    /// The live slot value (1..=4; 0 is reserved for the as-baked fallback).
    pub fn live_value(self) -> u64 {
        match self {
            HermesStatus::Resident => 1,
            HermesStatus::Stepping => 2,
            HermesStatus::Sleeping => 3,
            HermesStatus::Forked => 4,
        }
    }

    /// The live-pill case list every hermes status pill carries (values 1..=4).
    pub fn pill_cases() -> Vec<PillCase> {
        [
            HermesStatus::Resident,
            HermesStatus::Stepping,
            HermesStatus::Sleeping,
            HermesStatus::Forked,
        ]
        .into_iter()
        .map(|s| PillCase {
            value: s.live_value(),
            label: s.word().to_string(),
            tag: s.tag().to_string(),
        })
        .collect()
    }
}

/// **A hermes living in a Dregg Computer** — the view DreggNet's console does NOT have
/// yet (its `AgentView`, model.rs:99, is a one-shot deploy report; the F4 gap names the
/// missing `HermesView` explicitly). This is that shape: a persistent, resumable,
/// forkable resident with a budget meter, a mandate, and a receipt trail.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HermesView {
    /// The owning subject (the hirer).
    pub owner: String,
    /// The resident's cell id (hex) — its working set is a witnessed projection of this
    /// cell (`agent_memory.rs:121`). Full hex is adept-only on the card.
    pub cell_id: String,
    /// The resident's name/handle.
    pub name: String,
    /// The living status (see [`HermesStatus`]).
    pub status: HermesStatus,
    /// The mandate edges — CAN and CANNOT both shown (agent.rs:150/:305).
    pub mandate: Vec<MandateEdge>,
    /// The hard spend ceiling (`AgentRunReport.budget` via `AgentView::budget`).
    pub budget_units: u64,
    /// Budget consumed so far (`report.consumed`).
    pub consumed_units: u64,
    /// Sealed receipts count — the LIVE-BOUND number on the card (every step moves it).
    pub receipts: u64,
    /// Receipts whose witness is still deferred (symbolic mode; `symbolic_pending`,
    /// world.rs:1298). Non-zero paints an amber "collapse pending" pill — deferred is
    /// NEVER shown as verified (the vacuous-pass footgun the design warns about).
    pub deferred: u64,
    /// The last-beat summary line ("what it last did", the console's `last-run`).
    pub last_beat: String,
    /// Recent receipted actions, newest last (refusals interleaved in true order).
    pub recent: Vec<ReceiptRow>,
}

impl HermesView {
    /// Un-drawn budget headroom — the ceiling on everything the hermes could still do
    /// (`AgentView::headroom`, model.rs:126), floored at zero.
    pub fn headroom_units(&self) -> u64 {
        self.budget_units.saturating_sub(self.consumed_units)
    }
}

/// One line of the $DREGG spend ledger — mirrors `SpendEntry` (model.rs:194).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpendLine {
    /// The subject billed.
    pub owner: String,
    /// The resource kind charged (`"vat"` / `"hermes"` / `"site"` / `"storage"`).
    pub resource_kind: String,
    /// The specific resource charged.
    pub resource_id: String,
    /// The billing period label (an uptime-period index, a run id, a date).
    pub period: String,
    /// Units charged.
    pub units: u64,
}

/// The $DREGG balance + spend view — mirrors `DreggLedgerView` (model.rs:215).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LedgerView {
    /// The subject this ledger is for.
    pub subject: String,
    /// Current $DREGG balance.
    pub balance: u64,
    /// Total spent across the subject's resources (Σ of `entries`).
    pub total_spent: u64,
    /// Per-resource/period spend lines, already scoped to the subject.
    pub entries: Vec<SpendLine>,
}

/// **The assembled, cap-scoped console model for one signed-in subject** — mirrors
/// `ConsoleView` (model.rs:303), re-centred on the vat product: `computers` (vats) and
/// `hermeses` are the leading panels; sites/domains/storage keep living in DreggNet's
/// model and join this card when the adapter lands (they are plain list sections — the
/// vocabulary below already covers them).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsoleModel {
    /// The authenticated subject this view belongs to (`dregg:<16 hex>`).
    pub subject: String,
    /// When the view was assembled (RFC3339) — honest data age on the card.
    pub generated_at: String,
    /// The subject's Dregg Computers.
    pub computers: Vec<VatView>,
    /// The subject's resident hermeses.
    pub hermeses: Vec<HermesView>,
    /// The subject's $DREGG balance + spend.
    pub dregg: LedgerView,
}

impl ConsoleModel {
    /// **The cap-scoping seam** — narrow a (possibly multi-tenant) model to exactly
    /// `subject`'s own resources, echoing DreggNet `scope.rs` + the `Owned` trait
    /// (model.rs:25): a resource is kept iff its `owner == subject`. Spend lines are
    /// re-filtered and `total_spent` RECOMPUTED from the surviving lines (never trust a
    /// pre-aggregated total across a scope cut). The balance is kept only when the
    /// ledger already belongs to the subject — a foreign balance is zeroed, not leaked.
    pub fn scoped_to(&self, subject: &str) -> ConsoleModel {
        let entries: Vec<SpendLine> = self
            .dregg
            .entries
            .iter()
            .filter(|e| e.owner == subject)
            .cloned()
            .collect();
        let total_spent = entries.iter().map(|e| e.units).sum();
        ConsoleModel {
            subject: subject.to_string(),
            generated_at: self.generated_at.clone(),
            computers: self
                .computers
                .iter()
                .filter(|v| v.owner == subject)
                .cloned()
                .collect(),
            hermeses: self
                .hermeses
                .iter()
                .filter(|h| h.owner == subject)
                .cloned()
                .collect(),
            dregg: LedgerView {
                subject: subject.to_string(),
                balance: if self.dregg.subject == subject {
                    self.dregg.balance
                } else {
                    0
                },
                total_spent,
                entries,
            },
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SLOT PLAN — which model slot each live element reads (immediate-mode reads
// + the bind cursor). Fixed region bases so adding a vat never re-numbers a
// hermes slot (a live re-bind survives a fleet change).
// ─────────────────────────────────────────────────────────────────────────────

/// Slot 0: the $DREGG balance (the header `Bind`, fmt `amount`).
pub const SLOT_BALANCE: usize = 0;
/// First per-vat slot; vat `i` owns `[VAT_SLOT_BASE + i·stride, …+stride)`.
pub const VAT_SLOT_BASE: usize = 8;
/// Per-vat stride: `+0` settled-units (gauge), `+1` status (live pill).
pub const VAT_SLOT_STRIDE: usize = 2;
/// First per-hermes slot — a fixed base ABOVE the vat region so hermes slots are stable
/// as the fleet grows. Caps the vat region at `(64−8)/2 = 28` computers; past that the
/// builder saturates honestly (see [`vat_spent_slot`]) rather than colliding silently.
pub const HERMES_SLOT_BASE: usize = 64;
/// Per-hermes stride: `+0` status (live pill), `+1` receipts (Bind), `+2`
/// consumed-units (gauge), `+3` reserved (the beat counter, when the living loop lands).
pub const HERMES_SLOT_STRIDE: usize = 4;

/// The most computers the fixed slot regions can carry without collision.
pub const MAX_SLOTTED_VATS: usize = (HERMES_SLOT_BASE - VAT_SLOT_BASE) / VAT_SLOT_STRIDE;

/// Vat `i`'s settled-units gauge slot. Past [`MAX_SLOTTED_VATS`] every further vat
/// CLAMPS onto the last in-region pair — two gauges sharing a slot paint the same
/// number (visible, wrong-but-bounded) instead of silently overwriting a hermes slot
/// (invisible, unbounded). A 29-computer fleet is past this proto's slot plan.
pub fn vat_spent_slot(i: usize) -> usize {
    VAT_SLOT_BASE + i.min(MAX_SLOTTED_VATS - 1) * VAT_SLOT_STRIDE
}

/// Vat `i`'s status live-pill slot (same clamp as [`vat_spent_slot`]).
pub fn vat_status_slot(i: usize) -> usize {
    vat_spent_slot(i) + 1
}

/// Hermes `i`'s status live-pill slot.
pub fn hermes_status_slot(i: usize) -> usize {
    HERMES_SLOT_BASE + i * HERMES_SLOT_STRIDE
}

/// Hermes `i`'s receipts-count bind slot (the live-bound number on the card).
pub fn hermes_receipts_slot(i: usize) -> usize {
    hermes_status_slot(i) + 1
}

/// Hermes `i`'s consumed-units gauge slot.
pub fn hermes_spent_slot(i: usize) -> usize {
    hermes_status_slot(i) + 2
}

// ─────────────────────────────────────────────────────────────────────────────
// THE AFFORDANCE GRAMMAR — turn names the card fires. `arg` is the resource's
// index in ITS list (computers / hermeses), i64. Each name is the seam to a
// real control-plane verb (cited), so wiring the console to DreggNet is a
// dispatch table, not a redesign.
// ─────────────────────────────────────────────────────────────────────────────

/// Wake a sleeping vat — restore from its committed `checkpoint_root`
/// (control/src/server.rs:65; admission stays behind the funded lease).
pub const TURN_VAT_WAKE: &str = "vat.wake";
/// Sleep a running vat — checkpoint its state to a committed root (server.rs:65).
pub const TURN_VAT_SLEEP: &str = "vat.sleep";
/// Fork a vat into a divergent copy (`ServerFleet` fork server.rs:835 /
/// `World::fork` starbridge-v2/src/world.rs:695).
pub const TURN_VAT_FORK: &str = "vat.fork";
/// Explore a vat's World — the census read (cells + balances + receipts,
/// `world_explorer.rs:171`).
pub const TURN_VAT_EXPLORE: &str = "vat.explore";
/// Re-witness a vat's receipt chain against YOUR key
/// (`verify_receipt_chain_with_keys`, turn/src/verify.rs:245 — and the verify MUST
/// refuse a deferred receipt via `is_deferred`, collapse.rs:88, before calling it green).
pub const TURN_VAT_VERIFY: &str = "vat.verify";

/// Step a resident hermes one beat (real receipted turns, hireling.rs).
pub const TURN_HERMES_STEP: &str = "hermes.step";
/// Fork a hermes into a divergent World (the unglued F4 flow — `World::fork` +
/// `BranchStitchSession` exist; the glue is the named gap).
pub const TURN_HERMES_FORK: &str = "hermes.fork";
/// Resume a checkpointed hermes fail-closed (`AgentMemoryCheckpoint` resume,
/// agent_memory.rs:170 — four teeth re-witnessed).
pub const TURN_HERMES_RESUME: &str = "hermes.resume";
/// Re-witness a hermes' report/receipt chain (the console re-verify button —
/// DreggNet console/src/verify.rs re-witnesses the REAL proof, never a flag).
pub const TURN_HERMES_VERIFY: &str = "hermes.verify";

/// The verify-anything panel's turn — the submitted draft is the thing to re-witness.
pub const TURN_CONSOLE_VERIFY: &str = "console.verify";

// ─────────────────────────────────────────────────────────────────────────────
// THE BUILDER — pure ConsoleModel → ViewNode (no gpui, no HTML, no IO)
// ─────────────────────────────────────────────────────────────────────────────

/// A short display handle for a hex cell id: `6fa3c1…9d2e`. Char-based (never a
/// byte-slice panic on odd input); short ids pass through whole.
fn short_id(id: &str) -> String {
    let chars: Vec<char> = id.chars().collect();
    if chars.len() <= 12 {
        return id.to_string();
    }
    let head: String = chars[..6].iter().collect();
    let tail: String = chars[chars.len() - 4..].iter().collect();
    format!("{head}…{tail}")
}

/// Grouped-digit display for meter units (the shared consumer-delight formatter —
/// `1440` → `1,440`, identical in every renderer via [`crate::fmt`]).
fn amount(v: u64) -> String {
    format_value(v, BindFmt::Amount)
}

/// A static pill (no live slot) — the snapshot-truth badge.
fn static_pill(text: impl Into<String>, tag: &str) -> ViewNode {
    ViewNode::Pill {
        text: text.into(),
        tag: tag.to_string(),
        slot: None,
        cases: Vec::new(),
    }
}

/// A live pill: reads `slot` immediate-mode; the case list maps live values (all ≥ 1);
/// the static fallback is the SNAPSHOT truth (painted whenever the slot reads 0 — the
/// `0 = as-baked` convention, so an un-driven surface never lies).
fn live_pill(
    slot: usize,
    fallback_text: &str,
    fallback_tag: &str,
    cases: Vec<PillCase>,
) -> ViewNode {
    ViewNode::Pill {
        text: fallback_text.to_string(),
        tag: fallback_tag.to_string(),
        slot: Some(slot),
        cases,
    }
}

/// One Dregg Computer's card section — status + witness stance + identity + the uptime
/// budget gauge + the actuation menu (cap teeth shown dimmed, never hidden).
fn vat_section(i: usize, vat: &VatView) -> ViewNode {
    let mut children: Vec<ViewNode> = Vec::new();

    // Status row: a state glyph, the LIVE status pill (snapshot-truth fallback), and
    // the witness-stance badge (green only when the receipts are publishable NOW).
    children.push(ViewNode::Row(vec![
        ViewNode::Icon {
            glyph: "▣".to_string(),
            tag: vat.state.tag().to_string(),
        },
        live_pill(
            vat_status_slot(i),
            vat.state.word(),
            vat.state.tag(),
            VatState::pill_cases(),
        ),
        static_pill(vat.witness.word(), vat.witness.tag()),
    ]));

    // Identity: the short handle in the simple projection; the full hex is adept-only
    // (see-the-bones), and NEVER carries a Bind (the disclosure/bind-cursor invariant).
    children.push(ViewNode::Text(format!(
        "cell {} · {} · {}",
        short_id(&vat.cell_id),
        vat.region,
        vat.size
    )));
    children.push(ViewNode::Adept(Box::new(ViewNode::Text(format!(
        "cell id (full): {}",
        vat.cell_id
    )))));

    // Reachability: the v0 endpoint, or the named gap — the card never fakes a URL.
    children.push(match &vat.endpoint {
        Some(url) => ViewNode::Text(format!("endpoint {url}")),
        None => {
            ViewNode::Text("endpoint — not yet routed (v0 seam: ServerRecord.endpoint)".to_string())
        }
    });

    // The uptime-budget meter: a LIVE gauge (the native renderer fills it from the
    // slot; a live web card drives it once an executor is bound) + the honest numbers
    // as text so a STATIC bake still communicates the meter.
    children.push(ViewNode::Gauge {
        slot: vat_spent_slot(i),
        max: vat.budget_units,
        label: "uptime budget".to_string(),
    });
    children.push(ViewNode::Text(format!(
        "settled {} / {} · headroom {} · {} units/period · period {}",
        amount(vat.settled_units()),
        amount(vat.budget_units),
        amount(vat.headroom_units()),
        amount(vat.per_period_units),
        vat.periods_metered
    )));

    // The actuation menu — every verb visible, capability teeth shown as DIMMED rows
    // (the in-band refusal): wake only a sleeper, sleep only a runner, fork/explore
    // only a non-reaped computer; verify always (receipts outlive the machine).
    let arg = i as i64;
    let reaped = vat.state == VatState::Reaped;
    children.push(ViewNode::Menu {
        items: vec![
            MenuItem {
                label: "wake — restore from the committed checkpoint".to_string(),
                turn: TURN_VAT_WAKE.to_string(),
                arg,
                enabled: vat.state == VatState::Sleeping,
            },
            MenuItem {
                label: "sleep — checkpoint to a committed root".to_string(),
                turn: TURN_VAT_SLEEP.to_string(),
                arg,
                enabled: vat.state == VatState::Running,
            },
            MenuItem {
                label: "fork — a divergent copy of this computer".to_string(),
                turn: TURN_VAT_FORK.to_string(),
                arg,
                enabled: !reaped,
            },
            MenuItem {
                label: "explore — the World census (cells · balances · receipts)".to_string(),
                turn: TURN_VAT_EXPLORE.to_string(),
                arg,
                enabled: !reaped,
            },
            MenuItem {
                label: "verify — re-witness the receipt chain against YOUR key".to_string(),
                turn: TURN_VAT_VERIFY.to_string(),
                arg,
                enabled: true,
            },
        ],
    });

    ViewNode::Section {
        title: vat.name.clone(),
        // `genuine` accents the running computer's frame; others stay plain.
        tag: if vat.state == VatState::Running {
            "genuine".to_string()
        } else {
            String::new()
        },
        children,
    }
}

/// One hermes' panel section — live status pill + LIVE receipts bind + the mandate
/// (CAN and CANNOT), the budget gauge, the receipt trail, and the actuation menu.
fn hermes_section(i: usize, h: &HermesView) -> ViewNode {
    let mut children: Vec<ViewNode> = Vec::new();

    // Status row: glyph + live status pill + the LIVE-BOUND receipts count (this Bind
    // is the card's heartbeat — every committed step moves it).
    children.push(ViewNode::Row(vec![
        ViewNode::Icon {
            glyph: "✦".to_string(),
            tag: h.status.tag().to_string(),
        },
        live_pill(
            hermes_status_slot(i),
            h.status.word(),
            h.status.tag(),
            HermesStatus::pill_cases(),
        ),
        ViewNode::Bind {
            slot: hermes_receipts_slot(i),
            label: "receipts: ".to_string(),
            fmt: BindFmt::Raw,
        },
    ]));

    // Identity (short simple / full adept — no Bind inside the adept wrapper).
    children.push(ViewNode::Text(format!("cell {}", short_id(&h.cell_id))));
    children.push(ViewNode::Adept(Box::new(ViewNode::Text(format!(
        "cell id (full): {}",
        h.cell_id
    )))));

    // The last beat — what it last did, in one line.
    children.push(ViewNode::Text(format!("last beat — {}", h.last_beat)));

    // Witness debt: deferred receipts are AMBER and named, never counted as verified
    // (the symbolic vacuous-pass footgun the design doc warns about).
    if h.deferred > 0 {
        children.push(ViewNode::Row(vec![
            static_pill(format!("{} deferred", h.deferred), "warn"),
            ViewNode::Text(
                "symbolic witnesses pending — collapse re-derives them fail-closed".to_string(),
            ),
        ]));
    } else {
        children.push(ViewNode::Row(vec![static_pill("all witnessed", "good")]));
    }

    // The mandate-budget meter (live gauge + honest static numbers).
    children.push(ViewNode::Gauge {
        slot: hermes_spent_slot(i),
        max: h.budget_units,
        label: "mandate budget".to_string(),
    });
    children.push(ViewNode::Text(format!(
        "consumed {} / {} · headroom {}",
        amount(h.consumed_units),
        amount(h.budget_units),
        amount(h.headroom_units())
    )));

    // The mandate — CAN and CANNOT edges both shown (the boundary is the product).
    children.push(ViewNode::Divider);
    children.push(ViewNode::Text(
        "mandate — read off the live World, never self-reported".to_string(),
    ));
    children.push(ViewNode::List(
        h.mandate
            .iter()
            .map(|e| {
                ViewNode::Row(vec![
                    ViewNode::Icon {
                        glyph: if e.allowed { "✓" } else { "✗" }.to_string(),
                        tag: if e.allowed { "good" } else { "bad" }.to_string(),
                    },
                    ViewNode::Text(e.verb.clone()),
                ])
            })
            .collect(),
    ));

    // The receipt trail — refusals interleaved in true order, verdict per row.
    if !h.recent.is_empty() {
        children.push(ViewNode::Divider);
        children.push(ViewNode::Table(
            h.recent
                .iter()
                .map(|r| {
                    ViewNode::Row(vec![
                        static_pill(
                            if r.ok { "ok" } else { "refused" },
                            if r.ok { "good" } else { "refusal" },
                        ),
                        ViewNode::Text(r.action.clone()),
                        ViewNode::Text(r.note.clone()),
                    ])
                })
                .collect(),
        ));
    }

    // Actuation: step / fork / resume / re-verify — resume only bites a sleeper.
    let arg = i as i64;
    children.push(ViewNode::Menu {
        items: vec![
            MenuItem {
                label: "step — one receipted beat".to_string(),
                turn: TURN_HERMES_STEP.to_string(),
                arg,
                enabled: h.status != HermesStatus::Sleeping,
            },
            MenuItem {
                label: "fork — diverge it into a copied World".to_string(),
                turn: TURN_HERMES_FORK.to_string(),
                arg,
                enabled: true,
            },
            MenuItem {
                label: "resume — reify the checkpoint, fail-closed".to_string(),
                turn: TURN_HERMES_RESUME.to_string(),
                arg,
                enabled: h.status == HermesStatus::Sleeping,
            },
            MenuItem {
                label: "re-verify — re-witness the receipt chain".to_string(),
                turn: TURN_HERMES_VERIFY.to_string(),
                arg,
                enabled: true,
            },
        ],
    });

    ViewNode::Section {
        title: h.name.clone(),
        tag: String::new(),
        children,
    }
}

/// **Build the "My Dregg Computer" console card** — the whole management console as one
/// portable [`ViewNode`] tree: header ($DREGG balance, live-bound) · computers (status
/// pill + budget gauge + wake/sleep/fork/explore/verify) · hermeses (receipts + mandate
/// + live-bind status) · the spend ledger · the verify-anything panel.
///
/// PURE: model in, data out. No gpui, no HTML, no IO — the same tree walks into native
/// gpui widgets (`crate::render::AppletView`, feature `native`), a browser document
/// (`crate::web::render_card_document`, feature `web`), or a discord embed. Pair it with
/// [`console_bind_values`] (the pre-order `Bind` snapshot) and [`console_slot_seeds`]
/// (the immediate-mode slot seeds) to paint or drive it.
pub fn console_card(model: &ConsoleModel) -> ViewNode {
    let mut top: Vec<ViewNode> = Vec::new();

    // Where am I — the navigation spine (static crumbs; a host may make them turns).
    top.push(ViewNode::Breadcrumb {
        items: vec![
            Crumb {
                label: "deos".to_string(),
                turn: String::new(),
                arg: 0,
            },
            Crumb {
                label: "my dregg computer".to_string(),
                turn: String::new(),
                arg: 0,
            },
        ],
    });

    // ── The header: who + the live $DREGG balance + the trust framing. ──────────
    top.push(ViewNode::Section {
        title: "my dregg computer".to_string(),
        tag: "genuine".to_string(),
        children: vec![
            ViewNode::Row(vec![
                ViewNode::Bind {
                    slot: SLOT_BALANCE,
                    label: "$DREGG ".to_string(),
                    fmt: BindFmt::Amount,
                },
                static_pill("cap-scoped", "muted"),
                static_pill("live truth · verified turns", "good"),
            ]),
            ViewNode::Text(format!(
                "{} · total spent {} units",
                model.subject,
                amount(model.dregg.total_spent)
            )),
        ],
    });

    // ── Computers — one section per vat, in a two-up grid. ──────────────────────
    let computers: Vec<ViewNode> = if model.computers.is_empty() {
        vec![ViewNode::Text(
            "no computers yet — `dregg-cloud vat create --name mybox` mints one behind the funded lease".to_string(),
        )]
    } else {
        vec![ViewNode::Grid {
            cols: 2,
            children: model
                .computers
                .iter()
                .enumerate()
                .map(|(i, v)| vat_section(i, v))
                .collect(),
        }]
    };
    top.push(ViewNode::Section {
        title: "computers".to_string(),
        tag: String::new(),
        children: computers,
    });

    // ── Hermeses — the residents living in the computers. ───────────────────────
    let hermeses: Vec<ViewNode> = if model.hermeses.is_empty() {
        vec![ViewNode::Text(
            "no hermeses yet — hire a resident and it lives HERE, in your computer".to_string(),
        )]
    } else {
        model
            .hermeses
            .iter()
            .enumerate()
            .map(|(i, h)| hermes_section(i, h))
            .collect()
    };
    top.push(ViewNode::Section {
        title: "hermeses — resident agents".to_string(),
        tag: String::new(),
        children: hermeses,
    });

    // ── The spend ledger — every charge named (kind · resource · period · units). ──
    let spend: Vec<ViewNode> = if model.dregg.entries.is_empty() {
        vec![ViewNode::Text("no charges yet".to_string())]
    } else {
        vec![ViewNode::Table(
            model
                .dregg
                .entries
                .iter()
                .map(|e| {
                    ViewNode::Row(vec![
                        static_pill(e.resource_kind.clone(), "muted"),
                        ViewNode::Text(e.resource_id.clone()),
                        ViewNode::Text(e.period.clone()),
                        ViewNode::Text(format!("{} units", amount(e.units))),
                    ])
                })
                .collect(),
        )]
    };
    top.push(ViewNode::Section {
        title: "spend".to_string(),
        tag: String::new(),
        children: spend,
    });

    // ── Verify anything — the console's standing offer: green is a proof, not a
    //    promise. The submitted draft fires a real verify turn. ────────────────────
    top.push(ViewNode::Section {
        title: "verify anything".to_string(),
        tag: String::new(),
        children: vec![
            ViewNode::Text(
                "paste a receipt or root — the console re-witnesses it against YOUR anchor, \
                 and a deferred (symbolic) receipt is refused, never passed vacuously"
                    .to_string(),
            ),
            ViewNode::Input {
                bind_view: "verify-anything".to_string(),
                fire_turn: TURN_CONSOLE_VERIFY.to_string(),
                submit_label: "verify".to_string(),
            },
        ],
    });

    // ── The footer — data age + the portability thesis, on the glass. ────────────
    top.push(ViewNode::Divider);
    top.push(ViewNode::Text(format!(
        "assembled {} · one model, many faces — native gpui · web · phone",
        model.generated_at
    )));

    ViewNode::VStack(top)
}

/// The pre-order `Bind` snapshot for [`console_card`]'s tree — element `n` is the value
/// of the `n`th [`ViewNode::Bind`] in tree-walk order (the web renderer's `BindValues`
/// contract; the native renderer's bind plan mints ids in the same order).
///
/// Order (must mirror the builder): the header balance bind, then each hermes' receipts
/// bind (hermes sections follow the computers section, which carries NO binds — its
/// gauges and pills read immediate-mode and consume no cursor).
pub fn console_bind_values(model: &ConsoleModel) -> Vec<u64> {
    let mut values = vec![model.dregg.balance];
    values.extend(model.hermeses.iter().map(|h| h.receipts));
    values
}

/// Every immediate-mode `(slot, value)` a LIVE executor must seed so the live card
/// agrees with the snapshot: the balance bind's slot, each vat's status + settled-units,
/// each hermes' status + receipts + consumed-units. Status seeds use
/// [`VatState::live_value`]/[`HermesStatus::live_value`] (≥ 1 — slot value 0 is the
/// reserved as-baked fallback).
pub fn console_slot_seeds(model: &ConsoleModel) -> Vec<(usize, u64)> {
    let mut seeds = vec![(SLOT_BALANCE, model.dregg.balance)];
    for (i, v) in model.computers.iter().enumerate() {
        seeds.push((vat_spent_slot(i), v.settled_units()));
        seeds.push((vat_status_slot(i), v.state.live_value()));
    }
    for (i, h) in model.hermeses.iter().enumerate() {
        seeds.push((hermes_status_slot(i), h.status.live_value()));
        seeds.push((hermes_receipts_slot(i), h.receipts));
        seeds.push((hermes_spent_slot(i), h.consumed_units));
    }
    seeds
}

// ─────────────────────────────────────────────────────────────────────────────
// THE DEMO MODEL — fixture-shaped (mirrors DreggNet console/src/fixtures.rs:
// same subjects, same srv_demo01 numbers) so the two consoles can be eyeballed
// side-by-side. Multi-tenant ON PURPOSE: scoping must be exercised, not vacuous.
// ─────────────────────────────────────────────────────────────────────────────

/// The demo subject — the exact fixture subject DreggNet's console uses
/// (`fixtures.rs:23`), so the seam is eyeball-checkable.
pub const DEMO_SUBJECT: &str = "dregg:demo0001demo0001";
/// A second tenant (`fixtures.rs:25`) — their resources must NEVER reach the demo view.
pub const OTHER_SUBJECT: &str = "dregg:other0002other000";

/// A deterministic, multi-tenant demo model. The demo subject owns two computers (one
/// running Full-witness with an endpoint, one sleeping Symbolic without — both honest
/// states the card must paint), one resident hermes, and the fixture spend ledger; the
/// other tenant owns a computer and a hermes that scoping must drop.
pub fn demo_console() -> ConsoleModel {
    ConsoleModel {
        subject: DEMO_SUBJECT.to_string(),
        generated_at: "2026-07-03T04:44:00Z".to_string(),
        computers: vec![
            // Mirrors fixtures.rs srv_demo01 (api-server · iad · small · 5000/10/144),
            // vat-framed: cell-id identity + the v0 loopback endpoint + Full witness.
            VatView {
                owner: DEMO_SUBJECT.to_string(),
                cell_id: "6fa3c19b2d4e8a017c5b90e2f1a6d8349b0c7e5a4f21d6b8903e7c1a5d2f4e6b"
                    .to_string(),
                name: "mybox".to_string(),
                state: VatState::Running,
                region: "iad".to_string(),
                size: "small".to_string(),
                budget_units: 5_000,
                per_period_units: 10,
                periods_metered: 144,
                witness: WitnessStance::Full,
                endpoint: Some("http://127.0.0.1:4222".to_string()),
            },
            // A sleeping, symbolic-witness computer with NO endpoint yet — the card
            // must show the checkpointed state, the amber stance, and the named gap.
            VatView {
                owner: DEMO_SUBJECT.to_string(),
                cell_id: "0d84f2a6c1b95e37d20a8c4f6e1b3d5987c0a2e4f6b8d1c3a5079e2b4d6f8a1c"
                    .to_string(),
                name: "scratchpad".to_string(),
                state: VatState::Sleeping,
                region: "iad".to_string(),
                size: "small".to_string(),
                budget_units: 1_000,
                per_period_units: 5,
                periods_metered: 12,
                witness: WitnessStance::Symbolic,
                endpoint: None,
            },
            // The other tenant's computer (fixtures.rs srv_other99: lax · large ·
            // 50000/90/10) — must vanish under scoped_to(DEMO_SUBJECT).
            VatView {
                owner: OTHER_SUBJECT.to_string(),
                cell_id: "9e1d7b3f5a2c8e4d6b0f9a3c5e7d1b8f2a4c6e8d0b1f3a5c7e9d2b4f6a8c0e1d"
                    .to_string(),
                name: "other-srv".to_string(),
                state: VatState::Running,
                region: "lax".to_string(),
                size: "large".to_string(),
                budget_units: 50_000,
                per_period_units: 90,
                periods_metered: 10,
                witness: WitnessStance::Full,
                endpoint: None,
            },
        ],
        hermeses: vec![
            HermesView {
                owner: DEMO_SUBJECT.to_string(),
                cell_id: "b7e2a94c6d1f8350a2c4e6b8d0f1a3c5e7b9d2f4a6c8e0d1b3f5a7c9e2d4b6f8"
                    .to_string(),
                name: "deploy-bot".to_string(),
                status: HermesStatus::Resident,
                mandate: vec![
                    MandateEdge {
                        verb: "invoke:run_tests".to_string(),
                        allowed: true,
                    },
                    MandateEdge {
                        verb: "invoke:verify_deploy".to_string(),
                        allowed: true,
                    },
                    MandateEdge {
                        verb: "cell-write:/deploy".to_string(),
                        allowed: true,
                    },
                    // The CANNOT edge — the boundary shown, not hidden.
                    MandateEdge {
                        verb: "spawn:sub-agents".to_string(),
                        allowed: false,
                    },
                ],
                budget_units: 50,
                consumed_units: 12,
                receipts: 5,
                deferred: 0,
                last_beat: "verify_deploy — 12/12 checks green, sealed".to_string(),
                recent: vec![
                    ReceiptRow {
                        action: "cell-write /deploy".to_string(),
                        ok: true,
                        note: "demo-site".to_string(),
                    },
                    ReceiptRow {
                        action: "run_tests".to_string(),
                        ok: true,
                        note: "tests: 34 passed, 0 failed".to_string(),
                    },
                    ReceiptRow {
                        action: "spawn sub-agent".to_string(),
                        ok: false,
                        note: "outside the mandate — refused at the gate".to_string(),
                    },
                    ReceiptRow {
                        action: "verify_deploy".to_string(),
                        ok: true,
                        note: "deploy verified: 12/12 checks green".to_string(),
                    },
                ],
            },
            // The other tenant's hermes — must vanish under scoping.
            HermesView {
                owner: OTHER_SUBJECT.to_string(),
                cell_id: "c1f8b7e2a94c6d350a2c4e6b8d0f1a3c5e7b9d2f4a6c8e0d1b3f5a7c9e2d4b6a"
                    .to_string(),
                name: "other-bot".to_string(),
                status: HermesStatus::Sleeping,
                mandate: Vec::new(),
                budget_units: 100,
                consumed_units: 40,
                receipts: 9,
                deferred: 2,
                last_beat: "checkpointed".to_string(),
                recent: Vec::new(),
            },
        ],
        dregg: LedgerView {
            subject: DEMO_SUBJECT.to_string(),
            balance: 9_968,
            total_spent: 32,
            entries: vec![
                SpendLine {
                    owner: DEMO_SUBJECT.to_string(),
                    resource_kind: "vat".to_string(),
                    resource_id: "mybox".to_string(),
                    period: "p142".to_string(),
                    units: 10,
                },
                SpendLine {
                    owner: DEMO_SUBJECT.to_string(),
                    resource_kind: "vat".to_string(),
                    resource_id: "mybox".to_string(),
                    period: "p143".to_string(),
                    units: 10,
                },
                SpendLine {
                    owner: DEMO_SUBJECT.to_string(),
                    resource_kind: "vat".to_string(),
                    resource_id: "mybox".to_string(),
                    period: "p144".to_string(),
                    units: 10,
                },
                SpendLine {
                    owner: DEMO_SUBJECT.to_string(),
                    resource_kind: "hermes".to_string(),
                    resource_id: "deploy-bot".to_string(),
                    period: "run-1".to_string(),
                    units: 2,
                },
                // A foreign charge — scoping must drop it AND recompute the total.
                SpendLine {
                    owner: OTHER_SUBJECT.to_string(),
                    resource_kind: "vat".to_string(),
                    resource_id: "other-srv".to_string(),
                    period: "p10".to_string(),
                    units: 900,
                },
            ],
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TESTS — pure logic: the bind cursor, the scoping cut, the meter math, the
// honest-pill convention, the cap teeth, and the slot-seed coverage.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Walk every node pre-order (containers recursed in declaration order — the same
    /// order the renderers and the bind cursor walk).
    fn walk<'a>(n: &'a ViewNode, f: &mut impl FnMut(&'a ViewNode)) {
        f(n);
        match n {
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                cs.iter().for_each(|c| walk(c, f))
            }
            ViewNode::Section { children, .. } | ViewNode::Grid { children, .. } => {
                children.iter().for_each(|c| walk(c, f))
            }
            ViewNode::Tabs { panels, .. } => panels.iter().for_each(|c| walk(c, f)),
            ViewNode::Host { view: Some(v), .. } => walk(v, f),
            ViewNode::Adept(inner) => walk(inner, f),
            _ => {}
        }
    }

    /// The scoped demo model (what the card actually renders).
    fn scoped() -> ConsoleModel {
        demo_console().scoped_to(DEMO_SUBJECT)
    }

    /// THE BIND-CURSOR CONTRACT: the tree's pre-order `Bind` nodes and
    /// [`console_bind_values`] are the same length, in the same order — balance first
    /// (slot 0, amount-formatted), then each hermes' receipts bind on ITS slot.
    #[test]
    fn bind_values_align_with_the_trees_bind_cursor() {
        let model = scoped();
        let tree = console_card(&model);
        let mut binds: Vec<(usize, String)> = Vec::new();
        walk(&tree, &mut |n| {
            if let ViewNode::Bind { slot, label, .. } = n {
                binds.push((*slot, label.clone()));
            }
        });
        let values = console_bind_values(&model);
        assert_eq!(
            binds.len(),
            values.len(),
            "one snapshot value per Bind node, in tree-walk order"
        );
        assert_eq!(binds[0].0, SLOT_BALANCE, "the balance bind leads");
        assert_eq!(values[0], model.dregg.balance);
        // Each hermes' receipts bind rides its own fixed-region slot, in hermes order.
        for (i, h) in model.hermeses.iter().enumerate() {
            let (slot, label) = &binds[1 + i];
            assert_eq!(*slot, hermes_receipts_slot(i), "hermes {i} receipts slot");
            assert_eq!(label, "receipts: ");
            assert_eq!(values[1 + i], h.receipts);
        }
    }

    /// THE SCOPING CUT (the `Owned` seam): a foreign tenant's computers, hermeses, and
    /// spend lines all vanish, and the spend total is RECOMPUTED from the survivors —
    /// never the multi-tenant aggregate.
    #[test]
    fn scoped_to_drops_foreign_resources_and_recomputes_spend() {
        let all = demo_console();
        // The demo model is multi-tenant on purpose (scoping must not be vacuous).
        assert!(all.computers.iter().any(|v| v.owner == OTHER_SUBJECT));
        assert!(all.hermeses.iter().any(|h| h.owner == OTHER_SUBJECT));
        assert!(all.dregg.entries.iter().any(|e| e.owner == OTHER_SUBJECT));

        let mine = all.scoped_to(DEMO_SUBJECT);
        assert_eq!(mine.computers.len(), 2, "two demo computers survive");
        assert_eq!(mine.hermeses.len(), 1, "one demo hermes survives");
        assert!(mine.computers.iter().all(|v| v.owner == DEMO_SUBJECT));
        assert!(mine.hermeses.iter().all(|h| h.owner == DEMO_SUBJECT));
        assert!(mine.dregg.entries.iter().all(|e| e.owner == DEMO_SUBJECT));
        // 10+10+10+2 — the foreign 900-unit line is gone from the TOTAL, not just the list.
        assert_eq!(mine.dregg.total_spent, 32);
        // And nothing foreign leaks into the rendered card.
        let tree = console_card(&mine);
        let mut all_text = String::new();
        walk(&tree, &mut |n| {
            if let ViewNode::Text(t) = n {
                all_text.push_str(t);
            }
        });
        assert!(
            !all_text.contains("other-srv") && !all_text.contains("other-bot"),
            "no foreign resource name reaches the card"
        );

        // The other side of the cut: scoping to the OTHER subject keeps only theirs,
        // and the demo ledger's balance is not leaked to them.
        let theirs = all.scoped_to(OTHER_SUBJECT);
        assert_eq!(theirs.computers.len(), 1);
        assert_eq!(
            theirs.dregg.balance, 0,
            "a foreign balance is zeroed, not leaked"
        );
        assert_eq!(theirs.dregg.total_spent, 900);
    }

    /// THE METER MATH mirrors `ServerView` (model.rs:79-85), saturating: an overdrawn
    /// budget floors at zero headroom instead of wrapping.
    #[test]
    fn vat_meter_math_mirrors_server_view_and_saturates() {
        let model = scoped();
        let mybox = &model.computers[0];
        assert_eq!(mybox.settled_units(), 1_440, "144 periods × 10 units");
        assert_eq!(mybox.headroom_units(), 3_560, "5000 − 1440");

        let overdrawn = VatView {
            periods_metered: 10_000,
            ..mybox.clone()
        };
        assert_eq!(
            overdrawn.headroom_units(),
            0,
            "floored, never negative/wrapped"
        );
    }

    /// THE HONEST-PILL CONVENTION (`0 = as-baked`): every LIVE pill on the card maps
    /// only values ≥ 1, so an un-driven surface (static bake / unseeded applet) falls
    /// back to the pill's static text — which is the SNAPSHOT truth. A sleeping vat can
    /// never paint RUNNING statically.
    #[test]
    fn live_pills_reserve_zero_for_the_baked_truth() {
        let model = scoped();
        let tree = console_card(&model);
        let mut live_pills: Vec<(&str, &str, &Vec<PillCase>)> = Vec::new();
        walk(&tree, &mut |n| {
            if let ViewNode::Pill {
                text,
                tag,
                slot: Some(_),
                cases,
            } = n
            {
                live_pills.push((text.as_str(), tag.as_str(), cases));
            }
        });
        // One status pill per computer + one per hermes.
        assert_eq!(
            live_pills.len(),
            model.computers.len() + model.hermeses.len(),
            "every status pill is live-bound"
        );
        for (text, _tag, cases) in &live_pills {
            assert!(!cases.is_empty(), "a live pill carries its case map");
            assert!(
                cases.iter().all(|c| c.value != 0),
                "no case claims value 0 — the as-baked fallback stays reachable"
            );
            assert!(
                !text.is_empty(),
                "the fallback is the snapshot truth, not blank"
            );
        }
        // The sleeping vat's fallback says SLEEPING — the static bake cannot lie.
        assert_eq!(live_pills[1].0, "SLEEPING");
        assert_eq!(live_pills[1].1, "muted");
        // And driving the slot with the seed value upgrades to the same truth, live.
        let seeds = console_slot_seeds(&model);
        let sleeping_seed = seeds
            .iter()
            .find(|(s, _)| *s == vat_status_slot(1))
            .expect("the sleeping vat's status slot is seeded")
            .1;
        let (word, tag) = crate::tree::pill_display(
            live_pills[1].0,
            live_pills[1].1,
            live_pills[1].2,
            sleeping_seed,
        );
        assert_eq!(
            (word, tag),
            ("SLEEPING", "muted"),
            "seeded live value agrees with the snapshot"
        );
    }

    /// THE CAP TEETH: every vat carries all five verbs; a runner can sleep but not
    /// wake, a sleeper can wake but not sleep, and each menu row carries the vat's own
    /// index as its `arg` (the affordance payload the executor dispatches on).
    #[test]
    fn vat_affordances_carry_index_and_state_teeth() {
        let model = scoped();
        let tree = console_card(&model);
        let mut menus: Vec<&Vec<MenuItem>> = Vec::new();
        walk(&tree, &mut |n| {
            if let ViewNode::Menu { items } = n {
                // Vat menus are recognisable by their wake verb.
                if items.iter().any(|i| i.turn == TURN_VAT_WAKE) {
                    menus.push(items);
                }
            }
        });
        assert_eq!(menus.len(), model.computers.len(), "one menu per computer");

        let find = |items: &[MenuItem], turn: &str| -> MenuItem {
            items
                .iter()
                .find(|i| i.turn == turn)
                .unwrap_or_else(|| panic!("menu carries {turn}"))
                .clone()
        };
        // Vat 0 is RUNNING: sleep bites, wake is the dimmed tooth.
        assert!(find(menus[0], TURN_VAT_SLEEP).enabled);
        assert!(!find(menus[0], TURN_VAT_WAKE).enabled);
        // Vat 1 is SLEEPING: wake bites, sleep is dimmed.
        assert!(find(menus[1], TURN_VAT_WAKE).enabled);
        assert!(!find(menus[1], TURN_VAT_SLEEP).enabled);
        // Fork/explore/verify all present; verify always enabled.
        for (i, items) in menus.iter().enumerate() {
            assert!(find(items, TURN_VAT_FORK).enabled);
            assert!(find(items, TURN_VAT_EXPLORE).enabled);
            assert!(find(items, TURN_VAT_VERIFY).enabled);
            assert!(
                items.iter().all(|m| m.arg == i as i64),
                "every verb carries its computer's index"
            );
        }
    }

    /// THE HERMES TEETH mirror the lifecycle: a resident steps but cannot resume; a
    /// sleeper resumes but cannot step (checked via a sleeping variant of the demo).
    #[test]
    fn hermes_affordances_follow_the_lifecycle() {
        let mut model = scoped();
        let tree = console_card(&model);
        let items_of = |tree: &ViewNode| -> Vec<MenuItem> {
            let mut found = Vec::new();
            walk(tree, &mut |n| {
                if let ViewNode::Menu { items } = n {
                    if items.iter().any(|i| i.turn == TURN_HERMES_STEP) {
                        found = items.clone();
                    }
                }
            });
            found
        };
        let resident = items_of(&tree);
        assert!(
            resident
                .iter()
                .find(|i| i.turn == TURN_HERMES_STEP)
                .unwrap()
                .enabled
        );
        assert!(
            !resident
                .iter()
                .find(|i| i.turn == TURN_HERMES_RESUME)
                .unwrap()
                .enabled
        );

        model.hermeses[0].status = HermesStatus::Sleeping;
        let sleeping = items_of(&console_card(&model));
        assert!(
            !sleeping
                .iter()
                .find(|i| i.turn == TURN_HERMES_STEP)
                .unwrap()
                .enabled
        );
        assert!(
            sleeping
                .iter()
                .find(|i| i.turn == TURN_HERMES_RESUME)
                .unwrap()
                .enabled
        );
    }

    /// THE SLOT-SEED COVERAGE: every slot any live element on the card reads (Bind,
    /// Gauge, live Pill) is seeded exactly once by [`console_slot_seeds`] — a live
    /// executor seeded from it drives the WHOLE card, nothing dangling, nothing doubled.
    #[test]
    fn slot_seeds_cover_every_live_read_exactly_once() {
        let model = scoped();
        let tree = console_card(&model);
        let mut read_slots: Vec<usize> = Vec::new();
        walk(&tree, &mut |n| match n {
            ViewNode::Bind { slot, .. } | ViewNode::Gauge { slot, .. } => read_slots.push(*slot),
            ViewNode::Pill { slot: Some(s), .. } => read_slots.push(*s),
            _ => {}
        });
        let seeds = console_slot_seeds(&model);
        let mut seed_slots: Vec<usize> = seeds.iter().map(|(s, _)| *s).collect();
        seed_slots.sort_unstable();
        let dedup = {
            let mut d = seed_slots.clone();
            d.dedup();
            d
        };
        assert_eq!(seed_slots, dedup, "no slot is seeded twice");
        read_slots.sort_unstable();
        read_slots.dedup();
        assert_eq!(
            read_slots, seed_slots,
            "seeds cover exactly the slots the card reads"
        );
        // The two slot regions never collide (vat region tops out below the hermes base).
        assert!(vat_status_slot(MAX_SLOTTED_VATS - 1) < HERMES_SLOT_BASE);
        // And past the cap the vat slots CLAMP into region instead of invading it.
        assert!(vat_status_slot(MAX_SLOTTED_VATS + 5) < HERMES_SLOT_BASE);
    }

    /// THE VERIFY-ANYTHING PANEL is wired: an input whose submit fires the console
    /// verify turn (input → verified turn, the extended-input contract).
    #[test]
    fn verify_anything_input_fires_the_console_verify_turn() {
        let tree = console_card(&scoped());
        let mut found = false;
        walk(&tree, &mut |n| {
            if let ViewNode::Input {
                bind_view,
                fire_turn,
                submit_label,
            } = n
            {
                if fire_turn == TURN_CONSOLE_VERIFY {
                    assert_eq!(bind_view, "verify-anything");
                    assert_eq!(submit_label, "verify");
                    found = true;
                }
            }
        });
        assert!(found, "the verify-anything input is on the card");
    }

    /// PROGRESSIVE DISCLOSURE stays bind-safe: adept-only detail (full cell ids) is
    /// dropped in the simple projection WITHOUT disturbing the bind cursor (no `Bind`
    /// ever rides inside an `Adept` wrapper), so one `console_bind_values` snapshot
    /// paints both projections.
    #[test]
    fn adept_detail_carries_no_binds_and_discloses_cleanly() {
        let model = scoped();
        let tree = console_card(&model);
        // No Bind hides inside any Adept wrapper.
        walk(&tree, &mut |n| {
            if let ViewNode::Adept(inner) = n {
                walk(inner, &mut |m| {
                    assert!(
                        !matches!(m, ViewNode::Bind { .. }),
                        "adept detail must not consume the bind cursor"
                    );
                });
            }
        });
        // Simple hides the full hex; adept reveals it; bind counts agree.
        let simple = crate::tree::disclose(&tree, crate::tree::Disclosure::Simple);
        let adept = crate::tree::disclose(&tree, crate::tree::Disclosure::Adept);
        let count_binds = |t: &ViewNode| {
            let mut n = 0;
            walk(t, &mut |m| {
                if matches!(m, ViewNode::Bind { .. }) {
                    n += 1;
                }
            });
            n
        };
        assert_eq!(count_binds(&simple), console_bind_values(&model).len());
        assert_eq!(count_binds(&adept), console_bind_values(&model).len());
        let text_of = |t: &ViewNode| {
            let mut s = String::new();
            walk(t, &mut |m| {
                if let ViewNode::Text(x) = m {
                    s.push_str(x);
                }
            });
            s
        };
        let full_id = &model.computers[0].cell_id;
        assert!(
            !text_of(&simple).contains(full_id.as_str()),
            "simple hides the raw hex"
        );
        assert!(
            text_of(&adept).contains(full_id.as_str()),
            "adept shows the bones"
        );
    }

    /// THE STATE LIFT is total and honest: record words map to the vat framing, and an
    /// unknown word lands on Sleeping (exists, unclaimed) — never Running, never Reaped.
    #[test]
    fn vat_state_lifts_record_words_conservatively() {
        assert_eq!(VatState::from_record("running"), VatState::Running);
        assert_eq!(VatState::from_record("stopped"), VatState::Sleeping);
        assert_eq!(VatState::from_record("reaped"), VatState::Reaped);
        assert_eq!(VatState::from_record("wobbling"), VatState::Sleeping);
    }
}
