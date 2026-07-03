//! **THE ATTACH WIZARD** — "send your AI to live here" in five minutes.
//!
//! The desktop already HAS the whole confined-resident rail: the Agent Room
//! ([`super::agent_room`]) renders a resident's provable activity, and THE HIRELING
//! WELD ([`super::hireling`], over [`crate::resident_agent`] + `deos-hermes`) can
//! HIRE / STEP / FIRE a real cap-gated brain onto the LIVE World. But that machinery
//! wears the adept's face: the room's strip is one dense HIRE button under the
//! canonical attenuated mandate. A newcomer holding a Claude — or just curious what
//! "an agent living in your World" even means — has no warm front door onto it.
//!
//! This module is that door. It is a WIZARD WINDOW (its own [`WinKindTag::AttachWizard`],
//! anchored on its own sentinel cell) in the warm register of [`super::welcome`] — a
//! five-breath onboarding that walks a stranger from nothing to a living, stepping
//! resident:
//!
//!   1. **Name your resident** — a plain text name (or a suggested one), which becomes
//!      the ACP session label the room narrates it under.
//!   2. **Pick the brain** — the HERMETIC on-box [`deos_hermes::resident::ResidentBrain::OnBox`]
//!      by default (no key, no network — a real closed loop that thinks entirely on
//!      your box), or BYO key, HONESTLY LABELLED: the key is read from your OWN
//!      environment and reaches ONLY the provider call — never a tool-call, a
//!      receipt, the World the resident drives, or the ACP wire its reach travels
//!      (THE BRAIN-POCKET INVARIANT, [`deos_hermes::LlmKeys`]). The hermetic pick is a
//!      TRUTHFUL one: choosing it forces on-box even when a key is present
//!      ([`crate::resident_agent::AgentHandle::force_on_box`]), so no credential
//!      leaves the box.
//!   3. **Set the mandate + budget** — by DIRECT MANIPULATION: the resident starts at
//!      the canonical attenuated confinement (`write_file` denied, `terminal`
//!      rate-capped, a modest allowance) and the operator tightens or loosens each by
//!      poking it. Adoption IS attenuation, set with your own hands.
//!   4. **Review + HIRE** — the choices, plus the ground-truth brain label, then HIRE:
//!      the resident is minted on the LIVE World under exactly this mandate, the Agent
//!      Room opens pinned onto it, and it takes its FIRST perceive→decide→act beat —
//!      landing already stepping, not merely staged.
//!
//! ## No second machinery (the honesty line)
//!
//! The wizard invents NO parallel hire path. Its HIRE routes through the ONE
//! [`super::hireling::HirelingState::hire_with`] the room's own button now delegates
//! to — the same [`crate::resident_agent::hire_resident_seeded`] the phase-1
//! acceptance proved, the same mirror weld, the same in-band gate refusals. The
//! wizard only chooses the confinement + the brain in warm words; the substance is
//! the hireling's. A resident the wizard hires and one the room's HIRE button hires
//! are the same kind of real.
//!
//! ## The clobber-safe split (mirrors [`super::welcome`] / [`super::hireling`])
//!
//! This module owns the pure, gpui-free STATE MACHINE ([`WizardStep`], [`BrainPick`],
//! [`WizardState`] — the whole walk, its validation, and its [`WizardState::to_mandate`]
//! projection, all unit-tested below with zero renderer and zero environment), beside
//! an `impl DeosDesktop` block (the house pattern) that owns the window render, the
//! `cx.listener` click/step wiring, and the HIRE weld onto the hireling.

use gpui::{
    div, px, AnyElement, Context, FontWeight, InteractiveElement, IntoElement, MouseButton,
    MouseDownEvent, ParentElement, Styled,
};

use dregg_types::CellId;

use deos_hermes::resident::{resident_brain_from_env, ResidentBrain};

use crate::resident_agent::ResidentMandate;

use super::chrome::{
    bevel_raised, face_row, face_section, id_hex, id_short, nt_scroll_face, NT_DIM, NT_LABEL,
    NT_OK, NT_PANEL, NT_SELECT, NT_TITLE_TEXT, NT_WARN,
};
use super::layout::WinKindTag;
use super::{agent_room, DeosDesktop, FaceScrollKey};

/// The wizard's own anchor cell — a distinct non-ledger sentinel (like the Agent
/// Room's `0xA6`) so the wizard opens as its OWN window keyed apart from any
/// inspectable cell. `0xA7` sits one step past the room it feeds ("A7ttach").
pub fn wizard_window_cell() -> CellId {
    CellId::from_bytes([0xA7u8; 32]) // 'A7ttach' — the onboarding sentinel
}

/// Whether `cell` keys the Attach Wizard window.
pub fn is_attach_wizard(cell: &CellId) -> bool {
    cell == &wizard_window_cell()
}

/// A small palette of warm suggested names — a newcomer can poke one instead of
/// typing. They read as roles a resident might play, never as jargon.
pub const SUGGESTED_NAMES: [&str; 6] = [
    "scout",
    "archivist",
    "gardener",
    "courier",
    "sentinel",
    "scribe",
];

/// The default allowance the wizard opens the budget at — the canonical attenuated
/// mandate's body ([`ResidentMandate::attenuated`]), so the wizard STARTS at the
/// proven confinement and the operator moves from there.
pub const DEFAULT_ALLOWANCE: i64 = 10_000;
/// The step one poke of the budget moves the allowance by (direct manipulation).
pub const ALLOWANCE_STEP: i64 = 1_000;
/// The default `terminal` rate ceiling (the canonical attenuated mandate's).
pub const DEFAULT_TERMINAL_RATE: i64 = 5;
/// The `terminal` rate ceiling never climbs past this (a hand's budget, not a firehose).
pub const MAX_TERMINAL_RATE: i64 = 99;

// ── The brain pick ────────────────────────────────────────────────────────────────

/// The brain a resident will think with — the honest choice the wizard's step 2
/// offers. The default is [`BrainPick::Hermetic`]; a BYO key is opt-in and never
/// silently assumed.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum BrainPick {
    /// The HERMETIC on-box brain — the deterministic reactive
    /// [`deos_hermes::resident::ResidentBrain::OnBox`]: no key, no network, a REAL
    /// closed decide→gate→observe loop that runs entirely on your box. Choosing it
    /// PINS on-box even if a provider key sits in the environment — a truthful "no
    /// credential leaves this machine" pick.
    #[default]
    Hermetic,
    /// A BYO-key provider brain — resolved from the operator's OWN environment
    /// (`ANTHROPIC_API_KEY` / `HERMES_API_KEY`, the [`resident_brain_from_env`]
    /// precedence). The key reaches ONLY the provider call — never a tool-call, a
    /// receipt, the World, or the ACP wire (the brain-pocket invariant). When no key
    /// is present the rail honestly falls back to the on-box brain.
    ByoKey,
}

impl BrainPick {
    /// The warm card label.
    pub fn label(self) -> &'static str {
        match self {
            BrainPick::Hermetic => "Hermetic — on-box brain",
            BrainPick::ByoKey => "Bring your own key",
        }
    }

    /// The one plain sentence under the card.
    pub fn blurb(self) -> &'static str {
        match self {
            BrainPick::Hermetic => {
                "Thinks entirely on this box. No key, no network — a real closed loop, \
                 offline. Nothing about your resident ever leaves the machine."
            }
            BrainPick::ByoKey => {
                "Uses a provider key from your own environment. The key reaches only the \
                 provider call — never a tool-call, a receipt, your World, or the wire."
            }
        }
    }

    /// Whether this pick FORCES the on-box brain regardless of the environment.
    pub fn forces_on_box(self) -> bool {
        matches!(self, BrainPick::Hermetic)
    }

    /// Both picks, in display order (hermetic default first).
    pub const ALL: [BrainPick; 2] = [BrainPick::Hermetic, BrainPick::ByoKey];
}

/// THE BRAIN-POCKET INVARIANT, in the warm register — the reassurance the BYO-key
/// step shows so a stranger understands exactly where their credential can and
/// cannot go before they lean on it.
pub const BRAIN_POCKET_NOTE: &str =
    "Your key lives in a pocket only the brain can reach. It signs the request to \
     your provider and nothing else — it never rides a tool-call, a receipt, the \
     World your resident acts on, or the wire its reach travels.";

// ── The step machine ──────────────────────────────────────────────────────────────

/// The five breaths of the wizard. The first four are the SETUP walk (name · brain ·
/// mandate · review); [`WizardStep::Hired`] is the terminal celebration once the
/// resident is living in the Agent Room.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum WizardStep {
    /// Name your resident.
    #[default]
    Name,
    /// Pick the brain (hermetic on-box · BYO key).
    Brain,
    /// Set the attenuated mandate + budget by direct manipulation.
    Mandate,
    /// Review the choices + HIRE.
    Review,
    /// Hired — the resident is living (and stepping) in the Agent Room.
    Hired,
}

impl WizardStep {
    /// The warm headline for the step.
    pub fn title(self) -> &'static str {
        match self {
            WizardStep::Name => "Name your resident",
            WizardStep::Brain => "Give it a brain",
            WizardStep::Mandate => "Set what it may do",
            WizardStep::Review => "Look it over, then hire",
            WizardStep::Hired => "It lives here now",
        }
    }

    /// The one plain sentence under the headline.
    pub fn blurb(self) -> &'static str {
        match self {
            WizardStep::Name => "What should we call the agent that will live in your World?",
            WizardStep::Brain => "Where does it think? On this box, or through your own key.",
            WizardStep::Mandate => {
                "Every resident is confined. Tighten or loosen its reach with your own hands."
            }
            WizardStep::Review => "This is exactly the resident you are about to hire.",
            WizardStep::Hired => {
                "Your resident is in the Agent Room, already taking its first step."
            }
        }
    }

    /// The 1-based ordinal among the FOUR setup steps (Hired is `4`, the walk's end).
    pub fn ordinal(self) -> usize {
        match self {
            WizardStep::Name => 1,
            WizardStep::Brain => 2,
            WizardStep::Mandate => 3,
            WizardStep::Review => 4,
            WizardStep::Hired => 4,
        }
    }

    /// The next SETUP step (`Review` has no plain next — advancing it is the HIRE
    /// action, a distinct gesture; `Hired` is terminal).
    pub fn next(self) -> Option<WizardStep> {
        match self {
            WizardStep::Name => Some(WizardStep::Brain),
            WizardStep::Brain => Some(WizardStep::Mandate),
            WizardStep::Mandate => Some(WizardStep::Review),
            WizardStep::Review | WizardStep::Hired => None,
        }
    }

    /// The previous SETUP step (`Name` is the front door; `Hired` cannot go back —
    /// the resident is already living, and the wizard never un-hires by a Back click).
    pub fn prev(self) -> Option<WizardStep> {
        match self {
            WizardStep::Name | WizardStep::Hired => None,
            WizardStep::Brain => Some(WizardStep::Name),
            WizardStep::Mandate => Some(WizardStep::Brain),
            WizardStep::Review => Some(WizardStep::Mandate),
        }
    }

    /// The four setup steps, in order — the caller draws the progress dots from this.
    pub const SETUP: [WizardStep; 4] = [
        WizardStep::Name,
        WizardStep::Brain,
        WizardStep::Mandate,
        WizardStep::Review,
    ];
}

/// **The wizard's whole state** — the walk position plus every choice, all pure
/// primitives so the machine compiles and tests without a renderer OR an
/// environment. Owned by [`DeosDesktop`], keyed by [`wizard_window_cell`].
#[derive(Clone, Debug)]
pub struct WizardState {
    /// Which breath the operator is on.
    pub step: WizardStep,
    /// The resident's name (the ACP session label). Trimmed at [`Self::to_mandate`].
    pub name: String,
    /// Whether the name field is capturing keystrokes (the keyboard spine routes
    /// printable keys into `name` while this is set — see [`DeosDesktop::wizard_type_key`]).
    pub typing: bool,
    /// The chosen brain.
    pub brain: BrainPick,
    /// The allowance the resident's cell is born holding (its budget body).
    pub allowance: i64,
    /// The `terminal` tool's rate ceiling (a call budget on the resident's hands).
    pub terminal_rate: i64,
    /// Whether `write_file` is denied outright (the guaranteed legible refusal).
    pub deny_write: bool,
}

impl Default for WizardState {
    /// A fresh wizard opens named `scout`, brain hermetic, at the canonical
    /// attenuated mandate — so a stranger who pokes nothing still hires a real,
    /// well-confined resident, and every choice is a move away from a safe start.
    fn default() -> Self {
        WizardState {
            step: WizardStep::Name,
            name: "scout".to_string(),
            typing: false,
            brain: BrainPick::Hermetic,
            allowance: DEFAULT_ALLOWANCE,
            terminal_rate: DEFAULT_TERMINAL_RATE,
            deny_write: true,
        }
    }
}

impl WizardState {
    /// Whether the current step's requirements are met — the gate on advancing.
    /// Only the name step can block (a resident must be named); the rest are always
    /// satisfiable (the mandate is clamped to sane values as it is manipulated).
    pub fn can_advance(&self) -> bool {
        match self.step {
            WizardStep::Name => !self.name.trim().is_empty(),
            WizardStep::Brain | WizardStep::Mandate | WizardStep::Review => true,
            WizardStep::Hired => false,
        }
    }

    /// Whether the wizard is ready to HIRE — a named resident on the Review step.
    pub fn can_hire(&self) -> bool {
        self.step == WizardStep::Review && !self.name.trim().is_empty()
    }

    /// Advance one setup step if allowed; returns whether it moved. From `Review`
    /// there is no plain advance (HIRE is the distinct gesture), so this is `false`.
    pub fn advance(&mut self) -> bool {
        if !self.can_advance() {
            return false;
        }
        match self.step.next() {
            Some(next) => {
                self.step = next;
                self.typing = false;
                true
            }
            None => false,
        }
    }

    /// Step back one setup step if there is one; returns whether it moved.
    pub fn back(&mut self) -> bool {
        match self.step.prev() {
            Some(prev) => {
                self.step = prev;
                self.typing = false;
                true
            }
            None => false,
        }
    }

    /// Set the name outright (a suggested-name chip click).
    pub fn set_name(&mut self, name: &str) {
        self.name = name.to_string();
    }

    /// Append one typed character to the name (the keyboard spine's per-key push).
    pub fn push_name_char(&mut self, c: char) {
        // A name is a label, not a shell — keep it to legible, filesystem-safe glyphs.
        if c.is_alphanumeric() || matches!(c, ' ' | '-' | '_' | '.') {
            self.name.push(c);
        }
    }

    /// Delete the last name character (Backspace while typing).
    pub fn backspace_name(&mut self) {
        self.name.pop();
    }

    /// Pick the brain.
    pub fn set_brain(&mut self, brain: BrainPick) {
        self.brain = brain;
    }

    /// Move the allowance by `delta` (a budget poke), floored at zero — a resident
    /// with no allowance is honest (it simply cannot spend), never negative.
    pub fn bump_allowance(&mut self, delta: i64) {
        self.allowance = (self.allowance + delta).max(0);
    }

    /// Move the `terminal` rate ceiling by `delta`, clamped to `0..=MAX_TERMINAL_RATE`.
    /// Zero denies `terminal` outright (like `deny_write`); the cap keeps a hand from
    /// becoming a firehose.
    pub fn bump_terminal_rate(&mut self, delta: i64) {
        self.terminal_rate = (self.terminal_rate + delta).clamp(0, MAX_TERMINAL_RATE);
    }

    /// Toggle the `write_file` denial.
    pub fn toggle_deny_write(&mut self) {
        self.deny_write = !self.deny_write;
    }

    /// Whether the hire should PIN the on-box brain (the hermetic pick).
    pub fn force_on_box(&self) -> bool {
        self.brain.forces_on_box()
    }

    /// Mark the walk finished — the resident is hired and living in the Agent Room.
    pub fn mark_hired(&mut self) {
        self.step = WizardStep::Hired;
        self.typing = false;
    }

    /// **Project the wizard's choices into the confinement the hire lands under.**
    /// The name (trimmed) becomes the ACP session label; the manipulated budget,
    /// write denial, and terminal ceiling become the [`ResidentMandate`]. This is
    /// the ONLY coupling to the hire rail — the wizard hands over a mandate and the
    /// hireling does the minting (no duplicated hire logic).
    pub fn to_mandate(&self) -> ResidentMandate {
        ResidentMandate {
            session_id: self.name.trim().to_string(),
            allowance: self.allowance,
            deny_write: self.deny_write,
            terminal_rate: self.terminal_rate,
        }
    }
}

/// The plain-language account of the confinement the wizard's choices describe —
/// the review step's "here is exactly what it may do" line, in human words.
pub fn confinement_summary(state: &WizardState) -> String {
    let write = if state.deny_write {
        "cannot write files"
    } else {
        "may write files"
    };
    let terminal = if state.terminal_rate == 0 {
        "no terminal at all".to_string()
    } else {
        format!("terminal up to {} call(s) a session", state.terminal_rate)
    };
    format!(
        "{}, {terminal}, and an allowance of {} to spend acting.",
        write, state.allowance
    )
}

// ── The View half: the window render + the HIRE weld ──────────────────────────────

impl DeosDesktop {
    /// The wizard's live view state (created fresh on demand). Cloned for render like
    /// every other per-window state.
    fn attach_wizard_state(&mut self) -> WizardState {
        self.attach_wizards
            .entry(wizard_window_cell())
            .or_default()
            .clone()
    }

    /// **Open the Attach Wizard** — start a FRESH five-breath onboarding and land in
    /// it mold-ready. Reachable from the Spotter and the desktop menu. A fresh state
    /// each open makes "open the wizard" a predictable "start over", never a
    /// half-remembered walk.
    pub(super) fn open_attach_wizard(&mut self) {
        let cell = wizard_window_cell();
        self.attach_wizards.insert(cell, WizardState::default());
        self.land_in(cell, WinKindTag::AttachWizard);
        self.say(
            "Attach Wizard — send your AI to live here: name it, give it a brain, set what it \
             may do, then hire it into the Agent Room.",
        );
    }

    /// **HIRE from the wizard** — the five-breath walk's payoff. Builds the mandate
    /// from the operator's choices, hires through the SHARED
    /// [`Self::hire_room_resident_with`] (the hireling's one real hire path — no
    /// duplicated minting), then lands the resident already STEPPING: the Agent Room
    /// opens pinned onto it and it takes its first perceive→decide→act beat. Surfaces
    /// the honest refusal when the room is already staffed or the seed lane is spent.
    pub(super) fn wizard_hire(&mut self) {
        let cell = wizard_window_cell();
        let state = self.attach_wizard_state();
        if !state.can_hire() {
            self.say("Name your resident before hiring — a resident needs a name to answer to.");
            return;
        }
        // One resident per room. If the room is ALREADY staffed, the shared hire
        // would refuse — but it reports "staffed" (its button semantics), which the
        // wizard must NOT misread as "I hired a new one" (it would then celebrate +
        // step the SITTING resident under this wizard's name). Guard it here so the
        // wizard only celebrates a resident IT actually minted; the operator FIREs
        // the incumbent in the Agent Room first.
        if self.hireling.is_hired() {
            self.say(
                "A resident is already living here — open the Agent Room and FIRE it before \
                 hiring another (one resident per room).",
            );
            return;
        }
        let room = agent_room::agent_room_window_cell();
        let mandate = state.to_mandate();
        let force_on_box = state.force_on_box();
        // The one real hire path (the room's own HIRE button delegates here too).
        // Past the guard above, a `true` here means a NEW resident was minted.
        let staffed = self.hire_room_resident_with(room, mandate, force_on_box);
        if !staffed {
            // A genuine failure (e.g. the seed lane is spent) — already narrated by
            // the shared hire; leave the wizard on Review so the operator can retry.
            return;
        }
        // Land it ALREADY STEPPING — the first beat before the operator even arrives,
        // so the room is alive, not merely staged.
        self.step_room_resident();
        self.land_in(room, WinKindTag::AgentRoom);
        // The wizard closes its walk on the celebration; the resident lives in the room.
        self.attach_wizards.entry(cell).or_default().mark_hired();
        self.say("Your resident is living in the Agent Room now — watch it work.");
    }

    /// Route one keystroke into the wizard's name field when it is capturing typing.
    /// Called by the keyboard spine ([`Self::on_key_model`]) before the generic
    /// Escape ladder, so a focused name field eats printable keys and Backspace,
    /// while Escape/Enter close capture. Returns whether the key was consumed.
    pub(super) fn wizard_type_key(&mut self, key: &str, cmd: bool) -> bool {
        if cmd {
            // Never eat a chord (⌘K must still summon the Spotter over the wizard).
            return false;
        }
        let cell = wizard_window_cell();
        let Some(state) = self.attach_wizards.get_mut(&cell) else {
            return false;
        };
        if !state.typing {
            return false;
        }
        match key {
            "escape" | "enter" | "tab" => {
                state.typing = false;
                true
            }
            "backspace" | "delete" => {
                state.backspace_name();
                true
            }
            "space" => {
                state.push_name_char(' ');
                true
            }
            k => {
                let mut chars = k.chars();
                match (chars.next(), chars.next()) {
                    // A single-glyph key ("a", "7", "-") is a name character.
                    (Some(c), None) => {
                        state.push_name_char(c);
                        true
                    }
                    // A named key ("shift", "left", …) is not ours — let it pass.
                    _ => false,
                }
            }
        }
    }

    // ── Bake / test hooks (drive the wizard headlessly) ───────────────────────────

    /// BAKE: open the wizard (what the Spotter / menu entry does). Returns whether
    /// the wizard window is now open.
    pub fn bake_open_attach_wizard(&mut self) -> bool {
        self.open_attach_wizard();
        self.windows
            .contains_key(&(wizard_window_cell(), WinKindTag::AttachWizard))
    }

    /// BAKE: run the WHOLE wizard headlessly — name a resident, pick a brain, set a
    /// mandate by the same pure moves the buttons make, walk to Review, and HIRE.
    /// Returns whether a resident is hired AND has already committed at least one
    /// real turn (the "landed already stepping" guarantee), read off the live World.
    pub fn bake_wizard_run(&mut self, name: &str, hermetic: bool) -> bool {
        let cell = wizard_window_cell();
        self.open_attach_wizard();
        {
            let st = self.attach_wizards.entry(cell).or_default();
            st.set_name(name);
            st.advance(); // → Brain
            st.set_brain(if hermetic {
                BrainPick::Hermetic
            } else {
                BrainPick::ByoKey
            });
            st.advance(); // → Mandate
            st.bump_allowance(ALLOWANCE_STEP); // a direct-manipulation poke
            st.advance(); // → Review
        }
        self.wizard_hire();
        let hired = self.bake_resident_action_count() > 0;
        hired && self.attach_wizards.get(&cell).map(|s| s.step) == Some(WizardStep::Hired)
    }

    // ── The window render ─────────────────────────────────────────────────────────

    /// **The Attach Wizard window body** — the warm five-breath card: a progress
    /// spine, the current step's body (name · brain · mandate · review · hired), and
    /// the Back / Next / HIRE nav. Built fresh from the pure [`WizardState`] each
    /// paint; the listeners mutate that state and `cx.notify()`.
    pub(super) fn render_attach_wizard_window(
        &mut self,
        cell: CellId,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let state = self.attach_wizards.entry(cell).or_default().clone();
        let sc = self.face_scrolls.ensure(FaceScrollKey::Window(
            cell,
            WinKindTag::AttachWizard,
            state.step as u8,
        ));

        // The progress spine — four dots, the current one lit, the walk's shape at a
        // glance ("step 2 of 4").
        let mut spine = div().flex().flex_row().items_center().gap_1().my_1().child(
            div()
                .text_size(px(10.0))
                .text_color(gpui::rgb(NT_LABEL))
                .child(format!("step {} of 4", state.step.ordinal())),
        );
        for s in WizardStep::SETUP {
            let here =
                s == state.step || (state.step == WizardStep::Hired && s == WizardStep::Review);
            let done = s.ordinal() < state.step.ordinal();
            let color = if here {
                NT_SELECT
            } else if done {
                NT_OK
            } else {
                NT_DIM
            };
            spine = spine.child(
                div()
                    .w(px(14.0))
                    .h(px(14.0))
                    .flex()
                    .items_center()
                    .justify_center()
                    .text_size(px(9.0))
                    .text_color(gpui::rgb(color))
                    .font_weight(FontWeight::BOLD)
                    .child(format!("{}", s.ordinal())),
            );
        }

        let head = div()
            .flex()
            .flex_col()
            .gap_px()
            .child(
                div()
                    .text_size(px(13.0))
                    .font_weight(FontWeight::BOLD)
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
                    .child(state.step.title()),
            )
            .child(
                div()
                    .text_size(px(11.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(state.step.blurb()),
            );

        let body = match state.step {
            WizardStep::Name => self.render_wizard_name(cell, &state, cx),
            WizardStep::Brain => self.render_wizard_brain(cell, &state, cx),
            WizardStep::Mandate => self.render_wizard_mandate(cell, &state, cx),
            WizardStep::Review => self.render_wizard_review(cell, &state, cx),
            WizardStep::Hired => self.render_wizard_hired(&state, cx),
        };

        let nav = self.render_wizard_nav(cell, &state, cx);

        div()
            .id(gpui::SharedString::from(format!(
                "attach-wizard-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .flex()
            .flex_col()
            .gap_1()
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .child(spine)
            .child(head)
            .child(
                nt_scroll_face(
                    &sc,
                    div()
                        .id("attach-wizard-body")
                        .flex()
                        .flex_col()
                        .gap_1()
                        .p_1()
                        .child(body),
                )
                .flex_1()
                .min_h(px(0.0)),
            )
            .child(nav)
            .into_any_element()
    }

    /// Step 1 — the name field (click it to type) plus the suggested-name chips.
    fn render_wizard_name(
        &self,
        cell: CellId,
        state: &WizardState,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let caret = if state.typing { "▏" } else { "" };
        let name_line = if state.name.is_empty() {
            "(unnamed — click to type)".to_string()
        } else {
            format!("{}{caret}", state.name)
        };
        let field = bevel_raised(
            div()
                .id("attach-wizard-name-field")
                .px_2()
                .py_1()
                .text_size(px(13.0))
                .bg(gpui::rgb(if state.typing { 0xffffff } else { NT_PANEL }))
                .hover(|s| s.bg(gpui::rgb(0xffffff))),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.attach_wizards.entry(cell).or_default().typing = true;
                cx.notify();
            }),
        )
        .child(name_line);

        let mut chips = div().flex().flex_row().flex_wrap().gap_1().my_1();
        for suggested in SUGGESTED_NAMES {
            let selected = state.name == suggested;
            chips = chips.child(
                wiz_chip(format!("attach-wizard-name-{suggested}"), selected)
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            let st = this.attach_wizards.entry(cell).or_default();
                            st.set_name(suggested);
                            st.typing = false;
                            cx.notify();
                        }),
                    )
                    .child(suggested),
            );
        }

        div()
            .flex()
            .flex_col()
            .gap_1()
            .child(field)
            .child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child("or pick a name:"),
            )
            .child(chips)
            .into_any_element()
    }

    /// Step 2 — the two brain cards, the honest ground-truth line, and (on BYO) the
    /// brain-pocket invariant, in warm words.
    fn render_wizard_brain(
        &self,
        cell: CellId,
        state: &WizardState,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        // THE GROUND TRUTH — what will ACTUALLY think, resolved live: the hermetic
        // pick forces on-box; a BYO pick reflects the operator's real environment
        // (the provider by name, or an honest on-box fallback when no key is set).
        let actual = if state.force_on_box() {
            ResidentBrain::default().describe()
        } else {
            resident_brain_from_env().describe()
        };

        let mut cards = div().flex().flex_col().gap_1();
        for pick in BrainPick::ALL {
            let selected = pick == state.brain;
            cards = cards.child(
                wiz_card(format!("attach-wizard-brain-{}", pick.label()), selected)
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards.entry(cell).or_default().set_brain(pick);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .flex()
                            .flex_col()
                            .gap_px()
                            .child(
                                div()
                                    .text_size(px(12.0))
                                    .font_weight(FontWeight::BOLD)
                                    .child(pick.label()),
                            )
                            .child(
                                div()
                                    .text_size(px(10.0))
                                    .text_color(gpui::rgb(NT_LABEL))
                                    .child(pick.blurb()),
                            ),
                    ),
            );
        }

        let mut col = div()
            .flex()
            .flex_col()
            .gap_1()
            .child(cards)
            .child(face_row("will think with", &actual));

        // The brain-pocket reassurance is shown exactly when a key is in play.
        if state.brain == BrainPick::ByoKey {
            col = col.child(
                div()
                    .mt_1()
                    .p_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_WARN))
                    .child(BRAIN_POCKET_NOTE),
            );
        }
        col.into_any_element()
    }

    /// Step 3 — the mandate by direct manipulation: the allowance and terminal rate
    /// with -/+ pokes, and the write-file denial toggle.
    fn render_wizard_mandate(
        &self,
        cell: CellId,
        state: &WizardState,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let allowance_row = div()
            .flex()
            .flex_row()
            .items_center()
            .gap_1()
            .child(div().w(px(96.0)).text_size(px(11.0)).child("allowance"))
            .child(
                wiz_poke("attach-wizard-allow-dn")
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards
                                .entry(cell)
                                .or_default()
                                .bump_allowance(-ALLOWANCE_STEP);
                            cx.notify();
                        }),
                    )
                    .child("−"),
            )
            .child(
                div()
                    .w(px(72.0))
                    .text_size(px(12.0))
                    .font_weight(FontWeight::BOLD)
                    .child(format!("{}", state.allowance)),
            )
            .child(
                wiz_poke("attach-wizard-allow-up")
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards
                                .entry(cell)
                                .or_default()
                                .bump_allowance(ALLOWANCE_STEP);
                            cx.notify();
                        }),
                    )
                    .child("+"),
            );

        let rate_row = div()
            .flex()
            .flex_row()
            .items_center()
            .gap_1()
            .child(div().w(px(96.0)).text_size(px(11.0)).child("terminal rate"))
            .child(
                wiz_poke("attach-wizard-rate-dn")
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards
                                .entry(cell)
                                .or_default()
                                .bump_terminal_rate(-1);
                            cx.notify();
                        }),
                    )
                    .child("−"),
            )
            .child(
                div()
                    .w(px(72.0))
                    .text_size(px(12.0))
                    .font_weight(FontWeight::BOLD)
                    .child(if state.terminal_rate == 0 {
                        "denied".to_string()
                    } else {
                        format!("{}/session", state.terminal_rate)
                    }),
            )
            .child(
                wiz_poke("attach-wizard-rate-up")
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards
                                .entry(cell)
                                .or_default()
                                .bump_terminal_rate(1);
                            cx.notify();
                        }),
                    )
                    .child("+"),
            );

        let (write_label, write_color) = if state.deny_write {
            ("write files: DENIED", NT_WARN)
        } else {
            ("write files: allowed", NT_OK)
        };
        let write_row = wiz_card("attach-wizard-write-toggle", false)
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.attach_wizards
                        .entry(cell)
                        .or_default()
                        .toggle_deny_write();
                    cx.notify();
                }),
            )
            .child(
                div()
                    .text_size(px(11.0))
                    .text_color(gpui::rgb(write_color))
                    .child(format!("{write_label}  (click to toggle)")),
            );

        div()
            .flex()
            .flex_col()
            .gap_1()
            .child(allowance_row)
            .child(rate_row)
            .child(write_row)
            .child(
                div()
                    .mt_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(confinement_summary(state)),
            )
            .into_any_element()
    }

    /// Step 4 — the review card + the HIRE button (the HIRE gesture lives on the nav
    /// row's Next slot too; this restates the whole resident in one place).
    fn render_wizard_review(
        &self,
        _cell: CellId,
        state: &WizardState,
        _cx: &mut Context<Self>,
    ) -> AnyElement {
        let actual = if state.force_on_box() {
            ResidentBrain::default().describe()
        } else {
            resident_brain_from_env().describe()
        };
        div()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Your resident"))
            .child(face_row("name", state.name.trim()))
            .child(face_row("brain", state.brain.label()))
            .child(face_row("will think with", &actual))
            .child(face_row("may do", &confinement_summary(state)))
            .child(
                div()
                    .mt_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(
                        "HIRE mints it on your live World under exactly this mandate, opens the \
                         Agent Room onto it, and takes its first step.",
                    ),
            )
            .into_any_element()
    }

    /// The terminal celebration — the resident is living (and stepping) in the room.
    fn render_wizard_hired(&self, state: &WizardState, cx: &mut Context<Self>) -> AnyElement {
        let name = state.name.trim().to_string();
        let subject = self.hireling_subject_short();
        div()
            .flex()
            .flex_col()
            .gap_1()
            .child(
                div()
                    .text_size(px(12.0))
                    .text_color(gpui::rgb(NT_OK))
                    .child(format!(
                        "{name} is hired and living in the Agent Room{subject}."
                    )),
            )
            .child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(
                        "It has already taken its first step. Open the Agent Room to watch it \
                         work — STEP it again, or FIRE it (a real revocation) when its shift ends.",
                    ),
            )
            .child(
                bevel_raised(
                    div()
                        .id("attach-wizard-open-room")
                        .px_2()
                        .py_1()
                        .text_size(px(11.0))
                        .hover(|s| {
                            s.bg(gpui::rgb(NT_SELECT))
                                .text_color(gpui::rgb(NT_TITLE_TEXT))
                        }),
                )
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                        this.land_in(agent_room::agent_room_window_cell(), WinKindTag::AgentRoom);
                        cx.notify();
                    }),
                )
                .child("Open the Agent Room →"),
            )
            .into_any_element()
    }

    /// The nav row — Back (when there is a step behind) and the forward gesture:
    /// Next on the setup steps, HIRE on Review, nothing on Hired.
    fn render_wizard_nav(
        &self,
        cell: CellId,
        state: &WizardState,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let mut row = div().flex().flex_row().gap_1().mt_1();

        if state.step.prev().is_some() {
            row = row.child(
                wiz_nav("attach-wizard-back")
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.attach_wizards.entry(cell).or_default().back();
                            cx.notify();
                        }),
                    )
                    .child("← Back"),
            );
        }

        match state.step {
            WizardStep::Review => {
                row = row.child(
                    wiz_nav("attach-wizard-hire")
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.wizard_hire();
                                cx.notify();
                            }),
                        )
                        .child("HIRE this resident"),
                );
            }
            WizardStep::Hired => {}
            _ => {
                let can = state.can_advance();
                row = row.child(
                    wiz_nav("attach-wizard-next")
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.attach_wizards.entry(cell).or_default().advance();
                                cx.notify();
                            }),
                        )
                        .child(if can { "Next →" } else { "Name it first" }),
                );
            }
        }
        row.into_any_element()
    }

    /// The hired resident's short id for the celebration line (`" · a1b2c3d4"` when
    /// staffed, empty otherwise) — read off the hireling, the room's live subject.
    fn hireling_subject_short(&self) -> String {
        self.hireling
            .resident()
            .map(|c| format!(" · {}", id_short(&c)))
            .unwrap_or_default()
    }
}

// ── The dumb chrome primitives (the View owns the listeners) ──────────────────────

/// A selectable chip (a suggested name) — raised NT chrome, navy when selected.
fn wiz_chip(elem_id: String, selected: bool) -> gpui::Stateful<gpui::Div> {
    let mut inner = div()
        .id(gpui::SharedString::from(elem_id))
        .px_2()
        .py_1()
        .text_size(px(11.0));
    if selected {
        inner = inner
            .bg(gpui::rgb(NT_SELECT))
            .text_color(gpui::rgb(NT_TITLE_TEXT));
    } else {
        inner = inner.hover(|s| {
            s.bg(gpui::rgb(NT_SELECT))
                .text_color(gpui::rgb(NT_TITLE_TEXT))
        });
    }
    bevel_raised(inner)
}

/// A selectable full-width card (a brain pick / the write toggle) — raised, navy
/// left border when selected so the choice reads at a glance.
fn wiz_card(elem_id: impl Into<String>, selected: bool) -> gpui::Stateful<gpui::Div> {
    let mut inner = div()
        .id(gpui::SharedString::from(elem_id.into()))
        .px_2()
        .py_1()
        .border_l_2()
        .border_color(gpui::rgb(if selected { NT_SELECT } else { NT_DIM }));
    if selected {
        inner = inner.bg(gpui::rgb(0xe0e0ff));
    } else {
        inner = inner.hover(|s| s.bg(gpui::rgb(0xe8e8f8)));
    }
    bevel_raised(inner)
}

/// A tiny square -/+ poke button for the mandate steppers.
fn wiz_poke(elem_id: &'static str) -> gpui::Stateful<gpui::Div> {
    bevel_raised(
        div()
            .id(gpui::SharedString::from(elem_id))
            .w(px(20.0))
            .h(px(18.0))
            .flex()
            .items_center()
            .justify_center()
            .text_size(px(12.0))
            .font_weight(FontWeight::BOLD)
            .hover(|s| {
                s.bg(gpui::rgb(NT_SELECT))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
            }),
    )
}

/// A nav button (Back / Next / HIRE) — the raised chrome with the navy hover.
fn wiz_nav(elem_id: &'static str) -> gpui::Stateful<gpui::Div> {
    bevel_raised(
        div()
            .id(gpui::SharedString::from(elem_id))
            .px_2()
            .py_1()
            .text_size(px(11.0))
            .hover(|s| {
                s.bg(gpui::rgb(NT_SELECT))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
            }),
    )
}

// ── Unit tests for the pure state machine (no renderer, no environment) ───────────

#[cfg(test)]
mod tests {
    use super::*;

    /// THE WALK: a fresh wizard starts named + hermetic at the canonical attenuated
    /// mandate, advances name → brain → mandate → review, and steps back the same
    /// way — the five-breath spine, gpui-free and env-free.
    #[test]
    fn the_walk_advances_and_retreats() {
        let mut w = WizardState::default();
        assert_eq!(w.step, WizardStep::Name);
        assert_eq!(w.name, "scout", "a fresh wizard opens named, never blank");
        assert_eq!(
            w.brain,
            BrainPick::Hermetic,
            "hermetic is the default brain"
        );
        assert_eq!(w.allowance, DEFAULT_ALLOWANCE);
        assert_eq!(w.terminal_rate, DEFAULT_TERMINAL_RATE);
        assert!(
            w.deny_write,
            "the canonical attenuated mandate denies write"
        );

        assert!(w.advance());
        assert_eq!(w.step, WizardStep::Brain);
        assert!(w.advance());
        assert_eq!(w.step, WizardStep::Mandate);
        assert!(w.advance());
        assert_eq!(w.step, WizardStep::Review);
        // Review has no PLAIN advance — HIRE is the distinct gesture.
        assert!(!w.advance());
        assert_eq!(w.step, WizardStep::Review);

        assert!(w.back());
        assert_eq!(w.step, WizardStep::Mandate);
        assert!(w.back());
        assert_eq!(w.step, WizardStep::Brain);
        assert!(w.back());
        assert_eq!(w.step, WizardStep::Name);
        // Name is the front door — no step behind it.
        assert!(!w.back());
    }

    /// An unnamed resident cannot advance past the name step or hire (a resident
    /// must answer to a name). Whitespace does not count.
    #[test]
    fn a_resident_must_be_named() {
        let mut w = WizardState::default();
        w.name = "   ".to_string();
        assert!(!w.can_advance(), "blank/whitespace name blocks advance");
        assert!(!w.advance());
        assert_eq!(w.step, WizardStep::Name, "the walk stays put until named");

        w.set_name("archivist");
        assert!(w.can_advance());
        assert!(w.advance());
        assert_eq!(w.step, WizardStep::Brain);
        // On Review, a named resident can hire; a blanked one cannot.
        w.step = WizardStep::Review;
        assert!(w.can_hire());
        w.name = "".to_string();
        assert!(!w.can_hire(), "a nameless resident is never hireable");
    }

    /// Typing into the name field appends legible glyphs, skips control junk, and
    /// backspaces — the keyboard spine's per-key moves, tested pure.
    #[test]
    fn name_typing_keeps_legible_glyphs() {
        let mut w = WizardState::default();
        w.name.clear();
        for c in "scout-9".chars() {
            w.push_name_char(c);
        }
        w.push_name_char('/'); // a shell glyph — refused
        w.push_name_char('\n'); // control — refused
        assert_eq!(w.name, "scout-9", "only filesystem-safe label glyphs land");
        w.backspace_name();
        assert_eq!(w.name, "scout-");
    }

    /// The brain pick drives BOTH the label and the honest force-on-box decision:
    /// hermetic pins on-box (a truthful "no key leaves the box"); BYO defers to the
    /// environment.
    #[test]
    fn brain_pick_is_an_honest_choice() {
        let mut w = WizardState::default();
        assert_eq!(w.brain, BrainPick::Hermetic);
        assert!(
            w.force_on_box(),
            "the hermetic pick FORCES on-box — no credential leaves the box"
        );
        w.set_brain(BrainPick::ByoKey);
        assert!(
            !w.force_on_box(),
            "a BYO-key pick defers to the environment (never silently forced on-box)"
        );
        assert_eq!(BrainPick::ALL.len(), 2, "hermetic default + BYO key");
        assert!(BrainPick::Hermetic.forces_on_box());
        assert!(!BrainPick::ByoKey.forces_on_box());
    }

    /// The mandate is set by DIRECT MANIPULATION, and each poke is clamped to a sane
    /// value — allowance floors at zero, the terminal rate stays in `0..=MAX`, and
    /// the write denial toggles.
    #[test]
    fn mandate_manipulation_is_clamped() {
        let mut w = WizardState::default();
        w.bump_allowance(ALLOWANCE_STEP);
        assert_eq!(w.allowance, DEFAULT_ALLOWANCE + ALLOWANCE_STEP);
        // Allowance never goes negative, however hard it is poked down.
        for _ in 0..100 {
            w.bump_allowance(-ALLOWANCE_STEP);
        }
        assert_eq!(w.allowance, 0, "allowance floors at zero, never negative");

        // The terminal rate clamps to 0..=MAX.
        for _ in 0..200 {
            w.bump_terminal_rate(1);
        }
        assert_eq!(w.terminal_rate, MAX_TERMINAL_RATE, "rate caps at MAX");
        for _ in 0..200 {
            w.bump_terminal_rate(-1);
        }
        assert_eq!(w.terminal_rate, 0, "rate floors at zero (terminal denied)");

        assert!(w.deny_write);
        w.toggle_deny_write();
        assert!(!w.deny_write);
    }

    /// THE PROJECTION: the wizard's choices become exactly the confinement the hire
    /// lands under — the name (trimmed) the session label, the manipulated budget +
    /// denials the mandate. This is the sole coupling to the hire rail.
    #[test]
    fn to_mandate_projects_the_choices() {
        let mut w = WizardState::default();
        w.set_name("  gardener  ");
        w.brain = BrainPick::ByoKey;
        w.allowance = 4_200;
        w.terminal_rate = 3;
        w.deny_write = false;

        let m = w.to_mandate();
        assert_eq!(
            m.session_id, "gardener",
            "the name is trimmed into the label"
        );
        assert_eq!(m.allowance, 4_200);
        assert_eq!(m.terminal_rate, 3);
        assert!(!m.deny_write);

        // The default wizard projects the canonical attenuated mandate exactly, so
        // "poke nothing and hire" lands the phase-1-proven confinement.
        let def = WizardState::default().to_mandate();
        let canon = ResidentMandate::attenuated("scout");
        assert_eq!(def.session_id, canon.session_id);
        assert_eq!(def.allowance, canon.allowance);
        assert_eq!(def.terminal_rate, canon.terminal_rate);
        assert_eq!(def.deny_write, canon.deny_write);
    }

    /// The confinement summary speaks HUMAN — the review's "what it may do" line
    /// never leaks jargon, and it reflects the live toggles.
    #[test]
    fn confinement_summary_is_plain() {
        let mut w = WizardState::default();
        let s = confinement_summary(&w);
        assert!(s.contains("cannot write files"));
        assert!(s.contains("terminal up to 5"));
        for jargon in ["capability", "receipt", "mandate", "attenuat"] {
            assert!(
                !s.contains(jargon),
                "the summary stays human: found {jargon:?}"
            );
        }
        w.deny_write = false;
        w.terminal_rate = 0;
        let s2 = confinement_summary(&w);
        assert!(s2.contains("may write files"));
        assert!(s2.contains("no terminal at all"));
    }

    /// Hiring is a terminal, one-way breath: `mark_hired` lands on the celebration
    /// and a Back click never un-hires (the resident is already living).
    #[test]
    fn hired_is_terminal() {
        let mut w = WizardState::default();
        w.step = WizardStep::Review;
        w.mark_hired();
        assert_eq!(w.step, WizardStep::Hired);
        assert!(!w.typing);
        assert!(!w.can_advance(), "the walk is over");
        assert!(!w.back(), "Back never un-hires a living resident");
        assert_eq!(w.step, WizardStep::Hired);
    }
}
