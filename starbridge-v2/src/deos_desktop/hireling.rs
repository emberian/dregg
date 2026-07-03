//! **THE HIRELING WELD** — HIRE and FIRE a REAL confined resident from the Agent
//! Room.
//!
//! The Agent Room ([`super::agent_room`]) renders any cell's provable activity —
//! but until this weld the desktop had no way to PUT a real agent behind that
//! glass. [`crate::resident_agent`] ships the whole rail (a deos-hermes brain
//! driving the cap-gated [`deos_hermes::HermesGateway`], every ADMITTED call
//! mirrored as a real verified turn on the LIVE [`World`], every refusal
//! surfaced as gate truth); this module gives the room its HIRE / STEP / FIRE
//! affordances over that rail:
//!
//!   * **HIRE** — [`HirelingState::hire`] scans the LIVE ledger for a free
//!     genesis seed pair ([`free_seed_pair`]) and calls
//!     [`crate::resident_agent::hire_resident_seeded`]: the resident's cell is
//!     born on the operator's own World under the canonical ATTENUATED mandate
//!     (`write_file` denied outright, `terminal` rate-capped, a modest
//!     allowance), and the room pins onto it. The brain is HERMETIC by default
//!     (the on-box `LocalBrain` — no key, no network); a BYO-key environment
//!     resolves a live provider brain and the strip SAYS SO by name
//!     ([`deos_hermes::resident::ResidentBrain::describe`] — the honest label,
//!     never the credential).
//!   * **STEP** — [`HirelingState::step`] drives ONE perceive→decide→act beat:
//!     the next objective from the [`StepPlanner`] rotation goes through the
//!     resident's real closed loop, admitted calls land as receipted turns on
//!     the live ledger (THE PULSE announces them as green toasts; the Actions
//!     face fills from `World::receipts()`), and each NEW gate refusal arrives
//!     as an amber toast + a REFUSED row. The loop is CLICK-DRIVEN — one beat
//!     per STEP — because the handle's gateway borrows a `!Send` runtime and
//!     the mirror commits on the desktop's own `Rc<RefCell<World>>`; a
//!     background brain thread is the named future seam, not tonight's claim.
//!     (On a BYO-key environment a beat blocks on the provider round-trips —
//!     the price of a REAL brain on the render thread, stated plainly.)
//!   * **FIRE** — [`HirelingState::fire`] revokes the mandate FOR REAL: one
//!     verified turn carrying `RevokeCapability` for every slot the resident
//!     holds on the LIVE ledger (read off the World, never the handle's
//!     self-report), then the handle drops — the cap-gated gateway and its
//!     persisted budgets retire with it. The `'static` `AgentRuntime` the
//!     gateway borrowed was leaked at hire (the app-lived `cockpit_surface`
//!     pattern); that memory outlives the firing — the honest seam, named.
//!
//! ## Two truths, kept distinct (the red-team line)
//!
//! A COMMITTED mirror turn is World truth — it has a receipt, a height, a spot
//! in the provenance log, and the pulse announces it. A gate REFUSAL is SESSION
//! truth — the confinement leg that bit lives in the gateway, not the ledger, so
//! it is surfaced ([`HirelingState::merge_refusals_into`] → REFUSED rows;
//! [`super::DeosDesktop::step_room_resident`] → amber toasts) and NEVER
//! fabricated as a `TurnRejected` on the World.
//!
//! ## The clobber-safe split
//!
//! The gpui-free model ([`HirelingState`], [`StepPlanner`], [`free_seed_pair`],
//! the report types, the narration + refusal-row pure fns — all unit-tested
//! below, on a REAL live `World`) lives beside an `impl DeosDesktop` block (the
//! house pattern `app_shelf.rs` uses) that owns only the listeners, the toast
//! pushes, the status-bar narration, and the strip chrome.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, Styled,
};

use dregg_types::CellId;

use deos_hermes::resident::{resident_brain_from_env, ResidentBrain};

use crate::agent::{AgentAction, AgentActivity};
use crate::resident_agent::{hire_resident_seeded, AgentHandle, Refusal, ResidentMandate};
use crate::world::{make_open_cell, revoke_capability, CommitOutcome, World};

use super::chrome::{bevel_raised, id_short, NT_DIM, NT_OK, NT_SELECT, NT_TITLE_TEXT, NT_WARN};
use super::{toasts, DeosDesktop};

/// The ACP session id the room's hireling runs under (also its human label).
pub const ROOM_SESSION_ID: &str = "agent-room-resident";

/// The genesis-seed lane the hireling scan starts at — `0x5A`/`0x5B` is exactly
/// the pair [`crate::resident_agent::hire_resident`] hard-codes, so the FIRST
/// hire on a fresh image lands on the same cells the phase-1 acceptance proved.
pub const HIRE_SEED_BASE: u8 = 0x5A;

// ── The gpui-free model ─────────────────────────────────────────────────────────

/// **The step planner** — the rotation of confined objectives a STEP beat hands
/// the resident's brain. The verbs are deliberate: the on-box `LocalBrain` plans
/// tools from prompt keywords, so the FIRST objective always reaches for the
/// denied `write_file` (confinement is legible on beat one) alongside allowed
/// search/read work, and later objectives spend the `terminal` rate budget so a
/// long session eventually meets the RATE leg refusing too. Pure; unit-tested.
#[derive(Clone, Debug, Default)]
pub struct StepPlanner {
    next: usize,
}

/// The objective rotation (see [`StepPlanner`]). Order matters: index 0 carries
/// the denied write verb so the first beat produces both mirrored turns AND an
/// in-band refusal.
pub const OBJECTIVES: [&str; 4] = [
    "survey the image: search the ledger docs, read the source, then write a survey note",
    "read the workspace state and run the build",
    "search for stale receipts and inspect the transcript",
    "write the shift report, then run the tests",
];

impl StepPlanner {
    /// The next objective in rotation (wraps forever — a resident always has work).
    pub fn next_objective(&mut self) -> &'static str {
        let o = OBJECTIVES[self.next % OBJECTIVES.len()];
        self.next += 1;
        o
    }
}

/// What HIRE produced — the facts the status bar narrates (the brain label is
/// [`deos_hermes::resident::ResidentBrain::describe`]'s secret-free line).
#[derive(Clone, Debug)]
pub struct HireReport {
    /// The resident's cell on the LIVE World (the room pins onto it).
    pub cell: CellId,
    /// The honest brain label — "on-box LocalBrain (no key)" or the provider name.
    pub brain: String,
    /// The gate mandate's `terminal` rate ceiling (narrated so the operator
    /// knows the hands' budget).
    pub terminal_rate: i64,
    /// The allowance the resident's cell was born holding.
    pub allowance: i64,
}

/// What one STEP beat produced — the mirror weld's counts plus the refusals that
/// are NEW this beat (the toast pushes fire once per refusal, not per repaint).
#[derive(Clone, Debug)]
pub struct StepReport {
    /// The 1-based beat index since hire.
    pub step: usize,
    /// The objective this beat handed the brain.
    pub objective: &'static str,
    /// Admitted calls that committed real verified turns on the LIVE World.
    pub mirrored: usize,
    /// Calls the gate refused in-band this beat.
    pub refused: usize,
    /// The brain's own closing line for the beat (its self-report — rendered as
    /// flavor, never as ground truth).
    pub agent_text: String,
    /// The refusals appended THIS beat (session truth, for the amber toasts).
    pub new_refusals: Vec<Refusal>,
}

/// What FIRE produced — the real revocation turn's outcome plus the census of
/// slots it stripped.
#[derive(Debug)]
pub struct FireReport {
    /// The fired resident's cell (still on the ledger — history is not erased).
    pub cell: CellId,
    /// How many capability slots the revocation turn carried.
    pub revoked_slots: usize,
    /// The World executor's verdict on the revocation turn; `None` when the
    /// c-list was already empty (no ghost turn is committed for nothing).
    pub outcome: Option<CommitOutcome>,
}

/// **The room's staffing state** — the live [`AgentHandle`] while hired, the
/// step planner, and the hired-or-last resident (kept after FIRE so the
/// executor's account of the departed stays one read away). Owned by
/// [`DeosDesktop`]; gpui-free, so the whole hire→step→fire flow is
/// `cargo test`-able on a real `World`.
#[derive(Default)]
pub struct HirelingState {
    /// The live handle while a resident is hired; `None` = the room is unstaffed.
    handle: Option<AgentHandle>,
    /// The honest brain label resolved at hire (env-resolved once per hire; a
    /// mid-session env change re-resolves at the next hire, not silently).
    brain: String,
    /// The confined-objective rotation the STEP beats draw from.
    planner: StepPlanner,
    /// Beats driven since hire (reset on the next hire, not on fire — the
    /// narration counts the CURRENT employment).
    steps: usize,
    /// The hired-or-last resident cell (survives fire; `bake_resident_action_count`
    /// and the room's history read it).
    last_resident: Option<CellId>,
}

impl HirelingState {
    /// Whether a resident is currently hired.
    pub fn is_hired(&self) -> bool {
        self.handle.is_some()
    }

    /// The CURRENTLY hired resident's cell, if staffed.
    pub fn resident(&self) -> Option<CellId> {
        self.handle.as_ref().map(|h| h.cell)
    }

    /// The hired-or-last resident (the room's subject even after a firing).
    pub fn subject(&self) -> Option<CellId> {
        self.resident().or(self.last_resident)
    }

    /// The honest brain label of the current employment ("" when never hired).
    pub fn brain(&self) -> &str {
        &self.brain
    }

    /// Beats driven since the current hire.
    pub fn steps(&self) -> usize {
        self.steps
    }

    /// How many admitted calls have mirrored real desktop receipts this hire.
    pub fn mirrored_count(&self) -> usize {
        self.handle.as_ref().map(|h| h.receipts.len()).unwrap_or(0)
    }

    /// Every gate refusal of the current employment (session truth, surfaced).
    pub fn refusals(&self) -> &[Refusal] {
        self.handle
            .as_ref()
            .map(|h| h.refusals.as_slice())
            .unwrap_or(&[])
    }

    /// **HIRE** — mint a real confined resident on the live `world` under the
    /// canonical attenuated mandate, thinking with the env-resolved brain. Refuses
    /// (a surfaced string, never a panic) when the room is already staffed or the
    /// seed lane is exhausted. The room's plain HIRE button drives this; the Attach
    /// Wizard drives [`HirelingState::hire_with`] with an operator-shaped mandate +
    /// a hermetic pin.
    pub fn hire(&mut self, world: &Rc<RefCell<World>>) -> Result<HireReport, String> {
        self.hire_with(world, ResidentMandate::attenuated(ROOM_SESSION_ID), false)
    }

    /// **HIRE with an operator-shaped confinement** — the SINGLE hire path (the
    /// plain [`HirelingState::hire`] is this with the canonical attenuated mandate
    /// and the env-resolved brain). `mandate` carries the resident's name
    /// (session id), allowance body, `write_file` denial, and `terminal` rate
    /// ceiling — exactly what the Attach Wizard sets by direct manipulation.
    /// `force_on_box` pins the HERMETIC on-box brain regardless of a provider key
    /// in the environment (the wizard's truthful "no credential leaves the box"
    /// pick); `false` resolves the brain from the env like the plain hire.
    ///
    /// There is NO duplicated minting here — the resident cell + cap-gated gateway
    /// are stood up by the one [`hire_resident_seeded`] the phase-1 acceptance
    /// proved; this only chooses the confinement + the brain and records the
    /// employment. Refuses when already staffed or the seed lane is exhausted.
    pub fn hire_with(
        &mut self,
        world: &Rc<RefCell<World>>,
        mandate: ResidentMandate,
        force_on_box: bool,
    ) -> Result<HireReport, String> {
        if self.handle.is_some() {
            return Err(
                "a resident is already hired — FIRE it first (one hireling per room)".to_string(),
            );
        }
        let (peer_seed, agent_seed) = free_seed_pair(&world.borrow()).ok_or_else(|| {
            "the hireling genesis-seed lane is exhausted (128 hires on one image)".to_string()
        })?;
        let (terminal_rate, allowance) = (mandate.terminal_rate, mandate.allowance);
        // The honest brain label — the hermetic pin names the on-box brain even
        // when a key is present; otherwise it is resolved from the SAME environment
        // the handle's per-beat resolver reads, so the label names what will
        // ACTUALLY think (on-box by default; the BYO-key provider by name).
        let brain = if force_on_box {
            ResidentBrain::default().describe()
        } else {
            resident_brain_from_env().describe()
        };
        let mut handle = hire_resident_seeded(world, mandate, peer_seed, agent_seed);
        handle.force_on_box = force_on_box;
        let cell = handle.cell;
        self.handle = Some(handle);
        self.brain = brain.clone();
        self.planner = StepPlanner::default();
        self.steps = 0;
        self.last_resident = Some(cell);
        Ok(HireReport {
            cell,
            brain,
            terminal_rate,
            allowance,
        })
    }

    /// **STEP** — one perceive→decide→act beat: the next planned objective
    /// through the resident's real closed loop. Admitted calls mirror as real
    /// verified turns on `world` (inside [`AgentHandle::prompt`]); refusals are
    /// gate truth, returned in [`StepReport::new_refusals`] for the caller's
    /// amber toasts. Refuses when the room is unstaffed.
    pub fn step(&mut self, world: &Rc<RefCell<World>>) -> Result<StepReport, String> {
        let handle = self
            .handle
            .as_mut()
            .ok_or_else(|| "the room is unstaffed — HIRE a resident first".to_string())?;
        let objective = self.planner.next_objective();
        let refusals_before = handle.refusals.len();
        let summary = handle.prompt(world, objective);
        self.steps += 1;
        Ok(StepReport {
            step: self.steps,
            objective,
            mirrored: summary.mirrored,
            refused: summary.refused,
            agent_text: summary.agent_text,
            new_refusals: handle.refusals[refusals_before..].to_vec(),
        })
    }

    /// **FIRE** — detach the resident with a REAL revocation: one verified turn
    /// carrying `RevokeCapability` for every slot its cell holds on the LIVE
    /// ledger, then the handle (gateway + budgets) drops. The cell and its
    /// receipts REMAIN on the World — firing revokes authority, it does not
    /// rewrite history. Refuses when the room is unstaffed.
    pub fn fire(&mut self, world: &Rc<RefCell<World>>) -> Result<FireReport, String> {
        let handle = self
            .handle
            .take()
            .ok_or_else(|| "the room is unstaffed — nothing to fire".to_string())?;
        let cell = handle.cell;
        // The held slots read off the LIVE ledger — never the handle's self-report.
        let slots: Vec<u32> = world
            .borrow()
            .ledger()
            .get(&cell)
            .map(|c| c.capabilities.iter().map(|cap| cap.slot).collect())
            .unwrap_or_default();
        let outcome = if slots.is_empty() {
            // Nothing to revoke — commit NOTHING (anti-ghost), report honestly.
            None
        } else {
            let turn = {
                let w = world.borrow();
                w.turn(
                    cell,
                    slots.iter().map(|s| revoke_capability(cell, *s)).collect(),
                )
            };
            Some(world.borrow_mut().commit_turn(turn))
        };
        // `handle` drops here: the cap-gated gateway and its persisted budgets
        // retire with it. Its `'static` AgentRuntime was leaked at hire — the
        // app-lived cockpit_surface pattern; that memory outlives the firing
        // (the named teardown seam).
        Ok(FireReport {
            cell,
            revoked_slots: slots.len(),
            outcome,
        })
    }

    /// Merge the current employment's gate refusals into `activity` as REFUSED
    /// rows — only when the room is watching the hired resident itself. The rows
    /// land at the FRONT (the face is most-recent-first, and a refusal is the
    /// freshest session truth). See the module doc's two-truths line.
    pub fn merge_refusals_into(&self, resident: CellId, activity: &mut AgentActivity) {
        let Some(handle) = self.handle.as_ref() else {
            return;
        };
        if handle.cell != resident {
            return;
        }
        let mut merged = refusal_rows(&handle.refusals);
        merged.append(&mut activity.actions);
        activity.actions = merged;
    }
}

/// Scan the hireling seed lane (`0x5A + 2n`, wrapping) for a pair whose derived
/// genesis ids are BOTH absent from the live ledger. [`make_open_cell`] is the
/// exact id derivation the genesis path uses (the id is over the seed-derived
/// key + token, independent of balance), so this check is precise — a fresh
/// image yields the phase-1 `0x5A`/`0x5B` pair; a hire→fire→hire cycle steps
/// past the still-living fired cells. `None` after a full lap (a 128-hire image
/// — the surfaced-refusal path, not a panic).
pub fn free_seed_pair(world: &World) -> Option<(u8, u8)> {
    let mut seed = HIRE_SEED_BASE;
    for _ in 0..128 {
        let peer_free = world.ledger().get(&make_open_cell(seed, 0).id()).is_none();
        let agent_free = world
            .ledger()
            .get(&make_open_cell(seed.wrapping_add(1), 0).id())
            .is_none();
        if peer_free && agent_free {
            return Some((seed, seed.wrapping_add(1)));
        }
        seed = seed.wrapping_add(2);
    }
    None
}

/// Project gate refusals into REFUSED-faced [`AgentAction`] rows, LATEST FIRST
/// (the Actions face renders most-recent-first). Each row names itself as a
/// gate verdict so a reader never mistakes session truth for a World turn.
pub fn refusal_rows(refusals: &[Refusal]) -> Vec<AgentAction> {
    refusals
        .iter()
        .rev()
        .map(|r| AgentAction {
            height: None,
            committed: false,
            receipt_hash: None,
            action_count: 0,
            computrons: 0,
            summary: format!(
                "{} — {} · gate verdict (session truth, no World turn)",
                r.tool, r.reason
            ),
        })
        .collect()
}

/// The HIRE narration — the status bar's account of the new employment, in the
/// desktop's dense verdict voice (the brain label is the honest provenance).
pub fn narrate_hire(report: &HireReport) -> String {
    format!(
        "HIRED resident {} — brain: {} · gate mandate: write_file DENIED, terminal \
         ≤{}/session, allowance {} · STEP drives one perceive→decide→act beat",
        id_short(&report.cell),
        report.brain,
        report.terminal_rate,
        report.allowance
    )
}

/// The STEP narration — committed count in the `outcome_verdict` vocabulary,
/// with the first NEW refusal carried in-band (REFUSED is a moment, not a mute).
pub fn narrate_step(report: &StepReport) -> String {
    match report.new_refusals.first() {
        Some(r) => format!(
            "Resident step {} → {} turn(s) committed · REFUSED — {} ({})",
            report.step, report.mirrored, r.tool, r.reason
        ),
        None => format!(
            "Resident step {} → {} turn(s) committed",
            report.step, report.mirrored
        ),
    }
}

// ── The View half: actuation + the strip chrome (the View owns the listeners) ────

impl DeosDesktop {
    /// **HIRE from the room strip** — attach a real confined resident to the live
    /// World, pin the Agent Room onto it, and grow the icon census now (THE PULSE
    /// would catch the genesis on its next beat; the click deserves the immediate
    /// read). Returns whether the room is staffed after the call.
    pub(super) fn hire_room_resident(&mut self, room: CellId) -> bool {
        self.hire_room_resident_with(room, ResidentMandate::attenuated(ROOM_SESSION_ID), false)
    }

    /// **HIRE with an operator-shaped confinement** — the shared body behind both
    /// the room's plain HIRE button ([`Self::hire_room_resident`], the canonical
    /// attenuated mandate + env brain) and the Attach Wizard's HIRE (an
    /// operator-shaped mandate + the hermetic pin). Pins the Agent Room onto the
    /// new resident, grows the icon census now (the click deserves the immediate
    /// read; THE PULSE would catch the genesis on its next beat anyway), narrates,
    /// and returns whether the room is staffed after the call. The hire LOGIC is
    /// not duplicated — it delegates to [`HirelingState::hire_with`].
    pub(super) fn hire_room_resident_with(
        &mut self,
        room: CellId,
        mandate: ResidentMandate,
        force_on_box: bool,
    ) -> bool {
        let world = Rc::clone(&self.world);
        match self.hireling.hire_with(&world, mandate, force_on_box) {
            Ok(report) => {
                self.agent_rooms.entry(room).or_default().resident = Some(report.cell);
                let mut v: Vec<CellId> = {
                    let w = self.world.borrow();
                    w.ledger().iter().map(|(id, _)| *id).collect()
                };
                v.sort();
                self.cells = v;
                self.say(format!("{}.", narrate_hire(&report)));
                true
            }
            Err(reason) => {
                self.say(format!("HIRE refused: {reason}"));
                self.hireling.is_hired()
            }
        }
    }

    /// **STEP from the room strip** — one real perceive→decide→act beat. The
    /// mirrored turns reach the glass through THE PULSE (green toasts + the
    /// status heartbeat, off the dynamics stream); each NEW gate refusal is
    /// announced HERE as an amber toast, because a refusal is session truth the
    /// pulse cannot see (it never lands a World event). Returns whether the beat
    /// produced any motion (a mirrored turn or a refusal).
    pub(super) fn step_room_resident(&mut self) -> bool {
        let world = Rc::clone(&self.world);
        match self.hireling.step(&world) {
            Ok(report) => {
                for r in &report.new_refusals {
                    self.toast_rack.push(
                        toasts::ToastKind::Refused,
                        format!("resident gate: {} — {}", r.tool, r.reason),
                    );
                }
                self.say(format!(
                    "{} (height {}).",
                    narrate_step(&report),
                    self.world.borrow().height()
                ));
                report.mirrored > 0 || !report.new_refusals.is_empty()
            }
            Err(reason) => {
                self.say(format!("Resident step refused: {reason}"));
                false
            }
        }
    }

    /// **FIRE from the room strip** — revoke the mandate with a real verified
    /// turn and drop the handle; the outcome lands in the status bar through the
    /// house [`Self::outcome_verdict`] voice (the pulse will announce the
    /// revocation turn itself — it is a foreign committed turn like any other).
    /// Returns whether the revocation turn COMMITTED (`true` also for the
    /// empty-c-list firing, where there was honestly nothing to revoke).
    pub(super) fn fire_room_resident(&mut self) -> bool {
        let world = Rc::clone(&self.world);
        match self.hireling.fire(&world) {
            Ok(report) => {
                let verdict = match &report.outcome {
                    Some(o) => Self::outcome_verdict(o),
                    None => "nothing to revoke — the c-list was already empty".to_string(),
                };
                self.say(format!(
                    "FIRED resident {} — revocation turn ({} slot(s)) → {} (height {}). \
                     The gate + its budgets retired with the handle.",
                    id_short(&report.cell),
                    report.revoked_slots,
                    verdict,
                    self.world.borrow().height()
                ));
                report
                    .outcome
                    .as_ref()
                    .map(|o| o.is_committed())
                    .unwrap_or(true)
            }
            Err(reason) => {
                self.say(format!("FIRE refused: {reason}"));
                false
            }
        }
    }

    // ── Bake / test hooks (drive the weld headlessly) ─────────────────────────────

    /// HIRE a resident into the Agent Room (what the strip's HIRE button does) —
    /// a real `hire_resident_seeded` on the live World. Returns whether the room
    /// is staffed after the call.
    pub fn bake_hire_resident(&mut self) -> bool {
        let room = super::agent_room::agent_room_window_cell();
        self.hire_room_resident(room)
    }

    /// Drive ONE resident beat (what the strip's STEP button does) and report
    /// whether it produced motion (a mirrored turn or an in-band refusal).
    pub fn bake_step_resident(&mut self) -> bool {
        self.step_room_resident()
    }

    /// FIRE the hired resident (what the strip's FIRE button does) — the real
    /// revocation turn. Returns whether that turn COMMITTED.
    pub fn bake_fire_resident(&mut self) -> bool {
        self.fire_room_resident()
    }

    /// The hired-or-last resident's committed-turn count read off the LIVE
    /// World's receipt log (the executor's account — never the handle's
    /// self-report). `0` when the room never staffed.
    pub fn bake_resident_action_count(&self) -> usize {
        match self.hireling.subject() {
            Some(cell) => self
                .world
                .borrow()
                .receipts()
                .iter()
                .filter(|r| r.agent == cell)
                .count(),
            None => 0,
        }
    }

    // ── The strip chrome ──────────────────────────────────────────────────────────

    /// **The hireling strip** — mounted under the Agent Room's picker. Unstaffed:
    /// the HIRE affordance plus the honest would-be brain + mandate line.
    /// Staffed: the employment facts, the STEP / FIRE buttons, and the freshest
    /// gate refusal in amber (visible without switching to the Actions face).
    pub(super) fn render_hireling_strip(&self, room: CellId, cx: &mut Context<Self>) -> AnyElement {
        let mut strip = div().flex().flex_col().gap_1().my_1();
        match self.hireling.resident() {
            None => {
                // The would-be brain, resolved from the SAME env the hire will read.
                let brain = resident_brain_from_env().describe();
                strip = strip.child(
                    div()
                        .flex()
                        .flex_row()
                        .flex_wrap()
                        .gap_1()
                        .items_center()
                        .child(
                            hire_button_chrome("hireling-hire")
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                        this.hire_room_resident(room);
                                        cx.notify();
                                    }),
                                )
                                .child("HIRE resident  (real confined brain)"),
                        )
                        .child(
                            div()
                                .text_size(px(10.0))
                                .text_color(gpui::rgb(NT_DIM))
                                .child(format!(
                                    "unstaffed · brain: {brain} · mandate: write_file DENIED · \
                                 terminal rate-capped · one beat per STEP"
                                )),
                        ),
                );
            }
            Some(resident) => {
                strip = strip.child(
                    div()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(NT_OK))
                        .child(format!(
                            "staffed · resident {} · brain: {} · {} step(s) · {} mirrored \
                             turn(s) · {} refusal(s)",
                            id_short(&resident),
                            self.hireling.brain(),
                            self.hireling.steps(),
                            self.hireling.mirrored_count(),
                            self.hireling.refusals().len()
                        )),
                );
                strip = strip.child(
                    div()
                        .flex()
                        .flex_row()
                        .flex_wrap()
                        .gap_1()
                        .child(
                            hire_button_chrome("hireling-step")
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                        this.step_room_resident();
                                        cx.notify();
                                    }),
                                )
                                .child("STEP  (one perceive→decide→act beat)"),
                        )
                        .child(
                            hire_button_chrome("hireling-fire")
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                        this.fire_room_resident();
                                        cx.notify();
                                    }),
                                )
                                .child("FIRE  (revoke mandate — a real turn)"),
                        ),
                );
                if let Some(r) = self.hireling.refusals().last() {
                    strip = strip.child(
                        div()
                            .text_size(px(10.0))
                            .text_color(gpui::rgb(NT_WARN))
                            .child(format!("gate REFUSED {} — {}", r.tool, r.reason)),
                    );
                }
            }
        }
        strip.into_any_element()
    }
}

/// The raised NT chrome of one strip button (id + dense padding + navy hover).
/// The CALLER chains its own `.on_mouse_down(…, cx.listener(…))` + `.child(label)`
/// — the View owns the listeners (the clobber-safe split); this is dumb chrome.
fn hire_button_chrome(elem_id: &'static str) -> gpui::Stateful<gpui::Div> {
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

// ── Unit tests for the gpui-free core (real hire → step → fire on a live World) ──

#[cfg(test)]
mod tests {
    use super::*;

    /// The rotation wraps forever, and its FIRST objective carries the denied
    /// write verb beside allowed search/read verbs — confinement is legible on
    /// beat one (the on-box brain plans tools from these exact keywords).
    #[test]
    fn planner_rotation_reaches_the_denied_verb_first() {
        let mut planner = StepPlanner::default();
        let first = planner.next_objective();
        assert!(first.contains("write"), "beat one reaches the denied tool");
        assert!(
            first.contains("search") && first.contains("read"),
            "beat one also does allowed work (the refusal is IN-BAND, not fatal)"
        );
        // The rotation wraps: OBJECTIVES.len() more beats land back on the first.
        for _ in 0..OBJECTIVES.len() - 1 {
            planner.next_objective();
        }
        assert_eq!(planner.next_objective(), first, "the rotation wraps");
        // Every objective drives at least one verb the brain recognizes.
        for o in OBJECTIVES {
            assert!(
                ["search", "read", "inspect", "write", "run", "build", "test"]
                    .iter()
                    .any(|v| o.contains(v)),
                "objective '{o}' has a recognized verb"
            );
        }
    }

    /// Refusal rows are REFUSED-faced (never committed, no receipt), latest
    /// first, and name themselves as gate verdicts — the two-truths line.
    #[test]
    fn refusal_rows_are_refused_faced_and_latest_first() {
        let rows = refusal_rows(&[
            Refusal {
                tool: "write_file".to_string(),
                reason: "denied by mandate".to_string(),
            },
            Refusal {
                tool: "terminal".to_string(),
                reason: "rate exceeded".to_string(),
            },
        ]);
        assert_eq!(rows.len(), 2);
        assert!(
            rows[0].summary.starts_with("terminal"),
            "latest refusal first (the face is most-recent-first)"
        );
        for row in &rows {
            assert!(!row.committed, "a refusal is never a committed row");
            assert!(row.receipt_hash.is_none(), "no receipt can exist for it");
            assert!(
                row.summary.contains("gate verdict"),
                "the row names itself session truth"
            );
        }
    }

    /// The narrations carry the verdict voice: a refusing beat says REFUSED with
    /// the tool + reason in-band; a clean beat counts its committed turns.
    #[test]
    fn narrations_speak_the_verdict_voice() {
        let report = StepReport {
            step: 1,
            objective: OBJECTIVES[0],
            mirrored: 3,
            refused: 1,
            agent_text: String::new(),
            new_refusals: vec![Refusal {
                tool: "write_file".to_string(),
                reason: "denied by mandate".to_string(),
            }],
        };
        let line = narrate_step(&report);
        assert!(line.contains("3 turn(s) committed"));
        assert!(line.contains("REFUSED — write_file (denied by mandate)"));
        let clean = narrate_step(&StepReport {
            new_refusals: vec![],
            refused: 0,
            ..report
        });
        assert!(!clean.contains("REFUSED"));
    }

    /// THE ROOM'S ACCEPTANCE (gpui-free): hire a REAL confined resident onto a
    /// LIVE World, drive one STEP beat, and prove (a) its admitted calls mirrored
    /// receipted turns onto the live ledger, (b) its over-reach was REFUSED
    /// in-band and merges as a REFUSED row, and (c) FIRE commits a REAL
    /// revocation turn that strips the live mandate — then a re-hire lands on a
    /// FRESH seed pair (no genesis collision). Hermetic on a keyless env (the
    /// on-box brain); a BYO-key env drives the same loop live.
    #[test]
    fn hire_step_fire_is_real_on_a_live_world() {
        let (world, anchors) = crate::world::demo_world();
        let live = Rc::new(RefCell::new(world));
        let mut room = HirelingState::default();

        // Unstaffed refusals are surfaced, never panics.
        assert!(room.fire(&live).is_err());
        assert!(room.step(&live).is_err());

        let hired = room.hire(&live).expect("the room hires");
        assert!(room.is_hired());
        assert_eq!(room.subject(), Some(hired.cell));
        assert!(
            !hired.brain.is_empty(),
            "the brain label is honest, not blank"
        );
        // One hireling per room — the double hire is a surfaced refusal.
        assert!(room.hire(&live).is_err());

        let pre_receipts = live.borrow().receipts().len();
        let pre_height = live.borrow().height();
        let report = room.step(&live).expect("one beat drives");

        // (a) REAL receipted turns landed on the LIVE World.
        assert!(report.mirrored >= 1, "the beat mirrored at least one turn");
        assert_eq!(
            live.borrow().receipts().len(),
            pre_receipts + report.mirrored,
            "the live provenance log grew by exactly the mirrored turns"
        );
        assert_eq!(
            live.borrow().height(),
            pre_height + report.mirrored as u64,
            "the live World height advanced by exactly the mirrored turns"
        );

        // (b) The denied write was REFUSED in-band, and merges as a REFUSED row.
        assert!(
            report.new_refusals.iter().any(|r| r.tool == "write_file"),
            "the attenuated mandate refused the write: {:?}",
            report.new_refusals
        );
        let mut activity = AgentActivity::build(&live.borrow(), hired.cell, 24);
        let committed_rows = activity.actions.len();
        room.merge_refusals_into(hired.cell, &mut activity);
        assert!(activity.actions.len() > committed_rows, "rows were merged");
        assert!(
            !activity.actions[0].committed && activity.actions[0].summary.contains("gate verdict"),
            "the freshest row is the surfaced refusal"
        );
        // Watching a DIFFERENT cell merges nothing (the truth stays scoped).
        let mut other = AgentActivity::build(&live.borrow(), anchors[2], 24);
        let other_rows = other.actions.len();
        room.merge_refusals_into(anchors[2], &mut other);
        assert_eq!(other.actions.len(), other_rows);

        // (c) FIRE: a real revocation turn strips the LIVE mandate.
        let held_before = live
            .borrow()
            .ledger()
            .get(&hired.cell)
            .map(|c| c.capabilities.iter().count())
            .expect("the resident's cell lives on");
        assert!(held_before >= 1, "the hire granted a real cap edge");
        let fired = room.fire(&live).expect("the room fires");
        assert_eq!(fired.cell, hired.cell);
        assert_eq!(fired.revoked_slots, held_before);
        assert!(
            fired.outcome.as_ref().is_some_and(|o| o.is_committed()),
            "the revocation is a COMMITTED verified turn"
        );
        let held_after = live
            .borrow()
            .ledger()
            .get(&hired.cell)
            .map(|c| c.capabilities.iter().count())
            .expect("firing never erases the cell — history stays");
        assert_eq!(held_after, 0, "the LIVE mandate is empty after revocation");
        assert!(!room.is_hired(), "the room is unstaffed after the firing");
        assert_eq!(
            room.subject(),
            Some(hired.cell),
            "the departed stays the room's readable subject"
        );

        // RE-HIRE lands on a FRESH seed pair — no genesis collision with the
        // still-living fired cells.
        let second = room.hire(&live).expect("re-hire scans a free pair");
        assert_ne!(second.cell, hired.cell, "a fresh resident cell");
        assert!(
            live.borrow().ledger().get(&second.cell).is_some(),
            "the second resident lives on the same World"
        );
    }

    /// The seed scan: a fresh image yields the phase-1 `0x5A`/`0x5B` pair; after
    /// those ids exist it steps to the next free pair; and it is a surfaced
    /// `None` (never a panic) when the lane is exhausted.
    #[test]
    fn free_seed_pair_scans_past_occupied_ids() {
        let mut world = World::new();
        assert_eq!(free_seed_pair(&world), Some((0x5A, 0x5B)));
        // Occupy the base pair (exactly what one hire's genesis does).
        world.genesis_cell(0x5A, 0);
        world.genesis_cell(0x5B, 0);
        assert_eq!(free_seed_pair(&world), Some((0x5C, 0x5D)));
        // A half-occupied pair is skipped whole (peer + agent must BOTH be free).
        world.genesis_cell(0x5C, 0);
        assert_eq!(free_seed_pair(&world), Some((0x5E, 0x5F)));
    }
}
