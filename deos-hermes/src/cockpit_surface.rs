//! THE INTERACTIVE CONFINED-AGENT DOCK — a real agent chat, gated + receipted.
//!
//! This is the deos answer to a Claude/Cursor sidebar: you TYPE a prompt to the
//! confined Hermes agent, its reply streams in token-by-token, every tool it
//! reaches for appears LIVE in the ledger the instant deos's [`HermesGateway`]
//! decides — ✓ receipted (with the remaining budget) or ✗ refused (naming the
//! mandate leg that bit) — and the mandate panel's budget bars visibly deplete as
//! the agent spends. Multi-turn: the conversation accumulates across prompts.
//!
//! Mounting it in starbridge-v2's dock is a [`CockpitSurface`] forward (see the
//! 2-edit note below); the heavy logic — the live [`AgentDockView`] over a driven
//! [`HermesSession`] — lives here.
//!
//! ## How the live loop runs (foreground-stepped, no Send)
//!
//! The grounding runtime (the verified Lean executor inside [`dregg_sdk`]) is
//! `!Send`, so the ACP loop can NOT run on a background thread. Instead it runs on
//! the gpui foreground: on submit, [`HermesSession::run`] drives the whole prompt
//! over the in-process [`MockHermesPeer`] (or, with [`HermesSession::live`], the
//! real `hermes-acp` subprocess), capturing each [`StreamEvent`] + a mandate
//! snapshot. The view BUFFERS those and a gpui timer drains ONE per tick into the
//! [`AgentDockModel`], firing `cx.notify()` after each — so the reply streams in,
//! tool-calls land one at a time, and the budget depletes visibly. The events,
//! receipts, and verdicts are all REAL; the timer only paces the painting.
//!
//! ## THE READY-TO-DROP MOUNT (the 2-edit note)
//!
//! ```text
//! // EDIT 1 — starbridge-v2/src/dock/hermes_surface.rs  (NEW, gpui is always
//! //          present in starbridge-v2; the dock module is gpui-side already)
//! use deos_hermes::cockpit_surface::HermesDockSurface;
//! use crate::dock::surface::{CockpitSurface, SurfaceId};
//! use gpui::{AnyElement, App, FocusHandle, SharedString, Window};
//!
//! impl CockpitSurface for HermesDockSurface {
//!     fn item_id(&self) -> SurfaceId { SurfaceId(self.surface_id()) }
//!     fn tab_label(&self) -> SharedString { self.tab_label() }
//!     fn render_body(&mut self, w: &mut Window, cx: &mut App) -> AnyElement {
//!         self.render_body(w, cx)
//!     }
//!     fn focus_handle(&self, cx: &App) -> FocusHandle { self.focus_handle(cx) }
//!     fn is_dirty(&self, cx: &App) -> bool { self.is_dirty(cx) }
//!     fn boxed_clone(&self) -> Box<dyn CockpitSurface> { Box::new(self.clone()) }
//! }
//!
//! // EDIT 2 — starbridge-v2/src/dock/mod.rs
//! pub mod hermes_surface;
//! ```
//!
//! Plus the path dependency in starbridge-v2/Cargo.toml:
//! `deos-hermes = { path = "../deos-hermes" }`. Construct one with
//! [`HermesDockSurface::new_interactive`] (a fresh confined session) and mount it.

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};
use std::time::Duration;

use gpui::{
    AnyElement, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, Window, div, px,
};
use gpui_component::input::{Input, InputEvent, InputState};
use gpui_component::{h_flex, v_flex};

use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

use crate::acp_client::{AcpPeer, StreamEvent};
use crate::agent_peer::HermesAgentPeer;
use crate::bridge::HermesGateway;
use crate::grant_registry::GrantRegistry;
use crate::mandate::Mandate;
use crate::mock_peer::{MockHermesPeer, ScriptedCall};
use crate::resident::resident_brain_from_env;
use crate::surface::{
    AgentDockModel, ChatEntry, MandateBudget, PermissionMoment, RefusalLeg, ToolLine,
};

/// A buffered streaming step: one ACP delta + the mandate snapshot at that moment
/// (so the dock can repaint depleting budgets exactly as the gate spent them).
type StreamStep = (StreamEvent, Option<Mandate>);

/// A live, self-contained confined-agent session the dock drives. Owns the
/// grounding runtime + the [`HermesGateway`] (so budgets persist across turns) and
/// turns a typed prompt into an ordered stream of [`StreamStep`]s.
///
/// The runtime is `!Send`, so this lives on the gpui foreground thread. The
/// runtime is leaked once (a session lives for the whole app), which lets the
/// gateway hold a `'static` borrow into it without a self-referential struct.
pub struct HermesSession {
    /// The cap-gated gateway (held in an `Option` so a prompt run can `take()` it
    /// into the driving `AcpClient` and restore it — budgets persist across
    /// turns). The agent's "brain" is a prompt-derived scripted turn over the
    /// in-process [`MockHermesPeer`]: the live ACP wire + the real gate are
    /// exercised either way; only the brain is stood-in, per the confined-agent
    /// honest scope. A real `hermes-acp` subprocess swaps in here with no change
    /// to the rest of the dock.
    gateway: Option<HermesGateway<'static>>,
    session_id: String,
    clock: i64,
}

impl HermesSession {
    /// Open a fresh confined session with the standard deos confinement (per-kind
    /// floors + the curated per-tool tightenings: terminal rate-5, etc.).
    pub fn new(session_id: &str) -> HermesSession {
        let mut cclerk = AgentCipherclerk::new();
        let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
        // Leak the runtime: one per app-lived session; the gateway's `'static`
        // borrow points into it. (Box::leak is the standard owned-`'static` trick
        // for a long-lived `!Send` resource a view must hold without self-ref.)
        let runtime: &'static AgentRuntime = Box::leak(Box::new(AgentRuntime::new(
            Arc::new(RwLock::new(cclerk)),
            "deos",
        )));
        let registry = GrantRegistry::default_for_session(1_000).with_standard_tool_grants(1_000);
        let gateway = HermesGateway::new(runtime, root, registry);
        HermesSession {
            gateway: Some(gateway),
            session_id: session_id.to_string(),
            clock: 10,
        }
    }

    /// Open a confined session over an EXPLICIT, caller-built gateway — for a
    /// host that wants a specific confinement (a tighter per-tool rate, a
    /// whole-tool deny) rather than the standard floors `new` installs. The
    /// gateway must be `'static` (the live dock holds it for the app's life; the
    /// `Box::leak`'d runtime in `new` is the canonical way to get one). The
    /// session's clock starts at `start_clock` (the deadline-leg demo needs to
    /// place a prompt past the mandate deadline).
    pub fn with_gateway(
        session_id: &str,
        gateway: HermesGateway<'static>,
        start_clock: i64,
    ) -> HermesSession {
        HermesSession {
            gateway: Some(gateway),
            session_id: session_id.to_string(),
            clock: start_clock,
        }
    }

    /// Drive one prompt to completion, returning the ordered stream of deltas
    /// (each paired with the live mandate at that moment).
    ///
    /// THE WELD (the cheapest-wow swap): this now drives a REAL brain, not the
    /// keyword-script stand-in. By default the confined loop runs the on-box
    /// [`crate::LocalBrain`] — a genuine decide→gate→observe loop that needs no
    /// key and no network, so the dock is a real agent while staying hermetic;
    /// [`resident_brain_from_env`] upgrades it to a live BYO-key
    /// [`crate::HttpLlm`] when `ANTHROPIC_API_KEY` / `HERMES_API_KEY` is set. The
    /// scripted [`MockHermesPeer`] is retained as an escape hatch — set
    /// `DEOS_HERMES_MOCK=1` to force the old, fixed-list brain (e.g. for a
    /// deterministic screenshot). Either way the ACP wire, the gate, and the
    /// receipts are the SAME real surface; only the decision-maker changed.
    pub fn run(&mut self, prompt: &str) -> Vec<StreamStep> {
        if std::env::var("DEOS_HERMES_MOCK").is_ok() {
            let (reply, script) = scripted_turn(prompt);
            let peer = MockHermesPeer::with_reply(&self.session_id, script, &reply);
            self.drive(peer, prompt)
        } else {
            let brain = resident_brain_from_env();
            let peer = HermesAgentPeer::new(&self.session_id, brain);
            self.drive(peer, prompt)
        }
    }

    /// Drive one prompt over an arbitrary [`AcpPeer`] (a real brain-driven peer,
    /// or the scripted mock), taking the gateway into the client for the run and
    /// restoring it after so budgets persist across turns. Collects the raw event
    /// stream + verdicts, then pairs each event with the live mandate snapshot AS
    /// OF that point so the dock's budget bars deplete exactly as the gate spent
    /// them.
    fn drive<P: AcpPeer>(&mut self, peer: P, prompt: &str) -> Vec<StreamStep> {
        let start_clock = self.clock;
        let mut verdicts = Vec::new();
        let mut raw: Vec<StreamEvent> = Vec::new();
        let gw = self
            .gateway
            .take()
            .expect("the session gateway is present between turns");
        let mut client = crate::acp_client::AcpClient::new(peer, gw, start_clock);
        let _ = client.run_prompt_streaming("/deos/confined", prompt, None, &mut |ev| {
            if let StreamEvent::Verdict { call, outcome } = &ev {
                verdicts.push((call.clone(), outcome.clone()));
            }
            raw.push(ev);
        });
        let gateway = client.into_gateway();
        self.clock = start_clock + verdicts.len() as i64 + 1;

        // The gateway's per-key counters are final after the run; we reconstruct
        // the RUNNING mandate by deriving the inspector view from the verdicts
        // seen so far (`Mandate::from_session` overlays the verdict tally onto the
        // grants).
        let mut steps: Vec<StreamStep> = Vec::new();
        let mut seen: Vec<(crate::acp::ToolCallRequest, crate::acp::PermissionOutcome)> =
            Vec::new();
        for ev in raw {
            let snapshot = match &ev {
                StreamEvent::Verdict { call, outcome } => {
                    seen.push((call.clone(), outcome.clone()));
                    Some(running_mandate(&self.session_id, &gateway, &seen))
                }
                StreamEvent::Stopped { .. } => {
                    Some(running_mandate(&self.session_id, &gateway, &seen))
                }
                _ => None,
            };
            steps.push((ev, snapshot));
        }
        self.gateway = Some(gateway);
        steps
    }

    /// The current live mandate (all touched grants + every pinned per-tool one).
    pub fn mandate(&self) -> Mandate {
        let gw = self
            .gateway
            .as_ref()
            .expect("the session gateway is present between turns");
        Mandate::from_session(&self.session_id, gw, &[])
    }
}

/// Derive the live mandate view from the gateway + the verdicts seen SO FAR — but
/// override each row's `calls_made` with the count of allowed verdicts seen, so
/// the budget reflects the RUNNING spend (the gateway counters are already final).
fn running_mandate(
    session_id: &str,
    gateway: &HermesGateway<'static>,
    seen: &[(crate::acp::ToolCallRequest, crate::acp::PermissionOutcome)],
) -> Mandate {
    use crate::acp::PermissionOutcome;
    let mut m = Mandate::from_session(session_id, gateway, seen);
    // Recompute each row's spent count from the allowed verdicts seen so far (the
    // gateway's own counters are post-run; the receipts list on each row already
    // reflects the running `seen` slice, so spent = that row's receipt count).
    for row in &mut m.rows {
        let spent = seen
            .iter()
            .filter(|(call, outcome)| {
                matches!(outcome, PermissionOutcome::Allow { .. })
                    && gateway.registry().key_for_tool(&call.name) == row.key
            })
            .count() as i64;
        row.calls_made = spent;
        row.remaining = (row.rate_limit - spent).max(0);
    }
    m
}

/// Derive a plausible Hermes turn (a reply + the tool-calls it makes) from the
/// user's prompt. This is the stood-in "brain"; the ACP wire + the gate are real.
fn scripted_turn(prompt: &str) -> (String, Vec<ScriptedCall>) {
    let p = prompt.to_lowercase();
    let mut script = Vec::new();
    if p.contains("search") || p.contains("find") || p.contains("look up") || p.contains("what") {
        script.push(ScriptedCall::new(
            "web_search",
            serde_json::json!({ "query": prompt }),
        ));
    }
    if p.contains("build") || p.contains("compile") || p.contains("run") || p.contains("test") {
        script.push(ScriptedCall::new(
            "terminal",
            serde_json::json!({ "command": "cargo build" }),
        ));
        script.push(ScriptedCall::new(
            "terminal",
            serde_json::json!({ "command": "cargo test" }),
        ));
    }
    if p.contains("write") || p.contains("edit") || p.contains("note") || p.contains("save") {
        script.push(ScriptedCall::new(
            "write_file",
            serde_json::json!({ "path": "notes/plan.md", "content": prompt }),
        ));
    }
    if p.contains("read") || p.contains("show") || p.contains("open") {
        script.push(ScriptedCall::new(
            "read_file",
            serde_json::json!({ "path": "src/lib.rs" }),
        ));
    }
    // Always do SOMETHING so the gate fires and the demo isn't empty.
    if script.is_empty() {
        script.push(ScriptedCall::new(
            "web_search",
            serde_json::json!({ "query": prompt }),
        ));
    }
    let reply = format!(
        "On it. I'll work on \"{}\" — reaching for {} tool(s); each goes through deos's gate.",
        prompt.trim(),
        script.len()
    );
    (reply, script)
}

/// The live gpui view of the interactive confined-agent dock.
pub struct AgentDockView {
    model: AgentDockModel,
    session: HermesSession,
    /// The prompt input box (Enter-to-send).
    input: Entity<InputState>,
    focus: FocusHandle,
    /// Buffered streaming steps the timer drains one-per-tick (the streaming feel).
    pending: VecDeque<StreamStep>,
    _subs: Vec<Subscription>,
}

impl AgentDockView {
    /// Build the interactive view over a fresh confined session.
    pub fn new(model: AgentDockModel, window: &mut Window, cx: &mut Context<Self>) -> Self {
        let session = HermesSession::new(&model.session_id);
        Self::with_session(model, session, window, cx)
    }

    /// Build the view over an explicit session (e.g. a live-subprocess one).
    pub fn with_session(
        mut model: AgentDockModel,
        session: HermesSession,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        if model.status.is_empty() {
            model.status = "type a prompt to the confined agent and press Enter".into();
        }
        let input = cx.new(|cx| {
            InputState::new(window, cx).placeholder("Ask the confined agent…  (Enter to send)")
        });
        // Enter-to-send: on PressEnter (without shift), drive the typed prompt
        // through the gate. `subscribe_in` hands the Enter handler the window the
        // input clear + the session drive need.
        let sub = cx.subscribe_in(
            &input,
            window,
            |this, input, ev: &InputEvent, window, cx| {
                if let InputEvent::PressEnter { shift, .. } = ev {
                    if *shift {
                        return;
                    }
                    let text = input.read(cx).value().to_string();
                    if !text.trim().is_empty() {
                        input.update(cx, |s, cx| s.set_value("", window, cx));
                        this.submit(&text, cx);
                    }
                }
            },
        );

        // The streaming timer: drain ONE buffered step per tick into the model and
        // repaint. ~24ms/step makes the reply + tool-calls stream in visibly.
        cx.spawn(async move |this, cx| {
            loop {
                cx.background_executor()
                    .timer(Duration::from_millis(24))
                    .await;
                if this.update(cx, |this, cx| this.drain_one(cx)).is_err() {
                    break;
                }
            }
        })
        .detach();

        Self {
            model,
            session,
            input,
            focus: cx.focus_handle(),
            pending: VecDeque::new(),
            _subs: vec![sub],
        }
    }

    /// Submit a typed prompt: record it, drive the confined session, and buffer
    /// the resulting deltas for the streaming timer to paint.
    pub fn submit(&mut self, prompt: &str, cx: &mut Context<Self>) {
        self.model.push_user_prompt(prompt);
        // Drive the whole turn now (fast, in-process), buffering the deltas. We
        // split agent text into smaller pieces so it streams in word-by-word.
        let steps = self.session.run(prompt);
        for (ev, mandate) in steps {
            match ev {
                StreamEvent::AgentChunk { text } => {
                    for piece in split_streamable(&text) {
                        self.pending
                            .push_back((StreamEvent::AgentChunk { text: piece }, None));
                    }
                }
                other => self.pending.push_back((other, mandate)),
            }
        }
        cx.notify();
    }

    /// Drain one buffered streaming step into the model (the streaming heartbeat).
    fn drain_one(&mut self, cx: &mut Context<Self>) {
        if let Some((ev, mandate)) = self.pending.pop_front() {
            self.model.apply_event(&ev, mandate.as_ref());
            cx.notify();
        }
    }

    /// Drain EVERY buffered streaming step into the model at once (no per-tick
    /// pacing). The interactive dock uses the 24ms timer (`drain_one`) for the
    /// streaming feel; a host that mounts this view in a non-painting context — a
    /// headless `#[gpui::test]`, a one-shot CLI render — drives this instead to
    /// fold the whole turn deterministically. The folded events, receipts, and
    /// verdicts are identical either way; only the pacing differs. Returns the
    /// number of steps drained.
    pub fn drain_all(&mut self, cx: &mut Context<Self>) -> usize {
        let mut n = 0;
        while let Some((ev, mandate)) = self.pending.pop_front() {
            self.model.apply_event(&ev, mandate.as_ref());
            n += 1;
        }
        if n > 0 {
            cx.notify();
        }
        n
    }

    /// Replace the model (host-side push, e.g. a re-derive) and repaint.
    pub fn set_model(&mut self, model: AgentDockModel, cx: &mut Context<Self>) {
        self.model = model;
        cx.notify();
    }

    /// The live model (host-side inspection).
    pub fn model(&self) -> &AgentDockModel {
        &self.model
    }

    /// The live confined session (host-side inspection). Its
    /// [`HermesSession::mandate`] reads the gateway's CUMULATIVE counters (the
    /// real session-wide budget), distinct from the model's per-turn animated
    /// `mandate_rows` — a host/test that wants the whole-session depletion reads
    /// this.
    pub fn session(&self) -> &HermesSession {
        &self.session
    }
}

/// Split agent text into small streamable pieces (whitespace-preserving), so the
/// reply paints in word-by-word rather than appearing all at once.
fn split_streamable(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        cur.push(ch);
        if ch == ' ' || ch == '\n' {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    if out.is_empty() {
        out.push(text.to_string());
    }
    out
}

// ── the panes ──

impl AgentDockView {
    /// The multi-turn chat transcript: user prompts, streamed agent replies, and
    /// the gated tool-calls inline where the agent made them.
    fn transcript_pane(&self) -> AnyElement {
        let mut col = v_flex().gap_2().p_2();
        if self.model.transcript.is_empty() {
            col = col.child(
                div()
                    .text_color(MUTED)
                    .child("No conversation yet — type a prompt below and press Enter."),
            );
        }
        for entry in &self.model.transcript {
            col = col.child(self.transcript_entry(entry));
        }
        if self.model.running {
            col = col.child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child("▍ thinking…"),
            );
        }
        col.into_any_element()
    }

    fn transcript_entry(&self, entry: &ChatEntry) -> AnyElement {
        match entry {
            ChatEntry::User { text } => h_flex()
                .gap_2()
                .child(div().text_color(USER).min_w(px(48.)).child("you"))
                .child(
                    div()
                        .text_color(BODY)
                        .child(SharedString::from(text.clone())),
                )
                .into_any_element(),
            ChatEntry::Agent { text } => h_flex()
                .gap_2()
                .items_start()
                .child(div().text_color(AGENT).min_w(px(48.)).child("hermes"))
                .child(
                    div()
                        .text_color(BODY)
                        .child(SharedString::from(text.clone())),
                )
                .into_any_element(),
            ChatEntry::Tool { line } => self.inline_tool(line),
        }
    }

    /// A gated tool-call rendered inline in the transcript: the gate verdict right
    /// where the agent reached — ✓ receipt+budget or ✗ refused+leg.
    fn inline_tool(&self, line: &ToolLine) -> AnyElement {
        let (mark, color) = if line.allowed {
            ("✓", ALLOW)
        } else {
            ("✗", REJECT)
        };
        let rem = line
            .remaining
            .map(|r| format!("  ·  {r} left"))
            .unwrap_or_default();
        h_flex()
            .gap_2()
            .pl_4()
            .child(div().text_color(color).child(mark))
            .child(
                div()
                    .text_color(TOOL)
                    .min_w(px(96.))
                    .child(SharedString::from(format!("⚙ {}", line.name))),
            )
            .child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child(SharedString::from(format!("{}{}", line.detail, rem))),
            )
            .into_any_element()
    }

    /// THE PERMISSION MOMENT — the most recent gate decision, surfaced prominently:
    /// the tool, the cap it needed, the verdict (allow→receipt+budget / refuse→leg).
    fn permission_pane(&self) -> AnyElement {
        let mut col = v_flex().gap_1().p_2().border_1().rounded(px(6.)).child(
            div()
                .text_color(HEADING)
                .child("permission moment (the deos gate)"),
        );
        match &self.model.last_permission {
            None => {
                col =
                    col.child(div().text_color(MUTED).child(
                        "no tool-call gated yet — every agent reach is decided here, live.",
                    ));
            }
            Some(PermissionMoment {
                tool,
                mandate,
                allowed: true,
                detail,
                remaining,
                ..
            }) => {
                col = col
                    .child(
                        h_flex()
                            .gap_2()
                            .child(div().text_color(ALLOW).child("✓ ALLOWED"))
                            .child(
                                div()
                                    .text_color(BODY)
                                    .child(SharedString::from(format!("{tool}  under  {mandate}"))),
                            ),
                    )
                    .child(
                        div()
                            .text_color(MUTED)
                            .text_size(px(12.))
                            .child(SharedString::from(format!(
                                "{detail}  ·  budget left: {}",
                                remaining
                                    .map(|r| r.to_string())
                                    .unwrap_or_else(|| "—".into())
                            ))),
                    );
            }
            Some(PermissionMoment {
                tool,
                mandate,
                allowed: false,
                detail,
                leg,
                ..
            }) => {
                let leg = leg.unwrap_or(RefusalLeg::Other);
                col = col
                    .child(
                        h_flex()
                            .gap_2()
                            .child(div().text_color(REJECT).child("✗ REFUSED"))
                            .child(div().text_color(BODY).child(SharedString::from(format!(
                                "{tool}  under  {mandate}  —  leg: {}",
                                leg.label()
                            )))),
                    )
                    .child(
                        div()
                            .text_color(MUTED)
                            .text_size(px(12.))
                            .child(SharedString::from(detail.clone())),
                    );
            }
        }
        col.into_any_element()
    }

    /// THE MANDATE PANEL — the agent's live confinement, with budget bars that
    /// deplete as it spends. One row per touched mandate + every pinned per-tool grant.
    fn mandate_pane(&self) -> AnyElement {
        let mut col = v_flex()
            .gap_1()
            .p_2()
            .child(div().text_color(HEADING).child("mandate (live budgets)"));
        if self.model.mandate_rows.is_empty() {
            col = col.child(
                div()
                    .text_color(MUTED)
                    .child("the curated per-tool grants appear as the agent uses them."),
            );
        }
        for row in &self.model.mandate_rows {
            col = col.child(self.budget_row(row));
        }
        col.into_any_element()
    }

    fn budget_row(&self, row: &MandateBudget) -> AnyElement {
        let frac = row.fraction_spent();
        let bar_w = 120.0_f32;
        let filled = (bar_w * frac).max(0.0);
        let bar_color = if frac >= 1.0 {
            REJECT
        } else if frac >= 0.66 {
            WARN
        } else {
            ALLOW
        };
        h_flex()
            .gap_2()
            .child(
                div()
                    .text_color(if row.per_tool { TOOL } else { BODY })
                    .min_w(px(140.))
                    .child(SharedString::from(row.label.clone())),
            )
            // the budget bar: a filled track over a muted background
            .child(
                div()
                    .w(px(bar_w))
                    .h(px(8.))
                    .rounded(px(4.))
                    .bg(TRACK)
                    .child(div().w(px(filled)).h(px(8.)).rounded(px(4.)).bg(bar_color)),
            )
            .child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child(SharedString::from(format!(
                        "{}/{} used  ·  {} left",
                        row.spent,
                        row.rate_limit,
                        row.remaining()
                    ))),
            )
            .into_any_element()
    }

    /// The prompt input box (Enter-to-send), pinned at the bottom.
    fn input_pane(&self) -> AnyElement {
        v_flex()
            .gap_1()
            .p_2()
            .child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child(SharedString::from(self.model.status.clone())),
            )
            .child(Input::new(&self.input))
            .into_any_element()
    }
}

// A small, theme-independent palette so the surface paints without a specific
// gpui-component Theme variant installed (the headless capture + the cockpit both
// work). Plain gpui Rgba literals.
const HEADING: gpui::Rgba = gpui::Rgba {
    r: 0.85,
    g: 0.90,
    b: 1.0,
    a: 1.0,
};
const BODY: gpui::Rgba = gpui::Rgba {
    r: 0.82,
    g: 0.84,
    b: 0.88,
    a: 1.0,
};
const MUTED: gpui::Rgba = gpui::Rgba {
    r: 0.55,
    g: 0.58,
    b: 0.64,
    a: 1.0,
};
const USER: gpui::Rgba = gpui::Rgba {
    r: 0.60,
    g: 0.78,
    b: 1.0,
    a: 1.0,
};
const AGENT: gpui::Rgba = gpui::Rgba {
    r: 0.80,
    g: 0.72,
    b: 1.0,
    a: 1.0,
};
const TOOL: gpui::Rgba = gpui::Rgba {
    r: 0.95,
    g: 0.82,
    b: 0.55,
    a: 1.0,
};
const ALLOW: gpui::Rgba = gpui::Rgba {
    r: 0.45,
    g: 0.85,
    b: 0.55,
    a: 1.0,
};
const WARN: gpui::Rgba = gpui::Rgba {
    r: 0.95,
    g: 0.78,
    b: 0.40,
    a: 1.0,
};
const REJECT: gpui::Rgba = gpui::Rgba {
    r: 0.95,
    g: 0.45,
    b: 0.45,
    a: 1.0,
};
const TRACK: gpui::Rgba = gpui::Rgba {
    r: 0.18,
    g: 0.20,
    b: 0.25,
    a: 1.0,
};
const BG: gpui::Rgba = gpui::Rgba {
    r: 0.07,
    g: 0.08,
    b: 0.11,
    a: 1.0,
};

impl Render for AgentDockView {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        v_flex()
            .key_context("HermesDock")
            .track_focus(&self.focus)
            .size_full()
            .bg(BG)
            .p_2()
            .gap_2()
            .child(div().text_color(HEADING).child(SharedString::from(format!(
                "Hermes (confined) — session {}",
                self.model.session_id
            ))))
            // the conversation, scrollable, taking the bulk of the height
            .child(
                div()
                    .id("hermes-transcript")
                    .flex_1()
                    .overflow_y_scroll()
                    .child(self.transcript_pane()),
            )
            // the permission moment, prominent
            .child(self.permission_pane())
            // the live mandate budgets
            .child(self.mandate_pane())
            // the prompt input, pinned at the bottom
            .child(self.input_pane())
    }
}

impl Focusable for AgentDockView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

/// A dock-mountable confined-agent surface: a stable id + the live
/// [`AgentDockView`] entity. Cheap to [`Clone`] (a handle + an id).
#[derive(Clone)]
pub struct HermesDockSurface {
    id: u64,
    view: Entity<AgentDockView>,
}

impl HermesDockSurface {
    /// Build a confined-agent surface over a starting [`AgentDockModel`]. The
    /// `window` is needed to construct the prompt input (gpui's `InputState`).
    pub fn new(id: u64, model: AgentDockModel, window: &mut Window, cx: &mut App) -> Self {
        let view = cx.new(|cx| AgentDockView::new(model, window, cx));
        Self { id, view }
    }

    /// Build a fresh INTERACTIVE confined-agent surface (the common path): an
    /// empty live model + a fresh confined session, ready to take typed prompts.
    pub fn new_interactive(id: u64, session_id: &str, window: &mut Window, cx: &mut App) -> Self {
        Self::new(id, AgentDockModel::new_live(session_id), window, cx)
    }

    /// Wrap an already-built view entity.
    pub fn from_view(id: u64, view: Entity<AgentDockView>) -> Self {
        Self { id, view }
    }

    /// The live view entity.
    pub fn view(&self) -> &Entity<AgentDockView> {
        &self.view
    }

    /// Push a fresh model.
    pub fn set_model(&self, model: AgentDockModel, cx: &mut App) {
        self.view.update(cx, |v, cx| v.set_model(model, cx));
    }

    // --- the methods the host's `CockpitSurface` impl forwards to ------------

    /// `CockpitSurface::item_id` payload.
    pub fn surface_id(&self) -> u64 {
        self.id
    }

    /// `CockpitSurface::tab_label`.
    pub fn tab_label(&self) -> SharedString {
        SharedString::from("Hermes (confined)")
    }

    /// `CockpitSurface::focus_handle`.
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.view.read(cx).focus_handle(cx)
    }

    /// `CockpitSurface::render_body` — the live agent dock view.
    pub fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        div()
            .size_full()
            .child(self.view.clone())
            .into_any_element()
    }

    /// `CockpitSurface::is_dirty` — a confined agent is "dirty" (worth a marker)
    /// while its turn is in flight.
    pub fn is_dirty(&self, cx: &App) -> bool {
        self.view.read(cx).model().running
    }
}
