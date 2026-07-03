//! **THE WORKFLOW-COMPOSER SURFACE** — intents, workflows, and flow-refinement as
//! first-class desktop objects.
//!
//! This window exposes dregg's REAL workflow-composer + refinement machinery (the
//! flow algebra in [`dregg_deploy::refine`]) as an NT/Pharo workbench surface:
//!
//!   * **Intents** — a step a workflow can take, declared as a desired `Effect`
//!     over a live cell (transfer, grant, bump, set-field, seal). An intent is the
//!     *declarative* face: "this shape of effect is what I want to authorize." The
//!     palette of intents is the alphabet the workflow draws from.
//!   * **Workflow** — an ordered composition of intents. We lower the steps into a
//!     real `dregg_turn::CallForest` (one `bare_action` per step) and run it through
//!     the REAL composer [`dregg_deploy::refine::flow_of_forest`], which yields the
//!     proven flow-algebra `Proc` (sequence `⋆` of `Emit ℓ` letters). The composed
//!     `Proc` IS the object the refinement game decides over.
//!   * **Refinement** — "does workflow A refine workflow B?" We answer it with the
//!     REAL decision procedure [`dregg_deploy::refine::decide_refines`] — the online
//!     simulation game `A ≤ᶠ B`, routed through the verified Lean
//!     `@[export] dregg_decide_refines` (proven sound+complete by `decideRefines_iff`,
//!     LAW #1) and falling back to the σ-free mirror. The baseline B is the workflow's
//!     declared *envelope* (its allowed intent-shapes as a [`FlowSpec`] repeat-menu);
//!     adding a step OUTSIDE the envelope makes the workflow stop refining it, and the
//!     diverging intent is named.
//!
//! REAL UNDERNEATH: every `Proc`, every refinement verdict comes from `dregg-deploy`'s
//! flow machinery over `dregg-turn::Effect`s built against the live `World`'s cells —
//! no mock. The one seam: the live-`World` cells here are single-custody, so the
//! workflow is composed/refined but not (yet) *committed* as a multi-turn batch from
//! this window — composition + refinement is the decidable, proof-carrying core; firing
//! the composed workflow as turns rides the existing per-effect actuation path.

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, Styled,
};

use dregg_deploy::refine::{
    decide_refines, describe_effect, flow_of_forest, FlowSpec, IntentEffect, Proc, RefineVerdict,
};
use dregg_turn::action::Effect;
use dregg_turn::forest::{CallForest, CallTree};
use dregg_types::CellId;

use crate::world::{bare_action, grant_capability, transfer};

use super::chrome::{
    bevel_raised, face_row, face_section, id_short, DOC_REV_SLOT, GLYPH_ADD, GLYPH_PIN,
    GLYPH_REMOVE, NT_DIM, NT_FACE, NT_FACE_DARK, NT_OK, NT_PANEL, NT_SHADOW, NT_TEXT,
};
use super::DeosDesktop;

/// One step of a composed workflow — an INTENT (a declarative desired `Effect`) over
/// a live cell. The `kind` is the intent's shape; `effect` is the concrete effect it
/// lowers to (built against the workflow's subject cell + the desktop's user anchor).
#[derive(Clone)]
pub struct WorkflowStep {
    pub kind: IntentKind,
    pub effect: Effect,
}

/// **The intent vocabulary** — the declarative effect-shapes a workflow step can be.
/// Each maps to a concrete `dregg_turn::Effect` over the live cells; the refinement
/// game distinguishes them by the flow-algebra letter their effect projects to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IntentKind {
    /// Transfer value from the subject cell to the user anchor.
    Transfer,
    /// Grant a capability from the subject cell to the user anchor.
    Grant,
    /// Bump the subject cell's nonce (the always-available step).
    BumpNonce,
    /// Write the subject cell's revision slot (a state edit).
    SetRevision,
    /// Seal the subject cell (a lifecycle step — a WIDENING beyond a value/grant
    /// workflow, so the refinement panel can demonstrate a real divergence).
    Seal,
}

impl IntentKind {
    /// The short label shown in the intent palette + step list.
    pub fn label(self) -> &'static str {
        match self {
            IntentKind::Transfer => "Transfer 1,000 → user",
            IntentKind::Grant => "Grant cap → user",
            IntentKind::BumpNonce => "Bump nonce",
            IntentKind::SetRevision => "Set revision += 1",
            IntentKind::Seal => "Seal cell  (widening)",
        }
    }

    /// All intent kinds, in palette order.
    pub fn all() -> [IntentKind; 5] {
        [
            IntentKind::Transfer,
            IntentKind::Grant,
            IntentKind::BumpNonce,
            IntentKind::SetRevision,
            IntentKind::Seal,
        ]
    }
}

/// The composer's per-cell editing state — the live workflow being built over a
/// subject cell, plus the chosen refinement baseline. Owned by [`DeosDesktop`] and
/// keyed by the subject cell.
#[derive(Clone, Default)]
pub struct WorkflowState {
    /// The composed workflow's steps (intents), in firing order.
    pub steps: Vec<WorkflowStep>,
    /// How many leading steps form the refinement BASELINE (workflow B). The whole
    /// workflow (A) is checked to refine the envelope of its first `baseline_len`
    /// steps — so a step added beyond the baseline that widens the authority makes
    /// the refinement FAIL with a named divergence. `0` = baseline is empty (every
    /// non-empty workflow trivially diverges from it unless it too is empty).
    pub baseline_len: usize,
}

impl DeosDesktop {
    /// Build the concrete `Effect` an intent step lowers to, over `subject` and the
    /// user anchor — the genuine `dregg_turn::Effect`, the same shapes the cell's
    /// right-click actuation fires.
    pub(super) fn workflow_effect(&self, subject: CellId, kind: IntentKind) -> Effect {
        match kind {
            IntentKind::Transfer => transfer(subject, self.workflow_user(), 1_000),
            IntentKind::Grant => grant_capability(subject, subject, self.workflow_user(), 1),
            IntentKind::BumpNonce => Effect::IncrementNonce { cell: subject },
            IntentKind::SetRevision => {
                let mut fe = [0u8; 32];
                fe[..8].copy_from_slice(&1u64.to_le_bytes());
                Effect::SetField {
                    cell: subject,
                    index: DOC_REV_SLOT,
                    value: fe,
                }
            }
            IntentKind::Seal => Effect::CellSeal {
                target: subject,
                reason: [0u8; 32],
            },
        }
    }

    /// Lower a list of workflow steps into a real `dregg_turn::CallForest` — one
    /// `bare_action` per step, gathered as sibling roots in firing order. This is the
    /// bridge from the desktop's intent vocabulary to the protocol's call structure
    /// that the flow composer consumes.
    fn workflow_forest(&self, subject: CellId, steps: &[WorkflowStep]) -> CallForest {
        let mut forest = CallForest::new();
        for step in steps {
            forest.roots.push(CallTree::new(bare_action(
                subject,
                vec![step.effect.clone()],
            )));
        }
        forest
    }

    /// **COMPOSE** — the real workflow-composer call: lower the steps to a forest and
    /// run [`flow_of_forest`] to get the proven flow-algebra `Proc` (a `⋆`-chain of
    /// the steps' effect-letters in firing order). This `Proc` is the object the
    /// refinement game decides over.
    fn workflow_proc(&self, subject: CellId, steps: &[WorkflowStep]) -> Proc {
        let forest = self.workflow_forest(subject, steps);
        flow_of_forest(&forest)
    }

    /// The refinement BASELINE (workflow B) as a [`FlowSpec`] envelope — the menu of
    /// intent-shapes the baseline steps authorize. `A ≤ᶠ B` holds iff every step in
    /// the full workflow A fires an intent the baseline already offered.
    fn workflow_baseline_spec(&self, steps: &[WorkflowStep], baseline_len: usize) -> FlowSpec {
        let allowed: Vec<IntentEffect> = steps
            .iter()
            .take(baseline_len)
            .map(|s| IntentEffect::Exact(s.effect.clone()))
            .collect();
        FlowSpec::from_intent(&allowed)
    }

    /// **THE REFINEMENT DECISION** — does the full workflow A refine its baseline
    /// envelope B? Runs the REAL [`decide_refines`] over the composed `Proc` (A) and
    /// the baseline repeat-menu (B). Returns the verdict plus a human label for the
    /// first diverging intent (the step that widened beyond the envelope), if any.
    fn workflow_refines(
        &self,
        subject: CellId,
        steps: &[WorkflowStep],
        baseline_len: usize,
    ) -> RefineVerdict {
        let workflow = self.workflow_proc(subject, steps);
        let spec = self.workflow_baseline_spec(steps, baseline_len);
        // Materialize the baseline menu to the workflow's length (deploys/workflows
        // are linear, so this depth suffices for the game to decide membership).
        let menu = spec.to_menu_proc(steps.len().max(1));
        if decide_refines(&workflow, &menu) {
            RefineVerdict::Refines
        } else {
            // Locate the first step whose intent the baseline did not offer — the
            // named divergence witness (the widening effect). Per-step membership: a
            // step refines the baseline iff its singleton flow refines the menu.
            let mut finding = None;
            for step in steps.iter().skip(baseline_len) {
                let single = self.workflow_proc(subject, std::slice::from_ref(step));
                if !decide_refines(&single, &menu) {
                    finding = Some(describe_effect(&step.effect));
                    break;
                }
            }
            // Reuse the deploy crate's verdict shape via the public RefineVerdict; we
            // build a Diverges with a single located finding naming the widening.
            RefineVerdict::Diverges(vec![dregg_deploy::refine::RefineFinding {
                check: "workflow-refinement".to_string(),
                message: match &finding {
                    Some(lbl) => format!("step widens beyond the baseline envelope: {lbl}"),
                    None => "the workflow does not refine its baseline envelope".to_string(),
                },
                diverging_letter: None,
                diverging_effect_label: finding,
            }])
        }
    }

    // ── The composer's actuation (mutate the workflow state) ──────────────────────

    /// Append an intent step to the subject cell's workflow.
    pub(super) fn workflow_add_step(&mut self, subject: CellId, kind: IntentKind) {
        let effect = self.workflow_effect(subject, kind);
        let wf = self.workflow_state_mut(subject);
        wf.steps.push(WorkflowStep { kind, effect });
        self.say(format!(
            "Workflow {} — added intent “{}” ({} steps).",
            id_short(&subject),
            kind.label(),
            self.workflow_state(subject).steps.len()
        ));
    }

    /// Drop the last intent step from the subject cell's workflow.
    pub(super) fn workflow_pop_step(&mut self, subject: CellId) {
        let wf = self.workflow_state_mut(subject);
        wf.steps.pop();
        if wf.baseline_len > wf.steps.len() {
            wf.baseline_len = wf.steps.len();
        }
        self.say(format!(
            "Workflow {} — removed last intent ({} steps).",
            id_short(&subject),
            self.workflow_state(subject).steps.len()
        ));
    }

    /// Mark the current workflow length as the refinement baseline — the running
    /// workflow B that subsequently-added intents are held to refine.
    pub(super) fn workflow_pin_baseline(&mut self, subject: CellId) {
        let len = self.workflow_state(subject).steps.len();
        self.workflow_state_mut(subject).baseline_len = len;
        self.say(format!(
            "Workflow {} — pinned baseline at {len} step(s); new intents must REFINE it.",
            id_short(&subject)
        ));
    }

    /// Read-only access to a cell's workflow state (default-empty if untouched).
    pub(super) fn workflow_state(&self, subject: CellId) -> WorkflowState {
        self.workflows.get(&subject).cloned().unwrap_or_default()
    }

    fn workflow_state_mut(&mut self, subject: CellId) -> &mut WorkflowState {
        self.workflows.entry(subject).or_default()
    }

    // ── Bake / test hooks (drive the surface headlessly) ──────────────────────────

    /// Append an intent step (what clicking a palette intent does) — a bake/test hook.
    pub fn bake_workflow_add(&mut self, subject: CellId, kind: IntentKind) {
        self.workflow_add_step(subject, kind);
    }

    /// Pin the refinement baseline at the current length — a bake/test hook.
    pub fn bake_workflow_pin_baseline(&mut self, subject: CellId) {
        self.workflow_pin_baseline(subject);
    }

    /// The composed workflow's flow-`Proc` letter-trace count (= step count for a
    /// linear workflow) — a bake/test assertion hook proving the REAL composer ran.
    pub fn bake_workflow_letters(&self, subject: CellId) -> usize {
        let steps = self.workflow_state(subject).steps;
        // Count moves of the composed Proc by walking it (linear → one per step).
        let proc = self.workflow_proc(subject, &steps);
        workflow_trace_len(&proc)
    }

    /// Whether the current workflow refines its pinned baseline — a bake/test hook
    /// over the REAL `decide_refines`.
    pub fn bake_workflow_refines(&self, subject: CellId) -> bool {
        let wf = self.workflow_state(subject);
        self.workflow_refines(subject, &wf.steps, wf.baseline_len)
            .is_refine()
    }

    /// Open the workflow-composer window over `subject` (what "Compose Workflow…"
    /// does) — a bake/test hook.
    pub fn bake_open_workflow(&mut self, subject: CellId) {
        self.open_workflow_window(subject);
    }

    // ── Rendering: the dense workflow-composer body ───────────────────────────────

    /// **The workflow-composer body** — the intent palette, the composed step list,
    /// the live flow-`Proc` readout, and the refinement verdict. Each piece is REAL:
    /// the steps lower to a `CallForest`, the flow comes from [`flow_of_forest`], the
    /// verdict from [`decide_refines`].
    pub(super) fn render_workflow_body(
        &self,
        subject: CellId,
        scroll: &gpui::ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let wf = self.workflow_state(subject);
        let proc = self.workflow_proc(subject, &wf.steps);
        let trace = workflow_trace(&proc);
        let verdict = self.workflow_refines(subject, &wf.steps, wf.baseline_len);

        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "wfbody-{}",
                super::chrome::id_hex(&subject)
            )))
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1();

        // ── Intent palette (add a step) ──
        col = col.child(face_section("Intents (declarative steps)"));
        for kind in IntentKind::all() {
            col = col.child(self.workflow_palette_button(subject, kind, cx));
        }

        // ── Composed workflow (the step list) ──
        col = col.child(face_section("Workflow (composed steps · ⋆)"));
        if wf.steps.is_empty() {
            col = col.child(face_row("(empty)", "add intents from the palette above"));
        } else {
            for (i, step) in wf.steps.iter().enumerate() {
                let baseline_mark = if i < wf.baseline_len { ">B" } else { "  " };
                col = col.child(face_row(
                    &format!("{baseline_mark} [{i}]"),
                    step.kind.label(),
                ));
            }
            col = col
                .child(self.workflow_pop_button(subject, cx))
                .child(self.workflow_baseline_button(subject, cx));
        }

        // ── The composed flow-Proc (the real flow algebra) ──
        col = col
            .child(face_section("Flow (proven Proc · letters)"))
            .child(face_row("steps", &wf.steps.len().to_string()))
            .child(face_row("baseline B", &wf.baseline_len.to_string()))
            .child(face_row("letters", &format!("{} fired", trace.len())));
        // A compact letter trace (first bytes of each effect-letter) — the workflow's
        // observable alphabet, the granularity the game decides over.
        let letters: String = trace
            .iter()
            .map(|l| format!("{:04x}", (l >> 48) & 0xffff))
            .collect::<Vec<_>>()
            .join(" ");
        col = col.child(face_row(
            "trace",
            if letters.is_empty() { "—" } else { &letters },
        ));

        // ── Refinement verdict (the REAL decision) ──
        col = col.child(face_section(
            "Refinement  A ≤ᶠ B  (does workflow refine baseline?)",
        ));
        match &verdict {
            RefineVerdict::Refines => {
                col = col.child(
                    div()
                        .text_color(gpui::rgb(NT_OK))
                        .child("✓ REFINES — every step is within the baseline envelope."),
                );
            }
            RefineVerdict::Diverges(findings) => {
                col = col.child(
                    div()
                        .text_color(gpui::rgb(0xa00020))
                        .child("✗ DIVERGES — a step widens beyond the baseline."),
                );
                for f in findings {
                    col = col.child(face_row("why", &f.message));
                    if let Some(lbl) = &f.diverging_effect_label {
                        col = col.child(face_row("widening", lbl));
                    }
                }
            }
        }
        col = col.child(
            div()
                .mt_1()
                .text_size(px(10.0))
                .text_color(gpui::rgb(NT_DIM))
                .child(
                    "Pin a baseline, then add intents: a step within the baseline's intent \
                     shapes REFINES; a wider one (e.g. Seal) DIVERGES — decided by the proven \
                     dregg_deploy::refine game.",
                ),
        );

        // The composed body scrolls behind a REAL NT scrollbar (the persistent
        // handle keeps the operator's place while intents are added/popped).
        super::chrome::nt_scroll_face(scroll, col).into_any_element()
    }

    /// An intent-palette button: clicking it appends that intent to the workflow.
    fn workflow_palette_button(
        &self,
        subject: CellId,
        kind: IntentKind,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "wfadd-{}-{}",
                    super::chrome::id_hex(&subject),
                    kind.label()
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.workflow_add_step(subject, kind);
                cx.notify();
            }),
        )
        .child(format!("{GLYPH_ADD} {}", kind.label()))
    }

    fn workflow_pop_button(&self, subject: CellId, cx: &mut Context<Self>) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "wfpop-{}",
                    super::chrome::id_hex(&subject)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.workflow_pop_step(subject);
                cx.notify();
            }),
        )
        .child(format!("{GLYPH_REMOVE} remove last step"))
    }

    fn workflow_baseline_button(
        &self,
        subject: CellId,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "wfbase-{}",
                    super::chrome::id_hex(&subject)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.workflow_pin_baseline(subject);
                cx.notify();
            }),
        )
        .child(format!("{GLYPH_PIN} pin baseline B = current workflow"))
    }
}

/// The letters of a composed workflow `Proc` in firing order — the workflow's
/// observable trace (one letter per step for a linear workflow). A free helper so
/// the bake hooks and the body share it.
fn workflow_trace(proc: &Proc) -> Vec<u64> {
    // Walk the Proc's left-preferred move path (deploy/workflow flows are linear, so
    // this is the exact, full trace). Capped to guard a malformed input.
    let mut out = Vec::new();
    let mut cur = proc.clone();
    for _ in 0..4096 {
        let Some((l, next)) = proc_first_move(&cur) else {
            break;
        };
        out.push(l);
        cur = next;
    }
    out
}

fn workflow_trace_len(proc: &Proc) -> usize {
    workflow_trace(proc).len()
}

/// The first (left-preferred) `(letter, successor)` move of a `Proc` under the flow
/// algebra's step relation — a local mirror of the composer's move semantics, used
/// only to *read back* the composed flow's trace for display (the DECISION itself
/// always goes through the proven `decide_refines`).
fn proc_first_move(p: &Proc) -> Option<(u64, Proc)> {
    match p {
        Proc::Done => None,
        Proc::Emit(l) => Some((*l, Proc::Done)),
        Proc::Ch(a, b) => proc_first_move(a).or_else(|| proc_first_move(b)),
        Proc::Seqp(pp, r) => match r.as_ref() {
            Proc::Done => proc_first_move(pp),
            other => {
                proc_first_move(other).map(|(l, r2)| (l, Proc::Seqp(pp.clone(), Box::new(r2))))
            }
        },
    }
}

// Silence unused-import lints on chrome constants only used in some cfg paths.
const _: &[u32] = &[NT_FACE, NT_FACE_DARK, NT_SHADOW, NT_TEXT];
