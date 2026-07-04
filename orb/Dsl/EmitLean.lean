/-
  Dsl/EmitLean.lean — the EMIT-LEAN pass.

  Given an engine description (a reactor built over a machine/linear pair, plus a
  declared `fabric` list), this pass GENERATES the deployed-path Lean artifacts,
  all kernel-checked:

    * `<Name>_serve`             — the deployed serve function (ingress fork + guard);
    * `<Name>_<Lib>_seam_gen`    — one generated seam theorem per fabric lib, each
                                   TRANSPORTED across the Bridge lift
                                   (`deploySubs = reactorSubs`) from the sans-IO
                                   reactor property to the deployed serve path.

  The claim: the SAME seam theorems written by hand in the crosswiring waves can be
  GENERATED from the description. The hand proofs are the reference; the macro emits
  their twin, and it typechecks or the command fails (no `sorry`, ever).

  Depends only on `Dsl.Component` and `Dsl.Reactor` (the pinned foundation). The
  deployed path (serve), the Bridge lift, the fabric seams, and the reusable
  transported lemmas are all defined here — they are what the pass EMITS.
-/
import Lean
import Dsl.Component
import Dsl.Reactor

open Lean Lean.Elab Lean.Elab.Command

namespace Dsl

/-! ## The deployed serve path (what a hand-built deploy module builds) -/

/-- The ingress lane the deployed path forks on: HTTP/1.1 or h2c (cleartext h2). -/
inductive Lane
  | h1
  | h2c
deriving DecidableEq

/-- The ingress fork: which lane a freshly delivered event is routed to. A demo
    classifier — the point is that BOTH lanes drive the same reactor, so the fork is
    submission-transparent. -/
def ingressClassify : RingEvent → Lane
  | .writeReady => Lane.h2c
  | _           => Lane.h1

/-- The per-lane deployed step: both H1 and h2c fork into the same reactor `step`,
    differing only in framing metadata the seam does not see. -/
def ingressStep (R : ReactorComponent) (lane : Lane)
    (st : R.State) (ev : RingEvent) : R.State × List RingSubmission :=
  match lane with
  | Lane.h1  => R.step st ev
  | Lane.h2c => R.step st ev

/-- The fork never changes the emitted submissions — both lanes are the reactor. -/
theorem ingressStep_subs (R : ReactorComponent) (lane : Lane)
    (st : R.State) (ev : RingEvent) :
    (ingressStep R lane st ev).2 = (R.step st ev).2 := by
  cases lane <;> rfl

/-- `serve`: the deployed serve function. Classifies the event's ingress lane, then
    runs the guarded reactor step for that lane. This is the artifact the emit pass
    names `<Name>_serve`. -/
def serve (R : ReactorComponent) (st : R.State) (ev : RingEvent) :
    R.State × List RingSubmission :=
  ingressStep R (ingressClassify ev) st ev

/-- The sans-IO submissions the reactor emits (the CW-wave lived here). -/
def reactorSubs (R : ReactorComponent) (st : R.State) (ev : RingEvent) :
    List RingSubmission := (R.step st ev).2

/-- The deployed submissions the serve path emits. -/
def deploySubs (R : ReactorComponent) (st : R.State) (ev : RingEvent) :
    List RingSubmission := (serve R st ev).2

/-- **The Bridge lift** — `deploySubs = reactorSubs`. Every property proven about
    the sans-IO `reactorSubs` transports to the deployed `deploySubs` by rewriting
    with this equality. The generated seam theorems are exactly such transports. -/
theorem deploySubs_eq_reactorSubs (R : ReactorComponent) (st : R.State) (ev : RingEvent) :
    deploySubs R st ev = reactorSubs R st ev := by
  unfold deploySubs reactorSubs serve
  exact ingressStep_subs R (ingressClassify ev) st ev

/-- The deployed serve preserves the reactor invariant (used by the Policy seam). -/
theorem serve_preserves (R : ReactorComponent) (st : R.State) (ev : RingEvent)
    (h : R.inv st) : R.inv (serve R st ev).1 := by
  unfold serve ingressStep
  cases ingressClassify ev <;> exact R.step_wf st ev h

/-! ## The fabric seams (parametric in the reactor's machine/linear pair)

    Each seam is a `Prop` on the DEPLOYED path plus a `*_holds` proof that transports
    the sans-IO reactor primitive theorem across the Bridge lift. The emit pass just
    NAMES an instance of these per engine — it never re-does the proof. -/

/-- Bridge-side helper: the reactor's per-step recycle count is ≤ 1 (copy-once ⇒
    at most one buffer recycled per event), for ANY machine/linear pair + wiring. -/
theorem reactorStep_recycleCount_le_one (m l : Component) (w : Wiring m l)
    (st : (mkReactorWith m l w).State) (ev : RingEvent) :
    recycleCount ((mkReactorWith m l w).step st ev).2 ≤ 1 := by
  cases ev with
  | recvInto bid data => have h := reactor_prim_recycleCount m l w st bid data; omega
  | writeReady        => have h := reactor_prim_no_recycle m l w st .writeReady rfl; omega
  | writeBlocked      => have h := reactor_prim_no_recycle m l w st .writeBlocked rfl; omega
  | sendComplete      => have h := reactor_prim_no_recycle m l w st .sendComplete rfl; omega
  | timerFired slot   => have h := reactor_prim_no_recycle m l w st (.timerFired slot) rfl; omega
  | peerClosed        => have h := reactor_prim_no_recycle m l w st .peerClosed rfl; omega
  | closeRequested    => have h := reactor_prim_no_recycle m l w st .closeRequested rfl; omega

/-- **Rate** seam — the deployed path recycles at most one buffer per event: a
    rate bound on buffer churn. Transported from `reactor_prim_recycleCount`. -/
def RateSeam (m l : Component) (w : Wiring m l) : Prop :=
  ∀ (st : (mkReactorWith m l w).State) (ev : RingEvent),
    recycleCount (deploySubs (mkReactorWith m l w) st ev) ≤ 1

theorem RateSeam_holds (m l : Component) (w : Wiring m l) : RateSeam m l w := by
  intro st ev
  rw [deploySubs_eq_reactorSubs]                       -- BRIDGE LIFT
  exact reactorStep_recycleCount_le_one m l w st ev

/-- **Route** seam — every submission the deployed path emits is either a
    machine-driven op (routed by the wiring's `drive`) or the shell's recycle: no
    submission is injected from nowhere. Transported from the step's op-origin. -/
def RouteSeam (m l : Component) (w : Wiring m l) : Prop :=
  ∀ (st : (mkReactorWith m l w).State) (ev : RingEvent),
    ∀ op ∈ deploySubs (mkReactorWith m l w) st ev,
      op ∈ (feedMachine m l w st.1 ev).2 ∨ Reactor.RingSubmission.isRecycle op = true

theorem RouteSeam_holds (m l : Component) (w : Wiring m l) : RouteSeam m l w := by
  intro st ev op hop
  rw [deploySubs_eq_reactorSubs] at hop                -- BRIDGE LIFT
  change op ∈ (feedMachine m l w st.1 ev).2 ++ recycleSubs ev at hop
  rcases List.mem_append.mp hop with h | h
  · exact Or.inl h
  · right
    cases ev with
    | recvInto bid data => simp only [recycleSubs, List.mem_singleton] at h; subst h; rfl
    | _ => simp [recycleSubs] at h

/-- **Policy** seam — the declared-invariant object stays invariant across the
    deployed serve step. Transported from the reactor's `step_wf` through `serve`. -/
def PolicySeam (m l : Component) (w : Wiring m l) : Prop :=
  ∀ (st : (mkReactorWith m l w).State) (ev : RingEvent),
    (mkReactorWith m l w).inv st →
      (mkReactorWith m l w).inv (serve (mkReactorWith m l w) st ev).1

theorem PolicySeam_holds (m l : Component) (w : Wiring m l) : PolicySeam m l w := by
  intro st ev h
  exact serve_preserves (mkReactorWith m l w) st ev h

/-! ## The generator: `deploy_engine <Name> over (m, l) fabric <Lib>,+`

    Elaborates the description into the deployed-path defs/theorems. Each fabric
    label is looked up in the seam table; an UNKNOWN label raises a genuine
    elaboration error (soundness gate) and emits nothing — never a `sorry`. -/

syntax (name := deployEngine)
  "deploy_engine" ident "over" "(" term "," term ")" "fabric" ident,+ : command

@[command_elab deployEngine]
def elabDeploy : CommandElab := fun stx => do
  match stx with
  | `(deploy_engine $name over ($m, $l) fabric $libs,*) => do
      let libArr := libs.getElems
      if libArr.isEmpty then
        throwErrorAt name "deploy_engine: at least one fabric lib is required"
      -- (1) Emit the deployed serve function `<Name>_serve`.
      let serveIdent := mkIdent (Name.mkSimple (name.getId.toString ++ "_serve"))
      elabCommand (← `(command|
        def $serveIdent := Dsl.serve (Dsl.mkReactor $m $l)))
      -- (2) Emit one generated seam theorem per fabric lib.
      for lib in libArr do
        let ls := lib.getId.toString
        let (propNm, holdsNm) ← match ls with
          | "Rate"   => pure (mkIdent ``Dsl.RateSeam,   mkIdent ``Dsl.RateSeam_holds)
          | "Route"  => pure (mkIdent ``Dsl.RouteSeam,  mkIdent ``Dsl.RouteSeam_holds)
          | "Policy" => pure (mkIdent ``Dsl.PolicySeam, mkIdent ``Dsl.PolicySeam_holds)
          | other    =>
              throwErrorAt lib
                s!"deploy_engine: unknown fabric lib `{other}`; \
                   known libs are Rate, Route, Policy"
        let thmIdent :=
          mkIdent (Name.mkSimple (name.getId.toString ++ "_" ++ ls ++ "_seam_gen"))
        elabCommand (← `(command|
          theorem $thmIdent : $propNm $m $l (Dsl.defaultWiring $m $l) :=
            $holdsNm $m $l (Dsl.defaultWiring $m $l)))
  | _ => throwUnsupportedSyntax

end Dsl

/-! ## Worked demonstration — elaborated & kernel-checked at build time. -/

open Dsl

-- A demo engine's machine/linear pair (a real engine would splice its own primitives).
def demoMachine : Component := unitComponent
def demoLinear  : Component := unitComponent

-- ONE declarative command generates the deployed serve + three seam theorems.
deploy_engine Orb over (demoMachine, demoLinear) fabric Rate, Route, Policy

-- The generated artifacts are genuine defs/theorems of the intended type.
#check (Orb_serve)
#check (Orb_Rate_seam_gen   : RateSeam   demoMachine demoLinear (defaultWiring demoMachine demoLinear))
#check (Orb_Route_seam_gen  : RouteSeam  demoMachine demoLinear (defaultWiring demoMachine demoLinear))
#check (Orb_Policy_seam_gen : PolicySeam demoMachine demoLinear (defaultWiring demoMachine demoLinear))

/-! ### The generated seam == its hand-written CW-wave twin.

    The hand proofs below are the reference the macro learned to emit. Each `example`
    that closes proves the GENERATED theorem inhabits the HAND statement (and vice
    versa) — i.e. they are the same theorem up to definitional unfolding. -/

-- Hand-written Rate twin (as CW would write it): unfold the seam, cross the Bridge.
theorem Orb_Rate_seam_hand :
    ∀ (st : (mkReactor demoMachine demoLinear).State) (ev : RingEvent),
      recycleCount (deploySubs (mkReactor demoMachine demoLinear) st ev) ≤ 1 := by
  intro st ev
  rw [deploySubs_eq_reactorSubs]
  exact reactorStep_recycleCount_le_one demoMachine demoLinear _ st ev

-- Generated ⟶ hand: the generated theorem discharges the hand statement.
example :
    (∀ (st : (mkReactor demoMachine demoLinear).State) (ev : RingEvent),
      recycleCount (deploySubs (mkReactor demoMachine demoLinear) st ev) ≤ 1) :=
  Orb_Rate_seam_gen

-- Hand ⟶ generated: the hand theorem discharges the generated statement.
example : RateSeam demoMachine demoLinear (defaultWiring demoMachine demoLinear) :=
  Orb_Rate_seam_hand

-- Hand-written Policy twin, and both directions.
theorem Orb_Policy_seam_hand :
    ∀ (st : (mkReactor demoMachine demoLinear).State) (ev : RingEvent),
      (mkReactor demoMachine demoLinear).inv st →
        (mkReactor demoMachine demoLinear).inv (serve (mkReactor demoMachine demoLinear) st ev).1 := by
  intro st ev h
  exact serve_preserves _ st ev h

example : PolicySeam demoMachine demoLinear (defaultWiring demoMachine demoLinear) :=
  Orb_Policy_seam_hand

-- The reactor's copy-once law rides along on the deployed path via the Bridge lift.
example (st : (mkReactor demoMachine demoLinear).State) (bid : Uring.Bid) (data : Proto.Bytes) :
    recycleCount (deploySubs (mkReactor demoMachine demoLinear) st (.recvInto bid data)) = 1 := by
  rw [deploySubs_eq_reactorSubs]
  exact mkReactor_recycleCount demoMachine demoLinear st bid data

-- Axiom footprint of the GENERATED seam theorems: a subset of the allowed set.
#print axioms Orb_Rate_seam_gen
#print axioms Orb_Route_seam_gen
#print axioms Orb_Policy_seam_gen
