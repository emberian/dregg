/-
ProxyHealthCorrect — correctness of active health checking by refinement.

Active health checking probes each backend on an interval; each probe yields a
success or a failure. A backend's eligibility for traffic is governed by a
hysteresis rule with two thresholds:

  * HEALTHY  once `rise` **consecutive** successes have accumulated;
  * UNHEALTHY once `fall` **consecutive** failures have accumulated;

and every probe updates exactly the relevant consecutive counter while resetting
the other one. This is the rise/fall (a.k.a. healthy-threshold / unhealthy-
threshold) health-check rule as specified for active checks — e.g. the HAProxy
configuration manual's `rise <count>` / `fall <count>` server parameters
("`rise` … number of consecutive valid health checks before considering the
server UP"; "`fall` … number of consecutive invalid health checks before
considering the server DOWN"), matching the healthy_threshold / unhealthy_
threshold semantics of an active-check load balancer.

This module states that rule as an INDEPENDENT threshold FSM (`specStep`,
below) — written only from the prose above, with no reference to the running
machine `Proxy.hstep` — and proves the running machine's eligibility verdict
EQUALS the specification's on every probe history (`health_refines_spec`).

The specification is deliberately NOT the implementation renamed:

  * the spec re-evaluates BOTH thresholds on every probe; the implementation
    only tests the flip-relevant threshold (it never tests `rise` while already
    healthy, nor `fall` while already unhealthy);
  * the spec KEEPS the consecutive counter when a threshold flips the verdict;
    the implementation zeroes both counters on a flip.

So the two machines are NOT state-identical — their counter values diverge in
the "dead" direction — and the refinement is an invariant argument
(`rel_step`), not a definitional unfolding. The invariant records that the two
verdicts always agree, the failure counters agree while healthy, and the
success counters agree while unhealthy; the dead counter is free to differ,
which is exactly why a naive `rfl` cannot prove this.

Non-vacuity (`broken_no_hysteresis_fails`, `broken_no_recovery_fails`): a
machine that flips on a single probe (no hysteresis), or one that never
recovers, provably DISAGREES with the specification on a concrete history — so
the refinement theorem has real content and a wrong implementation fails it.
-/

import Proxy.Health

namespace Proxy.HealthSpec

open Proxy

/-! ## The independent specification

A verdict plus the two consecutive-run counters. Distinct types from the
implementation's `HealthState`, so the spec cannot be the implementation under
another name. -/

/-- Specified health verdict. -/
inductive Verdict where
  | healthy
  | unhealthy
deriving DecidableEq, Repr

/-- Specification state: the current verdict and the two consecutive-run
counters (`succ` = consecutive successes so far, `fail` = consecutive
failures so far). -/
structure SpecState where
  verdict : Verdict
  succ : Nat
  fail : Nat
deriving DecidableEq, Repr

/-- Optimistic start: healthy, both runs empty. -/
def SpecState.start : SpecState := ⟨.healthy, 0, 0⟩

/-- The specified transition, written straight from the rule: a probe extends
its own consecutive counter and resets the other; the verdict becomes HEALTHY
once the success run reaches `rise`, UNHEALTHY once the failure run reaches
`fall`, and is otherwise unchanged. Both thresholds are consulted on every
probe. -/
def specStep (g : HealthGate) (st : SpecState) (p : Probe) : SpecState :=
  match p with
  | .pass =>
    let s' := st.succ + 1
    { verdict := if g.rise ≤ s' then Verdict.healthy else st.verdict
      succ := s'
      fail := 0 }
  | .fail =>
    let f' := st.fail + 1
    { verdict := if g.fall ≤ f' then Verdict.unhealthy else st.verdict
      succ := 0
      fail := f' }

/-- Run a probe history through the specification, oldest first. -/
def specRun (g : HealthGate) (st : SpecState) : List Probe → SpecState
  | [] => st
  | p :: ps => specRun g (specStep g st p) ps

/-- Specified eligibility: a backend takes traffic iff its verdict is HEALTHY. -/
def SpecState.eligible (st : SpecState) : Bool :=
  match st.verdict with
  | .healthy => true
  | .unhealthy => false

@[simp] theorem specRun_cons (g : HealthGate) (st : SpecState) (p : Probe)
    (ps : List Probe) : specRun g st (p :: ps) = specRun g (specStep g st p) ps :=
  rfl

/-! ## The refinement invariant

The implementation `Proxy.hstep`/`Proxy.hrun` refines the specification: the
two verdicts always agree; the failure counters agree while healthy; the
success counters agree while unhealthy. -/

/-- The coupling invariant between an implementation state and a spec state. -/
structure Rel (s : HealthState) (st : SpecState) : Prop where
  verdict : s.up = true ↔ st.verdict = Verdict.healthy
  failEq : s.up = true → s.failStreak = st.fail
  passEq : s.up = false → s.passStreak = st.succ

/-- The aligned start states are related. -/
theorem rel_start : Rel HealthState.initUp SpecState.start where
  verdict := by simp [HealthState.initUp, SpecState.start]
  failEq := by intro _; rfl
  passEq := by intro h; simp [HealthState.initUp] at h

/-- **One-step refinement.** `Rel` is preserved by a probe. This is the crux:
it holds despite the two machines disagreeing on the dead counter after a
flip. -/
theorem rel_step (g : HealthGate) (s : HealthState) (st : SpecState)
    (h : Rel s st) (p : Probe) : Rel (hstep g s p) (specStep g st p) := by
  obtain ⟨u, ps, fs⟩ := s
  obtain ⟨v, cs, cf⟩ := st
  obtain ⟨hiff, hfs, hps⟩ := h
  cases p with
  | pass =>
    cases u with
    | true =>
      have hv : v = Verdict.healthy := hiff.mp rfl
      subst hv
      have himpl : hstep g ⟨true, ps, fs⟩ Probe.pass = ⟨true, ps + 1, 0⟩ := rfl
      have hspec : specStep g ⟨Verdict.healthy, cs, cf⟩ Probe.pass
          = ⟨Verdict.healthy, cs + 1, 0⟩ := by simp [specStep]
      rw [himpl, hspec]
      exact ⟨by simp, by intro _; rfl, by intro hc; simp at hc⟩
    | false =>
      have hv : v = Verdict.unhealthy := by
        cases v with
        | healthy => have hcon := hiff.mpr rfl; simp at hcon
        | unhealthy => rfl
      subst hv
      have hpscs : ps = cs := hps rfl
      subst hpscs
      by_cases hrise : g.rise ≤ ps + 1
      · have himpl : hstep g ⟨false, ps, fs⟩ Probe.pass = ⟨true, 0, 0⟩ := by
          simp [hstep, hrise]
        have hspec : specStep g ⟨Verdict.unhealthy, ps, cf⟩ Probe.pass
            = ⟨Verdict.healthy, ps + 1, 0⟩ := by simp [specStep, hrise]
        rw [himpl, hspec]
        exact ⟨by simp, by intro _; rfl, by intro hc; simp at hc⟩
      · have himpl : hstep g ⟨false, ps, fs⟩ Probe.pass = ⟨false, ps + 1, 0⟩ := by
          simp [hstep, hrise]
        have hspec : specStep g ⟨Verdict.unhealthy, ps, cf⟩ Probe.pass
            = ⟨Verdict.unhealthy, ps + 1, 0⟩ := by simp [specStep, hrise]
        rw [himpl, hspec]
        exact ⟨by simp, by intro hc; simp at hc, by intro _; rfl⟩
  | fail =>
    cases u with
    | true =>
      have hv : v = Verdict.healthy := hiff.mp rfl
      subst hv
      have hfscf : fs = cf := hfs rfl
      subst hfscf
      by_cases hfall : g.fall ≤ fs + 1
      · have himpl : hstep g ⟨true, ps, fs⟩ Probe.fail = ⟨false, 0, 0⟩ := by
          simp [hstep, hfall]
        have hspec : specStep g ⟨Verdict.healthy, cs, fs⟩ Probe.fail
            = ⟨Verdict.unhealthy, 0, fs + 1⟩ := by simp [specStep, hfall]
        rw [himpl, hspec]
        exact ⟨by simp, by intro hc; simp at hc, by intro _; rfl⟩
      · have himpl : hstep g ⟨true, ps, fs⟩ Probe.fail = ⟨true, 0, fs + 1⟩ := by
          simp [hstep, hfall]
        have hspec : specStep g ⟨Verdict.healthy, cs, fs⟩ Probe.fail
            = ⟨Verdict.healthy, 0, fs + 1⟩ := by simp [specStep, hfall]
        rw [himpl, hspec]
        exact ⟨by simp, by intro _; rfl, by intro hc; simp at hc⟩
    | false =>
      have hv : v = Verdict.unhealthy := by
        cases v with
        | healthy => have hcon := hiff.mpr rfl; simp at hcon
        | unhealthy => rfl
      subst hv
      have himpl : hstep g ⟨false, ps, fs⟩ Probe.fail = ⟨false, 0, fs + 1⟩ := rfl
      have hspec : specStep g ⟨Verdict.unhealthy, cs, cf⟩ Probe.fail
          = ⟨Verdict.unhealthy, 0, cf + 1⟩ := by simp [specStep]
      rw [himpl, hspec]
      exact ⟨by simp, by intro hc; simp at hc, by intro _; rfl⟩

/-- `Rel` is preserved across a whole probe history. -/
theorem rel_run (g : HealthGate) (s : HealthState) (st : SpecState)
    (h : Rel s st) : (trace : List Probe) →
    Rel (hrun g s trace) (specRun g st trace)
  | [] => by simpa using h
  | p :: ps => by
    rw [hrun_cons, specRun_cons]
    exact rel_run g (hstep g s p) (specStep g st p) (rel_step g s st h p) ps

/-- `Rel` forces the eligibility verdicts to coincide. -/
theorem rel_eligible {s : HealthState} {st : SpecState} (h : Rel s st) :
    s.up = st.eligible := by
  cases hv : st.verdict with
  | healthy =>
    have hup : s.up = true := h.verdict.mpr hv
    simp [SpecState.eligible, hv, hup]
  | unhealthy =>
    have hup : s.up = false := by
      cases hs : s.up with
      | true => have := h.verdict.mp hs; rw [hv] at this; exact absurd this (by decide)
      | false => rfl
    simp [SpecState.eligible, hv, hup]

/-! ## The refinement theorem -/

/-- **CORRECTNESS OF ACTIVE HEALTH CHECKING.** For every gate and every probe
history, the running health FSM's eligibility verdict (`.up`, snapshotted into
`Backend.healthy`) EQUALS the independently specified threshold-FSM verdict.
The implementation refines the rise/fall hysteresis specification on all
inputs. -/
theorem health_refines_spec (g : HealthGate) (trace : List Probe) :
    (hrun g HealthState.initUp trace).up
      = (specRun g SpecState.start trace).eligible :=
  rel_eligible (rel_run g HealthState.initUp SpecState.start rel_start trace)

/-! ## Non-vacuity: wrong implementations fail the specification

Two broken health machines that a load balancer must NOT ship. Each provably
disagrees with the specification on a concrete probe history, so the refinement
theorem above has genuine content — it is not `spec = spec`. -/

/-- Broken machine A: NO HYSTERESIS — flips the verdict on a single probe. -/
def noHystStep (_ : HealthGate) (_ : HealthState) : Probe → HealthState
  | .pass => ⟨true, 0, 0⟩
  | .fail => ⟨false, 0, 0⟩

def noHystRun (g : HealthGate) (s : HealthState) : List Probe → HealthState
  | [] => s
  | p :: ps => noHystRun g (noHystStep g s p) ps

/-- With `fall = 3`, one failure must NOT unseat a healthy backend (the spec
keeps it eligible), yet the no-hysteresis machine drops it. They disagree, so
the no-hysteresis machine is not a valid implementation. -/
theorem broken_no_hysteresis_fails :
    (noHystRun ⟨2, 3⟩ HealthState.initUp [Probe.fail]).up
      ≠ (specRun ⟨2, 3⟩ SpecState.start [Probe.fail]).eligible := by
  decide

/-- Broken machine B: NEVER RECOVERS — once down, passes cannot bring it up. -/
def stuckStep (_ : HealthGate) (s : HealthState) : Probe → HealthState
  | .pass => if s.up then ⟨true, 0, 0⟩ else ⟨false, 0, 0⟩
  | .fail => ⟨false, 0, 0⟩

def stuckRun (g : HealthGate) (s : HealthState) : List Probe → HealthState
  | [] => s
  | p :: ps => stuckRun g (stuckStep g s p) ps

/-- With `rise = 2`, `fall = 3`, a backend knocked down by three failures must
recover after two successes (the spec makes it eligible again), yet the stuck
machine stays down forever. They disagree, so a non-recovering machine is not a
valid implementation. -/
theorem broken_no_recovery_fails :
    (stuckRun ⟨2, 3⟩ HealthState.initUp
        [Probe.fail, Probe.fail, Probe.fail, Probe.pass, Probe.pass]).up
      ≠ (specRun ⟨2, 3⟩ SpecState.start
        [Probe.fail, Probe.fail, Probe.fail, Probe.pass, Probe.pass]).eligible := by
  decide

/-- Sanity: the SPECIFICATION itself exhibits the hysteresis it claims — one
failure leaves a healthy backend eligible; three consecutive failures drop it;
two subsequent successes restore it. (Concrete `decide` checks of the spec, not
the impl — the refinement theorem ties the impl to it.) -/
example : (specRun ⟨2, 3⟩ SpecState.start [Probe.fail]).eligible = true := by decide
example : (specRun ⟨2, 3⟩ SpecState.start
    [Probe.fail, Probe.fail, Probe.fail]).eligible = false := by decide
example : (specRun ⟨2, 3⟩ SpecState.start
    [Probe.fail, Probe.fail, Probe.fail, Probe.pass, Probe.pass]).eligible = true := by decide

end Proxy.HealthSpec
