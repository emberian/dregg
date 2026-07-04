/-
DrainCorrect — a specification of RFC-style graceful connection draining, stated
independently of any implementation, and a refinement theorem showing the drain
transition system (`Drain.step` / `Drain.run`) conforms to it.

The specification is the graceful-shutdown discipline shared by HTTP servers and
proxies (HTTP/1.1 `Connection: close` shutdown; HTTP/2 GOAWAY, RFC 9113 §6.8:
"Once sent, the sender will ignore … new streams", while "streams … established
before … [are] completed"; the general SIGTERM drain of a listener).  Reduced to
its lifecycle invariants it says:

  * once the drain signal has been issued, no new connection is admitted; and
  * every in-flight request is allowed to complete — the drained terminal state
    is entered exactly when the in-flight count has reached zero: never while
    work is still outstanding (no early cut-off), and always once the last
    request has finished (progress).

`DrainContract` below fixes those clauses over an ARBITRARY lifecycle system —
an abstract bundle of a start state, a transition function over the drain event
alphabet, and three observations (has-drained, in-the-drain-window, in-flight
count).  Nothing in the contract mentions the drain implementation.  The
refinement (`drain_refines_spec`) instantiates the contract with the real system
and discharges every clause.  Non-vacuity is witnessed by two mutants — one that
admits a connection after the signal, one that declares itself drained while a
request is still in flight — each of which is proved to VIOLATE the contract.
-/

import Drain.Trace

namespace Drain
namespace Correct

/-! ## The specification, stated independently of the implementation -/

/-- A drain signal has been issued somewhere in the event history.  This is a
fact about the observed input sequence alone. -/
def Signalled (es : List Event) : Prop := ∃ dl, Event.beginDrain dl ∈ es

/-- An abstract lifecycle system: a start state, a transition function over the
drain event alphabet emitting accept-outcomes, and three observations the
specification refers to — whether the system has reached the drained terminal,
whether it is inside the drain window (draining or drained), and its in-flight
count.  The transition/state type is opaque: the contract never inspects it. -/
structure System where
  σ : Type
  start : σ
  next : σ → Event → σ × List Output
  drained : σ → Bool
  winding : σ → Bool
  live : σ → Nat

/-- Fold an event history over a system, oldest event first. -/
def System.run (M : System) (es : List Event) : M.σ :=
  es.foldl (fun s e => (M.next s e).1) M.start

/-- **The graceful-drain contract.**  A lifecycle system conforms when, for
every event history:

* `noAdmitAfterSignal` — after the drain signal, an accept attempt never yields
  `admitted` (new connections are shut off);
* `neverDrainedWithWork` — the drained terminal is never observed while the
  in-flight count is positive (in-flight requests are allowed to complete);
* `drainCompletes` — a system in the drain window whose in-flight count has
  reached zero has reached the drained terminal (progress).

The definition mentions only `System`, `Signalled`, and the shared event/output
alphabet.  It does not refer to the drain implementation. -/
structure DrainContract (M : System) : Prop where
  noAdmitAfterSignal :
    ∀ es, Signalled es → Output.admitted ∉ (M.next (M.run es) .acceptReq).2
  neverDrainedWithWork :
    ∀ es, M.drained (M.run es) = true → M.live (M.run es) = 0
  drainCompletes :
    ∀ es, M.winding (M.run es) = true → M.live (M.run es) = 0 →
      M.drained (M.run es) = true

/-! ## Glue: relate `System.run` (a left fold) to `Drain.run` -/

/-- `Drain.run` is the left fold of `step`. -/
theorem run_eq_foldl (s : DState) (es : List Event) :
    Drain.run s es = es.foldl (fun s e => (step s e).1) s := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp only [Drain.run_cons, List.foldl_cons]; exact ih _

/-! ## The implementation as a `System` -/

/-- The real drain transition system, presented as an abstract `System`. -/
def DrainImpl : System where
  σ := DState
  start := init
  next := step
  drained := fun s => decide (s.mode = .drained)
  winding := fun s => decide (s.mode = .draining ∨ s.mode = .drained)
  live := fun s => s.inflight

@[simp] theorem drainImpl_next (s : DState) (e : Event) :
    DrainImpl.next s e = step s e := rfl
@[simp] theorem drainImpl_drained (s : DState) :
    DrainImpl.drained s = decide (s.mode = .drained) := rfl
@[simp] theorem drainImpl_winding (s : DState) :
    DrainImpl.winding s = decide (s.mode = .draining ∨ s.mode = .drained) := rfl
@[simp] theorem drainImpl_live (s : DState) : DrainImpl.live s = s.inflight := rfl

@[simp] theorem drainImpl_run (es : List Event) :
    DrainImpl.run es = Drain.run init es := by
  simp only [System.run, DrainImpl]
  exact (run_eq_foldl init es).symm

/-! ## Lemmas feeding the refinement -/

/-- Issuing a drain signal from any state leaves the running mode. -/
theorem beginDrain_leaves_running (s : DState) (dl : Nat) :
    (step s (Event.beginDrain dl)).1.mode ≠ .running := by
  simp only [step]
  split <;> (try split) <;> simp_all

/-- Once a `beginDrain` appears in the history, the run has left running for
good (begin-drain moves out of running and no transition re-enters it). -/
theorem run_notRunning_of_mem {s : DState} {es : List Event} {dl : Nat}
    (h : Event.beginDrain dl ∈ es) : (Drain.run s es).mode ≠ .running := by
  induction es generalizing s with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons e es ih =>
    rcases List.mem_cons.1 h with heq | hmem
    · subst heq
      rw [Drain.run_cons]
      exact run_notRunning es (beginDrain_leaves_running s dl)
    · rw [Drain.run_cons]; exact ih hmem

/-- A signalled run is not in running mode. -/
theorem signalled_notRunning {es : List Event} (h : Signalled es) :
    (Drain.run init es).mode ≠ .running := by
  obtain ⟨dl, hdl⟩ := h
  exact run_notRunning_of_mem hdl

/-! ## The refinement: the implementation conforms to the specification -/

/-- **Refinement.**  The drain transition system satisfies the graceful-drain
contract on every event history.  This is the headline correctness result:
the implementation *refines* the independent specification. -/
theorem drain_refines_spec : DrainContract DrainImpl where
  noAdmitAfterSignal := by
    intro es hsig
    simp only [drainImpl_run, drainImpl_next]
    rw [acceptReq_refused_of_not_running (signalled_notRunning hsig)]
    simp
  neverDrainedWithWork := by
    intro es hd
    simp only [drainImpl_run, drainImpl_drained, drainImpl_live] at hd ⊢
    have hmode : (Drain.run init es).mode = .drained := of_decide_eq_true hd
    obtain ⟨_, h2, _⟩ := reachable_drainShape es
    exact h2 hmode
  drainCompletes := by
    intro es hw hz
    simp only [drainImpl_run, drainImpl_drained, drainImpl_winding, drainImpl_live] at hw hz ⊢
    have hmode : (Drain.run init es).mode = .draining ∨ (Drain.run init es).mode = .drained :=
      of_decide_eq_true hw
    have : (Drain.run init es).mode = .drained :=
      (drained_iff_inflight_zero es hmode).2 hz
    exact decide_eq_true this

/-- The progress half spelled out as a biconditional: inside the drain window,
the drained terminal is reached exactly when the in-flight count is zero. -/
theorem drainImpl_drained_iff_idle (es : List Event)
    (hw : (Drain.run init es).mode = .draining ∨ (Drain.run init es).mode = .drained) :
    (Drain.run init es).mode = .drained ↔ (Drain.run init es).inflight = 0 :=
  drained_iff_inflight_zero es hw

/-! ## Non-vacuity: broken implementations violate the specification -/

/-- Mutant 1 — admits a new connection unconditionally, even after the drain
signal.  Every other transition is the real one. -/
def brokenAcceptNext (s : DState) : Event → DState × List Output
  | .acceptReq =>
      ({ s with inflight := s.inflight + 1, entered := s.entered + 1 }, [Output.admitted])
  | e => step s e

/-- The always-admitting mutant as a `System`. -/
def BrokenAccept : System where
  σ := DState
  start := init
  next := brokenAcceptNext
  drained := fun s => decide (s.mode = .drained)
  winding := fun s => decide (s.mode = .draining ∨ s.mode = .drained)
  live := fun s => s.inflight

/-- Mutant 2 — jumps straight to the drained terminal on a drain signal, even
with requests still in flight.  Every other transition is the real one. -/
def brokenProgressNext (s : DState) : Event → DState × List Output
  | .beginDrain dl => ({ s with mode := .drained, deadline := dl }, [])
  | e => step s e

/-- The drain-early mutant as a `System`. -/
def BrokenProgress : System where
  σ := DState
  start := init
  next := brokenProgressNext
  drained := fun s => decide (s.mode = .drained)
  winding := fun s => decide (s.mode = .draining ∨ s.mode = .drained)
  live := fun s => s.inflight

/-- **Non-vacuity, clause 1.**  A system that admits a connection after the
drain signal fails the contract: after `beginDrain 0`, the mutant still answers
an accept with `admitted`, contradicting `noAdmitAfterSignal`. -/
theorem brokenAccept_violates : ¬ DrainContract BrokenAccept := by
  intro h
  have hsig : Signalled [Event.beginDrain 0] := ⟨0, List.mem_cons_self _ _⟩
  have hno := h.noAdmitAfterSignal [Event.beginDrain 0] hsig
  have hmem : Output.admitted ∈
      (BrokenAccept.next (BrokenAccept.run [Event.beginDrain 0]) Event.acceptReq).2 := by
    decide
  exact hno hmem

/-- **Non-vacuity, clause 2.**  A system that reaches the drained terminal while
a request is still in flight fails the contract: after `[acceptReq, beginDrain 0]`
the mutant reports drained with one request in flight, contradicting
`neverDrainedWithWork`. -/
theorem brokenProgress_violates : ¬ DrainContract BrokenProgress := by
  intro h
  have hdr : BrokenProgress.drained
      (BrokenProgress.run [Event.acceptReq, Event.beginDrain 0]) = true := by decide
  have hlive := h.neverDrainedWithWork [Event.acceptReq, Event.beginDrain 0] hdr
  have hne : BrokenProgress.live
      (BrokenProgress.run [Event.acceptReq, Event.beginDrain 0]) = 1 := by decide
  rw [hlive] at hne
  exact absurd hne (by decide)

end Correct
end Drain
