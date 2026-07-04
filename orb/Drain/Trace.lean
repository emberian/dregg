/-
Drain.Trace — the drain FSM over a trace of events, and the headline theorems
as invariants of every reachable state.

A run is a list of `Event`s applied left to right from a starting `DState`.
`run` folds the state.  The two per-step invariants proved in `Drain.Basic` —
the accounting identity (`Accounted`) and the drain-shape invariant
(`DrainShape`) — are lifted over `run`, then specialized to states reachable
from `init`.

Headline results:

  * `accounting_identity` (**theorem 2**) — in every reachable state, the number
    of admitted requests equals in-flight + completed + force-closed: no
    in-flight request is silently lost.
  * `drained_iff_inflight_zero` (**theorem 3**) — among the draining/drained
    states, the server is drained exactly when the in-flight count is zero.
  * `run_closed` (**theorem 4**) — closed is absorbing over a whole run.
  * `run_notRunning` (**theorem 1**, trace form) — once out of running, a run
    never re-enters running, so every subsequent accept is refused.
-/

import Drain.Basic

namespace Drain

/-- Fold a list of events over the state, oldest first. -/
def run (s : DState) : List Event → DState
  | [] => s
  | e :: es => run (step s e).1 es

@[simp] theorem run_nil (s : DState) : run s [] = s := rfl

@[simp] theorem run_cons (s : DState) (e : Event) (es : List Event) :
    run s (e :: es) = run (step s e).1 es := rfl

/-! ### Lifting the invariants over a run -/

/-- The accounting identity is preserved along an entire run. -/
theorem run_accounted {s : DState} (es : List Event) (h : Accounted s) :
    Accounted (run s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (step_accounted e h)

/-- The drain-shape invariant is preserved along an entire run. -/
theorem run_drainShape {s : DState} (es : List Event) (h : DrainShape s) :
    DrainShape (run s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (step_drainShape e h)

/-- Every state reachable from `init` satisfies the accounting identity. -/
theorem reachable_accounted (es : List Event) : Accounted (run init es) :=
  run_accounted es accounted_init

/-- Every state reachable from `init` satisfies the drain-shape invariant. -/
theorem reachable_drainShape (es : List Event) : DrainShape (run init es) :=
  run_drainShape es drainShape_init

/-! ### Theorem 2 — the accounting identity in every reachable state -/

/-- **The accounting identity.** In every state reachable from a fresh server,
the total number of admitted requests equals the number still in flight, plus
those completed, plus those force-closed at the deadline.  Every in-flight
request is accounted for; none is silently dropped. -/
theorem accounting_identity (es : List Event) :
    (run init es).entered
      = (run init es).inflight + (run init es).completed + (run init es).forcedClosed :=
  reachable_accounted es

/-! ### Theorem 3 — drained iff the in-flight count is zero -/

/-- **Progress.** In any reachable draining/drained state, the server has drained
exactly when its in-flight count has reached zero: draining still has work
outstanding, drained has none. -/
theorem drained_iff_inflight_zero (es : List Event)
    (hmode : (run init es).mode = .draining ∨ (run init es).mode = .drained) :
    (run init es).mode = .drained ↔ (run init es).inflight = 0 := by
  obtain ⟨h1, h2, _⟩ := reachable_drainShape es
  constructor
  · intro hd; exact h2 hd
  · intro hz
    rcases hmode with hm | hm
    · exfalso; have := h1 hm; omega
    · exact hm

/-! ### Theorem 4 — closed is absorbing over a run -/

/-- **Closed is absorbing.** If a run begins in closed it ends in closed. -/
theorem run_closed {s : DState} (es : List Event) (h : s.mode = .closed) :
    (run s es).mode = .closed := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (closed_absorbing e h)

/-! ### Theorem 1 — once out of running, never back; accepts stay refused -/

/-- One step out of running stays out of running: no transition re-enters the
accepting mode. -/
theorem step_notRunning_absorbing {s : DState} (e : Event) (h : s.mode ≠ .running) :
    (step s e).1.mode ≠ .running := by
  cases e <;> simp only [step] <;> (repeat' split) <;> simp_all

/-- **New work stays shut off.** Once a run leaves running it never returns, so
the mode remains non-running for the rest of the run. -/
theorem run_notRunning {s : DState} (es : List Event) (h : s.mode ≠ .running) :
    (run s es).mode ≠ .running := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (step_notRunning_absorbing e h)

/-- Consequently, after the mode has left running, every accept along the run is
refused. -/
theorem no_admit_after_drain {s : DState} (es : List Event) (h : s.mode ≠ .running) :
    (step (run s es) .acceptReq).2 = [Output.refused] :=
  acceptReq_refused_of_not_running (run_notRunning es h)

/-! ### Executable checks -/

/-- A fresh server admits an accept. -/
example : (step init .acceptReq).2 = [Output.admitted] := by decide

/-- After begin-drain, an accept is refused. -/
example :
    (step (run init [.acceptReq, .beginDrain 10]) .acceptReq).2 = [Output.refused] := by
  decide

/-- Happy path: one connection is accepted, begin-drain fires, the connection
completes → the server is drained. -/
example : (run init [.acceptReq, .beginDrain 10, .complete]).mode = .drained := by
  decide

/-- Once drained, a clock tick closes the server. -/
example :
    (run init [.acceptReq, .beginDrain 10, .complete, .tick 3]).mode = .closed := by
  decide

/-- Begin-drain with nothing in flight goes straight to drained. -/
example : (run init [.beginDrain 10]).mode = .drained := by decide

/-- Straggler path: two connections still in flight at the deadline are
force-closed; the server closes and the force-closed tally records both. -/
example :
    (run init [.acceptReq, .acceptReq, .beginDrain 5, .forceClose 5]).mode = .closed := by
  decide

example :
    (run init [.acceptReq, .acceptReq, .beginDrain 5, .forceClose 5]).forcedClosed = 2 := by
  decide

/-- Before the deadline, a force-close is a no-op: the server stays draining
(no straggler dropped early). -/
example :
    (run init [.acceptReq, .beginDrain 5, .forceClose 4]).mode = .draining := by
  decide

/-- The accounting identity, concretely: entered = inflight + completed +
force-closed after a mixed run. -/
example :
    let s := run init [.acceptReq, .acceptReq, .beginDrain 5, .complete, .forceClose 5]
    s.entered = s.inflight + s.completed + s.forcedClosed := by decide

end Drain
