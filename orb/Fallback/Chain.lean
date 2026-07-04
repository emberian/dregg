/-
Fallback.Chain — the fallback-chain evaluator and its accounting theorems.

A fallback chain is an ordered `List (Handler Req Resp)`. The chain tries
handlers in configured order. A handler either produces a response (the chain
stops — it is served) or fails with an error class. On a failure the retry
policy decides: a *retryable* class falls through to the next handler; a
*terminal* class stops the chain immediately. If the chain is exhausted without
a success, the terminal error page is served. The served terminal page carries
an error class — the class that stopped the chain, or, if every handler fell
through, the last such class (seeded by a configured `fallback` class for the
empty chain).

`stepChain` threads the trace of tried handler ids (in order), the last error
class seen, and returns `(trace, served)`. It is fuel-free structural recursion
on the handler list, so it is total and deterministic by construction.

THEOREMS (mapped to the task):

  (1) served-exactly-once — every run serves EXACTLY ONE thing: one handler
      response OR the terminal error page, never zero, never two. Captured as an
      accounting identity `servedResponses + servedTerminal = 1` on `Served`,
      with `served_never_two` / `served_never_zero` spelling out the two halves.
      `runChain_served_once` lifts it to every run.
  (2) stops at first success — `stepChain_stop_at_success` /
      `runChain_stops_at_first_success`: once the first non-fall-through handler
      is a success, the served result is that handler's response and the trace
      is exactly the handlers up to and including it — NO handler after the
      winner appears. `runChain_success_trace_length` counts it.
  (3) non-retryable terminates immediately — `stepChain_stop_at_nonretryable` /
      `runChain_nonretryable_terminates`: the first handler to fail with a
      terminal class stops the chain there; later handlers are not tried.
  (4) total & deterministic, bounded by the handler count —
      `stepChain` is fuel-free structural recursion (totality by construction);
      `runChain_deterministic` (output depends only on input);
      `runChain_trace_length_le` (the trace never exceeds the handler count).
  (5) trace is a prefix of the configured chain — `stepChain_trace_prefix` /
      `runChain_trace_prefix`: in EVERY outcome the tried-handler trace is a
      prefix of the configured id list (no handler out of order, none skipped
      before the stopping point).

  Completeness of the case split: `stepChain_exhaust` — if every handler fails
  retryably, the terminal page is served and every handler was tried (trace =
  full id list). With (2) and (3) this exhausts the outcomes, reinforcing (1).
-/

import Fallback.Taxonomy

namespace Fallback.Chain

/-- One handler in the chain: a stable id plus a pure attempt that either
produces a response or fails with a classified error. Purity is what makes the
whole chain a deterministic function of its input. -/
structure Handler (Req Resp : Type) where
  hid : Nat
  run : Req → Outcome Resp

/-- What ultimately served a request: either some handler's response
(`byHandler`, carrying the winning id) or the terminal error page (`terminal`,
carrying the error class it renders). These are the only two possibilities —
that disjointness is theorem (1). -/
inductive Served (Resp : Type) where
  | byHandler (hid : Nat) (resp : Resp)
  | terminal (cls : ErrClass)
deriving Repr

variable {Req Resp : Type}

/-- Number of handler responses this outcome serves (`0` or `1`). -/
def Served.servedResponses : Served Resp → Nat
  | .byHandler _ _ => 1
  | .terminal _ => 0

/-- Number of terminal error pages this outcome serves (`0` or `1`). -/
def Served.servedTerminal : Served Resp → Nat
  | .byHandler _ _ => 0
  | .terminal _ => 1

/-! ### Theorem (1): served exactly once -/

/-- **Served exactly once (the accounting identity).** Every outcome serves
exactly one thing: a handler response and a terminal page never coexist, and it
is never neither. -/
theorem Served.served_once (s : Served Resp) :
    s.servedResponses + s.servedTerminal = 1 := by
  cases s <;> rfl

/-- **Never two.** A handler response and a terminal error page are never both
served. -/
theorem Served.served_never_two (s : Served Resp) :
    ¬ (s.servedResponses = 1 ∧ s.servedTerminal = 1) := by
  cases s <;> simp [Served.servedResponses, Served.servedTerminal]

/-- **Never zero.** Something is always served. -/
theorem Served.served_never_zero (s : Served Resp) :
    ¬ (s.servedResponses = 0 ∧ s.servedTerminal = 0) := by
  cases s <;> simp [Served.servedResponses, Served.servedTerminal]

/-! ### The evaluator -/

/-- Try the handlers in order, threading the trace `tr` of tried ids and the
last error class `lc` (the class the terminal page will render if the chain is
exhausted). Fuel-free structural recursion on the handler list.

  * a handler that produces a response wins immediately (chain stops);
  * a handler that fails retryably falls through, recording the class;
  * a handler that fails terminally stops the chain and serves that class;
  * the empty chain serves the terminal page for the carried class. -/
def stepChain (rp : RetryPolicy) :
    List (Handler Req Resp) → Req → List Nat → ErrClass → List Nat × Served Resp
  | [], _req, tr, lc => (tr, .terminal lc)
  | h :: rest, req, tr, _lc =>
    match h.run req with
    | .ok resp => (tr ++ [h.hid], .byHandler h.hid resp)
    | .err c =>
      match rp.retryable c with
      | true => stepChain rp rest req (tr ++ [h.hid]) c
      | false => (tr ++ [h.hid], .terminal c)

/-- Run a fallback chain on a request, from an empty trace. `fallback` is the
error class the terminal page renders if the chain is empty or every handler
falls through (i.e. the configured default error page). -/
def runChain (rp : RetryPolicy) (fallback : ErrClass)
    (hs : List (Handler Req Resp)) (req : Req) : List Nat × Served Resp :=
  stepChain rp hs req [] fallback

/-- Every run serves exactly one thing (theorem (1), lifted to `runChain`). -/
theorem runChain_served_once (rp : RetryPolicy) (fallback : ErrClass)
    (hs : List (Handler Req Resp)) (req : Req) :
    (runChain rp fallback hs req).2.servedResponses
      + (runChain rp fallback hs req).2.servedTerminal = 1 :=
  Served.served_once _

/-! ### Theorem (5): the trace is a prefix of the configured chain -/

/-- In every outcome, the tried-handler trace is the seed trace followed by a
prefix of the configured ids: no handler runs out of order, none is skipped
before the stopping point, and a stop merely truncates early. -/
theorem stepChain_trace_prefix (rp : RetryPolicy) (hs : List (Handler Req Resp)) :
    ∀ (req : Req) (tr : List Nat) (lc : ErrClass),
      (stepChain rp hs req tr lc).1 <+: tr ++ hs.map Handler.hid := by
  induction hs with
  | nil =>
    intro req tr _lc
    simp [stepChain]
  | cons h rest ih =>
    intro req tr lc
    have hrw : tr ++ (h :: rest).map Handler.hid
        = (tr ++ [h.hid]) ++ rest.map Handler.hid := by simp
    cases hrun : h.run req with
    | ok resp =>
      simp only [stepChain, hrun]
      rw [hrw]
      exact List.prefix_append _ _
    | err c =>
      cases hret : rp.retryable c with
      | false =>
        simp only [stepChain, hrun, hret]
        rw [hrw]
        exact List.prefix_append _ _
      | true =>
        simp only [stepChain, hrun, hret]
        rw [hrw]
        exact ih req (tr ++ [h.hid]) c

/-- The trace of a full run is a prefix of the configured id list. -/
theorem runChain_trace_prefix (rp : RetryPolicy) (fallback : ErrClass)
    (hs : List (Handler Req Resp)) (req : Req) :
    (runChain rp fallback hs req).1 <+: hs.map Handler.hid := by
  unfold runChain
  have := stepChain_trace_prefix rp hs req [] fallback
  simpa using this

/-! ### Theorem (4): total, deterministic, bounded by the handler count -/

/-- The trace never exceeds the seed length plus the handler count — the
fuel-free structural bound that witnesses termination. -/
theorem stepChain_length_le (rp : RetryPolicy) (hs : List (Handler Req Resp))
    (req : Req) (tr : List Nat) (lc : ErrClass) :
    (stepChain rp hs req tr lc).1.length ≤ tr.length + hs.length := by
  have hp := stepChain_trace_prefix rp hs req tr lc
  have h := hp.length_le
  simpa using h

/-- **Bounded by the handler count.** A full run's trace never exceeds the
number of configured handlers. -/
theorem runChain_trace_length_le (rp : RetryPolicy) (fallback : ErrClass)
    (hs : List (Handler Req Resp)) (req : Req) :
    (runChain rp fallback hs req).1.length ≤ hs.length := by
  unfold runChain
  have := stepChain_length_le rp hs req [] fallback
  simpa using this

/-- **Deterministic.** The output depends only on the input — no hidden state,
no nondeterminism (`runChain` is a pure function). -/
theorem runChain_deterministic (rp : RetryPolicy) (fallback : ErrClass)
    (hs : List (Handler Req Resp)) {req₁ req₂ : Req} (h : req₁ = req₂) :
    runChain rp fallback hs req₁ = runChain rp fallback hs req₂ := by
  subst h; rfl

/-! ### Theorem (2): stops at the first success -/

/-- **Stops at the first success.** If every handler before `h` fell through
(failed retryably) and `h` succeeds, then the chain serves `h`'s response and
the trace is exactly the handlers up to and including `h` — the handlers in
`post` are never tried (they contribute nothing to trace or outcome). -/
theorem stepChain_stop_at_success (rp : RetryPolicy) (req : Req)
    (h : Handler Req Resp) (post : List (Handler Req Resp)) (resp : Resp)
    (hwin : h.run req = .ok resp) :
    ∀ (pre : List (Handler Req Resp)),
      (∀ g ∈ pre, ∃ c, g.run req = .err c ∧ rp.retryable c = true) →
      ∀ (tr : List Nat) (lc : ErrClass),
        stepChain rp (pre ++ h :: post) req tr lc
          = (tr ++ (pre ++ [h]).map Handler.hid, .byHandler h.hid resp) := by
  intro pre
  induction pre with
  | nil =>
    intro _ tr lc
    simp [stepChain, hwin]
  | cons g pre' ih =>
    intro hpre tr lc
    obtain ⟨c, hgerr, hgret⟩ := hpre g (by simp)
    have hpre' : ∀ g' ∈ pre', ∃ c, g'.run req = .err c ∧ rp.retryable c = true :=
      fun g' hg' => hpre g' (List.mem_cons_of_mem _ hg')
    have hih := ih hpre' (tr ++ [g.hid]) c
    simp only [List.cons_append, stepChain, hgerr, hgret]
    rw [hih]
    simp [List.cons_append, List.map_cons, List.append_assoc]

/-- **The first success wins (full run).** The served outcome is the winner's
response and the trace stops at the winner — no handler after it runs. -/
theorem runChain_stops_at_first_success (rp : RetryPolicy) (fallback : ErrClass)
    (req : Req) (pre : List (Handler Req Resp)) (h : Handler Req Resp)
    (post : List (Handler Req Resp)) (resp : Resp)
    (hpre : ∀ g ∈ pre, ∃ c, g.run req = .err c ∧ rp.retryable c = true)
    (hwin : h.run req = .ok resp) :
    runChain rp fallback (pre ++ h :: post) req
      = ((pre ++ [h]).map Handler.hid, .byHandler h.hid resp) := by
  unfold runChain
  rw [stepChain_stop_at_success rp req h post resp hwin pre hpre [] fallback]
  simp

/-- **Exactly the winner-prefix ran.** The number of tried handlers on a success
is the winner's index plus one — everyone up to and including the winner, no one
after. -/
theorem runChain_success_trace_length (rp : RetryPolicy) (fallback : ErrClass)
    (req : Req) (pre : List (Handler Req Resp)) (h : Handler Req Resp)
    (post : List (Handler Req Resp)) (resp : Resp)
    (hpre : ∀ g ∈ pre, ∃ c, g.run req = .err c ∧ rp.retryable c = true)
    (hwin : h.run req = .ok resp) :
    (runChain rp fallback (pre ++ h :: post) req).1.length = pre.length + 1 := by
  rw [runChain_stops_at_first_success rp fallback req pre h post resp hpre hwin]
  simp

/-! ### Theorem (3): a non-retryable class terminates immediately -/

/-- **Non-retryable terminates immediately.** If every handler before `h` fell
through and `h` fails with a terminal (non-retryable) class `c`, the chain stops
at `h` and serves the terminal page for `c` — the handlers in `post` are never
tried. -/
theorem stepChain_stop_at_nonretryable (rp : RetryPolicy) (req : Req)
    (h : Handler Req Resp) (post : List (Handler Req Resp)) (c : ErrClass)
    (hstop : h.run req = .err c) (hnr : rp.retryable c = false) :
    ∀ (pre : List (Handler Req Resp)),
      (∀ g ∈ pre, ∃ c', g.run req = .err c' ∧ rp.retryable c' = true) →
      ∀ (tr : List Nat) (lc : ErrClass),
        stepChain rp (pre ++ h :: post) req tr lc
          = (tr ++ (pre ++ [h]).map Handler.hid, .terminal c) := by
  intro pre
  induction pre with
  | nil =>
    intro _ tr lc
    simp [stepChain, hstop, hnr]
  | cons g pre' ih =>
    intro hpre tr lc
    obtain ⟨c', hgerr, hgret⟩ := hpre g (by simp)
    have hpre' : ∀ g' ∈ pre', ∃ c'', g'.run req = .err c'' ∧ rp.retryable c'' = true :=
      fun g' hg' => hpre g' (List.mem_cons_of_mem _ hg')
    have hih := ih hpre' (tr ++ [g.hid]) c'
    simp only [List.cons_append, stepChain, hgerr, hgret]
    rw [hih]
    simp [List.cons_append, List.map_cons, List.append_assoc]

/-- **A terminal class stops the chain (full run).** -/
theorem runChain_nonretryable_terminates (rp : RetryPolicy) (fallback : ErrClass)
    (req : Req) (pre : List (Handler Req Resp)) (h : Handler Req Resp)
    (post : List (Handler Req Resp)) (c : ErrClass)
    (hpre : ∀ g ∈ pre, ∃ c', g.run req = .err c' ∧ rp.retryable c' = true)
    (hstop : h.run req = .err c) (hnr : rp.retryable c = false) :
    runChain rp fallback (pre ++ h :: post) req
      = ((pre ++ [h]).map Handler.hid, .terminal c) := by
  unfold runChain
  rw [stepChain_stop_at_nonretryable rp req h post c hstop hnr pre hpre [] fallback]
  simp

/-! ### Completeness of the case split: exhaustion -/

/-- **Exhaustion.** If every handler fails retryably, the terminal page is served
(for some class) and every handler was tried — the trace is the full configured
id list. Together with theorems (2) and (3) this covers all outcomes: a run
either wins at some handler, stops at a terminal class, or exhausts, and in every
case exactly one thing is served (theorem (1)). -/
theorem stepChain_exhaust (rp : RetryPolicy) (req : Req) :
    ∀ (hs : List (Handler Req Resp)),
      (∀ g ∈ hs, ∃ c, g.run req = .err c ∧ rp.retryable c = true) →
      ∀ (tr : List Nat) (lc : ErrClass),
        ∃ c, stepChain rp hs req tr lc = (tr ++ hs.map Handler.hid, .terminal c) := by
  intro hs
  induction hs with
  | nil =>
    intro _ tr lc
    exact ⟨lc, by simp [stepChain]⟩
  | cons g rest ih =>
    intro hall tr lc
    obtain ⟨c, hgerr, hgret⟩ := hall g (by simp)
    have hall' : ∀ g' ∈ rest, ∃ c', g'.run req = .err c' ∧ rp.retryable c' = true :=
      fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')
    obtain ⟨cf, hcf⟩ := ih hall' (tr ++ [g.hid]) c
    refine ⟨cf, ?_⟩
    simp only [stepChain, hgerr, hgret]
    rw [hcf]
    simp [List.map_cons, List.append_assoc]

/-! ### Worked examples (concrete, computed) -/

namespace Example

def hTimeout : Handler Unit String := { hid := 1, run := fun _ => .err .timeout }
def hConnect : Handler Unit String := { hid := 2, run := fun _ => .err .connectFailed }
def hOk : Handler Unit String := { hid := 3, run := fun _ => .ok "served-by-3" }
def hForbidden : Handler Unit String := { hid := 4, run := fun _ => .err .forbidden }

/-- First two fail retryably, the third wins: served by handler 3, trace `[1,2,3]`
(every earlier handler was tried in order, none after the winner). -/
example :
    runChain defaultPolicy .notFound [hTimeout, hConnect, hOk] ()
      = ([1, 2, 3], .byHandler 3 "served-by-3") := rfl

/-- A terminal (`forbidden`) class stops the chain immediately: handler 3 is
never tried, and the terminal page renders `forbidden`. -/
example :
    runChain defaultPolicy .notFound [hForbidden, hOk] ()
      = ([4], .terminal .forbidden) := rfl

/-- An empty chain serves the configured fallback terminal page, tried nothing. -/
example :
    runChain defaultPolicy .notFound ([] : List (Handler Unit String)) ()
      = ([], .terminal .notFound) := rfl

/-- Every handler falls through: the terminal page renders the last class seen
(`connectFailed` from handler 2), and every handler was tried. -/
example :
    runChain defaultPolicy .notFound [hTimeout, hConnect] ()
      = ([1, 2], .terminal .connectFailed) := rfl

end Example

end Fallback.Chain
