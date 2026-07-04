/-
Timeout — a per-request deadline decomposed into per-phase budgets.

An outbound request passes through an ordered pipeline of phases:

    resolve → connect → tls → request-write → response-first-byte → body

The per-request deadline is *decomposed* into a budget for each phase
(`Budgets`); the request deadline is their sum. Each phase is allowed to run
for at most its budget; overrunning the budget produces exactly one timeout
and stops the request.

Time is an explicit input, matching the `Flow.Deadline` convention (restated
here, not imported): a monotone clock tick arrives as an event
(`Ev.tick now` / `Ev.complete now`), a phase deadline is plain data in the
state, and phase expiry is a transition on the time input — so every theorem
quantifies over all clock behaviours. The machine clamps the observed clock to
`max`, so the clock (hence elapsed time since request start) never decreases,
no matter what the environment reports.

Accounting: `spent` is the total wall time charged to *completed* phases. The
machine keeps the invariant

    spent + Σ(budgets of the phases still to run) ≤ deadline          (`Inv`)

which is an equality at init (`init_inv`) and preserved by every step
(`step_inv`, `run_inv`). It yields the headline identity `spent ≤ deadline`
(`spent_le_deadline`): **the sum of consumed phase budgets never exceeds the
total deadline.**

Theorems:

  * `spent_le_deadline` (via `Inv`) — consumed ≤ total deadline;
  * `overrun_timeout` — a phase whose elapsed time exceeds its budget produces
    exactly one `timeout` output and moves to the terminal timed-out state;
  * `timedOut_absorbing` — the timed-out state is terminal: it emits nothing
    further and only advances its clock;
  * `within_budget_no_timeout` — a step that stays within budget emits no
    timeout;
  * `clock_monotone` / `elapsed_monotone` — the observed clock, and hence
    elapsed time since request start, never decreases across any step.
-/

namespace Proxy.Timeout

/-- The ordered phases of one outbound request. -/
inductive Phase where
  /-- Upstream name resolution. -/
  | resolve
  /-- TCP (or QUIC) connect. -/
  | connect
  /-- TLS handshake. -/
  | tls
  /-- Writing the request head + (buffered) body to the upstream. -/
  | requestWrite
  /-- Waiting for the first response byte (time-to-first-byte). -/
  | responseFirstByte
  /-- Streaming the response body. -/
  | body
deriving DecidableEq, Repr, Inhabited

/-- The per-request deadline, decomposed into one budget per phase. -/
structure Budgets where
  resolve : Nat
  connect : Nat
  tls : Nat
  requestWrite : Nat
  responseFirstByte : Nat
  body : Nat
deriving DecidableEq, Repr

/-- The budget allotted to a phase. -/
def budgetOf (b : Budgets) : Phase → Nat
  | .resolve => b.resolve
  | .connect => b.connect
  | .tls => b.tls
  | .requestWrite => b.requestWrite
  | .responseFirstByte => b.responseFirstByte
  | .body => b.body

/-- The phases in pipeline order. -/
def allPhases : List Phase :=
  [.resolve, .connect, .tls, .requestWrite, .responseFirstByte, .body]

/-- Sum of the budgets of a list of phases. -/
def sumBudgets (b : Budgets) : List Phase → Nat
  | [] => 0
  | p :: ps => budgetOf b p + sumBudgets b ps

@[simp] theorem sumBudgets_nil (b : Budgets) : sumBudgets b [] = 0 := rfl

@[simp] theorem sumBudgets_cons (b : Budgets) (p : Phase) (ps : List Phase) :
    sumBudgets b (p :: ps) = budgetOf b p + sumBudgets b ps := rfl

/-- The total per-request deadline: the sum of all phase budgets. -/
def totalDeadline (b : Budgets) : Nat := sumBudgets b allPhases

/-- Timeout outputs. A step emits `timeout p` exactly when phase `p`
overruns its budget. -/
inductive Output where
  | timeout (p : Phase)
deriving DecidableEq, Repr

/-- Machine inputs. Both carry the current clock instant `now` (time is an
explicit input); `complete` additionally reports that the active phase has
finished. -/
inductive Ev where
  /-- A clock observation at instant `now` (may fire a timeout). -/
  | tick (now : Nat)
  /-- The active phase finished at instant `now`. -/
  | complete (now : Nat)
deriving DecidableEq, Repr

/-- The instant carried by an event. -/
def Ev.now : Ev → Nat
  | .tick n => n
  | .complete n => n

/-- Machine state. `remaining` is the phases still to run, head = the active
phase; empty = the request finished all phases. `spent` is wall time charged
to completed phases; `phaseStart` is the clock instant the active phase began;
`start` is the request's start instant (fixed); `clock` is the last observed
(monotone) clock; `timedOut` marks the terminal timeout state; `deadline` is
the per-request total (fixed). -/
structure TState where
  remaining : List Phase
  spent : Nat
  phaseStart : Nat
  start : Nat
  clock : Nat
  timedOut : Bool
  deadline : Nat
deriving DecidableEq, Repr

/-- A fresh request: all phases pending, nothing spent, clock at the start
instant `0`, deadline the sum of budgets. -/
def TState.init (b : Budgets) : TState :=
  { remaining := allPhases, spent := 0, phaseStart := 0, start := 0,
    clock := 0, timedOut := false, deadline := totalDeadline b }

/-- Elapsed wall time since the request began. -/
def TState.elapsed (s : TState) : Nat := s.clock - s.start

/-- One step. Every branch clamps the clock to `max s.clock e.now` (so the
clock never goes backwards). While running, if the active phase's elapsed
time exceeds its budget the step emits one `timeout` and goes terminal;
otherwise a `complete` pops the phase (charging its elapsed time to `spent`)
and a `tick` simply keeps waiting. Terminal (timed-out or finished) states
only advance the clock. -/
def step (b : Budgets) (s : TState) (e : Ev) : TState × List Output :=
  match s.timedOut with
  | true => ({ s with clock := max s.clock e.now }, [])
  | false =>
    match s.remaining with
    | [] => ({ s with clock := max s.clock e.now }, [])
    | p :: rest =>
      if budgetOf b p < max s.clock e.now - s.phaseStart then
        ({ s with clock := max s.clock e.now, timedOut := true },
         [Output.timeout p])
      else
        match e with
        | .tick _ => ({ s with clock := max s.clock e.now }, [])
        | .complete _ =>
          ({ s with clock := max s.clock e.now,
                    phaseStart := max s.clock e.now,
                    remaining := rest,
                    spent := s.spent + (max s.clock e.now - s.phaseStart) }, [])

/-- Run a trace of events, oldest first. -/
def run (b : Budgets) (s : TState) : List Ev → TState
  | [] => s
  | e :: es => run b (step b s e).1 es

@[simp] theorem run_nil (b : Budgets) (s : TState) : run b s [] = s := rfl

@[simp] theorem run_cons (b : Budgets) (s : TState) (e : Ev) (es : List Ev) :
    run b s (e :: es) = run b (step b s e).1 es := rfl

/-! ### The clock (hence elapsed time) is monotone -/

/-- Every step advances the clock to `max s.clock e.now`; in particular the
clock never decreases. -/
theorem step_clock (b : Budgets) (s : TState) (e : Ev) :
    (step b s e).1.clock = max s.clock e.now := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- **Monotone clock.** No step ever moves the clock backwards. -/
theorem clock_monotone (b : Budgets) (s : TState) (e : Ev) :
    s.clock ≤ (step b s e).1.clock := by
  rw [step_clock]; exact Nat.le_max_left _ _

/-- `start` is fixed. -/
theorem step_start (b : Budgets) (s : TState) (e : Ev) :
    (step b s e).1.start = s.start := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- **Elapsed time never decreases.** Since the request start instant is fixed
and the clock is monotone, elapsed time since request start is monotone. -/
theorem elapsed_monotone (b : Budgets) (s : TState) (e : Ev) :
    s.elapsed ≤ (step b s e).1.elapsed := by
  simp only [TState.elapsed]
  rw [step_start]
  have := clock_monotone b s e
  omega

/-! ### The consumed-budget accounting identity -/

/-- The accounting invariant: time already spent plus the budgets of all
phases still to run never exceeds the deadline. -/
def Inv (b : Budgets) (s : TState) : Prop :=
  s.spent + sumBudgets b s.remaining ≤ s.deadline

/-- At init the invariant is an equality: nothing spent, all budgets pending,
deadline = their sum. -/
theorem init_inv (b : Budgets) : Inv b (TState.init b) := by
  simp only [Inv, TState.init, totalDeadline]
  omega

/-- The deadline is fixed across a step. -/
theorem step_deadline (b : Budgets) (s : TState) (e : Ev) :
    (step b s e).1.deadline = s.deadline := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- **Preservation.** Every step preserves the accounting invariant. -/
theorem step_inv (b : Budgets) (s : TState) (e : Ev) (h : Inv b s) :
    Inv b (step b s e).1 := by
  obtain ⟨rem, sp, ps, st, clk, to, dl⟩ := s
  cases to
  · -- not timed out
    cases rem with
    | nil => simpa [Inv, step] using h
    | cons p rest =>
      by_cases hover : budgetOf b p < max clk e.now - ps
      · -- overran: remaining and spent unchanged
        simpa [Inv, step, hover] using h
      · cases e with
        | tick n => simpa [Inv, step, hover] using h
        | complete n =>
          -- complete within budget: pop the phase, charge its elapsed time
          simp only [Inv] at h ⊢
          simp only [step]
          rw [if_neg hover]
          simp only [sumBudgets_cons] at h
          dsimp only
          omega
  · -- timed out
    simpa [Inv, step] using h

/-- Running a trace preserves the invariant. -/
theorem run_inv (b : Budgets) (s : TState) (es : List Ev) (h : Inv b s) :
    Inv b (run b s es) := by
  induction es generalizing s with
  | nil => simpa using h
  | cons e es ih => exact ih _ (step_inv b s e h)

/-- Every reachable state (from a fresh request) satisfies the invariant. -/
theorem run_init_inv (b : Budgets) (es : List Ev) :
    Inv b (run b (TState.init b) es) :=
  run_inv b _ es (init_inv b)

/-- **The sum of consumed phase budgets never exceeds the total deadline.**
Immediate from the invariant. -/
theorem spent_le_deadline (b : Budgets) (s : TState) (h : Inv b s) :
    s.spent ≤ s.deadline := by
  have : s.spent + sumBudgets b s.remaining ≤ s.deadline := h
  omega

/-- Corollary at the trace level. -/
theorem run_spent_le_deadline (b : Budgets) (es : List Ev) :
    (run b (TState.init b) es).spent ≤ (run b (TState.init b) es).deadline :=
  spent_le_deadline b _ (run_init_inv b es)

/-! ### Timeout: overrun fires exactly one output and goes terminal -/

/-- **Overrun ⇒ exactly one timeout, terminal.** A running machine whose
active phase `p` has elapsed more than its budget produces the single output
`[timeout p]` and transitions to the timed-out state. -/
theorem overrun_timeout (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (p : Phase) (rest : List Phase)
    (hrem : s.remaining = p :: rest)
    (hover : budgetOf b p < max s.clock e.now - s.phaseStart) :
    (step b s e).2 = [Output.timeout p] ∧ (step b s e).1.timedOut = true := by
  simp only [step, hrun, hrem]
  rw [if_pos hover]
  exact ⟨rfl, rfl⟩

/-- **The timed-out state is terminal.** Any event on a timed-out machine
emits nothing and leaves everything but the clock unchanged. -/
theorem timedOut_absorbing (b : Budgets) (s : TState) (e : Ev)
    (h : s.timedOut = true) :
    (step b s e).2 = [] ∧ (step b s e).1 = { s with clock := max s.clock e.now } := by
  refine ⟨?_, ?_⟩ <;> simp [step, h]

/-- Once timed-out, the machine stays timed-out. -/
theorem timedOut_stays (b : Budgets) (s : TState) (e : Ev)
    (h : s.timedOut = true) : (step b s e).1.timedOut = true := by
  simp only [step, h]

/-- **No spurious timeout.** A step whose active phase has not exceeded its
budget emits no output at all. -/
theorem within_budget_no_timeout (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (p : Phase) (rest : List Phase)
    (hrem : s.remaining = p :: rest)
    (hin : ¬ budgetOf b p < max s.clock e.now - s.phaseStart) :
    (step b s e).2 = [] := by
  simp only [step, hrun, hrem]
  rw [if_neg hin]
  cases e <;> rfl

/-- A finished machine (no phases left) also emits nothing. -/
theorem finished_no_timeout (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (hrem : s.remaining = []) :
    (step b s e).2 = [] := by
  simp only [step, hrun, hrem]

/-! ### Executable check -/

/-- A concrete decomposition: resolve 10, connect 20, tls 30, write 5,
first-byte 40, body 100 → total deadline 205. -/
example : totalDeadline ⟨10, 20, 30, 5, 40, 100⟩ = 205 := by decide

/-- The connect phase overruns (35 > 20): one timeout for `connect`, terminal.
State: connect active, phaseStart 10, clock advanced to 45. -/
example :
    let b : Budgets := ⟨10, 20, 30, 5, 40, 100⟩
    let s : TState := ⟨[.connect, .tls, .body], 10, 10, 0, 10, false, 205⟩
    (step b s (.tick 45)).2 = [Output.timeout .connect]
      ∧ (step b s (.tick 45)).1.timedOut = true := by
  decide

end Proxy.Timeout
