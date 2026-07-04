/-
Breaker — the circuit-breaker FSM guarding an upstream.

A breaker sits in front of an upstream and admits or short-circuits outbound
attempts. It has three phases:

    closed    — normal operation; attempts pass through. Consecutive failures
                are counted; reaching `threshold` trips the breaker open.
    open      — the upstream is presumed dead; every attempt is rejected. After
                `cooldown` has elapsed (measured on the time input), the breaker
                moves to half-open.
    halfOpen  — a single trial probe is admitted. Its success closes the
                breaker; its failure re-opens it. While that one probe is in
                flight, further attempts are rejected.

Time is an explicit input (the `Flow.Deadline` convention, restated here, not
imported): the cooldown elapses via `BEvent.tick now`, comparing `now` against
the instant the breaker opened. Admission requests (`BEvent.probe`) and attempt
results (`BEvent.success` / `BEvent.failure`) are the other inputs. A step
emits at most one output — `attempt` (an upstream attempt is admitted) or
`reject` (short-circuited).

Theorems:

  * `step_deterministic` / `output_le_one` / `phase_trichotomy` —
    **totality & determinism**: `step` is a total function (defined on every
    (phase, event) pair, always landing in one of the three phases) and hence
    deterministic; every step emits at most one output;
  * `open_no_attempt` — **the breaker actually breaks**: while open, NO event
    admits an upstream attempt;
  * `open_before_cooldown_stays` / `open_at_cooldown` — exact cooldown
    semantics: an open breaker stays open until `cooldown` has elapsed, then a
    tick moves it to half-open;
  * `halfOpen_probe_admits` / `halfOpen_inflight_rejects` — **half-open admits
    at most one probe at a time**: the first probe is admitted and marks a
    probe in flight; while one is in flight, probes are rejected;
  * `halfOpen_failure_reopens` — **no oscillation**: a single failure in
    half-open returns to open (it does not require re-crossing the failure
    threshold);
  * `halfOpen_success_closes` — a single success in half-open closes the
    breaker;
  * `closed_below_threshold` / `closed_trips_at_threshold` — exact trip
    semantics on the closed side.
-/

namespace Proxy.Breaker

/-- Breaker configuration. `threshold` consecutive failures trip a closed
breaker open; `cooldown` is how long an open breaker waits before admitting a
half-open probe. -/
structure BreakerCfg where
  threshold : Nat
  cooldown : Nat
deriving DecidableEq, Repr

/-- The breaker phase. -/
inductive BPhase where
  | closed
  | open
  | halfOpen
deriving DecidableEq, Repr, Inhabited

/-- Breaker inputs. `tick` advances the clock (and can move open → half-open);
`probe` is a request asking to reach upstream; `success` / `failure` report the
result of an admitted attempt. -/
inductive BEvent where
  | tick (now : Nat)
  | probe
  | success
  | failure
deriving DecidableEq, Repr

/-- Breaker outputs. `attempt` = an upstream attempt is admitted onto the wire;
`reject` = the request is short-circuited. -/
inductive BOutput where
  | attempt
  | reject
deriving DecidableEq, Repr

/-- Breaker state. `failures` is the consecutive-failure counter (closed);
`openedAt` is the clock instant the breaker last opened (cooldown origin);
`probeInFlight` marks that a half-open probe has been admitted and not yet
resolved; `clock` is the last observed (monotone) clock. -/
structure BState where
  phase : BPhase
  failures : Nat
  openedAt : Nat
  probeInFlight : Bool
  clock : Nat
deriving DecidableEq, Repr

/-- A fresh, closed breaker. -/
def BState.init : BState :=
  { phase := .closed, failures := 0, openedAt := 0, probeInFlight := false,
    clock := 0 }

/-- One step. `tick` clamps the clock forward and, if open past cooldown,
moves to half-open (fresh, no probe in flight). `probe` admits in closed and in
half-open (only when no probe is in flight, marking one), and rejects
otherwise. `failure` counts up in closed (tripping open at threshold) and
immediately re-opens half-open; `success` resets the closed counter and closes
a half-open probe. Events that do not apply to the current phase stutter. -/
def step (cfg : BreakerCfg) (s : BState) : BEvent → BState × List BOutput
  | .tick now =>
    let clk := max s.clock now
    match s.phase with
    | .open =>
      if cfg.cooldown ≤ now - s.openedAt then
        ({ s with phase := .halfOpen, probeInFlight := false, clock := clk }, [])
      else
        ({ s with clock := clk }, [])
    | _ => ({ s with clock := clk }, [])
  | .probe =>
    match s.phase with
    | .closed => (s, [BOutput.attempt])
    | .open => (s, [BOutput.reject])
    | .halfOpen =>
      if s.probeInFlight then (s, [BOutput.reject])
      else ({ s with probeInFlight := true }, [BOutput.attempt])
  | .success =>
    match s.phase with
    | .closed => ({ s with failures := 0 }, [])
    | .open => (s, [])
    | .halfOpen =>
      ({ s with phase := .closed, failures := 0, probeInFlight := false }, [])
  | .failure =>
    match s.phase with
    | .closed =>
      if cfg.threshold ≤ s.failures + 1 then
        ({ s with phase := .open, failures := 0, openedAt := s.clock }, [])
      else
        ({ s with failures := s.failures + 1 }, [])
    | .open => (s, [])
    | .halfOpen =>
      ({ s with phase := .open, probeInFlight := false, openedAt := s.clock }, [])

/-- Run a trace of events, oldest first. -/
def run (cfg : BreakerCfg) (s : BState) : List BEvent → BState
  | [] => s
  | e :: es => run cfg (step cfg s e).1 es

@[simp] theorem run_nil (cfg : BreakerCfg) (s : BState) : run cfg s [] = s := rfl

@[simp] theorem run_cons (cfg : BreakerCfg) (s : BState) (e : BEvent)
    (es : List BEvent) : run cfg s (e :: es) = run cfg (step cfg s e).1 es := rfl

/-! ### Totality and determinism -/

/-- **Determinism.** `step` is a function, so identical inputs give identical
results: the transition relation `r = step cfg s e` is deterministic. -/
theorem step_deterministic {cfg : BreakerCfg} {s : BState} {e : BEvent}
    {r₁ r₂ : BState × List BOutput}
    (h₁ : r₁ = step cfg s e) (h₂ : r₂ = step cfg s e) : r₁ = r₂ := by
  rw [h₁, h₂]

/-- **Totality (phase).** `step` is total: from any state and event it lands in
one of the three phases (no stuck states, no undefined transitions). -/
theorem phase_trichotomy (cfg : BreakerCfg) (s : BState) (e : BEvent) :
    (step cfg s e).1.phase = .closed
      ∨ (step cfg s e).1.phase = .open
      ∨ (step cfg s e).1.phase = .halfOpen := by
  cases (step cfg s e).1.phase
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **Bounded output.** Every step emits at most one output. -/
theorem output_le_one (cfg : BreakerCfg) (s : BState) (e : BEvent) :
    (step cfg s e).2.length ≤ 1 := by
  cases e <;> simp only [step] <;>
    (try split) <;> (try split) <;> simp

/-! ### The breaker actually breaks: open admits nothing -/

/-- **While open, no upstream attempt is admitted** — under any event. A probe
is rejected, a tick either stays open or moves to half-open (emitting nothing),
and stray results stutter. The breaker genuinely breaks the circuit. -/
theorem open_no_attempt (cfg : BreakerCfg) (s : BState) (e : BEvent)
    (h : s.phase = .open) : BOutput.attempt ∉ (step cfg s e).2 := by
  cases e <;> simp only [step, h] <;> (try split) <;> simp

/-- **Cooldown lower bound.** Before `cooldown` has elapsed since it opened, a
tick leaves the breaker open. -/
theorem open_before_cooldown_stays (cfg : BreakerCfg) (s : BState) (now : Nat)
    (h : s.phase = .open) (hlt : now - s.openedAt < cfg.cooldown) :
    (step cfg s (.tick now)).1.phase = .open := by
  simp only [step, h]
  rw [if_neg (by omega)]

/-- **Cooldown upper bound.** Once `cooldown` has elapsed since it opened, a
tick moves the breaker to half-open with no probe in flight. -/
theorem open_at_cooldown (cfg : BreakerCfg) (s : BState) (now : Nat)
    (h : s.phase = .open) (hge : cfg.cooldown ≤ now - s.openedAt) :
    (step cfg s (.tick now)).1.phase = .halfOpen
      ∧ (step cfg s (.tick now)).1.probeInFlight = false := by
  simp only [step, h]
  rw [if_pos hge]
  exact ⟨rfl, rfl⟩

/-! ### Half-open admits at most one probe at a time -/

/-- **First half-open probe is admitted** and marks a probe in flight. -/
theorem halfOpen_probe_admits (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .halfOpen) (hp : s.probeInFlight = false) :
    (step cfg s .probe).2 = [BOutput.attempt]
      ∧ (step cfg s .probe).1.probeInFlight = true := by
  refine ⟨?_, ?_⟩ <;> simp [step, h, hp]

/-- **At most one probe.** While a half-open probe is in flight, a further
probe is rejected — no second concurrent attempt is admitted. -/
theorem halfOpen_inflight_rejects (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .halfOpen) (hp : s.probeInFlight = true) :
    (step cfg s .probe).2 = [BOutput.reject] := by
  simp only [step, h, hp, if_pos]

/-- Consequently, a half-open probe-in-flight admits no attempt at all. -/
theorem halfOpen_inflight_no_attempt (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .halfOpen) (hp : s.probeInFlight = true) :
    BOutput.attempt ∉ (step cfg s .probe).2 := by
  rw [halfOpen_inflight_rejects cfg s h hp]; simp

/-! ### Half-open resolves without oscillation -/

/-- **No oscillation.** A single failure in half-open returns the breaker to
open — it does NOT require re-accumulating the failure threshold — and restarts
the cooldown. -/
theorem halfOpen_failure_reopens (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .halfOpen) :
    (step cfg s .failure).1.phase = .open
      ∧ (step cfg s .failure).1.probeInFlight = false
      ∧ (step cfg s .failure).1.openedAt = s.clock := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [step, h]

/-- A single success in half-open closes the breaker (clean counters). -/
theorem halfOpen_success_closes (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .halfOpen) :
    (step cfg s .success).1.phase = .closed
      ∧ (step cfg s .success).1.failures = 0
      ∧ (step cfg s .success).1.probeInFlight = false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [step, h]

/-! ### Exact trip semantics on the closed side -/

/-- Below the threshold, a failure only increments the counter — the breaker
stays closed. -/
theorem closed_below_threshold (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .closed) (hlt : ¬ cfg.threshold ≤ s.failures + 1) :
    (step cfg s .failure).1.phase = .closed
      ∧ (step cfg s .failure).1.failures = s.failures + 1 := by
  simp only [step, h]
  rw [if_neg hlt]
  exact ⟨rfl, rfl⟩

/-- At the threshold, a failure trips the breaker open (resetting the counter
and stamping the open instant). -/
theorem closed_trips_at_threshold (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .closed) (hge : cfg.threshold ≤ s.failures + 1) :
    (step cfg s .failure).1.phase = .open
      ∧ (step cfg s .failure).1.openedAt = s.clock := by
  simp only [step, h]
  rw [if_pos hge]
  exact ⟨rfl, rfl⟩

/-- A success in closed clears the consecutive-failure streak. -/
theorem closed_success_resets (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .closed) : (step cfg s .success).1.failures = 0 := by
  simp only [step, h]

/-- In closed, a probe is admitted. -/
theorem closed_probe_admits (cfg : BreakerCfg) (s : BState)
    (h : s.phase = .closed) : (step cfg s .probe).2 = [BOutput.attempt] := by
  simp only [step, h]

/-! ### Executable checks -/

/-- threshold 3: two failures keep it closed, the third trips it open. -/
example :
    (run ⟨3, 5⟩ BState.init [.failure, .failure]).phase = .closed := by decide

example :
    (run ⟨3, 5⟩ BState.init [.failure, .failure, .failure]).phase = .open := by
  decide

/-- A success in closed clears the streak, so a later burst restarts counting:
fail, fail, success, fail, fail — never three consecutive — still closed. -/
example :
    (run ⟨3, 5⟩ BState.init
      [.failure, .failure, .success, .failure, .failure]).phase = .closed := by
  decide

/-- Open until cooldown: opened at clock 0, cooldown 5. A tick at 4 stays open;
a tick at 5 moves to half-open. -/
example :
    (step ⟨3, 5⟩ ⟨.open, 0, 0, false, 0⟩ (.tick 4)).1.phase = .open := by decide

example :
    (step ⟨3, 5⟩ ⟨.open, 0, 0, false, 0⟩ (.tick 5)).1.phase = .halfOpen := by
  decide

/-- Half-open: first probe admitted, second rejected while in flight. -/
example :
    (step ⟨3, 5⟩ ⟨.halfOpen, 0, 0, false, 0⟩ .probe).2 = [BOutput.attempt] := by
  decide

example :
    (step ⟨3, 5⟩ ⟨.halfOpen, 0, 0, true, 0⟩ .probe).2 = [BOutput.reject] := by
  decide

/-- Half-open failure re-opens on a single failure. -/
example :
    (step ⟨3, 5⟩ ⟨.halfOpen, 0, 0, true, 9⟩ .failure).1.phase = .open := by
  decide

end Proxy.Breaker
