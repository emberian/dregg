/-
Connect — the upstream-connect machine.

One outbound connection establishment, end to end:

    resolving ──resolved──▶ connecting(target, deadline)
    connecting ──connected──▶ established(target)          (terminal)
    connecting ──refused | deadline──▶ backingOff           (if budget left)
                                    └─▶ exhausted           (terminal)
    backingOff ──timer──▶ connecting(next target, deadline) (fresh attempt)
                       └─▶ exhausted                        (budget spent)

The machine is sans-IO: the environment injects events (`resolved`,
`connected`, `refused`, `deadline` for the connect timeout firing, `timer`
for the backoff timer firing); the machine is a pure step function. Events
that make no sense in the current phase stutter (state unchanged) — a late
timer against an established connection is dropped, not acted on.

Each attempt re-selects its target through `pick : Nat → Option Nat`
(attempt index → backend id) — the hook through which the balancer
(`Proxy.Balance.select`, with the attempt index in `Ctx.round`) drives
retries across backends. The backoff delay doubles on every failure
(`delay_monotone`); the deadline carried by `connecting` is the configured
connect timeout, whose expiry the environment reports as `.deadline`.

Theorems:

  * `used_le_budget` / `attempt_consumes` — **retry budget respected**: the
    attempt counter is monotone, never exceeds the budget, and every entry
    into `connecting` consumes exactly one unit;
  * `established_absorbing` — **no retry after established**: `established`
    ignores every event, so no further attempt, backoff, or re-resolve can
    ever be caused by a machine that has already connected (dually
    `exhausted_absorbing`);
  * `progress_measure_decreases` + `drive_terminal` — **bounded
    termination**: a natural measure strictly decreases on every
    non-stuttering step, so under any live environment the machine reaches a
    terminal state within `3·budget + 2` productive steps — `connect_fuel`
    turns that into fuel-based totality with the concrete adversarial driver
    `kick` (every attempt times out);
  * `exhausted_spends_budget` — with a total selector (the balancer has an
    eligible backend), `exhausted` is reachable only by spending the entire
    budget: the machine never gives up early.
-/

import Proxy.Basic

namespace Proxy

/-- Connect configuration: attempt budget and per-attempt connect timeout. -/
structure ConnectCfg where
  /-- Maximum number of connect attempts (≥ 1 in sane configs). -/
  budget : Nat
  /-- Connect deadline carried into each `connecting` phase. -/
  timeout : Nat
deriving DecidableEq, Repr

/-- The phase of the connect machine. -/
inductive ConnPhase where
  /-- Waiting for upstream name resolution. -/
  | resolving
  /-- One attempt in flight against backend `target`, with a deadline. -/
  | connecting (target : Nat) (deadline : Nat)
  /-- Attempt failed; waiting out the backoff delay. -/
  | backingOff
  /-- Terminal success. -/
  | established (target : Nat)
  /-- Terminal failure: retry budget spent (or no backend selectable). -/
  | exhausted
deriving DecidableEq, Repr

/-- Machine state: phase + attempts used + current backoff delay. -/
structure ConnState where
  phase : ConnPhase
  used : Nat
  delay : Nat
deriving DecidableEq, Repr

/-- Fresh machine (delay starts at the configured base). -/
def ConnState.init (baseDelay : Nat) : ConnState :=
  ⟨.resolving, 0, baseDelay⟩

/-- Environment events. `refused` and `deadline` are the two attempt-failure
causes (immediate refusal vs. connect-timeout expiry); `timer` is the backoff
timer firing. -/
inductive ConnEvent where
  | resolved
  | connected
  | refused
  | deadline
  | timer
deriving DecidableEq, Repr

/-- Begin the next attempt: consult the budget, then the balancer. A `none`
from the selector (no eligible backend at all) short-circuits to
`exhausted`. -/
def beginAttempt (cfg : ConnectCfg) (pick : Nat → Option Nat)
    (s : ConnState) : ConnState :=
  if s.used < cfg.budget then
    match pick s.used with
    | some t => ⟨.connecting t cfg.timeout, s.used + 1, s.delay⟩
    | none => ⟨.exhausted, s.used, s.delay⟩
  else ⟨.exhausted, s.used, s.delay⟩

/-- An attempt failed: back off (doubling the delay) if budget remains,
otherwise give up. -/
def failAttempt (cfg : ConnectCfg) (s : ConnState) : ConnState :=
  if s.used < cfg.budget then ⟨.backingOff, s.used, s.delay * 2⟩
  else ⟨.exhausted, s.used, s.delay⟩

/-- The step function. Unmatched (phase, event) pairs stutter. -/
def cstep (cfg : ConnectCfg) (pick : Nat → Option Nat) (s : ConnState)
    (e : ConnEvent) : ConnState :=
  match s.phase, e with
  | .resolving, .resolved => beginAttempt cfg pick s
  | .connecting t _, .connected => ⟨.established t, s.used, s.delay⟩
  | .connecting _ _, .refused => failAttempt cfg s
  | .connecting _ _, .deadline => failAttempt cfg s
  | .backingOff, .timer => beginAttempt cfg pick s
  | _, _ => s

/-- Terminal phases: connected or given up. -/
def terminal (s : ConnState) : Bool :=
  match s.phase with
  | .established _ => true
  | .exhausted => true
  | _ => false

/-! ### The two transition helpers, characterized once -/

theorem beginAttempt_used_le {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} :
    s.used ≤ (beginAttempt cfg pick s).used
      ∧ (s.used ≤ cfg.budget → (beginAttempt cfg pick s).used ≤ cfg.budget)
      ∧ s.delay ≤ (beginAttempt cfg pick s).delay := by
  by_cases hb : s.used < cfg.budget
  · cases hp : pick s.used with
    | some t => simp [beginAttempt, hb, hp]; omega
    | none => simp [beginAttempt, hb, hp]
  · simp [beginAttempt, hb]

theorem failAttempt_used_le {cfg : ConnectCfg} {s : ConnState} :
    s.used ≤ (failAttempt cfg s).used
      ∧ (s.used ≤ cfg.budget → (failAttempt cfg s).used ≤ cfg.budget)
      ∧ s.delay ≤ (failAttempt cfg s).delay := by
  by_cases hb : s.used < cfg.budget
  · simp [failAttempt, hb]; omega
  · simp [failAttempt, hb]

/-- Entering `connecting` through `beginAttempt` consumes exactly one unit of
budget and requires budget headroom. -/
theorem beginAttempt_consumes {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} {t d : Nat}
    (h : (beginAttempt cfg pick s).phase = .connecting t d) :
    (beginAttempt cfg pick s).used = s.used + 1 ∧ s.used < cfg.budget := by
  by_cases hb : s.used < cfg.budget
  · cases hp : pick s.used with
    | some t' =>
      have heq : beginAttempt cfg pick s
          = ⟨.connecting t' cfg.timeout, s.used + 1, s.delay⟩ := by
        simp [beginAttempt, hb, hp]
      rw [heq]
      exact ⟨rfl, hb⟩
    | none =>
      have heq : beginAttempt cfg pick s = ⟨.exhausted, s.used, s.delay⟩ := by
        simp [beginAttempt, hb, hp]
      rw [heq] at h
      cases h
  · have heq : beginAttempt cfg pick s = ⟨.exhausted, s.used, s.delay⟩ := by
      simp [beginAttempt, hb]
    rw [heq] at h
    cases h

/-- `beginAttempt` lands in `exhausted` only with the budget spent — provided
the selector answers (`hpick`). -/
theorem beginAttempt_exhausted {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} (hpick : (pick s.used).isSome)
    (hused : s.used ≤ cfg.budget)
    (h : (beginAttempt cfg pick s).phase = .exhausted) :
    (beginAttempt cfg pick s).used = cfg.budget := by
  by_cases hb : s.used < cfg.budget
  · cases hp : pick s.used with
    | some t' =>
      have heq : beginAttempt cfg pick s
          = ⟨.connecting t' cfg.timeout, s.used + 1, s.delay⟩ := by
        simp [beginAttempt, hb, hp]
      rw [heq] at h
      cases h
    | none =>
      rw [hp] at hpick
      cases hpick
  · have heq : beginAttempt cfg pick s = ⟨.exhausted, s.used, s.delay⟩ := by
      simp [beginAttempt, hb]
    rw [heq]
    show s.used = cfg.budget
    omega

/-- `failAttempt` lands in `exhausted` only with the budget spent. -/
theorem failAttempt_exhausted {cfg : ConnectCfg} {s : ConnState}
    (hused : s.used ≤ cfg.budget)
    (h : (failAttempt cfg s).phase = .exhausted) :
    (failAttempt cfg s).used = cfg.budget := by
  by_cases hb : s.used < cfg.budget
  · have heq : failAttempt cfg s = ⟨.backingOff, s.used, s.delay * 2⟩ := by
      simp [failAttempt, hb]
    rw [heq] at h
    cases h
  · have heq : failAttempt cfg s = ⟨.exhausted, s.used, s.delay⟩ := by
      simp [failAttempt, hb]
    rw [heq]
    show s.used = cfg.budget
    omega

/-! ### Retry budget -/

/-- The attempt counter never moves backwards. -/
theorem used_monotone (cfg : ConnectCfg) (pick : Nat → Option Nat)
    (s : ConnState) (e : ConnEvent) : s.used ≤ (cstep cfg pick s e).used := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> cases e <;>
    first
      | exact Nat.le_refl _
      | exact beginAttempt_used_le.1
      | exact failAttempt_used_le.1

/-- **Retry budget respected.** `used ≤ budget` is inductive: no step ever
pushes the attempt counter past the budget. -/
theorem used_le_budget {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} (hs : s.used ≤ cfg.budget) (e : ConnEvent) :
    (cstep cfg pick s e).used ≤ cfg.budget := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> cases e <;>
    first
      | exact hs
      | exact beginAttempt_used_le.2.1 hs
      | exact failAttempt_used_le.2.1 hs

/-- The backoff delay never shrinks (it doubles on each failure and is
otherwise carried unchanged). -/
theorem delay_monotone (cfg : ConnectCfg) (pick : Nat → Option Nat)
    (s : ConnState) (e : ConnEvent) :
    s.delay ≤ (cstep cfg pick s e).delay := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> cases e <;>
    first
      | exact Nat.le_refl _
      | exact beginAttempt_used_le.2.2
      | exact failAttempt_used_le.2.2

/-- Every entry into `connecting` from outside consumes exactly one unit of
budget, and only happens while budget remains. -/
theorem attempt_consumes {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} {e : ConnEvent} {t d : Nat}
    (hpre : ∀ t' d', s.phase ≠ .connecting t' d')
    (hpost : (cstep cfg pick s e).phase = .connecting t d) :
    (cstep cfg pick s e).used = s.used + 1 ∧ s.used < cfg.budget := by
  obtain ⟨ph, u, dl⟩ := s
  cases ph <;> cases e <;>
    first
      | exact absurd rfl (hpre _ _)
      | exact beginAttempt_consumes hpost
      | cases hpost

/-! ### Absorption: no retry after established -/

/-- **No retry after established.** Every event stutters: an established
connection can never be re-dialed, re-resolved, or backed off by this
machine. -/
theorem established_absorbing {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} {t : Nat} (h : s.phase = .established t) (e : ConnEvent) :
    cstep cfg pick s e = s := by
  obtain ⟨ph, u, d⟩ := s
  simp at h
  subst h
  cases e <;> rfl

/-- `exhausted` is likewise absorbing: a machine that gave up stays given up
(the caller starts a NEW machine for a new request, with a fresh budget). -/
theorem exhausted_absorbing {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} (h : s.phase = .exhausted) (e : ConnEvent) :
    cstep cfg pick s e = s := by
  obtain ⟨ph, u, d⟩ := s
  simp at h
  subst h
  cases e <;> rfl

/-! ### Bounded termination -/

/-- Termination measure: three units per remaining attempt, plus a phase
cost ordering the intra-attempt progress `backingOff/resolving (1) →
connecting (2, after spending a unit) → terminal (0)`. -/
def phaseCost : ConnPhase → Nat
  | .resolving => 1
  | .connecting _ _ => 2
  | .backingOff => 1
  | .established _ => 0
  | .exhausted => 0

def cmeasure (cfg : ConnectCfg) (s : ConnState) : Nat :=
  (cfg.budget - s.used) * 3 + phaseCost s.phase

/-- Non-terminal states have positive measure. -/
theorem cmeasure_pos {cfg : ConnectCfg} {s : ConnState}
    (h : terminal s = false) : 0 < cmeasure cfg s := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> simp_all [terminal, cmeasure, phaseCost]

/-- The measure is bounded by the budget: `3·budget + 2` fuel always
suffices. -/
theorem cmeasure_le (cfg : ConnectCfg) (s : ConnState) :
    cmeasure cfg s ≤ 3 * cfg.budget + 2 := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> simp [cmeasure, phaseCost] <;> omega

/-- The measure strictly drops across `beginAttempt` from a cost-1 phase… -/
theorem beginAttempt_decreases {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {ph : ConnPhase} {u d : Nat} (hc : phaseCost ph = 1) :
    cmeasure cfg (beginAttempt cfg pick ⟨ph, u, d⟩)
      < cmeasure cfg ⟨ph, u, d⟩ := by
  by_cases hb : u < cfg.budget
  · cases hp : pick u with
    | some t =>
      have heq : beginAttempt cfg pick ⟨ph, u, d⟩
          = ⟨.connecting t cfg.timeout, u + 1, d⟩ := by
        simp [beginAttempt, hb, hp]
      rw [heq]
      show (cfg.budget - (u + 1)) * 3 + 2 < (cfg.budget - u) * 3 + phaseCost ph
      omega
    | none =>
      have heq : beginAttempt cfg pick ⟨ph, u, d⟩ = ⟨.exhausted, u, d⟩ := by
        simp [beginAttempt, hb, hp]
      rw [heq]
      show (cfg.budget - u) * 3 + 0 < (cfg.budget - u) * 3 + phaseCost ph
      omega
  · have heq : beginAttempt cfg pick ⟨ph, u, d⟩ = ⟨.exhausted, u, d⟩ := by
      simp [beginAttempt, hb]
    rw [heq]
    show (cfg.budget - u) * 3 + 0 < (cfg.budget - u) * 3 + phaseCost ph
    omega

/-- …and across `failAttempt` from the cost-2 `connecting` phase. -/
theorem failAttempt_decreases {cfg : ConnectCfg} {ph : ConnPhase} {u d : Nat}
    (hc : phaseCost ph = 2) :
    cmeasure cfg (failAttempt cfg ⟨ph, u, d⟩) < cmeasure cfg ⟨ph, u, d⟩ := by
  by_cases hb : u < cfg.budget
  · have heq : failAttempt cfg ⟨ph, u, d⟩ = ⟨.backingOff, u, d * 2⟩ := by
      simp [failAttempt, hb]
    rw [heq]
    show (cfg.budget - u) * 3 + 1 < (cfg.budget - u) * 3 + phaseCost ph
    omega
  · have heq : failAttempt cfg ⟨ph, u, d⟩ = ⟨.exhausted, u, d⟩ := by
      simp [failAttempt, hb]
    rw [heq]
    show (cfg.budget - u) * 3 + 0 < (cfg.budget - u) * 3 + phaseCost ph
    omega

/-- **Every productive step strictly decreases the measure.** Stuttering
steps are exactly the identity steps, so along any event sequence the
machine performs at most `cmeasure` productive transitions before sitting in
a terminal state (or stuttering forever waiting for its environment). -/
theorem progress_measure_decreases {cfg : ConnectCfg}
    {pick : Nat → Option Nat} {s : ConnState} {e : ConnEvent}
    (hprod : cstep cfg pick s e ≠ s) :
    cmeasure cfg (cstep cfg pick s e) < cmeasure cfg s := by
  obtain ⟨ph, u, d⟩ := s
  cases ph <;> cases e <;> (try exact absurd rfl hprod)
  case resolving.resolved => exact beginAttempt_decreases rfl
  case backingOff.timer => exact beginAttempt_decreases rfl
  case connecting.connected =>
    show (cfg.budget - u) * 3 + 0 < (cfg.budget - u) * 3 + 2
    omega
  case connecting.refused => exact failAttempt_decreases rfl
  case connecting.deadline => exact failAttempt_decreases rfl

/-- A fuel-indexed driver: ask the environment `next` for the next event,
step, stop at terminal states. -/
def drive (cfg : ConnectCfg) (pick : Nat → Option Nat)
    (next : ConnState → ConnEvent) : Nat → ConnState → ConnState
  | 0, s => s
  | fuel + 1, s =>
    if terminal s then s
    else drive cfg pick next fuel (cstep cfg pick s (next s))

/-- **Fuel-based totality.** Against any *live* environment (one whose next
event always moves the machine — no stutter-stalling), fuel `≥ cmeasure`
suffices to reach a terminal state: `established` or `exhausted`, no third
option, no unbounded retry. -/
theorem drive_terminal {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {next : ConnState → ConnEvent}
    (hlive : ∀ s, terminal s = false → cstep cfg pick s (next s) ≠ s)
    {fuel : Nat} :
    ∀ {s : ConnState}, cmeasure cfg s ≤ fuel →
      terminal (drive cfg pick next fuel s) = true := by
  induction fuel with
  | zero =>
    intro s hfuel
    cases ht : terminal s with
    | true => simp [drive, ht]
    | false =>
      have := cmeasure_pos (cfg := cfg) ht
      omega
  | succ fuel ih =>
    intro s hfuel
    cases ht : terminal s with
    | true => simp [drive, ht]
    | false =>
      have hdec := progress_measure_decreases (hlive s ht)
      simp only [drive, ht]
      rw [if_neg (by simp)]
      exact ih (by omega)

/-- The adversarial-but-live driver: resolution always answers, every
attempt times out at its deadline, every backoff timer fires. (The
worst-case environment for the retry budget.) -/
def kick (s : ConnState) : ConnEvent :=
  match s.phase with
  | .resolving => .resolved
  | .connecting _ _ => .deadline
  | .backingOff => .timer
  | _ => .connected

theorem kick_live (cfg : ConnectCfg) (pick : Nat → Option Nat) :
    ∀ s, terminal s = false → cstep cfg pick s (kick s) ≠ s := by
  intro s ht heq
  obtain ⟨ph, u, d⟩ := s
  have hphase := congrArg ConnState.phase heq
  cases ph with
  | established t => simp [terminal] at ht
  | exhausted => simp [terminal] at ht
  | resolving =>
    by_cases hb : u < cfg.budget
    · cases hp : pick u with
      | some t => simp [cstep, kick, beginAttempt, hb, hp] at hphase
      | none => simp [cstep, kick, beginAttempt, hb, hp] at hphase
    · simp [cstep, kick, beginAttempt, hb] at hphase
  | backingOff =>
    by_cases hb : u < cfg.budget
    · cases hp : pick u with
      | some t => simp [cstep, kick, beginAttempt, hb, hp] at hphase
      | none => simp [cstep, kick, beginAttempt, hb, hp] at hphase
    · simp [cstep, kick, beginAttempt, hb] at hphase
  | connecting t dl =>
    by_cases hb : u < cfg.budget
    · simp [cstep, kick, failAttempt, hb] at hphase
    · simp [cstep, kick, failAttempt, hb] at hphase

/-- **Concrete bounded termination.** Under the worst-case live environment,
`3·budget + 2` steps of fuel always land the machine in a terminal state. -/
theorem connect_fuel (cfg : ConnectCfg) (pick : Nat → Option Nat)
    (s : ConnState) :
    terminal (drive cfg pick kick (3 * cfg.budget + 2) s) = true :=
  drive_terminal (kick_live cfg pick) (cmeasure_le cfg s)

/-! ### Exhaustion accounting -/

/-- The exhaustion invariant, inductive-step form: with a total selector
(the balancer always has an eligible backend —
`Proxy.Balance.select_*_total`), a machine that steps into `exhausted` got
there by spending its whole budget. The machine never gives up early. -/
theorem exhausted_spends_budget {cfg : ConnectCfg} {pick : Nat → Option Nat}
    {s : ConnState} {e : ConnEvent}
    (hpick : ∀ k, (pick k).isSome)
    (hused : s.used ≤ cfg.budget)
    (hinv : s.phase = .exhausted → s.used = cfg.budget) :
    (cstep cfg pick s e).phase = .exhausted →
      (cstep cfg pick s e).used = cfg.budget := by
  intro hpost
  obtain ⟨ph, u, dl⟩ := s
  cases ph <;> cases e <;>
    first
      | exact hinv hpost
      | exact beginAttempt_exhausted (hpick _) hused hpost
      | exact failAttempt_exhausted hused hpost
      | cases hpost

end Proxy
