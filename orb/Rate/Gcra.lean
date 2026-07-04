/-
Rate.Gcra — the Generic Cell Rate Algorithm (GCRA) limiter, the dual view of
the same rate-limiting guarantee, over time-as-input.

Where the token bucket tracks a *stock* that fills over time, the GCRA tracks a
*theoretical arrival time* `tat`: the earliest clock value at which the next
request would be perfectly on-rate.  A request at clock `t` conforms — is
admitted — exactly when it is not too early, i.e. `tat ≤ t + burst`, where
`burst` (the classic limit `L`) is the tolerance that permits a bounded burst.
An admitted request pushes `tat` forward by one emission interval `t_int` (the
classic increment `I`, the reciprocal of the rate): `tat := max t tat + t_int`.
A rejected request changes nothing.

State (`Gcra`):

  * `tat`   — the theoretical arrival time (a clock value);
  * `t_int` — the emission interval: the minimum spacing between on-rate
    admissions (tokens⁻¹);
  * `burst` — the tolerance (`L`): how far ahead of schedule a request may
    arrive and still conform.

`t_int` and `burst` are parameters: no transition changes them.

Time is an input: each arrival carries its clock reading `t`.  The clock is
monotone, which the window bound takes as an explicit hypothesis on the trace
(`∀ t ∈ es, t ≤ tEnd`).

Results:

  * `gcraStep_tat_mono` (theorem 3 analog) — `tat` never runs backward.
  * `gcra_reject_unchanged` (theorem 4 analog) — a rejected request changes
    nothing (no phantom advance of `tat`).
  * `gcraRun_spacing` — the spacing lower bound: admitting `N` requests drives
    `tat` forward by at least `N * t_int`.  This is the rate limit from below:
    throughput costs schedule.
  * `gcra_rate_bound` (theorem 1 analog) — over a window ending at `tEnd`, the
    admitted count `N` satisfies `N * t_int ≤ (tEnd - tat₀) + burst + t_int`,
    i.e. `N ≤ 1 + (D + burst) / t_int` with `D = tEnd - tat₀`.  The same
    counting guarantee as the token bucket, in TAT form.
-/

namespace Rate

/-- GCRA state.  `t_int` and `burst` are parameters carried in the state. -/
structure Gcra where
  /-- Theoretical arrival time: the earliest on-rate clock value for the next
  request. -/
  tat : Nat
  /-- Emission interval: minimum spacing between on-rate admissions. -/
  t_int : Nat
  /-- Tolerance (`L`): how far ahead of schedule a request may conform. -/
  burst : Nat
deriving Repr, DecidableEq

/-- Apply one arrival at clock `t`.  Conforming (`tat ≤ t + burst`) admits and
advances `tat := max t tat + t_int`; otherwise the state is untouched. -/
def gcraStep (g : Gcra) (t : Nat) : Gcra :=
  if g.tat ≤ t + g.burst then { g with tat := max t g.tat + g.t_int } else g

/-- Whether an arrival at clock `t` admits (`1`) or not (`0`). -/
def gcraAdmits (g : Gcra) (t : Nat) : Nat :=
  if g.tat ≤ t + g.burst then 1 else 0

/-- Fold a list of arrival times. -/
def gcraRun (g : Gcra) : List Nat → Gcra
  | [] => g
  | t :: ts => gcraRun (gcraStep g t) ts

/-- Count admitted arrivals over a run. -/
def gcraCount (g : Gcra) : List Nat → Nat
  | [] => 0
  | t :: ts => gcraAdmits g t + gcraCount (gcraStep g t) ts

/-! ### `t_int` and `burst` are parameters -/

@[simp] theorem gcraStep_tint_eq (g : Gcra) (t : Nat) : (gcraStep g t).t_int = g.t_int := by
  unfold gcraStep; split <;> rfl

@[simp] theorem gcraStep_burst_eq (g : Gcra) (t : Nat) : (gcraStep g t).burst = g.burst := by
  unfold gcraStep; split <;> rfl

/-! ### Monotonicity and no phantom charge -/

/-- **Theorem 3 analog.**  A step never moves the theoretical arrival time
backward. -/
theorem gcraStep_tat_mono (g : Gcra) (t : Nat) : g.tat ≤ (gcraStep g t).tat := by
  unfold gcraStep; split
  · dsimp only; omega
  · exact Nat.le_refl _

/-- **Theorem 4 analog.**  A rejected (non-conforming) arrival changes nothing —
no phantom advance of `tat`. -/
theorem gcra_reject_unchanged {g : Gcra} {t : Nat} (h : ¬ g.tat ≤ t + g.burst) :
    gcraStep g t = g := by
  unfold gcraStep; rw [if_neg h]

/-! ### The spacing lower bound -/

/-- One step advances `tat` by at least `admits * t_int`: an admission costs a
full emission interval of schedule. -/
theorem gcraStep_spacing (g : Gcra) (t : Nat) :
    g.tat + gcraAdmits g t * g.t_int ≤ (gcraStep g t).tat := by
  unfold gcraStep gcraAdmits
  by_cases hc : g.tat ≤ t + g.burst
  · rw [if_pos hc, if_pos hc]; dsimp only; omega
  · rw [if_neg hc, if_neg hc]; omega

/-- **Spacing lower bound.**  Over a run, `tat` advances by at least
`(#admits) * t_int` from its starting value.  Admitting `N` requests requires at
least `N` emission intervals of schedule. -/
theorem gcraRun_spacing : ∀ (g : Gcra) (es : List Nat),
    g.tat + gcraCount g es * g.t_int ≤ (gcraRun g es).tat := by
  intro g es
  induction es generalizing g with
  | nil => simp [gcraRun, gcraCount]
  | cons t ts ih =>
    rw [gcraRun, gcraCount]
    have hstep := gcraStep_spacing g t
    have hi : (gcraStep g t).t_int = g.t_int := gcraStep_tint_eq g t
    have ihb := ih (gcraStep g t)
    rw [hi] at ihb
    rw [Nat.add_mul]
    omega

/-! ### The window upper bound and the rate bound -/

/-- One step preserves the window bound `tat ≤ tEnd + burst + t_int` when the
arrival is within the window (`t ≤ tEnd`).  The conformance test is what keeps
`tat` from outrunning the window: an admitted `tat` was `≤ t + burst ≤ tEnd +
burst` before the `+ t_int` push. -/
theorem gcraStep_upper (g : Gcra) (t tEnd : Nat)
    (ht : t ≤ tEnd) (h0 : g.tat ≤ tEnd + g.burst + g.t_int) :
    (gcraStep g t).tat ≤ tEnd + g.burst + g.t_int := by
  unfold gcraStep
  by_cases hc : g.tat ≤ t + g.burst
  · rw [if_pos hc]; dsimp only; omega
  · rw [if_neg hc]; exact h0

/-- **Window upper bound.**  If every arrival falls within the window
(`t ≤ tEnd`) and `tat` starts within `tEnd + burst + t_int`, then it stays there
for the whole run. -/
theorem gcraRun_upper (tEnd : Nat) : ∀ (g : Gcra) (es : List Nat),
    (∀ t ∈ es, t ≤ tEnd) → g.tat ≤ tEnd + g.burst + g.t_int →
    (gcraRun g es).tat ≤ tEnd + g.burst + g.t_int := by
  intro g es
  induction es generalizing g with
  | nil => intro _ h0; simpa [gcraRun] using h0
  | cons t ts ih =>
    intro hEnd h0
    rw [gcraRun]
    have ht : t ≤ tEnd := hEnd t (List.mem_cons_self _ _)
    have hstep := gcraStep_upper g t tEnd ht h0
    have hb : (gcraStep g t).burst = g.burst := gcraStep_burst_eq g t
    have hi : (gcraStep g t).t_int = g.t_int := gcraStep_tint_eq g t
    have hEnd' : ∀ x ∈ ts, x ≤ tEnd := fun x hx => hEnd x (List.mem_cons_of_mem t hx)
    have h0' : (gcraStep g t).tat ≤ tEnd + (gcraStep g t).burst + (gcraStep g t).t_int := by
      rw [hb, hi]; exact hstep
    have := ih (gcraStep g t) hEnd' h0'
    rwa [hb, hi] at this

/-- **Theorem 1 analog (the GCRA rate bound).**  Over a window whose arrivals
all fall at or before `tEnd`, starting from a limiter whose theoretical arrival
time is at most `tEnd`, the number of admitted requests `N` satisfies
`N * t_int ≤ (tEnd - tat₀) + burst + t_int`.  With `D := tEnd - tat₀` the window
duration, this is `N ≤ 1 + (D + burst) / t_int`: the same counting guarantee as
the token bucket, expressed through the theoretical arrival time. -/
theorem gcra_rate_bound (g : Gcra) (es : List Nat) (tEnd : Nat)
    (hEnd : ∀ t ∈ es, t ≤ tEnd) (h0 : g.tat ≤ tEnd) :
    gcraCount g es * g.t_int ≤ (tEnd - g.tat) + g.burst + g.t_int := by
  have hlow := gcraRun_spacing g es
  have hup := gcraRun_upper tEnd g es hEnd (by omega)
  omega

end Rate
