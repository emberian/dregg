/-
Rate.Trace — the token bucket over a trace of timed events, and the rate bound.

A run is a list of `Event`s applied left to right from a starting `Bucket`.
Two event kinds, each carrying the clock reading that is its time input:

  * `tick now` — the clock advances to `now`; the bucket refills, nothing is
    admitted.
  * `req now`  — a request arrives at clock `now`; the bucket first refills to
    `now`, then attempts to admit.  This is the lazy-refill discipline: a
    request sees the tokens it is due at its own arrival time before it charges.

`run` folds the state; `countAdmits` counts the requests that were admitted
along the way.  `duration` is the span the clock advanced over the run —
`(run b es).last - b.last` — which is well-defined precisely because the clock
is monotone (`run_last_mono`).

Headline results:

  * `run_account` — the trace-level conservation invariant: admits consumed,
    plus tokens remaining, plus the credit accounted at the start clock, is at
    most the starting stock plus the credit accounted at the end clock.
  * `rate_bound` — over a run, `#admits ≤ tokens₀ + rate * D`.
  * `rate_bound_cap` (**theorem 1**) — over any window of duration `D`, the
    number of admitted requests is at most `cap + rate * D`.
  * `rate_bound_from_init` — the same, specialized to a full-bucket cold start:
    `#admits ≤ cap + rate * D`, with `tokens₀ = cap`.
  * `run_tokens_le_cap` (**theorem 2**) — `tokens ≤ cap` holds throughout.
  * `run_last_mono` (**theorem 3**) — the clock never runs backward over a run.
-/

import Rate.Bucket

namespace Rate

/-- A timed event.  Each constructor carries the clock reading that is its time
input. -/
inductive Event where
  /-- The clock advances to `now`: refill only. -/
  | tick (now : Nat)
  /-- A request arrives at clock `now`: refill to `now`, then attempt to admit. -/
  | req (now : Nat)
deriving Repr, DecidableEq

/-- Apply one event to the bucket. -/
def stepB (b : Bucket) : Event → Bucket
  | .tick now => refill now b
  | .req now => (tryAdmit (refill now b)).1

/-- Whether one event admits a request (`1`) or not (`0`).  Only a `req` whose
post-refill bucket holds a token admits. -/
def admits (b : Bucket) : Event → Nat
  | .tick _ => 0
  | .req now => if 1 ≤ (refill now b).tokens then 1 else 0

/-- Fold a list of events over the bucket. -/
def run (b : Bucket) : List Event → Bucket
  | [] => b
  | e :: es => run (stepB b e) es

/-- Count the requests admitted over a run. -/
def countAdmits (b : Bucket) : List Event → Nat
  | [] => 0
  | e :: es => admits b e + countAdmits (stepB b e) es

/-- The window duration a run spans: how far the clock advanced.  Well-defined
because the clock is monotone (`run_last_mono`). -/
def duration (b : Bucket) (es : List Event) : Nat := (run b es).last - b.last

/-! ### `cap` and `rate` are parameters of a run -/

@[simp] theorem stepB_cap_eq (b : Bucket) (e : Event) : (stepB b e).cap = b.cap := by
  cases e <;> simp [stepB]

@[simp] theorem stepB_rate_eq (b : Bucket) (e : Event) : (stepB b e).rate = b.rate := by
  cases e <;> simp [stepB]

@[simp] theorem run_cap_eq (b : Bucket) (es : List Event) : (run b es).cap = b.cap := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih => rw [run]; rw [ih]; exact stepB_cap_eq b e

@[simp] theorem run_rate_eq (b : Bucket) (es : List Event) : (run b es).rate = b.rate := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih => rw [run]; rw [ih]; exact stepB_rate_eq b e

/-! ### Theorem 2 — the cap invariant, over a run -/

/-- One step preserves `tokens ≤ cap`. -/
theorem stepB_tokens_le_cap {b : Bucket} (e : Event) (h : b.tokens ≤ b.cap) :
    (stepB b e).tokens ≤ b.cap := by
  cases e with
  | tick now => exact refill_cap h
  | req now =>
    show (tryAdmit (refill now b)).1.tokens ≤ b.cap
    have hr : (refill now b).tokens ≤ (refill now b).cap := by
      rw [refill_cap_eq]; exact refill_cap h
    have := tryAdmit_cap hr
    rwa [refill_cap_eq] at this

/-- **Theorem 2 (cap invariant).**  If the bucket starts within capacity, the
token count never exceeds the capacity at any point in the run. -/
theorem run_tokens_le_cap {b : Bucket} (es : List Event) (h : b.tokens ≤ b.cap) :
    (run b es).tokens ≤ b.cap := by
  induction es generalizing b with
  | nil => exact h
  | cons e es ih =>
    rw [run]
    have hc : (stepB b e).cap = b.cap := stepB_cap_eq b e
    have hstep : (stepB b e).tokens ≤ (stepB b e).cap := by
      rw [hc]; exact stepB_tokens_le_cap e h
    have := ih (b := stepB b e) hstep
    rwa [hc] at this

/-! ### Theorem 3 — the clock is monotone over a run -/

/-- One step never moves the recorded clock backward. -/
theorem stepB_last_mono (b : Bucket) (e : Event) : b.last ≤ (stepB b e).last := by
  cases e with
  | tick now => exact refill_last_mono now b
  | req now =>
    show b.last ≤ (tryAdmit (refill now b)).1.last
    rw [tryAdmit_last_eq]
    exact refill_last_mono now b

/-- **Theorem 3 (monotone clock).**  Over a whole run the recorded clock never
runs backward, so `duration` is a genuine non-negative span. -/
theorem run_last_mono (b : Bucket) (es : List Event) : b.last ≤ (run b es).last := by
  induction es generalizing b with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    rw [run]
    exact Nat.le_trans (stepB_last_mono b e) (ih (b := stepB b e))

/-! ### Theorem 1 — the rate bound -/

/-- One step's local accounting inequality: the admits it contributes, plus the
tokens it leaves, plus the credit at the old clock, is at most the old stock
plus the credit at the new clock.  Every case reduces to `refill_account`. -/
theorem stepB_account (b : Bucket) (e : Event) :
    admits b e + (stepB b e).tokens + b.rate * b.last
      ≤ b.tokens + b.rate * (stepB b e).last := by
  cases e with
  | tick now =>
    have hr := refill_account now b
    simp only [admits, stepB]
    omega
  | req now =>
    have hr := refill_account now b
    -- `hr : (refill now b).tokens + rate*last ≤ b.tokens + rate*(refill now b).last`
    simp only [admits, stepB]
    have hl := tryAdmit_last_eq (refill now b)
    by_cases h1 : 1 ≤ (refill now b).tokens
    · -- admitted: exactly one token consumed, clock unchanged
      rw [if_pos h1, hl]
      have hc := tryAdmit_charge_one (tryAdmit_snd_true h1)
      omega
    · -- rejected: nothing consumed, clock unchanged
      rw [if_neg h1, hl]
      have hc := tryAdmit_reject_no_charge (tryAdmit_snd_false h1)
      rw [hc]
      omega

/-- **The trace conservation invariant.**  Admits consumed, plus tokens
remaining, plus the credit accounted at the start clock, is at most the starting
stock plus the credit accounted at the end clock.  Additive form, all in `Nat`. -/
theorem run_account (b : Bucket) (es : List Event) :
    countAdmits b es + (run b es).tokens + b.rate * b.last
      ≤ b.tokens + b.rate * (run b es).last := by
  induction es generalizing b with
  | nil => simp only [countAdmits, run]; omega
  | cons e es ih =>
    rw [countAdmits, run]
    have hstep := stepB_account b e
    have hrate : (stepB b e).rate = b.rate := stepB_rate_eq b e
    have ihb := ih (b := stepB b e)
    rw [hrate] at ihb
    omega

/-- **Rate bound (stock form).**  Over any run, the number of admitted requests
is at most the starting token stock plus `rate * D`, where `D` is the window
duration the clock advanced. -/
theorem rate_bound (b : Bucket) (es : List Event) :
    countAdmits b es ≤ b.tokens + b.rate * duration b es := by
  have hP := run_account b es
  have hmono := run_last_mono b es
  have htel : b.rate * duration b es + b.rate * b.last = b.rate * (run b es).last := by
    unfold duration
    rw [← Nat.mul_add, Nat.sub_add_cancel hmono]
  omega

/-- **Theorem 1 (the rate bound).**  Over any window of duration `D`, the number
of admitted requests is at most `cap + rate * D` — provided the bucket starts
within capacity.  This is the rate-limiting guarantee, as a counting bound over
the trace. -/
theorem rate_bound_cap (b : Bucket) (es : List Event) (h : b.tokens ≤ b.cap) :
    countAdmits b es ≤ b.cap + b.rate * duration b es := by
  have := rate_bound b es
  omega

/-- **Theorem 1, cold start.**  From a full-bucket cold boot, the number of
admitted requests over a run is at most `cap + rate * D`.  Here `D` is just the
final clock value, since the bucket starts at clock `0`. -/
theorem rate_bound_from_init (cap rate : Nat) (es : List Event) :
    countAdmits (init cap rate) es ≤ cap + rate * duration (init cap rate) es := by
  have h : (init cap rate).tokens ≤ (init cap rate).cap := Nat.le_refl _
  have := rate_bound_cap (init cap rate) es h
  simpa [init] using this

end Rate
