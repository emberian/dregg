/-
Rate — a token-bucket rate limiter as a transition system over an explicit
clock.

Convention: time is an input.  There is no ambient clock.  Every transition
that depends on time takes the current clock reading as an argument, and the
clock is monotone — a reading is never earlier than the previous one.  The
model *enforces* monotonicity rather than assuming it: a `refill` to a clock
value earlier than the bucket's recorded `last` reading stutters (leaves the
state unchanged) instead of running the refill backward.  Durations are counted
in the same units as the clock; the refill rate is tokens per clock unit.

State (`Bucket`):

  * `tokens` — tokens currently available to admit requests;
  * `last`   — the clock value at the most recent refill;
  * `cap`    — the capacity: the maximum standing token count (the burst size);
  * `rate`   — the refill rate, in tokens per clock unit.

`cap` and `rate` are parameters: no transition changes them (`refill_cap_eq`,
`refill_rate_eq`, `tryAdmit_cap_eq`, `tryAdmit_rate_eq`).

Transitions:

  * `refill now` — advance the clock to `now` and credit `rate * (now - last)`
    tokens, capped at `cap`, then set `last := now`.  A backward `now < last`
    stutters.
  * `tryAdmit`   — consume one token if one is available (admit → `true`),
    otherwise leave the bucket untouched (reject → `false`).

This file proves the per-step facts:

  * the cap invariant (`refill_cap`, `tryAdmit_cap`) — `tokens ≤ cap` is
    preserved (theorem 2, lifted over traces in `Rate.Trace`);
  * monotonicity (`refill_last_mono`, `refill_tokens_mono`) — the clock never
    runs backward and, under the cap invariant, a refill never removes tokens
    (theorem 3);
  * no phantom charge (`tryAdmit_reject_unchanged`, `tryAdmit_charge_one`) — a
    rejected request consumes no token; an admitted one consumes exactly one
    (theorem 4);
  * the refill accounting inequality (`refill_account`) — the token stock plus
    the elapsed-time credit is conserved up to capping.  This is the local
    ingredient the trace-level rate bound (theorem 1) is assembled from.
-/

namespace Rate

/-- Token-bucket state.  `cap` and `rate` are parameters carried in the state so
transitions are closed on `Bucket`; no transition changes them. -/
structure Bucket where
  /-- Tokens currently available. -/
  tokens : Nat
  /-- Clock value at the most recent refill. -/
  last : Nat
  /-- Capacity — the maximum standing token count (burst size). -/
  cap : Nat
  /-- Refill rate, in tokens per clock unit. -/
  rate : Nat
deriving Repr, DecidableEq

/-- A full bucket at clock `0`: `cap` tokens, capacity `cap`, rate `rate`. -/
def init (cap rate : Nat) : Bucket :=
  { tokens := cap, last := 0, cap := cap, rate := rate }

/-- Advance the clock to `now`, crediting `rate * (now - last)` tokens capped at
`cap`, then set `last := now`.  A backward reading (`now < last`) stutters, so
the recorded clock never moves backward and a stale reading cannot un-credit
tokens. -/
def refill (now : Nat) (b : Bucket) : Bucket :=
  if b.last ≤ now then
    { tokens := min b.cap (b.tokens + b.rate * (now - b.last)),
      last := now, cap := b.cap, rate := b.rate }
  else b

/-- Consume one token if available.  The boolean records the decision: `true`
(admitted, one token consumed) or `false` (rejected, state untouched). -/
def tryAdmit (b : Bucket) : Bucket × Bool :=
  if 1 ≤ b.tokens then
    ({ b with tokens := b.tokens - 1 }, true)
  else
    (b, false)

/-! ### `cap` and `rate` are parameters -/

@[simp] theorem refill_cap_eq (now : Nat) (b : Bucket) : (refill now b).cap = b.cap := by
  unfold refill; split <;> rfl

@[simp] theorem refill_rate_eq (now : Nat) (b : Bucket) : (refill now b).rate = b.rate := by
  unfold refill; split <;> rfl

@[simp] theorem tryAdmit_cap_eq (b : Bucket) : (tryAdmit b).1.cap = b.cap := by
  unfold tryAdmit; split <;> rfl

@[simp] theorem tryAdmit_rate_eq (b : Bucket) : (tryAdmit b).1.rate = b.rate := by
  unfold tryAdmit; split <;> rfl

/-! ### The cap invariant (theorem 2, per step) -/

/-- `refill` never lifts the token count above capacity. -/
theorem refill_cap {now : Nat} {b : Bucket} (h : b.tokens ≤ b.cap) :
    (refill now b).tokens ≤ b.cap := by
  unfold refill; split
  · dsimp only; omega
  · exact h

/-- `tryAdmit` never lifts the token count above capacity (it only ever removes
tokens). -/
theorem tryAdmit_cap {b : Bucket} (h : b.tokens ≤ b.cap) :
    (tryAdmit b).1.tokens ≤ b.cap := by
  unfold tryAdmit; split
  · dsimp only; omega
  · exact h

/-! ### Monotonicity (theorem 3, per step) -/

/-- The recorded clock never runs backward: a `refill` only ever moves `last`
forward (the backward-reading guard is what makes this hold unconditionally). -/
theorem refill_last_mono (now : Nat) (b : Bucket) : b.last ≤ (refill now b).last := by
  unfold refill; split
  · dsimp only; omega
  · exact Nat.le_refl _

/-- Under the cap invariant, a `refill` never removes tokens: the credit is
non-negative and capping cannot drop the stock below where it started (since it
was already within capacity). -/
theorem refill_tokens_mono {now : Nat} {b : Bucket} (h : b.tokens ≤ b.cap) :
    b.tokens ≤ (refill now b).tokens := by
  unfold refill; split
  · dsimp only; omega
  · exact Nat.le_refl _

/-- `tryAdmit` leaves the recorded clock unchanged (admission does not observe
time). -/
@[simp] theorem tryAdmit_last_eq (b : Bucket) : (tryAdmit b).1.last = b.last := by
  unfold tryAdmit; split <;> rfl

/-- Availability decides admission: a token in hand admits. -/
theorem tryAdmit_snd_true {b : Bucket} (h : 1 ≤ b.tokens) : (tryAdmit b).2 = true := by
  unfold tryAdmit; rw [if_pos h]

/-- No token in hand rejects. -/
theorem tryAdmit_snd_false {b : Bucket} (h : ¬ 1 ≤ b.tokens) : (tryAdmit b).2 = false := by
  unfold tryAdmit; rw [if_neg h]

/-! ### No phantom charge (theorem 4, per step) -/

/-- A rejected request leaves the bucket completely unchanged. -/
theorem tryAdmit_reject_unchanged {b : Bucket} (h : (tryAdmit b).2 = false) :
    (tryAdmit b).1 = b := by
  unfold tryAdmit at h ⊢; split
  · rename_i hge; rw [if_pos hge] at h; simp at h
  · rfl

/-- A rejected request consumes no token. -/
theorem tryAdmit_reject_no_charge {b : Bucket} (h : (tryAdmit b).2 = false) :
    (tryAdmit b).1.tokens = b.tokens := by
  rw [tryAdmit_reject_unchanged h]

/-- An admitted request consumes exactly one token — no more, no less. -/
theorem tryAdmit_charge_one {b : Bucket} (h : (tryAdmit b).2 = true) :
    (tryAdmit b).1.tokens + 1 = b.tokens := by
  unfold tryAdmit at h ⊢; split
  · rename_i hge; dsimp only; omega
  · rename_i hlt; rw [if_neg hlt] at h; simp at h

/-! ### The refill accounting inequality (ingredient for theorem 1) -/

/-- **Refill conservation.**  The token stock after a refill, plus the clock
credit already accounted at the old reading, is at most the old stock plus the
credit accounted at the new reading.  Equivalently, a refill adds at most
`rate * elapsed` tokens (capping can only add fewer).  Stated additively to keep
everything in `Nat`.  Holds unconditionally, including on the backward-reading
stutter. -/
theorem refill_account (now : Nat) (b : Bucket) :
    (refill now b).tokens + b.rate * b.last ≤ b.tokens + b.rate * (refill now b).last := by
  unfold refill; split
  · rename_i h
    -- `rate * (now - last) + rate * last = rate * now`, since `last ≤ now`.
    have hdist : b.rate * (now - b.last) + b.rate * b.last = b.rate * now := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h]
    dsimp only
    omega
  · omega

end Rate
