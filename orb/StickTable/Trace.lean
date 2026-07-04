/-
StickTable.Trace — the stick table over a trace of `track` events, and the
per-key counting bound.

A run is a list of `Ev`s (each a `(key, now)` pair — a request for `key` at clock
`now`) applied left to right from a starting `Table`.  `run` folds the state;
`countFor k` counts the events that targeted `k`.

Headline results:

  * `run_getCount` — the exact per-key accounting identity: after a run the
    counter for `k` is its starting value plus the number of `track` events for
    `k`.  Every event for `k` adds exactly one; no capping.
  * `run_count_bound` (**theorem 5**) — the counting bound analogous to the rate
    limiter: over any window (event trace) the tracked count for a key is bounded
    by the number of `track` events for it.  Here the bound is *tight* (equality)
    because, unlike the token bucket, there is no capacity ceiling.
  * `run_getLastSeen_mono` (**theorem 4, trace level**) — the recorded last-seen
    of any key never runs backward across a run.
  * `run_Wf` (**theorem 3, trace level**) — the finite key-unique invariant is
    preserved across a run.
-/

import StickTable.Basic

namespace StickTable

/-- A timed `track` event: a request for `key` arriving at clock `now`. -/
structure Ev where
  /-- The key tracked by this event. -/
  key : Nat
  /-- The clock reading at which the event arrives (the time input). -/
  now : Nat
deriving Repr, DecidableEq

/-- Fold a list of `track` events over the table, left to right. -/
def run (t : Table) : List Ev → Table
  | [] => t
  | ev :: rest => run (bump ev.key ev.now t) rest

/-- How many events in the trace target key `k`. -/
def countFor (k : Nat) : List Ev → Nat
  | [] => 0
  | ev :: rest => (if ev.key = k then 1 else 0) + countFor k rest

/-! ### Theorem 3 (trace level) — the invariant is preserved over a run -/

theorem run_Wf (t : Table) (evs : List Ev) (hwf : Wf t) : Wf (run t evs) := by
  induction evs generalizing t with
  | nil => simpa [run] using hwf
  | cons ev rest ih =>
    simp only [run]
    exact ih _ (bump_Wf ev.key ev.now hwf)

/-! ### Theorem 5 — the per-key counting identity and bound -/

/-- **The per-key accounting identity.**  After a run, the counter for `k` equals
its starting value plus the number of events that targeted `k`.  Each targeting
event contributes exactly one (`bump_getCount_self`); non-targeting events leave
it untouched (`bump_getCount_other`). -/
theorem run_getCount (k : Nat) (t : Table) (evs : List Ev) :
    getCount k (run t evs) = getCount k t + countFor k evs := by
  induction evs generalizing t with
  | nil => simp [run, countFor]
  | cons ev rest ih =>
    simp only [run, countFor]
    rw [ih (bump ev.key ev.now t)]
    by_cases hk : ev.key = k
    · rw [if_pos hk]
      have hstep : getCount k (bump ev.key ev.now t) = getCount k t + 1 := by
        rw [hk]; exact bump_getCount_self k ev.now t
      omega
    · rw [if_neg hk]
      have hne : k ≠ ev.key := fun he => hk he.symm
      have hstep : getCount k (bump ev.key ev.now t) = getCount k t := bump_getCount_other hne t
      omega

/-- The counter for `k` after a run from the empty table is exactly the number of
events targeting `k`. -/
theorem run_getCount_empty (k : Nat) (evs : List Ev) :
    getCount k (run [] evs) = countFor k evs := by
  rw [run_getCount]; simp [getCount, find]

/-- **Theorem 5 (counting bound).**  Over any trace, the tracked count for a key
is bounded by the number of `track` events for it — in fact equal (no capping).
This is the stick-table analogue of the rate limiter's `rate_bound`. -/
theorem run_count_bound (k : Nat) (t : Table) (evs : List Ev) :
    getCount k (run t evs) ≤ getCount k t + countFor k evs :=
  Nat.le_of_eq (run_getCount k t evs)

/-- The number of events targeting a key is at most the total number of events —
so the tracked count is also bounded by the window length. -/
theorem countFor_le_length (k : Nat) (evs : List Ev) :
    countFor k evs ≤ evs.length := by
  induction evs with
  | nil => simp [countFor]
  | cons ev rest ih =>
    simp only [countFor, List.length_cons]
    by_cases hk : ev.key = k
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega

/-- Counting bound in window-length form: from the empty table, the tracked count
for any key is at most the number of events in the window. -/
theorem run_count_le_length (k : Nat) (evs : List Ev) :
    getCount k (run [] evs) ≤ evs.length := by
  rw [run_getCount_empty]; exact countFor_le_length k evs

/-! ### Theorem 4 (trace level) — monotone last-seen over a run -/

/-- **Theorem 4 (over a run).**  The recorded last-seen of any key never runs
backward across a whole trace — the per-step `max` discipline lifts to the fold. -/
theorem run_getLastSeen_mono (k : Nat) (t : Table) (evs : List Ev) :
    getLastSeen k t ≤ getLastSeen k (run t evs) := by
  induction evs generalizing t with
  | nil => simp [run]
  | cons ev rest ih =>
    simp only [run]
    exact Nat.le_trans (bump_getLastSeen_mono ev.key ev.now k t)
      (ih (bump ev.key ev.now t))

end StickTable
