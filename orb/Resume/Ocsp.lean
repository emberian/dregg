/-
Resume — OCSP staple freshness and the atomic staple swap.

A stapled OCSP response certifies revocation status for a bounded window
`[thisUpdate, nextUpdate)`.  A front end must serve a staple only while it is
fresh (`now < nextUpdate`); a staple at or past `nextUpdate` is stale and must
never be handed out.  The current staple lives in a cache cell that a reload
(SIGHUP-style) swaps wholesale, so a concurrent request observes either the old
staple or the new one — never a field-torn mix.  This is the same atomic-swap
shape the config reload uses.

  * `Staple`   — the stapled response: its validity window and an opaque body.
  * `fresh`    — the freshness predicate `now ∈ [thisUpdate, nextUpdate)`.
  * `serve?`   — the single-staple serve decision (serve iff fresh).
  * `Cache`    — the current staple cell plus an append-only served log.
  * `request`  — serve the current staple iff present and fresh (else stutter).
  * `swap`     — replace the whole staple cell in one atomic step.
-/

namespace Resume

/-- A stapled OCSP response: the validity window `[thisUpdate, nextUpdate)` and
an opaque body identity. -/
structure Staple where
  thisUpdate : Nat
  nextUpdate : Nat
  body : Nat
deriving DecidableEq, Repr

/-- Freshness: the current time lies in the half-open validity window. -/
def Staple.fresh (s : Staple) (now : Nat) : Bool :=
  decide (s.thisUpdate ≤ now) && decide (now < s.nextUpdate)

/-- Freshness agrees with the window membership exactly. -/
theorem fresh_iff (s : Staple) (now : Nat) :
    s.fresh now = true ↔ s.thisUpdate ≤ now ∧ now < s.nextUpdate := by
  simp only [Staple.fresh, Bool.and_eq_true, decide_eq_true_eq]

/-- **A staple at or past `nextUpdate` is not fresh.** -/
theorem stale_not_fresh (s : Staple) (now : Nat) (h : s.nextUpdate ≤ now) :
    s.fresh now = false := by
  cases hb : s.fresh now with
  | false => rfl
  | true => have := (fresh_iff s now).mp hb; omega

/-- The single-staple serve decision: hand out the staple iff it is fresh. -/
def serve? (s : Staple) (now : Nat) : Option Staple :=
  if s.fresh now = true then some s else none

/-- Whatever is served is the current staple, and it is fresh. -/
theorem served_is_fresh {s r : Staple} {now : Nat} (h : serve? s now = some r) :
    r = s ∧ s.thisUpdate ≤ now ∧ now < s.nextUpdate := by
  unfold serve? at h
  by_cases hf : s.fresh now = true
  · rw [if_pos hf] at h
    obtain ⟨h1, h2⟩ := (fresh_iff s now).mp hf
    exact ⟨(Option.some.inj h).symm, h1, h2⟩
  · rw [if_neg hf] at h; exact absurd h (by simp)

/-- **Freshness invariant (point form).**  A staple at or past `nextUpdate` is
never served. -/
theorem stale_never_served (s : Staple) (now : Nat) (h : s.nextUpdate ≤ now) :
    serve? s now = none := by
  have hnf : ¬ (s.fresh now = true) := by
    intro hf; have := (fresh_iff s now).mp hf; omega
  unfold serve?
  rw [if_neg hnf]

/-! ### The staple cache and its atomic swap -/

/-- One served observation: the staple handed out and the time it went out. -/
structure Served where
  staple : Staple
  time : Nat
deriving DecidableEq, Repr

/-- The staple cache: the current cell (a whole `Option Staple`) and an
append-only log of served responses. -/
structure Cache where
  cur : Option Staple
  served : List Served
deriving Repr

/-- Cold boot: no staple, nothing served. -/
def Cache.init : Cache := { cur := none, served := [] }

/-- Serve the current staple at time `now`: append it to the log iff present
and fresh; otherwise stutter. -/
def Cache.request (now : Nat) (c : Cache) : Cache :=
  match c.cur with
  | none => c
  | some s => if s.fresh now = true then { c with served := ⟨s, now⟩ :: c.served } else c

/-- Swap the whole staple cell in one atomic step (SIGHUP-style reload).  Only
the `cur` field is replaced; the served log is untouched. -/
def Cache.swap (n : Option Staple) (c : Cache) : Cache := { c with cur := n }

/-- **Swap atomicity.**  A swap replaces only the staple cell, as one whole
value: the served log is unchanged and the cell becomes exactly `n`. -/
theorem swap_atomic (n : Option Staple) (c : Cache) :
    (c.swap n).cur = n ∧ (c.swap n).served = c.served :=
  ⟨rfl, rfl⟩

/-- **Old-or-new, never torn.**  Across a swap the staple cell is observed as
exactly the old cell or the new one — there is no observable intermediate that
mixes fields from the two. -/
theorem swap_old_or_new (n : Option Staple) (c : Cache) (obs : Option Staple)
    (h : obs = c.cur ∨ obs = (c.swap n).cur) : obs = c.cur ∨ obs = n := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- On a stale current staple, a request appends nothing (it stutters). -/
theorem request_stale_noop (now : Nat) (c : Cache) (s : Staple)
    (hc : c.cur = some s) (h : s.nextUpdate ≤ now) :
    (c.request now).served = c.served := by
  have hf : s.fresh now = false := stale_not_fresh s now h
  simp [Cache.request, hc, hf]

/-- On a fresh current staple, a request serves exactly that staple. -/
theorem request_fresh_serves (now : Nat) (c : Cache) (s : Staple)
    (hc : c.cur = some s) (hf : s.fresh now = true) :
    (c.request now).served = ⟨s, now⟩ :: c.served := by
  simp [Cache.request, hc, hf]

namespace Cache

/-- One step of the cache: serve a request, or swap the staple cell. -/
inductive Step : Cache → Cache → Prop where
  | request (now : Nat) (c : Cache) : Step c (c.request now)
  | swap (n : Option Staple) (c : Cache) : Step c (c.swap n)

/-- States reachable from a cold boot by any sequence of steps. -/
inductive Reachable : Cache → Prop where
  | init : Reachable Cache.init
  | step {c c' : Cache} : Reachable c → Step c c' → Reachable c'

/-- Cache invariant: every served staple was fresh at the time it was served. -/
def Wf (c : Cache) : Prop := ∀ e ∈ c.served, e.staple.fresh e.time = true

theorem wf_init : Wf Cache.init := by
  intro e he
  simp [Cache.init] at he

theorem wf_request (now : Nat) {c : Cache} (h : Wf c) : Wf (c.request now) := by
  cases hc : c.cur with
  | none => simp only [Cache.request, hc]; exact h
  | some s =>
    simp only [Cache.request, hc]
    by_cases hf : s.fresh now = true
    · rw [if_pos hf]
      intro e he
      rcases List.mem_cons.mp he with h1 | h1
      · rw [h1]; exact hf
      · exact h e h1
    · rw [if_neg hf]; exact h

theorem wf_swap (n : Option Staple) {c : Cache} (h : Wf c) : Wf (c.swap n) := by
  intro e he
  exact h e he

theorem wf_step {c c' : Cache} (h : Wf c) (hstep : Step c c') : Wf c' := by
  cases hstep with
  | request now c => exact wf_request now h
  | swap n c => exact wf_swap n h

/-- **The invariant holds throughout every run.** -/
theorem reachable_wf {c : Cache} (h : Reachable c) : Wf c := by
  induction h with
  | init => exact wf_init
  | step _ hstep ih => exact wf_step ih hstep

/-- **Freshness invariant (log form).**  In every reachable cache, every served
staple was strictly before its `nextUpdate` when served — no stale staple is
ever in the served log, and the swap preserves this. -/
theorem served_within_next_update {c : Cache} (h : Reachable c) :
    ∀ e ∈ c.served, e.time < e.staple.nextUpdate := by
  intro e he
  have := (reachable_wf h) e he
  exact ((fresh_iff e.staple e.time).mp this).2

end Cache

end Resume
