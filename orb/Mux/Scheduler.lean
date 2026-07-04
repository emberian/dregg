import Mux.Priority
import H2

/-!
# Mux.Scheduler — the priority-respecting stream picker

A connection carries a set of concurrent streams. Each stream has a priority
(`Mux.Priority`) and a pending send queue (`H2.Bytes`, matching the byte-string
convention used across this package). The scheduler `select` chooses the next
stream to serve.

The selection rule mirrors the reference RFC 9218 order: pick the pending
stream of **minimal rank** (`Priority.rank` — urgency first, then
non-incremental before incremental), breaking ties by **smallest stream id**.
`select` is a total function into `Option Stream`: `none` is the clean terminal
reached exactly when nothing is pending.

Headline theorems:

* `select_min_urgency` / `select_priority_respected` — **priority respected**:
  the selected stream has minimal urgency among pending streams; a
  strictly-higher-urgency (lower urgency value) pending stream is served first.
* `select_det_by_id` — **determinism by id**: among equal-urgency
  non-incremental pending streams the selection is the least id (no starvation
  ambiguity; the incremental case is handled by `Mux.RoundRobin`).
* `select_pending_mem` / `not_select_of_idle` — **never picks an idle stream**.
* `select_eq_none_iff` / `select_none_of_no_pending` / `select_isSome_of_pending`
  — **totality / clean terminal**: `select` yields `none` iff nothing pends.
-/

namespace Mux

/-- A schedulable stream: an id, a priority, and a pending send queue. -/
structure Stream where
  id : StreamId
  prio : Priority
  queue : H2.Bytes
deriving Repr, DecidableEq

namespace Stream

/-- The stream has pending data to send. -/
def hasPending (s : Stream) : Bool := !s.queue.isEmpty

end Stream

open Stream

/-! ## The selection order: lexicographic on `(rank, id)` -/

/-- Strict selection order: `a` is served strictly before `b`. Rank first
(urgency, then non-incremental before incremental), id as tie-break. -/
def slt (a b : Stream) : Prop :=
  a.prio.rank < b.prio.rank ∨ (a.prio.rank = b.prio.rank ∧ a.id < b.id)

/-- Non-strict selection order. -/
def sle (a b : Stream) : Prop :=
  a.prio.rank < b.prio.rank ∨ (a.prio.rank = b.prio.rank ∧ a.id ≤ b.id)

instance decSlt (a b : Stream) : Decidable (slt a b) := by unfold slt; infer_instance

theorem sle_refl (a : Stream) : sle a a := Or.inr ⟨rfl, Nat.le_refl _⟩

theorem sle_trans {a b c : Stream} (h1 : sle a b) (h2 : sle b c) : sle a c := by
  rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
  · exact Or.inl (Nat.lt_trans h1 h2)
  · rw [h2a] at h1; exact Or.inl h1
  · rw [← h1a] at h2; exact Or.inl h2
  · exact Or.inr ⟨h1a.trans h2a, Nat.le_trans h1b h2b⟩

theorem slt_to_sle {a b : Stream} (h : slt a b) : sle a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Nat.le_of_lt h2⟩

theorem not_slt_to_sle {a b : Stream} (h : ¬ slt a b) : sle b a := by
  unfold slt at h
  have hnr : ¬ a.prio.rank < b.prio.rank := fun hh => h (Or.inl hh)
  rcases Nat.lt_or_ge b.prio.rank a.prio.rank with hr | hr
  · exact Or.inl hr
  · have hrank : b.prio.rank = a.prio.rank :=
      Nat.le_antisymm (Nat.not_lt.mp hnr) hr
    have hid : ¬ a.id < b.id := fun hh => h (Or.inr ⟨hrank.symm, hh⟩)
    exact Or.inr ⟨hrank, Nat.le_of_not_lt hid⟩

/-- `s` is a strictly better candidate than `b` (comes earlier in the order). -/
def better (s b : Stream) : Bool := decide (slt s b)

theorem better_true {s b : Stream} (h : better s b = true) : slt s b :=
  of_decide_eq_true h
theorem better_false {s b : Stream} (h : better s b = false) : ¬ slt s b :=
  of_decide_eq_false h

/-! ## `bestOf`: minimal element of a list -/

/-- The minimal-order stream of a list (least `(rank, id)`), or `none` if
empty. -/
def bestOf : List Stream → Option Stream
  | [] => none
  | s :: rest =>
    match bestOf rest with
    | none => some s
    | some b => if better s b then some s else some b

theorem bestOf_eq_none : ∀ {l : List Stream}, bestOf l = none ↔ l = [] := by
  intro l
  cases l with
  | nil => simp [bestOf]
  | cons s rest =>
    simp only [bestOf]
    cases bestOf rest with
    | none => simp
    | some b => by_cases hb : better s b = true <;> simp [hb]

theorem bestOf_mem : ∀ {l : List Stream} {b : Stream}, bestOf l = some b → b ∈ l := by
  intro l
  induction l with
  | nil => intro b h; simp [bestOf] at h
  | cons s rest ih =>
    intro b h
    cases hbr : bestOf rest with
    | none =>
      simp only [bestOf, hbr] at h; obtain rfl := Option.some.inj h
      exact List.mem_cons_self _ _
    | some b0 =>
      simp only [bestOf, hbr] at h
      by_cases hb : better s b0 = true
      · rw [if_pos hb] at h; obtain rfl := Option.some.inj h
        exact List.mem_cons_self _ _
      · rw [if_neg hb] at h; obtain rfl := Option.some.inj h
        exact List.mem_cons_of_mem _ (ih hbr)

/-- **Minimality.** The `bestOf` element precedes every element in the order. -/
theorem bestOf_min : ∀ {l : List Stream} {b : Stream}, bestOf l = some b →
    ∀ x ∈ l, sle b x := by
  intro l
  induction l with
  | nil => intro b h; simp [bestOf] at h
  | cons s rest ih =>
    intro b h x hx
    cases hbr : bestOf rest with
    | none =>
      simp only [bestOf, hbr] at h; obtain rfl := Option.some.inj h
      have hnil : rest = [] := bestOf_eq_none.mp hbr
      subst hnil
      simp only [List.mem_singleton] at hx
      subst hx
      exact sle_refl _
    | some b0 =>
      simp only [bestOf, hbr] at h
      by_cases hb : better s b0 = true
      · rw [if_pos hb] at h; obtain rfl := Option.some.inj h
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact sle_refl _
        · exact sle_trans (slt_to_sle (better_true hb)) (ih hbr x hx')
      · rw [if_neg hb] at h; obtain rfl := Option.some.inj h
        have hbf : better s b0 = false := by
          cases h' : better s b0 with
          | true => exact absurd h' hb
          | false => rfl
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact not_slt_to_sle (better_false hbf)
        · exact ih hbr x hx'

/-! ## The scheduler -/

/-- **The scheduler.** Pick the minimal pending stream; `none` if none pends.
Total by construction. -/
def select (streams : List Stream) : Option Stream :=
  bestOf (streams.filter hasPending)

/-! ### Theorem 3 — an idle stream is never selected -/

/-- A selected stream is a member of the set and has pending data. -/
theorem select_pending_mem {streams : List Stream} {s : Stream}
    (h : select streams = some s) : s.hasPending = true ∧ s ∈ streams := by
  have hm := bestOf_mem h
  rw [List.mem_filter] at hm
  exact ⟨hm.2, hm.1⟩

/-- Contrapositive: a stream with no pending data is never selected. -/
theorem not_select_of_idle {streams : List Stream} {s : Stream}
    (h : s.hasPending = false) : select streams ≠ some s := by
  intro hsel
  have := (select_pending_mem hsel).1
  rw [h] at this
  exact Bool.noConfusion this

/-! ### Theorem 1 — priority respected -/

/-- **Priority respected.** The selected stream's urgency is ≤ that of every
pending stream: it is a minimal-urgency stream. -/
theorem select_min_urgency {streams : List Stream} {s : Stream}
    (h : select streams = some s) :
    ∀ t ∈ streams, t.hasPending = true → s.prio.urgency ≤ t.prio.urgency := by
  intro t ht hp
  have htf : t ∈ streams.filter hasPending := List.mem_filter.mpr ⟨ht, hp⟩
  have hmin := bestOf_min h t htf
  unfold sle at hmin
  rcases Nat.lt_or_ge t.prio.urgency s.prio.urgency with hlt | hge
  · exfalso
    have hr := Priority.rank_lt_of_urgency_lt hlt
    omega
  · exact hge

/-- Direct "served before" form: no strictly-higher-urgency (lower urgency
value) pending stream is passed over. If one exists, the selection is
impossible. -/
theorem select_priority_respected {streams : List Stream} {s t : Stream}
    (h : select streams = some s) (ht : t ∈ streams) (hp : t.hasPending = true)
    (hu : t.prio.urgency < s.prio.urgency) : False := by
  have := select_min_urgency h t ht hp
  omega

/-! ### Theorem 2a — determinism by id among equal-urgency non-incremental -/

/-- **Determinism by id.** Among pending streams of equal urgency that are both
non-incremental, the selected stream is the one with the least id — a
deterministic, starvation-free choice. (The incremental case uses round-robin;
see `Mux.RoundRobin`.) -/
theorem select_det_by_id {streams : List Stream} {s t : Stream}
    (h : select streams = some s) (ht : t ∈ streams) (hp : t.hasPending = true)
    (hu : t.prio.urgency = s.prio.urgency)
    (his : s.prio.incremental = false) (hit : t.prio.incremental = false) :
    s.id ≤ t.id := by
  have htf : t ∈ streams.filter hasPending := List.mem_filter.mpr ⟨ht, hp⟩
  have hmin := bestOf_min h t htf
  unfold sle at hmin
  have hrs : s.prio.rank = t.prio.rank := by
    unfold Priority.rank; rw [his, hit, hu]
  rcases hmin with hlt | ⟨_, hid⟩
  · exact absurd hrs (Nat.ne_of_lt hlt)
  · exact hid

/-! ### Theorem 5 — totality / clean terminal -/

/-- `select` is `none` exactly when nothing pends (the pending sublist is
empty). -/
theorem select_eq_none_iff {streams : List Stream} :
    select streams = none ↔ streams.filter hasPending = [] := bestOf_eq_none

/-- The empty connection terminates cleanly. -/
theorem select_nil : select [] = none := rfl

/-- If no stream has pending data, the scheduler selects nothing (clean
terminal). -/
theorem select_none_of_no_pending {streams : List Stream}
    (h : ∀ s ∈ streams, s.hasPending = false) : select streams = none := by
  rw [select_eq_none_iff]
  induction streams with
  | nil => rfl
  | cons a rest ih =>
    rw [List.filter_cons]
    have ha : hasPending a = false := h a (List.mem_cons_self _ _)
    simp only [ha, Bool.false_eq_true, if_false]
    exact ih (fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- Conversely, if some stream pends, the scheduler makes a selection: totality
in the productive direction. -/
theorem select_isSome_of_pending {streams : List Stream}
    (h : ∃ s ∈ streams, s.hasPending = true) : (select streams).isSome := by
  obtain ⟨s, hs, hp⟩ := h
  have hmem : s ∈ streams.filter hasPending := List.mem_filter.mpr ⟨hs, hp⟩
  have hne : streams.filter hasPending ≠ [] := by
    intro hnil; rw [hnil] at hmem; exact (List.not_mem_nil _) hmem
  cases hsel : select streams with
  | none => exact absurd (select_eq_none_iff.mp hsel) hne
  | some _ => rfl

/-! ## Checker-verified vectors -/

/-- Urgency dominates: u=0 is served before u=5 (both pending). -/
example :
    select [⟨7, ⟨5, false⟩, [1]⟩, ⟨3, ⟨0, true⟩, [2]⟩] = some ⟨3, ⟨0, true⟩, [2]⟩ := rfl
/-- At equal urgency, non-incremental precedes incremental. -/
example :
    select [⟨9, ⟨3, true⟩, [1]⟩, ⟨4, ⟨3, false⟩, [2]⟩] = some ⟨4, ⟨3, false⟩, [2]⟩ := rfl
/-- Equal priority: least id wins. -/
example :
    select [⟨8, ⟨3, false⟩, [1]⟩, ⟨2, ⟨3, false⟩, [2]⟩] = some ⟨2, ⟨3, false⟩, [2]⟩ := rfl
/-- An idle (empty-queue) higher-priority stream is skipped. -/
example :
    select [⟨1, ⟨0, false⟩, []⟩, ⟨2, ⟨6, false⟩, [9]⟩] = some ⟨2, ⟨6, false⟩, [9]⟩ := rfl
/-- Nothing pending: clean terminal. -/
example : select [⟨1, ⟨0, false⟩, []⟩] = none := rfl

end Mux
