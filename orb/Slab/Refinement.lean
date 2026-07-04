/-
Slab refinement: the concrete table denotes a partial map, and the table
operations commute with the abstraction.

The three theorem groups:

* **Refinement / commutation** — `abs_empty`, `abs_insert`, `abs_remove`,
  `remove_returns`: `Table` operations implement partial-map operations
  through the abstraction function `Table.abs`.
* **Invariant preservation** — `WF.empty`, `WF.insert`, `WF.remove`: the
  coupling invariant survives every operation.
* **Free-list soundness** — `free_disjoint_live`, `live_not_free`,
  `remove_free_nodup`: no live slot is ever on the free list, and no slot is
  freed twice.
-/
import Slab.Basic

namespace Slab

universe u

variable {σ : Type u}

namespace Table

/-! ### Lookup / abstraction commutation -/

@[simp] theorem lookup_empty (fd : Nat) : (empty : Table σ).lookup fd = none :=
  rfl

theorem lookup_insert_self (t : Table σ) (fd : Nat) (v : σ) :
    (t.insert fd v).lookup fd = some v := by
  cases h1 : t.fdIndex fd with
  | some s =>
    rw [insert_replace h1 v]
    simp [lookup, h1]
  | none =>
    cases hf : t.free with
    | cons s rest =>
      rw [insert_pop h1 hf v]
      simp [lookup]
    | nil =>
      rw [insert_fresh h1 hf v]
      simp [lookup]

theorem lookup_insert_ne {t : Table σ} (h : t.WF) {fd fd' : Nat}
    (hne : fd' ≠ fd) (v : σ) :
    (t.insert fd v).lookup fd' = t.lookup fd' := by
  cases h1 : t.fdIndex fd with
  | some s =>
    rw [insert_replace h1 v]
    cases h2 : t.fdIndex fd' with
    | none => simp [lookup, h2]
    | some s' =>
      have hss : s' ≠ s := by
        intro he; subst he
        exact hne (h.index_inj h2 h1)
      simp [lookup, h2, upd_ne t.slots (some v) hss]
  | none =>
    cases hf : t.free with
    | cons s rest =>
      rw [insert_pop h1 hf v]
      cases h2 : t.fdIndex fd' with
      | none => simp [lookup, upd_ne t.fdIndex (some s) hne, h2]
      | some s' =>
        have hdead : t.slots s = none :=
          (h.free_dead s (by rw [hf]; exact List.mem_cons_self s rest)).2
        have hss : s' ≠ s := by
          intro he; subst he
          have hlive := (h.index_live fd' s' h2).2.1
          rw [hdead] at hlive
          simp at hlive
        simp [lookup, upd_ne t.fdIndex (some s) hne, h2,
          upd_ne t.slots (some v) hss]
    | nil =>
      rw [insert_fresh h1 hf v]
      cases h2 : t.fdIndex fd' with
      | none => simp [lookup, upd_ne t.fdIndex (some t.nSlots) hne, h2]
      | some s' =>
        have hs' := (h.index_live fd' s' h2).1
        have hss : s' ≠ t.nSlots := by omega
        simp [lookup, upd_ne t.fdIndex (some t.nSlots) hne, h2,
          upd_ne t.slots (some v) hss]

theorem lookup_remove_self (t : Table σ) (fd : Nat) :
    (t.remove fd).2.lookup fd = none := by
  cases h1 : t.fdIndex fd with
  | none =>
    rw [remove_none h1]
    simp [lookup, h1]
  | some s =>
    rw [remove_some h1]
    simp [lookup]

theorem lookup_remove_ne {t : Table σ} (h : t.WF) {fd fd' : Nat}
    (hne : fd' ≠ fd) :
    (t.remove fd).2.lookup fd' = t.lookup fd' := by
  cases h1 : t.fdIndex fd with
  | none => rw [remove_none h1]
  | some s =>
    rw [remove_some h1]
    cases h2 : t.fdIndex fd' with
    | none => simp [lookup, upd_ne t.fdIndex none hne, h2]
    | some s' =>
      have hss : s' ≠ s := by
        intro he; subst he
        exact hne (h.index_inj h2 h1)
      simp [lookup, upd_ne t.fdIndex none hne, h2, upd_ne t.slots none hss]

/-- `remove` returns exactly the abstract binding. -/
theorem remove_returns (t : Table σ) (fd : Nat) :
    (t.remove fd).1 = t.lookup fd := by
  cases h1 : t.fdIndex fd with
  | none => rw [remove_none h1]; simp [lookup, h1]
  | some s => rw [remove_some h1]; simp [lookup, h1]

@[simp] theorem abs_empty : (empty : Table σ).abs = fun _ => none :=
  rfl

/-- `insert` commutes with the abstraction: it is point update on the map. -/
theorem abs_insert {t : Table σ} (h : t.WF) (fd : Nat) (v : σ) :
    (t.insert fd v).abs = upd t.abs fd (some v) := by
  funext fd'
  by_cases he : fd' = fd
  · subst he
    simp [abs, lookup_insert_self]
  · simp [abs, lookup_insert_ne h he v, upd_ne t.abs (some v) he]

/-- `remove` commutes with the abstraction: it is point deletion on the map. -/
theorem abs_remove {t : Table σ} (h : t.WF) (fd : Nat) :
    (t.remove fd).2.abs = upd t.abs fd none := by
  funext fd'
  by_cases he : fd' = fd
  · subst he
    simp [abs, lookup_remove_self]
  · simp [abs, lookup_remove_ne h he, upd_ne t.abs none he]

/-! ### Invariant preservation -/

protected theorem WF.empty : (empty : Table σ).WF where
  index_live := by intro fd s h; simp [Table.empty] at h
  live_indexed := by intro s h; simp [Table.empty] at h
  slots_bounded := by intros; rfl
  free_dead := by intro s h; simp [Table.empty] at h
  free_nodup := List.Pairwise.nil
  dead_free := by intro s h; simp [Table.empty] at h
  count_eq := rfl

protected theorem WF.insert {t : Table σ} (h : t.WF) (fd : Nat) (v : σ) :
    (t.insert fd v).WF := by
  cases h1 : t.fdIndex fd with
  | some s =>
    obtain ⟨hs_lt, hs_some, hs_fd⟩ := h.index_live fd s h1
    rw [insert_replace h1 v]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · -- index_live
      intro fd' s' h2
      obtain ⟨b1, b2, b3⟩ := h.index_live fd' s' h2
      refine ⟨b1, ?_, b3⟩
      by_cases hss : s' = s
      · rw [hss, upd_self]; rfl
      · rw [upd_ne t.slots (some v) hss]; exact b2
    · -- live_indexed
      intro s' hlt hsome
      by_cases hss : s' = s
      · rw [hss, hs_fd]; exact h1
      · rw [upd_ne t.slots (some v) hss] at hsome
        exact h.live_indexed s' hlt hsome
    · -- slots_bounded
      intro s' hge
      have hss : s' ≠ s := by omega
      rw [upd_ne t.slots (some v) hss]
      exact h.slots_bounded s' hge
    · -- free_dead
      intro s' hmem
      obtain ⟨b1, b2⟩ := h.free_dead s' hmem
      have hss : s' ≠ s := by
        intro he; rw [he] at b2; rw [b2] at hs_some; simp at hs_some
      exact ⟨b1, by rw [upd_ne t.slots (some v) hss]; exact b2⟩
    · -- free_nodup
      exact h.free_nodup
    · -- dead_free
      intro s' hlt hnone
      have hss : s' ≠ s := by
        intro he; rw [he, upd_self] at hnone; exact Option.noConfusion hnone
      rw [upd_ne t.slots (some v) hss] at hnone
      exact h.dead_free s' hlt hnone
    · -- count_eq
      rw [liveCount_upd_some_of_some v hs_lt hs_some]
      exact h.count_eq
  | none =>
    cases hf : t.free with
    | cons s rest =>
      have hmem : s ∈ t.free := by rw [hf]; exact List.mem_cons_self s rest
      obtain ⟨hs_lt, hs_dead⟩ := h.free_dead s hmem
      have hnodup := h.free_nodup
      rw [hf, List.nodup_cons] at hnodup
      rw [insert_pop h1 hf v]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · -- index_live
        intro fd' s' h2
        by_cases hfd : fd' = fd
        · rw [hfd, upd_self] at h2
          obtain rfl : s = s' := Option.some.inj h2
          refine ⟨hs_lt, by rw [upd_self]; rfl, by rw [upd_self, hfd]⟩
        · rw [upd_ne t.fdIndex (some s) hfd] at h2
          obtain ⟨b1, b2, b3⟩ := h.index_live fd' s' h2
          have hss : s' ≠ s := by
            intro he; rw [he, hs_dead] at b2; simp at b2
          exact ⟨b1, by rw [upd_ne t.slots (some v) hss]; exact b2,
            by rw [upd_ne t.slotFd fd hss]; exact b3⟩
      · -- live_indexed
        intro s' hlt hsome
        by_cases hss : s' = s
        · rw [hss]; simp
        · rw [upd_ne t.slots (some v) hss] at hsome
          have hidx := h.live_indexed s' hlt hsome
          have hfd' : t.slotFd s' ≠ fd := by
            intro he; rw [he, h1] at hidx; exact Option.noConfusion hidx
          rw [upd_ne t.slotFd fd hss, upd_ne t.fdIndex (some s) hfd']
          exact hidx
      · -- slots_bounded
        intro s' hge
        have hss : s' ≠ s := by omega
        rw [upd_ne t.slots (some v) hss]
        exact h.slots_bounded s' hge
      · -- free_dead
        intro s' hmem'
        have hmem'' : s' ∈ t.free := by
          rw [hf]; exact List.mem_cons_of_mem s hmem'
        obtain ⟨b1, b2⟩ := h.free_dead s' hmem''
        have hss : s' ≠ s := by
          intro he; rw [he] at hmem'; exact hnodup.1 hmem'
        exact ⟨b1, by rw [upd_ne t.slots (some v) hss]; exact b2⟩
      · -- free_nodup
        exact hnodup.2
      · -- dead_free
        intro s' hlt hnone
        have hss : s' ≠ s := by
          intro he; rw [he, upd_self] at hnone; exact Option.noConfusion hnone
        rw [upd_ne t.slots (some v) hss] at hnone
        have hmem' := h.dead_free s' hlt hnone
        rw [hf] at hmem'
        cases List.mem_cons.mp hmem' with
        | inl he => exact absurd he hss
        | inr hin => exact hin
      · -- count_eq
        rw [liveCount_upd_some_of_none v hs_lt hs_dead]
        have := h.count_eq
        omega
    | nil =>
      rw [insert_fresh h1 hf v]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · -- index_live
        intro fd' s' h2
        by_cases hfd : fd' = fd
        · rw [hfd, upd_self] at h2
          obtain rfl : t.nSlots = s' := Option.some.inj h2
          refine ⟨Nat.lt_succ_self _, by rw [upd_self]; rfl, by rw [upd_self, hfd]⟩
        · rw [upd_ne t.fdIndex (some t.nSlots) hfd] at h2
          obtain ⟨b1, b2, b3⟩ := h.index_live fd' s' h2
          have hss : s' ≠ t.nSlots := by omega
          exact ⟨by omega, by rw [upd_ne t.slots (some v) hss]; exact b2,
            by rw [upd_ne t.slotFd fd hss]; exact b3⟩
      · -- live_indexed
        intro s' hlt hsome
        by_cases hss : s' = t.nSlots
        · rw [hss]; simp
        · have hlt' : s' < t.nSlots := by omega
          rw [upd_ne t.slots (some v) hss] at hsome
          have hidx := h.live_indexed s' hlt' hsome
          have hfd' : t.slotFd s' ≠ fd := by
            intro he; rw [he, h1] at hidx; exact Option.noConfusion hidx
          rw [upd_ne t.slotFd fd hss, upd_ne t.fdIndex (some t.nSlots) hfd']
          exact hidx
      · -- slots_bounded
        intro s' hge
        have hss : s' ≠ t.nSlots := by omega
        rw [upd_ne t.slots (some v) hss]
        exact h.slots_bounded s' (by omega)
      · -- free_dead
        intro s' hmem'
        exact absurd hmem' (List.not_mem_nil s')
      · -- free_nodup
        exact List.Pairwise.nil
      · -- dead_free
        intro s' hlt hnone
        by_cases hss : s' = t.nSlots
        · rw [hss, upd_self] at hnone
          exact Option.noConfusion hnone
        · have hlt' : s' < t.nSlots := by omega
          rw [upd_ne t.slots (some v) hss] at hnone
          have hmem' := h.dead_free s' hlt' hnone
          rw [hf] at hmem'
          exact hmem'
      · -- count_eq
        have hstep : liveCount (upd t.slots t.nSlots (some v)) (t.nSlots + 1)
            = liveCount (upd t.slots t.nSlots (some v)) t.nSlots
              + (if ((upd t.slots t.nSlots (some v)) t.nSlots).isSome then 1 else 0) :=
          rfl
        rw [hstep, liveCount_upd_ge t.slots (some v) (Nat.le_refl _), upd_self]
        simp [h.count_eq]

protected theorem WF.remove {t : Table σ} (h : t.WF) (fd : Nat) :
    (t.remove fd).2.WF := by
  cases h1 : t.fdIndex fd with
  | none => rw [remove_none h1]; exact h
  | some s =>
    obtain ⟨hs_lt, hs_some, hs_fd⟩ := h.index_live fd s h1
    rw [remove_some h1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · -- index_live
      intro fd' s' h2
      by_cases hfd : fd' = fd
      · rw [hfd, upd_self] at h2
        exact Option.noConfusion h2
      · rw [upd_ne t.fdIndex none hfd] at h2
        obtain ⟨b1, b2, b3⟩ := h.index_live fd' s' h2
        have hss : s' ≠ s := by
          intro he; rw [he] at h2; exact hfd (h.index_inj h2 h1)
        exact ⟨b1, by rw [upd_ne t.slots none hss]; exact b2, b3⟩
    · -- live_indexed
      intro s' hlt hsome
      have hss : s' ≠ s := by
        intro he; rw [he, upd_self] at hsome; simp at hsome
      rw [upd_ne t.slots none hss] at hsome
      have hidx := h.live_indexed s' hlt hsome
      have hfd' : t.slotFd s' ≠ fd := by
        intro he; rw [he, h1] at hidx
        exact hss (Option.some.inj hidx).symm
      rw [upd_ne t.fdIndex none hfd']
      exact hidx
    · -- slots_bounded
      intro s' hge
      by_cases hss : s' = s
      · rw [hss, upd_self]
      · rw [upd_ne t.slots none hss]
        exact h.slots_bounded s' hge
    · -- free_dead
      intro s' hmem
      cases List.mem_cons.mp hmem with
      | inl he =>
        exact ⟨by rw [he]; exact hs_lt, by rw [he, upd_self]⟩
      | inr hin =>
        obtain ⟨b1, b2⟩ := h.free_dead s' hin
        by_cases hss : s' = s
        · exact ⟨b1, by rw [hss, upd_self]⟩
        · exact ⟨b1, by rw [upd_ne t.slots none hss]; exact b2⟩
    · -- free_nodup
      rw [List.nodup_cons]
      refine ⟨?_, h.free_nodup⟩
      intro hmem
      have hd := (h.free_dead s hmem).2
      rw [hd] at hs_some
      simp at hs_some
    · -- dead_free
      intro s' hlt hnone
      by_cases hss : s' = s
      · rw [hss]; exact List.mem_cons_self s t.free
      · rw [upd_ne t.slots none hss] at hnone
        exact List.mem_cons_of_mem s (h.dead_free s' hlt hnone)
    · -- count_eq
      have hlc := liveCount_upd_none hs_lt hs_some
      have hc := h.count_eq
      omega

/-! ### Free-list soundness (named corollaries) -/

/-- No live slot is ever on the free list. -/
theorem free_disjoint_live {t : Table σ} (h : t.WF) {s : Nat}
    (hs : s ∈ t.free) : t.slots s = none :=
  (h.free_dead s hs).2

/-- A slot currently backing a connection is not on the free list —
freeing it (once) cannot be a double free. -/
theorem live_not_free {t : Table σ} (h : t.WF) {fd s : Nat}
    (h1 : t.fdIndex fd = some s) : s ∉ t.free := by
  intro hmem
  have hdead := (h.free_dead s hmem).2
  have hsome := (h.index_live fd s h1).2.1
  rw [hdead] at hsome
  simp at hsome

/-- The free list never acquires duplicates: no double free. -/
theorem remove_free_nodup {t : Table σ} (h : t.WF) (fd : Nat) :
    (t.remove fd).2.free.Nodup :=
  (h.remove fd).free_nodup

/-! ### Cached-count corollaries -/

theorem lookup_none_iff_index {t : Table σ} (h : t.WF) (fd : Nat) :
    t.lookup fd = none ↔ t.fdIndex fd = none := by
  constructor
  · intro hn
    cases h1 : t.fdIndex fd with
    | none => rfl
    | some s =>
      have hsome := (h.index_live fd s h1).2.1
      rw [lookup, h1] at hn
      simp at hn
      rw [hn] at hsome
      simp at hsome
  · intro hn
    rw [lookup, hn]
    rfl

theorem count_insert_new {t : Table σ} (h : t.WF) {fd : Nat}
    (h1 : t.lookup fd = none) (v : σ) :
    (t.insert fd v).count = t.count + 1 := by
  have hidx := (lookup_none_iff_index h fd).mp h1
  cases hf : t.free with
  | cons s rest => rw [insert_pop hidx hf v]
  | nil => rw [insert_fresh hidx hf v]

theorem count_insert_replace {t : Table σ} {fd : Nat} {w : σ}
    (h1 : t.lookup fd = some w) (v : σ) :
    (t.insert fd v).count = t.count := by
  cases hidx : t.fdIndex fd with
  | none => rw [lookup, hidx] at h1; exact Option.noConfusion h1
  | some s => rw [insert_replace hidx v]

theorem remove_miss {t : Table σ} (h : t.WF) {fd : Nat}
    (h1 : t.lookup fd = none) : t.remove fd = (none, t) :=
  remove_none ((lookup_none_iff_index h fd).mp h1)

theorem count_remove_hit {t : Table σ} (h : t.WF) {fd : Nat} {w : σ}
    (h1 : t.lookup fd = some w) :
    (t.remove fd).2.count + 1 = t.count := by
  cases hidx : t.fdIndex fd with
  | none => rw [lookup, hidx] at h1; exact Option.noConfusion h1
  | some s =>
    obtain ⟨hs_lt, hs_some, _⟩ := h.index_live fd s hidx
    have hpos : 0 < liveCount t.slots t.nSlots := liveCount_pos hs_lt hs_some
    rw [remove_some hidx]
    show t.count - 1 + 1 = t.count
    have := h.count_eq
    omega

end Table

end Slab
