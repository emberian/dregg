/-
# Dregg2.Crypto.Deriv.Monotone — Stage 3: `toSumSubsets_monotone` (the LAST finiteness residual).

The multi-step finiteness `steps r n ⊆[≅] ⊕(pieces r)` chains the single-step closure
(`step_to_pieces`, banked) through `pieces`-MONOTONICITY: a `≅`-subset relation between two lists
lifts to their `⊕`-sums (`toSumSubsets_monotone`). That lift is the `Permute.lean` nodup /
permutation-erase combinatorics block — purely generic list reasoning (no `PredRE`, no semantics).
This file ports it (ITP'25 `Permute.lean`, lines ~109-376, read-only blueprint), updated for the
v4.30 mathlib `List` API. It is the LAST un-ported piece before `finiteness` closes.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Permute

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Crypto.Deriv.Combinatorics
open PredRE (Sim bot)

namespace PredRE

/-! ## Decidable equality on `PredRE` — CLASSICAL.

The ITP'25 nodup/erase block uses `List.erase`/`diff`/`permutations'Aux`, which need `DecidableEq` on
the element type. dregg's `Pred` has NO decidable equality (its opaque `Custom{vk_hash}` / rich
`StateConstraint` atoms are not `DecidableEq`-derivable). We supply a CLASSICAL `DecidableEq PredRE`:
this keeps `#assert_axioms` clean (dregg's allow-list includes `Classical.choice`), and is sound for
the finiteness COUNT — the count is purely existential (`∃ xs ∈ neSubsets …`), so a classical
equality on the syntactic state changes nothing semantic. -/
noncomputable instance : DecidableEq PredRE := Classical.typeDecidableEq PredRE

/-! ## `Sim`-specialized `subset_up_to` helpers. -/

theorem subset_to_subset_up_to_sim {xs ys : List PredRE} (h : xs ⊆ ys) :
    xs ⊆[ (· ≅ ·) ] ys := subset_to_subset_up_to (fun _ => Sim.rfl) h

theorem subset_up_to_trans_sim {xs ys zs : List PredRE}
    (h : xs ⊆[ (· ≅ ·) ] ys) (h1 : ys ⊆[ (· ≅ ·) ] zs) : xs ⊆[ (· ≅ ·) ] zs :=
  subset_up_to_trans (fun _ _ _ g1 g2 => Sim.trans g1 g2) h h1

/-! ## `subset_sim_toSum` — a `≅`-subset's `toSum` is `≅` a genuine subset's `toSum`. -/

theorem subset_sim_toSum {xs ys : List PredRE} (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
    ∃ us : List PredRE, us ⊆ ys ∧ us ≠ [] ∧ Sim (toSum xs) (toSum us) := by
  match xs with
  | [] => contradiction
  | [x] =>
    simp only [SubsetUpTo, mem_singleton, MemUpTo, forall_eq] at h
    have ⟨y, eq, mem⟩ := h
    exact ⟨[y], by simp only [subset_def, mem_singleton, forall_eq]; exact mem, cons_ne_nil y [], eq⟩
  | x :: x' :: xs =>
    have ⟨hx, h'⟩ := forall_mem_cons.mp h
    have ⟨us, sb, eq1, eq2⟩ := subset_sim_toSum (cons_ne_nil x' xs) h'
    have ⟨y, p1, p2⟩ := hx
    exact ⟨y::us, by simp only [subset_def, mem_cons, forall_eq_or_imp]; exact ⟨p2, sb⟩,
           cons_ne_nil y us, toSum_alt_cong (cons_ne_nil x' xs) eq1 p1 eq2⟩

/-! ## `nodup_equiv` — `toSum` is `≅` a NODUP subset's `toSum` (dedup via the ACI laws). -/

theorem deconstruct {x : PredRE} {ys : List PredRE} (h1 : x ∈ ys) :
    ∃ ys1 ys2, ys = ys1 ++ x::ys2 :=
  match ys with
  | [] => (mem_iff_append.mp h1).elim fun s ⟨t, ht⟩ => ⟨s, t, ht⟩
  | y::ys =>
    match mem_cons.mp h1 with
    | Or.inl g1 => ⟨[], ys, congrFun (congrArg cons g1.symm) ys⟩
    | Or.inr g1 =>
      have ⟨i1, i2, i3⟩ := deconstruct g1
      ⟨y::i1, i2, congrArg (cons y) i3⟩

theorem nodup_swap {x : PredRE} {z1 z2 : List PredRE}
    (h : (z1 ++ x :: z2).Nodup) : (x :: z1 ++ z2).Nodup := by
  -- (z1 ++ x :: z2) is a permutation of (x :: z1 ++ z2); Nodup is permutation-invariant.
  have hp : (z1 ++ x :: z2) ~ (x :: z1 ++ z2) := by
    simp only [cons_append]
    exact (List.perm_middle (a := x) (l₁ := z1) (l₂ := z2))
  exact (hp.nodup_iff).mp h

theorem nodup_equiv (xs : List PredRE) (ne : xs ≠ []) :
    ∃ zs : List PredRE, Nodup zs ∧ zs ≠ [] ∧ zs ⊆ xs ∧ Sim (toSum xs) (toSum zs) := by
  match xs with
  | []      => simp only [ne_eq, not_true_eq_false] at ne
  | x :: [] => exact ⟨[x], nodup_singleton x, ne, fun _ ha => ha, Sim.rfl⟩
  | x :: x1 :: xs =>
    have ⟨zs, nd, sb, fs1, fs2⟩ := nodup_equiv (x1::xs) (cons_ne_nil x1 xs)
    by_cases h : x ∈ zs
    · have ⟨z1, z2, z3⟩ := deconstruct h
      subst z3
      refine ⟨x::z1++z2, nodup_swap nd, cons_ne_nil _ _, ?_, ?_⟩
      · have t1 : z1 ⊆ x :: x1 :: xs := by
          simp only [subset_def, mem_cons]; intro a ha
          simp only [subset_def, mem_append, mem_cons] at fs1
          exact Or.inr (fs1 (Or.inl ha))
        have t2 : z2 ⊆ x :: x1 :: xs := by
          simp only [subset_def, mem_cons]; intro a ha
          simp only [subset_def, mem_append, mem_cons] at fs1
          exact Or.inr (fs1 (Or.inr (Or.inr ha)))
        simp only [cons_append, cons_subset, mem_cons, true_or, append_subset, true_and]
        exact ⟨t1, t2⟩
      · simp only [toSum, cons_append]
        apply Sim.trans (Sim.altCong Sim.rfl fs2)
        match z2 with
        | [] =>
          match z1 with
          | [] => exact Sim.idem
          | z1a::z1b =>
            apply Sim.trans (Sim.altCong Sim.rfl (toSum_append (cons_ne_nil z1a z1b) (cons_ne_nil x [])))
            simp only [append_nil]
            exact Sim.dedup
        | _::_ =>
          match z1 with
          | [] => exact Sim.trans (Sim.sym Sim.assoc) (Sim.trans (Sim.altCong Sim.idem Sim.rfl) Sim.rfl)
          | z1a::z1b =>
            apply Sim.trans (Sim.altCong Sim.rfl (toSum_append (cons_ne_nil z1a z1b)
                        (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])))
            apply Sim.trans (Sim.sym Sim.assoc)
            apply Sim.trans (Sim.sym Sim.assoc)
            apply Sim.trans (Sim.altCong Sim.assoc Sim.rfl)
            apply Sim.trans (Sim.altCong Sim.dedup Sim.rfl)
            exact Sim.trans Sim.assoc (Sim.trans (Sim.altCong Sim.rfl (Sim.sym (toSum_append
              (cons_ne_nil z1a z1b) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])))) Sim.rfl)
    · exact ⟨x :: zs, by simp only [nodup_cons]; exact ⟨h, nd⟩,
             by simp only [ne_eq, reduceCtorEq, not_false_eq_true],
             by simp only [cons_subset, mem_cons, true_or, true_and]; exact subset_cons_of_subset x fs1,
             toSum_alt_cong (cons_ne_nil x1 xs) sb Sim.rfl fs2⟩

theorem toSumnodup_equiv {xs ys : List PredRE}
    (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
    ∃ us : List PredRE, Nodup us ∧ us ≠ [] ∧ us ⊆ ys ∧ Sim (toSum xs) (toSum us) :=
  have ⟨xs', xs'_ys, xs'_ne, xs_xs'⟩ := subset_sim_toSum ne h
  have ⟨us, nd, us_xs', p, xs'_us⟩ := nodup_equiv xs' xs'_ne
  ⟨us, nd, us_xs', fun _ hx => xs'_ys (p hx), Sim.trans xs_xs' xs'_us⟩

/-! ## The erase / permutation block — `nodup_subset_to_neSubsets` (a NODUP subset is in `neSubsets`). -/

theorem perms_erase_helper {y : PredRE} {xs : List PredRE}
    (h1 : y ∈ xs) : xs ∈ permutations'Aux y ((xs).erase y) :=
  match xs with
  | [] => False.elim (not_mem_nil h1)
  | x::[] => by
    simp only [mem_singleton] at h1
    subst h1
    simp only [erase_cons_head, permutations'Aux, mem_singleton]
  | x1::x2::xs => by
    match mem_cons.mp h1 with
    | Or.inl h2 =>
      subst h2
      simp only [erase_cons_head, permutations'Aux, mem_cons, mem_map, true_or]
    | Or.inr h2 =>
      unfold List.erase
      by_cases g : x1 == y
      · simp only [g, permutations'Aux, mem_cons, cons.injEq, and_true, mem_map, exists_eq_right_right]
        simp only [beq_iff_eq.mp g, true_or]
      · simp only [g, permutations'Aux, mem_cons, cons.injEq, cons_injective, mem_map_of_injective]
        simp only [beq_iff_eq] at g
        simp only [g, false_and, false_or]
        exact perms_erase_helper (xs := (x2::xs)) h2

theorem subset_cons {xs : List PredRE} {x1 : PredRE} {ys : List PredRE}
    (h : xs ⊆ x1 :: ys) (not_in : x1 ∉ xs) : xs ⊆ ys := fun e he =>
  match mem_cons.mp (h he) with
  | Or.inl h1 => by subst h1; contradiction
  | Or.inr h1 => h1

theorem erase_cons1 {xs : List PredRE} {y x1 : PredRE} {ys : List PredRE}
    (hh1 : y ∈ (x1::xs)) (hh : (x1 :: xs).Nodup) (h : (x1 :: xs).erase y ⊆ y :: ys) :
    (x1 :: xs).erase y ⊆ ys := by
  match xs with
  | [] =>
    simp only [mem_singleton] at hh1
    subst hh1
    rw [erase_cons_head y []]
    exact nil_subset ys
  | x2::xs =>
    unfold List.erase at h
    by_cases g : x1 == y
    · simp only [g, cons_subset, mem_cons] at h
      unfold List.erase; simp only [g, cons_subset]
      obtain ⟨k1, k2⟩ := h
      match k1 with
      | Or.inl k =>
        subst k; simp only [beq_iff_eq] at g; subst g
        simp_all only [nodup_cons, mem_cons, true_or, not_true_eq_false, false_and]
      | Or.inr k =>
        simp only [k, true_and]
        simp only [beq_iff_eq] at g
        subst g
        simp only [nodup_cons, mem_cons, not_or] at hh
        exact subset_cons k2 hh.1.2
    · simp only [g, cons_subset, mem_cons] at h
      unfold List.erase
      simp only [g, cons_subset]
      simp only [beq_iff_eq] at g
      simp only [mem_cons] at hh1
      obtain ⟨k1, k2⟩ := h
      match hh1 with
      | Or.inl j => subst j; simp only [not_true_eq_false] at g
      | Or.inr j =>
        match k1 with
        | Or.inl k => subst k; exact False.elim (g rfl)
        | Or.inr k => exact ⟨k, erase_cons1 (ys := ys) (mem_cons.mpr j) (Nodup.of_cons hh) k2⟩

theorem nodup_subset_to_neSubsets {xs ys : List PredRE}
    (h : xs ≠ []) (sb : xs ⊆ ys) (nd : Nodup xs) : xs ∈ neSubsets ys := by
  match ys with
  | [] => simp only [subset_nil] at sb; contradiction
  | y::ys =>
    by_cases g : y ∈ xs
    · match xs with
      | [] => simp only [not_mem_nil] at g
      | x::[] =>
        simp only [mem_cons, not_mem_nil, or_false] at g
        subst g
        exact mem_of_mem_head? rfl
      | x1::x2::xs =>
        have f := Subset.trans (diff_subset (x1::x2::xs) [y]) sb
        have f' : (x1::x2::xs).diff [y] ⊆ ys := by
          simp only [diff_cons, diff_nil]
          simp only [diff_cons, diff_nil] at f
          exact erase_cons1 g nd f
        have f₁ : Nodup ((x1::x2::xs).diff [y]) := Nodup.diff nd
        have f₂ : (x1::x2::xs).diff [y] ≠ [] := by
          by_cases g1 : x1 = y
          · subst g1
            simp only [diff_cons, erase_cons_head, diff_nil, ne_eq, reduceCtorEq, not_false_eq_true]
          · simp only [diff_cons, diff_nil, ne_eq, erase_eq_nil_iff, reduceCtorEq, cons.injEq,
              and_false, or_self, not_false_eq_true]
        have ih := nodup_subset_to_neSubsets f₂ f' f₁
        simp only [neSubsets, diff_cons, diff_nil, mem_flatten, mem_map,
          exists_exists_and_eq_and] at ih
        obtain ⟨i1, i2, i3⟩ := ih
        simp only [neSubsets, neSublists, cons_append, nil_append, map_cons, permutations',
          flatMap_cons, permutations'Aux, flatMap_nil, append_nil, map_append, map_map,
          flatten_cons, flatten_append, mem_cons, cons.injEq, reduceCtorEq, and_false, mem_append,
          mem_flatten, mem_map, Function.comp_apply, exists_exists_and_eq_and, mem_flatMap,
          false_or]
        exact Or.inl ⟨i1, i2, (x1::x2::xs).erase y, i3, perms_erase_helper g⟩
    · exact neSubsets_extend (nodup_subset_to_neSubsets h (subset_cons sb g) nd)

theorem nodup_subset_to_neSubset {xs ys : List PredRE}
    (h : xs ≠ []) (sb : xs ⊆ ys) (nd : Nodup xs) : toSum xs ∈ ⊕ys :=
  mem_map_of_mem (nodup_subset_to_neSubsets h sb nd)

/-! ## `toSumSubsets_monotone` — the lift, the last finiteness residual. -/

theorem neSublist_to_subset {xs ys : List PredRE} (h : xs ∈ neSublists ys) : xs ⊆ ys :=
  Sublist.subset (neSublists_characterization.mp h).1

theorem neSubset_to_sublist {xs ys : List PredRE} (h : xs ∈ neSubsets ys) : xs ⊆ ys := by
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and] at h
  obtain ⟨a, ha, pa⟩ := h
  simp only [subset_def]; intro x hx
  exact neSublist_to_subset ha ((Perm.mem_iff (mem_permutations'.mp pa)).mp hx)

theorem subset_sim_perm {xs ys : List PredRE}
    (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) : (toSum xs) ∈[ (· ≅ ·) ] ⊕ys :=
  have ⟨us, ndup, ne, us_ys, ftoSum⟩ := toSumnodup_equiv ne h
  ⟨toSum us, ftoSum, nodup_subset_to_neSubset ne us_ys ndup⟩

theorem toSumSubsets_to_neSubset {x : PredRE} {xs : List PredRE} (h : x ∈ ⊕xs) :
    ∃ zs, zs ≠ [] ∧ x = toSum zs ∧ zs ⊆ xs := by
  have ⟨zs, zs_mem, zs_eq⟩ := mem_map.mp h
  match zs with
  | [] => have := neSubsets_ne zs_mem; simp only [ne_eq, not_true_eq_false] at this
  | z::zs => exact ⟨z::zs, cons_ne_nil z zs, zs_eq.symm, neSubset_to_sublist zs_mem⟩

/-- **`toSumSubsets_monotone`** — `xs ⊆[≅] ys → ⊕xs ⊆[≅] ⊕ys`. The lift that drives multi-step
finiteness. ITP'25 `toSumSubsets_monotone`. -/
theorem toSumSubsets_monotone {xs ys : List PredRE}
    (h : xs ⊆[ (· ≅ ·) ] ys) : ⊕xs ⊆[ (· ≅ ·) ] ⊕ys := fun x x_mem => by
  have ⟨zs, p1, p2, p3⟩ := toSumSubsets_to_neSubset x_mem; subst p2
  have zsxs := subset_to_subset_up_to_sim p3
  exact subset_sim_perm p1 (subset_up_to_trans_sim zsxs h)

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.subset_sim_toSum,
  Dregg2.Crypto.Deriv.PredRE.nodup_equiv,
  Dregg2.Crypto.Deriv.PredRE.nodup_subset_to_neSubsets,
  Dregg2.Crypto.Deriv.PredRE.toSumSubsets_monotone
]
