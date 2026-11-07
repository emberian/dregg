/-
# Dregg2.Crypto.Deriv.AciComplete — FRAGMENT COMPLETENESS of `normalize`, and the
# NON-COMMUTATIVITY of `alt` under `≅` as a machine-checked COROLLARY.

`AciNormal.lean` argues in PROSE that `Sim`'s three `alt` laws (`assoc`, `idem`, `dedup`) are the
identities of a **left regular band** (`x(yz)=(xy)z`, `xx=x`, `xyx=xy`) and hence that
`alt a b ≅ alt b a` is NOT derivable — the fact the whole "order-preserving first-occurrence dedup,
never sort" design rests on. That argument is a model-theoretic sketch about the FREE left regular
band; nothing in it was checked. This module replaces it with theorems.

## What is proved

1. **`sim_key`** — the *first-occurrence disjunct sequence* is a `Sim`-INVARIANT on the pure-`alt`
   fragment. Stated as: the partial canonical key `key : PredRE → Option (List PredRE)` is constant
   on `≅`-classes, for EVERY `R S : PredRE` (no side condition — outside the fragment `key` is
   `none` on both sides, which is how the star/cat blind spots are absorbed honestly).

2. **`sim_normalize_eq`** — FRAGMENT COMPLETENESS:
   `Sim R S → Frag R → normalize R = normalize S`, where `Frag R` says every leaf of `R`'s `alt`
   spine is a `reEq`-decidable non-`alt` leaf (`ε`, or `sym p` with `p` in `predBEq`'s fragment).
   `Frag S` is not assumed — it FOLLOWS (`sim_frag`).

3. **`normalize_alt_comm_ne` / `not_sim_alt_comm`** — the FALSIFIER: two concrete distinct leaves
   with `normalize (a ⋓ b) ≠ normalize (b ⋓ a)`, hence by (2) `¬ Sim (a ⋓ b) (b ⋓ a)`. `alt` is
   NOT commutative under `≅`, as a theorem. Any normalizer that SORTS disjuncts therefore has an
   obligation that is not merely unproved but UNPROVABLE.

## How the invariance goes through, generator by generator

The key is `ddf ∘ altList` gated by rigidity, and its one structural law is
`ddf_append : ddf (u ++ v) = mergeR (ddf u) (ddf v)` (`mergeR l m = l ++ m.filter (∉ l)`), which
makes `key` a HOMOMORPHISM into the order-preserving-union monoid (`key_alt`). Then:

* `assoc` — a NO-OP on `altList`: both sides flatten to the same list by `List.append_assoc`.
  (Handled at the list level, so no `mergeR`-associativity is ever needed.)
* `idem` — `mergeR l l = l`; `dedup` — `mergeR l (mergeR m l) = mergeR l m`. Both need only that
  each element `y` of `l` satisfies `reEq y y = true`, which is exactly what rigidity buys.
* `altCong` — free, by the homomorphism `key_alt`.
* `negCong`, `interCong`, `catCong` — both sides have a NON-`alt`, NON-rigid head, so `key` is
  `none` on both. This is where the missing `starCong` / right-`catCong` stop mattering: the
  fragment simply does not contain those leaves, and `key` says so rather than guessing.
* `rfl`/`sym`/`trans` — the closure, for free, because the invariant is an EQUALITY of keys.

## THE WIDENING (second half of this file)

`Sim` is now a FULL congruence: `Similarity.lean` carries `catCongR` and `starCong`, and
`sim_null`/`sim_der`/`sim_sound` cover them. The obstruction that capped the first half — "recursing
would be UNSOUND without `starCong` and a right `catCong`" — is therefore GONE, and the second half of
this file takes the widening:

4. **`nrm`** — a RECURSIVE normalizer (`nlist` flattens the spine with every leaf normalized
   recursively; `nrm = foldList ∘ ddf ∘ nlist`), with **`nrm_sim : Sim (nrm R) R`** on ALL of
   `PredRE`.

5. **`sim_nkey`** — the recursive key `nkey R = ddf (nlist R)` (rigidity-gated) is a `Sim`-invariant.
   Where `sim_key` discharged `negCong`/`interCong`/`catCong` by `none = none` (the blind spot), every
   structural congruence now TRANSPORTS ITS IH through a key equation
   (`nkey_star`/`nkey_cat`/`nkey_inter`/`nkey_neg`, into `Option.map`/`bind`).

6. **`sim_nrm_eq`** — WIDENED COMPLETENESS on **`RigidFull`**: every ATOMIC LEAF is `reEq`-decidable,
   the STRUCTURE IS ARBITRARY (`star`/`cat`/`inter`/`neg` nodes are IN). `rigidFull_of_frag` proves
   this strictly contains `Frag`; the `#guard`s exhibit `star (a ⋓ a) ≅ star a`, which is `RigidFull`
   and not `Frag`, being collapsed by `nrm` and NOT by `normalize`.

7. **`simDecide_correct`** — hence `simDecide R S := reEq (nrm R) (nrm S)` is a genuine computable
   DECISION PROCEDURE for `≅` whenever the left argument is `RigidFull`.

## Scope, stated exactly (no laundering)

This is still NOT full `PredRE` completeness. What remains is ONE axis, not two: leaves outside
`predBEq`'s decidable fragment — the `atom` leaf is INSIDE it (`Exec.StateConstraint` carries
`DecidableEq`, `Exec/Program.lean`), and the 07-19 widenings put the compound `not`/`and`/`or`,
the n-ary `allOf`/`anyOf`, and the typed `symMemberOf`/`digFieldEq` leaves inside it too, so the
still-uncovered leaves are only the typed reactive constructors — on which `rigidRE`
is fail-closed by the same one-sided-`reEq` discipline as `AciNormal`. That boundary widens exactly
as far as `predBEq` does, and every theorem below transports unchanged. The STRUCTURAL axis — the one `AciNormal`'s
residual §2 named as blocked — is closed. The residual is restated precisely at the bottom of this
file.

`normalize` itself is UNCHANGED (other modules depend on its shape); `nrm` is a new function beside
it, and the pure-`alt` results (1)–(3) stand on `normalize` exactly as before.

`Similarity.lean` is NOT edited (its `#assert_not_depends_on` pins stand). `sorry`-free.
-/
import Dregg2.Crypto.Deriv.AciNormal

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## Rigid leaves — the fragment's alphabet.

A leaf is RIGID when it is not an `alt` (so it is a genuine spine leaf) and `reEq` decides equality
on it (so first-occurrence deletion is exact, not fail-closed). `star`/`cat`/`inter`/`neg` leaves are
deliberately EXCLUDED: `Sim` can relate them to unequal terms through `altCong` + the missing
`starCong`, which is precisely the blind spot this fragment is carved to avoid. -/

/-- **`rigidLeaf R`** — `R` is a non-`alt` leaf on which `reEq` is a decision procedure. -/
def rigidLeaf : PredRE → Bool
  | .ε     => true
  | .sym p => predBEq p p
  | _      => false

/-- On a rigid leaf, `reEq` is REFLEXIVE — the half `reEq_sound` does not give, and the half the
deduplication laws need. -/
theorem reEq_refl_of_rigid {R : PredRE} (h : rigidLeaf R = true) : reEq R R = true := by
  cases R with
  | ε => rfl
  | sym p => simpa [reEq, rigidLeaf] using h
  | _ => simp [rigidLeaf] at h

/-! ## The order-preserving union monoid. -/

/-- `notMemR l y` — `y` has NO `reEq`-match in `l`. -/
def notMemR (l : List PredRE) (y : PredRE) : Bool := !(l.any (fun x => reEq x y))

/-- **`mergeR l m`** — order-preserving union: keep `l`, then append the elements of `m` that are
new. This is the multiplication of the free left regular band, written on lists. -/
def mergeR (l m : List PredRE) : List PredRE := l ++ m.filter (notMemR l)

/-- **`ddf l`** — first-occurrence deduplication, structurally recursive (the `dedupFirst` of
`AciNormal` is the same function; see `dedupFirst_eq_ddf`). -/
def ddf : List PredRE → List PredRE
  | []      => []
  | x :: xs => x :: (ddf xs).filter (fun y => !reEq x y)

theorem ddf_subset : ∀ {l : List PredRE} {y}, y ∈ ddf l → y ∈ l := by
  intro l
  induction l with
  | nil => intro y h; simp [ddf] at h
  | cons x xs ih =>
    intro y h
    rw [ddf] at h
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih (List.mem_of_mem_filter h))

/-- If every element of `m` already has a match in `l`, the merge adds nothing. -/
theorem filter_notMemR_nil {l m : List PredRE}
    (h : ∀ y ∈ m, ∃ x ∈ l, reEq x y = true) : m.filter (notMemR l) = [] := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
    have hy : notMemR l y = false := by
      obtain ⟨x, hx, hxy⟩ := h y (List.mem_cons_self ..)
      simp only [notMemR, Bool.not_eq_false']
      exact List.any_eq_true.mpr ⟨x, hx, hxy⟩
    rw [List.filter_cons, hy]
    simpa using ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- `mergeR l l = l` for a list of rigid leaves — the `idem` law, on lists. -/
theorem mergeR_self {l : List PredRE} (hr : ∀ y ∈ l, reEq y y = true) : mergeR l l = l := by
  rw [mergeR, filter_notMemR_nil (fun y hy => ⟨y, hy, hr y hy⟩), List.append_nil]

/-- `mergeR l (mergeR m l) = mergeR l m` for a list of rigid leaves — the `dedup` law (`xyx = xy`),
on lists. This is the left-regular-band identity itself. -/
theorem mergeR_dedup {l m : List PredRE} (hr : ∀ y ∈ l, reEq y y = true) :
    mergeR l (mergeR m l) = mergeR l m := by
  have hnil : (l.filter (notMemR m)).filter (notMemR l) = [] :=
    filter_notMemR_nil (fun y hy =>
      ⟨y, List.mem_of_mem_filter hy, hr y (List.mem_of_mem_filter hy)⟩)
  simp only [mergeR, List.filter_append, hnil, List.append_nil]

/-- **`ddf_append`** — the homomorphism law: first-occurrence dedup of a concatenation is the
order-preserving union of the parts' dedups. The whole invariance argument rests on this. -/
theorem ddf_append (u v : List PredRE) : ddf (u ++ v) = mergeR (ddf u) (ddf v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, ddf, mergeR]
    rw [List.filter_eq_self.mpr (fun y _ => by simp [notMemR])]
  | cons x u ih =>
    have hpred : (fun y => !reEq x y && notMemR (ddf u) y)
        = notMemR (x :: (ddf u).filter (fun y => !reEq x y)) := by
      funext y
      by_cases hxy : reEq x y = true
      · simp [notMemR, hxy]
      · have hxy' : reEq x y = false := by simpa using hxy
        have hiff : ((ddf u).filter (fun z => !reEq x z)).any (fun z => reEq z y)
            = (ddf u).any (fun z => reEq z y) := by
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h
            exact List.any_eq_true.mpr ⟨z, List.mem_of_mem_filter hz, hzy⟩
          · intro h
            obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h
            have hzeq : z = y := reEq_sound hzy
            refine List.any_eq_true.mpr ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, hzy⟩
            simp [hzeq, hxy']
        simp [notMemR, hxy', hiff]
    calc ddf (x :: u ++ v)
        = x :: (mergeR (ddf u) (ddf v)).filter (fun y => !reEq x y) := by
          rw [List.cons_append, ddf, ih]
      _ = x :: ((ddf u).filter (fun y => !reEq x y)
              ++ ((ddf v).filter (notMemR (ddf u))).filter (fun y => !reEq x y)) := by
          rw [mergeR, List.filter_append]
      _ = mergeR (ddf (x :: u)) (ddf v) := by
          rw [ddf, mergeR, List.cons_append, List.filter_filter, hpred]

/-! ## `dedupFirst` IS `ddf` — the bridge to `AciNormal.normalize`. -/

theorem dropEq_subset {x : PredRE} : ∀ {l : List PredRE} {y}, y ∈ dropEq x l → y ∈ l := by
  intro l
  induction l with
  | nil => intro y h; simp [dropEq] at h
  | cons a as ih =>
    intro y h
    rw [dropEq] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem reEq_false_of_mem_dropEq {x : PredRE} :
    ∀ {l : List PredRE} {y}, y ∈ dropEq x l → reEq x y = false := by
  intro l
  induction l with
  | nil => intro y h; simp [dropEq] at h
  | cons a as ih =>
    intro y h
    rw [dropEq] at h
    split at h
    · exact ih h
    · rename_i hxa
      rcases List.mem_cons.mp h with h | h
      · subst h; simpa using hxa
      · exact ih h

theorem dropEq_comm (x y : PredRE) (l : List PredRE) :
    dropEq x (dropEq y l) = dropEq y (dropEq x l) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hx : reEq x a = true <;> by_cases hy : reEq y a = true <;>
      simp_all [dropEq]

theorem dedupFirst_subset : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → ∀ {y},
    y ∈ dedupFirst l → y ∈ l := by
  intro n
  induction n with
  | zero =>
    intro l hl y hy
    cases l with
    | nil => simp [dedupFirst] at hy
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl y hy
    cases l with
    | nil => simp [dedupFirst] at hy
    | cons a as =>
      rw [dedupFirst] at hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ List.mem_cons_self ..
      · have hlen : (dropEq a as).length ≤ n :=
          Nat.le_trans (dropEq_length_le a as) (by simpa using hl)
        exact List.mem_cons_of_mem _ (dropEq_subset (ih _ hlen h))

theorem dedupFirst_dropEq_aux : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → ∀ x : PredRE,
    dedupFirst (dropEq x l) = (dedupFirst l).filter (fun y => !reEq x y) := by
  intro n
  induction n with
  | zero =>
    intro l hl x
    cases l with
    | nil => simp [dropEq, dedupFirst]
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl x
    cases l with
    | nil => simp [dropEq, dedupFirst]
    | cons a as =>
      have hasn : as.length ≤ n := by simpa using hl
      have hdropn : (dropEq a as).length ≤ n := Nat.le_trans (dropEq_length_le a as) hasn
      by_cases hxa : reEq x a = true
      · have hxa' : x = a := reEq_sound hxa
        subst hxa'
        have hfilter : (dedupFirst (dropEq x as)).filter (fun y => !reEq x y)
            = dedupFirst (dropEq x as) := by
          apply List.filter_eq_self.mpr
          intro y hy
          have := reEq_false_of_mem_dropEq (dedupFirst_subset n _ hdropn hy)
          simp [this]
        rw [dropEq, if_pos hxa, dedupFirst, List.filter_cons, hxa]
        simpa using hfilter.symm
      · have hxa' : reEq x a = false := by simpa using hxa
        rw [dropEq, if_neg (by simp [hxa']), dedupFirst, dedupFirst,
          List.filter_cons, hxa']
        rw [dropEq_comm, ih (dropEq a as) hdropn x]
        simp

/-- **`dedupFirst_eq_ddf`** — `AciNormal`'s well-founded `dedupFirst` is the structurally recursive
`ddf`. Everything proved about `ddf` therefore lands on `normalize`. -/
theorem dedupFirst_eq_ddf : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → dedupFirst l = ddf l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [dedupFirst, ddf]
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp [dedupFirst, ddf]
    | cons a as =>
      have hasn : as.length ≤ n := by simpa using hl
      rw [dedupFirst, ddf, dedupFirst_dropEq_aux as.length as (Nat.le_refl _) a,
        ih as hasn]

theorem dedupFirst_eq_ddf' (l : List PredRE) : dedupFirst l = ddf l :=
  dedupFirst_eq_ddf l.length l (Nat.le_refl _)

/-! ## The canonical key, and its `Sim`-invariance. -/

/-- `allRigid l` — every element of `l` is a rigid leaf. -/
def allRigid (l : List PredRE) : Bool := l.all rigidLeaf

/-- **`key R`** — the first-occurrence disjunct SEQUENCE of `R`'s `alt` spine, when every leaf of
that spine is rigid; `none` otherwise. `none` is the honest answer for terms outside the fragment
(a `star`/`cat`/`inter`/`neg` leaf, or a leaf outside `predBEq`'s decidable fragment). -/
def key (R : PredRE) : Option (List PredRE) :=
  if allRigid (altList R) then some (ddf (altList R)) else none

/-- **`Frag R`** — `R` is in the PURE-`alt` FRAGMENT: it is built from `alt` over leaves that are
`reEq`-decidable and are not themselves `alt`. -/
def Frag (R : PredRE) : Prop := allRigid (altList R) = true

theorem key_eq_some_of_frag {R : PredRE} (h : Frag R) : key R = some (ddf (altList R)) :=
  if_pos h

theorem frag_of_key_some {R : PredRE} {l} (h : key R = some l) : Frag R := by
  unfold key at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem key_rigid {R : PredRE} {l : List PredRE} (h : key R = some l) :
    ∀ y ∈ l, reEq y y = true := by
  have hf : Frag R := frag_of_key_some h
  have hl : l = ddf (altList R) := by
    rw [key_eq_some_of_frag hf] at h; exact (Option.some.inj h).symm
  intro y hy
  subst hl
  have hmem : y ∈ altList R := ddf_subset hy
  exact reEq_refl_of_rigid (List.all_eq_true.mp hf y hmem)

theorem altList_alt (l r : PredRE) : altList (.alt l r) = altList l ++ altList r := rfl

/-- **`key_alt`** — `key` is a HOMOMORPHISM from `alt` to `mergeR`. This is what makes the
congruence case of the invariance free. -/
theorem key_alt (R S : PredRE) :
    key (.alt R S) = (key R).bind (fun l => (key S).bind (fun m => some (mergeR l m))) := by
  unfold key
  rw [altList_alt]
  have hall : allRigid (altList R ++ altList S) = (allRigid (altList R) && allRigid (altList S)) := by
    simp [allRigid, List.all_append]
  rw [hall, ddf_append]
  cases hR : allRigid (altList R) <;> cases hS : allRigid (altList S) <;> simp

/-- Non-`alt`, non-rigid heads are OUT of the fragment: `key = none`. This is the clause that
absorbs `negCong` / `interCong` / `catCong` — and, silently, the absent `starCong`. -/
theorem key_neg (R : PredRE) : key (.neg R) = none := by simp [key, altList, allRigid, rigidLeaf]
theorem key_inter (R S : PredRE) : key (.inter R S) = none := by
  simp [key, altList, allRigid, rigidLeaf]
theorem key_cat (R S : PredRE) : key (.cat R S) = none := by
  simp [key, altList, allRigid, rigidLeaf]
theorem key_star (R : PredRE) : key (.star R) = none := by
  simp [key, altList, allRigid, rigidLeaf]

/-- **`sim_key`** — THE INVARIANCE THEOREM: the first-occurrence disjunct sequence is constant on
`≅`-classes. Induction on the `Sim` derivation; every generator is discharged above. Holds for ALL
of `PredRE` — outside the fragment both sides are `none`, which is a true statement about a
deliberately partial invariant, not a completeness claim. -/
theorem sim_key {R S : PredRE} (h : Sim R S) : key R = key S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    simp only [key, altList_alt, List.append_assoc]
    rfl
  | @dedup R₁ R₂ =>
    rw [key_alt, key_alt, key_alt]
    cases hR : key R₁ with
    | none => simp
    | some l =>
      cases hS : key R₂ with
      | none => simp
      | some m => simp [mergeR_dedup (key_rigid hR)]
  | @idem R =>
    rw [key_alt]
    cases hR : key R with
    | none => simp
    | some l => simp [mergeR_self (key_rigid hR)]
  | rfl => rfl
  | sym _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | negCong _ _ => rw [key_neg, key_neg]
  | altCong _ _ ih₁ ih₂ => rw [key_alt, key_alt, ih₁, ih₂]
  | interCong _ _ _ _ => rw [key_inter, key_inter]
  | catCong _ _ => rw [key_cat, key_cat]
  | catCongR _ _ => rw [key_cat, key_cat]
  | starCong _ _ => rw [key_star, key_star]

/-- The fragment is `Sim`-CLOSED: it is not an assumption on the right-hand side, it is a
consequence. -/
theorem sim_frag {R S : PredRE} (h : Sim R S) (hR : Frag R) : Frag S :=
  frag_of_key_some ((sim_key h) ▸ key_eq_some_of_frag hR)

/-! ## FRAGMENT COMPLETENESS of `normalize`. -/

/-- Refold a non-empty disjunct list. -/
def foldList : List PredRE → PredRE
  | []      => .ε
  | x :: xs => foldAlt x xs

/-- `normalize` IS "flatten, `ddf`, refold" — the bridge from `AciNormal`'s definition to the
canonical key. -/
theorem normalize_eq_foldList (R : PredRE) : normalize R = foldList (ddf (altList R)) := by
  unfold normalize
  cases h : altList R with
  | nil => exact absurd h (altList_ne_nil R)
  | cons x xs =>
    rw [← dedupFirst_eq_ddf' (x :: xs), dedupFirst]
    rfl

/-- **`sim_normalize_eq`** — FRAGMENT COMPLETENESS. For terms of the pure-`alt` fragment (an `alt`
tree over `reEq`-decidable non-`alt` leaves), `normalize` is a COMPLETE invariant of `≅`: similar
terms have EQUAL normal forms. Together with `AciNormal.normalize_sim` (soundness) this makes
`reEq (normalize R) (normalize S)` a genuine decision procedure for `≅` ON THAT FRAGMENT. -/
theorem sim_normalize_eq {R S : PredRE} (h : Sim R S) (hR : Frag R) : normalize R = normalize S := by
  have hkey : some (ddf (altList R)) = some (ddf (altList S)) := by
    rw [← key_eq_some_of_frag hR, ← key_eq_some_of_frag (sim_frag h hR)]; exact sim_key h
  rw [normalize_eq_foldList, normalize_eq_foldList, Option.some.inj hkey]

/-- The `←` direction, for the record: equal normal forms always imply similarity (this needs no
fragment hypothesis — it is `normalize_sim` plus `sym`/`trans`). -/
theorem normalize_eq_sim {R S : PredRE} (h : normalize R = normalize S) : Sim R S :=
  Sim.trans (Sim.sym (normalize_sim R)) (h ▸ normalize_sim S)

/-! # THE WIDENING — a RECURSIVE normalizer, complete on the FULL rigid fragment.

`Sim` is now a FULL congruence (`Similarity.lean` carries `catCongR` and `starCong`, and
`sim_null`/`sim_der`/`sim_sound` cover them). The obstruction named in `AciNormal`'s residual §2 —
"recursing is UNSOUND under the present `Sim`: there is no `starCong` and `catCong` covers the left
factor only" — is therefore GONE. This section takes the widening.

`normalize` itself is left exactly as it is (it is `AciNormal`'s, and other modules depend on its
shape). The recursive normalizer is a NEW function `nrm`, built from the SAME two pieces:

* `nlist R` — the `alt` spine of `R`, flattened, with every non-`alt` LEAF normalized RECURSIVELY
  (`star r ↦ star (nrm r)`, `cat a b ↦ cat (nrm a) (nrm b)`, …). `ddf` is deliberately NOT applied
  at `alt` nodes: applying it there would force `mergeR`-ASSOCIATIVITY into the `assoc` case, whereas
  leaving the spine raw makes `assoc` `List.append_assoc` again — the same trick that keeps the
  pure-`alt` argument short.
* `nrm R := foldList (ddf (nlist R))` — dedup once, at the top of each spine.

and the canonical key becomes `nkey R = ddf (nlist R)` (gated by rigidity), which is a homomorphism
for `alt` (`nkey_alt`, into `mergeR` — unchanged) AND is now DETERMINED-BY-THE-KEY at every other
constructor (`nkey_star`/`nkey_cat`/`nkey_inter`/`nkey_neg`, into `Option.map`/`bind`). That second
family is what the new congruences buy: `starCong`/`catCongR` become one-line rewrites instead of
`key = none` on both sides.

The fragment widens from `Frag` (pure-`alt` over rigid leaves) to **`RigidFull`**: EVERY ATOMIC LEAF
is `reEq`-decidable, the STRUCTURE IS ARBITRARY — `star`, `cat`, `inter`, `neg` nodes are now IN.
`rigidFull_of_frag` proves this is a genuine superset. -/

/-! ## `RigidFull` — rigidity at the leaves, arbitrary structure. -/

/-- **`rigidRE R`** — every atomic leaf of `R` is `reEq`-decidable. Unlike `rigidLeaf` this RECURSES
through `star`/`cat`/`inter`/`neg`, because `normalize`'s successor does too. -/
def rigidRE : PredRE → Bool
  | .ε         => true
  | .sym p     => predBEq p p
  | .alt a b   => rigidRE a && rigidRE b
  | .inter a b => rigidRE a && rigidRE b
  | .cat a b   => rigidRE a && rigidRE b
  | .star a    => rigidRE a
  | .neg a     => rigidRE a

/-- **`RigidFull R`** — the widened fragment. -/
def RigidFull (R : PredRE) : Prop := rigidRE R = true

/-- On the widened fragment `reEq` is REFLEXIVE — the half `reEq_sound` does not give. -/
theorem reEq_refl_of_rigidRE : ∀ {R : PredRE}, rigidRE R = true → reEq R R = true := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym p => intro h; simpa [reEq, rigidRE] using h
  | alt a b iha ihb =>
    intro h; simp only [rigidRE, Bool.and_eq_true] at h; simp [reEq, iha h.1, ihb h.2]
  | inter a b iha ihb =>
    intro h; simp only [rigidRE, Bool.and_eq_true] at h; simp [reEq, iha h.1, ihb h.2]
  | cat a b iha ihb =>
    intro h; simp only [rigidRE, Bool.and_eq_true] at h; simp [reEq, iha h.1, ihb h.2]
  | star a iha => intro h; simp only [rigidRE] at h; simp [reEq, iha h]
  | neg a iha => intro h; simp only [rigidRE] at h; simp [reEq, iha h]

/-- The widened fragment CONTAINS the old one: every pure-`alt` term over `rigidLeaf`s is
`RigidFull`. (The converse fails — see the `#guard`s: `star (a ⋓ a)` is `RigidFull`, not `Frag`.) -/
theorem rigidFull_of_frag : ∀ {R : PredRE}, Frag R → RigidFull R := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym p => intro h; simpa [RigidFull, rigidRE, Frag, altList, allRigid, rigidLeaf] using h
  | alt a b iha ihb =>
    intro h
    simp only [Frag, altList_alt, allRigid, List.all_append, Bool.and_eq_true] at h
    simp only [RigidFull, rigidRE, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | inter a b _ _ => intro h; simp [Frag, altList, allRigid, rigidLeaf] at h
  | cat a b _ _ => intro h; simp [Frag, altList, allRigid, rigidLeaf] at h
  | star a _ => intro h; simp [Frag, altList, allRigid, rigidLeaf] at h
  | neg a _ => intro h; simp [Frag, altList, allRigid, rigidLeaf] at h

/-! ## The recursive normalizer. -/

/-- **`nlist R`** — `R`'s `alt` spine, flattened, with every LEAF normalized RECURSIVELY. Structural
recursion; `ddf` is applied inside the leaves (once per spine) but NOT at the `alt` nodes. -/
def nlist : PredRE → List PredRE
  | .ε         => [.ε]
  | .sym p     => [.sym p]
  | .alt a b   => nlist a ++ nlist b
  | .inter a b => [.inter (foldList (ddf (nlist a))) (foldList (ddf (nlist b)))]
  | .cat a b   => [.cat (foldList (ddf (nlist a))) (foldList (ddf (nlist b)))]
  | .star a    => [.star (foldList (ddf (nlist a)))]
  | .neg a     => [.neg (foldList (ddf (nlist a)))]

/-- **`nrm R`** — the RECURSIVE ACI normal form: normalize the leaves, flatten the spine, keep the
first occurrence of each disjunct, refold. -/
def nrm (R : PredRE) : PredRE := foldList (ddf (nlist R))

theorem nlist_ne_nil (R : PredRE) : nlist R ≠ [] := by
  induction R with
  | alt a b iha _ =>
    simp only [nlist]; intro h; exact iha (List.append_eq_nil_iff.mp h).1
  | _ => simp [nlist]

theorem ddf_ne_nil : ∀ {l : List PredRE}, l ≠ [] → ddf l ≠ [] := by
  intro l h
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => simp [ddf]

theorem nlist_star (R : PredRE) : nlist (.star R) = [.star (nrm R)] := rfl
theorem nlist_neg (R : PredRE) : nlist (.neg R) = [.neg (nrm R)] := rfl
theorem nlist_cat (R S : PredRE) : nlist (.cat R S) = [.cat (nrm R) (nrm S)] := rfl
theorem nlist_inter (R S : PredRE) : nlist (.inter R S) = [.inter (nrm R) (nrm S)] := rfl
theorem nlist_alt (R S : PredRE) : nlist (.alt R S) = nlist R ++ nlist S := rfl

/-! ## SOUNDNESS — `Sim (nrm R) R`, now THROUGH the leaves.

Same two-step shape as `AciNormal.normalize_sim`, but the leaf steps use the NEW congruences:
`starCong` for `star`, `catCong`+`catCongR` for `cat`, `interCong`, `negCong`. -/

/-- Refolding a `ddf`'d spine is `AciNormal`'s `dedupFirst` fold — the bridge. -/
theorem foldList_ddf_cons (x : PredRE) (xs : List PredRE) :
    foldList (ddf (x :: xs)) = foldAlt x (dedupFirst (dropEq x xs)) := by
  rw [← dedupFirst_eq_ddf' (x :: xs), dedupFirst]; rfl

/-- From the head-form spine soundness, the `ddf` pass is `Sim`-neutral on top. -/
private theorem nrm_sim_of_head {R : PredRE}
    (h2 : ∀ x xs, nlist R = x :: xs → Sim (foldAlt x xs) R) : Sim (nrm R) R := by
  unfold nrm
  cases hl : nlist R with
  | nil => exact absurd hl (nlist_ne_nil R)
  | cons x xs =>
    rw [foldList_ddf_cons]
    refine Sim.trans (foldAlt_dedupFirst (dropEq x xs) x) ?_
    exact Sim.trans (foldAlt_dropEq x xs x Sim.idem) (h2 x xs hl)

private theorem nlist_singleton_sim {R t : PredRE} (hnl : nlist R = [t]) (ht : Sim t R) :
    (∀ h, Sim (foldAlt h (nlist R)) (.alt h R))
      ∧ (∀ x xs, nlist R = x :: xs → Sim (foldAlt x xs) R) := by
  constructor
  · intro h; rw [hnl]; exact Sim.altCong Sim.rfl ht
  · intro x xs hx
    rw [hnl] at hx
    simp only [List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ht

/-- **`nlist_fold_sim`** — the spine of `nlist` refolds back to the original, in both the
prefixed and the head form. Structural induction on `R`; the leaf cases are exactly the `Sim`
congruences, one per constructor. -/
theorem nlist_fold_sim : ∀ R : PredRE,
    (∀ h, Sim (foldAlt h (nlist R)) (.alt h R))
      ∧ (∀ x xs, nlist R = x :: xs → Sim (foldAlt x xs) R) := by
  intro R
  induction R with
  | ε => exact nlist_singleton_sim rfl Sim.rfl
  | sym p => exact nlist_singleton_sim rfl Sim.rfl
  | alt a b iha ihb =>
    constructor
    · intro h
      rw [nlist_alt, foldAlt_append]
      refine Sim.trans (ihb.1 (foldAlt h (nlist a))) ?_
      exact Sim.trans (Sim.altCong (iha.1 h) Sim.rfl) Sim.assoc
    · intro x xs hx
      rw [nlist_alt] at hx
      cases hla : nlist a with
      | nil => exact absurd hla (nlist_ne_nil a)
      | cons y ys =>
        rw [hla] at hx
        simp only [List.cons_append, List.cons.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        rw [foldAlt_append]
        exact Sim.trans (ihb.1 (foldAlt y ys)) (Sim.altCong (iha.2 y ys hla) Sim.rfl)
  | inter a b iha ihb =>
    exact nlist_singleton_sim (nlist_inter a b)
      (Sim.interCong (nrm_sim_of_head iha.2) (nrm_sim_of_head ihb.2))
  | cat a b iha ihb =>
    refine nlist_singleton_sim (nlist_cat a b) ?_
    exact Sim.trans (Sim.catCong (nrm_sim_of_head iha.2))
      (Sim.catCongR (nrm_sim_of_head ihb.2))
  | star a iha =>
    exact nlist_singleton_sim (nlist_star a) (Sim.starCong (nrm_sim_of_head iha.2))
  | neg a iha =>
    exact nlist_singleton_sim (nlist_neg a) (Sim.negCong (nrm_sim_of_head iha.2))

/-- **`nrm_sim`** — SOUNDNESS of the recursive normalizer, on ALL of `PredRE` (no fragment
hypothesis; rigidity only ever costs dedup POWER, never soundness). -/
theorem nrm_sim (R : PredRE) : Sim (nrm R) R := nrm_sim_of_head (nlist_fold_sim R).2

/-- Language-soundness, transported. -/
theorem nrm_derives (R : PredRE) (w : List Value) : derives w (nrm R) = derives w R :=
  sim_derives_syntactic (nrm_sim R) w

/-! ## Rigidity is preserved by normalization. -/

theorem rigidRE_foldAlt : ∀ (l : List PredRE) (h : PredRE), rigidRE h = true →
    (∀ y ∈ l, rigidRE y = true) → rigidRE (foldAlt h l) = true := by
  intro l
  induction l with
  | nil => intro h hh _; exact hh
  | cons a as ih =>
    intro h hh hl
    refine ih (.alt h a) ?_ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp [rigidRE, hh, hl a (List.mem_cons_self ..)]

theorem rigidRE_foldList {l : List PredRE} (hne : l ≠ []) (h : ∀ y ∈ l, rigidRE y = true) :
    rigidRE (foldList l) = true := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    exact rigidRE_foldAlt xs x (h x (List.mem_cons_self ..))
      (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **`rigid_nlist`** — on the widened fragment, every normalized disjunct is itself rigid. This is
what lets the left-regular-band deletion laws fire on the RECURSIVELY normalized leaves. -/
theorem rigid_nlist : ∀ {R : PredRE}, rigidRE R = true → ∀ y ∈ nlist R, rigidRE y = true := by
  intro R
  have step : ∀ (a : PredRE), (∀ y ∈ nlist a, rigidRE y = true) → rigidRE (nrm a) = true := by
    intro a ha
    exact rigidRE_foldList (ddf_ne_nil (nlist_ne_nil a)) (fun y hy => ha y (ddf_subset hy))
  induction R with
  | ε => intro _ y hy; simp only [nlist, List.mem_singleton] at hy; simp [hy, rigidRE]
  | sym p =>
    intro h y hy
    simp only [nlist, List.mem_singleton] at hy
    simpa [hy, rigidRE] using h
  | alt a b iha ihb =>
    intro h y hy
    simp only [rigidRE, Bool.and_eq_true] at h
    rw [nlist_alt] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact iha h.1 y hy
    · exact ihb h.2 y hy
  | inter a b iha ihb =>
    intro h y hy
    simp only [rigidRE, Bool.and_eq_true] at h
    simp only [nlist_inter, List.mem_singleton] at hy
    simp [hy, rigidRE, step a (iha h.1), step b (ihb h.2)]
  | cat a b iha ihb =>
    intro h y hy
    simp only [rigidRE, Bool.and_eq_true] at h
    simp only [nlist_cat, List.mem_singleton] at hy
    simp [hy, rigidRE, step a (iha h.1), step b (ihb h.2)]
  | star a iha =>
    intro h y hy
    simp only [rigidRE] at h
    simp only [nlist_star, List.mem_singleton] at hy
    simp [hy, rigidRE, step a (iha h)]
  | neg a iha =>
    intro h y hy
    simp only [rigidRE] at h
    simp only [nlist_neg, List.mem_singleton] at hy
    simp [hy, rigidRE, step a (iha h)]

theorem rigidRE_nrm {R : PredRE} (h : rigidRE R = true) : rigidRE (nrm R) = true :=
  rigidRE_foldList (ddf_ne_nil (nlist_ne_nil R)) (fun y hy => rigid_nlist h y (ddf_subset hy))

/-! ## The RECURSIVE key, and its `Sim`-invariance. -/

/-- **`nkey R`** — the recursive canonical key: the first-occurrence sequence of the spine of `R`
with every leaf recursively normalized, when `R` is `RigidFull`; `none` otherwise. -/
def nkey (R : PredRE) : Option (List PredRE) :=
  if rigidRE R then some (ddf (nlist R)) else none

theorem nkey_eq_some_of_rigid {R : PredRE} (h : RigidFull R) : nkey R = some (ddf (nlist R)) :=
  if_pos h

theorem rigid_of_nkey_some {R : PredRE} {l} (h : nkey R = some l) : RigidFull R := by
  unfold nkey at h; split at h
  · assumption
  · exact absurd h (by simp)

theorem nkey_rigid_elems {R : PredRE} {l : List PredRE} (h : nkey R = some l) :
    ∀ y ∈ l, reEq y y = true := by
  have hr : RigidFull R := rigid_of_nkey_some h
  have hl : l = ddf (nlist R) := by
    rw [nkey_eq_some_of_rigid hr] at h; exact (Option.some.inj h).symm
  intro y hy
  subst hl
  exact reEq_refl_of_rigidRE (rigid_nlist hr y (ddf_subset hy))

/-- `nkey` is a HOMOMORPHISM from `alt` into `mergeR` — the pure-`alt` half, unchanged. -/
theorem nkey_alt (R S : PredRE) :
    nkey (.alt R S) = (nkey R).bind (fun l => (nkey S).bind (fun m => some (mergeR l m))) := by
  unfold nkey
  rw [nlist_alt, ddf_append]
  cases hR : rigidRE R <;> cases hS : rigidRE S <;> simp [rigidRE, hR, hS]

/-! The NEW half: at every non-`alt` constructor the key is a FUNCTION OF THE SUB-KEYS. This is
exactly what `starCong` / `catCongR` buy — previously all four of these were `none`. -/

theorem nkey_star (R : PredRE) :
    nkey (.star R) = (nkey R).map (fun l => [PredRE.star (foldList l)]) := by
  unfold nkey
  cases hR : rigidRE R <;> simp [rigidRE, hR, nlist_star, nrm, ddf]

theorem nkey_neg (R : PredRE) :
    nkey (.neg R) = (nkey R).map (fun l => [PredRE.neg (foldList l)]) := by
  unfold nkey
  cases hR : rigidRE R <;> simp [rigidRE, hR, nlist_neg, nrm, ddf]

theorem nkey_cat (R S : PredRE) :
    nkey (.cat R S)
      = (nkey R).bind (fun l => (nkey S).map (fun m => [PredRE.cat (foldList l) (foldList m)])) := by
  unfold nkey
  cases hR : rigidRE R <;> cases hS : rigidRE S <;>
    simp [rigidRE, hR, hS, nlist_cat, nrm, ddf]

theorem nkey_inter (R S : PredRE) :
    nkey (.inter R S)
      = (nkey R).bind (fun l =>
          (nkey S).map (fun m => [PredRE.inter (foldList l) (foldList m)])) := by
  unfold nkey
  cases hR : rigidRE R <;> cases hS : rigidRE S <;>
    simp [rigidRE, hR, hS, nlist_inter, nrm, ddf]

/-- **`sim_nkey`** — THE WIDENED INVARIANCE THEOREM. The recursive first-occurrence key is constant
on `≅`-classes, for EVERY `R S : PredRE`. Compare `sim_key`: there the four structural congruence
cases were discharged by `none = none` (the blind spot); here every one of them TRANSPORTS ITS IH
through the corresponding key equation. -/
theorem sim_nkey {R S : PredRE} (h : Sim R S) : nkey R = nkey S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    -- `nlist` does NOT `ddf` at `alt` nodes, so associativity is `List.append_assoc` and no
    -- `mergeR`-associativity is ever needed.
    simp only [nkey, rigidRE, nlist_alt, List.append_assoc, Bool.and_assoc]
    rfl
  | @dedup R₁ R₂ =>
    by_cases h1 : rigidRE R₁ = true
    · by_cases h2 : rigidRE R₂ = true
      · have hrig : ∀ y ∈ ddf (nlist R₁), reEq y y = true := fun y hy =>
          reEq_refl_of_rigidRE (rigid_nlist h1 y (ddf_subset hy))
        simp only [nkey, rigidRE, nlist_alt, h1, h2, Bool.and_self]
        rw [ddf_append, ddf_append, ddf_append, mergeR_dedup hrig]
      · simp only [Bool.not_eq_true] at h2
        simp [nkey, rigidRE, h1, h2]
    · simp only [Bool.not_eq_true] at h1
      simp [nkey, rigidRE, h1]
  | @idem R =>
    by_cases h1 : rigidRE R = true
    · have hrig : ∀ y ∈ ddf (nlist R), reEq y y = true := fun y hy =>
        reEq_refl_of_rigidRE (rigid_nlist h1 y (ddf_subset hy))
      simp only [nkey, rigidRE, nlist_alt, h1, Bool.and_self]
      rw [ddf_append, mergeR_self hrig]
    · simp only [Bool.not_eq_true] at h1
      simp [nkey, rigidRE, h1]
  | rfl => rfl
  | sym _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | negCong _ ih => rw [nkey_neg, nkey_neg, ih]
  | altCong _ _ ih₁ ih₂ => rw [nkey_alt, nkey_alt, ih₁, ih₂]
  | interCong _ _ ih₁ ih₂ => rw [nkey_inter, nkey_inter, ih₁, ih₂]
  | catCong _ ih => rw [nkey_cat, nkey_cat, ih]
  | catCongR _ ih => rw [nkey_cat, nkey_cat, ih]
  | starCong _ ih => rw [nkey_star, nkey_star, ih]

/-- The widened fragment is `Sim`-CLOSED — again a consequence, not a hypothesis. -/
theorem sim_rigidFull {R S : PredRE} (h : Sim R S) (hR : RigidFull R) : RigidFull S :=
  rigid_of_nkey_some ((sim_nkey h) ▸ nkey_eq_some_of_rigid hR)

/-- **`sim_nrm_eq`** — WIDENED COMPLETENESS. On `RigidFull` — every atomic leaf `reEq`-decidable,
STRUCTURE ARBITRARY — the recursive normal form is a COMPLETE invariant of `≅`. This strictly
subsumes `sim_normalize_eq` (`rigidFull_of_frag`), and it is the case `AciNormal`'s residual §2 said
was blocked on `Sim` becoming a full congruence. -/
theorem sim_nrm_eq {R S : PredRE} (h : Sim R S) (hR : RigidFull R) : nrm R = nrm S := by
  have hk : some (ddf (nlist R)) = some (ddf (nlist S)) := by
    rw [← nkey_eq_some_of_rigid hR, ← nkey_eq_some_of_rigid (sim_rigidFull h hR)]
    exact sim_nkey h
  unfold nrm; rw [Option.some.inj hk]

/-- The `←` direction, unconditional (soundness plus `sym`/`trans`). -/
theorem nrm_eq_sim {R S : PredRE} (h : nrm R = nrm S) : Sim R S :=
  Sim.trans (Sim.sym (nrm_sim R)) (h ▸ nrm_sim S)

/-! ## …hence a genuine DECISION PROCEDURE for `≅` on the widened fragment. -/

/-- **`simDecide R S`** — computable: normalize both recursively, compare with the one-sided `reEq`. -/
def simDecide (R S : PredRE) : Bool := reEq (nrm R) (nrm S)

/-- **`simDecide_correct`** — `simDecide` DECIDES `≅` whenever the left argument is `RigidFull`.
`→` is unconditional (`reEq_sound` + `nrm_eq_sim`); `←` is the widened completeness plus reflexivity
of `reEq` on the normalized (hence still rigid) term. -/
theorem simDecide_correct {R S : PredRE} (hR : RigidFull R) :
    simDecide R S = true ↔ Sim R S := by
  constructor
  · intro h; exact nrm_eq_sim (reEq_sound h)
  · intro h
    have he : nrm R = nrm S := sim_nrm_eq h hR
    unfold simDecide
    rw [← he]
    exact reEq_refl_of_rigidRE (rigidRE_nrm hR)

/-- NON-VACUITY of the widened decision: it answers `false` on a genuinely non-similar RIGID pair
(the `alt`-commutativity falsifier survives the widening), and `true` on a similarity that lives
STRICTLY OUTSIDE the old `Frag` (under a `star`). Both are `#guard`ed below. -/
theorem not_sim_of_nrm_ne {R S : PredRE} (hR : RigidFull R) (h : nrm R ≠ nrm S) : ¬ Sim R S :=
  fun hs => h (sim_nrm_eq hs hR)

/-! ## THE FALSIFIER — `alt` is NOT commutative under `≅`.

The prose claim of `AciNormal.lean` ("the free left regular band on two generators has `ab ≠ ba`,
so `alt a b ≅ alt b a` is not derivable") is now a COROLLARY of fragment completeness, checked
against the ACTUAL `Sim` rather than against a model of it. -/

section Falsifier

private def q7 : Pred := .symEq "k" 7
private def q9 : Pred := .symEq "k" 9
private def s7 : PredRE := .sym q7
private def s9 : PredRE := .sym q9

theorem frag_s7_s9 : Frag (.alt s7 s9) := by unfold Frag; decide
theorem frag_s9_s7 : Frag (.alt s9 s7) := by unfold Frag; decide

theorem normalize_s7_s9 : normalize (.alt s7 s9) = .alt s7 s9 := by
  rw [normalize_eq_foldList]
  simp [altList, ddf, foldList, foldAlt, reEq, predBEq, s7, s9, q7, q9]

theorem normalize_s9_s7 : normalize (.alt s9 s7) = .alt s9 s7 := by
  rw [normalize_eq_foldList]
  simp [altList, ddf, foldList, foldAlt, reEq, predBEq, s7, s9, q7, q9]

theorem s7_ne_s9 : s7 ≠ s9 := by
  intro h
  simp [s7, s9, q7, q9] at h

/-- The two orders have DIFFERENT normal forms — decided, not asserted. -/
theorem normalize_alt_comm_ne : normalize (.alt s7 s9) ≠ normalize (.alt s9 s7) := by
  rw [normalize_s7_s9, normalize_s9_s7]
  intro h
  injection h with h1 _
  exact s7_ne_s9 h1

/-- **`not_sim_alt_comm`** — THE THEOREM the whole design rests on: `alt` is NOT commutative under
`≅`. Contrapositive of fragment completeness against the computed disequality above. A normalizer
that SORTS the disjunct list would need exactly this similarity, and it does not exist. -/
theorem not_sim_alt_comm : ¬ Sim (.alt s7 s9) (.alt s9 s7) := by
  intro h
  exact normalize_alt_comm_ne (sim_normalize_eq h frag_s7_s9)

/-- NON-VACUITY of `sim_normalize_eq`: a POSITIVE instance. `(a ⋓ b) ⋓ a ≅ a ⋓ b` really holds (by
`assoc` + `dedup`), both sides really are in the fragment, and completeness really equates their
normal forms — so the theorem is not merely true because its hypothesis is unsatisfiable. -/
theorem sim_dedup_witness : Sim (.alt (.alt s7 s9) s7) (.alt s7 s9) :=
  Sim.trans Sim.assoc Sim.dedup

theorem normalize_dedup_witness :
    normalize (.alt (.alt s7 s9) s7) = normalize (.alt s7 s9) :=
  sim_normalize_eq sim_dedup_witness (by unfold Frag; decide)

/-- …and the general shape: on the fragment, two distinct-normal-form terms are NEVER similar. -/
theorem not_sim_of_normalize_ne {R S : PredRE} (hR : Frag R)
    (h : normalize R ≠ normalize S) : ¬ Sim R S :=
  fun hs => h (sim_normalize_eq hs hR)

end Falsifier

/-! ## `#guard`s — the fragment predicate and the key are what they claim to be. -/

section Guards

private def g7 : PredRE := .sym (.symEq "k" 7)
private def g9 : PredRE := .sym (.symEq "k" 9)
-- `gAtom` is now INSIDE `predBEq`'s fragment (`Exec.StateConstraint` carries `DecidableEq`).
private def gAtom : PredRE := .sym (.atom (.fieldLeField "a" "b"))
-- `gOut` is inside the rigid fragment too: field-name equality is decidable.
private def gOut : PredRE := .sym (.fieldEqField "a" "b")

/-- `PredRE` has no `DecidableEq`, so the guards compare keys through the one-sided `reEq`
(fail-closed: a `true` here is a real equality, by `reEq_sound`). -/
private def keyBEq : Option (List PredRE) → Option (List PredRE) → Bool
  | none,   none   => true
  | some l, some m => l.length == m.length && (l.zip m).all (fun p => reEq p.1 p.2)
  | _,      _      => false

-- IN the fragment: `alt` trees over `ε`/decidable `sym` leaves — now INCLUDING the `atom` leaf.
#guard allRigid (altList (.alt (.alt g7 g9) g7)) = true
#guard allRigid (altList (.alt g7 .ε)) = true
#guard allRigid (altList (.alt gAtom g9)) = true
#guard (key (.alt gAtom g9)).isNone = false
-- A whole `star` term is not a top-level rigid `alt` leaf for the narrow `key` operation.
#guard allRigid (altList (.alt (.star g7) g9)) = false
#guard allRigid (altList (.alt gOut g9)) = true
#guard (key (.alt (.star g7) g9)).isNone = true
#guard (key (.alt gOut g9)).isNone = false

-- The key really is the ORDER-PRESERVING first-occurrence sequence, and it SEPARATES the two orders.
#guard keyBEq (key (.alt (.alt g7 g9) g7)) (some [g7, g9]) = true
#guard keyBEq (key (.alt g9 g7)) (some [g9, g7]) = true
#guard keyBEq (key (.alt g7 g9)) (key (.alt g9 g7)) = false
-- …while genuinely IDENTIFYING the ACI-redundant spellings.
#guard keyBEq (key (.alt (.alt g7 g9) g7)) (key (.alt g7 g9)) = true
#guard keyBEq (key (.alt g7 (.alt g9 g7))) (key (.alt g7 g9)) = true
#guard keyBEq (key (.alt g7 g7)) (key g7) = true

end Guards

/-! ## `#guard`s for the WIDENING — `nrm` collapses ACI redundancy UNDER `star` and `cat`, which
`normalize` provably cannot. -/

section WideGuards

-- The fragment REALLY widened: `star (g7 ⋓ g7)` is `RigidFull` but is NOT `Frag` (its whole spine is
-- one `star` leaf, which `rigidLeaf` rejects).
#guard rigidRE (.star (.alt g7 g7)) = true
#guard allRigid (altList (.star (.alt g7 g7))) = false
#guard rigidRE (.cat (.alt (.alt g7 g9) g7) (.star (.alt g9 g9))) = true
#guard allRigid (altList (.cat (.alt (.alt g7 g9) g7) (.star (.alt g9 g9)))) = false

-- UNDER A STAR: `star (g7 ⋓ g7)` ↦ `star g7`. `normalize` leaves it ALONE (it cannot recurse);
-- `nrm` collapses it. This pair is the whole point of the widening, in two lines.
#guard reEq (nrm (.star (.alt g7 g7))) (.star g7) = true
#guard reEq (normalize (.star (.alt g7 g7))) (.star g7) = false

-- UNDER A CAT, both factors at once (the `catCong` AND `catCongR` directions):
-- `((g7 ⋓ g9) ⋓ g7) · star (g9 ⋓ g9)` ↦ `(g7 ⋓ g9) · star g9`.
#guard reEq (nrm (.cat (.alt (.alt g7 g9) g7) (.star (.alt g9 g9))))
            (.cat (.alt g7 g9) (.star g9)) = true
#guard reEq (normalize (.cat (.alt (.alt g7 g9) g7) (.star (.alt g9 g9))))
            (.cat (.alt g7 g9) (.star g9)) = false

-- MIXED: dedup of two spine disjuncts that are similar-but-UNEQUAL as written — exactly the
-- `altCong` blind spot `AciNormal`'s residual §2 named. `star (g7 ⋓ g7) ⋓ star g7` ↦ `star g7`.
#guard reEq (nrm (.alt (.star (.alt g7 g7)) (.star g7))) (.star g7) = true
#guard reEq (normalize (.alt (.star (.alt g7 g7)) (.star g7)))
            (.alt (.star (.alt g7 g7)) (.star g7)) = true

-- …and under `neg` / `inter` too.
#guard reEq (nrm (.neg (.alt g7 g7))) (.neg g7) = true
#guard reEq (nrm (.inter (.alt g7 g7) (.alt (.alt g9 g7) g9))) (.inter g7 (.alt g9 g7)) = true

-- NOT over-collapsing: order is still PRESERVED under the recursion (no sort), and distinct
-- disjuncts still survive.
#guard reEq (nrm (.star (.alt g7 g9))) (.star (.alt g7 g9)) = true
#guard reEq (nrm (.star (.alt g9 g7))) (.star (.alt g7 g9)) = false
#guard reEq (nrm (.star g7)) (.star g9) = false

-- The DECISION PROCEDURE, both polarities, on terms outside the old fragment.
#guard simDecide (.star (.alt g7 g7)) (.star g7) = true
#guard simDecide (.star (.alt g7 g9)) (.star (.alt g9 g7)) = false
#guard simDecide (.cat (.alt g7 g7) (.star g9)) (.cat g7 (.star g9)) = true

-- Both `atom` and `fieldEqField` leaves are in the fragment: `rigidRE` accepts them and `nrm`
-- deduplicates them.
#guard rigidRE (.star (.alt gAtom gAtom)) = true
#guard rigidRE (.alt gAtom gAtom) = true
#guard rigidRE (.star (.alt gOut gOut)) = true
#guard rigidRE (.alt gOut gOut) = true
-- Spine LENGTH after `ddf`, witnessed by a DECIDABLE invariant rather than the one-sided `reEq`:
-- every rigid equal pair collapses to one first occurrence.
#guard (ddf (nlist (.alt g7 g7))).length = 1
#guard (ddf (nlist (.alt gAtom gAtom))).length = 1
#guard (ddf (nlist (.alt gOut gOut))).length = 1
#guard (ddf (nlist (.star (.alt gOut gOut)))).length = 1

/-! ### NON-VACUITY of the widening, as THEOREMS (not only as computed guards).

`sim_nrm_eq` would be uninteresting if its hypothesis were unsatisfiable outside `Frag`. It is not:
here is a real `Sim` derivation whose two sides live STRICTLY outside `Frag` (both are single `star`
leaves, which `rigidLeaf` rejects), whose normal forms completeness therefore equates — and, in the
other polarity, a `RigidFull` pair under a `star` that is provably NOT similar. -/

/-- A similarity that only exists because `Sim` gained `starCong`. -/
theorem sim_star_dedup_witness : Sim (.star (.alt g7 g7)) (.star g7) := Sim.starCong Sim.idem

theorem rigidFull_star_g7g7 : RigidFull (.star (.alt g7 g7)) := by
  unfold RigidFull; decide

/-- …and this pair is OUTSIDE the old fragment: `sim_normalize_eq` cannot be applied to it. -/
theorem not_frag_star_g7g7 : ¬ Frag (.star (.alt g7 g7)) := by
  unfold Frag; decide

/-- WIDENED COMPLETENESS, fired on that witness — a case the pure-`alt` theorem cannot reach. -/
theorem nrm_star_dedup_witness : nrm (.star (.alt g7 g7)) = nrm (.star g7) :=
  sim_nrm_eq sim_star_dedup_witness rigidFull_star_g7g7

theorem g7_ne_g9 : g7 ≠ g9 := by intro h; simp [g7, g9] at h

theorem nrm_star_alt_79 : nrm (.star (.alt g7 g9)) = .star (.alt g7 g9) := rfl
theorem nrm_star_alt_97 : nrm (.star (.alt g9 g7)) = .star (.alt g9 g7) := rfl

/-- The OTHER polarity, UNDER A STAR: `alt` is not commutative under `≅` even beneath a congruence
that `Sim` only just gained. A real disequality (constructor injection), not a `reEq = false`. -/
theorem not_sim_star_alt_comm : ¬ Sim (.star (.alt g7 g9)) (.star (.alt g9 g7)) := by
  refine not_sim_of_nrm_ne (by unfold RigidFull; decide) ?_
  rw [nrm_star_alt_79, nrm_star_alt_97]
  intro h
  injection h with h1
  injection h1 with h2 _
  exact g7_ne_g9 h2

end WideGuards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.reEq_refl_of_rigid, PredRE.ddf_subset, PredRE.filter_notMemR_nil,
  PredRE.mergeR_self, PredRE.mergeR_dedup, PredRE.ddf_append,
  PredRE.dropEq_subset, PredRE.reEq_false_of_mem_dropEq, PredRE.dropEq_comm,
  PredRE.dedupFirst_subset, PredRE.dedupFirst_dropEq_aux, PredRE.dedupFirst_eq_ddf',
  PredRE.key_alt, PredRE.key_neg, PredRE.key_inter, PredRE.key_cat,
  PredRE.sim_key, PredRE.sim_frag,
  PredRE.normalize_eq_foldList, PredRE.sim_normalize_eq, PredRE.normalize_eq_sim,
  PredRE.sim_dedup_witness, PredRE.normalize_dedup_witness,
  PredRE.normalize_alt_comm_ne, PredRE.not_sim_alt_comm, PredRE.not_sim_of_normalize_ne
]

/-! The WIDENING's keystones. -/

#assert_all_clean [
  PredRE.reEq_refl_of_rigidRE, PredRE.rigidFull_of_frag,
  PredRE.nlist_ne_nil, PredRE.ddf_ne_nil, PredRE.foldList_ddf_cons,
  PredRE.nlist_fold_sim, PredRE.nrm_sim, PredRE.nrm_derives,
  PredRE.rigidRE_foldAlt, PredRE.rigidRE_foldList, PredRE.rigid_nlist, PredRE.rigidRE_nrm,
  PredRE.nkey_rigid_elems, PredRE.nkey_alt,
  PredRE.nkey_star, PredRE.nkey_neg, PredRE.nkey_cat, PredRE.nkey_inter,
  PredRE.sim_nkey, PredRE.sim_rigidFull, PredRE.sim_nrm_eq, PredRE.nrm_eq_sim,
  PredRE.simDecide_correct, PredRE.not_sim_of_nrm_ne,
  PredRE.sim_star_dedup_witness, PredRE.rigidFull_star_g7g7, PredRE.not_frag_star_g7g7,
  PredRE.nrm_star_dedup_witness, PredRE.not_sim_star_alt_comm
]

/-!
## THE RESIDUAL — what is still NOT proved, after the widening.

`AciNormal`'s residual named TWO obstructions. **§2 (structural) is now CLOSED**; §3 (leaf equality)
is now closed for the `atom` leaf (`DecidableEq StateConstraint`), `fieldEqField`, the compound
`not`/`and`/`or` constructors, AND (second 07-19 widening) for the n-ary `allOf`/`anyOf` and the
typed `symMemberOf`/`digFieldEq` leaves. It remains open only for the typed reactive constructors
that `predBEq` does not yet descend.

**CLOSED — the structural axis.** `sim_nrm_eq : Sim R S → RigidFull R → nrm R = nrm S` is completeness
on a fragment whose STRUCTURE IS ARBITRARY: `star`, `cat`, `inter` and `neg` nodes are inside it, at
any depth, and the `altCong` blind spot §2 named (`alt (star (alt a a)) b ≅ alt (star a) b`, two
disjuncts similar-but-unequal) is decided correctly — `#guard`ed. What paid for it is `Similarity`'s
`catCongR`/`starCong`: with a full congruence the recursion is SOUND (`nrm_sim`, unconditional), and
with the recursion the key determines itself at every constructor (`nkey_star`/`nkey_cat`/…), so the
four congruence cases of `sim_nkey` transport instead of collapsing to `none = none`.

**NARROWED — the leaf axis, now covering only the compound/typed leaves.** `rigidRE` demands
`predBEq p p = true` at every atomic leaf. The **`atom` leaf is now DECIDED**: `Exec.StateConstraint`
carries a real `DecidableEq` (added to `Exec/Program.lean` — all payloads decidable, incl. the
`Label`/`ClearanceGraph` lattice carriers), so `predBEq` totalizes on `atom` and every `atom`-leaf
term is now inside `RigidFull` (`#guard`ed: `rigidRE (.alt gAtom gAtom) = true`, `ddf` collapses the
`atom` pair to length 1). The compound `not`/`and`/`or` constructors are DESCENDED structurally,
and the second 07-19 widening added the n-ary `allOf`/`anyOf` (elementwise, `predBEqList`) and the
typed `symMemberOf`/`digFieldEq` leaves — enum-membership and owner-match guards are inside
`RigidFull` now. `fieldEqField` is decided directly from its two field-name payloads. What is still
outside are the typed reactive constructors that `predBEq` does not yet descend.
The FULL statement, no rigidity side condition:

    `∀ R S, Sim R S → nrm R = nrm S`   -- FULL `PredRE`, no rigidity side condition

is still FALSE as stated only because of those remaining typed reactive leaves. It becomes provable
— with every theorem in this file transporting UNCHANGED,
since the invariance argument uses only `reEq_sound` plus reflexivity on the fragment — as `predBEq` is
extended to those constructors. The difference-cover work is independent: the reactive simple atoms
are already carried by `Pred.atom` and therefore already rigid.

**NOT a residual, but stated so it is not misread.** `≅` here is `Sim`, the ACI congruence on `alt`
plus the structural congruences. It contains NO unit/annihilator/star laws — `cat ε R ≅ R`,
`star (star R) ≅ star R`, `alt R (neg R) ≅ …` are not `Sim`-derivable and `nrm` does not attempt them.
"Complete for `≅`" therefore means complete for `Sim`, which is exactly the relation the Brzozowski
finiteness quotient is taken by (`Similarity.sim_sound`, `Finiteness.der_finite`) — it is the relation
`SymbolicEmptiness`'s unbounded rung needs decided, and `simDecide` now decides it on `RigidFull`.

What IS closed, restated: the order-preserving first-occurrence normal form is a COMPLETE invariant of
`≅` on the pure-`alt` fragment (`sim_normalize_eq`) and, recursively, on the whole rigid fragment
(`sim_nrm_eq`); and the SORTED normal form is UNREACHABLE (`not_sim_alt_comm`) — not merely unproved.
The "months-scale `Permute`/`Pieces`" estimate was priced against the sorting picture; the theorems
above say that price bought nothing, because the commutativity it needs is false.
-/

end Dregg2.Crypto.Deriv
