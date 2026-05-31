import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints

/-!
# Parametrized Coinduction (Paco)

This module implements parametrized coinduction for Lean 4, based on the Coq
paco library by Hur, Neis, Dreyer, and Vafeiadis.

## Overview

Standard coinduction (Knaster-Tarski) defines a coinductive relation as:
```
gfp F = ⋃ { R | R ⊆ F(R) }
```

To prove `gfp F x y`, you must provide a witness `R` with `R x y` and `R ⊆ F(R)`
*before* the proof starts. This makes some proofs difficult, especially transitivity
where intermediate elements change at each step.

Paco solves this by parametrizing the fixed point:
```
paco F r = gfp (fun R => F(R ∪ r))
```

The parameter `r` accumulates facts during the proof. The coinductive hypothesis
becomes `upaco F r = paco F r ∪ r`.

## Main Definitions

- `Rel α`: Binary relations on a type
- `MonoRel α`: Monotone relation transformers
- `paco F r`: Parametrized greatest fixed point
- `upaco F r`: The "usable" coinductive hypothesis (paco ∪ parameter)

## Main Theorems

- `paco_mon`: paco is monotone in the parameter
- `paco_unfold`: paco F r ≤ F (upaco F r)
- `paco_fold`: F (upaco F r) ≤ paco F r
- `paco_acc`: paco F (paco F r) ≤ paco F r (accumulation)
- `paco_coind`: Main coinduction principle

## References

- [The Power of Parameterization in Coinductive Proof (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [Paco Coq Library](https://github.com/snu-sf/paco)
- [Interaction Trees (POPL 2020)](https://github.com/DeepSpec/InteractionTrees)
-/

namespace Paco

/-!
## Binary Relations

We define binary relations and their lattice structure.
-/

/-- Binary relation on a type -/
abbrev Rel (α : Type*) := α → α → Prop

namespace Rel

variable {α : Type*}

/-- The bottom (empty) relation -/
def bot : Rel α := fun _ _ => False

/-- The top (full) relation -/
def top : Rel α := fun _ _ => True

/-- Union of relations -/
def union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y

/-- Intersection of relations -/
def inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y

/-- Subset ordering on relations -/
def le (R S : Rel α) : Prop := ∀ x y, R x y → S x y

instance : Bot (Rel α) := ⟨bot⟩
instance : Top (Rel α) := ⟨top⟩
instance : Max (Rel α) := ⟨union⟩
instance : Min (Rel α) := ⟨inter⟩
instance : LE (Rel α) := ⟨le⟩
instance : LT (Rel α) := ⟨fun R S => R ≤ S ∧ ¬S ≤ R⟩

@[simp] theorem bot_apply (x y : α) : (⊥ : Rel α) x y ↔ False := Iff.rfl
@[simp] theorem top_apply (x y : α) : (⊤ : Rel α) x y ↔ True := Iff.rfl
@[simp] theorem union_apply (R S : Rel α) (x y : α) : (R ⊔ S) x y ↔ R x y ∨ S x y := Iff.rfl
@[simp] theorem inter_apply (R S : Rel α) (x y : α) : (R ⊓ S) x y ↔ R x y ∧ S x y := Iff.rfl

theorem le_def (R S : Rel α) : R ≤ S ↔ ∀ x y, R x y → S x y := Iff.rfl

theorem le_refl (R : Rel α) : R ≤ R := fun _ _ h => h

theorem le_trans {R S T : Rel α} (hRS : R ≤ S) (hST : S ≤ T) : R ≤ T :=
  fun x y hR => hST x y (hRS x y hR)

theorem le_antisymm {R S : Rel α} (hRS : R ≤ S) (hSR : S ≤ R) : R = S :=
  funext fun x => funext fun y => propext ⟨hRS x y, hSR x y⟩

/-- `Trans` instance for the standalone `Rel.le` ordering, so that `calc R ≤ S ≤ T`
chains synthesize transitivity directly (mathlib's `Trans` instance is keyed on
`Preorder.toLE`, which is the `CompleteLattice`-derived `≤`; this provides the
matching instance for the unbundled `LE (Rel α)`). -/
instance instTransLeRel : @Trans (Rel α) (Rel α) (Rel α) (· ≤ ·) (· ≤ ·) (· ≤ ·) :=
  ⟨le_trans⟩

/-- Supremum of a set of relations -/
protected def sSup (S : Set (Rel α)) : Rel α := fun x y => ∃ R ∈ S, R x y

/-- Infimum of a set of relations -/
protected def sInf (S : Set (Rel α)) : Rel α := fun x y => ∀ R ∈ S, R x y

instance : SupSet (Rel α) := ⟨Rel.sSup⟩
instance : InfSet (Rel α) := ⟨Rel.sInf⟩

/-- Relations form a complete lattice -/
instance instCompleteLattice : CompleteLattice (Rel α) where
  sup := union
  le := le
  lt := fun R S => R ≤ S ∧ ¬S ≤ R
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  le_sup_left := fun R S x y hR => Or.inl hR
  le_sup_right := fun R S x y hS => Or.inr hS
  sup_le := fun R S T hRT hST x y h => h.elim (hRT x y) (hST x y)
  inf := inter
  inf_le_left := fun R S x y ⟨hR, _⟩ => hR
  inf_le_right := fun R S x y ⟨_, hS⟩ => hS
  le_inf := fun R S T hRS hRT x y hR => ⟨hRS x y hR, hRT x y hR⟩
  sSup := Rel.sSup
  isLUB_sSup := fun S =>
    ⟨-- sSup S is an upper bound: every member R ∈ S is ≤ sSup S
      fun R hR x y hRxy => ⟨R, hR, hRxy⟩,
      -- sSup S is the least upper bound: ≤ any upper bound U
      fun U hU x y => fun ⟨T, hT, hTxy⟩ => hU hT x y hTxy⟩
  sInf := Rel.sInf
  isGLB_sInf := fun S =>
    ⟨-- sInf S is a lower bound: sInf S ≤ every member R ∈ S
      fun R hR x y hxy => hxy R hR,
      -- sInf S is the greatest lower bound: any lower bound L ≤ sInf S
      fun L hL x y hLxy T hT => hL hT x y hLxy⟩
  top := top
  bot := bot
  le_top := fun _ _ _ _ => trivial
  bot_le := fun _ _ _ h => h.elim


/-- Helper: lift ≤ into the left side of ⊔. --/
theorem sup_le_sup_left_rel {R S T : Rel α} (h : R ≤ S) : R ⊔ T ≤ S ⊔ T :=
  sup_le_sup h (Rel.le_refl _)

/-- Helper: lift ≤ into the right side of ⊔. --/
theorem sup_le_sup_right_rel {R S T : Rel α} (h : R ≤ S) : T ⊔ R ≤ T ⊔ S :=
  sup_le_sup (Rel.le_refl _) h

theorem sup_bot (R : Rel α) : R ⊔ ⊥ = R := by
  ext x y; simp

theorem bot_sup (R : Rel α) : ⊥ ⊔ R = R := by
  ext x y; simp

/-!
### Scoped Notation and Additional Simp Lemmas
-/

/-- Scoped notation for relation subset -/
scoped infixl:50 " ⊆ᵣ " => Rel.le

theorem sup_assoc (R S T : Rel α) : (R ⊔ S) ⊔ T = R ⊔ (S ⊔ T) := by
  ext x y; simp only [union_apply]; tauto

theorem sup_comm (R S : Rel α) : R ⊔ S = S ⊔ R := by
  ext x y; simp only [union_apply]; tauto

theorem sup_idem (R : Rel α) : R ⊔ R = R := by
  ext x y; simp only [union_apply]; tauto

theorem inf_bot (R : Rel α) : R ⊓ ⊥ = ⊥ := by
  ext x y; simp

theorem bot_inf (R : Rel α) : ⊥ ⊓ R = ⊥ := by
  ext x y; simp

end Rel

/-!
## Monotone Relation Transformers

A relation transformer `F : Rel α → Rel α` is monotone if `R ≤ S` implies `F R ≤ F S`.
-/

/-- A relation transformer is monotone if it preserves the subset ordering -/
def Monotone2 {α : Type*} (F : Rel α → Rel α) : Prop :=
  ∀ R S, R ≤ S → F R ≤ F S

/-- Bundled monotone relation transformer -/
structure MonoRel (α : Type*) where
  /-- The underlying transformer -/
  F : Rel α → Rel α
  /-- Proof of monotonicity -/
  mono : Monotone2 F

namespace MonoRel

variable {α : Type*}

/-- Apply the transformer -/
instance : CoeFun (MonoRel α) (fun _ => Rel α → Rel α) := ⟨MonoRel.F⟩

/-- Monotonicity as an order homomorphism property -/
theorem mono' (F : MonoRel α) {R S : Rel α} (h : R ≤ S) : F R ≤ F S :=
  F.mono R S h

/-- Convert to OrderHom for use with mathlib's gfp -/
def toOrderHom (F : MonoRel α) : Rel α →o Rel α where
  toFun := F.F
  monotone' := fun _ _ h => F.mono _ _ h

end MonoRel

/-!
## Parametrized Greatest Fixed Point

The core paco definitions.
-/

/-- Parametrized greatest fixed point.

`paco F r x y` holds if there exists a relation R such that:
1. R is a post-fixpoint of `fun S => F (S ⊔ r)` (i.e., `R ⊆ F (R ⊔ r)`)
2. R x y holds

This allows accumulating hypotheses in `r` during coinductive proofs. -/
def paco {α : Type*} (F : MonoRel α) (r : Rel α) : Rel α :=
  fun x y => ∃ R : Rel α, (∀ a b, R a b → F (R ⊔ r) a b) ∧ R x y

/-- The "usable" coinductive hypothesis: paco ∪ parameter.

When doing a paco proof, you can use either:
- The coinductive result (left side, requires guardedness/progress)
- Previously accumulated facts (right side, immediately available) -/
def upaco {α : Type*} (F : MonoRel α) (r : Rel α) : Rel α :=
  paco F r ⊔ r

/-!
## Core Lemmas

### Monotonicity
-/

/-- paco is monotone in the parameter: if `r ≤ s` then `paco F r ≤ paco F s` -/
theorem paco_mon {α : Type*} (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    paco F r ≤ paco F s := by
  intro x y ⟨R, hR, hxy⟩
  refine ⟨R, ?_, hxy⟩
  intro a b hab
  apply F.mono' (sup_le_sup_left hrs R)
  exact hR a b hab

/-- upaco is monotone in the parameter -/
theorem upaco_mon {α : Type*} (F : MonoRel α) {r s : Rel α} (hrs : r ≤ s) :
    upaco F r ≤ upaco F s :=
  sup_le_sup (paco_mon F hrs) hrs

/-!
### Unfolding and Folding
-/

/-- Unfold paco: any element in paco satisfies F applied to upaco -/
theorem paco_unfold {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F r ≤ F (upaco F r) := by
  intro x y ⟨R, hR, hxy⟩
  -- Any witness relation R is contained in paco
  have hR_le : R ≤ paco F r := fun _ _ hab => ⟨R, hR, hab⟩
  apply F.mono' (sup_le_sup hR_le (Rel.le_refl r))
  exact hR x y hxy

/-- Fold paco: anything satisfying F applied to upaco is in paco -/
theorem paco_fold {α : Type*} (F : MonoRel α) (r : Rel α) :
    F (upaco F r) ≤ paco F r := by
  intro x y hxy
  refine ⟨F (upaco F r), ?_, hxy⟩
  intro a b hab
  have h1 : paco F r ≤ F (upaco F r) := paco_unfold F r
  have h2 : upaco F r ≤ F (upaco F r) ⊔ r := sup_le_sup h1 (Rel.le_refl r)
  apply F.mono' h2
  exact hab

/-- paco is a fixed point: paco F r = F (upaco F r)

Note: Not marked @[simp] to avoid infinite rewriting loops. -/
theorem paco_eq {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F r = F (upaco F r) :=
  Rel.le_antisymm (paco_unfold F r) (paco_fold F r)

/-!
### Accumulation

The key feature of paco: the ability to accumulate hypotheses.
-/

/-- Composition/multiplication: paco absorbs itself in the parameter -/
theorem paco_acc {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F (paco F r) ≤ paco F r := by
  intro x y ⟨R, hR, hxy⟩
  refine ⟨R ⊔ paco F r, ?_, Or.inl hxy⟩
  intro a b hab
  cases hab with
  | inl hRab =>
    apply F.mono' (le_sup_of_le_left (Rel.le_refl _))
    exact hR a b hRab
  | inr hPab =>
    apply F.mono' (sup_le_sup_right le_sup_right r)
    exact paco_unfold F r a b hPab

/-- Stronger accumulation: paco absorbs upaco in the parameter -/
theorem paco_acc_upaco {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F (upaco F r) ≤ paco F r := by
  intro x y ⟨R, hR, hxy⟩
  refine ⟨R ⊔ paco F r, ?_, Or.inl hxy⟩
  intro a b hab
  cases hab with
  | inl hRab =>
    -- R ⊔ upaco F r = R ⊔ paco F r ⊔ r
    have heq : R ⊔ upaco F r = R ⊔ paco F r ⊔ r := by
      ext u v; simp only [upaco, Rel.union_apply]; tauto
    rw [← heq]
    exact hR a b hRab
  | inr hPab =>
    apply F.mono' (sup_le_sup_right le_sup_right r)
    exact paco_unfold F r a b hPab

/-!
### Coinduction Principle
-/

/-- Main coinduction principle for paco (relational form).

To prove `R ≤ paco F r`, show that R is a post-fixpoint: `∀ a b, R a b → F (R ⊔ r) a b` -/
theorem paco_coind' {α : Type*} (F : MonoRel α) (r : Rel α) (R : Rel α)
    (hpost : ∀ a b, R a b → F (R ⊔ r) a b) : R ≤ paco F r :=
  fun _ _ hxy => ⟨R, hpost, hxy⟩

/-- Coinduction principle (pointwise form).

To prove `paco F r x y`, provide a relation R with:
1. `R x y` (the goal is in R)
2. `∀ a b, R a b → F (R ⊔ r) a b` (R is a post-fixpoint modulo r) -/
theorem paco_coind {α : Type*} (F : MonoRel α) (R : Rel α) (r : Rel α)
    {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ r) a b)
    (hxy : R x y) : paco F r x y :=
  paco_coind' F r R hpost x y hxy

/-!
### Relationship to Greatest Fixed Point
-/

/-- paco with empty parameter equals the greatest fixed point -/
theorem paco_bot {α : Type*} (F : MonoRel α) :
    paco F ⊥ = F.toOrderHom.gfp := by
  apply Rel.le_antisymm
  · -- paco F ⊥ ≤ gfp F
    intro x y ⟨R, hR, hxy⟩
    -- R is a post-fixpoint since R ⊔ ⊥ = R
    have hR' : R ≤ F.toOrderHom R := by
      intro a b hab
      have := hR a b hab
      simp only [Rel.sup_bot] at this
      exact this
    -- le_gfp gives R ≤ gfp F, apply pointwise
    exact OrderHom.le_gfp F.toOrderHom hR' x y hxy
  · -- gfp F ≤ paco F ⊥
    intro x y hxy
    refine ⟨F.toOrderHom.gfp, ?_, hxy⟩
    intro a b hab
    simp only [Rel.sup_bot]
    -- gfp is a fixed point, so gfp = F gfp, i.e., F.gfp a b → F (F.gfp) a b
    have heq : F.toOrderHom.gfp = F.toOrderHom F.toOrderHom.gfp := F.toOrderHom.map_gfp.symm
    rw [heq] at hab
    exact hab

/-- upaco with empty parameter equals the greatest fixed point -/
@[simp]
theorem upaco_bot {α : Type*} (F : MonoRel α) :
    upaco F ⊥ = paco F ⊥ := by
  simp only [upaco, Rel.sup_bot]

/-!
### Additional Utility Lemmas
-/

/-- Left injection into upaco -/
@[simp]
theorem paco_le_upaco {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F r ≤ upaco F r :=
  le_sup_left

/-- Right injection into upaco -/
@[simp]
theorem r_le_upaco {α : Type*} (F : MonoRel α) (r : Rel α) :
    r ≤ upaco F r :=
  le_sup_right

/-- upaco is idempotent in a sense -/
theorem upaco_sup_r {α : Type*} (F : MonoRel α) (r : Rel α) :
    upaco F r ⊔ r = upaco F r := by
  apply Rel.le_antisymm
  · intro x y h; rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
  · intro x y h; exact Or.inl h

/-- F applied to upaco contains paco -/
theorem paco_le_F_upaco {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F r ≤ F (upaco F r) :=
  paco_unfold F r

/-!
### Generalized Monotonicity

paco is monotone in both the functor and parameter.
-/

/-- Generalized monotonicity: paco is monotone in both F and r.

If `F₁ R ≤ F₂ R` for all R, and `r ≤ s`, then `paco F₁ r ≤ paco F₂ s`. -/
theorem paco_mon_gen {α : Type*} (F₁ F₂ : MonoRel α) {r s : Rel α}
    (hF : ∀ R, F₁ R ≤ F₂ R) (hrs : r ≤ s) :
    paco F₁ r ≤ paco F₂ s := by
  intro x y ⟨R, hR, hxy⟩
  refine ⟨R, ?_, hxy⟩
  intro a b hab
  -- hR gives F₁ (R ⊔ r) a b
  -- We need F₂ (R ⊔ s) a b
  -- First: F₁ (R ⊔ r) ≤ F₁ (R ⊔ s) by monotonicity since r ≤ s
  -- Then: F₁ (R ⊔ s) ≤ F₂ (R ⊔ s) by hF
  have h1 : F₁ (R ⊔ r) a b := hR a b hab
  have h2 : F₁ (R ⊔ r) ≤ F₁ (R ⊔ s) := F₁.mono' (sup_le_sup_left hrs R)
  have h3 : F₁ (R ⊔ s) ≤ F₂ (R ⊔ s) := hF (R ⊔ s)
  exact h3 a b (h2 a b h1)

/-- paco is antitone in F: if F₁ R ≤ F₂ R for all R, then paco F₁ r ≤ paco F₂ r -/
theorem paco_mon_F {α : Type*} (F₁ F₂ : MonoRel α) (r : Rel α)
    (hF : ∀ R, F₁ R ≤ F₂ R) :
    paco F₁ r ≤ paco F₂ r :=
  paco_mon_gen F₁ F₂ hF (Rel.le_refl r)

/-!
### Extracting GFP Results
-/

/-- Extract a gfp result from paco with any parameter.

If the parameter `r` is already contained in `gfp F`, then `paco F r` is also
contained in `gfp F`. This allows "closing" a paco proof to get a pure gfp result. -/
theorem paco_final {α : Type*} (F : MonoRel α) (r : Rel α) (hr : r ≤ F.toOrderHom.gfp) :
    paco F r ≤ F.toOrderHom.gfp := by
  intro x y ⟨R, hR, hxy⟩
  -- Use R ⊔ gfp F as a post-fixpoint witness
  -- This works because gfp F = F (gfp F) and R ⊆ F (R ⊔ r) ⊆ F (R ⊔ gfp F)
  have hRgfp_post : R ⊔ F.toOrderHom.gfp ≤ F.toOrderHom (R ⊔ F.toOrderHom.gfp) := by
    intro a b hab
    cases hab with
    | inl hRab =>
      -- R a b, so F (R ⊔ r) a b by hR
      -- Need F (R ⊔ gfp F) a b
      -- Since r ≤ gfp F, we have R ⊔ r ≤ R ⊔ gfp F
      have h1 : F (R ⊔ r) a b := hR a b hRab
      have h2 : R ⊔ r ≤ R ⊔ F.toOrderHom.gfp := sup_le_sup_left hr R
      exact F.mono' h2 a b h1
    | inr hgfp_ab =>
      -- gfp F a b, so F (gfp F) a b since gfp = F gfp
      -- Need F (R ⊔ gfp F) a b
      have hgfp_eq : F.toOrderHom.gfp = F.toOrderHom F.toOrderHom.gfp := F.toOrderHom.map_gfp.symm
      rw [hgfp_eq] at hgfp_ab
      exact F.mono' le_sup_right a b hgfp_ab
  exact OrderHom.le_gfp F.toOrderHom hRgfp_post x y (Or.inl hxy)

/-- Alternative: if paco F r holds and r ≤ paco F ⊥, then paco F ⊥ holds -/
theorem paco_close {α : Type*} (F : MonoRel α) (r : Rel α) (hr : r ≤ paco F ⊥) :
    paco F r ≤ paco F ⊥ :=
  le_trans (paco_mon F hr) (paco_acc F ⊥)

/-!
### Additional Accumulation Lemmas
-/

/-- Accumulate paco into upaco parameter.

This is the canonical accumulation pattern: facts proven via paco can be accumulated
into the parameter for future proofs. -/
theorem paco_accum {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F r ≤ paco F (upaco F r) :=
  paco_mon F (r_le_upaco F r)

/-!
### Paco/Upaco Idempotence
-/

/-- paco is idempotent over an upaco parameter. --/
theorem paco_upaco_eq {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F (upaco F r) = paco F r := by
  apply Rel.le_antisymm
  · exact paco_acc_upaco F r
  · exact paco_accum F r

/-- paco is idempotent when its parameter already contains paco. --/
theorem paco_idem {α : Type*} (F : MonoRel α) (r : Rel α) :
    paco F (r ⊔ paco F r) = paco F r := by
  have hcomm : (r ⊔ paco F r) = upaco F r := by
    apply Rel.le_antisymm
    · intro x y h; rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro x y h; rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
  rw [hcomm]; exact paco_upaco_eq F r

/-!
### Coinduction with Accumulation
-/

/-- Coinduction principle that allows using previously proven paco facts.

This combines `paco_coind` with accumulation: the coinductive hypothesis
includes both the witness relation R and the accumulated facts in r. -/
theorem paco_coind_acc {α : Type*} (F : MonoRel α) (R : Rel α) (r : Rel α)
    {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ upaco F r) a b)
    (hxy : R x y) : paco F r x y := by
  -- First get paco F (upaco F r) x y, then use paco_acc_upaco
  have h : paco F (upaco F r) x y := paco_coind F R (upaco F r) hpost hxy
  exact paco_acc_upaco F r x y h

end Paco
