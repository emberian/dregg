import Dregg2.Paco.Basic

/-!
# Generalized Parametrized Coinduction (GPaco)

This module extends paco with a **guarded** parameter that only becomes
available after making progress (applying F).

## Overview

GPaco adds a second parameter `g` (guarded) in addition to `r` (available):
- `r`: facts immediately available (base case)
- `g`: facts available after one F step (the guard is "released")

Based on the Coq gpaco library, when the closure operator is identity:
`gpaco F r g = paco F (r ⊔ g) ⊔ r`

## Main Definitions

- `gpaco F r g`: Generalized paco with available and guarded parameters
- `gupaco F r g`: The usable hypothesis after unfolding

## References

- [GPaco Paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [ITrees gpaco.v](https://github.com/DeepSpec/InteractionTrees)
-/

namespace Paco

variable {α : Type*}

/-!
## GPaco Definitions
-/

/-- Generalized paco with available parameter `r` and guarded parameter `g`.

`gpaco F r g = paco F (r ⊔ g) ⊔ r`

- `r`: immediately available (base case, no F required)
- `g`: guarded (becomes available after one F step) -/
def gpaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  paco F (r ⊔ g) ⊔ r

/-- The usable coinductive hypothesis for gpaco after unfolding.

`gupaco F r g = gpaco F r g ⊔ g = paco F (r ⊔ g) ⊔ r ⊔ g`

This equals `upaco F (r ⊔ g)` (the guard g is released). -/
def gupaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  gpaco F r g ⊔ g

/-!
## Basic Properties
-/

theorem gpaco_def (F : MonoRel α) (r g : Rel α) :
    gpaco F r g = paco F (r ⊔ g) ⊔ r := rfl

theorem gupaco_def (F : MonoRel α) (r g : Rel α) :
    gupaco F r g = gpaco F r g ⊔ g := rfl

/-- gupaco equals upaco with merged parameters -/
@[simp]
theorem gupaco_eq_upaco (F : MonoRel α) (r g : Rel α) :
    gupaco F r g = upaco F (r ⊔ g) := by
  ext x y
  simp only [gupaco, gpaco, upaco, Rel.union_apply]
  tauto

/-- gpaco with no guarded parameter -/
@[simp]
theorem gpaco_bot_g (F : MonoRel α) (r : Rel α) :
    gpaco F r ⊥ = upaco F r := by
  simp only [gpaco, Rel.sup_bot, upaco]

/-- gpaco with no available parameter -/
@[simp]
theorem gpaco_bot_r (F : MonoRel α) (g : Rel α) :
    gpaco F ⊥ g = paco F g := by
  simp only [gpaco, Rel.bot_sup]
  ext x y
  simp only [Rel.union_apply, Rel.bot_apply, or_false]

/-!
## Monotonicity
-/

/-- gpaco is monotone in r -/
theorem gpaco_mon_r (F : MonoRel α) (g : Rel α) {r r' : Rel α} (hr : r ≤ r') :
    gpaco F r g ≤ gpaco F r' g := by
  simp only [gpaco]
  apply sup_le_sup
  · exact paco_mon F (sup_le_sup_right hr g)
  · exact hr

/-- gpaco is monotone in g -/
theorem gpaco_mon_g (F : MonoRel α) (r : Rel α) {g g' : Rel α} (hg : g ≤ g') :
    gpaco F r g ≤ gpaco F r g' := by
  simp only [gpaco]
  apply sup_le_sup_right
  exact paco_mon F (sup_le_sup_left hg r)

/-- gpaco is monotone in both parameters -/
theorem gpaco_mon (F : MonoRel α) {r r' g g' : Rel α}
    (hr : r ≤ r') (hg : g ≤ g') : gpaco F r g ≤ gpaco F r' g' :=
  Rel.le_trans (gpaco_mon_r F g hr) (gpaco_mon_g F r' hg)

/-- gupaco is monotone in both parameters -/
theorem gupaco_mon (F : MonoRel α) {r r' g g' : Rel α}
    (hr : r ≤ r') (hg : g ≤ g') : gupaco F r g ≤ gupaco F r' g' := by
  simp only [gupaco]
  exact sup_le_sup (gpaco_mon F hr hg) hg

/-!
## Injections
-/

/-- r injects into gpaco (base case) -/
theorem r_le_gpaco (F : MonoRel α) (r g : Rel α) : r ≤ gpaco F r g :=
  le_sup_right

/-- paco F (r ⊔ g) injects into gpaco -/
theorem paco_le_gpaco (F : MonoRel α) (r g : Rel α) :
    paco F (r ⊔ g) ≤ gpaco F r g :=
  le_sup_left

/-- gpaco injects into gupaco -/
theorem gpaco_le_gupaco (F : MonoRel α) (r g : Rel α) :
    gpaco F r g ≤ gupaco F r g :=
  le_sup_left

/-- g injects into gupaco (guard released) -/
theorem g_le_gupaco (F : MonoRel α) (r g : Rel α) : g ≤ gupaco F r g :=
  le_sup_right

/-!
## Unfolding and Folding

The key property: unfolding gpaco releases the guard g.
-/

/-- Unfold gpaco: releases the guard g into gupaco.

`gpaco F r g ≤ F (gupaco F r g) ⊔ r`

After unfolding, the guard g becomes available in gupaco. -/
theorem gpaco_unfold (F : MonoRel α) (r g : Rel α) :
    gpaco F r g ≤ F (gupaco F r g) ⊔ r := by
  intro x y hxy
  cases hxy with
  | inl hpaco =>
    -- paco F (r ⊔ g) x y
    left
    have h := paco_unfold F (r ⊔ g) x y hpaco
    -- h : F (upaco F (r ⊔ g)) x y
    rw [gupaco_eq_upaco]
    exact h
  | inr hr =>
    right
    exact hr

/-- Fold into gpaco from F (gupaco) -/
theorem gpaco_fold (F : MonoRel α) (r g : Rel α) :
    F (gupaco F r g) ≤ gpaco F r g := by
  intro x y hxy
  left
  rw [gupaco_eq_upaco] at hxy
  exact paco_fold F (r ⊔ g) x y hxy

/-- gpaco step equation

Note: Not marked @[simp] to avoid infinite rewriting loops. -/
theorem gpaco_step (F : MonoRel α) (r g : Rel α) :
    gpaco F r g = F (gupaco F r g) ⊔ r := by
  apply Rel.le_antisymm
  · exact gpaco_unfold F r g
  · intro x y hxy
    cases hxy with
    | inl hF => exact gpaco_fold F r g x y hF
    | inr hr => exact r_le_gpaco F r g x y hr

/-!
## Accumulation
-/

/-- gpaco absorbs gupaco in the guard position -/
theorem gpaco_acc (F : MonoRel α) (r g : Rel α) :
    gpaco F r (gupaco F r g) ≤ gpaco F r g := by
  simp only [gpaco, gupaco]
  intro x y hxy
  cases hxy with
  | inl hpaco =>
    left
    -- r ⊔ (gpaco F r g ⊔ g) ≤ upaco F (r ⊔ g)
    have hle : r ⊔ (gpaco F r g ⊔ g) ≤ upaco F (r ⊔ g) := by
      intro a b hab
      simp only [gpaco, upaco, Rel.union_apply] at hab ⊢
      tauto
    have hpaco' := paco_mon F hle x y hpaco
    exact paco_acc_upaco F (r ⊔ g) x y hpaco'
  | inr hr =>
    right; exact hr

/-!
## Coinduction Principles
-/

/-- Simple coinduction for gpaco (no base case in hypothesis).

To prove `gpaco F r g x y`, provide R with:
1. `R x y`
2. `∀ a b, R a b → F (R ⊔ gupaco F r g) a b` -/
theorem gpaco_coind' (F : MonoRel α) (R : Rel α) (r g : Rel α)
    (hpost : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b)
    : R ≤ gpaco F r g := by
  intro x y hxy
  left -- go into paco F (r ⊔ g)
  apply paco_coind F (R ⊔ paco F (r ⊔ g)) (r ⊔ g)
  · intro a b hab
    cases hab with
    | inl hRab =>
      have hFab := hpost a b hRab
      -- hFab : F (R ⊔ gupaco F r g) a b
      -- Need: F ((R ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g)) a b
      have hle : R ⊔ gupaco F r g ≤ (R ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
        intro u v huv
        cases huv with
        | inl hR => left; left; exact hR
        | inr hgu =>
          rw [gupaco_eq_upaco] at hgu
          simp only [upaco, Rel.union_apply] at hgu
          cases hgu with
          | inl hp => left; right; exact hp
          | inr hrg => right; exact hrg
      exact F.mono' hle a b hFab
    | inr hpab =>
      have h := paco_unfold F (r ⊔ g) a b hpab
      have hle : upaco F (r ⊔ g) ≤ (R ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
        intro u v huv
        simp only [upaco, Rel.union_apply] at huv
        cases huv with
        | inl hp => left; right; exact hp
        | inr hrg => right; exact hrg
      exact F.mono' hle a b h
  · left; exact hxy

/-- Full coinduction for gpaco with base case.

To prove `gpaco F r g x y`, provide R with:
1. `R x y`
2. `∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b`

The base case `r a b` is handled by gpaco's definition: `gpaco = paco ⊔ r`. -/
theorem gpaco_coind (F : MonoRel α) (R : Rel α) (r g : Rel α)
    {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b)
    (hxy : R x y) : gpaco F r g x y := by
  -- Key insight: for elements where hpost returns r, they go to the r part of gpaco
  -- For elements where hpost returns F, they go to the paco part
  --
  -- Define the "productive" subset of R
  let R' : Rel α := fun a b => R a b ∧ ¬r a b
  -- If R' x y, use the paco coinduction
  -- Otherwise, r x y and we use r_le_gpaco
  by_cases hr : r x y
  · exact r_le_gpaco F r g x y hr
  · -- Need to show gpaco F r g x y via paco
    left
    apply paco_coind F (R' ⊔ paco F (r ⊔ g)) (r ⊔ g)
    · intro a b hab
      cases hab with
      | inl hR'ab =>
        obtain ⟨hRab, hnr⟩ := hR'ab
        cases hpost a b hRab with
        | inl hFab =>
          have hle : R ⊔ gupaco F r g ≤ (R' ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
            intro u v huv
            cases huv with
            | inl hR =>
              by_cases hr' : r u v
              · right; left; exact hr'
              · left; left; exact ⟨hR, hr'⟩
            | inr hgu =>
              rw [gupaco_eq_upaco] at hgu
              simp only [upaco, Rel.union_apply] at hgu
              cases hgu with
              | inl hp => left; right; exact hp
              | inr hrg => right; exact hrg
          exact F.mono' hle a b hFab
        | inr hrab =>
          -- Contradiction: we have ¬r a b but hpost gave r a b
          exact absurd hrab hnr
      | inr hpab =>
        have h := paco_unfold F (r ⊔ g) a b hpab
        have hle : upaco F (r ⊔ g) ≤ (R' ⊔ paco F (r ⊔ g)) ⊔ (r ⊔ g) := by
          intro u v huv
          simp only [upaco, Rel.union_apply] at huv
          cases huv with
          | inl hp => left; right; exact hp
          | inr hrg => right; exact hrg
        exact F.mono' hle a b h
    · left; exact ⟨hxy, hr⟩

/-!
## Relationship to paco
-/

/-- gpaco with equal parameters reduces to upaco -/
@[simp]
theorem gpaco_diag (F : MonoRel α) (r : Rel α) :
    gpaco F r r = upaco F r := by
  simp only [gpaco, upaco, Rel.sup_idem]

/-- Converting paco to gpaco -/
theorem paco_to_gpaco (F : MonoRel α) (r g : Rel α) :
    paco F (r ⊔ g) ≤ gpaco F r g := by
  intro x y h
  left
  exact h

end Paco
