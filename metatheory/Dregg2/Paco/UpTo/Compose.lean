import Dregg2.Paco.UpTo.Compat
import Dregg2.Paco.UpTo.Closures
import Dregg2.Paco.UpTo.WCompat

/-!
# Closure Composition and Union Lemmas

Systematic composition and union results for closures.
This module provides lemmas about how closures interact when composed or combined.
-/

namespace Paco

variable {α : Type*}

/-!
## Closure Union

The union of two closure operators applies both and takes the union of results.
-/

/-- Union of two closure operators -/
def cloUnion (clo₁ clo₂ : Rel α → Rel α) : Rel α → Rel α :=
  fun R => clo₁ R ⊔ clo₂ R

/-- Notation for closure union -/
scoped infixl:65 " ⊔ᶜ " => cloUnion

/-- Closure union is monotone when both components are monotone -/
theorem cloMono_union {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : CloMono clo₁) (h₂ : CloMono clo₂) :
    CloMono (clo₁ ⊔ᶜ clo₂) := by
  intro R S hRS x y h
  cases h with
  | inl h₁r => left; exact h₁ R S hRS x y h₁r
  | inr h₂r => right; exact h₂ R S hRS x y h₂r

/-- Left component is contained in closure union -/
theorem clo_le_cloUnion_left (clo₁ clo₂ : Rel α → Rel α) (R : Rel α) :
    clo₁ R ≤ (clo₁ ⊔ᶜ clo₂) R :=
  fun _ _ h => Or.inl h

/-- Right component is contained in closure union -/
theorem clo_le_cloUnion_right (clo₁ clo₂ : Rel α → Rel α) (R : Rel α) :
    clo₂ R ≤ (clo₁ ⊔ᶜ clo₂) R :=
  fun _ _ h => Or.inr h

/-- gupaco_clo is monotone in the closure operator.

If clo₁ ≤ clo₂ pointwise, then gupaco_clo F clo₁ R ≤ gupaco_clo F clo₂ R.
This is the key lemma for proving wcompat_union. -/
theorem gupaco_clo_mono_clo (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h_clo : ∀ R, clo₁ R ≤ clo₂ R) (R : Rel α) :
    gupaco_clo F clo₁ R ≤ gupaco_clo F clo₂ R := by
  -- gupaco_clo F clo R = rclo clo (paco (composeRclo F clo) R ⊔ R)
  -- Need to show both:
  -- 1. rclo clo₁ ≤ rclo clo₂ (via rclo.mono_clo)
  -- 2. paco (composeRclo F clo₁) R ≤ paco (composeRclo F clo₂) R (via paco_mon_gen)
  have h_rclo_clo_le : ∀ S, rclo clo₁ S ≤ rclo clo₂ S := fun S => rclo.mono_clo h_clo
  have h_paco_le : paco (composeRclo F clo₁) R ≤ paco (composeRclo F clo₂) R := by
    apply paco_mon_gen
    · intro S x y hFrclo
      simp only [composeRclo_def] at hFrclo ⊢
      exact F.mono' (h_rclo_clo_le S) x y hFrclo
    · exact Rel.le_refl R
  simp only [gupaco_clo_def, gpaco_clo_def, Rel.sup_idem]
  intro x y hrclo
  -- hrclo : rclo clo₁ (paco (composeRclo F clo₁) R ⊔ R) x y
  -- Goal: rclo clo₂ (paco (composeRclo F clo₂) R ⊔ R) x y
  have h_inner_le : paco (composeRclo F clo₁) R ⊔ R ≤ paco (composeRclo F clo₂) R ⊔ R :=
    sup_le_sup_right h_paco_le R
  have h_rclo_inner : rclo clo₁ (paco (composeRclo F clo₁) R ⊔ R) ≤
                      rclo clo₁ (paco (composeRclo F clo₂) R ⊔ R) := rclo.mono h_inner_le
  have h_rclo_outer : rclo clo₁ (paco (composeRclo F clo₂) R ⊔ R) ≤
                      rclo clo₂ (paco (composeRclo F clo₂) R ⊔ R) := h_rclo_clo_le _
  exact h_rclo_outer x y (h_rclo_inner x y hrclo)

/-- Union of weakly compatible closures is weakly compatible. -/
theorem wcompat_union (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : WCompatible F clo₁) (h₂ : WCompatible F clo₂) :
    WCompatible F (clo₁ ⊔ᶜ clo₂) := by
  intro R x y h
  cases h with
  | inl h₁r =>
    -- h₁r : clo₁ (F R) x y
    -- From h₁: clo₁ (F R) ≤ F (gupaco_clo F clo₁ R)
    have h_step := h₁ R x y h₁r
    -- h_step : F (gupaco_clo F clo₁ R) x y
    -- Need: F (gupaco_clo F (clo₁ ⊔ᶜ clo₂) R) x y
    have h_mono : gupaco_clo F clo₁ R ≤ gupaco_clo F (clo₁ ⊔ᶜ clo₂) R :=
      gupaco_clo_mono_clo F (fun S => clo_le_cloUnion_left clo₁ clo₂ S) R
    exact F.mono' h_mono x y h_step
  | inr h₂r =>
    -- h₂r : clo₂ (F R) x y
    have h_step := h₂ R x y h₂r
    have h_mono : gupaco_clo F clo₂ R ≤ gupaco_clo F (clo₁ ⊔ᶜ clo₂) R :=
      gupaco_clo_mono_clo F (fun S => clo_le_cloUnion_right clo₁ clo₂ S) R
    exact F.mono' h_mono x y h_step

/-!
## Composition Monotonicity
-/

/-- Composition of monotone closures is monotone -/
theorem cloMono_comp {clo₁ clo₂ : Rel α → Rel α}
    (h₁ : CloMono clo₁) (h₂ : CloMono clo₂) :
    CloMono (clo₁ ∘ clo₂) := by
  intro R S hRS
  exact h₁ _ _ (h₂ _ _ hRS)

/-!
## Closure Idempotence

Many closures satisfy `clo (clo R) = clo R`.
-/

/-- reflClosure is idempotent -/
theorem reflClosure_idem (R : Rel α) :
    reflClosure (reflClosure R) = reflClosure R := by
  ext x y
  constructor
  · intro h
    cases h with
    | inl heq => left; exact heq
    | inr hinner =>
      cases hinner with
      | inl heq' => left; exact heq'
      | inr hR => right; exact hR
  · intro h
    right; exact h

/-- symmClosure is idempotent -/
theorem symmClosure_idem (R : Rel α) :
    symmClosure (symmClosure R) = symmClosure R := by
  ext x y
  constructor
  · intro h
    cases h with
    | inl hs => exact hs
    | inr hs =>
      cases hs with
      | inl hr => right; exact hr
      | inr hr => left; exact hr
  · intro h
    left; exact h

/-- transClosure is idempotent -/
theorem transClosure_idem (R : Rel α) :
    transClosure (transClosure R) = transClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | base hinner => exact hinner
    | trans _ _ ih₁ ih₂ => exact transClosure.trans ih₁ ih₂
  · intro h
    exact transClosure.base h

/-- rtClosure is idempotent -/
theorem rtClosure_idem (R : Rel α) :
    rtClosure (rtClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hinner => exact hinner
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    exact rtClosure.base h

/-- eqvClosure is idempotent -/
theorem eqvClosure_idem (R : Rel α) :
    eqvClosure (eqvClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hinner => exact hinner
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    exact eqvClosure.base h

/-!
## Closure Absorption

When one closure subsumes another.
-/

/-- rtClosure absorbs reflClosure -/
theorem rtClosure_reflClosure (R : Rel α) :
    rtClosure (reflClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hrefl =>
      cases hrefl with
      | inl heq => subst heq; exact rtClosure.refl
      | inr hR => exact rtClosure.base hR
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hR => exact rtClosure.base (Or.inr hR)
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- rtClosure absorbs transClosure -/
theorem rtClosure_transClosure (R : Rel α) :
    rtClosure (transClosure R) = rtClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base htrans =>
      induction htrans with
      | base hR => exact rtClosure.base hR
      | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact rtClosure.refl
    | base hR => exact rtClosure.base (transClosure.base hR)
    | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- eqvClosure absorbs reflClosure -/
theorem eqvClosure_reflClosure (R : Rel α) :
    eqvClosure (reflClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hrefl =>
      cases hrefl with
      | inl heq => subst heq; exact eqvClosure.refl
      | inr hR => exact eqvClosure.base hR
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hR => exact eqvClosure.base (Or.inr hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-- eqvClosure absorbs symmClosure -/
theorem eqvClosure_symmClosure (R : Rel α) :
    eqvClosure (symmClosure R) = eqvClosure R := by
  ext x y
  constructor
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hsymm =>
      cases hsymm with
      | inl hR => exact eqvClosure.base hR
      | inr hR => exact eqvClosure.symm (eqvClosure.base hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂
  · intro h
    induction h with
    | refl => exact eqvClosure.refl
    | base hR => exact eqvClosure.base (Or.inl hR)
    | symm _ ih => exact eqvClosure.symm ih
    | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-!
## Closure Containment
-/

/-- R is contained in reflClosure R -/
theorem le_reflClosure (R : Rel α) : R ≤ reflClosure R :=
  fun _ _ h => Or.inr h

/-- R is contained in symmClosure R -/
theorem le_symmClosure (R : Rel α) : R ≤ symmClosure R :=
  fun _ _ h => Or.inl h

/-- R is contained in transClosure R -/
theorem le_transClosure (R : Rel α) : R ≤ transClosure R :=
  fun _ _ h => transClosure.base h

/-- R is contained in rtClosure R -/
theorem le_rtClosure (R : Rel α) : R ≤ rtClosure R :=
  fun _ _ h => rtClosure.base h

/-- R is contained in eqvClosure R -/
theorem le_eqvClosure (R : Rel α) : R ≤ eqvClosure R :=
  fun _ _ h => eqvClosure.base h

/-!
## Convenience re-exports

Compatibility composition (re-export from Compat.lean for convenience)
-/

/-- If clo₁ and clo₂ are both compatible with F, and clo₁ is monotone,
    then clo₁ ∘ clo₂ is compatible with F. -/
theorem compatible_compose (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁_mono : CloMono clo₁) (h₁ : Compatible F clo₁) (h₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂) :=
  compatible_comp F h₁_mono h₁ h₂

/-!
## Identity simplifications
-/

@[simp] theorem id_comp_clo (clo : Rel α → Rel α) : id ∘ clo = clo := rfl

@[simp] theorem clo_comp_id (clo : Rel α → Rel α) : clo ∘ id = clo := rfl

/-!
## Conditional Compatibility Helpers

Wrappers that give clearer names to the conditional compatibility theorems.
-/

/-- reflClosure is compatible when F preserves reflexivity -/
theorem reflClosure_compat_of_refl (F : MonoRel α)
    (hF : ∀ R, (∀ x, R x x) → ∀ x, F R x x) :
    Compatible F reflClosure :=
  reflClosure_compatible F hF

/-- symmClosure is compatible when F commutes with symmetry -/
theorem symmClosure_compat_of_symm (F : MonoRel α)
    (hF : ∀ R x y, F R x y → F (symmClosure R) y x) :
    Compatible F symmClosure :=
  symmClosure_compatible F hF

/-- congClosure is compatible when F respects the function -/
theorem congClosure_compat_of_cong (F : MonoRel α) (f : α → α)
    (hF : ∀ R x y, F R x y → F (congClosure f R) (f x) (f y)) :
    Compatible F (congClosure f) :=
  congClosure_compatible F f hF

end Paco
