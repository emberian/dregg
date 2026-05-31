import Dregg2.Paco.UpTo.Compat

/-!
# Common Up-To Closures

Standard closure operators that are commonly used with up-to techniques.

## Main Definitions

- `reflClosure`: Reflexive closure (adds identity pairs)
- `symmClosure`: Symmetric closure (adds reverse pairs)
- `transClosure`: Transitive closure
- `rtClosure`: Reflexive-transitive closure
- `eqvClosure`: Equivalence closure (reflexive, symmetric, transitive)
- `congClosure`: Congruence closure (lift through a function)

## Properties

Each closure is shown to be monotone. Compatibility results are conditional
on properties of the generating function F.
-/

namespace Paco

variable {α : Type*}

/-- Reflexive closure: adds identity pairs -/
def reflClosure (R : Rel α) : Rel α := fun x y => x = y ∨ R x y

/-- Symmetric closure: adds reverse pairs -/
def symmClosure (R : Rel α) : Rel α := fun x y => R x y ∨ R y x

/-- Transitive closure: iteratively applies R -/
inductive transClosure (R : Rel α) : Rel α where
  | base (h : R x y) : transClosure R x y
  | trans (h₁ : transClosure R x z) (h₂ : transClosure R z y) : transClosure R x y

/-- Reflexive-transitive closure -/
inductive rtClosure (R : Rel α) : Rel α where
  | refl : rtClosure R x x
  | base (h : R x y) : rtClosure R x y
  | trans (h₁ : rtClosure R x z) (h₂ : rtClosure R z y) : rtClosure R x y

/-- Equivalence closure (reflexive, symmetric, transitive) -/
inductive eqvClosure (R : Rel α) : Rel α where
  | refl : eqvClosure R x x
  | base (h : R x y) : eqvClosure R x y
  | symm (h : eqvClosure R x y) : eqvClosure R y x
  | trans (h₁ : eqvClosure R x z) (h₂ : eqvClosure R z y) : eqvClosure R x y

/-- Congruence closure: lift R through a function -/
def congClosure (f : α → α) (R : Rel α) : Rel α :=
  fun x y => ∃ a b, R a b ∧ x = f a ∧ y = f b

/-!
## Closure Properties
-/

/-- reflClosure is monotone -/
theorem reflClosure_mono : CloMono (reflClosure (α := α)) := by
  intro R S hRS x y h
  cases h with
  | inl heq => left; exact heq
  | inr hR => right; exact hRS x y hR

/-- symmClosure is monotone -/
theorem symmClosure_mono : CloMono (symmClosure (α := α)) := by
  intro R S hRS x y h
  cases h with
  | inl hR => left; exact hRS x y hR
  | inr hR => right; exact hRS y x hR

/-- transClosure is monotone -/
theorem transClosure_mono : CloMono (transClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | base hR => exact transClosure.base (hRS _ _ hR)
  | trans _ _ ih₁ ih₂ => exact transClosure.trans ih₁ ih₂

/-- rtClosure is monotone -/
theorem rtClosure_mono : CloMono (rtClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | refl => exact rtClosure.refl
  | base hR => exact rtClosure.base (hRS _ _ hR)
  | trans _ _ ih₁ ih₂ => exact rtClosure.trans ih₁ ih₂

/-- eqvClosure is monotone -/
theorem eqvClosure_mono : CloMono (eqvClosure (α := α)) := by
  intro R S hRS x y h
  induction h with
  | refl => exact eqvClosure.refl
  | base hR => exact eqvClosure.base (hRS _ _ hR)
  | symm _ ih => exact eqvClosure.symm ih
  | trans _ _ ih₁ ih₂ => exact eqvClosure.trans ih₁ ih₂

/-- congClosure is monotone (in R) for fixed f -/
theorem congClosure_mono (f : α → α) : CloMono (congClosure f) := by
  intro R S hRS x y ⟨a, b, hR, hxa, hyb⟩
  exact ⟨a, b, hRS a b hR, hxa, hyb⟩

/-!

## Compatibility Results

Note: Compatibility of these closures depends on the structure of F.
The following are conditional results that hold when F has certain properties.
-/

/-- If F preserves transitive closure, then transClosure is compatible with F. -/
theorem transClosure_compatible_of_preserve (F : MonoRel α)
    (h : ∀ R, transClosure (F R) ≤ F (transClosure R)) :
    Compatible F (transClosure (α := α)) := by
  intro R x y hTR
  exact h R x y hTR


/-- reflClosure is compatible if F is reflexive (F R x x for all x when R is reflexive) -/
theorem reflClosure_compatible (F : MonoRel α)
    (hF_refl : ∀ R : Rel α, (∀ x, R x x) → ∀ x, F R x x) :
    Compatible F reflClosure := by
  intro R x y h
  cases h with
  | inl heq =>
    subst heq
    apply hF_refl (reflClosure R)
    intro z
    left; rfl
  | inr hFR =>
    apply F.mono' (fun a b hab => Or.inr hab)
    exact hFR

/-- symmClosure is compatible if F commutes with symmetry -/
theorem symmClosure_compatible (F : MonoRel α)
    (hF_symm : ∀ R x y, F R x y → F (symmClosure R) y x) :
    Compatible F symmClosure := by
  intro R x y h
  cases h with
  | inl hFR =>
    apply F.mono' (fun a b hab => Or.inl hab)
    exact hFR
  | inr hFR =>
    exact hF_symm R y x hFR

/-- Congruence closure is compatible if F respects the function f -/
theorem congClosure_compatible (F : MonoRel α) (f : α → α)
    (hF_cong : ∀ R x y, F R x y → F (congClosure f R) (f x) (f y)) :
    Compatible F (congClosure f) := by
  intro R x y ⟨a, b, hFab, hxa, hyb⟩
  subst hxa hyb
  exact hF_cong R a b hFab

end Paco
