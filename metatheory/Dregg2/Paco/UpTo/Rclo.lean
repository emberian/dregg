import Dregg2.Paco.Basic

/-!
# Reflexive-Transitive Closure (rclo)

The core building block for up-to techniques. `rclo clo R` contains:
- Everything in R (base case)
- Everything obtained by applying clo to any relation contained in rclo
-/

namespace Paco

variable {α : Type*}

/-- Reflexive-transitive closure of a relation under a closure operator.

`rclo clo R` is the smallest relation containing R and closed under clo:
- `rclo_base`: R ⊆ rclo clo R
- `rclo_clo`: If R' ⊆ rclo clo R, then clo R' ⊆ rclo clo R -/
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base (h : R x y) : rclo clo R x y
  | clo (R' : Rel α) (hR' : R' ≤ rclo clo R) (h : clo R' x y) : rclo clo R x y

namespace rclo

variable {clo : Rel α → Rel α} {R S : Rel α}

/-- R is contained in rclo clo R -/
theorem base_le : R ≤ rclo clo R := fun _ _ h => base h

/-- clo R is contained in rclo clo R -/
theorem clo_base : clo R ≤ rclo clo R :=
  fun _ _ h => rclo.clo R base_le h

/-- rclo is monotone in R -/
theorem mono (hRS : R ≤ S) : rclo clo R ≤ rclo clo S := by
  intro x y h
  induction h with
  | base hr => exact base (hRS _ _ hr)
  | clo R' _ hclo ih => exact rclo.clo R' ih hclo

/-- rclo is monotone in clo (pointwise) -/
theorem mono_clo {clo₁ clo₂ : Rel α → Rel α} (h : ∀ R, clo₁ R ≤ clo₂ R) :
    rclo clo₁ R ≤ rclo clo₂ R := by
  intro x y hxy
  induction hxy with
  | base hr => exact base hr
  | clo R' _ hclo ih =>
    exact rclo.clo R' ih (h R' _ _ hclo)

/-- clo (rclo clo R) ⊆ rclo clo R -/
theorem clo_rclo : clo (rclo clo R) ≤ rclo clo R :=
  fun _ _ h => rclo.clo (rclo clo R) (fun _ _ hab => hab) h

/-- rclo is idempotent -/
theorem rclo_rclo : rclo clo (rclo clo R) ≤ rclo clo R := by
  intro x y h
  induction h with
  | base hr => exact hr
  | clo R' _ hclo ih => exact rclo.clo R' ih hclo

/-- Union injects into rclo -/
theorem union_le_rclo : rclo clo R ⊔ rclo clo S ≤ rclo clo (R ⊔ S) := by
  apply sup_le
  · exact mono le_sup_left
  · exact mono le_sup_right

/-- rclo is the smallest relation containing R and closed under clo -/
theorem rclo_smallest {R S : Rel α} (hRS : R ≤ S) (hclo : ∀ R', R' ≤ S → clo R' ≤ S) :
    rclo clo R ≤ S := by
  intro x y h
  induction h with
  | base hr => exact hRS _ _ hr
  | clo R' _ hcloR' ih => exact hclo R' ih _ _ hcloR'

/-- rclo with identity closure is identity -/
theorem rclo_id (R : Rel α) : rclo id R = R := by
  apply Rel.le_antisymm
  · apply rclo_smallest (Rel.le_refl R)
    intro R' hR'
    exact hR'
  · exact base_le

end rclo

end Paco
