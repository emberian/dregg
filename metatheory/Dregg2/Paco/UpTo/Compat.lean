import Dregg2.Paco.UpTo.Rclo

/-!
# Compatibility

A closure operator `clo` is compatible with `F` if it commutes appropriately
with the generating function.
-/

namespace Paco

variable {α : Type*}

/-- Strong compatibility: clo (F R) ≤ F (clo R).

This allows using clo during coinduction without breaking the argument. -/
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (F R) ≤ F (clo R)

/-- A closure is monotone if R ≤ S implies clo R ≤ clo S -/
def CloMono (clo : Rel α → Rel α) : Prop := Monotone2 clo

/-!
## Basic Compatible Closures
-/

/-- Identity is compatible with any F -/
theorem compatible_id (F : MonoRel α) : Compatible F id := fun _ => Rel.le_refl _

/-- Identity is monotone -/
theorem cloMono_id : CloMono (id : Rel α → Rel α) := fun _ _ h => h

/-- Composition of compatible closures is compatible -/
theorem compatible_comp (F : MonoRel α) {clo₁ clo₂ : Rel α → Rel α}
    (h₁_mono : CloMono clo₁) (h₁ : Compatible F clo₁) (h₂ : Compatible F clo₂) :
    Compatible F (clo₁ ∘ clo₂) := by
  intro R
  exact Rel.le_trans (h₁_mono _ _ (h₂ R)) (h₁ (clo₂ R))

/-- rclo of a compatible monotone closure is compatible -/
theorem rclo_compatible (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    Compatible F (rclo clo) := by
  intro R x y h
  induction h with
  | base hFR => exact F.mono' rclo.base_le _ _ hFR
  | clo R' _ hcloR' ih =>
    have h1 : clo R' ≤ clo (F (rclo clo R)) := h_mono R' _ ih
    have h2 : clo (F (rclo clo R)) ≤ F (clo (rclo clo R)) := h_compat (rclo clo R)
    have h3 : clo (rclo clo R) ≤ rclo clo R := rclo.clo_rclo
    have h4 : F (clo (rclo clo R)) ≤ F (rclo clo R) := F.mono' h3
    exact h4 _ _ (h2 _ _ (h1 _ _ hcloR'))

/-- rclo of a monotone closure is monotone -/
theorem rclo_mono (clo : Rel α → Rel α) : CloMono (rclo clo) :=
  fun _ _ h => rclo.mono h

/-!
## Extended Generator and Compatible'
-/

/-- The extended generator (id ⊔ F) as a MonoRel.

This is the key construction for defining compatibility with respect to
the "relaxed" generator that includes the identity. In Coq paco, this is `gf'`. -/
def extendedGen (F : MonoRel α) : MonoRel α where
  F := fun R => R ⊔ F R
  mono := fun _ _ hRS => sup_le_sup hRS (F.mono' hRS)

theorem extendedGen_def (F : MonoRel α) (R : Rel α) : extendedGen F R = R ⊔ F R := rfl

/-- Weak compatibility (Compatible'): clo (R ⊔ F R) ≤ clo R ⊔ F (clo R).

This is equivalent to being compatible with the extended generator (id ⊔ F).
It's weaker than F-compatibility because it allows elements to stay in the
identity part rather than requiring them to be in the F part. -/
def Compatible' (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)

/-- Compatible' F clo is equivalent to Compatible (extendedGen F) clo -/
theorem compatible'_iff_compat_extendedGen (F : MonoRel α) (clo : Rel α → Rel α) :
    Compatible' F clo ↔ Compatible (extendedGen F) clo := by
  constructor
  · intro h R
    -- h : clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)
    -- Goal: clo (extendedGen F R) ≤ extendedGen F (clo R)
    -- i.e., clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)
    exact h R
  · intro h R
    exact h R


/-!
## Tight Generator and Compatible∧
-/

/-- The tight generator (id ⊓ F) as a MonoRel. -/
def tightGen (F : MonoRel α) : MonoRel α where
  F := fun R => R ⊓ F R
  mono := fun _ _ hRS => inf_le_inf hRS (F.mono' hRS)

theorem tightGen_def (F : MonoRel α) (R : Rel α) : tightGen F R = R ⊓ F R := rfl

/-- Strong compatibility: clo (R ⊓ F R) ≤ clo R ⊓ F (clo R).

This is compatibility with the tight generator (id ⊓ F). -/
def CompatibleAnd (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R, clo (R ⊓ F R) ≤ clo R ⊓ F (clo R)

/-- CompatibleAnd F clo is equivalent to Compatible (tightGen F) clo -/
theorem compatibleAnd_iff_compat_tightGen (F : MonoRel α) (clo : Rel α → Rel α) :
    CompatibleAnd F clo ↔ Compatible (tightGen F) clo := by
  constructor <;> intro h R <;> simpa [CompatibleAnd, tightGen_def] using h R

/-!
## Optional Restriction for Companion Equality

The lemma `cpn (extendedGen F) ≤ cpn F` is false in general (counterexamples exist
when extendedGen is identity and closures can introduce elements from ⊤).
To recover the Coq PACO-style equality in Lean, we expose the following
assumption: every closure compatible with the extended generator is already
compatible with F.

This is a property of F (and the class of closures you allow) and can be
discharged in specialized settings.
-/

/-- Assumption: extendedGen-compatible closures are F-compatible. -/
class ExtCompatImpliesCompat (F : MonoRel α) : Prop where
  (h : ∀ clo, CloMono clo → Compatible (extendedGen F) clo → Compatible F clo)

/-!
## Sufficient Conditions

The following conditions provide concrete instances of ExtCompatImpliesCompat.
-/

/-- Inflationary generators: R ≤ F R for all R. -/
class Inflationary (F : MonoRel α) : Prop where
  (h : ∀ R, R ≤ F R)

/-- If F is inflationary, then any extendedGen-compatible closure is F-compatible. -/
instance extCompat_of_inflationary (F : MonoRel α) [Inflationary F] :
    ExtCompatImpliesCompat F :=
  ⟨by
    intro clo h_mono h_ext R x y hclo
    -- clo (F R) ≤ clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)
    have h1 : clo (F R) ≤ clo (R ⊔ F R) :=
      h_mono (F R) (R ⊔ F R) le_sup_right
    have h2 : clo (R ⊔ F R) ≤ clo R ⊔ F (clo R) := h_ext R
    -- clo R ⊔ F (clo R) ≤ F (clo R) since clo R ≤ F (clo R)
    have h3 : clo R ⊔ F (clo R) ≤ F (clo R) := by
      apply sup_le
      · exact Inflationary.h (F := F) (clo R)
      · exact Rel.le_refl _
    exact h3 x y (h2 x y (h1 x y hclo))⟩

/-- extendedGen is inflationary. -/
instance inflationary_extendedGen (F : MonoRel α) : Inflationary (extendedGen F) :=
  ⟨by
    intro R
    exact le_sup_left⟩


/-- extendedGen F satisfies ExtCompatImpliesCompat via inflationary. --/
instance extCompat_of_extendedGen (F : MonoRel α) : ExtCompatImpliesCompat (extendedGen F) := by
  infer_instance

end Paco
