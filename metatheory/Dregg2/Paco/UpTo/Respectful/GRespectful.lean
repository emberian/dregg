import Dregg2.Paco.UpTo.Respectful.Core

/-!
# Generalized Respectfulness
-/

namespace Paco

variable {α : Type*}

/-- Generalized respectfulness for `clo` with respect to `F`. --/
structure GRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition -/
  respect : ∀ l r, l ≤ r → l ≤ F r →
    clo l ≤ rclo (companion F) (F (rclo (cloUnion clo (gupaco_clo F (companion F))) r))

/-- Generalized respectfulness implies the closure is contained in the companion.

Currently routed through the Compatible' → companion chain, which requires:
- `Compatible' F clo`
- `ExtCompatImpliesCompat F`

This keeps the lemma usable in settings where Compatible' is available. -/
theorem grespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] : ∀ R, clo R ≤ companion F R :=
  compatible'_le_companion F h.mon h_compat'

/-- Generalized respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem grespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : GRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := grespect_companion F h h_compat' R
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

end Paco
