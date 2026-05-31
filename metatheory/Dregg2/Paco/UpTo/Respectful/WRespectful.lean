import Dregg2.Paco.UpTo.Respectful.Core
import Dregg2.Paco.UpTo.Respectful.Tagged

/-!
# Weak Respectfulness
-/

namespace Paco

variable {α : Type*}

/-!
### Extended Weak Respectfulness

The standard WRespectful requires BOTH `l ≤ r` AND `l ≤ F r`. But in Coq's compatible'
context where gf' = id ⊔ gf is used, the condition `l ≤ gf' r = l ≤ r ⊔ F r` can be
satisfied by EITHER `l ≤ r` OR `l ≤ F r`.

This motivates WRespectfulExt, which has:
- Hypothesis: l ≤ r ⊔ F r (satisfied by either branch)
- Conclusion: clo l ≤ rclo clo r ⊔ F (rclo clo r) (lands in extended generator)

This is the condition that actually matches Coq's compatible' proof structure.
-/

/-- Extended weak respectfulness: the condition used in Coq's compatible' proofs.

This version uses the "extended generator" formulation:
- Input: l ≤ extendedGen F r = l ≤ r ⊔ F r
- Output: clo l ≤ extendedGen F (rclo clo r) = rclo clo r ⊔ F (rclo clo r)

The key property is that the input condition is satisfied by EITHER l ≤ r OR l ≤ F r,
not requiring both simultaneously. This allows the tagged rclo proof to work. -/
structure WRespectfulExt (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The extended respect condition -/
  respect : ∀ l r, l ≤ r ⊔ F r → clo l ≤ rclo clo r ⊔ F (rclo clo r)

/-- Any Compatible' monotone closure satisfies WRespectfulExt.

This is because:
- clo l ≤ clo (r ⊔ F r) by monotonicity (since l ≤ r ⊔ F r)
- clo (r ⊔ F r) ≤ clo r ⊔ F (clo r) by Compatible'
- clo r ≤ rclo clo r by rclo.clo_base, and F respects ≤ -/
theorem cloMono_wrespectfulExt (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat' : Compatible' F clo) : WRespectfulExt F clo where
  mon := h_mono
  respect := by
    intro l r h_le_ext
    -- h_le_ext : l ≤ r ⊔ F r
    -- Goal: clo l ≤ rclo clo r ⊔ F (rclo clo r)
    have h1 : clo l ≤ clo (r ⊔ F r) := h_mono _ _ h_le_ext
    have h2 : clo (r ⊔ F r) ≤ clo r ⊔ F (clo r) := h_compat' r
    have h3 : clo r ⊔ F (clo r) ≤ rclo clo r ⊔ F (rclo clo r) := by
      apply sup_le
      · exact Rel.le_trans rclo.clo_base le_sup_left
      · exact Rel.le_trans (F.mono' rclo.clo_base) le_sup_right
    exact Rel.le_trans h1 (Rel.le_trans h2 h3)

/-- Weak respectfulness: a weaker condition than compatibility.

A closure `clo` is weakly respectful with respect to `F` if it is monotone and
for any `l ≤ r` with `l ≤ F r`, we have `clo l ≤ F (rclo clo r)`. -/
structure WRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ F (rclo clo r) when l ≤ r and l ≤ F r -/
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ F (rclo clo r)

/-- WRespectful + Compatible' implies WRespectfulExt. -/
theorem wrespect_to_ext (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectful F clo) (h_compat' : Compatible' F clo) : WRespectfulExt F clo :=
  cloMono_wrespectfulExt F h.mon h_compat'

/-- rcloTagged elements (both guarded and unguarded) land in rclo clo R ⊔ F (rclo clo R)
    when clo satisfies WRespectfulExt. -/
theorem rcloTagged_le_extendedGen (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α)
    (h : WRespectfulExt F clo) (b : Bool) :
    rcloTagged clo F R b ≤ rclo clo R ⊔ F (rclo clo R) := by
  intro x y hrt
  induction hrt with
  | base_unguarded hr =>
    left; exact rclo.base hr
  | base_guarded hf =>
    right; exact F.mono' rclo.base_le _ _ hf
  | clo_step b' R' hR' hclo ih =>
    -- hR' : ∀ a c, R' a c → rcloTagged clo F R b' a c
    -- hclo : clo R' x✝ y✝ (pattern match variables)
    -- ih : ∀ a c, R' a c → (rclo clo R ⊔ F (rclo clo R)) a c

    -- By ih: R' ≤ rclo clo R ⊔ F (rclo clo R)
    have hR'_le : R' ≤ rclo clo R ⊔ F (rclo clo R) := ih

    -- By WRespectfulExt with l = R' and r = rclo clo R:
    -- Need: R' ≤ rclo clo R ⊔ F (rclo clo R) ✓ (this is hR'_le)
    -- Conclusion: clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R))
    have h_resp := h.respect R' (rclo clo R) hR'_le
    -- h_resp : clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R))

    -- By rclo_rclo: rclo clo (rclo clo R) ≤ rclo clo R
    have h_rclo_rclo := rclo.rclo_rclo (clo := clo) (R := R)

    -- So: clo R' ≤ rclo clo R ⊔ F (rclo clo R)
    have h_final : clo R' ≤ rclo clo R ⊔ F (rclo clo R) := by
      intro a c hac
      cases h_resp a c hac with
      | inl h_in_rclo =>
        left; exact h_rclo_rclo a c h_in_rclo
      | inr h_in_F =>
        right; exact F.mono' h_rclo_rclo a c h_in_F

    exact h_final _ _ hclo

/-- Extended weak respectfulness implies rclo clo is Compatible'.

This theorem shows that if clo is weakly respectful, then rclo clo satisfies
the compatibility condition: rclo clo (R ⊔ F R) ≤ rclo clo R ⊔ F (rclo clo R).

**Proof strategy** (following Coq's wrespect0_compatible'):

The key insight is that Compatible' F clo = Compatible (extendedGen F) clo, where
extendedGen F R = R ⊔ F R. When working with this "extended generator", the
WRespectful GF condition `l ≤ (extendedGen F) r = l ≤ r ⊔ F r` is IMPLIED by `l ≤ r`.

This means we can apply WRespectful whenever we have `l ≤ r`, since:
- LE condition: `l ≤ r` (given)
- GF condition: `l ≤ r ⊔ F r` (follows from l ≤ r by le_sup_left)

The proof proceeds by induction on rclo:
- Base case: Elements from R go to rclo clo R (left), elements from F R go to F (rclo clo R)
- Clo case: Apply WRespectful with l = R' and r = rclo clo (R ⊔ F R)
  - LE: R' ≤ rclo clo (R ⊔ F R) is given by the rclo constructor
  - GF: R' ≤ rclo clo (R ⊔ F R) ⊔ F (rclo clo (R ⊔ F R)) follows from LE
  - WRespectful gives: clo R' ≤ F (rclo clo (rclo clo (R ⊔ F R)))
  - By rclo_rclo: rclo clo (rclo clo (R ⊔ F R)) ≤ rclo clo (R ⊔ F R)
  - By F.mono: F (rclo clo (rclo clo (R ⊔ F R))) ≤ F (rclo clo (R ⊔ F R))
  - Now use the IH: rclo clo (R ⊔ F R) ≤ rclo clo R ⊔ F (rclo clo R)
  - By F.mono: F (rclo clo (R ⊔ F R)) ≤ F (rclo clo R ⊔ F (rclo clo R))
  - Finally show F (rclo clo R ⊔ F (rclo clo R)) ≤ rclo clo R ⊔ F (rclo clo R)
-/
theorem wrespect_compatible' (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) : Compatible' F (rclo clo) := by
  intro R
  -- Let S be the target relation.
  let S : Rel α := rclo clo R ⊔ F (rclo clo R)
  -- Show rclo clo (R ⊔ F R) ≤ S by rclo_smallest.
  apply rclo.rclo_smallest
  · -- Base: R ⊔ F R ≤ S
    apply sup_le
    · exact Rel.le_trans rclo.base_le le_sup_left
    · exact Rel.le_trans (F.mono' rclo.base_le) le_sup_right
  · -- Clo-closed: if R' ≤ S then clo R' ≤ S
    intro R' hR'
    -- Apply WRespectfulExt with r = rclo clo R, noting S = r ⊔ F r.
    have h_resp :
        clo R' ≤ rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R)) :=
      h.respect R' (rclo clo R) hR'
    have h_shrink : rclo clo (rclo clo R) ≤ rclo clo R := rclo.rclo_rclo
    have h_sup : rclo clo (rclo clo R) ⊔ F (rclo clo (rclo clo R)) ≤ S := by
      apply sup_le
      · exact Rel.le_trans h_shrink le_sup_left
      · exact Rel.le_trans (F.mono' h_shrink) le_sup_right
    exact Rel.le_trans h_resp h_sup

/-- Extended weak respectfulness implies the closure is contained in the companion.

This is the key lemma connecting wrespectful to the companion.

**Proof strategy**: Show rclo clo R ≤ companion F R using rclo_smallest.
This requires showing the companion is clo-closed, which involves:
- Using WRespectfulExt on guarded inputs (F(companion F R))
- Handling unguarded inputs (R) via companion_extensive

**Note**: The proof has a circular dependency that requires either:
1. A weaker Compatible' definition (as in Coq paco)
2. A coinductive argument showing companion is clo-closed
3. A well-founded induction on rclo depth

Currently uses wrespect_compatible' in the extended form. -/
theorem wrespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) [ExtCompatImpliesCompat F] :
    ∀ R, clo R ≤ companion F R := by
  intro R
  -- Strategy: clo R ≤ rclo clo R ≤ companion F R
  -- The second step uses compatible'_le_companion via wrespect_compatible'
  have h_compat' : Compatible' F (rclo clo) := wrespect_compatible' F h
  have h1 : clo R ≤ rclo clo R := rclo.clo_base
  have h2 : rclo clo R ≤ companion F R :=
    compatible'_le_companion F (rclo_mono clo) h_compat' R
  exact Rel.le_trans h1 h2

/-- Weak respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem wrespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : WRespectfulExt F clo) [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := wrespect_companion F h R
  -- companion F R ≤ gupaco_clo F (companion F) R by companion_gupaco_eq
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

/-- Compatibility implies weak respectfulness -/
theorem compat_wrespect (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    WRespectful F clo where
  mon := h_mono
  respect := by
    intro l r _hle hlF x y hclo
    -- From clo l x y and l ≤ F r
    -- We have clo (F r) ≤ F (clo r) by compatibility
    -- And clo r ≤ rclo clo r by rclo.clo_base
    have h1 : clo l ≤ clo (F r) := h_mono l (F r) hlF
    have h2 : clo (F r) ≤ F (clo r) := h_compat r
    have h3 : clo r ≤ rclo clo r := rclo.clo_base
    have h4 : F (clo r) ≤ F (rclo clo r) := F.mono' h3
    exact h4 x y (h2 x y (h1 x y hclo))

end Paco
