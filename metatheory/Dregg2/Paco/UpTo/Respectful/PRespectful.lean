import Dregg2.Paco.UpTo.Respectful.Core
import Dregg2.Paco.UpTo.Respectful.Tagged

/-!
# Paco Respectfulness
-/

namespace Paco

variable {α : Type*}

/-- Paco respectfulness for `clo` with respect to `F`. --/
structure PRespectful (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ paco F (r ⊔ clo r) when l ≤ r and l ≤ F r -/
  respect : ∀ l r, l ≤ r → l ≤ F r → clo l ≤ paco F (r ⊔ clo r)


/-- Stronger respectfulness: uses `l ≤ r ⊔ F r` directly. --/
structure PRespectfulStrong (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  /-- The closure is monotone -/
  mon : CloMono clo
  /-- The respect condition: clo l ≤ paco F (r ⊔ clo r) when l ≤ r ⊔ F r -/
  respect : ∀ l r, l ≤ r ⊔ F r → clo l ≤ paco F (r ⊔ clo r)

/-- The closure operator for PRespectful: R ↦ upaco F (R ⊔ clo R).

This is the key closure used in proving PRespectful implies ≤ companion.
By showing this closure is compatible', we can use compatible'_le_companion. -/
def prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) : Rel α → Rel α :=
  fun R => upaco F (R ⊔ clo R)

/-- prespectClosure is monotone when clo is monotone -/
theorem prespectClosure_mono (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) : CloMono (prespectClosure F clo) := by
  intro R S hRS x y hpre
  simp only [prespectClosure] at hpre ⊢
  have h1 : R ⊔ clo R ≤ S ⊔ clo S := sup_le_sup hRS (h_mono R S hRS)
  exact upaco_mon F h1 x y hpre

/-- PRespectful lifts to the tagged domain. --/
theorem tagClosure_prespectful (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) : PRespectful (tagMonoRel F) (tagClosure clo) := by
  refine ⟨tagClosure_mono (α := α) h.mon, ?_⟩
  intro l r hle hleF x y hclo
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      simp [tagClosure] at hclo ⊢
      have hleL : projLeft l ≤ projLeft r :=
        fun a b hab => hle _ _ hab
      have hleFL : projLeft l ≤ F (projLeft r) := by
        intro a b hab
        have h' : (tagMonoRel F) r (Sum.inl a) (Sum.inl b) := hleF _ _ hab
        exact h'
      have hresp : clo (projLeft l) ≤ paco F (projLeft r ⊔ clo (projLeft r)) :=
        h.respect _ _ hleL hleFL
      have h' : projLeft (paco (tagMonoRel F) (r ⊔ tagClosure clo r)) a b := by
        simpa [projLeft_paco, projLeft_sup, projLeft_tagClosure] using hresp _ _ hclo
      exact h'
    | inr b =>
      cases hclo
  | inr a =>
    cases y with
    | inl b =>
      cases hclo
    | inr b =>
      simp [tagClosure] at hclo ⊢
      have hleR : projRight l ≤ projRight r :=
        fun a b hab => hle _ _ hab
      have hleFR : projRight l ≤ F (projRight r) := by
        intro a b hab
        have h' : (tagMonoRel F) r (Sum.inr a) (Sum.inr b) := hleF _ _ hab
        exact h'
      have hresp : clo (projRight l) ≤ paco F (projRight r ⊔ clo (projRight r)) :=
        h.respect _ _ hleR hleFR
      have h' : projRight (paco (tagMonoRel F) (r ⊔ tagClosure clo r)) a b := by
        simpa [projRight_paco, projRight_sup, projRight_tagClosure] using hresp _ _ hclo
      exact h'

/-- Project prespectClosure through the left tag. --/
theorem projLeft_prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel (Tag α)) :
    projLeft (prespectClosure (tagMonoRel F) (tagClosure clo) R) =
      prespectClosure F clo (projLeft R) := by
  simp [prespectClosure, projLeft_upaco, projLeft_sup, projLeft_tagClosure]

/-- Project prespectClosure through the right tag. --/
theorem projRight_prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel (Tag α)) :
    projRight (prespectClosure (tagMonoRel F) (tagClosure clo) R) =
      prespectClosure F clo (projRight R) := by
  simp [prespectClosure, projRight_upaco, projRight_sup, projRight_tagClosure]

/-- Forget tags for prespectClosure on a tagged relation. --/
theorem forgetTag_prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel (Tag α)) :
    forgetTag (prespectClosure (tagMonoRel F) (tagClosure clo) R) =
      prespectClosure F clo (projLeft R) ⊔ prespectClosure F clo (projRight R) := by
  simp [forgetTag, projLeft_prespectClosure, projRight_prespectClosure]


/-- prespectClosure on a tagged union splits by tag. --/
theorem prespectClosure_taggedUnion (F : MonoRel α) (clo : Rel α → Rel α)
    (R S : Rel α) :
    prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S) =
      taggedUnion (prespectClosure F clo R) (prespectClosure F clo S) := by
  ext x y
  constructor
  · intro h
    cases x <;> cases y
    · -- inl/inl
      rename_i a b
      have hproj : projLeft (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) a b := by
        simpa using h
      have h' : prespectClosure F clo R a b := by
        simpa [projLeft_prespectClosure, projLeft_taggedUnion] using hproj
      simpa [taggedUnion, tagLeft, tagRight] using h'
    · -- inl/inr: impossible by tag-closedness
      have hR : TagClosed (taggedUnion R S ⊔ tagClosure clo (taggedUnion R S)) := by
        exact TagClosed.sup (taggedUnion_closed R S) (tagClosure_closed (taggedUnion R S))
      have hclosed : TagClosed (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) := by
        simpa [prespectClosure] using (upaco_closed (F := F)
          (R := taggedUnion R S ⊔ tagClosure clo (taggedUnion R S)) hR)
      exact (hclosed.1 _ _ h).elim
    · -- inr/inl: impossible by tag-closedness
      have hR : TagClosed (taggedUnion R S ⊔ tagClosure clo (taggedUnion R S)) := by
        exact TagClosed.sup (taggedUnion_closed R S) (tagClosure_closed (taggedUnion R S))
      have hclosed : TagClosed (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) := by
        simpa [prespectClosure] using (upaco_closed (F := F)
          (R := taggedUnion R S ⊔ tagClosure clo (taggedUnion R S)) hR)
      exact (hclosed.2 _ _ h).elim
    · -- inr/inr
      rename_i a b
      have hproj : projRight (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) a b := by
        simpa using h
      have h' : prespectClosure F clo S a b := by
        simpa [projRight_prespectClosure, projRight_taggedUnion] using hproj
      simpa [taggedUnion, tagLeft, tagRight] using h'
  · intro h
    cases x <;> cases y
    · -- inl/inl
      rename_i a b
      have h' : prespectClosure F clo R a b := by
        simpa [taggedUnion, tagLeft, tagRight] using h
      have hproj : projLeft (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) a b := by
        simpa [projLeft_prespectClosure, projLeft_taggedUnion] using h'
      simpa using hproj
    · -- inl/inr
      cases h with
      | inl hL => cases hL
      | inr hR => cases hR
    · -- inr/inl
      cases h with
      | inl hL => cases hL
      | inr hR => cases hR
    · -- inr/inr
      rename_i a b
      have h' : prespectClosure F clo S a b := by
        simpa [taggedUnion, tagLeft, tagRight] using h
      have hproj : projRight (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)) a b := by
        simpa [projRight_prespectClosure, projRight_taggedUnion] using h'
      simpa using hproj

/-- prespectClosure on a tag-closed relation splits by tag. --/


theorem prespectClosure_tagClosed (F : MonoRel α) (clo : Rel α → Rel α)
    {R : Rel (Tag α)} (hR : TagClosed R) :
    prespectClosure (tagMonoRel F) (tagClosure clo) R =
      taggedUnion (prespectClosure F clo (projLeft R)) (prespectClosure F clo (projRight R)) := by
  have hR' : R = taggedUnion (projLeft R) (projRight R) := tagClosed_eq_taggedUnion hR
  rw [hR']
  simpa using (prespectClosure_taggedUnion (F := F) (clo := clo)
    (R := projLeft R) (S := projRight R))

/-- clo R is contained in prespectClosure -/
theorem clo_le_prespectClosure (F : MonoRel α) (clo : Rel α → Rel α) (R : Rel α) :
    clo R ≤ prespectClosure F clo R := by
  intro x y hclo
  simp only [prespectClosure, upaco]
  right  -- go to clo R side of the union
  exact Or.inr hclo





/-- Tag roundtrip: embedding into tags and projecting back preserves prespectClosure. --/
class TagRoundtrip (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  (h : ∀ R S,
    prespectClosure F clo (R ⊔ S) ≤
      forgetTag (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R S)))

/-- Right-branch guardedness for prespectClosure. --/
class PrespectRightGuarded (F : MonoRel α) (clo : Rel α → Rel α) : Prop where
  (h : ∀ R, prespectClosure F clo (F R) ≤ F (prespectClosure F clo R))

/-- Tag-roundtrip + right-guardedness yields Compatible' for prespectClosure. --/
theorem prespect_compatible'_tagged (F : MonoRel α) {clo : Rel α → Rel α}
    (_h : PRespectful F clo) [TagRoundtrip F clo] [PrespectRightGuarded F clo] :
    Compatible' F (prespectClosure F clo) := by
  have _ := _h.mon
  intro R
  have hround := TagRoundtrip.h (F := F) (clo := clo) R (F R)
  have hsplit :
      forgetTag (prespectClosure (tagMonoRel F) (tagClosure clo) (taggedUnion R (F R))) =
        prespectClosure F clo R ⊔ prespectClosure F clo (F R) := by
    simpa [projLeft_taggedUnion, projRight_taggedUnion] using
      (forgetTag_prespectClosure (F := F) (clo := clo) (R := taggedUnion R (F R)))
  have hmain : prespectClosure F clo (R ⊔ F R) ≤
      prespectClosure F clo R ⊔ prespectClosure F clo (F R) := by
    simpa [hsplit] using hround
  have hguard : prespectClosure F clo (F R) ≤ F (prespectClosure F clo R) :=
    PrespectRightGuarded.h (F := F) (clo := clo) R
  have hsup : prespectClosure F clo R ⊔ prespectClosure F clo (F R) ≤
      prespectClosure F clo R ⊔ F (prespectClosure F clo R) := by
    apply sup_le
    · exact le_sup_left
    · exact Rel.le_trans hguard le_sup_right
  exact Rel.le_trans hmain hsup

/-- PRespectfulStrong implies prespectClosure is Compatible'. --/
theorem prespect_compatible'_strong (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectfulStrong F clo) :
    Compatible' F (prespectClosure F clo) := by
  intro R
  -- It suffices to show prespectClosure F clo (R ⊔ F R) ≤ prespectClosure F clo R.
  set K : Rel α := R ⊔ clo R
  set S : Rel α := R ⊔ F R
  have hR_le_K : R ≤ K := le_sup_left
  have hK_le_U : K ≤ prespectClosure F clo R := by
    intro a b hK
    -- prespectClosure F clo R = upaco F (R ⊔ clo R)
    simp [prespectClosure, upaco]
    exact Or.inr hK
  have hFR_le_paco : F R ≤ paco F K := by
    have hR_le_upaco : R ≤ upaco F K := by
      intro a b hR
      simp [upaco]; right; left; exact hR
    have hFR_le_Fupaco : F R ≤ F (upaco F K) := F.mono' hR_le_upaco
    exact Rel.le_trans hFR_le_Fupaco (paco_fold (F := F) K)
  have hcloS_le_paco : clo S ≤ paco F K := by
    -- Use strong respectfulness with r = R.
    have hS_le : S ≤ R ⊔ F R := by
      intro a b hS; exact hS
    have h' := h.respect (l := S) (r := R) hS_le
    simpa [K, S] using h'
  have hparam : S ⊔ clo S ≤ K ⊔ paco F K := by
    apply sup_le
    · -- S ≤ K ⊔ paco F K
      have hS_le : S ≤ K ⊔ paco F K := by
        apply sup_le
        · -- R ≤ K ⊔ paco F K
          exact Rel.le_trans hR_le_K le_sup_left
        · -- F R ≤ K ⊔ paco F K
          exact Rel.le_trans hFR_le_paco le_sup_right
      simpa [S] using hS_le
    · -- clo S ≤ K ⊔ paco F K
      exact Rel.le_trans hcloS_le_paco le_sup_right
  have hpaco_le : paco F (S ⊔ clo S) ≤ paco F K := by
    have hp : paco F (S ⊔ clo S) ≤ paco F (K ⊔ paco F K) :=
      paco_mon F hparam
    have h_eq : paco F (K ⊔ paco F K) = paco F K := by
      simpa [K] using (paco_idem (F := F) K)
    simpa [h_eq] using hp
  have hparam_le : S ⊔ clo S ≤ prespectClosure F clo R := by
    -- prespectClosure F clo R = upaco F K = paco F K ⊔ K; hparam gives K ⊔ paco F K
    show S ⊔ clo S ≤ upaco F K
    intro a b hab
    rcases hparam a b hab with hK | hpaco
    · exact Or.inr hK
    · exact Or.inl hpaco
  have h_upaco_le : upaco F (S ⊔ clo S) ≤ prespectClosure F clo R := by
    -- upaco = paco ⊔ parameter
    intro a b hU
    simp [upaco] at hU
    cases hU with
    | inl hp =>
        have hp' : paco F (S ⊔ clo S) a b := hp
        have hp'' : paco F K a b := hpaco_le _ _ hp'
        -- paco F K ≤ upaco F K
        have : paco F K ≤ prespectClosure F clo R := by
          intro x y hx
          simp [prespectClosure, upaco]; left; exact hx
        exact this _ _ hp''
    | inr hparam' =>
        exact hparam_le _ _ hparam'
  have hmain : prespectClosure F clo S ≤ prespectClosure F clo R := by
    intro a b hpre
    -- unfold prespectClosure
    simpa [prespectClosure, S] using (h_upaco_le a b hpre)
  -- Compatible' goal
  exact Rel.le_trans hmain le_sup_left



/-- Right-branch guardedness from strong respectfulness, under inflationary F. --/
theorem prespect_right_guarded_strong (F : MonoRel α) [Inflationary F] {clo : Rel α → Rel α}
    (h : PRespectfulStrong F clo) (R : Rel α) :
    prespectClosure F clo (F R) ≤ F (prespectClosure F clo R) := by
  have hcompat : Compatible' F (prespectClosure F clo) := prespect_compatible'_strong F h
  have hmono : CloMono (prespectClosure F clo) := prespectClosure_mono F h.mon
  have h1 : prespectClosure F clo (F R) ≤ prespectClosure F clo (R ⊔ F R) :=
    hmono _ _ le_sup_right
  have h2 : prespectClosure F clo (R ⊔ F R) ≤ prespectClosure F clo R ⊔ F (prespectClosure F clo R) :=
    hcompat R
  have h3 : prespectClosure F clo R ⊔ F (prespectClosure F clo R) ≤ F (prespectClosure F clo R) := by
    apply sup_le
    · exact Inflationary.h (F := F) (prespectClosure F clo R)
    · exact Rel.le_refl _
  exact Rel.le_trans h1 (Rel.le_trans h2 h3)


/-- Inflationary F lets us recover Compatible' from strong respectfulness. --/
theorem prespect_compatible'_inflationary (F : MonoRel α) [Inflationary F]
    {clo : Rel α → Rel α} (h : PRespectfulStrong F clo) :
    Compatible' F (prespectClosure F clo) := by
  intro R
  have hRF : R ⊔ F R = F R := by
    apply sup_eq_right.mpr
    exact Inflationary.h (F := F) R
  have hguard : prespectClosure F clo (F R) ≤ F (prespectClosure F clo R) :=
    prespect_right_guarded_strong (F := F) h R
  have hguard' : prespectClosure F clo (F R) ≤ prespectClosure F clo R ⊔ F (prespectClosure F clo R) :=
    Rel.le_trans hguard le_sup_right
  simpa [hRF] using hguard'


/-- If F is inflationary, strong respectfulness yields right-branch guardedness. --/
theorem prespectRightGuarded_of_inflationary (F : MonoRel α) [Inflationary F]
    {clo : Rel α → Rel α} (h : PRespectfulStrong F clo) :
    PrespectRightGuarded F clo :=
  ⟨by
    intro R
    exact prespect_right_guarded_strong (F := F) h R⟩

/-- PRespectful implies prespectClosure is CompatibleAnd (tight generator). --/
theorem prespect_compatibleAnd (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) :
    CompatibleAnd F (prespectClosure F clo) := by
  intro R x y hC
  have hmono : CloMono (prespectClosure F clo) := prespectClosure_mono F h.mon
  have hleft : prespectClosure F clo (R ⊓ F R) ≤ prespectClosure F clo R :=
    hmono _ _ inf_le_left
  refine ⟨hleft _ _ hC, ?_⟩
  have hparam : (R ⊓ F R) ⊔ clo (R ⊓ F R) ≤ R ⊔ clo R := by
    apply sup_le_sup inf_le_left
    exact h.mon _ _ inf_le_left
  have hup : upaco F ((R ⊓ F R) ⊔ clo (R ⊓ F R)) ≤ prespectClosure F clo R := by
    simpa [prespectClosure] using (upaco_mon (F := F) hparam)
  have hpaco_to : paco F ((R ⊓ F R) ⊔ clo (R ⊓ F R)) ≤ F (prespectClosure F clo R) := by
    have h1 : paco F ((R ⊓ F R) ⊔ clo (R ⊓ F R)) ≤
        F (upaco F ((R ⊓ F R) ⊔ clo (R ⊓ F R))) :=
      paco_unfold (F := F) ((R ⊓ F R) ⊔ clo (R ⊓ F R))
    exact Rel.le_trans h1 (F.mono' hup)
  have hR_in : R ≤ prespectClosure F clo R := by
    intro a b hR
    simp [prespectClosure, upaco]
    right; left; exact hR
  have hC' := hC
  simp [prespectClosure, upaco] at hC'
  cases hC' with
  | inl hpaco =>
      exact hpaco_to _ _ hpaco
  | inr hbase =>
      cases hbase with
      | inl hS =>
          have hFR : F R x y := hS.2
          exact (F.mono' hR_in) _ _ hFR
      | inr hcloS =>
          have hrespect : clo (R ⊓ F R) ≤ paco F (R ⊔ clo R) :=
            h.respect _ _ inf_le_left inf_le_right
          have hpacoR : paco F (R ⊔ clo R) x y := hrespect _ _ hcloS
          have h1 : paco F (R ⊔ clo R) ≤ F (upaco F (R ⊔ clo R)) :=
            paco_unfold (F := F) (R ⊔ clo R)
          have h2 : F (upaco F (R ⊔ clo R)) x y := h1 _ _ hpacoR
          simpa [prespectClosure] using h2

/-- Paco respectfulness implies the closure is contained in the companion.

Currently routed through the Compatible' → companion chain, which requires:
- `Compatible' F clo`
- `ExtCompatImpliesCompat F`

This keeps the lemma usable in settings where Compatible' is available. -/
theorem prespect_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] : ∀ R, clo R ≤ companion F R :=
  compatible'_le_companion F h.mon h_compat'

/-- Paco respectfulness uclo lemma: clo R ≤ gupaco_clo F (companion F) R -/
theorem prespect_uclo (F : MonoRel α) {clo : Rel α → Rel α}
    (h : PRespectful F clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] (R : Rel α) :
    clo R ≤ gupaco_clo F (companion F) R := by
  intro x y hclo
  have h1 : clo R ≤ companion F R := prespect_companion F h h_compat' R
  have h2 : companion F R = gupaco_clo F (companion F) R := (companion_gupaco_eq F R).symm
  rw [← h2]
  exact h1 x y hclo

end Paco
