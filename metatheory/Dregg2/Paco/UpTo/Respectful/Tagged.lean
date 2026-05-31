import Dregg2.Paco.UpTo.Compat

/-!
# Tagged Relations for Respectfulness
-/

namespace Paco

variable {α : Type*}

/-!
## Weak Respectfulness

### Proof-Relevant Tagged Relations

The Coq proof of `wrespect_compatible'` works because Coq's proof terms constructively
track which branch of a disjunction each element came from. In Lean's classical setting,
case analysis on `Or` loses this information.

To recover this, we define **tagged relations** that explicitly track provenance:
- Elements are tagged as either "unguarded" (from the base relation) or "guarded" (from F)
- This tracking is preserved through closure operations
- When we need to apply WRespectful, we can use the tag to satisfy the conditions
-/

/-- A tagged element of a relation, tracking whether it came from the "unguarded" (left)
    or "guarded" (right/F) branch. This is the proof-relevant version of `R ⊔ F R`. -/
inductive Tagged (R : Rel α) (S : Rel α) : Rel α
  | unguarded : R x y → Tagged R S x y
  | guarded : S x y → Tagged R S x y

/-- Tagged relation embeds into the union -/
theorem Tagged.toSup {R S : Rel α} : Tagged R S ≤ R ⊔ S := by
  intro x y h
  cases h with
  | unguarded hr => left; exact hr
  | guarded hs => right; exact hs

/-- Union embeds into tagged relation (non-constructively) -/
theorem Tagged.fromSup {R S : Rel α} : R ⊔ S ≤ Tagged R S := by
  intro x y h
  cases h with
  | inl hr => exact Tagged.unguarded hr
  | inr hs => exact Tagged.guarded hs

/-- Tagged is monotone in both arguments -/
theorem Tagged.mono {R R' S S' : Rel α} (hR : R ≤ R') (hS : S ≤ S') :
    Tagged R S ≤ Tagged R' S' := by
  intro x y h
  cases h with
  | unguarded hr => exact Tagged.unguarded (hR x y hr)
  | guarded hs => exact Tagged.guarded (hS x y hs)

/-- rclo with explicit guardedness tracking.

This is the key construction for the proof. Each element tracks whether it was derived
through an F application (guarded) or purely through R and clo (unguarded).

The key invariant is:
- Unguarded elements satisfy `rclo clo R`
- Guarded elements satisfy `F (rclo clo R)` -/
inductive rcloTagged (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α) : Bool → Rel α
  /-- Base unguarded: element from R -/
  | base_unguarded : R x y → rcloTagged clo F R false x y
  /-- Base guarded: element from F R -/
  | base_guarded : F R x y → rcloTagged clo F R true x y
  /-- Closure preserves guardedness tag -/
  | clo_step (b : Bool) (R' : Rel α) :
      (∀ a c, R' a c → rcloTagged clo F R b a c) →
      clo R' x y →
      rcloTagged clo F R b x y

/-- Unguarded elements of rcloTagged are in rclo clo R -/
theorem rcloTagged_unguarded_le_rclo (clo : Rel α → Rel α) (F : MonoRel α) (R : Rel α) :
    rcloTagged clo F R false ≤ rclo clo R := by
  intro x y h
  -- Generalize false to b with hypothesis hb : b = false
  generalize hb : false = b at h
  induction h with
  | base_unguarded hr => exact rclo.base hr
  | base_guarded hf => exact absurd hb Bool.false_ne_true
  | clo_step b' R' hR' hclo ih =>
    subst hb  -- b' = false
    -- ih : ∀ a c, R' a c → rclo clo R a c (the IH is over R' elements)
    have hR'_le : R' ≤ rclo clo R := fun a c hac => ih a c hac rfl
    exact rclo.clo R' hR'_le hclo


/-!
## Generalized Tagged rclo

This variant separates the unguarded and guarded base relations, which is useful
when tracking guardedness through closures in PRespectful proofs.
-/

/-- rclo with explicit guardedness tracking over two base relations. -/
inductive rcloTagged2 (clo : Rel α → Rel α) (R S : Rel α) : Bool → Rel α
  | base_unguarded : R x y → rcloTagged2 clo R S false x y
  | base_guarded : S x y → rcloTagged2 clo R S true x y
  | clo_step (b : Bool) (R' : Rel α) :
      (∀ a c, R' a c → rcloTagged2 clo R S b a c) →
      clo R' x y →
      rcloTagged2 clo R S b x y

/-- Unguarded elements of rcloTagged2 are in rclo clo R. -/
theorem rcloTagged2_unguarded_le_rclo (clo : Rel α → Rel α) (R S : Rel α) :
    rcloTagged2 clo R S false ≤ rclo clo R := by
  intro x y h
  generalize hb : false = b at h
  induction h with
  | base_unguarded hr => exact rclo.base hr
  | base_guarded hs => exact absurd hb Bool.false_ne_true
  | clo_step b' R' hR' hclo ih =>
    subst hb
    have hR'_le : R' ≤ rclo clo R := fun a c hac => ih a c hac rfl
    exact rclo.clo R' hR'_le hclo

/-- Guarded elements of rcloTagged2 are in rclo clo S. -/
theorem rcloTagged2_guarded_le_rclo (clo : Rel α → Rel α) (R S : Rel α) :
    rcloTagged2 clo R S true ≤ rclo clo S := by
  intro x y h
  generalize hb : true = b at h
  induction h with
  | base_unguarded hr => cases hb
  | base_guarded hs => exact rclo.base hs
  | clo_step b' R' hR' hclo ih =>
    subst hb
    have hR'_le : R' ≤ rclo clo S := fun a c hac => ih a c hac rfl
    exact rclo.clo R' hR'_le hclo

/-- rcloTagged2 embeds into rclo clo (R ⊔ S) by forgetting tags. -/
theorem rcloTagged2_le_rclo_sup (clo : Rel α → Rel α) (R S : Rel α) (b : Bool) :
    rcloTagged2 clo R S b ≤ rclo clo (R ⊔ S) := by
  intro x y h
  induction h with
  | base_unguarded hr => exact rclo.base (Or.inl hr)
  | base_guarded hs => exact rclo.base (Or.inr hs)
  | clo_step b' R' hR' hclo ih =>
    have hR'_le : R' ≤ rclo clo (R ⊔ S) := ih
    exact rclo.clo R' hR'_le hclo



/-!
## Tagging via Sum Types

This section provides a proof-relevant tagging mechanism by moving tags into the
underlying type. This makes tag preservation explicit and avoids losing branch
information during case splits.
-/

/-- Tagged sum used to track guarded and unguarded branches. --/
def Tag (α : Type*) := Sum α α

/-- Tag a relation on the left side of `Sum`. -/
def tagLeft (R : Rel α) : Rel (Tag α) :=
  fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => R a b
    | _, _ => False

/-- Tag a relation on the right side of `Sum`. -/
def tagRight (R : Rel α) : Rel (Tag α) :=
  fun x y =>
    match x, y with
    | Sum.inr a, Sum.inr b => R a b
    | _, _ => False

/-- Project the left-tagged part of a relation. -/
def projLeft (R : Rel (Tag α)) : Rel α :=
  fun x y => R (Sum.inl x) (Sum.inl y)

/-- Project the right-tagged part of a relation. -/
def projRight (R : Rel (Tag α)) : Rel α :=
  fun x y => R (Sum.inr x) (Sum.inr y)

/-- Forget tags by taking the union of projections. -/
def forgetTag (R : Rel (Tag α)) : Rel α :=
  projLeft R ⊔ projRight R

/-- Monotonicity of left projection. --/
theorem projLeft_mono {R S : Rel (Tag α)} (h : R ≤ S) : projLeft R ≤ projLeft S :=
  fun _ _ hxy => h _ _ hxy

/-- Monotonicity of right projection. --/
theorem projRight_mono {R S : Rel (Tag α)} (h : R ≤ S) : projRight R ≤ projRight S :=
  fun _ _ hxy => h _ _ hxy

/-- Forgetting tags is monotone. --/
theorem forgetTag_mono {R S : Rel (Tag α)} (h : R ≤ S) : forgetTag R ≤ forgetTag S := by
  intro x y hxy
  cases hxy with
  | inl hL => exact Or.inl (projLeft_mono h _ _ hL)
  | inr hR => exact Or.inr (projRight_mono h _ _ hR)

@[simp] theorem projLeft_tagLeft (R : Rel α) : projLeft (tagLeft R) = R := by
  rfl

@[simp] theorem projRight_tagRight (R : Rel α) : projRight (tagRight R) = R := by
  rfl

@[simp] theorem projLeft_tagRight (R : Rel α) : projLeft (tagRight R) = ⊥ := by
  rfl

@[simp] theorem projRight_tagLeft (R : Rel α) : projRight (tagLeft R) = ⊥ := by
  rfl

/-- Union of tagged relations, keeping tags separate. -/
def taggedUnion (R S : Rel α) : Rel (Tag α) :=
  tagLeft R ⊔ tagRight S

@[simp] theorem projLeft_taggedUnion (R S : Rel α) : projLeft (taggedUnion R S) = R := by
  ext x y; simp [taggedUnion, tagLeft, tagRight, projLeft]

@[simp] theorem projRight_taggedUnion (R S : Rel α) : projRight (taggedUnion R S) = S := by
  ext x y; simp [taggedUnion, tagLeft, tagRight, projRight]

/-- Forgetting tags from a tagged union recovers the union. -/
theorem forgetTag_taggedUnion (R S : Rel α) : forgetTag (taggedUnion R S) = R ⊔ S := by
  ext x y; simp [forgetTag, taggedUnion, projLeft, projRight, tagLeft, tagRight]

/-- Lift a monotone transformer to a tagged domain, preserving tags. -/
def tagMonoRel (F : MonoRel α) : MonoRel (Tag α) where
  F := fun R x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => F (projLeft R) a b
    | Sum.inr a, Sum.inr b => F (projRight R) a b
    | _, _ => False
  mono := by
    intro R S hRS x y hxy
    cases x <;> cases y <;> simp at hxy ⊢
    · exact F.mono' (fun a b hab => hRS _ _ hab) _ _ hxy
    · exact F.mono' (fun a b hab => hRS _ _ hab) _ _ hxy

/-- Lift a closure to a tagged domain, preserving tags. -/
def tagClosure (clo : Rel α → Rel α) : Rel (Tag α) → Rel (Tag α) :=
  fun R x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => clo (projLeft R) a b
    | Sum.inr a, Sum.inr b => clo (projRight R) a b
    | _, _ => False

/-- Tag-preserving relations: no cross-tag pairs. --/
def TagClosed (R : Rel (Tag α)) : Prop :=
  (∀ a b, R (Sum.inl a) (Sum.inr b) → False) ∧
  (∀ a b, R (Sum.inr a) (Sum.inl b) → False)

/-- Left-tagged relations are tag-closed. --/
theorem tagLeft_closed (R : Rel α) : TagClosed (tagLeft R) := by
  constructor <;> intro a b h <;> cases h

/-- Right-tagged relations are tag-closed. --/
theorem tagRight_closed (R : Rel α) : TagClosed (tagRight R) := by
  constructor <;> intro a b h <;> cases h

/-- Tagged unions are tag-closed. --/
theorem taggedUnion_closed (R S : Rel α) : TagClosed (taggedUnion R S) := by
  constructor <;> intro a b h
  · cases h with
    | inl hL => cases hL
    | inr hR => cases hR
  · cases h with
    | inl hL => cases hL
    | inr hR => cases hR


/-- Roundtrip: tag-closed relations are exactly the tagged union of projections. --/
theorem tagClosed_eq_taggedUnion {R : Rel (Tag α)} (h : TagClosed R) :
    R = taggedUnion (projLeft R) (projRight R) := by
  ext x y
  cases x <;> cases y
  · -- inl/inl
    simp [taggedUnion, tagLeft, tagRight, projLeft]
  · -- inl/inr
    constructor
    · intro hxy
      exact (h.1 _ _ hxy).elim
    · intro hxy
      simp [taggedUnion, tagLeft, tagRight] at hxy
  · -- inr/inl
    constructor
    · intro hxy
      exact (h.2 _ _ hxy).elim
    · intro hxy
      simp [taggedUnion, tagLeft, tagRight] at hxy
  · -- inr/inr
    simp [taggedUnion, tagLeft, tagRight, projRight]

/-- Tag-closed is preserved by union. --/
theorem TagClosed.sup {R S : Rel (Tag α)} (hR : TagClosed R) (hS : TagClosed S) :
    TagClosed (R ⊔ S) := by
  constructor <;> intro a b h
  · cases h with
    | inl hL => exact hR.1 _ _ hL
    | inr hR' => exact hS.1 _ _ hR'
  · cases h with
    | inl hL => exact hR.2 _ _ hL
    | inr hR' => exact hS.2 _ _ hR'

/-- Tag-closed is preserved by tagClosure. --/
theorem tagClosure_closed {clo : Rel α → Rel α} (R : Rel (Tag α)) :
    TagClosed (tagClosure clo R) := by
  constructor <;> intro a b h <;> cases h

/-- Tag-closed holds for paco over tagMonoRel. --/
theorem paco_closed (F : MonoRel α) (R : Rel (Tag α)) :
    TagClosed (paco (tagMonoRel F) R) := by
  constructor <;> intro a b h
  · rcases h with ⟨R', hR', hxy⟩
    have h' := hR' (Sum.inl a) (Sum.inr b) hxy
    simpa using h'
  · rcases h with ⟨R', hR', hxy⟩
    have h' := hR' (Sum.inr a) (Sum.inl b) hxy
    simpa using h'

/-- Tag-closed holds for upaco when the parameter is tag-closed. --/
theorem upaco_closed (F : MonoRel α) {R : Rel (Tag α)} (hR : TagClosed R) :
    TagClosed (upaco (tagMonoRel F) R) := by
  apply TagClosed.sup (paco_closed F R) hR

/-- If clo is monotone, so is its tagged lift. -/
theorem tagClosure_mono {clo : Rel α → Rel α} (h_mono : CloMono clo) :
    CloMono (tagClosure (α := α) clo) := by
  intro R S hRS x y hxy
  cases x <;> cases y <;> try cases hxy
  · exact h_mono _ _ (fun a b hab => hRS _ _ hab) _ _ hxy
  · exact h_mono _ _ (fun a b hab => hRS _ _ hab) _ _ hxy

@[simp] theorem projLeft_sup (R S : Rel (Tag α)) :
    projLeft (R ⊔ S) = projLeft R ⊔ projLeft S := by
  rfl

@[simp] theorem projRight_sup (R S : Rel (Tag α)) :
    projRight (R ⊔ S) = projRight R ⊔ projRight S := by
  rfl

@[simp] theorem projLeft_tagMonoRel (F : MonoRel α) (R : Rel (Tag α)) :
    projLeft ((tagMonoRel F) R) = F (projLeft R) := by
  rfl

@[simp] theorem projRight_tagMonoRel (F : MonoRel α) (R : Rel (Tag α)) :
    projRight ((tagMonoRel F) R) = F (projRight R) := by
  rfl

@[simp] theorem projLeft_tagClosure (clo : Rel α → Rel α) (R : Rel (Tag α)) :
    projLeft (tagClosure clo R) = clo (projLeft R) := by
  rfl

@[simp] theorem projRight_tagClosure (clo : Rel α → Rel α) (R : Rel (Tag α)) :
    projRight (tagClosure clo R) = clo (projRight R) := by
  rfl

/-- Project paco on the left tag. --/
@[simp] theorem projLeft_paco (F : MonoRel α) (R : Rel (Tag α)) :
    projLeft (paco (tagMonoRel F) R) = paco F (projLeft R) := by
  apply Rel.le_antisymm
  · intro x y h
    rcases h with ⟨R', hR', hxy⟩
    refine ⟨projLeft R', ?_, hxy⟩
    intro a b hab
    have h' := hR' (Sum.inl a) (Sum.inl b) hab
    simpa using h'
  · intro x y h
    rcases h with ⟨R', hR', hxy⟩
    refine ⟨tagLeft R', ?_, ?_⟩
    · intro a b hab
      cases a <;> cases b <;> simp [tagMonoRel, tagLeft] at hab ⊢
      have h' := hR' _ _ hab
      have hproj : projLeft (tagLeft R' ⊔ R) = R' ⊔ projLeft R := by
        ext x y; simp [projLeft, tagLeft]
      simpa [tagMonoRel, hproj] using h'
    · simpa using hxy

/-- Project paco on the right tag. --/
@[simp] theorem projRight_paco (F : MonoRel α) (R : Rel (Tag α)) :
    projRight (paco (tagMonoRel F) R) = paco F (projRight R) := by
  apply Rel.le_antisymm
  · intro x y h
    rcases h with ⟨R', hR', hxy⟩
    refine ⟨projRight R', ?_, hxy⟩
    intro a b hab
    have h' := hR' (Sum.inr a) (Sum.inr b) hab
    simpa using h'
  · intro x y h
    rcases h with ⟨R', hR', hxy⟩
    refine ⟨tagRight R', ?_, ?_⟩
    · intro a b hab
      cases a <;> cases b <;> simp [tagMonoRel, tagRight] at hab ⊢
      have h' := hR' _ _ hab
      have hproj : projRight (tagRight R' ⊔ R) = R' ⊔ projRight R := by
        ext x y; simp [projRight, tagRight]
      simpa [tagMonoRel, hproj] using h'
    · simpa using hxy

/-- Project upaco on the left tag. --/
theorem projLeft_upaco (F : MonoRel α) (R : Rel (Tag α)) :
    projLeft (upaco (tagMonoRel F) R) = upaco F (projLeft R) := by
  simp [upaco]

/-- Project upaco on the right tag. --/
theorem projRight_upaco (F : MonoRel α) (R : Rel (Tag α)) :
    projRight (upaco (tagMonoRel F) R) = upaco F (projRight R) := by
  simp [upaco]

/-- Forget tags for paco on a tagged relation. --/
theorem forgetTag_paco (F : MonoRel α) (R : Rel (Tag α)) :
    forgetTag (paco (tagMonoRel F) R) =
      paco F (projLeft R) ⊔ paco F (projRight R) := by
  simp [forgetTag]

/-- Forget tags for upaco on a tagged relation. --/
theorem forgetTag_upaco (F : MonoRel α) (R : Rel (Tag α)) :
    forgetTag (upaco (tagMonoRel F) R) =
      upaco F (projLeft R) ⊔ upaco F (projRight R) := by
  simp [forgetTag, upaco]

end Paco
