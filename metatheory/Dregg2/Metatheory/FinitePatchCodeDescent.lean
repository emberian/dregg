/-
# Dregg2.Metatheory.FinitePatchCodeDescent — a concrete finite patch-code adapter.

`ProofObjectDescent` supplies exact gluing, while `RobustProofObjectDescent` supplies
finite weighted query machinery.  This file joins those interfaces to an elementary
notion of a finite patch code: each patch carries a local constraint, and a global
codeword is a word whose restriction satisfies every local constraint.

The final section is a completely proved, deliberately small weighted agreement code.
Two singleton patches overlap a two-point hub.  The hub is constrained to be constant;
the tester queries the two hub overlaps with weights one and two.  For every locally
valid submitted family, its rejection weight is *exactly* its weighted block distance
from the constant codeword selected by the hub.  Thus zero rejection reconstructs a
unique codeword, and a one-error family shows the coefficient is sharp.

No expansion, local-testability, HDX, sheaf-code, or IOPP result is imported or claimed.
Those results would be larger concrete instances of the same adapter.
-/
import Dregg2.Metatheory.RobustProofObjectDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.DeriveFintype

namespace Dregg2.Metatheory.FinitePatchCodeDescent

open Set
open scoped BigOperators
open Dregg2.Metatheory.ProofObjectDescent
open Dregg2.Metatheory.RobustProofObjectDescent

universe u v w

/-! ## 1. Locally constrained finite patch codes. -/

/-- A finite cover together with a predicate selecting the valid section on each patch. -/
structure FinitePatchCode (X : Type u) (I : Type v) (Symbol : Type w)
    [DecidableEq X] where
  cover : FinCover X I
  localConstraint : (i : I) → LocalSection (fun _ : X => Symbol) (cover.patchSet i) → Prop

namespace FinitePatchCode

variable {X : Type u} {I : Type v} {Symbol : Type w} [DecidableEq X]

/-- Every submitted local view satisfies the constraint of its own patch. -/
def LocallyValid (C : FinitePatchCode X I Symbol)
    (s : SectionFamily C.cover (fun _ : X => Symbol)) : Prop :=
  ∀ i, C.localConstraint i (s i)

/-- A global word is a codeword when all of its patch restrictions are locally valid. -/
def IsCodeword (C : FinitePatchCode X I Symbol) (g : X → Symbol) : Prop :=
  ∀ i, C.localConstraint i (fun x _ => g x)

/-- Local validity is preserved by exact reconstruction: a matching, locally valid family
has one unique global amalgamation, and that amalgamation is a codeword. -/
theorem reconstruct_codeword (C : FinitePatchCode X I Symbol)
    (s : SectionFamily C.cover (fun _ : X => Symbol))
    (hlocal : C.LocallyValid s)
    (hmatch : Matching C.cover.patchSet (fun _ : X => Symbol) s) :
    ∃! g : X → Symbol,
      C.IsCodeword g ∧ RestrictsTo C.cover.patchSet (fun _ : X => Symbol) s g := by
  obtain ⟨g, hg, huniq⟩ :=
    (matching_iff_existsUnique_amalgamation C.cover.toDataCover s).mp hmatch
  refine ⟨g, ⟨?_, hg⟩, ?_⟩
  · intro i
    have hsection : (fun x (hx : x ∈ C.cover.patchSet i) => g x) = s i := by
      funext x hx
      exact hg i x hx
    rw [hsection]
    exact hlocal i
  · intro g' hg'
    exact huniq g' hg'.2

/-! ## 2. The complete finite overlap tester. -/

/-- Query every ordered patch pair with unit weight.  This is a finite weighted tester;
larger applications can replace it by a sparse weighted edge distribution only after
proving the corresponding agreement theorem. -/
noncomputable def completeOverlapTester (C : FinitePatchCode X I Symbol)
    [Fintype X] [Fintype I] [DecidableEq Symbol] :
    WeightedQueryModel (SectionFamily C.cover (fun _ : X => Symbol)) (I × I) :=
  wholeOverlapQueryModel C.cover (fun _ : X => Symbol)

theorem completeOverlap_rejectedWeight_eq_badCount
    (C : FinitePatchCode X I Symbol) [Fintype X] [Fintype I] [DecidableEq Symbol]
    (s : SectionFamily C.cover (fun _ : X => Symbol)) :
    (completeOverlapTester C).rejectedWeight s = overlapBadCount C.cover s := by
  classical
  simp [completeOverlapTester, wholeOverlapQueryModel,
    WeightedQueryModel.rejectedWeight, weightedCount, overlapBadCount, overlapBadEdges]
  convert (Finset.card_filter _ _).symm
  split_ifs <;> simp [*]

/-- Zero rejection by the complete finite tester reconstructs a unique global codeword. -/
theorem reconstruct_codeword_of_zero_completeOverlap
    (C : FinitePatchCode X I Symbol) [Fintype X] [Fintype I] [DecidableEq Symbol]
    (s : SectionFamily C.cover (fun _ : X => Symbol))
    (hlocal : C.LocallyValid s)
    (hzero : (completeOverlapTester C).rejectedWeight s = 0) :
    ∃! g : X → Symbol,
      C.IsCodeword g ∧ RestrictsTo C.cover.patchSet (fun _ : X => Symbol) s g := by
  apply C.reconstruct_codeword s hlocal
  apply (overlapBadCount_eq_zero_iff_matching C.cover s).mp
  rw [← completeOverlap_rejectedWeight_eq_badCount C s]
  exact hzero

end FinitePatchCode

/-! ## 3. A concrete weighted three-patch code. -/

namespace WeightedStar

/-- `left` and `right` are singleton patches; `hub` sees both points. -/
inductive PatchId where
  | left
  | right
  | hub
  deriving DecidableEq

instance : Fintype PatchId where
  elems := {.left, .right, .hub}
  complete := by intro x; cases x <;> simp

def patch : PatchId → Finset Bool
  | .left => {false}
  | .right => {true}
  | .hub => Finset.univ

def cover : FinCover Bool PatchId where
  patch := patch
  locate x := by
    cases x
    · exact ⟨.left, by simp [patch]⟩
    · exact ⟨.right, by simp [patch]⟩

/-- Only the hub has a nontrivial local code constraint: its two symbols must agree. -/
def localConstraint :
    (i : PatchId) → LocalSection (fun _ : Bool => Bool) (cover.patchSet i) → Prop
  | .left, _ => True
  | .right, _ => True
  | .hub, s =>
      s false (by simp [FinCover.patchSet, cover, patch]) =
        s true (by simp [FinCover.patchSet, cover, patch])

def code : FinitePatchCode Bool PatchId Bool where
  cover := cover
  localConstraint := localConstraint

def leftBit (s : SectionFamily cover (fun _ : Bool => Bool)) : Bool :=
  s .left false (by simp [FinCover.patchSet, cover, patch])

def rightBit (s : SectionFamily cover (fun _ : Bool => Bool)) : Bool :=
  s .right true (by simp [FinCover.patchSet, cover, patch])

def hubFalse (s : SectionFamily cover (fun _ : Bool => Bool)) : Bool :=
  s .hub false (by simp [FinCover.patchSet, cover, patch])

def hubTrue (s : SectionFamily cover (fun _ : Bool => Bool)) : Bool :=
  s .hub true (by simp [FinCover.patchSet, cover, patch])

/-- The canonical locally valid family with singleton symbols `a,b` and constant hub `c`. -/
def family (a b c : Bool) : SectionFamily cover (fun _ : Bool => Bool)
  | .left => fun _ _ => a
  | .right => fun _ _ => b
  | .hub => fun _ _ => c

theorem family_locallyValid (a b c : Bool) : code.LocallyValid (family a b c) := by
  intro i
  cases i <;> simp [code, localConstraint, family]

/-- Every locally valid family is exactly a three-bit family; the hub constraint removes
the otherwise independent fourth bit. -/
theorem eq_family_of_locallyValid
    (s : SectionFamily cover (fun _ : Bool => Bool)) (hlocal : code.LocallyValid s) :
    s = family (leftBit s) (rightBit s) (hubFalse s) := by
  have hhub : hubFalse s = hubTrue s := hlocal .hub
  funext i x hx
  cases i <;> cases x
  · rfl
  · simp [FinCover.patchSet, cover, patch] at hx
  · simp [FinCover.patchSet, cover, patch] at hx
  · rfl
  · rfl
  · exact hhub.symm

/-- The hub of a locally valid family selects a constant global codeword. -/
def hubWord (s : SectionFamily cover (fun _ : Bool => Bool)) : Bool → Bool :=
  fun _ => hubFalse s

theorem hubWord_isCodeword (s : SectionFamily cover (fun _ : Bool => Bool)) :
    code.IsCodeword (hubWord s) := by
  intro i
  cases i <;> simp [code, localConstraint, hubWord]

/-! ## 4. A sparse weighted overlap tester and its exact error law. -/

/-- Query `false` compares left with the hub and has weight one; query `true` compares
right with the hub and has weight two. -/
def queryEdge : Bool → PatchId × PatchId
  | false => (.left, .hub)
  | true => (.right, .hub)

noncomputable def tester : WeightedQueryModel (SectionFamily cover (fun _ : Bool => Bool)) Bool where
  weight q := if q then 2 else 1
  reject s q := wholeOverlapReject s (queryEdge q)
  rejectDecidable _ _ := Classical.propDecidable _

/-- Weighted distance of the two singleton patch blocks from an arbitrary global word.
The weights are exactly the corresponding overlap-query weights. -/
def singletonBlockDistance (s : SectionFamily cover (fun _ : Bool => Bool))
    (g : Bool → Bool) : Nat :=
  (if leftBit s = g false then 0 else 1) +
    (if rightBit s = g true then 0 else 2)

/-- Weighted block distance from the hub-selected word.  The hub itself has distance zero by
construction; singleton errors inherit their query weights. -/
def hubDistance (s : SectionFamily cover (fun _ : Bool => Bool)) : Nat :=
  singletonBlockDistance s (hubWord s)

theorem hubDistance_eq_singletonBlockDistance
    (s : SectionFamily cover (fun _ : Bool => Bool)) :
    hubDistance s = singletonBlockDistance s (hubWord s) := rfl

theorem family_rejection (a b c : Bool) :
    tester.rejectedWeight (family a b c) =
      (if a = c then 0 else 1) + (if b = c then 0 else 2) := by
  cases a <;> cases b <;> cases c <;>
    simp [WeightedQueryModel.rejectedWeight, weightedCount, tester, queryEdge,
      wholeOverlapReject, family, cover, patch, FinCover.patchSet]

theorem family_distance (a b c : Bool) :
    hubDistance (family a b c) =
      (if a = c then 0 else 1) + (if b = c then 0 else 2) := by
  rfl

theorem family_matching_iff (a b c : Bool) :
    Matching cover.patchSet (fun _ : Bool => Bool) (family a b c) ↔
      a = c ∧ b = c := by
  constructor
  · intro h
    exact ⟨
      h .left .hub false
        (by simp [FinCover.patchSet, cover, patch])
        (by simp [FinCover.patchSet, cover, patch]),
      h .right .hub true
        (by simp [FinCover.patchSet, cover, patch])
        (by simp [FinCover.patchSet, cover, patch])⟩
  · rintro ⟨rfl, rfl⟩
    intro i j x hi hj
    cases i <;> cases j <;> rfl

theorem family_zero_rejection_iff_matching (a b c : Bool) :
    tester.rejectedWeight (family a b c) = 0 ↔
      Matching cover.patchSet (fun _ : Bool => Bool) (family a b c) := by
  rw [family_rejection, family_matching_iff]
  by_cases hac : a = c <;> by_cases hbc : b = c <;> simp [hac, hbc]

/-- **Concrete positive-error theorem.**  This is proved from the three-patch system,
not stored as an abstract soundness assumption: on every locally valid family, rejection
weight equals the weighted distance to an explicitly produced global codeword. -/
theorem rejection_eq_hubDistance
    (s : SectionFamily cover (fun _ : Bool => Bool)) (hlocal : code.LocallyValid s) :
    tester.rejectedWeight s = hubDistance s := by
  rw [eq_family_of_locallyValid s hlocal]
  exact (family_rejection _ _ _).trans (family_distance _ _ _).symm

/-- Constructive sampled-soundness statement for this explicit code: the hub produces a
global codeword whose weighted singleton-block error is exactly the tester's rejection
weight.  In particular, the usual lower and upper bounds both hold with coefficient one. -/
theorem exists_codeword_with_exact_error
    (s : SectionFamily cover (fun _ : Bool => Bool)) (hlocal : code.LocallyValid s) :
    ∃ g : Bool → Bool,
      code.IsCodeword g ∧ singletonBlockDistance s g = tester.rejectedWeight s := by
  refine ⟨hubWord s, hubWord_isCodeword s, ?_⟩
  exact (rejection_eq_hubDistance s hlocal).symm

/-- Zero rejection therefore yields exact, unique codeword reconstruction. -/
theorem zero_rejection_reconstructs
    (s : SectionFamily cover (fun _ : Bool => Bool)) (hlocal : code.LocallyValid s)
    (hzero : tester.rejectedWeight s = 0) :
    ∃! g : Bool → Bool,
      code.IsCodeword g ∧ RestrictsTo cover.patchSet (fun _ : Bool => Bool) s g := by
  apply code.reconstruct_codeword s hlocal
  have hs := eq_family_of_locallyValid s hlocal
  rw [hs] at hzero ⊢
  exact (family_zero_rejection_iff_matching _ _ _).mp hzero

/-! ## 5. Teeth and sharpness. -/

def oneError : SectionFamily cover (fun _ : Bool => Bool) := family false true true

theorem oneError_locallyValid : code.LocallyValid oneError := family_locallyValid _ _ _

theorem oneError_rejects_one : tester.rejectedWeight oneError = 1 := by
  simpa [oneError] using family_rejection false true true

theorem oneError_distance_one : hubDistance oneError = 1 := by
  simpa [oneError] using family_distance false true true

theorem oneError_block_distance_one :
    singletonBlockDistance oneError (hubWord oneError) = 1 :=
  oneError_distance_one

theorem oneError_not_matching :
    ¬ Matching cover.patchSet (fun _ : Bool => Bool) oneError := by
  intro h
  have hbad := h .left .hub false
    (by simp [FinCover.patchSet, cover, patch])
    (by simp [FinCover.patchSet, cover, patch])
  change false = true at hbad
  contradiction

theorem oneError_no_amalgamation :
    ¬ ∃ g : Bool → Bool,
      RestrictsTo cover.patchSet (fun _ : Bool => Bool) oneError g :=
  incompatible_no_amalgamation oneError oneError_not_matching

/-- The factor-one lower bound is sharp: multiplying distance by two already fails. -/
theorem no_factor_two_bound_on_oneError :
    ¬ 2 * hubDistance oneError ≤ tester.rejectedWeight oneError := by
  rw [oneError_distance_one, oneError_rejects_one]
  decide

end WeightedStar

#assert_all_clean [
  FinitePatchCode.reconstruct_codeword,
  FinitePatchCode.completeOverlap_rejectedWeight_eq_badCount,
  FinitePatchCode.reconstruct_codeword_of_zero_completeOverlap,
  WeightedStar.family_locallyValid,
  WeightedStar.eq_family_of_locallyValid,
  WeightedStar.hubWord_isCodeword,
  WeightedStar.hubDistance_eq_singletonBlockDistance,
  WeightedStar.family_rejection,
  WeightedStar.family_distance,
  WeightedStar.family_matching_iff,
  WeightedStar.family_zero_rejection_iff_matching,
  WeightedStar.rejection_eq_hubDistance,
  WeightedStar.exists_codeword_with_exact_error,
  WeightedStar.zero_rejection_reconstructs,
  WeightedStar.oneError_locallyValid,
  WeightedStar.oneError_rejects_one,
  WeightedStar.oneError_distance_one,
  WeightedStar.oneError_block_distance_one,
  WeightedStar.oneError_not_matching,
  WeightedStar.oneError_no_amalgamation,
  WeightedStar.no_factor_two_bound_on_oneError]

end Dregg2.Metatheory.FinitePatchCodeDescent
