import Dregg2.Paco.UpTo.Compat
import Dregg2.Paco.UpTo.Cpn

/-!
# Guardedness Analysis for Companion Proofs

This module analyzes the guardedness tracking problem and provides auxiliary
lemmas for working with cpn and extendedGen.

## The Problem

The key theorem `cpn_extendedGen_F_compat` (in Respectful.lean) states (under
the `ExtCompatImpliesCompat F` assumption):
  `cpn (extendedGen F) (F R) ≤ F (cpn (extendedGen F) R)`

This says: starting from F-guarded input and closing under ext-compatible
closures, we stay F-guarded.

The Coq paco library proves this using constructive case analysis that tracks
which branch of the disjunction `R ⊔ F R` elements came from. In Lean's
classical logic, this information is lost during case analysis.

## Key Lemmas

We CAN prove weaker but useful properties:
1. `F (cpn ext R) ≤ cpn ext R` (F-application is absorbed)
2. `cpn ext (F R) ≤ cpn ext R` (F-guarded input is in cpn ext R)
3. `cpn F = cpn ext` requires the full F-compatibility proof

## Analysis

The fundamental issue is that ext-compatible closures don't necessarily
preserve F-guardedness. Given `clo (F R)` where clo is ext-compatible:
- clo (F R) ≤ clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)

The case split loses the information that the input was purely F-guarded.
-/

namespace Paco

variable {α : Type*}

/-!
## Key Lemmas for extendedGen and cpn
-/

/-- F (cpn ext R) is absorbed into cpn ext R.
This is cpn.step specialized to extendedGen. -/
theorem F_cpn_ext_le_cpn_ext (F : MonoRel α) (R : Rel α) :
    F (cpn (extendedGen F) R) ≤ cpn (extendedGen F) R := by
  have h : extendedGen F (cpn (extendedGen F) R) ≤ cpn (extendedGen F) R := cpn.step
  -- extendedGen F X = X ⊔ F X, so F X ≤ extendedGen F X
  have h2 : F (cpn (extendedGen F) R) ≤ extendedGen F (cpn (extendedGen F) R) := le_sup_right
  exact Rel.le_trans h2 h

/-- F R is contained in F (cpn ext R) -/
theorem F_R_le_F_cpn_ext (F : MonoRel α) (R : Rel α) :
    F R ≤ F (cpn (extendedGen F) R) :=
  F.mono' cpn.base

/-- F R is contained in cpn ext R (via cpn_step) -/
theorem F_R_le_cpn_ext (F : MonoRel α) (R : Rel α) :
    F R ≤ cpn (extendedGen F) R :=
  Rel.le_trans (F_R_le_F_cpn_ext F R) (F_cpn_ext_le_cpn_ext F R)

/-- cpn ext (F R) ≤ cpn ext R.
This is weaker than F-compatibility but still useful. -/
theorem cpn_ext_F_le_cpn_ext (F : MonoRel α) (R : Rel α) :
    cpn (extendedGen F) (F R) ≤ cpn (extendedGen F) R :=
  -- F R ≤ cpn ext R, so by cpn.mono: cpn ext (F R) ≤ cpn ext (cpn ext R)
  -- By cpn_cpn: cpn ext (cpn ext R) ≤ cpn ext R
  Rel.le_trans
    (cpn.cpn_cloMono (F R) (cpn (extendedGen F) R) (F_R_le_cpn_ext F R))
    cpn.cpn_cpn

/-!
## The TMP Property from Coq

The Coq proof uses a key property TMP:
  `gf (cpn gf r) ≤ cpn gf r ∧ gf (cpn gf r)`

This says F (cpn F R) is in BOTH cpn F R AND F (cpn F R).
The first part is cpn.step, the second is trivial.

This property is crucial because it means elements starting from F-guarded
input are simultaneously in both parts of the disjunction, so EITHER branch
of case analysis can be shown to yield F-guarded output.
-/

/-- TMP property: F (cpn F R) is in both cpn F R and F (cpn F R) -/
theorem tmp_property (F : MonoRel α) (R : Rel α) :
    F (cpn F R) ≤ cpn F R ⊓ F (cpn F R) := by
  intro x y hf
  constructor
  · exact cpn.step x y hf  -- F (cpn F R) ≤ cpn F R
  · exact hf                -- F (cpn F R) ≤ F (cpn F R) trivially

/-- TMP property for extendedGen -/
theorem tmp_property_ext (F : MonoRel α) (R : Rel α) :
    F (cpn (extendedGen F) R) ≤ cpn (extendedGen F) R ⊓ F (cpn (extendedGen F) R) := by
  intro x y hf
  constructor
  · exact F_cpn_ext_le_cpn_ext F R x y hf
  · exact hf

/-!
## Analysis of the Proof Gap

For `cpn_extendedGen_F_compat`, we need (under `ExtCompatImpliesCompat F`):
  `cpn ext (F R) ≤ F (cpn ext R)`

What we CAN prove:
  `cpn ext (F R) ≤ cpn ext R` (shown above as cpn_ext_F_le_cpn_ext)

The gap is showing elements stay in the F-part rather than just cpn ext R.

The Coq proof achieves this by:
1. Using constructive case analysis that tracks which branch of ⊔ we're in
2. Showing BOTH branches of `cpn ext R ⊔ F (cpn ext R)` yield F (cpn ext R)
   when the input was F-guarded

In Lean's classical logic, we lose the branch information during case analysis,
making this proof structure unavailable.

### Possible Approaches

1. **Add assumptions on F**: Require F to have properties like distributivity
   over ⊔, or being a QPF, that would make the proof go through.

2. **Work with cpn F instead of cpn ext**: The theorem `cpn.compat` already
   gives us F-compatibility of cpn F. If we can show cpn F = cpn ext directly,
   we'd have F-compatibility of cpn ext.

3. **Accept weaker theorems**: For many applications, `cpn ext (F R) ≤ cpn ext R`
   may be sufficient, as cpn ext R is still a valid coinductive hypothesis.

4. **Use a constructive fragment**: Work in a subset of Lean that preserves
   constructive case analysis information.
-/

end Paco
