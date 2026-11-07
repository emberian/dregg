/-
# Compositional policy compilation

Top-level alternatives compile independently, then use `Certified.union` and the
same checked minimization/relabeling as the derivative compiler. This avoids
constructing derivatives of a large raw union. Every intermediate and returned
table still carries `Certified.hdec`; the factor compiler consumes that same
certificate when compiling absence.

Other surface forms retain the derivative compiler. This is not a replacement
regex semantics or a claim that every regex operation has a compositional backend.
-/
import Dregg2.Policy.Union

namespace Dregg2.Policy

open Dregg2.Crypto.Deriv.PredRE

/-- Compile alternatives separately and compose their certified byte languages. -/
def certifySurface : (r : Re) → Except String (Certified (elabRe r) × List String)
  | .alt l r => do
      let (a, na) ← certifySurface l
      let (b, nb) ← certifySurface r
      let c ← certifyUnion a b
      let (c, nt) := c.trim
      pure (c.optimize (na ++ nb ++ nt))
  | r => certify (elabRe r)

/-- The absence compiler takes the compositional whole-word certificate directly. -/
def certifySurfaceAbsence (r : Re) (limit : Nat := 100000) :
    Except String (Certified (absenceOf (elabRe r)) × List String) := do
  let (c, notes) ← certifySurface r
  certifyAbsenceFrom r c notes limit

/-- A three-row reachable candidate for the six-row unequal-size union fixture. -/
def trimCandidate : Table :=
  ⟨3, fun s _ => if s = 0 then 1 else 2, fun s => s < 2, 0⟩

def trimEmbedding (s : Nat) : Nat := if s = 0 then 3 else if s = 1 then 4 else 0

set_option maxRecDepth 4096 in
/-- The candidate's actual embedding passes the same checker used by `trim`. -/
theorem trim_candidate_checked :
    simCheck trimCandidate UnionReference.either.t trimEmbedding = true := by decide

def trimReference : Certified (.alt any .ε) :=
  UnionReference.either.restrict trimCandidate trimEmbedding trim_candidate_checked

/-- Three unreachable rows can be omitted without changing the language. -/
theorem trim_reference_choices : trimReference.t.n = 3 ∧ UnionReference.either.t.n = 6 ∧
    trimReference.t.acc (trimReference.t.run trimReference.t.start []) = true ∧
    trimReference.t.acc (trimReference.t.run trimReference.t.start [255]) = true ∧
    trimReference.t.acc (trimReference.t.run trimReference.t.start [0, 255]) = false := by decide

/-- A label shift cannot be mistaken for a certified embedding. -/
theorem trim_wrong_embedding_refused :
    simCheck UnionReference.either.t UnionReference.either.t (fun s => s + 1) = false := by decide

#assert_all_clean [trim_candidate_checked, trim_reference_choices, trim_wrong_embedding_refused]

/-- info: 'Dregg2.Policy.Certified.restrict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certified.restrict

/-- info: 'Dregg2.Policy.trim_candidate_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trim_candidate_checked

/-- info: 'Dregg2.Policy.trim_reference_choices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trim_reference_choices

/-- info: 'Dregg2.Policy.trim_wrong_embedding_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trim_wrong_embedding_refused

-- The existing derivative compiler already carries Classical.choice; composition adds none.
/-- info: 'Dregg2.Policy.certify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certify

/-- info: 'Dregg2.Policy.certifySurface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifySurface

/-- info: 'Dregg2.Policy.certifySurfaceAbsence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifySurfaceAbsence

end Dregg2.Policy
