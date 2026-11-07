/-
# Proof-producing optimizer certificates for direct logic

`DirectLogicOptimization` proves the algebraic rewrites.  This module packages
them as an executable, fail-closed translation validator for a bounded Boolean
formula fragment.  Raw claims contain redundant before/after terms and are
therefore tamperable data; the checker accepts a claim only when both endpoints
are exactly reconstructed from its rule payload.  Composite certificates also
check every transitive boundary.

The deterministic optimizer recursively optimizes children, proposes one
root rewrite, and runs the same checker before emitting that step.  A separate
fanout entry point consumes an explicit DAG-sharing opportunity.  Theorems
connect checker acceptance to source semantics, the exact field graph
compiler's `Accepts` relation, and symbolic cost nonincrease.
-/

import Dregg2.Metatheory.DirectLogicOptimization

namespace Dregg2.Metatheory.DirectLogicOptimizerCertificate

open Dregg2.Logic.BoolGraph
open Dregg2.Metatheory.ArithmetizationCost
open Dregg2.Metatheory.ArithmetizationCost.BackendCost
open Dregg2.Metatheory.ArithmetizationCost.BooleanGraph

set_option autoImplicit false

/-! ## 1. A bounded, serializable source fragment -/

/-- Atoms are `Fin n`, so a serialized formula cannot name an atom outside its
declared public bound. -/
inductive Formula (n : Nat) where
  | atom : Fin n → Formula n
  | top : Formula n
  | bot : Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
  deriving DecidableEq, Repr

namespace Formula

def Holds {n : Nat} (truth : Fin n → Prop) : Formula n → Prop
  | .atom a => truth a
  | .top => True
  | .bot => False
  | .not p => ¬ Holds truth p
  | .and p q => Holds truth p ∧ Holds truth q
  | .or p q => Holds truth p ∨ Holds truth q

/-- Erasure into the already verified exact field-graph source. -/
def toGraph {n : Nat} : Formula n → Dregg2.Logic.BoolGraph.Formula (Fin n)
  | .atom a => .atom a
  | .top => .top
  | .bot => .bot
  | .not p => .not (toGraph p)
  | .and p q => .and (toGraph p) (toGraph q)
  | .or p q => .or (toGraph p) (toGraph q)

theorem graphEval_iff_holds {F : Type*} [Field F] {n : Nat}
    (residual : Fin n → F) (p : Formula n) :
    Eval residual p.toGraph ↔ Holds (fun a => residual a = 0) p := by
  induction p <;> simp [toGraph, Holds, Eval, *]

/-- Singleton-aware disjunction used by explicit fanout certificates. -/
def anyOpt {n : Nat} : List (Formula n) → Formula n
  | [] => .bot
  | [p] => p
  | p :: q :: ps => .or p (anyOpt (q :: ps))
termination_by ps => ps.length

theorem holds_anyOpt {n : Nat} (truth : Fin n → Prop) (ps : List (Formula n)) :
    Holds truth (anyOpt ps) ↔ ∃ p, p ∈ ps ∧ Holds truth p := by
  induction ps with
  | nil => simp [anyOpt, Holds]
  | cons p ps ih =>
      cases ps with
      | nil => simp [anyOpt]
      | cons q qs => simp [anyOpt, Holds, ih]

def duplicatedAndMany {n : Nat} (p : Formula n) (qs : List (Formula n)) : Formula n :=
  anyOpt (qs.map fun q => .and p q)

def sharedAndMany {n : Nat} (p : Formula n) (qs : List (Formula n)) : Formula n :=
  match qs with
  | [] => .bot
  | _ :: _ => .and p (anyOpt qs)

theorem sharedAndMany_holds_iff {n : Nat} (truth : Fin n → Prop)
    (p : Formula n) (qs : List (Formula n)) :
    Holds truth (sharedAndMany p qs) ↔ Holds truth (duplicatedAndMany p qs) := by
  cases qs with
  | nil => simp [sharedAndMany, duplicatedAndMany, anyOpt, Holds]
  | cons q qs =>
      rw [duplicatedAndMany, holds_anyOpt]
      simp only [List.mem_map]
      rw [show sharedAndMany p (q :: qs) = .and p (anyOpt (q :: qs)) by rfl]
      rw [Holds, holds_anyOpt]
      constructor
      · rintro ⟨hp, r, hr, hqr⟩
        exact ⟨.and p r, ⟨r, hr, rfl⟩, hp, hqr⟩
      · rintro ⟨candidate, ⟨r, hr, rfl⟩, hp, hqr⟩
        exact ⟨hp, r, hr, hqr⟩

theorem toGraph_anyOpt {n : Nat} (ps : List (Formula n)) :
    (anyOpt ps).toGraph =
      Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.anyOpt
        (ps.map toGraph) := by
  induction ps with
  | nil =>
      simp [anyOpt, toGraph,
        Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.anyOpt]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [anyOpt,
            Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.anyOpt]
      | cons q qs =>
          simp only [anyOpt, toGraph,
            Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.anyOpt,
            List.map_cons]
          rw [ih]
          simp

theorem toGraph_duplicatedAndMany {n : Nat} (p : Formula n)
    (qs : List (Formula n)) :
    (duplicatedAndMany p qs).toGraph =
      Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.duplicatedAndMany
        p.toGraph (qs.map toGraph) := by
  rw [duplicatedAndMany,
    Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.duplicatedAndMany,
    toGraph_anyOpt]
  simp [List.map_map, Function.comp_def, toGraph]

theorem toGraph_sharedAndMany {n : Nat} (p : Formula n)
    (qs : List (Formula n)) :
    (sharedAndMany p qs).toGraph =
      Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAndMany
        p.toGraph (qs.map toGraph) := by
  cases qs with
  | nil => rfl
  | cons q qs =>
      simp only [sharedAndMany, toGraph,
        Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAndMany,
        List.map_cons]
      rw [toGraph_anyOpt]
      simp

/-- Symbolic relation cost of the erased exact Boolean graph. -/
def graphCost {n : Nat} (p : Formula n) : BackendCost :=
  Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost p.toGraph

theorem graphCost_degree_le_two {n : Nat} (p : Formula n) :
    p.graphCost.maxDegree ≤ 2 :=
  Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.degree_le_two p.toGraph

theorem graphCost_tableCells_eq_zero {n : Nat} (p : Formula n) :
    p.graphCost.tableCells = 0 := by
  induction p with
  | atom a => rfl
  | top => rfl
  | bot => rfl
  | not p ih =>
      change p.graphCost.tableCells + 0 = 0
      simpa using ih
  | and p q ihp ihq =>
      change p.graphCost.tableCells + q.graphCost.tableCells + 0 = 0
      simp [ihp, ihq]
  | or p q ihp ihq =>
      change p.graphCost.tableCells + q.graphCost.tableCells + 0 = 0
      simp [ihp, ihq]

theorem graphCost_not_degree_eq_two {n : Nat} (p : Formula n) :
    (Formula.not p).graphCost.maxDegree = 2 := by
  have hp := graphCost_degree_le_two p
  change max p.graphCost.maxDegree 2 = 2
  exact Nat.max_eq_right hp

theorem graphCost_and_degree_eq_two {n : Nat} (p q : Formula n) :
    (Formula.and p q).graphCost.maxDegree = 2 := by
  have hp := graphCost_degree_le_two p
  have hq := graphCost_degree_le_two q
  change max (max p.graphCost.maxDegree q.graphCost.maxDegree) 2 = 2
  exact Nat.max_eq_right (max_le hp hq)

theorem graphCost_or_degree_eq_two {n : Nat} (p q : Formula n) :
    (Formula.or p q).graphCost.maxDegree = 2 := by
  have hp := graphCost_degree_le_two p
  have hq := graphCost_degree_le_two q
  change max (max p.graphCost.maxDegree q.graphCost.maxDegree) 2 = 2
  exact Nat.max_eq_right (max_le hp hq)

theorem graphCost_anyOpt_degree_eq_two {n : Nat} (ps : List (Formula n))
    (hne : ps ≠ []) (hall : ∀ p ∈ ps, p.graphCost.maxDegree = 2) :
    (anyOpt ps).graphCost.maxDegree = 2 := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
      cases ps with
      | nil => simpa [anyOpt] using hall p (by simp)
      | cons q qs =>
          rw [anyOpt]
          exact graphCost_or_degree_eq_two p (anyOpt (q :: qs))

theorem graphCost_duplicatedAndMany_degree_eq_two {n : Nat} (p : Formula n)
    (qs : List (Formula n)) (hne : qs ≠ []) :
    (duplicatedAndMany p qs).graphCost.maxDegree = 2 := by
  rw [duplicatedAndMany]
  apply graphCost_anyOpt_degree_eq_two
  · simpa using hne
  · intro branch hbranch
    simp only [List.mem_map] at hbranch
    obtain ⟨q, _, rfl⟩ := hbranch
    exact graphCost_and_degree_eq_two p q

theorem graphCost_sharedAndMany_degree_eq_two {n : Nat} (p : Formula n)
    (qs : List (Formula n)) (hne : qs ≠ []) :
    (sharedAndMany p qs).graphCost.maxDegree = 2 := by
  cases qs with
  | nil => contradiction
  | cons q qs =>
      rw [sharedAndMany]
      exact graphCost_and_degree_eq_two p (anyOpt (q :: qs))

/-- Every coordinate of `optimized` is no larger than the corresponding
coordinate of `original`; no backend-specific weights are hidden. -/
structure CostLE {n : Nat} (optimized original : Formula n) : Prop where
  equations : optimized.graphCost.equations ≤ original.graphCost.equations
  multiplications :
    optimized.graphCost.multiplications ≤ original.graphCost.multiplications
  witnesses : optimized.graphCost.witnesses ≤ original.graphCost.witnesses
  maxDegree : optimized.graphCost.maxDegree ≤ original.graphCost.maxDegree
  tableCells : optimized.graphCost.tableCells ≤ original.graphCost.tableCells

namespace CostLE

theorem refl {n : Nat} (p : Formula n) : CostLE p p := by
  constructor <;> exact Nat.le_refl _

theorem trans {n : Nat} {p q r : Formula n} (hpq : CostLE p q)
    (hqr : CostLE q r) : CostLE p r := by
  constructor
  · exact hpq.equations.trans hqr.equations
  · exact hpq.multiplications.trans hqr.multiplications
  · exact hpq.witnesses.trans hqr.witnesses
  · exact hpq.maxDegree.trans hqr.maxDegree
  · exact hpq.tableCells.trans hqr.tableCells

theorem notCongr {n : Nat} {p q : Formula n} (h : CostLE p q) :
    CostLE (.not p) (.not q) := by
  constructor
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      Nat.add_le_add_right h.equations booleanNotGateCost.equations
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      Nat.add_le_add_right h.multiplications booleanNotGateCost.multiplications
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      Nat.add_le_add_right h.witnesses booleanNotGateCost.witnesses
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      max_le_max h.maxDegree (Nat.le_refl booleanNotGateCost.maxDegree)
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      Nat.add_le_add_right h.tableCells booleanNotGateCost.tableCells

theorem binaryCongr {n : Nat} {p p' q q' : Formula n}
    (hp : CostLE p p') (hq : CostLE q q') :
    CostLE (.and p q) (.and p' q') ∧ CostLE (.or p q) (.or p' q') := by
  have heq : p.graphCost.equations + q.graphCost.equations ≤
      p'.graphCost.equations + q'.graphCost.equations :=
    Nat.add_le_add hp.equations hq.equations
  have hmul : p.graphCost.multiplications + q.graphCost.multiplications ≤
      p'.graphCost.multiplications + q'.graphCost.multiplications :=
    Nat.add_le_add hp.multiplications hq.multiplications
  have hwit : p.graphCost.witnesses + q.graphCost.witnesses ≤
      p'.graphCost.witnesses + q'.graphCost.witnesses :=
    Nat.add_le_add hp.witnesses hq.witnesses
  have hdeg : max p.graphCost.maxDegree q.graphCost.maxDegree ≤
      max p'.graphCost.maxDegree q'.graphCost.maxDegree :=
    max_le_max hp.maxDegree hq.maxDegree
  have hcell : p.graphCost.tableCells + q.graphCost.tableCells ≤
      p'.graphCost.tableCells + q'.graphCost.tableCells :=
    Nat.add_le_add hp.tableCells hq.tableCells
  have hand : CostLE (.and p q) (.and p' q') := by
    constructor
    · simpa [graphCost, toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
        Nat.add_le_add_right heq booleanBinaryGateCost.equations
    · simpa [graphCost, toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
        Nat.add_le_add_right hmul booleanBinaryGateCost.multiplications
    · simpa [graphCost, toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
        Nat.add_le_add_right hwit booleanBinaryGateCost.witnesses
    · simpa [graphCost, toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
        max_le_max hdeg (Nat.le_refl booleanBinaryGateCost.maxDegree)
    · simpa [graphCost, toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
        Nat.add_le_add_right hcell booleanBinaryGateCost.tableCells
  refine ⟨hand, ?_⟩
  constructor
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using hand.equations
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using
      hand.multiplications
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using hand.witnesses
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using hand.maxDegree
  · simpa [graphCost, toGraph,
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost] using hand.tableCells

end CostLE

end Formula

/-! ## 2. Raw local claims and their fail-closed checker -/

/-- Rule payloads reconstruct both endpoints; they do not trust the endpoints
carried by an untrusted claim. -/
inductive Rule (n : Nat) where
  | notTop
  | notBot
  | doubleNot (p : Formula n)
  | andTopLeft (p : Formula n)
  | andTopRight (p : Formula n)
  | andBotLeft (p : Formula n)
  | andBotRight (p : Formula n)
  | orBotLeft (p : Formula n)
  | orBotRight (p : Formula n)
  | orTopLeft (p : Formula n)
  | orTopRight (p : Formula n)
  | factorAnd (p q r : Formula n)
  | factorOr (p q r : Formula n)
  | fanoutAnd (p : Formula n) (qs : List (Formula n))
  deriving DecidableEq, Repr

namespace Rule

def source {n : Nat} : Rule n → Formula n
  | .notTop => .not .top
  | .notBot => .not .bot
  | .doubleNot p => .not (.not p)
  | .andTopLeft p => .and .top p
  | .andTopRight p => .and p .top
  | .andBotLeft p => .and .bot p
  | .andBotRight p => .and p .bot
  | .orBotLeft p => .or .bot p
  | .orBotRight p => .or p .bot
  | .orTopLeft p => .or .top p
  | .orTopRight p => .or p .top
  | .factorAnd p q r => .or (.and p q) (.and p r)
  | .factorOr p q r => .and (.or p q) (.or p r)
  | .fanoutAnd p qs => Formula.duplicatedAndMany p qs

def target {n : Nat} : Rule n → Formula n
  | .notTop => .bot
  | .notBot => .top
  | .doubleNot p => p
  | .andTopLeft p | .andTopRight p => p
  | .andBotLeft _ | .andBotRight _ => .bot
  | .orBotLeft p | .orBotRight p => p
  | .orTopLeft _ | .orTopRight _ => .top
  | .factorAnd p q r => .and p (.or q r)
  | .factorOr p q r => .or p (.and q r)
  | .fanoutAnd p qs => Formula.sharedAndMany p qs

/-- Empty fanout is semantically harmless but is not an optimization, so the
validator rejects it. -/
def Guard {n : Nat} : Rule n → Prop
  | .fanoutAnd _ qs => qs ≠ []
  | _ => True

def guardCheck {n : Nat} : Rule n → Bool
  | .fanoutAnd _ qs => !qs.isEmpty
  | _ => true

theorem guardCheck_eq_true {n : Nat} (r : Rule n) :
    r.guardCheck = true ↔ r.Guard := by
  cases r <;> simp [guardCheck, Guard]

theorem sound {n : Nat} (truth : Fin n → Prop) (r : Rule n) (hguard : r.Guard) :
    Formula.Holds truth r.source ↔ Formula.Holds truth r.target := by
  cases r with
  | notTop => simp [source, target, Formula.Holds]
  | notBot => simp [source, target, Formula.Holds]
  | doubleNot p => simp [source, target, Formula.Holds]
  | andTopLeft p => simp [source, target, Formula.Holds]
  | andTopRight p => simp [source, target, Formula.Holds]
  | andBotLeft p => simp [source, target, Formula.Holds]
  | andBotRight p => simp [source, target, Formula.Holds]
  | orBotLeft p => simp [source, target, Formula.Holds]
  | orBotRight p => simp [source, target, Formula.Holds]
  | orTopLeft p => simp [source, target, Formula.Holds]
  | orTopRight p => simp [source, target, Formula.Holds]
  | factorAnd p q r => simp [source, target, Formula.Holds, and_or_left]
  | factorOr p q r => simp [source, target, Formula.Holds, or_and_left]
  | fanoutAnd p qs => exact Formula.sharedAndMany_holds_iff truth p qs |>.symm

theorem equations_nonincrease {n : Nat} (r : Rule n) (hguard : r.Guard) :
    r.target.graphCost.equations ≤ r.source.graphCost.equations := by
  cases r with
  | fanoutAnd p qs =>
      have hmap : qs.map Formula.toGraph ≠ [] := by simpa [Guard] using hguard
      have hs :=
        Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAndMany_exact_saving
          p.toGraph (qs.map Formula.toGraph) hmap
      change
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.sharedAndMany p qs).toGraph).equations ≤
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.duplicatedAndMany p qs).toGraph).equations
      rw [Formula.toGraph_duplicatedAndMany, Formula.toGraph_sharedAndMany]
      omega
  | doubleNot p =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost]
      omega
  | factorAnd p q r | factorOr p q r =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanBinaryGateCost]
      omega
  | _ =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost, booleanBinaryGateCost]

theorem multiplications_nonincrease {n : Nat} (r : Rule n) (hguard : r.Guard) :
    r.target.graphCost.multiplications ≤ r.source.graphCost.multiplications := by
  cases r with
  | fanoutAnd p qs =>
      have hmap : qs.map Formula.toGraph ≠ [] := by simpa [Guard] using hguard
      have hs :=
        Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAndMany_exact_saving
          p.toGraph (qs.map Formula.toGraph) hmap
      change
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.sharedAndMany p qs).toGraph).multiplications ≤
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.duplicatedAndMany p qs).toGraph).multiplications
      rw [Formula.toGraph_duplicatedAndMany, Formula.toGraph_sharedAndMany]
      omega
  | doubleNot p =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost]
      omega
  | factorAnd p q r | factorOr p q r =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanBinaryGateCost]
      omega
  | _ =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost, booleanBinaryGateCost]

theorem witnesses_nonincrease {n : Nat} (r : Rule n) (hguard : r.Guard) :
    r.target.graphCost.witnesses ≤ r.source.graphCost.witnesses := by
  cases r with
  | fanoutAnd p qs =>
      have hmap : qs.map Formula.toGraph ≠ [] := by simpa [Guard] using hguard
      have hs :=
        Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAndMany_exact_saving
          p.toGraph (qs.map Formula.toGraph) hmap
      change
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.sharedAndMany p qs).toGraph).witnesses ≤
        (Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
          (Formula.duplicatedAndMany p qs).toGraph).witnesses
      rw [Formula.toGraph_duplicatedAndMany, Formula.toGraph_sharedAndMany]
      omega
  | doubleNot p =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost]
      omega
  | factorAnd p q r | factorOr p q r =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanBinaryGateCost]
      omega
  | _ =>
      simp [source, target, Formula.graphCost, Formula.toGraph,
        Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost,
        booleanNotGateCost, booleanBinaryGateCost]

theorem source_degree_eq_two {n : Nat} (r : Rule n) (hguard : r.Guard) :
    r.source.graphCost.maxDegree = 2 := by
  cases r with
  | fanoutAnd p qs =>
      exact Formula.graphCost_duplicatedAndMany_degree_eq_two p qs hguard
  | notTop | notBot | doubleNot =>
      apply Formula.graphCost_not_degree_eq_two
  | andTopLeft | andTopRight | andBotLeft | andBotRight | factorOr =>
      apply Formula.graphCost_and_degree_eq_two
  | orBotLeft | orBotRight | orTopLeft | orTopRight | factorAnd =>
      apply Formula.graphCost_or_degree_eq_two

theorem cost_nonincrease {n : Nat} (r : Rule n) (hguard : r.Guard) :
    Formula.CostLE r.target r.source := by
  constructor
  · exact equations_nonincrease r hguard
  · exact multiplications_nonincrease r hguard
  · exact witnesses_nonincrease r hguard
  · rw [source_degree_eq_two r hguard]
    exact Formula.graphCost_degree_le_two r.target
  · rw [Formula.graphCost_tableCells_eq_zero, Formula.graphCost_tableCells_eq_zero]

end Rule

/-- Redundant endpoints make this suitable as decoded, untrusted certificate
data.  Changing either endpoint without changing the rule causes rejection. -/
structure LocalClaim (n : Nat) where
  before : Formula n
  after : Formula n
  rule : Rule n
  deriving DecidableEq, Repr

def ValidLocal {n : Nat} (c : LocalClaim n) : Prop :=
  c.before = c.rule.source ∧ c.after = c.rule.target ∧ c.rule.Guard

def checkLocal {n : Nat} (c : LocalClaim n) : Bool :=
  decide (c.before = c.rule.source) &&
    decide (c.after = c.rule.target) && c.rule.guardCheck

theorem checkLocal_eq_true_iff {n : Nat} (c : LocalClaim n) :
    checkLocal c = true ↔ ValidLocal c := by
  simp [checkLocal, ValidLocal, Rule.guardCheck_eq_true, and_assoc]

theorem checkLocal_sound {n : Nat} (truth : Fin n → Prop) (c : LocalClaim n)
    (hcheck : checkLocal c = true) :
    Formula.Holds truth c.before ↔ Formula.Holds truth c.after := by
  simp only [checkLocal, Bool.and_eq_true, decide_eq_true_eq,
    Rule.guardCheck_eq_true] at hcheck
  rcases hcheck with ⟨⟨hbefore, hafter⟩, hguard⟩
  rw [hbefore, hafter]
  exact c.rule.sound truth hguard

/-! ## 3. Compositional raw certificates -/

inductive Certificate (n : Nat) where
  | refl (p : Formula n)
  | rewrite (claim : LocalClaim n)
  | trans (left right : Certificate n)
  | notCongr (child : Certificate n)
  | andCongr (left right : Certificate n)
  | orCongr (left right : Certificate n)
  deriving Repr

namespace Certificate

def source {n : Nat} : Certificate n → Formula n
  | .refl p => p
  | .rewrite c => c.before
  | .trans left _ => left.source
  | .notCongr child => .not child.source
  | .andCongr left right => .and left.source right.source
  | .orCongr left right => .or left.source right.source

def target {n : Nat} : Certificate n → Formula n
  | .refl p => p
  | .rewrite c => c.after
  | .trans _ right => right.target
  | .notCongr child => .not child.target
  | .andCongr left right => .and left.target right.target
  | .orCongr left right => .or left.target right.target

/-- A transitive node checks its boundary in addition to both children. -/
def check {n : Nat} : Certificate n → Bool
  | .refl _ => true
  | .rewrite c => checkLocal c
  | .trans left right =>
      left.check && right.check && decide (left.target = right.source)
  | .notCongr child => child.check
  | .andCongr left right | .orCongr left right => left.check && right.check

theorem check_sound {n : Nat} (truth : Fin n → Prop) (cert : Certificate n)
    (hcheck : cert.check = true) :
    Formula.Holds truth cert.source ↔ Formula.Holds truth cert.target := by
  induction cert with
  | refl p => rfl
  | rewrite claim => exact checkLocal_sound truth claim hcheck
  | trans left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hleft, hright⟩, hboundary⟩
      have h1 := ihLeft hleft
      have h2 := ihRight hright
      have h1' : Formula.Holds truth left.source ↔ Formula.Holds truth right.source := by
        simpa [hboundary] using h1
      exact h1'.trans h2
  | notCongr child ih =>
      exact not_congr (ih hcheck)
  | andCongr left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true] at hcheck
      exact and_congr (ihLeft hcheck.1) (ihRight hcheck.2)
  | orCongr left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true] at hcheck
      exact or_congr (ihLeft hcheck.1) (ihRight hcheck.2)

/-- Accepted certificates are optimization-oriented as well as semantic: all
five symbolic backend coordinates are nonincreasing. -/
theorem check_cost_nonincrease {n : Nat} (cert : Certificate n)
    (hcheck : cert.check = true) : Formula.CostLE cert.target cert.source := by
  induction cert with
  | refl p => exact Formula.CostLE.refl p
  | rewrite claim =>
      simp only [check, checkLocal, Bool.and_eq_true, decide_eq_true_eq,
        Rule.guardCheck_eq_true] at hcheck
      rcases hcheck with ⟨⟨hbefore, hafter⟩, hguard⟩
      rw [source, target, hbefore, hafter]
      exact claim.rule.cost_nonincrease hguard
  | trans left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨hleft, hright⟩, hboundary⟩
      have hl := ihLeft hleft
      have hr := ihRight hright
      have hr' : Formula.CostLE right.target left.target := by
        simpa [hboundary] using hr
      exact hr'.trans hl
  | notCongr child ih =>
      exact Formula.CostLE.notCongr (ih hcheck)
  | andCongr left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true] at hcheck
      exact (Formula.CostLE.binaryCongr (ihLeft hcheck.1) (ihRight hcheck.2)).1
  | orCongr left right ihLeft ihRight =>
      simp only [check, Bool.and_eq_true] at hcheck
      exact (Formula.CostLE.binaryCongr (ihLeft hcheck.1) (ihRight hcheck.2)).2

theorem graphEval_iff {F : Type*} [Field F] {n : Nat} (residual : Fin n → F)
    (cert : Certificate n) (hcheck : cert.check = true) :
    Eval residual cert.source.toGraph ↔ Eval residual cert.target.toGraph := by
  rw [Formula.graphEval_iff_holds, Formula.graphEval_iff_holds]
  exact cert.check_sound (fun a => residual a = 0) hcheck

theorem accepts_iff {F : Type*} [Field F] {n : Nat} (residual : Fin n → F)
    (cert : Certificate n) (hcheck : cert.check = true) :
    Accepts residual cert.source.toGraph ↔ Accepts residual cert.target.toGraph := by
  rw [compile_exact, compile_exact]
  exact cert.graphEval_iff residual hcheck

end Certificate

/-! ## 4. A deterministic, checker-gated optimizer -/

def ruleClaim {n : Nat} (before : Formula n) (r : Rule n) : LocalClaim n where
  before := before
  after := r.target
  rule := r

/-- Deterministic priority order for one root proposal. -/
def proposeRoot {n : Nat} : Formula n → Option (Rule n)
  | .not .top => some .notTop
  | .not .bot => some .notBot
  | .not (.not p) => some (.doubleNot p)
  | .and .top p => some (.andTopLeft p)
  | .and p .top => some (.andTopRight p)
  | .and .bot p => some (.andBotLeft p)
  | .and p .bot => some (.andBotRight p)
  | .or .bot p => some (.orBotLeft p)
  | .or p .bot => some (.orBotRight p)
  | .or .top p => some (.orTopLeft p)
  | .or p .top => some (.orTopRight p)
  | .or (.and p q) (.and p' r) =>
      if p = p' then some (.factorAnd p q r) else none
  | .and (.or p q) (.or p' r) =>
      if p = p' then some (.factorOr p q r) else none
  | _ => none

/-- Finish a child-validated certificate with at most one checked root step.
If proposal or checker logic is wrong, the proposal is silently refused. -/
def finish {n : Nat} (base : Certificate n) : Formula n × Certificate n :=
  match proposeRoot base.target with
  | none => (base.target, base)
  | some rule =>
      let claim := ruleClaim base.target rule
      if checkLocal claim then
        (rule.target, .trans base (.rewrite claim))
      else
        (base.target, base)

theorem finish_source {n : Nat} (base : Certificate n) :
    (finish base).2.source = base.source := by
  simp only [finish]
  split <;> rename_i hproposal
  · rfl
  · split <;> rfl

theorem finish_target {n : Nat} (base : Certificate n) :
    (finish base).2.target = (finish base).1 := by
  simp only [finish]
  split <;> rename_i hproposal
  · rfl
  · split <;> rfl

theorem finish_checked {n : Nat} (base : Certificate n) (hbase : base.check = true) :
    (finish base).2.check = true := by
  simp only [finish]
  split <;> rename_i hproposal
  · exact hbase
  · split <;> rename_i hlocal
    · simp only [Certificate.check, hbase, Bool.true_and, Certificate.source]
      rw [hlocal]
      simp [ruleClaim]
    · exact hbase

/-- Recursive deterministic optimizer.  Every emitted root step is gated by
`checkLocal`, and congruence certificates retain all child evidence. -/
def optimize {n : Nat} : Formula n → Formula n × Certificate n
  | .atom a => (.atom a, .refl (.atom a))
  | .top => (.top, .refl .top)
  | .bot => (.bot, .refl .bot)
  | .not p =>
      let child := optimize p
      finish (.notCongr child.2)
  | .and p q =>
      let left := optimize p
      let right := optimize q
      finish (.andCongr left.2 right.2)
  | .or p q =>
      let left := optimize p
      let right := optimize q
      finish (.orCongr left.2 right.2)

theorem optimize_source {n : Nat} (p : Formula n) :
    (optimize p).2.source = p := by
  induction p with
  | atom a => rfl
  | top => rfl
  | bot => rfl
  | not p ih =>
      rw [optimize, finish_source]
      simp [Certificate.source, ih]
  | and p q ihp ihq =>
      rw [optimize, finish_source]
      simp [Certificate.source, ihp, ihq]
  | or p q ihp ihq =>
      rw [optimize, finish_source]
      simp [Certificate.source, ihp, ihq]

theorem optimize_target {n : Nat} (p : Formula n) :
    (optimize p).2.target = (optimize p).1 := by
  cases p <;> simp [optimize, finish_target, Certificate.target]

theorem optimize_checked {n : Nat} (p : Formula n) :
    (optimize p).2.check = true := by
  induction p with
  | atom a => rfl
  | top => rfl
  | bot => rfl
  | not p ih =>
      apply finish_checked
      simpa [Certificate.check] using ih
  | and p q ihp ihq =>
      apply finish_checked
      simp [Certificate.check, ihp, ihq]
  | or p q ihp ihq =>
      apply finish_checked
      simp [Certificate.check, ihp, ihq]

theorem optimize_holds_iff {n : Nat} (truth : Fin n → Prop) (p : Formula n) :
    Formula.Holds truth p ↔ Formula.Holds truth (optimize p).1 := by
  have hsem := (optimize p).2.check_sound truth (optimize_checked p)
  rw [optimize_source, optimize_target] at hsem
  exact hsem

theorem optimize_accepts_iff {F : Type*} [Field F] {n : Nat}
    (residual : Fin n → F) (p : Formula n) :
    Accepts residual p.toGraph ↔ Accepts residual (optimize p).1.toGraph := by
  have hsem := (optimize p).2.accepts_iff residual (optimize_checked p)
  rw [optimize_source, optimize_target] at hsem
  exact hsem

theorem optimize_cost_nonincrease {n : Nat} (p : Formula n) :
    Formula.CostLE (optimize p).1 p := by
  have hcost := (optimize p).2.check_cost_nonincrease (optimize_checked p)
  rw [optimize_target, optimize_source] at hcost
  exact hcost

/-- Deterministic entry point for an explicit nonempty DAG fanout opportunity. -/
def optimizeFanout {n : Nat} (p : Formula n) (qs : List (Formula n)) :
    Formula n × Certificate n :=
  let before := Formula.duplicatedAndMany p qs
  let rule := Rule.fanoutAnd p qs
  let claim := ruleClaim before rule
  if checkLocal claim then
    (rule.target, .rewrite claim)
  else
    (before, .refl before)

theorem optimizeFanout_checked {n : Nat} (p : Formula n) (qs : List (Formula n)) :
    (optimizeFanout p qs).2.check = true := by
  simp only [optimizeFanout]
  split <;> rename_i hcheck
  · exact hcheck
  · rfl

theorem optimizeFanout_source {n : Nat} (p : Formula n) (qs : List (Formula n)) :
    (optimizeFanout p qs).2.source = Formula.duplicatedAndMany p qs := by
  simp only [optimizeFanout]
  split <;> rfl

theorem optimizeFanout_target {n : Nat} (p : Formula n) (qs : List (Formula n)) :
    (optimizeFanout p qs).2.target = (optimizeFanout p qs).1 := by
  simp only [optimizeFanout]
  split <;> rfl

theorem optimizeFanout_cost_nonincrease {n : Nat} (p : Formula n)
    (qs : List (Formula n)) :
    Formula.CostLE (optimizeFanout p qs).1 (Formula.duplicatedAndMany p qs) := by
  have hcost := (optimizeFanout p qs).2.check_cost_nonincrease
    (optimizeFanout_checked p qs)
  rw [optimizeFanout_target, optimizeFanout_source] at hcost
  exact hcost

/-! ## 5. Executable rejection and optimization specimens -/

def atom0 : Formula 4 := .atom ⟨0, by decide⟩
def atom1 : Formula 4 := .atom ⟨1, by decide⟩
def atom2 : Formula 4 := .atom ⟨2, by decide⟩
def atom3 : Formula 4 := .atom ⟨3, by decide⟩

def identitySpecimen : Formula 4 :=
  .and .top (.not (.not atom0))

def factorSpecimen : Formula 4 :=
  .or (.and identitySpecimen atom1) (.and identitySpecimen atom2)

def goodFactorClaim : LocalClaim 4 :=
  { before := .or (.and atom0 atom1) (.and atom0 atom2)
    after := .and atom0 (.or atom1 atom2)
    rule := .factorAnd atom0 atom1 atom2 }

def tamperedEndpointClaim : LocalClaim 4 :=
  { goodFactorClaim with after := .and atom3 (.or atom1 atom2) }

def emptyFanoutClaim : LocalClaim 4 :=
  { before := .bot
    after := .bot
    rule := .fanoutAnd atom0 [] }

def brokenBoundaryCertificate : Certificate 4 :=
  .trans (.rewrite goodFactorClaim) (.refl atom3)

#guard checkLocal goodFactorClaim
#guard !checkLocal tamperedEndpointClaim
#guard !checkLocal emptyFanoutClaim
#guard !brokenBoundaryCertificate.check
#guard (optimize factorSpecimen).2.check
#guard (optimize factorSpecimen).1 == .and atom0 (.or atom1 atom2)
#guard (optimizeFanout atom0 [atom1, atom2, atom3]).2.check
#guard (optimizeFanout atom0 []).1 == .bot

theorem factorSpecimen_exact_cost :
    factorSpecimen.graphCost.equations = 30 ∧
    (optimize factorSpecimen).1.graphCost.equations = 13 ∧
    factorSpecimen.graphCost.multiplications = 26 ∧
    (optimize factorSpecimen).1.graphCost.multiplications = 13 ∧
    factorSpecimen.graphCost.witnesses = 17 ∧
    (optimize factorSpecimen).1.graphCost.witnesses = 8 := by
  decide

theorem factorSpecimen_strict :
    (optimize factorSpecimen).1.graphCost.equations <
      factorSpecimen.graphCost.equations ∧
    (optimize factorSpecimen).1.graphCost.multiplications <
      factorSpecimen.graphCost.multiplications ∧
    (optimize factorSpecimen).1.graphCost.witnesses <
      factorSpecimen.graphCost.witnesses := by
  decide

#assert_all_clean [
  Formula.graphEval_iff_holds,
  Formula.holds_anyOpt,
  Formula.sharedAndMany_holds_iff,
  Formula.toGraph_anyOpt,
  Formula.toGraph_duplicatedAndMany,
  Formula.toGraph_sharedAndMany,
  Formula.graphCost_degree_le_two,
  Formula.graphCost_tableCells_eq_zero,
  Formula.graphCost_duplicatedAndMany_degree_eq_two,
  Formula.graphCost_sharedAndMany_degree_eq_two,
  Rule.sound,
  Rule.cost_nonincrease,
  checkLocal_eq_true_iff,
  checkLocal_sound,
  Certificate.check_sound,
  Certificate.check_cost_nonincrease,
  Certificate.graphEval_iff,
  Certificate.accepts_iff,
  finish_source,
  finish_target,
  finish_checked,
  optimize_source,
  optimize_target,
  optimize_checked,
  optimize_holds_iff,
  optimize_accepts_iff,
  optimize_cost_nonincrease,
  optimizeFanout_checked,
  optimizeFanout_source,
  optimizeFanout_target,
  optimizeFanout_cost_nonincrease,
  factorSpecimen_exact_cost,
  factorSpecimen_strict
]

end Dregg2.Metatheory.DirectLogicOptimizerCertificate
