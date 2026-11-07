/-
# Trace-column interpolation for the deployed Effect-VM AIR

This file supplies the concrete BabyBear half of the trace-column bridge: every main-trace
column is Lagrange-interpolated on the committed BabyBear `2^27` domain, arithmetic expressions
are interpreted in those column polynomials, and every arithmetic constraint composition evaluates
to the canonical BabyBear image of `arithResidual` at each trace row.

The one structural premise is `t.rows.length ≤ 2^27`.  This is exactly the deployed BabyBear
2-adicity cap proved in `BabyBearFriField`; it is needed to keep the selected `omega27` row points
distinct.  Interaction-bus constraints are deliberately excluded by `isArith`: their polynomial
argument is the separate LogUp/table AIR, not the main-table row-local composition.
-/
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Dregg2.Circuit.AirChecksSatisfied
import Dregg2.Circuit.BabyBearFriDeployed

namespace Dregg2.Circuit.TraceColumnInterp

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## The concrete deployed row points -/

/-- The maximum deployed BabyBear power-of-two evaluation-domain size. -/
def domainSize : Nat := 2 ^ 27

/-- Row `i` is evaluated at the `i`th point of the committed `omega27` BabyBear domain. -/
noncomputable def rowPt (i : Nat) : BabyBear := omega27 ^ i

/-- The committed `omega27` has exact multiplicative order `2^27`. -/
theorem omega27_isPrimitiveRoot : IsPrimitiveRoot omega27 domainSize := by
  have hnot : omega27 ^ (2 : Nat) ^ 26 ≠ 1 := by
    rw [omega27_neg]
    decide
  have hfin : omega27 ^ (2 : Nat) ^ (26 + 1) = 1 := by
    rw [show (2 : Nat) ^ (26 + 1) = (2 ^ 26) * 2 by ring]
    rw [pow_mul, omega27_neg]
    simp
  have hord : orderOf omega27 = (2 : Nat) ^ (26 + 1) :=
    orderOf_eq_prime_pow hnot hfin
  rw [domainSize, show (27 : Nat) = 26 + 1 by omega, ← hord]
  exact IsPrimitiveRoot.orderOf omega27

/-- `rowPt` is literally the point map of the committed max-domain FRI geometry. -/
theorem rowPt_eq_deployed_point (i : Nat) (hi : i < domainSize) :
    rowPt i = friSetupMaxDomain.geom.p ⟨i, by simpa [domainSize] using hi⟩ := by
  rfl

/-- Distinct in-range row indices select distinct deployed BabyBear domain points. -/
theorem rowPt_injective_on_range {n : Nat} (hn : n ≤ domainSize) :
    Set.InjOn rowPt (Finset.range n) := by
  intro i hi j hj hij
  apply omega27_isPrimitiveRoot.pow_inj
  · exact lt_of_lt_of_le (Finset.mem_range.mp hi) hn
  · exact lt_of_lt_of_le (Finset.mem_range.mp hj) hn
  · exact hij

/-! ## Row interpolation and real trace columns -/

/-- Interpolate one BabyBear value per real trace row on the deployed row points. -/
noncomputable def rowPoly (t : VmTrace) (v : Nat → BabyBear) : Polynomial BabyBear :=
  Lagrange.interpolate (Finset.range t.rows.length) rowPt v

/-- Lagrange interpolation reads back the supplied value at every real trace row. -/
theorem rowPoly_eval (t : VmTrace) (v : Nat → BabyBear)
    (hcap : t.rows.length ≤ domainSize) (i : Nat) (hi : i < t.rows.length) :
    (rowPoly t v).eval (rowPt i) = v i := by
  exact Lagrange.eval_interpolate_at_node v (rowPt_injective_on_range hcap)
    (Finset.mem_range.mpr hi)

/-- The genuine main-trace column polynomial.  Rows are `Assignment = Nat → Int`, so `getD`
selects the real row and agrees definitionally with `envAt`; the cast is the canonical `Int.cast`
into the deployed BabyBear field. -/
noncomputable def colPoly (t : VmTrace) (col : Nat) : Polynomial BabyBear :=
  rowPoly t fun i => ((t.rows.getD i zeroAsg col : Int) : BabyBear)

/-- A column polynomial reads back the exact deployed trace cell at a real row. -/
theorem colPoly_eval (t : VmTrace) (col : Nat)
    (hcap : t.rows.length ≤ domainSize) (i : Nat) (hi : i < t.rows.length) :
    (colPoly t col).eval (rowPt i) = (((envAt t i).loc col : Int) : BabyBear) := by
  exact rowPoly_eval t _ hcap i hi

/-! ## Polynomial interpretations of the two expression grammars -/

/-- Interpret a deployed one-row expression in the genuine column polynomials. -/
noncomputable def exprPoly (t : VmTrace) : EmittedExpr → Polynomial BabyBear
  | .var col => colPoly t col
  | .const k => C (k : BabyBear)
  | .add a b => exprPoly t a + exprPoly t b
  | .mul a b => exprPoly t a * exprPoly t b

/-- A polynomial-level next-row operator.  It is an interpolation of the shifted values of `p`,
with zero at the final row, exactly matching `envAt`'s `List.getD` zero-off-the-end convention. -/
noncomputable def nextShift (t : VmTrace) (p : Polynomial BabyBear) : Polynomial BabyBear :=
  rowPoly t fun i => if i + 1 < t.rows.length then p.eval (rowPt (i + 1)) else 0

/-- Shifting a genuine column polynomial reads the exact `envAt.nxt` cell, including the final-row
zero default. -/
theorem nextShift_colPoly_eval (t : VmTrace) (col : Nat)
    (hcap : t.rows.length ≤ domainSize) (i : Nat) (hi : i < t.rows.length) :
    (nextShift t (colPoly t col)).eval (rowPt i) =
      (((envAt t i).nxt col : Int) : BabyBear) := by
  rw [nextShift, rowPoly_eval t _ hcap i hi]
  by_cases hn : i + 1 < t.rows.length
  · rw [if_pos hn, colPoly_eval t col hcap (i + 1) hn]
    rfl
  · rw [if_neg hn]
    simp only [envAt]
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hn)]
    rfl

/-- Interpret a deployed two-row expression in current and shifted genuine column polynomials. -/
noncomputable def windowExprPoly (t : VmTrace) : WindowExpr → Polynomial BabyBear
  | .loc col => colPoly t col
  | .nxt col => nextShift t (colPoly t col)
  | .const k => C (k : BabyBear)
  | .add a b => windowExprPoly t a + windowExprPoly t b
  | .mul a b => windowExprPoly t a * windowExprPoly t b

/-- ⚑ The challenge-gate composition. A `chal i` leaf interpolates to the CONSTANT polynomial
`C (t.chal i)` — the challenge is fixed across the whole domain (one Fiat–Shamir draw per proof),
which is exactly `p3-air`'s `ExtEntry::Challenge => degree_multiple() = 0` in the interpolation
picture: it contributes no degree because it is not a column.

⚠ Base-lane, like `arithResidual`: the deployed composition is over the quartic extension. See
`AirChecksSatisfied.arithResidual`'s `chalGate` arm for the fidelity note. -/
noncomputable def chalExprPoly (t : VmTrace) : ChalExpr → Polynomial BabyBear
  | .loc col => colPoly t col
  | .nxt col => nextShift t (colPoly t col)
  | .const k => C (k : BabyBear)
  | .chal i => C ((t.chal i : Int) : BabyBear)
  | .add a b => chalExprPoly t a + chalExprPoly t b
  | .mul a b => chalExprPoly t a * chalExprPoly t b

theorem exprPoly_eval (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) (e : EmittedExpr) :
    (exprPoly t e).eval (rowPt i) = (((e.eval (envAt t i).loc : Int)) : BabyBear) := by
  induction e with
  | var col => exact colPoly_eval t col hcap i hi
  | const k => simp [exprPoly, EmittedExpr.eval]
  | add a b iha ihb => simp [exprPoly, EmittedExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [exprPoly, EmittedExpr.eval, iha, ihb]

theorem windowExprPoly_eval (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) (e : WindowExpr) :
    (windowExprPoly t e).eval (rowPt i) = (((e.eval (envAt t i) : Int)) : BabyBear) := by
  induction e with
  | loc col => exact colPoly_eval t col hcap i hi
  | nxt col => exact nextShift_colPoly_eval t col hcap i hi
  | const k => simp [windowExprPoly, WindowExpr.eval]
  | add a b iha ihb => simp [windowExprPoly, WindowExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [windowExprPoly, WindowExpr.eval, iha, ihb]

theorem chalExprPoly_eval (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) (e : ChalExpr) :
    (chalExprPoly t e).eval (rowPt i) = (((e.eval (envAt t i) : Int)) : BabyBear) := by
  induction e with
  | loc col => exact colPoly_eval t col hcap i hi
  | nxt col => exact nextShift_colPoly_eval t col hcap i hi
  | const k => simp [chalExprPoly, ChalExpr.eval]
  | chal j => simp [chalExprPoly, ChalExpr.eval, envAt]
  | add a b iha ihb => simp [chalExprPoly, ChalExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [chalExprPoly, ChalExpr.eval, iha, ihb]

/-! ## Guard selectors and the arithmetic constraint composition -/

private noncomputable def boolScalar (b : Bool) : BabyBear := if b then 1 else 0

/-- Interpolated first-row selector. -/
noncomputable def firstSelector (t : VmTrace) : Polynomial BabyBear :=
  rowPoly t fun i => boolScalar (i == 0)

/-- Interpolated last-row selector. -/
noncomputable def lastSelector (t : VmTrace) : Polynomial BabyBear :=
  rowPoly t fun i => boolScalar (i + 1 == t.rows.length)

theorem firstSelector_eval (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) :
    (firstSelector t).eval (rowPt i) = boolScalar (i == 0) :=
  rowPoly_eval t _ hcap i hi

theorem lastSelector_eval (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) :
    (lastSelector t).eval (rowPt i) = boolScalar (i + 1 == t.rows.length) :=
  rowPoly_eval t _ hcap i hi

/-- The main-table arithmetic constraint composition.  `d` remains an explicit argument so this
has the deployed descriptor-facing shape; the expression itself is determined by `c` and the
descriptor's concrete witness `t`.  Bus arms are `0` only as a total-function placeholder and are
excluded from the correctness theorem by `isArith`. -/
noncomputable def constraintPoly (_d : EffectVmDescriptor2) (t : VmTrace) :
    VmConstraint2 → Polynomial BabyBear
  | .base (.gate body) => (1 - lastSelector t) * exprPoly t body
  | .base (.transition hi lo) =>
      (1 - lastSelector t) *
        (nextShift t (colPoly t (sbCol hi)) - colPoly t (saCol lo))
  | .base (.boundary .first body) => firstSelector t * exprPoly t body
  | .base (.boundary .last body) => lastSelector t * exprPoly t body
  | .base (.piBinding .first col k) =>
      firstSelector t * (colPoly t col - C ((t.pub k : Int) : BabyBear))
  | .base (.piBinding .last col k) =>
      lastSelector t * (colPoly t col - C ((t.pub k : Int) : BabyBear))
  | .windowGate w =>
      if w.onTransition then (1 - lastSelector t) * windowExprPoly t w.body
      else windowExprPoly t w.body
  | .chalGate w =>
      if w.onTransition then (1 - lastSelector t) * chalExprPoly t w.body
      else chalExprPoly t w.body
  | .lookup _ => 0
  | .memOp _ => 0
  | .mapOp _ => 0
  | .umemOp _ => 0
  | .proofBind _ => 0

/-- **K'(b), the trace-column interpolation bridge.**  At every real deployed trace row, the
composition made from interpolated trace columns evaluates to the canonical BabyBear lift of the
raw integer AIR residual.  The theorem is intentionally scoped to `isArith`; LogUp/table bus arms
do not have a row-local main-table composition. -/
theorem constraintPoly_eval_eq_arithResidual
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (i : Nat) (hi : i < t.rows.length) (c : VmConstraint2) (hc : isArith c) :
    (constraintPoly d t c).eval (rowPt i) =
      ((arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c : Int) : BabyBear) := by
  cases c with
  | base c =>
      cases c with
      | gate body =>
          cases hlast : (i + 1 == t.rows.length) <;>
            simp [constraintPoly, arithResidual, eval_sub, eval_mul, eval_one,
              lastSelector_eval t hcap i hi, boolScalar, hlast, exprPoly_eval t hcap i hi]
      | transition high low =>
          cases hlast : (i + 1 == t.rows.length) <;>
            simp [constraintPoly, arithResidual, eval_sub, eval_mul, eval_one,
              lastSelector_eval t hcap i hi, boolScalar, hlast,
              nextShift_colPoly_eval t (sbCol high) hcap i hi,
              colPoly_eval t (saCol low) hcap i hi]
      | boundary row body =>
          cases row with
          | first =>
              cases hfirst : (i == 0) <;>
                simp [constraintPoly, arithResidual, eval_mul,
                  firstSelector_eval t hcap i hi, boolScalar, hfirst,
                  exprPoly_eval t hcap i hi]
          | last =>
              cases hlast : (i + 1 == t.rows.length) <;>
                simp [constraintPoly, arithResidual, eval_mul,
                  lastSelector_eval t hcap i hi, boolScalar, hlast,
                  exprPoly_eval t hcap i hi]
      | piBinding row col k =>
          cases row with
          | first =>
              cases hfirst : (i == 0) <;>
                simp [constraintPoly, arithResidual, eval_sub, eval_mul,
                  firstSelector_eval t hcap i hi, boolScalar, hfirst,
                  colPoly_eval t col hcap i hi, envAt]
          | last =>
              cases hlast : (i + 1 == t.rows.length) <;>
                simp [constraintPoly, arithResidual, eval_sub, eval_mul,
                  lastSelector_eval t hcap i hi, boolScalar, hlast,
                  colPoly_eval t col hcap i hi, envAt]
  | windowGate w =>
      cases hw : w.onTransition <;>
        cases hlast : (i + 1 == t.rows.length) <;>
          simp [constraintPoly, arithResidual, hw, hlast, eval_sub, eval_mul, eval_one,
            lastSelector_eval t hcap i hi, boolScalar,
            windowExprPoly_eval t hcap i hi]
  | chalGate w =>
      cases hw : w.onTransition <;>
        cases hlast : (i + 1 == t.rows.length) <;>
          simp [constraintPoly, arithResidual, hw, hlast, eval_sub, eval_mul, eval_one,
            lastSelector_eval t hcap i hi, boolScalar,
            chalExprPoly_eval t hcap i hi]
  | lookup l => exact absurd hc (by simp [isArith])
  | memOp m => exact absurd hc (by simp [isArith])
  | mapOp m => exact absurd hc (by simp [isArith])
  | umemOp m => exact absurd hc (by simp [isArith])
  | proofBind p => exact absurd hc (by simp [isArith])

/-- Explicit statement of the excluded interaction-bus arms. -/
theorem bus_constraints_excluded :
    (∀ l, ¬ isArith (.lookup l)) ∧
    (∀ m, ¬ isArith (.memOp m)) ∧
    (∀ m, ¬ isArith (.mapOp m)) ∧
    (∀ m, ¬ isArith (.umemOp m)) ∧
    (∀ p, ¬ isArith (.proofBind p)) := by
  simp [isArith]

/-! ## Both-truth teeth -/

section Teeth

open Dregg2.Circuit.AirChecksSatisfied

private def gate0 : VmConstraint2 := .base (.gate (.var 0))

/-- FIRE: the honest deployed two-row trace's genuine column composition equals its residual. -/
example :
    (constraintPoly dArith tHonest gate0).eval (rowPt 0) =
      ((arithResidual (envAt tHonest 0) (0 == 0)
        (0 + 1 == tHonest.rows.length) gate0 : Int) : BabyBear) := by
  apply constraintPoly_eval_eq_arithResidual dArith tHonest
  · simp [domainSize, tHonest]
  · simp [tHonest]
  · simp [gate0, isArith]

/-- The composition obtained by changing the opened value of column `0` by one while retaining
the honest trace residual.  This is not `constraintPoly`; it is the adversary's tampered column
opening passed through the same gate and last-row selector. -/
noncomputable def tamperedGatePoly : Polynomial BabyBear :=
  (1 - lastSelector tHonest) * (colPoly tHonest 0 + C 1)

/-- BITE: changing that column value makes the polynomial evaluation disagree with the honest raw
AIR residual at row zero. -/
theorem tampered_column_bites :
    tamperedGatePoly.eval (rowPt 0) ≠
      ((arithResidual (envAt tHonest 0) (0 == 0)
        (0 + 1 == tHonest.rows.length) gate0 : Int) : BabyBear) := by
  have hcap : tHonest.rows.length ≤ domainSize := by simp [tHonest, domainSize]
  have h0 : 0 < tHonest.rows.length := by simp [tHonest]
  simp only [tamperedGatePoly, eval_mul, eval_sub, eval_one, eval_add, eval_C,
    lastSelector_eval tHonest hcap 0 h0, colPoly_eval tHonest 0 hcap 0 h0]
  simp [gate0, tHonest, zRow, arithResidual, envAt, EmittedExpr.eval, boolScalar]

end Teeth

#assert_axioms omega27_isPrimitiveRoot
#assert_axioms rowPt_injective_on_range
#assert_axioms rowPoly_eval
#assert_axioms colPoly_eval
#assert_axioms nextShift_colPoly_eval
#assert_axioms exprPoly_eval
#assert_axioms windowExprPoly_eval
#assert_axioms constraintPoly_eval_eq_arithResidual
#assert_axioms bus_constraints_excluded
#assert_axioms tampered_column_bites

#check @constraintPoly_eval_eq_arithResidual

end Dregg2.Circuit.TraceColumnInterp
