/-
# Gabbay's matrix semantics: the executable interpolation core

This file formalizes the concrete matrix mechanism used in ePrint 2024/954:

* a matrix symbol has a fixed row arity;
* a valuation supplies a nonempty integer matrix with a declared column length;
* every row is represented by its univariate Lagrange interpolant over `ℚ` at
  the one-based nodes `1, ..., length`;
* `lookup C i t` composes the row interpolant with the polynomial denotation of
  `t`, while `length C` exposes the declared length;
* bounded quantifiers range over exactly those declared nodes;
* zero means true, equality is a squared residual, conjunction/universal use
  addition, and disjunction/existential use multiplication.

The main theorem is a genuine ordinary-logic soundness-and-completeness result,
not merely a restatement of zero-valued semantics.  Its load-bearing carrier is
`ℚ`: every generated residual is nonnegative, so finite sums cannot cancel.

This is the coherent executable core, not every construct in the paper.  In
particular, the impredicative `term(phi)` form and static row-order predicates
are deliberately outside this file.  The Skolem example at the end shows how a
finite function witness is compiled as an input/output matrix and checked by a
bounded universal formula.
-/
import Dregg2.Tactics
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Linarith

namespace Dregg2.Metatheory.GabbayMatrixSemantics

open scoped BigOperators

noncomputable section

/-! ## 1. Intrinsically sized integer matrices and row interpolation -/

/-- A signature of matrix-variable symbols.  The row arity belongs to the
symbol, exactly as in Gabbay's syntax. -/
structure MatrixSignature where
  Symbol : Type
  arity : Symbol -> Nat

/-- A valuation for a symbol of row arity `rows`: a nonempty integer matrix
with an intrinsic, declared column length. -/
structure IntMatrix (rows : Nat) where
  length : Nat
  length_pos : 0 < length
  cell : Fin rows -> Fin length -> Int

/-- A valuation chooses one correctly row-sized matrix for every symbol. -/
abbrev Valuation (S : MatrixSignature) :=
  (C : S.Symbol) -> IntMatrix (S.arity C)

namespace IntMatrix

variable {rows : Nat} (M : IntMatrix rows)

/-- Gabbay's interpolation domain is one-based: column `j` is sampled at
the rational node `j + 1`. -/
def node (j : Fin M.length) : Rat := (j.1 + 1 : Nat)

/-- Distinct declared columns give distinct rational interpolation nodes. -/
theorem node_injective : Function.Injective M.node := by
  intro i j h
  apply Fin.ext
  have h' : i.1 + 1 = j.1 + 1 := by
    exact Nat.cast_injective (R := Rat) h
  exact Nat.add_right_cancel h'

/-- The univariate Lagrange interpolant of one integer row. -/
def rowPolynomial (row : Fin rows) : Polynomial Rat :=
  Lagrange.interpolate Finset.univ M.node
    (fun j => (M.cell row j : Rat))

/-- **Interpolation correctness on the declared domain.**  Evaluating a row
polynomial at the one-based node of a declared column returns that exact cell. -/
@[simp] theorem eval_rowPolynomial (row : Fin rows) (j : Fin M.length) :
    (M.rowPolynomial row).eval (M.node j) = (M.cell row j : Rat) := by
  exact Lagrange.eval_interpolate_at_node _ M.node_injective.injOn
    (Finset.mem_univ j)

/-- Every row interpolant has degree strictly below the declared length. -/
theorem rowPolynomial_degree_lt_length (row : Fin rows) :
    (M.rowPolynomial row).degree < M.length := by
  simpa [rowPolynomial] using
    (Lagrange.degree_interpolate_lt (s := Finset.univ)
      (fun j : Fin M.length => (M.cell row j : Rat)) M.node_injective.injOn)

/-- Exact number of integer cells carried by this matrix. -/
def tableSize : Nat := rows * M.length

@[simp] theorem tableSize_eq : M.tableSize = rows * M.length := rfl

end IntMatrix

/-! ## 2. The one-variable matrix term language -/

/-- The term fragment needed by the matrix construction.  `index` is the
paper's unique variable `X`; `lookup C row t` denotes row interpolation followed
by polynomial composition. -/
inductive Term (S : MatrixSignature) where
  | index
  | rational (q : Rat)
  | add (a b : Term S)
  | sub (a b : Term S)
  | mul (a b : Term S)
  | lookup (C : S.Symbol) (row : Fin (S.arity C)) (arg : Term S)
  | length (C : S.Symbol)

/-- Polynomial denotation of matrix terms. -/
def denoteTerm {S : MatrixSignature} (rho : Valuation S) : Term S -> Polynomial Rat
  | .index => Polynomial.X
  | .rational q => Polynomial.C q
  | .add a b => denoteTerm rho a + denoteTerm rho b
  | .sub a b => denoteTerm rho a - denoteTerm rho b
  | .mul a b => denoteTerm rho a * denoteTerm rho b
  | .lookup C row arg =>
      (rho C).rowPolynomial row |>.comp (denoteTerm rho arg)
  | .length C => Polynomial.C (rho C).length

/-- Numerical term evaluation is polynomial evaluation.  Keeping this named
separates the source semantics from the compiler theorem below. -/
def evalTerm {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (t : Term S) : Rat :=
  (denoteTerm rho t).eval x

@[simp] theorem evalTerm_index {S : MatrixSignature} (rho : Valuation S) (x : Rat) :
    evalTerm rho x (.index : Term S) = x := by
  simp [evalTerm, denoteTerm]

@[simp] theorem evalTerm_rational {S : MatrixSignature} (rho : Valuation S)
    (x q : Rat) :
    evalTerm rho x (.rational q : Term S) = q := by
  simp [evalTerm, denoteTerm]

@[simp] theorem evalTerm_add {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (a b : Term S) :
    evalTerm rho x (.add a b) = evalTerm rho x a + evalTerm rho x b := by
  simp [evalTerm, denoteTerm]

@[simp] theorem evalTerm_sub {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (a b : Term S) :
    evalTerm rho x (.sub a b) = evalTerm rho x a - evalTerm rho x b := by
  simp [evalTerm, denoteTerm]

@[simp] theorem evalTerm_mul {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (a b : Term S) :
    evalTerm rho x (.mul a b) = evalTerm rho x a * evalTerm rho x b := by
  simp [evalTerm, denoteTerm]

@[simp] theorem evalTerm_length {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (C : S.Symbol) :
    evalTerm rho x (.length C) = (rho C).length := by
  simp [evalTerm, denoteTerm]

/-- Lookup is polynomial composition, hence numerical evaluation first
evaluates the index term and then evaluates the selected row interpolant. -/
@[simp] theorem evalTerm_lookup {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (C : S.Symbol) (row : Fin (S.arity C)) (arg : Term S) :
    evalTerm rho x (.lookup C row arg) =
      ((rho C).rowPolynomial row).eval (evalTerm rho x arg) := by
  simp [evalTerm, denoteTerm, Polynomial.eval_comp]

/-- Indexed lookup at `X = j+1` recovers the exact integer table cell. -/
@[simp] theorem eval_lookup_index_at_node {S : MatrixSignature} (rho : Valuation S)
    (C : S.Symbol) (row : Fin (S.arity C)) (j : Fin (rho C).length) :
    evalTerm rho ((rho C).node j) (.lookup C row .index) =
      ((rho C).cell row j : Rat) := by
  simp

/-! ## 3. Zero-true formulas and declared-domain quantifiers -/

/-- The positive first-order formula fragment.  Every bounded quantifier names
the matrix whose declared columns are its exact range. -/
inductive Formula (S : MatrixSignature) where
  | top
  | bottom
  | eq (a b : Term S)
  | and (p q : Formula S)
  | or (p q : Formula S)
  | forallIn (C : S.Symbol) (body : Formula S)
  | existsIn (C : S.Symbol) (body : Formula S)

/-- Gabbay's compositional polynomial residual.  A quantifier captures the
unique index variable and therefore denotes a constant polynomial obtained by
folding the body over all declared one-based nodes. -/
def denoteFormula {S : MatrixSignature} (rho : Valuation S) : Formula S -> Polynomial Rat
  | .top => 0
  | .bottom => 1
  | .eq a b => (denoteTerm rho a - denoteTerm rho b) ^ 2
  | .and p q => denoteFormula rho p + denoteFormula rho q
  | .or p q => denoteFormula rho p * denoteFormula rho q
  | .forallIn C body =>
      Polynomial.C (∑ j : Fin (rho C).length,
        (denoteFormula rho body).eval ((rho C).node j))
  | .existsIn C body =>
      Polynomial.C (∏ j : Fin (rho C).length,
        (denoteFormula rho body).eval ((rho C).node j))

/-- Direct residual evaluation of a compiled formula. -/
def residual {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (p : Formula S) : Rat :=
  (denoteFormula rho p).eval x

/-- Ordinary logical semantics.  This definition does not mention zero-valued
acceptance: equality is equality, connectives are propositions, and bounded
quantifiers are genuine finite `forall`/`exists`. -/
def Holds {S : MatrixSignature} (rho : Valuation S) (x : Rat) : Formula S -> Prop
  | .top => True
  | .bottom => False
  | .eq a b => evalTerm rho x a = evalTerm rho x b
  | .and p q => Holds rho x p /\ Holds rho x q
  | .or p q => Holds rho x p \/ Holds rho x q
  | .forallIn C body => forall j : Fin (rho C).length,
      Holds rho ((rho C).node j) body
  | .existsIn C body => exists j : Fin (rho C).length,
      Holds rho ((rho C).node j) body

/-- Every generated rational residual is nonnegative.  This invariant is the
reason addition and finite sums can represent conjunction and universal
quantification without cancellation. -/
theorem residual_nonnegative {S : MatrixSignature} (rho : Valuation S) :
    forall (p : Formula S) (x : Rat), 0 <= residual rho x p := by
  intro p
  induction p with
  | top => intro x; simp [residual, denoteFormula]
  | bottom => intro x; simp [residual, denoteFormula]
  | eq a b =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_pow,
        Polynomial.eval_sub]
      exact sq_nonneg _
  | and p q ihp ihq =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_add]
      exact add_nonneg (ihp x) (ihq x)
  | or p q ihp ihq =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_mul]
      exact mul_nonneg (ihp x) (ihq x)
  | forallIn C body ih =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_C]
      exact Finset.sum_nonneg fun j _ => ih ((rho C).node j)
  | existsIn C body ih =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_C]
      exact Finset.prod_nonneg fun j _ => ih ((rho C).node j)

/-- **Zero-true soundness and completeness over nonnegative rationals.** -/
theorem residual_eq_zero_iff_holds {S : MatrixSignature} (rho : Valuation S) :
    forall (p : Formula S) (x : Rat), residual rho x p = 0 <-> Holds rho x p := by
  intro p
  induction p with
  | top => intro x; simp [residual, denoteFormula, Holds]
  | bottom => intro x; simp [residual, denoteFormula, Holds]
  | eq a b =>
      intro x
      simp [residual, denoteFormula, Holds, evalTerm, sub_eq_zero]
  | and p q ihp ihq =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_add, Holds]
      have hpiff : (denoteFormula rho p).eval x = 0 <-> Holds rho x p := by
        simpa only [residual] using ihp x
      have hqiff : (denoteFormula rho q).eval x = 0 <-> Holds rho x q := by
        simpa only [residual] using ihq x
      constructor
      · intro h
        have hp : (denoteFormula rho p).eval x = 0 := by
          have hp0 := residual_nonnegative rho p x
          have hq0 := residual_nonnegative rho q x
          change 0 <= (denoteFormula rho p).eval x at hp0
          change 0 <= (denoteFormula rho q).eval x at hq0
          linarith
        have hq : (denoteFormula rho q).eval x = 0 := by
          have hp0 := residual_nonnegative rho p x
          have hq0 := residual_nonnegative rho q x
          change 0 <= (denoteFormula rho p).eval x at hp0
          change 0 <= (denoteFormula rho q).eval x at hq0
          linarith
        exact ⟨hpiff.1 hp, hqiff.1 hq⟩
      · rintro ⟨hp, hq⟩
        rw [hpiff.2 hp, hqiff.2 hq, add_zero]
  | or p q ihp ihq =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_mul, Holds]
      have hpiff : (denoteFormula rho p).eval x = 0 <-> Holds rho x p := by
        simpa only [residual] using ihp x
      have hqiff : (denoteFormula rho q).eval x = 0 <-> Holds rho x q := by
        simpa only [residual] using ihq x
      rw [mul_eq_zero, hpiff, hqiff]
  | forallIn C body ih =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_C, Holds]
      rw [Finset.sum_eq_zero_iff_of_nonneg]
      · constructor
        · intro h j
          exact (ih ((rho C).node j)).1 (h j (Finset.mem_univ j))
        · intro h j _
          exact (ih ((rho C).node j)).2 (h j)
      · intro j _
        exact residual_nonnegative rho body ((rho C).node j)
  | existsIn C body ih =>
      intro x
      simp only [residual, denoteFormula, Polynomial.eval_C, Holds]
      rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨j, _, hj⟩
        exact ⟨j, (ih ((rho C).node j)).1 hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, Finset.mem_univ j, (ih ((rho C).node j)).2 hj⟩

/-- Soundness direction, convenient at proof-system boundaries. -/
theorem sound {S : MatrixSignature} (rho : Valuation S) (p : Formula S) (x : Rat)
    (h : residual rho x p = 0) : Holds rho x p :=
  (residual_eq_zero_iff_holds rho p x).1 h

/-- Completeness direction, convenient for witness generation. -/
theorem complete {S : MatrixSignature} (rho : Valuation S) (p : Formula S) (x : Rat)
    (h : Holds rho x p) : residual rho x p = 0 :=
  (residual_eq_zero_iff_holds rho p x).2 h

/-- A bounded universal performs exactly one body evaluation per declared
column. -/
def quantifierExpansion {S : MatrixSignature} (rho : Valuation S)
    (C : S.Symbol) : Nat := (rho C).length

@[simp] theorem quantifierExpansion_eq_length {S : MatrixSignature}
    (rho : Valuation S) (C : S.Symbol) :
    quantifierExpansion rho C = (rho C).length := rfl

/-- Capturing the unique index makes a bounded universal a constant
polynomial, hence its degree is at most zero. -/
theorem forall_degree_le_zero {S : MatrixSignature} (rho : Valuation S)
    (C : S.Symbol) (body : Formula S) :
    (denoteFormula rho (.forallIn C body)).degree <= 0 := by
  change (Polynomial.C (∑ j : Fin (rho C).length,
    (denoteFormula rho body).eval ((rho C).node j))).degree <= 0
  exact Polynomial.degree_C_le

/-- The same exact degree bound holds for bounded existence. -/
theorem exists_degree_le_zero {S : MatrixSignature} (rho : Valuation S)
    (C : S.Symbol) (body : Formula S) :
    (denoteFormula rho (.existsIn C body)).degree <= 0 := by
  change (Polynomial.C (∏ j : Fin (rho C).length,
    (denoteFormula rho body).eval ((rho C).node j))).degree <= 0
  exact Polynomial.degree_C_le

/-! ## 4. A compiled finite Skolem/function-table witness -/

/-- One matrix symbol whose two rows are respectively an input and its chosen
Skolem output. -/
inductive SkolemSymbol where
  | table
  deriving DecidableEq

def skolemSignature : MatrixSignature where
  Symbol := SkolemSymbol
  arity _ := 2

/-- Three graph entries for the finite function `f(n) = n + 1`:
`(0,1)`, `(1,2)`, `(2,3)`. -/
def successorTable : IntMatrix 2 where
  length := 3
  length_pos := by decide
  cell row col :=
    if row.1 = 0 then (col.1 : Int) else ((col.1 + 1 : Nat) : Int)

@[simp] theorem successorTable_cell (row : Fin 2) (col : Fin successorTable.length) :
    successorTable.cell row col =
      if row.1 = 0 then (col.1 : Int) else ((col.1 + 1 : Nat) : Int) := by
  rfl

def successorValuation : Valuation skolemSignature
  | .table => successorTable

def inputRow : Fin 2 := 0
def outputRow : Fin 2 := 1

/-- Source formula saying that every declared Skolem output is its input plus
one.  This is compiled through the same matrix interpolation and bounded
universal machinery as an arbitrary formula. -/
def successorSkolemFormula : Formula skolemSignature :=
  .forallIn .table
    (.eq
      (.lookup .table outputRow .index)
      (.add (.lookup .table inputRow .index) (.rational 1)))

/-- The concrete function-table witness satisfies the ordinary logical
specification at every one of its three declared columns. -/
theorem successorTable_holds (x : Rat) :
    Holds successorValuation x successorSkolemFormula := by
  simp only [successorSkolemFormula, Holds]
  intro j
  refine (eval_lookup_index_at_node successorValuation SkolemSymbol.table outputRow j).trans ?_
  refine Eq.trans ?_ (evalTerm_add _ _ _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· + ·)
    (eval_lookup_index_at_node successorValuation SkolemSymbol.table inputRow j)
    (evalTerm_rational _ _ _)).symm
  change (((if (outputRow : Fin 2).1 = 0 then (j.1 : Int) else ((j.1 + 1 : Nat) : Int)) : Int) :
      Rat) =
    (((if (inputRow : Fin 2).1 = 0 then (j.1 : Int) else ((j.1 + 1 : Nat) : Int)) : Int) : Rat) + 1
  norm_num [outputRow, inputRow]

/-- The compiled residual of the Skolem table is exactly zero. -/
theorem successorTable_compiles_to_zero (x : Rat) :
    residual successorValuation x successorSkolemFormula = 0 :=
  complete successorValuation successorSkolemFormula x (successorTable_holds x)

/-- The compiled closed formula is the zero polynomial, not merely zero at a
single verifier-selected point. -/
theorem successorTable_polynomial_eq_zero :
    denoteFormula successorValuation successorSkolemFormula = 0 := by
  change Polynomial.C (∑ j : Fin successorTable.length,
    (denoteFormula successorValuation
      (.eq
        (.lookup .table outputRow .index)
        (.add (.lookup .table inputRow .index) (.rational 1)))).eval
      (successorTable.node j)) = 0
  rw [← Polynomial.C_0, Polynomial.C_inj]
  have h := successorTable_compiles_to_zero 0
  simp only [successorSkolemFormula, residual, denoteFormula, Polynomial.eval_C] at h
  exact h

/-- The example's exact witness table size is six integer cells. -/
theorem successorTable_size : successorTable.tableSize = 6 := by
  rfl

/-- The input row's actual interpolant is `X - 1`. -/
theorem successorTable_inputPolynomial :
    successorTable.rowPolynomial inputRow = Polynomial.X - Polynomial.C 1 := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq
  · exact successorTable.node_injective.injOn
  · rw [Polynomial.degree_X_sub_C]
    change 1 < 3
    decide
  · intro j _
    fin_cases j <;>
      norm_num [IntMatrix.node, successorTable_cell, inputRow]

/-- The output row's actual interpolant is `X`. -/
theorem successorTable_outputPolynomial :
    successorTable.rowPolynomial outputRow = Polynomial.X := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq
  · exact successorTable.node_injective.injOn
  · rw [Polynomial.degree_X]
    change 1 < 3
    decide
  · intro j _
    fin_cases j <;>
      norm_num [IntMatrix.node, successorTable_cell, outputRow]

/-- Both nonconstant example rows have exact degree one. -/
theorem successorTable_row_degrees_exact :
    (successorTable.rowPolynomial inputRow).degree = 1 /\
    (successorTable.rowPolynomial outputRow).degree = 1 := by
  rw [successorTable_inputPolynomial, successorTable_outputPolynomial,
    Polynomial.degree_X_sub_C, Polynomial.degree_X]
  exact ⟨rfl, rfl⟩

/-- Each example row is represented by a polynomial of degree strictly below
the three-column table length. -/
theorem successorTable_row_degree_lt_three (row : Fin 2) :
    (successorTable.rowPolynomial row).degree < 3 := by
  exact successorTable.rowPolynomial_degree_lt_length row

#assert_all_clean [IntMatrix.node_injective, IntMatrix.eval_rowPolynomial,
  IntMatrix.rowPolynomial_degree_lt_length, IntMatrix.tableSize_eq,
  evalTerm_lookup, eval_lookup_index_at_node, residual_nonnegative,
  residual_eq_zero_iff_holds, sound, complete, quantifierExpansion_eq_length,
  forall_degree_le_zero, exists_degree_le_zero, successorTable_holds,
  successorTable_cell, successorTable_compiles_to_zero,
  successorTable_polynomial_eq_zero, successorTable_size,
  successorTable_inputPolynomial, successorTable_outputPolynomial,
  successorTable_row_degrees_exact, successorTable_row_degree_lt_three]

end

end Dregg2.Metatheory.GabbayMatrixSemantics
