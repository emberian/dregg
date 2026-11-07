/-
# Coherence bridge for the two Gabbay matrix presentations

`GabbayMatrixCompiler` is the canonical front end: it carries the corrected
finite-field backends, cost algebra, and proof-carrying projection certificate.
`GabbayMatrixSemantics` is retained as a compact executable view with especially
useful interpolation and successor-table specimens.  This module proves that
the latter is an adapter into the former on their complete common fragment.

The only extra premise is positive row arity.  The semantics view permits a
zero-row matrix signature, while the paper and the compiler require every
matrix symbol to have at least one row.  Under that explicit premise, the
bridge proves equality of matrix nodes and row interpolants, term and formula
polynomials, source satisfaction, zero residuals, exact expansion costs, and
the numerator/denominator bounds carried by compiler certificates.  The
successor/Skolem table is transported through the same bridge, including its
exact row polynomials, cost, field certificate, and finite Skolem witness.
-/
import Dregg2.Metatheory.GabbayMatrixCompiler
import Dregg2.Metatheory.GabbayMatrixSemantics

namespace Dregg2.Metatheory.GabbayMatrixBridge

open scoped BigOperators

noncomputable section

/-! ## Signature, matrix, and valuation adapters -/

/-- The exact common-signature premise.  It is automatic for every signature
admitted by the canonical compiler. -/
structure PositiveArity (S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature) : Prop where
  positive : forall C, 0 < S.arity C

/-- Regard a positive-arity semantics signature as a canonical compiler
signature. -/
def toSignature (S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature) (h : PositiveArity S) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Signature where
  Symbol := S.Symbol
  arity := S.arity
  arity_pos := h.positive

/-- The matrix adapter changes names only: length becomes columns and cell
becomes entry. -/
def toMatrix {rows : Nat} (M : Dregg2.Metatheory.GabbayMatrixSemantics.IntMatrix rows) : Dregg2.Metatheory.GabbayMatrixCompiler.Matrix rows where
  cols := M.length
  cols_pos := M.length_pos
  entry := M.cell

/-- Pointwise valuation adapter. -/
def toValuation {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) : Dregg2.Metatheory.GabbayMatrixCompiler.Valuation (toSignature S h) where
  matrix C := toMatrix (rho C)

@[simp] theorem toMatrix_cols {rows : Nat} (M : Dregg2.Metatheory.GabbayMatrixSemantics.IntMatrix rows) :
    (toMatrix M).cols = M.length := rfl

@[simp] theorem toMatrix_entry {rows : Nat} (M : Dregg2.Metatheory.GabbayMatrixSemantics.IntMatrix rows)
    (row : Fin rows) (j : Fin M.length) :
    (toMatrix M).entry row j = M.cell row j := rfl

/-- The one-based interpolation nodes are definitionally the same data. -/
@[simp] theorem columnNode_eq_node {rows : Nat} (M : Dregg2.Metatheory.GabbayMatrixSemantics.IntMatrix rows)
    (j : Fin M.length) :
    Dregg2.Metatheory.GabbayMatrixCompiler.columnNode j = M.node j := rfl

/-- **Row-interpolation coherence.**  The two presentations construct the
same Lagrange polynomial, not merely extensionally equal node values. -/
theorem rowPolynomial_agrees {rows : Nat} (M : Dregg2.Metatheory.GabbayMatrixSemantics.IntMatrix rows)
    (row : Fin rows) :
    Dregg2.Metatheory.GabbayMatrixCompiler.rowPolynomial (toMatrix M) row = M.rowPolynomial row := rfl

/-! ## Syntax adapters and denotational coherence -/

def toTerm {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S) :
    Dregg2.Metatheory.GabbayMatrixSemantics.Term S -> Dregg2.Metatheory.GabbayMatrixCompiler.Term (toSignature S h)
  | .index => .index
  | .rational q => .rat q
  | .add a b => .add (toTerm h a) (toTerm h b)
  | .sub a b => .sub (toTerm h a) (toTerm h b)
  | .mul a b => .mul (toTerm h a) (toTerm h b)
  | .lookup C row arg => .lookup C row (toTerm h arg)
  | .length C => .length C

/-- Term-polynomial compilation commutes with the adapter. -/
theorem termPolynomial_agrees {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (term : Dregg2.Metatheory.GabbayMatrixSemantics.Term S) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Term.polynomial (toValuation h rho) (toTerm h term) =
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteTerm rho term := by
  induction term with
  | index => rfl
  | rational q => rfl
  | add a b iha ihb => simp [toTerm, Dregg2.Metatheory.GabbayMatrixCompiler.Term.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteTerm, iha, ihb]
  | sub a b iha ihb => simp [toTerm, Dregg2.Metatheory.GabbayMatrixCompiler.Term.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteTerm, iha, ihb]
  | mul a b iha ihb => simp [toTerm, Dregg2.Metatheory.GabbayMatrixCompiler.Term.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteTerm, iha, ihb]
  | lookup C row arg ih =>
      change ((rho C).rowPolynomial row).comp
          (Dregg2.Metatheory.GabbayMatrixCompiler.Term.polynomial
            (toValuation h rho) (toTerm h arg)) =
        ((rho C).rowPolynomial row).comp
          (Dregg2.Metatheory.GabbayMatrixSemantics.denoteTerm rho arg)
      rw [ih]
  | length C => rfl

/-- Numerical term semantics is the same on every rational input, including
off-domain inputs where both views evaluate the same interpolating polynomial. -/
theorem termValue_agrees {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (x : Rat) (term : Dregg2.Metatheory.GabbayMatrixSemantics.Term S) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Term.denote (toValuation h rho) x (toTerm h term) =
      Dregg2.Metatheory.GabbayMatrixSemantics.evalTerm rho x term := by
  rw [← Dregg2.Metatheory.GabbayMatrixCompiler.Term.eval_polynomial]
  exact congrArg (fun p : Polynomial Rat => p.eval x)
    (termPolynomial_agrees h rho term)

def toFormula {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S) :
    Dregg2.Metatheory.GabbayMatrixSemantics.Formula S -> Dregg2.Metatheory.GabbayMatrixCompiler.Formula (toSignature S h)
  | .top => .top
  | .bottom => .bottom
  | .eq a b => .equal (toTerm h a) (toTerm h b)
  | .and p q => .and (toFormula h p) (toFormula h q)
  | .or p q => .or (toFormula h p) (toFormula h q)
  | .forallIn C body => .forallIn C (toFormula h body)
  | .existsIn C body => .existsIn C (toFormula h body)

/-- Formula-polynomial compilation commutes with the adapter. -/
theorem formulaPolynomial_agrees {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature}
    (h : PositiveArity S) (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S)
    (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial (toValuation h rho) (toFormula h formula) =
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula rho formula := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | eq a b => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula, termPolynomial_agrees]
  | and p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula, ihp, ihq]
  | or p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial,
      Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula, ihp, ihq]
  | forallIn C body ih =>
      change Polynomial.C (∑ j : Fin (rho C).length,
          (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial
            (toValuation h rho) (toFormula h body)).eval ((rho C).node j)) =
        Polynomial.C (∑ j : Fin (rho C).length,
          (Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula rho body).eval
            ((rho C).node j))
      rw [ih]
  | existsIn C body ih =>
      change Polynomial.C (∏ j : Fin (rho C).length,
          (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial
            (toValuation h rho) (toFormula h body)).eval ((rho C).node j)) =
        Polynomial.C (∏ j : Fin (rho C).length,
          (Dregg2.Metatheory.GabbayMatrixSemantics.denoteFormula rho body).eval
            ((rho C).node j))
      rw [ih]

/-- **Source-semantics coherence.**  Ordinary satisfaction is preserved and
reflected structurally, without appealing to zero-valued acceptance. -/
theorem satisfies_iff {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) (x : Rat) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt (toValuation h rho) x (toFormula h formula) <->
      Dregg2.Metatheory.GabbayMatrixSemantics.Holds rho x formula := by
  induction formula generalizing x with
  | top => rfl
  | bottom => rfl
  | eq a b => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt, Dregg2.Metatheory.GabbayMatrixSemantics.Holds,
      termValue_agrees]
  | and p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt,
      Dregg2.Metatheory.GabbayMatrixSemantics.Holds, ihp, ihq]
  | or p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt,
      Dregg2.Metatheory.GabbayMatrixSemantics.Holds, ihp, ihq]
  | forallIn C body ih =>
      change (forall j : Fin (rho C).length,
          Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt
            (toValuation h rho) ((rho C).node j) (toFormula h body)) <->
        forall j : Fin (rho C).length,
          Dregg2.Metatheory.GabbayMatrixSemantics.Holds rho ((rho C).node j) body
      exact forall_congr' (fun j => ih ((rho C).node j))
  | existsIn C body ih =>
      change (exists j : Fin (rho C).length,
          Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt
            (toValuation h rho) ((rho C).node j) (toFormula h body)) <->
        exists j : Fin (rho C).length,
          Dregg2.Metatheory.GabbayMatrixSemantics.Holds rho ((rho C).node j) body
      exact exists_congr (fun j => ih ((rho C).node j))

/-- Residual evaluation is literally the same rational value. -/
theorem residual_agrees {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) (x : Rat) :
    (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial (toValuation h rho)
      (toFormula h formula)).eval x = Dregg2.Metatheory.GabbayMatrixSemantics.residual rho x formula := by
  rw [formulaPolynomial_agrees]
  rfl

/-- Consequently, the residual-zero judgements agree in both directions. -/
theorem residual_zero_iff {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) (x : Rat) :
    (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial (toValuation h rho)
      (toFormula h formula)).eval x = 0 <->
      Dregg2.Metatheory.GabbayMatrixSemantics.residual rho x formula = 0 := by
  rw [residual_agrees]

/-- The compiler theorem and the semantics theorem are the same theorem through
the adapter. -/
theorem compiler_correct_iff_semantics_correct {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature}
    (h : PositiveArity S) (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S)
    (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) (x : Rat) :
    ((Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial (toValuation h rho)
      (toFormula h formula)).eval x = 0 <->
        Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt (toValuation h rho) x (toFormula h formula)) <->
      (Dregg2.Metatheory.GabbayMatrixSemantics.residual rho x formula = 0 <-> Dregg2.Metatheory.GabbayMatrixSemantics.Holds rho x formula) := by
  rw [residual_agrees, satisfies_iff]

/-! ## Exact cost and certificate transport -/

/-- The semantics-side view of the canonical cost recurrence.  Defining it on
the older syntax makes cost agreement a theorem rather than an assertion that
the two implementations happen to look similar. -/
def viewCost {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) :
    Dregg2.Metatheory.GabbayMatrixSemantics.Formula S -> Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost
  | .top | .bottom => {}
  | .eq _ _ => { atoms := 1 }
  | .and p q => viewCost rho p + viewCost rho q + { adds := 1 }
  | .or p q => viewCost rho p + viewCost rho q + { muls := 1 }
  | .forallIn C body =>
      Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale (rho C).length (viewCost rho body) +
        { adds := (rho C).length - 1 }
  | .existsIn C body =>
      Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale (rho C).length (viewCost rho body) +
        { muls := (rho C).length - 1 }

/-- Exact atoms/additions/multiplications agree after translation. -/
theorem cost_agrees {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature} (h : PositiveArity S)
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost (toValuation h rho) (toFormula h formula) =
      viewCost rho formula := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | eq a b => rfl
  | and p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost, viewCost, ihp, ihq]
  | or p q ihp ihq => simp [toFormula, Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost, viewCost, ihp, ihq]
  | forallIn C body ih =>
      change Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale
          (rho C).length
          (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost
            (toValuation h rho) (toFormula h body)) +
            { adds := (rho C).length - 1 } =
        Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale
          (rho C).length (viewCost rho body) +
            { adds := (rho C).length - 1 }
      rw [ih]
  | existsIn C body ih =>
      change Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale
          (rho C).length
          (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost
            (toValuation h rho) (toFormula h body)) +
            { muls := (rho C).length - 1 } =
        Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost.scale
          (rho C).length (viewCost rho body) +
            { muls := (rho C).length - 1 }
      rw [ih]

/-- A certificate stated entirely over the semantics view.  Its transport below
produces the canonical compiler certificate without recomputing or trusting any
bound. -/
structure ViewCertificate {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature}
    (rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S) (formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S)
    (x : Rat) (p : Nat) where
  maxColumns : Nat
  maxEntryAbs : Nat
  columnsBound : forall C, (rho C).length <= maxColumns
  entriesBound : forall C (row : Fin (S.arity C)) (j : Fin (rho C).length),
    ((rho C).cell row j).natAbs <= maxEntryAbs
  expansionCost : Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost
  expansionCost_exact : expansionCost = viewCost rho formula
  numeratorBound : (Dregg2.Metatheory.GabbayMatrixSemantics.residual rho x formula).num.natAbs < p
  denominatorBound : (Dregg2.Metatheory.GabbayMatrixSemantics.residual rho x formula).den < p

/-- Certificate transport is lossless: matrix bounds, exact cost, and both
rational projection bounds become the canonical certificate fields. -/
def ViewCertificate.toCompiler {S : Dregg2.Metatheory.GabbayMatrixSemantics.MatrixSignature}
    (h : PositiveArity S) {rho : Dregg2.Metatheory.GabbayMatrixSemantics.Valuation S}
    {formula : Dregg2.Metatheory.GabbayMatrixSemantics.Formula S} {x : Rat} {p : Nat}
    (certificate : ViewCertificate rho formula x p) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.CompilerCertificate (toValuation h rho)
      (toFormula h formula) x p where
  maxColumns := certificate.maxColumns
  maxEntryAbs := certificate.maxEntryAbs
  columnsBound := by
    intro C
    exact certificate.columnsBound C
  entriesBound := by
    intro C row j
    exact certificate.entriesBound C row j
  expansionCost := certificate.expansionCost
  expansionCost_exact := certificate.expansionCost_exact.trans
    (cost_agrees h rho formula).symm
  numeratorBound := by
    rw [residual_agrees]
    exact certificate.numeratorBound
  denominatorBound := by
    rw [residual_agrees]
    exact certificate.denominatorBound

/-! ## The successor/Skolem specimen through the bridge -/

def skolemPositive : PositiveArity Dregg2.Metatheory.GabbayMatrixSemantics.skolemSignature where
  positive := by intro C; cases C; decide

def successorCompilerValuation :
    Dregg2.Metatheory.GabbayMatrixCompiler.Valuation (toSignature Dregg2.Metatheory.GabbayMatrixSemantics.skolemSignature skolemPositive) :=
  toValuation skolemPositive Dregg2.Metatheory.GabbayMatrixSemantics.successorValuation

def successorCompilerFormula :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula (toSignature Dregg2.Metatheory.GabbayMatrixSemantics.skolemSignature skolemPositive) :=
  toFormula skolemPositive Dregg2.Metatheory.GabbayMatrixSemantics.successorSkolemFormula

/-- Both exact degree-one row-polynomial specimens survive the adapter. -/
theorem successor_row_polynomials_bridge :
    Dregg2.Metatheory.GabbayMatrixCompiler.rowPolynomial
        (successorCompilerValuation.matrix .table) Dregg2.Metatheory.GabbayMatrixSemantics.inputRow =
        Polynomial.X - Polynomial.C 1 /\
      Dregg2.Metatheory.GabbayMatrixCompiler.rowPolynomial
        (successorCompilerValuation.matrix .table) Dregg2.Metatheory.GabbayMatrixSemantics.outputRow =
        Polynomial.X := by
  constructor
  · exact Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_inputPolynomial
  · exact Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_outputPolynomial

/-- The ordinary source theorem transports to the canonical front end. -/
theorem successor_holds_through_bridge (x : Rat) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.SatisfiesAt successorCompilerValuation x
      successorCompilerFormula := by
  exact (satisfies_iff skolemPositive Dregg2.Metatheory.GabbayMatrixSemantics.successorValuation
    Dregg2.Metatheory.GabbayMatrixSemantics.successorSkolemFormula x).2 (Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_holds x)

/-- The translated compiler residual is exactly zero. -/
theorem successor_residual_zero_through_bridge (x : Rat) :
    (Dregg2.Metatheory.GabbayMatrixCompiler.Formula.polynomial successorCompilerValuation
      successorCompilerFormula).eval x = 0 := by
  exact (residual_zero_iff skolemPositive Dregg2.Metatheory.GabbayMatrixSemantics.successorValuation
    Dregg2.Metatheory.GabbayMatrixSemantics.successorSkolemFormula x).2
      (Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_compiles_to_zero x)

/-- Three equality atoms and two additions is the exact exhaustive-universal
cost for the three-column Skolem table. -/
theorem successor_cost_through_bridge :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.cost successorCompilerValuation successorCompilerFormula =
      { atoms := 3, adds := 2 : Dregg2.Metatheory.GabbayMatrixCompiler.Formula.Cost } := by
  decide

/-- The canonical row-function view really is the successor Skolem function. -/
theorem successor_skolem_through_bridge :
    forall j : Fin (successorCompilerValuation.matrix .table).cols,
      exists y : Rat,
        y = ((successorCompilerValuation.matrix .table).entry
          Dregg2.Metatheory.GabbayMatrixSemantics.inputRow j : Rat) + 1 := by
  apply Dregg2.Metatheory.GabbayMatrixCompiler.Formula.rowFunction_skolem successorCompilerValuation .table
    Dregg2.Metatheory.GabbayMatrixSemantics.outputRow
  intro j
  change (((if (Dregg2.Metatheory.GabbayMatrixSemantics.outputRow : Fin 2).1 = 0 then (j.1 : Int)
      else ((j.1 + 1 : Nat) : Int)) : Int) : Rat) =
    (((if (Dregg2.Metatheory.GabbayMatrixSemantics.inputRow : Fin 2).1 = 0 then (j.1 : Int)
      else ((j.1 + 1 : Nat) : Int)) : Int) : Rat) + 1
  norm_num [Dregg2.Metatheory.GabbayMatrixSemantics.outputRow, Dregg2.Metatheory.GabbayMatrixSemantics.inputRow]

/-- A full semantics-view bound certificate for the specimen. -/
def successorViewCertificate (x : Rat) :
    ViewCertificate Dregg2.Metatheory.GabbayMatrixSemantics.successorValuation
      Dregg2.Metatheory.GabbayMatrixSemantics.successorSkolemFormula x 17 where
  maxColumns := 3
  maxEntryAbs := 3
  columnsBound := by
    intro C
    cases C
    rfl
  entriesBound := by
    intro C row j
    cases C
    change (if row.1 = 0 then (j.1 : Int) else ((j.1 + 1 : Nat) : Int)).natAbs <= 3
    fin_cases row <;> fin_cases j <;> norm_num
  expansionCost := { atoms := 3, adds := 2 }
  expansionCost_exact := by decide
  numeratorBound := by
    rw [Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_compiles_to_zero]
    norm_num
  denominatorBound := by
    rw [Dregg2.Metatheory.GabbayMatrixSemantics.successorTable_compiles_to_zero]
    norm_num

local instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The transported certificate discharges the canonical p=17 projection
theorem with no duplicated bound proof. -/
theorem successor_projected_through_bridge (x : Rat) :
    Dregg2.Metatheory.GabbayMatrixCompiler.Formula.projectedResidual (p := 17) successorCompilerValuation
      successorCompilerFormula x = 0 := by
  exact (((successorViewCertificate x).toCompiler skolemPositive).projected_exact).2
    (successor_holds_through_bridge x)

#assert_all_clean [toMatrix_cols, toMatrix_entry, columnNode_eq_node,
  rowPolynomial_agrees, termPolynomial_agrees, termValue_agrees,
  formulaPolynomial_agrees, satisfies_iff, residual_agrees, residual_zero_iff,
  compiler_correct_iff_semantics_correct, cost_agrees,
  successor_row_polynomials_bridge, successor_holds_through_bridge,
  successor_residual_zero_through_bridge, successor_cost_through_bridge,
  successor_skolem_through_bridge, successor_projected_through_bridge]

end


end Dregg2.Metatheory.GabbayMatrixBridge
