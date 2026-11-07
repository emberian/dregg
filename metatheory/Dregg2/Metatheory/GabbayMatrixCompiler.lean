/-
# A verified matrix-language front end for direct FOL arithmetization

This module formalizes the constructive core of Gabbay's matrix presentation,
rather than only its connective algebra.  A source valuation assigns each
matrix symbol a nonempty integer matrix with a statically fixed row arity and a
runtime finite column count.  The source language contains the distinguished
index variable, rational constants, arithmetic, interpolated row lookup
`C_i(t)`, matrix length, equality, positive connectives, and quantifiers over
the complete declared column domain of a matrix.

The compilation is syntax directed:

* every row is represented by its explicit Lagrange interpolating polynomial;
* terms compile by polynomial arithmetic and polynomial composition;
* equality compiles to a square, conjunction/universal quantification to sums,
  and disjunction/existential quantification to products;
* evaluation of the resulting rational polynomial is zero exactly when the
  independent source semantics holds;
* deterministic numerator/denominator bounds certify a sound projection into
  a prime field; and
* a separate Boolean false-bit compiler gives an exact finite-field repair
  without any positivity or no-cancellation premise in the target field.

The scope is deliberately precise.  This is the positive, one-index,
matrix-variable fragment of the paper.  It supports constant row-range checks,
but not `term(phi)`, general recursion, arbitrary variable-free range bounds,
or a proof that one polynomial representation is cryptographically succinct.
The compiler certificate exposes source expansion cost, matrix bounds, and the
complete rational-to-field projection obligations.  It is a mathematical
front end; descriptor emission and a runtime decoder are separate refinement
layers.
-/
import Dregg2.Metatheory.IntegerProjectionSoundness
import Mathlib.LinearAlgebra.Lagrange

namespace Dregg2.Metatheory.GabbayMatrixCompiler

open scoped BigOperators
open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.IntegerProjectionSoundness

noncomputable section

universe u

/-! ## Matrix signatures and valuations -/

/-- A collection of matrix-variable symbols with a fixed positive row arity. -/
structure Signature where
  Symbol : Type u
  arity : Symbol -> Nat
  arity_pos : forall C, 0 < arity C

/-- A nonempty finite integer matrix.  Rows are fixed by the signature; the
column count is part of the valued matrix. -/
structure Matrix (rows : Nat) where
  cols : Nat
  cols_pos : 0 < cols
  entry : Fin rows -> Fin cols -> Int

/-- A valuation assigns a concrete matrix of the declared row arity to every
matrix-variable symbol. -/
structure Valuation (S : Signature) where
  matrix : (C : S.Symbol) -> Matrix (S.arity C)

variable {S : Signature}

local instance classicalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Column `j` is represented by the paper's one-based rational node `j+1`. -/
def columnNode {n : Nat} (j : Fin n) : Rat := (j.val + 1 : Nat)

theorem columnNode_injective {n : Nat} : Function.Injective (@columnNode n) := by
  intro i j h
  apply Fin.ext
  change (((i.val + 1 : Nat) : Rat)) = ((j.val + 1 : Nat) : Rat) at h
  have h' : i.val + 1 = j.val + 1 := Rat.natCast_injective h
  omega

/-- The explicit Lagrange interpolant of one matrix row. -/
def rowPolynomial {rows : Nat} (M : Matrix rows) (row : Fin rows) : Polynomial Rat :=
  Lagrange.interpolate Finset.univ columnNode
    (fun j : Fin M.cols => (M.entry row j : Rat))

/-- The row interpolant recovers every declared matrix entry. -/
@[simp] theorem eval_rowPolynomial_column {rows : Nat} (M : Matrix rows)
    (row : Fin rows) (j : Fin M.cols) :
    (rowPolynomial M row).eval (columnNode j) = (M.entry row j : Rat) := by
  exact Lagrange.eval_interpolate_at_node
    (fun k : Fin M.cols => (M.entry row k : Rat))
    (columnNode_injective.injOn) (Finset.mem_univ j)

/-- A row of length `n` has an interpolant of degree strictly below `n`.
This is the exact interpolation-degree fact; it is not a prover-cost claim. -/
theorem degree_rowPolynomial_lt_cols {rows : Nat} (M : Matrix rows)
    (row : Fin rows) :
    (rowPolynomial M row).degree < M.cols := by
  have h := Lagrange.degree_interpolate_lt
    (s := Finset.univ) (v := @columnNode M.cols)
    (fun k : Fin M.cols => (M.entry row k : Rat)) columnNode_injective.injOn
  simpa [rowPolynomial] using h

/-- A matrix quantifier has exactly its declared number of instantiations. -/
@[simp] theorem card_columnDomain {rows : Nat} (M : Matrix rows) :
    Fintype.card (Fin M.cols) = M.cols := by
  simp

/-! ## The one-index matrix language -/

/-- Gabbay-shaped terms.  Lookup composes the interpolating polynomial for a
row with the polynomial denoted by its argument. -/
inductive Term (S : Signature) where
  | index : Term S
  | rat : Rat -> Term S
  | add : Term S -> Term S -> Term S
  | sub : Term S -> Term S -> Term S
  | mul : Term S -> Term S -> Term S
  | lookup (C : S.Symbol) (row : Fin (S.arity C)) : Term S -> Term S
  | length (C : S.Symbol) : Term S

/-- The positive matrix-FOL fragment.  `rowLt` and `ltRow` are the executable
constant-bound specialization of the paper's variable-free row range checks. -/
inductive Formula (S : Signature) where
  | top : Formula S
  | bottom : Formula S
  | equal : Term S -> Term S -> Formula S
  | and : Formula S -> Formula S -> Formula S
  | or : Formula S -> Formula S -> Formula S
  | forallIn (C : S.Symbol) : Formula S -> Formula S
  | existsIn (C : S.Symbol) : Formula S -> Formula S
  | rowLt (C : S.Symbol) (row : Fin (S.arity C)) (bound : Rat) : Formula S
  | ltRow (bound : Rat) (C : S.Symbol) (row : Fin (S.arity C)) : Formula S

namespace Term

/-- Independent term semantics.  Matrix application evaluates the actual row
interpolant, so out-of-domain lookup remains total exactly as polynomial
composition is total. -/
def denote (V : Valuation S) (x : Rat) : Term S -> Rat
  | .index => x
  | .rat q => q
  | .add left right => denote V x left + denote V x right
  | .sub left right => denote V x left - denote V x right
  | .mul left right => denote V x left * denote V x right
  | .lookup C row arg =>
      (rowPolynomial (V.matrix C) row).eval (denote V x arg)
  | .length C => V.matrix C |>.cols

/-- Syntax-directed compilation of a term to a univariate rational polynomial. -/
def polynomial (V : Valuation S) : Term S -> Polynomial Rat
  | .index => Polynomial.X
  | .rat q => Polynomial.C q
  | .add left right => polynomial V left + polynomial V right
  | .sub left right => polynomial V left - polynomial V right
  | .mul left right => polynomial V left * polynomial V right
  | .lookup C row arg => (rowPolynomial (V.matrix C) row).comp (polynomial V arg)
  | .length C => Polynomial.C (V.matrix C |>.cols)

/-- Term compilation is exact at every rational index, not only at matrix
columns. -/
@[simp] theorem eval_polynomial (V : Valuation S) (x : Rat) (term : Term S) :
    (polynomial V term).eval x = denote V x term := by
  induction term with
  | index => simp [polynomial, denote]
  | rat q => simp [polynomial, denote]
  | add left right ihl ihr => simp [polynomial, denote, ihl, ihr]
  | sub left right ihl ihr => simp [polynomial, denote, ihl, ihr]
  | mul left right ihl ihr => simp [polynomial, denote, ihl, ihr]
  | lookup C row arg ih => simp [polynomial, denote, Polynomial.eval_comp, ih]
  | length C => simp [polynomial, denote]

/-- At a declared column, direct lookup of the distinguished index is exactly
the stored matrix entry. -/
@[simp] theorem denote_lookup_index_column (V : Valuation S) (C : S.Symbol)
    (row : Fin (S.arity C)) (j : Fin (V.matrix C).cols) :
    denote V (columnNode j) (.lookup C row .index) =
      ((V.matrix C).entry row j : Rat) := by
  simp [denote]

end Term

namespace Formula

/-- Ordinary source truth, defined before and independently of the compiled
formula polynomial.  Quantifiers enumerate the complete column domain declared
by their matrix symbol. -/
def SatisfiesAt (V : Valuation S) (x : Rat) : Formula S -> Prop
  | .top => True
  | .bottom => False
  | .equal left right => left.denote V x = right.denote V x
  | .and p q => SatisfiesAt V x p /\ SatisfiesAt V x q
  | .or p q => SatisfiesAt V x p \/ SatisfiesAt V x q
  | .forallIn C p => forall j : Fin (V.matrix C).cols,
      SatisfiesAt V (columnNode j) p
  | .existsIn C p => exists j : Fin (V.matrix C).cols,
      SatisfiesAt V (columnNode j) p
  | .rowLt C row bound => forall j : Fin (V.matrix C).cols,
      ((V.matrix C).entry row j : Rat) < bound
  | .ltRow bound C row => forall j : Fin (V.matrix C).cols,
      bound < ((V.matrix C).entry row j : Rat)

/-- The direct rational-polynomial compiler.  A quantifier closes over the
distinguished index by evaluating the body at every one-based column node. -/
def polynomial (V : Valuation S) : Formula S -> Polynomial Rat
  | .top => 0
  | .bottom => 1
  | .equal left right => (left.polynomial V - right.polynomial V) ^ 2
  | .and p q => polynomial V p + polynomial V q
  | .or p q => polynomial V p * polynomial V q
  | .forallIn C p => Polynomial.C
      (∑ j : Fin (V.matrix C).cols, (polynomial V p).eval (columnNode j))
  | .existsIn C p => Polynomial.C
      (∏ j : Fin (V.matrix C).cols, (polynomial V p).eval (columnNode j))
  | .rowLt C row bound => Polynomial.C
      (if forall j : Fin (V.matrix C).cols,
          ((V.matrix C).entry row j : Rat) < bound then 0 else 1)
  | .ltRow bound C row => Polynomial.C
      (if forall j : Fin (V.matrix C).cols,
          bound < ((V.matrix C).entry row j : Rat) then 0 else 1)

/-- Every compiled predicate residual is nonnegative at every rational point.
This is the load-bearing invariant behind addition-as-conjunction. -/
theorem eval_polynomial_nonneg (V : Valuation S) (formula : Formula S) (x : Rat) :
    0 <= (polynomial V formula).eval x := by
  induction formula generalizing x with
  | top => simp [polynomial]
  | bottom => simp [polynomial]
  | equal left right => simp [polynomial, sq_nonneg]
  | and p q ihp ihq =>
      simp only [polynomial, Polynomial.eval_add]
      exact add_nonneg (ihp x) (ihq x)
  | or p q ihp ihq =>
      simp only [polynomial, Polynomial.eval_mul]
      exact mul_nonneg (ihp x) (ihq x)
  | forallIn C p ih =>
      simp only [polynomial, Polynomial.eval_C]
      exact Finset.sum_nonneg (fun _ _ => ih _)
  | existsIn C p ih =>
      simp only [polynomial, Polynomial.eval_C]
      exact Finset.prod_nonneg (fun _ _ => ih _)
  | rowLt C row bound =>
      simp only [polynomial, Polynomial.eval_C]
      split <;> norm_num
  | ltRow bound C row =>
      simp only [polynomial, Polynomial.eval_C]
      split <;> norm_num

/-- **Matrix-FOL compiler theorem.**  The direct rational polynomial evaluates
to zero exactly when the independent source semantics is true. -/
theorem eval_polynomial_eq_zero_iff (V : Valuation S) (formula : Formula S)
    (x : Rat) :
    (polynomial V formula).eval x = 0 <-> SatisfiesAt V x formula := by
  induction formula generalizing x with
  | top => simp [polynomial, SatisfiesAt]
  | bottom => simp [polynomial, SatisfiesAt]
  | equal left right =>
      simp only [polynomial, Polynomial.eval_pow, Polynomial.eval_sub,
        Term.eval_polynomial, SatisfiesAt, sq_eq_zero_iff]
      exact sub_eq_zero
  | and p q ihp ihq =>
      simp only [polynomial, Polynomial.eval_add, SatisfiesAt]
      rw [add_eq_zero_iff_of_nonneg (eval_polynomial_nonneg V p x)
        (eval_polynomial_nonneg V q x), ihp x, ihq x]
  | or p q ihp ihq =>
      simp only [polynomial, Polynomial.eval_mul, SatisfiesAt]
      rw [mul_eq_zero, ihp x, ihq x]
  | forallIn C p ih =>
      simp only [polynomial, Polynomial.eval_C, SatisfiesAt]
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun j =>
        eval_polynomial_nonneg V p (columnNode j))]
      constructor
      · intro h j
        exact (ih (columnNode j)).mp (congrFun h j)
      · intro h
        funext j
        exact (ih (columnNode j)).mpr (h j)
  | existsIn C p ih =>
      simp only [polynomial, Polynomial.eval_C, SatisfiesAt]
      simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
      exact exists_congr (fun j => ih (columnNode j))
  | rowLt C row bound =>
      simp only [polynomial, Polynomial.eval_C, SatisfiesAt]
      by_cases h : forall j : Fin (V.matrix C).cols,
          ((V.matrix C).entry row j : Rat) < bound <;> simp [h]
  | ltRow bound C row =>
      simp only [polynomial, Polynomial.eval_C, SatisfiesAt]
      by_cases h : forall j : Fin (V.matrix C).cols,
          bound < ((V.matrix C).entry row j : Rat) <;> simp [h]

/-! ## Exact finite-field repairs -/

/-- Project the complete rational residual to a prime field. -/
def projectedResidual {p : Nat} [Fact p.Prime] (V : Valuation S)
    (formula : Formula S) (x : Rat) : ZMod p :=
  rationalProjection ((polynomial V formula).eval x)

/-- **Certified no-wrap projection theorem.**  The two explicit bounds are the
complete deterministic obstruction to carrying this rational zero claim into
the chosen prime field. -/
theorem projectedResidual_eq_zero_iff {p : Nat} [Fact p.Prime]
    (V : Valuation S) (formula : Formula S) (x : Rat)
    (hnum : ((polynomial V formula).eval x).num.natAbs < p)
    (hden : ((polynomial V formula).eval x).den < p) :
    projectedResidual (p := p) V formula x = 0 <->
      SatisfiesAt V x formula := by
  rw [projectedResidual, rationalProjection_eq_zero_iff_of_bounds hnum hden,
    eval_polynomial_eq_zero_iff]

/-- Exact Boolean false-bit compilation over any field.  This structurally
repairs conjunction and quantifiers instead of casting rational sums into the
field. -/
def falseBit {F : Type*} [Field F] (V : Valuation S) (x : Rat) : Formula S -> F
  | .top => 0
  | .bottom => 1
  | .equal left right => if left.denote V x = right.denote V x then 0 else 1
  | .and p q => falseAnd (falseBit (F := F) V x p) (falseBit (F := F) V x q)
  | .or p q => falseOr (falseBit (F := F) V x p) (falseBit (F := F) V x q)
  | .forallIn C p =>
      if forall j : Fin (V.matrix C).cols,
          falseBit (F := F) V (columnNode j) p = 0 then 0 else 1
  | .existsIn C p =>
      if exists j : Fin (V.matrix C).cols,
          falseBit (F := F) V (columnNode j) p = 0 then 0 else 1
  | .rowLt C row bound =>
      if forall j : Fin (V.matrix C).cols,
          ((V.matrix C).entry row j : Rat) < bound then 0 else 1
  | .ltRow bound C row =>
      if forall j : Fin (V.matrix C).cols,
          bound < ((V.matrix C).entry row j : Rat) then 0 else 1

/-- The Boolean repair always returns a bit and is exact for the full matrix
formula, including both bounded quantifiers. -/
theorem falseBit_isBit_and_correct {F : Type*} [Field F]
    (V : Valuation S) (formula : Formula S) (x : Rat) :
    IsBit (falseBit (F := F) V x formula) /\
      (falseBit (F := F) V x formula = 0 <-> SatisfiesAt V x formula) := by
  induction formula generalizing x with
  | top => simp [falseBit, SatisfiesAt, IsBit]
  | bottom => simp [falseBit, SatisfiesAt, IsBit]
  | equal left right =>
      by_cases h : left.denote V x = right.denote V x <;>
        simp [falseBit, SatisfiesAt, IsBit, h]
  | and p q ihp ihq =>
      have hp := ihp x
      have hq := ihq x
      refine ⟨falseAnd_is_bit hp.1 hq.1, ?_⟩
      rw [falseBit, SatisfiesAt, falseAnd_eq_zero_iff hp.1 hq.1, hp.2, hq.2]
  | or p q ihp ihq =>
      have hp := ihp x
      have hq := ihq x
      refine ⟨falseOr_is_bit hp.1 hq.1, ?_⟩
      rw [falseBit, SatisfiesAt, falseOr_eq_zero_iff hp.1 hq.1, hp.2, hq.2]
  | forallIn C p ih =>
      by_cases h : forall j : Fin (V.matrix C).cols,
          falseBit (F := F) V (columnNode j) p = 0
      · rw [falseBit, if_pos h]
        refine And.intro (Or.inl rfl) ?_
        simp only [SatisfiesAt, true_iff]
        intro j
        exact (ih (columnNode j)).2.mp (h j)
      · rw [falseBit, if_neg h]
        refine And.intro (Or.inr rfl) ?_
        simp only [one_ne_zero, false_iff, SatisfiesAt]
        intro hs
        apply h
        intro j
        exact (ih (columnNode j)).2.mpr (hs j)
  | existsIn C p ih =>
      by_cases h : exists j : Fin (V.matrix C).cols,
          falseBit (F := F) V (columnNode j) p = 0
      · rw [falseBit, if_pos h]
        refine And.intro (Or.inl rfl) ?_
        simp only [SatisfiesAt, true_iff]
        obtain ⟨j, hj⟩ := h
        exact ⟨j, (ih (columnNode j)).2.mp hj⟩
      · rw [falseBit, if_neg h]
        refine And.intro (Or.inr rfl) ?_
        simp only [one_ne_zero, false_iff, SatisfiesAt]
        rintro ⟨j, hj⟩
        exact h ⟨j, (ih (columnNode j)).2.mpr hj⟩
  | rowLt C row bound =>
      by_cases h : forall j : Fin (V.matrix C).cols,
          ((V.matrix C).entry row j : Rat) < bound <;>
        simp [falseBit, SatisfiesAt, IsBit, h]
  | ltRow bound C row =>
      by_cases h : forall j : Fin (V.matrix C).cols,
          bound < ((V.matrix C).entry row j : Rat) <;>
        simp [falseBit, SatisfiesAt, IsBit, h]

theorem falseBit_eq_zero_iff {F : Type*} [Field F]
    (V : Valuation S) (formula : Formula S) (x : Rat) :
    falseBit (F := F) V x formula = 0 <-> SatisfiesAt V x formula :=
  (falseBit_isBit_and_correct V formula x).2

/-! ## Expansion costs and proof-carrying compiler certificates -/

/-- Exact symbolic work of the direct residual compiler after bounded
quantifiers are unrolled.  `adds` and `muls` count residual-combining
operations; atom construction and term-polynomial composition remain separate
backend costs. -/
structure Cost where
  atoms : Nat := 0
  adds : Nat := 0
  muls : Nat := 0
  deriving DecidableEq, Repr

namespace Cost

def add (left right : Cost) : Cost where
  atoms := left.atoms + right.atoms
  adds := left.adds + right.adds
  muls := left.muls + right.muls

instance : Add Cost := ⟨add⟩

def scale (n : Nat) (cost : Cost) : Cost where
  atoms := n * cost.atoms
  adds := n * cost.adds
  muls := n * cost.muls

end Cost

/-- Exact unrolled residual cost.  An `n`-element nonempty sum/product uses
`n-1` combining operations. -/
def cost (V : Valuation S) : Formula S -> Cost
  | .top | .bottom => {}
  | .equal _ _ | .rowLt _ _ _ | .ltRow _ _ _ => { atoms := 1 }
  | .and p q => cost V p + cost V q + { adds := 1 }
  | .or p q => cost V p + cost V q + { muls := 1 }
  | .forallIn C p =>
      Cost.scale (V.matrix C).cols (cost V p) + { adds := (V.matrix C).cols - 1 }
  | .existsIn C p =>
      Cost.scale (V.matrix C).cols (cost V p) + { muls := (V.matrix C).cols - 1 }

@[simp] theorem cost_forall_atoms (V : Valuation S) (C : S.Symbol) (p : Formula S) :
    (cost V (.forallIn C p)).atoms = (V.matrix C).cols * (cost V p).atoms := by
  rfl

@[simp] theorem cost_forall_adds (V : Valuation S) (C : S.Symbol) (p : Formula S) :
    (cost V (.forallIn C p)).adds =
      (V.matrix C).cols * (cost V p).adds + ((V.matrix C).cols - 1) := by
  rfl

@[simp] theorem cost_exists_atoms (V : Valuation S) (C : S.Symbol) (p : Formula S) :
    (cost V (.existsIn C p)).atoms = (V.matrix C).cols * (cost V p).atoms := by
  rfl

@[simp] theorem cost_exists_muls (V : Valuation S) (C : S.Symbol) (p : Formula S) :
    (cost V (.existsIn C p)).muls =
      (V.matrix C).cols * (cost V p).muls + ((V.matrix C).cols - 1) := by
  rfl

/-- A proof-carrying certificate for the direct prime-field route.  It exposes
the finite-model bounds and exact source expansion cost, and it carries rather
than hides the final rational projection obligations. -/
structure CompilerCertificate (V : Valuation S) (formula : Formula S)
    (x : Rat) (p : Nat) where
  maxColumns : Nat
  maxEntryAbs : Nat
  columnsBound : forall C, (V.matrix C).cols <= maxColumns
  entriesBound : forall C (row : Fin (S.arity C)) (j : Fin (V.matrix C).cols),
    ((V.matrix C).entry row j).natAbs <= maxEntryAbs
  expansionCost : Cost
  expansionCost_exact : expansionCost = cost V formula
  numeratorBound : ((polynomial V formula).eval x).num.natAbs < p
  denominatorBound : ((polynomial V formula).eval x).den < p

/-- A checked certificate immediately discharges the no-wrap compiler theorem. -/
theorem CompilerCertificate.projected_exact {p : Nat} [Fact p.Prime]
    {V : Valuation S} {formula : Formula S} {x : Rat}
    (certificate : CompilerCertificate V formula x p) :
    projectedResidual (p := p) V formula x = 0 <->
      SatisfiesAt V x formula :=
  projectedResidual_eq_zero_iff V formula x certificate.numeratorBound
    certificate.denominatorBound

/-! ## Matrix rows as finite function and Skolem witnesses -/

/-- A selected output row is a finite Skolem function over the common column
domain.  This packages the witness shape used by matrix encodings of partial
functions. -/
def rowFunction (V : Valuation S) (C : S.Symbol) (output : Fin (S.arity C)) :
    Fin (V.matrix C).cols -> Rat :=
  fun j => ((V.matrix C).entry output j : Rat)

/-- Verifying a relation pointwise on a matrix output row produces an explicit
Skolem witness for every declared input column. -/
theorem rowFunction_skolem (V : Valuation S) (C : S.Symbol)
    (output : Fin (S.arity C)) (P : Fin (V.matrix C).cols -> Rat -> Prop)
    (h : forall j, P j (rowFunction V C output j)) :
    forall j, exists y, P j y := by
  intro j
  exact ⟨rowFunction V C output j, h j⟩

/-! ## Nontrivial two-row function example -/

inductive DemoSymbol where
  | neg
  deriving DecidableEq, Repr

def demoSignature : Signature where
  Symbol := DemoSymbol
  arity := fun | .neg => 2
  arity_pos := by intro C; cases C; decide

def demoMatrix : Matrix 2 where
  cols := 2
  cols_pos := by decide
  entry row col := if row.val = col.val then 0 else 1

def demoValuation : Valuation demoSignature where
  matrix := fun | .neg => demoMatrix

def demoInputRow : Fin (demoSignature.arity .neg) := ⟨0, by decide⟩
def demoOutputRow : Fin (demoSignature.arity .neg) := ⟨1, by decide⟩

theorem demoMatrix_rows_sum (j : Fin demoMatrix.cols) :
    (demoMatrix.entry ⟨0, by decide⟩ j : Rat) +
      (demoMatrix.entry ⟨1, by decide⟩ j : Rat) = 1 := by
  change
    ((if 0 = j.val then 0 else 1 : Int) : Rat) +
      ((if 1 = j.val then 0 else 1 : Int) : Rat) = 1
  fin_cases j <;> norm_num

/-- The matrix claims to implement Boolean negation: output plus input is one
at every declared column. -/
def demoNegationLaw : Formula demoSignature :=
  .forallIn .neg
    (.equal
      (.add (.lookup .neg demoInputRow .index)
        (.lookup .neg demoOutputRow .index))
      (.rat 1))

theorem demoNegationLaw_true (x : Rat) :
    Formula.SatisfiesAt demoValuation x demoNegationLaw := by
  simp only [demoNegationLaw, Formula.SatisfiesAt]
  intro j
  change
    Term.denote demoValuation (columnNode j)
        (.lookup .neg demoInputRow .index) +
      Term.denote demoValuation (columnNode j)
        (.lookup .neg demoOutputRow .index) = 1
  refine (congrArg₂ (· + ·)
    (Term.denote_lookup_index_column demoValuation DemoSymbol.neg demoInputRow j)
    (Term.denote_lookup_index_column demoValuation DemoSymbol.neg demoOutputRow j)).trans ?_
  exact demoMatrix_rows_sum j

/-- The direct unrolling has two equality atoms and one sum operation. -/
theorem demoNegationLaw_cost :
    cost demoValuation demoNegationLaw = { atoms := 2, adds := 1 : Cost } := by
  decide

/-- The Boolean repair accepts the same nontrivial matrix function over every
field. -/
theorem demoNegationLaw_boolean {F : Type*} [Field F] (x : Rat) :
    Formula.falseBit (F := F) demoValuation x demoNegationLaw = 0 := by
  exact (Formula.falseBit_eq_zero_iff demoValuation demoNegationLaw x).2
    (demoNegationLaw_true x)

/-- A concrete proof-carrying no-wrap certificate.  The example's complete
rational residual is zero, its denominator is one, both entries are bounded by
one, and the quantifier expands to the exact two-atom cost above. -/
def demoCertificate (x : Rat) :
    CompilerCertificate demoValuation demoNegationLaw x 17 where
  maxColumns := 2
  maxEntryAbs := 1
  columnsBound := by
    intro C
    cases C
    rfl
  entriesBound := by
    intro C row j
    cases C
    change (if row.val = j.val then 0 else 1 : Int).natAbs <= 1
    split <;> norm_num
  expansionCost := { atoms := 2, adds := 1 }
  expansionCost_exact := demoNegationLaw_cost.symm
  numeratorBound := by
    have hzero := (eval_polynomial_eq_zero_iff demoValuation demoNegationLaw x).2
      (demoNegationLaw_true x)
    rw [hzero]
    norm_num
  denominatorBound := by
    have hzero := (eval_polynomial_eq_zero_iff demoValuation demoNegationLaw x).2
      (demoNegationLaw_true x)
    rw [hzero]
    norm_num

local instance demoPrime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem demoNegationLaw_projected (x : Rat) :
    projectedResidual (p := 17) demoValuation demoNegationLaw x = 0 := by
  exact ((demoCertificate x).projected_exact).2 (demoNegationLaw_true x)

/-- The output row is an explicit finite Skolem witness for the relation
`input + output = 1`. -/
theorem demoNegationLaw_skolem :
    forall j : Fin demoMatrix.cols, exists y : Rat,
      (demoMatrix.entry ⟨0, by decide⟩ j : Rat) + y = 1 := by
  intro j
  refine ⟨(demoMatrix.entry ⟨1, by decide⟩ j : Rat), ?_⟩
  exact demoMatrix_rows_sum j

#assert_all_clean [columnNode_injective, eval_rowPolynomial_column,
  degree_rowPolynomial_lt_cols, card_columnDomain, Term.eval_polynomial,
  Term.denote_lookup_index_column, Formula.eval_polynomial_nonneg,
  Formula.eval_polynomial_eq_zero_iff, Formula.projectedResidual_eq_zero_iff,
  Formula.falseBit_isBit_and_correct, Formula.falseBit_eq_zero_iff,
  Formula.cost_forall_atoms, Formula.cost_forall_adds,
  Formula.cost_exists_atoms, Formula.cost_exists_muls,
  Formula.CompilerCertificate.projected_exact, Formula.rowFunction_skolem,
  Formula.demoMatrix_rows_sum, Formula.demoNegationLaw_true,
  Formula.demoNegationLaw_cost,
  Formula.demoNegationLaw_boolean, Formula.demoNegationLaw_projected,
  Formula.demoNegationLaw_skolem]

end Formula

end


end Dregg2.Metatheory.GabbayMatrixCompiler
