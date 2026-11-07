/-
# The polynomial frontier for cartesian-closed evaluation

Yoneda postcomposition by a *fixed* arrow is linear on one-hot coordinates.
That fact does not make the internal evaluator of a cartesian closed category
linear: evaluation consumes a variable function and a variable argument.  This
file isolates the difference.

For finite types `A` and `B`, the ordinary evaluator

    `(A → B) × A → B`

has an exact total-degree-two finite-field polynomial presentation.  The
construction is the evaluation tensor: select one function coordinate and one
argument coordinate, then route their product to the selected output.

The bound is sharp for every nondegenerate exponential.  Every total-degree-at-
most-one polynomial has zero mixed finite difference between its function and
argument blocks.  Evaluation has a nonzero mixed difference as soon as `A`
and `B` each contain two distinguishable elements.  Conversely, an affine
presentation exists exactly when `A` or `B` is subsingleton.  This obstruction
is structural, not cardinal: it already occurs for the two-element exponential
and over every field.

The conclusion is deliberately narrower than cryptographic soundness.  These
polynomials are exact on valid one-hot codes.  They do not enforce one-hotness,
commit inputs, provide a low-degree test, or make the exponentially large
function coordinate space succinct.  Intensional CCC presentations such as
the shared interaction nets in `IntensionalCCCCategory` can avoid materializing
that table, but their local-step receipts and cryptographic bindings are
separate constructions.

Standalone construction: no integration root is modified.  Pure; no axioms.
-/

import Dregg2.Metatheory.FamilyPolynomialYonedaFrontier
import Dregg2.Calculus.IntensionalCCCCategory

namespace Dregg2.Metatheory.CCCPolynomialEvaluationFrontier

open Dregg2.Metatheory.FinitePolynomialFunctions
open Dregg2.Metatheory.FinitePolynomialCategoryClassification

open scoped BigOperators

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} {F : Type w} [Field F]

/-! ## 1. Exact quadratic presentation of evaluation -/

/-- Pack the one-hot code of a function and the one-hot code of its argument
into disjoint variable blocks. -/
def evaluationInput (f : A → B) (a : A) : ((A → B) ⊕ A) → F :=
  pack (oneHot (F := F) f) (oneHot (F := F) a)

/-- Output coordinate `b` of extensional evaluation.

Each term has one function variable and one argument variable.  Thus this is
the tensor contraction for evaluation, rather than the linear matrix for
postcomposition by an already-fixed arrow. -/
def evaluationPolynomial [Fintype A] [Fintype B] [DecidableEq A] (b : B) :
    MvPolynomial ((A → B) ⊕ A) F :=
  ∑ f : A → B, ∑ a : A,
    MvPolynomial.C (oneHot (F := F) (f a) b) *
      MvPolynomial.X (Sum.inl f) * MvPolynomial.X (Sum.inr a)

/-- The evaluation tensor computes the one-hot code of `f a` exactly on every
valid pair of one-hot inputs. -/
@[simp] theorem eval_evaluationPolynomial [Fintype A] [Fintype B] [DecidableEq A]
    (f : A → B) (a : A) (b : B) :
    MvPolynomial.eval (evaluationInput (F := F) f a)
    (evaluationPolynomial (A := A) (B := B) (F := F) b) =
      oneHot (F := F) (f a) b := by
  classical
  simp only [evaluationPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    evaluationInput, pack, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_eq_single f]
  · rw [Finset.sum_eq_single a]
    · have hff : oneHot (F := F) f f = 1 := by
        simp only [oneHot, if_pos]
      have haa : oneHot (F := F) a a = 1 := by
        simp only [oneHot, if_pos]
      rw [hff, haa, mul_one, mul_one]
    · intro a' _ hne
      simp [oneHot, hne]
    · simp
  · intro f' _ hne
    simp [oneHot, hne]
  · simp

/-- The displayed evaluator is genuinely a degree-at-most-two polynomial as
syntax, not only a quadratic-looking semantic expression. -/
theorem evaluationPolynomial_totalDegree_le_two [Fintype A] [Fintype B]
    [DecidableEq A]
    (b : B) :
    (evaluationPolynomial (A := A) (B := B) (F := F) b).totalDegree ≤ 2 := by
  classical
  unfold evaluationPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro f _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  calc
    (MvPolynomial.C (oneHot (F := F) (f a) b) *
          MvPolynomial.X (Sum.inl f) *
          MvPolynomial.X (Sum.inr a)).totalDegree ≤
        (MvPolynomial.C (oneHot (F := F) (f a) b) *
          MvPolynomial.X (Sum.inl f)).totalDegree +
          (MvPolynomial.X (Sum.inr a) :
            MvPolynomial ((A → B) ⊕ A) F).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ ((MvPolynomial.C (oneHot (F := F) (f a) b) :
            MvPolynomial ((A → B) ⊕ A) F).totalDegree +
          (MvPolynomial.X (Sum.inl f) :
            MvPolynomial ((A → B) ⊕ A) F).totalDegree) + 1 := by
      exact Nat.add_le_add (MvPolynomial.totalDegree_mul _ _) (by simp)
    _ = 2 := by simp

/-- Holding the function fixed collapses evaluation to a linear routing map
on argument coordinates. -/
def fixedFunctionEvaluationPolynomial [Fintype A]
    (f : A → B) (b : B) : MvPolynomial A F :=
  ∑ a : A,
    MvPolynomial.C (oneHot (F := F) (f a) b) * MvPolynomial.X a

@[simp] theorem eval_fixedFunctionEvaluationPolynomial [Fintype A]
    (f : A → B) (a : A) (b : B) :
    MvPolynomial.eval (oneHot (F := F) a)
        (fixedFunctionEvaluationPolynomial (F := F) f b) =
      oneHot (F := F) (f a) b := by
  classical
  simp only [fixedFunctionEvaluationPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.sum_eq_single a]
  · have haa : oneHot (F := F) a a = 1 := by
      simp only [oneHot, if_pos]
    rw [haa, mul_one]
  · intro a' _ hne
    simp [oneHot, hne]
  · simp

theorem fixedFunctionEvaluationPolynomial_totalDegree_le_one [Fintype A]
    (f : A → B) (b : B) :
    (fixedFunctionEvaluationPolynomial (F := F) f b).totalDegree ≤ 1 := by
  classical
  unfold fixedFunctionEvaluationPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  calc
    (MvPolynomial.C (oneHot (F := F) (f a) b) *
        MvPolynomial.X a).totalDegree ≤
      (MvPolynomial.C (oneHot (F := F) (f a) b) :
        MvPolynomial A F).totalDegree +
        (MvPolynomial.X a : MvPolynomial A F).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

/-- Holding the argument fixed is likewise linear on function coordinates. -/
def fixedArgumentEvaluationPolynomial [Fintype A] [Fintype B]
    [DecidableEq A] (a : A) (b : B) : MvPolynomial (A → B) F :=
  ∑ f : A → B,
    MvPolynomial.C (oneHot (F := F) (f a) b) * MvPolynomial.X f

@[simp] theorem eval_fixedArgumentEvaluationPolynomial
    [Fintype A] [Fintype B] [DecidableEq A]
    (f : A → B) (a : A) (b : B) :
    MvPolynomial.eval (oneHot (F := F) f)
        (fixedArgumentEvaluationPolynomial (F := F) a b) =
      oneHot (F := F) (f a) b := by
  classical
  simp only [fixedArgumentEvaluationPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.sum_eq_single f]
  · have hff : oneHot (F := F) f f = 1 := by
      simp only [oneHot, if_pos]
    rw [hff, mul_one]
  · intro f' _ hne
    simp [oneHot, hne]
  · simp

theorem fixedArgumentEvaluationPolynomial_totalDegree_le_one
    [Fintype A] [Fintype B] [DecidableEq A]
    (a : A) (b : B) :
    (fixedArgumentEvaluationPolynomial (F := F) a b).totalDegree ≤ 1 := by
  classical
  unfold fixedArgumentEvaluationPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro f _
  calc
    (MvPolynomial.C (oneHot (F := F) (f a) b) *
        MvPolynomial.X f).totalDegree ≤
      (MvPolynomial.C (oneHot (F := F) (f a) b) :
        MvPolynomial (A → B) F).totalDegree +
        (MvPolynomial.X f : MvPolynomial (A → B) F).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

/-! ## 2. Mixed finite differences detect interaction degree -/

/-- The mixed finite difference of a polynomial between its left and right
variable blocks.  Affine functions have zero mixed difference. -/
def mixedDifference {X : Type*} {Y : Type*}
    (p : MvPolynomial (X ⊕ Y) F)
    (x₀ x₁ : X → F) (y₀ y₁ : Y → F) : F :=
  MvPolynomial.eval (pack x₀ y₀) p -
    MvPolynomial.eval (pack x₀ y₁) p -
    MvPolynomial.eval (pack x₁ y₀) p +
    MvPolynomial.eval (pack x₁ y₁) p

private theorem finsupp_eq_zero_of_sum_eq_zero {X : Type*}
    (d : X →₀ ℕ) (h : d.sum (fun _ n => n) = 0) : d = 0 := by
  ext x
  apply Nat.eq_zero_of_le_zero
  calc
    d x = (Finsupp.single x (d x)).sum (fun _ n => n) := by simp
    _ ≤ d.sum (fun _ n => n) :=
      Finsupp.single_le_sum d (by intro _ _; exact Nat.zero_le _) x
    _ = 0 := h

/-- A monomial of total degree at most one has zero mixed difference. -/
private theorem mixedDifference_monomial_zero_of_sum_le_one
    {X : Type*} {Y : Type*} (d : (X ⊕ Y) →₀ ℕ) (c : F)
    (hdegree : d.sum (fun _ n => n) ≤ 1)
    (x₀ x₁ : X → F) (y₀ y₁ : Y → F) :
    mixedDifference (MvPolynomial.monomial d c) x₀ x₁ y₀ y₁ = 0 := by
  have hcases : d.sum (fun _ n => n) = 0 ∨ d.sum (fun _ n => n) = 1 := by
    omega
  rcases hcases with hzero | hone
  · have hd : d = 0 := finsupp_eq_zero_of_sum_eq_zero d hzero
    subst d
    simp [mixedDifference]
  · rcases (Finsupp.sum_eq_one_iff d).mp hone with ⟨z, rfl⟩
    cases z with
    | inl x =>
        simp [mixedDifference, MvPolynomial.eval_monomial, pack]
    | inr y =>
        simp [mixedDifference, MvPolynomial.eval_monomial, pack]

/-- **All total-degree-one polynomials have zero cross interaction.**

This is the algebraic lower-bound engine.  It applies to arbitrary polynomial
syntax, not merely to a hand-chosen affine normal form. -/
theorem mixedDifference_zero_of_totalDegree_le_one
    {X : Type*} {Y : Type*} (p : MvPolynomial (X ⊕ Y) F)
    (hdegree : p.totalDegree ≤ 1)
    (x₀ x₁ : X → F) (y₀ y₁ : Y → F) :
    mixedDifference p x₀ x₁ y₀ y₁ = 0 := by
  classical
  rw [p.as_sum]
  have hsum : ∀ s : Finset ((X ⊕ Y) →₀ ℕ), s ⊆ p.support →
      mixedDifference
          (∑ d ∈ s, MvPolynomial.monomial d (p.coeff d))
          x₀ x₁ y₀ y₁ = 0 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp [mixedDifference]
    | @insert d s hd ih =>
        rw [Finset.sum_insert hd]
        have hdmem : d ∈ p.support := hs (by simp)
        have hsmem : s ⊆ p.support := by
          intro e he
          exact hs (by simp [he])
        have hmono := mixedDifference_monomial_zero_of_sum_le_one
          d (p.coeff d)
          ((MvPolynomial.le_totalDegree hdmem).trans hdegree) x₀ x₁ y₀ y₁
        have hrest := ih hsmem
        dsimp [mixedDifference] at hmono hrest ⊢
        simp only [MvPolynomial.eval_add]
        linear_combination hmono + hrest
  exact hsum p.support (fun _ h => h)

/-! ## 3. A pointwise obstruction for arbitrary CCC semantics -/

/-- The pointwise data exposed by an internal evaluator after choosing a
semantic probe.  In a concrete CCC, `FunctionPoint` can be the global points
of an exponential object and `evaluate` the global-point action of its
evaluation morphism.  The coordinate types and encodings are deliberately
arbitrary: the obstruction below is not tied to one-hot tables. -/
structure PointEvaluationModel
    (FunctionPoint ArgumentPoint OutputPoint : Type*) (F : Type*) where
  FunctionCoord : Type*
  ArgumentCoord : Type*
  OutputCoord : Type*
  codeFunction : FunctionPoint → FunctionCoord → F
  codeArgument : ArgumentPoint → ArgumentCoord → F
  codeOutput : OutputPoint → OutputCoord → F
  evaluate : FunctionPoint → ArgumentPoint → OutputPoint

namespace PointEvaluationModel

variable {K Aₚ Bₚ : Type*}

/-- The semantic mixed rectangle seen at one output coordinate. -/
def semanticRectangle (M : PointEvaluationModel K Aₚ Bₚ F)
    (k₀ k₁ : K) (a₀ a₁ : Aₚ) (output : M.OutputCoord) : F :=
  M.codeOutput (M.evaluate k₀ a₀) output -
    M.codeOutput (M.evaluate k₀ a₁) output -
    M.codeOutput (M.evaluate k₁ a₀) output +
    M.codeOutput (M.evaluate k₁ a₁) output

/-- A total-degree-one polynomial implementation of the probed evaluator. -/
structure DegreeOnePresentation (M : PointEvaluationModel K Aₚ Bₚ F) where
  polynomial : M.OutputCoord →
    MvPolynomial (M.FunctionCoord ⊕ M.ArgumentCoord) F
  degree_le_one : ∀ output, (polynomial output).totalDegree ≤ 1
  exact : ∀ (k : K) (a : Aₚ) (output : M.OutputCoord),
    MvPolynomial.eval (pack (M.codeFunction k) (M.codeArgument a))
        (polynomial output) =
      M.codeOutput (M.evaluate k a) output

/-- **Probe-level CCC obstruction.**  A single nonzero evaluation rectangle
rules out every degree-one polynomial implementation, regardless of the sizes
or shapes of the chosen coordinate spaces. -/
theorem noDegreeOne_of_semanticRectangle_ne_zero
    (M : PointEvaluationModel K Aₚ Bₚ F)
    (k₀ k₁ : K) (a₀ a₁ : Aₚ) (output : M.OutputCoord)
    (hnonzero : M.semanticRectangle k₀ k₁ a₀ a₁ output ≠ 0) :
    ¬ Nonempty M.DegreeOnePresentation := by
  rintro ⟨P⟩
  have hzero := mixedDifference_zero_of_totalDegree_le_one
    (P.polynomial output) (P.degree_le_one output)
    (M.codeFunction k₀) (M.codeFunction k₁)
    (M.codeArgument a₀) (M.codeArgument a₁)
  dsimp [mixedDifference] at hzero
  rw [P.exact k₀ a₀ output, P.exact k₀ a₁ output,
    P.exact k₁ a₀ output, P.exact k₁ a₁ output] at hzero
  exact hnonzero hzero

end PointEvaluationModel

/-! ## 4. The extensional evaluator has nonzero mixed difference -/

/-- If `a₀ ≠ a₁` and `b₀ ≠ b₁`, evaluation contains a Boolean-sized mixed
interaction rectangle.  The result uses only four valid inputs. -/
theorem evaluation_mixedDifference_nonzero [Fintype A] [Fintype B]
    [DecidableEq A]
    {a₀ a₁ : A} (ha : a₀ ≠ a₁) {b₀ b₁ : B} (hb : b₀ ≠ b₁) :
    mixedDifference (evaluationPolynomial (F := F) b₁)
      (oneHot (F := F) (fun _ : A => b₀))
      (oneHot (F := F) (fun a => if a = a₁ then b₁ else b₀))
      (oneHot (F := F) a₀) (oneHot (F := F) a₁) ≠ 0 := by
  intro hzero
  simp only [mixedDifference] at hzero
  have heval : ∀ (f : A → B) (a : A),
      MvPolynomial.eval (pack (oneHot (F := F) f) (oneHot (F := F) a))
          (evaluationPolynomial (F := F) b₁) =
        oneHot (F := F) (f a) b₁ := by
    intro f a
    simpa [evaluationInput] using
      (eval_evaluationPolynomial (F := F) f a b₁)
  rw [heval, heval, heval, heval] at hzero
  have hone : (1 : F) = 0 := by
    simpa [oneHot, ha, hb.symm] using hzero
  exact one_ne_zero hone

/-- **No degree-one polynomial family can present a nondegenerate CCC
evaluator.**  This obstruction holds already for one output coordinate. -/
theorem no_degree_one_evaluation [DecidableEq A]
    {a₀ a₁ : A} (ha : a₀ ≠ a₁) {b₀ b₁ : B} (hb : b₀ ≠ b₁) :
    ¬ ∃ polynomials : B → MvPolynomial ((A → B) ⊕ A) F,
        (∀ b, (polynomials b).totalDegree ≤ 1) ∧
        ∀ (f : A → B) (a : A) (b : B),
          MvPolynomial.eval (evaluationInput (F := F) f a) (polynomials b) =
            oneHot (F := F) (f a) b := by
  rintro ⟨polynomials, hdegree, hexact⟩
  let f₀ : A → B := fun _ => b₀
  let f₁ : A → B := fun a => if a = a₁ then b₁ else b₀
  have hcross := mixedDifference_zero_of_totalDegree_le_one
    (polynomials b₁) (hdegree b₁)
    (oneHot (F := F) f₀) (oneHot (F := F) f₁)
    (oneHot (F := F) a₀) (oneHot (F := F) a₁)
  have hexact' : ∀ (f : A → B) (a : A) (b : B),
      MvPolynomial.eval (pack (oneHot (F := F) f) (oneHot (F := F) a))
          (polynomials b) = oneHot (F := F) (f a) b := by
    intro f a b
    simpa [evaluationInput] using hexact f a b
  dsimp [mixedDifference] at hcross
  rw [hexact' f₀ a₀ b₁, hexact' f₀ a₁ b₁,
    hexact' f₁ a₀ b₁, hexact' f₁ a₁ b₁] at hcross
  have hone : (1 : F) = 0 := by
    simpa [f₀, f₁, oneHot, ha, hb.symm] using hcross
  exact one_ne_zero hone

/-! ## 5. Exact classification of the affine degeneracies -/

/-- A degree-one polynomial family that is exact on valid evaluation codes. -/
structure DegreeOneEvaluationPresentation (A : Type u) (B : Type v)
    (F : Type w) [Field F] where
  polynomial : B → MvPolynomial ((A → B) ⊕ A) F
  degree_le_one : ∀ b, (polynomial b).totalDegree ≤ 1
  exact : ∀ (f : A → B) (a : A) (b : B),
    MvPolynomial.eval (evaluationInput (F := F) f a) (polynomial b) =
      oneHot (F := F) (f a) b

/-- Evaluation has no input points when the domain is empty, so the zero
polynomial family is vacuously exact. -/
def degreeOneOfEmptyDomain [IsEmpty A] :
    DegreeOneEvaluationPresentation A B F where
  polynomial := fun _ => 0
  degree_le_one := fun _ => by simp
  exact := fun _ a _ => isEmptyElim a

/-- An empty codomain has no output coordinates to implement. -/
def degreeOneOfEmptyCodomain [IsEmpty B] :
    DegreeOneEvaluationPresentation A B F where
  polynomial := fun b => isEmptyElim b
  degree_le_one := fun b => isEmptyElim b
  exact := fun _ _ b => isEmptyElim b

/-- If the domain is subsingleton, evaluation is only a function lookup: no
function/argument interaction remains. -/
def degreeOneOfSubsingletonDomain [Fintype A] [Fintype B] [DecidableEq A]
    [Nonempty A]
    (hA : Subsingleton A) : DegreeOneEvaluationPresentation A B F := by
  letI : Subsingleton A := hA
  classical
  let a₀ : A := Classical.choice (inferInstanceAs (Nonempty A))
  exact {
        polynomial := fun b =>
          ∑ f : A → B,
            MvPolynomial.C (oneHot (F := F) (f a₀) b) *
              MvPolynomial.X (Sum.inl f)
        degree_le_one := by
          intro b
          apply MvPolynomial.totalDegree_finsetSum_le
          intro f _
          calc
            (MvPolynomial.C (oneHot (F := F) (f a₀) b) *
                MvPolynomial.X (Sum.inl f)).totalDegree ≤
              (MvPolynomial.C (oneHot (F := F) (f a₀) b) :
                MvPolynomial ((A → B) ⊕ A) F).totalDegree +
                (MvPolynomial.X (Sum.inl f) :
                  MvPolynomial ((A → B) ⊕ A) F).totalDegree :=
                MvPolynomial.totalDegree_mul _ _
            _ = 1 := by simp
        exact := by
          intro f a b
          have ha : a = a₀ := Subsingleton.elim _ _
          subst a
          simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
            MvPolynomial.eval_C, MvPolynomial.eval_X, evaluationInput,
            pack, Sum.elim_inl]
          rw [Finset.sum_eq_single f]
          · have hff : oneHot (F := F) f f = 1 := by
              simp only [oneHot, if_pos]
            rw [hff, mul_one]
          · intro f' _ hne
            simp [oneHot, hne]
          · simp }

/-- If the codomain is subsingleton, evaluation is constant and therefore
degree zero. -/
def degreeOneOfSubsingletonCodomain [Fintype A] [Fintype B]
    [Nonempty B]
    (hB : Subsingleton B) : DegreeOneEvaluationPresentation A B F := by
  letI : Subsingleton B := hB
  classical
  let b₀ : B := Classical.choice (inferInstanceAs (Nonempty B))
  exact {
        polynomial := fun b => MvPolynomial.C (oneHot (F := F) b₀ b)
        degree_le_one := fun _ => by simp
        exact := by
          intro f a b
          have hfa : f a = b₀ := Subsingleton.elim _ _
          simp [hfa] }

/-- **Sharp classification.**  Extensional CCC evaluation admits a degree-one
finite-field polynomial presentation exactly in the degenerate cases where
the domain or codomain is subsingleton. -/
theorem degreeOneEvaluation_nonempty_iff [Fintype A] [Fintype B]
    [DecidableEq A] :
    Nonempty (DegreeOneEvaluationPresentation A B F) ↔
      Subsingleton A ∨ Subsingleton B := by
  constructor
  · rintro ⟨P⟩
    by_contra h
    push Not at h
    have hAnt : Nontrivial A := h.1
    have hBnt : Nontrivial B := h.2
    letI : Nontrivial A := hAnt
    letI : Nontrivial B := hBnt
    rcases exists_pair_ne A with ⟨a₀, a₁, ha⟩
    rcases exists_pair_ne B with ⟨b₀, b₁, hb⟩
    exact no_degree_one_evaluation (F := F) ha hb
      ⟨P.polynomial, P.degree_le_one, P.exact⟩
  · rintro (hA | hB)
    · rcases isEmpty_or_nonempty A with hEmpty | hNonempty
      · letI : IsEmpty A := hEmpty
        exact ⟨degreeOneOfEmptyDomain (F := F)⟩
      · letI : Nonempty A := hNonempty
        exact ⟨degreeOneOfSubsingletonDomain (F := F) hA⟩
    · rcases isEmpty_or_nonempty B with hEmpty | hNonempty
      · letI : IsEmpty B := hEmpty
        exact ⟨degreeOneOfEmptyCodomain (F := F)⟩
      · letI : Nonempty B := hNonempty
        exact ⟨degreeOneOfSubsingletonCodomain (F := F) hB⟩

/-- The complete degree frontier for finite extensional exponentials: degree
two always suffices, while degree one suffices exactly in the degenerate
cases. -/
theorem finite_exponential_polynomial_frontier [Fintype A] [Fintype B]
    [DecidableEq A] :
    (∀ b : B,
      (evaluationPolynomial (A := A) (B := B) (F := F) b).totalDegree ≤ 2) ∧
    (Nonempty (DegreeOneEvaluationPresentation A B F) ↔
      Subsingleton A ∨ Subsingleton B) :=
  ⟨fun b => evaluationPolynomial_totalDegree_le_two
      (A := A) (B := B) (F := F) b,
    degreeOneEvaluation_nonempty_iff⟩

/-! ## 6. Intensional escape hatch and the cryptographic boundary -/

/-- Existing typed shared nets provide a concrete intensional inhabitant of
an exponential without enumerating the extensional function space. -/
def representedExponential
    (domain codomain : Dregg2.Calculus.IntensionalCCCTrace.Ty) :=
  Dregg2.Calculus.IntensionalCCCTrace.Net []
    (.arr domain codomain)

/-- The intensional route preserves denotation under each certified local
interaction step.  This avoids a dense extensional table; it does not by
itself supply a commitment or an interactive proof protocol. -/
theorem intensional_localStep_preserves_evaluation
    {domain codomain : Dregg2.Calculus.IntensionalCCCTrace.Ty}
    {before after : representedExponential domain codomain}
    (step : Dregg2.Calculus.IntensionalCCCTrace.LocalStep before after) :
    after.denote PUnit.unit = before.denote PUnit.unit :=
  Dregg2.Calculus.IntensionalCCCTrace.localStep_denote step PUnit.unit

#assert_all_clean [eval_evaluationPolynomial,
  evaluationPolynomial_totalDegree_le_two,
  eval_fixedFunctionEvaluationPolynomial,
  fixedFunctionEvaluationPolynomial_totalDegree_le_one,
  eval_fixedArgumentEvaluationPolynomial,
  fixedArgumentEvaluationPolynomial_totalDegree_le_one,
  mixedDifference_zero_of_totalDegree_le_one,
  PointEvaluationModel.noDegreeOne_of_semanticRectangle_ne_zero,
  evaluation_mixedDifference_nonzero,
  no_degree_one_evaluation,
  degreeOneEvaluation_nonempty_iff,
  finite_exponential_polynomial_frontier,
  intensional_localStep_preserves_evaluation]

end

end Dregg2.Metatheory.CCCPolynomialEvaluationFrontier
