/-
# Exact arithmetization of finite extensional HOL formulas

`FinitePolynomialFunctions.FiniteHOL` supplies an intrinsically typed simply
typed lambda calculus whose arrows are complete finite tables.  This file
closes the formula-level gap.  It gives:

* a syntax-directed Boolean false-bit compiler for every connective and for
  quantification over every finite type, including arrow types;
* a lossless flattening of typed environments into a finite field power;
* coordinatewise polynomial realizations of all typed terms; and
* one polynomial whose value is a Boolean false-bit for every formula.

The construction is exact, but deliberately does not make a succinctness
claim.  Quantifiers enumerate complete finite value spaces and the final
polynomial is obtained by truth-table interpolation.  At arrow types those
tables already have exponentially many coordinates.  Thus this is a semantic
existence construction and a checked compilation specification, not evidence
for constant-cost arbitrary higher-order quantification.
-/
import Dregg2.Metatheory.FinitePolynomialFunctions
import Dregg2.Metatheory.FinitePolynomialFunctionLimits
import Dregg2.Metatheory.FOLArithmetizationCorrected

namespace Dregg2.Metatheory.FiniteHOLFormulaArithmetization

open Dregg2.Metatheory.FinitePolynomialFunctions
open Dregg2.Metatheory.FinitePolynomialFunctions.FiniteHOL
open Dregg2.Metatheory.FinitePolynomialFunctionLimits
open Dregg2.Metatheory.FOLArithmetizationCorrected

noncomputable section

variable {F : Type} [Field F] [Fintype F]
variable {A B : Ty} {Γ : List Ty}

local instance classicalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## A syntax-directed Boolean compiler for full finite HOL -/

/-- Compile a finite-HOL formula to a Boolean *false bit*.

Zero means true and one means false.  The propositional nodes use the field
operations from the corrected FOL construction.  A quantifier ranges over the
complete finite interpretation of its bound type and tests the recursively
compiled body.  Equality and quantifier nodes are extensionally decidable on
these finite types.  This noncomputable specification intentionally leaves a
concrete enumeration algorithm to a refinement layer. -/
noncomputable def formulaFalseBit : {Γ : List Ty} → Formula F Γ → Env F Γ → F
  | _, .top, _ => 0
  | _, .bottom, _ => 1
  | _, .equal left right, env => if denote left env = denote right env then 0 else 1
  | _, .and p q, env => falseAnd (formulaFalseBit p env) (formulaFalseBit q env)
  | _, .or p q, env => falseOr (formulaFalseBit p env) (formulaFalseBit q env)
  | _, .imp p q, env =>
      falseOr (falseNot (formulaFalseBit p env)) (formulaFalseBit q env)
  | _, .not p, env => falseNot (formulaFalseBit p env)
  | _, .forall_ A p, env =>
      if ∀ x : Val F A, formulaFalseBit p (x, env) = 0 then 0 else 1
  | _, .exists_ A p, env =>
      if ∃ x : Val F A, formulaFalseBit p (x, env) = 0 then 0 else 1

/-- The full compiler theorem: every compiled formula is a bit, and it is zero
exactly when the extensional finite-HOL semantics satisfies the formula. -/
theorem formulaFalseBit_isBit_and_correct :
    ∀ {Γ : List Ty} (p : Formula F Γ) (env : Env F Γ),
      IsBit (formulaFalseBit p env) ∧
        (formulaFalseBit p env = 0 ↔ Satisfies p env) := by
  intro Γ p
  induction p with
  | top =>
      intro env
      simp [formulaFalseBit, Satisfies, IsBit]
  | bottom =>
      intro env
      simp [formulaFalseBit, Satisfies, IsBit]
  | equal left right =>
      intro env
      by_cases h : denote left env = denote right env <;>
        simp [formulaFalseBit, Satisfies, IsBit, h]
  | and p q ihp ihq =>
      intro env
      have hp := ihp env
      have hq := ihq env
      refine ⟨falseAnd_is_bit hp.1 hq.1, ?_⟩
      rw [formulaFalseBit, Satisfies, falseAnd_eq_zero_iff hp.1 hq.1, hp.2, hq.2]
  | or p q ihp ihq =>
      intro env
      have hp := ihp env
      have hq := ihq env
      refine ⟨falseOr_is_bit hp.1 hq.1, ?_⟩
      rw [formulaFalseBit, Satisfies, falseOr_eq_zero_iff hp.1 hq.1, hp.2, hq.2]
  | imp p q ihp ihq =>
      intro env
      have hp := ihp env
      have hq := ihq env
      have hnp : IsBit (falseNot (formulaFalseBit p env)) := falseNot_is_bit hp.1
      refine ⟨falseOr_is_bit hnp hq.1, ?_⟩
      rw [formulaFalseBit, Satisfies, falseOr_eq_zero_iff hnp hq.1,
        falseNot_eq_zero_iff hp.1, hq.2]
      constructor
      · rintro (hnp | hq)
        · intro hpSat
          exact False.elim (hnp (hp.2.mpr hpSat))
        · exact fun _ => hq
      · intro himp
        by_cases hp0 : formulaFalseBit p env = 0
        · exact Or.inr (himp (hp.2.mp hp0))
        · exact Or.inl hp0
  | not p ihp =>
      intro env
      have hp := ihp env
      refine ⟨falseNot_is_bit hp.1, ?_⟩
      rw [formulaFalseBit, Satisfies, falseNot_eq_zero_iff hp.1]
      exact not_congr hp.2
  | forall_ A p ih =>
      intro env
      by_cases h : ∀ x : Val F A, formulaFalseBit p (x, env) = 0
      · rw [formulaFalseBit, if_pos h]
        refine ⟨Or.inl rfl, ?_⟩
        simp only [Satisfies, true_iff]
        intro x
        exact (ih (x, env)).2.mp (h x)
      · rw [formulaFalseBit, if_neg h]
        refine ⟨Or.inr rfl, ?_⟩
        simp only [one_ne_zero, false_iff, Satisfies]
        intro hs
        apply h
        intro x
        exact (ih (x, env)).2.mpr (hs x)
  | exists_ A p ih =>
      intro env
      by_cases h : ∃ x : Val F A, formulaFalseBit p (x, env) = 0
      · rw [formulaFalseBit, if_pos h]
        refine ⟨Or.inl rfl, ?_⟩
        simp only [Satisfies, true_iff]
        obtain ⟨x, hx⟩ := h
        exact ⟨x, (ih (x, env)).2.mp hx⟩
      · rw [formulaFalseBit, if_neg h]
        refine ⟨Or.inr rfl, ?_⟩
        simp only [one_ne_zero, false_iff, Satisfies]
        rintro ⟨x, hx⟩
        exact h ⟨x, (ih (x, env)).2.mpr hx⟩

/-- A convenient projection of the full compiler theorem. -/
theorem formulaFalseBit_isBit (p : Formula F Γ) (env : Env F Γ) :
    IsBit (formulaFalseBit p env) :=
  (formulaFalseBit_isBit_and_correct p env).1

/-- Zero of the compiled residual is exactly HOL truth. -/
theorem formulaFalseBit_eq_zero_iff (p : Formula F Γ) (env : Env F Γ) :
    formulaFalseBit p env = 0 ↔ Satisfies p env :=
  (formulaFalseBit_isBit_and_correct p env).2

/-! ## Flattening contexts into finite field powers -/

/-- Coordinates of a typed context.  A context environment is exactly one field
element for every coordinate of every variable in the context. -/
def ContextCoord (F : Type) : List Ty → Type
  | [] => Empty
  | A :: Γ => Coord F A ⊕ ContextCoord F Γ

/-- Every context-coordinate type is finite. -/
instance contextCoordFinite : (Γ : List Ty) → Finite (ContextCoord F Γ)
  | [] => inferInstanceAs (Finite Empty)
  | A :: Γ => by
      letI := coordFinite (F := F) A
      letI := contextCoordFinite Γ
      exact inferInstanceAs (Finite (Coord F A ⊕ ContextCoord F Γ))

/-- Flatten a typed environment into its field-power point. -/
def flattenEnv : {Γ : List Ty} → Env F Γ → ContextCoord F Γ → F
  | [], _, i => nomatch i
  | _ :: _, env, Sum.inl i => env.1 i
  | _ :: _, env, Sum.inr j => flattenEnv env.2 j

/-- Reconstruct a typed environment from its field-power point. -/
def unflattenEnv : {Γ : List Ty} → (ContextCoord F Γ → F) → Env F Γ
  | [], _ => PUnit.unit
  | _ :: _, point =>
      (fun i => point (Sum.inl i), unflattenEnv (fun j => point (Sum.inr j)))

omit [Field F] [Fintype F] in
/-- Reconstruction after flattening is identity. -/
@[simp] theorem unflattenEnv_flattenEnv : ∀ {Γ : List Ty} (env : Env F Γ),
    unflattenEnv (flattenEnv env) = env := by
  intro Γ
  induction Γ with
  | nil =>
      intro env
      cases env
      rfl
  | cons A Γ ih =>
      intro env
      apply Prod.ext
      · funext i
        rfl
      · exact ih env.2

omit [Field F] [Fintype F] in
/-- Flattening after reconstruction is identity. -/
@[simp] theorem flattenEnv_unflattenEnv : ∀ {Γ : List Ty}
    (point : ContextCoord F Γ → F), flattenEnv (unflattenEnv point) = point := by
  intro Γ
  induction Γ with
  | nil =>
      intro point
      funext i
      exact Empty.elim i
  | cons A Γ ih =>
      intro point
      funext ij
      cases ij with
      | inl i => rfl
      | inr j => exact congrFun (ih (fun k => point (Sum.inr k))) j

/-- Typed environments are exactly their flattened finite-field points. -/
def environmentEquiv (Γ : List Ty) : Env F Γ ≃ (ContextCoord F Γ → F) where
  toFun := flattenEnv
  invFun := unflattenEnv
  left_inv := unflattenEnv_flattenEnv
  right_inv := flattenEnv_unflattenEnv

/-! ## Polynomial compilation of all terms and formulas -/

/-- The polynomial for one output coordinate of an arbitrary well-typed term.

This interpolates the complete extensional denotation as a function of the
flattened environment.  The result therefore includes lambda and application,
but may be exponentially large. -/
def termPolynomial (term : Tm F Γ A) (j : Coord F A) :
    MvPolynomial (ContextCoord F Γ) F := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  exact interpolate (fun point => denote term (unflattenEnv point) j)

/-- Exactness at every raw field-power point. -/
@[simp] theorem eval_termPolynomial_point (term : Tm F Γ A)
    (point : ContextCoord F Γ → F) (j : Coord F A) :
    MvPolynomial.eval point (termPolynomial term j) = denote term (unflattenEnv point) j := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  simp only [termPolynomial, eval_interpolate]

/-- Exactness of the term polynomial at every typed environment. -/
@[simp] theorem eval_termPolynomial (term : Tm F Γ A) (env : Env F Γ)
    (j : Coord F A) :
    MvPolynomial.eval (flattenEnv env) (termPolynomial term j) = denote term env j := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  simp only [termPolynomial, eval_interpolate, unflattenEnv_flattenEnv]

/-- The application node's globally interpolated polynomial agrees with the
specialized table-lookup polynomial on the denotations of its two operands. -/
theorem termPolynomial_app_agrees_with_applicationPolynomial
    (fn : Tm F Γ (.arr A B)) (arg : Tm F Γ A) (env : Env F Γ) (j : Coord F B) :
    MvPolynomial.eval (flattenEnv env) (termPolynomial (.app fn arg) j) =
      MvPolynomial.eval (pack (denote fn env) (denote arg env))
        (applicationPolynomial A B j) := by
  rw [eval_termPolynomial, eval_applicationPolynomial_denote]

/-- Polynomial beta at a lambda boundary.  The outer lambda coordinate at an
argument `x` is the body polynomial evaluated in the extended environment. -/
theorem termPolynomial_lambda_beta (body : Tm F (A :: Γ) B)
    (env : Env F Γ) (x : Val F A) (j : Coord F B) :
    MvPolynomial.eval (flattenEnv env) (termPolynomial (.lam body) (x, j)) =
      MvPolynomial.eval (flattenEnv (Γ := A :: Γ) (x, env)) (termPolynomial body j) := by
  refine (eval_termPolynomial (.lam body) env (x, j)).trans
    (Eq.trans ?_ (eval_termPolynomial body (x, env) j).symm)
  rfl

/-- The complete polynomial arithmetization of a finite-HOL formula.  Its
variables are precisely the flattened coordinates of the free context. -/
def formulaPolynomial (p : Formula F Γ) : MvPolynomial (ContextCoord F Γ) F := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  exact interpolate (fun point => formulaFalseBit p (unflattenEnv point))

/-- Polynomial evaluation at every raw field-power point recovers the compiled
false-bit for the corresponding reconstructed environment. -/
@[simp] theorem eval_formulaPolynomial_point (p : Formula F Γ)
    (point : ContextCoord F Γ → F) :
    MvPolynomial.eval point (formulaPolynomial p) =
      formulaFalseBit p (unflattenEnv point) := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  simp only [formulaPolynomial, eval_interpolate]

/-- Polynomial evaluation recovers the syntax-directed formula false-bit. -/
@[simp] theorem eval_formulaPolynomial (p : Formula F Γ) (env : Env F Γ) :
    MvPolynomial.eval (flattenEnv env) (formulaPolynomial p) = formulaFalseBit p env := by
  letI := Fintype.ofFinite (ContextCoord F Γ)
  simp only [formulaPolynomial, eval_interpolate, unflattenEnv_flattenEnv]

/-- **Full finite-HOL polynomial compiler theorem.**  The polynomial evaluates
to zero exactly when the source formula is true, for arbitrary formulas with
products, lambdas, applications, equality at all finite types, Boolean
connectives, and quantifiers over all finite values (including functions). -/
theorem eval_formulaPolynomial_eq_zero_iff (p : Formula F Γ) (env : Env F Γ) :
    MvPolynomial.eval (flattenEnv env) (formulaPolynomial p) = 0 ↔ Satisfies p env := by
  rw [eval_formulaPolynomial]
  exact formulaFalseBit_eq_zero_iff p env

/-- The full compiler theorem stated directly on arbitrary raw polynomial
inputs; `unflattenEnv` supplies the unique corresponding typed environment. -/
theorem eval_formulaPolynomial_point_eq_zero_iff (p : Formula F Γ)
    (point : ContextCoord F Γ → F) :
    MvPolynomial.eval point (formulaPolynomial p) = 0 ↔
      Satisfies p (unflattenEnv point) := by
  rw [eval_formulaPolynomial_point]
  exact formulaFalseBit_eq_zero_iff p (unflattenEnv point)

/-- Formula polynomials are Boolean on every point arising from a typed
environment. -/
theorem eval_formulaPolynomial_isBit (p : Formula F Γ) (env : Env F Γ) :
    IsBit (MvPolynomial.eval (flattenEnv env) (formulaPolynomial p)) := by
  rw [eval_formulaPolynomial]
  exact formulaFalseBit_isBit p env

/-- The formula polynomial is Boolean on the entire ambient field power, not
merely on a proper subset of encoded inputs. -/
theorem eval_formulaPolynomial_point_isBit (p : Formula F Γ)
    (point : ContextCoord F Γ → F) :
    IsBit (MvPolynomial.eval point (formulaPolynomial p)) := by
  rw [eval_formulaPolynomial_point]
  exact formulaFalseBit_isBit p (unflattenEnv point)

/-- Universal quantification compiles exactly, at every finite type. -/
theorem eval_formulaPolynomial_forall_eq_zero_iff (p : Formula F (A :: Γ))
    (env : Env F Γ) :
    MvPolynomial.eval (flattenEnv env) (formulaPolynomial (.forall_ A p)) = 0 ↔
      ∀ x : Val F A, Satisfies p (x, env) := by
  rw [eval_formulaPolynomial_eq_zero_iff]
  rfl

/-- Existential quantification compiles exactly, at every finite type. -/
theorem eval_formulaPolynomial_exists_eq_zero_iff (p : Formula F (A :: Γ))
    (env : Env F Γ) :
    MvPolynomial.eval (flattenEnv env) (formulaPolynomial (.exists_ A p)) = 0 ↔
      ∃ x : Val F A, Satisfies p (x, env) := by
  rw [eval_formulaPolynomial_eq_zero_iff]
  rfl

/-- The higher-order specialization: a universal arrow quantifier ranges over
every extensional finite function table, with no first-order collapse. -/
theorem eval_formulaPolynomial_forall_arrow_eq_zero_iff
    (p : Formula F (.arr A B :: Γ)) (env : Env F Γ) :
    MvPolynomial.eval (flattenEnv env) (formulaPolynomial (.forall_ (.arr A B) p)) = 0 ↔
      ∀ table : ExpCoord (Coord F A) (Coord F B) F → F, Satisfies p (table, env) := by
  rw [eval_formulaPolynomial_eq_zero_iff]
  rfl

/-! ## Exact size of exhaustive higher-order quantification -/

omit [Field F] in
/-- A quantifier at any finite HOL type ranges over exactly one field value per
coordinate assignment. -/
theorem card_quantifierDomain (A : Ty) :
    Nat.card (Val F A) = Nat.card F ^ Nat.card (Coord F A) := by
  exact Nat.card_fun

/-- At an arrow type, the exhaustive quantifier domain has
`q^(m * q^n)` elements: the number of complete functions from `F^n` to `F^m`.
This is the exact cost boundary hidden by the semantic existence theorem. -/
theorem card_arrowQuantifierDomain (A B : Ty) :
    Nat.card (Val F (.arr A B)) =
      Nat.card F ^
        (Nat.card (Coord F B) * Nat.card F ^ Nat.card (Coord F A)) := by
  exact card_tableObject (F := F) (σ := Coord F A) (τ := Coord F B)

#assert_all_clean [formulaFalseBit_isBit_and_correct, formulaFalseBit_isBit,
  formulaFalseBit_eq_zero_iff, unflattenEnv_flattenEnv, flattenEnv_unflattenEnv,
  eval_termPolynomial_point, eval_termPolynomial,
  termPolynomial_app_agrees_with_applicationPolynomial,
  termPolynomial_lambda_beta, eval_formulaPolynomial,
  eval_formulaPolynomial_point,
  eval_formulaPolynomial_eq_zero_iff, eval_formulaPolynomial_point_eq_zero_iff,
  eval_formulaPolynomial_isBit, eval_formulaPolynomial_point_isBit,
  eval_formulaPolynomial_forall_eq_zero_iff,
  eval_formulaPolynomial_exists_eq_zero_iff,
  eval_formulaPolynomial_forall_arrow_eq_zero_iff, card_quantifierDomain,
  card_arrowQuantifierDomain]

end

end Dregg2.Metatheory.FiniteHOLFormulaArithmetization
