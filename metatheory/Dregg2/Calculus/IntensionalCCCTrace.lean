/-
# Dregg2.Calculus.IntensionalCCCTrace -- local, shared STLC evidence

This file supplies an intensional alternative to the complete finite function
tables in `FiniteHOLFormulaArithmetization`.  Its source is the simply typed
lambda calculus with unit, natural-number constants, products, arrows, and a
unary operation.  The target adds an explicit `share` binder.  A beta
interaction does not enumerate an arrow table and does not copy its argument:

```
  (lambda x. body) argument  -->  share argument as x in body
```

`LocalStep` is typed local-rewrite evidence.  Its congruence constructors are
the path to one active interaction, so a step has exactly one rewrite while
retaining its address depth.  `Trace` composes those certificates.  Both source
and target have ordinary set-theoretic, intensional function semantics, and the
compiler and every accepted local trace preserve that denotation.

The final specimen makes sharing quantitative.  An eight-node computation is
bound once and referenced twice: beta costs one local rewrite, the shared graph
contains eight work nodes, while literal substitution contains sixteen.  The
target size is constant in the finite-field cardinality `q`; the comparison
function records that an extensional one-input/two-output table instead has
`2*q` coordinates.

Scope is deliberately narrow.  This is an intensional presentation of a useful
free-CCC internal-language fragment, not a proof of the free universal
property, not an embedding of arbitrary cartesian closed categories, and not a
cryptographic IOP/IOPP or polynomial commitment scheme.
-/
import Dregg2.Tactics

namespace Dregg2.Calculus.IntensionalCCCTrace

/-! ## Intrinsically typed source language -/

/-- Types of the simply typed/free-CCC internal-language fragment. -/
inductive Ty where
  | unit
  | nat
  | prod (left right : Ty)
  | arr (domain codomain : Ty)
  deriving DecidableEq, Repr

/-- An intensional set interpretation.  In particular, an arrow is a Lean
function, not a materialized table of all input/output coordinates. -/
@[reducible] def Val : Ty -> Type
  | .unit => PUnit
  | .nat => Nat
  | .prod A B => Val A × Val B
  | .arr A B => Val A -> Val B

/-- Well-typed de Bruijn variables. -/
inductive Var : List Ty -> Ty -> Type where
  | zero : Var (A :: Γ) A
  | succ : Var Γ A -> Var (B :: Γ) A
  deriving DecidableEq, Repr

/-- Typed environments, ordered like the de Bruijn context. -/
def Env : List Ty -> Type
  | [] => PUnit
  | A :: Γ => Val A × Env Γ

/-- Total lookup, with the result type enforced by the variable index. -/
def lookup : Var Γ A -> Env Γ -> Val A
  | .zero, env => env.1
  | .succ x, env => lookup x env.2

/-- Source STLC terms.  `let1` makes source-level sharing expressible, while
ordinary lambda/application terms need not mention the target representation. -/
inductive Tm : List Ty -> Ty -> Type where
  | var : Var Γ A -> Tm Γ A
  | unit : Tm Γ .unit
  | lit : Nat -> Tm Γ .nat
  | succ : Tm Γ .nat -> Tm Γ .nat
  | pair : Tm Γ A -> Tm Γ B -> Tm Γ (.prod A B)
  | fst : Tm Γ (.prod A B) -> Tm Γ A
  | snd : Tm Γ (.prod A B) -> Tm Γ B
  | lam : Tm (A :: Γ) B -> Tm Γ (.arr A B)
  | app : Tm Γ (.arr A B) -> Tm Γ A -> Tm Γ B
  | let1 : Tm Γ A -> Tm (A :: Γ) B -> Tm Γ B

/-- Standard set denotation of the source term. -/
def Tm.denote : Tm Γ A -> Env Γ -> Val A
  | .var x, env => lookup x env
  | .unit, _ => PUnit.unit
  | .lit n, _ => n
  | .succ n, env => n.denote env + 1
  | .pair left right, env => (left.denote env, right.denote env)
  | .fst p, env => (p.denote env).1
  | .snd p, env => (p.denote env).2
  | .lam body, env => fun x => body.denote (x, env)
  | .app fn arg, env => fn.denote env (arg.denote env)
  | .let1 value body, env => body.denote (value.denote env, env)

/-- Pure source syntax size. -/
def Tm.nodeCount : Tm Γ A -> Nat
  | .var _ => 1
  | .unit => 1
  | .lit _ => 1
  | .succ n => n.nodeCount + 1
  | .pair left right => left.nodeCount + right.nodeCount + 1
  | .fst p => p.nodeCount + 1
  | .snd p => p.nodeCount + 1
  | .lam body => body.nodeCount + 1
  | .app fn arg => fn.nodeCount + arg.nodeCount + 1
  | .let1 value body => value.nodeCount + body.nodeCount + 1

/-! ## Target graphs with explicit sharing -/

/-- Intensional target graphs.  `share value body` stores `value` once and
binds de Bruijn index zero in `body`; multiple variable leaves point to that
one binding rather than containing copied subgraphs. -/
inductive Net : List Ty -> Ty -> Type where
  | var : Var Γ A -> Net Γ A
  | unit : Net Γ .unit
  | lit : Nat -> Net Γ .nat
  | succ : Net Γ .nat -> Net Γ .nat
  | pair : Net Γ A -> Net Γ B -> Net Γ (.prod A B)
  | fst : Net Γ (.prod A B) -> Net Γ A
  | snd : Net Γ (.prod A B) -> Net Γ B
  | lam : Net (A :: Γ) B -> Net Γ (.arr A B)
  | app : Net Γ (.arr A B) -> Net Γ A -> Net Γ B
  | lift : Net Γ A -> Net (B :: Γ) A
  | share : Net Γ A -> Net (A :: Γ) B -> Net Γ B

/-- Target denotation.  A sharing node evaluates its definition once in the
semantic expression and supplies its value to every bound reference. -/
def Net.denote : Net Γ A -> Env Γ -> Val A
  | .var x, env => lookup x env
  | .unit, _ => PUnit.unit
  | .lit n, _ => n
  | .succ n, env => n.denote env + 1
  | .pair left right, env => (left.denote env, right.denote env)
  | .fst p, env => (p.denote env).1
  | .snd p, env => (p.denote env).2
  | .lam body, env => fun x => body.denote (x, env)
  | .app fn arg, env => fn.denote env (arg.denote env)
  | .lift net, env => net.denote env.2
  | .share value body, env => body.denote (value.denote env, env)

/-- Target graph size counts the shared definition once. -/
def Net.nodeCount : Net Γ A -> Nat
  | .var _ => 1
  | .unit => 1
  | .lit _ => 1
  | .succ n => n.nodeCount + 1
  | .pair left right => left.nodeCount + right.nodeCount + 1
  | .fst p => p.nodeCount + 1
  | .snd p => p.nodeCount + 1
  | .lam body => body.nodeCount + 1
  | .app fn arg => fn.nodeCount + arg.nodeCount + 1
  | .lift net => net.nodeCount + 1
  | .share value body => value.nodeCount + body.nodeCount + 1

/-- Number of primitive unary work nodes in a target. -/
def Net.workCount : Net Γ A -> Nat
  | .var _ => 0
  | .unit => 0
  | .lit _ => 0
  | .succ n => n.workCount + 1
  | .pair left right => left.workCount + right.workCount
  | .fst p => p.workCount
  | .snd p => p.workCount
  | .lam body => body.workCount
  | .app fn arg => fn.workCount + arg.workCount
  | .lift net => net.workCount
  | .share value body => value.workCount + body.workCount

/-- Number of explicit sharing binders. -/
def Net.shareCount : Net Γ A -> Nat
  | .var _ => 0
  | .unit => 0
  | .lit _ => 0
  | .succ n => n.shareCount
  | .pair left right => left.shareCount + right.shareCount
  | .fst p => p.shareCount
  | .snd p => p.shareCount
  | .lam body => body.shareCount
  | .app fn arg => fn.shareCount + arg.shareCount
  | .lift net => net.shareCount
  | .share value body => value.shareCount + body.shareCount + 1

/-- Untyped de Bruijn depth, used only to count graph references. -/
def Var.index : Var Γ A -> Nat
  | .zero => 0
  | .succ x => x.index + 1

/-- Number of references to de Bruijn depth `depth`.  Passing beneath a binder
increments the searched depth, so the count follows the same binding rather
than accidentally counting the new binder. -/
def Net.indexUses (depth : Nat) : Net Γ A -> Nat
  | .var x => if x.index = depth then 1 else 0
  | .unit => 0
  | .lit _ => 0
  | .succ n => n.indexUses depth
  | .pair left right => left.indexUses depth + right.indexUses depth
  | .fst p => p.indexUses depth
  | .snd p => p.indexUses depth
  | .lam body => body.indexUses (depth + 1)
  | .app fn arg => fn.indexUses depth + arg.indexUses depth
  | .lift net =>
      match depth with
      | 0 => 0
      | d + 1 => net.indexUses d
  | .share value body => value.indexUses depth + body.indexUses (depth + 1)

/-! ## A structure-preserving compiler -/

/-- Compile the source internal language to the target graph language.
Source `let1` becomes the explicit target sharing binder. -/
def compile : Tm Γ A -> Net Γ A
  | .var x => .var x
  | .unit => .unit
  | .lit n => .lit n
  | .succ n => .succ (compile n)
  | .pair left right => .pair (compile left) (compile right)
  | .fst p => .fst (compile p)
  | .snd p => .snd (compile p)
  | .lam body => .lam (compile body)
  | .app fn arg => .app (compile fn) (compile arg)
  | .let1 value body => .share (compile value) (compile body)

/-- The result type exposed by a target graph.  This projection is useful as
an explicit statement of the intrinsic type-preservation invariant. -/
def Net.resultTy (_ : Net Γ A) : Ty := A

/-- Compilation preserves the intrinsic result type exactly. -/
@[simp] theorem compile_resultTy (term : Tm Γ A) :
    (compile term).resultTy = A := rfl

/-- Compilation introduces no table or hidden global expansion: target size is
exactly source syntax size. -/
theorem compile_nodeCount (term : Tm Γ A) :
    (compile term).nodeCount = term.nodeCount := by
  induction term <;> simp [compile, Net.nodeCount, Tm.nodeCount, *]

/-- Semantic compiler correctness for all open terms and environments. -/
theorem compile_denote (term : Tm Γ A) (env : Env Γ) :
    (compile term).denote env = term.denote env := by
  induction term <;> simp [compile, Net.denote, Tm.denote, *] <;> (try funext x) <;>
    apply_assumption

/-! ## Typed local rewrite evidence -/

/-- A certificate for exactly one local interaction.  The root constructors are
the active rules; every other constructor is one edge of the address locating
that interaction.  Before and after share the same context and result type by
construction. -/
inductive LocalStep : {Γ : List Ty} -> {A : Ty} -> Net Γ A -> Net Γ A -> Type where
  | beta {Γ A B} (body : Net (A :: Γ) B) (arg : Net Γ A) :
      LocalStep (.app (.lam body) arg) (.share arg body)
  | eta {Γ A B} (fn : Net Γ (.arr A B)) :
      LocalStep (.lam (.app (.lift fn) (.var .zero))) fn
  | fstPair {Γ A B} (left : Net Γ A) (right : Net Γ B) :
      LocalStep (.fst (.pair left right)) left
  | sndPair {Γ A B} (left : Net Γ A) (right : Net Γ B) :
      LocalStep (.snd (.pair left right)) right
  | underSucc {Γ} {before after : Net Γ .nat} (step : LocalStep before after) :
      LocalStep (.succ before) (.succ after)
  | pairLeft {Γ A B} {before after : Net Γ A}
      (step : LocalStep before after) (right : Net Γ B) :
      LocalStep (.pair before right) (.pair after right)
  | pairRight {Γ A B} (left : Net Γ A) {before after : Net Γ B}
      (step : LocalStep before after) :
      LocalStep (.pair left before) (.pair left after)
  | underFst {Γ A B} {before after : Net Γ (.prod A B)}
      (step : LocalStep before after) :
      LocalStep (.fst before) (.fst after)
  | underSnd {Γ A B} {before after : Net Γ (.prod A B)}
      (step : LocalStep before after) :
      LocalStep (.snd before) (.snd after)
  | underLam {Γ A B} {before after : Net (A :: Γ) B}
      (step : LocalStep before after) :
      LocalStep (.lam before) (.lam after)
  | appFn {Γ A B} {before after : Net Γ (.arr A B)}
      (step : LocalStep before after) (arg : Net Γ A) :
      LocalStep (.app before arg) (.app after arg)
  | appArg {Γ A B} (fn : Net Γ (.arr A B)) {before after : Net Γ A}
      (step : LocalStep before after) :
      LocalStep (.app fn before) (.app fn after)
  | underLift {Γ A B} {before after : Net Γ A}
      (step : LocalStep before after) :
      LocalStep (Net.lift (B := B) before) (Net.lift (B := B) after)
  | shareValue {Γ A B} {before after : Net Γ A}
      (step : LocalStep before after) (body : Net (A :: Γ) B) :
      LocalStep (.share before body) (.share after body)
  | shareBody {Γ A B} (value : Net Γ A) {before after : Net (A :: Γ) B}
      (step : LocalStep before after) :
      LocalStep (.share value before) (.share value after)

/-- Intrinsic type preservation for a local certificate. -/
theorem localStep_resultTy {before after : Net Γ A}
    (_ : LocalStep before after) : before.resultTy = after.resultTy := rfl

/-- Every certificate contains one active rewrite, regardless of its address. -/
def LocalStep.rewriteCost {before after : Net Γ A}
    (_ : LocalStep before after) : Nat := 1

/-- Address depth of the unique active rewrite. -/
def LocalStep.addressDepth : {before after : Net Γ A} -> LocalStep before after -> Nat
  | _, _, .beta _ _ => 0
  | _, _, .eta _ => 0
  | _, _, .fstPair _ _ => 0
  | _, _, .sndPair _ _ => 0
  | _, _, .underSucc step => step.addressDepth + 1
  | _, _, .pairLeft step _ => step.addressDepth + 1
  | _, _, .pairRight _ step => step.addressDepth + 1
  | _, _, .underFst step => step.addressDepth + 1
  | _, _, .underSnd step => step.addressDepth + 1
  | _, _, .underLam step => step.addressDepth + 1
  | _, _, .appFn step _ => step.addressDepth + 1
  | _, _, .appArg _ step => step.addressDepth + 1
  | _, _, .underLift step => step.addressDepth + 1
  | _, _, .shareValue step _ => step.addressDepth + 1
  | _, _, .shareBody _ step => step.addressDepth + 1

/-- Every active rule, at every local address, preserves denotation. -/
theorem localStep_denote {before after : Net Γ A}
    (step : LocalStep before after) (env : Env Γ) :
    after.denote env = before.denote env := by
  induction step with
  | beta => rfl
  | eta => rfl
  | fstPair => rfl
  | sndPair => rfl
  | underSucc _ ih => simp only [Net.denote, ih]
  | pairLeft _ _ ih => simp only [Net.denote, ih]
  | pairRight _ _ ih => simp only [Net.denote, ih]
  | underFst _ ih => simp only [Net.denote, ih]
  | underSnd _ ih => simp only [Net.denote, ih]
  | underLam _ ih =>
      simp only [Net.denote]
      funext x
      exact ih (x, env)
  | appFn _ _ ih => simp only [Net.denote, ih]
  | appArg _ _ ih => simp only [Net.denote, ih]
  | underLift _ ih => simp only [Net.denote, ih]
  | shareValue _ _ ih => simp only [Net.denote, ih]
  | shareBody _ _ ih =>
      simp only [Net.denote]
      exact ih _

/-- A finite sequence of local certificates. -/
inductive Trace : Net Γ A -> Net Γ A -> Type where
  | refl (net : Net Γ A) : Trace net net
  | cons (step : LocalStep start middle) (tail : Trace middle finish) :
      Trace start finish

/-- Exact number of active rewrites in a trace. -/
def Trace.rewriteCost : {start finish : Net Γ A} -> Trace start finish -> Nat
  | _, _, .refl _ => 0
  | _, _, .cons step tail => step.rewriteCost + tail.rewriteCost

/-- Trace soundness: all reconstructed local interactions preserve meaning. -/
theorem trace_denote {start finish : Net Γ A} (trace : Trace start finish)
    (env : Env Γ) : finish.denote env = start.denote env := by
  induction trace with
  | refl => rfl
  | cons step tail ih => exact ih.trans (localStep_denote step env)

/-! ## Beta simulation through explicit sharing -/

/-- A source beta redex compiles to one target-local interaction whose result
contains the argument exactly once behind a sharing binder. -/
def betaSimulation (body : Tm (A :: Γ) B) (arg : Tm Γ A) :
    LocalStep (compile (.app (.lam body) arg))
      (.share (compile arg) (compile body)) :=
  .beta (compile body) (compile arg)

@[simp] theorem betaSimulation_cost (body : Tm (A :: Γ) B) (arg : Tm Γ A) :
    (betaSimulation body arg).rewriteCost = 1 := rfl

/-- The beta/share simulation theorem, stated against source denotation. -/
theorem betaSimulation_denote (body : Tm (A :: Γ) B) (arg : Tm Γ A)
    (env : Env Γ) :
    (Net.share (compile arg) (compile body)).denote env =
      (Tm.app (Tm.lam body) arg).denote env := by
  exact (localStep_denote (betaSimulation body arg) env).trans
    (compile_denote (.app (.lam body) arg) env)

/-- The explicit environment-lift node supports the usual extensional eta
interaction as one local step. -/
def etaExpansion (fn : Net Γ (.arr A B)) : Net Γ (.arr A B) :=
  .lam (.app (.lift fn) (.var .zero))

def etaSimulation (fn : Net Γ (.arr A B)) : LocalStep (etaExpansion fn) fn :=
  .eta fn

@[simp] theorem etaSimulation_cost (fn : Net Γ (.arr A B)) :
    (etaSimulation fn).rewriteCost = 1 := rfl

/-- Target eta preserves the full intensional function denotation, with no
enumeration of the domain. -/
theorem etaSimulation_denote (fn : Net Γ (.arr A B)) (env : Env Γ) :
    fn.denote env = (etaExpansion fn).denote env :=
  localStep_denote (etaSimulation fn) env

/-- Product beta is likewise one local typed interaction. -/
def fstSimulation (left : Tm Γ A) (right : Tm Γ B) :
    LocalStep (compile (.fst (.pair left right))) (compile left) :=
  .fstPair (compile left) (compile right)

/-! ## Exact sharing and cost specimen -/

namespace Reference

/-- Eight primitive operations stand in for an argument whose internal work
must not be duplicated by beta reduction. -/
def work : Nat -> Tm Γ .nat
  | 0 => .lit 0
  | n + 1 => .succ (work n)

def duplicateBody : Tm (.nat :: []) (.prod .nat .nat) :=
  .pair (.var .zero) (.var .zero)

def source : Tm [] (.prod .nat .nat) :=
  .app (.lam duplicateBody) (work 8)

def start : Net [] (.prod .nat .nat) := compile source

/-- The one-step beta target contains `work 8` once and two references to its
bound value. -/
def shared : Net [] (.prod .nat .nat) :=
  .share (compile (work 8)) (compile duplicateBody)

/-- Literal substitution is included only as a size/cost comparator. -/
def copied : Net [] (.prod .nat .nat) :=
  .pair (compile (work 8)) (compile (work 8))

def betaEvidence : LocalStep start shared := betaSimulation duplicateBody (work 8)

def betaTrace : Trace start shared := .cons betaEvidence (.refl shared)

theorem beta_is_one_local_rewrite : betaTrace.rewriteCost = 1 := by decide

theorem shared_has_one_binder : shared.shareCount = 1 := by decide

theorem shared_body_has_two_references :
    (compile duplicateBody).indexUses 0 = 2 := by decide

theorem shared_work_exact : shared.workCount = 8 := by decide

theorem copied_work_exact : copied.workCount = 16 := by decide

theorem shared_nodes_exact : shared.nodeCount = 13 := by decide

theorem copied_nodes_exact : copied.nodeCount = 19 := by decide

theorem beta_reduces_node_count : start.nodeCount = shared.nodeCount + 1 := by decide

theorem specimen_denotation : shared.denote PUnit.unit = (8, 8) := by decide

theorem beta_trace_sound : shared.denote PUnit.unit = start.denote PUnit.unit :=
  trace_denote betaTrace PUnit.unit

/-- Coordinate count of an extensional finite-field arrow table with `n` input
coordinates and `m` output coordinates.  This comparison formula is not used
by `compile`, `LocalStep`, or `Trace`. -/
def extensionalTableCoordinates (q inputCoordinates outputCoordinates : Nat) : Nat :=
  outputCoordinates * q ^ inputCoordinates

theorem duplicate_table_coordinates (q : Nat) :
    extensionalTableCoordinates q 1 2 = 2 * q := by
  simp [extensionalTableCoordinates]

/-- The graph cost is independent of field cardinality: for every `q`, the
same compiled shared target has exactly thirteen nodes. -/
theorem shared_cost_is_cardinality_parametric (_q : Nat) :
    shared.nodeCount = 13 := shared_nodes_exact

/-- From cardinality seven onward, even the coordinate spine of the matching
one-input/two-output extensional table is larger than the entire shared graph. -/
theorem shared_smaller_than_table_coordinates {q : Nat} (hq : 7 <= q) :
    shared.nodeCount < extensionalTableCoordinates q 1 2 := by
  rw [shared_nodes_exact, duplicate_table_coordinates]
  omega

end Reference

#assert_all_clean [
  compile_resultTy,
  compile_nodeCount,
  compile_denote,
  localStep_resultTy,
  localStep_denote,
  trace_denote,
  betaSimulation_cost,
  betaSimulation_denote,
  etaSimulation_cost,
  etaSimulation_denote,
  Reference.beta_is_one_local_rewrite,
  Reference.shared_has_one_binder,
  Reference.shared_body_has_two_references,
  Reference.shared_work_exact,
  Reference.copied_work_exact,
  Reference.shared_nodes_exact,
  Reference.copied_nodes_exact,
  Reference.beta_reduces_node_count,
  Reference.specimen_denotation,
  Reference.beta_trace_sound,
  Reference.duplicate_table_coordinates,
  Reference.shared_cost_is_cardinality_parametric,
  Reference.shared_smaller_than_table_coordinates
]

end Dregg2.Calculus.IntensionalCCCTrace
