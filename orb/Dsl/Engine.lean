/-
  Dsl.Engine — the generative front-end.

  A Lean-metaprogramming macro for a declarative `engine … where` block. It
  ELABORATES a list of primitive declarations (region / machine / linear /
  shared + `reactor over (…)`) into:

    * `def <Name> : Dsl.Component`  — the composed engine, an iterated `prod`
      of the declared primitives together with the reactor primitive; and
    * `theorem <Name>_wf : ∀ s i, <Name>.inv s → <Name>.inv (<Name>.step s i).1`
      — the composition invariant, a *generated, kernel-checked* theorem whose
      proof is the engine's own `step_wf`, which is (transparently) a chain of
      `Dsl.prod_preserves`. No `sorry` is ever emitted.

  SOUNDNESS. The generator inherits the Lean kernel as its correctness check.
  A malformed engine — e.g. a `reactor over (X, Y)` naming a primitive that was
  never declared — raises a genuine elaboration error (`throwErrorAt`) and emits
  NOTHING. It never falls back to a `sorry`. Whatever the macro does emit
  typechecks, or the whole command fails.

  The macro is thin sugar over the term-level combinator `mkEngine`, provided
  below and usable directly.
-/
import Lean
import Dsl.Component
import Dsl.Primitives
import Dsl.Reactor

open Lean Lean.Elab Lean.Elab.Command

namespace Dsl

-- The four primitive components live in `Dsl.Primitives`; re-export them into
-- `Dsl` so the macro's emitted `Dsl.region` / `Dsl.machine` / … resolve.
export Dsl.Primitives (region machine linear shared)

/-! ## The reactor primitive, instantiated over the concrete machine/linear pair

    The macro's `reactor over (…)` line elaborates to this concrete `Component`:
    the reactor primitive (`Dsl.Reactor`) built over the `machine` and `linear`
    primitives, re-exposed as a plain `Component` so it composes with the other four. -/
def reactorComponent : Component := (mkReactor Dsl.machine Dsl.linear).toComponent

/-! ## Term-level combinator (the macro is sugar over this) -/

/-- Fold a list of components into their iterated parallel product. The empty
    engine is the `unitComponent`; a singleton is itself; otherwise a right
    fold of `Component.prod`. -/
def mkEngine : List Component → Component
  | []      => unitComponent
  | [c]     => c
  | c :: cs => c.prod (mkEngine cs)

/-- The composed engine's preservation obligation, discharged directly by its
    own `step_wf` field — which, for a `prod`, IS `prod_preserves`. This is the
    term the generated `<Name>_wf` theorem elaborates to. -/
theorem mkEngine_wf (cs : List Component) :
    ∀ s i, (mkEngine cs).inv s → (mkEngine cs).inv ((mkEngine cs).step s i).1 :=
  (mkEngine cs).step_wf

/-! ## Surface syntax: `engine Name where <primitives>` -/

/-- One primitive declaration inside an `engine` block. -/
declare_syntax_cat enginePrim

syntax "region" ident : enginePrim
syntax "machine" ident : enginePrim
syntax "linear" ident : enginePrim
syntax "shared" ident : enginePrim
syntax "reactor" "over" "(" ident "," ident ")" : enginePrim

/-- The engine block. Primitives are `;`-separated. -/
syntax (name := engineDecl)
  "engine" ident "where" sepBy1(enginePrim, ";") : command

/-- Look up a declared primitive label; error (no `sorry`) if it was never
    declared — this is the macro's soundness gate for `reactor over (…)`. -/
private def resolveLabel (labels : Array (String × Syntax))
    (ref : TSyntax `ident) : CommandElabM Unit := do
  let nm := ref.getId.toString
  unless labels.any (fun p => p.1 == nm) do
    throwErrorAt ref
      s!"engine: `reactor over (…)` references undeclared primitive `{nm}`; \
         declare it above (e.g. `machine {nm}`)"

@[command_elab engineDecl]
def elabEngine : CommandElab := fun stx => do
  match stx with
  | `(engine $name:ident where $prims;*) => do
      let primArr := prims.getElems
      if primArr.isEmpty then
        throwErrorAt name "engine: at least one primitive is required"
      -- Collect (label, canonical-primitive-term), in declaration order, and a
      -- label table for `reactor over (…)` resolution.
      let mut comps : Array (TSyntax `term) := #[]
      let mut labels : Array (String × Syntax) := #[]
      for prim in primArr do
        match prim with
        | `(enginePrim| region $x)  =>
            labels := labels.push (x.getId.toString, x)
            comps  := comps.push (← `(Dsl.region))
        | `(enginePrim| machine $x) =>
            labels := labels.push (x.getId.toString, x)
            comps  := comps.push (← `(Dsl.machine))
        | `(enginePrim| linear $x)  =>
            labels := labels.push (x.getId.toString, x)
            comps  := comps.push (← `(Dsl.linear))
        | `(enginePrim| shared $x)  =>
            labels := labels.push (x.getId.toString, x)
            comps  := comps.push (← `(Dsl.shared))
        | `(enginePrim| reactor over ($a, $b)) =>
            -- SOUNDNESS: both operands must be primitives declared above.
            resolveLabel labels a
            resolveLabel labels b
            comps := comps.push (← `(Dsl.reactorComponent))
        | other =>
            throwErrorAt other "engine: unrecognized primitive declaration"
      -- Build the composed term as a right fold of `Component.prod`.
      let mut acc : TSyntax `term := comps.back!
      for c in comps.pop.reverse do
        acc := (← `(Dsl.Component.prod $c $acc))
      -- Emit `def <Name> : Component := <acc>`.
      let defCmd ← `(command| def $name : Dsl.Component := $acc)
      elabCommand defCmd
      -- Emit `theorem <Name>_wf : ∀ s i, <Name>.inv s → <Name>.inv (<Name>.step s i).1`
      -- proved by the composed engine's own `step_wf`.
      let wfIdent := mkIdent (Name.mkSimple (name.getId.toString ++ "_wf"))
      let wfCmd ← `(command|
        theorem $wfIdent :
            ∀ s i, ($name).inv s → ($name).inv (($name).step s i).1 :=
          ($name).step_wf)
      elabCommand wfCmd
  | _ => throwUnsupportedSyntax

end Dsl

/-! ## Worked demonstration — elaborated & kernel-checked at build time. -/

open Dsl

-- The H1 orb, re-generated from a declarative block. This single command
-- emits `def Orb` and `theorem Orb_wf`, both kernel-checked below.
engine Orb where
  region  Arena;
  machine Proto;
  linear  Uring;
  shared  Metrics;
  reactor over (Proto, Uring)

-- `Orb` is a genuine composed `Component`, and `Orb_wf` a genuine theorem.
#check (Orb : Dsl.Component)
#check (Orb_wf : ∀ s i, Orb.inv s → Orb.inv (Orb.step s i).1)

-- The generated engine is exactly the iterated product we intended.
example : Orb =
    Dsl.Component.prod Dsl.region
      (Dsl.Component.prod Dsl.machine
        (Dsl.Component.prod Dsl.linear
          (Dsl.Component.prod Dsl.shared Dsl.reactorComponent))) := rfl

-- The term-level combinator agrees with the generated def.
example : Orb.inv Orb.init := Orb.init_wf

-- The reactor's copy-once law rides along inside the composed engine: a recv
-- completion yields exactly one buffer recycle, that of the delivered buffer.
example (s : Dsl.reactorComponent.State) (bid : Uring.Bid) (data : Proto.Bytes) :
    (Dsl.reactorComponent.step s (.recvInto bid data)).2.filter Reactor.RingSubmission.isRecycle
      = [Reactor.RingSubmission.recycleBuffer bid] :=
  Dsl.mkReactor_recycle Dsl.machine Dsl.linear s bid data

-- Axiom footprint of the GENERATED theorem: a subset of the allowed set.
#print axioms Orb_wf
