# Dsl.Engine — the `engine … where` generative front-end

`Dsl/Engine.lean` is the Lean-metaprogramming macro that turns a declarative
`engine … where` block into a **composed, kernel-checked** network engine: one
command emits a `Component` def *and* its preservation theorem. It is the
generation mechanism the DSL design calls for — new libraries connect by adding
a line, not by hand-crosswiring.

Built for Lean 4 `v4.17.0`, **core only** (uses `import Lean` —
`Lean.Elab`/`Lean.Syntax`/`Lean.Macro` — no Mathlib).

## What a worked block generates

```lean
open Dsl

engine Orb where
  region  Arena;
  machine Proto;
  linear  Uring;
  shared  Metrics;
  reactor over (Proto, Uring)
```

This single command elaborates to **two top-level declarations**:

```lean
-- (1) the composed engine: an iterated `prod` of the declared primitives
--     plus the reactor primitive
def Orb : Dsl.Component :=
  Dsl.Component.prod Dsl.region
    (Dsl.Component.prod Dsl.machine
      (Dsl.Component.prod Dsl.linear
        (Dsl.Component.prod Dsl.shared Dsl.reactorComponent)))

-- (2) the generated composition-invariant theorem, proved by the engine's own
--     `step_wf` — which, for a `prod`, IS `Dsl.prod_preserves`. No `sorry`.
theorem Orb_wf :
    ∀ s i, Orb.inv s → Orb.inv (Orb.step s i).1 :=
  Orb.step_wf
```

`Orb_wf` is a **real, kernel-accepted** theorem: the conjoined invariant of every
declared primitive is preserved by the composed step, with no re-proof beyond
each primitive's own `step_wf`. Its proof term chains `Dsl.prod_preserves`
through the product tree.

The naming rule is mechanical: `engine <Name>` emits `def <Name>` and
`theorem <Name>_wf`.

## The primitive clauses

| Clause                        | Emits (canonical primitive term) |
| ----------------------------- | -------------------------------- |
| `region  <label>`             | `Dsl.region`                     |
| `machine <label>`             | `Dsl.machine`                    |
| `linear  <label>`             | `Dsl.linear`                     |
| `shared  <label>`             | `Dsl.shared`                     |
| `reactor over (<lbl>, <lbl>)` | `Dsl.reactorComponent`           |

Primitives are `;`-separated inside the block. The two operands of
`reactor over (…)` must name primitives **declared earlier in the same block**;
this is the reactor's copy-once seam (`RingEvent → RingSubmission`,
`recv_recycles_exactly_once`) riding along inside the composite.

## Soundness — a bad generation FAILS to typecheck, never `sorry`

The generator inherits the Lean kernel as its correctness check. Two rejection
paths, both verified:

- **Undeclared reactor operand** — `reactor over (Nope, Missing)` with no
  matching primitive above raises
  `error: engine: reactor over (…) references undeclared primitive Nope …`
  via `throwErrorAt`, and emits **nothing**.
- **Unknown primitive keyword** — `frobnicate X` is rejected at parse time:
  `error: unexpected identifier; expected enginePrim`.

There is no `sorry` fallback anywhere. Whatever the macro emits typechecks, or
the whole command fails.

## The term-level combinator (macro is thin sugar over it)

```lean
def Dsl.mkEngine : List Dsl.Component → Dsl.Component
  | []      => Dsl.unitComponent          -- the composition identity
  | [c]     => c
  | c :: cs => c.prod (Dsl.mkEngine cs)

theorem Dsl.mkEngine_wf (cs : List Dsl.Component) :
    ∀ s i, (Dsl.mkEngine cs).inv s → (Dsl.mkEngine cs).inv ((Dsl.mkEngine cs).step s i).1 :=
  (Dsl.mkEngine cs).step_wf
```

The macro builds the same iterated product as a flat term (nicer generated
`def`), but `mkEngine` is available directly for programmatic composition.

## Interface consumed from the foundation modules

`Engine.lean` imports `Dsl.Component`, `Dsl.Primitives`, `Dsl.Reactor` and
depends on exactly these names (the agreed calculus surface):

- `Dsl.Component` (structure with `State/Input/Output/inv/init/step/init_wf/step_wf`)
- `Dsl.Component.prod`, `Dsl.prod_preserves`, `Dsl.unitComponent`
- primitives `Dsl.region`, `Dsl.machine`, `Dsl.linear`, `Dsl.shared`
- reactor `Dsl.reactorComponent`, `Dsl.RingEvent`, `Dsl.recv_recycles_exactly_once`

If a sibling module exposes one of these under a different identifier,
integration is a one-line rename in the emission strings — the mechanism is
unaffected.

## Verification

`lake build` green; zero `sorry`/`admit`. Axiom footprint of the generated
theorem is within the allowed set `{propext, Quot.sound, Classical.choice}`:

```
'Orb'                             depends on axioms: [propext]
'Orb_wf'                          depends on axioms: [propext]
'Dsl.prod_preserves'             does not depend on any axioms
'Dsl.reachable_inv'              does not depend on any axioms
'Dsl.recv_recycles_exactly_once' depends on axioms: [propext]
```

The demonstration at the bottom of `Engine.lean` is checked at build time:
`#check Orb`, `#check Orb_wf`, an `example … := rfl` proving the generated def is
exactly the intended product tree, and `#print axioms Orb_wf`.

### Scope of the v1 delivery

This is emit-lean end to end: the macro re-generates the composed model and its
seam theorem, kernel-accepted. `emit-pancake` / `emit-hol4` (the rest of the
full triple) are the follow-on — the generation *mechanism* is proven here on
the primitives that already carry their preservation theorem.
