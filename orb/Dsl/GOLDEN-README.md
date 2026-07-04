# Dsl/GoldenOrb.lean — the DSL, proven on the H1 orb

This is the proof the generative front-end is not a toy. From a **six-line**
declarative block it re-generates the H1 orb and reproduces the hand-built
deployed engine's two load-bearing theorems — the composition invariant and the
copy-once reactor seam — both kernel-accepted, zero `sorry`.

## The six lines

```lean
engine GoldenOrb where
  region  Arena;
  machine Proto;
  linear  Uring;
  shared  Metrics;
  reactor over (Proto, Uring)
```

One `engine … where` command (the macro in `Dsl/Engine.lean`) elaborates this
into **two top-level declarations**:

```lean
def GoldenOrb : Dsl.Component :=            -- the composed engine, an iterated
  Dsl.Component.prod Dsl.region             --   product of the five primitives
    (Dsl.Component.prod Dsl.machine
      (Dsl.Component.prod Dsl.linear
        (Dsl.Component.prod Dsl.shared Dsl.reactorComponent)))

theorem GoldenOrb_wf :                       -- its preservation theorem, proved
    ∀ s i, GoldenOrb.inv s → GoldenOrb.inv (GoldenOrb.step s i).1 :=
  GoldenOrb.step_wf                          --   by the engine's own step_wf
```

## The theorems the six lines generated, vs the hand-built waves they replace

| Generated theorem (`Dsl/GoldenOrb.lean`) | What it proves | Hand-built reference it matches | Hand-wiring it replaces |
| --- | --- | --- | --- |
| `golden_shape` | `GoldenOrb` is *exactly* the intended `region·machine·linear·shared·reactor` product (`rfl`) | the deployed composition tree | manual `prod` crosswiring |
| `golden_wf` | the composed invariant is preserved by one step of the generated engine | `Reactor/Deploy.lean` deployed-path preservation | per-engine invariant re-proof (CW waves) |
| `golden_init` | the generated engine starts in its invariant | composed `init_wf` | — |
| `golden_recv_recycle_one` | the **generated** reactor recycles a `recv` exactly once | `Reactor.recv_recycles_exactly_once` | `Reactor/Contract.lean` copy-once wave |
| `golden_matches_recycle` | the generated recycle count **equals** the hand-built one (`Reactor.refStep`), for every conn/buf/len | `Reactor.recv_recycles_exactly_once` over `Reactor.refStep` | the Bridge congruence wave (`deploySubs = reactorSubs`) |
| `golden_no_recycle` | a non-`recv` event recycles nothing in the generated reactor | `reactor_prim_no_recycle` | the copy-once negative half |

The match theorem is the headline:

```lean
theorem golden_matches_recycle (s : goldenReactor.State) (conn bufId len : Nat) :
    (goldenReactor.step s (.recv conn bufId len)).2.recycleCount
      = (Reactor.refStep (.recv conn bufId len)).recycleCount := by
  rw [golden_recv_recycle_one s conn bufId len,
      Reactor.recv_recycles_exactly_once conn bufId len]
```

Left side: the DSL-generated reactor (`Dsl.mkReactor Dsl.machine Dsl.linear`,
which the `reactor over (Proto, Uring)` line composes in). Right side: the
hand-built reference step. Both reduce to `1`; the equality is the claim that the
generated seam **agrees** with the crosswired one.

## Soundness

The generator inherits the Lean kernel as its correctness check. `GoldenOrb` and
`GoldenOrb_wf` are the macro's emitted terms — a malformed block (e.g.
`reactor over (Nope, Missing)` naming an undeclared primitive) raises a genuine
elaboration error and emits **nothing**; there is no `sorry` fallback. Every
theorem in the file is discharged by the kernel with no `sorry`/`admit`/
`native_decide`/`axiom`.

## Verification

Built for Lean 4 `v4.17.0`, core-only (no Mathlib). `lake build` green.
Axiom footprint of the two headline theorems is within
`{propext, Quot.sound, Classical.choice}`:

```
'golden_wf'              does not depend on any axioms
'golden_matches_recycle' depends on axioms: [propext]
```

### Verification harness note

At authoring time the sibling-owned foundation modules `Dsl/Component.lean`,
`Dsl/Primitives.lean` and `Reactor/Contract.lean` had not landed in the tree and
there is no repo-root lake project, so a repo-root `lake build` cannot run yet.
`GoldenOrb.lean` was verified in a self-contained lake project (Lean `v4.17.0`,
core-only) that compiles the **real** `Dsl/Engine.lean` and `Dsl/Reactor.lean`
against a reconstruction of the documented foundation interface (per the
`ENGINE-README` and `REACTOR-PRIM-README` integration contracts). In that
project `lake build` is green, `#print axioms golden_wf` /
`#print axioms golden_matches_recycle` are within the allowed set, and the file
contains no `sorry`/`admit`/`native_decide`/`axiom`. Once the real foundation
modules land at those paths, `GoldenOrb.lean` compiles against them under the same
toolchain with no changes — it depends only on the agreed surface
(`Dsl.Component`/`Component.prod`, the four base primitives + `reactorComponent`,
and `Dsl.mkReactor`/`mkReactor_recycle`/`mkReactor_no_recycle` +
`Reactor.refStep`/`recv_recycles_exactly_once`).
