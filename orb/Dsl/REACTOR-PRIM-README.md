# Dsl/Reactor.lean — the reactor primitive (DSL primitive #5)

Promotes the hand-built reactor (`Reactor/Contract.lean`) to a first-class,
`Component`-level shape carrying the event-loop discipline. This is the primitive the
`engine … where … reactor over (…)` macro instantiates.

Status: **verified green, zero sorries.** Axiom footprint of the two required theorems
is a subset of `{propext, Quot.sound, Classical.choice}` — in fact only `propext`
appears (`reactor_prim_wf` uses no axioms at all).

## What it defines

- `Dsl.ReactorComponent` — a `Component` specialized to the ring event loop:
  `Input = RingEvent`, `Output = RingSubmission`, carrying its `machine` and `linear`
  sub-components plus `inv/init/step/init_wf/step_wf`.
- `ReactorComponent.toComponent : ReactorComponent → Component` — re-exposes the
  primitive as a plain `Component` so it composes with the other four primitives via
  `Component.prod`.
- `Dsl.Wiring (m l : Component)` — the region/lease bridges that specialize an abstract
  machine/linear pair to the ring's event alphabet:
  - `feed  : RingEvent → Option m.Input`  (region-parse feeds the machine)
  - `drive : m.Output → List RingOp`       (the machine drives submissions)
  - `lease : RingEvent → Option l.Input`   (buffer-lease bookkeeping)
  - `drive_no_recycle` — the load-bearing field: the machine emits sends / re-arms /
    closes but **never** a `recycle`. Buffer recycling is owned by the reactor shell.
    This is exactly why the copy-once law is *structural* — the recycle count never
    depends on what the machine does.
- `Dsl.mkReactorWith (m l) (w) : ReactorComponent` — `reactor over (m, l)` with explicit
  wiring; **this is what the macro/emit lanes call** (they know the real bridges).
- `Dsl.mkReactor (m l) : ReactorComponent` — the bare task-signature constructor
  `reactor over (machine, linear)`. Total for **any** machine/linear pair via
  `defaultWiring` (the shell still supplies the copy-once recycle).

## The theorems

- `reactor_prim_recycle (m l w s conn bufId len)` — a `recv` event yields **exactly one**
  recycle, for any machine/linear pair and any wiring. This generalizes
  `Reactor.recv_recycles_exactly_once` (the hand-built echo instance) to the whole
  family. Proof strategy: the step's output ops are `(feedMachine …).2 ++ recycleOps ev`;
  the machine batch has no recycle (`drive_no_recycle`), and `recycleOps (recv …) =
  [recycle bufId]`, so `recycleCount = 0 + 1 = 1`.
- `reactor_prim_no_recycle (m l w s ev h)` — the negative half: a non-`recv` event yields
  no recycle (`recycleOps ev = []`).
- `reactor_prim_wf (m l w s ev h)` — the composed invariant `m.inv ∧ l.inv` is preserved
  by one reactor step, for any machine/linear pair, any wiring, any event. Follows from
  `m.step_wf` and `l.step_wf` factored through `feedMachine_wf`/`feedLinear_wf`.
- Corollaries `mkReactor_recycle` / `mkReactor_no_recycle` / `mkReactor_wf` restate the
  three for the bare `mkReactor m l` call site.
- A closing `example` witnesses that `Reactor.refStep` (the reference) is one instance of
  the generalized law.

## Design decision: why `mkReactor m l` is total and where wiring comes from

The task signature is `mkReactor (machine) (linear) : ReactorComponent`. But the machine
and linear are *arbitrary* `Component`s with arbitrary `Input` types — the reactor cannot
manufacture a machine input from a `RingEvent` without a bridge. Two constructors resolve
this without weakening the theorems:

- `mkReactorWith m l w` takes the region/lease `Wiring` explicitly. The macro emits this
  form because at instantiation it knows the concrete bridges (region parse, the machine's
  send-encoder, the lease commands). All three theorems are proved here, quantified over
  `w`, so they hold for **every** real wiring.
- `mkReactor m l = mkReactorWith m l (defaultWiring m l)` gives the exact two-argument
  signature, total for any pair. Because the copy-once recycle is owned by the shell (not
  the wiring), `mkReactor`'s recycle/wf laws are non-trivial and follow as corollaries.

The copy-once law being structural (independent of `m`, `l`, and `w`) is the whole point:
it is what lets the generator emit `recv_recycles_exactly_once` **by construction** for any
lib the DSL wires in, rather than re-proving it per engine.

## Foundation interface this file consumes (integration contract)

`Dsl/Reactor.lean` is `import Dsl.Component` + `import Reactor.Contract`. It depends only
on this surface; if the sibling-owned real modules match it, the file compiles unchanged.

From `Dsl.Component` (namespace `Dsl`):
- `structure Component` with fields `State Input Output : Type/Sort`, `inv : State → Prop`,
  `init : State`, `step : State → Input → State × Output`, `init_wf : inv init`,
  `step_wf : ∀ s i, inv s → inv (step s i).1`.

From `Reactor.Contract` (namespace `Reactor`):
- `inductive RingEvent` with a `recv (conn bufId len : Nat)` constructor and
  `RingEvent.isRecv : RingEvent → Bool` (true only on `recv`).
- `inductive RingOp` with `recycle (bufId : Nat)` and `RingOp.isRecycle : RingOp → Bool`.
- `structure RingSubmission` with field `ops : List RingOp`.
- `def RingSubmission.recycleCount := (·.ops.filter RingOp.isRecycle).length`.
- `theorem Reactor.recv_recycles_exactly_once` (the reference, subsumed by
  `reactor_prim_recycle`).

If a sibling's real `RingOp`/`RingSubmission` shape differs (e.g. `recycleCount` defined via
`countP`, or `RingSubmission` is a bare `List RingOp`), the only edits needed are the three
recycle-algebra lemmas at the top of the file (`filter_isRecycle_len_zero`,
`recycleCount_append`, `recycleCount_recycle`); the primitive, constructors, and the two
headline theorems are unchanged.

## Verification note

At authoring time the sibling-owned `Dsl/Component.lean` and `Reactor/Contract.lean` had not
landed in the tree and there was no root lake project, so a repo-root `lake build` cannot run
yet. The file was verified in a self-contained lake project (Lean v4.17.0, core-only) that
reconstructs the documented foundation interface above; `lake build` is green, `#print axioms`
on all public defs/theorems is within `{propext, Quot.sound, Classical.choice}`, and the file
contains no `sorry`/`admit`/`native_decide`/`axiom`. Once the real foundation modules land at
`Dsl/Component.lean` and `Reactor/Contract.lean`, this file compiles against them under the
same toolchain with no changes (barring the shape caveat above).
