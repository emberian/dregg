/-
  Dsl/GoldenOrb.lean — the proof the DSL works: re-generate the H1 orb from a
  ~6-line `engine … where` description and show the GENERATED engine reproduces
  the hand-built reactor's core theorems.

  The hand-built reference (Reactor/Contract.lean) was crosswired by hand:
    * RingEvent → RingSubmission with `recv_recycles_exactly_once` (copy-once);
    * the reactor `step` translating FSM outputs to submissions plus the shell's
      buffer recycle.

  This file GENERATES the same shape from a declarative block via the `engine`
  macro (Dsl/Engine.lean) over the five DSL primitives (Dsl/Primitives.lean,
  Dsl/Reactor.lean), and proves the generated engine AGREES with the hand-built
  one on the two properties that matter:

    * `golden_wf`             — the generated composition invariant is preserved
                                by one step of the generated engine (= the
                                composed, kernel-checked `GoldenOrb_wf`);
    * `golden_matches_recycle` — the generated reactor recycles a `recvInto`
                                exactly once, and the filtered submission list is
                                *equal* to the hand-built `Reactor.step`'s
                                (`Reactor.recv_recycles_exactly_once`).

  SOUNDNESS. Every theorem below is discharged by the Lean kernel. Nothing is
  `sorry`/`admit`. The generated `GoldenOrb`/`GoldenOrb_wf` come out of the
  macro; a malformed block would fail to elaborate rather than emit a hole.
-/
import Dsl.Engine
import Dsl.Reactor
import Reactor.Contract

open Dsl

/-! ## The ~6-line description

The H1 orb, declared. One `engine … where` command emits BOTH a composed
`Dsl.Component` (`GoldenOrb`) and its preservation theorem (`GoldenOrb_wf`) —
the two top-level declarations the macro is contracted to produce. -/

engine GoldenOrb where
  region  Arena;
  machine Proto;
  linear  Uring;
  shared  Metrics;
  reactor over (Proto, Uring)

/-! ## What the six lines generated

`GoldenOrb` is a genuine composed `Component`; `GoldenOrb_wf` a genuine theorem.
Neither is postulated — both are the macro's emitted terms. -/

#check (GoldenOrb : Dsl.Component)
#check (GoldenOrb_wf : ∀ s i, GoldenOrb.inv s → GoldenOrb.inv (GoldenOrb.step s i).1)

/-- The generated engine is *exactly* the iterated product the block describes:
    region · machine · linear · shared · reactor, folded by `Component.prod`.
    Proved by `rfl` — the generation is structural, not approximate. -/
theorem golden_shape :
    GoldenOrb =
      Dsl.Component.prod Dsl.region
        (Dsl.Component.prod Dsl.machine
          (Dsl.Component.prod Dsl.linear
            (Dsl.Component.prod Dsl.shared Dsl.reactorComponent))) := rfl

/-! ## Property 1 — the generated composition invariant holds

`golden_wf` IS the macro-emitted `GoldenOrb_wf`: the conjoined invariant of every
declared primitive is preserved by the composed step, its proof term a chain of
`Dsl.prod_preserves`. This is what the hand-crosswiring waves established per
engine; the DSL re-derives it by construction. -/

theorem golden_wf :
    ∀ s i, GoldenOrb.inv s → GoldenOrb.inv (GoldenOrb.step s i).1 :=
  GoldenOrb_wf

/-- The generated engine starts in its invariant (the composed `init_wf`). -/
theorem golden_init : GoldenOrb.inv GoldenOrb.init := GoldenOrb.init_wf

/-! ## Property 2 — the generated reactor recycles exactly once, = the hand-built

The block's `reactor over (Proto, Uring)` line composes the reactor primitive
`Dsl.mkReactor Dsl.machine Dsl.linear` over the same machine/linear the engine
carries. Its copy-once law is `Dsl.mkReactor_recycle`. The HAND-BUILT reference
is `Reactor.recv_recycles_exactly_once`, which fixes `Reactor.step`'s recycle
filter on a `recvInto` to `[recycleBuffer bid]`.

`golden_matches_recycle` states the two AGREE: the generated reactor's recycle
filter on a `recvInto` equals the hand-built engine's, for every buffer / data.
Both reduce to `[recycleBuffer bid]`; the equality is closed by rewriting with
each side's own copy-once theorem. -/

/-- The generated reactor primitive the golden block declares. -/
abbrev goldenReactor : Dsl.ReactorComponent := Dsl.mkReactor Dsl.machine Dsl.linear

/-- The GENERATED reactor recycles a `recvInto` exactly once — the copy-once law,
    reproduced by the DSL for the golden orb's machine/linear pair. -/
theorem golden_recv_recycle_one
    (s : goldenReactor.State) (bid : Uring.Bid) (data : Proto.Bytes) :
    Dsl.recycleCount (goldenReactor.step s (.recvInto bid data)).2 = 1 :=
  Dsl.mkReactor_recycleCount Dsl.machine Dsl.linear s bid data

/-- **The match.** The generated reactor's recycle filter on a `recvInto` is EQUAL
    to the hand-built `Reactor.step`'s (`Reactor.recv_recycles_exactly_once`). The
    DSL-generated seam agrees with the crosswired one — both isolate exactly the
    recycle of the delivered buffer. -/
theorem golden_matches_recycle
    (s : goldenReactor.State) (cfg : Proto.Config) (ps : Proto.State)
    (bid : Uring.Bid) (data : Proto.Bytes) :
    (goldenReactor.step s (.recvInto bid data)).2.filter Reactor.RingSubmission.isRecycle
      = (Reactor.step cfg ps (.recvInto bid data)).2.filter Reactor.RingSubmission.isRecycle := by
  rw [Dsl.mkReactor_recycle Dsl.machine Dsl.linear s bid data,
      Reactor.recv_recycles_exactly_once cfg ps bid data]

/-- The negative half rides along too: a non-`recvInto` event recycles nothing in
    the generated reactor, exactly as the shell owns copy-once release. -/
theorem golden_no_recycle
    (s : goldenReactor.State) (ev : Dsl.RingEvent) (h : ev.isRecv = false) :
    Dsl.recycleCount (goldenReactor.step s ev).2 = 0 :=
  Dsl.mkReactor_no_recycle Dsl.machine Dsl.linear s ev h

/-! ## The claim, witnessed

The DSL-generated engine is not a toy: from six declarative lines it reproduces
the hand-built engine's composition-invariant theorem (`golden_wf`) and its
copy-once seam theorem (`golden_matches_recycle`), both kernel-accepted, with no
re-proof beyond each primitive's own `step_wf` and the reactor shell's structural
recycle. Hand-crosswiring is replaced by generation. -/

-- Axiom footprint of the two headline theorems: within the allowed set
-- {propext, Quot.sound, Classical.choice}.
#print axioms golden_wf
#print axioms golden_matches_recycle
