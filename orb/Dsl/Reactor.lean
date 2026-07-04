/-
  Dsl/Reactor.lean — the 5th DSL primitive: the reactor as a first-class Component-shape.

  A `ReactorComponent` is a `Dsl.Component` whose `Input = RingEvent` and
  `Output = RingSubmission`, carrying the event-loop discipline the hand-built
  `Reactor.step` proved by hand — the copy-once law — but now as a primitive that
  composes an arbitrary machine-Component and linear-Component.

  `reactor over (m, l)` (constructor `mkReactor m l`, or `mkReactorWith m l w` with
  explicit region/lease wiring) builds a Component where:
    * the region-parse feeds the machine   (Wiring.feed  : RingEvent → Option m.Input)
    * the machine drives submissions        (Wiring.drive : m.Output → List RingSubmission)
    * the linear resource is the buffer lease (Wiring.lease : RingEvent → Option l.Input)
  and recycle-exactly-once holds BY CONSTRUCTION for ANY machine/linear pair: the
  reactor shell — not the machine — owns the single `recycleBuffer` submission, so
  the count is structural.

  THEOREMS
    * reactor_prim_recycle : a `recvInto` event yields exactly one recycle —
      `(step …).2.filter RingSubmission.isRecycle = [recycleBuffer bid]` — for any
      machine/linear pair + any wiring (generalizes
      `Reactor.recv_recycles_exactly_once`).
    * reactor_prim_wf      : the composed invariant (m.inv ∧ l.inv) is preserved.

  This is the shape the `engine … where … reactor over (…)` macro instantiates.
-/
import Dsl.Component
import Reactor.Contract

namespace Dsl

open Reactor (RingEvent RingSubmission)

/-- Re-export the ring alphabet into the `Dsl` namespace so the macro and the
    golden test can name `Dsl.RingEvent` / `Dsl.RingSubmission`. -/
abbrev RingEvent := Reactor.RingEvent
abbrev RingSubmission := Reactor.RingSubmission

/-- Is this event a recv completion (the only event the shell recycles for)? -/
def RingEvent.isRecv : RingEvent → Bool
  | .recvInto _ _ => true
  | _             => false

/-! ### The composition identity -/

/-- The unit component — a single-state, output-free component, the identity of
    the parallel product and the empty engine's value. -/
def unitComponent : Component where
  State   := Unit
  Input   := Unit
  Output  := Unit
  inv     := fun _ => True
  init    := ()
  step    := fun _ _ => ((), [])
  init_wf := trivial
  step_wf := fun _ _ _ => trivial

/-! ### Recycle-count algebra on submission batches -/

/-- The number of buffer-recycle submissions in a batch (copy-once ⇒ at most one
    per event). Counting is the real `RingSubmission.isRecycle` Bool + list-filter. -/
def recycleCount (subs : List RingSubmission) : Nat :=
  (subs.filter Reactor.RingSubmission.isRecycle).length

/-- Recycle count distributes over concatenation of batches. -/
theorem recycleCount_append (xs ys : List RingSubmission) :
    recycleCount (xs ++ ys) = recycleCount xs + recycleCount ys := by
  simp [recycleCount, List.filter_append, List.length_append]

/-- A batch of non-recycle submissions has empty recycle-filter. -/
theorem filter_isRecycle_nil (xs : List RingSubmission)
    (h : ∀ s ∈ xs, Reactor.RingSubmission.isRecycle s = false) :
    xs.filter Reactor.RingSubmission.isRecycle = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro s hs
  simp [h s hs]

/-- A batch with no recycle submission recycles nothing. -/
theorem recycleCount_no (xs : List RingSubmission)
    (h : ∀ s ∈ xs, Reactor.RingSubmission.isRecycle s = false) :
    recycleCount xs = 0 := by
  simp [recycleCount, filter_isRecycle_nil xs h]

/-- A lone `recycleBuffer` submission recycles exactly once. -/
theorem recycleCount_recycle (bid : Uring.Bid) :
    recycleCount [Reactor.RingSubmission.recycleBuffer bid] = 1 := rfl

/-! ### The wiring: how a RingEvent drives the machine and the lease -/

/-- The region/lease wiring that specializes an abstract machine/linear pair to the
    ring's event alphabet. `drive_no_recycle` is the load-bearing discipline: the
    machine emits application submissions (sends, re-arms, closes) but NEVER a
    `recycleBuffer` — buffer recycling is owned by the reactor shell, which is why the
    copy-once law is structural. -/
structure Wiring (m l : Component) where
  /-- region-parse: a recv delivers bytes the machine can consume; other events may not. -/
  feed  : RingEvent → Option m.Input
  /-- the machine drives submissions (sends / re-arms / closes) — never a recycle. -/
  drive : m.Output → List RingSubmission
  /-- lease bookkeeping fed to the linear resource. -/
  lease : RingEvent → Option l.Input
  /-- the machine never emits a recycle submission (the shell owns copy-once release). -/
  drive_no_recycle : ∀ o, ∀ s ∈ drive o, Reactor.RingSubmission.isRecycle s = false

/-- The default wiring over any machine/linear pair: no parse, no sends, no lease.
    The reactor shell still supplies the copy-once recycle, so the copy-once law and
    invariant preservation hold — this is what makes the bare `mkReactor m l`
    (task-signature) total for ANY pair. The macro/emit lanes pass real wiring via
    `mkReactorWith`. -/
def defaultWiring (m l : Component) : Wiring m l where
  feed  := fun _ => none
  drive := fun _ => []
  lease := fun _ => none
  drive_no_recycle := by intro _ s hs; simp at hs

/-! ### The reactor step, factored for clean preservation proofs -/

/-- Advance the machine when the event parses to a machine input; else hold.
    Returns the next machine state and the machine-driven submission batch. -/
def feedMachine (m l : Component) (w : Wiring m l)
    (ms : m.State) (ev : RingEvent) : m.State × List RingSubmission :=
  match w.feed ev with
  | some inp => ((m.step ms inp).1, (m.step ms inp).2.flatMap w.drive)
  | none     => (ms, [])

/-- Advance the linear resource when the event carries a lease command; else hold. -/
def feedLinear (m l : Component) (w : Wiring m l)
    (ls : l.State) (ev : RingEvent) : l.State :=
  match w.lease ev with
  | some li => (l.step ls li).1
  | none    => ls

/-- The copy-once recycle the SHELL emits: exactly one `recycleBuffer` per recv
    completion, none for any other event. -/
def recycleSubs (ev : RingEvent) : List RingSubmission :=
  match ev with
  | .recvInto bid _ => [Reactor.RingSubmission.recycleBuffer bid]
  | _               => []

/-- One reactor transition over the composed (machine × linear) state. -/
def reactorStep (m l : Component) (w : Wiring m l)
    (s : m.State × l.State) (ev : RingEvent) :
    (m.State × l.State) × List RingSubmission :=
  (((feedMachine m l w s.1 ev).1, feedLinear m l w s.2 ev),
   (feedMachine m l w s.1 ev).2 ++ recycleSubs ev)

/-! ### Structural facts about the factored pieces -/

theorem feedMachine_wf (m l : Component) (w : Wiring m l)
    {ms : m.State} (ev : RingEvent) (h : m.inv ms) :
    m.inv (feedMachine m l w ms ev).1 := by
  unfold feedMachine
  split
  · exact m.step_wf _ _ h
  · exact h

theorem feedLinear_wf (m l : Component) (w : Wiring m l)
    {ls : l.State} (ev : RingEvent) (h : l.inv ls) :
    l.inv (feedLinear m l w ls ev) := by
  unfold feedLinear
  split
  · exact l.step_wf _ _ h
  · exact h

theorem feedMachine_no_recycle (m l : Component) (w : Wiring m l)
    (ms : m.State) (ev : RingEvent) :
    ∀ s ∈ (feedMachine m l w ms ev).2, Reactor.RingSubmission.isRecycle s = false := by
  unfold feedMachine
  split
  · intro s hs
    rw [List.mem_flatMap] at hs
    obtain ⟨o, _, hmem⟩ := hs
    exact w.drive_no_recycle o s hmem
  · intro s hs; simp at hs

theorem feedMachine_filter_nil (m l : Component) (w : Wiring m l)
    (ms : m.State) (ev : RingEvent) :
    (feedMachine m l w ms ev).2.filter Reactor.RingSubmission.isRecycle = [] :=
  filter_isRecycle_nil _ (feedMachine_no_recycle m l w ms ev)

/-! ### The reactor as a first-class Component primitive -/

/-- The 5th DSL primitive: a `Component` specialized to the ring's event loop
    (`Input = RingEvent`, `Output = RingSubmission`), carrying its machine and linear
    sub-components. `toComponent` re-exposes it as a plain `Component` so it composes
    with the other four primitives via `Component.prod`. -/
structure ReactorComponent where
  machine : Component
  linear  : Component
  State   : Type
  inv     : State → Prop
  init    : State
  step    : State → RingEvent → State × List RingSubmission
  init_wf : inv init
  step_wf : ∀ s ev, inv s → inv (step s ev).1

/-- View the reactor primitive as a plain `Component` (Input = RingEvent,
    Output = RingSubmission) for composition with the other primitives. -/
def ReactorComponent.toComponent (R : ReactorComponent) : Component where
  State   := R.State
  Input   := RingEvent
  Output  := RingSubmission
  inv     := R.inv
  init    := R.init
  step    := R.step
  init_wf := R.init_wf
  step_wf := R.step_wf

/-- `reactor over (m, l)` with explicit region/lease wiring — what the macro emits. -/
def mkReactorWith (m l : Component) (w : Wiring m l) : ReactorComponent where
  machine := m
  linear  := l
  State   := m.State × l.State
  inv     := fun s => m.inv s.1 ∧ l.inv s.2
  init    := (m.init, l.init)
  step    := reactorStep m l w
  init_wf := ⟨m.init_wf, l.init_wf⟩
  step_wf := by
    intro s ev h
    exact ⟨feedMachine_wf m l w ev h.1, feedLinear_wf m l w ev h.2⟩

/-- The task-signature constructor: `reactor over (machine, linear)`.
    Total for ANY machine/linear pair (uses `defaultWiring`); the emit lanes and macro
    call `mkReactorWith` when they have real region/lease bridges. -/
def mkReactor (m l : Component) : ReactorComponent :=
  mkReactorWith m l (defaultWiring m l)

/-! ### The primitive-level theorems the macro instantiates -/

/-- **reactor_prim_recycle** — a `recvInto` event yields exactly one recycle, and it
    is the recycle of *that* buffer, for ANY machine/linear pair and ANY wiring.
    Generalizes `Reactor.recv_recycles_exactly_once` (the `Reactor.step` instance):
    the reactor shell owns the single recycle, so the filtered output never depends on
    the composed sub-components. -/
theorem reactor_prim_recycle (m l : Component) (w : Wiring m l)
    (s : (mkReactorWith m l w).State) (bid : Uring.Bid) (data : Proto.Bytes) :
    ((mkReactorWith m l w).step s (.recvInto bid data)).2.filter
        Reactor.RingSubmission.isRecycle
      = [Reactor.RingSubmission.recycleBuffer bid] := by
  show ((feedMachine m l w s.1 (.recvInto bid data)).2 ++ recycleSubs (.recvInto bid data)).filter
        Reactor.RingSubmission.isRecycle = _
  rw [List.filter_append, feedMachine_filter_nil, List.nil_append]
  rfl

/-- The recycle **count** on a recv is exactly one — the copy-once law as a Nat. -/
theorem reactor_prim_recycleCount (m l : Component) (w : Wiring m l)
    (s : (mkReactorWith m l w).State) (bid : Uring.Bid) (data : Proto.Bytes) :
    recycleCount ((mkReactorWith m l w).step s (.recvInto bid data)).2 = 1 := by
  unfold recycleCount
  rw [reactor_prim_recycle]
  rfl

/-- A non-`recvInto` event yields no recycle (the copy-once law's negative half). -/
theorem reactor_prim_no_recycle (m l : Component) (w : Wiring m l)
    (s : (mkReactorWith m l w).State) (ev : RingEvent) (h : ev.isRecv = false) :
    recycleCount ((mkReactorWith m l w).step s ev).2 = 0 := by
  show recycleCount ((feedMachine m l w s.1 ev).2 ++ recycleSubs ev) = 0
  rw [recycleCount_append, recycleCount_no _ (feedMachine_no_recycle m l w s.1 ev)]
  have hz : recycleSubs ev = [] := by
    cases ev with
    | recvInto bid data => simp [RingEvent.isRecv] at h
    | _ => rfl
  simp [hz, recycleCount]

/-- **reactor_prim_wf** — the composed invariant `m.inv ∧ l.inv` is preserved by one
    reactor step, for ANY machine/linear pair and ANY wiring and ANY event. -/
theorem reactor_prim_wf (m l : Component) (w : Wiring m l)
    (s : (mkReactorWith m l w).State) (ev : RingEvent)
    (h : (mkReactorWith m l w).inv s) :
    (mkReactorWith m l w).inv ((mkReactorWith m l w).step s ev).1 :=
  (mkReactorWith m l w).step_wf s ev h

/-! ### Corollaries specialized to the bare `mkReactor` (macro/emit call site) -/

theorem mkReactor_recycle (m l : Component)
    (s : (mkReactor m l).State) (bid : Uring.Bid) (data : Proto.Bytes) :
    ((mkReactor m l).step s (.recvInto bid data)).2.filter
        Reactor.RingSubmission.isRecycle
      = [Reactor.RingSubmission.recycleBuffer bid] :=
  reactor_prim_recycle m l (defaultWiring m l) s bid data

theorem mkReactor_recycleCount (m l : Component)
    (s : (mkReactor m l).State) (bid : Uring.Bid) (data : Proto.Bytes) :
    recycleCount ((mkReactor m l).step s (.recvInto bid data)).2 = 1 :=
  reactor_prim_recycleCount m l (defaultWiring m l) s bid data

theorem mkReactor_no_recycle (m l : Component)
    (s : (mkReactor m l).State) (ev : RingEvent) (h : ev.isRecv = false) :
    recycleCount ((mkReactor m l).step s ev).2 = 0 :=
  reactor_prim_no_recycle m l (defaultWiring m l) s ev h

theorem mkReactor_wf (m l : Component)
    (s : (mkReactor m l).State) (ev : RingEvent) (h : (mkReactor m l).inv s) :
    (mkReactor m l).inv ((mkReactor m l).step s ev).1 :=
  reactor_prim_wf m l (defaultWiring m l) s ev h

/-! ### The generalization is faithful: the hand-built reference is one instance.

The hand-built `Reactor.step` recycles a recv exactly once
(`Reactor.recv_recycles_exactly_once`). `reactor_prim_recycle` proves the SAME
filtered-output property holds structurally for every `mkReactorWith m l w`, i.e. for
any machine, any linear resource, and any region/lease wiring. -/
example (cfg : Proto.Config) (ps : Proto.State) (bid : Uring.Bid) (data : Proto.Bytes) :
    (Reactor.step cfg ps (.recvInto bid data)).2.filter Reactor.RingSubmission.isRecycle
      = [Reactor.RingSubmission.recycleBuffer bid] :=
  Reactor.recv_recycles_exactly_once cfg ps bid data

end Dsl
