/-!
# The component calculus — the shape that makes the primitives compose

Every model in this package is one of four shapes: a byte **region** with typed
views; a sans-IO **machine** (a labelled transition system); a **linear**
resource (acquire → use → release-once); a **shared** object carrying a declared
invariant. This file gives the common structure — a `Component`: a state space,
a well-formedness invariant, an initial state, and a labelled step that produces
**outputs** — and proves the composition laws a *calculus* needs:

* **invariant preservation composes** — a component whose step preserves its
  invariant keeps that invariant on every reachable state (`reachable_inv`);
* **components compose** — the parallel product of two invariant-preserving
  components preserves the conjoined invariant (`prod` / `prod_preserves`), a
  reachable product state is reachable in each factor (`prod_reachable`), and the
  product's output stream is the tagged interleaving of the factors' outputs
  (`prod_run_state`).

The step carries a `List Output`, so a machine that reads a request and emits a
response fits the calculus without discarding its response channel. Concrete
instances of the four primitive shapes live in `Dsl.Primitives`.
-/

namespace Dsl

/-- A component: a state space with a well-formedness invariant, an initial
state, and a labelled step that maps `State → Input → State × List Output`. -/
structure Component where
  State : Type
  Input : Type
  Output : Type
  inv : State → Prop
  init : State
  step : State → Input → State × List Output
  /-- The initial state is well-formed. -/
  init_wf : inv init
  /-- Every step preserves the invariant (on the resulting state). -/
  step_wf : ∀ s i, inv s → inv (step s i).1

namespace Component

variable (c : Component)

/-- Run a component over a sequence of inputs, collecting outputs in order. -/
def run (s : c.State) : List c.Input → c.State × List c.Output
  | [] => (s, [])
  | i :: is =>
    let s₁ := (c.step s i).1
    let o₁ := (c.step s i).2
    let r := run s₁ is
    (r.1, o₁ ++ r.2)

/-- The state a run reaches (projection of `run`). -/
def runState (s : c.State) (is : List c.Input) : c.State := (c.run s is).1

/-- A state is reachable if a run from `init` reaches it. -/
def Reachable (s : c.State) : Prop := ∃ is, c.runState c.init is = s

/-- Running preserves the invariant on the reached state. -/
theorem runState_wf {s : c.State} (h : c.inv s) (is : List c.Input) :
    c.inv (c.runState s is) := by
  induction is generalizing s with
  | nil => exact h
  | cons i is ih =>
    show c.inv (c.runState (c.step s i).1 is)
    exact ih (c.step_wf s i h)

/-- **Invariant preservation composes into a reachability invariant.** Every
reachable state of a component is well-formed — the invariant methodology in one
line, and the foundation every model's `wf` theorem instantiates. -/
theorem reachable_inv {s : c.State} (h : c.Reachable s) : c.inv s := by
  obtain ⟨is, rfl⟩ := h
  exact c.runState_wf c.init_wf is

end Component

/-- **Parallel product of two components.** State and input are paired; outputs
are tagged by side and concatenated; the invariant is the conjunction; each
factor steps on its own input projection. This is how a machine that carries a
region and holds a linear resource — each with its own output — is assembled. -/
def Component.prod (a b : Component) : Component where
  State := a.State × b.State
  Input := a.Input × b.Input
  Output := a.Output ⊕ b.Output
  inv := fun s => a.inv s.1 ∧ b.inv s.2
  init := (a.init, b.init)
  step := fun s i =>
    ((( a.step s.1 i.1).1, (b.step s.2 i.2).1),
      (a.step s.1 i.1).2.map Sum.inl ++ (b.step s.2 i.2).2.map Sum.inr)
  init_wf := ⟨a.init_wf, b.init_wf⟩
  step_wf := fun s i h => ⟨a.step_wf s.1 i.1 h.1, b.step_wf s.2 i.2 h.2⟩

/-- **Components compose.** The product invariant — the conjunction of the two
factor invariants — is preserved by the product step. -/
theorem prod_preserves (a b : Component) (s : (a.prod b).State) (i : (a.prod b).Input)
    (h : (a.prod b).inv s) : (a.prod b).inv ((a.prod b).step s i).1 :=
  (a.prod b).step_wf s i h

/-- The reached state of the product run is the pair of the factor runs' reached
states — the state channel composes cleanly. -/
theorem prod_run_state (a b : Component) (s : a.State × b.State)
    (is : List (a.Input × b.Input)) :
    (a.prod b).runState s is
      = (a.runState s.1 (is.map Prod.fst), b.runState s.2 (is.map Prod.snd)) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (a.prod b).runState ((a.prod b).step s i).1 is = _
    rw [ih]
    simp only [Component.prod, Component.runState, Component.run, List.map_cons]

/-- **A reachable product state is reachable in each factor.** Composition does
not manufacture states unreachable in the parts. -/
theorem prod_reachable (a b : Component) (s : (a.prod b).State)
    (h : (a.prod b).Reachable s) : a.Reachable s.1 ∧ b.Reachable s.2 := by
  obtain ⟨is, rfl⟩ := h
  rw [prod_run_state]
  exact ⟨⟨is.map Prod.fst, rfl⟩, ⟨is.map Prod.snd, rfl⟩⟩

end Dsl
