/-
# Dregg2.Execution — userspace programs: configurations, runs, and invariants.

The bridge from single turns to **whole executions of protocols** ("userspace programs"):
a program's operational semantics is a transition system over *configurations* (global
states); a *run* is a finite reachability chain of steps; and the central reusable result
is **invariant preservation along any run** — the induction principle by which a per-step
property (conservation, authority confinement, a safety predicate) lifts to a property of
the entire execution.

This is what lets dregg2 state and prove *the big things about userspace programs*:
- **safety**: a bad configuration is never reachable from a good start;
- **conservation over time**: total resource is invariant across an arbitrary run (not
  just one turn — `Core.conservation_step` is per-turn; `invariant_run` lifts it);
- **(later) progress / liveness**: every reachable non-final config can step.

`invariant_run`, `safe_of_stepInvariant`, and the run-algebra lemmas are PROVED (no
`sorry`) — they are pure induction over the reachability relation, independent of any
particular protocol, and are instantiated by concrete protocols (e.g.
`Protocol.Transfer`'s payment channel).
-/
import Dregg2.Tactics

namespace Dregg2.Execution

universe u

/-- A **transition system** = the operational semantics of a userspace program: a space
of configurations and a (possibly nondeterministic, possibly partial) step relation. A
dregg2 program's `Step` is "some admissible turn / JointTurn fires"; here it is abstract. -/
structure System where
  /-- The configuration space (the global state). -/
  Config : Type u
  /-- One execution step (one committed turn). -/
  Step   : Config → Config → Prop

variable {S : System}

/-- A **run** (execution / trace): the reflexive–transitive closure of `Step`. `Run S s t`
means `t` is reachable from `s` by some finite sequence of steps. -/
inductive Run (S : System) : S.Config → S.Config → Prop where
  | refl (s : S.Config) : Run S s s
  | step {s t u : S.Config} : S.Step s t → Run S t u → Run S s u

/-- `Reachable S init t` — `t` arises in some execution started at `init`. -/
def Reachable (S : System) (init t : S.Config) : Prop := Run S init t

/-- Runs compose (transitivity of reachability) — PROVED. -/
theorem Run.trans {s t u : S.Config} (h₁ : Run S s t) (h₂ : Run S t u) : Run S s u := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep _ ih => exact Run.step hstep (ih h₂)

/-- A single step appended to a run — PROVED. -/
theorem Run.snoc {s t u : S.Config} (h : Run S s t) (hstep : S.Step t u) : Run S s u :=
  h.trans (Run.step hstep (Run.refl u))

/-- A predicate `I` on configurations is a **step-invariant** if every step preserves it. -/
def StepInvariant (S : System) (I : S.Config → Prop) : Prop :=
  ∀ s t, I s → S.Step s t → I t

/-- **Invariant preservation along ANY run — the keystone, PROVED.** If `I` is a
step-invariant and holds at the start, it holds at every reachable configuration. This is
the induction principle that lifts a per-turn law to a law about the whole execution. -/
theorem invariant_run {I : S.Config → Prop}
    (hpres : StepInvariant S I) {s t : S.Config}
    (hrun : Run S s t) : I s → I t := by
  induction hrun with
  | refl _ => exact id
  | step hstep _ ih => exact fun hi => ih (hpres _ _ hi hstep)

/-- A **safety** property: a `Bad` configuration is never reachable from `init`. -/
def Safe (S : System) (init : S.Config) (Bad : S.Config → Prop) : Prop :=
  ∀ t, Reachable S init t → ¬ Bad t

/-- **Safety from a step-invariant — PROVED.** If `¬ Bad` is a step-invariant and holds
initially, the system is safe (the standard inductive-invariant safety argument). -/
theorem safe_of_stepInvariant {init : S.Config} {Bad : S.Config → Prop}
    (hpres : StepInvariant S (fun s => ¬ Bad s)) (hinit : ¬ Bad init) :
    Safe S init Bad :=
  fun _t hreach => invariant_run hpres hreach hinit

/-- A configuration is **final** (a halted program) when it cannot step. -/
def Final (S : System) (s : S.Config) : Prop := ∀ t, ¬ S.Step s t

/-- **Progress / deadlock-freedom** (a property to *prove per system*, stated here as the
target): every reachable non-final configuration can take a step. (For dregg2 this is the
choreographic deadlock-freedom of `Coordination`/`Projection`, instantiated.) -/
def Progresses (S : System) (init : S.Config) : Prop :=
  ∀ t, Reachable S init t → ¬ Final S t → ∃ u, S.Step t u

end Dregg2.Execution
