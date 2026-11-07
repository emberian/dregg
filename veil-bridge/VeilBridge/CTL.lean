/-
# VeilBridge.CTL: breadstuffs' CTL over a Veil transition system

One shared definition, `VeilBridge.toSystem`, reads a Veil `RelationalTransitionSystem` at a fixed
background theory as a breadstuffs `Dregg2.Execution.System` (configurations = Veil states, one step =
Veil's label-hiding `next`). Everything in `Dregg2.Proof.CTL` and `Dregg2.Proof.MuCalculus` then
applies to a Veil protocol unchanged.

The weld theorem `invariant_iff_AG`: a Veil invariant (a property of every reachable state, the thing
Veil's checkers and SMT proofs establish) is exactly breadstuffs' greatest-fixpoint `AG` holding at
every initial state. That is the hook for CTL checking on Veil-style systems: Veil supplies the
transition system and its safety facts, breadstuffs supplies the branching-time calculus.
-/
import Veil
import Dregg2.Proof.CTL

namespace VeilBridge

open Dregg2.Execution

variable {ρ σ l : Type}

/-- **The shared definition.** A Veil relational transition system at background theory `th`, as a
breadstuffs `System`. Reducible, so `(toSystem sys th).Config` is `σ` at the transparency v4.35's
unifier checks instances at. -/
@[reducible] def toSystem (sys : Veil.RelationalTransitionSystem ρ σ l) (th : ρ) : System where
  Config := σ
  Step := sys.next th

variable (sys : Veil.RelationalTransitionSystem ρ σ l) (th : ρ)

/-- A breadstuffs run from a Veil-reachable state stays Veil-reachable. -/
theorem reachable_of_run {s t : σ} (hs : sys.reachable th s)
    (hrun : Run (toSystem sys th) s t) : sys.reachable th t :=
  invariant_run (S := toSystem sys th) (I := sys.reachable th)
    (fun _ _ hi hstep => Veil.RelationalTransitionSystem.reachable.step _ _ hi hstep) hrun hs

/-- Every Veil-reachable state is reached by a breadstuffs run from some initial state. -/
theorem run_of_reachable {t : σ} (ht : sys.reachable th t) :
    ∃ s₀, sys.assumptions th ∧ sys.init th s₀ ∧ Run (toSystem sys th) s₀ t := by
  induction ht with
  | init s has hinit => exact ⟨s, has, hinit, Run.refl (S := toSystem sys th) s⟩
  | step s s' _ hn ih =>
      obtain ⟨s₀, has, hinit, hrun⟩ := ih
      exact ⟨s₀, has, hinit, Run.snoc (S := toSystem sys th) hrun hn⟩

/-- **The weld.** A Veil invariant is breadstuffs' `AG` at every initial state. -/
theorem invariant_iff_AG (P : Set σ) :
    (∀ s, sys.reachable th s → s ∈ P) ↔
      (∀ s₀, sys.assumptions th → sys.init th s₀ →
        s₀ ∈ Dregg2.Proof.CTL.AG (toSystem sys th) P) := by
  constructor
  · intro hinv s₀ has hinit
    rw [Dregg2.Proof.CTL.AG_iff_all_reachable]
    intro t hrun
    exact hinv t (reachable_of_run sys th
      (Veil.RelationalTransitionSystem.reachable.init s₀ has hinit) hrun)
  · intro hag t ht
    obtain ⟨s₀, has, hinit, hrun⟩ := run_of_reachable sys th ht
    exact (Dregg2.Proof.CTL.AG_iff_all_reachable (toSystem sys th) P s₀).1
      (hag s₀ has hinit) t hrun

#assert_all_clean [reachable_of_run, run_of_reachable, invariant_iff_AG]

end VeilBridge
