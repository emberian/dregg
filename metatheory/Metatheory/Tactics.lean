/-
# Metatheory.Tactics — shared proof automation for the dregg2 metatheory.

Small, honest helpers shared across the modules and the executable protocols. The rule:
these CLOSE genuinely-routine goals (reflexivity, definitional simp, injection cleanup,
linear arithmetic). They are NOT a way to make a real obligation *look* discharged — if a
helper does not close a goal, the goal is real: prove it properly or leave an explicit
`sorry` with a one-line reason. (Never `admit`, never a fresh `axiom`, never
`native_decide` on a non-decidable prop.)

Grows as recurring patterns emerge from the proof-discharge swarm.
-/
import Mathlib.Tactic.Tauto

namespace Metatheory.Tactics

/-- `dregg_auto` — best-effort closer for *routine* obligations only: reflexivity,
`trivial`, definitional/hypothesis `simp`, linear arithmetic, propositional tautology.
Use it as the last step of a proof; if it fails, the goal carries real content. -/
macro "dregg_auto" : tactic =>
  `(tactic| first
    | rfl
    | trivial
    | (intros; first | rfl | trivial | simp_all | omega | tauto)
    | simp_all
    | omega
    | tauto)

/-- `option_inj at h` — collapse `some x = some y` (and any nested `(·,·) = (·,·)`) in `h`
to its component equalities; the standard first move when reading back a protocol step
that returned `some (newState…)`. -/
macro "option_inj" "at" h:ident : tactic =>
  `(tactic| simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident)

end Metatheory.Tactics
