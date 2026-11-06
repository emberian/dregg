/-
  Tactics used by the generated file.  Nothing here is trusted: each macro
  only searches for a proof the Lean kernel then checks.
-/
import PanSem.Prelude

/-- Checker 2: prove a reflected HOL4 defining equation by unfolding the
reflected definition only. -/
macro "hol_eqn " f:ident : tactic =>
  `(tactic| first
      | (rw [$f:ident])
      | (simp only [$f:ident])
      | (unfold $f:ident; rfl)
      | rfl)

