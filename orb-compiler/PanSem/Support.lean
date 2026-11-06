/-
  Proved (untrusted) lemmas about reflected definitions, needed by the
  termination argument of the reflected clocked `evaluate`.  These are the
  Lean counterparts of panSem's `fix_clock_IMP_LESS_EQ`.
-/
import PanSem.Generated
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace P3.Pan

theorem fix_clock_clock {γ α ε : Type} (s : state ε) (r : α × state γ) :
    (fix_clock s r).2.clock =
      if s.clock < r.2.clock then s.clock else r.2.clock := by
  obtain ⟨a, b⟩ := r
  simp only [fix_clock]

theorem dec_clock_clock {θ : Type} (s : state θ) : (dec_clock s).clock = s.clock - 1 := by
  simp only [dec_clock]

/-- Termination of the reflected clocked `evaluate` (HOL's measure
`(s.clock, prog_size)`): unfold the lexicographic order, rewrite the clock of
`fix_clock`/`dec_clock` results (lemmas in Support.lean), split the
conditionals and close by linear arithmetic. -/
macro "pan_decreasing" : tactic =>
  `(tactic| (simp_wf
             simp only [Prod.lex_def, fix_clock_clock, dec_clock_clock, true_and] at *
             (repeat' split) <;> omega))

end P3.Pan
