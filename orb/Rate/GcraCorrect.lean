/-
Rate.GcraCorrect — a CORRECTNESS proof for the GCRA limiter.

`Rate/Gcra.lean` establishes safety-flavoured facts about `gcraStep`
(monotonicity of the theoretical arrival time, no phantom charge on rejection,
the spacing and window bounds).  Those say the limiter is well-behaved; they do
NOT pin down *which* request is admitted at a given clock reading.

This file supplies the missing correctness statement: it defines, independently
of `gcraStep`, exactly what the Generic Cell Rate Algorithm is required to do —
its conformance test and its state update — directly from the algorithm's
reference definition, and then proves that `gcraStep` computes precisely that.

Reference definition (the "virtual scheduling algorithm" form of the GCRA,
GCRA(I, L) — ATM Forum Traffic Management Specification 4.0, §4.4.2; equivalently
ITU-T Recommendation I.371).  A limiter carries a Theoretical Arrival Time `TAT`,
an increment `I` (the emission interval), and a limit `L` (the tolerance).  A
cell arriving at time `t` is:

  * NON-CONFORMING when it arrives more than `L` ahead of schedule, i.e. when
      `t < TAT - L`   (equivalently `TAT - t > L`);
  * CONFORMING otherwise, i.e. when
      `t ≥ TAT - L`,
    and a conforming arrival updates the schedule to
      `TAT := max t TAT + I`.
    A non-conforming arrival leaves `TAT` unchanged.

The spec below is that reference definition transcribed with no reference to the
implementation.  Note the *form* differs from the code: the reference test is the
"not too early" inequality `TAT - L ≤ t`, whereas `gcraStep` tests
`TAT ≤ t + burst`.  The refinement theorem is where those two forms are shown to
coincide, so this is a genuine obligation and not the implementation renamed.
-/

import Rate.Gcra

namespace Rate

/-! ### The independent specification (from the GCRA reference definition) -/

/-- **Reference conformance test.**  A request arriving at clock `t` conforms
when it is not more than the tolerance `tau` ahead of the theoretical arrival
time `tat`, i.e. `t ≥ tat - tau` (the ATM Forum / I.371 "not too early" test,
written with the `TAT - L ≤ t` inequality).  Decidable, so it can drive an
`if`. -/
def specAdmit (tat tau t : Nat) : Prop := tat - tau ≤ t

instance (tat tau t : Nat) : Decidable (specAdmit tat tau t) :=
  inferInstanceAs (Decidable (tat - tau ≤ t))

/-- **Reference schedule update on a conforming arrival.**  The theoretical
arrival time advances to `max t tat + T`, where `T` is the emission interval.
This is the reference `TAT := max(t, TAT) + I`. -/
def specTat (tat T t : Nat) : Nat := max t tat + T

/-- The full reference step: the state the GCRA reference definition prescribes
after an arrival at clock `t`.  On a conforming arrival the theoretical arrival
time is updated to `specTat`; on a non-conforming arrival the state is
unchanged.  Defined purely from `specAdmit` / `specTat` — it never mentions
`gcraStep`. -/
def specStep (g : Gcra) (t : Nat) : Gcra :=
  if specAdmit g.tat g.burst t then { g with tat := specTat g.tat g.t_int t } else g

/-! ### The refinement theorem: `gcraStep` computes the reference step -/

/-- **Admit decision refinement.**  The implementation's conformance test
(`tat ≤ t + burst`) holds exactly when the reference test (`tat - tau ≤ t`) does.
Over `Nat`, `tat ≤ t + burst ↔ tat - burst ≤ t`; this is where the two written
forms of the test are shown equal.  A limiter using the *wrong* tolerance would
break this equivalence. -/
theorem gcra_admit_matches_spec (g : Gcra) (t : Nat) :
    (g.tat ≤ t + g.burst) ↔ specAdmit g.tat g.burst t := by
  unfold specAdmit; omega

/-- **Refinement theorem (correctness of GCRA).**  For every limiter state and
every arrival clock, `gcraStep` produces exactly the state the GCRA reference
definition prescribes: it admits precisely the conforming arrivals (per the
reference conformance test) and, on admission, advances the theoretical arrival
time to exactly the reference value `max t tat + T`.  This is `gcraStep`
extensionally equal to the independent `specStep`. -/
theorem gcra_refines_spec (g : Gcra) (t : Nat) :
    gcraStep g t = specStep g t := by
  unfold gcraStep specStep specAdmit specTat
  by_cases h : g.tat - g.burst ≤ t
  · rw [if_pos h, if_pos (by omega : g.tat ≤ t + g.burst)]
  · rw [if_neg h, if_neg (by omega : ¬ g.tat ≤ t + g.burst)]

/-- The admit *count* function likewise agrees with the reference test: it
returns `1` exactly on conforming arrivals. -/
theorem gcra_admits_iff_spec (g : Gcra) (t : Nat) :
    gcraAdmits g t = 1 ↔ specAdmit g.tat g.burst t := by
  unfold gcraAdmits specAdmit
  by_cases h : g.tat - g.burst ≤ t
  · rw [if_pos (by omega : g.tat ≤ t + g.burst)]; simp [h]
  · rw [if_neg (by omega : ¬ g.tat ≤ t + g.burst)]; simp; omega

/-! ### Non-vacuity: the spec constrains, and the boundary is exact

The theorem is not `impl = impl` and not `P → P`.  The spec is a distinct
predicate (`tat - tau ≤ t`) from the implementation's test (`tat ≤ t + burst`),
and it genuinely rejects some arrivals.  The witnesses below fix a concrete
limiter with `tat = 10`, `tau = burst = 3` (so `tat - tau = 7`) and exhibit the
knife-edge: the arrival at `t = 7` (exactly `tat - tau`) admits, and the arrival
one tick earlier at `t = 6` rejects.  A limiter that admitted unconditionally
would fail the second, and a limiter using the wrong tolerance would move the
edge — so `gcra_refines_spec` pins the behaviour down. -/

/-- Boundary, admit side: at `t = tat - tau` exactly, the arrival conforms and
the schedule advances to `max 7 10 + 5 = 15`. -/
example : gcraStep { tat := 10, t_int := 5, burst := 3 } 7
    = { tat := 15, t_int := 5, burst := 3 } := by decide

/-- Boundary, reject side: one tick earlier, at `t = tat - tau - 1 = 6`, the
arrival is non-conforming and the state is untouched.  An unconditional-admit
implementation would instead advance `tat` here — this is the case that
distinguishes the real GCRA from a vacuous one. -/
example : gcraStep { tat := 10, t_int := 5, burst := 3 } 6
    = { tat := 10, t_int := 5, burst := 3 } := by decide

/-- The admit decision itself at the two boundary clocks: admits at `7`, … -/
example : gcraAdmits { tat := 10, t_int := 5, burst := 3 } 7 = 1 := by decide
/-- … and rejects at `6`. -/
example : gcraAdmits { tat := 10, t_int := 5, burst := 3 } 6 = 0 := by decide

/-- The reference predicate is genuinely selective: it holds at the boundary… -/
example : specAdmit 10 3 7 := by decide
/-- … and fails one tick before it, confirming the spec rejects (is not the
constantly-true predicate a vacuous spec would be). -/
example : ¬ specAdmit 10 3 6 := by decide

end Rate
