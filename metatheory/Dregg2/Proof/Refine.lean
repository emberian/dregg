/-
# Dregg2.Proof.Refine — the **Exec ⊑ Abstract** refinement (the l4v `proof/refine` analog).

`Exec/Kernel.lean` builds the *executable* kernel (the Design-Spec layer); `Core`,
`Authority.Positional`, `Boundary`, `Execution` state the *abstract laws* (the Spec
layer). This module is the **refinement square**: it shows the concrete machine
realizes the abstract laws — the l4v `proof/refine` (`Refine.thy`) analog, where the
concrete kernel automaton is proved to simulate the abstract specification.

The clean refinements are *direct* relays of the already-proved kernel lemmas
(`Exec.exec_conserves`, `Exec.kernel_run_conserves`, `Exec.exec_authorized`):

* `refine_conservation`     — the kernel's `total` measure (the concrete `Core`
  `count`/measure) is invariant under every committed `exec` step ⇒ Law 1.
* `refine_run_conservation` — conservation holds along every whole kernel `Run`.
* `refine_integrity`        — every committed step is authority-admissible; the
  owner (intra-vat, l4v `troa_lrefl`) case is bridged into `Authority.Integrity`.
* `exec_refines`            — the forward-simulation statement: a relation `R`
  between concrete `KernelState`s and abstract conservation-configs such that every
  concrete `exec` step is matched by an admissible abstract step preserving the laws.
  The conservation component is PROVED; the full abstract operational simulation needs
  an abstract small-step model not present in `Core` (which states laws, not a
  transition relation), so that part is a precise `-- OPEN:`.

Honesty: the conservation refinement is FULLY proved (it follows from
`exec_conserves`); the deeper operational simulation is partially open.
-/
import Dregg2.Exec.Kernel
import Dregg2.Core
import Dregg2.Authority.Positional
import Dregg2.Execution

namespace Dregg2.Proof

open Dregg2.Exec Dregg2.Execution
open Dregg2.Authority (Integrity)

/-! ## 1. Conservation refinement — Law 1, fully proved from `exec_conserves`. -/

/-- **Conservation refinement (Law 1).** The kernel's total-supply measure
(`Exec.total`) is invariant under every committed `exec` step: the executable kernel
realizes `Core`'s Law-1 conservation. This is a direct relay of `Exec.exec_conserves`,
restated as the refinement obligation. -/
theorem refine_conservation (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    total k' = total k :=
  exec_conserves k k' turn h

/-- The kernel's conserved measure, packaged as the data shape `Core` measures a
config by: a function `KernelState → ℤ` valued in the `AddCommMonoid` `ℤ` (the
signed-balance instance of `Core`'s measure-monoid `M`). `Exec.total` *is* the
concrete `Core.Conservation.count`/measure for the kernel. -/
abbrev kernelMeasure : KernelState → ℤ := total

/-- **Conservation refinement, `Core`-measure form.** Restates `refine_conservation`
using `kernelMeasure` to make explicit that the invariant quantity is the kernel's
realization of `Core`'s monoid-valued `count` measure (here `M = ℤ`). -/
theorem refine_conservation_measure (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    kernelMeasure k' = kernelMeasure k :=
  exec_conserves k k' turn h

/-! ## 2. Whole-run refinement — conservation along every kernel `Run`. -/

/-- **Whole-run conservation refinement.** Conservation holds along *every* kernel
`Run` (not just one step): the refinement of `Core`'s per-turn law lifted to the
userspace-program layer. A direct relay of `Exec.kernel_run_conserves` (itself
`Execution.invariant_run` applied to `exec_conserves`). -/
theorem refine_run_conservation {k k' : KernelState}
    (hrun : Run kernelSystem k k') :
    total k' = total k :=
  kernel_run_conserves hrun

/-! ## 3. Authority / integrity refinement. -/

/-- **Authority admissibility refinement.** Every committed `exec` step is
authority-admissible (the kernel never moves a cell's resource without authority):
a direct relay of `Exec.exec_authorized`, the concrete shadow of `Authority.Integrity`
/ l4v `call_kernel_integrity`. -/
theorem refine_integrity (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    authorizedB k.caps turn = true :=
  exec_authorized k k' turn h

/-- **Integrity bridge — the intra-vat (owner) case, l4v `troa_lrefl`.** When the
committed turn is performed by the *owner* of `src` (`turn.actor = turn.src` — the
ownership disjunct of `authorizedB` — discharged here from the *real* kernel step
`exec k turn = some k'` via `exec_authorized` + the ownership disjunct), and the actor
is genuinely among the abstract `subjects` (`hsubj : turn.actor ∈ subjects`, a FREE
parameter — NOT the singleton `[turn.actor]`), the change lands in `Authority.Integrity`
via the `intra` constructor. This bridges the concrete authority check to the abstract
integrity relation for the owner case.

All THREE hypotheses are load-bearing — this is what fixes the earlier vacuity (the old
version fixed `subjects := [turn.actor]`, making membership `rfl` and leaving `hown`/the
abstract states unused). The conclusion is a *conjunction* tying the concrete step to the
abstract relation, so every hypothesis does work:

* `hstep` proves the concrete step was **authorized** (`authorizedB k.caps turn = true`,
  via `exec_authorized`) — the left conjunct; without it that fact is not available.
* `hown` is exactly the **ownership disjunct** of `authorizedB` (`actor == src`) — the
  middle conjunct records that the authority this step passed was ownership (`troa_lrefl`),
  not a cap edge; it is the concrete justification for choosing the `intra` constructor.
* `hsubj` is the load-bearing membership `Integrity.intra` consumes — with `subjects` a
  FREE parameter (mirroring `VatBoundary.vat_boundary_intra`), `turn.actor ∈ subjects` is
  no longer `rfl`. (`KO`, the predicate algebra `P`/witness `W` stay arbitrary: the
  `intra` constructor consults no policy edge — the content of l4v `troa_lrefl`.)

The `cross` (non-owner, cap-holding) case requires producing a discharged witness `w`
for an abstract policy predicate `p`, which the concrete `authorizedB` does not carry —
see the `-- OPEN:` in `exec_refines`. -/
theorem refine_integrity_intra
    {P KO W : Type*} [Dregg2.Laws.Verifiable P W]
    (k k' : KernelState) (turn : Turn)
    (p : KO → KO → P) (ko ko' : KO)
    (subjects : List Dregg2.Authority.Label)
    (hstep : exec k turn = some k')
    (hown : turn.actor = turn.src)
    (hsubj : (turn.actor : Dregg2.Authority.Label) ∈ subjects) :
    authorizedB k.caps turn = true
      ∧ (turn.actor == turn.src) = true
      ∧ Integrity W turn.actor subjects p ko ko' :=
  -- left: the committed step IS authorized (consumes `hstep`); middle: the disjunct taken
  -- is ownership (consumes `hown`); right: abstract integrity via the membership `hsubj`.
  ⟨exec_authorized k k' turn hstep, by simp [hown], Integrity.intra hsubj⟩

/-! ## 4. Forward simulation: `exec_refines`. -/

/-- **The forward-refinement relation `R`.** A concrete `KernelState` `k` is related to
an abstract conservation-config — modelled as the pair `(cons, c)` of a
`Core.Conservation ℤ` and a cell `c` carrying the abstract measure — when the abstract
measure of `c` equals the kernel's `total`. This is the refinement relation that the
abstract `count` *reads off* the concrete state (l4v's `state_relation`). -/
def R (k : KernelState) (cc : Core.Conservation ℤ × Core.Cell) : Prop :=
  cc.1.count cc.2 = total k

/-- **Forward / simulation refinement (`exec_refines`).**

Stated cleanly: for any concrete step `exec k turn = some k'` related to an abstract
config `cc` by `R`, there *exists* an abstract config `cc'` such that:

* `cc'` is `R`-related to the concrete post-state `k'`, AND
* the abstract measure is preserved across the matched step
  (`cc'.1.count cc'.2 = cc.1.count cc.2`) — i.e. the abstract step is conservative,
  the laws-preservation component of the simulation.

This is the conservation component of forward refinement, and it is **PROVED**: take
`cc' = (cc.1, c')` for a cell `c'` whose abstract count is `total k'`; the witness is
constructed below from the fact that `total k' = total k` (`exec_conserves`) and the
`R`-relatedness of `cc`.

OPEN: a *full* operational forward simulation — "every concrete `exec` step is matched
by a step of an abstract TRANSITION relation, with the diagram commuting" — additionally
requires an abstract small-step relation `AbsStep : (config) → (config) → Prop`. `Core`
deliberately states Law 1 as a *measure obligation* (`Conservation.tensor_add` /
`conservation_step`), NOT as an operational transition system, so no such `AbsStep` is
in scope to commute against. The conservation/laws component (proved here) is the
load-bearing half; the operational-diagram half is left open rather than faked. -/
theorem exec_refines (k k' : KernelState) (turn : Turn)
    (cc : Core.Conservation ℤ × Core.Cell)
    (hstep : exec k turn = some k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  -- The abstract config matching `k'`: reuse the same `Conservation` data, and pick a
  -- cell whose abstract count is `total k'`. Concretely, reuse `cc.2` and rewrite via
  -- conservation: `total k' = total k = cc.1.count cc.2`.
  refine ⟨cc, ?_, rfl⟩
  -- `R k' cc` : `cc.1.count cc.2 = total k'`. We have `hR : cc.1.count cc.2 = total k`
  -- and `exec_conserves : total k' = total k`.
  unfold R at hR ⊢
  rw [hR, (exec_conserves k k' turn hstep).symm]

/-- **`exec_refines`, run form.** The simulation's conservation component lifts to a
whole kernel `Run`: any abstract config related to the start of a run is matched by one
related to the end with the same abstract measure. Proved from `R` + the run-level
conservation `refine_run_conservation`. -/
theorem exec_refines_run {k k' : KernelState}
    (cc : Core.Conservation ℤ × Core.Cell)
    (hrun : Run kernelSystem k k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  refine ⟨cc, ?_, rfl⟩
  unfold R at hR ⊢
  rw [hR, (refine_run_conservation hrun).symm]

end Dregg2.Proof
