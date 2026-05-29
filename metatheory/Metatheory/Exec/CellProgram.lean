/-
# Metatheory.Exec.CellProgram — the CellProgram DSL (the developer-facing coalgebra).

`dregg2 §1.5`: "the CellProgram IS the coalgebra structure-map". This module gives the
object a **developer writes** to determine a cell's admissibility, and shows its
DENOTATION is the executable coalgebra structure-map `denote : KernelState → Turn →
Option KernelState` — i.e. the `Boundary.TurnCoalg.step` for the kernel carrier.

A `CellProgram` is an ADDITIONAL gate layered ON TOP OF the kernel's own fail-closed
checks (`Exec.exec`): it decides which turns the cell will even *consider*, and only
those that it admits are then run through `Exec.exec` (which still enforces
conservation + authority). So a program can only ever *tighten* `exec`, never bypass it.

The keystones (PROVED, reusing `Kernel.exec_conserves` + `Execution.invariant_run`):
- `denote_conserves` — any turn a CellProgram admits-and-commits preserves `total`
  (because `denote` succeeds only when `exec` succeeds, and `exec` conserves);
- `denote_run_conserves` — conservation across an ENTIRE program run.

The link to `Boundary.TurnCoalg` is stated as `OPEN` where a full coalgebra instance
would need machinery (a concrete `Obs`/`AdmissibleTurn` and a totalising successor) not
present at this layer; the executable correspondence (`denote` = the partial structure
map) is given concretely.
-/
import Metatheory.Exec.Kernel
import Metatheory.Boundary
import Metatheory.Execution
import Metatheory.Tactics

namespace Metatheory.Exec

open Metatheory.Execution

/-! ## The guard language — a small DSL the developer writes -/

/-- **`Guard`** — a tiny, computable predicate language a developer composes to express a
cell's admissibility policy. Each constructor is a balance/authority predicate over the
current `KernelState` and the proposed `Turn`; `Guard.and`/`Guard.or` build conjunctions
and disjunctions. This is the *surface syntax*; `Guard.eval` interprets it to a `Bool`. -/
inductive Guard where
  /-- Always admit (the trivial policy). -/
  | tt        : Guard
  /-- Never admit. -/
  | ff        : Guard
  /-- Admit only if the kernel itself would authorize the actor over `src`. -/
  | authorized : Guard
  /-- Admit only if the transfer amount is at most `cap` (a per-turn balance ceiling). -/
  | amountLe  : ℤ → Guard
  /-- Admit only if `src`'s balance after the move stays ≥ `floor` (a reserve floor). -/
  | reserveSrc : ℤ → Guard
  /-- Admit only when the actor moves its OWN resource (`actor = src`; no delegated caps). -/
  | selfOnly  : Guard
  /-- Conjunction. -/
  | and       : Guard → Guard → Guard
  /-- Disjunction. -/
  | or        : Guard → Guard → Guard

/-- **Interpret a `Guard` to a `Bool`** against a state and a proposed turn. Computable;
this is what turns the DSL surface into the admissibility decision. -/
def Guard.eval (g : Guard) (k : KernelState) (turn : Turn) : Bool :=
  match g with
  | .tt           => true
  | .ff           => false
  | .authorized   => authorizedB k.caps turn
  | .amountLe c   => turn.amt ≤ c
  | .reserveSrc f => f ≤ k.bal turn.src - turn.amt
  | .selfOnly     => turn.actor == turn.src
  | .and a b      => a.eval k turn && b.eval k turn
  | .or a b       => a.eval k turn || b.eval k turn

/-! ## `CellProgram` — the object the developer writes -/

/-- **`CellProgram`** — the developer-authored object that determines a cell's
admissibility. At minimum it carries a computable admissibility guard `admits`; the
canonical way to build one is from a `Guard` (`ofGuard`), but `admits` may be any
`KernelState → Turn → Bool` (so handwritten policies are first-class). -/
structure CellProgram where
  /-- The admissibility guard: the program decides which turns it will even consider. -/
  admits : KernelState → Turn → Bool

/-- Build a `CellProgram` from a `Guard` of the DSL (the intended developer path). -/
def CellProgram.ofGuard (g : Guard) : CellProgram where
  admits := fun k turn => g.eval k turn

/-- The trivial program: admit everything (so `denote` collapses exactly to `exec`). -/
def CellProgram.permissive : CellProgram := CellProgram.ofGuard .tt

/-! ## `denote` — the executable coalgebra structure-map -/

/-- **`denote` — run a turn through the program.** The program is an ADDITIONAL gate over
the kernel's own checks: a turn commits iff the program `admits` it AND the kernel's
`exec` accepts it. This is the executable coalgebra structure-map (the partial
`KernelState → Turn → Option KernelState`); `Boundary.TurnCoalg.step` is its totalised
shape. -/
def CellProgram.denote (p : CellProgram) (k : KernelState) (turn : Turn) :
    Option KernelState :=
  if p.admits k turn then exec k turn else none

/-- **`denote` only ever tightens `exec`.** Whenever the program commits a turn, the
kernel commits the SAME turn to the SAME state — the program never produces a transition
the kernel would not. (The witness that `denote` cannot bypass `exec`.) -/
theorem denote_eq_exec_on_success (p : CellProgram) (k k' : KernelState) (turn : Turn)
    (h : p.denote k turn = some k') : exec k turn = some k' := by
  unfold CellProgram.denote at h
  by_cases hp : p.admits k turn = true
  · rw [if_pos hp] at h; exact h
  · simp only [Bool.not_eq_true] at hp
    rw [if_neg (by simp [hp])] at h
    exact absurd h (by simp)


/-! ## Conservation: a CellProgram cannot bypass the resource law -/

/-- **`denote_conserves` — PROVED.** Any turn a `CellProgram` admits-and-commits still
preserves `total`. The program only gates `exec`; it never bypasses conservation. Proved
directly from `Kernel.exec_conserves` via `denote_eq_exec_on_success`. -/
theorem denote_conserves (p : CellProgram) (k k' : KernelState) (turn : Turn)
    (h : p.denote k turn = some k') : total k' = total k :=
  exec_conserves k k' turn (denote_eq_exec_on_success p k k' turn h)

/-! ## The CellProgram-induced execution system and whole-run conservation -/

/-- The `Execution.System` a `CellProgram` induces: a step is any turn the PROGRAM
admits-and-commits (a tighter `Step` than `kernelSystem`'s). -/
def CellProgram.system (p : CellProgram) : System where
  Config := KernelState
  Step k k' := ∃ turn, p.denote k turn = some k'

/-- **`denote_run_conserves` — PROVED.** Conservation across an ENTIRE program run:
`total` is invariant along any run of the program-induced system. Lifts the per-turn
`denote_conserves` to the whole execution via `Execution.invariant_run`, the same shape
as `Kernel.kernel_run_conserves`. -/
theorem denote_run_conserves (p : CellProgram) {k k' : KernelState}
    (hrun : Run p.system k k') : total k' = total k := by
  have hpres : StepInvariant p.system (fun c => total c = total k) := by
    intro a b ha hstep
    obtain ⟨turn, hturn⟩ := hstep
    rw [denote_conserves p a b turn hturn]; exact ha
  exact invariant_run hpres hrun rfl

/-- A program-induced step is in particular a kernel step: the program system REFINES the
kernel system (every program transition is a kernel transition). PROVED. -/
theorem system_refines_kernel (p : CellProgram) {k k' : KernelState}
    (h : p.system.Step k k') : kernelSystem.Step k k' := by
  obtain ⟨turn, hturn⟩ := h
  exact ⟨turn, denote_eq_exec_on_success p k k' turn hturn⟩

/-! ## Link to `Boundary.TurnCoalg` — the program AS the coalgebra structure-map

`dregg2 §1.5`: "the CellProgram IS the coalgebra structure-map". The functor is
`F X = Obs × (AdmissibleTurn ⇒ X)` (`Boundary.F`). For the kernel carrier the
denotation `denote : KernelState → Turn → Option KernelState` is precisely the *partial*
transition component `AdmissibleTurn ⇒ X` of that structure map, with:

  * carrier            `X            = KernelState`
  * input alphabet     `AdmissibleTurn = Turn` (the program decides admissibility via
                                          `p.admits`, exactly the `AdmissibleTurn` guard);
  * transition         `next x t      = denote x t`  (partial — `Option`, fail-closed).

The correspondence below makes the transition component literal. Note `denote` lands in
`Option KernelState`, i.e. the *partial* structure map; `Boundary.TurnCoalg.step` is the
TOTAL map `Carrier → Obs × (AdmissibleTurn → Carrier)`. The two are reconciled by
(a) restricting `AdmissibleTurn` to the turns the program actually admits-and-commits
(making the map total on that subtype), and (b) choosing an `Obs`. -/

/-- **The (partial) coalgebra transition component a `CellProgram` denotes** — literally
`denote`, repackaged as a `KernelState → Turn → Option KernelState` to read as the
`AdmissibleTurn ⇒ Carrier` arrow of `Boundary.F`. -/
def CellProgram.coalgTransition (p : CellProgram) :
    KernelState → Turn → Option KernelState :=
  p.denote

/-- The transition component is definitionally `denote` (the correspondence is literal,
not up-to-anything). PROVED. -/
theorem CellProgram.coalgTransition_eq (p : CellProgram) (k : KernelState) (turn : Turn) :
    p.coalgTransition k turn = p.denote k turn := rfl

-- OPEN: A full `Boundary.TurnCoalg KernelState (committed-turn subtype)` *instance*
-- (a TOTAL `step : Carrier → Obs × (AdmissibleTurn → Carrier)`) needs two pieces not
-- present at this layer: (1) a concrete `Obs` (the cell's externally-visible badge —
-- the PI surface), and (2) a totalisation of `denote` along an `AdmissibleTurn` subtype
-- `{t // (p.denote k t).isSome}` so the successor is again a `KernelState` rather than
-- `Option KernelState`. The dependency of that subtype on the *current* `k` makes the
-- successor map dependent (a sigma-coalgebra), which the `Boundary.F`/`TurnCoalg` shape
-- here (uniform `AdmissibleTurn`) does not yet accommodate. The executable
-- correspondence (`coalgTransition = denote` = the partial structure map) is the honest,
-- proved content; the total instance awaits the `Obs`/PI-surface layer.

/-! ## It runs (`#eval`) — reusing `Kernel.s0`/`t1`/`tBad`. -/

/-- A reserve-floor policy: admit only self-moves that leave ≥ 50 in `src` (a developer
guard composed from the DSL). -/
def reservePolicy : CellProgram :=
  CellProgram.ofGuard (.and .selfOnly (.reserveSrc 50))

#eval (CellProgram.permissive.denote s0 t1).isSome     -- true (collapses to exec)
#eval (CellProgram.permissive.denote s0 tBad).isSome    -- false (exec rejects)
#eval (reservePolicy.denote s0 t1).isSome               -- true (100-30=70 ≥ 50)
#eval (reservePolicy.denote s0 { t1 with amt := 60 }).isSome  -- false (100-60=40 < 50)
#eval (CellProgram.permissive.denote s0 t1).map total   -- some 105 (conserved)

end Metatheory.Exec
