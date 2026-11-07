/-
# Dregg2.Circuit.Emit.AutomataflStepBackend — LEG A, the BACK END at ARBITRARY `n`.

`AutomataflStepRefine` §2.5 made the FRONT-END gate membership `n`-generic (board range · coordinate
decompose · both auto one-hots · the auto pin · the four ray scans), `AutomataflStepCoord` made the
`evalH` bridge / one-hot / coordinate reads `n`-generic, and `AutomataflStepCapstone` closed all four
rays `∀ n` (`raycast_*_of_satN`). What stayed pinned at `n = 2` was the REFINEMENT side of the
BACK END: ~2000 lines of `AutomataflStepRefine` written against the ABSOLUTE column literals
`58`/`105`/`152`/`209` with `by decide` membership over the concrete 418-constraint list.

This file adds the `∀ n` TWINS alongside those (nothing in `AutomataflStepRefine` is rewritten —
exactly how §D.7/§D.8 did it for Leg R):

* **§1 — pure `Head` plumbing.** `varsVal` is multiplicative over `++`, so the two back-end head
  COMBINATORS evaluate in closed form at ARBITRARY columns: `evalHStep_forcedGe0Term`
  (`forced_ge0`'s recomposed head `2·ib·d + ib − d − 1` for ANY `d`) and `evalHStep_caseGateHead`
  (`assert_case`'s gate `∏gate · (field − formula)` for ANY gate/formula). Both replace the
  `n = 2`-only `… .eval e.loc = ⟨explicit sum⟩ from rfl` rewrites, which only ever worked because
  every column was a numeral.
* **§2 — `n`-GENERIC BACK-END STRUCTURED MEMBERSHIP** over the parametric bases
  (`NGen.A_DECIDE_X_BASE n` / `A_DECIDE_Y_BASE n` / `A_CHOOSE_BASE n` / `A_STEP_BASE n`), climbed with
  explicit `mem_append_left`/`mem_append_right`/`mem_map`/`mem_range` (never `simp`/`tauto`, which
  `whnf` the symbolic folds and time out) — `decideAxisConstraints` internals in full, plus
  `chooseOffsetConstraints n`, `stepConstraints n` and the board-update fold.
* **§3 — the `forced_ge0` guard soundness `∀ n`** (`ge0N_of_sat`), descriptor-generic and column-
  generic, resting on `forcedGe0_coreW` (the widened no-wrap window; the `n = 2` `forcedGe0_core`
  hard-codes `|D| ≤ 100`).
* **§4 — the `decideAxis` chain over `A_*_BASE n`, `∀ n`**: `da_ipw_sel`/`da_inw_sel` (the size-3
  `what`-alphabet one-hots — CONSTANT width in `n`, but at symbolic base), the six guard bits
  `gpd`/`gnd`/`lt`/`gt`/`le`/`gm` and the `min` gadget.
* **§5 — the nine decode cases at ARBITRARY distance.** The `AutomataflStepRefine.decode_*` family is
  PURE but takes `hpd : pd = 1 ∨ pd = 2` — an `n = 2` hypothesis. Restated here as `1 ≤ pd`
  (`decodeN_*`), which is what a ray at board size `n` actually gives.
* **§6 — `decideAxis_x_soundN` / `decideAxis_y_soundN`**: `decodeDecision = evaluateAxis` at
  ARBITRARY `n`, consuming `AutomataflStepCapstone.rayN_of_sat` for the distances.

## The named width ceiling (a REAL descriptor fact, surfaced not papered over)

`decide_axis`'s six comparison gadgets are `SMALL_RBITS = 5` bits wide, so the range witness `S` they
carry satisfies `0 ≤ S ≤ 31`. The compared magnitudes are distances in `[1, n]`, so at `n ≥ 34` a
LEGITIMATE trace has no satisfying 5-bit decomposition — the emitted `decide_axis` block is
UNSATISFIABLE there. That is a satisfiability ceiling, not a soundness hole: the SAT⇒SEM direction
proven here needs only the no-wrap window, which this file carries as the EXPLICIT hypothesis
`hnwin : (n : ℤ) ≤ 1000000`. The deployed `n = 11` sits far inside both.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`, no
assumed hypothesis: every premise is either an emitted-gate membership (proven), a canonicality
envelope (`StepCanon`, inhabited by the `AutomataflStepRefine` §6 witness) or an explicit arithmetic
window on `n`.
-/
import Dregg2.Circuit.Emit.AutomataflStepCoord
import Dregg2.Circuit.Emit.AutomataflStepCapstone

namespace Dregg2.Circuit.Emit.AutomataflStepBackend

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflStepCoord
open Dregg2.Circuit.Emit.AutomataflCoord (varsVal termVal sum_map_mul_left)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Games.Automatafl (Board Coord Particle Dir Decision Raycast evaluateAxis)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — Pure `Head` plumbing for the BACK-END combinators.

The `n = 2` proofs computed each back-end gate with `… .eval e.loc = ⟨explicit sum⟩ from rfl`. That
`rfl` only closes when every column is a NUMERAL. Here the two back-end head combinators
(`forcedGe0Term`, `assertCase`) are evaluated in CLOSED FORM at arbitrary columns, so the same
extraction runs at `A_DECIDE_X_BASE n`. -/

/-- A `*`-fold factors its start value out. -/
theorem foldl_mul_start (a : Nat → ℤ) (L : List Nat) (s : ℤ) :
    L.foldl (fun acc v => acc * a v) s = s * L.foldl (fun acc v => acc * a v) 1 := by
  induction L generalizing s with
  | nil => simp
  | cons c cs ih => simp only [List.foldl_cons]; rw [ih (s * a c), ih (1 * a c)]; ring

/-- `varsVal` in `foldl`-from-`1` normal form (the empty product is `1`). -/
theorem varsVal_eq_foldl (a : Nat → ℤ) (L : List Nat) :
    varsVal a L = L.foldl (fun acc v => acc * a v) 1 := by
  cases L with
  | nil => rfl
  | cons c cs => simp only [varsVal, List.foldl_cons, one_mul]

/-- `varsVal` is MULTIPLICATIVE over `++`. This is what makes `assert_case`'s `gate ++ t.2` product
factor into `∏gate · ∏t.2`. -/
theorem varsVal_append (a : Nat → ℤ) (L M : List Nat) :
    varsVal a (L ++ M) = varsVal a L * varsVal a M := by
  rw [varsVal_eq_foldl, varsVal_eq_foldl a L, varsVal_eq_foldl a M, List.foldl_append,
    foldl_mul_start a M (L.foldl (fun acc v => acc * a v) 1)]

/-- `varsVal` on a cons: the product peels its head. -/
theorem varsVal_cons (a : Nat → ℤ) (c : Nat) (L : List Nat) :
    varsVal a (c :: L) = a c * varsVal a L := by
  have h := varsVal_append a [c] L
  simpa [varsVal] using h

/-- A `foldl` over an ARBITRARY element type whose every step adds a fixed `delta y`. The
`List Nat`-typed `evalHStep_foldl_step` cannot see the `List (ℤ × List Nat)` term folds the two
back-end combinators are built from. -/
theorem evalHStep_foldl_gen {α : Type _} (a : Nat → ℤ) (init : Head) (ys : List α)
    (step : Head → α → Head) (delta : α → ℤ)
    (hstep : ∀ h y, evalHStep (step h y) a = evalHStep h a + delta y) :
    evalHStep (ys.foldl step init) a = evalHStep init a + (ys.map delta).sum := by
  induction ys generalizing init with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]; ring

/-- The term-sum of a `Head` is its value minus its constant. -/
theorem termSum_eq (a : Nat → ℤ) (h : Head) :
    (h.terms.map (termVal a)).sum = evalHStep h a - h.const := by
  simp [evalHStep]

/-- **`forced_ge0`'s recomposed head, in closed form at ANY columns.** `2·ib·d + ib − d − 1`, for an
ARBITRARY inner head `d` — the `n = 2` proofs had to spell this out per numeral base. -/
theorem evalHStep_forcedGe0Term (a : Nat → ℤ) (ib : Nat) (dh : Head) :
    evalHStep (forcedGe0Term ib dh) a
      = 2 * a ib * evalHStep dh a + a ib - evalHStep dh a - 1 := by
  have hh1 : evalHStep (dh.terms.foldl
        (fun h (t : ℤ × List Nat) => h.addProd (2 * t.1) (ib :: t.2)) Head.zero) a
      = 2 * a ib * (evalHStep dh a - dh.const) := by
    rw [evalHStep_foldl_gen a Head.zero dh.terms _
      (fun t => 2 * t.1 * (a ib * varsVal a t.2))
      (by intro h t; rw [evalHStep_addProd, varsVal_cons]; try ring), evalHStep_zero]
    rw [show (fun t : ℤ × List Nat => 2 * t.1 * (a ib * varsVal a t.2))
          = (fun t : ℤ × List Nat => (2 * a ib) * termVal a t) from by
        funext t; simp only [termVal]; try ring]
    rw [sum_map_mul_left, termSum_eq]; ring
  simp only [forcedGe0Term]
  rw [evalHStep_addConst, evalHStep_append, evalHStep_scale, evalHStep_addLin, evalHStep_addProd,
    hh1]
  simp only [varsVal, List.foldl_nil]
  ring

/-- `assert_case`'s gate head (the `if formula.const == 0` branch the nine emitted cases all take —
every case formula in the table has constant `0`). -/
def caseGateHead (gate : List Nat) (fieldCol : Nat) (fm : Head) : Head :=
  let h0 := Head.zero.addProd 1 (gate ++ [fieldCol])
  fm.terms.foldl (fun h (t : ℤ × List Nat) => h.addProd (-t.1) (gate ++ t.2)) h0

/-- The emitted `assertCase` IS `cgH (caseGateHead …)` whenever the formula has zero constant. -/
theorem assertCase_eq (gate : List Nat) (fieldCol : Nat) (fm : Head) (hconst : fm.const = 0) :
    assertCase gate fieldCol fm = cgH (caseGateHead gate fieldCol fm) := by
  simp only [assertCase, caseGateHead, hconst]
  norm_num

/-- **`assert_case`'s gate, in closed form at ANY columns**: `∏gate · (field − formula)`. This single
lemma replaces the nine per-case `rfl` expansions the `n = 2` chain needed. -/
theorem evalHStep_caseGateHead (a : Nat → ℤ) (gate : List Nat) (fieldCol : Nat) (fm : Head)
    (hconst : fm.const = 0) :
    evalHStep (caseGateHead gate fieldCol fm) a
      = varsVal a gate * (a fieldCol - evalHStep fm a) := by
  simp only [caseGateHead]
  rw [evalHStep_foldl_gen a _ fm.terms _
    (fun t => -t.1 * (varsVal a gate * varsVal a t.2))
    (by intro h t; rw [evalHStep_addProd, varsVal_append]; try ring)]
  rw [evalHStep_addProd, evalHStep_zero, varsVal_append]
  rw [show (fun t : ℤ × List Nat => -t.1 * (varsVal a gate * varsVal a t.2))
        = (fun t : ℤ × List Nat => (-varsVal a gate) * termVal a t) from by
      funext t; simp only [termVal]; try ring]
  rw [sum_map_mul_left, termSum_eq, hconst]
  have hv1 : varsVal a [fieldCol] = a fieldCol := by simp [varsVal]
  rw [hv1]
  ring

/-- The `range_nonneg` recomposition over a `forced_ge0` term, at `SMALL_RBITS = 5`: the head is the
`forced_ge0` witness minus the 5-bit sum. Column-generic. -/
theorem evalHStep_ge0Bits (a : Nat → ℤ) (ib bit0 : Nat) (dh : Head) :
    evalHStep ((List.range SMALL_RBITS).foldl
        (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) ((bitsFrom bit0 SMALL_RBITS)[k]!))
        (forcedGe0Term ib dh)) a
      = (2 * a ib * evalHStep dh a + a ib - evalHStep dh a - 1)
        - ((2 : ℤ) ^ 0 * a (bit0 + 0) + (2 : ℤ) ^ 1 * a (bit0 + 1) + (2 : ℤ) ^ 2 * a (bit0 + 2)
           + (2 : ℤ) ^ 3 * a (bit0 + 3) + (2 : ℤ) ^ 4 * a (bit0 + 4)) := by
  rw [evalHStep_foldl_addLinF, evalHStep_forcedGe0Term]
  have hb : ∀ k, k < SMALL_RBITS → (bitsFrom bit0 SMALL_RBITS)[k]! = bit0 + k := by
    intro k hk; exact getElem!_range_map SMALL_RBITS (bit0 + ·) hk
  have hmap : ((List.range SMALL_RBITS).map
        (fun k => -((2 : ℤ) ^ k) * a ((bitsFrom bit0 SMALL_RBITS)[k]!)))
      = (List.range SMALL_RBITS).map (fun k => -((2 : ℤ) ^ k) * a (bit0 + k)) := by
    apply List.map_congr_left; intro k hk; rw [hb k (List.mem_range.mp hk)]
  rw [hmap]
  have hr : List.range SMALL_RBITS = [0, 1, 2, 3, 4] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-! ## §2 — n-GENERIC BACK-END STRUCTURED MEMBERSHIP.

`(automataflStepDescN n).constraints = (frontEnd n ++ backEnd n) ++ commit n` and
`backEnd n = decideAxis(x) ++ decideAxis(y) ++ chooseOffset n ++ step n` (left-associated). Every
climb below is explicit — `List.mem_append_left`/`mem_append_right`/`mem_map`/`mem_range` — because
`simp`/`tauto` `whnf` the symbolic `List.range n` folds. -/

theorem mem_constraintsN_of_backEnd {n : Nat} {x : VmConstraint2}
    (h : x ∈ NGen.backEndConstraints n) : x ∈ (automataflStepDescN n).constraints := by
  rw [constraintsN_eq]; exact List.mem_append_left _ (List.mem_append_right _ h)

/-- The `xdec` `decide_axis` block, at `NGen.A_DECIDE_X_BASE n`, over rays XP/XN. -/
theorem mem_be_decideX {n : Nat} {x : VmConstraint2}
    (h : x ∈ decideAxisConstraints (NGen.A_DECIDE_X_BASE n)
            (NGen.rWhat n 0) (NGen.rWhat n 1) (NGen.rDist n 0) (NGen.rDist n 1)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_constraintsN_of_backEnd; unfold NGen.backEndConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

/-- The `ydec` `decide_axis` block, at `NGen.A_DECIDE_Y_BASE n`, over rays YP/YN. -/
theorem mem_be_decideY {n : Nat} {x : VmConstraint2}
    (h : x ∈ decideAxisConstraints (NGen.A_DECIDE_Y_BASE n)
            (NGen.rWhat n 2) (NGen.rWhat n 3) (NGen.rDist n 2) (NGen.rDist n 3)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_constraintsN_of_backEnd; unfold NGen.backEndConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

/-- The `choose_offset` block, at `NGen.A_CHOOSE_BASE n`. -/
theorem mem_be_choose {n : Nat} {x : VmConstraint2} (h : x ∈ NGen.chooseOffsetConstraints n) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_constraintsN_of_backEnd; unfold NGen.backEndConstraints
  exact List.mem_append_left _ (List.mem_append_right _ h)

/-- The step + board-update block, at `NGen.A_STEP_BASE n`. -/
theorem mem_be_step {n : Nat} {x : VmConstraint2} (h : x ∈ NGen.stepConstraints n) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_constraintsN_of_backEnd; unfold NGen.backEndConstraints
  exact List.mem_append_right _ h

/-! ### §2.1 — `forced_ge0` / `range_nonneg` family-internal membership (base-generic). -/

theorem mem_ge0_ib (ib : Nat) (dh : Head) (bits : List Nat) :
    cg (gBin ib) ∈ forcedGe0Constraints ib dh bits := List.mem_cons_self

theorem mem_ge0_bit (ib : Nat) (dh : Head) (bits : List Nat) {c : Nat} (hc : c ∈ bits) :
    cg (gBin c) ∈ forcedGe0Constraints ib dh bits :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem mem_ge0_head (ib : Nat) (dh : Head) (bits : List Nat) :
    cgH ((List.range bits.length).foldl
          (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) (bits[k]!)) (forcedGe0Term ib dh))
      ∈ forcedGe0Constraints ib dh bits :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem mem_bitsFrom (start len k : Nat) (hk : k < len) : start + k ∈ bitsFrom start len :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

/-! ### §2.2 — `decideAxisConstraints` internals, at an ARBITRARY base `b`.

`decideAxisConstraints` is already fully base-parametric in the emitter (every internal offset is
`b + k`), so ONE set of membership lemmas serves both axes at every `n`. -/

/-- The zeta-expanded shape of `decideAxisConstraints` — 12 left-associated segments. `rfl`
checks that this is the emitted object, so the climbs below cannot drift from it. -/
theorem decideAxis_unfold (b pw nw pd nd : Nat) :
    decideAxisConstraints b pw nw pd nd
      = [ cg (memberExpr b [0, 1, 2, 3]) ]
        ++ [ cg (gBin (b + 1)) ]
        ++ oneHotConstraints [b + 4, b + 5, b + 6] (Head.lin 1 pw)
        ++ oneHotConstraints [b + 7, b + 8, b + 9] (Head.lin 1 nw)
        ++ forcedGe0Constraints (b + 10) ((Head.lin 1 pd).addConst (-2))
             (bitsFrom (b + 11) SMALL_RBITS)
        ++ forcedGe0Constraints (b + 16) ((Head.lin 1 nd).addConst (-2))
             (bitsFrom (b + 17) SMALL_RBITS)
        ++ forcedGe0Constraints (b + 22) (((Head.lin 1 nd).addLin (-1) pd).addConst (-1))
             (bitsFrom (b + 23) SMALL_RBITS)
        ++ forcedGe0Constraints (b + 28) (((Head.lin 1 pd).addLin (-1) nd).addConst (-1))
             (bitsFrom (b + 29) SMALL_RBITS)
        ++ forcedGe0Constraints (b + 34) ((Head.lin 1 nd).addLin (-1) pd)
             (bitsFrom (b + 35) SMALL_RBITS)
        ++ [ cgH ((((Head.lin 1 (b + 40)).addProd (-1) [b + 34, pd]).addLin (-1) nd).addProd 1
                    [b + 34, nd]) ]
        ++ forcedGe0Constraints (b + 41) ((Head.lin 1 (b + 40)).addConst (-2))
             (bitsFrom (b + 42) SMALL_RBITS)
        ++ decideCasesConstraints [b + 4, b + 5, b + 6] [b + 7, b + 8, b + 9]
             [b, b + 1, b + 2, b + 3] pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 34)
             (b + 41) := rfl

section DAMem
variable (b pw nw pd nd : Nat)

theorem mem_da_variant :
    cg (memberExpr b [0, 1, 2, 3]) ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_singleton.mpr rfl

theorem mem_da_posBin : cg (gBin (b + 1)) ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem mem_da_ipw {x : VmConstraint2}
    (h : x ∈ oneHotConstraints [b + 4, b + 5, b + 6] (Head.lin 1 pw)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_inw {x : VmConstraint2}
    (h : x ∈ oneHotConstraints [b + 7, b + 8, b + 9] (Head.lin 1 nw)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_gpd {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 10) ((Head.lin 1 pd).addConst (-2))
           (bitsFrom (b + 11) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_gnd {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 16) ((Head.lin 1 nd).addConst (-2))
           (bitsFrom (b + 17) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_lt {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 22) (((Head.lin 1 nd).addLin (-1) pd).addConst (-1))
           (bitsFrom (b + 23) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_gt {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 28) (((Head.lin 1 pd).addLin (-1) nd).addConst (-1))
           (bitsFrom (b + 29) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_le {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 34) ((Head.lin 1 nd).addLin (-1) pd)
           (bitsFrom (b + 35) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_minHead :
    cgH ((((Head.lin 1 (b + 40)).addProd (-1) [b + 34, pd]).addLin (-1) nd).addProd 1 [b + 34, nd])
      ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem mem_da_gm {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (b + 41) ((Head.lin 1 (b + 40)).addConst (-2))
           (bitsFrom (b + 42) SMALL_RBITS)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_da_cases {x : VmConstraint2}
    (h : x ∈ decideCasesConstraints [b + 4, b + 5, b + 6] [b + 7, b + 8, b + 9]
           [b, b + 1, b + 2, b + 3] pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 34)
           (b + 41)) :
    x ∈ decideAxisConstraints b pw nw pd nd := by
  rw [decideAxis_unfold]
  exact List.mem_append_right _ h

end DAMem

/-! ### §2.3 — the nine-case truth table, base-generic.

`decideCasesConstraints` is a `flatMap` over a LITERAL nine-entry table whose entries are `Head`s over
symbolic columns. `casesTable` re-states that table (checked `rfl` against the emitter by
`decideCases_eq`), so a specific case's `assert_case` gate is located by `mem_flatMap` + `mem_map`
without ever `decide`-ing a concrete list. -/

/-- The emitter's nine `(pw,nw)` case formulas, re-stated so membership can name an entry. -/
def casesTable (pd nd minC gpd gnd lt gt gm : Nat) : List ((Nat × Nat) × List Head) :=
  [ ((2, 1), [Head.lin 3 gpd, Head.lin 1 gpd, Head.zero.addProd 1 [gpd, pd],
              Head.zero.addProd 1 [gpd, nd]])
  , ((1, 2), [Head.lin 3 gnd, Head.zero, Head.zero.addProd 1 [gnd, nd],
              Head.zero.addProd 1 [gnd, pd]])
  , ((1, 1), [(Head.lin 2 lt).addLin 2 gt, Head.lin 1 gt, Head.zero,
              (Head.zero.addProd 1 [lt, minC]).addProd 1 [gt, minC]])
  , ((1, 0), [Head.lin 2 gnd, Head.zero, Head.zero, Head.zero.addProd 1 [gnd, pd]])
  , ((0, 1), [Head.lin 2 gpd, Head.lin 1 gpd, Head.zero, Head.zero.addProd 1 [gpd, nd]])
  , ((2, 2), [(Head.zero.addProd 1 [lt, gm]).addProd 1 [gt, gm], Head.zero.addProd 1 [lt, gm],
              (Head.zero.addProd 1 [lt, gm, minC]).addProd 1 [gt, gm, minC], Head.zero])
  , ((2, 0), [Head.lin 1 gpd, Head.lin 1 gpd, Head.zero.addProd 1 [gpd, pd], Head.zero])
  , ((0, 2), [Head.lin 1 gnd, Head.zero, Head.zero.addProd 1 [gnd, nd], Head.zero])
  , ((0, 0), [Head.zero, Head.zero, Head.zero, Head.zero]) ]

theorem decideCases_eq (ipw inw fields : List Nat)
    (pd nd minC gpd gnd lt gt le gm : Nat) :
    decideCasesConstraints ipw inw fields pd nd minC gpd gnd lt gt le gm
      = (casesTable pd nd minC gpd gnd lt gt gm).flatMap
          (fun (c : (Nat × Nat) × List Head) =>
            (List.range 4).map (fun (k : Nat) =>
              assertCase [ipw[c.1.1]!, inw[c.1.2]!] (fields[k]!) ((c.2)[k]!))) := rfl

/-- Locate ONE `assert_case` gate: the case entry (by membership in the table) and the field index. -/
theorem mem_decideCases {ipw inw fields : List Nat} {pd nd minC gpd gnd lt gt le gm : Nat}
    {ij : Nat × Nat} {fs : List Head}
    (hc : (ij, fs) ∈ casesTable pd nd minC gpd gnd lt gt gm) {k : Nat} (hk : k < 4) :
    assertCase [ipw[ij.1]!, inw[ij.2]!] (fields[k]!) (fs[k]!)
      ∈ decideCasesConstraints ipw inw fields pd nd minC gpd gnd lt gt le gm := by
  rw [decideCases_eq]
  exact List.mem_flatMap.mpr ⟨(ij, fs), hc, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩

/-! ### §2.4 — `chooseOffsetConstraints n` and `stepConstraints n` segment membership.

Not consumed by the `decide_axis` chain below — these are the FOUNDATION the next lane
(`chooseOffset` / `automatonOffset` / the `astep` capstone) stands on, landed here so that lane never
has to touch a frozen numeral. -/

/-- `col` is pinned boolean and to the column rule; `ox`/`oy` to the cardinal alphabet. Each is a
`∀ n` membership at the parametric `A_CHOOSE_BASE n` (the frozen `n = 2` numerals `206`/`207`/`208`
are gone). -/
theorem mem_co_colBin (n : Nat) :
    cg (gBin (NGen.A_CHOOSE_BASE n + 54)) ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem mem_co_colRule (n : Nat) :
    cgH ((Head.lin 1 (NGen.A_CHOOSE_BASE n + 54)).addConst (-COL_RULE))
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem mem_co_oxMem (n : Nat) :
    cg (memberExpr (NGen.A_CHOOSE_BASE n + 55) [-1, 0, 1])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem mem_co_oyMem (n : Nat) :
    cg (memberExpr (NGen.A_CHOOSE_BASE n + 56) [-1, 0, 1])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

/-- The score-compare `sgt` guard block (`sx − sy − 1 ≥ 0`) at `A_CHOOSE_BASE n` — first segment. -/
theorem mem_co_sgt (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_CHOOSE_BASE n)
          (((scoreHead (NGen.A_DECIDE_X_BASE n) (NGen.A_DECIDE_X_BASE n + 2)
                (NGen.A_DECIDE_X_BASE n + 3)).append
             ((scoreHead (NGen.A_DECIDE_Y_BASE n) (NGen.A_DECIDE_Y_BASE n + 2)
                (NGen.A_DECIDE_Y_BASE n + 3)).scale (-1))).addConst (-1))
          (bitsFrom (NGen.A_CHOOSE_BASE n + 1) SCORE_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact h

/-- The `xmove = [xVar ≥ 1]` guard block at `A_CHOOSE_BASE n + 42`. -/
theorem mem_co_xmove (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_CHOOSE_BASE n + 42)
          ((Head.lin 1 (NGen.A_DECIDE_X_BASE n)).addConst (-1))
          (bitsFrom (NGen.A_CHOOSE_BASE n + 43) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `ymove = [yVar ≥ 1]` guard block at `A_CHOOSE_BASE n + 48`. -/
theorem mem_co_ymove (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_CHOOSE_BASE n + 48)
          ((Head.lin 1 (NGen.A_DECIDE_Y_BASE n)).addConst (-1))
          (bitsFrom (NGen.A_CHOOSE_BASE n + 49) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The board-UPDATE gate for cell `c` — the `n`-generic locator the next lane needs (`new[c]` is
forced from `old[c]`, the move mask `m` and the two `sel_target` one-hots). -/
theorem mem_step_update (n c : Nat) (hc : c < NGen.KK n) :
    cgH (((((Head.lin 1 (NGen.new n c)).addLin (-1) (NGen.old n c)).addProd (-AUTO)
              [NGen.A_STEP_BASE n + 34 + 2 * n,
               ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 2 * n + j))[c / n]!,
               ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 3 * n + j))[c % n]!]).addProd 1
              [NGen.A_STEP_BASE n + 34 + 2 * n,
               ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 2 * n + j))[c / n]!,
               ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 3 * n + j))[c % n]!,
               NGen.old n c]).addProd 1
              [NGen.A_STEP_BASE n + 34 + 2 * n, NGen.selRow n (c / n), NGen.selCol n (c % n),
               NGen.old n c])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step
  show _ ∈ _ ++ _
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩

/-! ## §3 — the `forced_ge0` guard soundness, `∀ n`, descriptor- and column-generic. -/

/-- Two integers inside `[−10⁹, 10⁹]` congruent mod `p` are equal (`2·10⁹ < p = 2013265921`). Wider
than `AutomataflStepRefine.eq_of_modEq_win`, which is what pins its `forcedGe0_core` to `|D| ≤ 100`
— an `n = 2` luxury. -/
theorem eq_of_modEq_wide {a b : ℤ} (ha : -1000000000 ≤ a ∧ a ≤ 1000000000)
    (hb : -1000000000 ≤ b ∧ b ≤ 1000000000) (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd; obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb; omega

/-- **The `forced_ge0` NO-WRAP heart at board-scale magnitudes.** Identical in content to
`AutomataflStepRefine.forcedGe0_core`, with the `|D| ≤ 100` / `S ≤ 31` windows widened to `10⁶` so a
distance in `[1, n]` fits for every `n` this file admits. -/
theorem forcedGe0_coreW {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 1000000)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -1000000 ≤ D) (hDhi : D ≤ 1000000) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0 : ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_wide (by omega) (by omega) hmod
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1 : ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_wide (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hc; omega⟩

section Ge0
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`ge0N_of_sat` — the `forced_ge0` bit IS the comparison, at ARBITRARY columns.** The three gate
memberships are literally what `mem_ge0_ib` / `mem_ge0_bit` / `mem_ge0_head` produce; `hD` is the
closed form of the compared head (via `evalHStep_*`). No numeral appears anywhere. -/
theorem ge0N_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (ib bit0 : Nat) (dh : Head) (D : ℤ)
    (hibG : cg (gBin ib) ∈ d.constraints)
    (hbits : ∀ k, k < SMALL_RBITS → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hhead : cgH ((List.range SMALL_RBITS).foldl
        (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) ((bitsFrom bit0 SMALL_RBITS)[k]!))
        (forcedGe0Term ib dh)) ∈ d.constraints)
    (hD : evalHStep dh (envAt t i).loc = D)
    (hDlo : -1000000 ≤ D) (hDhi : D ≤ 1000000) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
    ∧ ((envAt t i).loc ib = 1 → 0 ≤ D) ∧ ((envAt t i).loc ib = 0 → D ≤ -1) := by
  set e := envAt t i with he
  have hibB : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (sgate hsat i hi hibG) (canon_loc hc i _)
  have b0 : e.loc bit0 = 0 ∨ e.loc bit0 = 1 := by
    have := bin_of_gate (sgate hsat i hi (hbits 0 (by decide))) (canon_loc hc i (bit0 + 0))
    simpa using this
  have b1 : e.loc (bit0 + 1) = 0 ∨ e.loc (bit0 + 1) = 1 :=
    bin_of_gate (sgate hsat i hi (hbits 1 (by decide))) (canon_loc hc i _)
  have b2 : e.loc (bit0 + 2) = 0 ∨ e.loc (bit0 + 2) = 1 :=
    bin_of_gate (sgate hsat i hi (hbits 2 (by decide))) (canon_loc hc i _)
  have b3 : e.loc (bit0 + 3) = 0 ∨ e.loc (bit0 + 3) = 1 :=
    bin_of_gate (sgate hsat i hi (hbits 3 (by decide))) (canon_loc hc i _)
  have b4 : e.loc (bit0 + 4) = 0 ∨ e.loc (bit0 + 4) = 1 :=
    bin_of_gate (sgate hsat i hi (hbits 4 (by decide))) (canon_loc hc i _)
  have hg := sgateH hsat i hi hhead
  rw [← he] at hg
  rw [headToExpr_evalStep, evalHStep_ge0Bits, hD] at hg
  have hmod : (2 * e.loc ib * D + e.loc ib - D - 1)
      ≡ (e.loc bit0 + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2) + 8 * e.loc (bit0 + 3)
          + 16 * e.loc (bit0 + 4)) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have core := forcedGe0_coreW (ib := e.loc ib) (D := D)
    (S := e.loc bit0 + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2) + 8 * e.loc (bit0 + 3)
          + 16 * e.loc (bit0 + 4)) hibB
    (by rcases b0 with h|h <;> rcases b1 with h1|h1 <;> rcases b2 with h2|h2 <;>
        rcases b3 with h3|h3 <;> rcases b4 with h4|h4 <;> rw [h, h1, h2, h3, h4] <;> norm_num)
    (by rcases b0 with h|h <;> rcases b1 with h1|h1 <;> rcases b2 with h2|h2 <;>
        rcases b3 with h3|h3 <;> rcases b4 with h4|h4 <;> rw [h, h1, h2, h3, h4] <;> norm_num)
    hmod hDlo hDhi
  exact ⟨hibB, core.1, core.2⟩

/-- **`oneHot3N_of_sat` — the size-3 `what`-alphabet one-hot at an ARBITRARY base.** `decide_axis`'s
`ipw`/`inw` one-hots are CONSTANT width (the particle alphabet), so this is not `oneHotStepN_of_sat`
(whose selectors are `(List.range n).map sel`); the content is the same and the base is symbolic. -/
theorem oneHot3N_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c0 c1 c2 idxCol : Nat)
    (hb0 : cg (gBin c0) ∈ d.constraints) (hb1 : cg (gBin c1) ∈ d.constraints)
    (hb2 : cg (gBin c2) ∈ d.constraints)
    (hsumG : cgH ([c0, c1, c2].foldl (fun h co => h.addLin 1 co) (Head.c (-1))) ∈ d.constraints)
    (hidxG : cgH ((([c0, c1, c2].length |> List.range).foldl
                    (fun h (j : Nat) => h.addLin (j : ℤ) ([c0, c1, c2][j]!)) Head.zero).append
                  ((Head.lin 1 idxCol).scale (-1))) ∈ d.constraints) :
    ((envAt t i).loc c0 = 0 ∨ (envAt t i).loc c0 = 1)
    ∧ ((envAt t i).loc c1 = 0 ∨ (envAt t i).loc c1 = 1)
    ∧ ((envAt t i).loc c2 = 0 ∨ (envAt t i).loc c2 = 1)
    ∧ (envAt t i).loc c0 + (envAt t i).loc c1 + (envAt t i).loc c2 = 1
    ∧ (envAt t i).loc c1 + 2 * (envAt t i).loc c2 = (envAt t i).loc idxCol := by
  set e := envAt t i with he
  have B0 : e.loc c0 = 0 ∨ e.loc c0 = 1 :=
    bin_of_gate (sgate hsat i hi hb0) (canon_loc hc i _)
  have B1 : e.loc c1 = 0 ∨ e.loc c1 = 1 :=
    bin_of_gate (sgate hsat i hi hb1) (canon_loc hc i _)
  have B2 : e.loc c2 = 0 ∨ e.loc c2 = 1 :=
    bin_of_gate (sgate hsat i hi hb2) (canon_loc hc i _)
  have hsum : e.loc c0 + e.loc c1 + e.loc c2 = 1 := by
    have hg := sgateH hsat i hi hsumG
    rw [headToExpr_evalStep, evalHStep_foldl_addLin, evalHStep_c] at hg
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hg
    have hmod := (gate_modEq_iff (a := e.loc c0 + e.loc c1 + e.loc c2) (b := 1) (by ring)).mp hg
    rcases B0 with h|h <;> rcases B1 with h'|h' <;> rcases B2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h, h', h'']; norm_num) (by norm_num) hmod
  have hidx : e.loc c1 + 2 * e.loc c2 = e.loc idxCol := by
    have hg := sgateH hsat i hi hidxG
    rw [headToExpr_evalStep, evalHStep_append, evalHStep_foldl_idxBang, evalHStep_zero,
      evalHStep_scale, evalHStep_lin] at hg
    have hr : List.range [c0, c1, c2].length = [0, 1, 2] := rfl
    rw [hr] at hg
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hg
    norm_num at hg
    have hmod := (gate_modEq_iff (a := e.loc c1 + 2 * e.loc c2) (b := e.loc idxCol) (by ring)).mp hg
    have hcL : Canon (e.loc c1 + 2 * e.loc c2) := by
      rcases B1 with h|h <;> rcases B2 with h'|h' <;> rw [h, h'] <;>
        exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨B0, B1, B2, hsum, hidx⟩

end Ge0

/-! ## §3.5 — small `varsVal` computations for the emitted product terms. -/

theorem varsVal_single (a : Nat → ℤ) (x : Nat) : varsVal a [x] = a x := by simp [varsVal]

theorem varsVal_pair (a : Nat → ℤ) (x y : Nat) : varsVal a [x, y] = a x * a y := by
  rw [varsVal_cons, varsVal_single]

theorem varsVal_triple (a : Nat → ℤ) (x y z : Nat) :
    varsVal a [x, y, z] = a x * a y * a z := by
  rw [varsVal_cons, varsVal_pair]; ring

theorem canon_of_bounds {x : ℤ} (h0 : 0 ≤ x) (h1 : x ≤ 4000000) : Canon x :=
  ⟨h0, by omega⟩

/-! ## §4 — THE `decide_axis` CHAIN over `A_*_BASE n`, `∀ n`.

Everything below is DESCRIPTOR-generic and BASE-generic: the only descriptor contact is the
hypothesis `hmem` (`decideAxisConstraints b pw nw pd nd ⊆ d.constraints`), discharged at
`automataflStepDescN n` by `mem_be_decideX` / `mem_be_decideY` in §6. The arithmetic content is
IDENTICAL to the `n = 2` chain in `AutomataflStepRefine` §4.8; the column addressing and the
membership are what changed. The distance envelope is carried as the explicit bound `N`
(`1 ≤ dist ≤ N ≤ 10⁶`), which a ray at board size `n` supplies with `N := n`. -/

section Axis
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- The `ipw` one-hot over the POSITIVE ray's `what`-code, at columns `b+4 .. b+6`. -/
theorem da_ipw_sel (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat)
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints) :
    ((envAt t i).loc (b + 4) = 0 ∨ (envAt t i).loc (b + 4) = 1)
    ∧ ((envAt t i).loc (b + 5) = 0 ∨ (envAt t i).loc (b + 5) = 1)
    ∧ ((envAt t i).loc (b + 6) = 0 ∨ (envAt t i).loc (b + 6) = 1)
    ∧ (envAt t i).loc (b + 4) + (envAt t i).loc (b + 5) + (envAt t i).loc (b + 6) = 1
    ∧ (envAt t i).loc (b + 5) + 2 * (envAt t i).loc (b + 6) = (envAt t i).loc pw :=
  oneHot3N_of_sat hsat hc i hi (b + 4) (b + 5) (b + 6) pw
    (hmem _ (mem_da_ipw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_ipw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_ipw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_ipw b pw nw pd nd oneHot_sigma))
    (hmem _ (mem_da_ipw b pw nw pd nd oneHot_index))

/-- The `inw` one-hot over the NEGATIVE ray's `what`-code, at columns `b+7 .. b+9`. -/
theorem da_inw_sel (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat)
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints) :
    ((envAt t i).loc (b + 7) = 0 ∨ (envAt t i).loc (b + 7) = 1)
    ∧ ((envAt t i).loc (b + 8) = 0 ∨ (envAt t i).loc (b + 8) = 1)
    ∧ ((envAt t i).loc (b + 9) = 0 ∨ (envAt t i).loc (b + 9) = 1)
    ∧ (envAt t i).loc (b + 7) + (envAt t i).loc (b + 8) + (envAt t i).loc (b + 9) = 1
    ∧ (envAt t i).loc (b + 8) + 2 * (envAt t i).loc (b + 9) = (envAt t i).loc nw :=
  oneHot3N_of_sat hsat hc i hi (b + 7) (b + 8) (b + 9) nw
    (hmem _ (mem_da_inw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_inw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_inw b pw nw pd nd (oneHot_bool (by simp))))
    (hmem _ (mem_da_inw b pw nw pd nd oneHot_sigma))
    (hmem _ (mem_da_inw b pw nw pd nd oneHot_index))

/-- `gpd = [pd ≥ 2]` at column `b+10`, at ARBITRARY base and ARBITRARY distance envelope. -/
theorem da_gpd_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 10) = 0 ∨ (envAt t i).loc (b + 10) = 1)
    ∧ ((envAt t i).loc (b + 10) = 1 → 2 ≤ (envAt t i).loc pd)
    ∧ ((envAt t i).loc (b + 10) = 0 → (envAt t i).loc pd ≤ 1) := by
  have h := ge0N_of_sat hsat hc i hi (b + 10) (b + 11) ((Head.lin 1 pd).addConst (-2))
    ((envAt t i).loc pd - 2)
    (hmem _ (mem_da_gpd b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_gpd b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 11) SMALL_RBITS k hk))))
    (hmem _ (mem_da_gpd b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addConst, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- `gnd = [nd ≥ 2]` at column `b+16`. -/
theorem da_gnd_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 16) = 0 ∨ (envAt t i).loc (b + 16) = 1)
    ∧ ((envAt t i).loc (b + 16) = 1 → 2 ≤ (envAt t i).loc nd)
    ∧ ((envAt t i).loc (b + 16) = 0 → (envAt t i).loc nd ≤ 1) := by
  have h := ge0N_of_sat hsat hc i hi (b + 16) (b + 17) ((Head.lin 1 nd).addConst (-2))
    ((envAt t i).loc nd - 2)
    (hmem _ (mem_da_gnd b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_gnd b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 17) SMALL_RBITS k hk))))
    (hmem _ (mem_da_gnd b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addConst, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- `lt = [pd < nd]` at column `b+22`. -/
theorem da_lt_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 22) = 0 ∨ (envAt t i).loc (b + 22) = 1)
    ∧ ((envAt t i).loc (b + 22) = 1 → (envAt t i).loc pd < (envAt t i).loc nd)
    ∧ ((envAt t i).loc (b + 22) = 0 → (envAt t i).loc nd ≤ (envAt t i).loc pd) := by
  have h := ge0N_of_sat hsat hc i hi (b + 22) (b + 23)
    (((Head.lin 1 nd).addLin (-1) pd).addConst (-1))
    ((envAt t i).loc nd - (envAt t i).loc pd - 1)
    (hmem _ (mem_da_lt b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_lt b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 23) SMALL_RBITS k hk))))
    (hmem _ (mem_da_lt b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addConst, evalHStep_addLin, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- `gt = [nd < pd]` at column `b+28`. -/
theorem da_gt_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 28) = 0 ∨ (envAt t i).loc (b + 28) = 1)
    ∧ ((envAt t i).loc (b + 28) = 1 → (envAt t i).loc nd < (envAt t i).loc pd)
    ∧ ((envAt t i).loc (b + 28) = 0 → (envAt t i).loc pd ≤ (envAt t i).loc nd) := by
  have h := ge0N_of_sat hsat hc i hi (b + 28) (b + 29)
    (((Head.lin 1 pd).addLin (-1) nd).addConst (-1))
    ((envAt t i).loc pd - (envAt t i).loc nd - 1)
    (hmem _ (mem_da_gt b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_gt b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 29) SMALL_RBITS k hk))))
    (hmem _ (mem_da_gt b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addConst, evalHStep_addLin, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- `le = [pd ≤ nd]` at column `b+34` (the `min` selector). -/
theorem da_le_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 34) = 0 ∨ (envAt t i).loc (b + 34) = 1)
    ∧ ((envAt t i).loc (b + 34) = 1 → (envAt t i).loc pd ≤ (envAt t i).loc nd)
    ∧ ((envAt t i).loc (b + 34) = 0 → (envAt t i).loc nd < (envAt t i).loc pd) := by
  have h := ge0N_of_sat hsat hc i hi (b + 34) (b + 35) ((Head.lin 1 nd).addLin (-1) pd)
    ((envAt t i).loc nd - (envAt t i).loc pd)
    (hmem _ (mem_da_le b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_le b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 35) SMALL_RBITS k hk))))
    (hmem _ (mem_da_le b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addLin, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- The `min` gadget at column `b+40`: `min = le·pd + nd − le·nd`. -/
theorem da_min_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    (envAt t i).loc (b + 40)
      = (envAt t i).loc (b + 34) * (envAt t i).loc pd + (envAt t i).loc nd
        - (envAt t i).loc (b + 34) * (envAt t i).loc nd := by
  obtain ⟨leB, _, _⟩ := da_le_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hg := sgateH hsat i hi (hmem _ (mem_da_minHead b pw nw pd nd))
  rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_addLin, evalHStep_addProd,
    evalHStep_lin, varsVal_pair, varsVal_pair] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_
    ((gate_modEq_iff (a := (envAt t i).loc (b + 40))
      (b := (envAt t i).loc (b + 34) * (envAt t i).loc pd + (envAt t i).loc nd
             - (envAt t i).loc (b + 34) * (envAt t i).loc nd) (by ring)).mp hg)
  rcases leB with h | h <;> rw [h] <;> exact canon_of_bounds (by nlinarith) (by nlinarith)

/-- `gm = [min ≥ 2]` at column `b+41`. -/
theorem da_gm_sound (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000) :
    ((envAt t i).loc (b + 41) = 0 ∨ (envAt t i).loc (b + 41) = 1)
    ∧ ((envAt t i).loc (b + 41) = 1 → 2 ≤ (envAt t i).loc (b + 40))
    ∧ ((envAt t i).loc (b + 41) = 0 → (envAt t i).loc (b + 40) ≤ 1) := by
  obtain ⟨leB, _, _⟩ := da_le_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hmin := da_min_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hlo : 1 ≤ (envAt t i).loc (b + 40) := by
    rw [hmin]; rcases leB with h | h <;> rw [h] <;> nlinarith
  have hhi : (envAt t i).loc (b + 40) ≤ N := by
    rw [hmin]; rcases leB with h | h <;> rw [h] <;> nlinarith
  have h := ge0N_of_sat hsat hc i hi (b + 41) (b + 42) ((Head.lin 1 (b + 40)).addConst (-2))
    ((envAt t i).loc (b + 40) - 2)
    (hmem _ (mem_da_gm b pw nw pd nd (mem_ge0_ib _ _ _)))
    (fun k hk => hmem _ (mem_da_gm b pw nw pd nd
      (mem_ge0_bit _ _ _ (mem_bitsFrom (b + 42) SMALL_RBITS k hk))))
    (hmem _ (mem_da_gm b pw nw pd nd (mem_ge0_head _ _ _)))
    (by rw [evalHStep_addConst, evalHStep_lin]; ring) (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- **One `assert_case` field equality, base-generic.** When the case's two one-hot selectors are
both `1`, the gate `∏gate·(field − formula)` forces the witnessed field column to the case formula.
This ONE lemma replaces the 36 per-numeral `rfl` gate expansions the `n = 2` chain carried. -/
theorem daCaseField_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat)
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (g1 g2 fieldCol : Nat) (fm : Head)
    (hcaseMem : assertCase [g1, g2] fieldCol fm
      ∈ decideCasesConstraints [b + 4, b + 5, b + 6] [b + 7, b + 8, b + 9]
          [b, b + 1, b + 2, b + 3] pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 34)
          (b + 41))
    (hconst : fm.const = 0)
    (hg1 : (envAt t i).loc g1 = 1) (hg2 : (envAt t i).loc g2 = 1)
    (hcanon : Canon (evalHStep fm (envAt t i).loc)) :
    (envAt t i).loc fieldCol = evalHStep fm (envAt t i).loc := by
  have hm := hmem _ (mem_da_cases b pw nw pd nd hcaseMem)
  rw [assertCase_eq _ _ _ hconst] at hm
  have hg := sgateH hsat i hi hm
  rw [headToExpr_evalStep, evalHStep_caseGateHead _ _ _ _ hconst, varsVal_pair, hg1, hg2] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) hcanon
    ((gate_modEq_iff (a := (envAt t i).loc fieldCol) (b := evalHStep fm (envAt t i).loc)
      (by ring)).mp hg)

end Axis

/-! ## §5 — THE NINE DECODE CASES AT ARBITRARY DISTANCE.

`AutomataflStepRefine.decode_*` is PURE arithmetic, so it is `n`-independent in its DENOTATION — but
every one of them takes `hpd : pd = 1 ∨ pd = 2`, which is the `n = 2` distance alphabet. At board size
`n` a ray's distance is anywhere in `[1, n]`. These twins take exactly `1 ≤ pd` / `1 ≤ nd`, which is
what `AutomataflStepCapstone.rayN_of_sat` delivers, and are otherwise the same statements. -/

theorem decodeN_vacVac {pd nd v pos att rep : ℤ}
    (hv : v = 0) (hpos : pos = 0) (hatt : att = 0) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat } { what := .vacuum, dist := nd.toNat } := by
  subst hv hpos hatt hrep; simp [decodeDecision, evaluateAxis]

theorem decodeN_attRep {pd nd gpd v pos att rep : ℤ}
    (hpd : 1 ≤ pd)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = 3 * gpd) (hpos : pos = gpd) (hatt : att = gpd * pd) (hrep : rep = gpd * nd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat }
                     { what := .repulsor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hpd1 : pd = 1 := le_antisymm (hg2 rfl) hpd
    subst hpd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < pd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_repAtt {pd nd gnd v pos att rep : ℤ}
    (hnd : 1 ≤ nd)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = 3 * gnd) (hpos : pos = 0) (hatt : att = gnd * nd) (hrep : rep = gnd * pd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat }
                     { what := .attractor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hnd1 : nd = 1 := le_antisymm (hg2 rfl) hnd
    subst hnd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < nd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_repVac {pd nd gnd v pos att rep : ℤ}
    (hnd : 1 ≤ nd)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = 2 * gnd) (hpos : pos = 0) (hatt : att = 0) (hrep : rep = gnd * pd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat }
                     { what := .vacuum, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hnd1 : nd = 1 := le_antisymm (hg2 rfl) hnd
    subst hnd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < nd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_vacRep {pd nd gpd v pos att rep : ℤ}
    (hpd : 1 ≤ pd)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = 2 * gpd) (hpos : pos = gpd) (hatt : att = 0) (hrep : rep = gpd * nd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat }
                     { what := .repulsor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hpd1 : pd = 1 := le_antisymm (hg2 rfl) hpd
    subst hpd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < pd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_attVac {pd nd gpd v pos att rep : ℤ}
    (hpd : 1 ≤ pd)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = gpd) (hpos : pos = gpd) (hatt : att = gpd * pd) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat }
                     { what := .vacuum, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hpd1 : pd = 1 := le_antisymm (hg2 rfl) hpd
    subst hpd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < pd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_vacAtt {pd nd gnd v pos att rep : ℤ}
    (hnd : 1 ≤ nd)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = gnd) (hpos : pos = 0) (hatt : att = gnd * nd) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat }
                     { what := .attractor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg <;> subst hv <;> subst hpos <;> subst hatt <;> subst hrep
  · have hnd1 : nd = 1 := le_antisymm (hg2 rfl) hnd
    subst hnd1; norm_num [decodeDecision, evaluateAxis]
  · have hgt : 1 < nd.toNat := by have := hg1 rfl; omega
    norm_num [decodeDecision, evaluateAxis, hgt]

theorem decodeN_repRep {pd nd le lt gt minv v pos att rep : ℤ}
    (hpd : 1 ≤ pd) (hnd : 1 ≤ nd)
    (hlt0 : lt = 0 ∨ lt = 1) (hlt1 : lt = 1 → pd < nd) (hlt2 : lt = 0 → nd ≤ pd)
    (hgt0 : gt = 0 ∨ gt = 1) (hgt1 : gt = 1 → nd < pd) (hgt2 : gt = 0 → pd ≤ nd)
    (hle0 : le = 0 ∨ le = 1) (hle1 : le = 1 → pd ≤ nd) (hle2 : le = 0 → nd < pd)
    (hminv : minv = le * pd + nd - le * nd)
    (hv : v = 2 * lt + 2 * gt) (hpos : pos = gt) (hatt : att = 0)
    (hrep : rep = lt * minv + gt * minv) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat }
                     { what := .repulsor, dist := nd.toNat } := by
  rcases hlt0 with hl | hl <;> rcases hgt0 with hgv | hgv <;> subst hl <;> subst hgv
  · -- lt = 0, gt = 0: nd ≤ pd and pd ≤ nd, so the distances agree.
    have hpe : pd = nd := le_antisymm (hgt2 rfl) (hlt2 rfl)
    have hte : pd.toNat = nd.toNat := by omega
    subst hv; subst hpos; subst hatt; subst hrep
    norm_num [decodeDecision, evaluateAxis, hte]
  · -- lt = 0, gt = 1: nd < pd, min = nd.
    have hnp : nd < pd := hgt1 rfl
    have hlev : le = 0 := by rcases hle0 with h | h; · exact h
                             · exact absurd (hle1 h) (by omega)
    have hmv : minv = nd := by rw [hminv, hlev]; ring
    subst hv; subst hpos; subst hatt; subst hrep; rw [hmv]
    have hne : ¬ (pd.toNat = nd.toNat) := by omega
    have hmin : min pd.toNat nd.toNat = nd.toNat := min_eq_right (by omega)
    have hgtn : nd.toNat < pd.toNat := by omega
    norm_num [decodeDecision, evaluateAxis, hne, hmin, hgtn]
  · -- lt = 1, gt = 0: pd < nd, min = pd.
    have hpn : pd < nd := hlt1 rfl
    have hlev : le = 1 := by rcases hle0 with h | h; · exact absurd (hle2 h) (by omega)
                             · exact h
    have hmv : minv = pd := by rw [hminv, hlev]; ring
    subst hv; subst hpos; subst hatt; subst hrep; rw [hmv]
    have hne : ¬ (pd.toNat = nd.toNat) := by omega
    have hmin : min pd.toNat nd.toNat = pd.toNat := min_eq_left (by omega)
    have hgtn : ¬ (nd.toNat < pd.toNat) := by omega
    norm_num [decodeDecision, evaluateAxis, hne, hmin, hgtn]
  · -- lt = 1, gt = 1 is impossible (pd < nd and nd < pd).
    exact absurd (hlt1 rfl) (by have := hgt1 rfl; omega)

theorem decodeN_attAtt {pd nd le lt gt gm minv v pos att rep : ℤ}
    (hpd : 1 ≤ pd) (hnd : 1 ≤ nd)
    (hlt0 : lt = 0 ∨ lt = 1) (hlt1 : lt = 1 → pd < nd) (hlt2 : lt = 0 → nd ≤ pd)
    (hgt0 : gt = 0 ∨ gt = 1) (hgt1 : gt = 1 → nd < pd) (hgt2 : gt = 0 → pd ≤ nd)
    (hle0 : le = 0 ∨ le = 1) (hle1 : le = 1 → pd ≤ nd) (hle2 : le = 0 → nd < pd)
    (hgm0 : gm = 0 ∨ gm = 1) (hgm1 : gm = 1 → 2 ≤ minv) (hgm2 : gm = 0 → minv ≤ 1)
    (hminv : minv = le * pd + nd - le * nd)
    (hv : v = lt * gm + gt * gm) (hpos : pos = lt * gm)
    (hatt : att = lt * gm * minv + gt * gm * minv) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat }
                     { what := .attractor, dist := nd.toNat } := by
  rcases hlt0 with hl | hl <;> rcases hgt0 with hgv | hgv <;> subst hl <;> subst hgv
  · have hpe : pd = nd := le_antisymm (hgt2 rfl) (hlt2 rfl)
    have hte : pd.toNat = nd.toNat := by omega
    subst hv; subst hpos; subst hatt; subst hrep
    norm_num [decodeDecision, evaluateAxis, hte]
  · -- lt = 0, gt = 1: nd < pd, min = nd.
    have hnp : nd < pd := hgt1 rfl
    have hlev : le = 0 := by rcases hle0 with h | h; · exact h
                             · exact absurd (hle1 h) (by omega)
    have hmv : minv = nd := by rw [hminv, hlev]; ring
    have hne : ¬ (pd.toNat = nd.toNat) := by omega
    have hmin : min pd.toNat nd.toNat = nd.toNat := min_eq_right (by omega)
    have hlted : ¬ (pd.toNat < nd.toNat) := by omega
    subst hv; subst hpos; subst hatt; subst hrep
    rcases hgm0 with hg | hg <;> subst hg
    · have hb : minv ≤ 1 := hgm2 rfl
      rw [hmv] at hb
      have hnot : ¬ (1 < min pd.toNat nd.toNat) := by rw [hmin]; omega
      norm_num [decodeDecision, evaluateAxis, hne, hnot]
    · have h2 : 2 ≤ minv := hgm1 rfl
      rw [hmv] at h2
      have hgtm : 1 < min pd.toNat nd.toNat := by rw [hmin]; omega
      rw [hmv]
      norm_num [decodeDecision, evaluateAxis, hne, hmin, hgtm, hlted]
      omega
  · -- lt = 1, gt = 0: pd < nd, min = pd.
    have hpn : pd < nd := hlt1 rfl
    have hlev : le = 1 := by rcases hle0 with h | h; · exact absurd (hle2 h) (by omega)
                             · exact h
    have hmv : minv = pd := by rw [hminv, hlev]; ring
    have hne : ¬ (pd.toNat = nd.toNat) := by omega
    have hmin : min pd.toNat nd.toNat = pd.toNat := min_eq_left (by omega)
    have hlted : pd.toNat < nd.toNat := by omega
    subst hv; subst hpos; subst hatt; subst hrep
    rcases hgm0 with hg | hg <;> subst hg
    · have hb : minv ≤ 1 := hgm2 rfl
      rw [hmv] at hb
      have hnot : ¬ (1 < min pd.toNat nd.toNat) := by rw [hmin]; omega
      norm_num [decodeDecision, evaluateAxis, hne, hnot]
    · have h2 : 2 ≤ minv := hgm1 rfl
      rw [hmv] at h2
      have hgtm : 1 < min pd.toNat nd.toNat := by rw [hmin]; omega
      rw [hmv]
      norm_num [decodeDecision, evaluateAxis, hne, hmin, hgtm, hlted]
      omega
  · exact absurd (hlt1 rfl) (by have := hgt1 rfl; omega)

/-! ## §6 — the nine `decide_axis` cases OFF THE GATES, `∀ n`, and the per-axis capstone. -/

section AxisCases
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`decide_axis` case (2,1) — attractor / repulsor ⇒ `.unbalancedPair` — at ARBITRARY base and distance envelope.** -/
theorem daCase_attRep (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 2) (hnwv : (envAt t i).loc nw = 1) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 6) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 8) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gpd_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) b
      (Head.lin 3 (b + 10))
      (mem_decideCases (ij := (2, 1)) (fs := [Head.lin 3 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero.addProd 1 [b + 10, nd]])
        List.mem_cons_self (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) (b + 1)
      (Head.lin 1 (b + 10))
      (mem_decideCases (ij := (2, 1)) (fs := [Head.lin 3 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero.addProd 1 [b + 10, nd]])
        List.mem_cons_self (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hpos
  rw [one_mul] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) (b + 2)
      (Head.zero.addProd 1 [b + 10, pd])
      (mem_decideCases (ij := (2, 1)) (fs := [Head.lin 3 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero.addProd 1 [b + 10, nd]])
        List.mem_cons_self (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
  simp only [zero_add, one_mul] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) (b + 3)
      (Head.zero.addProd 1 [b + 10, nd])
      (mem_decideCases (ij := (2, 1)) (fs := [Head.lin 3 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero.addProd 1 [b + 10, nd]])
        List.mem_cons_self (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
  simp only [zero_add, one_mul] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (2 : ℤ) = Particle.attractor from rfl]
  try rw [show codeToParticle (1 : ℤ) = Particle.repulsor from rfl]
  exact decodeN_attRep hpd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (1,2) — repulsor / attractor ⇒ `.unbalancedPair` — at ARBITRARY base and distance envelope.** -/
theorem daCase_repAtt (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 1) (hnwv : (envAt t i).loc nw = 2) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 5) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 9) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gnd_sound hsat hc i hi b pw nw pd nd hmem hnd1 hndn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) b
      (Head.lin 3 (b + 16))
      (mem_decideCases (ij := (1, 2)) (fs := [Head.lin 3 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ List.mem_cons_self) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) (b + 1)
      (Head.zero)
      (mem_decideCases (ij := (1, 2)) (fs := [Head.lin 3 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ List.mem_cons_self) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) (b + 2)
      (Head.zero.addProd 1 [b + 16, nd])
      (mem_decideCases (ij := (1, 2)) (fs := [Head.lin 3 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ List.mem_cons_self) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
  simp only [zero_add, one_mul] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) (b + 3)
      (Head.zero.addProd 1 [b + 16, pd])
      (mem_decideCases (ij := (1, 2)) (fs := [Head.lin 3 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ List.mem_cons_self) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
  simp only [zero_add, one_mul] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (1 : ℤ) = Particle.repulsor from rfl]
  try rw [show codeToParticle (2 : ℤ) = Particle.attractor from rfl]
  exact decodeN_repAtt hnd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (1,0) — repulsor / vacuum ⇒ `.fromRepulsor` — at ARBITRARY base and distance envelope.** -/
theorem daCase_repVac (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 1) (hnwv : (envAt t i).loc nw = 0) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 5) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 7) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gnd_sound hsat hc i hi b pw nw pd nd hmem hnd1 hndn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) b
      (Head.lin 2 (b + 16))
      (mem_decideCases (ij := (1, 0)) (fs := [Head.lin 2 (b + 16), Head.zero, Head.zero, Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) (b + 1)
      (Head.zero)
      (mem_decideCases (ij := (1, 0)) (fs := [Head.lin 2 (b + 16), Head.zero, Head.zero, Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) (b + 2)
      (Head.zero)
      (mem_decideCases (ij := (1, 0)) (fs := [Head.lin 2 (b + 16), Head.zero, Head.zero, Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) (b + 3)
      (Head.zero.addProd 1 [b + 16, pd])
      (mem_decideCases (ij := (1, 0)) (fs := [Head.lin 2 (b + 16), Head.zero, Head.zero, Head.zero.addProd 1 [b + 16, pd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
  simp only [zero_add, one_mul] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (1 : ℤ) = Particle.repulsor from rfl]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  exact decodeN_repVac hnd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (0,1) — vacuum / repulsor ⇒ `.fromRepulsor` — at ARBITRARY base and distance envelope.** -/
theorem daCase_vacRep (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 0) (hnwv : (envAt t i).loc nw = 1) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 4) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 8) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gpd_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) b
      (Head.lin 2 (b + 10))
      (mem_decideCases (ij := (0, 1)) (fs := [Head.lin 2 (b + 10), Head.lin 1 (b + 10), Head.zero, Head.zero.addProd 1 [b + 10, nd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) (b + 1)
      (Head.lin 1 (b + 10))
      (mem_decideCases (ij := (0, 1)) (fs := [Head.lin 2 (b + 10), Head.lin 1 (b + 10), Head.zero, Head.zero.addProd 1 [b + 10, nd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hpos
  rw [one_mul] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) (b + 2)
      (Head.zero)
      (mem_decideCases (ij := (0, 1)) (fs := [Head.lin 2 (b + 10), Head.lin 1 (b + 10), Head.zero, Head.zero.addProd 1 [b + 10, nd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) (b + 3)
      (Head.zero.addProd 1 [b + 10, nd])
      (mem_decideCases (ij := (0, 1)) (fs := [Head.lin 2 (b + 10), Head.lin 1 (b + 10), Head.zero, Head.zero.addProd 1 [b + 10, nd]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
  simp only [zero_add, one_mul] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  try rw [show codeToParticle (1 : ℤ) = Particle.repulsor from rfl]
  exact decodeN_vacRep hpd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (2,0) — attractor / vacuum ⇒ `.towardAttractor` — at ARBITRARY base and distance envelope.** -/
theorem daCase_attVac (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 2) (hnwv : (envAt t i).loc nw = 0) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 6) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 7) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gpd_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) b
      (Head.lin 1 (b + 10))
      (mem_decideCases (ij := (2, 0)) (fs := [Head.lin 1 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  rw [one_mul] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) (b + 1)
      (Head.lin 1 (b + 10))
      (mem_decideCases (ij := (2, 0)) (fs := [Head.lin 1 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hpos
  rw [one_mul] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) (b + 2)
      (Head.zero.addProd 1 [b + 10, pd])
      (mem_decideCases (ij := (2, 0)) (fs := [Head.lin 1 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
  simp only [zero_add, one_mul] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) (b + 3)
      (Head.zero)
      (mem_decideCases (ij := (2, 0)) (fs := [Head.lin 1 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (2 : ℤ) = Particle.attractor from rfl]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  exact decodeN_attVac hpd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (0,2) — vacuum / attractor ⇒ `.towardAttractor` — at ARBITRARY base and distance envelope.** -/
theorem daCase_vacAtt (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 0) (hnwv : (envAt t i).loc nw = 2) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 4) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 9) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨gB, gg1, gg2⟩ := da_gnd_sound hsat hc i hi b pw nw pd nd hmem hnd1 hndn hN
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) b
      (Head.lin 1 (b + 16))
      (mem_decideCases (ij := (0, 2)) (fs := [Head.lin 1 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin] at hvar
  rw [one_mul] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) (b + 1)
      (Head.zero)
      (mem_decideCases (ij := (0, 2)) (fs := [Head.lin 1 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) (b + 2)
      (Head.zero.addProd 1 [b + 16, nd])
      (mem_decideCases (ij := (0, 2)) (fs := [Head.lin 1 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gB with hq|hq <;> rw [hq] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
  simp only [zero_add, one_mul] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) (b + 3)
      (Head.zero)
      (mem_decideCases (ij := (0, 2)) (fs := [Head.lin 1 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd], Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  try rw [show codeToParticle (2 : ℤ) = Particle.attractor from rfl]
  exact decodeN_vacAtt hnd1 gB gg1 gg2 hvar hpos hatt hrep

/-- **`decide_axis` case (0,0) — vacuum / vacuum ⇒ `.none` — at ARBITRARY base and distance envelope.** -/
theorem daCase_vacVac (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 0) (hnwv : (envAt t i).loc nw = 0) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 4) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 7) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) b
      (Head.zero)
      (mem_decideCases (ij := (0, 0)) (fs := [Head.zero, Head.zero, Head.zero, Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) (b + 1)
      (Head.zero)
      (mem_decideCases (ij := (0, 0)) (fs := [Head.zero, Head.zero, Head.zero, Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) (k := 1) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) (b + 2)
      (Head.zero)
      (mem_decideCases (ij := (0, 0)) (fs := [Head.zero, Head.zero, Head.zero, Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) (b + 3)
      (Head.zero)
      (mem_decideCases (ij := (0, 0)) (fs := [Head.zero, Head.zero, Head.zero, Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  try rw [show codeToParticle (0 : ℤ) = Particle.vacuum from rfl]
  exact decodeN_vacVac hvar hpos hatt hrep

/-- **`decide_axis` case (1,1) — repulsor / repulsor ⇒ `.fromRepulsor`.** -/
theorem daCase_repRep (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 1) (hnwv : (envAt t i).loc nw = 1) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 5) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 8) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨ltB, lt1, lt2⟩ := da_lt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  obtain ⟨gtB, gt1, gt2⟩ := da_gt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  obtain ⟨leB, le1, le2⟩ := da_le_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hmineq := da_min_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hmlo : 0 ≤ (envAt t i).loc (b + 40) := by
    rw [hmineq]; rcases leB with h|h <;> rw [h] <;> nlinarith
  have hmhi : (envAt t i).loc (b + 40) ≤ N := by
    rw [hmineq]; rcases leB with h|h <;> rw [h] <;> nlinarith
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) b
      ((Head.lin 2 (b + 22)).addLin 2 (b + 28))
      (mem_decideCases (ij := (1, 1))
        (fs := [(Head.lin 2 (b + 22)).addLin 2 (b + 28), Head.lin 1 (b + 28), Head.zero,
                (Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (k := 0) (by decide))
      rfl hip hin
      (by rw [evalHStep_addLin, evalHStep_lin]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h, h'] <;>
            exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_addLin, evalHStep_lin] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) (b + 1)
      (Head.lin 1 (b + 28))
      (mem_decideCases (ij := (1, 1))
        (fs := [(Head.lin 2 (b + 22)).addLin 2 (b + 28), Head.lin 1 (b + 28), Head.zero,
                (Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (k := 1) (by decide))
      rfl hip hin
      (by rw [evalHStep_lin]
          rcases gtB with h|h <;> rw [h] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_lin, one_mul] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) (b + 2)
      Head.zero
      (mem_decideCases (ij := (1, 1))
        (fs := [(Head.lin 2 (b + 22)).addLin 2 (b + 28), Head.lin 1 (b + 28), Head.zero,
                (Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (k := 2) (by decide))
      rfl hip hin (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) (b + 3)
      ((Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40])
      (mem_decideCases (ij := (1, 1))
        (fs := [(Head.lin 2 (b + 22)).addLin 2 (b + 28), Head.lin 1 (b + 28), Head.zero,
                (Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40]])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (k := 3) (by decide))
      rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h, h'] <;>
            exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair] at hrep
  simp only [zero_add, one_mul] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (1 : ℤ) = Particle.repulsor from rfl]
  exact decodeN_repRep hpd1 hnd1 ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 hmineq hvar hpos hatt hrep

/-- **`decide_axis` case (2,2) — attractor / attractor ⇒ `.towardAttractor`.** -/
theorem daCase_attAtt (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwv : (envAt t i).loc pw = 2) (hnwv : (envAt t i).loc nw = 2) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  rw [hpwv] at iidx; rw [hnwv] at nidx
  have hip : (envAt t i).loc (b + 6) = 1 := by
    rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
  have hin : (envAt t i).loc (b + 9) = 1 := by
    rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
  obtain ⟨ltB, lt1, lt2⟩ := da_lt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  obtain ⟨gtB, gt1, gt2⟩ := da_gt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  obtain ⟨leB, le1, le2⟩ := da_le_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  obtain ⟨gmB, gm1, gm2⟩ := da_gm_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hmineq := da_min_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN
  have hmlo : 0 ≤ (envAt t i).loc (b + 40) := by
    rw [hmineq]; rcases leB with h|h <;> rw [h] <;> nlinarith
  have hmhi : (envAt t i).loc (b + 40) ≤ N := by
    rw [hmineq]; rcases leB with h|h <;> rw [h] <;> nlinarith
  have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) b
      ((Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41])
      (mem_decideCases (ij := (2, 2))
        (fs := [(Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41],
                Head.zero.addProd 1 [b + 22, b + 41],
                (Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40],
                Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
        (k := 0) (by decide))
      rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with h''|h'' <;>
            rw [h, h', h''] <;> exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair] at hvar
  simp only [zero_add, one_mul] at hvar
  have hpos := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) (b + 1)
      (Head.zero.addProd 1 [b + 22, b + 41])
      (mem_decideCases (ij := (2, 2))
        (fs := [(Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41],
                Head.zero.addProd 1 [b + 22, b + 41],
                (Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40],
                Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
        (k := 1) (by decide))
      rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]
          rcases ltB with h|h <;> rcases gmB with h''|h'' <;> rw [h, h''] <;>
            exact canon_of_bounds (by norm_num) (by norm_num))
  rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hpos
  simp only [zero_add, one_mul] at hpos
  have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) (b + 2)
      ((Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40])
      (mem_decideCases (ij := (2, 2))
        (fs := [(Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41],
                Head.zero.addProd 1 [b + 22, b + 41],
                (Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40],
                Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
        (k := 2) (by decide))
      rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_triple, varsVal_triple]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with h''|h'' <;>
            rw [h, h', h''] <;> exact canon_of_bounds (by nlinarith) (by nlinarith))
  rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_triple, varsVal_triple] at hatt
  simp only [zero_add, one_mul] at hatt
  have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) (b + 3)
      Head.zero
      (mem_decideCases (ij := (2, 2))
        (fs := [(Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41],
                Head.zero.addProd 1 [b + 22, b + 41],
                (Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40],
                Head.zero])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
        (k := 3) (by decide))
      rfl hip hin (by rw [evalHStep_zero]; exact canon_zero)
  rw [evalHStep_zero] at hrep
  rw [hpwv, hnwv]
  try rw [show codeToParticle (2 : ℤ) = Particle.attractor from rfl]
  exact decodeN_attAtt hpd1 hnd1 ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 gmB gm1 gm2 hmineq
    hvar hpos hatt hrep

/-- **THE PER-AXIS CAPSTONE, `∀ n`: `decodeDecision = evaluateAxis` at an ARBITRARY base.** Splits on
the two ray `what`-codes over all nine `evaluate_axis` cases; each closes against the emitted gates at
`b`, with the distances constrained only by the explicit envelope `1 ≤ dist ≤ N ≤ 10⁶`. -/
theorem decideAxis_soundN (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 1000000)
    (hpwm : (envAt t i).loc pw = 0 ∨ (envAt t i).loc pw = 1 ∨ (envAt t i).loc pw = 2)
    (hnwm : (envAt t i).loc nw = 0 ∨ (envAt t i).loc nw = 1 ∨ (envAt t i).loc nw = 2) :
    decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1)) ((envAt t i).loc (b + 2))
        ((envAt t i).loc (b + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc pw), dist := ((envAt t i).loc pd).toNat }
          { what := codeToParticle ((envAt t i).loc nw), dist := ((envAt t i).loc nd).toNat } := by
  rcases hpwm with hp|hp|hp <;> rcases hnwm with hn|hn|hn
  · exact daCase_vacVac hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_vacRep hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_vacAtt hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_repVac hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_repRep hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_repAtt hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_attVac hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_attRep hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn
  · exact daCase_attAtt hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN hp hn

end AxisCases

/-! ## §7 — `decideAxis_{x,y}_soundN` off `Satisfied2 (automataflStepDescN n)`, ∀ n.

The two axes instantiate the base-generic capstone at `NGen.A_DECIDE_X_BASE n` / `A_DECIDE_Y_BASE n`
over the `n`-parametric ray columns. The distance envelope is supplied by
`AutomataflStepCapstone.rayN_of_sat` (`dist = K`, `1 ≤ K ≤ n`) — NOT assumed — and the `what`-code
alphabet by the ray's own emitted `member` gate. These SUBSUME `AutomataflStepRefine`'s
`decideAxis_x_sound` / `decideAxis_y_sound`, which are the `n = 2` instances. -/

section StepAxes
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepCapstone (rayN_of_sat)

/-- The `xdec` axis at ARBITRARY `n`: the decoded `(variant, pos, att, rep)` at
`NGen.A_DECIDE_X_BASE n` IS `evaluateAxis` of the XP/XN rays. -/
theorem decideAxis_x_soundN (n : Nat) (hn : (n : ℤ) < 2013265921) (hnwin : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE n))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 0)),
            dist := ((envAt t i).loc (NGen.rDist n 0)).toNat }
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 1)),
            dist := ((envAt t i).loc (NGen.rDist n 1)).toNat } := by
  obtain ⟨K0, hK0a, hK0b, hd0, _⟩ :=
    rayN_of_sat (t := t) n 0 1 0 hn (fun x hx => mem_fe_ray0 hx) hsat hc i hi
  obtain ⟨K1, hK1a, hK1b, hd1, _⟩ :=
    rayN_of_sat (t := t) n 1 (-1) 0 hn (fun x hx => mem_fe_ray1 hx) hsat hc i hi
  refine decideAxis_soundN hsat hc i hi (NGen.A_DECIDE_X_BASE n) (NGen.rWhat n 0)
    (NGen.rWhat n 1) (NGen.rDist n 0) (NGen.rDist n 1) (N := (n : ℤ))
    (fun x hx => mem_be_decideX hx)
    (by rw [hd0]; exact_mod_cast hK0a) (by rw [hd0]; exact_mod_cast hK0b)
    (by rw [hd1]; exact_mod_cast hK1a) (by rw [hd1]; exact_mod_cast hK1b) hnwin ?_ ?_
  · exact mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 0) [0, 1, 2])
      (mem_fe_ray0 ray_whatMem_mem)) (canon_loc hc i _)
  · exact mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 1) [0, 1, 2])
      (mem_fe_ray1 ray_whatMem_mem)) (canon_loc hc i _)

/-- The `ydec` axis at ARBITRARY `n`, over the YP/YN rays at `NGen.A_DECIDE_Y_BASE n`. -/
theorem decideAxis_y_soundN (n : Nat) (hn : (n : ℤ) < 2013265921) (hnwin : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 2)),
            dist := ((envAt t i).loc (NGen.rDist n 2)).toNat }
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 3)),
            dist := ((envAt t i).loc (NGen.rDist n 3)).toNat } := by
  obtain ⟨K2, hK2a, hK2b, hd2, _⟩ :=
    rayN_of_sat (t := t) n 2 0 1 hn (fun x hx => mem_fe_ray2 hx) hsat hc i hi
  obtain ⟨K3, hK3a, hK3b, hd3, _⟩ :=
    rayN_of_sat (t := t) n 3 0 (-1) hn (fun x hx => mem_fe_ray3 hx) hsat hc i hi
  refine decideAxis_soundN hsat hc i hi (NGen.A_DECIDE_Y_BASE n) (NGen.rWhat n 2)
    (NGen.rWhat n 3) (NGen.rDist n 2) (NGen.rDist n 3) (N := (n : ℤ))
    (fun x hx => mem_be_decideY hx)
    (by rw [hd2]; exact_mod_cast hK2a) (by rw [hd2]; exact_mod_cast hK2b)
    (by rw [hd3]; exact_mod_cast hK3a) (by rw [hd3]; exact_mod_cast hK3b) hnwin ?_ ?_
  · exact mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 2) [0, 1, 2])
      (mem_fe_ray2 ray_whatMem_mem)) (canon_loc hc i _)
  · exact mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 3) [0, 1, 2])
      (mem_fe_ray3 ray_whatMem_mem)) (canon_loc hc i _)

/-- The deployed board size `n = 11` discharges the no-wrap window: the ∀-n axis capstone is not
vacuous at the size the game actually runs. -/
theorem decideAxis_x_sound_n11 (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE 11))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE 11 + 1))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE 11 + 2))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE 11 + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat 11 0)),
            dist := ((envAt t i).loc (NGen.rDist 11 0)).toNat }
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat 11 1)),
            dist := ((envAt t i).loc (NGen.rDist 11 1)).toNat } :=
  decideAxis_x_soundN 11 (by norm_num) (by norm_num) hsat hc i hi

/-- Same at `n = 3` (the first size where the `n = 2` layout numerals are WRONG). -/
theorem decideAxis_y_sound_n3 (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE 3))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE 3 + 1))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE 3 + 2))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE 3 + 3))
      = evaluateAxis
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat 3 2)),
            dist := ((envAt t i).loc (NGen.rDist 3 2)).toNat }
          { what := codeToParticle ((envAt t i).loc (NGen.rWhat 3 3)),
            dist := ((envAt t i).loc (NGen.rDist 3 3)).toNat } :=
  decideAxis_y_soundN 3 (by norm_num) (by norm_num) hsat hc i hi

end StepAxes

/-! ## §8 — layout pins: the parametric bases really are the frozen numerals at `n = 2`, and they
tile without overlap at `n = 3` / the deployed `n = 11` (so the `∀ n` membership above is not a
statement about a degenerate layout). -/

#guard NGen.A_DECIDE_X_BASE 2 == 58
#guard NGen.A_DECIDE_Y_BASE 2 == 105
#guard NGen.A_CHOOSE_BASE 2 == 152
#guard NGen.A_STEP_BASE 2 == 209
#guard NGen.A_DECIDE_X_BASE 3 == 86
#guard NGen.A_STEP_BASE 3 == 237
#guard NGen.A_DECIDE_X_BASE 11 == 430
#guard NGen.A_DECIDE_Y_BASE 11 == 477
#guard NGen.A_CHOOSE_BASE 11 == 524
#guard NGen.A_STEP_BASE 11 == 581

/-! ## §9 — Axiom pins. -/

#assert_axioms varsVal_append
#assert_axioms evalHStep_forcedGe0Term
#assert_axioms evalHStep_caseGateHead
#assert_axioms mem_be_decideX
#assert_axioms mem_be_decideY
#assert_axioms mem_be_choose
#assert_axioms mem_be_step
#assert_axioms mem_step_update
#assert_axioms mem_decideCases
#assert_axioms ge0N_of_sat
#assert_axioms oneHot3N_of_sat
#assert_axioms da_gpd_sound
#assert_axioms da_gnd_sound
#assert_axioms da_lt_sound
#assert_axioms da_gt_sound
#assert_axioms da_le_sound
#assert_axioms da_min_sound
#assert_axioms da_gm_sound
#assert_axioms daCaseField_of_sat
#assert_axioms decodeN_repRep
#assert_axioms decodeN_attAtt
#assert_axioms decideAxis_soundN
#assert_axioms decideAxis_x_soundN
#assert_axioms decideAxis_y_soundN
#assert_axioms decideAxis_x_sound_n11

end Dregg2.Circuit.Emit.AutomataflStepBackend
