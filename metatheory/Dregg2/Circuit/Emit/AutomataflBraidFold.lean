/-
# AutomataflBraidFold — M7 of the multi-round conflict braid: THE `runTurn` FOLD

⚑ SUBSTRATE. This file authors **no AIR, no gadget, no constraint**. It is the SPEC-side fold
(`AutomataflRules.roundStep` / `runTurn`) that COMPOSES the already-proven Lean-authored-AIR
refinements: M2 (`legC_sat_imp_roundAgainN11`, a satisfying Leg C trace = one `.again` round) and
M6 (`turn_sat_imp_roundStepMarks_pi`, the clean round consuming the accumulated `RoundState`). The
Leg C / Leg R / Leg A descriptors live under `Dregg2.Circuit.Emit.Automatafl*` and are unchanged;
nothing here is Rust.

## What M7 proves

`braid_sat_imp_runTurn` (n = 11, P = 2): given a TRACE of rounds —

* `k` conflict rounds, each a satisfying Leg C trace whose decoded `RoundState` windows chain
  (`roundStateDecodeOut (tᵢ) RoundStateAgrees roundStateDecodeIn (tᵢ₊₁)`, the fold seam), and
* a clean round whose satisfying resolve-marks + step traces have `marksIn` agreeing with the last
  conflict round's `marksOut` (the C→R handoff) —

the decoded final board IS `(runTurn ⟨.column⟩ g (openRound b₀ seats) subsTrace)`'s board, cell for
cell at n = 11.

## The two technical seams

1. **The RoundState / `Perm` thread.** The fold seam is `RoundStateAgrees` (§ M1 proved literal `=`
   FALSE — the marks list's insertion order is not recoverable from an n² indicator). `roundStep`
   is `RoundStateAgrees`-CONGRUENT: `MoveLegal` reads `marks` only through `∉` (`Perm`-invariant),
   `RoundWF` only through `Nodup`, and every board read is through `cellAt` / `size` / `automaton`,
   so cell-agreeing boards + `Perm`-marks produce the same clash set (as LISTS), the same locked /
   waiting fields (EQUAL), `Perm`-marks on the re-entry state, and cell-agreeing resolved boards.
   `roundStep_agree` is that congruence; the fold threads it.

2. **Termination.** `AutomataflTermination.againDepth_le` bounds the conflict rounds by n² (121 at
   n = 11); `runTurn` is TOTAL on any trace and returns `none` only when the trace runs out. This
   file carries the trace as an explicit hypothesis (the prover supplies the k conflict subs plus
   the clean subs); the n² bound tells the host a trace of length n² + 1 always suffices, so no fuel
   hypothesis is smuggled into the theorem.

## Scope, said out loud

P = 2 (`LEGC_SEATS = 2`): a pair clash re-enters BOTH seats, so the clean round's moves are both
fresh and `locked = []`. **P = 2 is not a limitation being carried — P = 2 IS the deployed game**
(`dregg-automatafl/src/reference.rs::{stock_two_player, GOAL_CORNERS_2P}`, the stock two-player 11×11
board). Board equality is stated CELL-WISE (as everywhere in this tree — `Board` carries function
fields, so `=` is neither decidable nor what any capstone states).

## `hseat0` IS DISCHARGED AT THE DEPLOYED GOAL ASSIGNMENT

The generic-`seats` capstones below take `hseat0 : seats.contains 0 = true` because they quantify
over an ARBITRARY seat list. That is not a residual and not owed work: at the deployed assignment it
is a THEOREM. `AutomataflRules.stockGoals2_seats` proves `(stockGoals2 size).seats = [0, 1]` by `rfl`
at EVERY size (`size` enters only the corner coordinates, never a seat), so
`stockGoals2_seats_contains_zero` discharges `hseat0` outright. §5b lands the deployed instances —
`rm_clean_resolves_stock` and `braid_sat_imp_runTurn_stock` — at `g := stockGoals2 11`,
`seats := (stockGoals2 11).seats`, with **NO `hseat0` hypothesis**. The generic forms are kept
because they are the more general statements.
-/
import Dregg2.Games.AutomataflTermination
import Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone

namespace Dregg2.Circuit.Emit.AutomataflBraidFold

open Dregg2.Games.Automatafl
open Dregg2.Games.AutomataflRules
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt Satisfied2)
open Dregg2.Circuit.Emit.AutomataflLegCEmit (RoundStateAgrees roundStateDecodeIn roundStateDecodeOut
  freshSubsDecode)
open Dregg2.Circuit.Emit.AutomataflLegCRefine (legC_sat_imp_roundAgainN11)
open Dregg2.Circuit.Emit.AutomataflResolveRefine (boardDecodeOldN moveDecodeN)
open Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone (outcomeBoard MovesWindow movesWindow_eleven)
open Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone (rmRoundStateIn rm_fresh_keeps_both
  automataflResolveMarksDescN turn_sat_imp_roundStepMarks_pi)
open Dregg2.Circuit.Emit.AutomataflStepRefine (codeToParticle StepCanon)
open Dregg2.Circuit.Emit.AutomataflStepEmit (automataflStepDescN)
open Dregg2.Circuit.Emit.AutomataflCommit (feltCount)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1  Board cell-agreement, and the board-derived congruences

`BoardAgrees b1 b2` is the board half of `RoundStateAgrees`: same size, same automaton, cell-wise
equal. Everything `roundStep` reads out of the board bottoms out in `cellAt` / `size` / `automaton`,
so each board-derived quantity is congruent under `BoardAgrees` — LITERALLY equal (as a function or
list) for the marks-independent ones, `BoardAgrees` again for the boards `resolveMoves` /
`automatonStepCfg` produce. -/

structure BoardAgrees (b1 b2 : Board) : Prop where
  size : b1.size = b2.size
  auto : b1.automaton = b2.automaton
  cell : ∀ c, b1.cellAt c = b2.cellAt c

namespace BoardAgrees

theorem refl (b : Board) : BoardAgrees b b := ⟨rfl, rfl, fun _ => rfl⟩

theorem symm {b1 b2 : Board} (h : BoardAgrees b1 b2) : BoardAgrees b2 b1 :=
  ⟨h.size.symm, h.auto.symm, fun c => (h.cell c).symm⟩

theorem trans {b1 b2 b3 : Board} (h : BoardAgrees b1 b2) (h' : BoardAgrees b2 b3) :
    BoardAgrees b1 b3 :=
  ⟨h.size.trans h'.size, h.auto.trans h'.auto, fun c => (h.cell c).trans (h'.cell c)⟩

end BoardAgrees

variable {b1 b2 : Board}

/-- `carAt` reads only `cellAt`. -/
theorem carAt_agree (hB : BoardAgrees b1 b2) : carAt b1 = carAt b2 := by
  funext c; unfold carAt; rw [hB.cell c]

/-- `collideAt` reads only `cellAt`. -/
theorem collideAt_agree (hB : BoardAgrees b1 b2) (ms : List Move) (d : Coord) :
    collideAt b1 ms d = collideAt b2 ms d := by
  simp only [collideAt, hB.cell]

/-- `clashCoords` reads the board only through `collideAt`. -/
theorem clashCoords_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    clashCoords b1 ms = clashCoords b2 ms := by
  simp only [clashCoords, collideAt, hB.cell]

/-- `blockedB` reads only `cellAt`. -/
theorem blockedB_agree (hB : BoardAgrees b1 b2) : blockedB b1 = blockedB b2 := by
  funext ms m; simp only [blockedB, hB.cell]

/-- `edgeMap` reads the board only through `blockedB`. -/
theorem edgeMap_agree (hB : BoardAgrees b1 b2) : edgeMap b1 = edgeMap b2 := by
  funext ms c; simp only [edgeMap, edgeOf, blockedB_agree hB]

/-- `landMap` is built from `edgeMap` and `carAt`. -/
theorem landMap_agree (hB : BoardAgrees b1 b2) : landMap b1 = landMap b2 := by
  funext ms; simp only [landMap, edgeMap_agree hB, carAt_agree hB]

/-- `movers` is built from `carAt` and `landMap`. -/
theorem movers_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    movers b1 ms = movers b2 ms := by
  simp only [movers, moverList, carAt_agree hB, landMap_agree hB]

/-- `inBounds` depends on the board only through `size`, so its `decide` is congruent. -/
theorem inBounds_decide_agree (hB : BoardAgrees b1 b2) (x : Coord) :
    decide (b1.inBounds x) = decide (b2.inBounds x) :=
  decide_eq_decide.mpr (by unfold Board.inBounds; rw [hB.size])

/-- `landBad` reads `movers`, `landMap`, `carAt`, and `inBounds` (size only). -/
theorem landBad_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    landBad b1 ms = landBad b2 ms := by
  funext c
  simp only [landBad, movers_agree hB, landMap_agree hB, carAt_agree hB, inBounds_decide_agree hB]

/-- `unresolved` reads `movers`, `landBad`, `landMap`. -/
theorem unresolved_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    unresolved b1 ms = unresolved b2 ms := by
  simp only [unresolved, movers_agree hB, landBad_agree hB, landMap_agree hB]

/-- `resolvableB` reads only `unresolved`. -/
theorem resolvableB_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    resolvableB b1 ms = resolvableB b2 ms := by
  simp only [resolvableB, unresolved_agree hB]

/-! ### The boards `resolveMoves` produces cell-agree -/

theorem writeBoard_size (b : Board) (M : List Coord) (L : Coord → Coord) :
    (writeBoard b M L).size = b.size := rfl

theorem writeBoard_auto (b : Board) (M : List Coord) (L : Coord → Coord) :
    (writeBoard b M L).automaton = b.automaton := rfl

theorem resolveMoves_size (b : Board) (ms : List Move) :
    (resolveMoves b ms).size = b.size := by
  unfold resolveMoves; split <;> rfl

theorem resolveMoves_auto (b : Board) (ms : List Move) :
    (resolveMoves b ms).automaton = b.automaton := by
  unfold resolveMoves; split <;> rfl

/-- `writeBoard` at a common mover-list / landing-map cell-agrees when the underlying boards do. -/
theorem writeBoard_cell_agree (hB : BoardAgrees b1 b2) (M : List Coord) (L : Coord → Coord)
    (q : Coord) : (writeBoard b1 M L).cellAt q = (writeBoard b2 M L).cellAt q := by
  by_cases hq : q.x < b2.size ∧ q.y < b2.size
  · have hq1 : q.x < b1.size ∧ q.y < b1.size := by rw [hB.size]; exact hq
    rw [writeBoard_cellAt b1 M L q hq1, writeBoard_cellAt b2 M L q hq]
    cases arrivalAt M L q with
    | some c => exact hB.cell c
    | none =>
      by_cases hm : memB M q = true
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm]; exact hB.cell q
  · have hq1 : ¬ (q.x < b1.size ∧ q.y < b1.size) := by rw [hB.size]; exact hq
    unfold Board.cellAt
    simp only [writeBoard_size]
    exact (if_neg hq1).trans (if_neg hq).symm

theorem resolveMoves_agree (hB : BoardAgrees b1 b2) (ms : List Move) :
    BoardAgrees (resolveMoves b1 ms) (resolveMoves b2 ms) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [resolveMoves_size, resolveMoves_size]; exact hB.size
  · rw [resolveMoves_auto, resolveMoves_auto]; exact hB.auto
  · intro q
    unfold resolveMoves
    rw [resolvableB_agree hB ms, movers_agree hB ms, landMap_agree hB]
    split
    · exact writeBoard_cell_agree hB _ _ q
    · exact hB.cell q

/-! ### `raycast` and the automaton step -/

theorem raycastFuel_agree (hB : BoardAgrees b1 b2) :
    ∀ (fuel : Nat) (x y dx dy : Int) (dist : Nat),
      raycastFuel b1 x y dx dy dist fuel = raycastFuel b2 x y dx dy dist fuel := by
  intro fuel
  induction fuel with
  | zero => intro x y dx dy dist; rfl
  | succ f ih =>
    intro x y dx dy dist
    rw [raycastFuel, raycastFuel]
    by_cases hb : (0 : Int) ≤ x + dx ∧ x + dx < b2.size ∧ (0 : Int) ≤ y + dy ∧ y + dy < b2.size
    · have hb1 : (0 : Int) ≤ x + dx ∧ x + dx < b1.size ∧ (0 : Int) ≤ y + dy ∧ y + dy < b1.size := by
        rw [hB.size]; exact hb
      simp only [if_pos hb, if_pos hb1, hB.cell]
      by_cases hv : (b2.cellAt ⟨(x + dx).toNat, (y + dy).toNat⟩).isVacuum = true
      · simp only [if_pos hv]; exact ih (x + dx) (y + dy) dx dy (dist + 1)
      · simp only [if_neg hv]
    · have hb1 : ¬ ((0 : Int) ≤ x + dx ∧ x + dx < b1.size ∧ (0 : Int) ≤ y + dy ∧ y + dy < b1.size) := by
        rw [hB.size]; exact hb
      simp only [if_neg hb, if_neg hb1]

theorem raycast_agree (hB : BoardAgrees b1 b2) (from_ : Coord) (d : Dir) :
    b1.raycast from_ d = b2.raycast from_ d := by
  unfold Board.raycast
  rw [hB.size]; exact raycastFuel_agree hB _ _ _ _ _ _

theorem automatonOffsetCfg_agree (hB : BoardAgrees b1 b2) (tb : TieBreak) :
    automatonOffsetCfg b1 tb = automatonOffsetCfg b2 tb := by
  unfold automatonOffsetCfg
  rw [hB.auto, raycast_agree hB, raycast_agree hB, raycast_agree hB, raycast_agree hB]

theorem stepTo_agree (hB : BoardAgrees b1 b2) (nc : Coord) :
    BoardAgrees (stepTo b1 nc) (stepTo b2 nc) := by
  refine ⟨hB.size, rfl, ?_⟩
  intro q
  by_cases hq : q.x < b2.size ∧ q.y < b2.size
  · have hq1 : q.x < b1.size ∧ q.y < b1.size := by rw [hB.size]; exact hq
    rw [cellAt_in (stepTo b1 nc) q hq1, cellAt_in (stepTo b2 nc) q hq]
    simp only [stepTo, hB.auto]
    by_cases h1 : q = nc
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : q = b2.automaton
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, ← cellAt_in b1 q hq1, ← cellAt_in b2 q hq]
        exact hB.cell q
  · have hq1 : ¬ (q.x < b1.size ∧ q.y < b1.size) := by rw [hB.size]; exact hq
    unfold Board.cellAt
    simp only [show (stepTo b1 nc).size = b1.size from rfl, show (stepTo b2 nc).size = b2.size from rfl]
    rw [if_neg hq1, if_neg hq]

theorem automatonStepCfg_agree (hB : BoardAgrees b1 b2) (cfg : GameConfig) :
    BoardAgrees (automatonStepCfg cfg b1) (automatonStepCfg cfg b2) := by
  simp only [automatonStepCfg, automatonOffsetCfg_agree hB, hB.auto, hB.size, hB.cell]
  split
  · exact stepTo_agree hB _
  · exact hB

theorem winOnEntry_agree {before1 before2 after1 after2 : Board}
    (hbefore : BoardAgrees before1 before2) (hafter : BoardAgrees after1 after2)
    (g : GoalAssignment) : winOnEntry before1 after1 g = winOnEntry before2 after2 g := by
  unfold winOnEntry
  rw [hbefore.auto, hafter.auto]

/-- `MoveLegal` reads the board through `size` / `automaton` and `marks` through `∈` — the first two
`BoardAgrees`-congruent, the last `Perm`-invariant. -/
theorem MoveLegal_agree {marks1 marks2 : List Coord} (hB : BoardAgrees b1 b2)
    (hm : marks1.Perm marks2) (m : Move) :
    MoveLegal b1 marks1 m ↔ MoveLegal b2 marks2 m := by
  simp only [MoveLegal, Board.inBounds, Board.isAutomaton, hB.size, hB.auto, hm.mem_iff]

theorem moveLegalB_agree {marks1 marks2 : List Coord} (hB : BoardAgrees b1 b2)
    (hm : marks1.Perm marks2) (m : Move) :
    moveLegalB b1 marks1 m = moveLegalB b2 marks2 m := by
  unfold moveLegalB
  exact decide_eq_decide.mpr (MoveLegal_agree hB hm m)

/-! ## §2  `roundStep` is `RoundStateAgrees`-congruent

`RoundStateAgrees` (M1's honest relation: board cell-agreement, `marks` up to `Perm`, `locked` /
`waiting` EQUAL) is preserved by one round: the fresh filter reads `waiting` (equal), `board`
(cell-agree) and `marks` (`Perm`), so it keeps the SAME list; `all = locked ++ fresh` is then EQUAL;
the clash set is a board-congruent list, hence EQUAL; so the re-entry `locked` / `waiting` are EQUAL,
the re-entry `marks` are `Perm`, and the resolved board / winner are `BoardAgrees` / equal. -/

/-- The board half of `RoundStateAgrees`. -/
theorem rs_boardAgrees {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2) :
    BoardAgrees rs1.board rs2.board :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem roundFresh_agree {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2) (subs : List Move) :
    roundFresh rs1 subs = roundFresh rs2 subs := by
  obtain ⟨hsize, hauto, hcell, hmarks, hlocked, hwaiting⟩ := h
  unfold roundFresh
  apply List.filter_congr
  intro m _
  rw [hwaiting, moveLegalB_agree ⟨hsize, hauto, hcell⟩ hmarks m]

theorem roundAll_agree {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2) (subs : List Move) :
    roundAll rs1 subs = roundAll rs2 subs := by
  unfold roundAll
  rw [h.2.2.2.2.1, roundFresh_agree h subs]

theorem roundCs_agree {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2) (subs : List Move) :
    roundCs rs1 subs = roundCs rs2 subs := by
  have hB := rs_boardAgrees h
  unfold roundCs
  rw [roundAll_agree h subs, clashCoords_agree hB (roundAll rs2 subs),
    unresolved_agree hB (roundAll rs2 subs)]

theorem roundAgainState_agree {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2)
    (subs : List Move) :
    RoundStateAgrees (roundAgainState rs1 subs) (roundAgainState rs2 subs) := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
  · simp only [roundAgainState, roundCs_agree h subs]
    exact (h.2.2.2.1.append_right _).dedup
  · simp only [roundAgainState, roundAll_agree h subs, roundCs_agree h subs]
  · simp only [roundAgainState, roundAll_agree h subs, roundCs_agree h subs]

/-- **`roundStep` congruence.** On `RoundStateAgrees` inputs, one round produces the SAME outcome
constructor: `Perm`-agreeing re-entry states, or `BoardAgrees` resolved boards with equal winner. -/
theorem roundStep_agree (cfg : GameConfig) (g : GoalAssignment) {rs1 rs2 : RoundState}
    (subs : List Move) (h : RoundStateAgrees rs1 rs2) :
    (match roundStep cfg g rs1 subs, roundStep cfg g rs2 subs with
     | .again a1, .again a2 => RoundStateAgrees a1 a2
     | .resolved bd1 w1, .resolved bd2 w2 => BoardAgrees bd1 bd2 ∧ w1 = w2
     | _, _ => False) := by
  have hB := rs_boardAgrees h
  rw [roundStep_eq, roundStep_eq, roundCs_agree h subs, roundAll_agree h subs]
  by_cases hcs : (roundCs rs2 subs).isEmpty = true
  · simp only [if_pos hcs]
    refine ⟨?_, ?_⟩
    · exact automatonStepCfg_agree (resolveMoves_agree hB (roundAll rs2 subs)) cfg
    · exact winOnEntry_agree (resolveMoves_agree hB (roundAll rs2 subs))
        (automatonStepCfg_agree (resolveMoves_agree hB (roundAll rs2 subs)) cfg) g
  · simp only [if_neg hcs]
    exact roundAgainState_agree h subs

/-! ## §3  `RoundStateAgrees` algebra, the fold seam, and the accepted-leaf predicate -/

theorem rsagrees_refl (rs : RoundState) : RoundStateAgrees rs rs :=
  ⟨rfl, rfl, fun _ => rfl, List.Perm.refl _, rfl, rfl⟩

theorem rsagrees_symm {rs1 rs2 : RoundState} (h : RoundStateAgrees rs1 rs2) :
    RoundStateAgrees rs2 rs1 :=
  ⟨h.1.symm, h.2.1.symm, fun c => (h.2.2.1 c).symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm,
    h.2.2.2.2.2.symm⟩

theorem rsagrees_trans {rs1 rs2 rs3 : RoundState} (h : RoundStateAgrees rs1 rs2)
    (h' : RoundStateAgrees rs2 rs3) : RoundStateAgrees rs1 rs3 :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun c => (h.2.2.1 c).trans (h'.2.2.1 c),
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.1.trans h'.2.2.2.2.1,
    h.2.2.2.2.2.trans h'.2.2.2.2.2⟩

/-- **The fold seam.** `FoldSeam rs0 [t₀,…,t_{k-1}] rsT` says: `rs0` agrees with `decodeIn t₀`, each
`decodeOut tᵢ` agrees with `decodeIn tᵢ₊₁`, and `decodeOut t_{k-1}` agrees with the clean round's
target `rsT` (or, when `k = 0`, `rs0` agrees with `rsT` directly). This is exactly the chain of
RoundState-window equalities the light-client fold checks between the emitted proofs. -/
def FoldSeam : RoundState → List VmTrace → RoundState → Prop
  | rs0, [], rsT => RoundStateAgrees rs0 rsT
  | rs0, t :: ts, rsT =>
      RoundStateAgrees rs0 (roundStateDecodeIn 11 (envAt t 0))
      ∧ FoldSeam (roundStateDecodeOut 11 (envAt t 0)) ts rsT

/-- The seam is left-congruent under `RoundStateAgrees`: a state that agrees with the seam's head
seams the same tail. -/
theorem FoldSeam_congr_head {a b rsT : RoundState} (hab : RoundStateAgrees a b) :
    ∀ ts : List VmTrace, FoldSeam b ts rsT → FoldSeam a ts rsT
  | [], hb => rsagrees_trans hab hb
  | _ :: _, hb => ⟨rsagrees_trans hab hb.1, hb.2⟩

/-- **An accepted Leg C leaf** — a satisfying, canonical, non-trivial trace of the deployed Leg C
descriptor. Its own hash / init / final / mem-address witnesses are existential (each round is a
separate proof). -/
def LegCAccepted (t : VmTrace) : Prop :=
  ∃ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
    Satisfied2 hash (Dregg2.Circuit.Emit.AutomataflLegCEmit.automataflLegCDescN 11) minit mfin maddrs t
      ∧ StepCanon t ∧ 1 < t.rows.length

/-- M2, packaged: an accepted Leg C leaf decodes to one `roundStep .again` round, up to
`RoundStateAgrees` on the produced re-entry state. -/
theorem legCAccepted_again (g : GoalAssignment) {t : VmTrace} (ht : LegCAccepted t) :
    ∃ rs', roundStep ⟨.column⟩ g (roundStateDecodeIn 11 (envAt t 0)) (freshSubsDecode 11 (envAt t 0))
             = .again rs'
           ∧ RoundStateAgrees rs' (roundStateDecodeOut 11 (envAt t 0)) := by
  obtain ⟨hash, minit, mfin, maddrs, hsat, hc, hlen⟩ := ht
  exact legC_sat_imp_roundAgainN11 g hsat hc hlen

/-- The decoded per-round submissions each round of the fold consumes. -/
def conflictSubs (t : VmTrace) : List Move := freshSubsDecode 11 (envAt t 0)

/-- The clean round's two decoded submissions (P = 2: both seats are fresh). -/
def cleanSubs (tR : VmTrace) : List Move :=
  [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1]

/-! ## §4  The conflict-round fold

`runTurn` over the k conflict rounds' decoded submissions peels off k `.again` steps and lands in a
state that `RoundStateAgrees` the clean round's target — threading M2 through `roundStep_agree` at
each step, and `roundStep_again_wf` for the `RoundWF` invariant that keeps the seam meaningful. -/

theorem runTurn_conflict_fold (g : GoalAssignment) (rsT : RoundState) (rest : List (List Move)) :
    ∀ (Cs : List VmTrace) (rs0 : RoundState), RoundWF rs0 →
      (∀ t ∈ Cs, LegCAccepted t) → FoldSeam rs0 Cs rsT →
      ∃ rsK, RoundWF rsK ∧ RoundStateAgrees rsK rsT
        ∧ runTurn ⟨.column⟩ g rs0 (Cs.map conflictSubs ++ rest)
            = runTurn ⟨.column⟩ g rsK rest := by
  intro Cs
  induction Cs with
  | nil =>
    intro rs0 hwf _ hseam
    exact ⟨rs0, hwf, hseam, by simp only [List.map_nil, List.nil_append]⟩
  | cons t ts ih =>
    intro rs0 hwf hacc hseam
    obtain ⟨hbase, htail⟩ := hseam
    obtain ⟨rs'd, hstepd, hagreed⟩ := legCAccepted_again g (hacc t List.mem_cons_self)
    have hcong := roundStep_agree ⟨.column⟩ g (freshSubsDecode 11 (envAt t 0)) hbase
    rw [hstepd] at hcong
    cases hstep0 : roundStep ⟨.column⟩ g rs0 (freshSubsDecode 11 (envAt t 0)) with
    | resolved bd w => rw [hstep0] at hcong; exact hcong.elim
    | again rs'0 =>
      rw [hstep0] at hcong
      have hcong' : RoundStateAgrees rs'0 rs'd := hcong
      have hwf'0 : RoundWF rs'0 := roundStep_again_wf hwf hstep0
      have hagree'0 : RoundStateAgrees rs'0 (roundStateDecodeOut 11 (envAt t 0)) :=
        rsagrees_trans hcong' hagreed
      have hseam'0 : FoldSeam rs'0 ts rsT := FoldSeam_congr_head hagree'0 ts htail
      obtain ⟨rsK, hwfK, hagreeK, hrun⟩ :=
        ih rs'0 hwf'0 (fun t' ht' => hacc t' (List.mem_cons_of_mem _ ht')) hseam'0
      refine ⟨rsK, hwfK, hagreeK, ?_⟩
      rw [List.map_cons, List.cons_append]
      simp only [runTurn, conflictSubs, hstep0]
      exact hrun

/-! ## §5  The M7 capstone -/

/-- The clean round of the accumulated `RoundState` RESOLVES (constructor `.resolved`): the fresh
filter keeps both moves (`rm_fresh_keeps_both`), `hclean` empties the clash set, `hres` empties the
merge set, so `roundStep` takes the resolve branch. -/
theorem rm_clean_resolves (g : GoalAssignment) (seats : List Pid)
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length) (hseat0 : seats.contains 0 = true)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true) :
    ∃ afterRM winRM,
      roundStep ⟨.column⟩ g (rmRoundStateIn 11 (envAt tR 0) seats) (cleanSubs tR)
        = .resolved afterRM winRM := by
  have hfresh := rm_fresh_keeps_both movesWindow_eleven.base hsatR hcR hlenR seats hseat0
  have hall : roundAll (rmRoundStateIn 11 (envAt tR 0) seats) (cleanSubs tR) = cleanSubs tR := by
    unfold roundAll roundFresh
    show (rmRoundStateIn 11 (envAt tR 0) seats).locked ++ _ = cleanSubs tR
    rw [show (rmRoundStateIn 11 (envAt tR 0) seats).locked = [] from rfl, List.nil_append]
    exact hfresh
  have hcs0 : roundCs (rmRoundStateIn 11 (envAt tR 0) seats) (cleanSubs tR) = [] := by
    unfold roundCs
    rw [hall]
    have hclash : clashCoords (rmRoundStateIn 11 (envAt tR 0) seats).board (cleanSubs tR) = [] :=
      hclean
    rw [hclash]
    simp only [List.isEmpty_nil, if_true]
    exact (List.isEmpty_iff.mp hres :
      unresolved (rmRoundStateIn 11 (envAt tR 0) seats).board (cleanSubs tR) = [])
  have hcs : (roundCs (rmRoundStateIn 11 (envAt tR 0) seats) (cleanSubs tR)).isEmpty = true :=
    List.isEmpty_iff.mpr hcs0
  exact ⟨_, _, by rw [roundStep_eq, if_pos hcs]⟩

/-- **`braid_sat_imp_runTurn` — THE M7 WHOLE-TURN CAPSTONE (n = 11, P = 2).**

Given a chain of accepted Leg C conflict rounds `Cs` whose decoded RoundState windows seam
(`FoldSeam`) into the clean round's accumulated state `rmRoundStateIn tR`, and the clean round's
resolve-marks (`tR`) + step (`tA`) traces satisfying the M6 hypotheses (with `marksIn` carried by the
seam), the whole multi-round turn `runTurn` RESOLVES, and its final board is — cell for cell — the
board decoded off the step trace `tA`. The conflict rounds are threaded by M2 through the
`RoundStateAgrees` congruence of `roundStep`; the clean round is M6. -/
theorem braid_sat_imp_runTurn (g : GoalAssignment) (seats : List Pid) (b0 : Board)
    (Cs : List VmTrace) (hCsAcc : ∀ t ∈ Cs, LegCAccepted t)
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA (automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hseat0 : seats.contains 0 = true)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true)
    (hseamPack : ∀ j, j < feltCount 11 → tR.pub (16 + feltCount 11 + j) = tA.pub (16 + j))
    (hseamAutoX : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1))
    (hfold : FoldSeam (openRound b0 seats) Cs (rmRoundStateIn 11 (envAt tR 0) seats)) :
    ∃ (finalBoard : Board) (win : Option Pid),
      runTurn ⟨.column⟩ g (openRound b0 seats) (Cs.map conflictSubs ++ [cleanSubs tR])
          = some (finalBoard, win)
      ∧ ∀ x y : Nat, x < 11 → y < 11 →
          codeToParticle ((envAt tA 0).loc
              (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
            = finalBoard.cellAt ⟨x, y⟩ := by
  -- 1. Fold the conflict rounds: land in `rsK` agreeing with the clean round's target.
  obtain ⟨rsK, _, hagreeK, hrun⟩ :=
    runTurn_conflict_fold g (rmRoundStateIn 11 (envAt tR 0) seats) [cleanSubs tR] Cs
      (openRound b0 seats) (roundWF_openRound b0 seats) hCsAcc hfold
  -- 2. The clean round resolves for the decoded target.
  obtain ⟨afterRM, winRM, hRMres⟩ := rm_clean_resolves g seats hsatR hcR hlenR hseat0 hclean hres
  -- 3. Congruence: `rsK` agrees the target, so its clean round resolves to a cell-agreeing board.
  have hcong := roundStep_agree ⟨.column⟩ g (cleanSubs tR) hagreeK
  rw [hRMres] at hcong
  cases hstepK : roundStep ⟨.column⟩ g rsK (cleanSubs tR) with
  | again a => rw [hstepK] at hcong; exact hcong.elim
  | resolved after' win' =>
    rw [hstepK] at hcong
    have hcong' : BoardAgrees after' afterRM ∧ win' = winRM := hcong
    obtain ⟨hBoard, _⟩ := hcong'
    refine ⟨after', win', ?_, ?_⟩
    · rw [hrun]
      simp only [runTurn, hstepK]
    · intro x y hx hy
      have hM6 := turn_sat_imp_roundStepMarks_pi g seats hsatR hcR hlenR hsatA hcA hlenA hseat0
        hclean hres hseamPack hseamAutoX hseamAutoY x y hx hy
      rw [show ([moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] : List Move)
            = cleanSubs tR from rfl] at hM6
      rw [hRMres] at hM6
      simp only [outcomeBoard] at hM6
      rw [hM6]
      exact (hBoard.cell ⟨x, y⟩).symm

/-! ## §5b  THE DEPLOYED-GAME INSTANCE — `hseat0` DISCHARGED, NOT ASSUMED

The stock two-player 11×11 game is what runs: `stockGoals2 11` is `reference.rs::GOAL_CORNERS_2P`
corner for corner, and `stockGoals2_seats` computes its seat list to `[0, 1]` by `rfl`. Instantiating
the capstones there turns the who-routing hypothesis into a proof obligation we DISCHARGE, so the
deployed statements are unconditional in the seats: every hypothesis they still carry is about the
TRACES (satisfaction of the emitted descriptors, canonicity, the PI seam, this round being clean and
resolvable) or about the fold seam — none about the ruleset.

What this does NOT change: the shape is still `descriptor-satisfaction → spec`, standing on the same
undischarged proof-system floor as every capstone in this tree. Discharging `hseat0` retires a
GAME-RULES hypothesis, not a soundness one. -/

/-- `rm_clean_resolves` at the deployed goal assignment — no `hseat0`. -/
theorem rm_clean_resolves_stock
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true) :
    ∃ afterRM winRM,
      roundStep ⟨.column⟩ (stockGoals2 11)
          (rmRoundStateIn 11 (envAt tR 0) (stockGoals2 11).seats) (cleanSubs tR)
        = .resolved afterRM winRM :=
  rm_clean_resolves (stockGoals2 11) (stockGoals2 11).seats hsatR hcR hlenR
    (stockGoals2_seats_contains_zero 11) hclean hres

/-- **`braid_sat_imp_runTurn_stock` — THE M7 WHOLE-TURN CAPSTONE FOR THE GAME THAT IS DEPLOYED.**

`braid_sat_imp_runTurn` with the goal assignment and the seat list fixed to the stock two-player
11×11 game (`stockGoals2 11` = `reference.rs::GOAL_CORNERS_2P`; seats `[0, 1]`), and with **NO
`hseat0` hypothesis** — `stockGoals2_seats_contains_zero` discharges it. Given a chain of accepted
Leg C conflict rounds seaming into the clean round's accumulated state, plus the clean round's
resolve-marks and step traces, the whole multi-round turn of the DEPLOYED game RESOLVES and its final
board is, cell for cell, the board decoded off the step trace. -/
theorem braid_sat_imp_runTurn_stock (b0 : Board)
    (Cs : List VmTrace) (hCsAcc : ∀ t ∈ Cs, LegCAccepted t)
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA (automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true)
    (hseamPack : ∀ j, j < feltCount 11 → tR.pub (16 + feltCount 11 + j) = tA.pub (16 + j))
    (hseamAutoX : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1))
    (hfold : FoldSeam (openRound b0 (stockGoals2 11).seats) Cs
        (rmRoundStateIn 11 (envAt tR 0) (stockGoals2 11).seats)) :
    ∃ (finalBoard : Board) (win : Option Pid),
      runTurn ⟨.column⟩ (stockGoals2 11) (openRound b0 (stockGoals2 11).seats)
            (Cs.map conflictSubs ++ [cleanSubs tR])
          = some (finalBoard, win)
      ∧ ∀ x y : Nat, x < 11 → y < 11 →
          codeToParticle ((envAt tA 0).loc
              (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
            = finalBoard.cellAt ⟨x, y⟩ :=
  braid_sat_imp_runTurn (stockGoals2 11) (stockGoals2 11).seats b0 Cs hCsAcc hsatR hcR hlenR
    hsatA hcA hlenA (stockGoals2_seats_contains_zero 11) hclean hres hseamPack hseamAutoX hseamAutoY
    hfold

/-! ### Non-vacuity canaries for the deployed instance

The instantiation fixes the RULESET, not the traces: the seat list it substitutes is the real
two-seat list, and the opening round it substitutes really has BOTH seats waiting and nothing
locked / marked — so the clean round's fresh filter has two live seats to admit, not an empty one
that would make the fold trivially true. -/

#guard (stockGoals2 11).seats = [0, 1]
#guard (stockGoals2 11) = GoalAssignment.mk [(⟨0, 0⟩, 0), (⟨10, 0⟩, 0), (⟨0, 10⟩, 1), (⟨10, 10⟩, 1)]
#guard (openRound stockTwoPlayer (stockGoals2 11).seats).waiting = [0, 1]
#guard (openRound stockTwoPlayer (stockGoals2 11).seats).locked = []
#guard (openRound stockTwoPlayer (stockGoals2 11).seats).marks = []
-- and `hseat0` is NOT a tautology over goal assignments — an assignment that seats nobody at `0`
-- refutes it. The deployed one satisfies it, which is what makes the discharge above CONTENT.
#guard (GoalAssignment.mk [(⟨0, 0⟩, 5), (⟨10, 10⟩, 7)]).seats.contains 0 = false

/-! ## §6  Axiom hygiene -/

#assert_all_clean [
  moveLegalB_agree,
  resolveMoves_agree,
  raycastFuel_agree,
  automatonStepCfg_agree,
  winOnEntry_agree,
  roundFresh_agree,
  roundCs_agree,
  roundAgainState_agree,
  roundStep_agree,
  rsagrees_trans,
  FoldSeam_congr_head,
  legCAccepted_again,
  runTurn_conflict_fold,
  rm_clean_resolves,
  braid_sat_imp_runTurn,
  rm_clean_resolves_stock,
  braid_sat_imp_runTurn_stock
]

#print axioms braid_sat_imp_runTurn
#print axioms braid_sat_imp_runTurn_stock

end Dregg2.Circuit.Emit.AutomataflBraidFold
