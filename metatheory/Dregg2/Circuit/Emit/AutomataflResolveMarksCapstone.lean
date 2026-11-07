/-
# `AutomataflResolveMarksCapstone` — LEG R FOR A **CLEAN ROUND OF A MULTI-ROUND TURN** (braid **M6**).

`docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md` §4.3, §9.3, §10 (M6, the B3 work). The existing
resolve capstone (`AutomataflResolveMovesCapstone.resolve_sat_imp_roundBoardN`) proves the emitted
`cMidV4` board IS `AutomataflRules.roundStep`'s resolve board — but only for a FIRST round: the moves
are the raw decoded pair and `marks = []`. A multi-round turn's CLEAN round consumes an ACCUMULATED
`RoundState` (`marks ≠ []`, from the prior Leg C clash rounds), and the fresh submissions must be
`MoveLegal` **against those accumulated marks**.

## THE DECISION — RE-CHECK, not INHERIT (and why it is the sound one)

The clean round N is preceded by its OWN reveal `S_N`; its fresh moves have passed NO Leg C legality
gate (each clash round adjudicates its OWN round's submissions, and round N is not a clash). The
RoundState seam carries the marks **VALUE** (`C_last.OUT.marks == R.IN.marks`), but the seam does NOT
check that round N's fresh moves avoid those marks. So the marks-legality `frm,to ∉ marksIn` of the
clean round's moves is UNATTESTED unless Leg R itself re-checks it. INHERIT would rest the legality on
a gate that never ran. Therefore **the clean-round resolve leg RE-CHECKS marks-legality** — exactly as
Leg C does — and this file makes it a THEOREM of the descriptor, not an assumed hypothesis
(`resolveMarksMoveLegal`). At `marks = []` the re-check is vacuous, which is why the old capstone did
not need it.

## THE KEY OBSERVATION — `resolveMoves` is MARKS-INDEPENDENT

`AutomataflRules.resolveMoves bd ms` never reads `marks`; marks gate LEGALITY at PROPOSAL, not the
resolution function. So the emitted `cMidV4 = resolveMoves` is UNCHANGED by the marks carry, and the
board half REUSES `resolve_sat_imp_roundBoardN` verbatim (via the restriction lemma below). What M6
ADDS is (a) the accumulated `marksIn` WINDOW carried (published, base-4 injective, closing the seam to
Leg C's `marksOut`), and (b) the marks-legality re-check.

## THE ARCHITECTURE — ADDITIVE

`automataflResolveMarksDescN n` is `automataflResolveDescN n`'s constraints PLUS a marks tail (the
`marksIn` commitment `AutomataflMarks.marksCommitFamilyAt`, the destination one-hots, and the two
marks-legality gates), at fresh columns above `R_WIDTH n`. It touches NOTHING in the resolve
descriptor or its byte-golden. The tail carries NO memOp / mapOp / hash site, so
`resolveMarks_restrict` recovers a full `Satisfied2 (automataflResolveDescN n)` from a satisfying
marks-descriptor trace, and the whole resolve capstone chain applies unchanged.

⚑ **SUBSTRATE, SAID OUT LOUD.** This is **LEAN-AUTHORED AIR**. Every gate is a `VmConstraint2` emitted
here; Rust only fills traces. `dregg-automatafl/src/{air,moves,builder}.rs` stays DEBT.

## Axiom hygiene
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no
assumed-hypothesis, no weakened capstone.
-/
import Dregg2.Circuit.Emit.AutomataflTurnCapstone
import Dregg2.Circuit.Emit.AutomataflLegCRefine

namespace Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.AutomataflStepRefine (StepCanon canon_loc eq_of_modEq_canon codeToParticle
  canon_one canon_zero)
open Dregg2.Circuit.Emit.AutomataflResolveRefine (boardDecodeOldN moveDecodeN validMoveN_of_sat)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow mvLift)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Circuit.Emit.AutomataflLegCRefine (readAt_collapse mem_marksListDecode_iff)
open Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
  (MovesWindow movesWindow_two movesWindow_three movesWindow_eleven resolve_sat_imp_roundBoardN
   outcomeBoard roundStep_pair_outcomeBoard)
open Dregg2.Circuit.Emit.AutomataflMarks (marksCommitFamilyAt marksDecodeAt marksCode marksBoardOf
  marksWindowLanes mem2_of_gate)
open Dregg2.Circuit.Emit.AutomataflLegCEmit (readAtHead norHead marksListDecode piPin)
open Dregg2.Circuit.Emit.AutomataflCommit (feltCount packCell boardCode)
open Dregg2.Games.Automatafl (Board Coord Particle Move Pid MoveValid)
open Dregg2.Games.AutomataflRules (RoundState roundStep clashCoords resolveMoves resolvableB moveLegalB
  moveLegalB_iff MoveLegal GameConfig GoalAssignment automatonStepCfg openRound unresolved
  stockGoals2 stockGoals2_seats stockGoals2_seats_contains_zero)
open Dregg2.Circuit.Emit.AutomataflTurnCapstone (turn_sat_imp_roundStep_pi)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1 — THE COLUMN LAYOUT (a marks tail above `R_WIDTH n`).

The resolve descriptor occupies `[0, R_WIDTH n)`. The marks tail begins at `RM0 n = R_WIDTH n`, so the
two never collide and the resolve descriptor's own columns keep their numerals. -/

/-- The marks tail's base column. -/
def RM0 (n : Nat) : Nat := NGen.R_WIDTH n
/-- `marksIn` indicator cell `c` (linear index `y·n + x`). -/
def rMarksInCell (n : Nat) (c : Nat) : Nat := RM0 n + c
/-- `marksIn` packed felt `j`. -/
def rMarksInFelt (n : Nat) (j : Nat) : Nat := RM0 n + NGen.KK n + j
/-- Base of the destination one-hot block (Leg R's dst one-hots live inside its dropped occlusion
block; the marks legality needs its own, like Leg C). -/
def RTSEL0 (n : Nat) : Nat := RM0 n + NGen.KK n + NGen.RFC n
/-- Destination-ROW selector `j` of move `w` (one-hot at `cTy`). -/
def rTSelRow (n w j : Nat) : Nat := RTSEL0 n + (2 * n) * w + j
/-- Destination-COLUMN selector `j` of move `w` (one-hot at `cTx`). -/
def rTSelCol (n w j : Nat) : Nat := RTSEL0 n + (2 * n) * w + n + j
/-- Base of the per-move marks-query block. -/
def RMVQ0 (n : Nat) : Nat := RTSEL0 n + 2 * (2 * n)
/-- `marksIn[frm[w]]` — the source-endpoint marks read. -/
def rInMarksFrm (n w : Nat) : Nat := RMVQ0 n + 3 * w + 0
/-- `marksIn[to[w]]` — the destination-endpoint marks read. -/
def rInMarksTo (n w : Nat) : Nat := RMVQ0 n + 3 * w + 1
/-- `legal[w] = ¬inMarksFrm ∧ ¬inMarksTo` — the marks half of `moveLegalB`, PINNED to `1`. -/
def rLegal (n w : Nat) : Nat := RMVQ0 n + 3 * w + 2
/-- The marks-descriptor trace width. -/
def RM_WIDTH (n : Nat) : Nat := RMVQ0 n + 3 * 2

/-- `marksIn`'s published window base (append-only past the resolve descriptor's PIs). -/
def rPiMarksIn (n : Nat) : Nat := NGen.R_PI_COUNT n

/-! ## §2 — THE MARKS TAIL FAMILIES (all `.base`; NO memOp / mapOp / hash site). -/

/-- The `marksIn` commitment — M0's `marksCommitFamilyAt`: `{0,1}` range gates ‖ base-4 pack gates ‖
packed-felt PI bindings. NOT re-implemented. -/
def rMarksFamily (n : Nat) : List VmConstraint2 :=
  marksCommitFamilyAt n (rMarksInCell n) (rMarksInFelt n) (rPiMarksIn n)

/-- The destination one-hots of move `w`, pinned at its `(tx, ty)` columns. -/
def rDestOneHot (n w : Nat) : List VmConstraint2 :=
  oneHotAtCol ((List.range n).map (rTSelRow n w)) (NGen.cTy n (NGen.mvBase n w))
  ++ oneHotAtCol ((List.range n).map (rTSelCol n w)) (NGen.cTx n (NGen.mvBase n w))

/-- **THE MARKS LEGALITY GATE.** `inMarksFrm[w]` / `inMarksTo[w]` are `marksIn` read at the move's two
endpoints through the resolve descriptor's SOURCE one-hots (`cSelRow`/`cSelCol`, already pinned at
`(fx,fy)` by `validateMove`) and this file's DESTINATION one-hots (pinned at `(tx,ty)`). `legal[w]` is
their NOR, PINNED to `1`: a submission naming a marked square makes the leaf UNSAT — exactly
`roundStep`'s `subs.filter (… moveLegalB …)` refusing it. The geometric half of `MoveLegal` is already
forced by the resolve descriptor's own `validateMove`. -/
def rLegality (n w : Nat) : List VmConstraint2 :=
  [ cgH (readAtHead n (rInMarksFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
          (NGen.cSelCol n (NGen.mvBase n w)) (rMarksInCell n))
  , cgH (readAtHead n (rInMarksTo n w) (rTSelRow n w) (rTSelCol n w) (rMarksInCell n))
  , cgH (norHead (rLegal n w) (rInMarksFrm n w) (rInMarksTo n w))
  , cgH ((Head.lin 1 (rLegal n w)).addConst (-1)) ]

/-- The marks tail's families (a list-of-families, so membership is ONE `List.mem_flatten` step). -/
def resolveMarksFamilies (n : Nat) : List (List VmConstraint2) :=
  [ rMarksFamily n, rDestOneHot n 0, rDestOneHot n 1, rLegality n 0, rLegality n 1 ]

/-- The whole marks tail. -/
def resolveMarksTail (n : Nat) : List VmConstraint2 := (resolveMarksFamilies n).flatten

/-- **`automataflResolveMarksDescN n`** — the marks-carrying resolve descriptor. Additive: the resolve
constraints VERBATIM, then the marks tail. -/
def automataflResolveMarksDescN (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-resolve-marks-n" ++ toString n
  , traceWidth  := RM_WIDTH n
  , piCount     := NGen.R_PI_COUNT n + feltCount n
  , tables      := []
  , constraints := NGen.resolveConstraints n ++ resolveMarksTail n
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — THE TAIL IS memOp/mapOp-FREE (the restriction-lemma obligation). -/

/-- A generic "every element of `l.map g` is `.base`" step. -/
theorem base_of_mem_map {α : Type} {l : List α} {g : α → VmConstraint2}
    (hg : ∀ a, ∃ b, g a = VmConstraint2.base b) {c : VmConstraint2} (hc : c ∈ l.map g) :
    ∃ b, c = VmConstraint2.base b := by
  rw [List.mem_map] at hc; obtain ⟨a, _, rfl⟩ := hc; exact hg a

/-- `rMarksFamily` is all `.base` (the three commitment sub-families are maps into `.base`). -/
theorem marksFamily_base (n : Nat) : ∀ c ∈ rMarksFamily n, ∃ b, c = VmConstraint2.base b := by
  intro c hc
  simp only [rMarksFamily, marksCommitFamilyAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksRangeCellsAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksPackConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksCommitConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflCommit.packBoardConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflCommit.commitBoardConstraintsAt, List.mem_append] at hc
  rcases hc with (h | h) | h <;>
    · exact base_of_mem_map (fun _ => ⟨_, rfl⟩) h

/-- `rDestOneHot` is all `.base` (`oneHotAtCol` = map of `cg`, then two `cgH`s). -/
theorem destOneHot_base (n w : Nat) : ∀ c ∈ rDestOneHot n w, ∃ b, c = VmConstraint2.base b := by
  intro c hc
  simp only [rDestOneHot, oneHotAtCol, oneHotConstraints, List.mem_append,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with ((h | h) | h) | ((h | h) | h) <;>
    first
      | (exact base_of_mem_map (fun _ => ⟨_, rfl⟩) h)
      | (subst h; exact ⟨_, rfl⟩)

/-- `rLegality` is all `.base` (four `cgH`s). -/
theorem legality_base (n w : Nat) : ∀ c ∈ rLegality n w, ∃ b, c = VmConstraint2.base b := by
  intro c hc
  simp only [rLegality, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- Every constraint in the marks tail is a `.base` constraint. -/
theorem tail_all_base (n : Nat) : ∀ c ∈ resolveMarksTail n, ∃ b, c = VmConstraint2.base b := by
  intro c hc
  rw [resolveMarksTail, List.mem_flatten] at hc
  obtain ⟨fam, hfam, hc⟩ := hc
  simp only [resolveMarksFamilies, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hfam
  rcases hfam with rfl | rfl | rfl | rfl | rfl
  · exact marksFamily_base n c hc
  · exact destOneHot_base n 0 c hc
  · exact destOneHot_base n 1 c hc
  · exact legality_base n 0 c hc
  · exact legality_base n 1 c hc

theorem tail_memfree (n : Nat) :
    (resolveMarksTail n).filterMap
      (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem tail_mapfree (n : Nat) :
    (resolveMarksTail n).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

/-! ## §4 — THE RESTRICTION LEMMA. -/

section Restrict
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- `x ++ y = x` when `y = []` (lambda-free, so the remaining subgoal keeps the goal's own term). -/
theorem append_eq_self_nil {α : Type} {x y : List α} (h : y = []) : x ++ y = x := by
  rw [h, List.append_nil]

theorem memOpsOf_restrict :
    memOpsOf (automataflResolveMarksDescN n) = memOpsOf (automataflResolveDescN n) := by
  show (NGen.resolveConstraints n ++ resolveMarksTail n).filterMap _
      = (NGen.resolveConstraints n).filterMap _
  rw [List.filterMap_append]
  refine append_eq_self_nil ?_
  apply List.filterMap_eq_nil_iff.mpr
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem mapOpsOf_restrict :
    mapOpsOf (automataflResolveMarksDescN n) = mapOpsOf (automataflResolveDescN n) := by
  show (NGen.resolveConstraints n ++ resolveMarksTail n).filterMap _
      = (NGen.resolveConstraints n).filterMap _
  rw [List.filterMap_append]
  refine append_eq_self_nil ?_
  apply List.filterMap_eq_nil_iff.mpr
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem memLog_restrict :
    memLog (automataflResolveMarksDescN n) t = memLog (automataflResolveDescN n) t := by
  simp only [memLog, memOpsOf_restrict]

theorem mapLog_restrict :
    mapLog (automataflResolveMarksDescN n) t = mapLog (automataflResolveDescN n) t := by
  simp only [mapLog, mapOpsOf_restrict]

/-- **`resolveMarks_restrict` — the reuse enabler.** A satisfying marks-descriptor trace restricts to
a satisfying resolve-descriptor trace on the SAME `t` / `minit` / `mfin` / `maddrs`. The resolve
constraints are a prefix of the marks constraints (`mem_append_left`); the marks tail adds no memOp /
mapOp / hash / range, so every memory / table leg transfers by rewriting the logs. -/
theorem resolveMarks_restrict
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t) :
    Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t := by
  refine ⟨?_, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    exact hsat.rowConstraints i hi c (List.mem_append_left _ hc)
  · intro i _; trivial
  · intro i _ r hr; cases hr
  · intro op hop
    exact hsat.memClosed op (by rw [memLog_restrict]; exact hop)
  · rw [← memLog_restrict]; exact hsat.memDisciplined
  · rw [← memLog_restrict]; exact hsat.memBalanced
  · rw [← memLog_restrict]; exact hsat.memTableFaithful
  · rw [← mapLog_restrict]; exact hsat.mapTableFaithful

end Restrict

/-! ## §5 — MEMBERSHIP OF THE TAIL FAMILIES in the marks descriptor. -/

theorem mem_rm_resolve {n : Nat} {g : VmConstraint2} (hg : g ∈ NGen.resolveConstraints n) :
    g ∈ (automataflResolveMarksDescN n).constraints := List.mem_append_left _ hg

theorem mem_rm_tail {n : Nat} {g : VmConstraint2} (hg : g ∈ resolveMarksTail n) :
    g ∈ (automataflResolveMarksDescN n).constraints := List.mem_append_right _ hg

/-- One step from a tail family to the marks descriptor. -/
theorem mem_rm_fam {n : Nat} {g : VmConstraint2} {fam : List VmConstraint2}
    (hf : fam ∈ resolveMarksFamilies n) (hg : g ∈ fam) :
    g ∈ (automataflResolveMarksDescN n).constraints :=
  mem_rm_tail (List.mem_flatten.mpr ⟨fam, hf, hg⟩)

theorem mem_rm_marksFamily {n : Nat} {g : VmConstraint2} (hg : g ∈ rMarksFamily n) :
    g ∈ (automataflResolveMarksDescN n).constraints :=
  mem_rm_fam (by simp [resolveMarksFamilies]) hg

theorem mem_rm_destOneHot {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ rDestOneHot n w) : g ∈ (automataflResolveMarksDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_rm_fam (by simp [resolveMarksFamilies]) hg
  · exact mem_rm_fam (by simp [resolveMarksFamilies]) hg

theorem mem_rm_legality {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ rLegality n w) : g ∈ (automataflResolveMarksDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_rm_fam (by simp [resolveMarksFamilies]) hg
  · exact mem_rm_fam (by simp [resolveMarksFamilies]) hg

/-! ## §6 — THE MARKS WINDOW CARRY (the seam ingredient).

`marksPack_pi_of_mem` (M0), fed the tail's three ingredients, pins the published `marksIn` window to
the base-4 pack of the decoded `marksIn` indicator — so `C_last.OUT.marks == R.IN.marks` is a base-4
injective (hash-free) window equality, exactly as Leg C's marks seam. -/

section WindowCarry
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The `{0,1}` range gate of `marksIn` cell `idx` is emitted. -/
theorem mem_rm_marks_range (idx : Nat) (hidx : idx < n * n) :
    (.base (.gate (Dregg2.Circuit.Emit.AutomataflCommit.memberExpr (rMarksInCell n idx) [0, 1]))
      : VmConstraint2) ∈ (automataflResolveMarksDescN n).constraints :=
  mem_rm_marksFamily
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_range hidx (rMarksInCell n) (rMarksInFelt n)
      (rPiMarksIn n))

/-- The base-4 pack gate of `marksIn` felt `j` is emitted. -/
theorem mem_rm_marks_pack (j : Nat) (hj : j < feltCount n) :
    Dregg2.Circuit.Emit.AutomataflCommit.linGate
        (Dregg2.Circuit.Emit.AutomataflCommit.packTermsAt n j (rMarksInCell n) (rMarksInFelt n)) 0
      ∈ (automataflResolveMarksDescN n).constraints :=
  mem_rm_marksFamily
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_pack hj (rMarksInCell n) (rMarksInFelt n)
      (rPiMarksIn n))

/-- The `.piBinding` of `marksIn` felt `j` is emitted. -/
theorem mem_rm_marks_pi (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (rMarksInFelt n j) (rPiMarksIn n + j)) : VmConstraint2)
      ∈ (automataflResolveMarksDescN n).constraints :=
  mem_rm_marksFamily
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_pi hj (rMarksInCell n) (rMarksInFelt n)
      (rPiMarksIn n))

/-- The `marksIn` cells are indicator bits (from the emitted `{0,1}` gate). -/
theorem rm_marksAlpha_of_sat
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (idx : Nat) (hidx : idx < n * n) :
    (envAt t 0).loc (rMarksInCell n idx) = 0 ∨ (envAt t 0).loc (rMarksInCell n idx) = 1 :=
  Dregg2.Circuit.Emit.AutomataflMarks.marksAlpha_of_mem hsat hc hlen (rMarksInCell n) idx
    (mem_rm_marks_range idx hidx)

/-- **`resolveMarks_marksIn_pi_of_sat` — THE WINDOW CARRY.** The published `marksIn` window
`PI[rPiMarksIn + j]` IS (mod `p`) the `j`-th packed felt of the `marksIn` indicator decoded off the
descriptor's own cell columns. Base-4 injective, hash-free — the seam to Leg C's `marksOut`. -/
theorem resolveMarks_marksIn_pi_of_sat
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (rPiMarksIn n + j)
      ≡ packCell (marksCode (marksDecodeAt n (rMarksInCell n) (envAt t 0)) n) j [ZMOD 2013265921] :=
  Dregg2.Circuit.Emit.AutomataflMarks.marksPack_pi_of_mem hsat hlen (rMarksInCell n) (rMarksInFelt n)
    (rPiMarksIn n) j (fun i hi => rm_marksAlpha_of_sat hsat hc hlen i hi)
    (mem_rm_marks_pack j hj) (mem_rm_marks_pi j hj)

end WindowCarry

/-! ## §7 — THE BOARD HALF, REUSED (the KEY OBSERVATION exploited).

`resolveMoves` is marks-independent, so `cMidV4` is UNCHANGED by the marks carry: the board-cell
capstone is `resolve_sat_imp_roundBoardN` on the RESTRICTED resolve trace, verbatim. -/

section BoardHalf
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`resolveMarks_cMidV4_roundBoard` — the marks-descriptor board cell IS `roundStep`'s resolve
board.** `codeToParticle (cMidV4)` is `old` on a clash and the VALIDATED `resolveMoves` cell otherwise,
at accumulated marks — the SAME conclusion as `resolve_sat_imp_roundBoardN`, off the marks descriptor,
because `resolveMoves` never reads marks. -/
theorem resolveMarks_cMidV4_roundBoard
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (if clashCoords (boardDecodeOldN n (envAt t i))
            [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] ≠ []
          then boardDecodeOldN n (envAt t i)
          else resolveMoves (boardDecodeOldN n (envAt t i))
            [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ :=
  resolve_sat_imp_roundBoardN (resolveMarks_restrict hsat) hc i hi W x y hx hy

end BoardHalf

/-! ## §7b — THE MARKS-LEGALITY RE-CHECK, as a DESCRIPTOR THEOREM.

`resolveMarksMoveLegal` mirrors Leg C's `legcMoveLegal`: the source one-hots come free from the
resolve descriptor's own `validateMove`; the destination one-hots are this file's; `readAt_collapse`
collapses `inMarksFrm`/`inMarksTo` to the pinned `marksIn` cells; the `{0,1}` gate makes them bits;
`legal[w] = 1` (NOR) forces both to `0`, i.e. `frm ∉ marks ∧ to ∉ marks`. Together with the geometric
half (`validMoveN_of_sat` on the restricted trace) this is `MoveLegal … marks` EXACTLY — the marks
conjunct is now PROVEN of the descriptor, NOT assumed. -/

section Legality
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The SOURCE one-hots, from the resolve descriptor's `validateMove` (via restriction membership). -/
theorem rm_srcOneHots
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w < 2)
    (hn : (n : ℤ) < 2013265921) :
    (∃ Y : Nat, Y < n ∧ (envAt t i).loc (NGen.cFy n (NGen.mvBase n w)) = (Y : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (NGen.cSelRow n (NGen.mvBase n w) j)) n Y)
    ∧ (∃ X : Nat, X < n ∧ (envAt t i).loc (NGen.cFx n (NGen.mvBase n w)) = (X : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (NGen.cSelCol n (NGen.mvBase n w) j)) n X) := by
  refine ⟨?_, ?_⟩
  · exact oneHotN_of_sat hsat hc i hi n hn (NGen.cSelRow n (NGen.mvBase n w))
      (NGen.cFy n (NGen.mvBase n w))
      (fun j hj => mem_rm_resolve (mvLift n w hw (vm_selRow n (NGen.mvBase n w) j hj)))
      (mem_rm_resolve (mvLift n w hw (vm_srRs n (NGen.mvBase n w))))
      (mem_rm_resolve (mvLift n w hw (vm_srRi n (NGen.mvBase n w))))
  · exact oneHotN_of_sat hsat hc i hi n hn (NGen.cSelCol n (NGen.mvBase n w))
      (NGen.cFx n (NGen.mvBase n w))
      (fun j hj => mem_rm_resolve (mvLift n w hw (vm_selCol n (NGen.mvBase n w) j hj)))
      (mem_rm_resolve (mvLift n w hw (vm_srCs n (NGen.mvBase n w))))
      (mem_rm_resolve (mvLift n w hw (vm_srCi n (NGen.mvBase n w))))

/-- The DESTINATION one-hots, from this file's own `rDestOneHot` gates. -/
theorem rm_destOneHots
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1)
    (hn : (n : ℤ) < 2013265921) :
    (∃ TY : Nat, TY < n ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n w)) = (TY : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (rTSelRow n w j)) n TY)
    ∧ (∃ TX : Nat, TX < n ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n w)) = (TX : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (rTSelCol n w j)) n TX) := by
  refine ⟨?_, ?_⟩
  · exact oneHotN_of_sat hsat hc i hi n hn (rTSelRow n w) (NGen.cTy n (NGen.mvBase n w))
      (fun j hj => mem_rm_destOneHot hw (List.mem_append_left _
        (mem_oneHotAtCol_sel ((List.range n).map (rTSelRow n w)) (NGen.cTy n (NGen.mvBase n w))
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
      (mem_rm_destOneHot hw (List.mem_append_left _
        (mem_oneHotAtCol_sumHead ((List.range n).map (rTSelRow n w)) (NGen.cTy n (NGen.mvBase n w)))))
      (mem_rm_destOneHot hw (List.mem_append_left _
        (mem_oneHotAtCol_idxHead ((List.range n).map (rTSelRow n w)) (NGen.cTy n (NGen.mvBase n w)))))
  · exact oneHotN_of_sat hsat hc i hi n hn (rTSelCol n w) (NGen.cTx n (NGen.mvBase n w))
      (fun j hj => mem_rm_destOneHot hw (List.mem_append_right _
        (mem_oneHotAtCol_sel ((List.range n).map (rTSelCol n w)) (NGen.cTx n (NGen.mvBase n w))
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
      (mem_rm_destOneHot hw (List.mem_append_right _
        (mem_oneHotAtCol_sumHead ((List.range n).map (rTSelCol n w)) (NGen.cTx n (NGen.mvBase n w)))))
      (mem_rm_destOneHot hw (List.mem_append_right _
        (mem_oneHotAtCol_idxHead ((List.range n).map (rTSelCol n w)) (NGen.cTx n (NGen.mvBase n w)))))

/-- **`resolveMarksMoveLegal` — THE RE-CHECK, PROVEN.** On a satisfying canonical trace of the
marks-carrying resolve descriptor, the decoded move `which` IS `MoveLegal` against the decoded
accumulated `marksIn` list — geometry from the resolve descriptor, `frm,to ∉ marks` from THIS file's
legality gate. Nothing is assumed. -/
theorem resolveMarksMoveLegal (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1) :
    MoveLegal (boardDecodeOldN n (envAt t i)) (marksListDecode n (rMarksInCell n) (envAt t i))
      (moveDecodeN n (envAt t i) w) := by
  set e := envAt t i with he
  have hw2 : w < 2 := by rcases hw with rfl | rfl <;> norm_num
  have hvalid : MoveValid (boardDecodeOldN n e) (moveDecodeN n e w) :=
    validMoveN_of_sat (resolveMarks_restrict hsat) hc i hi w ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM
      W.rbits (mvLift n w hw2)
  obtain ⟨⟨Yw, hYlt, hfyw, hrow⟩, ⟨Xw, hXlt, hfxw, hcol⟩⟩ := rm_srcOneHots hsat hc i hi w hw2 W.lt_p
  obtain ⟨⟨TYw, hTYlt, htyw, hdrow⟩, ⟨TXw, hTXlt, htxw, hdcol⟩⟩ := rm_destOneHots hsat hc i hi w hw W.lt_p
  have hfrm : (moveDecodeN n e w).frm = (⟨Xw, Yw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [hfxw, hfyw]; simp
  have hto : (moveDecodeN n e w).to = (⟨TXw, TYw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [htxw, htyw]; simp
  have hidxF : Yw * n + Xw < n * n := by
    calc Yw * n + Xw < Yw * n + n := by omega
      _ = (Yw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidxT : TYw * n + TXw < n * n := by
    calc TYw * n + TXw < TYw * n + n := by omega
      _ = (TYw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  -- reads collapse to the marks cells
  have hrdF : e.loc (rInMarksFrm n w) = e.loc (rMarksInCell n (Yw * n + Xw)) :=
    readAt_collapse hsat hc i hi (rInMarksFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
      (NGen.cSelCol n (NGen.mvBase n w)) (rMarksInCell n) Yw Xw hrow hcol
      (mem_rm_legality hw (List.mem_cons_self))
  have hrdT : e.loc (rInMarksTo n w) = e.loc (rMarksInCell n (TYw * n + TXw)) :=
    readAt_collapse hsat hc i hi (rInMarksTo n w) (rTSelRow n w) (rTSelCol n w) (rMarksInCell n)
      TYw TXw hdrow hdcol (mem_rm_legality hw (List.mem_cons_of_mem _ (List.mem_cons_self)))
  -- marks cells are {0,1}
  have hmiF : e.loc (rMarksInCell n (Yw * n + Xw)) = 0 ∨ e.loc (rMarksInCell n (Yw * n + Xw)) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_rm_marks_range (Yw * n + Xw) hidxF)) (canon_loc hc i _)
  have hmiT : e.loc (rMarksInCell n (TYw * n + TXw)) = 0 ∨ e.loc (rMarksInCell n (TYw * n + TXw)) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_rm_marks_range (TYw * n + TXw) hidxT)) (canon_loc hc i _)
  -- legal[w] = 1
  have hlegal1 : e.loc (rLegal n w) = 1 := by
    have hgg := ngateH hsat i hi (mem_rm_legality hw (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
    have hE : (headToExpr ((Head.lin 1 (rLegal n w)).addConst (-1))).eval e.loc
        = e.loc (rLegal n w) + (-1) := by canon_head_eval [headToExpr]
    rw [hE] at hgg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hgg)
  -- the NOR gate
  have hnorEq : e.loc (rInMarksFrm n w) + e.loc (rInMarksTo n w)
      - e.loc (rInMarksFrm n w) * e.loc (rInMarksTo n w) = 0 := by
    have hgg := ngateH hsat i hi (mem_rm_legality hw (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self))))
    have hE : (headToExpr (norHead (rLegal n w) (rInMarksFrm n w) (rInMarksTo n w))).eval e.loc
        = e.loc (rLegal n w) + (-1) + e.loc (rInMarksFrm n w) + e.loc (rInMarksTo n w)
          + (-1) * (e.loc (rInMarksFrm n w) * e.loc (rInMarksTo n w)) := by
      rw [headToExpr_eval]
      simp only [norHead, evalH_addProd, evalH_addLin, evalH_addConst, evalH_lin, varsVal,
        List.foldl_cons, List.foldl_nil]
      ring
    rw [hE, hlegal1] at hgg
    have haF : e.loc (rInMarksFrm n w) = 0 ∨ e.loc (rInMarksFrm n w) = 1 := by rw [hrdF]; exact hmiF
    have hbT : e.loc (rInMarksTo n w) = 0 ∨ e.loc (rInMarksTo n w) = 1 := by rw [hrdT]; exact hmiT
    have hmod : e.loc (rInMarksFrm n w) + e.loc (rInMarksTo n w)
        - e.loc (rInMarksFrm n w) * e.loc (rInMarksTo n w) ≡ 0 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hgg
    refine eq_of_modEq_canon ?_ canon_zero hmod
    rcases haF with h | h <;> rcases hbT with h' | h' <;> rw [h, h'] <;> exact ⟨by norm_num, by norm_num⟩
  have haF : e.loc (rInMarksFrm n w) = 0 ∨ e.loc (rInMarksFrm n w) = 1 := by rw [hrdF]; exact hmiF
  have hbT : e.loc (rInMarksTo n w) = 0 ∨ e.loc (rInMarksTo n w) = 1 := by rw [hrdT]; exact hmiT
  have hab : e.loc (rInMarksFrm n w) = 0 ∧ e.loc (rInMarksTo n w) = 0 := by
    rcases haF with h | h <;> rcases hbT with h' | h' <;> rw [h, h'] at hnorEq <;>
      first | exact ⟨h, h'⟩ | (exfalso; norm_num at hnorEq)
  have hmarksInF : e.loc (rMarksInCell n (Yw * n + Xw)) = 0 := by rw [← hrdF]; exact hab.1
  have hmarksInT : e.loc (rMarksInCell n (TYw * n + TXw)) = 0 := by rw [← hrdT]; exact hab.2
  have hfrmNotMem : (⟨Xw, Yw⟩ : Coord) ∉ marksListDecode n (rMarksInCell n) e := by
    intro hmem
    rw [mem_marksListDecode_iff] at hmem
    rw [hmarksInF] at hmem
    exact absurd hmem.2.2 (by norm_num)
  have htoNotMem : (⟨TXw, TYw⟩ : Coord) ∉ marksListDecode n (rMarksInCell n) e := by
    intro hmem
    rw [mem_marksListDecode_iff] at hmem
    rw [hmarksInT] at hmem
    exact absurd hmem.2.2 (by norm_num)
  obtain ⟨hne, hrook, hibF, hibT, hautoF, -, -, -⟩ := hvalid
  exact ⟨hne, hrook, hibF, hibT, hautoF, by rw [hfrm]; exact hfrmNotMem,
    by rw [hto]; exact htoNotMem⟩

end Legality

/-! ## §7c — CONSUMING THE ACCUMULATED ROUNDSTATE.

The clean round's decoded RoundState (`rmRoundStateIn`) has `marks = marksListDecode …` (the
accumulated marks from the prior Leg C rounds), `locked = []` and `waiting = seats` — the P = 2
landing (a pair clash re-enters BOTH seats, so the clean round's moves are BOTH fresh and the locked
list is empty; M1/M2, `LEGC_SEATS = 2`). The fresh filter keeps both moves because each is marks-legal
(`resolveMarksMoveLegal`, PROVEN — not assumed) and claims seat `0` (`moveDecodeN`'s hard-coded `who`),
which the generic-`seats` lemmas below carry as `hseat0 : seats.contains 0 = true`.

⚑ `hseat0` IS NOT DEBT. At the DEPLOYED goal assignment it is a THEOREM, not a hypothesis:
`AutomataflRules.stockGoals2_seats` proves `(stockGoals2 size).seats = [0, 1]` by `rfl` at EVERY
size, so `stockGoals2_seats_contains_zero` discharges it. The stock-instance capstone
(`turn_sat_imp_roundStepMarks_pi_stock`, §7d) carries NO `hseat0`. The generic-`seats` form is kept
because it is the more general statement, not because anything is owed. -/

section RoundState
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The RoundState the clean round consumes: the decoded board, the ACCUMULATED marks, `locked = []`,
`waiting = seats`. -/
def rmRoundStateIn (n : Nat) (e : VmRowEnv) (seats : List Pid) : RoundState :=
  { board   := boardDecodeOldN n e
  , marks   := marksListDecode n (rMarksInCell n) e
  , locked  := []
  , waiting := seats }

/-- **THE REFERENCE REDUCTION (generalized off `openRound`).** `roundStep_pair_outcomeBoard` with the
opening round `openRound b seats` (marks = [], locked = []) generalized to an ARBITRARY RoundState with
`locked = []` (the P = 2 clean round consumes an accumulated `marks ≠ []`). Same proof shape. -/
theorem roundStep_marks_outcomeBoard (cfg : GameConfig) (g : GoalAssignment) (rs : RoundState)
    (ma mb : Move) (hlocked : rs.locked = [])
    (hfresh : ([ma, mb].filter (fun m => rs.waiting.contains m.who && moveLegalB rs.board rs.marks m))
        = [ma, mb])
    (hres : resolvableB rs.board [ma, mb] = true) :
    outcomeBoard (roundStep cfg g rs [ma, mb]) =
      (if clashCoords rs.board [ma, mb] = []
       then automatonStepCfg cfg (resolveMoves rs.board [ma, mb]) else rs.board) := by
  have hunres : unresolved rs.board [ma, mb] = [] := List.isEmpty_iff.mp hres
  unfold roundStep outcomeBoard
  simp only [hlocked, List.nil_append, hfresh]
  by_cases hcl : clashCoords rs.board [ma, mb] = []
  · rw [if_pos hcl]
    simp only [hcl, List.isEmpty_nil, if_true, hunres]
  · rw [if_neg hcl]
    have hne : (clashCoords rs.board [ma, mb]).isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff]; exact hcl
    simp only [hne, Bool.false_eq_true, if_false]

/-- **The fresh filter keeps both moves** — `hfresh` DISCHARGED from the descriptor. Each move is
marks-legal (`resolveMarksMoveLegal`) and claims seat `0`, which the seat list must hold (`hseat0`;
DISCHARGED at the deployed `stockGoals2` by `stockGoals2_seats_contains_zero`), so the `roundStep`
fresh filter admits both. -/
theorem rm_fresh_keeps_both (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (seats : List Pid)
    (hseat0 : seats.contains 0 = true) :
    ([moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1].filter
        (fun m => seats.contains m.who
          && moveLegalB (boardDecodeOldN n (envAt t 0)) (marksListDecode n (rMarksInCell n) (envAt t 0)) m))
      = [moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1] := by
  rw [List.filter_eq_self]
  intro m hm
  have hleg : ∀ w : Nat, w = 0 ∨ w = 1 →
      moveLegalB (boardDecodeOldN n (envAt t 0)) (marksListDecode n (rMarksInCell n) (envAt t 0))
        (moveDecodeN n (envAt t 0) w) = true := by
    intro w hw; rw [moveLegalB_iff]; exact resolveMarksMoveLegal W hsat hc 0 (by omega) w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have hwho : ∀ w : Nat, (moveDecodeN n (envAt t 0) w).who = 0 := fun _ => rfl
  rcases hm with rfl | rfl
  · simp only [hwho, hseat0, hleg 0 (Or.inl rfl), Bool.and_self]
  · simp only [hwho, hseat0, hleg 1 (Or.inr rfl), Bool.and_self]

/-- **`resolve_sat_imp_roundBoardMarksN` — THE M6 BOARD CAPSTONE.** Off the marks-carrying resolve
descriptor at ACCUMULATED marks, the decoded `cMidV4` cell IS the board `roundStep`'s clean round
resolves — `resolveMoves rs.board [mv0, mv1]` (the PRE-automaton board; `roundStep` steps the
automaton AFTER, a separate leg). The board half is `resolveMarks_cMidV4_roundBoard` (marks
independent); the clash branch is eliminated by `hclean`. -/
theorem resolve_sat_imp_roundBoardMarksN (W : MovesWindow n)
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hclean : clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] = [])
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (resolveMoves (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  rw [resolveMarks_cMidV4_roundBoard hsat hc i hi W x y hx hy, if_neg (fun h => h hclean)]

/-- **`rmRoundStep_marks_outcomeBoard` — THE REFERENCE REDUCTION (marks form).** On the clean round of
the accumulated RoundState, `roundStep`'s outcome board is `automatonStepCfg cfg (resolveMoves
rs.board [mv0, mv1])` — the automaton step applied to the resolved board. `hfresh` is DISCHARGED
(`rm_fresh_keeps_both`); only `hres` (resolvability) and `hclean` remain. This is the reference side
Phase D composes with Leg A. -/
theorem rmRoundStep_marks_outcomeBoard (W : BoardWindow n) (g : GoalAssignment) (seats : List Pid)
    (hsat : Satisfied2 hash (automataflResolveMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (hseat0 : seats.contains 0 = true)
    (hclean : clashCoords (boardDecodeOldN n (envAt t 0))
        [moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN n (envAt t 0))
        [moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1] = true) :
    outcomeBoard (roundStep ⟨.column⟩ g (rmRoundStateIn n (envAt t 0) seats)
        [moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1])
      = automatonStepCfg ⟨.column⟩ (resolveMoves (boardDecodeOldN n (envAt t 0))
          [moveDecodeN n (envAt t 0) 0, moveDecodeN n (envAt t 0) 1]) := by
  have hstep := roundStep_marks_outcomeBoard ⟨.column⟩ g (rmRoundStateIn n (envAt t 0) seats)
    (moveDecodeN n (envAt t 0) 0) (moveDecodeN n (envAt t 0) 1) rfl
    (rm_fresh_keeps_both W hsat hc hlen seats hseat0) hres
  rw [hstep]
  simp only [rmRoundStateIn]
  exact if_pos hclean

/-- The board capstone at the deployed `n = 11`. -/
theorem resolve_sat_imp_roundBoardMarks11
    (hsat : Satisfied2 hash (automataflResolveMarksDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt t i))
        [moveDecodeN 11 (envAt t i) 0, moveDecodeN 11 (envAt t i) 1] = [])
    (x y : Nat) (hx : x < 11) (hy : y < 11) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 11 (y * 11 + x)))
      = (resolveMoves (boardDecodeOldN 11 (envAt t i))
          [moveDecodeN 11 (envAt t i) 0, moveDecodeN 11 (envAt t i) 1]).cellAt ⟨x, y⟩ :=
  resolve_sat_imp_roundBoardMarksN movesWindow_eleven hsat hc i hi hclean x y hx hy

/-- The board capstone at `n = 2` (the minimal instance). -/
theorem resolve_sat_imp_roundBoardMarks2
    (hsat : Satisfied2 hash (automataflResolveMarksDescN 2) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hclean : clashCoords (boardDecodeOldN 2 (envAt t i))
        [moveDecodeN 2 (envAt t i) 0, moveDecodeN 2 (envAt t i) 1] = [])
    (x y : Nat) (hx : x < 2) (hy : y < 2) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 2 (y * 2 + x)))
      = (resolveMoves (boardDecodeOldN 2 (envAt t i))
          [moveDecodeN 2 (envAt t i) 0, moveDecodeN 2 (envAt t i) 1]).cellAt ⟨x, y⟩ :=
  resolve_sat_imp_roundBoardMarksN movesWindow_two hsat hc i hi hclean x y hx hy

end RoundState

/-! ## §7d — THE WHOLE-TURN CAPSTONE, GENERALIZED OFF `marks = []` (M6).

`turn_sat_imp_roundStepMarks_pi` is `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` for the CLEAN
round of a MULTI-round turn: the resolve leg is the marks-carrying descriptor, and the round consumes
the ACCUMULATED `RoundState` (`rmRoundStateIn`, `marks ≠ []`). The `hfresh` HYPOTHESIS of the old
capstone is GONE — the marks-legality is DISCHARGED from the descriptor (`resolveMarksMoveLegal`), so
in the GENERIC-`seats` statement only the who-routing `hseat0 : seats.contains 0` is left standing.
**At the deployed game it is not left standing either**: `turn_sat_imp_roundStepMarks_pi_stock` fixes
`g := stockGoals2 11` and `seats := (stockGoals2 11).seats` — the stock two-player 11×11 game that
`dregg-automatafl/src/reference.rs::{stock_two_player, GOAL_CORNERS_2P}` deploys — and discharges
`hseat0` by `stockGoals2_seats_contains_zero`, so the deployed capstone is UNCONDITIONAL in the seats.
The seam is still the fold's PI equalities; the resolve-side ingredients ride the restricted resolve
trace, and the appended marks window (`PI[R_PI_COUNT …)`) sits ABOVE the mid/auto seam slots, so it
does not disturb them. -/

section TurnMarks
open Dregg2.Circuit.Emit.AutomataflStepEmit (automataflStepDescN)

variable {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
variable {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}

/-- Both moves are `moveLegalB` against the EMPTY marks (geometry from `resolveMarksMoveLegal`, and
`∉ []` trivially) — what the base capstone's `hfresh` needs. -/
theorem rm_moveLegal_empty
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1) :
    moveLegalB (boardDecodeOldN 11 (envAt tR 0)) [] (moveDecodeN 11 (envAt tR 0) w) = true := by
  rw [moveLegalB_iff]
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ :=
    resolveMarksMoveLegal movesWindow_eleven.base hsatR hcR 0 (by omega) w hw
  exact ⟨h1, h2, h3, h4, h5, by simp, by simp⟩

/-- **`turn_sat_imp_roundStepMarks_pi` — THE M6 WHOLE-TURN CAPSTONE.** The decoded NEW board IS the
board `AutomataflRules.roundStep` produces for the CLEAN round consuming the ACCUMULATED RoundState
(`rmRoundStateIn`, `marks ≠ []`) — cell-wise, off ONLY the fold's PI equalities and `hseat0`. No
`hfresh`. (`hseat0` is the price of the ARBITRARY seat list; see
`turn_sat_imp_roundStepMarks_pi_stock` for the deployed instance, where it is discharged.) -/
theorem turn_sat_imp_roundStepMarks_pi (g : GoalAssignment) (seats : List Pid)
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
    (hseamAutoX : tR.pub (NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1)) :
    ∀ x y : Nat, x < 11 → y < 11 →
      codeToParticle ((envAt tA 0).loc
          (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
        = (outcomeBoard (roundStep ⟨.column⟩ g (rmRoundStateIn 11 (envAt tR 0) seats)
              [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])).cellAt ⟨x, y⟩ := by
  -- `hfresh` at `marks = []`, derived from the descriptor (geometry + `∉ []`).
  have hfreshEmpty : ([moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1].filter
      (fun m => seats.contains m.who
        && moveLegalB (boardDecodeOldN 11 (envAt tR 0)) [] m))
      = [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] := by
    rw [List.filter_eq_self]
    intro m hm
    have hwho : ∀ w : Nat, (moveDecodeN 11 (envAt tR 0) w).who = 0 := fun _ => rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · simp only [hwho, hseat0, rm_moveLegal_empty hsatR hcR hlenR 0 (Or.inl rfl), Bool.and_self]
    · simp only [hwho, hseat0, rm_moveLegal_empty hsatR hcR hlenR 1 (Or.inr rfl), Bool.and_self]
  -- the existing whole-turn capstone at `marks = []`, on the RESTRICTED resolve trace.
  have hbase := turn_sat_imp_roundStep_pi g seats (resolveMarks_restrict hsatR) hcR hlenR hsatA hcA
    hlenA hclean hfreshEmpty hres hseamPack hseamAutoX hseamAutoY
  -- both outcome boards (openRound and rmRoundStateIn) reduce to the same automaton∘resolve board.
  have hopen := roundStep_pair_outcomeBoard ⟨.column⟩ g (boardDecodeOldN 11 (envAt tR 0)) seats
    (moveDecodeN 11 (envAt tR 0) 0) (moveDecodeN 11 (envAt tR 0) 1) hfreshEmpty hres
  rw [if_pos hclean] at hopen
  have hmarks := rmRoundStep_marks_outcomeBoard movesWindow_eleven.base g seats hsatR hcR hlenR
    hseat0 hclean hres
  intro x y hx hy
  rw [hbase x y hx hy, hopen, ← hmarks]

/-- **`turn_sat_imp_roundStepMarks_pi_stock` — THE M6 WHOLE-TURN CAPSTONE AT THE DEPLOYED GAME.**

The same conclusion as `turn_sat_imp_roundStepMarks_pi`, with the goal assignment and the seat list
fixed to **the stock two-player 11×11 game that is actually deployed** — `stockGoals2 11` is
`dregg-automatafl/src/reference.rs::GOAL_CORNERS_2P` corner for corner, and its seat list is
`[0, 1]` — and with **NO `hseat0` hypothesis**: who is seated is `stockGoals2_seats_contains_zero`,
a `rfl`-theorem about the deployed assignment. P = 2 is not a restriction being carried here; P = 2
IS the game. Every hypothesis that remains is about the TRACES (satisfaction, canonicity, the PI
seam, this round being clean and resolvable) — none about the ruleset. -/
theorem turn_sat_imp_roundStepMarks_pi_stock
    (hsatR : Satisfied2 hashR (automataflResolveMarksDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA (automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true)
    (hseamPack : ∀ j, j < feltCount 11 → tR.pub (16 + feltCount 11 + j) = tA.pub (16 + j))
    (hseamAutoX : tR.pub (NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1)) :
    ∀ x y : Nat, x < 11 → y < 11 →
      codeToParticle ((envAt tA 0).loc
          (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
        = (outcomeBoard (roundStep ⟨.column⟩ (stockGoals2 11)
              (rmRoundStateIn 11 (envAt tR 0) (stockGoals2 11).seats)
              [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])).cellAt ⟨x, y⟩ :=
  turn_sat_imp_roundStepMarks_pi (stockGoals2 11) (stockGoals2 11).seats hsatR hcR hlenR hsatA hcA
    hlenA (stockGoals2_seats_contains_zero 11) hclean hres hseamPack hseamAutoX hseamAutoY

end TurnMarks

/-! ## §8 — SHAPE CANARIES. -/

#guard (automataflResolveMarksDescN 11).name == "dregg-automatafl-resolve-marks-n11"
#guard (automataflResolveMarksDescN 11).tables.length == 0
#guard (automataflResolveMarksDescN 11).hashSites.length == 0
#guard (automataflResolveMarksDescN 11).ranges.length == 0
#guard feltCount 11 == 9
#guard marksWindowLanes 11 == 9

/-! ## §9 — Axiom hygiene. -/

#assert_axioms tail_all_base
#assert_axioms tail_memfree
#assert_axioms tail_mapfree
#assert_axioms memOpsOf_restrict
#assert_axioms resolveMarks_restrict
#assert_axioms resolveMarks_marksIn_pi_of_sat
#assert_axioms resolveMarks_cMidV4_roundBoard
#assert_axioms rm_srcOneHots
#assert_axioms rm_destOneHots
#assert_axioms resolveMarksMoveLegal
#assert_axioms roundStep_marks_outcomeBoard
#assert_axioms rm_fresh_keeps_both
#assert_axioms resolve_sat_imp_roundBoardMarksN
#assert_axioms resolve_sat_imp_roundBoardMarks11
#assert_axioms resolve_sat_imp_roundBoardMarks2
#assert_axioms rmRoundStep_marks_outcomeBoard
#assert_axioms rm_moveLegal_empty
#assert_axioms turn_sat_imp_roundStepMarks_pi
#assert_axioms turn_sat_imp_roundStepMarks_pi_stock

end Dregg2.Circuit.Emit.AutomataflResolveMarksCapstone
