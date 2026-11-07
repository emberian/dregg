/-
# Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone — LEG R'S CAPSTONE AGAINST THE VALIDATED GAME.

The OLD capstone (`AutomataflResolveCapstone.resolve_sat_imp_resolveMid`) closes only at `NN = 2` and
against the OLD `Automatafl.resolveMid`, and §6 of that file documents WHY it is not restatable at
`n ≥ 3`: the OLD descriptor and the FIXED reference disagree on the OCCLUDED-STAYER class (defect #8).

This file is the CHUNK-4 landing that closes the DIRECT half of that wound IN THE CIRCUIT (the
occluded STAYER — a piece whose own move is blocked keeps its cell). The chunk-1/chunk-3 emitter grew
the corrected columns:

  * `cOccIncl` — the INCLUSIVE occlusion (destination endpoint included), which chunk 2
    (`AutomataflOcclusionBridgeN.occ_iff_blocked_of_sat`) proved equals the VALIDATED-game predicate
    `AutomataflRules.blockedB`.
  * `cCarryV2 i = surv · nz_i · (1 − occIncl_i) · (1 − nonLeave_i)` — the corrected carry, which now
    KEEPS the stayer: an occluded piece has `occIncl = 1`, so `cCarryV2 = 0`, so the emitted board
    rewrite no longer overwrites it.
  * `cNonLeave i`, `cResolvable`, `cWBoardV2`, `cMidV2` — the non-leaver bit, the resolvable surface,
    and the `cResolvable`-gated corrected board.

This file consumes those columns off `Satisfied2 (automataflResolveDescN n)`. It is downstream of the
bridge and of the OLD capstone, and is strictly ADDITIVE — it touches neither the OLD capstone nor the
chunk-1/2/3 emit/bridge objects.

The full `resolve_sat_imp_resolveMovesN` capstone is NOT assembled here: §7 exhibits a SECOND wound,
disjoint from defect #8, that makes the unconditional statement FALSE at `n ≥ 3` against this
descriptor. The DIRECT carry was corrected to inclusive occlusion (`cCarryV2` reads `cOccIncl =
blockedB`), but the FLOW-THROUGH bit `cFtA`/`cFtB` — and the `cBadA`/`cBadB`/`cResolvable` surface it
gates — still ride the EXCLUSIVE `cOcc = occluded`, so a piece riding into a downstream edge that is
inclusive-blocked (a non-mover sits on the downstream destination) is mishandled and the round is
wrongly declared unresolvable. `flowThroughOcclusionGap_witness_n3` is the executable falsifier.
Assembling the capstone is chunk 5's obligation and requires re-emitting the flow-through / resolvable
columns onto `cOccIncl` first.

## Axiom hygiene
`#assert_axioms` subset `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.AutomataflResolveCapstone
import Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN

namespace Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflResolveRefine
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow mvLift occLift)
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid occluded)

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## §1 — the board-size window for the chunk-4 landing.

A superset of the OLD `BoardWindow`: it adds the INCLUSIVE occlusion masked-sum bound `3n + 3 ≤ 999`
that `occ_iff_blocked_of_sat` needs (the exclusive `occluded` used `3n ≤ 999`; the inclusive
`blockedB` adds the destination line felt). Every field is EXPLICIT board arithmetic — decidable at a
concrete `n`, holding at `n = 2`, `n = 3`, `n = 11`. NON-VACUOUS at `n = 3` (a 3-line has an interior
cell, and a piece ON the destination now fires `blockedB`, which the exclusive `occluded` misses). -/
structure MovesWindow (n : Nat) : Prop where
  /-- The full OLD board window (drives `validMoveN_of_sat`, the coordinate decode, the exclusive
  occlusion bridge, and the pattern/selection extractions). -/
  base   : BoardWindow n
  /-- The INCLUSIVE occlusion masked-sum window (`3n + 3 ≤ 999`). -/
  msumI  : 3 * (n : ℤ) + 3 ≤ 999

theorem movesWindow_two : MovesWindow 2 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_two, by norm_num⟩
theorem movesWindow_three : MovesWindow 3 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_three, by norm_num⟩
theorem movesWindow_eleven : MovesWindow 11 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_eleven, by norm_num⟩

/-! ## §2 — `blockedV2N_of_sat`: the emitted INCLUSIVE occlusion column IS the VALIDATED-game
`AutomataflRules.blockedB`.

This wires chunk 2 (`occ_iff_blocked_of_sat`) through the membership navigators and the reference
`MoveValid` (from `validMoveN_of_sat`), off nothing but `Satisfied2 (automataflResolveDescN n)` and
the board window — no `resolvableB` hypothesis. It is the occlusion half of the defect-#8 closure:
the corrected carry reads THIS column, so the circuit's "is my move blocked" question is answered by
exactly the validated game's `blockedB`. -/
section Blocked
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The two board decodes (this-file's re-export of `ResolveRefine`'s, and `OcclusionBridgeN`'s) are
the SAME structure literal, so `MoveValid` transports along `rfl`. -/
theorem bdMove_eq (which : Nat) (e : VmRowEnv) :
    MoveValid (boardDecodeOldN n e) (moveDecodeN n e which)
      ↔ MoveValid (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.boardDecodeOldN n e)
          (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.moveDecodeN n e which) := Iff.rfl

/-- **`blockedV2N_of_sat`.** `cOccIncl[which] = 1` iff the VALIDATED-game `blockedB` of the decoded
board / two decoded moves / decoded move `which` is `true`. UNCONDITIONAL (only the window). -/
theorem blockedV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (which : Nat) (hw : which < 2) :
    (envAt t i).loc (NGen.cOccIncl n which) = 1
      ↔ Dregg2.Games.AutomataflRules.blockedB (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) which, moveDecodeN n (envAt t i) (1 - which)]
          (moveDecodeN n (envAt t i) which) = true := by
  have hvalid : Dregg2.Games.Automatafl.MoveValid
      (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.boardDecodeOldN n (envAt t i))
      (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.moveDecodeN n (envAt t i) which) :=
    (bdMove_eq which (envAt t i)).mp
      (validMoveN_of_sat hsat hc i hi which ((n : ℤ) - 1) W.base.pos W.base.lt_p rfl W.base.sqM
        W.base.rbits (mvLift n which hw))
  have h := Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.occ_iff_blocked_of_sat n which
    W.base.lt_p W.base.sq511 W.msumI hsat hc i hi (occLift n which hw)
    (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.inclLiftN n which (NGen.occBase n which) hw rfl)
    (mvLift n which hw) (mvLift n (1 - which) (by omega)) hvalid
  exact h

end Blocked

/-! ## §3 — `cv2Lift`: the membership navigator into the corrected-carry staging block.

The chunk-3 `cCv1 = surv·nz` / `cCv2 = cCv1·(1−occIncl)` columns are LIVE — §11's `cv2ValN_of_sat` /
`carryV3ArithN_of_sat` read them, and the whole V3/V4 surface rides `cCv2`. This navigator is what
those extractions use to reach the block's gates.

The chunk-3 EXTRACTION TWINS that once lived here (`carryV2ArithN_of_sat`, §4
`nonLeaveGateN_of_sat`, §5 `midV2CellN_of_sat`, §6 `writeCellV2N_of_sat`, and the §12/§13 chunk-5
twins `midV3CellN_of_sat`/`writeCellV3N_of_sat`) were DELETED: the live capstone chain runs
§19's V4 extraction into `resolve_sat_imp_roundBoardN`, and nothing consumed the superseded V2/V3
board twins. The `cCarryV2` / `cNonLeave` columns they read are still emitted (they feed `cCv2` and
the V4 surface); the `cWBoardV2`/`cMidV2`/`cWBoardV3`/`cMidV3` columns they read are not. -/
section CarryV2
variable {n : Nat}

/-- Membership lift into `carryV2One n which` at either piece index. -/
theorem cv2Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.carryV2One n which) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_carryV2
  rw [NGen.carryV2Constraints]
  interval_cases which
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h
end CarryV2

/-! ## §7 — THE FLOW-THROUGH OCCLUSION GAP: why `resolve_sat_imp_resolveMovesN` is NOT assembled
here, and which descriptor column is STILL WRONG. (A SECOND wound, disjoint from defect #8.)

Chunk 4 corrected the DIRECT carry: `cCarryV2 = surv · nz · (1 − cOccIncl) · (1 − cNonLeave)` reads
the INCLUSIVE occlusion `cOccIncl = blockedB` (§2), so an occluded piece that STAYS is now kept — the
defect-#8 occluded-stayer (`AutomataflResolveCapstone.occludedStayer_witness_n3`) resolves correctly.

But the CONFLUENCE / FLOW-THROUGH surface was NOT switched to inclusive occlusion. The descriptor's
flow-through bit `cFtA`/`cFtB` (`resolveFactsN_of_sat.ftAIff`/`ftBIff`) rides the EXCLUSIVE `occluded`
of the OTHER piece — `occluded bd [sa, sb] mb = false` — to decide whether A rides through B's vacated
source and continues along B's edge. `occluded` is INTERIOR-ONLY; the reference `landMap` uses
`blockedB` = `pathCells = interior ++ [dst]`, DESTINATION INCLUDED. They disagree exactly when the
downstream piece's move is clear through its interior but its DESTINATION holds a non-mover.

THE CLASS (n ≥ 3, `flowThroughOcclusionGap_witness_n3`).  A on `sa` wants `da = sb`, B's EMPTY source;
B nominally moves `sb → db` with `db` held by a non-mover `C`.  Then:

  * `blockedB bd [ma,mb] mb = true` (C on B's destination) but `occluded bd [sa,sb] mb = false`
    (B's interior is clear) — the exclusive/inclusive gap.
  * The REFERENCE: B's edge is blocked, so A's walk dead-ends on the emptied waypoint `sb`, and
    `landMap sa = da = sb`; the round is `resolvableB` and A moves `sa → sb`.
  * The DESCRIPTOR: `ftAIff` fires (`da = sb`, `bnz = 0`, `surv = 1`, `¬occluded_b`, `db ≠ sa`), so the
    ft-selected destination of A is `db` — the WRONG landing (it flows A through a blocked edge).
    `cLandNz 0 = 1` (`db` occupied) and `cCarryB = 0` (`sb` vacuum ⇒ `bnz = 0`) force `cNonLeave 0 = 1`
    (§4), hence `cBadA = cCarryA · cNonLeave 0 = 1`, hence `cResolvable = 0` (`resolvableConstraints`).
    So `cMidV2 = cResolvable · cWBoardV2 + (1 − cResolvable) · old = old` — the circuit declares the
    round UNRESOLVABLE and falls back to the IDENTITY board, while the reference moves A.

So `codeToParticle (cMidV2 …) = (resolveMoves …).cellAt …` is FALSE at `sa` for this witness: LHS
`= attractor` (A kept), RHS `= vacuum` (A vacated). The unconditional capstone is therefore NOT
provable at `n ≥ 3` (hence not at `n = 11`) against THIS descriptor — not for want of assembly, but
because `cFtA`/`cFtB` (and the `cBadA`/`cBadB`/`cResolvable` surface they gate) must be re-emitted to
ride the INCLUSIVE `cOccIncl = blockedB`, not the exclusive `cOcc = occluded`. That re-emit is chunk
5's obligation; the witness below is its executable falsifier — `decide`d entirely on the reference
semantics and the exact `ftAIff` antecedent, so it goes red the moment the fixed descriptor makes the
flow-through respect the blocked downstream destination. -/

section FlowThroughGap
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A at `(2,0)` (attractor) wants `(1,0)` — B's EMPTY source and A's own dead-end
waypoint. B at `(1,0)` (vacuum source) nominally moves to `(0,0)`, held by a non-mover repulsor `C`.
A's onward edge through `(1,0)` into `(0,0)` is INCLUSIVE-blocked (`C` on B's destination) but
EXCLUSIVE-clear (B's interior is empty). The automaton sits at `(2,2)`, off both moves. -/
def ftBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨2, 0⟩, Particle.attractor), (⟨0, 0⟩, Particle.repulsor)] ⟨2, 2⟩
def ftMA : Move := Move.mk 0 ⟨2, 0⟩ ⟨1, 0⟩
def ftMB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE FLOW-THROUGH GAP IS NOT EMPTY, AT `n = 3`.** Both moves are legal with distinct sources and
distinct raw destinations. B's move is INCLUSIVE-blocked yet EXCLUSIVE-clear (the gap), and the exact
`cFtA` antecedent (`ftAIff`) holds — `da = sb`, `carAt sb = false` (`bnz = 0`), `¬occluded_b`,
`db ≠ sa` — with `db` occupied by a non-mover, so the descriptor sets `cLandNz 0 = 1 ⇒ cBadA = 1 ⇒
cResolvable = 0` and emits the IDENTITY board. The REFERENCE instead resolves cleanly
(`resolvableB = true`) and lands A on the emptied waypoint (`landMap sa = da`, `resolveMoves` moves
A off `sa`). Every clause `decide`d on the reference semantics. -/
theorem flowThroughOcclusionGap_witness_n3 :
    MoveValid ftBoard ftMA ∧ MoveValid ftBoard ftMB
      ∧ ftMA.frm ≠ ftMB.frm ∧ ftMA.to ≠ ftMB.to
      ∧ ftMA.frm ≠ ftMA.to ∧ ftMB.frm ≠ ftMB.to
      -- THE GAP: B's move is inclusive-blocked but exclusive-clear.
      ∧ blockedB ftBoard [ftMA, ftMB] ftMB = true
      ∧ occluded ftBoard [ftMA.frm, ftMB.frm] ftMB = false
      -- the exact `ftAIff` antecedent, so the descriptor's flow-through FIRES and points A at `db`:
      ∧ ftMA.to = ftMB.frm
      ∧ carAt ftBoard ftMB.frm = false
      ∧ ftMB.to ≠ ftMA.frm
      -- the ft-selected landing `db` is occupied by a non-mover, firing `cLandNz`/`cBadA`:
      ∧ carAt ftBoard ftMB.to = true
      ∧ carAt ftBoard ftMA.frm = true
      -- yet the REFERENCE resolves cleanly and MOVES A onto the emptied waypoint:
      ∧ resolvableB ftBoard [ftMA, ftMB] = true
      ∧ landMap ftBoard [ftMA, ftMB] ftMA.frm = ftMA.to
      ∧ (resolveMoves ftBoard [ftMA, ftMB]).cellAt ftMA.frm = Particle.vacuum
      ∧ (resolveMoves ftBoard [ftMA, ftMB]).cellAt ftMA.to = Particle.attractor
      ∧ ftBoard.cellAt ftMA.frm = Particle.attractor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end FlowThroughGap

/-! ## §9 — `ftV2{A,B}N_of_sat`: the CORRECTED FLOW-THROUGH bit reads INCLUSIVE occlusion.

This is the SECOND WOUND's fix, extracted off `Satisfied2` at arbitrary `n`. The chunk-5 emitter's
`cFtV2A = eqAb · ¬bnz · surv · ¬occIncl_b · ¬eqBa` is the OLD five-conjunct `cFtA` with the OTHER
piece's block read as the INCLUSIVE `cOccIncl` (`= blockedB`, via §2) instead of the exclusive `cOcc`
(`= occluded`). The gate SHAPE is identical to the OLD flow-through chain, so Leg 6's `ftN_of_sat`
(fully column-parametric) applies verbatim — only the occlusion NOT-bit column changes from `cNOccb`
to `cNOccIb`. The conclusion's occlusion conjunct is the emitted `cOccIncl` column, which
`blockedV2N_of_sat` (§2) has already pinned to the VALIDATED-game `blockedB` — so on the
`flowThroughOcclusionGap` class (B interior-clear but destination inclusive-blocked) the corrected
`cFtV2A` fires iff `blockedB … mb = false`, where the OLD `cFtA` fired on `occluded … mb = false`. -/
section FtV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into the CHUNK-5 corrected flow-through family. -/
theorem ftV2Lift {g : VmConstraint2} (h : g ∈ NGen.flowThroughV2Constraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_flowThroughV2 h

/-- Membership lift into the OLD flow-through family (source of the shared `cNBnz`/`cNAnz`/`cNEqba`/
`cNEqab` NOT-bits the corrected chain reuses). -/
theorem ftLift {g : VmConstraint2} (h : g ∈ NGen.flowThroughConstraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_flowThrough h

/-- **`ftV2AN_of_sat`.** The corrected A-side flow-through bit is `1` iff A's dest is B's source, B's
source is vacuum (`bnz = 0`), the round survives, B's move is NOT inclusive-blocked (`cOccIncl 1 = 0`)
and B does not point back at A (`eqBa = 0`). Every conjunct is a column already known boolean; the
occlusion conjunct is the INCLUSIVE `cOccIncl 1` (`= blockedB … mb`, §2), not the exclusive `cOcc`. -/
theorem ftV2AN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtV2A n) = 0 ∨ (envAt t i).loc (NGen.cFtV2A n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtV2A n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cOccIncl n 1) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNBnz n) (NGen.cNOccIb n) (NGen.cNEqba n) (NGen.cFtV2a1 n)
    (NGen.cFtV2a2 n) (NGen.cFtV2a3 n) (NGen.cFtV2A n) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cBnz n)
    (NGen.cOccIncl n 1) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cSurv n)
    (ftLift (by rw [NGen.flowThroughConstraints]; exact List.mem_cons_self))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_self))
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    hab hbnz hocc hba hsurv

/-- **`ftV2BN_of_sat`.** The corrected B-side flow-through bit — the mirror, reading `cOccIncl 0`
(`= blockedB … ma`). -/
theorem ftV2BN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtV2B n) = 0 ∨ (envAt t i).loc (NGen.cFtV2B n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtV2B n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ∧ (envAt t i).loc (NGen.cAnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cOccIncl n 0) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNAnz n) (NGen.cNOccIa n) (NGen.cNEqab n) (NGen.cFtV2b1 n)
    (NGen.cFtV2b2 n) (NGen.cFtV2b3 n) (NGen.cFtV2B n) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cAnz n)
    (NGen.cOccIncl n 0) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cSurv n)
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
    hba hanz hocc hab hsurv

end FtV2

/-! ## §10 — `nonLeaveV2GateN_of_sat`: the CORRECTED non-leaver bit is `landNzV2 ∧ ¬cCv2_other`.

The chunk-5 twin of §4, but recomputed on the CORRECTED landing (`cLandNzV2` reads the OLD board at
the `wDstV2` = corrected-flow-through landing) and on the CORRECTED journeys bit (`cCv2 (1−which)`, the
inclusive-occlusion carry, in place of the OLD exclusive-occlusion `carryCol`). Pure gate algebra. -/
section NonLeaveV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `nonLeaveV2One n which` at either piece index. -/
theorem nlV2Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.nonLeaveV2One n which) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_nonLeaveV2
  rw [NGen.nonLeaveV2Constraints]
  interval_cases which
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

/-- **`nonLeaveV2GateN_of_sat`.** `cNonLeaveV2[which]` is boolean and is `1` iff the CORRECTED landing
is non-vacuum (`cLandNzV2 = 1`) and the OTHER piece's inclusive-occlusion carry is zero
(`cCv2 (1−which) = 0`). -/
theorem nonLeaveV2GateN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hlandnz : (envAt t i).loc (NGen.cLandNzV2 n which) = 0
        ∨ (envAt t i).loc (NGen.cLandNzV2 n which) = 1)
    (hcv2Other : (envAt t i).loc (NGen.cCv2 n (1 - which)) = 0
        ∨ (envAt t i).loc (NGen.cCv2 n (1 - which)) = 1) :
    ((envAt t i).loc (NGen.cNonLeaveV2 n which) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cNonLeaveV2 n which) = 1 ↔
          ((envAt t i).loc (NGen.cLandNzV2 n which) = 1
            ∧ (envAt t i).loc (NGen.cCv2 n (1 - which)) = 0)) := by
  set e := envAt t i with he
  have hmem : cgH (((Head.lin 1 (NGen.cNonLeaveV2 n which)).addLin (-1) (NGen.cLandNzV2 n which)).addProd 1
              [(NGen.cLandNzV2 n which), (NGen.cCv2 n (1 - which))])
      ∈ (automataflResolveDescN n).constraints :=
    nlV2Lift which hw (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (((Head.lin 1 (NGen.cNonLeaveV2 n which)).addLin (-1)
        (NGen.cLandNzV2 n which)).addProd 1
        [(NGen.cLandNzV2 n which), (NGen.cCv2 n (1 - which))])).eval e.loc
      = e.loc (NGen.cNonLeaveV2 n which) + (-1) * e.loc (NGen.cLandNzV2 n which)
        + e.loc (NGen.cLandNzV2 n which) * e.loc (NGen.cCv2 n (1 - which)) := by canon_head_eval [headToExpr]
  rw [hE] at hg
  have hnl : e.loc (NGen.cNonLeaveV2 n which)
      = e.loc (NGen.cLandNzV2 n which)
        - e.loc (NGen.cLandNzV2 n which) * e.loc (NGen.cCv2 n (1 - which)) := by
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [hnl, a, b] <;> norm_num
  · rw [hnl]
    rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [a, b] <;> norm_num

end NonLeaveV2

/-! ## §11 — `cv2ValN_of_sat` and `carryV3ArithN_of_sat`: the CORRECTED carry rides the CORRECTED
non-leaver.

`cCv2 = surv · nz · (1 − occIncl)` is the chunk-3 inclusive-occlusion carry seed (already correct on
the occluded STAYER). `cCarryV3 = cCv2 · (1 − cNonLeaveV2)` rides the CORRECTED non-leaver (§10), so
on the `flowThroughOcclusionGap` class A now CARRIES (`cCarryV3 0 = 1`) onto the emptied waypoint,
where the chunk-3 `cCarryV2` (riding the OLD `cNonLeave`) kept A. Pure gate algebra. -/
section CarryV3
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `carryV3Constraints`. -/
theorem cv3Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.carryV3Constraints n) : g ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_carryV3 h

/-- **`cv2ValN_of_sat`.** The chunk-3 journeys seed `cCv2 = cCv1 · (1 − occIncl) = surv · nz ·
(1 − occIncl)` is boolean, as a standalone value (extracted from the chunk-3 carryV2 family). -/
theorem cv2ValN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hnz : (envAt t i).loc (NGen.nzCol n which) = 0 ∨ (envAt t i).loc (NGen.nzCol n which) = 1)
    (hoccI : (envAt t i).loc (NGen.cOccIncl n which) = 0
        ∨ (envAt t i).loc (NGen.cOccIncl n which) = 1) :
    ((envAt t i).loc (NGen.cCv2 n which) = 0 ∨ (envAt t i).loc (NGen.cCv2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCv2 n which) = 1 ↔
          ((envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.nzCol n which) = 1
            ∧ (envAt t i).loc (NGen.cOccIncl n which) = 0)) := by
  set e := envAt t i with he
  have hcv1 : e.loc (NGen.cCv1 n which) = e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which) := by
    have hmem : prodPin (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
        ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_self)
    exact prodN_of_sat hsat hc i hi (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
      hmem hsurv hnz
  have hcv1B : e.loc (NGen.cCv1 n which) = 0 ∨ e.loc (NGen.cCv1 n which) = 1 := by
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rw [hcv1, a, b] <;> norm_num
  have hcv2 : e.loc (NGen.cCv2 n which)
      = e.loc (NGen.cCv1 n which) - e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := by
    have hmem : cgH (NGen.cv2Head n which) ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hg := rgateHN hsat i hi hmem
    have hE : (headToExpr (NGen.cv2Head n which)).eval e.loc
        = e.loc (NGen.cCv2 n which) + (-1) * e.loc (NGen.cCv1 n which)
          + e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := by canon_head_eval [headToExpr, NGen.cv2Head]
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [a, c] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [hcv2, a, c] <;> norm_num
  · rw [hcv2, hcv1]
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hoccI with c | c <;>
      rw [a, b, c] <;> norm_num

/-- **`carryV3ArithN_of_sat`.** `cCarryV3[which] = cCv2 · (1 − cNonLeaveV2)` is boolean and is `1` iff
`cCv2 = 1` and `cNonLeaveV2 = 0`. -/
theorem carryV3ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hcv2 : (envAt t i).loc (NGen.cCv2 n which) = 0 ∨ (envAt t i).loc (NGen.cCv2 n which) = 1)
    (hnl : (envAt t i).loc (NGen.cNonLeaveV2 n which) = 0
        ∨ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 1) :
    ((envAt t i).loc (NGen.cCarryV3 n which) = 0 ∨ (envAt t i).loc (NGen.cCarryV3 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryV3 n which) = 1 ↔
          ((envAt t i).loc (NGen.cCv2 n which) = 1
            ∧ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 0)) := by
  set e := envAt t i with he
  have hmem : cgH (NGen.carryV3Head n which) ∈ (automataflResolveDescN n).constraints := by
    refine cv3Lift which hw ?_
    rw [NGen.carryV3Constraints]
    interval_cases which
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.carryV3Head n which)).eval e.loc
      = e.loc (NGen.cCarryV3 n which) + (-1) * e.loc (NGen.cCv2 n which)
        + e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeaveV2 n which) := by canon_head_eval [headToExpr, NGen.carryV3Head]
  rw [hE] at hg
  have hcarry : e.loc (NGen.cCarryV3 n which)
      = e.loc (NGen.cCv2 n which) - e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeaveV2 n which) := by
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [a, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [hcarry, a, d] <;> norm_num
  · rw [hcarry]
    rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [a, d] <;> norm_num

end CarryV3

/-! ## §14 — `resolvableV2ArithN_of_sat`: the CORRECTED resolvable surface.

`cResolvableV2 = ¬mergeV2 · ¬badV2A · ¬badV2B`, with `badV2_i = cCv2_i · cNonLeaveV2_i` (the journeys
bit `cCv2` is the inclusive-occlusion carry; the non-leaver is the CORRECTED §10 one). Pure gate
algebra over the twelve-gate logic tail of `resolvableV2Constraints`; `cMergeV2` (the confluence bit)
is taken boolean. In the `flowThroughOcclusionGap` class the CORRECTED landing puts A on the emptied
VACUUM waypoint, so `cNonLeaveV2 0 = 0` (§10) ⇒ `badV2A = 0`, where the OLD `cResolvable` rejected the
round (`cBadA = 1`). This is the circuit analog of `AutomataflRules.resolvableB_pair` (the
NO-CONFLUENCE-at-`m = 2` collapse) — the SECOND wound's resolvable half. -/
section ResolvableV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The twelve-gate boolean-logic tail of `resolvableV2Constraints` (`cIdentV2 … cResolvableV2`),
transcribed literally so the RIGHT operand of the outer `++` in `resolvableV2Constraints` is
syntactically this list — the four `cDestV2` gates and the `resEqV2` `eq_coords` are its left operand. -/
def resV2LogicTail : List VmConstraint2 :=
  [ prodPin (NGen.cIdentV2 n) (NGen.cEqBit n (NGen.eqBase n 0)) (NGen.cEqBit n (NGen.eqBase n 1))
  , prodPin (NGen.cBothCarryV2 n) (NGen.cCv2 n 0) (NGen.cCv2 n 1)
  , prodPin (NGen.cMc1V2 n) (NGen.cBothCarryV2 n) (NGen.cResEqV2 n)
  , notBitPin (NGen.cNotIdentV2 n) (NGen.cIdentV2 n)
  , prodPin (NGen.cMergeV2 n) (NGen.cMc1V2 n) (NGen.cNotIdentV2 n)
  , prodPin (NGen.cBadV2A n) (NGen.cCv2 n 0) (NGen.cNonLeaveV2 n 0)
  , prodPin (NGen.cBadV2B n) (NGen.cCv2 n 1) (NGen.cNonLeaveV2 n 1)
  , notBitPin (NGen.cNMergeV2 n) (NGen.cMergeV2 n)
  , notBitPin (NGen.cNBadV2A n) (NGen.cBadV2A n)
  , notBitPin (NGen.cNBadV2B n) (NGen.cBadV2B n)
  , prodPin (NGen.cR1V2 n) (NGen.cNMergeV2 n) (NGen.cNBadV2A n)
  , prodPin (NGen.cResolvableV2 n) (NGen.cR1V2 n) (NGen.cNBadV2B n) ]

/-- Membership lift into the twelve-gate logic tail: it is the RIGHT operand of the outer `++`. -/
theorem resV2Lift {g : VmConstraint2} (h : g ∈ resV2LogicTail (n := n)) :
    g ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_resolvableV2 ?_
  rw [NGen.resolvableV2Constraints]
  exact List.mem_append_right _ h

/-- **`resolvableV2ArithN_of_sat`.** `cResolvableV2` is boolean and is `1` iff no confluence
(`cMergeV2 = 0`) and neither piece has a bad journey (`badV2_i = cCv2_i · cNonLeaveV2_i = 0`, i.e. the
carrying piece does not land on a non-leaver). -/
theorem resolvableV2ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hcv2a : (envAt t i).loc (NGen.cCv2 n 0) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 0) = 1)
    (hcv2b : (envAt t i).loc (NGen.cCv2 n 1) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 1) = 1)
    (hnla : (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 1)
    (hnlb : (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 1)
    (hmerge : (envAt t i).loc (NGen.cMergeV2 n) = 0 ∨ (envAt t i).loc (NGen.cMergeV2 n) = 1) :
    ((envAt t i).loc (NGen.cResolvableV2 n) = 0 ∨ (envAt t i).loc (NGen.cResolvableV2 n) = 1)
      ∧ ((envAt t i).loc (NGen.cResolvableV2 n) = 1 ↔
          ((envAt t i).loc (NGen.cMergeV2 n) = 0
            ∧ ((envAt t i).loc (NGen.cCv2 n 0) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 0)
            ∧ ((envAt t i).loc (NGen.cCv2 n 1) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 0))) := by
  set e := envAt t i with he
  -- badV2A = cCv2_0 · nonLeaveV2_0  (gate 5 of the logic tail)
  have hbadA : e.loc (NGen.cBadV2A n) = e.loc (NGen.cCv2 n 0) * e.loc (NGen.cNonLeaveV2 n 0) :=
    prodN_of_sat hsat hc i hi (NGen.cBadV2A n) (NGen.cCv2 n 0) (NGen.cNonLeaveV2 n 0)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      hcv2a hnla
  have hbadAB : e.loc (NGen.cBadV2A n) = 0 ∨ e.loc (NGen.cBadV2A n) = 1 := by
    rcases hcv2a with a | a <;> rcases hnla with b | b <;> rw [hbadA, a, b] <;> norm_num
  -- badV2B = cCv2_1 · nonLeaveV2_1  (gate 6)
  have hbadB : e.loc (NGen.cBadV2B n) = e.loc (NGen.cCv2 n 1) * e.loc (NGen.cNonLeaveV2 n 1) :=
    prodN_of_sat hsat hc i hi (NGen.cBadV2B n) (NGen.cCv2 n 1) (NGen.cNonLeaveV2 n 1)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
      hcv2b hnlb
  have hbadBB : e.loc (NGen.cBadV2B n) = 0 ∨ e.loc (NGen.cBadV2B n) = 1 := by
    rcases hcv2b with a | a <;> rcases hnlb with b | b <;> rw [hbadB, a, b] <;> norm_num
  -- ¬merge, ¬badA, ¬badB  (gates 7, 8, 9)
  have hnm : e.loc (NGen.cNMergeV2 n) = 1 - e.loc (NGen.cMergeV2 n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNMergeV2 n) (NGen.cMergeV2 n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) hmerge
  have hnmB : e.loc (NGen.cNMergeV2 n) = 0 ∨ e.loc (NGen.cNMergeV2 n) = 1 := by
    rcases hmerge with a | a <;> rw [hnm, a] <;> norm_num
  have hnA : e.loc (NGen.cNBadV2A n) = 1 - e.loc (NGen.cBadV2A n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNBadV2A n) (NGen.cBadV2A n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))) hbadAB
  have hnAB : e.loc (NGen.cNBadV2A n) = 0 ∨ e.loc (NGen.cNBadV2A n) = 1 := by
    rcases hbadAB with a | a <;> rw [hnA, a] <;> norm_num
  have hnB : e.loc (NGen.cNBadV2B n) = 1 - e.loc (NGen.cBadV2B n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNBadV2B n) (NGen.cBadV2B n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))) hbadBB
  have hnBB : e.loc (NGen.cNBadV2B n) = 0 ∨ e.loc (NGen.cNBadV2B n) = 1 := by
    rcases hbadBB with a | a <;> rw [hnB, a] <;> norm_num
  -- r1 = ¬merge · ¬badA  (gate 10), resolvable = r1 · ¬badB  (gate 11)
  have hr1 : e.loc (NGen.cR1V2 n) = e.loc (NGen.cNMergeV2 n) * e.loc (NGen.cNBadV2A n) :=
    prodN_of_sat hsat hc i hi (NGen.cR1V2 n) (NGen.cNMergeV2 n) (NGen.cNBadV2A n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))) hnmB hnAB
  have hr1B : e.loc (NGen.cR1V2 n) = 0 ∨ e.loc (NGen.cR1V2 n) = 1 := by
    rcases hnmB with a | a <;> rcases hnAB with b | b <;> rw [hr1, a, b] <;> norm_num
  have hres : e.loc (NGen.cResolvableV2 n) = e.loc (NGen.cR1V2 n) * e.loc (NGen.cNBadV2B n) :=
    prodN_of_sat hsat hc i hi (NGen.cResolvableV2 n) (NGen.cR1V2 n) (NGen.cNBadV2B n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))) hr1B hnBB
  refine ⟨?_, ?_⟩
  · rcases hr1B with a | a <;> rcases hnBB with b | b <;> rw [hres, a, b] <;> norm_num
  · rw [hres, hr1, hnm, hnA, hnB, hbadA, hbadB]
    rcases hcv2a with a | a <;> rcases hcv2b with b | b <;> rcases hnla with c | c <;>
      rcases hnlb with d | d <;> rcases hmerge with f | f <;> rw [a, b, c, d, f] <;>
      simp <;> omega

end ResolvableV2

/-! ## §15 — THE SECOND WOUND, CLOSED IN-CIRCUIT AGAINST THE VALIDATED GAME.

`flowThroughOcclusionGap_witness_n3` (§7) is a SPEC-side falsifier that stays green (it is `decide`d on
the reference). The IN-CIRCUIT canary is here: composing §2 (`blockedV2N_of_sat` — the emitted
`cOccIncl` IS the validated-game `blockedB`) with §9 (`ftV2AN_of_sat` — the corrected flow-through
reads `cOccIncl`), the corrected A-side flow-through bit vanishes exactly when B's move is INCLUSIVE-
blocked — the flow-through-gap condition (B interior-clear but destination holds a non-mover). The OLD
`cFtA` (chunk-3 and before) fired here because it read the EXCLUSIVE `occluded = false`; the corrected
`cFtV2A` does NOT, so A dead-ends on the emptied waypoint as `landMap` (inclusive `blockedB`) demands.
This is the wound closed against the ACTUAL emitted descriptor, unconditional in `n`. -/
section WoundClosed
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (blockedB)

/-- **`ftV2A_inclBlocked_kills_flowThrough`.** When B's move is INCLUSIVE-blocked (validated-game
`blockedB … mb = true`), the corrected A-side flow-through bit is `0` — the second wound closed on the
real descriptor. (Contrast: the OLD `cFtA` read the exclusive `occluded`, which is `false` on this
class, so it WRONGLY fired.) -/
theorem ftV2A_inclBlocked_kills_flowThrough
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hblocked : blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 1, moveDecodeN n (envAt t i) 0]
        (moveDecodeN n (envAt t i) 1) = true) :
    (envAt t i).loc (NGen.cFtV2A n) = 0 := by
  obtain ⟨hb, hiff⟩ := ftV2AN_of_sat hsat hc i hi hab hbnz hocc hba hsurv
  have hocc1 : (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    (blockedV2N_of_sat hsat hc i hi W 1 (by norm_num)).mpr hblocked
  rcases hb with h0 | h1
  · exact h0
  · obtain ⟨_, _, _, hoccZero, _⟩ := hiff.mp h1
    rw [hocc1] at hoccZero; exact absurd hoccZero (by norm_num)

end WoundClosed

/-! ## §16 — `dstIndV2N_of_sat`: the CORRECTED landing indicator.

The chunk-5 twin of `AutomataflResolveCapstone.dstIndN_of_sat`, over the CORRECTED destination one-hots
`wDstV2Row`/`wDstV2Col` (pinned to `destHead …(cFtV2)`) instead of the OLD `wDstRow`/`wDstCol` (pinned
to `destHead …(cFtA/cFtB)`). The row×col product IS the indicator of the square the CORRECTED
flow-through bit selects — the piece's own `to` when `cFtV2 = 0`, the OTHER piece's `to` when
`cFtV2 = 1`. This is the LANDING half of the landing-correspondence input: paired with §9 (`cFtV2` =
inclusive flow-through) it is the emitted landing that a full capstone matches to `landMap_pair`. -/
section DstIndV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Circuit.Emit.AutomataflResolveCapstone (oneHotHeadN_of_sat destHead_select oneHot_pair_ind)

/-- The j-th CORRECTED destination-ROW selector boolean of piece `i`. -/
theorem weV2_dstRow_sel (i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstV2Row n i j)) ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_sel ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n))
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
theorem weV2_dstRow_sum (i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstV2Row n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstRow_idx (i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstV2Row n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
        ((destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
          (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)).scale (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstCol_sel (i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstV2Col n i j)) ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sel ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n))
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
theorem weV2_dstCol_sum (i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstV2Col n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstCol_idx (i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstV2Col n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
        ((destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
          (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)).scale (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))

/-- **`dstIndV2N_of_sat`.** The corrected destination row×column one-hot product IS the indicator of
the square the CORRECTED flow-through bit `cFtV2` selects — the piece's own `to` when `cFtV2 = 0`, the
OTHER piece's `to` when `cFtV2 = 1` — at every cell. -/
theorem dstIndV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    ∀ x y : Nat, x < n → y < n →
      (envAt t i).loc (NGen.wDstV2Row n which y) * (envAt t i).loc (NGen.wDstV2Col n which x)
        = if (⟨x, y⟩ : Coord)
             = (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
                then (moveDecodeN n (envAt t i) (1 - which)).to
                else (moveDecodeN n (envAt t i) which).to)
          then 1 else 0 := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  have hcanonRow : Canon (evalH (destHead (NGen.cTy n (NGen.mvBase n which))
      (NGen.cTy n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hy1.1, lt_trans hy1.2 hn⟩
    · rw [if_neg h]; exact ⟨hy0.1, lt_trans hy0.2 hn⟩
  have hcanonCol : Canon (evalH (destHead (NGen.cTx n (NGen.mvBase n which))
      (NGen.cTx n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hx1.1, lt_trans hx1.2 hn⟩
    · rw [if_neg h]; exact ⟨hx0.1, lt_trans hx0.2 hn⟩
  obtain ⟨ar, harLt, harEq, hrow⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstV2Row n which)
      (destHead (NGen.cTy n (NGen.mvBase n which)) (NGen.cTy n (NGen.mvBase n (1 - which))) ftc)
      hcanonRow
      (fun j hj => mem_resolve_of_mem_destV2OneHot (weV2_dstRow_sel which j hw hj))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstRow_sum which hw))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstRow_idx which hw))
  obtain ⟨ac, hacLt, hacEq, hcol⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstV2Col n which)
      (destHead (NGen.cTx n (NGen.mvBase n which)) (NGen.cTx n (NGen.mvBase n (1 - which))) ftc)
      hcanonCol
      (fun j hj => mem_resolve_of_mem_destV2OneHot (weV2_dstCol_sel which j hw hj))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstCol_sum which hw))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstCol_idx which hw))
  rw [destHead_select _ _ _ _ hft] at harEq hacEq
  have hpt : (if e.loc ftc = 1
        then (moveDecodeN n e (1 - which)).to
        else (moveDecodeN n e which).to)
      = (⟨ac, ar⟩ : Coord) := by
    by_cases h : e.loc ftc = 1
    · rw [if_pos h] at harEq hacEq ⊢
      simp only [moveDecodeN, harEq, hacEq, Int.toNat_natCast]
    · rw [if_neg h] at harEq hacEq ⊢
      simp only [moveDecodeN, harEq, hacEq, Int.toNat_natCast]
  intro x y hx hy
  rw [hpt]
  exact oneHot_pair_ind hrow hcol x y hx hy

end DstIndV2

/-! ## §17 — `landOldV2N_of_sat` / `landNzV2N_of_sat`: the CORRECTED-landing occupancy read.

`cLandOldV2 i` is the OLD-board code at the square the CORRECTED flow-through bit selects (own `.to`
when `cFtV2 = 0`, the OTHER piece's `.to` when `cFtV2 = 1`): the emitted `landOldV2Head` masked
double-sum, collapsed through the corrected-landing one-hot (`dstIndV2N_of_sat`). `cLandNzV2 i` is its
`≥ 1` bit, which the particle-alphabet envelope makes exactly `carAt` at that landing square. Clean
parametric read lemmas — the flow-through boolean and the two `.to` coordinate bounds are handed in
(as `dstIndV2N_of_sat` itself takes them), so the correspondence caller supplies them off the facts. -/
section LandV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Circuit.Emit.AutomataflCoord (evalH evalH_foldl_step evalH_addProd evalH_lin varsVal
  dot_oneHot2 headToExpr_eval)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)

/-- The clean semantic value of `landOldV2Head`, the twin of `evalH_sourceReadHead`. -/
theorem evalH_landOldV2Head (a : Nat → ℤ) (i : Nat) :
    evalH (NGen.landOldV2Head n i) a
      = a (NGen.cLandOldV2 n i)
        + ((List.range n).map (fun y => ((List.range n).map (fun x =>
            a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x)
              * (- a (NGen.old n (y * n + x))))).sum)).sum := by
  have hinner : ∀ (h : Head) (y : Nat),
      evalH ((List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)]) h) a
        = evalH h a
          + ((List.range n).map (fun x =>
              a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x)
                * (- a (NGen.old n (y * n + x))))).sum := by
    intro h y
    exact evalH_foldl_step a h (List.range n)
      (fun h2 x => h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)])
      (fun x => a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x) * (- a (NGen.old n (y * n + x))))
      (by intro h2 x; rw [evalH_addProd]; simp only [varsVal, List.foldl_cons, List.foldl_nil]; ring)
  rw [NGen.landOldV2Head,
    evalH_foldl_step a (Head.lin 1 (NGen.cLandOldV2 n i)) (List.range n)
      (fun h y => (List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)]) h)
      (fun y => ((List.range n).map (fun x =>
          a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x) * (- a (NGen.old n (y * n + x))))).sum)
      hinner,
    evalH_lin]
  ring

/-- **Grid collapse of a product-indicator masked double-sum.** If `row y · col x` is the indicator of
`⟨lx, ly⟩` on the `n × n` grid, the masked board double-sum picks out `payload ly lx`. Pure. -/
theorem gridProdInd_collapse (row col : Nat → ℤ) (payload : Nat → Nat → ℤ)
    (lx ly : Nat) (hlx : lx < n) (hly : ly < n)
    (hind : ∀ x y, x < n → y < n → row y * col x = if (⟨x, y⟩ : Coord) = ⟨lx, ly⟩ then 1 else 0) :
    ((List.range n).map (fun y => ((List.range n).map (fun x =>
        row y * col x * payload y x)).sum)).sum = payload ly lx := by
  have hcollapse := dot_oneHot2 (rv := fun y => if y = ly then (1:ℤ) else 0)
    (cv := fun x => if x = lx then (1:ℤ) else 0) (n := n) (ay := ly) (ax := lx)
    ⟨hly, fun j _ => rfl⟩ ⟨hlx, fun j _ => rfl⟩ payload
  rw [← hcollapse]
  refine congrArg List.sum ?_
  apply List.map_congr_left; intro y hy; have hyn := List.mem_range.mp hy
  refine congrArg List.sum ?_
  apply List.map_congr_left; intro x hx; have hxn := List.mem_range.mp hx
  rw [hind x y hxn hyn]
  by_cases hxy : (⟨x, y⟩ : Coord) = ⟨lx, ly⟩
  · have hx' : x = lx := ((Coord.mk.injEq x y lx ly).mp hxy).1
    have hy' : y = ly := ((Coord.mk.injEq x y lx ly).mp hxy).2
    rw [if_pos hxy, if_pos hy', if_pos hx']; ring
  · rw [if_neg hxy]
    have hz : (if y = ly then (1:ℤ) else 0) * (if x = lx then (1:ℤ) else 0) = 0 := by
      by_cases hy' : y = ly
      · by_cases hx' : x = lx
        · exact absurd ((Coord.mk.injEq x y lx ly).mpr ⟨hx', hy'⟩) hxy
        · rw [if_neg hx', mul_zero]
      · rw [if_neg hy', zero_mul]
    rw [hz]

/-- **`landOldV2N_of_sat`.** The corrected-landing OLD-board code column IS the OLD board cell at the
square the corrected flow-through bit selects. Stated as an exact integer equality (both sides
canonical). `which = 0` reads `cFtV2A`, `which = 1` reads `cFtV2B`. -/
theorem landOldV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    (envAt t i).loc (NGen.cLandOldV2 n which)
      = (envAt t i).loc (NGen.old n
          (((if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) (1 - which)).to
              else (moveDecodeN n (envAt t i) which).to).y) * n
           + (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) (1 - which)).to
              else (moveDecodeN n (envAt t i) which).to).x)) := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  set L : Coord := (if e.loc ftc = 1 then (moveDecodeN n e (1 - which)).to
                    else (moveDecodeN n e which).to) with hL
  have hLx : L.x < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTx n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTx n (NGen.mvBase n which))).toNat < n; omega
  have hLy : L.y < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTy n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat < n; omega
  -- the corrected-landing indicator
  have hdi := dstIndV2N_of_sat hsat hc i hi which hw hn hft hx0 hy0 hx1 hy1
  rw [← he, ← hftc, ← hL] at hdi
  -- the masked double-sum gate
  have hmem : cgH (NGen.landOldV2Head n which) ∈ (automataflResolveDescN n).constraints :=
    nlV2Lift which hw (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  have hg := rgateHN hsat i hi hmem
  rw [headToExpr_eval, evalH_landOldV2Head] at hg
  have hcollapse : ((List.range n).map (fun y => ((List.range n).map (fun x =>
        e.loc (NGen.wDstV2Row n which y) * e.loc (NGen.wDstV2Col n which x)
          * (- e.loc (NGen.old n (y * n + x))))).sum)).sum
      = - e.loc (NGen.old n (L.y * n + L.x)) := by
    have := gridProdInd_collapse (n := n) (fun y => e.loc (NGen.wDstV2Row n which y))
      (fun x => e.loc (NGen.wDstV2Col n which x))
      (fun y x => - e.loc (NGen.old n (y * n + x))) L.x L.y hLx hLy
      (fun x y hx hy => by rw [hdi x y hx hy])
    simpa using this
  rw [hcollapse] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ?_
  exact (gate_modEq_iff (by ring)).mp hg

/-- **`landNzV2N_of_sat`.** The corrected-landing occupancy bit is boolean and is `1` iff the OLD
board carries a piece (`carAt = true`) at the square the corrected flow-through bit selects. -/
theorem landNzV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    ((envAt t i).loc (NGen.cLandNzV2 n which) = 0 ∨ (envAt t i).loc (NGen.cLandNzV2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cLandNzV2 n which) = 1 ↔
          Dregg2.Games.AutomataflRules.carAt (boardDecodeOldN n (envAt t i))
            (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
             then (moveDecodeN n (envAt t i) (1 - which)).to
             else (moveDecodeN n (envAt t i) which).to) = true) := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  set L : Coord := (if e.loc ftc = 1 then (moveDecodeN n e (1 - which)).to
                    else (moveDecodeN n e which).to) with hL
  have hLx : L.x < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTx n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTx n (NGen.mvBase n which))).toNat < n; omega
  have hLy : L.y < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTy n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat < n; omega
  have hLc : L.y * n + L.x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (L.y + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega : L.y + 1 ≤ n)
    have hexp : (L.y + 1) * n = L.y * n + n := by ring
    omega
  -- the read value: cLandOldV2 = old at the landing cell
  have hread := landOldV2N_of_sat hsat hc i hi which hw hn hft hx0 hy0 hx1 hy1
  rw [← he, ← hftc, ← hL] at hread
  -- alphabet of the landing cell
  have halpha : e.loc (NGen.old n (L.y * n + L.x)) = 0 ∨ e.loc (NGen.old n (L.y * n + L.x)) = 1
      ∨ e.loc (NGen.old n (L.y * n + L.x)) = 2 ∨ e.loc (NGen.old n (L.y * n + L.x)) = 3 :=
    Dregg2.Circuit.Emit.AutomataflStepRefine.mem4_of_gate
      (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_old n (L.y * n + L.x) hLc)))
      (canon_loc hc i _)
  have hbnd : -99 ≤ e.loc (NGen.cLandOldV2 n which) ∧ e.loc (NGen.cLandOldV2 n which) ≤ 99 := by
    rw [hread]; rcases halpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  -- the ≥1 bit
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5N_of_sat hsat hc i hi (NGen.cLandOldV2 n which) (NGen.cLandNzV2 n which)
      (NGen.landNzV2Bit n which 0)
      (nlV2Lift which hw (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _))))
      (fun k hk => nlV2Lift which hw
        (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ k hk))))
      (nlV2Lift which hw (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _))))
      hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  -- cLandNzV2 = 1 ↔ the landing OLD cell is nonzero
  have hiff_old : e.loc (NGen.cLandNzV2 n which) = 1 ↔ e.loc (NGen.old n (L.y * n + L.x)) ≠ 0 := by
    rw [hread] at h1 h0
    rcases halpha with h | h | h | h <;> rw [h] at h1 h0 ⊢
    · constructor
      · intro hone; exact absurd (h1 hone) (by norm_num)
      · intro hne; exact absurd rfl hne
    all_goals
      constructor
      · intro _; norm_num
      · intro _
        rcases hb with hz | ho
        · exact absurd (h0 hz) (by norm_num)
        · exact ho
  -- the landing cell decodes to the OLD board cell there, and `carAt` reads its non-vacuity
  have hcarr : Dregg2.Games.AutomataflRules.carAt (boardDecodeOldN n e) L = true
      ↔ e.loc (NGen.old n (L.y * n + L.x)) ≠ 0 := by
    have hcode : (boardDecodeOldN n e).cellAt L
        = codeToParticle (e.loc (NGen.old n (L.y * n + L.x))) := by
      simp only [boardDecodeOldN, Board.cellAt]
      exact if_pos (⟨hLx, hLy⟩ : L.x < n ∧ L.y < n)
    rw [Dregg2.Games.AutomataflRules.carAt, hcode]
    rcases halpha with h | h | h | h <;> rw [h] <;> decide
  exact ⟨hb, hiff_old.trans hcarr.symm⟩

end LandV2

/-! ## §18 — THE THIRD WOUND: the 2-CYCLE STAY, which the V3 surface does NOT close.

Chunks 4–5 corrected two configuration classes against the VALIDATED game: the occluded STAYER
(defect #8, §2/§3/§15) and the FLOW-THROUGH gap (§7/§9/§15). Casing the CORRECTED carry `cCarryV3`
against the reference `landMap_pair_a/b` 5-config if-tree discharges FIVE of the six landing arms —
blocked-stays, independent-own-dest, occluded-stayer, caterpillar, flow-through — but the SIXTH arm,
the **2-CYCLE** (`landMap_pair_twoCycle_a/b`), MISMATCHES.

THE CLASS (n ≥ 2). A carries at `sa`, wants `da = sb`; B carries at `sb`, wants `db = sa`; both
unblocked, distinct sources, distinct raw destinations. This is the symmetric 2-cycle A→B, B→A.

  * The FIXED reference (`AutomataflRules.landMap`, ruling C / audit divergence 3.5a — *"2-cycles:
    Always stay in place"*, the `twoCyc` dead-end in `leaves`) keeps BOTH pieces: `landMap sa = sa`,
    `landMap sb = sb`, `movers = []`, `resolvableB = true`, `resolveMoves = identity`.
  * The DESCRIPTOR SWAPS. `cFtV2A = 0` (the `¬eq_ba` conjunct is false in a 2-cycle), so A's corrected
    landing is `da = sb`; `cCv2 0 = surv·carSa·¬BA = 1`; `cLandNzV2 0 = carAt sb = 1`; the corrected
    non-leaver reads the OTHER piece's SEED carry `cCv2 1 = surv·carSb·¬BB = 1`, so
    `cNonLeaveV2 0 = cLandNzV2 0 · (1 − cCv2 1) = 1 · 0 = 0`, whence `cCarryV3 0 = cCv2 0 · ¬cNonLeaveV2 0
    = 1` — A CARRIES onto `sb`. Symmetrically `cCarryV3 1 = 1` carries B onto `sa`. And
    `cResolvableV2 = 1` (no merge — the two corrected dests `da = sb`, `db = sa` are DISTINCT — and no
    bad journey). So the emitted board writes the SWAP `mid[sa] = p_b`, `mid[sb] = p_a`.

The root cause: the corrected non-leaver `cNonLeaveV2 = landNzV2 · (1 − cCv2_other)` proxies "the piece
on my landing square does not itself leave" by the OTHER piece's SEED carry `cCv2` — but in a 2-cycle
BOTH seed carries are `1` even though BOTH pieces ultimately STAY (a mutual, recursive disposition the
reference captures with its dedicated `twoCyc` bit + the `leaves` fixpoint). The V3 surface has NO
two-cycle column, so the mutual stay is unmodeled. Closing it is a FOURTH emitter obligation: a
`cTwoCyc_i = eq_ab · eq_ba · ¬BA · ¬BB` bit ANDed as `¬cTwoCyc` into each carry (equivalently
`cCarryV4 = cCarryV3 · ¬cTwoCyc`), so a detected 2-cycle forces the carry to `0` and the pieces are
kept — exactly the reference's ruling C. (The detector is OCCUPANCY-BLIND: the `carSa · carSb` source
conjuncts are OMITTED — seventh-wound repair, §20 — so it also fires on the vacuum-far 2-cycle, README
3.5b, exactly like the reference `twoCyc`.)

`twoCycleStay_witness_n3` is the executable falsifier, `decide`d entirely on the reference semantics:
the reference STAYS (identity board) where the descriptor SWAPS, so with `p_a ≠ p_b` the unconditional
`codeToParticle (cMidV3 …) = (resolveMoves …).cellAt …` is FALSE at `sa` (LHS `= p_b` from the swap,
RHS `= p_a` from the stay). Hence the full capstone is STILL NOT assemblable at `n ≥ 3` against this
descriptor — the landing correspondence closes 5 of 6 arms; the 2-cycle arm is the residual. -/
section TwoCycleWound
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A (attractor) at `(0,0)` wants `(1,0)`; B (repulsor) at `(1,0)` wants `(0,0)`. Both
carry, both unblocked (each source is the OTHER's passable waypoint), rook-aligned in row 0. The
automaton sits at `(2,2)`, off both moves. This is the symmetric 2-cycle A→B, B→A. -/
def tcBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨0, 0⟩, Particle.attractor), (⟨1, 0⟩, Particle.repulsor)] ⟨2, 2⟩
def tcMA : Move := Move.mk 0 ⟨0, 0⟩ ⟨1, 0⟩
def tcMB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE 2-CYCLE STAY IS NOT EMPTY, AT `n = 3`, AND V3 GETS IT WRONG.** Both moves are legal with
distinct sources and distinct raw destinations, both unblocked, both carrying, forming the symmetric
2-cycle (`da = sb`, `db = sa`). The REFERENCE keeps BOTH pieces in place (`landMap sa = sa`,
`landMap sb = sb`, `resolvableB = true`, `resolveMoves = identity`). The descriptor's corrected surface
instead SWAPS them (see the section note: `cCarryV3 0 = cCarryV3 1 = 1`, `cResolvableV2 = 1`), so
`codeToParticle (cMidV3 …) = (resolveMoves …).cellAt …` is FALSE at `sa` — attractor kept by the
reference, repulsor written by the descriptor. Every clause `decide`d on the reference semantics. -/
theorem twoCycleStay_witness_n3 :
    MoveValid tcBoard tcMA ∧ MoveValid tcBoard tcMB
      ∧ tcMA.frm ≠ tcMB.frm ∧ tcMA.to ≠ tcMB.to
      ∧ tcMA.frm ≠ tcMA.to ∧ tcMB.frm ≠ tcMB.to
      -- the symmetric 2-cycle, both unblocked:
      ∧ tcMA.to = tcMB.frm ∧ tcMB.to = tcMA.frm
      ∧ blockedB tcBoard [tcMA, tcMB] tcMA = false
      ∧ blockedB tcBoard [tcMA, tcMB] tcMB = false
      ∧ carAt tcBoard tcMA.frm = true ∧ carAt tcBoard tcMB.frm = true
      -- the REFERENCE STAYS both pieces (ruling C, audit 3.5a):
      ∧ landMap tcBoard [tcMA, tcMB] tcMA.frm = tcMA.frm
      ∧ landMap tcBoard [tcMA, tcMB] tcMB.frm = tcMB.frm
      ∧ resolvableB tcBoard [tcMA, tcMB] = true
      ∧ (resolveMoves tcBoard [tcMA, tcMB]).cellAt tcMA.frm = Particle.attractor
      ∧ (resolveMoves tcBoard [tcMA, tcMB]).cellAt tcMB.frm = Particle.repulsor
      ∧ tcBoard.cellAt tcMA.frm = Particle.attractor
      ∧ tcBoard.cellAt tcMB.frm = Particle.repulsor
      ∧ Particle.attractor ≠ Particle.repulsor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end TwoCycleWound

/-! ## §19 — THE V4 EXTRACTION TWINS: the 2-CYCLE detector and the FINAL corrected board rewrite.

The chunk-6 twins of §11 (`carryV3ArithN`), §12 (`midV3CellN`) and §13 (`writeCellV3N`), over the
FINAL corrected columns. `cTwoCyc` is the mutual-2-cycle detector (`§18`'s fix); `cCarryV4 =
cCarryV3 · (1 − cTwoCyc)` forces the corrected carry to `0` on a detected 2-cycle so both pieces are
kept; `cWBoardV4`/`cMidV4` are the `cResolvableV2`-gated FINAL board rewrite driven by `cCarryV4` and
the CHUNK-5 corrected `wDstV2` landing. Pure gate algebra — the mechanical mirrors of §11–§13. -/
section V4Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `twoCycConstraints`. -/
theorem tcLift {g : VmConstraint2} (h : g ∈ NGen.twoCycConstraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_twoCyc h

/-- Membership lift into `carryV4Constraints`. -/
theorem cv4Lift {g : VmConstraint2} (h : g ∈ NGen.carryV4Constraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_carryV4 h

/-- **`twoCycN_of_sat`.** The mutual 2-cycle detector `cTwoCyc` is boolean and is `1` iff both raw
destinations point at the other source (`eqAb = eqBa = 1`) and neither move is inclusive-blocked
(`cOccIncl 1 = cOccIncl 0 = 0`, the `cNOccIb`/`cNOccIa` NOT bits emitted by `flowThroughV2`).
OCCUPANCY-BLIND — the `cAnz`/`cBnz` source-carry conjuncts are DROPPED (seventh-wound repair), so the
detector fires on the two reversed unblocked edges alone, exactly like the reference
`AutomataflRules.twoCyc` (which also detects the VACUUM-FAR 2-cycle, README 3.5b, ruling C). -/
theorem twoCycN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hocc1 : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hocc0 : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1) :
    ((envAt t i).loc (NGen.cTwoCyc n) = 0 ∨ (envAt t i).loc (NGen.cTwoCyc n) = 1)
      ∧ ((envAt t i).loc (NGen.cTwoCyc n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1
            ∧ (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∧ (envAt t i).loc (NGen.cOccIncl n 0) = 0)) := by
  set e := envAt t i with he
  -- the inclusive-occlusion NOT bits (gate 0 and gate 5 of `flowThroughV2Constraints`)
  have hnoccb : e.loc (NGen.cNOccIb n) = 1 - e.loc (NGen.cOccIncl n 1) :=
    notBitN_of_sat hsat hc i hi (NGen.cNOccIb n) (NGen.cOccIncl n 1)
      (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_self)) hocc1
  have hnoccbB : e.loc (NGen.cNOccIb n) = 0 ∨ e.loc (NGen.cNOccIb n) = 1 := by
    rcases hocc1 with h | h <;> rw [hnoccb, h] <;> norm_num
  have hnocca : e.loc (NGen.cNOccIa n) = 1 - e.loc (NGen.cOccIncl n 0) :=
    notBitN_of_sat hsat hc i hi (NGen.cNOccIa n) (NGen.cOccIncl n 0)
      (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) hocc0
  have hnoccaB : e.loc (NGen.cNOccIa n) = 0 ∨ e.loc (NGen.cNOccIa n) = 1 := by
    rcases hocc0 with h | h <;> rw [hnocca, h] <;> norm_num
  -- the three-product 2-cycle chain (OCCUPANCY-BLIND: no `cAnz`/`cBnz`)
  have htc1 : e.loc (NGen.cTwoCyc1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 2)) * e.loc (NGen.cEqBit n (NGen.eqBase n 3)) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc1 n) (NGen.cEqBit n (NGen.eqBase n 2))
      (NGen.cEqBit n (NGen.eqBase n 3))
      (tcLift (by rw [NGen.twoCycConstraints]; exact List.mem_cons_self)) hab hba
  have htc1B : e.loc (NGen.cTwoCyc1 n) = 0 ∨ e.loc (NGen.cTwoCyc1 n) = 1 := by
    rcases hab with a | a <;> rcases hba with b | b <;> rw [htc1, a, b] <;> norm_num
  have htc2 : e.loc (NGen.cTwoCyc2 n) = e.loc (NGen.cTwoCyc1 n) * e.loc (NGen.cNOccIb n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc2 n) (NGen.cTwoCyc1 n) (NGen.cNOccIb n)
      (tcLift (by rw [NGen.twoCycConstraints]; exact List.mem_cons_of_mem _ List.mem_cons_self))
      htc1B hnoccbB
  have htc2B : e.loc (NGen.cTwoCyc2 n) = 0 ∨ e.loc (NGen.cTwoCyc2 n) = 1 := by
    rcases htc1B with a | a <;> rcases hnoccbB with b | b <;> rw [htc2, a, b] <;> norm_num
  have htc : e.loc (NGen.cTwoCyc n) = e.loc (NGen.cTwoCyc2 n) * e.loc (NGen.cNOccIa n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc n) (NGen.cTwoCyc2 n) (NGen.cNOccIa n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      htc2B hnoccaB
  have hval : e.loc (NGen.cTwoCyc n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 2)) * e.loc (NGen.cEqBit n (NGen.eqBase n 3))
        * (1 - e.loc (NGen.cOccIncl n 1)) * (1 - e.loc (NGen.cOccIncl n 0)) := by
    rw [htc, htc2, htc1, hnoccb, hnocca]
  refine ⟨?_, ?_⟩
  · rcases hab with a | a <;> rcases hba with b | b <;> rcases hocc1 with c | c <;>
      rcases hocc0 with d | d <;>
      rw [hval, a, b, c, d] <;> norm_num
  · rw [hval]
    rcases hab with a | a <;> rcases hba with b | b <;> rcases hocc1 with c | c <;>
      rcases hocc0 with d | d <;>
      rw [a, b, c, d] <;> norm_num

/-- **`carryV4ArithN_of_sat`.** `cCarryV4[which] = cCarryV3[which] · (1 − cTwoCyc)` is boolean and is
`1` iff `cCarryV3[which] = 1` and `cTwoCyc = 0` — the FINAL carry, forced to `0` on a detected
2-cycle so the piece is KEPT. -/
theorem carryV4ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hcv3 : (envAt t i).loc (NGen.cCarryV3 n which) = 0
        ∨ (envAt t i).loc (NGen.cCarryV3 n which) = 1)
    (htc : (envAt t i).loc (NGen.cTwoCyc n) = 0 ∨ (envAt t i).loc (NGen.cTwoCyc n) = 1) :
    ((envAt t i).loc (NGen.cCarryV4 n which) = 0 ∨ (envAt t i).loc (NGen.cCarryV4 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryV4 n which) = 1 ↔
          ((envAt t i).loc (NGen.cCarryV3 n which) = 1
            ∧ (envAt t i).loc (NGen.cTwoCyc n) = 0)) := by
  set e := envAt t i with he
  have hntc : e.loc (NGen.cNTwoCyc n) = 1 - e.loc (NGen.cTwoCyc n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNTwoCyc n) (NGen.cTwoCyc n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    List.mem_cons_self)))) htc
  have hntcB : e.loc (NGen.cNTwoCyc n) = 0 ∨ e.loc (NGen.cNTwoCyc n) = 1 := by
    rcases htc with h | h <;> rw [hntc, h] <;> norm_num
  have hcarry : e.loc (NGen.cCarryV4 n which)
      = e.loc (NGen.cCarryV3 n which) * e.loc (NGen.cNTwoCyc n) := by
    have hmem : prodPin (NGen.cCarryV4 n which) (NGen.cCarryV3 n which) (NGen.cNTwoCyc n)
        ∈ (automataflResolveDescN n).constraints := by
      refine cv4Lift ?_
      rw [NGen.carryV4Constraints]
      interval_cases which
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    exact prodN_of_sat hsat hc i hi (NGen.cCarryV4 n which) (NGen.cCarryV3 n which) (NGen.cNTwoCyc n)
      hmem hcv3 hntcB
  refine ⟨?_, ?_⟩
  · rcases hcv3 with a | a <;> rcases hntcB with b | b <;> rw [hcarry, a, b] <;> norm_num
  · rw [hcarry, hntc]
    rcases hcv3 with a | a <;> rcases htc with b | b <;> rw [a, b] <;> norm_num

/-- **`midV4CellN_of_sat`.** The FINAL corrected-board cell gate `cMidV4[c] = cResolvableV2 ·
cWBoardV4[c] + (1 − cResolvableV2) · old[c]`, rearranged (stated mod `p`) — the twin of §12. -/
theorem midV4CellN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cMidV4 n c)
      ≡ (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV4 n c)
        + (envAt t i).loc (NGen.old n c)
        - (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
  have hmem : cgH (NGen.midV4CellHead n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV4
    rw [NGen.midV4Constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.midV4CellHead n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cMidV4 n c)
        + (-1) * ((envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV4 n c))
        + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c) := by canon_head_eval [headToExpr, NGen.midV4CellHead]
  rw [hE] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **`writeCellV4N_of_sat`.** The emitted FINAL corrected `cWBoardV4` cell gate, rearranged — the twin
of §13, with `carryV3Col` replaced by the 2-cycle-gated `carryV4Col` (the `wDstV2` landing one-hots
are unchanged). Same degree-7 shape. Stated mod `p`; `x`/`y` = column/row. -/
theorem writeCellV4N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat) (hy : y = c / n) (hx : x = c % n)
    (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cWBoardV4 n c)
      ≡ (1 - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x))
           - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x))
           - (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x))
           - (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
                * (envAt t i).loc (NGen.wDstV2Col n 1 x))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
           + (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x)) * ((envAt t i).loc (NGen.carryV4Col n 0)
                * ((envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wSrcRow n 1 y) * (envAt t i).loc (NGen.wSrcCol n 1 x)))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x))))
          * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * (envAt t i).loc (NGen.particleCol n 0)
        + (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
            * (envAt t i).loc (NGen.wDstV2Col n 1 x)) * (envAt t i).loc (NGen.particleCol n 1)
        - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
            * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
            * (envAt t i).loc (NGen.particleCol n 1)
        [ZMOD 2013265921] := by
  subst hy; subst hx
  have hmem : cgH (NGen.writeCellV4Head n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV4
    rw [NGen.midV4Constraints]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hshape : (headToExpr (NGen.writeCellV4Head n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cWBoardV4 n c) + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.particleCol n 0))
        + (envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.particleCol n 1))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 0)
            * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wSrcRow n 1 (c / n)) * (envAt t i).loc (NGen.wSrcCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.particleCol n 1) := by canon_head_eval [headToExpr, NGen.writeCellV4Head]
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end V4Extract

/-! ## §20 — THE SEVENTH WOUND, CLOSED: the VACUUM-FAR 2-CYCLE (README 3.5b), now KEPT by `cTwoCyc`.

The ORIGINAL V4 `cTwoCyc` detector fired on `eqAb · eqBa · ¬occIncl1 · ¬occIncl0 · anz · bnz` — it
required BOTH sources to carry (`anz = carSa`, `bnz = carSb`). But the VALIDATED-game `twoCyc`
(`AutomataflRules` line 214, ruling C / README 3.5b) fires on the mere EXISTENCE of the two reversed
unblocked edges: `E sa = some sb` (needs `¬BA`) and `E sb = some sa` (needs `da = sb`, `db = sa`,
`¬BB`) — with NO occupancy requirement. `edgeOf` is blind to `carAt` of a source, so a move FROM a
VACUUM square still contributes its edge. On the README's own named case 3.5b — *"a move from an empty
square directly back to some source square — the piece simply doesn't move"* — the far source `sb` is
VACUUM (`carSb = false`, so `bnz = 0`), yet the reference STILL detects the 2-cycle and STAYS A
(`landMap sa = sa`, `resolveMoves` keeps A). The old `anz · bnz`-gated `cTwoCyc` read `bnz = 0` ⇒
`cTwoCyc = 0` and MOVED A into the empty `sb` — a mismatch that blocked the 2-cycle arm.

THE REPAIR (this landing): `AutomataflResolveEmit.twoCycConstraints` now emits
`cTwoCyc = eqAb · eqBa · (1 − cOccIncl 1) · (1 − cOccIncl 0)` — the `cAnz · cBnz` conjuncts DROPPED, so
the detector is OCCUPANCY-BLIND, firing on the two reversed unblocked edges alone (the exact reference
`twoCyc` condition). `twoCycN_of_sat` (§19) now PROVES `cTwoCyc = 1 ↔ eqAb=1 ∧ eqBa=1 ∧ cOccIncl 1=0 ∧
cOccIncl 0=0` — no source-carry hypothesis. On this vacuum-far witness the detector FIRES
(`cTwoCyc = 1`), so `carryV4ArithN_of_sat` gives `cCarryV4 0 = cCarryV3 0 · ¬cTwoCyc = 0` and
`writeCellV4`/`cMidV4` KEEP A on `sa` — matching `resolveMoves`. The witness below now anchors that
correspondence (reference keeps A, and the fixed occupancy-blind `cTwoCyc` keeps A too); the gate-level
`cTwoCyc = 1` at `cBnz = 0` is exhibited by `AutomataflResolveEmit`'s SEVENTH-WOUND-FLIPPED canary. -/
section VacuumTwoCycleWound
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A (attractor) at `(0,0)` wants `(1,0)`; the phantom move B goes `(1,0) → (0,0)` FROM AN
EMPTY square (`(1,0)` is vacuum — the ONLY board piece is A at `(0,0)`). Both legal, distinct sources,
distinct raw destinations, both unblocked, forming the symmetric 2-cycle (`da = sb`, `db = sa`) — and
`carSb = false` (the far source is vacuum), the case the OLD `anz · bnz`-gated `cTwoCyc` missed and the
fixed OCCUPANCY-BLIND `cTwoCyc` now catches. The automaton sits at `(2,2)`, off both moves. -/
def vtcBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3 [(⟨0, 0⟩, Particle.attractor)] ⟨2, 2⟩
def vtcMA : Move := Move.mk 0 ⟨0, 0⟩ ⟨1, 0⟩
def vtcMB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE VACUUM-FAR 2-CYCLE STAYS, AT `n = 3`, AND THE FIXED `cTwoCyc` NOW KEEPS IT.** Both moves are
legal with distinct sources and distinct raw destinations, both unblocked, forming the symmetric
2-cycle (`da = sb`, `db = sa`). A carries (`carSa = true`); the far source is VACUUM (`carSb = false`) —
the case the ORIGINAL `cTwoCyc = … · anz · bnz` missed (it needed `bnz = carSb = 1`). The REFERENCE
keeps A in place (`landMap sa = sa`, `resolvableB = true`, `resolveMoves` keeps A on `sa` and leaves
`sb` vacuum — ruling C / README 3.5b); the seventh-wound repair makes the occupancy-blind `cTwoCyc`
FIRE on this row (`twoCycN_of_sat`, no source-carry hypothesis), so `cCarryV4 0 = 0` and `cMidV4` KEEP A
too — the two now AGREE. Every clause `decide`d on the reference semantics. -/
theorem vacuumTwoCycleStay_witness_n3 :
    MoveValid vtcBoard vtcMA ∧ MoveValid vtcBoard vtcMB
      ∧ vtcMA.frm ≠ vtcMB.frm ∧ vtcMA.to ≠ vtcMB.to
      ∧ vtcMA.frm ≠ vtcMA.to ∧ vtcMB.frm ≠ vtcMB.to
      -- the symmetric 2-cycle, both unblocked:
      ∧ vtcMA.to = vtcMB.frm ∧ vtcMB.to = vtcMA.frm
      ∧ blockedB vtcBoard [vtcMA, vtcMB] vtcMA = false
      ∧ blockedB vtcBoard [vtcMA, vtcMB] vtcMB = false
      -- A carries, but the FAR source is VACUUM (the clause the V4 `cTwoCyc` requires and this row lacks):
      ∧ carAt vtcBoard vtcMA.frm = true
      ∧ carAt vtcBoard vtcMB.frm = false
      -- the REFERENCE STAYS A (ruling C, README 3.5b — the reversed edges exist despite the vacuum source):
      ∧ landMap vtcBoard [vtcMA, vtcMB] vtcMA.frm = vtcMA.frm
      ∧ resolvableB vtcBoard [vtcMA, vtcMB] = true
      ∧ (resolveMoves vtcBoard [vtcMA, vtcMB]).cellAt vtcMA.frm = Particle.attractor
      ∧ (resolveMoves vtcBoard [vtcMA, vtcMB]).cellAt vtcMB.frm = Particle.vacuum
      ∧ vtcBoard.cellAt vtcMA.frm = Particle.attractor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end VacuumTwoCycleWound

/-! ## §21 — WHY the FORK/COLLIDE reference is `roundStep`, NOT raw `resolveMoves`.

The unconditional capstone quantifies over rows where the two decoded moves FORK (`sa = sb`) or COLLIDE
(`da = db`, both sources non-vacuum). On such a row the descriptor sets `surv = 0` (`selectionN_of_sat`'s
`survIff`), so every carry vanishes and `cWBoardV4 = old` — the emitted MID board is the OLD board
(identity). The task framed the matching reference as `resolveMoves b [ma, mb] = b`, but that is FALSE:
the game's `AutomataflRules.roundStep` detects the fork/collide clash FIRST (`clashCoords`, via the
SYNTACTIC `forkAt`/`collideAt` — blocking-INDEPENDENT) and re-enters the round with the board UNCHANGED
(`.again { board := rs.board, … }`); it NEVER calls `resolveMoves` on a clashing round. Raw
`resolveMoves` on such a pair does NOT give identity when exactly ONE move is blocked: it moves the
SURVIVING (unblocked) piece. So the emitted `cWBoardV4 = old` corresponds to `roundStep`'s re-entry
board, and the fork/collide capstone arm must target `roundStep` (board unchanged that round), not raw
`resolveMoves`. The witness below `decide`s that raw `resolveMoves` MOVES the unblocked piece on a
one-blocked collide, pinning that the reference target is `roundStep`. -/
section ForkCollideRawResolve
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A (attractor) at `(1,2)` and B (repulsor) at `(0,0)` both target `D = (1,0)` (a COLLIDE:
`da = db`, both sources non-vacuum). A move `(1,2) → (1,0)` is BLOCKED by the static piece at the
interior `(1,1)`; B move `(0,0) → (1,0)` is clear. -/
def cobBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨1, 2⟩, Particle.attractor), (⟨0, 0⟩, Particle.repulsor), (⟨1, 1⟩, Particle.attractor)] ⟨2, 2⟩
def cobMA : Move := Move.mk 0 ⟨1, 2⟩ ⟨1, 0⟩
def cobMB : Move := Move.mk 1 ⟨0, 0⟩ ⟨1, 0⟩

/-- **RAW `resolveMoves` IS NOT IDENTITY ON A ONE-BLOCKED COLLIDE.** The pair collides (`da = db`, both
non-vacuum), so `roundStep` would re-enter with the board UNCHANGED (matching the descriptor's
`surv = 0 ⇒ cWBoardV4 = old`). But A is blocked and B is not, so RAW `resolveMoves` MOVES B onto the
shared destination `(1,0)` and VACATES B's source `(0,0)` — proving the fork/collide reference must be
`roundStep`, not raw `resolveMoves` (the task's item (3) `resolveMoves = b` is the wrong target). Every
clause `decide`d on the reference semantics. -/
theorem collideOneBlocked_rawResolveMoves_moves_witness :
    MoveValid cobBoard cobMA ∧ MoveValid cobBoard cobMB
      ∧ cobMA.to = cobMB.to                       -- COLLIDE: same destination
      ∧ cobMA.frm ≠ cobMB.frm
      ∧ carAt cobBoard cobMA.frm = true ∧ carAt cobBoard cobMB.frm = true
      ∧ blockedB cobBoard [cobMA, cobMB] cobMA = true    -- A blocked (interior `(1,1)`)
      ∧ blockedB cobBoard [cobMA, cobMB] cobMB = false   -- B unblocked
      -- raw `resolveMoves` MOVES B (NOT identity): B vacates `(0,0)`, lands `(1,0)`:
      ∧ resolvableB cobBoard [cobMA, cobMB] = true
      ∧ (resolveMoves cobBoard [cobMA, cobMB]).cellAt cobMB.frm = Particle.vacuum
      ∧ (resolveMoves cobBoard [cobMA, cobMB]).cellAt cobMB.to = Particle.repulsor
      ∧ cobBoard.cellAt cobMB.frm = Particle.repulsor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end ForkCollideRawResolve

/-! ## §22 — THE LANDING CORRESPONDENCE: the emitted FINAL carry `cCarryV4` IS the reference mover set.

This is the 6-arm capstone-target correspondence. On a CLEAN round (`surv = 1`, distinct decoded
sources), `cCarryV4 which = 1` iff piece `which` is a reference MOVER (`carAt sX ∧ landMap sX ≠ sX`),
and when it carries, the emitted `cFtV2`-selected landing IS the reference `landMap sX` — all six
`landMap_pair_a`/`landMap_pair_b` arms (blocked-stay, independent, occluded-stayer, 2-cycle stay,
caterpillar, flow-through), threaded through the V4 column extractions. The 2-cycle arm is the one the
seventh-wound occupancy-blind `cTwoCyc` fix closed. -/
section LandCorr
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves movers arrivalAt
  memB landMap_pair_a landMap_pair_b landMap_pair_blocked_a landMap_pair_blocked_b movers_pair
  resolveMoves_cell_pair carAt_to_false_of_not_blocked blockedB_swap)

/-- **THE A-SIDE LANDING CORRESPONDENCE.** Off a satisfying, canonical row on a CLEAN round (surv = 1,
distinct sources), the FINAL carry `cCarryV4 0` is `1` iff piece A is a MOVER of the reference round
(`carAt sa ∧ landMap sa ≠ sa`), and when it carries, the emitted `cFtV2`-selected landing IS the
reference `landMap sa`. All six `landMap_pair_a` arms verified. -/
theorem landV4CorrespondenceA_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hne : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm) :
    ((envAt t i).loc (NGen.cCarryV4 n 0) = 1 ↔
        (carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true
          ∧ landMap (boardDecodeOldN n (envAt t i))
              [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
              (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).frm))
      ∧ ((envAt t i).loc (NGen.cCarryV4 n 0) = 1 →
          (if (envAt t i).loc (NGen.cFtV2A n) = 1
            then (moveDecodeN n (envAt t i) 1).to else (moveDecodeN n (envAt t i) 0).to)
          = landMap (boardDecodeOldN n (envAt t i))
              [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
              (moveDecodeN n (envAt t i) 0).frm) := by
  -- ============ gather every fact (about `envAt t i`), then fold with `set` ============
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  have hlegA : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).to := F.validA.1
  have hlegB : (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).to := F.validB.1
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  -- pattern bits, read as `Coord` equalities
  obtain ⟨heq2B, heq2I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, heq3I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  have heq2C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ↔
      (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).frm := by
    rw [heq2I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxa.1 hfxb.1,
      AutomataflResolveCapstone.toNat_injN htya.1 hfyb.1]
  have heq3C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ↔
      (moveDecodeN n (envAt t i) 1).to = (moveDecodeN n (envAt t i) 0).frm := by
    rw [heq3I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxb.1 hfxa.1,
      AutomataflResolveCapstone.toNat_injN htyb.1 hfya.1]
  -- inclusive occlusion columns: boolean + validated-game `blockedB`
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  have hocc0I : (envAt t i).loc (NGen.cOccIncl n 0) = 1 ↔
      blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
        (moveDecodeN n (envAt t i) 0) = true := by
    have h := blockedV2N_of_sat hsat hc i hi W 0 (by norm_num)
    simpa using h
  have hocc1I : (envAt t i).loc (NGen.cOccIncl n 1) = 1 ↔
      blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
        (moveDecodeN n (envAt t i) 1) = true := by
    have h := blockedV2N_of_sat hsat hc i hi W 1 (by norm_num)
    rw [blockedB_swap] at h
    simpa using h
  -- carAt translations
  have hAnz : (envAt t i).loc (NGen.cAnz n) = 1 ↔
      carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true := by
    rw [F.anzIff, carAt]; cases (boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 0).frm |>.isVacuum <;> simp
  have hBnz : (envAt t i).loc (NGen.cBnz n) = 1 ↔
      carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true := by
    rw [F.bnzIff, carAt]; cases (boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 1).frm |>.isVacuum <;> simp
  -- the V4 column families
  obtain ⟨hftB, hftI⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hlnzB, hlnzI⟩ := landNzV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftB
    htxa htya htxb htyb
  simp only [beq_self_eq_true, if_true, Nat.sub_zero] at hlnzI
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  obtain ⟨hnlB, hnlI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 0 (by norm_num) hlnzB hcv2_1B
  obtain ⟨hcv3B, hcv3I⟩ := carryV3ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv2_0B hnlB
  obtain ⟨htcB, htcI⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  obtain ⟨hcv4B, hcv4I⟩ := carryV4ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv3B htcB
  -- ============ fold ============
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  have hnz0 : NGen.nzCol n 0 = NGen.cAnz n := rfl
  have hnz1 : NGen.nzCol n 1 = NGen.cBnz n := rfl
  -- carry-is-zero shortcut
  have carryZeroFromCv2 : e.loc (NGen.cCv2 n 0) = 0 → e.loc (NGen.cCarryV4 n 0) = 0 := by
    intro h0
    have hcv3z : e.loc (NGen.cCarryV3 n 0) = 0 := by
      rcases hcv3B with hz | ho
      · exact hz
      · exact absurd (hcv3I.mp ho).1 (by rw [h0]; norm_num)
    rcases hcv4B with hz | ho
    · exact hz
    · exact absurd (hcv4I.mp ho).1 (by rw [hcv3z]; norm_num)
  -- ============ case BLOCKED A ============
  by_cases hBA : blockedB bd [ma, mb] ma = true
  · -- cCv2 0 = 0 (occ0 = 1), so carry = 0; landMap sa = sa
    have hocc0one : e.loc (NGen.cOccIncl n 0) = 1 := hocc0I.mpr hBA
    have hcv2z : e.loc (NGen.cCv2 n 0) = 0 := by
      rcases hcv2_0B with hz | ho
      · exact hz
      · exact absurd (hcv2_0I.mp ho).2.2 (by rw [hocc0one]; norm_num)
    have hc4z := carryZeroFromCv2 hcv2z
    have hlm : landMap bd [ma, mb] ma.frm = ma.frm := landMap_pair_blocked_a bd ma mb hne hBA
    refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
      fun h => absurd h.2 (by rw [hlm]; exact fun q => q rfl)⟩,
      fun h => absurd h (by rw [hc4z]; norm_num)⟩
  · simp only [Bool.not_eq_true] at hBA
    have hocc0zero : e.loc (NGen.cOccIncl n 0) = 0 := by
      rcases hocc0B with hz | ho
      · exact hz
      · exact absurd (hocc0I.mp ho) (by rw [hBA]; exact Bool.false_ne_true)
    by_cases hCA : carAt bd ma.frm = true
    · -- the live analysis
      have hcv2one : e.loc (NGen.cCv2 n 0) = 1 := hcv2_0I.mpr ⟨hsurv, hAnz.mpr hCA, hocc0zero⟩
      -- carry = 1 ↔ nonLeave 0 = 0 ∧ twoCyc = 0
      have hcarryChar : e.loc (NGen.cCarryV4 n 0) = 1 ↔
          (e.loc (NGen.cNonLeaveV2 n 0) = 0 ∧ e.loc (NGen.cTwoCyc n) = 0) := by
        rw [hcv4I, hcv3I]
        constructor
        · rintro ⟨⟨_, hnl⟩, htc⟩; exact ⟨hnl, htc⟩
        · rintro ⟨hnl, htc⟩; exact ⟨⟨hcv2one, hnl⟩, htc⟩
      -- ===== the zero-iffs used to translate columns into the game predicates =====
      have hocc1_zero_iff : e.loc (NGen.cOccIncl n 1) = 0 ↔ blockedB bd [ma, mb] mb = false := by
        constructor
        · intro h0; cases hbb : blockedB bd [ma, mb] mb
          · rfl
          · rw [hocc1I.mpr hbb] at h0; exact absurd h0 (by norm_num)
        · intro hbb; rcases hocc1B with h | h
          · exact h
          · rw [hocc1I.mp h] at hbb; exact Bool.noConfusion hbb
      have hbnz_zero_iff : e.loc (NGen.cBnz n) = 0 ↔ carAt bd mb.frm = false := by
        constructor
        · intro h0; cases hcb : carAt bd mb.frm
          · rfl
          · rw [hBnz.mpr hcb] at h0; exact absurd h0 (by norm_num)
        · intro hcb; rcases F.bnzB with h | h
          · exact h
          · rw [hBnz.mp h] at hcb; exact Bool.noConfusion hcb
      have heq3_zero_iff : e.loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0 ↔ mb.to ≠ ma.frm := by
        constructor
        · intro h0 heq; rw [heq3C.mpr heq] at h0; exact absurd h0 (by norm_num)
        · intro hne3; rcases heq3B with h | h
          · exact h
          · exact absurd (heq3C.mp h) hne3
      -- ===== derived-column props =====
      have hFtProp : e.loc (NGen.cFtV2A n) = 1 ↔
          (ma.to = mb.frm ∧ carAt bd mb.frm = false ∧ blockedB bd [ma, mb] mb = false
            ∧ mb.to ≠ ma.frm) := by
        rw [hftI, heq2C, hbnz_zero_iff, hocc1_zero_iff, heq3_zero_iff]
        constructor
        · rintro ⟨e2, hb, _, o1, e3⟩; exact ⟨e2, hb, o1, e3⟩
        · rintro ⟨e2, hb, o1, e3⟩; exact ⟨e2, hb, hsurv, o1, e3⟩
      have hTwoCycProp : e.loc (NGen.cTwoCyc n) = 1 ↔
          (ma.to = mb.frm ∧ mb.to = ma.frm ∧ blockedB bd [ma, mb] mb = false) := by
        rw [htcI, heq2C, heq3C, hocc1_zero_iff]
        constructor
        · rintro ⟨e2, e3, o1, _⟩; exact ⟨e2, e3, o1⟩
        · rintro ⟨e2, e3, o1⟩; exact ⟨e2, e3, o1, hocc0zero⟩
      have hCv2_1Prop : e.loc (NGen.cCv2 n 1) = 1 ↔
          (carAt bd mb.frm = true ∧ blockedB bd [ma, mb] mb = false) := by
        rw [hcv2_1I, hnz1, hBnz, hocc1_zero_iff]
        constructor
        · rintro ⟨_, hc, hb⟩; exact ⟨hc, hb⟩
        · rintro ⟨hc, hb⟩; exact ⟨hsurv, hc, hb⟩
      -- ===== closers =====
      have hBAp : ¬ (blockedB bd [ma, mb] ma = true) := by rw [hBA]; exact Bool.false_ne_true
      have carryZeroTC : e.loc (NGen.cTwoCyc n) = 1 → e.loc (NGen.cCarryV4 n 0) = 0 := by
        intro h1; rcases hcv4B with hz | ho
        · exact hz
        · exact absurd (hcv4I.mp ho).2 (by rw [h1]; norm_num)
      have carryZeroNL : e.loc (NGen.cNonLeaveV2 n 0) = 1 → e.loc (NGen.cCarryV4 n 0) = 0 := by
        intro h1
        have hcv3z : e.loc (NGen.cCarryV3 n 0) = 0 := by
          rcases hcv3B with hz | ho
          · exact hz
          · exact absurd (hcv3I.mp ho).2 (by rw [h1]; norm_num)
        rcases hcv4B with hz | ho
        · exact hz
        · exact absurd (hcv4I.mp ho).1 (by rw [hcv3z]; norm_num)
      have nlZero : (e.loc (NGen.cLandNzV2 n 0) = 0 ∨ e.loc (NGen.cCv2 n 1) = 1)
          → e.loc (NGen.cNonLeaveV2 n 0) = 0 := by
        intro h; rcases hnlB with hz | ho
        · exact hz
        · obtain ⟨ha, hb⟩ := hnlI.mp ho
          rcases h with h | h
          · rw [h] at ha; exact absurd ha (by norm_num)
          · rw [h] at hb; exact absurd hb (by norm_num)
      have nlOne : e.loc (NGen.cLandNzV2 n 0) = 1 → e.loc (NGen.cCv2 n 1) = 0
          → e.loc (NGen.cNonLeaveV2 n 0) = 1 := fun a b => hnlI.mpr ⟨a, b⟩
      have tcZero : ¬ (ma.to = mb.frm ∧ mb.to = ma.frm ∧ blockedB bd [ma, mb] mb = false)
          → e.loc (NGen.cTwoCyc n) = 0 := by
        intro h; rcases htcB with hz | ho
        · exact hz
        · exact absurd (hTwoCycProp.mp ho) h
      -- landing-column value from the flow-through bit
      have landOf0 : e.loc (NGen.cFtV2A n) = 0 →
          (e.loc (NGen.cLandNzV2 n 0) = 1 ↔ carAt bd ma.to = true) := by
        intro hft0; rw [hlnzI]; simp [hft0]
      have landOf1 : e.loc (NGen.cFtV2A n) = 1 →
          (e.loc (NGen.cLandNzV2 n 0) = 1 ↔ carAt bd mb.to = true) := by
        intro hft1; rw [hlnzI]; simp [hft1]
      -- ===== the six landMap arms =====
      by_cases hEAB : ma.to = mb.frm
      · by_cases hBB : blockedB bd [ma, mb] mb = true
        · -- EAB ∧ BB : landMap = if carSb then sa else da; cFtV2A = 0
          have hft0 : e.loc (NGen.cFtV2A n) = 0 := by
            rcases hftB with h | h
            · exact h
            · exact absurd (hFtProp.mp h).2.2.1 (by rw [hBB]; decide)
          have hcv2_1z : e.loc (NGen.cCv2 n 1) = 0 := by
            rcases hcv2_1B with h | h
            · exact h
            · exact absurd (hCv2_1Prop.mp h).2 (by rw [hBB]; decide)
          have hland : (if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to) = ma.to := by
            simp [hft0]
          by_cases hCB : carAt bd mb.frm = true
          · -- carSb : stuck ⇒ landMap = sa ; carry = 0
            have hlnz1 : e.loc (NGen.cLandNzV2 n 0) = 1 := by
              rw [landOf0 hft0, hEAB]; exact hCB
            have hnl1 : e.loc (NGen.cNonLeaveV2 n 0) = 1 := nlOne hlnz1 hcv2_1z
            have hc4z := carryZeroNL hnl1
            have hLM : landMap bd [ma, mb] ma.frm = ma.frm := by
              rw [landMap_pair_a bd ma mb hne hlegA hlegB,
                if_neg hBAp, if_pos hEAB, if_pos hBB, if_pos hCB]
            refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
              fun h => absurd hLM h.2⟩, fun h => absurd h (by rw [hc4z]; norm_num)⟩
          · -- ¬carSb : into empty ⇒ landMap = da ; carry = 1
            have hCBf : carAt bd mb.frm = false := by simpa using hCB
            have hlnz0 : e.loc (NGen.cLandNzV2 n 0) = 0 := by
              rcases hlnzB with h | h
              · exact h
              · rw [landOf0 hft0, hEAB, hCBf] at h; exact absurd h Bool.false_ne_true
            have hnl0 := nlZero (Or.inl hlnz0)
            have htc0 := tcZero (fun ⟨_, _, hb⟩ => by rw [hBB] at hb; exact Bool.noConfusion hb)
            have hc41 : e.loc (NGen.cCarryV4 n 0) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
            have hLM : landMap bd [ma, mb] ma.frm = ma.to := by
              rw [landMap_pair_a bd ma mb hne hlegA hlegB,
                if_neg hBAp, if_pos hEAB, if_pos hBB, if_neg hCB]
            refine ⟨⟨fun _ => ⟨hCA, by rw [hLM]; exact fun q => hlegA q.symm⟩, fun _ => hc41⟩,
              fun _ => hland.trans hLM.symm⟩
        · -- EAB ∧ ¬BB
          simp only [Bool.not_eq_true] at hBB
          by_cases hEBA : mb.to = ma.frm
          · -- 2-CYCLE : landMap = sa ; carry = 0 (twoCyc fires — occupancy-blind)
            have htc1 : e.loc (NGen.cTwoCyc n) = 1 := hTwoCycProp.mpr ⟨hEAB, hEBA, hBB⟩
            have hc4z := carryZeroTC htc1
            have hLM : landMap bd [ma, mb] ma.frm = ma.frm := by
              rw [landMap_pair_a bd ma mb hne hlegA hlegB,
                if_neg hBAp, if_pos hEAB, if_neg (by rw [hBB]; exact Bool.false_ne_true),
                if_pos hEBA]
            refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
              fun h => absurd hLM h.2⟩, fun h => absurd h (by rw [hc4z]; norm_num)⟩
          · -- ¬EBA : caterpillar (carSb) or flow-through (¬carSb)
            have htc0 := tcZero (fun ⟨_, he3, _⟩ => hEBA he3)
            by_cases hCB : carAt bd mb.frm = true
            · -- caterpillar : landMap = da ; carry = 1 ; cFtV2A = 0 (bnz ≠ 0)
              have hft0 : e.loc (NGen.cFtV2A n) = 0 := by
                rcases hftB with h | h
                · exact h
                · exact absurd (hFtProp.mp h).2.1 (by rw [hCB]; decide)
              have hcv2_1one : e.loc (NGen.cCv2 n 1) = 1 := hCv2_1Prop.mpr ⟨hCB, hBB⟩
              have hnl0 := nlZero (Or.inr hcv2_1one)
              have hc41 : e.loc (NGen.cCarryV4 n 0) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
              have hland : (if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to) = ma.to := by
                simp [hft0]
              have hLM : landMap bd [ma, mb] ma.frm = ma.to := by
                rw [landMap_pair_a bd ma mb hne hlegA hlegB,
                  if_neg hBAp, if_pos hEAB, if_neg (by rw [hBB]; exact Bool.false_ne_true),
                  if_neg hEBA, if_pos hCB]
              refine ⟨⟨fun _ => ⟨hCA, by rw [hLM]; exact fun q => hlegA q.symm⟩, fun _ => hc41⟩,
                fun _ => hland.trans hLM.symm⟩
            · -- flow-through : landMap = db ; carry = 1 ; cFtV2A = 1
              have hCBf : carAt bd mb.frm = false := by simpa using hCB
              have hft1 : e.loc (NGen.cFtV2A n) = 1 := hFtProp.mpr ⟨hEAB, hCBf, hBB, hEBA⟩
              -- db is not a source, mb unblocked ⇒ carAt db = false
              have hnsB : ([ma, mb].any (fun m' => m'.frm == mb.to)) = false := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
                  beq_eq_false_iff_ne]
                exact ⟨fun q => hEBA q.symm, hlegB⟩
              have hcarDb : carAt bd mb.to = false :=
                carAt_to_false_of_not_blocked bd [ma, mb] mb hBB hnsB
              have hlnz0 : e.loc (NGen.cLandNzV2 n 0) = 0 := by
                rcases hlnzB with h | h
                · exact h
                · rw [landOf1 hft1] at h; rw [hcarDb] at h; exact absurd h Bool.false_ne_true
              have hnl0 := nlZero (Or.inl hlnz0)
              have hc41 : e.loc (NGen.cCarryV4 n 0) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
              have hland : (if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to) = mb.to := by
                simp [hft1]
              have hLM : landMap bd [ma, mb] ma.frm = mb.to := by
                rw [landMap_pair_a bd ma mb hne hlegA hlegB,
                  if_neg hBAp, if_pos hEAB, if_neg (by rw [hBB]; exact Bool.false_ne_true),
                  if_neg hEBA, if_neg hCB]
              refine ⟨⟨fun _ => ⟨hCA, by rw [hLM]; exact hEBA⟩, fun _ => hc41⟩,
                fun _ => hland.trans hLM.symm⟩
      · -- ¬EAB : independent ⇒ landMap = da ; carry = 1 ; cFtV2A = 0
        have hft0 : e.loc (NGen.cFtV2A n) = 0 := by
          rcases hftB with h | h
          · exact h
          · exact absurd (hFtProp.mp h).1 hEAB
        have hnsA : ([ma, mb].any (fun m' => m'.frm == ma.to)) = false := by
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
            beq_eq_false_iff_ne]
          exact ⟨hlegA, fun q => hEAB q.symm⟩
        have hcarDa : carAt bd ma.to = false :=
          carAt_to_false_of_not_blocked bd [ma, mb] ma hBA hnsA
        have hlnz0 : e.loc (NGen.cLandNzV2 n 0) = 0 := by
          rcases hlnzB with h | h
          · exact h
          · rw [landOf0 hft0] at h; rw [hcarDa] at h; exact absurd h Bool.false_ne_true
        have hnl0 := nlZero (Or.inl hlnz0)
        have htc0 := tcZero (fun ⟨he2, _, _⟩ => hEAB he2)
        have hc41 : e.loc (NGen.cCarryV4 n 0) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
        have hland : (if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to) = ma.to := by
          simp [hft0]
        have hLM : landMap bd [ma, mb] ma.frm = ma.to := by
          rw [landMap_pair_a bd ma mb hne hlegA hlegB, if_neg hBAp, if_neg hEAB]
        refine ⟨⟨fun _ => ⟨hCA, by rw [hLM]; exact fun q => hlegA q.symm⟩, fun _ => hc41⟩,
          fun _ => hland.trans hLM.symm⟩
    · -- carAt sa = false ⇒ cCv2 0 = 0 ⇒ carry = 0; RHS false
      have hanzzero : e.loc (NGen.cAnz n) = 0 := by
        rcases F.anzB with hz | ho
        · exact hz
        · exact absurd (hAnz.mp ho) hCA
      have hcv2z : e.loc (NGen.cCv2 n 0) = 0 := by
        rcases hcv2_0B with hz | ho
        · exact hz
        · exact absurd (hcv2_0I.mp ho).2.1 (by rw [hnz0, hanzzero]; norm_num)
      have hc4z := carryZeroFromCv2 hcv2z
      refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
        fun h => absurd h.1 hCA⟩,
        fun h => absurd h (by rw [hc4z]; norm_num)⟩

/-- **THE B-SIDE LANDING CORRESPONDENCE.** The mirror of `landV4CorrespondenceA_of_sat`: `cCarryV4 1`
is `1` iff piece B moves, and its emitted landing is `landMap sb`. All six `landMap_pair_b` arms. -/
theorem landV4CorrespondenceB_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hne : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm) :
    ((envAt t i).loc (NGen.cCarryV4 n 1) = 1 ↔
        (carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true
          ∧ landMap (boardDecodeOldN n (envAt t i))
              [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
              (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).frm))
      ∧ ((envAt t i).loc (NGen.cCarryV4 n 1) = 1 →
          (if (envAt t i).loc (NGen.cFtV2B n) = 1
            then (moveDecodeN n (envAt t i) 0).to else (moveDecodeN n (envAt t i) 1).to)
          = landMap (boardDecodeOldN n (envAt t i))
              [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
              (moveDecodeN n (envAt t i) 1).frm) := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  have hlegA : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).to := F.validA.1
  have hlegB : (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).to := F.validB.1
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  obtain ⟨heq2B, heq2I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, heq3I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  have heq2C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ↔
      (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).frm := by
    rw [heq2I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxa.1 hfxb.1,
      AutomataflResolveCapstone.toNat_injN htya.1 hfyb.1]
  have heq3C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ↔
      (moveDecodeN n (envAt t i) 1).to = (moveDecodeN n (envAt t i) 0).frm := by
    rw [heq3I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxb.1 hfxa.1,
      AutomataflResolveCapstone.toNat_injN htyb.1 hfya.1]
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  have hocc0I : (envAt t i).loc (NGen.cOccIncl n 0) = 1 ↔
      blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
        (moveDecodeN n (envAt t i) 0) = true := by
    have h := blockedV2N_of_sat hsat hc i hi W 0 (by norm_num)
    simpa using h
  have hocc1I : (envAt t i).loc (NGen.cOccIncl n 1) = 1 ↔
      blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
        (moveDecodeN n (envAt t i) 1) = true := by
    have h := blockedV2N_of_sat hsat hc i hi W 1 (by norm_num)
    rw [blockedB_swap] at h
    simpa using h
  have hAnz : (envAt t i).loc (NGen.cAnz n) = 1 ↔
      carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true := by
    rw [F.anzIff, carAt]; cases (boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 0).frm |>.isVacuum <;> simp
  have hBnz : (envAt t i).loc (NGen.cBnz n) = 1 ↔
      carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true := by
    rw [F.bnzIff, carAt]; cases (boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 1).frm |>.isVacuum <;> simp
  obtain ⟨hftB, hftI⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  obtain ⟨hlnzB, hlnzI0⟩ := landNzV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftB
    htxb htyb htxa htya
  have hlnzI : (envAt t i).loc (NGen.cLandNzV2 n 1) = 1 ↔
      carAt (boardDecodeOldN n (envAt t i))
        (if (envAt t i).loc (NGen.cFtV2B n) = 1 then (moveDecodeN n (envAt t i) 0).to
         else (moveDecodeN n (envAt t i) 1).to) = true := by simpa using hlnzI0
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  obtain ⟨hnlB, hnlI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 1 (by norm_num) hlnzB hcv2_0B
  obtain ⟨hcv3B, hcv3I⟩ := carryV3ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv2_1B hnlB
  obtain ⟨htcB, htcI⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  obtain ⟨hcv4B, hcv4I⟩ := carryV4ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv3B htcB
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  have hnz0 : NGen.nzCol n 0 = NGen.cAnz n := rfl
  have hnz1 : NGen.nzCol n 1 = NGen.cBnz n := rfl
  have carryZeroFromCv2 : e.loc (NGen.cCv2 n 1) = 0 → e.loc (NGen.cCarryV4 n 1) = 0 := by
    intro h0
    have hcv3z : e.loc (NGen.cCarryV3 n 1) = 0 := by
      rcases hcv3B with hz | ho
      · exact hz
      · exact absurd (hcv3I.mp ho).1 (by rw [h0]; norm_num)
    rcases hcv4B with hz | ho
    · exact hz
    · exact absurd (hcv4I.mp ho).1 (by rw [hcv3z]; norm_num)
  by_cases hBB : blockedB bd [ma, mb] mb = true
  · have hocc1one : e.loc (NGen.cOccIncl n 1) = 1 := hocc1I.mpr hBB
    have hcv2z : e.loc (NGen.cCv2 n 1) = 0 := by
      rcases hcv2_1B with hz | ho
      · exact hz
      · exact absurd (hcv2_1I.mp ho).2.2 (by rw [hocc1one]; norm_num)
    have hc4z := carryZeroFromCv2 hcv2z
    have hlm : landMap bd [ma, mb] mb.frm = mb.frm := landMap_pair_blocked_b bd ma mb hne hBB
    refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
      fun h => absurd h.2 (by rw [hlm]; exact fun q => q rfl)⟩,
      fun h => absurd h (by rw [hc4z]; norm_num)⟩
  · simp only [Bool.not_eq_true] at hBB
    have hocc1zero : e.loc (NGen.cOccIncl n 1) = 0 := by
      rcases hocc1B with hz | ho
      · exact hz
      · exact absurd (hocc1I.mp ho) (by rw [hBB]; exact Bool.false_ne_true)
    by_cases hCB : carAt bd mb.frm = true
    · have hcv2one : e.loc (NGen.cCv2 n 1) = 1 := hcv2_1I.mpr ⟨hsurv, hBnz.mpr hCB, hocc1zero⟩
      have hcarryChar : e.loc (NGen.cCarryV4 n 1) = 1 ↔
          (e.loc (NGen.cNonLeaveV2 n 1) = 0 ∧ e.loc (NGen.cTwoCyc n) = 0) := by
        rw [hcv4I, hcv3I]
        constructor
        · rintro ⟨⟨_, hnl⟩, htc⟩; exact ⟨hnl, htc⟩
        · rintro ⟨hnl, htc⟩; exact ⟨⟨hcv2one, hnl⟩, htc⟩
      have hocc0_zero_iff : e.loc (NGen.cOccIncl n 0) = 0 ↔ blockedB bd [ma, mb] ma = false := by
        constructor
        · intro h0; cases hbb : blockedB bd [ma, mb] ma
          · rfl
          · rw [hocc0I.mpr hbb] at h0; exact absurd h0 (by norm_num)
        · intro hbb; rcases hocc0B with h | h
          · exact h
          · rw [hocc0I.mp h] at hbb; exact Bool.noConfusion hbb
      have hanz_zero_iff : e.loc (NGen.cAnz n) = 0 ↔ carAt bd ma.frm = false := by
        constructor
        · intro h0; cases hca : carAt bd ma.frm
          · rfl
          · rw [hAnz.mpr hca] at h0; exact absurd h0 (by norm_num)
        · intro hca; rcases F.anzB with h | h
          · exact h
          · rw [hAnz.mp h] at hca; exact Bool.noConfusion hca
      have heq2_zero_iff : e.loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0 ↔ ma.to ≠ mb.frm := by
        constructor
        · intro h0 heq; rw [heq2C.mpr heq] at h0; exact absurd h0 (by norm_num)
        · intro hne2; rcases heq2B with h | h
          · exact h
          · exact absurd (heq2C.mp h) hne2
      have hFtProp : e.loc (NGen.cFtV2B n) = 1 ↔
          (mb.to = ma.frm ∧ carAt bd ma.frm = false ∧ blockedB bd [ma, mb] ma = false
            ∧ ma.to ≠ mb.frm) := by
        rw [hftI, heq3C, hanz_zero_iff, hocc0_zero_iff, heq2_zero_iff]
        constructor
        · rintro ⟨e3, hb, _, o0, e2⟩; exact ⟨e3, hb, o0, e2⟩
        · rintro ⟨e3, hb, o0, e2⟩; exact ⟨e3, hb, hsurv, o0, e2⟩
      have hTwoCycProp : e.loc (NGen.cTwoCyc n) = 1 ↔
          (ma.to = mb.frm ∧ mb.to = ma.frm ∧ blockedB bd [ma, mb] ma = false) := by
        rw [htcI, heq2C, heq3C, hocc0_zero_iff]
        constructor
        · rintro ⟨e2, e3, _, o0⟩; exact ⟨e2, e3, o0⟩
        · rintro ⟨e2, e3, o0⟩; exact ⟨e2, e3, hocc1zero, o0⟩
      have hCv2_0Prop : e.loc (NGen.cCv2 n 0) = 1 ↔
          (carAt bd ma.frm = true ∧ blockedB bd [ma, mb] ma = false) := by
        rw [hcv2_0I, hnz0, hAnz, hocc0_zero_iff]
        constructor
        · rintro ⟨_, hc, hb⟩; exact ⟨hc, hb⟩
        · rintro ⟨hc, hb⟩; exact ⟨hsurv, hc, hb⟩
      have hBBp : ¬ (blockedB bd [ma, mb] mb = true) := by rw [hBB]; exact Bool.false_ne_true
      have carryZeroTC : e.loc (NGen.cTwoCyc n) = 1 → e.loc (NGen.cCarryV4 n 1) = 0 := by
        intro h1; rcases hcv4B with hz | ho
        · exact hz
        · exact absurd (hcv4I.mp ho).2 (by rw [h1]; norm_num)
      have carryZeroNL : e.loc (NGen.cNonLeaveV2 n 1) = 1 → e.loc (NGen.cCarryV4 n 1) = 0 := by
        intro h1
        have hcv3z : e.loc (NGen.cCarryV3 n 1) = 0 := by
          rcases hcv3B with hz | ho
          · exact hz
          · exact absurd (hcv3I.mp ho).2 (by rw [h1]; norm_num)
        rcases hcv4B with hz | ho
        · exact hz
        · exact absurd (hcv4I.mp ho).1 (by rw [hcv3z]; norm_num)
      have nlZero : (e.loc (NGen.cLandNzV2 n 1) = 0 ∨ e.loc (NGen.cCv2 n 0) = 1)
          → e.loc (NGen.cNonLeaveV2 n 1) = 0 := by
        intro h; rcases hnlB with hz | ho
        · exact hz
        · obtain ⟨ha, hb⟩ := hnlI.mp ho
          rcases h with h | h
          · rw [h] at ha; exact absurd ha (by norm_num)
          · rw [h] at hb; exact absurd hb (by norm_num)
      have nlOne : e.loc (NGen.cLandNzV2 n 1) = 1 → e.loc (NGen.cCv2 n 0) = 0
          → e.loc (NGen.cNonLeaveV2 n 1) = 1 := fun a b => hnlI.mpr ⟨a, b⟩
      have tcZero : ¬ (ma.to = mb.frm ∧ mb.to = ma.frm ∧ blockedB bd [ma, mb] ma = false)
          → e.loc (NGen.cTwoCyc n) = 0 := by
        intro h; rcases htcB with hz | ho
        · exact hz
        · exact absurd (hTwoCycProp.mp ho) h
      have landOf0 : e.loc (NGen.cFtV2B n) = 0 →
          (e.loc (NGen.cLandNzV2 n 1) = 1 ↔ carAt bd mb.to = true) := by
        intro hft0; rw [hlnzI]; simp [hft0]
      have landOf1 : e.loc (NGen.cFtV2B n) = 1 →
          (e.loc (NGen.cLandNzV2 n 1) = 1 ↔ carAt bd ma.to = true) := by
        intro hft1; rw [hlnzI]; simp [hft1]
      by_cases hEBA : mb.to = ma.frm
      · by_cases hBA : blockedB bd [ma, mb] ma = true
        · have hft0 : e.loc (NGen.cFtV2B n) = 0 := by
            rcases hftB with h | h
            · exact h
            · exact absurd (hFtProp.mp h).2.2.1 (by rw [hBA]; decide)
          have hcv2_0z : e.loc (NGen.cCv2 n 0) = 0 := by
            rcases hcv2_0B with h | h
            · exact h
            · exact absurd (hCv2_0Prop.mp h).2 (by rw [hBA]; decide)
          have hland : (if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to) = mb.to := by
            simp [hft0]
          by_cases hCA : carAt bd ma.frm = true
          · have hlnz1 : e.loc (NGen.cLandNzV2 n 1) = 1 := by
              rw [landOf0 hft0, hEBA]; exact hCA
            have hnl1 : e.loc (NGen.cNonLeaveV2 n 1) = 1 := nlOne hlnz1 hcv2_0z
            have hc4z := carryZeroNL hnl1
            have hLM : landMap bd [ma, mb] mb.frm = mb.frm := by
              rw [landMap_pair_b bd ma mb hne hlegA hlegB,
                if_neg hBBp, if_pos hEBA, if_pos hBA, if_pos hCA]
            refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
              fun h => absurd hLM h.2⟩, fun h => absurd h (by rw [hc4z]; norm_num)⟩
          · have hCAf : carAt bd ma.frm = false := by simpa using hCA
            have hlnz0 : e.loc (NGen.cLandNzV2 n 1) = 0 := by
              rcases hlnzB with h | h
              · exact h
              · rw [landOf0 hft0, hEBA, hCAf] at h; exact absurd h Bool.false_ne_true
            have hnl0 := nlZero (Or.inl hlnz0)
            have htc0 := tcZero (fun ⟨_, _, hb⟩ => by rw [hBA] at hb; exact Bool.noConfusion hb)
            have hc41 : e.loc (NGen.cCarryV4 n 1) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
            have hLM : landMap bd [ma, mb] mb.frm = mb.to := by
              rw [landMap_pair_b bd ma mb hne hlegA hlegB,
                if_neg hBBp, if_pos hEBA, if_pos hBA, if_neg hCA]
            refine ⟨⟨fun _ => ⟨hCB, by rw [hLM]; exact fun q => hlegB q.symm⟩, fun _ => hc41⟩,
              fun _ => hland.trans hLM.symm⟩
        · simp only [Bool.not_eq_true] at hBA
          by_cases hEAB : ma.to = mb.frm
          · have htc1 : e.loc (NGen.cTwoCyc n) = 1 := hTwoCycProp.mpr ⟨hEAB, hEBA, hBA⟩
            have hc4z := carryZeroTC htc1
            have hLM : landMap bd [ma, mb] mb.frm = mb.frm := by
              rw [landMap_pair_b bd ma mb hne hlegA hlegB,
                if_neg hBBp, if_pos hEBA, if_neg (by rw [hBA]; exact Bool.false_ne_true),
                if_pos hEAB]
            refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
              fun h => absurd hLM h.2⟩, fun h => absurd h (by rw [hc4z]; norm_num)⟩
          · have htc0 := tcZero (fun ⟨he2, _, _⟩ => hEAB he2)
            by_cases hCA : carAt bd ma.frm = true
            · have hft0 : e.loc (NGen.cFtV2B n) = 0 := by
                rcases hftB with h | h
                · exact h
                · exact absurd (hFtProp.mp h).2.1 (by rw [hCA]; decide)
              have hcv2_0one : e.loc (NGen.cCv2 n 0) = 1 := hCv2_0Prop.mpr ⟨hCA, hBA⟩
              have hnl0 := nlZero (Or.inr hcv2_0one)
              have hc41 : e.loc (NGen.cCarryV4 n 1) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
              have hland : (if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to) = mb.to := by
                simp [hft0]
              have hLM : landMap bd [ma, mb] mb.frm = mb.to := by
                rw [landMap_pair_b bd ma mb hne hlegA hlegB,
                  if_neg hBBp, if_pos hEBA, if_neg (by rw [hBA]; exact Bool.false_ne_true),
                  if_neg hEAB, if_pos hCA]
              refine ⟨⟨fun _ => ⟨hCB, by rw [hLM]; exact fun q => hlegB q.symm⟩, fun _ => hc41⟩,
                fun _ => hland.trans hLM.symm⟩
            · have hCAf : carAt bd ma.frm = false := by simpa using hCA
              have hft1 : e.loc (NGen.cFtV2B n) = 1 := hFtProp.mpr ⟨hEBA, hCAf, hBA, hEAB⟩
              have hnsA : ([ma, mb].any (fun m' => m'.frm == ma.to)) = false := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
                  beq_eq_false_iff_ne]
                exact ⟨hlegA, fun q => hEAB q.symm⟩
              have hcarDa : carAt bd ma.to = false :=
                carAt_to_false_of_not_blocked bd [ma, mb] ma hBA hnsA
              have hlnz0 : e.loc (NGen.cLandNzV2 n 1) = 0 := by
                rcases hlnzB with h | h
                · exact h
                · rw [landOf1 hft1] at h; rw [hcarDa] at h; exact absurd h Bool.false_ne_true
              have hnl0 := nlZero (Or.inl hlnz0)
              have hc41 : e.loc (NGen.cCarryV4 n 1) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
              have hland : (if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to) = ma.to := by
                simp [hft1]
              have hLM : landMap bd [ma, mb] mb.frm = ma.to := by
                rw [landMap_pair_b bd ma mb hne hlegA hlegB,
                  if_neg hBBp, if_pos hEBA, if_neg (by rw [hBA]; exact Bool.false_ne_true),
                  if_neg hEAB, if_neg hCA]
              refine ⟨⟨fun _ => ⟨hCB, by rw [hLM]; exact hEAB⟩, fun _ => hc41⟩,
                fun _ => hland.trans hLM.symm⟩
      · have hft0 : e.loc (NGen.cFtV2B n) = 0 := by
          rcases hftB with h | h
          · exact h
          · exact absurd (hFtProp.mp h).1 hEBA
        have hnsB : ([ma, mb].any (fun m' => m'.frm == mb.to)) = false := by
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
            beq_eq_false_iff_ne]
          exact ⟨fun q => hEBA q.symm, hlegB⟩
        have hcarDb : carAt bd mb.to = false :=
          carAt_to_false_of_not_blocked bd [ma, mb] mb hBB hnsB
        have hlnz0 : e.loc (NGen.cLandNzV2 n 1) = 0 := by
          rcases hlnzB with h | h
          · exact h
          · rw [landOf0 hft0] at h; rw [hcarDb] at h; exact absurd h Bool.false_ne_true
        have hnl0 := nlZero (Or.inl hlnz0)
        have htc0 := tcZero (fun ⟨_, he3, _⟩ => hEBA he3)
        have hc41 : e.loc (NGen.cCarryV4 n 1) = 1 := hcarryChar.mpr ⟨hnl0, htc0⟩
        have hland : (if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to) = mb.to := by
          simp [hft0]
        have hLM : landMap bd [ma, mb] mb.frm = mb.to := by
          rw [landMap_pair_b bd ma mb hne hlegA hlegB, if_neg hBBp, if_neg hEBA]
        refine ⟨⟨fun _ => ⟨hCB, by rw [hLM]; exact fun q => hlegB q.symm⟩, fun _ => hc41⟩,
          fun _ => hland.trans hLM.symm⟩
    · have hbnzzero : e.loc (NGen.cBnz n) = 0 := by
        rcases F.bnzB with hz | ho
        · exact hz
        · exact absurd (hBnz.mp ho) hCB
      have hcv2z : e.loc (NGen.cCv2 n 1) = 0 := by
        rcases hcv2_1B with hz | ho
        · exact hz
        · exact absurd (hcv2_1I.mp ho).2.1 (by rw [hnz1, hbnzzero]; norm_num)
      have hc4z := carryZeroFromCv2 hcv2z
      refine ⟨⟨fun h => absurd h (by rw [hc4z]; norm_num),
        fun h => absurd h.1 hCB⟩,
        fun h => absurd h (by rw [hc4z]; norm_num)⟩

end LandCorr

/-! ## §22b — `mergeV2N_of_sat`: the confluence bit `cMergeV2`, semantically extracted.

`cMergeV2 = cMc1V2 · cNotIdentV2 = (cBothCarryV2 · cResEqV2) · (1 − cIdentV2)`, with
`cBothCarryV2 = cCv2 0 · cCv2 1`, `cIdentV2 = eq_ff · eq_tt` (sources coincide AND raw dests
coincide, the identical-move exception). So the merge conflict fires exactly when BOTH pieces carry
(in the corrected inclusive-occlusion sense), their CORRECTED landings coincide (`cResEqV2 = 1`), and
the pair is NOT the identical move. Pure gate algebra over the twelve-gate `resV2LogicTail` (§14). -/
section MergeV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`mergeV2N_of_sat`.** The confluence bit is boolean and is `1` iff both pieces carry, the
corrected landings coincide (`cResEqV2 = 1`), and the pair is not the identical move
(`eq_ff = 0 ∨ eq_tt = 0`). -/
theorem mergeV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (heqff : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (heqtt : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hcv2a : (envAt t i).loc (NGen.cCv2 n 0) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 0) = 1)
    (hcv2b : (envAt t i).loc (NGen.cCv2 n 1) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 1) = 1)
    (hreseq : (envAt t i).loc (NGen.cResEqV2 n) = 0 ∨ (envAt t i).loc (NGen.cResEqV2 n) = 1) :
    ((envAt t i).loc (NGen.cMergeV2 n) = 0 ∨ (envAt t i).loc (NGen.cMergeV2 n) = 1)
      ∧ ((envAt t i).loc (NGen.cMergeV2 n) = 1 ↔
          ((envAt t i).loc (NGen.cCv2 n 0) = 1 ∧ (envAt t i).loc (NGen.cCv2 n 1) = 1
            ∧ (envAt t i).loc (NGen.cResEqV2 n) = 1
            ∧ ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
                ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0))) := by
  set e := envAt t i with he
  -- cIdentV2 = eq_ff · eq_tt  (gate 0)
  have hident : e.loc (NGen.cIdentV2 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) :=
    prodN_of_sat hsat hc i hi (NGen.cIdentV2 n) (NGen.cEqBit n (NGen.eqBase n 0))
      (NGen.cEqBit n (NGen.eqBase n 1))
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n); exact List.mem_cons_self)) heqff heqtt
  have hidentB : e.loc (NGen.cIdentV2 n) = 0 ∨ e.loc (NGen.cIdentV2 n) = 1 := by
    rcases heqff with a | a <;> rcases heqtt with b | b <;> rw [hident, a, b] <;> norm_num
  -- cBothCarryV2 = cCv2 0 · cCv2 1  (gate 1)
  have hbc : e.loc (NGen.cBothCarryV2 n) = e.loc (NGen.cCv2 n 0) * e.loc (NGen.cCv2 n 1) :=
    prodN_of_sat hsat hc i hi (NGen.cBothCarryV2 n) (NGen.cCv2 n 0) (NGen.cCv2 n 1)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ List.mem_cons_self)) hcv2a hcv2b
  have hbcB : e.loc (NGen.cBothCarryV2 n) = 0 ∨ e.loc (NGen.cBothCarryV2 n) = 1 := by
    rcases hcv2a with a | a <;> rcases hcv2b with b | b <;> rw [hbc, a, b] <;> norm_num
  -- cMc1V2 = cBothCarryV2 · cResEqV2  (gate 2)
  have hmc1 : e.loc (NGen.cMc1V2 n) = e.loc (NGen.cBothCarryV2 n) * e.loc (NGen.cResEqV2 n) :=
    prodN_of_sat hsat hc i hi (NGen.cMc1V2 n) (NGen.cBothCarryV2 n) (NGen.cResEqV2 n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      hbcB hreseq
  have hmc1B : e.loc (NGen.cMc1V2 n) = 0 ∨ e.loc (NGen.cMc1V2 n) = 1 := by
    rcases hbcB with a | a <;> rcases hreseq with b | b <;> rw [hmc1, a, b] <;> norm_num
  -- cNotIdentV2 = 1 − cIdentV2  (gate 3)
  have hni : e.loc (NGen.cNotIdentV2 n) = 1 - e.loc (NGen.cIdentV2 n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNotIdentV2 n) (NGen.cIdentV2 n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                       (List.mem_cons_of_mem _ List.mem_cons_self)))) hidentB
  have hniB : e.loc (NGen.cNotIdentV2 n) = 0 ∨ e.loc (NGen.cNotIdentV2 n) = 1 := by
    rcases hidentB with a | a <;> rw [hni, a] <;> norm_num
  -- cMergeV2 = cMc1V2 · cNotIdentV2  (gate 4)
  have hmerge : e.loc (NGen.cMergeV2 n) = e.loc (NGen.cMc1V2 n) * e.loc (NGen.cNotIdentV2 n) :=
    prodN_of_sat hsat hc i hi (NGen.cMergeV2 n) (NGen.cMc1V2 n) (NGen.cNotIdentV2 n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                       (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
      hmc1B hniB
  refine ⟨?_, ?_⟩
  · rcases hmc1B with a | a <;> rcases hniB with b | b <;> rw [hmerge, a, b] <;> norm_num
  · rw [hmerge, hmc1, hni, hbc, hident]
    rcases hcv2a with a | a <;> rcases hcv2b with b | b <;> rcases hreseq with c | c <;>
      rcases heqff with d | d <;> rcases heqtt with f | f <;> rw [a, b, c, d, f] <;> simp

end MergeV2

/-! ## §22c — `resEqV2CoordN_of_sat`: the confluence comparator `cResEqV2` IS the equality of the two
CORRECTED landing squares.

`cResEqV2` is an `eq_coords` over the two INTERPOLATED corrected-landing coordinate columns
(`cDestV2X/Y 0`, driven by `cFtV2A`; `cDestV2X/Y 1`, driven by `cFtV2B`). Threading the four
`destHead`-pinning gates (`cDestV2 = to_own + ft·(to_other − to_own)`) through the boolean-`ft`
selection and the `Int.toNat` coordinate bridge, the raw-integer equality the comparator tests IS the
`Coord` equality of the two selected landings — the LANDING half the confluence bit `cMergeV2`
consumes (§22b). -/
section ResEqV2Coord
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **The `cDestV2` destHead pin.** A `cgH ((Head.lin 1 col).append ((destHead own other ftc).scale
(-1)))` gate pins the interpolated landing column `col` to the boolean-`ftc` selection between the two
witnessed coordinate columns — `col = if ftc = 1 then other else own`. -/
theorem destV2PinN (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (col own other ftc : Nat)
    (hmem : cgH ((Head.lin 1 col).append ((destHead own other ftc).scale (-1)))
        ∈ (automataflResolveDescN n).constraints)
    (hft : (envAt t i).loc ftc = 0 ∨ (envAt t i).loc ftc = 1) :
    (envAt t i).loc col
      = if (envAt t i).loc ftc = 1 then (envAt t i).loc other else (envAt t i).loc own := by
  have hg := rgateHN hsat i hi hmem
  rw [headToExpr_eval, evalH_append, evalH_lin, evalH_scale,
    AutomataflResolveCapstone.destHead_select _ _ _ _ hft] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
  split <;> exact canon_loc hc i _

/-- **`resEqV2CoordN_of_sat`.** The corrected-landing comparator `cResEqV2` is `1` exactly when the two
`cFtV2`-selected landing squares coincide AS COORDS: `(if cFtV2A then mb.to else ma.to) = (if cFtV2B
then ma.to else mb.to)`. -/
theorem resEqV2CoordN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hfta : (envAt t i).loc (NGen.cFtV2A n) = 0 ∨ (envAt t i).loc (NGen.cFtV2A n) = 1)
    (hftb : (envAt t i).loc (NGen.cFtV2B n) = 0 ∨ (envAt t i).loc (NGen.cFtV2B n) = 1) :
    ((envAt t i).loc (NGen.cResEqV2 n) = 0 ∨ (envAt t i).loc (NGen.cResEqV2 n) = 1)
      ∧ ((envAt t i).loc (NGen.cResEqV2 n) = 1 ↔
      (if (envAt t i).loc (NGen.cFtV2A n) = 1
        then (moveDecodeN n (envAt t i) 1).to else (moveDecodeN n (envAt t i) 0).to)
      = (if (envAt t i).loc (NGen.cFtV2B n) = 1
        then (moveDecodeN n (envAt t i) 0).to else (moveDecodeN n (envAt t i) 1).to)) := by
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  set e := envAt t i with he
  -- the four `destHead` pins
  have px0 : e.loc (NGen.cDestV2X n 0)
      = if e.loc (NGen.cFtV2A n) = 1 then e.loc (NGen.cTx n (NGen.mvBase n 1))
        else e.loc (NGen.cTx n (NGen.mvBase n 0)) :=
    destV2PinN hsat hc i hi (NGen.cDestV2X n 0) (NGen.cTx n (NGen.mvBase n 0))
      (NGen.cTx n (NGen.mvBase n 1)) (NGen.cFtV2A n)
      (mem_resolve_of_mem_resolvableV2 (List.mem_append_left _ (List.mem_append_left _
        List.mem_cons_self))) hfta
  have py0 : e.loc (NGen.cDestV2Y n 0)
      = if e.loc (NGen.cFtV2A n) = 1 then e.loc (NGen.cTy n (NGen.mvBase n 1))
        else e.loc (NGen.cTy n (NGen.mvBase n 0)) :=
    destV2PinN hsat hc i hi (NGen.cDestV2Y n 0) (NGen.cTy n (NGen.mvBase n 0))
      (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFtV2A n)
      (mem_resolve_of_mem_resolvableV2 (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) hfta
  have px1 : e.loc (NGen.cDestV2X n 1)
      = if e.loc (NGen.cFtV2B n) = 1 then e.loc (NGen.cTx n (NGen.mvBase n 0))
        else e.loc (NGen.cTx n (NGen.mvBase n 1)) :=
    destV2PinN hsat hc i hi (NGen.cDestV2X n 1) (NGen.cTx n (NGen.mvBase n 1))
      (NGen.cTx n (NGen.mvBase n 0)) (NGen.cFtV2B n)
      (mem_resolve_of_mem_resolvableV2 (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hftb
  have py1 : e.loc (NGen.cDestV2Y n 1)
      = if e.loc (NGen.cFtV2B n) = 1 then e.loc (NGen.cTy n (NGen.mvBase n 0))
        else e.loc (NGen.cTy n (NGen.mvBase n 1)) :=
    destV2PinN hsat hc i hi (NGen.cDestV2Y n 1) (NGen.cTy n (NGen.mvBase n 1))
      (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFtV2B n)
      (mem_resolve_of_mem_resolvableV2 (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)))))) hftb
  -- the four coordinate bounds (both `if` branches are witnessed coords in `[0, n)`)
  have bx0 : 0 ≤ e.loc (NGen.cDestV2X n 0) ∧ e.loc (NGen.cDestV2X n 0) ≤ (n : ℤ) - 1 := by
    rw [px0]; split
    · exact hM _ htxb
    · exact hM _ htxa
  have by0 : 0 ≤ e.loc (NGen.cDestV2Y n 0) ∧ e.loc (NGen.cDestV2Y n 0) ≤ (n : ℤ) - 1 := by
    rw [py0]; split
    · exact hM _ htyb
    · exact hM _ htya
  have bx1 : 0 ≤ e.loc (NGen.cDestV2X n 1) ∧ e.loc (NGen.cDestV2X n 1) ≤ (n : ℤ) - 1 := by
    rw [px1]; split
    · exact hM _ htxa
    · exact hM _ htxb
  have by1 : 0 ≤ e.loc (NGen.cDestV2Y n 1) ∧ e.loc (NGen.cDestV2Y n 1) ≤ (n : ℤ) - 1 := by
    rw [py1]; split
    · exact hM _ htya
    · exact hM _ htyb
  -- the two selected landings, as `⟨toNat, toNat⟩` of the pinned coordinate columns
  have keyA : (if e.loc (NGen.cFtV2A n) = 1
        then (moveDecodeN n e 1).to else (moveDecodeN n e 0).to)
      = (⟨(e.loc (NGen.cDestV2X n 0)).toNat, (e.loc (NGen.cDestV2Y n 0)).toNat⟩ : Coord) := by
    rw [px0, py0]; by_cases h : e.loc (NGen.cFtV2A n) = 1 <;> simp [h, moveDecodeN]
  have keyB : (if e.loc (NGen.cFtV2B n) = 1
        then (moveDecodeN n e 0).to else (moveDecodeN n e 1).to)
      = (⟨(e.loc (NGen.cDestV2X n 1)).toNat, (e.loc (NGen.cDestV2Y n 1)).toNat⟩ : Coord) := by
    rw [px1, py1]; by_cases h : e.loc (NGen.cFtV2B n) = 1 <;> simp [h, moveDecodeN]
  -- the comparator, extracted over the raw integer columns
  obtain ⟨hb, hiff⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cDestV2X n 0) (NGen.cDestV2Y n 0)
    (NGen.cDestV2X n 1) (NGen.cDestV2Y n 1) (NGen.resEqV2Base n) ((n : ℤ) - 1)
    (by have := W.base.sq999; linarith) bx0 by0 bx1 by1
    (fun h => mem_resolve_of_mem_resolvableV2 (List.mem_append_left _ (List.mem_append_right _ h)))
  have hcre : (envAt t i).loc (NGen.cResEqV2 n)
      = (envAt t i).loc (NGen.cEqBit n (NGen.resEqV2Base n)) := rfl
  refine ⟨by rw [hcre, ← he]; exact hb, ?_⟩
  rw [hcre, ← he, hiff, keyA, keyB,
    Coord.mk.injEq, AutomataflResolveCapstone.toNat_injN bx0.1 bx1.1,
    AutomataflResolveCapstone.toNat_injN by0.1 by1.1]

/-- **`mergeV2_zero_of_distinctDest`.** On a surviving round with distinct raw destinations the
confluence bit vanishes: if both pieces carry (`cCv2 = 1`) the OTHER piece being occupied forces
`cFtV2 = 0` for each, so the two corrected landings are exactly `ma.to` / `mb.to`, which differ —
so the comparator `cResEqV2 = 0` and hence `cMergeV2 = 0`. (No `hne`; a `roundStep`-clean, non-fork
distinct-dest pair never merges.) -/
theorem mergeV2_zero_of_distinctDest
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hdd : (moveDecodeN n (envAt t i) 0).to ≠ (moveDecodeN n (envAt t i) 1).to) :
    (envAt t i).loc (NGen.cMergeV2 n) = 0 := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  set e := envAt t i with he
  -- inclusive-occlusion booleans
  have hocc0B : e.loc (NGen.cOccIncl n 0) = 0 ∨ e.loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : e.loc (NGen.cOccIncl n 1) = 0 ∨ e.loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  -- the two pattern bits (eq_ff / eq_tt) and the two crossing bits (eq2 / eq3), as booleans
  obtain ⟨heqffB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨heqttB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨heq2B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  -- corrected flow-through bits (booleans + iffs), corrected carry seeds (booleans + iffs)
  obtain ⟨hftaB, hftaI⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hftbB, hftbI⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  -- the comparator and the merge bit
  obtain ⟨hreseqB, hreseqI⟩ := resEqV2CoordN_of_sat hsat hc i hi W hftaB hftbB
  obtain ⟨hmergeB, hmergeI⟩ := mergeV2N_of_sat hsat hc i hi heqffB heqttB hcv2_0B hcv2_1B hreseqB
  -- if the merge fired, both carry, so both flow-through bits are 0, so landings are `ma.to`/`mb.to`
  rcases hmergeB with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨hc0, hc1, hre1, -⟩ := hmergeI.mp h1
    -- cCv2 1 = 1 ⇒ cBnz = 1 ⇒ cFtV2A = 0
    have hbnz1 : e.loc (NGen.cBnz n) = 1 := (hcv2_1I.mp hc1).2.1
    have hfta0 : e.loc (NGen.cFtV2A n) = 0 := by
      rcases hftaB with h | h
      · exact h
      · exact absurd (hftaI.mp h).2.1 (by rw [hbnz1]; norm_num)
    -- cCv2 0 = 1 ⇒ cAnz = 1 ⇒ cFtV2B = 0
    have hanz1 : e.loc (NGen.cAnz n) = 1 := (hcv2_0I.mp hc0).2.1
    have hftb0 : e.loc (NGen.cFtV2B n) = 0 := by
      rcases hftbB with h | h
      · exact h
      · exact absurd (hftbI.mp h).2.1 (by rw [hanz1]; norm_num)
    -- so the two corrected landings are the raw destinations, which are distinct
    have hland := hreseqI.mp hre1
    rw [if_neg (by rw [hfta0]; norm_num), if_neg (by rw [hftb0]; norm_num)] at hland
    exact hdd hland

end ResEqV2Coord


/-! ## §23 — THE CLASH-CASE CELL: a fork/collide row (`surv = 0`) leaves the FINAL board = OLD.

On a clashing round the selection block sets `cSurv = 0` (`selectionN_of_sat.survIff`), so every V4
carry seed `cCv2` is `0`, hence every `cCarryV4` is `0`, hence the write-cell polynomial collapses to
`old` and — through the `cResolvableV2`-gate telescoping to the identity — `cMidV4 = old`. This is the
board `AutomataflRules.roundStep` re-enters with on a clash (board unchanged). Proved via the BOARD
CELL directly, NOT the false `cResolvableV2 = resolvableB` predicate biconditional. -/
section Clash
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **THE CLASH-CASE CELL (surv = 0).** On a fork/collide row the selection kills survival
(`cSurv = 0`), so every V4 carry vanishes and the emitted FINAL board cell IS the OLD cell —
proved through the BOARD-CELL equality directly (no `cResolvableV2 = resolvableB` predicate route). -/
theorem midV4_old_of_surv_zero
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0) (c : Nat) (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cMidV4 n c) = (envAt t i).loc (NGen.old n c) := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  -- eq bits (needed only as booleans for ftV2AN / twoCycN)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  obtain ⟨heq2B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  -- ftV2A / ftV2B booleans → landNzV2 booleans → nonLeaveV2 booleans
  obtain ⟨hftaB, -⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inl hsurv)
  obtain ⟨hftbB, -⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inl hsurv)
  obtain ⟨hlnzaB, -⟩ := landNzV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB
    htxa htya htxb htyb
  obtain ⟨hlnzbB, -⟩ := landNzV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB
    htxb htyb htxa htya
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inl hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inl hsurv) F.bnzB hocc1B
  obtain ⟨hnlaB, -⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 0 (by norm_num) hlnzaB hcv2_1B
  obtain ⟨hnlbB, -⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 1 (by norm_num) hlnzbB hcv2_0B
  obtain ⟨hcv3aB, hcv3aI⟩ := carryV3ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv2_0B hnlaB
  obtain ⟨hcv3bB, hcv3bI⟩ := carryV3ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv2_1B hnlbB
  obtain ⟨htcB, -⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  obtain ⟨hcv4aB, hcv4aI⟩ := carryV4ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv3aB htcB
  obtain ⟨hcv4bB, hcv4bI⟩ := carryV4ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv3bB htcB
  -- surv = 0 ⇒ both seed carries are 0 ⇒ both V4 carries are 0
  have hcv2_0z : (envAt t i).loc (NGen.cCv2 n 0) = 0 := by
    rcases hcv2_0B with h | h
    · exact h
    · exact absurd (hcv2_0I.mp h).1 (by rw [hsurv]; norm_num)
  have hcv2_1z : (envAt t i).loc (NGen.cCv2 n 1) = 0 := by
    rcases hcv2_1B with h | h
    · exact h
    · exact absurd (hcv2_1I.mp h).1 (by rw [hsurv]; norm_num)
  have hcv3az : (envAt t i).loc (NGen.cCarryV3 n 0) = 0 := by
    rcases hcv3aB with h | h
    · exact h
    · exact absurd (hcv3aI.mp h).1 (by rw [hcv2_0z]; norm_num)
  have hcv3bz : (envAt t i).loc (NGen.cCarryV3 n 1) = 0 := by
    rcases hcv3bB with h | h
    · exact h
    · exact absurd (hcv3bI.mp h).1 (by rw [hcv2_1z]; norm_num)
  have hcc0 : (envAt t i).loc (NGen.carryV4Col n 0) = 0 := by
    rcases hcv4aB with h | h
    · exact h
    · exact absurd (hcv4aI.mp h).1 (by rw [hcv3az]; norm_num)
  have hcc1 : (envAt t i).loc (NGen.carryV4Col n 1) = 0 := by
    rcases hcv4bB with h | h
    · exact h
    · exact absurd (hcv4bI.mp h).1 (by rw [hcv3bz]; norm_num)
  -- with both carries 0 the write-cell polynomial collapses to `old`
  have hcw : (envAt t i).loc (NGen.cWBoardV4 n c) ≡ (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
    have hwb := writeCellV4N_of_sat hsat i hi c (c / n) (c % n) rfl rfl hcK
    rw [hcc0, hcc1] at hwb
    calc (envAt t i).loc (NGen.cWBoardV4 n c)
        ≡ _ [ZMOD 2013265921] := hwb
      _ = (envAt t i).loc (NGen.old n c) := by ring
  -- the resolvable-gated mid cell is then `old` mod p, hence equal by alphabet canonicity
  have hmid := midV4CellN_of_sat hsat i hi c hcK
  have key : (envAt t i).loc (NGen.cMidV4 n c) ≡ (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
    calc (envAt t i).loc (NGen.cMidV4 n c)
        ≡ (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV4 n c)
          + (envAt t i).loc (NGen.old n c)
          - (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
          [ZMOD 2013265921] := hmid
      _ ≡ (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
          + (envAt t i).loc (NGen.old n c)
          - (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
          [ZMOD 2013265921] :=
        (Int.ModEq.mul_left _ hcw).add_right _ |>.sub_right _
      _ = (envAt t i).loc (NGen.old n c) := by ring
  exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) key

end Clash

/-! ## §24 — THE ASSEMBLY CONNECTIVES: the `surv ↔ clash` bridge and the clash board branch.

Two connectives the round-board capstone rides on:

* `surv_iff_clash_empty_of_sat` — the circuit's `cSurv = 1` bit IS the reference's "no fork/collide"
  (`clashCoords = []`). This is `ResolveFactsN.survIff` composed, arm for arm, with the spec-side
  `AutomataflRules.clashCoords_pair_iff` (fork ⟺ shared source / distinct dest; collide ⟺ shared
  dest / distinct non-vacuum sources).
* `midV4_cell_old_of_surv_zero` — on a clashing round (`surv = 0`), the decoded FINAL board cell IS
  the decoded OLD cell (§23 lifted through `codeToParticle`). This is the board `roundStep` re-enters
  with on a clash: `.again { board := rs.board … }` — the board is unchanged. -/
section Assembly
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (clashCoords carAt clashCoords_pair_iff)

/-- The decoded OLD board cell at an in-bounds coordinate IS `codeToParticle` of its `old` column. -/
theorem oldCell_decode (x y : Nat) (e : VmRowEnv) (hx : x < n) (hy : y < n) :
    codeToParticle (e.loc (NGen.old n (y * n + x)))
      = (boardDecodeOldN n e).cellAt ⟨x, y⟩ := by
  simp only [boardDecodeOldN, Board.cellAt]
  exact (if_pos (show x < n ∧ y < n from ⟨hx, hy⟩)).symm

/-- **THE SURV↔CLASH BRIDGE (circuit side).** Off a satisfying, canonical row, the survival bit is
`1` exactly when the reference round has no fork/collide conflict — `cSurv = 1 ↔ clashCoords = []`. -/
theorem surv_iff_clash_empty_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n) :
    (envAt t i).loc (NGen.cSurv n) = 1 ↔
      clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] = [] := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  have hbr := clashCoords_pair_iff bd ma mb
  have hcaA : carAt bd ma.frm = true ↔ (bd.cellAt ma.frm).isVacuum = false := by simp [carAt]
  have hcaB : carAt bd mb.frm = true ↔ (bd.cellAt mb.frm).isVacuum = false := by simp [carAt]
  rw [F.survIff]
  constructor
  · intro hnd
    by_contra hcl
    apply hnd
    rcases hbr.mp hcl with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hcaA.mp h3, hcaB.mp h4⟩
  · intro hcl hd
    refine (hbr.mpr ?_) hcl
    rcases hd with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hcaA.mpr h3, hcaB.mpr h4⟩

/-- **THE CLASH BOARD BRANCH.** On a clashing round (`surv = 0`) the decoded FINAL board cell IS the
decoded OLD cell — the board `roundStep` re-enters with unchanged. §23 lifted through the alphabet. -/
theorem midV4_cell_old_of_surv_zero
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0) (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (boardDecodeOldN n (envAt t i)).cellAt ⟨x, y⟩ := by
  have hcK : y * n + x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (y + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hexp : (y + 1) * n = y * n + n := by ring
    omega
  rw [midV4_old_of_surv_zero hsat hc i hi W hsurv (y * n + x) hcK]
  exact oldCell_decode x y (envAt t i) hx hy

end Assembly


/-! ## §25 — THE CLEAN DISTINCT BOARD CELL: the FINAL board cell IS the VALIDATED `resolveMoves` cell.

On a surviving round with distinct decoded sources AND distinct decoded destinations (the "clean
distinct" class), the decoded FINAL board cell `cMidV4` IS the reference `AutomataflRules.resolveMoves`
cell — the new `midCell_of_facts` against the VALIDATED game. Threads:

* §22 `landV4CorrespondenceA/B` — `cCarryV4 which = 1 ⟺ piece `which` is a reference MOVER, and its
  emitted landing IS `landMap`;
* §22b/c `mergeV2_zero_of_distinctDest` + §14 `resolvableV2ArithN` — `cResolvableV2` collapses either
  to `1` (telescoping `cMidV4 = cWBoardV4`) OR to `0` on the STUCK sub-case (A carries but is pinned
  behind a non-leaving/blocked B), where BOTH pieces are non-movers so both `cWBoardV4` and the
  reference board are unchanged — so `cMidV4 ≡ cWBoardV4` UNCONDITIONALLY;
* `AutomataflResolveRefine.cellAlgebra` — the degree-7 board-update collapse to the four-indicator
  if-tree;
* §16 `dstIndV2N` + `ResolveFactsN.srcInd` + `paVal`/`pbVal` — the emitted one-hots and source
  particles;
* the spec's `resolveMoves_cell_pair` + `arrivalAt_pair` — the reference arrival form.

NOTE (proof-strategy correction, not a wound): `cResolvableV2 = 1` is NOT universal on the clean
distinct class. The STUCK arm (A non-vacuum, not inclusive-blocked, but landing on an occupied square
whose occupant B is itself blocked/non-leaving, with distinct dests) has `cResolvableV2 = 0`; there
BOTH `cCarryV4` are `0`, so `cWBoardV4 = old` and the reference `movers = []`, and both boards equal
`old`. The `cMidV4 ≡ cWBoardV4` step below handles both `cResolvableV2` polarities. -/
section CleanCell
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (carAt landMap movers resolveMoves arrivalAt memB memB_iff
  mem_movers_pair resolveMoves_cell_pair arrivalAt_pair)

/-- **THE CLEAN DISTINCT BOARD CELL.** On a surviving round with distinct decoded sources and distinct
decoded destinations, the decoded FINAL board cell IS the reference `resolveMoves` cell, at every
in-bounds coordinate, at arbitrary board size `n`. -/
theorem cleanDistinctBoardCell
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hne : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm)
    (hdd : (moveDecodeN n (envAt t i) 0).to ≠ (moveDecodeN n (envAt t i) 1).to)
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (resolveMoves (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  -- ============ gather every fact (about `envAt t i`), then fold with `set` ============
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  have hlegA : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).to := F.validA.1
  have hlegB : (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).to := F.validB.1
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  -- pattern bits (booleans)
  obtain ⟨heqffB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨heqttB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨heq2B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  -- inclusive occlusion booleans
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  -- flow-through booleans
  obtain ⟨hftaB, -⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hftbB, -⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  -- landing-occupancy booleans
  obtain ⟨hlnzaB, -⟩ := landNzV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB
    htxa htya htxb htyb
  obtain ⟨hlnzbB, -⟩ := landNzV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB
    htxb htyb htxa htya
  -- corrected carry seeds
  obtain ⟨hcv2_0B, -⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, -⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  -- corrected non-leaver bits
  obtain ⟨hnlaB, hnlaI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 0 (by norm_num) hlnzaB hcv2_1B
  obtain ⟨hnlbB, hnlbI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 1 (by norm_num) hlnzbB hcv2_0B
  -- V3 carries
  obtain ⟨hcv3aB, hcv3aI⟩ := carryV3ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv2_0B hnlaB
  obtain ⟨hcv3bB, hcv3bI⟩ := carryV3ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv2_1B hnlbB
  -- 2-cycle detector + V4 carries
  obtain ⟨htcB, -⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  obtain ⟨hcv4aB, hcv4aI⟩ := carryV4ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv3aB htcB
  obtain ⟨hcv4bB, hcv4bI⟩ := carryV4ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv3bB htcB
  -- confluence bit vanishes; the resolvable surface
  have hmergeZero := mergeV2_zero_of_distinctDest hsat hc i hi W hsurv hdd
  obtain ⟨hresB, hresI⟩ :=
    resolvableV2ArithN_of_sat hsat hc i hi hcv2_0B hcv2_1B hnlaB hnlbB (Or.inl hmergeZero)
  -- the landing correspondences
  have hcorrA := landV4CorrespondenceA_of_sat hsat hc i hi W hsurv hne
  have hcorrB := landV4CorrespondenceB_of_sat hsat hc i hi W hsurv hne
  -- per-cell standalone reads (gathered BEFORE `set`, so `set` folds `envAt t i`/decodes)
  have hcK : y * n + x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (y + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hexp : (y + 1) * n = y * n + n := by ring
    omega
  have hda : (envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2A n) = 1
              then (moveDecodeN n (envAt t i) 1).to else (moveDecodeN n (envAt t i) 0).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB htxa htya htxb htyb x y hx hy
    simpa using h
  have hdb : (envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) 0).to else (moveDecodeN n (envAt t i) 1).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB htxb htyb htxa htya x y hx hy
    simpa using h
  have hn0 : 0 < n := by omega
  have hyy : y = (y * n + x) / n := by
    rw [Nat.add_comm, Nat.mul_comm y n, Nat.add_mul_div_left x y hn0, Nat.div_eq_of_lt hx,
      Nat.zero_add]
  have hxx : x = (y * n + x) % n := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hwb := writeCellV4N_of_sat hsat i hi (y * n + x) y x hyy hxx hcK
  have hmv := midV4CellN_of_sat hsat i hi (y * n + x) hcK
  have hbdcell := oldCell_decode x y (envAt t i) hx hy
  -- ============ fold ============
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  set destV2A : Coord := if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to with hdestV2A
  set destV2B : Coord := if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to with hdestV2B
  -- carryV4Col = cCarryV4
  have hcc0 : NGen.carryV4Col n 0 = NGen.cCarryV4 n 0 := rfl
  have hcc1 : NGen.carryV4Col n 1 = NGen.cCarryV4 n 1 := rfl
  -- movers-membership ⟺ carries
  have hmemA_iff : ma.frm ∈ movers bd [ma, mb] ↔ e.loc (NGen.cCarryV4 n 0) = 1 := by
    rw [mem_movers_pair bd ma mb hne]
    exact ⟨fun ⟨_, hcar, hmov⟩ => hcorrA.1.mpr ⟨hcar, hmov⟩,
      fun h => ⟨Or.inl rfl, (hcorrA.1.mp h).1, (hcorrA.1.mp h).2⟩⟩
  have hmemB_iff : mb.frm ∈ movers bd [ma, mb] ↔ e.loc (NGen.cCarryV4 n 1) = 1 := by
    rw [mem_movers_pair bd ma mb hne]
    exact ⟨fun ⟨_, hcar, hmov⟩ => hcorrB.1.mpr ⟨hcar, hmov⟩,
      fun h => ⟨Or.inr rfl, (hcorrB.1.mp h).1, (hcorrB.1.mp h).2⟩⟩
  -- landing identities under carry
  have hLA : e.loc (NGen.cCarryV4 n 0) = 1 → landMap bd [ma, mb] ma.frm = destV2A :=
    fun h => (hcorrA.2 h).symm
  have hLB : e.loc (NGen.cCarryV4 n 1) = 1 → landMap bd [ma, mb] mb.frm = destV2B :=
    fun h => (hcorrB.2 h).symm
  -- resolvableV2 = 0 collapses both V4 carries (the STUCK sub-case)
  have hcarryV4_collapse : e.loc (NGen.cResolvableV2 n) = 0 →
      e.loc (NGen.cCarryV4 n 0) = 0 ∧ e.loc (NGen.cCarryV4 n 1) = 0 := by
    intro hrv0
    have hnot : ¬ (e.loc (NGen.cMergeV2 n) = 0
        ∧ (e.loc (NGen.cCv2 n 0) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 0) = 0)
        ∧ (e.loc (NGen.cCv2 n 1) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 1) = 0)) := by
      intro h; rw [hresI.mpr h] at hrv0; exact absurd hrv0 (by norm_num)
    have cv4a0_of_cv3a0 : e.loc (NGen.cCarryV3 n 0) = 0 → e.loc (NGen.cCarryV4 n 0) = 0 := by
      intro h; rcases hcv4aB with hz | ho
      · exact hz
      · exact absurd (hcv4aI.mp ho).1 (by rw [h]; norm_num)
    have cv4b0_of_cv3b0 : e.loc (NGen.cCarryV3 n 1) = 0 → e.loc (NGen.cCarryV4 n 1) = 0 := by
      intro h; rcases hcv4bB with hz | ho
      · exact hz
      · exact absurd (hcv4bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_cv2a0 : e.loc (NGen.cCv2 n 0) = 0 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).1 (by rw [h]; norm_num)
    have cv3b0_of_cv2b0 : e.loc (NGen.cCv2 n 1) = 0 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_nla : e.loc (NGen.cNonLeaveV2 n 0) = 1 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).2 (by rw [h]; norm_num)
    have cv3b0_of_nlb : e.loc (NGen.cNonLeaveV2 n 1) = 1 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).2 (by rw [h]; norm_num)
    by_cases hbadA : e.loc (NGen.cCv2 n 0) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 0) = 1
    · obtain ⟨_, hn0⟩ := hbadA
      have hc1z : e.loc (NGen.cCv2 n 1) = 0 := by simpa using (hnlaI.mp hn0).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_nla hn0), cv4b0_of_cv3b0 (cv3b0_of_cv2b0 hc1z)⟩
    · have hbadB : e.loc (NGen.cCv2 n 1) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 1) = 1 := by
        by_contra hbn
        apply hnot
        refine ⟨hmergeZero, ?_, ?_⟩
        · rcases hcv2_0B with h | h
          · exact Or.inl h
          · rcases hnlaB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbadA
        · rcases hcv2_1B with h | h
          · exact Or.inl h
          · rcases hnlbB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbn
      obtain ⟨_, hn1⟩ := hbadB
      have hc0z : e.loc (NGen.cCv2 n 0) = 0 := by simpa using (hnlbI.mp hn1).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_cv2a0 hc0z), cv4b0_of_cv3b0 (cv3b0_of_nlb hn1)⟩
  -- indicator readings at (x, y)
  have hsa := F.srcIndA x y hx hy
  have hsb := F.srcIndB x y hx hy
  have hda' : e.loc (NGen.wDstV2Row n 0 y) * e.loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord) = destV2A then (1 : ℤ) else 0 := hda
  have hdb' : e.loc (NGen.wDstV2Row n 1 y) * e.loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord) = destV2B then (1 : ℤ) else 0 := hdb
  -- cMidV4 ≡ cWBoardV4 (both resolvableV2 polarities)
  have hmidwb : e.loc (NGen.cMidV4 n (y * n + x)) ≡ e.loc (NGen.cWBoardV4 n (y * n + x))
      [ZMOD 2013265921] := by
    rcases hresB with hr0 | hr1
    · obtain ⟨hca0, hcb0⟩ := hcarryV4_collapse hr0
      have hwb0 := hwb
      rw [hcc0, hcc1, hca0, hcb0] at hwb0
      have hwbold : e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ e.loc (NGen.old n (y * n + x))
          [ZMOD 2013265921] := by
        calc e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ _ [ZMOD 2013265921] := hwb0
          _ = e.loc (NGen.old n (y * n + x)) := by ring
      calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.old n (y * n + x)) := by rw [hr0]; ring
        _ ≡ e.loc (NGen.cWBoardV4 n (y * n + x)) [ZMOD 2013265921] := hwbold.symm
    · calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.cWBoardV4 n (y * n + x)) := by rw [hr1]; ring
  -- write-cell polynomial, substituted into the four indicator products
  have hmod : e.loc (NGen.cMidV4 n (y * n + x))
      ≡ (1 - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)))
          * e.loc (NGen.old n (y * n + x))
        + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 0)
        + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 1)
        - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
            * e.loc (NGen.particleCol n 1)
      [ZMOD 2013265921] := by
    have hwb1 := hwb
    rw [hcc0, hcc1, hsa, hsb, hda', hdb'] at hwb1
    exact hmidwb.trans hwb1
  -- indicator booleans and same-piece exclusions
  have bA : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = ma.frm <;> simp [h, q]
  have bB : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2A <;> simp [h, q]
  have bC : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = mb.frm <;> simp [h, q]
  have bD : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2B <;> simp [h, q]
  have eAB : (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)) = 0 := by
    rcases hcv4aB with h | h
    · rw [h]; ring
    · have hdne : destV2A ≠ ma.frm := by rw [← hLA h]; exact (hcorrA.1.mp h).2
      by_cases q1 : (⟨x, y⟩ : Coord) = ma.frm
      · by_cases q2 : (⟨x, y⟩ : Coord) = destV2A
        · exact absurd (q2.symm.trans q1) hdne
        · simp [q2]
      · simp [q1]
  have eCD : (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)) = 0 := by
    rcases hcv4bB with h | h
    · rw [h]; ring
    · have hdne : destV2B ≠ mb.frm := by rw [← hLB h]; exact (hcorrB.1.mp h).2
      by_cases q1 : (⟨x, y⟩ : Coord) = mb.frm
      · by_cases q2 : (⟨x, y⟩ : Coord) = destV2B
        · exact absurd (q2.symm.trans q1) hdne
        · simp [q2]
      · simp [q1]
  have holdc : 0 ≤ e.loc (NGen.old n (y * n + x)) ∧ e.loc (NGen.old n (y * n + x)) ≤ 3 := by
    rcases F.alphaOld (y * n + x) hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  -- `cMidV4` carries NO alphabet gate (only the committed `mid` column does); its canonicity comes
  -- straight from `StepCanon` (`canon_loc`), which is exactly what `cellAlgebra` needs to pin the
  -- mod-`p` collapse to an on-alphabet equality.
  have hmidc : Canon (e.loc (NGen.cMidV4 n (y * n + x))) := canon_loc hc i _
  have hpaA : 0 ≤ e.loc (NGen.particleCol n 0) ∧ e.loc (NGen.particleCol n 0) ≤ 3 := by
    rcases F.paAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hpbA : 0 ≤ e.loc (NGen.particleCol n 1) ∧ e.loc (NGen.particleCol n 1) ≤ 3 := by
    rcases F.pbAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have halg := AutomataflResolveRefine.cellAlgebra bA bB bC bD eAB eCD holdc hmidc hpaA hpbA hmod
  -- product-to-prop bridge
  have prodOne : ∀ (c : ℤ) (P : Prop) [Decidable P], (c = 0 ∨ c = 1) →
      (c * (if P then (1:ℤ) else 0) = 1 ↔ c = 1 ∧ P) := by
    intro c P _ hc
    by_cases hP : P <;> rcases hc with h | h <;> simp [hP, h]
  -- the three condition equivalences
  have hBiff : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1
      ↔ (ma.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] ma.frm = (⟨x, y⟩ : Coord)) := by
    rw [prodOne _ _ hcv4aB, hmemA_iff]
    exact ⟨fun ⟨hm, hq2⟩ => ⟨hm, by rw [hLA hm]; exact hq2.symm⟩,
      fun ⟨hm, hlm⟩ => ⟨hm, by rw [← hLA hm]; exact hlm.symm⟩⟩
  have hDiff : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1
      ↔ (mb.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] mb.frm = (⟨x, y⟩ : Coord)) := by
    rw [prodOne _ _ hcv4bB, hmemB_iff]
    exact ⟨fun ⟨hm, hq2⟩ => ⟨hm, by rw [hLB hm]; exact hq2.symm⟩,
      fun ⟨hm, hlm⟩ => ⟨hm, by rw [← hLB hm]; exact hlm.symm⟩⟩
  have hMemiff : (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1
        ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1)
      ↔ memB (movers bd [ma, mb]) (⟨x, y⟩ : Coord) = true := by
    rw [prodOne _ _ hcv4aB, prodOne _ _ hcv4bB, memB_iff]
    constructor
    · rintro (⟨hm, hxy⟩ | ⟨hm, hxy⟩)
      · rw [hxy]; exact hmemA_iff.mpr hm
      · rw [hxy]; exact hmemB_iff.mpr hm
    · intro hmem
      obtain ⟨hcor, _, _⟩ := (mem_movers_pair bd ma mb hne _).mp hmem
      rcases hcor with h | h
      · exact Or.inl ⟨hmemA_iff.mp (h ▸ hmem), h⟩
      · exact Or.inr ⟨hmemB_iff.mp (h ▸ hmem), h⟩
  -- the reference cell, in arrival form
  have hInA : bd.inBounds ma.to := F.validA.2.2.2.1
  have hInB : bd.inBounds mb.to := F.validB.2.2.2.1
  have hq : bd.inBounds (⟨x, y⟩ : Coord) := ⟨hx, hy⟩
  rw [resolveMoves_cell_pair bd ma mb hne hlegA hlegB hdd hInA hInB ⟨x, y⟩ hq,
    arrivalAt_pair bd ma mb hne hlegA hlegB hdd ⟨x, y⟩]
  -- decode the emitted if-tree, converting values, and match branch-for-branch
  rw [halg, apply_ite codeToParticle, apply_ite codeToParticle, apply_ite codeToParticle,
    show codeToParticle 0 = Particle.vacuum from by decide, ← F.paVal, ← F.pbVal, hbdcell]
  by_cases h1 : ma.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] ma.frm = (⟨x, y⟩ : Coord)
  · rw [if_pos (hBiff.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hBiff.mp h)), if_neg h1]
    by_cases h2 : mb.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] mb.frm = (⟨x, y⟩ : Coord)
    · rw [if_pos (hDiff.mpr h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hDiff.mp h)), if_neg h2]
      by_cases h3 : memB (movers bd [ma, mb]) (⟨x, y⟩ : Coord) = true
      · rw [if_pos (hMemiff.mpr h3), if_pos h3]
      · rw [if_neg (fun h => h3 (hMemiff.mp h)), if_neg h3]

end CleanCell

/-! ## §26 — THE SHARED-DEST SINGLE-VACUUM BOARD CELL (edge `da = db`, one source vacuum).

On a surviving round (`surv = 1`) with distinct decoded sources (`sa ≠ sb`) but a SHARED decoded
destination (`da = db`) where NOT both sources carry (`¬(carSa ∧ carSb)`, forced by `¬collide` on a
surviving round), at most ONE piece is a mover. The decoded FINAL board cell `cMidV4` IS the reference
`resolveMoves` cell. Threads §22 (still applies — it needs distinct SOURCE, which holds) and the
`_sep` single-effective-mover collapse (`¬both-movers` in place of the distinct-dest `hdd`); the
confluence bit vanishes because a merge needs BOTH pieces to carry. -/
section EdgeBCell
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (carAt landMap movers resolveMoves arrivalAt memB memB_iff
  mem_movers_pair carAt_of_mover resolveMoves_cell_pair_sep arrivalAt_pair_sep)

/-- **`mergeV2_zero_of_notBothNz`.** On a surviving round where the two decoded sources are NOT both
carrying (`¬(cAnz = 1 ∧ cBnz = 1)`), the confluence bit vanishes: a merge needs BOTH pieces to carry
(`cCv2 = 1`, which forces `nz = 1`), so it never fires. -/
theorem mergeV2_zero_of_notBothNz
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hnbnz : ¬((envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1)) :
    (envAt t i).loc (NGen.cMergeV2 n) = 0 := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  set e := envAt t i with he
  have hocc0B : e.loc (NGen.cOccIncl n 0) = 0 ∨ e.loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : e.loc (NGen.cOccIncl n 1) = 0 ∨ e.loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  obtain ⟨heqffB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨heqttB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨heq2B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  obtain ⟨hftaB, -⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hftbB, -⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  obtain ⟨hreseqB, -⟩ := resEqV2CoordN_of_sat hsat hc i hi W hftaB hftbB
  obtain ⟨hmergeB, hmergeI⟩ := mergeV2N_of_sat hsat hc i hi heqffB heqttB hcv2_0B hcv2_1B hreseqB
  rcases hmergeB with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨hcc0, hcc1, -, -⟩ := hmergeI.mp h1
    exact hnbnz ⟨(hcv2_0I.mp hcc0).2.1, (hcv2_1I.mp hcc1).2.1⟩

/-- **THE SHARED-DEST SINGLE-VACUUM BOARD CELL.** On a surviving round with distinct decoded sources,
a SHARED decoded destination, and NOT both sources carrying, the decoded FINAL board cell IS the
reference `resolveMoves` cell, at every in-bounds coordinate, at arbitrary board size `n`. -/
theorem sharedDestVacuumBoardCell
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hne : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm)
    (hto : (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to)
    (hnbc : ¬(carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true
             ∧ carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true))
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (resolveMoves (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  have hlegA : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).to := F.validA.1
  have hlegB : (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).to := F.validB.1
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  obtain ⟨heqffB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨heqttB, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨heq2B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, -⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  obtain ⟨hftaB, -⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hftbB, -⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  obtain ⟨hlnzaB, -⟩ := landNzV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB
    htxa htya htxb htyb
  obtain ⟨hlnzbB, -⟩ := landNzV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB
    htxb htyb htxa htya
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  obtain ⟨hnlaB, hnlaI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 0 (by norm_num) hlnzaB hcv2_1B
  obtain ⟨hnlbB, hnlbI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 1 (by norm_num) hlnzbB hcv2_0B
  obtain ⟨hcv3aB, hcv3aI⟩ := carryV3ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv2_0B hnlaB
  obtain ⟨hcv3bB, hcv3bI⟩ := carryV3ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv2_1B hnlbB
  obtain ⟨htcB, -⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  obtain ⟨hcv4aB, hcv4aI⟩ := carryV4ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv3aB htcB
  obtain ⟨hcv4bB, hcv4bI⟩ := carryV4ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv3bB htcB
  -- confluence bit vanishes (¬both-carry), via `¬(cAnz = 1 ∧ cBnz = 1)` from `hnbc`
  have hnbnz : ¬((envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1) := by
    rintro ⟨ha, hb⟩
    exact hnbc ⟨by simp only [carAt, F.anzIff.mp ha, Bool.not_false],
                by simp only [carAt, F.bnzIff.mp hb, Bool.not_false]⟩
  have hmergeZero := mergeV2_zero_of_notBothNz hsat hc i hi W hsurv hnbnz
  obtain ⟨hresB, hresI⟩ :=
    resolvableV2ArithN_of_sat hsat hc i hi hcv2_0B hcv2_1B hnlaB hnlbB (Or.inl hmergeZero)
  have hcorrA := landV4CorrespondenceA_of_sat hsat hc i hi W hsurv hne
  have hcorrB := landV4CorrespondenceB_of_sat hsat hc i hi W hsurv hne
  have hcK : y * n + x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (y + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hexp : (y + 1) * n = y * n + n := by ring
    omega
  have hda : (envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2A n) = 1
              then (moveDecodeN n (envAt t i) 1).to else (moveDecodeN n (envAt t i) 0).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB htxa htya htxb htyb x y hx hy
    simpa using h
  have hdb : (envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) 0).to else (moveDecodeN n (envAt t i) 1).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB htxb htyb htxa htya x y hx hy
    simpa using h
  have hn0 : 0 < n := by omega
  have hyy : y = (y * n + x) / n := by
    rw [Nat.add_comm, Nat.mul_comm y n, Nat.add_mul_div_left x y hn0, Nat.div_eq_of_lt hx,
      Nat.zero_add]
  have hxx : x = (y * n + x) % n := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hwb := writeCellV4N_of_sat hsat i hi (y * n + x) y x hyy hxx hcK
  have hmv := midV4CellN_of_sat hsat i hi (y * n + x) hcK
  have hbdcell := oldCell_decode x y (envAt t i) hx hy
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  set destV2A : Coord := if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to with hdestV2A
  set destV2B : Coord := if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to with hdestV2B
  have hcc0 : NGen.carryV4Col n 0 = NGen.cCarryV4 n 0 := rfl
  have hcc1 : NGen.carryV4Col n 1 = NGen.cCarryV4 n 1 := rfl
  have hmemA_iff : ma.frm ∈ movers bd [ma, mb] ↔ e.loc (NGen.cCarryV4 n 0) = 1 := by
    rw [mem_movers_pair bd ma mb hne]
    exact ⟨fun ⟨_, hcar, hmov⟩ => hcorrA.1.mpr ⟨hcar, hmov⟩,
      fun h => ⟨Or.inl rfl, (hcorrA.1.mp h).1, (hcorrA.1.mp h).2⟩⟩
  have hmemB_iff : mb.frm ∈ movers bd [ma, mb] ↔ e.loc (NGen.cCarryV4 n 1) = 1 := by
    rw [mem_movers_pair bd ma mb hne]
    exact ⟨fun ⟨_, hcar, hmov⟩ => hcorrB.1.mpr ⟨hcar, hmov⟩,
      fun h => ⟨Or.inr rfl, (hcorrB.1.mp h).1, (hcorrB.1.mp h).2⟩⟩
  have hLA : e.loc (NGen.cCarryV4 n 0) = 1 → landMap bd [ma, mb] ma.frm = destV2A :=
    fun h => (hcorrA.2 h).symm
  have hLB : e.loc (NGen.cCarryV4 n 1) = 1 → landMap bd [ma, mb] mb.frm = destV2B :=
    fun h => (hcorrB.2 h).symm
  -- the SEPARATION hypothesis: not both are movers (each mover carries; not both carry)
  have hsep : ¬(ma.frm ∈ movers bd [ma, mb] ∧ mb.frm ∈ movers bd [ma, mb]) := by
    rintro ⟨hA, hB⟩
    exact hnbc ⟨carAt_of_mover bd [ma, mb] ma.frm hA, carAt_of_mover bd [ma, mb] mb.frm hB⟩
  have hcarryV4_collapse : e.loc (NGen.cResolvableV2 n) = 0 →
      e.loc (NGen.cCarryV4 n 0) = 0 ∧ e.loc (NGen.cCarryV4 n 1) = 0 := by
    intro hrv0
    have hnot : ¬ (e.loc (NGen.cMergeV2 n) = 0
        ∧ (e.loc (NGen.cCv2 n 0) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 0) = 0)
        ∧ (e.loc (NGen.cCv2 n 1) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 1) = 0)) := by
      intro h; rw [hresI.mpr h] at hrv0; exact absurd hrv0 (by norm_num)
    have cv4a0_of_cv3a0 : e.loc (NGen.cCarryV3 n 0) = 0 → e.loc (NGen.cCarryV4 n 0) = 0 := by
      intro h; rcases hcv4aB with hz | ho
      · exact hz
      · exact absurd (hcv4aI.mp ho).1 (by rw [h]; norm_num)
    have cv4b0_of_cv3b0 : e.loc (NGen.cCarryV3 n 1) = 0 → e.loc (NGen.cCarryV4 n 1) = 0 := by
      intro h; rcases hcv4bB with hz | ho
      · exact hz
      · exact absurd (hcv4bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_cv2a0 : e.loc (NGen.cCv2 n 0) = 0 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).1 (by rw [h]; norm_num)
    have cv3b0_of_cv2b0 : e.loc (NGen.cCv2 n 1) = 0 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_nla : e.loc (NGen.cNonLeaveV2 n 0) = 1 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).2 (by rw [h]; norm_num)
    have cv3b0_of_nlb : e.loc (NGen.cNonLeaveV2 n 1) = 1 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).2 (by rw [h]; norm_num)
    by_cases hbadA : e.loc (NGen.cCv2 n 0) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 0) = 1
    · obtain ⟨_, hn0⟩ := hbadA
      have hc1z : e.loc (NGen.cCv2 n 1) = 0 := by simpa using (hnlaI.mp hn0).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_nla hn0), cv4b0_of_cv3b0 (cv3b0_of_cv2b0 hc1z)⟩
    · have hbadB : e.loc (NGen.cCv2 n 1) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 1) = 1 := by
        by_contra hbn
        apply hnot
        refine ⟨hmergeZero, ?_, ?_⟩
        · rcases hcv2_0B with h | h
          · exact Or.inl h
          · rcases hnlaB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbadA
        · rcases hcv2_1B with h | h
          · exact Or.inl h
          · rcases hnlbB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbn
      obtain ⟨_, hn1⟩ := hbadB
      have hc0z : e.loc (NGen.cCv2 n 0) = 0 := by simpa using (hnlbI.mp hn1).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_cv2a0 hc0z), cv4b0_of_cv3b0 (cv3b0_of_nlb hn1)⟩
  have hsa := F.srcIndA x y hx hy
  have hsb := F.srcIndB x y hx hy
  have hda' : e.loc (NGen.wDstV2Row n 0 y) * e.loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord) = destV2A then (1 : ℤ) else 0 := hda
  have hdb' : e.loc (NGen.wDstV2Row n 1 y) * e.loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord) = destV2B then (1 : ℤ) else 0 := hdb
  have hmidwb : e.loc (NGen.cMidV4 n (y * n + x)) ≡ e.loc (NGen.cWBoardV4 n (y * n + x))
      [ZMOD 2013265921] := by
    rcases hresB with hr0 | hr1
    · obtain ⟨hca0, hcb0⟩ := hcarryV4_collapse hr0
      have hwb0 := hwb
      rw [hcc0, hcc1, hca0, hcb0] at hwb0
      have hwbold : e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ e.loc (NGen.old n (y * n + x))
          [ZMOD 2013265921] := by
        calc e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ _ [ZMOD 2013265921] := hwb0
          _ = e.loc (NGen.old n (y * n + x)) := by ring
      calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.old n (y * n + x)) := by rw [hr0]; ring
        _ ≡ e.loc (NGen.cWBoardV4 n (y * n + x)) [ZMOD 2013265921] := hwbold.symm
    · calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.cWBoardV4 n (y * n + x)) := by rw [hr1]; ring
  have hmod : e.loc (NGen.cMidV4 n (y * n + x))
      ≡ (1 - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)))
          * e.loc (NGen.old n (y * n + x))
        + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 0)
        + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 1)
        - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
            * e.loc (NGen.particleCol n 1)
      [ZMOD 2013265921] := by
    have hwb1 := hwb
    rw [hcc0, hcc1, hsa, hsb, hda', hdb'] at hwb1
    exact hmidwb.trans hwb1
  have bA : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = ma.frm <;> simp [h, q]
  have bB : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2A <;> simp [h, q]
  have bC : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = mb.frm <;> simp [h, q]
  have bD : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2B <;> simp [h, q]
  have eAB : (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)) = 0 := by
    rcases hcv4aB with h | h
    · rw [h]; ring
    · have hdne : destV2A ≠ ma.frm := by rw [← hLA h]; exact (hcorrA.1.mp h).2
      by_cases q1 : (⟨x, y⟩ : Coord) = ma.frm
      · by_cases q2 : (⟨x, y⟩ : Coord) = destV2A
        · exact absurd (q2.symm.trans q1) hdne
        · simp [q2]
      · simp [q1]
  have eCD : (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)) = 0 := by
    rcases hcv4bB with h | h
    · rw [h]; ring
    · have hdne : destV2B ≠ mb.frm := by rw [← hLB h]; exact (hcorrB.1.mp h).2
      by_cases q1 : (⟨x, y⟩ : Coord) = mb.frm
      · by_cases q2 : (⟨x, y⟩ : Coord) = destV2B
        · exact absurd (q2.symm.trans q1) hdne
        · simp [q2]
      · simp [q1]
  have holdc : 0 ≤ e.loc (NGen.old n (y * n + x)) ∧ e.loc (NGen.old n (y * n + x)) ≤ 3 := by
    rcases F.alphaOld (y * n + x) hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hmidc : Canon (e.loc (NGen.cMidV4 n (y * n + x))) := canon_loc hc i _
  have hpaA : 0 ≤ e.loc (NGen.particleCol n 0) ∧ e.loc (NGen.particleCol n 0) ≤ 3 := by
    rcases F.paAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hpbA : 0 ≤ e.loc (NGen.particleCol n 1) ∧ e.loc (NGen.particleCol n 1) ≤ 3 := by
    rcases F.pbAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have halg := AutomataflResolveRefine.cellAlgebra bA bB bC bD eAB eCD holdc hmidc hpaA hpbA hmod
  have prodOne : ∀ (c : ℤ) (P : Prop) [Decidable P], (c = 0 ∨ c = 1) →
      (c * (if P then (1:ℤ) else 0) = 1 ↔ c = 1 ∧ P) := by
    intro c P _ hc
    by_cases hP : P <;> rcases hc with h | h <;> simp [hP, h]
  have hBiff : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1
      ↔ (ma.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] ma.frm = (⟨x, y⟩ : Coord)) := by
    rw [prodOne _ _ hcv4aB, hmemA_iff]
    exact ⟨fun ⟨hm, hq2⟩ => ⟨hm, by rw [hLA hm]; exact hq2.symm⟩,
      fun ⟨hm, hlm⟩ => ⟨hm, by rw [← hLA hm]; exact hlm.symm⟩⟩
  have hDiff : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1
      ↔ (mb.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] mb.frm = (⟨x, y⟩ : Coord)) := by
    rw [prodOne _ _ hcv4bB, hmemB_iff]
    exact ⟨fun ⟨hm, hq2⟩ => ⟨hm, by rw [hLB hm]; exact hq2.symm⟩,
      fun ⟨hm, hlm⟩ => ⟨hm, by rw [← hLB hm]; exact hlm.symm⟩⟩
  have hMemiff : (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1
        ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1)
      ↔ memB (movers bd [ma, mb]) (⟨x, y⟩ : Coord) = true := by
    rw [prodOne _ _ hcv4aB, prodOne _ _ hcv4bB, memB_iff]
    constructor
    · rintro (⟨hm, hxy⟩ | ⟨hm, hxy⟩)
      · rw [hxy]; exact hmemA_iff.mpr hm
      · rw [hxy]; exact hmemB_iff.mpr hm
    · intro hmem
      obtain ⟨hcor, _, _⟩ := (mem_movers_pair bd ma mb hne _).mp hmem
      rcases hcor with h | h
      · exact Or.inl ⟨hmemA_iff.mp (h ▸ hmem), h⟩
      · exact Or.inr ⟨hmemB_iff.mp (h ▸ hmem), h⟩
  have hInA : bd.inBounds ma.to := F.validA.2.2.2.1
  have hInB : bd.inBounds mb.to := F.validB.2.2.2.1
  have hq : bd.inBounds (⟨x, y⟩ : Coord) := ⟨hx, hy⟩
  rw [resolveMoves_cell_pair_sep bd ma mb hne hlegA hlegB hInA hInB hsep ⟨x, y⟩ hq,
    arrivalAt_pair_sep bd ma mb hne hlegA hlegB hsep ⟨x, y⟩]
  rw [halg, apply_ite codeToParticle, apply_ite codeToParticle, apply_ite codeToParticle,
    show codeToParticle 0 = Particle.vacuum from by decide, ← F.paVal, ← F.pbVal, hbdcell]
  by_cases h1 : ma.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] ma.frm = (⟨x, y⟩ : Coord)
  · rw [if_pos (hBiff.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hBiff.mp h)), if_neg h1]
    by_cases h2 : mb.frm ∈ movers bd [ma, mb] ∧ landMap bd [ma, mb] mb.frm = (⟨x, y⟩ : Coord)
    · rw [if_pos (hDiff.mpr h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hDiff.mp h)), if_neg h2]
      by_cases h3 : memB (movers bd [ma, mb]) (⟨x, y⟩ : Coord) = true
      · rw [if_pos (hMemiff.mpr h3), if_pos h3]
      · rw [if_neg (fun h => h3 (hMemiff.mp h)), if_neg h3]

end EdgeBCell

/-! ## §27 — THE IDENTICAL-MOVE BOARD CELL (edge `sa = sb`, `da = db`).

On a surviving round (`surv = 1`) where the two decoded moves are IDENTICAL up to the player id
(`sa = sb` and `da = db` — which `¬fork` forces once `sa = sb`), the reference `dedup`s them to ONE
mover, and the decoded FINAL board cell `cMidV4` IS the reference `resolveMoves` cell. This is the
`hne`-FREE landing correspondence: with `sa = sb` the two moves are the SAME edge (`cFtV2A = cFtV2B =
0`, `cTwoCyc = 0`, both carries agree ⟺ the single mover condition `carAt sa ∧ ¬blockedB`), and the
confluence bit vanishes by the IDENTICAL-move exception (`cIdentV2 = eq_ff · eq_tt = 1`). Matched to
`resolveMoves_cell_identical`. -/
section EdgeCCell
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (carAt blockedB resolveMoves resolveMoves_cell_identical
  carAt_to_false_of_not_blocked)

/-- **THE IDENTICAL-MOVE BOARD CELL.** On a surviving round with `sa = sb` and `da = db`, the decoded
FINAL board cell IS the reference `resolveMoves` cell, at every in-bounds coordinate, at arbitrary `n`.
The `hne`-free landing correspondence: one edge, both carries agree with the single-mover condition. -/
theorem identicalMoveBoardCell
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 1)
    (hsrc : (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm)
    (hto : (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to)
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (resolveMoves (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  have hlegA : (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 0).to := F.validA.1
  have hlegB : (moveDecodeN n (envAt t i) 1).frm ≠ (moveDecodeN n (envAt t i) 1).to := F.validB.1
  obtain ⟨hfxa, hfya, htxa, htya⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ :=
    AutomataflResolveCapstone.moveCoordBounds hsat hc i hi W.base 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  -- eq bits (with their iffs)
  obtain ⟨heqffB, heqffI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨heqttB, heqttI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨heq2B, heq2I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨heq3B, heq3I⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.base.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  have heqffC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1 ↔
      (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm := by
    rw [heqffI]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN hfxa.1 hfxb.1,
      AutomataflResolveCapstone.toNat_injN hfya.1 hfyb.1]
  have heqttC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1 ↔
      (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to := by
    rw [heqttI]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxa.1 htxb.1,
      AutomataflResolveCapstone.toNat_injN htya.1 htyb.1]
  have heq2C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ↔
      (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).frm := by
    rw [heq2I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxa.1 hfxb.1,
      AutomataflResolveCapstone.toNat_injN htya.1 hfyb.1]
  have heq3C : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ↔
      (moveDecodeN n (envAt t i) 1).to = (moveDecodeN n (envAt t i) 0).frm := by
    rw [heq3I]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [AutomataflResolveCapstone.toNat_injN htxb.1 hfxa.1,
      AutomataflResolveCapstone.toNat_injN htyb.1 hfya.1]
  -- d ≠ s (move legality), and the crossing bits vanish (identical move is not a chain/2-cycle)
  have hds : (moveDecodeN n (envAt t i) 0).to ≠ (moveDecodeN n (envAt t i) 0).frm :=
    fun h => hlegA h.symm
  have heq2z : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0 := by
    rcases heq2B with h | h
    · exact h
    · exfalso; have hh := heq2C.mp h; rw [← hsrc] at hh; exact hds hh
  have heq3z : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0 := by
    rcases heq3B with h | h
    · exact h
    · exfalso; have hh := heq3C.mp h; rw [← hto] at hh; exact hds hh
  -- occlusion bits + `blockedB` iff
  have hocc0B : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 0 (NGen.occBase n 0)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 0 (NGen.occBase n 0))))
      (canon_loc hc i _)
  have hocc1B : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    bin_of_gate (rgateN hsat i hi (AutomataflOcclusionBridgeN.inclLiftN n 1 (NGen.occBase n 1)
      (by norm_num) rfl (AutomataflOcclusionBridgeN.voI_occIncl_ib n 1 (NGen.occBase n 1))))
      (canon_loc hc i _)
  have hocc0I : (envAt t i).loc (NGen.cOccIncl n 0) = 1 ↔
      blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
        (moveDecodeN n (envAt t i) 0) = true := by
    have h := blockedV2N_of_sat hsat hc i hi W 0 (by norm_num)
    simpa using h
  -- flow-through bits (with iffs) → both vanish (`ma.to ≠ mb.frm`, `mb.to ≠ ma.frm`)
  obtain ⟨hftaB, hftaI⟩ := ftV2AN_of_sat hsat hc i hi heq2B F.bnzB hocc1B heq3B (Or.inr hsurv)
  obtain ⟨hftbB, hftbI⟩ := ftV2BN_of_sat hsat hc i hi heq3B F.anzB hocc0B heq2B (Or.inr hsurv)
  have hfta0 : (envAt t i).loc (NGen.cFtV2A n) = 0 := by
    rcases hftaB with h | h
    · exact h
    · exfalso; have := (hftaI.mp h).1; rw [heq2z] at this; exact absurd this (by norm_num)
  have hftb0 : (envAt t i).loc (NGen.cFtV2B n) = 0 := by
    rcases hftbB with h | h
    · exact h
    · exfalso; have := (hftbI.mp h).1; rw [heq3z] at this; exact absurd this (by norm_num)
  -- landing-occupancy (with iffs, cleaned)
  obtain ⟨hlnzaB, -⟩ := landNzV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB
    htxa htya htxb htyb
  obtain ⟨hlnzbB, -⟩ := landNzV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB
    htxb htyb htxa htya
  obtain ⟨hcv2_0B, hcv2_0I⟩ := cv2ValN_of_sat hsat hc i hi 0 (by norm_num) (Or.inr hsurv) F.anzB hocc0B
  obtain ⟨hcv2_1B, hcv2_1I⟩ := cv2ValN_of_sat hsat hc i hi 1 (by norm_num) (Or.inr hsurv) F.bnzB hocc1B
  obtain ⟨hnlaB, hnlaI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 0 (by norm_num) hlnzaB hcv2_1B
  obtain ⟨hnlbB, hnlbI⟩ := nonLeaveV2GateN_of_sat hsat hc i hi 1 (by norm_num) hlnzbB hcv2_0B
  obtain ⟨hcv3aB, hcv3aI⟩ := carryV3ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv2_0B hnlaB
  obtain ⟨hcv3bB, hcv3bI⟩ := carryV3ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv2_1B hnlbB
  obtain ⟨htcB, htcI⟩ := twoCycN_of_sat hsat hc i hi heq2B heq3B hocc1B hocc0B
  have htc0 : (envAt t i).loc (NGen.cTwoCyc n) = 0 := by
    rcases htcB with h | h
    · exact h
    · exfalso; have := (htcI.mp h).1; rw [heq2z] at this; exact absurd this (by norm_num)
  obtain ⟨hcv4aB, hcv4aI⟩ := carryV4ArithN_of_sat hsat hc i hi 0 (by norm_num) hcv3aB htcB
  obtain ⟨hcv4bB, hcv4bI⟩ := carryV4ArithN_of_sat hsat hc i hi 1 (by norm_num) hcv3bB htcB
  obtain ⟨hreseqB, -⟩ := resEqV2CoordN_of_sat hsat hc i hi W hftaB hftbB
  obtain ⟨hmergeB, hmergeI⟩ := mergeV2N_of_sat hsat hc i hi heqffB heqttB hcv2_0B hcv2_1B hreseqB
  -- confluence bit vanishes by the IDENTICAL-move exception (`eq_ff = eq_tt = 1`)
  have hmergeZero : (envAt t i).loc (NGen.cMergeV2 n) = 0 := by
    rcases hmergeB with h0 | h1
    · exact h0
    · exfalso; obtain ⟨-, -, -, hlast⟩ := hmergeI.mp h1
      rcases hlast with h | h
      · rw [heqffC.mpr hsrc] at h; exact absurd h (by norm_num)
      · rw [heqttC.mpr hto] at h; exact absurd h (by norm_num)
  obtain ⟨hresB, hresI⟩ :=
    resolvableV2ArithN_of_sat hsat hc i hi hcv2_0B hcv2_1B hnlaB hnlbB (Or.inl hmergeZero)
  -- indicator products at (x, y), the write-cell polynomial pieces
  have hcK : y * n + x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (y + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hexp : (y + 1) * n = y * n + n := by ring
    omega
  have hda : (envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2A n) = 1
              then (moveDecodeN n (envAt t i) 1).to else (moveDecodeN n (envAt t i) 0).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 0 (by norm_num) W.base.lt_p hftaB htxa htya htxb htyb x y hx hy
    simpa using h
  have hdb : (envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord)
           = (if (envAt t i).loc (NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) 0).to else (moveDecodeN n (envAt t i) 1).to)
        then (1 : ℤ) else 0 := by
    have h := dstIndV2N_of_sat hsat hc i hi 1 (by norm_num) W.base.lt_p hftbB htxb htyb htxa htya x y hx hy
    simpa using h
  have hn0 : 0 < n := by omega
  have hyy : y = (y * n + x) / n := by
    rw [Nat.add_comm, Nat.mul_comm y n, Nat.add_mul_div_left x y hn0, Nat.div_eq_of_lt hx,
      Nat.zero_add]
  have hxx : x = (y * n + x) % n := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hwb := writeCellV4N_of_sat hsat i hi (y * n + x) y x hyy hxx hcK
  have hmv := midV4CellN_of_sat hsat i hi (y * n + x) hcK
  have hbdcell := oldCell_decode x y (envAt t i) hx hy
  -- ============ fold ============
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  set destV2A : Coord := if e.loc (NGen.cFtV2A n) = 1 then mb.to else ma.to with hdestV2A
  set destV2B : Coord := if e.loc (NGen.cFtV2B n) = 1 then ma.to else mb.to with hdestV2B
  have hcc0 : NGen.carryV4Col n 0 = NGen.cCarryV4 n 0 := rfl
  have hcc1 : NGen.carryV4Col n 1 = NGen.cCarryV4 n 1 := rfl
  have hdA : destV2A = ma.to := by rw [hdestV2A, if_neg (by rw [hfta0]; norm_num)]
  have hdB : destV2B = mb.to := by rw [hdestV2B, if_neg (by rw [hftb0]; norm_num)]
  -- occlusion(1) ↔ `blockedB … mb`, and `blockedB … mb = blockedB … ma` (identical move)
  have hocc1I : e.loc (NGen.cOccIncl n 1) = 1 ↔ blockedB bd [ma, mb] mb = true := by
    have hh := blockedV2N_of_sat hsat hc i hi W 1 (by norm_num)
    rw [Dregg2.Games.AutomataflRules.blockedB_swap] at hh
    simpa using hh
  have hblkeq : blockedB bd [ma, mb] mb = blockedB bd [ma, mb] ma :=
    (Dregg2.Games.AutomataflRules.blockedB_identical bd ma mb hsrc hto).symm
  -- the single-mover characterization of BOTH final carries (hne-free). The nonleaver is killed by
  -- the OTHER carry: on an identical move BOTH pieces carry, so `cCv2 (1−which) = 1`.
  have hC0 : e.loc (NGen.cCarryV4 n 0) = 1 ↔
      (carAt bd ma.frm = true ∧ blockedB bd [ma, mb] ma = false) := by
    constructor
    · intro h
      have h2 := (hcv3aI.mp (hcv4aI.mp h).1).1
      obtain ⟨-, hnz, hoccz⟩ := hcv2_0I.mp h2
      refine ⟨by have hv : (bd.cellAt ma.frm).isVacuum = false := F.anzIff.mp hnz
                 simp [carAt, hv], ?_⟩
      by_cases hbb : blockedB bd [ma, mb] ma = true
      · exfalso; rw [hocc0I.mpr hbb] at hoccz; exact absurd hoccz (by norm_num)
      · simpa using hbb
    · rintro ⟨hcar, hb⟩
      have hoccz0 : e.loc (NGen.cOccIncl n 0) = 0 := by
        rcases hocc0B with h | h
        · exact h
        · exact absurd (hocc0I.mp h) (by rw [hb]; decide)
      have hbmb : blockedB bd [ma, mb] mb = false := by rw [hblkeq]; exact hb
      have hoccz1 : e.loc (NGen.cOccIncl n 1) = 0 := by
        rcases hocc1B with h | h
        · exact h
        · exact absurd (hocc1I.mp h) (by rw [hbmb]; decide)
      have hnza : e.loc (NGen.cAnz n) = 1 := F.anzIff.mpr (by simpa [carAt] using hcar)
      have hnzb : e.loc (NGen.cBnz n) = 1 := F.bnzIff.mpr (by rw [← hsrc]; simpa [carAt] using hcar)
      have hcv2_0_one : e.loc (NGen.cCv2 n 0) = 1 := hcv2_0I.mpr ⟨hsurv, hnza, hoccz0⟩
      have hcv2_1_one : e.loc (NGen.cCv2 n 1) = 1 := hcv2_1I.mpr ⟨hsurv, hnzb, hoccz1⟩
      have hnl0 : e.loc (NGen.cNonLeaveV2 n 0) = 0 := by
        rcases hnlaB with h | h
        · exact h
        · exact absurd (hnlaI.mp h).2 (by rw [hcv2_1_one]; norm_num)
      exact hcv4aI.mpr ⟨hcv3aI.mpr ⟨hcv2_0_one, hnl0⟩, htc0⟩
  have hC1 : e.loc (NGen.cCarryV4 n 1) = 1 ↔
      (carAt bd ma.frm = true ∧ blockedB bd [ma, mb] ma = false) := by
    constructor
    · intro h
      have h2 := (hcv3bI.mp (hcv4bI.mp h).1).1
      obtain ⟨-, hnz, hoccz⟩ := hcv2_1I.mp h2
      refine ⟨by have hv : (bd.cellAt ma.frm).isVacuum = false := by
                   rw [hsrc]; exact F.bnzIff.mp hnz
                 simp [carAt, hv], ?_⟩
      by_cases hbb : blockedB bd [ma, mb] ma = true
      · exfalso
        have hbmb : blockedB bd [ma, mb] mb = true := by rw [hblkeq]; exact hbb
        rw [hocc1I.mpr hbmb] at hoccz; exact absurd hoccz (by norm_num)
      · simpa using hbb
    · rintro ⟨hcar, hb⟩
      have hoccz0 : e.loc (NGen.cOccIncl n 0) = 0 := by
        rcases hocc0B with h | h
        · exact h
        · exact absurd (hocc0I.mp h) (by rw [hb]; decide)
      have hbmb : blockedB bd [ma, mb] mb = false := by rw [hblkeq]; exact hb
      have hoccz1 : e.loc (NGen.cOccIncl n 1) = 0 := by
        rcases hocc1B with h | h
        · exact h
        · exact absurd (hocc1I.mp h) (by rw [hbmb]; decide)
      have hnza : e.loc (NGen.cAnz n) = 1 := F.anzIff.mpr (by simpa [carAt] using hcar)
      have hnzb : e.loc (NGen.cBnz n) = 1 := F.bnzIff.mpr (by rw [← hsrc]; simpa [carAt] using hcar)
      have hcv2_0_one : e.loc (NGen.cCv2 n 0) = 1 := hcv2_0I.mpr ⟨hsurv, hnza, hoccz0⟩
      have hcv2_1_one : e.loc (NGen.cCv2 n 1) = 1 := hcv2_1I.mpr ⟨hsurv, hnzb, hoccz1⟩
      have hnl1 : e.loc (NGen.cNonLeaveV2 n 1) = 0 := by
        rcases hnlbB with h | h
        · exact h
        · exact absurd (hnlbI.mp h).2 (by rw [hcv2_0_one]; norm_num)
      exact hcv4bI.mpr ⟨hcv3bI.mpr ⟨hcv2_1_one, hnl1⟩, htc0⟩
  -- indicator readings + write-cell polynomial (identical to §25's derivation)
  have hsa := F.srcIndA x y hx hy
  have hsb := F.srcIndB x y hx hy
  have hda' : e.loc (NGen.wDstV2Row n 0 y) * e.loc (NGen.wDstV2Col n 0 x)
      = if (⟨x, y⟩ : Coord) = destV2A then (1 : ℤ) else 0 := hda
  have hdb' : e.loc (NGen.wDstV2Row n 1 y) * e.loc (NGen.wDstV2Col n 1 x)
      = if (⟨x, y⟩ : Coord) = destV2B then (1 : ℤ) else 0 := hdb
  have hcarryV4_collapse : e.loc (NGen.cResolvableV2 n) = 0 →
      e.loc (NGen.cCarryV4 n 0) = 0 ∧ e.loc (NGen.cCarryV4 n 1) = 0 := by
    intro hrv0
    have hnot : ¬ (e.loc (NGen.cMergeV2 n) = 0
        ∧ (e.loc (NGen.cCv2 n 0) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 0) = 0)
        ∧ (e.loc (NGen.cCv2 n 1) = 0 ∨ e.loc (NGen.cNonLeaveV2 n 1) = 0)) := by
      intro h; rw [hresI.mpr h] at hrv0; exact absurd hrv0 (by norm_num)
    have cv4a0_of_cv3a0 : e.loc (NGen.cCarryV3 n 0) = 0 → e.loc (NGen.cCarryV4 n 0) = 0 := by
      intro h; rcases hcv4aB with hz | ho
      · exact hz
      · exact absurd (hcv4aI.mp ho).1 (by rw [h]; norm_num)
    have cv4b0_of_cv3b0 : e.loc (NGen.cCarryV3 n 1) = 0 → e.loc (NGen.cCarryV4 n 1) = 0 := by
      intro h; rcases hcv4bB with hz | ho
      · exact hz
      · exact absurd (hcv4bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_cv2a0 : e.loc (NGen.cCv2 n 0) = 0 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).1 (by rw [h]; norm_num)
    have cv3b0_of_cv2b0 : e.loc (NGen.cCv2 n 1) = 0 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).1 (by rw [h]; norm_num)
    have cv3a0_of_nla : e.loc (NGen.cNonLeaveV2 n 0) = 1 → e.loc (NGen.cCarryV3 n 0) = 0 := by
      intro h; rcases hcv3aB with hz | ho
      · exact hz
      · exact absurd (hcv3aI.mp ho).2 (by rw [h]; norm_num)
    have cv3b0_of_nlb : e.loc (NGen.cNonLeaveV2 n 1) = 1 → e.loc (NGen.cCarryV3 n 1) = 0 := by
      intro h; rcases hcv3bB with hz | ho
      · exact hz
      · exact absurd (hcv3bI.mp ho).2 (by rw [h]; norm_num)
    by_cases hbadA : e.loc (NGen.cCv2 n 0) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 0) = 1
    · obtain ⟨_, hn0⟩ := hbadA
      have hc1z : e.loc (NGen.cCv2 n 1) = 0 := by simpa using (hnlaI.mp hn0).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_nla hn0), cv4b0_of_cv3b0 (cv3b0_of_cv2b0 hc1z)⟩
    · have hbadB : e.loc (NGen.cCv2 n 1) = 1 ∧ e.loc (NGen.cNonLeaveV2 n 1) = 1 := by
        by_contra hbn
        apply hnot
        refine ⟨hmergeZero, ?_, ?_⟩
        · rcases hcv2_0B with h | h
          · exact Or.inl h
          · rcases hnlaB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbadA
        · rcases hcv2_1B with h | h
          · exact Or.inl h
          · rcases hnlbB with h2 | h2
            · exact Or.inr h2
            · exact absurd ⟨h, h2⟩ hbn
      obtain ⟨_, hn1⟩ := hbadB
      have hc0z : e.loc (NGen.cCv2 n 0) = 0 := by simpa using (hnlbI.mp hn1).2
      exact ⟨cv4a0_of_cv3a0 (cv3a0_of_cv2a0 hc0z), cv4b0_of_cv3b0 (cv3b0_of_nlb hn1)⟩
  have hmidwb : e.loc (NGen.cMidV4 n (y * n + x)) ≡ e.loc (NGen.cWBoardV4 n (y * n + x))
      [ZMOD 2013265921] := by
    rcases hresB with hr0 | hr1
    · obtain ⟨hca0, hcb0⟩ := hcarryV4_collapse hr0
      have hwb0 := hwb
      rw [hcc0, hcc1, hca0, hcb0] at hwb0
      have hwbold : e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ e.loc (NGen.old n (y * n + x))
          [ZMOD 2013265921] := by
        calc e.loc (NGen.cWBoardV4 n (y * n + x)) ≡ _ [ZMOD 2013265921] := hwb0
          _ = e.loc (NGen.old n (y * n + x)) := by ring
      calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.old n (y * n + x)) := by rw [hr0]; ring
        _ ≡ e.loc (NGen.cWBoardV4 n (y * n + x)) [ZMOD 2013265921] := hwbold.symm
    · calc e.loc (NGen.cMidV4 n (y * n + x))
          ≡ e.loc (NGen.cResolvableV2 n) * e.loc (NGen.cWBoardV4 n (y * n + x))
            + e.loc (NGen.old n (y * n + x))
            - e.loc (NGen.cResolvableV2 n) * e.loc (NGen.old n (y * n + x)) [ZMOD 2013265921] := hmv
        _ = e.loc (NGen.cWBoardV4 n (y * n + x)) := by rw [hr1]; ring
  have hmod : e.loc (NGen.cMidV4 n (y * n + x))
      ≡ (1 - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
           - e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
           + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
               * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)))
          * e.loc (NGen.old n (y * n + x))
        + e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 0)
        + e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)
            * e.loc (NGen.particleCol n 1)
        - e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)
            * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0))
            * e.loc (NGen.particleCol n 1)
      [ZMOD 2013265921] := by
    have hwb1 := hwb
    rw [hcc0, hcc1, hsa, hsb, hda', hdb'] at hwb1
    exact hmidwb.trans hwb1
  have bA : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = ma.frm <;> simp [h, q]
  have bB : e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 := by
    rcases hcv4aB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2A <;> simp [h, q]
  have bC : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = mb.frm <;> simp [h, q]
  have bD : e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 0
      ∨ e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1 := by
    rcases hcv4bB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destV2B <;> simp [h, q]
  have eAB : (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 0) * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0)) = 0 := by
    have hdne : destV2A ≠ ma.frm := by rw [hdA]; exact hds
    by_cases q1 : (⟨x, y⟩ : Coord) = ma.frm
    · by_cases q2 : (⟨x, y⟩ : Coord) = destV2A
      · exact absurd (q2.symm.trans q1) hdne
      · simp [q2]
    · simp [q1]
  have eCD : (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
      * (e.loc (NGen.cCarryV4 n 1) * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0)) = 0 := by
    have hdne : destV2B ≠ mb.frm := by rw [hdB]; exact fun h => hlegB h.symm
    by_cases q1 : (⟨x, y⟩ : Coord) = mb.frm
    · by_cases q2 : (⟨x, y⟩ : Coord) = destV2B
      · exact absurd (q2.symm.trans q1) hdne
      · simp [q2]
    · simp [q1]
  have holdc : 0 ≤ e.loc (NGen.old n (y * n + x)) ∧ e.loc (NGen.old n (y * n + x)) ≤ 3 := by
    rcases F.alphaOld (y * n + x) hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hmidc : Canon (e.loc (NGen.cMidV4 n (y * n + x))) := canon_loc hc i _
  have hpaA : 0 ≤ e.loc (NGen.particleCol n 0) ∧ e.loc (NGen.particleCol n 0) ≤ 3 := by
    rcases F.paAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hpbA : 0 ≤ e.loc (NGen.particleCol n 1) ∧ e.loc (NGen.particleCol n 1) ≤ 3 := by
    rcases F.pbAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have halg := AutomataflResolveRefine.cellAlgebra bA bB bC bD eAB eCD holdc hmidc hpaA hpbA hmod
  -- the reference identical-move cell
  have hInA : bd.inBounds ma.to := F.validA.2.2.2.1
  have hq : bd.inBounds (⟨x, y⟩ : Coord) := ⟨hx, hy⟩
  rw [resolveMoves_cell_identical bd ma mb hsrc hto hlegA hInA ⟨x, y⟩ hq]
  rw [halg, apply_ite codeToParticle, apply_ite codeToParticle, apply_ite codeToParticle,
    show codeToParticle 0 = Particle.vacuum from by decide, ← F.paVal, ← F.pbVal, hbdcell]
  -- match branch-for-branch: both carries agree with the single-mover condition; `destV2A = destV2B = ma.to`
  by_cases hcarry : carAt bd ma.frm = true ∧ blockedB bd [ma, mb] ma = false
  · rw [if_pos hcarry]
    have hc40 : e.loc (NGen.cCarryV4 n 0) = 1 := hC0.mpr hcarry
    have hc41 : e.loc (NGen.cCarryV4 n 1) = 1 := hC1.mpr hcarry
    by_cases hxyd : (⟨x, y⟩ : Coord) = ma.to
    · rw [if_pos (show e.loc (NGen.cCarryV4 n 0)
              * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 by
            rw [hdA, if_pos hxyd, hc40]; ring), if_pos hxyd]
    · rw [if_neg (show ¬ e.loc (NGen.cCarryV4 n 0)
              * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 by
            rw [hdA, if_neg hxyd]; simp),
        if_neg (show ¬ e.loc (NGen.cCarryV4 n 1)
              * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1 by
            rw [hdB, if_neg (hto ▸ hxyd)]; simp),
        if_neg hxyd]
      by_cases hxys : (⟨x, y⟩ : Coord) = ma.frm
      · rw [if_pos (Or.inl (show e.loc (NGen.cCarryV4 n 0)
              * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1 by
            rw [if_pos hxys, hc40]; ring)), if_pos hxys]
      · rw [if_neg (show ¬ (e.loc (NGen.cCarryV4 n 0)
                * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1
              ∨ e.loc (NGen.cCarryV4 n 1)
                * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1) by
            rintro (h | h)
            · rw [if_neg hxys] at h; simp at h
            · rw [← hsrc, if_neg hxys] at h; simp at h),
        if_neg hxys]
  · rw [if_neg hcarry]
    have hc40 : e.loc (NGen.cCarryV4 n 0) = 0 := by
      rcases hcv4aB with h | h
      · exact h
      · exact absurd (hC0.mp h) hcarry
    have hc41 : e.loc (NGen.cCarryV4 n 1) = 0 := by
      rcases hcv4bB with h | h
      · exact h
      · exact absurd (hC1.mp h) hcarry
    rw [if_neg (show ¬ e.loc (NGen.cCarryV4 n 0)
            * (if (⟨x, y⟩ : Coord) = destV2A then (1:ℤ) else 0) = 1 by rw [hc40]; simp),
      if_neg (show ¬ e.loc (NGen.cCarryV4 n 1)
            * (if (⟨x, y⟩ : Coord) = destV2B then (1:ℤ) else 0) = 1 by rw [hc41]; simp),
      if_neg (show ¬ (e.loc (NGen.cCarryV4 n 0)
              * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1
            ∨ e.loc (NGen.cCarryV4 n 1)
              * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1) by
          rintro (h | h)
          · rw [hc40] at h; simp at h
          · rw [hc41] at h; simp at h)]

end EdgeCCell

/-! ## §28 — THE RESOLVE CAPSTONE: `resolve_sat_imp_roundBoardN`, UNCONDITIONAL, arbitrary `n`.

The decoded FINAL board cell `cMidV4` IS the board `AutomataflRules.roundStep` produces this round:
`old` on a clash (`clashCoords ≠ []`, the round re-enters unchanged) and the VALIDATED `resolveMoves`
cell otherwise — at EVERY in-bounds coordinate, off nothing but `Satisfied2 (automataflResolveDescN n)`
and `StepCanon`, at ARBITRARY board size `n`. Dispatches the surviving round into the three
EXHAUSTIVE sub-cases (§25 clean-distinct / §26 shared-dest-vacuum / §27 identical) via the `surv ↔
clashCoords = []` bridge (§24) and the reference `survIff` fork/collide structure; the clash branch is
§24's `midV4_cell_old_of_surv_zero`. -/
section RoundBoard
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (carAt clashCoords resolveMoves)

/-- **THE RESOLVE CAPSTONE.** `codeToParticle (cMidV4 …)` IS the `roundStep` board cell — `old` on a
clash, the VALIDATED `resolveMoves` cell otherwise — unconditionally, at arbitrary `n`. -/
theorem resolve_sat_imp_roundBoardN
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (x y : Nat) (hx : x < n) (hy : y < n) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 n (y * n + x)))
      = (if clashCoords (boardDecodeOldN n (envAt t i))
            [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] ≠ []
          then boardDecodeOldN n (envAt t i)
          else resolveMoves (boardDecodeOldN n (envAt t i))
            [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  have F := AutomataflResolveCapstone.resolveFactsN_of_sat hsat hc i hi W.base
  by_cases hcl : clashCoords (boardDecodeOldN n (envAt t i))
      [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] = []
  · rw [if_neg (fun h => h hcl)]
    have hsurv : (envAt t i).loc (NGen.cSurv n) = 1 :=
      (surv_iff_clash_empty_of_sat hsat hc i hi W).mpr hcl
    have hns := F.survIff.mp hsurv
    by_cases hsrc : (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm
    · have hto : (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to := by
        by_contra hdd; exact hns (Or.inl ⟨hsrc, hdd⟩)
      exact identicalMoveBoardCell hsat hc i hi W hsurv hsrc hto x y hx hy
    · by_cases hdst : (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to
      · have hnbc : ¬(carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true
              ∧ carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true) := by
          rintro ⟨ha, hb⟩
          exact hns (Or.inr ⟨hdst, hsrc, by simpa [carAt] using ha, by simpa [carAt] using hb⟩)
        exact sharedDestVacuumBoardCell hsat hc i hi W hsurv hsrc hdst hnbc x y hx hy
      · exact cleanDistinctBoardCell hsat hc i hi W hsurv hsrc hdst x y hx hy
  · rw [if_pos hcl]
    have hsurv0 : (envAt t i).loc (NGen.cSurv n) = 0 := by
      rcases F.survB with h | h
      · exact h
      · exact absurd ((surv_iff_clash_empty_of_sat hsat hc i hi W).mp h) hcl
    exact midV4_cell_old_of_surv_zero hsat hc i hi W hsurv0 x y hx hy

/-- The capstone at `n = 11` (the deployed 11×11 automatafl board). -/
theorem resolve_sat_imp_roundBoard11
    (hsat : Satisfied2 hash (automataflResolveDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (x y : Nat) (hx : x < 11) (hy : y < 11) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 11 (y * 11 + x)))
      = (if clashCoords (boardDecodeOldN 11 (envAt t i))
            [moveDecodeN 11 (envAt t i) 0, moveDecodeN 11 (envAt t i) 1] ≠ []
          then boardDecodeOldN 11 (envAt t i)
          else resolveMoves (boardDecodeOldN 11 (envAt t i))
            [moveDecodeN 11 (envAt t i) 0, moveDecodeN 11 (envAt t i) 1]).cellAt ⟨x, y⟩ :=
  resolve_sat_imp_roundBoardN hsat hc i hi movesWindow_eleven x y hx hy

/-- The capstone at `n = 3` (the small board the decide-verified branch witnesses live on). -/
theorem resolve_sat_imp_roundBoard3
    (hsat : Satisfied2 hash (automataflResolveDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (x y : Nat) (hx : x < 3) (hy : y < 3) :
    codeToParticle ((envAt t i).loc (NGen.cMidV4 3 (y * 3 + x)))
      = (if clashCoords (boardDecodeOldN 3 (envAt t i))
            [moveDecodeN 3 (envAt t i) 0, moveDecodeN 3 (envAt t i) 1] ≠ []
          then boardDecodeOldN 3 (envAt t i)
          else resolveMoves (boardDecodeOldN 3 (envAt t i))
            [moveDecodeN 3 (envAt t i) 0, moveDecodeN 3 (envAt t i) 1]).cellAt ⟨x, y⟩ :=
  resolve_sat_imp_roundBoardN hsat hc i hi movesWindow_three x y hx hy

/-! The reference side of the connection: what `roundStep` does with a two-move round. Note the
resolved board is `automatonStepCfg cfg (resolveMoves …)` — roundStep applies the automaton step AFTER
resolution, so `cMidV4` (which `resolve_sat_imp_roundBoardN` pins to `resolveMoves`/`old`) is the
PRE-automaton board roundStep resolves from / re-enters with, NOT the post-automaton output. The
automaton step is a SEPARATE (step) leg. -/

/-- The board an outcome carries: the re-entry board on `.again`, the resolved board on `.resolved`. -/
def outcomeBoard : Dregg2.Games.AutomataflRules.RoundOutcome → Board
  | .again rs => rs.board
  | .resolved b _ => b

open Dregg2.Games.AutomataflRules (roundStep openRound moveLegalB automatonStepCfg resolvableB
  unresolved GameConfig GoalAssignment)

/-- **THE `roundStep` REDUCTION (reference side).** On a two-move round whose fresh-move filter keeps
both moves and which is resolvable, `roundStep` re-enters with the OLD board on a clash and resolves
via `automatonStepCfg cfg (resolveMoves …)` otherwise. Composed with `resolve_sat_imp_roundBoardN`
(`cMidV4 = old`/`resolveMoves`) this identifies `cMidV4` as the board `roundStep` resolves from /
re-enters with — before the automaton step. -/
theorem roundStep_pair_outcomeBoard (cfg : GameConfig) (g : GoalAssignment) (b : Board)
    (seats : List Dregg2.Games.Automatafl.Pid) (ma mb : Move)
    (hfresh : ([ma, mb].filter (fun m => seats.contains m.who && moveLegalB b [] m)) = [ma, mb])
    (hres : resolvableB b [ma, mb] = true) :
    outcomeBoard (roundStep cfg g (openRound b seats) [ma, mb]) =
      (if clashCoords b [ma, mb] = []
       then automatonStepCfg cfg (resolveMoves b [ma, mb]) else b) := by
  have hunres : unresolved b [ma, mb] = [] := List.isEmpty_iff.mp hres
  unfold roundStep openRound outcomeBoard
  simp only [List.nil_append, hfresh]
  by_cases hcl : clashCoords b [ma, mb] = []
  · rw [if_pos hcl]
    simp only [hcl, List.isEmpty_nil, if_true, hunres]
  · rw [if_neg hcl]
    have hne : (clashCoords b [ma, mb]).isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff]; exact hcl
    simp only [hne, Bool.false_eq_true, if_false]

end RoundBoard

/-! ## §8 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#assert_axioms movesWindow_three
#assert_axioms blockedV2N_of_sat
#assert_axioms flowThroughOcclusionGap_witness_n3
-- CHUNK-5 corrected-surface (V3) extraction, off `Satisfied2 (automataflResolveDescN n)`:
#assert_axioms ftV2AN_of_sat
#assert_axioms ftV2BN_of_sat
#assert_axioms nonLeaveV2GateN_of_sat
#assert_axioms cv2ValN_of_sat
#assert_axioms carryV3ArithN_of_sat
#assert_axioms resolvableV2ArithN_of_sat
#assert_axioms dstIndV2N_of_sat
#assert_axioms ftV2A_inclBlocked_kills_flowThrough
-- CHUNK-5 corrected-landing occupancy read (the connective the landing correspondence consumes):
#assert_axioms gridProdInd_collapse
#assert_axioms landOldV2N_of_sat
#assert_axioms landNzV2N_of_sat
-- THE THIRD WOUND (2-cycle STAY): the spec-side falsifier the V3 surface does not close.
#assert_axioms twoCycleStay_witness_n3
-- CHUNK-6 FINAL corrected-surface (V4) extraction, off `Satisfied2 (automataflResolveDescN n)`:
#assert_axioms twoCycN_of_sat
#assert_axioms carryV4ArithN_of_sat
#assert_axioms midV4CellN_of_sat
#assert_axioms writeCellV4N_of_sat
-- THE SEVENTH WOUND, CLOSED (vacuum-far 2-cycle, README 3.5b): the occupancy-blind `cTwoCyc` (`anz · bnz`
-- dropped) now KEEPS A, matching the reference — this witness anchors that agreement.
#assert_axioms vacuumTwoCycleStay_witness_n3
-- WHY the fork/collide reference is `roundStep`, not raw `resolveMoves`.
#assert_axioms collideOneBlocked_rawResolveMoves_moves_witness
-- §22 THE LANDING CORRESPONDENCE — all six landMap arms, both pieces (the capstone target).
#assert_axioms landV4CorrespondenceA_of_sat
#assert_axioms landV4CorrespondenceB_of_sat
-- §22b/§22c THE CONFLUENCE EXTRACTION — cMergeV2 semantic characterization, the cResEqV2 Coord
-- bridge, and the clean-case cMergeV2 = 0 (no confluence on a surviving distinct-dest pair).
#assert_axioms mergeV2N_of_sat
#assert_axioms destV2PinN
#assert_axioms resEqV2CoordN_of_sat
#assert_axioms mergeV2_zero_of_distinctDest
-- §23 THE CLASH-CASE CELL — a fork/collide row leaves the FINAL board = OLD (roundStep re-entry).
#assert_axioms midV4_old_of_surv_zero
-- §24 THE ASSEMBLY CONNECTIVES — surv↔clash bridge, and the clash board branch (particle level).
#assert_axioms surv_iff_clash_empty_of_sat
#assert_axioms midV4_cell_old_of_surv_zero
-- §25 THE CLEAN DISTINCT BOARD CELL — the decoded FINAL board cell IS the VALIDATED `resolveMoves`
-- cell on the clean distinct (distinct raw src AND dst) class, ∀ in-bounds (x, y), at arbitrary `n`.
#assert_axioms cleanDistinctBoardCell
-- §26 THE SHARED-DEST SINGLE-VACUUM BOARD CELL — edge `da = db`, one source vacuum (¬both-carry):
-- one effective mover; `cMidV4` IS the `resolveMoves` cell via the `_sep` collapse, ∀ (x, y), any `n`.
#assert_axioms mergeV2_zero_of_notBothNz
#assert_axioms sharedDestVacuumBoardCell
-- §27 THE IDENTICAL-MOVE BOARD CELL — edge `sa = sb`, `da = db` (dedups to one mover); `cMidV4` IS
-- the `resolveMoves` cell via the hne-free single-mover correspondence, ∀ (x, y), any `n`.
#assert_axioms identicalMoveBoardCell
-- §28 THE RESOLVE CAPSTONE — `codeToParticle (cMidV4)` IS the roundStep board cell (old on clash, the
-- VALIDATED `resolveMoves` otherwise), UNCONDITIONAL, at arbitrary `n`, and at `n = 11` and `n = 3`.
#assert_axioms resolve_sat_imp_roundBoardN
#assert_axioms resolve_sat_imp_roundBoard11
#assert_axioms resolve_sat_imp_roundBoard3
-- The reference-side `roundStep` reduction: re-enter with old on clash, resolve via the automaton
-- step on `resolveMoves` otherwise — the honest connection (the automaton wrapping made explicit).
#assert_axioms roundStep_pair_outcomeBoard

end Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
