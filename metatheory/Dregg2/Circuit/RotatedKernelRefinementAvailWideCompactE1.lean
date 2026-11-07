/-
# Dregg2.Circuit.RotatedKernelRefinementAvailWideCompactE1 — the transfer availability tooth,
restated over the DEPLOYED E1-COMPACTED wide member (Epoch-1 second flag-day: the dead v1-face
bands deleted), through the master bridge `RotWideCompactE1.compactE1_expand` STACKED on the S2
bridge.

## What this module is

Epoch-1 S2 deleted the two rotated 1-felt chains; E1 (this lane) additionally deletes the DEAD
v1-face column bands (the retired aux band `90 .. 187` including the 60-column balance
bit-decomposition, plus the gentian refuse tail) — 103 columns on the deployed transfer row,
`1704 → 1601`. The deployed `transferVmDescriptor2R24` row is now
`compactE1 (compactS2 transferAvailWideRefused 198 885) ks` where `ks = deadColsE1 (…) 90` is
the DERIVED per-member kill-set (every column at index `≥ 90` referenced by nothing surviving).

This module is the CROWN COROLLARY: a `Satisfied2` witness of the DEPLOYED E1-compact row expands
(E1 bridge) to a witness of the S2-compact member, and thence (the existing S2 crown) the whole
availability keystone chain fires. The wrap-forgery teeth hold of the object the light client
actually resolves.

## The two side conditions, by compiled evaluation

`compactE1Ok … = true` is discharged HERE from the cheap `transitionCeilingOk` (the only
member-specific fact — every `.transition` face column `≤ 89 < 90`), via the GENERIC gate lemma
`compactE1Ok_of_ceiling` (killability is unreferencedness by construction — no per-constraint
kernel cross-product). `transitionCeilingOk` is a fact about the deployed bytes, so it is checked by
compiled evaluation (`native_decide`; ember, 2026-11-06: concrete data by the compiler, general
theorems by the kernel).

## Axiom hygiene

`transferWide_ceilingOk` rests on its own `transferWide_ceilingOk._native.native_decide.ax_1_1`;
the keystones also rest on the compact module's side conditions
(`RotatedKernelRefinementAvailWideCompact`). Every pin below is therefore `#assert_compiled`, which
re-runs each such claim and refuses any other axiom; `RotTableSideW_expandG` is not pinned here.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact
import Dregg2.Circuit.Emit.RotWideCompactE1

namespace Dregg2.Circuit.RotatedKernelRefinementAvailWideCompactE1

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.RotWideCompactS2 (compactS2)
open Dregg2.Circuit.Emit.RotWideCompactE1
open Dregg2.Circuit.Emit.AvailWideMembers (transferAvailWideRefused)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW rotatedEncodesAvail)
open Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact (transferWideDeployedC)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option maxRecDepth 16000

/-- The face ceiling for the wide members: strictly above every `.transition` face column
(`sbCol`/`saCol` ≤ 89). -/
def E1_FLOOR : Nat := 90

/-- The E1-compact wide transfer row: the S2-compact crown member, additionally E1-compacted at
its DERIVED kill-set (the dead v1-face bands at index `≥ 90`). BYTE SOURCE (STAGED — the emit
driver's E1 pass is the deployment cutover, not yet landed): once `EmitWideRegistryProbe` applies
`compactE1` after `compactForEmit`, it emits `emitVmJson2` of exactly this value under the
`transferVmDescriptor2R24` key. At current HEAD the deployed transfer row is the S2-only
`transferWideDeployedC`; this theorem proves the availability keystone holds of the E1-compact row
the cutover will mint (the bridge is unconditional; the byte-identity to the deployed artifact
follows the emit cutover). -/
def transferWideDeployedE1 : EffectVmDescriptor2 :=
  compactE1 transferWideDeployedC (deadColsE1 transferWideDeployedC E1_FLOOR)

/-- The E1 emit gate, kernel-checked via the cheap ceiling: every `.transition` in the S2-compact
transfer row reads a face column below 90, so the DERIVED kill-set passes `compactE1Ok`. -/
theorem transferWide_ceilingOk : transitionCeilingOk transferWideDeployedC E1_FLOOR = true := by
  native_decide

/-- The whole E1 side-condition bundle, from the ceiling. -/
theorem transferWide_compactE1Ok :
    compactE1Ok transferWideDeployedC (deadColsE1 transferWideDeployedC E1_FLOOR) = true :=
  compactE1Ok_of_ceiling transferWideDeployedC E1_FLOOR transferWide_ceilingOk

/-- The wide table side transports onto the E1-expanded trace: `expandTraceG` leaves EVERY
auxiliary table (poseidon2, range) untouched, so the chip-faithfulness and range pins ride
verbatim. -/
theorem RotTableSideW_expandG {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ} {t : VmTrace}
    (ks : List Nat) (hside : RotTableSideW permOut hash t) :
    RotTableSideW permOut hash (expandTraceG ks t) :=
  { permWidth := hside.permWidth
  , chipHashIsLane0 := hside.chipHashIsLane0
  , chipTableFaithful := hside.chipTableFaithful
  , rangesWide := hside.rangesWide }

/-- **THE CROWN COROLLARY** — the availability + exact-debit forcing, over the DEPLOYED
E1-compacted wide transfer row. A satisfying witness of `transferWideDeployedE1` EXPANDS
(`compactE1_expand`) to a witness of the S2-compact crown member, and the landed S2 crown
(`availability_and_exact_move_forced_deployedCompact`) fires: `tr.amt ≤ pre.bal src a` and the
EXACT ℤ debit. The audit's wrap-forgery class is closed on the deployed Epoch-1 E1 bytes. -/
theorem availability_and_exact_move_forced_deployedE1 (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferWideDeployedE1 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs
      (Dregg2.Circuit.Emit.RotWideCompactS2.expandTrace permOut 198 885
        (expandTraceG (deadColsE1 transferWideDeployedC E1_FLOOR) t))
      pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  -- E1 expansion: Satisfied2 of the deployed E1 row → Satisfied2 of the S2-compact crown member
  have hsatS2 : Satisfied2 hash transferWideDeployedC minit mfin maddrs
      (expandTraceG (deadColsE1 transferWideDeployedC E1_FLOOR) t) :=
    compactE1_expand hash transferWideDeployedC (deadColsE1 transferWideDeployedC E1_FLOOR)
      minit mfin maddrs t transferWide_compactE1Ok hsat
  -- the S2 crown fires on the E1-expanded trace (table side transports; chip tables untouched)
  exact Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact.availability_and_exact_move_forced_deployedCompact
    hash hperm (RotTableSideW_expandG _ hside) hsatS2 pre post tr a henc

/-- The over-debit tooth on the deployed E1-compact row (the audit forgery class is UNSAT). -/
theorem deployedE1_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferWideDeployedE1 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs
      (Dregg2.Circuit.Emit.RotWideCompactS2.expandTrace permOut 198 885
        (expandTraceG (deadColsE1 transferWideDeployedC E1_FLOOR) t))
      pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (availability_and_exact_move_forced_deployedE1 hash hperm hside hsat
    pre post tr a henc).1
  omega

#assert_compiled transferWide_ceilingOk
#assert_compiled transferWide_compactE1Ok
#assert_compiled availability_and_exact_move_forced_deployedE1
#assert_compiled deployedE1_rejects_overdebit

end Dregg2.Circuit.RotatedKernelRefinementAvailWideCompactE1
