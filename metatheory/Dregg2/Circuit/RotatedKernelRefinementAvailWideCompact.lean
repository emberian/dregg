/-
# Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact — the transfer availability tooth,
restated over the DEPLOYED S2-COMPACTED wide member (Epoch 1), through the master bridge.

## What this module is

Epoch 1 deleted the S2 dead stratum (the two rotated 1-felt Merkle–Damgård chains) from every
wide registry member: the deployed `transferVmDescriptor2R24` row is now
`compactS2 transferAvailWideRefused 198 885` (`EmitWideRegistryProbe` emits exactly this value;
the `s2compact` companion line pins the geometry pair). This module is the CROWN COROLLARY of
the bridge (`RotWideCompactS2.compactS2_expand`): a `Satisfied2` witness of the DEPLOYED compact
row expands to a witness of the pre-compact member, and the whole availability keystone chain
(`RotatedKernelRefinementAvailWide`) fires on the expansion — so the wrap-forgery teeth hold of
the object the light client actually resolves, not of a retired sibling.

The per-member side condition `compactOk … = true` is a fact about the deployed descriptor's
concrete bytes, so it is discharged HERE by compiled evaluation (`native_decide`; ember,
2026-11-06: concrete data by the compiler, general theorems by the kernel): the same decidable
bundle the emit driver enforces at emit time. Kernel reduction (`decide +kernel`) took ~2 min and
14 GB for this module.

The decode (`rotatedEncodesAvail`) is stated over the EXPANDED trace. That is not a weakening:
`expandTrace_shape` pins the expansion to the compact trace row-for-row on every surviving
column (every column the decode reads — the face and ledger ties — survives; only the deleted
chain columns are recomputed), same row count, same public inputs. The remaining follow-up
(HORIZONLOG 2026-07-18) is the mechanical field-wise transport of the decode structure itself.

## Axiom hygiene

The two side conditions rest on their own `<theorem>._native.native_decide.ax_1_1` and are pinned
with `#assert_compiled`; so are the two keystones that use them. `RotTableSideW_expand` and
`expandTrace_tf_other` stay `#assert_axioms`-clean.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvailWide
import Dregg2.Circuit.Emit.RotWideCompactS2

namespace Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.RotWideCompactS2
open Dregg2.Circuit.Emit.AvailWideMembers (transferAvailWideRefused)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW rotatedEncodesAvail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option maxRecDepth 16000

/-- The DEPLOYED Epoch-1 wide transfer row: the refuse-carrying avail crown member, S2-compacted
at its emitted geometry (bb = 198 — the avail face width; lane base 885).

⚑ LANE BASE 877 -> 885 at the 2026-08-01 KEY-NONET flag day (`76c3f7b9b`, pre-limbs 184 -> 187),
and the number is READ, not re-derived here: `s2LaneBaseOf` takes it off the member's OWN first S2
lookup, the emit prints it on the `s2compact` companion line, and `circuit/src/effect_vm/
s2_compact_generated.rs` now carries `("transferVmDescriptor2R24", 198, 885)`. The move is +8 on
the lane base and 0 on `bb` for ALL 49 tabulated members — a flat delta, which is the cross-check
that the region shifted rather than any member's own geometry changing. Before this re-typing,
`decide` proved `compactOk transferAvailWideRefused 198 877 = false` and the three keystones below
went `sorryAx`-red. BYTE SOURCE:
`EmitWideRegistryProbe` emits `emitVmJson2` of exactly this value under the
`transferVmDescriptor2R24` key. -/
def transferWideDeployedC : EffectVmDescriptor2 :=
  compactS2 transferAvailWideRefused 198 885

/-- The emit gate, by compiled evaluation: the deployed transfer row's S2 stratum is EXACTLY the
expected dead pair of chains and nothing surviving touches a deleted column. (The same
decidable bundle the emit driver enforces; a falsifying member would refuse to emit AND
refuse to elaborate here.) -/
theorem transferWide_compactOk : compactOk transferAvailWideRefused 198 885 = true := by
  native_decide

/-- Non-poseidon2 tables are untouched by the expansion (the range/memory/map tables the
faithful side pins). -/
theorem expandTrace_tf_other (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace)
    (tid : TableId) (h : tid ≠ TableId.poseidon2) :
    (expandTrace permOut bb laneBase t).tf tid = t.tf tid := by
  simp [expandTrace, h]

/-- The wide table side transports onto the expanded trace (the chip extension is genuine, the
range pins ride untouched). -/
theorem RotTableSideW_expand {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ} {t : VmTrace}
    (bb laneBase : Nat) (hplan : planOk (s2Plan bb laneBase) = true)
    (hside : RotTableSideW permOut hash t) :
    RotTableSideW permOut hash (expandTrace permOut bb laneBase t) :=
  { permWidth := hside.permWidth
  , chipHashIsLane0 := hside.chipHashIsLane0
  , chipTableFaithful :=
      expandTrace_chipSoundN permOut bb laneBase t hplan hside.chipTableFaithful
  , rangesWide := by
      intro b hb
      rw [expandTrace_tf_other permOut bb laneBase t _ (by
        simp only [Dregg2.Circuit.Emit.EffectVmEmitV2.rangeTidW]
        split <;> simp)]
      exact hside.rangesWide b hb }

/-- `planOk` for the deployed transfer geometry (a projection of `compactOk`, decided once). -/
theorem transferWide_planOk : planOk (s2Plan 198 885) = true := by native_decide

/-- **THE CROWN COROLLARY** — the availability + exact-debit forcing, over the DEPLOYED
S2-compacted wide transfer row. A satisfying witness of `transferWideDeployedC` EXPANDS
(`compactS2_expand`) to a witness of the pre-compact refuse-carrying crown member, and the
landed keystone chain fires: `tr.amt ≤ pre.bal src a` and the EXACT ℤ debit. The audit's
wrap-forgery class is closed on the deployed Epoch-1 bytes. -/
theorem availability_and_exact_move_forced_deployedCompact (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferWideDeployedC minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs (expandTrace permOut 198 885 t)
      pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hsatX : Satisfied2 hash transferAvailWideRefused minit mfin maddrs
      (expandTrace permOut 198 885 t) :=
    compactS2_expand permOut hash hperm transferAvailWideRefused 198 885
      minit mfin maddrs t transferWide_compactOk hsat
  exact Dregg2.Circuit.RotatedKernelRefinementAvailWide.availability_and_exact_move_forced_refusedWide
    hash (RotTableSideW_expand 198 885 transferWide_planOk hside) hsatX pre post tr a henc

/-- The over-debit tooth on the deployed compact row (the audit forgery class is UNSAT). -/
theorem deployedCompact_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferWideDeployedC minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs (expandTrace permOut 198 885 t)
      pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (availability_and_exact_move_forced_deployedCompact hash hperm hside hsat
    pre post tr a henc).1
  omega

#assert_compiled transferWide_compactOk
#assert_compiled transferWide_planOk
#assert_compiled availability_and_exact_move_forced_deployedCompact
#assert_compiled deployedCompact_rejects_overdebit

end Dregg2.Circuit.RotatedKernelRefinementAvailWideCompact
