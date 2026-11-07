/-
# Dregg2.Circuit.Emit.WideCompactTable — the per-member S2-compaction table for the WIDE emit.

The block base `bb` per wide registry key (the face width `rotateV3` laid each member's rotated
BEFORE limbs at), assembled from the SAME sources the wide members were built from — positional
(`v3RegistryWideBB` / `v3RegistryCapOpenWideBB` / `v3RegistryCapOpenWriteWideTable`) plus the
avail-retargeted overrides. The values are CHECKED, not trusted: `compactForEmit` refuses to
compact a member unless `compactOk` proves its S2 stratum at that `bb` is exactly the expected
dead pair of 1-felt chains. A wrong `bb` cannot mis-compact — it fails the emit, closed.

The lane base is never tabulated: it is read off each member's own first S2 lookup
(`s2LaneBaseOf`) and re-verified wholesale by the shape check.
-/
import Dregg2.Circuit.Emit.RotWideCompactS2
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.HeapOpenEmit

namespace Dregg2.Circuit.Emit.WideCompactTable

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.RotWideCompactS2

/-- The avail-retargeted / separately-routed keys whose deployed face is NOT the positional
`v3RegistryWideBB` face, plus the live-only tail members. Checked by `compactOk` per member. -/
def wideBBSpecial : List (String × Nat) :=
  [ ("transferVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH)
  , ("burnVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH)
  , ("transferCapOpenEffVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH)
  , ("transferFeeVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmitTransfer.FEE_AVAIL_WIDTH)
  , ("transferCapOpenTBVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmitTransfer.AVAIL_WIDTH)
  , ("heapWriteVmDescriptor2R24",
      Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor.traceWidth)
  , ("supplyMintVmDescriptor2R24",
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintTickFace.traceWidth)
    -- the single-tick grain turn (initiative 10): rotated at the 188-wide face, like setField.
  , ("grainTurnVmDescriptor2R24", Dregg2.Circuit.Emit.EffectVmEmit.EFFECT_VM_WIDTH) ]
  ++ Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpenWriteWideTable.map
      (fun e => (e.1, e.2.2))

/-- The positional face-width table: the 45 emit-source keys aligned with their `bb` lists. -/
def wideBBPositional : List (String × Nat) :=
  (Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpenWide.map (·.1)).zip
    (Dregg2.Circuit.Emit.EffectVmEmitRotationWide.v3RegistryWideBB
      ++ Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpenWideBB)

/-- The block base for a wide registry key (specials shadow the positional table). -/
def bbFor (key : String) : Option Nat :=
  match wideBBSpecial.lookup key with
  | some bb => some bb
  | none => wideBBPositional.lookup key

/-- **The emit-side compaction** — compact a wide member at its tabulated `bb`, deriving the
lane base from the member itself, FAILING CLOSED unless the whole `compactOk` bundle holds.
Returns `(compact member, bb, laneBase)` — the geometry triple the Rust producer table carries. -/
def compactForEmit (key : String) (d : EffectVmDescriptor2) :
    Except String (EffectVmDescriptor2 × Nat × Nat) :=
  match bbFor key with
  | none => .error s!"S2-compact: no bb table entry for {key}"
  | some bb =>
    match s2LaneBaseOf d bb with
    | none => .error s!"S2-compact: {key} (bb={bb}) has no recognizable S2 stratum"
    | some lb =>
      if compactOk d bb lb then
        .ok (compactS2 d bb lb, bb, lb)
      else
        .error (s!"S2-compact REFUSED for {key} (bb={bb}, laneBase={lb}) — compactOk failed: "
          ++ "the S2 stratum is NOT the expected dead pair of rotated 1-felt chains "
          ++ "(the deletion premise is falsified; the emit fails closed)")

end Dregg2.Circuit.Emit.WideCompactTable
