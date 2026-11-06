/-
# Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated — the R=24 rotated member for the grain turn.

`grainTurnVmDescriptor2R24` is assembled exactly as the deployed `setFieldVmDescriptor2-{slot}R24`
members are (`EffectVmEmitRotationV3.v3RegistryBare`), generalised from one written slot to the five
grain slots:
  * `rotateV3` + the authority continuity weld (`frozenAuthorityColEqs`), with the fields completion
    freezes kept ONLY for the unwritten slots 0..2 (24 freezes; the per-slot member keeps 56);
  * `graduateV1`;
  * `withSelectorGate SEL_GRAIN_TURN` (a row is a NoOp pad or the grain row);
  * the IR-v2 window gate `grainNoSecondActiveRow` (no active row after row 0);
  * `withSetFieldCompletionPins j` for each grain slot `j` (8 lanes × 5 slots = 40 tail PIs
    publishing the high lanes of the five written 32-byte values).
The `withDfaRcPins` outermost wrap (`v3Registry`) and the wide twin (`wideAppend`, `v3RegistryWide`)
are the registry-entry steps; they are NOT applied here because this member is in no registry.

STATUS: design branch `i10-single-tick-grain-descriptor`, ember-gated. Not emitted, not deployed.
-/
import Dregg2.Circuit.Emit.EffectVmEmitGrainTurn
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitGrainTurn

set_option autoImplicit false

/-- The five grain slots. -/
def grainSlots : List (Fin 8) := [3, 4, 5, 6, 7]

#guard grainSlots == (List.finRange 8).filter (fun j => IsGrainSlot j)

/-- The fields completion freezes for the UNWRITTEN slots only (0..2): every completion lane not
owned by a grain slot stays frozen BEFORE↔AFTER. -/
def fieldsCompletionFreezesExceptGrain (w : Nat) : List VmConstraint :=
  (fieldsCompletionOffs.filter
      (fun off => !(grainSlots.any (fun j => (fieldsSlotLanes j).contains off)))).map
    (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

#guard (fieldsCompletionFreezesExceptGrain 186).length == 24

/-- `rotateV3` + the authority continuity weld + the unwritten-slot completion freezes. -/
def rotateV3FrozenAuthorityGrain (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with constraints :=
      r.constraints
        ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezesExceptGrain d.traceWidth) }

/-- The graduated rotated core. -/
def grainTurnV3Core : EffectVmDescriptor2 :=
  graduateV1 (rotateV3FrozenAuthorityGrain grainTurnVmDescriptor)

/-- Append the single-active-row window gate. -/
def withGrainWindow (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with constraints := g.constraints ++ [.windowGate grainNoSecondActiveRow] }

/-- Publish the completion lanes of all five written slots. -/
def withGrainCompletionPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  grainSlots.foldl (fun acc j => withSetFieldCompletionPins j acc) g

/-- **`grainTurnVmDescriptor2R24`** — the single-tick multi-field grain member (bare, pre-rc). -/
def grainTurnVmDescriptor2R24 : EffectVmDescriptor2 :=
  withGrainCompletionPins (withGrainWindow (withSelectorGate SEL_GRAIN_TURN grainTurnV3Core))

#guard grainTurnVmDescriptor2R24.piCount == grainTurnV3Core.piCount + 40
#guard grainTurnV3Core.traceWidth
  == (setFieldV3 3).traceWidth
#guard grainTurnVmDescriptor2R24.constraints.length
  == grainTurnV3Core.constraints.length + 1 + 1 + 40

/-- The window gate is a constraint of the member. -/
theorem window_mem :
    VmConstraint2.windowGate grainNoSecondActiveRow ∈ grainTurnVmDescriptor2R24.constraints := by
  unfold grainTurnVmDescriptor2R24 withGrainCompletionPins
  simp only [grainSlots, List.foldl_cons, List.foldl_nil, withSetFieldCompletionPins_constraints]
  simp [withGrainWindow]

end Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated
