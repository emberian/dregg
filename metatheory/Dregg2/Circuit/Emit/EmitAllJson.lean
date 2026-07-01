/-
# Dregg2.Circuit.Emit.EmitAllJson — the EMIT-ALL executable (descriptor registry source).

Imports every effect's emit module and prints, for each emitted `EffectVmDescriptor`, a line

  `<LEAN_DEF_NAME>\t<descriptor.name>\t<emitVmJson descriptor>`

so the Rust descriptor registry (`circuit/src/effect_vm_descriptors.rs`) can be regenerated
byte-for-byte from the verified Lean emit. This is a SCRATCH executable (like `EmitCheck.lean`):
run it with `lake env lean --run Dregg2/Circuit/Emit/EmitAllJson.lean`.

The descriptor `name` is the canonical wire identity. NOTE: four selectors SHARE the attenuate
descriptor object (delegate / delegateAtten / revokeDelegation / introduce all `:= attenuateVmDescriptor`),
so the same JSON serves multiple effect selectors — the Rust registry maps selector → JSON, not
name → JSON, to capture this many-to-one fan-out.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
import Dregg2.Circuit.Emit.EffectVmEmitCreateCell
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmEmitDelegate
import Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitSpawn
import Dregg2.Circuit.Emit.EffectVmEmitRecordRoot
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape

open Dregg2.Circuit.Emit.EffectVmEmit

/-- One registry entry: the Lean def name + its emitted descriptor. -/
structure Entry where
  defName : String
  desc    : EffectVmDescriptor

open Dregg2.Circuit.Emit in
/-- Every emitted descriptor, paired with its Lean def name. The fully-qualified opens
keep this readable; the `attenuateVmDescriptor` reuses (delegate/delegateAtten/revoke/introduce)
are listed explicitly so the line count equals the distinct (selector-bearing) emit modules. -/
def allEntries : List Entry :=
  [ ⟨"transferVmDescriptor",            EffectVmEmitTransfer.transferVmDescriptor⟩
  , ⟨"attenuateVmDescriptor",           EffectVmEmitAttenuateA.attenuateVmDescriptor⟩
  , ⟨"bridgeMintVmDescriptor",          EffectVmEmitBridgeMint.bridgeMintVmDescriptor⟩
  , ⟨"burnVmDescriptor",                EffectVmEmitBurn.burnVmDescriptor⟩
  , ⟨"cellDestroyVmDescriptor",         EffectVmEmitCellDestroy.cellDestroyVmDescriptor⟩
  , ⟨"cellSealVmDescriptor",            EffectVmEmitCellSeal.cellSealVmDescriptor⟩
    -- cellUnseal (selector 50): the lifecycle Sealed→Live inverse, runtime-reconciled onto the
    -- SAME frozen-frame + nonce-tick row shape as cellSeal-v2; the lifecycle flip stays verified
    -- in-module (off-row, `cellUnsealA_full_sound`).
  , ⟨"cellUnsealVmDescriptor",          EffectVmEmitCellUnseal.cellUnsealVmDescriptor⟩
    -- LIFECYCLE/BIRTH graduations: the WIRE descriptor is the RUNTIME ACTOR row (frozen-frame +
    -- nonce-tick); the born-empty CHILD faces stay verified in-module (off-row content).
  , ⟨"createCellActorVmDescriptor",     EffectVmEmitCreateCell.createCellActorVmDescriptor⟩
  , ⟨"factoryActorVmDescriptor",        EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor⟩
  , ⟨"delegateVmDescriptor",            EffectVmEmitDelegate.delegateVmDescriptor⟩
  , ⟨"delegateAttenVmDescriptor",       EffectVmEmitDelegateAtten.delegateAttenVmDescriptor⟩
  , ⟨"emitEventVmDescriptor",           EffectVmEmitEmitEvent.emitEventVmDescriptor⟩
  , ⟨"exerciseVmDescriptor",            EffectVmEmitExercise.exerciseVmDescriptor⟩
  , ⟨"incrementNonceVmDescriptor",      EffectVmEmitIncrementNonce.incrementNonceVmDescriptor⟩
  , ⟨"introduceVmDescriptor",           EffectVmEmitIntroduce.introduceVmDescriptor⟩
  , ⟨"makeSovereignRuntimeVmDescriptor", EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor⟩
  , ⟨"mintVmDescriptor",                EffectVmEmitMint.mintVmDescriptor⟩
  , ⟨"noteCreateVmDescriptor",          EffectVmEmitNoteCreate.noteCreateVmDescriptor⟩
  , ⟨"noteSpendVmDescriptor",           EffectVmEmitNoteSpend.noteSpendVmDescriptor⟩
  , ⟨"pipelinedSendVmDescriptor",       EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor⟩
    -- (F2a) the six queue descriptors are GONE from the emit-all manifest: the queue family
    -- dissolved into the verified factory cells (`Dregg2/Apps/QueueFactory` et al).
  , ⟨"receiptArchiveActorVmDescriptor", EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor⟩
  , ⟨"refreshVmDescriptor",             EffectVmEmitRefreshDelegation.refreshVmDescriptor⟩
  , ⟨"refusalVmDescriptor",             EffectVmEmitRefusal.refusalVmDescriptor⟩
  , ⟨"revokeVmDescriptor",              EffectVmEmitRevokeDelegation.revokeVmDescriptor⟩
    -- RevokeCapability (selector 24): the GRADUATED cap-REMOVAL v1 FACE (cap-root MOVE + frame
    -- freeze, the SAME row shape as attenuate); the in-circuit sorted-tree slot DELETION is the v2
    -- leg (`revokeCapabilityVmDescriptor2`: held-membership map-read + ZERO-value remove-write).
  , ⟨"revokeCapabilityVmDescriptor",    EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor⟩
  , ⟨"setPermsVmDescriptor",            EffectVmEmitSetPermissions.setPermsVmDescriptor⟩
  , ⟨"setVKVmDescriptor",               EffectVmEmitSetVK.setVKVmDescriptor⟩
  , ⟨"spawnActorVmDescriptor",          EffectVmEmitSpawn.spawnActorVmDescriptor⟩
    -- RECORD-LAYER STAGE 2: transfer descriptor + `fields_root`-absorbing GROUP-4 (site 3's
    -- spare 4th input now binds the user-field-map root cell into `state_commit`). Width-neutral
    -- (186): the carrier is the existing `state.FIELDS_ROOT` (= RESERVED, col 89) within the base
    -- layout, so the generic descriptor interpreter runs it with no width change.
  , ⟨"recordVmDescriptor",              EffectVmEmitRecordRoot.recordVmDescriptor⟩
    -- CAP-RESHAPE CROWN (#103): the OPENABLE capability_root descriptor — non-amp (per-bit submask
    -- gates `granted ⊑ held`) + production-authority (the mint opens the issuer cap from the held-set
    -- root). Not selector-bound (the sdk authority-binding routes to it by name); byte-pinned by
    -- `circuit/src/cap_reshape_descriptor.rs` (a STANDALONE loader, not the locked selector registry).
  , ⟨"capReshapeVmDescriptor",          EffectVmEmitCapReshape.capReshapeVmDescriptor⟩
    -- GENUINE NON-AMP cap-graph descriptors (the ARGUS linchpin on the delegation family): the §G
    -- genuine cap-root RECOMPUTE (`new_cap_root = hash[edge_leaf, old_root]`, op-tagged) PLUS the
    -- in-circuit `granted ⊑ held` submask gate (`EffectVmEmitCapReshape.capDelegNonAmpGates`) on the
    -- SAME `rights` felt the recompute binds. So a verifying delegation/attenuate/introduce/revoke/
    -- refresh proof now means BOTH: the cap-root is genuinely recomputed (no opaque digest) AND the
    -- granted rights do not amplify (over-grant rejected in-circuit). Additive + width-neutral (186);
    -- the shared `attenuateVmDescriptorGenuineNonAmp` object backs all six (the op tag distinguishes
    -- the mutation, so one JSON serves the family — selector→JSON fan-out, like the v1 face above).
  , ⟨"attenuateVmDescriptorGenuineNonAmp", EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNonAmp⟩
  , ⟨"delegateVmDescriptorGenuineNonAmp",  EffectVmEmitDelegate.delegateVmDescriptorGenuineNonAmp⟩
  , ⟨"delegateAttenVmDescriptorGenuineNonAmp", EffectVmEmitDelegateAtten.delegateAttenVmDescriptorGenuineNonAmp⟩
  , ⟨"introduceVmDescriptorGenuineNonAmp",  EffectVmEmitIntroduce.introduceVmDescriptorGenuineNonAmp⟩
  , ⟨"revokeVmDescriptorGenuineNonAmp",     EffectVmEmitRevokeDelegation.revokeVmDescriptorGenuineNonAmp⟩
  , ⟨"refreshVmDescriptorGenuineNonAmp",    EffectVmEmitRefreshDelegation.refreshVmDescriptorGenuineNonAmp⟩ ]

def main : IO Unit := do
  for e in allEntries do
    IO.println s!"{e.defName}\t{e.desc.name}\t{emitVmJson e.desc}"
