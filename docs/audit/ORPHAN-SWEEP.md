# ORPHAN-SWEEP — defined-but-undeployed descriptors, keystones, and seams

**Adversarial Audit — the orphan sweep.** Repo `/Users/ember/dev/breadstuffs` @ `main`,
HEAD `c5de88508`. READ-ONLY census: this document + one scaffolded guard test edit nothing else.
Every row grounds to `file:line` at HEAD.

This is the **dual of R3** (`PRODUCER-DESCRIPTOR-COVERAGE.md`: *every deployed member has a test*).
This sweep asks the mirror question: **is every proven descriptor / keystone actually deployed?** R1
(`TRUST-BASE-CENSUS.md §6 R1`) exposed one instance — `v3OfFrozenSetField` + `setFieldV3_pins_value`
are green and axiom-clean but describe a descriptor the light client never runs (deployed setField
uses `v3OfFrozen`). That was a *class*, not a one-off. Below is the class, swept.

---

## 0. What "DEPLOYED" means here

A definition is **deployed** (reachable from the running system) iff it is reached by one of:

1. **The committed registries** — `circuit/descriptors/*.tsv`, `include_str!`'d by
   `circuit/src/effect_vm_descriptors.rs`. The **live** one is
   `rotation-v3-staged-registry.tsv` (58 members, 1-felt — the prover keeps using this per-map V3
   registry until the gated VK epoch flips, `effect_vm_descriptors.rs:572`). `rotation-wide-*` and
   `…-umem-welded-*` are **STAGED covers** (committed, wired ahead of the flag-day, not the running
   default).
2. **What the Lean registries emit** — the def-bodies of `v3RegistryBare`/`v3Registry`
   (`EffectVmEmitRotationV3.lean:5323/5372`), `v3RegistryCapOpen*` (`CapOpenEmit.lean:1280/1437/1670`),
   `v3RegistryWide` (`EffectVmEmitRotationWide.lean:1259`), `weldedWideRegistry`
   (`EffectVmEmitUMemWeldWide.lean:261`), `umemCohort{,Multi}Registry`.
3. **The Rust producers** — `circuit/src/effect_vm/trace_rotated.rs :: generate_rotated_*`.
4. **The verifier** — `circuit/src/descriptor_ir2.rs :: verify_vm_descriptor2`, and the
   `effect_vm_descriptors.rs` load path.

An **orphan** is a definition no deployed path reaches. Theorems and `#guard`s are **not** deployment
edges — a descriptor referenced only by a soundness theorem is proven, not shipped. That is exactly
how the dangerous class hides: a green `#assert_axioms` proof about a descriptor no registry lists.

Reachability was computed by transitive token-BFS over the `:=` bodies of all top-level `def`s from
the deployed roots (excluding `.claude/worktrees/**`), cross-checked against the committed TSV member
keys and the Rust load path.

---

## 1. Counts

**Descriptor def-sites** producing `EffectVmDescriptor2`/`EffectVmDescriptor` under
`metatheory/Dregg2/Circuit/`: **275** across **273** names.
- Reachable from a deployed registry: **150** (omitted below).
- **ORPHANS: 125 def-sites**, classified:

| Class | What | Count |
|---|---:|
| **A. superseded-predecessor (v2 cohort)** | the old `v2Registry` members the v3 cohort replaced | 21 |
| **B. superseded-predecessor (per-effect Wide/FullState builders)** | replaced by the generic `wideAppend`-over-`v3Registry` fold | 31 |
| **C. built-not-shipped (richer proven variant, plainer sibling deployed)** | the setField exemplar + all analogs | 34 |
| **D. faces never wired to any deployed registry** | whole effects / pre-V3 standalone faces | 15 |
| **E. scaffold / test / proof-only** | probes, demos, refinement-proof descriptors | 24 |
| **F. out-of-scope (Argus subtree)** | flagged, not in the swept globs | 4 |

**Keystone orphans** (theorems/`#assert_axioms` about an orphaned descriptor): the setField
refinement stack (8 `#assert_axioms` + `setField_descriptorComplete`) and the 3 dedicated-accumulator
8-felt keystones — see §3.

The **DANGEROUS** subset (keystones whose property the deployed light-client path genuinely lacks):
**2 families** — the dedicated accumulator roots (~31-bit lane-0 deployed vs proven 8-felt) and the
setField circuit-grounded refinement (deployed rides an *assumed* bridge + a large-write completeness
gap). Both are soundness-safe on a re-executing full node; both **misled the census** because the
green keystone reads as if the deployed descriptor has the property. See §3/§5.

---

## 2. Q1 — DESCRIPTOR / EMIT ORPHANS

Only the orphans are listed (the 150 deployed defs are omitted). "reach?" = reachable from a deployed
registry (no / only-v2). All file paths under `metatheory/Dregg2/Circuit/`.

### A. Superseded-predecessor — v2 cohort (reached ONLY by `v2Registry`, `Emit/EffectVmEmitV2.lean:1474`)

`transferVmDescriptor2`:717, `burnVmDescriptor2`:719, `mintVmDescriptor2`:721, `noteSpendVmDescriptor2`:723,
`noteCreateVmDescriptor2`:725, `cellSealVmDescriptor2`:727, `cellDestroyVmDescriptor2`:729,
`refusalVmDescriptor2`:731, `setPermsVmDescriptor2`:733, `setVKVmDescriptor2`:735, `exerciseVmDescriptor2`:737,
`pipelinedSendVmDescriptor2`:739, `refreshVmDescriptor2`:741, `incrementNonceVmDescriptor2`:743,
`revokeVmDescriptor2`:745, `introduceVmDescriptor2`:747, `attenuateVmDescriptor2`:1049,
`revokeCapabilityVmDescriptor2`:1141, `customVmDescriptor2`:1252, `setFieldDynVmDescriptor2`:1407
— all `Emit/EffectVmEmitV2.lean`. Plus **`attenuateVmDescriptor2Base`** (`:749`) — DEAD: even `v2Registry`
never reaches it (only a `#guard` length-compare references it).
**Classification: superseded (v2). Deploying: n/a — delete when the v2 epoch is closed.**

### B. Superseded-predecessor — per-effect Wide/FullState builders (replaced by generic `wideAppend`)

`v3RegistryWide` is `v3Registry.zip(...).map (wideAppend …)` — it re-wraps the live cohort and references
**none** of the per-effect `*VmDescriptorWide` defs; `weldedWideRegistry` maps `weldUMemIntoWide` over
`crownWideHosts`. So these individual builders are genuinely unreferenced:

`attenuateVmDescriptorWide` (`Emit/EffectVmEmitAttenuateA.lean:942`), `bridgeMintVmDescriptorWide`
(`Emit/EffectVmEmitBridgeMint.lean:514`), `burnVmDescriptorWide` (`Emit/EffectVmEmitBurnRunnable.lean:78`),
`cellDestroyVmDescriptorWide` (`…CellDestroyFullState.lean:45`), `cellSealVmDescriptorWide`
(`…CellSealFullState.lean:51`), `cellUnsealVmDescriptorWide` (`…CellUnseal.lean:273`),
`createCellVmDescriptorWide` (`…CreateCellFullState.lean:45`), `factoryVmDescriptorWide`
(`…CreateCellFromFactoryFullState.lean:43`), `delegateVmDescriptorWide` (`…Delegate.lean:287`),
`delegateAttenVmDescriptorWide` (`…DelegateAtten.lean:265`), `emitEventVmDescriptorWide`
(`…EmitEventWide.lean:101`), `exerciseVmDescriptorWide` (`…ExerciseWide.lean:107`),
`incrementNonceVmDescriptorWide` (`…IncrementNonceFullState.lean:62`), `introduceVmDescriptorWide`
(`…Introduce.lean:553`), `makeSovereignVmDescriptorWide` (`…MakeSovereignFullState.lean:46`),
`mintVmDescriptorWide` (`…MintRunnable.lean:74`), `noopVmDescriptorWide` (`…NoopWide.lean:92`),
`noteCreateVmDescriptorWide` (`…NoteCreate.lean:856`), `noteSpendVmDescriptorWide` (`…NoteSpend.lean:873`),
`pipelinedSendVmDescriptorWide` (`…PipelinedSendWide.lean:119`), `archiveVmDescriptorWide`
(`…ReceiptArchiveWide.lean:111`), `refreshVmDescriptorWide` (`…RefreshDelegation.lean:692`),
`refusalVmDescriptorWide` (`…RefusalFullState.lean:44`), `revokeDelegationVmDescriptorWide`
(`…RevokeDelegation.lean:566`), `setFieldVmDescriptorWide` (`…SetFieldFullState.lean:49`),
`setPermsVmDescriptorWide` (`…SetPermissionsFullState.lean:46`), `setVKVmDescriptorWide`
(`…SetVKFullState.lean:44`), `transferVmDescriptorWide` (`…FullStateRunnable.lean:347`), plus the
earlier wide-construction helpers `rotateV3Wide` (`…RotationWide.lean:510`), `v3OfWide` (`:529`),
`wideAppendOverGated` (`:1147`).
**Classification: superseded builders. Deploying: n/a — the deployed wide path replaces them.**

### C. BUILT-NOT-SHIPPED — richer proven variant defined, plainer sibling deployed

These are the true R1-class orphans: a *better* descriptor exists with proofs, but the registry ships
the plainer one.

**C1 — the setField exemplar** (registry `EffectVmEmitRotationV3.lean:5364` deploys
`withSelectorGate SEL_SET_FIELD (v3OfFrozen (setFieldTickFace slot))`):
| orphan | def | deploying takes |
|---|---|---|
| `rotateV3FrozenAuthoritySetField` | `Emit/EffectVmEmitRotationV3.lean:3110` | swap the registry wrap to the freeze-EXCEPT variant + the VALUE8 lane weld (VK-affecting, gated) |
| `v3OfFrozenSetField` | `…RotationV3.lean:3143` | same |
| `setFieldV3` | `…RotationV3.lean:3164` | same |

**C2 — `Genuine`/`GenuineNonAmp`/`GenuineNoRecompute` cap-family variants** (deployed ships the plainer
`v3Of …` / `attenuateV3` face):
`attenuateVmDescriptorGenuine` (`…AttenuateA.lean:578`), `…GenuineNoRecompute` (`:600`), `…GenuineNonAmp`
(`:820`), `delegateVmDescriptorGenuine` (`…Delegate.lean:190`), `…GenuineNonAmp` (`:240`),
`delegateAttenVmDescriptorGenuine` (`…DelegateAtten.lean:172`), `…GenuineNonAmp` (`:225`),
`introduceVmDescriptorGenuine` (`…Introduce.lean:434`), `…GenuineNonAmp` (`:487`),
`refreshVmDescriptorGenuine` (`…RefreshDelegation.lean:562`), `…GenuineNonAmp` (`:617`),
`revokeVmDescriptorGenuine` (`…RevokeDelegation.lean:438`), `…GenuineNonAmp` (`:494`).
NOTE: for the cap crown the *deployed* non-amp authority rides `capReshapeVmDescriptor`/`attenuateV3` +
the cap-open after-spine path; these `Genuine*` faces are the earlier per-effect non-amp proofs, now
superseded-or-parallel. Verify none of their unique properties is un-carried before deleting.

**C3 — other richer V3 variants defined but not wired:**
`setFieldDynV3` (`…RotationV3.lean:2040`; ships `setFieldDynForcedV3`), `delegateV3` (`:1864`; delegate
folded into attenuate), `refusalPayloadV3` (`:4143`; ships `refusalFieldsWriteV3`), `refusalV3` (`:4462`),
`rotateV3WithPayloadColumn` (`:4084`), `setProgramV3` (`:4616`).

**C4 — carrier-enrichment ("teeth"/keyed/deployed/membership/accumulator) V3 variants defined, not wired:**
`makeSovereignV3Keyed` (`Emit/CarrierComposed.lean:85`), `makeSovereignV3Deployed` (`:221`),
`withMembershipTeethPins` (`:387`), `transferV3Membership` (`:454`), `withOctetTeeth`
(`Emit/CarrierOctetGates.lean:173`), `withOctetTeethBoth` (`:236`), `withFactoryChildVkTeeth` (`:273`),
`withHatcheryContractTeeth` (`:291`), `withMembershipPubkeyCompress` (`:580`), `effFieldsReadOpenV3`
(`:707`), **`effAccumWriteV3`** (`Emit/AccumulatorOpenEmit.lean:129` — the 8-felt accumulator carrier;
see §3 DANGEROUS), `withMembershipAuthRoot` (`Emit/MembershipAuthRootEdge.lean:87`).
These are the carrier-deployment "third edge" builders (cf. memory: carrier-deployment architecture).
Most are proven-and-committed but not yet wired into a deployed registry member — the STEP-N carrier
welds mid-flight.

### D. Faces never wired to ANY deployed registry

**D1 — whole effects, standalone/proven/unshipped:** `delegateVmDescriptor`
(`…Delegate.lean:92`), `delegateAttenVmDescriptor` (`…DelegateAtten.lean:84`), `crossSideDescriptor`
(`…CrossSide.lean:199`), `capReshapeVmDescriptor` (`…CapReshape.lean:525`), `heapWriteVmDescriptor`
(`…HeapRoot.lean:127`), `recordVmDescriptor` (`…RecordRoot.lean:243`), `bilateralAggDescriptor`
(`…BilateralAgg.lean:243`), `bundleFoldDescriptor` (`…BundleFold.lean:125`).
NOTE: several of these (`capReshapeVmDescriptor`, `heapWriteVmDescriptor`, `bilateralAggDescriptor`,
`bundleFoldDescriptor`) have standalone committed descriptor JSONs (`dregg-effectvm-capreshape-v1.json`,
`dregg-bilateral-aggregation-v2.json`, `dregg-bundle-tree-fold-v2.json`) that are **not** members of any
live TSV registry — they are aggregation/crown descriptors verified on their own recursion-gated path,
not through the effect-vm registry. Confirm each has its own deployed verify path before treating as dead.

**D2 — pre-V3 standalone `*Descriptor` faces of effects shipped via a `*V3` wrapper** (superseded):
`createCellVmDescriptor` (`…CreateCell.lean:110` → `createCellV3`), `factoryVmDescriptor`
(`…CreateCellFromFactory.lean:91` → `factoryV3`), `makeSovereignVmDescriptor` (`…MakeSovereign.lean:92`
→ `makeSovereignV3`), `spawnVmDescriptor` (`…Spawn.lean:137` → `spawnV3`), `receiptArchiveVmDescriptor`
(`…ReceiptArchive.lean:148` → `receiptArchiveV3`), `noteCreateVmDescriptorFull` (`…NoteCreate.lean:624`
→ `noteCreateV3`), `noteSpendVmDescriptorFull` (`…NoteSpend.lean:633` → `noteSpendV3`).
NOTE: the `*V3` wrappers wrap `…TickFace`/runtime faces, so these Full faces are the raw inner faces
the wrapper supersedes — not independently deployed. Benign.

### E. Scaffold / test / proof-only (benign)

Probes: `rotationProbeVmDescriptor{,2}` (`…Rotation.lean:292/305`), `rotationCaveatProbeVmDescriptor{,2}`
(`…RotationCaveat.lean:352/365`), `rotationProbeVmDescriptorR{,2}` (`…RotationR.lean:439/450`).
Demos/fixtures: `demoV2`/`demoU`/`demoC` (`DescriptorIR2.lean:1507/1619/1758`), `embedV1`
(`DescriptorIR2.lean:414`), `emptyDescriptor2`/`oneRangeDescriptor2` (`DecideSatisfied2.lean:240/275`),
`descOf` (`DecideSatisfied2Golden.lean:103`), `transferDescr` (`CircuitSoundnessAssembled.lean:132`),
`crossCellConservationDescriptor` (`CrossCellConservation.lean:201`), `dropLegacyCommitPins1`
(`…RotationWide.lean:1084`, proof-side transformer used only in `v3RegistryWide_sound`).
Refinement-proof scaffolds (the descriptor the refinement theorem is *stated about*, aliasing a deployed
member): `transferV3` (`RotatedKernelRefinement.lean:72`), `incNonceV3`
(`RotatedKernelRefinementIncNonce.lean:70`), `burnV3` (`RotatedKernelRefinementMintBurn.lean:68`),
`setFieldV3` (`RotatedKernelRefinementSetField.lean:66`, 2nd site — **not** benign, see §3).

### F. Out-of-scope (Argus subtree, flagged for completeness)

`compileEFold` (`Circuit/Argus/CompileE.lean:173`), `seqDescr` (`Circuit/Argus/CompileFold.lean:115`),
`compileFold` (`:228`), `compileRevoke` (`Circuit/Argus/Effects/RevokeDelegation.lean:195`).

---

## 3. Q2 — KEYSTONE ORPHANS (the dangerous ones)

A keystone orphan is a theorem / `#assert_axioms` block proving a property of an orphaned descriptor.
For each, the question: does the **deployed** descriptor have the same property proven (safe/redundant),
or **lack** it (DANGEROUS — false confidence)?

### 3a. The setField refinement stack — about `setFieldV3 = v3OfFrozenSetField` (NOT deployed)

The deployed member is built from `v3OfFrozen` (freeze-ALL, `EffectVmEmitRotationV3.lean:3058`); the
keystones are stated at `Satisfied2 (setFieldV3 slot)` = `v3OfFrozenSetField` (freeze-EXCEPT-slot,
`:3143/3164`). `v3OfFrozenSetField` appears in **no** registry.

| keystone | file:line | `#assert_axioms` | verdict |
|---|---|---|---|
| `setField_value_forced` | `RotatedKernelRefinementSetField.lean:204` | `:306` | DANGEROUS (grounding) |
| `setField_descriptorRefines` | `:238` | `:307` | DANGEROUS (grounding) |
| `setField_descriptorRefines_fullActionStep` | `:254` | `:308` | DANGEROUS (grounding) |
| `descriptorRefines_rejects_wrong_value` | `:274` | `:309` | DANGEROUS (grounding) |
| `descriptorRefines_rejects_moved_bystander` | `:287` | `:310` | DANGEROUS (grounding) |
| `rotated_row_cellSpec` | `:122` | `:304` | DANGEROUS (grounding) |
| `rotated_row_gates` | `:91` | `:303` | DANGEROUS (grounding) |
| `setField_descriptorComplete` | `CircuitCompletenessValue.lean:446` | — | DANGEROUS (completeness) |

Consumers inheriting the orphan: `ClosureAll.lean:625`, `ClosureFanoutGenuine.lean:212` both bundle
`Satisfied2 (RotatedKernelRefinementSetField.setFieldV3 slot)`.

**Why DANGEROUS but NOT a soundness forge** (reconciling with `TRUST-BASE-CENSUS.md §6 R1`): the
deployed `v3OfFrozen` over-freezes the written slot's 7 completion lanes (`fieldsCompletionFreezes`,
`…RotationV3.lean:2903`, applied `:2958`) — *stronger* than the freeze-EXCEPT variant, so no forge. Two
real problems remain:
1. **Grounding gap.** The circuit→kernel refinement for the deployed setField rung (`Rfix 5` = registry
   position 28 = `setFieldVmDescriptor2-0R24`, `CircuitSoundnessAssembled.lean:316`) is discharged
   through the **assumed** `∀ e, EffectDecodeBridge S hash Rfix e` residual family
   (`CircuitSoundnessAssembled.lean:68`, named `:613-622`), NOT from these circuit-grounded teeth. The
   teeth ground `v3OfFrozenSetField`; the deployed descriptor's refinement is an assumption. The green
   keystones read as if setField refinement is circuit-grounded — it is not, for the deployed variant.
2. **Completeness gap.** `setField_descriptorComplete` proves an honest witness exists for the
   freeze-EXCEPT variant. The deployed freeze-ALL variant **rejects** an honest large-value write (high
   bytes moved off the frozen pre-state). Completeness does NOT transfer. Named residual = the VALUE8
   weld (VK-affecting, gated).

**NOT dangerous (redundant/safe):** `setFieldV3_pins_value` (`…RotationV3.lean:3200`),
`setFieldV3_pins_nonce_tick` (`:3169`) and their reject-teeth (`:3219`/`:3189`) are stated about
`rotateV3 (setFieldTickFace slot)` — the shared per-row core present in BOTH variants — so lane-0 value
pinning genuinely holds for the deployed descriptor. That narrow property is safe.

### 3b. The dedicated-accumulator 8-felt keystones — about `effAccumWriteV3` (NOT deployed)

The DEPLOYED `noteSpendV3` / `noteCreateV3` / `createCellV3` carry the nullifier / commitment / accounts
root update as INLINE `MapOp`s whose `holdsAt` denotes **lane 0 only** — a `scalarRootGroup`
(`…RotationV3.lean:1570-1571`: "denotation is lane 0; no after-spine keystone forces lanes 1..7 — the
root stays ~31-bit"). The 8-felt binding is proven only about the **assurance-twin** descriptor
`effAccumWriteV3` (`Emit/AccumulatorOpenEmit.lean:129`, an orphan — §2 C4), via keystones like
`nullifierWrite_forces_write8_sat` (`RotatedKernelRefinementCapFamily.lean:1645+`) which the code itself
labels "⚑ ASSURANCE-LAYER (not the deployed apex descriptor)" (`:1637`).

**Verdict: DANGEROUS at the light-client level, safe on a full node.** A re-executing validator is
protected by the Rust `CanonicalHeapTree8` producer + the `node8` map-op AIR (forge-rejection PROVEN by
`vk_epoch_notes`/`vk_epoch_birth`). But the **deployed apex descriptor the light client verifies against**
denotes only lane 0 for these three roots → their in-circuit binding is the ~31-bit fold, not the
claimed faithful ~124-bit. This is precisely the `docs/FAITHFUL-STATE-COMMITMENT.md` scar surface. The
green 8-felt keystones stand beside a lane-0 deployed denotation — the "misled us" pattern. Named
residual: "flipping the apex to quantify over `effAccumWriteV3` is a SEPARATE VK epoch" (`:1642`).

> **⚑ AUDIT RESOLUTION 2026-07-03 — REFUTED (STAGED-VS-DEPLOYED CONFLATION). This verdict above was
> WRONG.** An adversarial forge (`circuit/tests/accumulator_completion_lane_forge.rs`, both tests GREEN)
> attacked the accumulator root's completion lanes 1..7 directly against **the descriptor the light
> client actually runs** and found them BOUND at 8-felt (~124-bit), not lane-0. The error was reading
> the Lean `scalarRootGroup` *after-spine* denotation (`EffectVmEmitRotationV3.lean:1570`) as if it were
> the whole binding — it is not. What the deployed descriptor JSON carries, and what the deployed Rust
> verifier resolves, both independently bind the full 8-felt root:
>
> 1. **The deployed verifier resolves the WIDE / WELDED registry, NOT the 1-felt V3.** For a single-cohort
>    noteSpend/noteCreate lead, `turn/src/executor/proof_verify.rs:684/704/1219` resolves
>    `WIDE_REGISTRY_STAGED_TSV` and then sets `require_welded = true` (`:1219`), DROPPING the bare form so
>    the SOLE accepted descriptor is the welded twin
>    `noteSpend-v1-rot24-v3-insert-heapopen-umem-wide-welded` (2829-wide, 8-felt anchors + umem_op). The
>    umem VK epoch was FIRED (`da0c47dd6` "umem IS the deployed prover"; `443661298` "umem-welded WIDE as
>    deployed default") — so §1's "the live one is `rotation-v3-staged-registry.tsv` (1-felt)" is STALE
>    for the effect-vm verify path. The SDK light-client producer/verifier route NoteCreate through
>    `generate_rotated_note_create_wide` (the insert-shaped `effAccumInsertV3` member), confirmed by
>    `vk_epoch_notes_light_client_binding::notecreate_forced_on_wire_through_live_wide_producer`.
> 2. **Every deployed member's inline map-op binds an 8-felt `new_root` group — including the narrow V3
>    member the sweep cited.** In `rotation-v3-staged-registry.tsv`, `rotation-wide-registry-staged.tsv`
>    AND `…-umem-welded-…tsv`, the noteCreate `.insert` map-op's `new_root` is an 8-element column group
>    (narrow cols `[441,482..488]`; wide/welded `[442,489..495]`), enforced through the arity-16 `node8`
>    compression on BUS_P2. The producer fills those lanes with the genuine `CanonicalHeapTree8::root8()`
>    high felts (`trace_rotated.rs:1409-1424`).
> 3. **The forge is UNSAT on BOTH geometries.** `wide_notecreate_completion_lane_forge_verdict` (the LC
>    geometry) and `narrow_v3_notecreate_completion_lane_forge_verdict` (the sweep's own cited registry)
>    each forge `new_root` lanes 1..7 to arbitrary values ≠ the genuine insert, keep lane 0 honest, make
>    the trace fully self-consistent, and REFUSE through `prove`/`verify` ALONE. The grow-gate binds all
>    eight felts. (The setField exemplar that seeded the "class" is a genuine completion-lane seam because
>    its written-slot lanes are freeze-bound, not map-op-bound — that dangerous #2 stands; the accumulator
>    roots are structurally different: a map-op, not a freeze.)
>
> Net: the accumulator roots are **LC-faithful at ~124-bit** on the deployed path. The `effAccumWriteV3`
> orphan (§2 C4) is a redundant assurance twin of an already-8-felt-deployed binding, not the sole carrier
> of a property the deployed path lacks. Item #1 in §5 and §6 is retired.
>
> **Honest coverage caveat:** the N=3 empirical run exercised a **Transfer** turn, whose wide descriptor
> carries **no map-op** (`transferVmDescriptor2R24` constraint kinds = gate/transition/pi_binding/lookup
> only). So the "live on iron under the faithful VK" evidence does NOT yet cover a noteSpend/noteCreate/
> createCell turn end-to-end on the testnet — the 8-felt accumulator binding is proven by the in-circuit
> forge here, not yet by an on-chain accumulator turn.

*(By contrast, the cap-write / heap / fields accumulator roots DO deploy the after-spine 8-felt model —
the `*WriteCapOpen` family is present in `rotation-v3-staged-registry.tsv`, and
`effect_vm_descriptors.rs:2045` routes `has_after_spine`. Those are OPTION-I deployed and are the safe
counterexample that makes the three note/create roots stand out.)*

---

## 4. Q3 — BUILT-BUT-UNDEPLOYED SEAMS (cross-ref census + memory)

| seam | built (file:line) | deployed path? | what deploying takes |
|---|---|---|---|
| **value8 setField weld** | `v3OfFrozenSetField`/`setFieldV3` `…RotationV3.lean:3143/3164`; freeze-EXCEPT `fieldsCompletionFreezesExcept` `:2913` | **NO** — registry `:5364` ships `v3OfFrozen` (freeze-ALL); large-value writes rejected | swap registry wrap to freeze-EXCEPT + force the 7 completion lanes to declared `value8` params; VK-affecting, gated |
| **dedicated accumulator 8-felt (notes/create)** | `effAccumWriteV3` `AccumulatorOpenEmit.lean:129`; `nullifierWrite_forces_write8_sat` `…CapFamily.lean:1645` | **NO at LC** — apex denotes lane-0 (`scalarRootGroup` `:1570`); full-node safe via Rust node8 AIR | flip the apex to quantify over `effAccumWriteV3` for the 3 roots; SEPARATE VK epoch (producers already fill 8 lanes) |
| **DECO carrier** | `Crypto/Deco.lean` (`deco_bridge`/`deco_verify_sound`/`deco_binds_payment`/`deco_registry_cascade`, all proven) | **NO** — consumed only by `ClosureSurface.lean`/`ClosureTransfer.lean` (proof files); no carrier ARM emits a deco descriptor into any registry | add a `custom(vk)`-routed deco carrier member (the cascade proves it composes through `custom`); needs a deployed descriptor arm + producer |
| **G5 discharge / vault (tags 18/19)** | Lean emitter `EmitDischargeVaultSat.lean` (uncommitted-to-TSV); Rust `discharge_weld.rs`/`vault_weld.rs`/`satisfaction_weld.rs` | **NO** — `dischargeSat`/`vaultSat` in **no** TSV; welds referenced only by a doc comment (`helpers.rs:69-70`), called by no producer. `satisfaction_weld.rs:24`: "not on any live path". `settleEscrowSatVmDescriptor2R24` (the sibling) IS a TSV member but flagged "VK-EPOCH §6 BLOCKER 1 — staged welded" (`effect_vm_descriptors.rs:2524`) | emit the discharge/vault rows into the registry TSV + wire the weld into the settle-escrow producer; staged behind the VK epoch |
| **umem flip** | `weldedWideRegistry` `…UMemWeldWide.lean:261`; `rotation-wide-umem-welded-registry-staged.tsv` | **STAGED, not default** — the live prover uses the 1-felt `rotation-v3-staged-registry.tsv`; "the flag-day flips a registry pointer" (`effect_vm_descriptors.rs:572`) | the gated VK epoch: commit the wide-welded VK + flip the deployed default (per memory: umem-as-primitive epoch, deliberately gated) |

---

## 5. THE DANGEROUS SET (keystones proving a property the deployed LC path LACKS)

Ranked by how much they mislead a reader of the "axiom-clean" green.

1. ~~**Dedicated accumulator roots — 8-felt keystones vs lane-0 deployment.**~~ **⚑ REFUTED 2026-07-03
   (see §3b AUDIT RESOLUTION).** The forge (`circuit/tests/accumulator_completion_lane_forge.rs`) shows
   the deployed descriptor (WIDE/welded that the LC verifier resolves, AND even the narrow V3 member)
   binds ALL EIGHT `new_root` lanes through the inline `.insert` map-op / `node8` AIR — a completion-lane
   forge is UNSAT. The "lane-0 `scalarRootGroup`" reading (`…RotationV3.lean:1570`) was the after-spine
   denotation only, NOT the map-op binding; this was the R1 staged-vs-deployed trap. The accumulator
   roots are **LC-faithful at ~124-bit**. `effAccumWriteV3` is a redundant assurance twin, not the sole
   carrier. (Dangerous #2, setField, is a real freeze-bound completion seam and STANDS.)

2. **setField refinement stack — circuit-grounding + completeness about `v3OfFrozenSetField`.** 8
   `#assert_axioms` keystones (`RotatedKernelRefinementSetField.lean`) + `setField_descriptorComplete`
   describe the freeze-EXCEPT variant. The deployed freeze-ALL setField (a) rides the **assumed**
   `EffectDecodeBridge` for its refinement, not these teeth, and (b) rejects honest large-value writes
   (completeness fails). **Soundness-safe** (freeze binds harder), but the green reads as if the deployed
   setField's refinement is circuit-grounded and complete — it is neither. Already partly corrected by R1.

Everything else in §2 is a benign orphan (superseded predecessor, scaffold, or a proven-but-parallel
variant whose deployed sibling carries an equal-or-stronger property). No new soundness forge found.

---

## 6. THE UNFINISHED-DEPLOYMENT SET (built + proven + never wired, ranked by value)

1. ~~**Dedicated accumulator 8-felt apex flip**~~ **⚑ ALREADY DEPLOYED / REFUTED 2026-07-03.** The
   deployed WIDE/welded (and even narrow V3) note/create/create-cell members already bind the root 8-felt
   via the inline `.insert` map-op — proven UNSAT-to-forge by `accumulator_completion_lane_forge.rs`. The
   separate `effAccumWriteV3` apex flip is NOT needed for LC faithfulness (it is a redundant twin). No
   floor here. (Remaining honest gap: an on-chain accumulator turn in the N=3 run — see §3b caveat.)
2. **VALUE8 setField weld** (`v3OfFrozenSetField` + lane-force). Buys faithful large-value field writes
   (today capped at lane-0 ≤~31-bit values). Completeness, not soundness. VK-affecting.
3. **G5 discharge / vault (tags 18/19)**. Fully-built Lean+Rust machinery (`EmitDischargeVaultSat.lean`,
   `discharge_weld.rs`, `vault_weld.rs`) reaching no live path. Deploying = emit the rows + wire the
   settle-escrow producer. (`settleEscrowSatVmDescriptor2R24` is the staged host.)
4. **Carrier "third-edge" teeth** (§2 C4: `withOctetTeeth`, `withFactoryChildVkTeeth`,
   `withHatcheryContractTeeth`, `withMembershipAuthRoot`, `makeSovereignV3Deployed`, …). Mid-flight
   carrier-deployment welds (cf. memory carrier-deployment architecture); each needs its registry member
   wired so the teeth==committed-authority third edge is live, not vacuous.
5. **DECO carrier**. Proven zkTLS payment-attestation predicate with no deployed `custom(vk)` arm.
   Lower urgency (a feature, not a floor).

---

## 7. THE GUARD (recommendation + scaffold)

**Recommendation.** Add the **dual of R3's coverage gate**. R3
(`producer_descriptor_coverage_gate.rs`) asserts *every deployed member has a test*. This sweep needs:
**every keystone-carrying descriptor is registry-reachable** — a proof about a descriptor no registry
lists must fail the build unless explicitly allowlisted with a reason. That flips the setField/accumulator
class from "discovered by a manual audit" to "caught at CI the moment a keystone is written about an
undeployed descriptor."

**Design (mirrors the existing static-ledger idiom).** A static ledger of
`(keystone_theorem, descriptor_def, DeployStatus)` where `DeployStatus` is `Deployed` or
`OrphanAllowlisted { reason }`. The test asserts no entry is a bare orphan. New keystones about
undeployed descriptors force a conscious allowlist decision (with a named reason + closure lane), exactly
the "name every residual" discipline. `EffectVmDescriptor2` derives no `BEq` on its constraint list
(`DescriptorIR2.lean:400`), so the machine-checkable membership check keys on the descriptor `.name` /
registry member key rather than structural equality; the ledger is the source of truth and is reviewed
against `v3RegistryBare`'s member list on change.

**Scaffold delivered:** `circuit/tests/keystone_descriptor_deployment_gate.rs` — the ledger for the two
DANGEROUS families found here (setField refinement stack, dedicated accumulator 8-felt) + the benign
`*_pins_value` redundant-safe entries, each with its DeployStatus and reason. It passes today (all
orphans are allowlisted with their §5/§6 reason) and fails if a new keystone descriptor is added without
an allowlist entry. It is the anti-regression tooth for this audit.

---

## 8. Reconciliation with prior audits

- `TRUST-BASE-CENSUS.md §6 R1` found the setField orphan and correctly refuted the "live soundness gap"
  framing (deployed freeze binds). This sweep confirms that and adds the **grounding gap** (deployed
  refinement rides the assumed bridge) + the generalization to the **whole class**.
- `PRODUCER-DESCRIPTOR-COVERAGE.md` (R3) is the forward dual: deployed→tested. This doc is proven→deployed.
  Together they close the two-way coverage question.
- The accumulator find is the same object as the `docs/FAITHFUL-STATE-COMMITMENT.md` ~31-bit-vs-124-bit
  discipline, viewed through the orphan lens: the faithful keystone exists but the deployed apex doesn't
  quantify over it for three roots.
