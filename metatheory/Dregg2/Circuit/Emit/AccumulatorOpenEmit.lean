/-
# Dregg2.Circuit.Emit.AccumulatorOpenEmit — the LIVE accumulator-membership open, the FOURTH/FIFTH/SIXTH
faithful-root after-spine (nullifier · commitments · cells — the three DEDICATED accumulator roots).

The exact twin of `HeapOpenEmit.lean` / `FieldsOpenEmit.lean` §11/§12 for the three accumulator roots
(`nullifier_root` @ limb 26, `commitments_root` @ limb 27, `cells_root` @ limb 0). Each accumulator update
is a SET-INSERT of a `(key, value)` leaf into a sorted-Poseidon2 tree; the keystone `accumOpen_writesTo8`
reduces the faithful 8-felt accumulator-write to TWO membership witnesses sharing a path (before = old leaf
against the BEFORE accumulator-root group; after = in-place-updated leaf, SAME key, new value, against the
AFTER accumulator-root group), FORCING `EffectVmEmitRotationV3.heapWritesTo8` over the FULL ~124-bit root —
NEVER the lane-0 squeeze the accumulator geometry (limb 26/27/0 + the 21 dedicated completion limbs 67..87)
is grown over.

REUSE (the whole point — NO spine re-proof, like fields did): the three accumulator families ride the SAME
`node8` / `CanonicalHeapTree8` lane as the heap root, i.e. the SAME `DeployedHeapTree.Heap8Scheme`
(`heapNodeOf8`, `heapLeafDigest8`, `recomposeUp8`). So the entire §0-§3 machinery of `HeapOpenEmit`
(`HeapMembershipCore`, `heapLeafLookup`, `heapPermOut`, the leaf/node digest soundness, the fold, the
STEP-A keystone `heapOpen_writesTo8`, AND the generic before-membership read appendix `effHeapOpenV3` with
its `effHeapOpenV3_core` / `effHeapOpenV3_satisfied2_strips_to_base`) is re-used VERBATIM — it is already
fully parametric in `CapOpenCols` + `Heap8Scheme`. The SOLE new material here is the §4 AFTER-spine
appendix, PARAMETRIC over the accumulator spec `(groupCol, keyCol, valueCol)` and instantiated three times
(nullifier / commitments / cells) at the consumer trio.

## ⚑ THE INLINE-MAP-OP SUBTLETY (honest scope statement)
The DEPLOYED accumulator writes are INLINE `MapOp`s (`nullifierInsertOp`, `commitmentsInsertOp`,
`cellsInsertOp`) appended to `noteSpendV3` / `noteCreateV3` / `createCellV3` — and `MapOp.holdsAt` /
`MapOp.rowAt` / `mapLog` denote LANE 0 only (see `DescriptorIR2.lean:511`). The full 8-felt faithfulness of
the deployed map-op is carried in Rust by the genuine `CanonicalHeapTree8` producer + the map-op `node8` AIR
binding all 8 lanes (deployed-faithful, forge-rejection PROVEN by `vk_epoch_notes` / `vk_epoch_birth`). The
after-spine `effAccumWriteV3` built here is the LEAN ASSURANCE-LAYER twin of that binding: its `Satisfied2`
TRACE-FORCES the faithful 8-felt write over the committed accumulator group-cols, EXACTLY as heap/fields.
Unlike heap/fields (whose deployed apex descriptor IS the after-spine, OPTION I), the accumulator apex
quantifies over the inline-map-op descriptors, so the after-spine trio stands as the ASSURANCE twin
alongside the deployed node8-AIR faithfulness — flipping the deployed default to the after-spine is a
SEPARATE VK epoch (the accumulator producers already fill the 8 lanes; the flip is the descriptor swap).
This is NOT laundering: deployed-faithful is independently real, and this is the same 8-felt keystone
cap/heap/fields carry.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named WIDE
chip-soundness `ChipTableSoundN (heapPermOut S8)`, inherited from `HeapOpenEmit`/`DeployedHeapTree`.
-/
import Dregg2.Circuit.Emit.HeapOpenEmit

namespace Dregg2.Circuit.Emit.AccumulatorOpenEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (TraceFamily VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapOpen
  (CapOpenCols DEPTH nodeLookup dirBoolGate dirBoolVal rootPinGate groupVal)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.CapMerkleGeneric (StepG)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols nodeLookups dirBoolGates rootPinGates eqGate eqGate_eval
   diffGate_exact
   CAP_OPEN_SPAN AFTER_SPINE_SPAN AFTER_SPINE_BASE)
open Dregg2.Circuit.Emit.HeapOpenEmit
  (heapLeafLookup heapLeafPairOf heapLeafTripleOf heapPermOut HeapMembershipCore heapOpen_writesTo8
   heapOpenConstraints effHeapOpenV3 effHeapOpenV3_core effHeapOpenV3_satisfied2_strips_to_base
   effHeapOpenV3_mapLog effHeapOpenV3_memLog)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN)

set_option autoImplicit false

/-! ## §4 — the AFTER-spine appendix, PARAMETRIC over the accumulator spec `(groupCol, keyCol, valueCol)`.

The before-membership read appendix is REUSED verbatim from `HeapOpenEmit` (`effHeapOpenV3` /
`effHeapOpenV3_core`): the generic ARITY-3 IMT `(key, value, nextAddr)` node8 membership. ⚠ This line
said "arity-2" — false since the 2026-07-12 IMT move (`919b2b0b8d`). The appendix it names absorbs THREE
leaf columns (`HeapOpenEmit.heapLeafInputs`, `#guard`-pinned at length 3, matching
`heap_root.rs::HeapLeaf::digest8`), and the accumulator trees are literally built out of the same
`heap_root::HeapLeaf` (see `trace_rotated.rs::lay_accum_insert_read_appendix`), so the pointer column is
absorbed here too. The after-spine below welds the
read's `capRoot` group to the committed BEFORE accumulator group (`groupCol EFFECT_VM_WIDTH`), the after
`capRoot` group to the AFTER accumulator group (`groupCol (EFFECT_VM_WIDTH + B_SPAN)`), pins the key to the
accumulator's published KEY column and the after-leaf value to the accumulator's VALUE column. -/

/-- The after-spine accumulator column layout. `sib`/`dir` SHARED with the read; `capRoot` IS the committed
AFTER accumulator-root block (`groupCol (EFFECT_VM_WIDTH + B_SPAN)`), the accumulator twin of `afterSpineColsH`
with the group col left abstract. -/
def afterSpineColsA (groupCol : Nat → Fin 8 → Nat) (w : Nat) : CapOpenCols :=
  { leaf       := fun i => AFTER_SPINE_BASE w + i.val
  , leafDigest := fun i => AFTER_SPINE_BASE w + 7 + i.val
  , sib        := (capOpenCols w).sib
  , dir        := (capOpenCols w).dir
  , node       := fun lvl i => AFTER_SPINE_BASE w + 15 + 8 * lvl + i.val
  , capRoot    := fun i => groupCol (EFFECT_VM_WIDTH + B_SPAN) i
  , src        := AFTER_SPINE_BASE w + 15 + 8 * DEPTH
  , effBit     := AFTER_SPINE_BASE w + 16 + 8 * DEPTH
  , bit        := fun i => AFTER_SPINE_BASE w + 17 + 8 * DEPTH + i }

theorem afterSpineColsA_dir (groupCol : Nat → Fin 8 → Nat) (w : Nat) :
    (afterSpineColsA groupCol w).dir = (capOpenCols w).dir := rfl

/-- The after `capRoot` group IS the committed AFTER accumulator-root block (as a `Digest8` read). -/
theorem afterSpineA_capRoot_after (groupCol : Nat → Fin 8 → Nat) (w : Nat) (env : VmRowEnv) :
    groupVal env (afterSpineColsA groupCol w).capRoot
      = (fun i => env.loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) i)) := rfl

/-- The 3 narrowed-leaf weld gates: after leaf 0 (key) = the read's key; after leaf 1 (value) = the
accumulator's published VALUE column (`valueCol`); after leaf 2 (IMT `nextAddr`) = the read's pointer
(the value update HOLDS the sorted-chain pointer fixed). -/
def afterLeafWeldsA (valueCol : Nat) (w : Nat) : List VmConstraint2 :=
  [ .base (.gate (eqGate ((afterSpineColsA (fun _ _ => 0) w).leaf 0) ((capOpenCols w).leaf 0)))
  , .base (.gate (eqGate ((afterSpineColsA (fun _ _ => 0) w).leaf 1) valueCol))
  , .base (.gate (eqGate ((afterSpineColsA (fun _ _ => 0) w).leaf 2) ((capOpenCols w).leaf 2))) ]

/-- The 8 BEFORE accumulator-root weld gates: the read's appendix `capRoot` group equals the committed
BEFORE accumulator block (`groupCol EFFECT_VM_WIDTH`). -/
def beforeRootWeldsA (groupCol : Nat → Fin 8 → Nat) (w : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot i) (groupCol EFFECT_VM_WIDTH i))))

/-- The key-bind gate: the read leaf's `key` (leaf 0) equals the accumulator's published KEY column
(`keyCol` — e.g. `NULLIFIER_PARAM_COL`) — so the forced 8-felt write is keyed at the SAME key the deployed
inline `MapOp` uses (a runtime column, like heap's `HEAP_ADDR`, not fields' compile-time const). -/
def keyBindGateA (keyCol : Nat) (w : Nat) : EmittedExpr :=
  eqGate ((capOpenCols w).leaf 0) keyCol

/-- The after-spine constraint list (appended past the reused heap-open read appendix): the after-leaf
absorb, the 16 after-node absorbs, the 8 after root-pins, the 2 narrowed-leaf welds, the 8 before-root
welds, and the key bind. Structurally identical to `afterSpineConstraintsH`/`afterSpineConstraintsF`. -/
def afterSpineConstraintsA (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat) (w : Nat) :
    List VmConstraint2 :=
  .lookup (heapLeafLookup (afterSpineColsA groupCol w))
  :: ((List.range DEPTH).map (fun lvl => VmConstraint2.lookup (nodeLookup (afterSpineColsA groupCol w) lvl)))
  ++ ((List.finRange 8).map (fun i => VmConstraint2.base (.gate (rootPinGate (afterSpineColsA groupCol w) i))))
  ++ afterLeafWeldsA valueCol w
  ++ beforeRootWeldsA groupCol w
  ++ [VmConstraint2.base (.gate (keyBindGateA keyCol w))]

/-- **`effAccumWriteV3 groupCol keyCol valueCol base name`** — the reused heap-open read descriptor
(`effHeapOpenV3`) WIDENED by the accumulator after-spine appendix: the assurance-layer accumulator-write
descriptor. Its `Satisfied2` FORCES the faithful 8-felt accumulator-write (`effAccumWriteV3_forces_write8`). -/
def effAccumWriteV3 (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { (effHeapOpenV3 base name) with
    name        := name
    traceWidth  := (effHeapOpenV3 base name).traceWidth + AFTER_SPINE_SPAN
    constraints := (effHeapOpenV3 base name).constraints
                     ++ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth }

/-- Every after-spine constraint is a constraint of the write descriptor. -/
theorem effAccumWriteV3_afterMem (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth) :
    c ∈ (effAccumWriteV3 groupCol keyCol valueCol base name).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the write descriptor strips (constraint-subset) to a `Satisfied2` of the reused
heap-open read descriptor `effHeapOpenV3` — the after-spine appendix is all `.lookup`/`.base (.gate …)`,
reads no base column and contributes no map/mem op. -/
theorem effAccumWriteV3_strips_to_accumOpen (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t) :
    Satisfied2 hash (effHeapOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effAccumWriteV3 groupCol keyCol valueCol base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effAccumWriteV3, afterSpineConstraintsA,
      afterLeafWeldsA, beforeRootWeldsA, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effAccumWriteV3 groupCol keyCol valueCol base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effAccumWriteV3, afterSpineConstraintsA,
      afterLeafWeldsA, beforeRootWeldsA, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effAccumWriteV3 groupCol keyCol valueCol base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effAccumWriteV3 groupCol keyCol valueCol base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effHeapOpenV3 base name).constraints
                     ++ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- **`effAccumWriteV3_satisfied2_strips_to_base`** — THE FULL ASSURANCE BRIDGE: a `Satisfied2` of the
after-spine accumulator-write restricts to a `Satisfied2` of the bare `base` (both appendices are ADDITIVE —
all lookups + base gates, no map/mem op). Composes the after-spine strip with the reused read-appendix
strip (`effHeapOpenV3_satisfied2_strips_to_base`). -/
theorem effAccumWriteV3_satisfied2_strips_to_base (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  effHeapOpenV3_satisfied2_strips_to_base hash base name minit mfin maddrs t
    (effAccumWriteV3_strips_to_accumOpen groupCol keyCol valueCol hash base name minit mfin maddrs t h)

/-- **`effAccumWriteV3_afterCore`** — the AFTER-spine `HeapMembershipCore`, derived from `Satisfied2` of the
write descriptor. The `dirBool` is reused from the read (the SHARED dir column). Field-faithful: the
root-pin gates arrive `≡ 0 [ZMOD p]` and collapse to ℤ through cell canonicality (`(−p, p)` residual). -/
theorem effAccumWriteV3_afterCore (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hdir : ∀ lvl < DEPTH,
      (dirBoolGate (capOpenCols base.traceWidth) lvl).eval (envAt t i).loc = 0) :
    HeapMembershipCore t.tf (afterSpineColsA groupCol base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effAccumWriteV3_afterMem groupCol keyCol valueCol base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · have hin : VmConstraint2.lookup (heapLeafLookup (afterSpineColsA groupCol base.traceWidth))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := List.mem_cons_self
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (afterSpineColsA groupCol base.traceWidth) lvl)
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ?_)))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have := hdir lvl hlvl
    exact this
  · intro k
    have hin : VmConstraint2.base (.gate (rootPinGate (afterSpineColsA groupCol base.traceWidth) k))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_)))
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (rootPinGate (afterSpineColsA groupCol base.traceWidth) k).eval
        (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
    unfold rootPinGate at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact diffGate_exact (hcells _) (hcells _) h'

/-- Any after-spine `.base (.gate g)` constraint forces `g.eval ≡ 0 [ZMOD p]` on an active (non-last)
row — the field-faithful consequence (`holdsVm` binds under `when_transition`, reduced by `hlastf`). -/
theorem afterSpineA_gate_forces (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr)
    (hin : VmConstraint2.base (.gate g)
             ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effAccumWriteV3_afterMem groupCol keyCol valueCol base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (hmem _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- An after-spine COLUMN weld (`eqGate a b`) forces the ℤ equality `loc a = loc b` on an active row,
under cell canonicality: the mod-`p` congruence's residual lies in `(−p, p)` and collapses. -/
theorem afterSpineA_eqGate_forces (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (a b : Nat)
    (hin : VmConstraint2.base (.gate (eqGate a b))
             ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth) :
    (envAt t i).loc a = (envAt t i).loc b := by
  have h := afterSpineA_gate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
    i hi hnotlast _ hin
  unfold eqGate at h
  simp only [EmittedExpr.eval] at h
  have := diffGate_exact (hcells a) (hcells b) h
  linarith

/-- **`accumOpen_writesTo8` — THE STEP-A KEYSTONE (per accumulator family, via the shared spine).** Two
`HeapMembershipCore` witnesses sharing the sibling path (before = old leaf against the BEFORE accumulator
group; after = updated leaf, SAME key, new value, against the AFTER accumulator group) FORCE the faithful
8-felt `heapWritesTo8` over the FULL ~124-bit accumulator root. Since the accumulator families ride the
SAME `Heap8Scheme` node8 lane, this IS `HeapOpenEmit.heapOpen_writesTo8` re-instantiated at the accumulator
after-spine cols — NO spine re-proof. Named here for the assurance-case deliverable. -/
theorem accumOpen_writesTo8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (cBefore cAfter : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hBefore : HeapMembershipCore tf cBefore env)
    (hAfter  : HeapMembershipCore tf cAfter env)
    (hsib : cAfter.sib = cBefore.sib)
    (hdir : cAfter.dir = cBefore.dir)
    (hkey : (heapLeafTripleOf cAfter env).1 = (heapLeafTripleOf cBefore env).1)
    (hnext : (heapLeafTripleOf cAfter env).2.2 = (heapLeafTripleOf cBefore env).2.2) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
        (groupVal env cBefore.capRoot)
        ((heapLeafTripleOf cBefore env).1) ((heapLeafTripleOf cAfter env).2.1)
        (groupVal env cAfter.capRoot) :=
  heapOpen_writesTo8 S8 tf cBefore cAfter env hChip hBefore hAfter hsib hdir hkey hnext

/-- **`effAccumWriteV3_forces_write8` — THE STEP-A DELIVERABLE (assurance layer, per accumulator family).**
A `Satisfied2` of the after-spine accumulator-write descriptor TRACE-FORCES the faithful 8-felt write over
the FULL committed BEFORE/AFTER accumulator-root groups (`groupCol EFFECT_VM_WIDTH` / `groupCol
(EFFECT_VM_WIDTH + B_SPAN)`, the whole ~124-bit root): the read leaf `(key, oldVal)` is
membership-authenticated against the before group, the updated leaf `(key, valueCol)` against the after
group, along the SHARED path — keyed at the accumulator's published `keyCol`, written to `valueCol`. Forced
from `Satisfied2` via the shared §11 keystone — NEVER from `henc`'s `SpineCommits`. -/
theorem effAccumWriteV3_forces_write8 (S8 : Heap8Scheme)
    (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumWriteV3 groupCol keyCol valueCol base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
        (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))
        ((envAt t i).loc keyCol)
        ((envAt t i).loc valueCol)
        (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) k)) := by
  set e := envAt t i with he
  -- the BEFORE membership core (the reused heap-open read) + its dirBool.
  have hbeforeSat := effAccumWriteV3_strips_to_accumOpen groupCol keyCol valueCol
    hash base name minit mfin maddrs t hsat
  have hbeforeCore : HeapMembershipCore t.tf (capOpenCols base.traceWidth) e :=
    effHeapOpenV3_core base name hash minit mfin maddrs t hbeforeSat i hi hnotlast hcells
  -- the AFTER membership core (reusing the read's dirBool over the SHARED dir column).
  have hafterCore : HeapMembershipCore t.tf (afterSpineColsA groupCol base.traceWidth) e :=
    effAccumWriteV3_afterCore groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells hbeforeCore.dirBool
  -- weld: after leaf 0 (key) = read leaf 0.
  have hslot : e.loc ((afterSpineColsA groupCol base.traceWidth).leaf 0)
      = e.loc ((capOpenCols base.traceWidth).leaf 0) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsA groupCol base.traceWidth).leaf 0)
        ((capOpenCols base.traceWidth).leaf 0)))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsA, afterSpineColsA]
    exact afterSpineA_eqGate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells _ _ hin
  -- weld: after leaf 1 (value) = valueCol.
  have hvalw : e.loc ((afterSpineColsA groupCol base.traceWidth).leaf 1) = e.loc valueCol := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsA groupCol base.traceWidth).leaf 1)
        valueCol)) ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsA, afterSpineColsA]
    exact afterSpineA_eqGate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells _ _ hin
  -- weld: after leaf 2 (IMT nextAddr) = read leaf 2 (the value update HOLDS the pointer).
  have hnextw : e.loc ((afterSpineColsA groupCol base.traceWidth).leaf 2)
      = e.loc ((capOpenCols base.traceWidth).leaf 2) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsA groupCol base.traceWidth).leaf 2)
        ((capOpenCols base.traceWidth).leaf 2)))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsA, afterSpineColsA]
    exact afterSpineA_eqGate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells _ _ hin
  -- key bind: read leaf 0 = keyCol.
  have hkeyb : e.loc ((capOpenCols base.traceWidth).leaf 0) = e.loc keyCol := by
    have hin : VmConstraint2.base (.gate (keyBindGateA keyCol base.traceWidth))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_right _ ?_
      simp
    exact afterSpineA_eqGate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells ((capOpenCols base.traceWidth).leaf 0) keyCol hin
  -- before-block accumulator-root weld: the read's appendix capRoot group IS the committed BEFORE block.
  have hbroot : groupVal e (capOpenCols base.traceWidth).capRoot
      = (fun k => e.loc (groupCol EFFECT_VM_WIDTH k)) := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
        (groupCol EFFECT_VM_WIDTH k)))
        ∈ afterSpineConstraintsA groupCol keyCol valueCol base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := afterSpineA_eqGate_forces groupCol keyCol valueCol base name hash minit mfin maddrs t hsat
      i hi hnotlast hcells _ _ hin
    simpa [groupVal] using this
  -- assemble the shared §11 keystone over the two cores along the SHARED path (+ the held pointer).
  have hkey : (heapLeafTripleOf (afterSpineColsA groupCol base.traceWidth) e).1
      = (heapLeafTripleOf (capOpenCols base.traceWidth) e).1 := hslot
  have hnext : (heapLeafTripleOf (afterSpineColsA groupCol base.traceWidth) e).2.2
      = (heapLeafTripleOf (capOpenCols base.traceWidth) e).2.2 := hnextw
  have hw := accumOpen_writesTo8 S8 t.tf (capOpenCols base.traceWidth)
    (afterSpineColsA groupCol base.traceWidth) e hChip hbeforeCore hafterCore rfl rfl hkey hnext
  rw [hbroot] at hw
  rw [afterSpineA_capRoot_after] at hw
  -- rewrite key (read leaf 0 → keyCol) and value (after leaf 1 → valueCol).
  have hkeyb' : (heapLeafTripleOf (capOpenCols base.traceWidth) e).1 = e.loc keyCol := hkeyb
  have hvalw' : (heapLeafTripleOf (afterSpineColsA groupCol base.traceWidth) e).2.1 = e.loc valueCol := hvalw
  rw [hkeyb', hvalw'] at hw
  exact hw

#assert_axioms effAccumWriteV3_afterCore
#assert_axioms accumOpen_writesTo8
#assert_axioms effAccumWriteV3_forces_write8

end Dregg2.Circuit.Emit.AccumulatorOpenEmit
