/-
# ExactNullifierAafiRotatedStateWeld

The exact AAFI/FNSP-v3 circuit previously computed faithful eight-felt FNS3 checkpoints, but its
last sixteen public inputs still named those checkpoints directly.  That was an honest staging
point, not a state transition: a caller could choose the checkpoint PIs independently of the
committed rotated state envelope.

This module closes the Lean side of that boundary, additively and without emitting a runtime/VK:

* the first sixty v3 public inputs remain unchanged;
* PI 60..67 is now the wide commitment of the carried BEFORE rotated state;
* PI 68..75 is now the wide commitment of the successor AFTER rotated state;
* the exact pre/post FNS3(root8,count4) digests are welded into the verified rotated layout's
  faithful-eight `.nullifier` group;
* the complete BEFORE payload is transition-carried, so the first-row commitment and last-row
  FNS3 weld refer to one state rather than two unrelated row witnesses;
* every non-nullifier payload lane (including iroot) is preserved into the AFTER state — the count
  is `ROTATED_PAYLOAD_WIDTH - 8`, stated as that partition below and NOT as a literal, because the
  literal (177 at the 184-limb geometry) is exactly what the key-nonet flag day silently falsified.

The descriptor is deliberately not emitted or registered as a production artifact here.  The
remaining production seam is the Rust witness/refinement cutover: populate these two rotated
blocks, use the FNS3 envelope rather than a raw root in the map-operation boundary, regenerate the
descriptor fingerprint/VK, and only then select it in the runtime registry.
-/

import Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide
import Mathlib.Tactic
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
open Dregg2.Circuit.ExactNullifierAafiPlan (RawValue Root8 PathStep4)

set_option autoImplicit false

/-! ## 1. Allocated geometry -/

/-- The exact AAFI circuit remains the core. -/
def CORE_WIDTH : Nat := V3_TRACE_WIDTH

/-- One rotated payload is the verified pre-iroot limbs plus iroot.  The extent is read from
`RotatedLayout.rotatedNumPreLimbs` and never re-spelled here. -/
def ROTATED_PAYLOAD_WIDTH : Nat := rotatedNumPreLimbs + 1

def BEFORE_BLOCK_BASE : Nat := CORE_WIDTH
def AFTER_BLOCK_BASE : Nat := BEFORE_BLOCK_BASE + ROTATED_PAYLOAD_WIDTH
def ROTATED_HOST_WIDTH : Nat := AFTER_BLOCK_BASE + ROTATED_PAYLOAD_WIDTH

/-- Each wide chain owns `wideNumCarriers` eight-felt carriers (`EffectVmEmitRotationWide`, one per
emitted wide lookup — 63 at the key-nonet geometry). -/
def BEFORE_CARRIER_BASE : Nat := ROTATED_HOST_WIDTH
def AFTER_CARRIER_BASE : Nat := BEFORE_CARRIER_BASE + wideCarrierBlockSpan
def WELDED_TRACE_WIDTH : Nat := ROTATED_HOST_WIDTH + wideAppendixSpan

/-- The old v3 tail is replaced, not appended: the public ABI stays 76 felts. -/
def CORE_PI_COUNT : Nat := PI_PRE_STATE_COMMIT_BASE
def PI_BEFORE_ROTATED_COMMIT_BASE : Nat := CORE_PI_COUNT
def PI_AFTER_ROTATED_COMMIT_BASE : Nat := PI_BEFORE_ROTATED_COMMIT_BASE + 8
def WELDED_PI_COUNT : Nat := PI_AFTER_ROTATED_COMMIT_BASE + 8

def nullifierOffsets : List Nat :=
  (List.finRange 8).map (layoutGroupCol .nullifier)

/-- Every payload lane except the faithful-eight nullifier checkpoint is preserved.  This includes
the iroot, the last lane of the payload (`ROTATED_PAYLOAD_WIDTH - 1`): the exact append mutates only
the nullifier accumulator component. -/
def stableFrameOffsets : List Nat :=
  (List.range ROTATED_PAYLOAD_WIDTH).filter fun off => !nullifierOffsets.contains off

/-! ### The geometry pins — which of these is a GATE, and against what

⚑ A pin of a constant against its OWN definition is DECORATION.  It cannot go red for any reason
except that the definition moved, and its only available "repair" is retyping the literal.  The
2026-08-01 KEY-NONET flag day (`rotatedNumPreLimbs` 184 → 187) is the proof: every literal in this
block that named a quantity the flag day MOVES went red at once, took the whole emitter cone —
and with it `check-descriptor-drift.sh` — offline, and detected nothing whatsoever.  Those literals
are gone.  What is left is one of three things, and each says which it is:

* a **cross-source gate** — a relation between two independently authored objects;
* a **placement-vs-allocation** relation — a region walk against a declared width;
* a **non-movement pin** — a literal on a quantity this flag day must NOT have moved, which is a
  real gate precisely because a widening that reached it would go red here. -/

-- ⚑ CROSS-SOURCE GATE.  `ROTATED_PAYLOAD_WIDTH` derives from the SCALAR extent
-- `RotatedLayout.rotatedNumPreLimbs`; `rotated196.occupied` is the layout's independently authored
-- column ENUMERATION (singles ++ groups ++ carrier octets ++ their ninth lanes ++ the fields
-- nonet).  Under `rotated196_legal`'s `disjoint` + `inBounds` the two agree only on a COMPLETE
-- tiling, so this goes red on exactly the shape the key-nonet flag day exists to forbid: an extent
-- bumped with no columns behind it, or a column allocated past a stale extent.
#guard ROTATED_PAYLOAD_WIDTH == rotated196.occupied.length + 1

-- NON-MOVEMENT PIN.  The exact-AAFI core sits BELOW both rotated blocks; a rotation flag day must
-- not reach it.  2442 is `ExactNullifierAafiDescriptorPlan.V3_TRACE_WIDTH`, computed there from the
-- FNS3 step schedule — a widening that moved the core goes red HERE.
#guard CORE_WIDTH == 2442
#guard BEFORE_BLOCK_BASE == CORE_WIDTH

-- PLACEMENT vs ALLOCATION.  The left side WALKS the regions (core, two payload blocks, two wide
-- carrier blocks of `wideCarrierBlockSpan` each); the right side is the width this descriptor
-- ALLOCATES (`ROTATED_HOST_WIDTH + wideAppendixSpan`).  Two allocation policies in two modules: a
-- carrier block that outgrew its appendix would put its last carrier column outside the declared
-- trace width, and that is what this catches.
#guard AFTER_CARRIER_BASE + wideCarrierBlockSpan == WELDED_TRACE_WIDTH

-- NON-MOVEMENT PIN — the PUBLIC ABI.  76 felts is the wire-visible contract (`piCount` in the
-- emitted descriptor and in every verifier that reads it).  The flag day must not move it.
#guard CORE_PI_COUNT == 60
#guard PI_BEFORE_ROTATED_COMMIT_BASE == 60
#guard PI_AFTER_ROTATED_COMMIT_BASE == 68
#guard WELDED_PI_COUNT == 76

-- NON-MOVEMENT PIN + PARTITION.  The nullifier group's columns are unmoved by the flag day (every
-- column 0..183 keeps its meaning), the group really is INSIDE the carried payload, and the stable
-- frame is exactly its complement — stated as a partition of `ROTATED_PAYLOAD_WIDTH`, never as the
-- literal 177 the flag day falsified.
#guard nullifierOffsets == [26, 68, 69, 70, 71, 72, 73, 74]
#guard nullifierOffsets.all (fun off => decide (off < ROTATED_PAYLOAD_WIDTH))
#guard stableFrameOffsets.length + nullifierOffsets.length == ROTATED_PAYLOAD_WIDTH

/-! ## 2. Actual weld gates -/

def carryBody (col : Nat) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow (Dregg2.Circuit.GateExpr.gThread col col)

/-- ⚑ **THE BYTE PIN.** `carryBody` is `GateExpr.gThread` at the window view -- the SAME object
`AccumulatorNonRevocationEmit.constBody`,
`EffectActionBindingEmit.contWindowBody` and `DyckStackEmit.wThread` each wrote out separately.
`rfl`, for every column: no emitted byte moved. -/
theorem carryBody_eq (col : Nat) :
    carryBody col = WindowExpr.add (.nxt col) (.mul (.const (-1)) (.loc col)) := rfl

/-- The input state published on row zero is the input state opened by FNS3 on the last row. -/
def beforePayloadContinuity : List VmConstraint2 :=
  (List.range ROTATED_PAYLOAD_WIDTH).map fun off =>
    .windowGate ⟨carryBody (BEFORE_BLOCK_BASE + off), true⟩

/-- Outside the nullifier group the transition is the identity. -/
def stableFrameConstraints : List VmConstraint2 :=
  stableFrameOffsets.map fun off => .base (.boundary .last
    (esub (.var (AFTER_BLOCK_BASE + off)) (.var (BEFORE_BLOCK_BASE + off))))

/-- Weld the two circuit-derived FNS3 checkpoints to the nullifier group of the two committed
rotated payloads.  All eight lanes are used; no lane-zero/raw-root downgrade survives. -/
def fns3WeldConstraints : List VmConstraint2 :=
  (List.finRange 8).map (fun i => .base (.boundary .last
    (esub (.var (preStateCommitDigestCols.getD i.val 0))
      (.var (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i))))) ++
  (List.finRange 8).map (fun i => .base (.boundary .last
    (esub (.var (postStateCommitDigestCols.getD i.val 0))
      (.var (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i)))))

def wideStateLookups : List VmConstraint2 :=
  rotV3WideLookups BEFORE_BLOCK_BASE BEFORE_CARRIER_BASE ++
    rotV3WideLookups AFTER_BLOCK_BASE AFTER_CARRIER_BASE

def wideStatePins : List VmConstraint2 :=
  commitPins .first (carrierCols BEFORE_CARRIER_BASE wideCommitCarrier) PI_BEFORE_ROTATED_COMMIT_BASE ++
    commitPins .last (carrierCols AFTER_CARRIER_BASE wideCommitCarrier) PI_AFTER_ROTATED_COMMIT_BASE

/-- Only the first sixty v3 pins survive.  In particular the old caller-selected FNS3 digest pins
at 60..75 are absent; those slots now publish the outer rotated-state commitments. -/
def retainedCorePins : List VmConstraint2 :=
  (v3PublicPins.take CORE_PI_COUNT).map publicPinConstraint

def exactRotatedStateConstraints : List VmConstraint2 :=
  baseV2ConstraintsWithoutPins ++ exactAafiConstraints ++ retainedCorePins ++
    beforePayloadContinuity ++ stableFrameConstraints ++ fns3WeldConstraints ++
    wideStateLookups ++ wideStatePins

def exactNullifierAafiRotatedStateDescriptor : EffectVmDescriptor2 :=
  { name := "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state"
  , traceWidth := WELDED_TRACE_WIDTH
  , piCount := WELDED_PI_COUNT
  , tables := [mainTableDef WELDED_TRACE_WIDTH, poseidon2State16ChipTableDef,
      poseidon2ChipTableDef, rangeTable 15, rangeTable 16]
  , constraints := exactRotatedStateConstraints
  , hashSites := []
  , ranges := [] }

-- EMITTED-LIST relations, stated against the geometry they claim to cover rather than against a
-- literal count.  Every payload lane gets exactly one carry gate; every payload lane is either
-- frozen across the transition or one of the eight welded nullifier lanes; the wide chain emits one
-- lookup per carrier per block.
#guard beforePayloadContinuity.length == ROTATED_PAYLOAD_WIDTH
#guard stableFrameConstraints.length + nullifierOffsets.length == ROTATED_PAYLOAD_WIDTH
#guard fns3WeldConstraints.length == 2 * nullifierOffsets.length
#guard wideStateLookups.length == 2 * wideNumCarriers
#guard wideStatePins.length == 16
#guard retainedCorePins.length == CORE_PI_COUNT
#guard (v3PublicPins.take CORE_PI_COUNT).map (fun p => p.pi) == List.range 60
-- NON-MOVEMENT PIN — the emitted public ABI.  (The trace width is NOT pinned to a literal here: it
-- is `WELDED_TRACE_WIDTH` by construction, and its real check is the placement-vs-allocation guard
-- above.)
#guard exactNullifierAafiRotatedStateDescriptor.piCount == 76
#guard exactNullifierAafiRotatedStateDescriptor.tables.length == 5
#guard exactNullifierAafiRotatedStateDescriptor.tables.map (fun t => t.id) ==
  [.main, poseidon2state16, .poseidon2, rangeTid 15, rangeTid 16]

/-! ### Structural membership teeth -/

theorem beforePayloadContinuity_mem (off : Nat) (hoff : off < ROTATED_PAYLOAD_WIDTH) :
    .windowGate ⟨carryBody (BEFORE_BLOCK_BASE + off), true⟩ ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .windowGate ⟨carryBody (BEFORE_BLOCK_BASE + off), true⟩ ∈
      beforePayloadContinuity :=
    List.mem_map.mpr ⟨off, List.mem_range.mpr hoff, rfl⟩
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem fns3PreWeld_mem (i : Fin 8) :
    .base (.boundary .last
      (esub (.var (preStateCommitDigestCols.getD i.val 0))
        (.var (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i)))) ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .base (.boundary .last
      (esub (.var (preStateCommitDigestCols.getD i.val 0))
        (.var (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i)))) ∈
      fns3WeldConstraints := by
    unfold fns3WeldConstraints
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem fns3PostWeld_mem (i : Fin 8) :
    .base (.boundary .last
      (esub (.var (postStateCommitDigestCols.getD i.val 0))
        (.var (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i)))) ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .base (.boundary .last
      (esub (.var (postStateCommitDigestCols.getD i.val 0))
        (.var (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i)))) ∈
      fns3WeldConstraints := by
    unfold fns3WeldConstraints
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem stableFrameConstraint_mem (off : Nat) (hoff : off ∈ stableFrameOffsets) :
    .base (.boundary .last
      (esub (.var (AFTER_BLOCK_BASE + off)) (.var (BEFORE_BLOCK_BASE + off)))) ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .base (.boundary .last
      (esub (.var (AFTER_BLOCK_BASE + off)) (.var (BEFORE_BLOCK_BASE + off)))) ∈
      stableFrameConstraints := List.mem_map.mpr ⟨off, hoff, rfl⟩
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem beforeWideLookup_mem :
    ∀ c ∈ rotV3WideLookups BEFORE_BLOCK_BASE BEFORE_CARRIER_BASE,
      c ∈ exactNullifierAafiRotatedStateDescriptor.constraints := by
  intro c hc
  have hlocal : c ∈ wideStateLookups := List.mem_append_left _ hc
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem afterWideLookup_mem :
    ∀ c ∈ rotV3WideLookups AFTER_BLOCK_BASE AFTER_CARRIER_BASE,
      c ∈ exactNullifierAafiRotatedStateDescriptor.constraints := by
  intro c hc
  have hlocal : c ∈ wideStateLookups := List.mem_append_right _ hc
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem beforeWidePin_mem (k : Nat) (hk : k < 8) :
    .base (.piBinding .first ((carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).getD k 0)
      (PI_BEFORE_ROTATED_COMMIT_BASE + k)) ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .base (.piBinding .first ((carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).getD k 0)
      (PI_BEFORE_ROTATED_COMMIT_BASE + k)) ∈ wideStatePins := by
    unfold wideStatePins commitPins
    apply List.mem_append_left
    rw [List.mem_map]
    refine ⟨((carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).getD k 0, k), ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨k, ?_, ?_⟩
    · rw [List.length_zipIdx, carrierCols_length]
      exact hk
    · rw [List.getElem_zipIdx]
      have hk' : k < (carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).length := by
        rw [carrierCols_length]
        exact hk
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

theorem afterWidePin_mem (k : Nat) (hk : k < 8) :
    .base (.piBinding .last ((carrierCols AFTER_CARRIER_BASE wideCommitCarrier).getD k 0)
      (PI_AFTER_ROTATED_COMMIT_BASE + k)) ∈
      exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hlocal : .base (.piBinding .last ((carrierCols AFTER_CARRIER_BASE wideCommitCarrier).getD k 0)
      (PI_AFTER_ROTATED_COMMIT_BASE + k)) ∈ wideStatePins := by
    unfold wideStatePins commitPins
    apply List.mem_append_right
    rw [List.mem_map]
    refine ⟨((carrierCols AFTER_CARRIER_BASE wideCommitCarrier).getD k 0, k), ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨k, ?_, ?_⟩
    · rw [List.length_zipIdx, carrierCols_length]
      exact hk
    · rw [List.getElem_zipIdx]
      have hk' : k < (carrierCols AFTER_CARRIER_BASE wideCommitCarrier).length := by
        rw [carrierCols_length]
        exact hk
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    List.mem_append]
  tauto

private theorem modeq_of_shape {e a b : ℤ} (hshape : e = a - b)
    (h : e ≡ 0 [ZMOD 2013265921]) : a ≡ b [ZMOD 2013265921] := by
  subst hshape
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (a - b) = b - a := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-! ### Facts extracted from an actual satisfying descriptor trace -/

theorem satisfying_last_row_welds_fns3
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length)
    (hlast : (row + 1 == t.rows.length) = true) (i : Fin 8) :
    (envAt t row).loc (preStateCommitDigestCols.getD i.val 0) ≡
        (envAt t row).loc (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i)
          [ZMOD 2013265921] ∧
      (envAt t row).loc (postStateCommitDigestCols.getD i.val 0) ≡
        (envAt t row).loc (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i)
          [ZMOD 2013265921] := by
  have hconstraints := hsat.rowConstraints row hrow
  constructor
  · have h := hconstraints _ (fns3PreWeld_mem i)
    simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
    have hz := h hlast
    apply modeq_of_shape (e :=
      (esub (.var (preStateCommitDigestCols.getD i.val 0))
        (.var (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i))).eval (envAt t row).loc)
    · simp [esub, eadd, eneg, emul, EmittedExpr.eval, sub_eq_add_neg]
    · exact hz
  · have h := hconstraints _ (fns3PostWeld_mem i)
    simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
    have hz := h hlast
    apply modeq_of_shape (e :=
      (esub (.var (postStateCommitDigestCols.getD i.val 0))
        (.var (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i))).eval (envAt t row).loc)
    · simp [esub, eadd, eneg, emul, EmittedExpr.eval, sub_eq_add_neg]
    · exact hz

theorem satisfying_last_row_preserves_stable_frame
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row off : Nat) (hrow : row < t.rows.length)
    (hlast : (row + 1 == t.rows.length) = true) (hoff : off ∈ stableFrameOffsets) :
    (envAt t row).loc (AFTER_BLOCK_BASE + off) ≡
      (envAt t row).loc (BEFORE_BLOCK_BASE + off) [ZMOD 2013265921] := by
  have h := hsat.rowConstraints row hrow _ (stableFrameConstraint_mem off hoff)
  simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
  have hz := h hlast
  apply modeq_of_shape (e :=
    (esub (.var (AFTER_BLOCK_BASE + off))
      (.var (BEFORE_BLOCK_BASE + off))).eval (envAt t row).loc)
  · simp [esub, eadd, eneg, emul, EmittedExpr.eval, sub_eq_add_neg]
  · exact hz

/-- Both wide lookup chains of a satisfying trace really compute the commitment primitive over
their own row's `rotatedNumPreLimbs` limbs and iroot. -/
theorem satisfying_row_computes_wide_state_commits
    (permW : List ℤ → List ℤ) (scalarHash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (hchip : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 scalarHash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    carrierVals BEFORE_CARRIER_BASE wideCommitCarrier (envAt t row).loc =
        wireCommitR8 permW (preLimbsWide BEFORE_BLOCK_BASE (envAt t row).loc)
          ((envAt t row).loc (BEFORE_BLOCK_BASE + B_IROOT)) ∧
      carrierVals AFTER_CARRIER_BASE wideCommitCarrier (envAt t row).loc =
        wireCommitR8 permW (preLimbsWide AFTER_BLOCK_BASE (envAt t row).loc)
          ((envAt t row).loc (AFTER_BLOCK_BASE + B_IROOT)) := by
  have hconstraints := hsat.rowConstraints row hrow
  constructor
  · apply rotV3WidePin permW (t.tf .poseidon2) hchip (envAt t row)
      BEFORE_BLOCK_BASE BEFORE_CARRIER_BASE
    intro p hp
    have hmem := beforeWideLookup_mem
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have h := hconstraints _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using h
  · apply rotV3WidePin permW (t.tf .poseidon2) hchip (envAt t row)
      AFTER_BLOCK_BASE AFTER_CARRIER_BASE
    intro p hp
    have hmem := afterWideLookup_mem
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have h := hconstraints _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using h

/-- The two computed eight-felt carriers are the descriptor's public state boundary: BEFORE on the
first row and AFTER on the last row. -/
theorem satisfying_row_publishes_wide_state_commits
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    ((row == 0) = true → ∀ k, (hk : k < 8) →
      (envAt t row).loc ((carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).getD k 0) ≡
        (envAt t row).pub (PI_BEFORE_ROTATED_COMMIT_BASE + k) [ZMOD 2013265921]) ∧
    ((row + 1 == t.rows.length) = true → ∀ k, (hk : k < 8) →
      (envAt t row).loc ((carrierCols AFTER_CARRIER_BASE wideCommitCarrier).getD k 0) ≡
        (envAt t row).pub (PI_AFTER_ROTATED_COMMIT_BASE + k) [ZMOD 2013265921]) := by
  have hconstraints := hsat.rowConstraints row hrow
  constructor
  · intro hfirst k hk
    have h := hconstraints _ (beforeWidePin_mem k hk)
    simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
    exact h hfirst
  · intro hlast k hk
    have h := hconstraints _ (afterWidePin_mem k hk)
    simp only [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at h
    exact h hlast

/-! ## 3. Semantic binding and localized collision teeth -/

/-- A semantic rotated state with an explicit proof that its faithful nullifier lanes carry the
FNS3 checkpoint.  This mirrors exactly the emitted `fns3WeldConstraints`. -/
structure CarriedRotatedState where
  limbs : List ℤ
  iroot : ℤ
  checkpoint : Root8
  limbs_length : limbs.length = rotatedNumPreLimbs
  checkpoint_weld : ∀ i : Fin 8,
    limbs.getD (layoutGroupCol .nullifier i) 0 = checkpoint i

def outerCommit (permW : List ℤ → List ℤ) (s : CarriedRotatedState) : List ℤ :=
  wireCommitR8 permW s.limbs s.iroot

/-- Semantic projection of the emitted `ROTATED_PAYLOAD_WIDTH`-cell payload. -/
def payloadAt (s : CarriedRotatedState) (off : Nat) : ℤ :=
  if off = rotatedNumPreLimbs then s.iroot else s.limbs.getD off 0

def PreservesStableFrame (before after : CarriedRotatedState) : Prop :=
  ∀ off ∈ stableFrameOffsets, payloadAt before off = payloadAt after off

/-- Direct rejection tooth for every emitted identity lane (`stableFrameOffsets`). -/
theorem changed_stable_frame_cell_rejected {before after : CarriedRotatedState}
    {off : Nat} (hoff : off ∈ stableFrameOffsets)
    (hchanged : payloadAt before off ≠ payloadAt after off) :
    ¬ PreservesStableFrame before after := by
  intro hpres
  exact hchanged (hpres off hoff)

/-- Commitment-side tooth: changing any rotated payload cell moves the eight-felt outer commitment,
or the existing wide extractor returns a concrete deployed-permutation collision. -/
theorem changed_payload_moves_or_wire_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (left right : CarriedRotatedState) (off : Nat)
    (hchanged : payloadAt left off ≠ payloadAt right off) :
    outerCommit permW left ≠ outerCommit permW right ∨
      WireColl permW left.limbs left.iroot right.limbs right.iroot := by
  have hstate : ¬ (left.limbs = right.limbs ∧ left.iroot = right.iroot) := by
    rintro ⟨hlimbs, hiroot⟩
    apply hchanged
    simp [payloadAt, hlimbs, hiroot]
  by_cases hcommit : outerCommit permW left = outerCommit permW right
  · rcases wireCommitR8_binds_or_collides permW hW
        (left.limbs_length.trans right.limbs_length.symm) hcommit with hsame | hcoll
    · exact absurd hsame hstate
    · exact Or.inr hcoll
  · exact Or.inl hcommit

/-- The stable-frame-specific form used by the emitted identity gates. -/
theorem changed_stable_frame_moves_or_wire_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (left right : CarriedRotatedState) (off : Nat)
    (_hoff : off ∈ stableFrameOffsets)
    (hchanged : payloadAt left off ≠ payloadAt right off) :
    outerCommit permW left ≠ outerCommit permW right ∨
      WireColl permW left.limbs left.iroot right.limbs right.iroot :=
  changed_payload_moves_or_wire_collides permW hW left right off hchanged

theorem checkpoint_eq_of_limbs_eq {left right : CarriedRotatedState}
    (h : left.limbs = right.limbs) : left.checkpoint = right.checkpoint := by
  funext i
  rw [← left.checkpoint_weld i, ← right.checkpoint_weld i, h]

/-- Equal outer commitments bind the entire carried state (hence the FNS3 checkpoint), or expose
the wide permutation collision returned by the existing constructive extractor. -/
theorem carried_checkpoint_binds_or_wire_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (left right : CarriedRotatedState)
    (h : outerCommit permW left = outerCommit permW right) :
    left.checkpoint = right.checkpoint ∨
      WireColl permW left.limbs left.iroot right.limbs right.iroot := by
  rcases wireCommitR8_binds_or_collides permW hW
      (left.limbs_length.trans right.limbs_length.symm) h with hsame | hcoll
  · exact Or.inl (checkpoint_eq_of_limbs_eq hsame.1)
  · exact Or.inr hcoll

theorem wrong_carried_checkpoint_moves_or_wire_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (left right : CarriedRotatedState)
    (hne : left.checkpoint ≠ right.checkpoint) :
    outerCommit permW left ≠ outerCommit permW right ∨
      WireColl permW left.limbs left.iroot right.limbs right.iroot := by
  by_cases hcommit : outerCommit permW left = outerCommit permW right
  · rcases carried_checkpoint_binds_or_wire_collides permW hW left right hcommit with heq | hcoll
    · exact absurd heq hne
    · exact Or.inr hcoll
  · exact Or.inl hcommit

theorem rootBlock_injective :
    Function.Injective rootBlock := by
  intro left right h
  unfold rootBlock at h
  exact List.ofFn_injective h

theorem accumulatorStateBlock_root_eq_of_eq {leftRoot rightRoot : Root8}
    {leftCount rightCount : RawValue}
    (h : accumulatorStateBlock leftRoot leftCount =
      accumulatorStateBlock rightRoot rightCount) : leftRoot = rightRoot := by
  have ht := congrArg (fun xs : List ℤ => xs.take 9) h
  have hleft : (accumulatorStateBlock leftRoot leftCount).take 9 =
      [EXACT_STATE_DOMAIN] ++ rootBlock leftRoot := by
    unfold accumulatorStateBlock
    rw [List.take_append_of_le_length]
    · simp [rootBlock_length]
    · simp [rootBlock_length]
  have hright : (accumulatorStateBlock rightRoot rightCount).take 9 =
      [EXACT_STATE_DOMAIN] ++ rootBlock rightRoot := by
    unfold accumulatorStateBlock
    rw [List.take_append_of_le_length]
    · simp [rootBlock_length]
    · simp [rootBlock_length]
  change (accumulatorStateBlock leftRoot leftCount).take 9 =
    (accumulatorStateBlock rightRoot rightCount).take 9 at ht
  rw [hleft, hright] at ht
  exact rootBlock_injective (List.cons.inj ht).2

theorem carried_checkpoint_wrong_root_forces_collision
    {leftRoot rightRoot : Root8} {leftCount rightCount : RawValue}
    (hne : leftRoot ≠ rightRoot)
    (heq : accumulatorStateCommitReal leftRoot leftCount =
      accumulatorStateCommitReal rightRoot rightCount) :
    FullStateHash8Collision
      (accumulatorStateBlock leftRoot leftCount)
      (accumulatorStateBlock rightRoot rightCount) := by
  refine ⟨?_, heq⟩
  intro hblock
  exact hne (accumulatorStateBlock_root_eq_of_eq hblock)

/-! ### Raw-root / FNS3 type-confusion teeth -/

/-- A digest of some explicitly named raw-root preimage cannot be accepted as the FNS3 checkpoint
for `(root,count)` unless the values differ (the weld rejects) or those two domain-separated
preimages collide under the real full-state sponge. -/
theorem raw_digest_in_fns3_slot_rejects_or_collides
    (rawPreimage : List ℤ) (root : Root8) (count : RawValue)
    (hraw : root = fullStateHash8 rawPreimage)
    (hmaterial : rawPreimage ≠ accumulatorStateBlock root count) :
    root ≠ accumulatorStateCommitReal root count ∨
      FullStateHash8Collision rawPreimage (accumulatorStateBlock root count) := by
  by_cases heq : root = accumulatorStateCommitReal root count
  · right
    refine ⟨hmaterial, ?_⟩
    simpa [accumulatorStateCommitReal] using hraw.symm.trans heq
  · exact Or.inl heq

theorem exactNodeBlock_ne_accumulatorStateBlock
    (current : Root8) (step : PathStep4) (count : RawValue) :
    exactNodeBlock current step ≠
      accumulatorStateBlock (exactParent4Real current step) count := by
  intro h
  have hhead := congrArg (fun xs : List ℤ => xs.headD 0) h
  norm_num [exactNodeBlock, accumulatorStateBlock, EXACT_NODE_DOMAIN, EXACT_STATE_DOMAIN] at hhead

/-- Specialized production tooth: the ordinary exact-tree root (`FNN2`) is not the carried
checkpoint type (`FNS3`).  Placing that raw root in the FNS3 lanes rejects, unless the concrete
`FNN2` node block and `FNS3(root,count)` block collide. -/
theorem raw_exact_root_in_fns3_slot_rejects_or_collides
    (current : Root8) (step : PathStep4) (count : RawValue) :
    exactParent4Real current step ≠
        accumulatorStateCommitReal (exactParent4Real current step) count ∨
      FullStateHash8Collision (exactNodeBlock current step)
        (accumulatorStateBlock (exactParent4Real current step) count) := by
  apply raw_digest_in_fns3_slot_rejects_or_collides
  · rfl
  · exact exactNodeBlock_ne_accumulatorStateBlock current step count

def OpensCheckpoint (s : CarriedRotatedState) (root : Root8) (count : RawValue) : Prop :=
  s.checkpoint = accumulatorStateCommitReal root count

/-- Apex state-boundary statement.  If a forged carried state opens the same outer checkpoint while
changing either exact nullifier root or count, one of the two concrete hash layers has collided:
the wide rotated commitment, or the inner domain-separated FNS3 sponge. -/
theorem wrong_fns3_opening_moves_or_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (left right : CarriedRotatedState)
    (leftRoot rightRoot : Root8) (leftCount rightCount : RawValue)
    (hleft : OpensCheckpoint left leftRoot leftCount)
    (hright : OpensCheckpoint right rightRoot rightCount)
    (hwrong : leftRoot ≠ rightRoot ∨ leftCount ≠ rightCount) :
    outerCommit permW left ≠ outerCommit permW right ∨
      WireColl permW left.limbs left.iroot right.limbs right.iroot ∨
      FullStateHash8Collision
        (accumulatorStateBlock leftRoot leftCount)
        (accumulatorStateBlock rightRoot rightCount) := by
  by_cases houter : outerCommit permW left = outerCommit permW right
  · rcases carried_checkpoint_binds_or_wire_collides permW hW left right houter with hcp | hwire
    · right; right
      refine ⟨?_, ?_⟩
      · intro hblock
        rcases hwrong with hroot | hcount
        · exact hroot (accumulatorStateBlock_root_eq_of_eq hblock)
        · exact hcount (accumulatorStateBlock_count_eq_of_eq hblock)
      · unfold OpensCheckpoint at hleft hright
        simpa [accumulatorStateCommitReal] using hleft.symm.trans (hcp.trans hright)
    · exact Or.inr (Or.inl hwire)
  · exact Or.inl houter

#assert_axioms checkpoint_eq_of_limbs_eq
#assert_axioms satisfying_last_row_welds_fns3
#assert_axioms satisfying_last_row_preserves_stable_frame
#assert_axioms satisfying_row_computes_wide_state_commits
#assert_axioms satisfying_row_publishes_wide_state_commits
#assert_axioms carried_checkpoint_binds_or_wire_collides
#assert_axioms wrong_carried_checkpoint_moves_or_wire_collides
#assert_axioms changed_stable_frame_cell_rejected
#assert_axioms changed_payload_moves_or_wire_collides
#assert_axioms changed_stable_frame_moves_or_wire_collides
#assert_axioms accumulatorStateBlock_root_eq_of_eq
#assert_axioms carried_checkpoint_wrong_root_forces_collision
#assert_axioms raw_digest_in_fns3_slot_rejects_or_collides
#assert_axioms raw_exact_root_in_fns3_slot_rejects_or_collides
#assert_axioms wrong_fns3_opening_moves_or_collides

end Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
