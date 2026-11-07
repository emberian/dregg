/-
# Dregg2.Circuit.Emit.ShieldedNoteAppendDescriptor — L2: the Lean-authored IN-AIR APPEND
  GROW-GATE for the **shielded-note accumulator** (`cell/src/shielded_note_set.rs`), so that
  `ShieldedNoteSet::root8()` is trustworthy as the `piCOMMITTED` source that closes seam #15.

## ⚑ THE GROUND-TRUTH FINDING FIRST: the grow-gate ALREADY GENERALIZES; L2 is the INSTANCE
   plus the one thing the three cleartext families do not have — the HIDING leaf.

`docs/DESIGN-shielded-apex-tree-reconciliation.md` §6 L2 asks for "the Lean-authored in-AIR append
grow-gate, generalizing the `ShieldedWholeNoteSwapSubstrate` aafi32 append". Reading the record
first (`feedback-orient-from-the-record`), there are TWO already-landed generic append laws, and
between them they cover the whole of the append semantics the shielded set needs:

  * **The SET-LEVEL 8-felt insert gate** — `Emit.AccumulatorInsertEmit`. `effAccumInsertV3` is a
    PARAMETRIC descriptor constructor over `(groupCol, keyCol, valueCol, sel, base, name)`, and
    `effAccumInsertV3_forces_write8` proves `Satisfied2 ⟹ accumInserts8` over the FULL committed
    8-felt BEFORE/AFTER root groups — never lane-0. `accumInserts8` IS "the AFTER tree is the
    BEFORE tree plus exactly this leaf": key FRESH in BEFORE (no duplicate), spliced `(key, value)`
    leaf PRESENT in AFTER, and the committed key set grows by EXACTLY `key` in sorted order
    (`update_sound8`). It is explicitly "parametric over the 3 families" — nullifier, commitments,
    cells (`RotatedKernelRefinementCapFamily` §J′ instantiates all three).
    **The shielded-note set is the FOURTH family.**
  * **The PHYSICAL two-path AAFI append law** — `MapOpsColumnLayout.aafiInsert_forces_imtInsert`
    (the same aafi32 append shape the substrate descriptor emits, but DEPTH-GENERIC and
    VALUE-GENERIC): an accepting AAFI row forces the committed digest vector to change at EXACTLY
    two positions (low-`nextAddr := k`, append at a distinct FREE slot), with the pointer bracket
    `low.addr < k < low.next` surviving. Instantiated at `dep := HEAP_TREE_DEPTH = 16` and the
    HIDING value `0`, that is precisely "appended at the next AAFI free index, no prior leaf
    rewritten, none dropped, no shift".

So this module does NOT re-author tree combinatorics, a Merkle chain, or a second append law.
What it DOES author is the part that genuinely does not exist yet:

  1. **`effShieldedNoteAppendV3`** — the shielded family's descriptor: `effAccumInsertV3` plus the
     **HIDING-LEAF ZERO PIN** on the leaf's value column. The three deployed families all key a
     value-CARRYING leaf (`split_u64(value).0` — a cleartext note value / revocation height); the
     shielded leaf is `HeapLeaf::entry(fold(commitment), 0)` and MUST carry no cleartext value
     (`shielded_note_set.rs:266-283`, DESIGN §3 R1 "with no cleartext value column"). That pin is a
     NEW in-AIR constraint with no analogue in the cleartext families, and it is exactly what makes
     R2 (reusing `note_commitments`, whose value column is load-bearing) unsound.
  2. **`shieldedAppends8`** — the shielded append relation (`accumInserts8` at value `0`) and its
     soundness consequences: growth-by-exactly-the-commitment, prior leaves preserved, no duplicate,
     the appended leaf hiding.
  3. **The rejection teeth** — a cleartext value smuggled into the leaf is UNSAT; a duplicate append
     is UNSAT; a dropped prior leaf is UNSAT; a FROZEN after-root (`after = before`) is UNSAT
     unconditionally.
  4. **The completeness / non-vacuity demo** — an honest append of a fresh hiding commitment
     SATISFIES and strictly grows the committed key set (so the gate is not a DoS), plus two-sided
     `#guard` canaries on the hiding pin itself.

Why NOT a second bespoke depth-16 descriptor mirroring `ShieldedWholeNoteSwapSubstrateDescriptor`
column-for-column: that descriptor's geometry is hard-wired (`DEPTH := 32`, 16-lane keys, a 16-lane
wide binding, the market-swap/nullifier payload) and is not parameterisable to the depth-16 3-felt
`heap_root.rs` IMT leaf the L0 accumulator actually commits. Re-authoring it would duplicate an
append law that is already proven generically and would put the shielded set on a SECOND tree
encoding — the DESIGN §7 Q2 "one committed tree encoding" mistake. L0 already chose the encoding
(`CanonicalHeapTree8`, `shielded_note_set.rs:297-308`); this module gates THAT tree.

## The soundness statement, at the resolution it actually holds

`shieldedNoteAppend_forces_grow8`: a satisfying `effShieldedNoteAppendV3` trace, on an active row,
with the realizable non-membership bracket + the two spine bindings, FORCES

    accumInserts8 S8 beforeRoot (loc keyCol) 0 afterRoot

over the FULL committed 8-felt BEFORE/AFTER root groups — i.e. the committed key set of AFTER is
EXACTLY that of BEFORE plus the appended commitment key, the appended leaf carries value `0`, and
the appended key was ABSENT from BEFORE. The `0` is TRACE-FORCED (`shieldedAppend_forces_hiding_leaf`),
not assumed.

## Floors and residuals — NAMED, not laundered

FLOORS (legitimate, the same family every landed accumulator module carries):
  * `Poseidon2SpongeCR` — the sponge/`mapNode` collision-resistance the §5 physical AAFI law rides
    (`aafiInsert_forces_imtInsert`); the same floor `MapOpsColumnLayout` / `IndexedMerkleTree` /
    every deployed map-op stands on.
  * `SpineCommits8` / `GapOpen8` — the realizable spine↔root binding and the pred/succ bracket, a
    HYPOTHESIS (the deployed `compute_canonical_heap_root_8` fold), never an axiom. Same status as
    in `AccumulatorInsertEmit` and the three deployed families.
  * `PreRootModelsChain` — the NAMED, differential-checkable `xs = imtLayout phys ∧ phys ~ c`
    layout faithfulness the §5 `_layout` bridge consumes (not a free membership).

RESIDUALS (NOT closed here, per the DESIGN §6 lane table):
  * **L1** — landing `ShieldedNoteSet::root8()` as a rotation carrier BASE LIMB is a VK epoch that
    re-baselines the whole rotated cohort. This module is parametric over `groupCol`, so it holds
    for whatever limb L1 lands; it does NOT choose one, and NO deployed descriptor bytes change.
  * **L4** — routing `apply_shielded_transfer` through this gate and sourcing `piCOMMITTED` from
    `root8()`. Until then the gate constrains nothing deployed.
  * The sort key is the LOSSY `fold_bytes32_to_bb(commitment)` (~31-bit) — as for ALL FOUR sibling
    accumulators (`shielded_note_set.rs:38-45` says so). The ROOT is 8 felts; the KEY is not. The
    key-widening path exists (`SortedTreeInsertWide8` at `K := Digest8Key`) and is composed with
    here at `K := ℤ` (§4), but the deployed key stays the folded felt.
  * The AAFI `seq` column L0 persists is the ORDER-DEPENDENT replay layer; `root8()` itself is the
    SORTED-COMPACTED, order-INDEPENDENT root (`shielded_note_set.rs:78-85, 217-236`). §1-§3 gate the
    sorted spine; §5 gates the physical append-at-free-index. Both are needed and both are here.
  * §6's completeness/non-vacuity witness lives at the `[LinearOrder K]`-GENERIC `SpineCommitsW`
    wrapper (`Root := Bool`, the exact level `SortedTreeInsertWide8`'s own landed `insOpens` demo
    uses), NOT at a concrete `Heap8Scheme`. That is deliberate and stated rather than papered over: a
    concrete `SpineCommits8` inhabitant at a REAL Poseidon2 scheme is a collision-resistance-strength
    claim about which leaves open, not something a Lean term can exhibit. What §6 does establish is
    that the grow-gate's SET-LEVEL relation genuinely FIRES on an honest append and genuinely
    EXCLUDES a value-carrying leaf — so the teeth are not vacuous and the gate is not a DoS.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; every import read-only. No
`sorry`/`admit`/`native_decide`. BYTE-SAFE: a NEW descriptor constructor and new theorems only —
`effAccumInsertV3` and every deployed descriptor are untouched (`shieldedAppend_is_additive`).
-/
import Dregg2.Circuit.Emit.AccumulatorInsertEmit
import Dregg2.Circuit.SortedTreeInsertWide8
import Dregg2.Circuit.IndexedMerkleTree

namespace Dregg2.Circuit.Emit.ShieldedNoteAppendDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint EFFECT_VM_WIDTH)
open Dregg2.Circuit.DescriptorIR2
  (VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (MembersAt8)
open Dregg2.Circuit.Emit.AccumulatorInsertEmit
  (effAccumInsertV3 effAccumInsertV3_forces_write8 accumInserts8 accumInserts8_setGrows
   accumInserts8_fresh accumInserts8_value_present)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8 (SpineCommits8 keysOf8 GapOpen8 update_sound8)
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (SpineCommitsW keysOfW)
open Dregg2.Circuit.SortedTreeInsertWide8 (sortedInsertW update_soundW update_preserves_sortedW)
open Dregg2.Crypto.NonMembership (Sorted)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the HIDING-LEAF ZERO PIN: the one in-AIR constraint the three cleartext families lack.

The sibling accumulators key a VALUE-CARRYING leaf — the noteCreate grow-gate literally reads
`split_u64(value).0` out of the leaf. A shielded note MUST NOT reveal its value, so its leaf is
`HeapLeaf::entry(fold(commitment), 0)`: the folded commitment as sort key, and a **ZERO value
column**. This section pins that column IN-AIR, so a prover cannot smuggle a cleartext value (or
any other side-channel felt) into the committed shielded leaf. -/

/-- **`hidingZeroBody sel valueCol`** — the HIDING pin body: the accumulator leaf's VALUE column is
`0`. `sel = none` pins it unconditionally; `sel = some s` gates the pin on the effect's runtime
selector column `s` (`s · value = 0`), exactly the `AccumulatorInsertEmit.bindGateI` discipline —
ACTIVE on the firing row (`s = 1`), vacuous on padding. -/
def hidingZeroBody (sel : Option Nat) (valueCol : Nat) : EmittedExpr :=
  match sel with
  | none   => .var valueCol
  | some s => .mul (.var s) (.var valueCol)

/-- The HIDING appendix: the per-row pin plus its LAST-ROW re-lowering (a `.gate` rides the
`when_transition()` domain, so the wrap row needs the boundary form — the deployed last-row-repair
shape, cf. `ShieldedSpendDescriptor`'s re-lowerings). Both are `.base` constraints: they read no
base column and contribute NO map/mem op, so the appendix is strictly additive. -/
def hidingZeroConstraints (sel : Option Nat) (valueCol : Nat) : List VmConstraint2 :=
  [ .base (.gate (hidingZeroBody sel valueCol))
  , .base (.boundary .last (hidingZeroBody sel valueCol)) ]

/-- **`effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name`** — THE SHIELDED-NOTE APPEND
GROW-GATE: the parametric 8-felt insert-shaped accumulator descriptor (`effAccumInsertV3`, whose
`Satisfied2` forces the spliced-leaf membership in the REBUILT after-tree over the FULL committed
8-felt group) PLUS the hiding-leaf zero pin. `groupCol` is left ABSTRACT: which carrier limb the
shielded root occupies is L1's VK-epoch decision, and this gate is sound for whichever it lands. -/
def effShieldedNoteAppendV3 (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { effAccumInsertV3 groupCol keyCol valueCol sel base name with
    name        := name
    constraints := (effAccumInsertV3 groupCol keyCol valueCol sel base name).constraints
                     ++ hidingZeroConstraints sel valueCol }

/-- **BYTE-SAFETY, stated.** The shielded gate is the insert gate's constraint list with the hiding
appendix APPENDED — `effAccumInsertV3` (and therefore every deployed descriptor it hosts) is
untouched. A structural `rfl`, so the additivity is not a claim but a definitional fact. -/
theorem shieldedAppend_is_additive (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String) :
    (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name).constraints
      = (effAccumInsertV3 groupCol keyCol valueCol sel base name).constraints
          ++ hidingZeroConstraints sel valueCol := rfl

/-- The trace WIDTH is unchanged by the hiding pin (it reads an existing column). -/
theorem shieldedAppend_width (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String) :
    (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name).traceWidth
      = (effAccumInsertV3 groupCol keyCol valueCol sel base name).traceWidth := rfl

/-- Every hiding-appendix constraint is a constraint of the shielded gate. -/
theorem shieldedAppend_appMem (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ hidingZeroConstraints sel valueCol) :
    c ∈ (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name).constraints :=
  List.mem_append_right _ hc

-- Structural pins: the hiding appendix is exactly two `.base` constraints, and it adds NO map/mem op.
#guard (hidingZeroConstraints none 5).length == 2
#guard (hidingZeroConstraints (some 3) 5).length == 2

-- ⚑ TWO-SIDED CANARY on the pin itself (neither vacuous nor a DoS): an honest hiding leaf
-- (`value = 0`) makes the body VANISH; a smuggled cleartext value (`value = 7`) does NOT.
#guard decide ((hidingZeroBody none 5).eval (fun c => if c = 5 then 0 else 3) = 0)
#guard decide (¬ ((hidingZeroBody none 5).eval (fun c => if c = 5 then 7 else 3) = 0))
-- ... and the selector-gated form: ACTIVE row (`s = 1`) bites, padding row (`s = 0`) is vacuous.
#guard decide (¬ ((hidingZeroBody (some 3) 5).eval
  (fun c => if c = 3 then 1 else if c = 5 then 7 else 0) = 0))
#guard decide ((hidingZeroBody (some 3) 5).eval
  (fun c => if c = 3 then 0 else if c = 5 then 7 else 0) = 0)

/-! ## §1 — `Satisfied2` FORCES the hiding leaf (the trace-level tooth). -/

/-- Canonical-cell exactness at zero: a cell that is `≡ 0 [ZMOD p]` and canonical IS `0` over ℤ. -/
private theorem canonical_zero {x : ℤ} (hx : 0 ≤ x ∧ x < 2013265921)
    (h : x ≡ 0 [ZMOD 2013265921]) : x = 0 := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- A `Satisfied2` of the shielded gate STRIPS to a `Satisfied2` of the underlying insert gate: the
hiding appendix is all `.base`, reads no base column, and contributes no map/mem op. -/
theorem shieldedAppend_strips_to_insert (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (hash : List ℤ → ℤ) (base : EffectVmDescriptor2) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
           minit mfin maddrs t) :
    Satisfied2 hash (effAccumInsertV3 groupCol keyCol valueCol sel base name) minit mfin maddrs t := by
  have hmapOps :
      Dregg2.Circuit.DescriptorIR2.mapOpsOf
          (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
        = Dregg2.Circuit.DescriptorIR2.mapOpsOf
            (effAccumInsertV3 groupCol keyCol valueCol sel base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effShieldedNoteAppendV3, hidingZeroConstraints,
      List.filterMap_append]
  have hmemOps :
      Dregg2.Circuit.DescriptorIR2.memOpsOf
          (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
        = Dregg2.Circuit.DescriptorIR2.memOpsOf
            (effAccumInsertV3 groupCol keyCol valueCol sel base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effShieldedNoteAppendV3, hidingZeroConstraints,
      List.filterMap_append]
  have hmemLog :
      Dregg2.Circuit.DescriptorIR2.memLog
          (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name) t
        = Dregg2.Circuit.DescriptorIR2.memLog
            (effAccumInsertV3 groupCol keyCol valueCol sel base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog :
      Dregg2.Circuit.DescriptorIR2.mapLog
          (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name) t
        = Dregg2.Circuit.DescriptorIR2.mapLog
            (effAccumInsertV3 groupCol keyCol valueCol sel base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effAccumInsertV3 groupCol keyCol valueCol sel base name).constraints
                     ++ hidingZeroConstraints sel valueCol
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- **⚑ THE HIDING TOOTH (`shieldedAppend_forces_hiding_leaf`).** A satisfying shielded-gate trace
FORCES the accumulator leaf's VALUE column to `0` on every active (non-last) row where the pin is
armed. The committed shielded leaf is `(fold(commitment), 0)` — there is NO cleartext value column
for a prover to fill. This is the in-AIR realization of `shielded_note_set.rs`'s
`accumulator_leaf`. -/
theorem shieldedAppend_forces_hiding_leaf (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (hash : List ℤ → ℤ) (base : EffectVmDescriptor2) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
              minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1) :
    (envAt t i).loc valueCol = 0 := by
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hin : VmConstraint2.base (.gate (hidingZeroBody sel valueCol))
      ∈ hidingZeroConstraints sel valueCol := List.mem_cons_self
  have h := hsat.rowConstraints i hi _
    (shieldedAppend_appMem groupCol keyCol valueCol sel base name _ hin)
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, hlastf] at h
  cases hs : sel with
  | none =>
    have h0 : (envAt t i).loc valueCol ≡ 0 [ZMOD 2013265921] := by
      simpa [hidingZeroBody, hs, EmittedExpr.eval] using h
    exact canonical_zero (hcells valueCol) h0
  | some s =>
    have hs1 : (envAt t i).loc s = 1 := hsel s hs
    have hmul : (envAt t i).loc s * (envAt t i).loc valueCol ≡ 0 [ZMOD 2013265921] := by
      simpa [hidingZeroBody, hs, EmittedExpr.eval] using h
    rw [hs1, one_mul] at hmul
    exact canonical_zero (hcells valueCol) hmul

/-- **REJECTION TOOTH #1 — A CLEARTEXT VALUE IN THE SHIELDED LEAF IS UNSAT.** A trace whose leaf
value column is anything but `0` on an armed active row does NOT satisfy the shielded gate. The
value-carrying leaf shape the three cleartext families use is UNREPRESENTABLE here — which is
exactly why the shielded set cannot reuse `note_commitments` (DESIGN §3 R2, rejected). -/
theorem cleartext_value_in_shielded_leaf_unsat (groupCol : Nat → Fin 8 → Nat)
    (keyCol valueCol : Nat) (sel : Option Nat) (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1)
    (hleak : (envAt t i).loc valueCol ≠ 0) :
    ¬ Satisfied2 hash (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
        minit mfin maddrs t :=
  fun hsat => hleak (shieldedAppend_forces_hiding_leaf groupCol keyCol valueCol sel hash base name
    minit mfin maddrs t hsat i hi hnotlast hcells hsel)

#assert_axioms canonical_zero
#assert_axioms shieldedAppend_is_additive
#assert_axioms shieldedAppend_strips_to_insert
#assert_axioms shieldedAppend_forces_hiding_leaf
#assert_axioms cleartext_value_in_shielded_leaf_unsat

/-! ## §2 — `shieldedAppends8`: the faithful 8-felt SHIELDED append, and its soundness. -/

/-- **`shieldedAppends8 S8 beforeRoot key afterRoot`** — the faithful 8-felt shielded-note append:
`accumInserts8` at the HIDING value `0`. Unfolded: the BEFORE root commits a sorted spine, the
commitment `key` is ABSENT from BEFORE (no duplicate), the hiding leaf `(key, 0)` is a MEMBER of
AFTER, and the AFTER root commits `sortedInsert key spine`. Over the FULL committed 8-felt
BEFORE/AFTER root groups (~124-bit), never lane-0. -/
def shieldedAppends8 (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ) (afterRoot : Digest8) :
    Prop :=
  accumInserts8 S8 beforeRoot key 0 afterRoot

/-- **⚑ SOUNDNESS (a) — GROWTH BY EXACTLY THE APPENDED COMMITMENT.** The AFTER committed key set is
EXACTLY the BEFORE set plus the appended commitment key: nothing else appears, nothing disappears.
This is the whole grow-gate claim at the set level (`update_sound8`). -/
theorem shieldedAppends8_growth (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) :=
  accumInserts8_setGrows S8 beforeRoot key 0 afterRoot h

/-- **SOUNDNESS (b) — NO PRIOR LEAF IS DROPPED.** Every key committed in BEFORE is still committed
in AFTER. A grow-gate that silently pruned a prior shielded note would be a censorship channel. -/
theorem shieldedAppends8_preserves_prior (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    ∀ y ∈ keysOf8 S8 beforeRoot, y ∈ keysOf8 S8 afterRoot :=
  fun y hy => (shieldedAppends8_growth S8 beforeRoot key afterRoot h y).mpr (Or.inr hy)

/-- **SOUNDNESS (c) — NOTHING ELSE IS APPENDED.** Every key committed in AFTER is either the single
appended commitment or was already committed in BEFORE. -/
theorem shieldedAppends8_no_extra (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    ∀ y ∈ keysOf8 S8 afterRoot, y = key ∨ y ∈ keysOf8 S8 beforeRoot :=
  fun y hy => (shieldedAppends8_growth S8 beforeRoot key afterRoot h y).mp hy

/-- **SOUNDNESS (d) — NO DUPLICATE.** The appended commitment was genuinely ABSENT from BEFORE: this
is a FRESH-key append, not a silent overwrite of an existing shielded note. The in-AIR twin of
`ShieldedNoteSet::insert`'s `DuplicateShieldedNote` rejection. -/
theorem shieldedAppends8_fresh (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    key ∉ keysOf8 S8 beforeRoot :=
  accumInserts8_fresh S8 beforeRoot key 0 afterRoot h

/-- **SOUNDNESS (e) — THE APPENDED LEAF IS HIDING.** The leaf that is a member of the AFTER tree is
`(key, 0)`: the folded commitment with a ZERO value column. The value lives inside the commitment,
never as a committed leaf field. -/
theorem shieldedAppends8_leaf_is_hiding (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    MembersAt8 S8 afterRoot (key, 0) :=
  accumInserts8_value_present S8 beforeRoot key 0 afterRoot h

/-- **SOUNDNESS (f) — THE APPENDED COMMITMENT IS COMMITTED AFTER.** The appended key is a member of
the AFTER committed key set — the fact `piCOMMITTED` must be able to certify. -/
theorem shieldedAppends8_key_committed_after (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (h : shieldedAppends8 S8 beforeRoot key afterRoot) :
    key ∈ keysOf8 S8 afterRoot :=
  (shieldedAppends8_growth S8 beforeRoot key afterRoot h key).mpr (Or.inl rfl)

/-! ### §2b — the REJECTION TEETH at the relation level (each non-vacuous: it refutes a concrete
forged transition, and §6 exhibits an HONEST transition that satisfies). -/

/-- **REJECTION TOOTH #2 — A DUPLICATE APPEND IS UNSAT.** Re-appending a shielded commitment already
committed in BEFORE admits NO shielded append relation. (Deployed twin: `ShieldedNoteSet::insert`
returns `DuplicateShieldedNote`; here it is unrepresentable in-AIR.) -/
theorem duplicate_shielded_append_unsat (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (hdup : key ∈ keysOf8 S8 beforeRoot) :
    ¬ shieldedAppends8 S8 beforeRoot key afterRoot :=
  fun h => shieldedAppends8_fresh S8 beforeRoot key afterRoot h hdup

/-- **REJECTION TOOTH #3 — DROPPING A PRIOR LEAF IS UNSAT.** A claimed transition whose AFTER root
omits a key committed in BEFORE admits NO shielded append relation: the accumulator is GROW-ONLY. -/
theorem dropped_prior_leaf_unsat (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (y : ℤ) (hy : y ∈ keysOf8 S8 beforeRoot)
    (hdrop : y ∉ keysOf8 S8 afterRoot) :
    ¬ shieldedAppends8 S8 beforeRoot key afterRoot :=
  fun h => hdrop (shieldedAppends8_preserves_prior S8 beforeRoot key afterRoot h y hy)

/-- **REJECTION TOOTH #4 — A FORGED AFTER-ROOT THAT OMITS THE APPEND IS UNSAT.** If the claimed
AFTER root does not commit the appended commitment, there is no append relation to be had — the
published root cannot be decoupled from the leaf it is supposed to have absorbed. -/
theorem forged_after_root_unsat (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (afterRoot : Digest8) (hmiss : key ∉ keysOf8 S8 afterRoot) :
    ¬ shieldedAppends8 S8 beforeRoot key afterRoot :=
  fun h => hmiss (shieldedAppends8_key_committed_after S8 beforeRoot key afterRoot h)

/-- **⚑ REJECTION TOOTH #5 — A FROZEN ROOT IS UNSAT, UNCONDITIONALLY.** Republishing the BEFORE root
as the AFTER root (the "append that moved nothing" — the forgery a node would use to accept a
shielded output without committing it) admits NO shielded append relation, for ANY scheme, root and
commitment. No hypothesis at all: the appended key must be present after and absent before, and one
root cannot do both. -/
theorem frozen_after_root_unsat (S8 : Heap8Scheme) (root : Digest8) (key : ℤ) :
    ¬ shieldedAppends8 S8 root key root :=
  fun h => shieldedAppends8_fresh S8 root key root h
    (shieldedAppends8_key_committed_after S8 root key root h)

#assert_axioms shieldedAppends8_growth
#assert_axioms shieldedAppends8_preserves_prior
#assert_axioms shieldedAppends8_no_extra
#assert_axioms shieldedAppends8_fresh
#assert_axioms shieldedAppends8_leaf_is_hiding
#assert_axioms shieldedAppends8_key_committed_after
#assert_axioms duplicate_shielded_append_unsat
#assert_axioms dropped_prior_leaf_unsat
#assert_axioms forged_after_root_unsat
#assert_axioms frozen_after_root_unsat

/-! ## §3 — THE DESCRIPTOR-LEVEL KEYSTONE: `Satisfied2` FORCES the shielded append. -/

/-- **⚑⚑ THE L2 KEYSTONE (`shieldedNoteAppend_forces_grow8`).** A `Satisfied2` of the shielded
grow-gate, on an active row, together with the WIDE chip soundness and the realizable non-membership
bracket + spine bindings, FORCES the faithful 8-felt shielded append `shieldedAppends8` over the FULL
committed BEFORE/AFTER root groups: the AFTER tree is the BEFORE tree PLUS EXACTLY the appended
hiding leaf `(key, 0)` — no prior leaf dropped, nothing else appended, no duplicate, and the leaf's
value column TRACE-FORCED to `0` (not assumed).

The `0` is the load-bearing difference from the three cleartext families: they instantiate
`effAccumInsertV3` with a value column carrying `split_u64(value).0`; here that column is pinned. -/
theorem shieldedNoteAppend_forces_grow8 (S8 : Heap8Scheme)
    (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat) (sel : Option Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
              minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k)) spine)
    (g : GapOpen8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))
           ((envAt t i).loc keyCol))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) k))
                (sortedInsert ((envAt t i).loc keyCol) spine)) :
    shieldedAppends8 S8
      (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))
      ((envAt t i).loc keyCol)
      (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) k)) := by
  have hzero : (envAt t i).loc valueCol = 0 :=
    shieldedAppend_forces_hiding_leaf groupCol keyCol valueCol sel hash base name
      minit mfin maddrs t hsat i hi hnotlast hcells hsel
  have hins := effAccumInsertV3_forces_write8 S8 groupCol keyCol valueCol sel base name
    hash minit mfin maddrs t hChip
    (shieldedAppend_strips_to_insert groupCol keyCol valueCol sel hash base name
      minit mfin maddrs t hsat)
    i hi hnotlast hcells hsel spine hbefore g hcov hafter
  show accumInserts8 S8 _ _ 0 _
  rwa [hzero] at hins

/-- **THE HEADLINE CONSEQUENCE, in one shot.** From a satisfying shielded-gate trace plus the
realizable carriers: the AFTER committed shielded-note key set is EXACTLY the BEFORE set plus the
appended commitment. This is the statement that makes `ShieldedNoteSet::root8()` a trustworthy
`piCOMMITTED` source: a node cannot publish a root that contains a note nobody appended, nor drop
one that was. -/
theorem shieldedNoteAppend_forces_growth (S8 : Heap8Scheme)
    (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat) (sel : Option Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effShieldedNoteAppendV3 groupCol keyCol valueCol sel base name)
              minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k)) spine)
    (g : GapOpen8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))
           ((envAt t i).loc keyCol))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) k))
                (sortedInsert ((envAt t i).loc keyCol) spine)) :
    ∀ y, y ∈ keysOf8 S8 (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + B_SPAN) k))
      ↔ (y = (envAt t i).loc keyCol
          ∨ y ∈ keysOf8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))) :=
  shieldedAppends8_growth S8 _ _ _
    (shieldedNoteAppend_forces_grow8 S8 groupCol keyCol valueCol sel base name hash minit mfin
      maddrs t hChip hsat i hi hnotlast hcells hsel spine hbefore g hcov hafter)

#assert_axioms shieldedNoteAppend_forces_grow8
#assert_axioms shieldedNoteAppend_forces_growth

/-! ## §4 — COMPOSING THE LANDED Wide8 INSERT LEMMAS (`SortedTreeInsertWide8`).

`SortedTreeNonMembershipHeap8.{SpineCommits8, keysOf8, update_sound8}` — which `accumInserts8` and
§2 ride — are the `K := ℤ` shadow of `SortedTreeInsertWide8`'s `[LinearOrder K]`-GENERIC
`SpineCommitsW` / `keysOfW` / `update_soundW` wrapper. This section makes the shadow EXPLICIT (so the
shielded growth is literally an instance of the landed generic keystone, not a parallel re-proof)
and carries the sortedness-preservation corollary. It also fixes, as a definitional fact, that the
deployed ℤ splice `sortedInsert` IS the generic `sortedInsertW` — the bridge the key-widening
follow-up (`K := Digest8Key`) will ride when the ~31-bit `fold_bytes32_to_bb` sort key is retired. -/

/-- The deployed ℤ sorted splice IS the `[LinearOrder K]`-generic one at `K := ℤ` — proved, not
asserted, so the key-widening path is a genuine instantiation of the SAME splice. -/
theorem sortedInsert_eq_sortedInsertW (k : ℤ) :
    ∀ xs : List ℤ, sortedInsert k xs = sortedInsertW k xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x t ih =>
    unfold sortedInsert sortedInsertW
    by_cases hlt : k < x
    · simp [hlt]
    · by_cases hkx : k = x
      · simp [hkx]
      · simp [hlt, hkx, ih]

/-- `SpineCommits8` IS `SpineCommitsW` at the deployed heap opening (`MembersAt8`), `K := ℤ`,
`V := ℤ`, `Root := Digest8`. The bridge that lets the shielded family consume the landed generic
Wide8 insert keystone directly. -/
theorem spineCommits8_toW (S8 : Heap8Scheme) (root : Digest8) (spine : List ℤ)
    (h : SpineCommits8 S8 root spine) :
    SpineCommitsW (V := ℤ) (MembersAt8 S8) root spine :=
  { sorted := h.sorted, present_iff := h.present_iff }

/-- The committed key sets coincide: `keysOf8` is `keysOfW` at the deployed opening. -/
theorem keysOf8_eq_keysOfW (S8 : Heap8Scheme) (root : Digest8) :
    keysOf8 S8 root = keysOfW (V := ℤ) (MembersAt8 S8) root := rfl

/-- **⚑ THE SHIELDED GROWTH, THROUGH THE LANDED GENERIC Wide8 KEYSTONE.** The shielded append's
set-growth is exactly `SortedTreeInsertWide8.update_soundW` instantiated at the deployed heap
opening — no re-proof of tree combinatorics, the generic insert wrapper does the work. -/
theorem shielded_growth_via_wide8 (S8 : Heap8Scheme) (beforeRoot afterRoot : Digest8) (key : ℤ)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine)
    (hfresh : key ∉ keysOf8 S8 beforeRoot)
    (hafter : SpineCommits8 S8 afterRoot (sortedInsertW key spine)) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) :=
  update_soundW (V := ℤ) (MembersAt8 S8) beforeRoot afterRoot key spine
    (spineCommits8_toW S8 beforeRoot spine hbefore) hfresh
    (spineCommits8_toW S8 afterRoot _ hafter)

/-- **SORTEDNESS PRESERVED (Wide8).** The spine the shielded append commits stays strictly
increasing, so the accumulator remains a sorted tree the next open/append can ride —
`update_preserves_sortedW`, instantiated. -/
theorem shielded_after_spine_sorted (S8 : Heap8Scheme) (beforeRoot : Digest8) (key : ℤ)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine) (hfresh : key ∉ spine) :
    Sorted (sortedInsertW key spine) :=
  update_preserves_sortedW (V := ℤ) (MembersAt8 S8) beforeRoot key spine
    (spineCommits8_toW S8 beforeRoot spine hbefore) hfresh

#assert_axioms sortedInsert_eq_sortedInsertW
#assert_axioms spineCommits8_toW
#assert_axioms keysOf8_eq_keysOfW
#assert_axioms shielded_growth_via_wide8
#assert_axioms shielded_after_spine_sorted

/-! ## §5 — THE PHYSICAL APPEND FACE: AAFI at the DEPLOYED depth and the HIDING value.

§2-§4 gate the SORTED-COMPACTED spine — which is exactly what `ShieldedNoteSet::root8()` is (a
`BTreeMap` folded through `CanonicalHeapTree8`, order-independent). The AAFI `seq` column L0
persists is the ORDER-DEPENDENT replay layer (`iter_in_append_order` / `aafi_leaves` /
`aafi_next_free_index`); its in-AIR gate is the landed depth-generic two-path AAFI law, which this
section INSTANTIATES at `dep := HEAP_TREE_DEPTH` and the hiding value `0`. This is where "appended
at the NEXT AAFI free index, with no prior leaf rewritten and none dropped" becomes a theorem: the
committed digest vector changes at EXACTLY TWO positions and every other slot is untouched. -/

section Aafi

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (perfectRoot HEAP_TREE_DEPTH)
open Dregg2.Circuit.MapOpsColumnLayout (aafiLeafHash AafiGatesAt aafiInsert_forces_imtInsert)
open Dregg2.Circuit.IndexedMerkleTree
  (ImtLeaf ImtSorted ImtAbsent imtInsert imtAddrs imtLeafHash PreRootModelsChain
   imtAbsent_excludes mem_imtAddrs_imtInsert aafiGates_force_imtAbsent_layout
   aafiGates_force_sortedKeys_layout)

/-- **`ShieldedAafiGatesAt`** — the deployed AAFI append gate for the SHIELDED note set: the landed
depth-generic `AafiGatesAt` at the deployed heap depth (`HEAP_TREE_DEPTH = 16`, the depth
`shielded_note_set.rs::root8` builds at) and the HIDING leaf value `0`. The appended leaf is
`hash[cm, 0, low.next]` — the folded commitment, a ZERO value column, and the IMT pointer. -/
def ShieldedAafiGatesAt (hash : List ℤ → ℤ)
    (oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ) : Prop :=
  AafiGatesAt hash HEAP_TREE_DEPTH oldRoot newRoot cm 0 lowAddr lowValue lowNext freeEmpty

/-- **⚑ THE PHYSICAL APPEND LAW, INSTANTIATED (`shieldedAafi_forces_two_point_append`).** Under the
named `Poseidon2SpongeCR` floor, an accepting shielded AAFI row FORCES its `(before, after)` roots to
be a two-point update of ONE committed digest vector: the low leaf's pointer relinked to the new
commitment, and the HIDING leaf `hash[cm, 0, low.next]` written at a DISTINCT FREE slot that was
EMPTY. The pointer bracket `low.addr < cm < low.next` survives — the freshness witness. Pure
instantiation of the landed `aafiInsert_forces_imtInsert`; no new tree combinatorics. -/
theorem shieldedAafi_forces_two_point_append (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : ShieldedAafiGatesAt hash oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty) :
    ∃ (xs : List ℤ) (p1 p2 : Nat),
      xs.length = 2 ^ HEAP_TREE_DEPTH ∧
      p1 ≠ p2 ∧
      oldRoot = perfectRoot hash HEAP_TREE_DEPTH xs ∧
      xs[p1]? = some (aafiLeafHash hash lowAddr lowValue lowNext) ∧
      (xs.set p1 (aafiLeafHash hash lowAddr lowValue cm))[p2]? = some freeEmpty ∧
      newRoot = perfectRoot hash HEAP_TREE_DEPTH
        ((xs.set p1 (aafiLeafHash hash lowAddr lowValue cm)).set p2
          (aafiLeafHash hash cm 0 lowNext)) ∧
      lowAddr < cm ∧ cm < lowNext :=
  aafiInsert_forces_imtInsert hash hCR HEAP_TREE_DEPTH hg

/-- **⚑ NO PRIOR LEAF IS REWRITTEN OR DROPPED (`shieldedAafi_prior_slots_untouched`).** Every slot
of the committed digest vector other than the two the append touches is BYTE-IDENTICAL before and
after. A shielded append cannot rewrite, relink, or delete any previously committed note leaf while
keeping the published root. This is the append-at-free-index (no-shift) guarantee, stated on the
actual committed vector. -/
theorem shieldedAafi_prior_slots_untouched (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : ShieldedAafiGatesAt hash oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty) :
    ∃ (xs : List ℤ) (p1 p2 : Nat),
      xs.length = 2 ^ HEAP_TREE_DEPTH ∧
      p1 ≠ p2 ∧
      oldRoot = perfectRoot hash HEAP_TREE_DEPTH xs ∧
      newRoot = perfectRoot hash HEAP_TREE_DEPTH
        ((xs.set p1 (aafiLeafHash hash lowAddr lowValue cm)).set p2
          (aafiLeafHash hash cm 0 lowNext)) ∧
      (∀ q : Nat, q ≠ p1 → q ≠ p2 →
        ((xs.set p1 (aafiLeafHash hash lowAddr lowValue cm)).set p2
          (aafiLeafHash hash cm 0 lowNext))[q]? = xs[q]?) ∧
      lowAddr < cm ∧ cm < lowNext := by
  obtain ⟨xs, p1, p2, hlen, hne, hor, hmem1, hmem2, hnew, hlk, hkn⟩ :=
    shieldedAafi_forces_two_point_append hash hCR hg
  refine ⟨xs, p1, p2, hlen, hne, hor, hnew, ?_, hlk, hkn⟩
  intro q hq1 hq2
  rw [List.getElem?_set_ne (Ne.symm hq2), List.getElem?_set_ne (Ne.symm hq1)]

/-- **THE DUPLICATE-APPEND TOOTH AT THE PHYSICAL LEVEL.** With the low-leaf membership discharged
from the NAMED `PreRootModelsChain` layout faithfulness, an accepting shielded AAFI row forces the
appended commitment to be POINTER-BRACKET ABSENT from the committed sorted chain — and on a sorted
chain a bracket-absent key is genuinely not in the address spine (`imtAbsent_excludes`). So a
shielded commitment already in the tree admits NO accepting append row. -/
theorem shieldedAafi_forces_fresh_commitment (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (pad : ℤ) {c : List ImtLeaf} {oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ}
    (hs : ImtSorted c)
    (hg : ShieldedAafiGatesAt hash oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad HEAP_TREE_DEPTH c oldRoot) :
    cm ∉ imtAddrs c :=
  imtAbsent_excludes hs
    (aafiGates_force_imtAbsent_layout hash hCR HEAP_TREE_DEPTH pad hg hpad hcorr)

/-- **THE CHAIN INVARIANT IS PRESERVED.** An accepting shielded append keeps the committed chain
sorted (and its felt projection `Heap.SortedKeys`), so the accumulator can absorb the next append —
the liveness half of the grow-gate. Instantiation of `aafiGates_force_sortedKeys_layout`. -/
theorem shieldedAafi_preserves_sorted_chain (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (pad : ℤ) {c : List ImtLeaf} {oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ}
    (hs : ImtSorted c)
    (hg : ShieldedAafiGatesAt hash oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad HEAP_TREE_DEPTH c oldRoot) :
    ImtSorted (imtInsert c cm 0)
      ∧ Dregg2.Substrate.Heap.SortedKeys (Dregg2.Circuit.IndexedMerkleTree.imtToHeap
          (imtInsert c cm 0)) :=
  aafiGates_force_sortedKeys_layout hash hCR HEAP_TREE_DEPTH pad hs hg hpad hcorr

/-- **THE CHAIN GROWS BY EXACTLY THE APPENDED COMMITMENT.** At the linked-chain level too, the
address spine after the append is precisely the spine before plus `cm`. The chain twin of
`shieldedAppends8_growth`. -/
theorem shieldedAafi_chain_growth (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (pad : ℤ) {c : List ImtLeaf} {oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : ShieldedAafiGatesAt hash oldRoot newRoot cm lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad HEAP_TREE_DEPTH c oldRoot) :
    ∀ x, x ∈ imtAddrs (imtInsert c cm 0) ↔ x = cm ∨ x ∈ imtAddrs c :=
  mem_imtAddrs_imtInsert
    (aafiGates_force_imtAbsent_layout hash hCR HEAP_TREE_DEPTH pad hg hpad hcorr)

#assert_axioms shieldedAafi_forces_two_point_append
#assert_axioms shieldedAafi_prior_slots_untouched
#assert_axioms shieldedAafi_forces_fresh_commitment
#assert_axioms shieldedAafi_preserves_sorted_chain
#assert_axioms shieldedAafi_chain_growth

end Aafi

/-! ## §6 — COMPLETENESS / NON-VACUITY: an HONEST shielded append SATISFIES (not a DoS).

The rejection teeth above are only worth something if the honest transition is admissible. This
section exhibits a concrete shielded append — three folded commitment keys, a HIDING opening
predicate (only zero-valued leaves ever open), a real BEFORE root, a real AFTER root — and shows the
grow-gate FIRES: the fresh commitment is absent before and present after (strict growth), every
prior commitment survives, the grown spine is exactly the sorted splice, and the appended leaf's
value column is `0`. Mirrors `SortedTreeInsertWide8`'s wrapper-level non-vacuity demo. -/

section Completeness

/-- Three folded shielded-note commitment keys (`fold_bytes32_to_bb` images), strictly increasing. -/
def cmLo : ℤ := 11
/-- The FRESH commitment this turn appends — bracketed strictly between the two committed ones. -/
def cmNew : ℤ := 42
/-- The largest already-committed commitment key. -/
def cmHi : ℤ := 77

/-- The committed shielded spine BEFORE the turn: two hiding notes. -/
def demoBeforeSpine : List ℤ := [cmLo, cmHi]

/-- The demo opening predicate over a `Bool`-indexed root (`false` = BEFORE, `true` = AFTER). It is
HIDING BY CONSTRUCTION: a leaf opens only if its VALUE COLUMN IS ZERO and its key is in that root's
committed spine. No value-carrying leaf is ever a member — the accumulator-level shape of the in-AIR
pin `hidingZeroBody`. -/
def demoOpens : Bool → ℤ × ℤ → Prop :=
  fun r e => e.2 = 0 ∧ (if r then e.1 ∈ sortedInsertW cmNew demoBeforeSpine
                        else e.1 ∈ demoBeforeSpine)

theorem demoBeforeSpine_sorted : Sorted demoBeforeSpine := by
  show List.Pairwise (· < ·) demoBeforeSpine
  decide

/-- The grown spine is EXACTLY `[cmLo, cmNew, cmHi]` — the fresh commitment splices into its
bracket, prior entries verbatim and in order. -/
theorem demo_after_spine_eq : sortedInsertW cmNew demoBeforeSpine = [cmLo, cmNew, cmHi] := by decide

theorem demo_after_spine_sorted : Sorted (sortedInsertW cmNew demoBeforeSpine) := by
  rw [demo_after_spine_eq]
  show List.Pairwise (· < ·) [cmLo, cmNew, cmHi]
  decide

/-- The BEFORE root commits the sorted two-note spine. -/
theorem demoOpens_before_spine : SpineCommitsW (V := ℤ) demoOpens false demoBeforeSpine :=
  { sorted := demoBeforeSpine_sorted
    present_iff := fun k =>
      ⟨fun ⟨_e, he, hz, hmem⟩ => he ▸ (by simpa [SortedTreeNonMembershipWide8.keyOfW] using hmem),
       fun hk => ⟨(k, 0), rfl, rfl, by simpa using hk⟩⟩ }

/-- The AFTER root commits the GROWN spine. -/
theorem demoOpens_after_spine :
    SpineCommitsW (V := ℤ) demoOpens true (sortedInsertW cmNew demoBeforeSpine) :=
  { sorted := demo_after_spine_sorted
    present_iff := fun k =>
      ⟨fun ⟨_e, he, hz, hmem⟩ => he ▸ (by simpa [SortedTreeNonMembershipWide8.keyOfW] using hmem),
       fun hk => ⟨(k, 0), rfl, rfl, by simpa using hk⟩⟩ }

/-- The fresh commitment is genuinely ABSENT from the BEFORE committed key set. -/
theorem demoOpens_fresh : cmNew ∉ keysOfW (V := ℤ) demoOpens false := by
  rintro ⟨e, he, _hz, hmem⟩
  simp only [if_neg Bool.false_ne_true] at hmem
  have hk : e.1 = cmNew := he
  rw [hk] at hmem
  exact absurd hmem (by decide)

/-- **★ COMPLETENESS — THE HONEST APPEND FIRES.** The committed shielded key set after the turn is
EXACTLY the set before plus the appended commitment. The gate ADMITS the honest transition; it is
not a denial-of-service dressed as a soundness gate. -/
theorem demo_shielded_append_grows :
    ∀ y, y ∈ keysOfW (V := ℤ) demoOpens true
      ↔ (y = cmNew ∨ y ∈ keysOfW (V := ℤ) demoOpens false) :=
  update_soundW (V := ℤ) demoOpens false true cmNew demoBeforeSpine
    demoOpens_before_spine demoOpens_fresh demoOpens_after_spine

/-- **★ STRICT GROWTH.** The append is not a no-op: the commitment is PRESENT after and ABSENT
before. A satisfying honest transition genuinely MOVES the committed root. -/
theorem demo_strict_growth :
    cmNew ∈ keysOfW (V := ℤ) demoOpens true ∧ cmNew ∉ keysOfW (V := ℤ) demoOpens false :=
  ⟨(demo_shielded_append_grows cmNew).mpr (Or.inl rfl), demoOpens_fresh⟩

/-- **★ PRIOR NOTES SURVIVE.** Both already-committed shielded notes are still committed after. -/
theorem demo_prior_notes_preserved :
    cmLo ∈ keysOfW (V := ℤ) demoOpens true ∧ cmHi ∈ keysOfW (V := ℤ) demoOpens true := by
  constructor
  · exact (demo_shielded_append_grows cmLo).mpr (Or.inr ⟨(cmLo, 0), rfl, rfl, by decide⟩)
  · exact (demo_shielded_append_grows cmHi).mpr (Or.inr ⟨(cmHi, 0), rfl, rfl, by decide⟩)

/-- **★ THE HIDING DISCIPLINE HOLDS IN THE WITNESS.** Every leaf that opens against the AFTER root —
including the newly appended one — carries a ZERO value column. The committed shielded tree reveals
no note value. -/
theorem demo_every_member_is_hiding : ∀ e : ℤ × ℤ, demoOpens true e → e.2 = 0 :=
  fun _e h => h.1

/-- **★ THE APPENDED LEAF IS THE HIDING LEAF.** `(cmNew, 0)` — the `HeapLeaf::entry(fold(cm), 0)`
shape `shielded_note_set.rs::accumulator_leaf` builds — genuinely opens against the AFTER root. -/
theorem demo_appended_leaf_opens : demoOpens true (cmNew, 0) := by
  refine ⟨rfl, ?_⟩
  rw [demo_after_spine_eq]
  decide

/-- **★ A VALUE-CARRYING LEAF NEVER OPENS.** The same commitment key with a NON-ZERO value column is
NOT a member of the committed shielded tree — the hiding discipline is a genuine exclusion, not a
convention. -/
theorem demo_value_carrying_leaf_excluded : ¬ demoOpens true (cmNew, 5) := by
  rintro ⟨hz, -⟩
  exact absurd hz (by decide)

#assert_axioms demoBeforeSpine_sorted
#assert_axioms demo_after_spine_eq
#assert_axioms demoOpens_before_spine
#assert_axioms demoOpens_after_spine
#assert_axioms demoOpens_fresh
#assert_axioms demo_shielded_append_grows
#assert_axioms demo_strict_growth
#assert_axioms demo_prior_notes_preserved
#assert_axioms demo_every_member_is_hiding
#assert_axioms demo_appended_leaf_opens
#assert_axioms demo_value_carrying_leaf_excluded

end Completeness

end Dregg2.Circuit.Emit.ShieldedNoteAppendDescriptor
