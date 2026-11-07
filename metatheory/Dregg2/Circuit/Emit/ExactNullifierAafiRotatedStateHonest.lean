/-
# ExactNullifierAafiRotatedStateHonest

The first concrete slice of the remaining full exact-AAFI witness: a sixteen-row arithmetic
envelope for the full-domain tagged insert

  BOT < REAL(ffff..ffff) < TOP,     count 1 -> 2,     append slot 1.

It simultaneously exercises the endpoint dispatch, both 16-limb lex gadgets, cursor-to-base4-path
quotient, exact count increment, bit gates, count continuity, fixed depth, and genuine 16-bit range
tables.  State16 sponges and the outer rotated-wide carriers remain independent solver layers.
-/

import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateRefine
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHonest

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv sbCol saCol)
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateRefine

set_option autoImplicit false

/-! ## 1. Exact arithmetic slice -/

/-- The raw-nullifier range rows are included explicitly: the witness reaches the top u16 value in
all sixteen lanes, rather than demonstrating only an endpoint-sized key. -/
def fullRawRangePlan : List RangePlan := u16Ranges NULLIFIER_RAW_BASE 16

def arithmeticRangePlan : List RangePlan := incrementalRangePlan ++ fullRawRangePlan

def arithmeticRangeConstraints : List VmConstraint2 := arithmeticRangePlan.map rangeLookup

def arithmeticGateConstraints : List VmConstraint2 :=
  positionConstraintsV3 ++ taggedEndpointConstraints ++ bracketConstraints ++
    radixCarryConstraints ++ cursorRadixConstraints ++ countIncrementConstraints ++
    countContinuityConstraints ++ depthConstraints

def arithmeticConstraints : List VmConstraint2 :=
  arithmeticRangeConstraints ++ arithmeticGateConstraints

def arithmeticDescriptor : EffectVmDescriptor2 :=
  { name := "exact-aafi::full-domain-insert-arithmetic-nonvacuity"
  , traceWidth := V3_TRACE_WIDTH
  , piCount := 0
  , tables := [mainTableDef V3_TRACE_WIDTH, rangeTable 16]
  , constraints := arithmeticConstraints
  , hashSites := []
  , ranges := [] }

#guard fullRawRangePlan.length == 16
#guard arithmeticRangePlan.length == 64
#guard arithmeticGateConstraints.length == 136
#guard arithmeticConstraints.length == 200
#guard arithmeticRangePlan.all fun r => r.bits == 16

/-! ## 2. Driven 16-row full-domain assignment -/

/-- Row `level` of the concrete insert.  The predecessor is canonical BOT, its successor canonical
TOP, and the inserted raw key is the maximum 256-bit value represented faithfully as sixteen
u16 limbs.  Both endpoint-dispatched lex gadgets therefore compare `0 < [1,0,..]`; selector lane
zero is the unique selector and delta is zero.

The authenticated cursor starts at one.  Its first radix-four digit is one (`APP_POS_B0 = 1`) and
the quotient is zero from row one upward; every remaining append-path digit is zero. -/
def arithmeticRow (level col : Nat) : ℤ :=
  if NULLIFIER_RAW_BASE ≤ col ∧ col < NULLIFIER_RAW_BASE + 16 then 65535
  else if col = LEVEL_COL then Int.ofNat level
  else if col = LOW_ADDR_TAG then 0
  else if col = LOW_NEXT_TAG then 2
  else if col = PRE_COUNT_BASE then 1
  else if col = POST_COUNT_BASE then 2
  else if col = CURSOR_Q_LO ∧ level = 0 then 1
  else if col = APP_POS_B0 ∧ level = 0 then 1
  else if col = LEX_LOW_KEY_AUX_BASE then 1
  else if col = LEX_KEY_NEXT_AUX_BASE then 1
  else 0

def arithmeticRows : List Assignment :=
  (List.range TREE_DEPTH).map arithmeticRow

/-- Both custom range identities are kept explicit.  This slice uses only the exact u16 table. -/
def arithmeticTf : TraceFamily := fun tid =>
  if tid = rangeTid 16 then rangeRows 16 else []

def arithmeticTrace : VmTrace where
  rows := arithmeticRows
  pub := zeroAsg
  tf := arithmeticTf

@[simp] theorem arithmeticRows_length : arithmeticRows.length = TREE_DEPTH := by
  simp [arithmeticRows]

@[simp] theorem arithmeticTrace_rows_ne : arithmeticTrace.rows ≠ [] := by
  simp [arithmeticTrace, arithmeticRows, TREE_DEPTH]

theorem arithmeticTrace_range16 : arithmeticTrace.tf (rangeTid 16) = rangeRows 16 := by
  simp [arithmeticTrace, arithmeticTf]

/-- Concrete full-domain tooth: every raw key limb on every main row is exactly `0xffff`. -/
theorem raw_key_is_all_ff (level lane : Nat) (hlevel : level < TREE_DEPTH) (hlane : lane < 16) :
    (arithmeticTrace.rows.getD level zeroAsg) (NULLIFIER_RAW_BASE + lane) = 65535 := by
  have hget : arithmeticTrace.rows.getD level zeroAsg = arithmeticRow level := by
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa [arithmeticTrace, arithmeticRows] using hlevel)]
    simp [arithmeticTrace, arithmeticRows, Option.getD]
  rw [hget]
  unfold arithmeticRow
  rw [if_pos (by omega)]

/-! ## 3. Kernel-decided gate family and faithful range membership -/

/-- Computable denotation for exactly the arithmetic constraint constructors used in this slice.
The general `VmConstraint2.holdsAt` also has map reconciliation arms and is intentionally not
globally decidable; matching first keeps this checker kernel-executable. -/
def arithmeticConstraintCheck (env : VmRowEnv) (isFirst isLast : Bool) :
    VmConstraint2 → Bool
  | .base (.gate body) =>
      if isLast then true else decide (body.eval env.loc ≡ 0 [ZMOD 2013265921])
  | .base (.transition hi lo) =>
      if isLast then true else decide (env.nxt (sbCol hi) ≡ env.loc (saCol lo) [ZMOD 2013265921])
  | .base (.boundary .first body) =>
      if isFirst then decide (body.eval env.loc ≡ 0 [ZMOD 2013265921]) else true
  | .base (.boundary .last body) =>
      if isLast then decide (body.eval env.loc ≡ 0 [ZMOD 2013265921]) else true
  | .base (.piBinding .first col pi) =>
      if isFirst then decide (env.loc col ≡ env.pub pi [ZMOD 2013265921]) else true
  | .base (.piBinding .last col pi) =>
      if isLast then decide (env.loc col ≡ env.pub pi [ZMOD 2013265921]) else true
  | .windowGate ⟨body, true⟩ =>
      if isLast then true else decide (body.eval env ≡ 0 [ZMOD 2013265921])
  | .windowGate ⟨body, false⟩ => decide (body.eval env ≡ 0 [ZMOD 2013265921])
  | _ => false

theorem arithmeticConstraintCheck_sound (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (c : VmConstraint2) (h : arithmeticConstraintCheck env isFirst isLast c = true) :
    c.holdsAt (fun _ => 0) tf env isFirst isLast := by
  cases c with
  | base v =>
      cases v with
      | gate body =>
          cases isLast <;>
            simpa [arithmeticConstraintCheck, VmConstraint2.holdsAt,
              Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] using h
      | transition hi lo =>
          cases isLast <;>
            simpa [arithmeticConstraintCheck, VmConstraint2.holdsAt,
              Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] using h
      | boundary row body =>
          cases row <;> cases isFirst <;> cases isLast <;>
            simpa [arithmeticConstraintCheck, VmConstraint2.holdsAt,
              Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] using h
      | piBinding row col pi =>
          cases row <;> cases isFirst <;> cases isLast <;>
            simpa [arithmeticConstraintCheck, VmConstraint2.holdsAt,
              Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] using h
  | windowGate w =>
      rcases w with ⟨body, onTransition⟩
      cases onTransition <;> cases isLast <;>
        simpa [arithmeticConstraintCheck, VmConstraint2.holdsAt, WindowConstraint.holdsAt]
          using h
  -- ⚑ The challenge gate falls through `arithmeticConstraintCheck`'s `_ => false` arm: this
  -- checker predates the kind and does NOT decide it, so a chal-gate-bearing descriptor is
  -- REFUSED here rather than silently accepted. `simp … at h` closes the goal from `false = true`.
  | chalGate w => simp [arithmeticConstraintCheck] at h
  | lookup l => simp [arithmeticConstraintCheck] at h
  | memOp m => simp [arithmeticConstraintCheck] at h
  | mapOp m => simp [arithmeticConstraintCheck] at h
  | umemOp m => simp [arithmeticConstraintCheck] at h
  | proofBind p => simp [arithmeticConstraintCheck] at h

/-- Finite checker for every non-lookup arithmetic constraint on every one of the sixteen rows. -/
def arithmeticGateChecks : Bool :=
  (List.range TREE_DEPTH).all fun row =>
    arithmeticGateConstraints.all fun c =>
      arithmeticConstraintCheck (envAt arithmeticTrace row)
        (row == 0) (row + 1 == arithmeticTrace.rows.length) c

theorem arithmeticGateChecks_true : arithmeticGateChecks = true := by
  set_option maxRecDepth 131072 in
    set_option maxHeartbeats 0 in
      decide

theorem arithmetic_gates_hold (row : Nat) (hrow : row < arithmeticTrace.rows.length)
    (c : VmConstraint2) (hc : c ∈ arithmeticGateConstraints) :
    c.holdsAt (fun _ => 0) arithmeticTrace.tf (envAt arithmeticTrace row)
      (row == 0) (row + 1 == arithmeticTrace.rows.length) := by
  have hlevel : row ∈ List.range TREE_DEPTH := by
    rw [List.mem_range]
    simpa [arithmeticTrace] using hrow
  have hcheck :=
    List.all_eq_true.mp (List.all_eq_true.mp arithmeticGateChecks_true row hlevel) c hc
  have hsound := arithmeticConstraintCheck_sound arithmeticTrace.tf (envAt arithmeticTrace row)
    (row == 0) (row + 1 == arithmeticTrace.rows.length) c hcheck
  simpa only using hsound

/-- Finite checker for the value side of every genuine u16 range lookup on every row. -/
def arithmeticRangeChecks : Bool :=
  (List.range TREE_DEPTH).all fun row =>
    arithmeticRangePlan.all fun r =>
      decide (0 ≤ arithmeticRow row r.col ∧ arithmeticRow row r.col < (2 : ℤ) ^ r.bits)

theorem arithmeticRangeChecks_true : arithmeticRangeChecks = true := by
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide

theorem arithmetic_range_bound (row : Nat) (hrow : row < TREE_DEPTH)
    (r : RangePlan) (hr : r ∈ arithmeticRangePlan) :
    0 ≤ arithmeticRow row r.col ∧ arithmeticRow row r.col < (2 : ℤ) ^ r.bits := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      (List.all_eq_true.mp arithmeticRangeChecks_true row (List.mem_range.mpr hrow)) r hr)

theorem arithmetic_range_bits (r : RangePlan) (hr : r ∈ arithmeticRangePlan) : r.bits = 16 := by
  have hall : arithmeticRangePlan.all (fun q => q.bits == 16) = true := by decide
  simpa using of_decide_eq_true (List.all_eq_true.mp hall r hr)

theorem arithmetic_range_lookup_holds (row : Nat) (hrow : row < TREE_DEPTH)
    (r : RangePlan) (hr : r ∈ arithmeticRangePlan) :
    (rangeLookup r).holdsAt (fun _ => 0) arithmeticTrace.tf (envAt arithmeticTrace row)
      (row == 0) (row + 1 == arithmeticTrace.rows.length) := by
  have hloc : (envAt arithmeticTrace row).loc = arithmeticRow row := by
    rw [show (envAt arithmeticTrace row).loc = arithmeticTrace.rows.getD row zeroAsg from rfl]
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa [arithmeticTrace, arithmeticRows] using hrow)]
    simp [arithmeticTrace, arithmeticRows, Option.getD]
  have hbits := arithmetic_range_bits r hr
  change [(envAt arithmeticTrace row).loc r.col] ∈ arithmeticTrace.tf (rangeTid r.bits)
  rw [hloc, hbits, arithmeticTrace_range16]
  have hb := arithmetic_range_bound row hrow r hr
  rw [hbits] at hb
  exact (range_row_mem_iff _ _).2 hb

/-! ## 4. Non-empty `Satisfied2` for the whole arithmetic envelope -/

@[simp] theorem arithmetic_memOps_empty : memOpsOf arithmeticDescriptor = [] := by
  rfl

@[simp] theorem arithmetic_mapOps_empty : mapOpsOf arithmeticDescriptor = [] := by
  rfl

@[simp] theorem arithmetic_memLog_empty (t : VmTrace) : memLog arithmeticDescriptor t = [] := by
  simp [memLog]

@[simp] theorem arithmetic_mapLog_empty (t : VmTrace) : mapLog arithmeticDescriptor t = [] := by
  simp [mapLog]

/-- A genuine sixteen-row `Satisfied2` witness for the full-domain tagged arithmetic transition.
The range table is definitionally the complete `[0,2^16)` table, not a membership-only table made
from the witness values. -/
theorem satisfied2_arithmetic_full_domain :
    Satisfied2 (fun _ => 0) arithmeticDescriptor (fun _ => 0) (fun _ => (0, 0)) []
      arithmeticTrace where
  rowConstraints := by
    intro row hrow c hc
    have hlevel : row < TREE_DEPTH := by simpa [arithmeticTrace] using hrow
    simp only [arithmeticDescriptor, arithmeticConstraints, List.mem_append] at hc
    rcases hc with hrange | hgate
    · simp only [arithmeticRangeConstraints, List.mem_map] at hrange
      obtain ⟨r, hr, rfl⟩ := hrange
      exact arithmetic_range_lookup_holds row hlevel r hr
    · exact arithmetic_gates_hold row hrow c hgate
  rowHashes := by intro row hrow; trivial
  rowRanges := by intro row hrow r hr; simp [arithmeticDescriptor] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; simp at hop
  memDisciplined := by rw [arithmetic_memLog_empty]; trivial
  memBalanced := by simpa using memCheck_nil (fun _ => 0) (fun _ => (0, 0))
  memTableFaithful := by
    rw [arithmetic_memLog_empty, List.map_nil]
    simp [arithmeticTrace, arithmeticTf, rangeTid, RANGE_W_TID_BASE]
  mapTableFaithful := by
    rw [arithmetic_mapLog_empty]
    simp [arithmeticTrace, arithmeticTf, rangeTid, RANGE_W_TID_BASE]

theorem arithmetic_full_domain_genuinely_nonvacuous :
    ∃ t : VmTrace, t.rows.length = TREE_DEPTH ∧ t.rows ≠ [] ∧
      Satisfied2 (fun _ => 0) arithmeticDescriptor (fun _ => 0) (fun _ => (0, 0)) [] t :=
  ⟨arithmeticTrace, by simp [arithmeticTrace], arithmeticTrace_rows_ne,
    satisfied2_arithmetic_full_domain⟩

/-! ## 5. Smaller exact residual after the two concrete solver layers -/

/-- What remains after composing this module's arithmetic witness with the state16/FNS3 solver:
the note-opening pack, the four actual leaf/path hashes and roots, the two rotated payload fills,
and the two sixty-site wide chains/public pins.  Every arithmetic/count/path-position column is now
fixed by `arithmeticRow`; every state16 output is produced by `solveState16Plan`. -/
def HonestHashAndWideResidual (t : VmTrace) : Prop :=
  t.rows.length = TREE_DEPTH ∧
  (∀ row < TREE_DEPTH, ∀ step ∈ allPermutationSteps ++ v3PermutationSteps,
    State16StepHolds deployedPerm16 (envAt t row).loc step) ∧
  (∀ row < TREE_DEPTH, ∀ c ∈
      (firstPackConstraints ++ leafLinkConstraints ++ continuityConstraints ++
       leafLinkConstraintsV3 ++ rootContinuityConstraints ++ middleRootConstraints ++
       successorCarrierContinuity ++ successorCarrierDerived ++ beforePayloadContinuity ++
       stableFrameConstraints ++ fns3WeldConstraints ++ wideStateLookups ++ wideStatePins ++
       retainedCorePins),
    c.holdsAt (fun _ => 0) t.tf (envAt t row)
      (row == 0) (row + 1 == t.rows.length))

#assert_axioms raw_key_is_all_ff
#assert_axioms arithmeticGateChecks_true
#assert_axioms arithmeticRangeChecks_true
#assert_axioms satisfied2_arithmetic_full_domain
#assert_axioms arithmetic_full_domain_genuinely_nonvacuous

end Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHonest
