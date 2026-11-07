/-
# ExactNullifierAafiRotatedStateRefine

Independent refinement layer for the additive exact-AAFI rotated-state descriptor.  The emitter
module fixes geometry and proves local gate extraction.  This module gives the state16 lookup bus
an execution meaning and assembles those local facts into one adversarial trace theorem: the two
public wide commitments open rotated states whose nullifier lanes are the circuit-computed FNS3
checkpoints, while every other payload cell is preserved.

No descriptor artifact or verifier key is emitted here.
-/

import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
import Dregg2.Circuit.Emit.EffectVmRotationWideCommitIff
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
open Dregg2.Circuit.ExactNullifierAafiPlan (RawValue Root8)

set_option autoImplicit false

/-! ## 1. State16 rows have a genuine execution meaning -/

/-- One planned state16 site is genuinely executed by `perm16` on assignment `a`. -/
def State16StepHolds (perm16 : List ℤ → List ℤ) (a : Assignment)
    (step : State16Step) : Prop :=
  step.outputCols.map a = perm16 (step.input.map (·.eval a))

/-- Every incremental state16 step is present in the welded descriptor. -/
theorem v3State16Lookup_mem {step : State16Step} (hstep : step ∈ v3PermutationSteps) :
    v3State16Lookup step ∈ exactNullifierAafiRotatedStateDescriptor.constraints := by
  have hv3 : v3State16Lookup step ∈ v3State16Lookups :=
    List.mem_map.mpr ⟨step, hstep, rfl⟩
  simp only [exactNullifierAafiRotatedStateDescriptor, exactRotatedStateConstraints,
    exactAafiConstraints, List.mem_append]
  tauto

/-- A satisfying descriptor trace plus a sound state16 table forces every one of the 78
incremental permutation sites to be a genuine complete-state transition. -/
theorem satisfying_state16_step
    (perm16 : List ℤ → List ℤ) (scalarHash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (hchip : ChipTableSoundState16 perm16 (t.tf poseidon2state16))
    (hsat : Satisfied2 scalarHash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) (step : State16Step)
    (hstep : step ∈ v3PermutationSteps) :
    State16StepHolds perm16 (envAt t row).loc step := by
  have hc := hsat.rowConstraints row hrow _ (v3State16Lookup_mem hstep)
  simp only [v3State16Lookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  exact chip_lookup_sound_state16 perm16 (t.tf poseidon2state16) hchip
    (envAt t row).loc step.input step.outputCols
    (by
      have hall : v3PermutationSteps.all (fun s => s.input.length == 16) = true := by
        decide
      have hs := List.all_eq_true.mp hall step hstep
      have h16 : step.input.length = 16 := by simpa using of_decide_eq_true hs
      exact h16)
    hc

/-! ## 2. The two FNS3 plans, as an explicit reusable refinement boundary -/

/-- The state16 meaning of an emitted FNS3 plan.  This is deliberately a relation over the exact
five emitted steps rather than an assumed hash oracle: all five equalities are extracted from the
lookup table by `satisfying_fns3_plans` below. -/
def Fns3PlanExecution (perm16 : List ℤ → List ℤ) (a : Assignment)
    (chain countBase stateBase : Nat) : Prop :=
  ∀ step ∈ spongePlan stateBase (stateCommitPreimage chain countBase),
    State16StepHolds perm16 a step

theorem preStateCommitPlan_subset_v3 :
    ∀ step ∈ preStateCommitPlan, step ∈ v3PermutationSteps := by
  intro step hstep
  exact List.mem_append_left _ (List.mem_append_right _ hstep)

theorem postStateCommitPlan_subset_v3 :
    ∀ step ∈ postStateCommitPlan, step ∈ v3PermutationSteps := by
  intro step hstep
  exact List.mem_append_right _ hstep

/-- Both five-step FNS3 executions are forced on every row of every satisfying trace. -/
theorem satisfying_fns3_plans
    (perm16 : List ℤ → List ℤ) (scalarHash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (hchip : ChipTableSoundState16 perm16 (t.tf poseidon2state16))
    (hsat : Satisfied2 scalarHash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length) :
    Fns3PlanExecution perm16 (envAt t row).loc 0 PRE_COUNT_BASE PRE_STATE_COMMIT_BASE ∧
      Fns3PlanExecution perm16 (envAt t row).loc 3 POST_COUNT_BASE POST_STATE_COMMIT_BASE := by
  constructor
  · intro step hstep
    exact satisfying_state16_step perm16 scalarHash minit mfin maddrs t hchip hsat row hrow
      step (preStateCommitPlan_subset_v3 step hstep)
  · intro step hstep
    exact satisfying_state16_step perm16 scalarHash minit mfin maddrs t hchip hsat row hrow
      step (postStateCommitPlan_subset_v3 step hstep)

/-! ## 3. Honest state16 table construction (the non-vacuity core builder) -/

/-- Genuine state16 chip rows required by the incremental plan on one main-trace row. -/
def state16TableOf (perm16 : List ℤ → List ℤ) (a : Assignment) : Table :=
  v3PermutationSteps.map fun step => chipRowState16 perm16 (step.input.map (·.eval a))

/-- The prover-built table is semantically sound whenever the permutation returns sixteen lanes
on the sixteen-lane states used by the plan.  This is the reusable honest-table core: it does not
obtain membership by copying forged output columns into the table. -/
theorem state16TableOf_sound (perm16 : List ℤ → List ℤ) (a : Assignment)
    (hout : ∀ step ∈ v3PermutationSteps,
      (perm16 (step.input.map (·.eval a))).length = CHIP_STATE_LANES) :
    ChipTableSoundState16 perm16 (state16TableOf perm16 a) := by
  intro r hr
  simp only [state16TableOf, List.mem_map] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  refine ⟨step.input.map (·.eval a), ?_, hout step hstep, rfl⟩
  have hall : v3PermutationSteps.all (fun s => s.input.length == 16) = true := by
    decide
  have hs := List.all_eq_true.mp hall step hstep
  have h16 : step.input.length = 16 := by simpa using of_decide_eq_true hs
  simpa using (h16.trans rfl : step.input.length = CHIP_STATE_LANES)

/-- If the row's state columns contain the actual permutation outputs, every incremental lookup
hits the genuine table built above.  This is the lookup half of an honest descriptor witness. -/
theorem state16_lookup_holds_of_execution (perm16 : List ℤ → List ℤ) (a : Assignment)
    (step : State16Step) (hstep : step ∈ v3PermutationSteps)
    (hexec : State16StepHolds perm16 a step) :
    (chipLookupTupleState16 step.input step.outputCols step.width).map (·.eval a) ∈
      state16TableOf perm16 a := by
  unfold state16TableOf
  rw [List.mem_map]
  refine ⟨step, hstep, ?_⟩
  -- ⚠ do NOT unfold `padTo`/`padToE`: `map_eval_padToE` carries the emitted block straight onto
  -- the tabulated one, and `padTo` is `take`-shaped now, so unfolding leaves a `List.take` to
  -- re-align across.
  simp only [chipLookupTupleState16, chipLookupTupleN, chipRowState16, chipRowN,
    map_eval_padToE, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, EmittedExpr.eval, List.length_map]
  rw [hexec]

/-! ### A concrete non-empty FNS3 execution

The full 3,760-column witness also contains the note opening, four linked-leaf paths, lex bracket,
count/radix arithmetic, and two sixty-site outer commitments.  To keep the state16 closure
independent, the following tiny descriptor isolates precisely the five pre-FNS3 lookups.  Its
witness is generated by executing the KAT-locked Lean Poseidon2 permutation step by step.  Thus the
lookup satisfiability result below is non-vacuous and chip-sound; it is not a table made by copying
arbitrary claimed output columns.
-/

/-- Canonical Int-facing wrapper around the deployed Lean Poseidon2-w16 permutation.  `ofFn`
exposes exactly the sixteen circuit lanes and makes the bus-width theorem definitional. -/
def deployedPerm16 (xs : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin 16 =>
    Int.ofNat ((Dregg2.Circuit.Poseidon2BabyBearW16.perm (xs.map fieldNat)).getD i.val 0)

@[simp] theorem deployedPerm16_length (xs : List ℤ) :
    (deployedPerm16 xs).length = CHIP_STATE_LANES := by
  simp only [deployedPerm16, List.length_ofFn, CHIP_STATE_LANES, CHIP_RATE]

/-- Write a complete output-state block into an assignment. -/
def writeState (a : Assignment) (cols : List Nat) (vals : List ℤ) : Assignment :=
  (cols.zip vals).foldl (fun acc cv => Function.update acc cv.1 cv.2) a

/-- Execute one planned bus site and materialize its genuine output columns. -/
def solveState16Step (perm16 : List ℤ → List ℤ) (a : Assignment)
    (step : State16Step) : Assignment :=
  writeState a step.outputCols (perm16 (step.input.map (·.eval a)))

/-- Topological honest solver for a list of state16 sites. -/
def solveState16Plan (perm16 : List ℤ → List ℤ) (a : Assignment)
    (steps : List State16Step) : Assignment :=
  steps.foldl (solveState16Step perm16) a

/-- A concrete, canonical prior accumulator opening: the exact empty-leaf digest as root and
cursor/count one.  The five FNS3 states themselves are then produced, not supplied. -/
def concretePreFns3Seed : Assignment := fun col =>
  if _h : col ∈ exactNodeDigestCols 0 then
    Int.ofNat (exactEmptyDigestNat.getD ((exactNodeDigestCols 0).idxOf col) 0)
  else if col = PRE_COUNT_BASE then 1
  else 0

def concretePreFns3Row : Assignment :=
  solveState16Plan deployedPerm16 concretePreFns3Seed preStateCommitPlan

/-- Boolean form of a complete finite plan execution, convenient for driven concrete witnesses. -/
def state16PlanChecks (perm16 : List ℤ → List ℤ) (a : Assignment)
    (steps : List State16Step) : Bool :=
  steps.all fun step =>
    decide (step.outputCols.map a = perm16 (step.input.map (·.eval a)))

theorem state16PlanChecks_sound (perm16 : List ℤ → List ℤ) (a : Assignment)
    (steps : List State16Step) (h : state16PlanChecks perm16 a steps = true) :
    ∀ step ∈ steps, State16StepHolds perm16 a step := by
  intro step hstep
  change step.outputCols.map a = perm16 (step.input.map (·.eval a))
  exact of_decide_eq_true (List.all_eq_true.mp h step hstep)

/-- The concrete row really executes all five FNS3 sites under the deployed permutation.  This is
a kernel-decided theorem over 80 output lanes; corrupting any generated lane makes it fail. -/
theorem concretePreFns3Row_executes :
    Fns3PlanExecution deployedPerm16 concretePreFns3Row
      0 PRE_COUNT_BASE PRE_STATE_COMMIT_BASE := by
  apply state16PlanChecks_sound deployedPerm16 concretePreFns3Row preStateCommitPlan
  set_option maxRecDepth 32768 in
    set_option maxHeartbeats 0 in
      decide

/-- The five-lookup descriptor used only for the independent non-vacuity witness. -/
def preFns3OnlyDescriptor : EffectVmDescriptor2 :=
  { name := "exact-aafi::pre-fns3-state16-nonvacuity"
  , traceWidth := PRE_STATE_COMMIT_BASE + 5 * 16
  , piCount := 0
  , tables := [mainTableDef (PRE_STATE_COMMIT_BASE + 5 * 16), poseidon2State16ChipTableDef]
  , constraints := preStateCommitPlan.map v3State16Lookup
  , hashSites := []
  , ranges := [] }

def concretePreFns3Trace : VmTrace where
  rows := [concretePreFns3Row]
  pub := zeroAsg
  tf := fun tid =>
    if tid = poseidon2state16 then state16TableOf deployedPerm16 concretePreFns3Row else []

@[simp] theorem concretePreFns3Trace_rows_ne : concretePreFns3Trace.rows ≠ [] := by
  simp [concretePreFns3Trace]

private theorem preFns3_mem_v3 {step : State16Step} (h : step ∈ preStateCommitPlan) :
    step ∈ v3PermutationSteps := preStateCommitPlan_subset_v3 step h

@[simp] theorem preFns3Only_memOps_empty : memOpsOf preFns3OnlyDescriptor = [] := by
  simp [memOpsOf, preFns3OnlyDescriptor, v3State16Lookup]

@[simp] theorem preFns3Only_mapOps_empty : mapOpsOf preFns3OnlyDescriptor = [] := by
  simp [mapOpsOf, preFns3OnlyDescriptor, v3State16Lookup]

@[simp] theorem preFns3Only_memLog_empty (t : VmTrace) :
    memLog preFns3OnlyDescriptor t = [] := by
  simp [memLog]

@[simp] theorem preFns3Only_mapLog_empty (t : VmTrace) :
    mapLog preFns3OnlyDescriptor t = [] := by
  simp [mapLog]

/-- **Concrete non-vacuity.** A non-empty main trace, with a sound table of genuine Poseidon2
rows, satisfies all five FNS3 lookups.  This is the reusable state16 witness core needed by the
full rotated descriptor; the named remainder is exactly the non-state16 arithmetic/path/wide-row
fill, not an assumed hash step. -/
theorem satisfied2_preFns3_concrete (scalarHash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 scalarHash preFns3OnlyDescriptor minit mfin [] concretePreFns3Trace where
  rowConstraints := by
    intro i hi c hc
    have hi0 : i = 0 := by
      simpa [concretePreFns3Trace] using hi
    subst i
    simp only [preFns3OnlyDescriptor, List.mem_map] at hc
    obtain ⟨step, hstep, rfl⟩ := hc
    change (chipLookupTupleState16 step.input step.outputCols step.width).map
      (·.eval concretePreFns3Row) ∈
        (if poseidon2state16 = poseidon2state16 then
          state16TableOf deployedPerm16 concretePreFns3Row else [])
    rw [if_pos rfl]
    apply state16_lookup_holds_of_execution deployedPerm16 concretePreFns3Row step
      (preFns3_mem_v3 hstep)
    exact concretePreFns3Row_executes step hstep
  rowHashes := by
    intro i hi
    trivial
  rowRanges := by
    intro i hi r hr
    simp [preFns3OnlyDescriptor] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    simp at hop
  memDisciplined := by
    rw [preFns3Only_memLog_empty]
    trivial
  memBalanced := by
    simpa using memCheck_nil minit mfin
  memTableFaithful := by
    rw [preFns3Only_memLog_empty, List.map_nil]
    show (if TableId.memory = poseidon2state16 then
      state16TableOf deployedPerm16 concretePreFns3Row else []) = []
    rw [if_neg]
    simp [poseidon2state16]
  mapTableFaithful := by
    rw [preFns3Only_mapLog_empty]
    show (if TableId.mapOps = poseidon2state16 then
      state16TableOf deployedPerm16 concretePreFns3Row else []) = []
    rw [if_neg]
    simp [poseidon2state16]

/-- The isolated genuine FNS3 circuit is jointly satisfiable by a NON-EMPTY trace. -/
theorem preFns3_genuinely_nonvacuous (scalarHash : List ℤ → ℤ) :
    ∃ t : VmTrace, t.rows ≠ [] ∧
      Satisfied2 scalarHash preFns3OnlyDescriptor (fun _ => 0) (fun _ => (0, 0)) [] t :=
  ⟨concretePreFns3Trace, concretePreFns3Trace_rows_ne,
    satisfied2_preFns3_concrete scalarHash (fun _ => 0) (fun _ => (0, 0))⟩

/-- The still-independent full-descriptor witness obligation.  Unlike a prose TODO this is an
executable interface: it asks only for the row arithmetic/path/wide constraints left after the ten
FNS3 sites, whose honest state16 solver and genuine table are supplied above. -/
def FullRotatedWitnessResidual (perm16 : List ℤ → List ℤ) (t : VmTrace) : Prop :=
  t.rows ≠ [] ∧
  (∀ row < t.rows.length, ∀ step ∈ v3PermutationSteps,
    State16StepHolds perm16 (envAt t row).loc step) ∧
  (∀ row < t.rows.length, ∀ c ∈ exactNullifierAafiRotatedStateDescriptor.constraints,
    (match c with | .lookup l => l.table ≠ poseidon2state16 | _ => True) →
      c.holdsAt (fun _ => 0) t.tf (envAt t row)
        (row == 0) (row + 1 == t.rows.length))

/-! ## 4. Adversarial public-boundary apex -/

/-- What a verifier learns at a particular last row, without pretending either permutation is
globally injective.  `preFns3`/`postFns3` are the exact five-step state16 executions; the two
published octets are the genuine wide commitments; every one of the 177 stable cells agrees.
The payload/FNS3 equations are field equations because AIR constraints live in BabyBear. -/
structure ExactRotatedBoundaryOpening (perm16 permW : List ℤ → List ℤ)
    (t : VmTrace) (row : Nat) : Prop where
  preFns3 : Fns3PlanExecution perm16 (envAt t row).loc 0 PRE_COUNT_BASE PRE_STATE_COMMIT_BASE
  postFns3 : Fns3PlanExecution perm16 (envAt t row).loc 3 POST_COUNT_BASE POST_STATE_COMMIT_BASE
  preNullifierWeld : ∀ i : Fin 8,
    (envAt t row).loc (preStateCommitDigestCols.getD i.val 0) ≡
      (envAt t row).loc (BEFORE_BLOCK_BASE + layoutGroupCol .nullifier i)
        [ZMOD 2013265921]
  postNullifierWeld : ∀ i : Fin 8,
    (envAt t row).loc (postStateCommitDigestCols.getD i.val 0) ≡
      (envAt t row).loc (AFTER_BLOCK_BASE + layoutGroupCol .nullifier i)
        [ZMOD 2013265921]
  stable177 : ∀ off ∈ stableFrameOffsets,
    (envAt t row).loc (AFTER_BLOCK_BASE + off) ≡
      (envAt t row).loc (BEFORE_BLOCK_BASE + off) [ZMOD 2013265921]
  beforeWide : carrierVals BEFORE_CARRIER_BASE wideCommitCarrier (envAt t row).loc =
    wireCommitR8 permW (preLimbsWide BEFORE_BLOCK_BASE (envAt t row).loc)
      ((envAt t row).loc (BEFORE_BLOCK_BASE + B_IROOT))
  afterWide : carrierVals AFTER_CARRIER_BASE wideCommitCarrier (envAt t row).loc =
    wireCommitR8 permW (preLimbsWide AFTER_BLOCK_BASE (envAt t row).loc)
      ((envAt t row).loc (AFTER_BLOCK_BASE + B_IROOT))
  piBefore : ∀ k, (hk : k < 8) →
    (envAt t row).loc ((carrierCols BEFORE_CARRIER_BASE wideCommitCarrier).getD k 0) ≡
      (envAt t row).pub (PI_BEFORE_ROTATED_COMMIT_BASE + k) [ZMOD 2013265921]
  piAfter : ∀ k, (hk : k < 8) →
    (envAt t row).loc ((carrierCols AFTER_CARRIER_BASE wideCommitCarrier).getD k 0) ≡
      (envAt t row).pub (PI_AFTER_ROTATED_COMMIT_BASE + k) [ZMOD 2013265921]

/-- **Adversarial soundness/extraction apex.** Any satisfying trace with genuine state16 and wide
chip tables forces the complete FNS3/rotated-state/public-input boundary.  In particular, PI60..75
cannot name independently chosen digests: they publish the two wide commits computed from payloads
whose nullifier lanes are the circuit's pre/post state-commit executions, and all 177 remaining
payload cells are unchanged. -/
theorem satisfying_exact_rotated_boundary
    (perm16 permW : List ℤ → List ℤ) (scalarHash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (hstate16 : ChipTableSoundState16 perm16 (t.tf poseidon2state16))
    (hwide : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 scalarHash exactNullifierAafiRotatedStateDescriptor minit mfin maddrs t)
    (row : Nat) (hrow : row < t.rows.length)
    (hfirst : (row == 0) = true) (hlast : (row + 1 == t.rows.length) = true) :
    ExactRotatedBoundaryOpening perm16 permW t row := by
  obtain ⟨hpre, hpost⟩ := satisfying_fns3_plans perm16 scalarHash minit mfin maddrs t
    hstate16 hsat row hrow
  have hweld := satisfying_last_row_welds_fns3 scalarHash minit mfin
    maddrs t hsat row hrow hlast
  obtain ⟨hbeforeWide, hafterWide⟩ := satisfying_row_computes_wide_state_commits permW
    scalarHash minit mfin maddrs t hwide hsat row hrow
  obtain ⟨hpiBefore, hpiAfter⟩ := satisfying_row_publishes_wide_state_commits scalarHash
    minit mfin maddrs t hsat row hrow
  exact
    { preFns3 := hpre
    , postFns3 := hpost
    , preNullifierWeld := fun i => (hweld i).1
    , postNullifierWeld := fun i => (hweld i).2
    , stable177 := fun off hoff =>
        satisfying_last_row_preserves_stable_frame scalarHash minit mfin maddrs t hsat row off
          hrow hlast hoff
    , beforeWide := hbeforeWide
    , afterWide := hafterWide
    , piBefore := hpiBefore hfirst
    , piAfter := hpiAfter hlast }

#assert_axioms satisfying_state16_step
#assert_axioms satisfying_fns3_plans
#assert_axioms state16TableOf_sound
#assert_axioms state16_lookup_holds_of_execution
#assert_axioms concretePreFns3Row_executes
#assert_axioms satisfied2_preFns3_concrete
#assert_axioms preFns3_genuinely_nonvacuous
#assert_axioms satisfying_exact_rotated_boundary

end Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateRefine
