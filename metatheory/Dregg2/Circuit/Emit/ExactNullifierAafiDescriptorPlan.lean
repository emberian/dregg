/-
# Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan

Lean-authored FNSP-v3 plan for the exact indexed-nullifier successor.  This module turns the
semantic two-path witness in `ExactNullifierAafiPlan` into concrete IR2 geometry:

* three exact linked-leaf sponges (`old low`, `low.next := key`, and appended `key/value/next`);
* four depth-16 4-ary node sponges, sharing the predecessor path in pairs and the append path in
  pairs, with the predecessor-new and append-empty roots forced equal;
* a tagged BOT/REAL/TOP bracket whose REAL arm compares all sixteen raw-u16 nullifier limbs;
* an append position forced from the authenticated count by a limbwise radix-4 quotient chain;
* an exact u64 `postCount = preCount + 1` chain;
* domain-separated state16 commitments to `(root8, count4)` before and after the update.

The descriptor stays additive and is not emitted to Rust here.  It imports the deployed FNSP-v2
plan, retains its first 44 public inputs, and appends exact prior-root/count, successor-count, and
the two accumulator-state commitments.  The old public successor-root carrier is no longer a host
oracle: it is carried through all rows and forced equal to the fourth path's derived root.

Capacity policy is explicit.  A PRE count must be below `4^16 = 2^32` (its high two u16 limbs are
zero).  The POST count may equal `2^32`, representing the terminal full tree.  Such a terminal
state cannot be used as another PRE state, so there is no wrap/alias at capacity.
-/

import Dregg2.Circuit.ExactNullifierAafiPlan
import Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
import Dregg2.Circuit.GateExpr
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (TableId VmConstraint2 EffectVmDescriptor2 mainTableDef poseidon2state16
   poseidon2State16ChipTableDef chipLookupTupleState16 emitVmJson2)
open Dregg2.Circuit.ExactNullifierAafiPlan
  (RawNullifierKey RawValue ExactLeaf Root8 PathStep4 Parent4 exactLeafBlock rawValueBlock
   rawValueBlock_injective EXACT_LINKED_LEAF_DOMAIN botKey topKey realKey rawZeroKey rawAllFfKey
   full_raw_domain_between_endpoints zeroValue)
open Dregg2.Circuit.CommitmentTreeWide (hashMany8Real)
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan

set_option autoImplicit false

/-! ## 1. Concrete full-state hash meanings and localized collision carriers -/

def EXACT_NODE_DOMAIN : ℤ := 0x464e4e32   -- `FNN2`
def EXACT_EMPTY_DOMAIN : ℤ := 0x464e4532  -- `FNE2`
def EXACT_STATE_DOMAIN : ℤ := 0x464e5333  -- `FNS3`

#guard decide (EXACT_NODE_DOMAIN != EXACT_LINKED_LEAF_DOMAIN)
#guard decide (EXACT_EMPTY_DOMAIN != EXACT_LINKED_LEAF_DOMAIN)
#guard decide (EXACT_STATE_DOMAIN != EXACT_LINKED_LEAF_DOMAIN)
#guard decide (EXACT_NODE_DOMAIN != EXACT_EMPTY_DOMAIN)
#guard decide (EXACT_NODE_DOMAIN != EXACT_STATE_DOMAIN)
#guard decide (EXACT_EMPTY_DOMAIN != EXACT_STATE_DOMAIN)

/-- Canonical BabyBear representative used by the real state16 schedule.  On every u16/count input
accepted below this is simply `Int.toNat`; the modulus operation only makes the semantic function
total outside the accepted envelope. -/
def fieldNat (x : ℤ) : Nat := (x % (FIELD_MODULUS : ℤ)).toNat

def rootBlock (root : Root8) : List ℤ := List.ofFn root

@[simp] theorem rootBlock_length (root : Root8) : (rootBlock root).length = 8 := by
  rw [rootBlock, List.length_ofFn]
  try rfl

/-- The exact deployed full-state sponge, exposed at all eight squeezed lanes. -/
def fullStateHash8 (inputs : List ℤ) : Root8 :=
  let digest := hashMany8Real (inputs.map fieldNat)
  fun i => (digest.getD i.val 0 : ℤ)

def exactLeafDigestReal (leaf : ExactLeaf) : Root8 :=
  fullStateHash8 (exactLeafBlock leaf)

def siblingIndex0 : Fin (Dregg2.Circuit.ExactNullifierAafiPlan.TREE_ARITY - 1) :=
  ⟨0, by decide⟩
def siblingIndex1 : Fin (Dregg2.Circuit.ExactNullifierAafiPlan.TREE_ARITY - 1) :=
  ⟨1, by decide⟩
def siblingIndex2 : Fin (Dregg2.Circuit.ExactNullifierAafiPlan.TREE_ARITY - 1) :=
  ⟨2, by decide⟩

def exactChildren4 (current : Root8) (step : PathStep4) : List Root8 :=
  match step.position.val with
  | 0 => [current, step.siblings siblingIndex0, step.siblings siblingIndex1,
      step.siblings siblingIndex2]
  | 1 => [step.siblings siblingIndex0, current, step.siblings siblingIndex1,
      step.siblings siblingIndex2]
  | 2 => [step.siblings siblingIndex0, step.siblings siblingIndex1, current,
      step.siblings siblingIndex2]
  | _ => [step.siblings siblingIndex0, step.siblings siblingIndex1,
      step.siblings siblingIndex2, current]

def exactNodeBlock (current : Root8) (step : PathStep4) : List ℤ :=
  [EXACT_NODE_DOMAIN] ++ (exactChildren4 current step).flatMap rootBlock

def exactParent4Real : Parent4 := fun current step =>
  fullStateHash8 (exactNodeBlock current step)

def exactEmptyLeafReal : Root8 := fullStateHash8 [EXACT_EMPTY_DOMAIN]

/-- The accumulator-state commitment authenticates the cursor/count together with its root. -/
def accumulatorStateBlock (root : Root8) (count : RawValue) : List ℤ :=
  ([EXACT_STATE_DOMAIN] ++ rootBlock root) ++ rawValueBlock count

def accumulatorStateCommitReal (root : Root8) (count : RawValue) : Root8 :=
  fullStateHash8 (accumulatorStateBlock root count)

/-- A collision is localized to the actual domain-separated full-state sponge input.  No global
injectivity fiction is introduced. -/
structure FullStateHash8Collision (left right : List ℤ) : Prop where
  inputs_differ : left ≠ right
  digests_equal : fullStateHash8 left = fullStateHash8 right

theorem accumulatorStateBlock_cursor_injective (root : Root8) :
    Function.Injective (accumulatorStateBlock root) := by
  intro a b h
  unfold accumulatorStateBlock at h
  exact rawValueBlock_injective (List.append_right_injective _ h)

theorem accumulatorStateBlock_count_eq_of_eq {leftRoot rightRoot : Root8}
    {leftCount rightCount : RawValue}
    (h : accumulatorStateBlock leftRoot leftCount =
      accumulatorStateBlock rightRoot rightCount) : leftCount = rightCount := by
  apply rawValueBlock_injective
  have hd := congrArg (fun xs : List ℤ => xs.drop 9) h
  simpa [accumulatorStateBlock, List.drop_left' (rootBlock_length leftRoot),
    List.drop_left' (rootBlock_length rightRoot)] using hd

/-- A changed authenticated cursor under an unchanged state commitment is exactly a concrete
full-state sponge collision, not an assumed impossibility. -/
theorem wrong_cursor_commit_forces_collision {root : Root8} {a b : RawValue}
    (hne : a ≠ b) (heq : accumulatorStateCommitReal root a = accumulatorStateCommitReal root b) :
    FullStateHash8Collision (accumulatorStateBlock root a) (accumulatorStateBlock root b) := by
  refine ⟨?_, heq⟩
  exact fun h => hne (accumulatorStateBlock_cursor_injective root h)

/-- Cross-turn form: even if an adversary also substitutes the inner root, two openings of the
same carried FNS3 checkpoint with different counts yield a concrete collision. -/
theorem carried_checkpoint_wrong_count_forces_collision
    {leftRoot rightRoot : Root8} {leftCount rightCount : RawValue}
    (hne : leftCount ≠ rightCount)
    (heq : accumulatorStateCommitReal leftRoot leftCount =
      accumulatorStateCommitReal rightRoot rightCount) :
    FullStateHash8Collision
      (accumulatorStateBlock leftRoot leftCount)
      (accumulatorStateBlock rightRoot rightCount) := by
  refine ⟨?_, heq⟩
  intro hblock
  exact hne (accumulatorStateBlock_count_eq_of_eq hblock)

/-- The exact external weld contract: `priorCommit` is read from signed/committed state and
`successorCommit` is the value written into the next state.  The descriptor computes and publicly
pins both openings; the remaining live integration is to allocate this eight-felt group in the
rotated state/checkpoint rather than treating either PI as caller-selected. -/
structure CommittedAccumulatorTransition where
  priorCommit : Root8
  successorCommit : Root8
  priorRoot : Root8
  successorRoot : Root8
  priorCount : RawValue
  successorCount : RawValue
  prior_opens : priorCommit = accumulatorStateCommitReal priorRoot priorCount
  successor_opens : successorCommit = accumulatorStateCommitReal successorRoot successorCount

/-- Replacing any material predecessor-leaf preimage while retaining its digest is a localized
collision.  `material` names the exact 39-input wire inequality, so no impossible injectivity of
the finite sponge is assumed. -/
theorem wrong_predecessor_digest_forces_collision {old forged : ExactLeaf}
    (material : exactLeafBlock old ≠ exactLeafBlock forged)
    (heq : exactLeafDigestReal old = exactLeafDigestReal forged) :
    FullStateHash8Collision (exactLeafBlock old) (exactLeafBlock forged) :=
  ⟨material, heq⟩

/-- A substituted successor/path node which changes the ordered 33-input node preimage but retains
the root is likewise a concrete collision. -/
theorem wrong_successor_path_forces_collision {cur cur' : Root8} {path path' : PathStep4}
    (material : exactNodeBlock cur path ≠ exactNodeBlock cur' path')
    (heq : exactParent4Real cur path = exactParent4Real cur' path') :
    FullStateHash8Collision (exactNodeBlock cur path) (exactNodeBlock cur' path') :=
  ⟨material, heq⟩

/-! ## 2. Exact capacity policy -/

def TREE_CAPACITY : Nat := 4 ^ 16

def appendCountAccepts (pre post : Nat) : Prop := pre < TREE_CAPACITY ∧ post = pre + 1

theorem count_at_capacity_refused_as_pre (post : Nat) :
    ¬ appendCountAccepts TREE_CAPACITY post := by
  simp [appendCountAccepts]

theorem last_slot_reaches_terminal_full :
    appendCountAccepts (TREE_CAPACITY - 1) TREE_CAPACITY := by
  constructor <;> norm_num [TREE_CAPACITY]

#guard TREE_CAPACITY == 4294967296

/-! The durable mirror uses zero-based spend sequence numbers, while physical slot zero is occupied
forever by the BOT sentinel.  Therefore record `append_seq = s` lives at slot `s+1`; the spend that
creates it proves `preCount = s+1` and `postCount = s+2`. -/

def GENESIS_OCCUPIED_SLOTS : Nat := 1
def physicalSlotOfAppendSeq (seq : Nat) : Nat := seq + GENESIS_OCCUPIED_SLOTS
def preCountForAppendSeq (seq : Nat) : Nat := physicalSlotOfAppendSeq seq
def postCountForAppendSeq (seq : Nat) : Nat := preCountForAppendSeq seq + 1

theorem append_seq_maps_to_physical_slot (seq : Nat) :
    physicalSlotOfAppendSeq seq = seq + 1 := by
  rfl

theorem append_seq_counts (seq : Nat) :
    preCountForAppendSeq seq = seq + 1 ∧ postCountForAppendSeq seq = seq + 2 := by
  simp [preCountForAppendSeq, postCountForAppendSeq, physicalSlotOfAppendSeq,
    GENESIS_OCCUPIED_SLOTS]

theorem last_append_seq_fills_tree :
    physicalSlotOfAppendSeq (TREE_CAPACITY - 2) = TREE_CAPACITY - 1 ∧
      postCountForAppendSeq (TREE_CAPACITY - 2) = TREE_CAPACITY := by
  norm_num [physicalSlotOfAppendSeq, postCountForAppendSeq, preCountForAppendSeq,
    GENESIS_OCCUPIED_SLOTS, TREE_CAPACITY]

/-! ### Canonical logical-empty genesis: BOT sentinel only, never the all-empty root -/

def exactNodeDigestList (children : List Root8) : Root8 :=
  fullStateHash8 ([EXACT_NODE_DOMAIN] ++ children.flatMap rootBlock)

def exactEmptySubtreeRoot : Nat → Root8
  | 0 => exactEmptyLeafReal
  | depth + 1 =>
      let child := exactEmptySubtreeRoot depth
      exactNodeDigestList [child, child, child, child]

def exactGenesisLeaf : ExactLeaf :=
  { addr := botKey, value := zeroValue, nextAddr := topKey }

/-- Root of the physical tree with the permanent BOT leaf at slot zero and every remaining slot
empty.  The recursive left-child shape pins append-order placement, not sorted compaction. -/
def exactGenesisRoot : Nat → Root8
  | 0 => exactLeafDigestReal exactGenesisLeaf
  | depth + 1 =>
      let occupied := exactGenesisRoot depth
      let empty := exactEmptySubtreeRoot depth
      exactNodeDigestList [occupied, empty, empty, empty]

def countZero : RawValue := fun _ => 0
def countOne : RawValue := fun i => if i.val = 0 then 1 else 0

def logicalEmptyAccumulatorRoot : Root8 := exactGenesisRoot 16
def allEmptyAccumulatorRoot : Root8 := exactEmptySubtreeRoot 16
def logicalEmptyAccumulatorCommit : Root8 :=
  accumulatorStateCommitReal logicalEmptyAccumulatorRoot countOne

theorem countOne_ne_countZero : countOne ≠ countZero := by
  intro h
  have h0 := congrFun h ⟨0, by decide⟩
  norm_num [countOne, countZero] at h0

/-- If migration aliases the all-empty/count-zero state to the canonical BOT-only/count-one
genesis commitment, it has produced a concrete full-state sponge collision. -/
theorem all_empty_genesis_alias_forces_collision
    (heq : accumulatorStateCommitReal logicalEmptyAccumulatorRoot countOne =
      accumulatorStateCommitReal allEmptyAccumulatorRoot countZero) :
    FullStateHash8Collision
      (accumulatorStateBlock logicalEmptyAccumulatorRoot countOne)
      (accumulatorStateBlock allEmptyAccumulatorRoot countZero) := by
  refine ⟨?_, heq⟩
  intro hblock
  exact countOne_ne_countZero (accumulatorStateBlock_count_eq_of_eq hblock)

#guard GENESIS_OCCUPIED_SLOTS == 1
#guard (rawValueBlock countOne).length == 4

/-! ### Tagged endpoints and order ABI

BOT and TOP are separate tagged keys with zero payload lanes.  Every raw 256-bit string is wrapped
as REAL, so the all-zero and all-`ff` FNF2 outputs remain ordinary spendable keys.  The descriptor
below enforces precisely this three-way wire representation.

The map order is also a new ABI: numeric little-endian-u16 lane zero is compared first.  It is NOT
Rust `[u8; 32]` derived lexicographic order.  The KAT below is the reversal witness which a runtime
comparator differential must preserve.
-/

theorem all_zero_and_all_ff_are_real_keys :
    (botKey < realKey rawZeroKey ∧ realKey rawZeroKey < topKey) ∧
      (botKey < realKey rawAllFfKey ∧ realKey rawAllFfKey < topKey) :=
  full_raw_domain_between_endpoints

def orderKatU16A : RawNullifierKey :=
  toLex (fun i => if i.val = 0 then 256 else 0) -- bytes begin `00 01`
def orderKatU16B : RawNullifierKey :=
  toLex (fun i => if i.val = 0 then 255 else 0) -- bytes begin `ff 00`

def orderKatBytesA : List Nat := [0, 1] ++ List.replicate 30 0
def orderKatBytesB : List Nat := [255, 0] ++ List.replicate 30 0

/-- Numeric u16-lane lex says `00 01` (256) is ABOVE `ff 00` (255). -/
theorem orderKat_u16_lane_reversal : orderKatU16B < orderKatU16A := by
  refine ⟨⟨0, by decide⟩, fun j hj => ?_, ?_⟩
  · have hz : j.val < 0 := hj
    omega
  · norm_num [orderKatU16A, orderKatU16B]

-- Byte lex says the opposite: `00 01` is BELOW `ff 00`.
#guard decide (orderKatBytesA < orderKatBytesB)
#guard decide (¬ orderKatBytesB < orderKatBytesA)

/-! ## 3. FNSP-v3 additive column layout -/

def V3_BASE : Nat := TRACE_WIDTH

def LOW_ADDR_TAG : Nat := V3_BASE
def LOW_ADDR_BASE : Nat := LOW_ADDR_TAG + 1
def LOW_VALUE_BASE : Nat := LOW_ADDR_BASE + 16
def LOW_NEXT_TAG : Nat := LOW_VALUE_BASE + 4
def LOW_NEXT_BASE : Nat := LOW_NEXT_TAG + 1

def ROOT_CUR_BASE : Nat := LOW_NEXT_BASE + 16
def rootCurBase (chain : Nat) : Nat := ROOT_CUR_BASE + chain * 8

def PRED_SIB_BASE : Nat := ROOT_CUR_BASE + 4 * 8
def PRED_POS_B0 : Nat := PRED_SIB_BASE + 3 * 8
def PRED_POS_B1 : Nat := PRED_POS_B0 + 1
def APP_SIB_BASE : Nat := PRED_POS_B1 + 1
def APP_POS_B0 : Nat := APP_SIB_BASE + 3 * 8
def APP_POS_B1 : Nat := APP_POS_B0 + 1

def LEX_LOW_KEY_AUX_BASE : Nat := APP_POS_B1 + 1
def LEX_KEY_NEXT_AUX_BASE : Nat := LEX_LOW_KEY_AUX_BASE + 17

def LEAF_SHARED_STATE_BASE : Nat := LEX_KEY_NEXT_AUX_BASE + 17
def LEAF_SHARED_STATE_STEPS : Nat := 5
def OLD_LEAF_STATE_BASE : Nat := LEAF_SHARED_STATE_BASE + 16 * LEAF_SHARED_STATE_STEPS
def LEAF_TAIL_STATE_STEPS : Nat := 6
def LOW_NEW_LEAF_STATE_BASE : Nat := OLD_LEAF_STATE_BASE + 16 * LEAF_TAIL_STATE_STEPS
def APPENDED_LEAF_STATE_BASE : Nat := LOW_NEW_LEAF_STATE_BASE + 16 * LEAF_TAIL_STATE_STEPS
def APPENDED_LEAF_STATE_STEPS : Nat := 11

def EXACT_NODE_STATE_STEPS : Nat := 10
def NODE_CHAINS_BASE : Nat := APPENDED_LEAF_STATE_BASE + 16 * APPENDED_LEAF_STATE_STEPS
def nodeStateBase (chain : Nat) : Nat :=
  NODE_CHAINS_BASE + chain * 16 * EXACT_NODE_STATE_STEPS

def PRE_COUNT_BASE : Nat := NODE_CHAINS_BASE + 4 * 16 * EXACT_NODE_STATE_STEPS
def POST_COUNT_BASE : Nat := PRE_COUNT_BASE + 4
def CURSOR_Q_LO : Nat := POST_COUNT_BASE + 4
def CURSOR_Q_HI : Nat := CURSOR_Q_LO + 1
def RADIX_CARRY_B0 : Nat := CURSOR_Q_HI + 1
def RADIX_CARRY_B1 : Nat := RADIX_CARRY_B0 + 1
def COUNT_CARRY_BASE : Nat := RADIX_CARRY_B1 + 1

def STATE_COMMIT_STEPS : Nat := 5
def PRE_STATE_COMMIT_BASE : Nat := COUNT_CARRY_BASE + 3
def POST_STATE_COMMIT_BASE : Nat := PRE_STATE_COMMIT_BASE + 16 * STATE_COMMIT_STEPS
def V3_TRACE_WIDTH : Nat := POST_STATE_COMMIT_BASE + 16 * STATE_COMMIT_STEPS

#guard V3_BASE == 1023
#guard LOW_ADDR_TAG == 1023
#guard LOW_ADDR_BASE == 1024
#guard LOW_VALUE_BASE == 1040
#guard LOW_NEXT_TAG == 1044
#guard LOW_NEXT_BASE == 1045
#guard ROOT_CUR_BASE == 1061
#guard PRED_SIB_BASE == 1093
#guard APP_SIB_BASE == 1119
#guard LEX_LOW_KEY_AUX_BASE == 1145
#guard LEAF_SHARED_STATE_BASE == 1179
#guard OLD_LEAF_STATE_BASE == 1259
#guard LOW_NEW_LEAF_STATE_BASE == 1355
#guard APPENDED_LEAF_STATE_BASE == 1451
#guard NODE_CHAINS_BASE == 1627
#guard PRE_COUNT_BASE == 2267
#guard POST_COUNT_BASE == 2271
#guard CURSOR_Q_LO == 2275
#guard COUNT_CARRY_BASE == 2279
#guard PRE_STATE_COMMIT_BASE == 2282
#guard POST_STATE_COMMIT_BASE == 2362
#guard V3_TRACE_WIDTH == 2442

/-! ## 4. Concrete full-state sponge schedules -/

def digestColsAt (stateBase absorbChunks : Nat) : List Nat :=
  cols (stateBase + 16 * (absorbChunks - 1)) 4 ++ cols (stateBase + 16 * absorbChunks) 4

def oldLeafPreimage : List EmittedExpr :=
  [.const EXACT_LINKED_LEAF_DOMAIN, .var LOW_ADDR_TAG] ++
    vars LOW_ADDR_BASE 16 ++ vars LOW_VALUE_BASE 4 ++
    [.var LOW_NEXT_TAG] ++ vars LOW_NEXT_BASE 16

def lowNewLeafPreimage : List EmittedExpr :=
  [.const EXACT_LINKED_LEAF_DOMAIN, .var LOW_ADDR_TAG] ++
    vars LOW_ADDR_BASE 16 ++ vars LOW_VALUE_BASE 4 ++
    [.const 1] ++ vars NULLIFIER_RAW_BASE 16

def appendedLeafPreimage : List EmittedExpr :=
  [.const EXACT_LINKED_LEAF_DOMAIN, .const 1] ++
    vars NULLIFIER_RAW_BASE 16 ++ vars VALUE_BASE 4 ++
    [.var LOW_NEXT_TAG] ++ vars LOW_NEXT_BASE 16

/-- The old and pointer-updated predecessor leaves share their first twenty inputs, hence their
first five absorb permutations.  Sharing those exact full-state outputs saves five state16 sites
without sharing across the first divergent chunk (`value[3] || next[0..2]`). -/
def sharedLeafPrefix : List EmittedExpr := oldLeafPreimage.take 20
def oldLeafTail : List EmittedExpr := oldLeafPreimage.drop 20
def lowNewLeafTail : List EmittedExpr := lowNewLeafPreimage.drop 20

def sharedLeafPlan : List State16Step :=
  (chunks4 sharedLeafPrefix).mapIdx fun stage chunk =>
    ⟨absorbInputExpr LEAF_SHARED_STATE_BASE oldLeafPreimage.length stage chunk,
      stateCols LEAF_SHARED_STATE_BASE stage, by exact of_decide_eq_true (Eq.refl true)⟩

def absorbAfterShared (tailBase stage : Nat) (chunk : List EmittedExpr) : List EmittedExpr :=
  let prior := if stage = 0 then (stateCols LEAF_SHARED_STATE_BASE 4).map .var
    else (stateCols tailBase (stage - 1)).map .var
  let rate := padChunk chunk
  (List.range 16).map fun i =>
    if i < 4 then eadd (prior.getD i (.const 0)) (rate.getD i (.const 0))
    else prior.getD i (.const 0)

def leafTailPlan (tailBase : Nat) (tail : List EmittedExpr) : List State16Step :=
  let chunks := chunks4 tail
  let absorb := chunks.mapIdx fun stage chunk =>
    ⟨absorbAfterShared tailBase stage chunk, stateCols tailBase stage, by exact of_decide_eq_true (Eq.refl true)⟩
  absorb ++ [⟨(stateCols tailBase (chunks.length - 1)).map .var,
    stateCols tailBase chunks.length, by exact of_decide_eq_true (Eq.refl true)⟩]

def oldLeafPlan : List State16Step := leafTailPlan OLD_LEAF_STATE_BASE oldLeafTail
def lowNewLeafPlan : List State16Step :=
  leafTailPlan LOW_NEW_LEAF_STATE_BASE lowNewLeafTail
def appendedLeafPlan : List State16Step :=
  spongePlan APPENDED_LEAF_STATE_BASE appendedLeafPreimage

def oldLeafDigestCols : List Nat := digestColsAt OLD_LEAF_STATE_BASE 5
def lowNewLeafDigestCols : List Nat := digestColsAt LOW_NEW_LEAF_STATE_BASE 5
def appendedLeafDigestCols : List Nat := digestColsAt APPENDED_LEAF_STATE_BASE 10

def chainCur (chain lane : Nat) : EmittedExpr := .var (rootCurBase chain + lane)
def pathSibBase (chain : Nat) : Nat := if chain < 2 then PRED_SIB_BASE else APP_SIB_BASE
def pathB0 (chain : Nat) : EmittedExpr := .var (if chain < 2 then PRED_POS_B0 else APP_POS_B0)
def pathB1 (chain : Nat) : EmittedExpr := .var (if chain < 2 then PRED_POS_B1 else APP_POS_B1)
def pathSib (chain sibling lane : Nat) : EmittedExpr :=
  .var (pathSibBase chain + sibling * 8 + lane)

def v3Ind0 (chain : Nat) : EmittedExpr :=
  emul (oneMinus (pathB0 chain)) (oneMinus (pathB1 chain))
def v3Ind1 (chain : Nat) : EmittedExpr := emul (pathB0 chain) (oneMinus (pathB1 chain))
def v3Ind2 (chain : Nat) : EmittedExpr := emul (oneMinus (pathB0 chain)) (pathB1 chain)
def v3Ind3 (chain : Nat) : EmittedExpr := emul (pathB0 chain) (pathB1 chain)

def v3ChildExpr (chain slot lane : Nat) : EmittedExpr :=
  match slot with
  | 0 => eadd (pathSib chain 0 lane)
      (emul (v3Ind0 chain) (esub (chainCur chain lane) (pathSib chain 0 lane)))
  | 1 => eadd
      (eadd (emul (pathSib chain 0 lane) (v3Ind0 chain))
        (emul (chainCur chain lane) (v3Ind1 chain)))
      (emul (pathSib chain 1 lane) (eadd (v3Ind2 chain) (v3Ind3 chain)))
  | 2 => eadd
      (eadd (emul (pathSib chain 1 lane) (eadd (v3Ind0 chain) (v3Ind1 chain)))
        (emul (chainCur chain lane) (v3Ind2 chain)))
      (emul (pathSib chain 2 lane) (v3Ind3 chain))
  | _ => eadd (pathSib chain 2 lane)
      (emul (v3Ind3 chain) (esub (chainCur chain lane) (pathSib chain 2 lane)))

def exactNodePreimage (chain : Nat) : List EmittedExpr :=
  .const EXACT_NODE_DOMAIN ::
    ((List.range 4).flatMap fun slot => (List.range 8).map (v3ChildExpr chain slot))

def exactNodePlan (chain : Nat) : List State16Step :=
  spongePlan (nodeStateBase chain) (exactNodePreimage chain)

def exactNodeDigestCols (chain : Nat) : List Nat := digestColsAt (nodeStateBase chain) 9

def stateCommitPreimage (chain countBase : Nat) : List EmittedExpr :=
  .const EXACT_STATE_DOMAIN ::
    ((exactNodeDigestCols chain).map .var ++ vars countBase 4)

def preStateCommitPlan : List State16Step :=
  spongePlan PRE_STATE_COMMIT_BASE (stateCommitPreimage 0 PRE_COUNT_BASE)
def postStateCommitPlan : List State16Step :=
  spongePlan POST_STATE_COMMIT_BASE (stateCommitPreimage 3 POST_COUNT_BASE)

def preStateCommitDigestCols : List Nat := digestColsAt PRE_STATE_COMMIT_BASE 4
def postStateCommitDigestCols : List Nat := digestColsAt POST_STATE_COMMIT_BASE 4

def v3PermutationSteps : List State16Step :=
  sharedLeafPlan ++ oldLeafPlan ++ lowNewLeafPlan ++ appendedLeafPlan ++
    (List.range 4).flatMap exactNodePlan ++ preStateCommitPlan ++ postStateCommitPlan

#guard oldLeafPreimage.length == 39
#guard lowNewLeafPreimage.length == 39
#guard appendedLeafPreimage.length == 39
#guard sharedLeafPrefix.length == 20
#guard oldLeafTail.length == 19
#guard lowNewLeafTail.length == 19
#guard sharedLeafPlan.length == 5
#guard oldLeafPlan.length == 6
#guard lowNewLeafPlan.length == 6
#guard appendedLeafPlan.length == 11
#guard (exactNodePreimage 0).length == 33
#guard (exactNodePlan 0).length == 10
#guard (stateCommitPreimage 0 PRE_COUNT_BASE).length == 13
#guard preStateCommitPlan.length == 5
#guard postStateCommitPlan.length == 5
#guard v3PermutationSteps.length == 78
#guard v3PermutationSteps.all fun step => step.input.length == 16
#guard v3PermutationSteps.all fun step => step.outputCols.length == 16

def v3State16Lookup (step : State16Step) : VmConstraint2 :=
  .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols step.width⟩

def v3State16Lookups : List VmConstraint2 := v3PermutationSteps.map v3State16Lookup

/-! ## 5. Exact u16 lex bracket -/

def auxSelector (auxBase i : Nat) : EmittedExpr := .var (auxBase + i)
def auxDelta (auxBase : Nat) : EmittedExpr := .var (auxBase + 16)

def sumExpr : List EmittedExpr → EmittedExpr :=
  List.foldl eadd (.const 0)

def selectorSum (auxBase : Nat) : EmittedExpr :=
  sumExpr ((List.range 16).map (auxSelector auxBase))

def selectorPrefix (auxBase k : Nat) : EmittedExpr :=
  sumExpr ((List.range (k + 1)).map (auxSelector auxBase))

def selectedDifferenceExpr (left right : Nat → EmittedExpr) (auxBase : Nat) : EmittedExpr :=
  sumExpr ((List.range 16).map fun i =>
    emul (auxSelector auxBase i) (esub (right i) (left i)))

def lex16BodiesExpr (left right : Nat → EmittedExpr) (auxBase : Nat) : List EmittedExpr :=
  ((List.range 16).map fun i => bitBody (auxBase + i)) ++
  [esub (selectorSum auxBase) (.const 1)] ++
  ((List.range 15).map fun i =>
    emul (oneMinus (selectorPrefix auxBase i))
      (esub (left i) (right i))) ++
  [esub (esub (selectedDifferenceExpr left right auxBase) (.const 1))
    (auxDelta auxBase)]

def baseExpr (base i : Nat) : EmittedExpr := .var (base + i)

def lex16Bodies (leftBase rightBase auxBase : Nat) : List EmittedExpr :=
  lex16BodiesExpr (baseExpr leftBase) (baseExpr rightBase) auxBase

def lex16ConstraintsExpr (left right : Nat → EmittedExpr) (auxBase : Nat) :
    List VmConstraint2 :=
  (lex16BodiesExpr left right auxBase).map fun body => .base (.gate body)

/-- A fixed raw vector with lane zero equal to one.  Endpoint comparisons dispatch to `0 < e0`;
REAL comparisons dispatch to the actual sixteen-limb relation. -/
def endpointUnitRaw (i : Nat) : EmittedExpr := if i = 0 then .const 1 else .const 0

def lowIsReal : EmittedExpr := .var LOW_ADDR_TAG
def nextIsReal : EmittedExpr := esub (.const 2) (.var LOW_NEXT_TAG)

def lowBracketLeft (i : Nat) : EmittedExpr :=
  emul lowIsReal (.var (LOW_ADDR_BASE + i))

def lowBracketRight (i : Nat) : EmittedExpr :=
  eadd (emul lowIsReal (.var (NULLIFIER_RAW_BASE + i)))
    (emul (oneMinus lowIsReal) (endpointUnitRaw i))

def nextBracketLeft (i : Nat) : EmittedExpr :=
  emul nextIsReal (.var (NULLIFIER_RAW_BASE + i))

def nextBracketRight (i : Nat) : EmittedExpr :=
  eadd (emul nextIsReal (.var (LOW_NEXT_BASE + i)))
    (emul (oneMinus nextIsReal) (endpointUnitRaw i))

/-- Address tag is BOT/REAL; successor tag is REAL/TOP.  BOT/TOP payload lanes are forced zero,
making the wire encoding canonical rather than merely order-equivalent. -/
def taggedEndpointConstraints : List VmConstraint2 :=
  [ .base (.gate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
      (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf LOW_ADDR_TAG)))),
    .base (.gate (emul (esub (.var LOW_NEXT_TAG) (.const 1))
      (esub (.var LOW_NEXT_TAG) (.const 2)))) ] ++
  ((List.range 16).map fun i => .base (.gate
    (emul (oneMinus (.var LOW_ADDR_TAG)) (.var (LOW_ADDR_BASE + i))))) ++
  ((List.range 16).map fun i => .base (.gate
    (emul (esub (.var LOW_NEXT_TAG) (.const 1)) (.var (LOW_NEXT_BASE + i)))))

def bracketConstraints : List VmConstraint2 :=
  lex16ConstraintsExpr lowBracketLeft lowBracketRight LEX_LOW_KEY_AUX_BASE ++
  lex16ConstraintsExpr nextBracketLeft nextBracketRight LEX_KEY_NEXT_AUX_BASE

#guard (lex16Bodies LOW_ADDR_BASE NULLIFIER_RAW_BASE LEX_LOW_KEY_AUX_BASE).length == 33
#guard taggedEndpointConstraints.length == 34
#guard bracketConstraints.length == 66

/-! ## 6. Count/path linkage and structural root gates -/

def v3BitConstraints (bits : List Nat) : List VmConstraint2 :=
  bits.map (fun col => .base (.gate (bitBody col))) ++
    bits.map (fun col => .base (.boundary .last (bitBody col)))

def positionConstraintsV3 : List VmConstraint2 :=
  v3BitConstraints [PRED_POS_B0, PRED_POS_B1, APP_POS_B0, APP_POS_B1]

def appendPosition : EmittedExpr :=
  eadd (.var APP_POS_B0) (emul (.const 2) (.var APP_POS_B1))

def radixCarry : EmittedExpr :=
  eadd (.var RADIX_CARRY_B0) (emul (.const 2) (.var RADIX_CARRY_B1))

def radixCarryConstraints : List VmConstraint2 :=
  [ .base (.gate (bitBody RADIX_CARRY_B0)),
    .base (.gate (bitBody RADIX_CARRY_B1)) ]

def radixLowWindow : Dregg2.Circuit.DescriptorIR2.WindowExpr :=
  .add
    (.add (.loc CURSOR_Q_LO) (.mul (.const (-4)) (.nxt CURSOR_Q_LO)))
    (.add (.mul (.const 65536) (.loc RADIX_CARRY_B0))
      (.add (.mul (.const 131072) (.loc RADIX_CARRY_B1))
        (.add (.mul (.const (-1)) (.loc APP_POS_B0))
          (.mul (.const (-2)) (.loc APP_POS_B1)))))

def radixHighWindow : Dregg2.Circuit.DescriptorIR2.WindowExpr :=
  .add (.loc CURSOR_Q_HI)
    (.add (.mul (.const (-1)) (.loc RADIX_CARRY_B0))
      (.add (.mul (.const (-2)) (.loc RADIX_CARRY_B1))
        (.mul (.const (-4)) (.nxt CURSOR_Q_HI))))

/-- Limbwise `q = 4*q' + position`.  Each equation has magnitude far below BabyBear, so the field
equality is also the intended integer equality once the u16 lookups and carry bits hold. -/
def cursorRadixConstraints : List VmConstraint2 :=
  [ .base (.boundary .first (esub (.var CURSOR_Q_LO) (.var PRE_COUNT_BASE))),
    .base (.boundary .first (esub (.var CURSOR_Q_HI) (.var (PRE_COUNT_BASE + 1)))),
    .windowGate ⟨radixLowWindow, true⟩,
    .windowGate ⟨radixHighWindow, true⟩,
    .base (.boundary .last (esub (.var CURSOR_Q_LO) appendPosition)),
    .base (.boundary .last (.var CURSOR_Q_HI)) ]

def countCarry (i : Nat) : EmittedExpr := .var (COUNT_CARRY_BASE + i)

/-- PRE is below capacity (high two limbs zero); POST is its exact u64 successor.  POST may be
`2^32`, but that image cannot satisfy the PRE high-zero gate in a later proof. -/
def countIncrementConstraints : List VmConstraint2 :=
  [ .base (.boundary .first (bitBody (COUNT_CARRY_BASE + 0))),
    .base (.boundary .first (bitBody (COUNT_CARRY_BASE + 1))),
    .base (.boundary .first (bitBody (COUNT_CARRY_BASE + 2))),
    .base (.boundary .first (.var (PRE_COUNT_BASE + 2))),
    .base (.boundary .first (.var (PRE_COUNT_BASE + 3))),
    .base (.boundary .first
      (eadd (esub (esub (.var POST_COUNT_BASE) (.var PRE_COUNT_BASE)) (.const 1))
        (emul (.const 65536) (countCarry 0)))),
    .base (.boundary .first
      (eadd (esub (esub (.var (POST_COUNT_BASE + 1)) (.var (PRE_COUNT_BASE + 1)))
        (countCarry 0)) (emul (.const 65536) (countCarry 1)))),
    .base (.boundary .first
      (eadd (esub (esub (.var (POST_COUNT_BASE + 2)) (.var (PRE_COUNT_BASE + 2)))
        (countCarry 1)) (emul (.const 65536) (countCarry 2)))),
    .base (.boundary .first
      (esub (esub (.var (POST_COUNT_BASE + 3)) (.var (PRE_COUNT_BASE + 3)))
        (countCarry 2))) ]

def exactEmptyDigestNat : List Nat := hashMany8Real [fieldNat EXACT_EMPTY_DOMAIN]

def emptyDigestExpr (lane : Nat) : EmittedExpr :=
  .const (exactEmptyDigestNat.getD lane 0)

def leafLinkBody (chain lane : Nat) : EmittedExpr :=
  let source := match chain with
    | 0 => .var (oldLeafDigestCols.getD lane 0)
    | 1 => .var (lowNewLeafDigestCols.getD lane 0)
    | 2 => emptyDigestExpr lane
    | _ => .var (appendedLeafDigestCols.getD lane 0)
  esub (chainCur chain lane) source

def leafLinkConstraintsV3 : List VmConstraint2 :=
  (List.range 4).flatMap fun chain =>
    (List.range 8).map fun lane => .base (.boundary .first (leafLinkBody chain lane))

def rootContinuity (chain lane : Nat) : Dregg2.Circuit.DescriptorIR2.WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gThread (rootCurBase chain + lane)
      ((exactNodeDigestCols chain).getD lane 0))

def rootContinuityConstraints : List VmConstraint2 :=
  (List.range 4).flatMap fun chain =>
    (List.range 8).map fun lane => .windowGate ⟨rootContinuity chain lane, true⟩

def middleRootConstraints : List VmConstraint2 :=
  (List.range 8).map fun lane => .base (.boundary .last
    (esub (.var ((exactNodeDigestCols 1).getD lane 0))
      (.var ((exactNodeDigestCols 2).getD lane 0))))

def successorCarrierContinuity : List VmConstraint2 :=
  (List.range 8).map fun lane => .windowGate ⟨
    Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
      (Dregg2.Circuit.GateExpr.gCarry (SUCCESSOR_NULLIFIER_ROOT_BASE + lane)), true⟩

def successorCarrierDerived : List VmConstraint2 :=
  (List.range 8).map fun lane => .base (.boundary .last
    (esub (.var (SUCCESSOR_NULLIFIER_ROOT_BASE + lane))
      (.var ((exactNodeDigestCols 3).getD lane 0))))

def countContinuity (base lane : Nat) : VmConstraint2 := .windowGate ⟨
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gCarry (base + lane)), true⟩

def countContinuityConstraints : List VmConstraint2 :=
  (List.range 4).map (countContinuity PRE_COUNT_BASE) ++
    (List.range 4).map (countContinuity POST_COUNT_BASE)

/-! ## 7. Range tables and public ABI -/

def incrementalRangePlan : List RangePlan :=
  u16Ranges LOW_ADDR_BASE 16 ++ u16Ranges LOW_VALUE_BASE 4 ++ u16Ranges LOW_NEXT_BASE 16 ++
    u16Ranges PRE_COUNT_BASE 4 ++ u16Ranges POST_COUNT_BASE 4 ++
    u16Ranges CURSOR_Q_LO 2 ++
    [⟨LEX_LOW_KEY_AUX_BASE + 16, 16⟩, ⟨LEX_KEY_NEXT_AUX_BASE + 16, 16⟩]

def incrementalRangeConstraints : List VmConstraint2 :=
  incrementalRangePlan.map rangeLookup

#guard incrementalRangePlan.length == 48

def PI_PRIOR_NULLIFIER_ROOT_BASE : Nat := PI_COUNT
def PI_PRE_COUNT_BASE : Nat := PI_PRIOR_NULLIFIER_ROOT_BASE + 8
def PI_POST_COUNT_BASE : Nat := PI_PRE_COUNT_BASE + 4
def PI_PRE_STATE_COMMIT_BASE : Nat := PI_POST_COUNT_BASE + 4
def PI_POST_STATE_COMMIT_BASE : Nat := PI_PRE_STATE_COMMIT_BASE + 8
def V3_PI_COUNT : Nat := PI_POST_STATE_COMMIT_BASE + 8

def v3PublicPins : List PublicPin :=
  publicPins ++
  pins .last (exactNodeDigestCols 0) PI_PRIOR_NULLIFIER_ROOT_BASE ++
  pins .first (cols PRE_COUNT_BASE 4) PI_PRE_COUNT_BASE ++
  pins .first (cols POST_COUNT_BASE 4) PI_POST_COUNT_BASE ++
  pins .last preStateCommitDigestCols PI_PRE_STATE_COMMIT_BASE ++
  pins .last postStateCommitDigestCols PI_POST_STATE_COMMIT_BASE

def v3PublicPinConstraints : List VmConstraint2 :=
  v3PublicPins.map publicPinConstraint

#guard PI_PRIOR_NULLIFIER_ROOT_BASE == 44
#guard PI_PRE_COUNT_BASE == 52
#guard PI_POST_COUNT_BASE == 56
#guard PI_PRE_STATE_COMMIT_BASE == 60
#guard PI_POST_STATE_COMMIT_BASE == 68
#guard V3_PI_COUNT == 76
#guard v3PublicPins.length == V3_PI_COUNT
#guard v3PublicPins.map (·.pi) == List.range V3_PI_COUNT

/-! ## 8. Concrete additive descriptor and honest envelope -/

def baseV2ConstraintsWithoutPins : List VmConstraint2 :=
  state16Lookups ++ rangeLookups ++ positionConstraints ++ firstPackConstraints ++
    leafLinkConstraints ++ continuityConstraints ++ depthConstraints

def exactAafiConstraints : List VmConstraint2 :=
  v3State16Lookups ++ incrementalRangeConstraints ++ positionConstraintsV3 ++
    taggedEndpointConstraints ++ bracketConstraints ++ radixCarryConstraints ++ cursorRadixConstraints ++
    countIncrementConstraints ++ leafLinkConstraintsV3 ++ rootContinuityConstraints ++
    middleRootConstraints ++ successorCarrierContinuity ++ successorCarrierDerived ++
    countContinuityConstraints

def faithfulNoteSpendV3Constraints : List VmConstraint2 :=
  baseV2ConstraintsWithoutPins ++ exactAafiConstraints ++ v3PublicPinConstraints

def faithfulNoteSpendV3Descriptor : EffectVmDescriptor2 :=
  { name := "faithful-note-spend-v3::exact-aafi-nullifier-state16"
  , traceWidth := V3_TRACE_WIDTH
  , piCount := V3_PI_COUNT
  , tables := [mainTableDef V3_TRACE_WIDTH, poseidon2State16ChipTableDef,
      rangeTable 15, rangeTable 16]
  , constraints := faithfulNoteSpendV3Constraints
  , hashSites := []
  , ranges := [] }

def V3_INCREMENTAL_WIDTH : Nat := V3_TRACE_WIDTH - TRACE_WIDTH
def V3_INCREMENTAL_STATE16_SITES_PER_ROW : Nat := v3PermutationSteps.length
def V3_TOTAL_STATE16_SITES_PER_ROW : Nat := state16Lookups.length + v3State16Lookups.length
def V3_TOTAL_STATE16_EVENTS : Nat := TREE_DEPTH * V3_TOTAL_STATE16_SITES_PER_ROW
def V3_INCREMENTAL_RANGE16_SITES_PER_ROW : Nat := incrementalRangePlan.length
def V3_TOTAL_RANGE_SITES_PER_ROW : Nat := rangeLookups.length + incrementalRangePlan.length
def V3_TOTAL_RANGE_EVENTS : Nat := TREE_DEPTH * V3_TOTAL_RANGE_SITES_PER_ROW

#guard V3_INCREMENTAL_WIDTH == 1419
#guard V3_INCREMENTAL_STATE16_SITES_PER_ROW == 78
#guard V3_TOTAL_STATE16_SITES_PER_ROW == 128
#guard V3_TOTAL_STATE16_EVENTS == 2048
#guard V3_INCREMENTAL_RANGE16_SITES_PER_ROW == 48
#guard V3_TOTAL_RANGE_SITES_PER_ROW == 180
#guard V3_TOTAL_RANGE_EVENTS == 2880
#guard v3State16Lookups.all fun c => match c with
  | .lookup l => l.table == poseidon2state16 && l.tuple.length == REQUIRED_STATE16_TUPLE
  | _ => false
#guard faithfulNoteSpendV3Descriptor.traceWidth == 2442
#guard faithfulNoteSpendV3Descriptor.piCount == 76
#guard faithfulNoteSpendV3Descriptor.tables.length == 4
#guard faithfulNoteSpendV3Descriptor.hashSites.isEmpty
#guard faithfulNoteSpendV3Descriptor.ranges.isEmpty

/-- The bytes are evaluable and deterministic, but deliberately not emitted/registered until the
remaining descriptor-level refinement theorem and an independent witness constructor are green. -/
def faithfulNoteSpendV3DescriptorJson : String := emitVmJson2 faithfulNoteSpendV3Descriptor

#guard faithfulNoteSpendV3DescriptorJson.startsWith
  "{\"name\":\"faithful-note-spend-v3::exact-aafi-nullifier-state16\",\"ir\":2,\"trace_width\":2442"

#assert_axioms accumulatorStateBlock_cursor_injective
#assert_axioms wrong_cursor_commit_forces_collision
#assert_axioms carried_checkpoint_wrong_count_forces_collision
#assert_axioms wrong_predecessor_digest_forces_collision
#assert_axioms wrong_successor_path_forces_collision
#assert_axioms count_at_capacity_refused_as_pre
#assert_axioms last_slot_reaches_terminal_full

end Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
