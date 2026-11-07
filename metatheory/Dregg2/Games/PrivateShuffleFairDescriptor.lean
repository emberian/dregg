/-
# Dregg2.Games.PrivateShuffleFairDescriptor

Lean author for the fixed-eight joint-entropy layer above
`PrivateShuffleDescriptor`.

One attempt has eight participant contributions.  Each contribution is a
canonical 16-bit value committed, with eight full-field blind lanes, before
reveal.  Their sum in `ZMod 2^16` is the joint entropy.  Entropy values
`0..40319` are accepted *without reduction* and interpreted through an exact
equivalence

  `Fin 40320 ≃ Equiv.Perm (Fin 8)`.

Thus every accepted rank has exactly one permutation and every permutation has
exactly one accepted rank.  Values `40320..65535` are rejected.  A rejected
attempt is itself a proof result (public `accepted = false`, zero deal root),
so a receipt protocol can require every attempt to be recorded.

The single static relation cannot prove temporal facts.  In particular:

* “all other contributions were fixed before the honest reveal” is the
  commit-before-reveal / hiding assumption used by the uniformity theorem;
* a last revealer or coordinator can still abort after learning the result;
* if an application permits an unrecorded restart, it reintroduces choice.

Those boundaries are represented below rather than laundered into a claim of
non-abortable fairness.
-/
import Dregg2.Games.PrivateShuffleDescriptor
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic

namespace Dregg2.Games.PrivateShuffleFairDescriptor

open scoped BigOperators
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact entropy and rank semantics. -/

def PARTICIPANT_COUNT : Nat := 8
def ENTROPY_BITS : Nat := 16
def ENTROPY_SPACE : Nat := 2 ^ ENTROPY_BITS
def PERMUTATION_COUNT : Nat := 40320
def DIGEST_WIDTH : Nat := 8
def BABYBEAR_MODULUS : Int := 2013265921

abbrev Entropy := ZMod ENTROPY_SPACE

local instance entropySpaceNeZero : NeZero ENTROPY_SPACE :=
  ⟨by norm_num [ENTROPY_SPACE, ENTROPY_BITS]⟩

local instance permutationCountNeZero : NeZero PERMUTATION_COUNT :=
  ⟨by norm_num [PERMUTATION_COUNT]⟩

/-- ASCII `JEN8`: participant-seed commitment domain. -/
def COMMIT_DOMAIN_TAG : Int := 1246051896

/-- ASCII `JFR8`: fixed 8-party/add16/reject40320/decomposeFin rule. -/
def RULE_ID : Int := 1246122552

def SHUFFLE_RULE_ID : Int :=
  Dregg2.Games.PrivateShuffleDescriptor.RULE_ID

/-- The recursive mixed-radix equivalence is not an arbitrary enumeration.
`decomposeFin` chooses the image of zero and recursively permutes the remaining
`Fin n`; `finProdFinEquiv` assigns the first digit a block of `(n-1)!` ranks. -/
def permRankEquiv : (n : Nat) → Equiv.Perm (Fin n) ≃ Fin n.factorial
  | 0 =>
      { toFun := fun _ => ⟨0, by norm_num [Nat.factorial]⟩
      , invFun := fun _ => Equiv.refl _
      , left_inv := by
          intro p
          ext x
          exact Fin.elim0 x
      , right_inv := by
          intro r
          apply Fin.ext
          have h : r.val < 1 := r.isLt
          show 0 = r.val
          omega }
  | n + 1 =>
      Equiv.Perm.decomposeFin.trans
        ((Equiv.prodCongr (Equiv.refl _) (permRankEquiv n)).trans
          finProdFinEquiv)

theorem factorial_eight : Nat.factorial 8 = PERMUTATION_COUNT := by
  norm_num [PERMUTATION_COUNT, Nat.factorial]

def fin40320EquivFactorial8 : Fin PERMUTATION_COUNT ≃ Fin (Nat.factorial 8) :=
  finCongr factorial_eight.symm

/-- Exactly one permutation for every accepted entropy rank. -/
def permutationOfRankEquiv : Fin PERMUTATION_COUNT ≃ Equiv.Perm (Fin 8) :=
  fin40320EquivFactorial8.trans (permRankEquiv 8).symm

def permutationOfRank (rank : Fin PERMUTATION_COUNT) : Equiv.Perm (Fin 8) :=
  permutationOfRankEquiv rank

theorem permutationOfRank_bijective : Function.Bijective permutationOfRank :=
  permutationOfRankEquiv.bijective

theorem permutationOfRank_no_duplicate (rank : Fin PERMUTATION_COUNT) :
    Function.Injective (permutationOfRank rank) :=
  (permutationOfRank rank).injective

theorem permutationOfRank_no_omission (rank : Fin PERMUTATION_COUNT) :
    Function.Surjective (permutationOfRank rank) :=
  (permutationOfRank rank).surjective

def AcceptedEntropy : Type := {x : Entropy // x.val < PERMUTATION_COUNT}

/-- Rejection is exact: the accepted subset has cardinality exactly `8!`, and
the accepted value itself is the rank.  There is no `% 40320`. -/
def acceptedEntropyRankEquiv : AcceptedEntropy ≃ Fin PERMUTATION_COUNT where
  toFun x := ⟨x.1.val, x.2⟩
  invFun r :=
    ⟨(r.val : Entropy), by
      rw [ZMod.val_natCast_of_lt]
      · exact r.isLt
      · exact r.isLt.trans (by norm_num [PERMUTATION_COUNT, ENTROPY_SPACE, ENTROPY_BITS])⟩
  left_inv x := by
    apply Subtype.ext
    exact ZMod.natCast_zmod_val x.1
  right_inv r := by
    apply Fin.ext
    change (r.val : Entropy).val = r.val
    rw [ZMod.val_natCast_of_lt]
    exact r.isLt.trans (by norm_num [PERMUTATION_COUNT, ENTROPY_SPACE, ENTROPY_BITS])

/-- The exact conditional-uniform map: accepted joint entropy and permutations
are equivalent finite types, not merely “close” in statistical distance. -/
def acceptedEntropyPermutationEquiv :
    AcceptedEntropy ≃ Equiv.Perm (Fin 8) :=
  acceptedEntropyRankEquiv.trans permutationOfRankEquiv

theorem acceptedEntropyPermutation_bijective :
    Function.Bijective acceptedEntropyPermutationEquiv :=
  acceptedEntropyPermutationEquiv.bijective

def accepted (x : Entropy) : Bool := decide (x.val < PERMUTATION_COUNT)

theorem accepted_iff (x : Entropy) :
    accepted x = true ↔ x.val < PERMUTATION_COUNT := by
  simp [accepted]

/-- A fixed collection of all non-honest contributions enters only through
its additive aggregate.  “Fixed” is the temporal/independence premise: it must
be selected before the honest contribution is learned. -/
def jointFromOneHonest (fixedOthers honest : Entropy) : Entropy :=
  honest + fixedOthers

def jointFromOneHonestEquiv (fixedOthers : Entropy) : Entropy ≃ Entropy where
  toFun := jointFromOneHonest fixedOthers
  invFun := fun joint => joint - fixedOthers
  left_inv := by intro x; simp [jointFromOneHonest]
  right_inv := by intro x; simp [jointFromOneHonest]

/-- If at least one contribution is uniform and hidden until the others are
fixed, additive joint entropy modulo `2^16` is exactly uniform.  This theorem
is the finite bijection underlying that statement; it does not assert that a
network transcript actually met the temporal premise. -/
theorem commit_before_reveal_one_honest_uniform (fixedOthers : Entropy) :
    Function.Bijective (jointFromOneHonest fixedOthers) :=
  (jointFromOneHonestEquiv fixedOthers).bijective

/-! ## 2. Commitment tree and accepted/rejected attempt relation. -/

structure PrivateWitness where
  seeds : Fin 8 → Entropy
  commitBlinding : Fin 8 → Fin 8 → Int
  dealBlinding : Fin 8 → Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  attempt : Int
  commitmentRoot : Fin 8 → Int
  accepted : Bool
  dealRoot : Fin 8 → Int
  deriving DecidableEq, Repr

def CanonicalBlinding (w : PrivateWitness) : Prop :=
  (∀ participant lane,
    0 ≤ w.commitBlinding participant lane ∧
      w.commitBlinding participant lane < BABYBEAR_MODULUS) ∧
  (∀ seat lane,
    0 ≤ w.dealBlinding seat lane ∧
      w.dealBlinding seat lane < BABYBEAR_MODULUS)

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  ((List.finRange 8).all fun participant =>
    (List.finRange 8).all fun lane =>
      decide (0 ≤ w.commitBlinding participant lane ∧
        w.commitBlinding participant lane < BABYBEAR_MODULUS)) &&
  ((List.finRange 8).all fun seat =>
    (List.finRange 8).all fun lane =>
      decide (0 ≤ w.dealBlinding seat lane ∧
        w.dealBlinding seat lane < BABYBEAR_MODULUS))

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]

def jointEntropy (w : PrivateWitness) : Entropy :=
  ∑ participant, w.seeds participant

def acceptedAttempt (w : PrivateWitness) : Bool := accepted (jointEntropy w)

def acceptedRank (w : PrivateWitness)
    (h : (jointEntropy w).val < PERMUTATION_COUNT) : Fin PERMUTATION_COUNT :=
  ⟨(jointEntropy w).val, h⟩

/-- Reject witnesses still carry a deterministic internal permutation (rank
zero), but the public deal root is forced to zero.  It is not a dealt game. -/
def effectiveRank (w : PrivateWitness) : Fin PERMUTATION_COUNT :=
  if h : (jointEntropy w).val < PERMUTATION_COUNT then acceptedRank w h
  else ⟨0, by norm_num [PERMUTATION_COUNT]⟩

def dealWitness (w : PrivateWitness) :
    Dregg2.Games.PrivateShuffleDescriptor.PrivateWitness where
  cards := permutationOfRank (effectiveRank w)
  blinding := w.dealBlinding

/-- Exactly sixteen inputs: domain/session/rule/attempt/participant/seed,
eight blind felts, and two explicit framing zeros. -/
def commitmentLeafPreimage (pub : PublicStatement) (w : PrivateWitness)
    (participant : Fin 8) : List Int :=
  [COMMIT_DOMAIN_TAG, pub.session, pub.rule, pub.attempt, participant.val,
    (w.seeds participant).val] ++
    List.ofFn (w.commitBlinding participant) ++ [0, 0]

def commitmentLeaf (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) (participant : Fin 8) :
    Fin 8 → Int :=
  hash8 (commitmentLeafPreimage pub w participant)

def node8 (hash8 : List Int → Fin 8 → Int)
    (left right : Fin 8 → Int) : Fin 8 → Int :=
  hash8 (List.ofFn left ++ List.ofFn right)

def commitmentLevel1 (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) (pair : Fin 4) : Fin 8 → Int :=
  node8 hash8
    (commitmentLeaf hash8 pub w ⟨2 * pair.val, by omega⟩)
    (commitmentLeaf hash8 pub w ⟨2 * pair.val + 1, by omega⟩)

def commitmentLevel2 (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) (pair : Fin 2) : Fin 8 → Int :=
  node8 hash8
    (commitmentLevel1 hash8 pub w ⟨2 * pair.val, by omega⟩)
    (commitmentLevel1 hash8 pub w ⟨2 * pair.val + 1, by omega⟩)

def commitmentRoot (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Fin 8 → Int :=
  node8 hash8
    (commitmentLevel2 hash8 pub w 0)
    (commitmentLevel2 hash8 pub w 1)

def computedDealRoot (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Fin 8 → Int :=
  Dregg2.Games.PrivateShuffleDescriptor.dealRoot
    hash8 pub.session (dealWitness w)

def resultDealRoot (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Fin 8 → Int :=
  if acceptedAttempt w then computedDealRoot hash8 pub w else fun _ => 0

def Accepts (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  pub.rule = RULE_ID ∧
  pub.commitmentRoot = commitmentRoot hash8 pub w ∧
  pub.accepted = acceptedAttempt w ∧
  pub.dealRoot = resultDealRoot hash8 pub w

def check (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.commitmentRoot == commitmentRoot hash8 pub w) &&
  (pub.accepted == acceptedAttempt w) &&
  (pub.dealRoot == resultDealRoot hash8 pub w)

theorem check_iff (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindingCheck_iff, and_assoc]

theorem accepted_attempt_exact_permutation
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement}
    {w : PrivateWitness} (h : check hash8 pub w = true)
    (_ha : pub.accepted = true) :
    Function.Injective (dealWitness w).cards ∧
      Function.Surjective (dealWitness w).cards := by
  have hw := (check_iff hash8 pub w).mp h
  exact ⟨(permutationOfRank (effectiveRank w)).injective,
    (permutationOfRank (effectiveRank w)).surjective⟩

theorem accepted_attempt_root_is_existing_shuffle_root
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement}
    {w : PrivateWitness} (h : check hash8 pub w = true)
    (ha : pub.accepted = true) :
    pub.dealRoot = Dregg2.Games.PrivateShuffleDescriptor.dealRoot
      hash8 pub.session (dealWitness w) := by
  have hw := (check_iff hash8 pub w).mp h
  have haw : acceptedAttempt w = true := hw.2.2.2.1 ▸ ha
  simpa [resultDealRoot, computedDealRoot, haw] using hw.2.2.2.2

theorem rejected_attempt_has_zero_deal_root
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement}
    {w : PrivateWitness} (h : check hash8 pub w = true)
    (ha : pub.accepted = false) : pub.dealRoot = fun _ => 0 := by
  have hw := (check_iff hash8 pub w).mp h
  have haw : acceptedAttempt w = false := hw.2.2.2.1 ▸ ha
  simpa [resultDealRoot, haw] using hw.2.2.2.2

/-! ## 3. Lean-authored fixed AIR descriptor. -/

/- Public columns are deliberately identical to the PI layout. -/
def SESSION : Nat := 0
def RULE : Nat := 1
def ATTEMPT : Nat := 2
def COMMIT_ROOT_BASE : Nat := 3
def ACCEPTED : Nat := 11
def DEAL_ROOT_PUBLIC_BASE : Nat := 12

def COMMIT_ROOT (lane : Nat) : Nat := COMMIT_ROOT_BASE + lane
def DEAL_ROOT_PUBLIC (lane : Nat) : Nat := DEAL_ROOT_PUBLIC_BASE + lane

def SEED_BASE : Nat := 20
def SEED_BIT_BASE : Nat := 28
def CARRY : Nat := 156
def CARRY_BIT_BASE : Nat := 157
def ENTROPY_COL : Nat := 160
def ENTROPY_BIT_BASE : Nat := 161
def LOW_SLACK : Nat := 177
def LOW_SLACK_BIT_BASE : Nat := 178
def HIGH_SLACK : Nat := 194
def HIGH_SLACK_BIT_BASE : Nat := 195
def RANK : Nat := 211
def REMAINDER_BASE : Nat := 212
def DIGIT_BASE : Nat := 218
def DIGIT_SELECTOR_BASE : Nat := 225
def PERM_SELECTOR_BASE : Nat := 260
def COMMIT_BLIND_BASE : Nat := 463
def COMMIT_LEAF_BASE : Nat := 527
def COMMIT_LEVEL1_BASE : Nat := 591
def COMMIT_LEVEL2_BASE : Nat := 623
def DEAL_BLIND_BASE : Nat := 639
def DEAL_LEAF_BASE : Nat := 703
def DEAL_LEVEL1_BASE : Nat := 767
def DEAL_LEVEL2_BASE : Nat := 799
def DEAL_CALC_ROOT_BASE : Nat := 815
def TRACE_WIDTH : Nat := 823

def SEED (participant : Nat) : Nat := SEED_BASE + participant
def SEED_BIT (participant bit : Nat) : Nat :=
  SEED_BIT_BASE + ENTROPY_BITS * participant + bit
def CARRY_BIT (bit : Nat) : Nat := CARRY_BIT_BASE + bit
def ENTROPY_BIT (bit : Nat) : Nat := ENTROPY_BIT_BASE + bit
def LOW_SLACK_BIT (bit : Nat) : Nat := LOW_SLACK_BIT_BASE + bit
def HIGH_SLACK_BIT (bit : Nat) : Nat := HIGH_SLACK_BIT_BASE + bit
def REMAINDER (stage : Nat) : Nat := REMAINDER_BASE + stage - 1
def DIGIT (stage : Nat) : Nat := DIGIT_BASE + stage

def digitSelectorOffset : Nat → Nat
  | 0 => 0
  | 1 => 8
  | 2 => 15
  | 3 => 21
  | 4 => 26
  | 5 => 30
  | _ => 33

def DIGIT_SELECTOR (stage value : Nat) : Nat :=
  DIGIT_SELECTOR_BASE + digitSelectorOffset stage + value

def permSelectorOffset : Nat → Nat
  | 2 => 0
  | 3 => 4
  | 4 => 13
  | 5 => 29
  | 6 => 54
  | 7 => 90
  | _ => 139

def PERM_SELECTOR (size pos card : Nat) : Nat :=
  PERM_SELECTOR_BASE + permSelectorOffset size + size * pos + card

def COMMIT_BLIND (participant lane : Nat) : Nat :=
  COMMIT_BLIND_BASE + DIGEST_WIDTH * participant + lane
def COMMIT_LEAF (participant lane : Nat) : Nat :=
  COMMIT_LEAF_BASE + DIGEST_WIDTH * participant + lane
def COMMIT_LEVEL1 (pair lane : Nat) : Nat :=
  COMMIT_LEVEL1_BASE + DIGEST_WIDTH * pair + lane
def COMMIT_LEVEL2 (pair lane : Nat) : Nat :=
  COMMIT_LEVEL2_BASE + DIGEST_WIDTH * pair + lane

def DEAL_BLIND (seat lane : Nat) : Nat :=
  DEAL_BLIND_BASE + DIGEST_WIDTH * seat + lane
def DEAL_LEAF (seat lane : Nat) : Nat :=
  DEAL_LEAF_BASE + DIGEST_WIDTH * seat + lane
def DEAL_LEVEL1 (pair lane : Nat) : Nat :=
  DEAL_LEVEL1_BASE + DIGEST_WIDTH * pair + lane
def DEAL_LEVEL2 (pair lane : Nat) : Nat :=
  DEAL_LEVEL2_BASE + DIGEST_WIDTH * pair + lane
def DEAL_CALC_ROOT (lane : Nat) : Nat := DEAL_CALC_ROOT_BASE + lane

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x
def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recomposeBody (col : Nat) (bitCol : Nat → Nat) (bits : Nat) : EmittedExpr :=
  sub (v col)
    (sumE ((List.range bits).map fun bit =>
      weighted ((2 : Int) ^ bit) (v (bitCol bit))))

def seedBodies : List EmittedExpr :=
  ((List.range PARTICIPANT_COUNT).flatMap fun participant =>
    ((List.range ENTROPY_BITS).map fun bit => binaryBody (SEED_BIT participant bit)) ++
    [recomposeBody (SEED participant) (SEED_BIT participant) ENTROPY_BITS])

def carryBodies : List EmittedExpr :=
  ((List.range 3).map fun bit => binaryBody (CARRY_BIT bit)) ++
  [recomposeBody CARRY CARRY_BIT 3]

def entropyBodies : List EmittedExpr :=
  ((List.range ENTROPY_BITS).map fun bit => binaryBody (ENTROPY_BIT bit)) ++
  [recomposeBody ENTROPY_COL ENTROPY_BIT ENTROPY_BITS]

def seedSumBody : EmittedExpr :=
  sub
    (sumE ((List.range PARTICIPANT_COUNT).map fun participant => v (SEED participant)))
    (add (v ENTROPY_COL) (weighted ENTROPY_SPACE (v CARRY)))

def slackBodies : List EmittedExpr :=
  ((List.range ENTROPY_BITS).map fun bit => binaryBody (LOW_SLACK_BIT bit)) ++
  [recomposeBody LOW_SLACK LOW_SLACK_BIT ENTROPY_BITS] ++
  ((List.range ENTROPY_BITS).map fun bit => binaryBody (HIGH_SLACK_BIT bit)) ++
  [recomposeBody HIGH_SLACK HIGH_SLACK_BIT ENTROPY_BITS]

/-- Exact threshold, in both directions.  On the accepted branch
`entropy + lowSlack = 40319`; on reject `entropy = 40320 + highSlack`. -/
def thresholdBodies : List EmittedExpr :=
  [ binaryBody ACCEPTED
  , mul (v ACCEPTED)
      (sub (add (v ENTROPY_COL) (v LOW_SLACK)) (c (PERMUTATION_COUNT - 1)))
  , mul (sub (c 1) (v ACCEPTED))
      (sub (v ENTROPY_COL) (add (c PERMUTATION_COUNT) (v HIGH_SLACK)))
  , sub (v RANK) (mul (v ACCEPTED) (v ENTROPY_COL)) ]

def rankStage (stage : Nat) : Nat := if stage = 0 then RANK else REMAINDER stage

def rankWeight : Nat → Int
  | 0 => 5040
  | 1 => 720
  | 2 => 120
  | 3 => 24
  | 4 => 6
  | 5 => 2
  | _ => 1

def digitSelectorBodies : List EmittedExpr :=
  (List.range 7).flatMap fun stage =>
    (List.range (8 - stage)).map fun value =>
      binaryBody (DIGIT_SELECTOR stage value)

def digitOneBodies : List EmittedExpr :=
  (List.range 7).map fun stage =>
    sub
      (sumE ((List.range (8 - stage)).map fun value =>
        v (DIGIT_SELECTOR stage value)))
      (c 1)

def digitRecomposeBodies : List EmittedExpr :=
  (List.range 7).map fun stage =>
    sub (v (DIGIT stage))
      (sumE ((List.range (8 - stage)).map fun (value : Nat) =>
        weighted (value : Int) (v (DIGIT_SELECTOR stage value))))

def rankDecomposeBodies : List EmittedExpr :=
  (List.range 7).map fun stage =>
    if stage < 6 then
      sub (v (rankStage stage))
        (add (weighted (rankWeight stage) (v (DIGIT stage)))
          (v (rankStage (stage + 1))))
    else sub (v (rankStage stage)) (v (DIGIT stage))

def previousPermSelector (size pos card : Nat) : EmittedExpr :=
  if size = 2 then
    if pos = 0 ∧ card = 0 then c 1 else c 0
  else v (PERM_SELECTOR (size - 1) pos card)

def permExpected (size pos card : Nat) : EmittedExpr :=
  let stage := 8 - size
  if pos = 0 then v (DIGIT_SELECTOR stage card)
  else if card = 0 then
    sumE ((List.range (size - 1)).map fun q =>
      mul (v (DIGIT_SELECTOR stage (q + 1)))
        (previousPermSelector size (pos - 1) q))
  else
    mul (previousPermSelector size (pos - 1) (card - 1))
      (sub (c 1) (v (DIGIT_SELECTOR stage card)))

/-- The circuit form of `Perm.decomposeFin.symm`: choose the image of zero,
then lift the recursively decoded smaller permutation and swap values `0` and
the chosen digit.  Every cell is an explicit degree-two equality. -/
def permutationBodies : List EmittedExpr :=
  (List.range 7).flatMap fun level =>
    let size := level + 2
    (List.range size).flatMap fun pos =>
      (List.range size).map fun card =>
        sub (v (PERM_SELECTOR size pos card)) (permExpected size pos card)

def finalPermutationBodies : List EmittedExpr :=
  ((List.range 8).map fun pos =>
    sub (sumE ((List.range 8).map fun card => v (PERM_SELECTOR 8 pos card))) (c 1)) ++
  ((List.range 8).map fun card =>
    sub (sumE ((List.range 8).map fun pos => v (PERM_SELECTOR 8 pos card))) (c 1))

def cardExpr (seat : Nat) : EmittedExpr :=
  sumE ((List.range 8).map fun (card : Nat) =>
    weighted (card : Int) (v (PERM_SELECTOR 8 seat card)))

def digestExprs (f : Nat → Nat) : List EmittedExpr :=
  (List.range DIGEST_WIDTH).map fun lane => v (f lane)

def digestCols (f : Nat → Nat) : List Nat :=
  (List.range DIGEST_WIDTH).map f

def commitmentLeafInputExprs (participant : Nat) : List EmittedExpr :=
  [c COMMIT_DOMAIN_TAG, v SESSION, v RULE, v ATTEMPT, c participant,
    v (SEED participant)] ++
  (List.range DIGEST_WIDTH).map (fun lane => v (COMMIT_BLIND participant lane)) ++
  [c 0, c 0]

def commitmentLeafLookups : List VmConstraint2 :=
  (List.range 8).map fun participant =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN (commitmentLeafInputExprs participant)
        (digestCols (COMMIT_LEAF participant))⟩

def commitmentLevel1Lookups : List VmConstraint2 :=
  (List.range 4).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (COMMIT_LEAF (2 * pair)) ++
          digestExprs (COMMIT_LEAF (2 * pair + 1)))
        (digestCols (COMMIT_LEVEL1 pair))⟩

def commitmentLevel2Lookups : List VmConstraint2 :=
  (List.range 2).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (COMMIT_LEVEL1 (2 * pair)) ++
          digestExprs (COMMIT_LEVEL1 (2 * pair + 1)))
        (digestCols (COMMIT_LEVEL2 pair))⟩

def commitmentRootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN
      (digestExprs (COMMIT_LEVEL2 0) ++ digestExprs (COMMIT_LEVEL2 1))
      ((List.range DIGEST_WIDTH).map COMMIT_ROOT)⟩

def dealLeafInputExprs (seat : Nat) : List EmittedExpr :=
  [c Dregg2.Games.PrivateShuffleDescriptor.LEAF_DOMAIN_TAG,
    v SESSION, c SHUFFLE_RULE_ID, c seat, cardExpr seat] ++
  (List.range DIGEST_WIDTH).map (fun lane => v (DEAL_BLIND seat lane)) ++
  [c 0, c 0, c 0]

def dealLeafLookups : List VmConstraint2 :=
  (List.range 8).map fun seat =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN (dealLeafInputExprs seat) (digestCols (DEAL_LEAF seat))⟩

def dealLevel1Lookups : List VmConstraint2 :=
  (List.range 4).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (DEAL_LEAF (2 * pair)) ++ digestExprs (DEAL_LEAF (2 * pair + 1)))
        (digestCols (DEAL_LEVEL1 pair))⟩

def dealLevel2Lookups : List VmConstraint2 :=
  (List.range 2).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (DEAL_LEVEL1 (2 * pair)) ++ digestExprs (DEAL_LEVEL1 (2 * pair + 1)))
        (digestCols (DEAL_LEVEL2 pair))⟩

def dealRootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN
      (digestExprs (DEAL_LEVEL2 0) ++ digestExprs (DEAL_LEVEL2 1))
      ((List.range DIGEST_WIDTH).map DEAL_CALC_ROOT)⟩

def hashLookups : List VmConstraint2 :=
  commitmentLeafLookups ++ commitmentLevel1Lookups ++
  commitmentLevel2Lookups ++ [commitmentRootLookup] ++
  dealLeafLookups ++ dealLevel1Lookups ++ dealLevel2Lookups ++ [dealRootLookup]

def dealRootBindingBodies : List EmittedExpr :=
  ((List.range DIGEST_WIDTH).map fun lane =>
    mul (v ACCEPTED)
      (sub (v (DEAL_ROOT_PUBLIC lane)) (v (DEAL_CALC_ROOT lane)))) ++
  ((List.range DIGEST_WIDTH).map fun lane =>
    mul (sub (c 1) (v ACCEPTED)) (v (DEAL_ROOT_PUBLIC lane)))

def semanticBodies : List EmittedExpr :=
  [sub (v RULE) (c RULE_ID)] ++
  seedBodies ++ carryBodies ++ entropyBodies ++ [seedSumBody] ++
  slackBodies ++ thresholdBodies ++
  digitSelectorBodies ++ digitOneBodies ++ digitRecomposeBodies ++
  rankDecomposeBodies ++ permutationBodies ++ finalPermutationBodies ++
  dealRootBindingBodies

def publicPins : List VmConstraint2 :=
  (List.range 20).map fun col => .base (.piBinding .first col col)

/-- The fixed relation has 30 real full-width Poseidon lookups: fifteen for
the participant-commitment tree and fifteen for the existing private-deal tree.
All arithmetic and recursive rank/permutation teeth are copied to `.last` so a
height-one trace cannot evade them. -/
def privateShuffleFairN8Descriptor : EffectVmDescriptor2 :=
  { name := "private-shuffle-fair-n8::add16-reject40320-decomposefin-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 20
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privateShuffleFairN8Descriptor.traceWidth == 823
#guard privateShuffleFairN8Descriptor.piCount == 20
#guard commitmentLeafLookups.length == 8
#guard dealLeafLookups.length == 8
#guard hashLookups.length == 30
#guard digitSelectorBodies.length == 35
#guard permutationBodies.length == 203
#guard semanticBodies.length == 488
#guard privateShuffleFairN8Descriptor.constraints.length == 30 + 2 * 488 + 20
#guard !(emitVmJson2 privateShuffleFairN8Descriptor).contains "1246122553"

/-! ### Emitted-AIR extraction/refinement boundary. -/

def fairM0 : Int → Int := fun _ => 0
def fairF0 : Int → Int × Nat := fun _ => (0, 0)

def constTrace (a pis : Assignment) (tf : TraceFamily) : VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := by simp [constTrace]

@[simp] theorem constTrace_loc0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).loc = a := by
  funext col
  simp [envAt, constTrace]

@[simp] theorem constTrace_pub0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).pub = pis := rfl

@[simp] theorem constTrace_tf (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).tf = tf := rfl

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < BABYBEAR_MODULUS

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privateShuffleFairN8Descriptor.constraints := by
  simp [privateShuffleFairN8Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privateShuffleFairN8Descriptor.constraints := by
  simp [privateShuffleFairN8Descriptor, hpin]

theorem hash_lookup_mem {lookup : VmConstraint2} (hlookup : lookup ∈ hashLookups) :
    lookup ∈ privateShuffleFairN8Descriptor.constraints := by
  simp [privateShuffleFairN8Descriptor, hlookup]

theorem semantic_gate_vanishes {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateShuffleFairN8Descriptor fairM0 fairF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem public_pin_sound {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateShuffleFairN8Descriptor fairM0 fairF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem chip_lookup_sound_of_mem {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateShuffleFairN8Descriptor fairM0 fairF0 []
      (constTrace a pis tf))
    {inputs : List EmittedExpr} {outputs : List Nat}
    (hinlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted inputs.length)
    (hmem : VmConstraint2.lookup
      ⟨TableId.poseidon2, chipLookupTupleN inputs outputs⟩ ∈ hashLookups) :
    outputs.map a = permOut (inputs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) _ (hash_lookup_mem hmem)
  have hlookup :
      (chipLookupTupleN inputs outputs).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    inputs outputs hinlen hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  canonicalCells : CanonicalAssignment a
  semanticGates : ∀ body ∈ semanticBodies,
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  -- ⚑ The arity condition is NAMED (`hadm`), not an anonymous arrow: `chipLookupTupleN`'s
  -- side condition discharges by `assumption` off exactly this binder, so the tuple named in the
  -- next hypothesis is the one whose arity has been shown admitted.
  hashTrees : ∀ (inputs : List EmittedExpr) (outputs : List Nat)
    (hadm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted inputs.length),
    VmConstraint2.lookup ⟨TableId.poseidon2, chipLookupTupleN inputs outputs hadm⟩ ∈ hashLookups →
    outputs.map a = permOut (inputs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

theorem privateShuffleFairN8_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateShuffleFairN8Descriptor fairM0 fairF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   fun _ _ hinlen hmem => chip_lookup_sound_of_mem permOut hChip hsat hinlen hmem,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

/-! ## 4. Honest temporal boundary and abort/restart tooth. -/

/-- A protocol-level premise, deliberately outside `Accepts`: commitments are
finalized before reveals, at least one contribution is uniform conditioned on
the prior view, and every completed/rejected attempt is appended rather than
silently discarded.  Cryptographic implementations discharge `binding` and
`hiding`; a cell/receipt state machine discharges `ordered` and `recorded`. -/
structure AttemptHistory where
  commitmentsBeforeReveals : Bool
  oneContributionUniformGivenPriorView : Bool
  commitmentBinding : Bool
  commitmentHidingUntilReveal : Bool
  completedAttemptsRecorded : Bool
  deriving DecidableEq, Repr

def FairAttemptHistory (history : AttemptHistory) : Prop :=
  history.commitmentsBeforeReveals = true ∧
  history.oneContributionUniformGivenPriorView = true ∧
  history.commitmentBinding = true ∧
  history.commitmentHidingUntilReveal = true ∧
  history.completedAttemptsRecorded = true

/-- The static relation does not force its own temporal premises: the same
accepted witness can be paired with an explicitly unfair external history. -/
theorem accepts_is_compatible_with_failed_temporal_assumptions :
    ∃ (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement)
      (w : PrivateWitness) (history : AttemptHistory),
      Accepts hash8 pub w ∧ ¬ FairAttemptHistory history := by
  let zeroHash : List Int → Fin 8 → Int := fun _ _ => 0
  let w : PrivateWitness :=
    { seeds := fun _ => 0
    , commitBlinding := fun _ _ => 0
    , dealBlinding := fun _ _ => 0 }
  let pub : PublicStatement :=
    { session := 1
    , rule := RULE_ID
    , attempt := 0
    , commitmentRoot := fun _ => 0
    , accepted := true
    , dealRoot := fun _ => 0 }
  let history : AttemptHistory :=
    { commitmentsBeforeReveals := false
    , oneContributionUniformGivenPriorView := false
    , commitmentBinding := false
    , commitmentHidingUntilReveal := false
    , completedAttemptsRecorded := false }
  have ha : Accepts zeroHash pub w := by
    simp [Accepts, CanonicalBlinding, pub, w, acceptedAttempt, accepted,
      jointEntropy, resultDealRoot, computedDealRoot, commitmentRoot,
      commitmentLevel2, commitmentLevel1, commitmentLeaf, node8, zeroHash,
      Dregg2.Games.PrivateShuffleDescriptor.dealRoot,
      Dregg2.Games.PrivateShuffleDescriptor.level2,
      Dregg2.Games.PrivateShuffleDescriptor.level1,
      Dregg2.Games.PrivateShuffleDescriptor.node8,
      Dregg2.Games.PrivateShuffleDescriptor.leafDigest,
      RULE_ID, BABYBEAR_MODULUS, PERMUTATION_COUNT]
  exact ⟨zeroHash, pub, w, history, ha, by simp [FairAttemptHistory, history]⟩

/-- There are at least two accepted ranks with different deterministic deals.
If a coordinator is allowed to suppress the first accepted receipt and start a
fresh attempt, it can recover a choice.  Preventing that requires the recorded
attempt/timeout state machine, not another polynomial in this static AIR. -/
theorem unrecorded_restart_reintroduces_choice :
    ∃ r0 r1 : Fin PERMUTATION_COUNT,
      r0 ≠ r1 ∧ permutationOfRank r0 ≠ permutationOfRank r1 := by
  let r0 : Fin PERMUTATION_COUNT := ⟨0, by norm_num [PERMUTATION_COUNT]⟩
  let r1 : Fin PERMUTATION_COUNT := ⟨1, by norm_num [PERMUTATION_COUNT]⟩
  refine ⟨r0, r1, Fin.ne_of_val_ne (by simp [r0, r1]), ?_⟩
  exact (permutationOfRankEquiv.injective.ne (by decide))

#guard ENTROPY_SPACE == 65536
#guard PERMUTATION_COUNT == Nat.factorial 8

#assert_all_clean [
  Dregg2.Games.PrivateShuffleFairDescriptor.factorial_eight,
  Dregg2.Games.PrivateShuffleFairDescriptor.permutationOfRank_bijective,
  Dregg2.Games.PrivateShuffleFairDescriptor.permutationOfRank_no_duplicate,
  Dregg2.Games.PrivateShuffleFairDescriptor.permutationOfRank_no_omission,
  Dregg2.Games.PrivateShuffleFairDescriptor.acceptedEntropyPermutation_bijective,
  Dregg2.Games.PrivateShuffleFairDescriptor.commit_before_reveal_one_honest_uniform,
  Dregg2.Games.PrivateShuffleFairDescriptor.check_iff,
  Dregg2.Games.PrivateShuffleFairDescriptor.accepted_attempt_exact_permutation,
  Dregg2.Games.PrivateShuffleFairDescriptor.accepted_attempt_root_is_existing_shuffle_root,
  Dregg2.Games.PrivateShuffleFairDescriptor.rejected_attempt_has_zero_deal_root,
  Dregg2.Games.PrivateShuffleFairDescriptor.privateShuffleFairN8_emitted_air_sound,
  Dregg2.Games.PrivateShuffleFairDescriptor.accepts_is_compatible_with_failed_temporal_assumptions,
  Dregg2.Games.PrivateShuffleFairDescriptor.unrecorded_restart_reintroduces_choice]

end Dregg2.Games.PrivateShuffleFairDescriptor
