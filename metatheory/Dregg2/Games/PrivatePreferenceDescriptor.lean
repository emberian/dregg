/-
# Dregg2.Games.PrivatePreferenceDescriptor

A reusable fixed-shape private preference aggregation proof family for guild
votes, party decisions, matchmaking ranking, and quest choices.

Family: exactly four participants and four options.  Every private ballot is a
canonical score vector with each score in `[0,3]`.  The public statement is only
`(session, rule, ballotRoot[0..8), winner)`: neither ballots, aggregate scores,
nor the winning score are public.  The winner is the LOWEST option index with
maximal aggregate score.

The sixteen two-bit scores are faithfully packed into two 16-bit felts.  A
domain-separated full-arity Poseidon2 permutation absorbs both packs, eight
canonical blind felts, and explicit zero framing, exposing all eight output
lanes.  Rust fills and proves this Lean-authored layout; it does not author AIR.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics

namespace Dregg2.Games.PrivatePreferenceDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact semantic relation and checker. -/

def PARTICIPANT_COUNT : Nat := 4
def OPTION_COUNT : Nat := 4
def SCORE_BITS : Nat := 2
def TOTAL_BITS : Nat := 4
def DIGEST_WIDTH : Nat := 8

def BABYBEAR_MODULUS : Int := 2013265921

/-- `PRF4`: commitment domain tag for this exact two-pack score encoding. -/
def ROOT_DOMAIN_TAG : Int := 1347569204

/-- `PRN4`: fixed `N=4,K=4,score<4,lowest-index-tie` rule identifier. -/
def RULE_ID : Int := 1347571252

structure PrivateWitness where
  scores : Fin 4 → Fin 4 → Fin 4
  blinding : Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  ballotRoot : Fin 8 → Int
  winner : Nat
  deriving DecidableEq, Repr

def CanonicalBlinding (w : PrivateWitness) : Prop :=
  ∀ i, 0 ≤ w.blinding i ∧ w.blinding i < BABYBEAR_MODULUS

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  (List.ofFn w.blinding).all fun z => decide (0 ≤ z ∧ z < BABYBEAR_MODULUS)

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- One ballot as four base-4 digits, hence an injective byte. -/
def ballotPackOf (ballot : Fin 4 → Fin 4) : Int :=
  (ballot 0).val + 4 * (ballot 1).val + 16 * (ballot 2).val + 64 * (ballot 3).val

theorem ballotPackOf_bounds (ballot : Fin 4 → Fin 4) :
    0 ≤ ballotPackOf ballot ∧ ballotPackOf ballot < 256 := by
  simp only [ballotPackOf]
  have h0 := (ballot 0).isLt
  have h1 := (ballot 1).isLt
  have h2 := (ballot 2).isLt
  have h3 := (ballot 3).isLt
  omega

theorem ballotPackOf_injective : Function.Injective ballotPackOf := by
  intro left right h
  have hp :
      ((left 0).val : Int) + 4 * (left 1).val + 16 * (left 2).val + 64 * (left 3).val =
      ((right 0).val : Int) + 4 * (right 1).val + 16 * (right 2).val + 64 * (right 3).val := by
    simpa [ballotPackOf] using h
  have l0 := (left 0).isLt; have l1 := (left 1).isLt
  have l2 := (left 2).isLt; have l3 := (left 3).isLt
  have r0 := (right 0).isLt; have r1 := (right 1).isLt
  have r2 := (right 2).isLt; have r3 := (right 3).isLt
  have h0 : (left 0).val = (right 0).val := by omega
  have h1 : (left 1).val = (right 1).val := by omega
  have h2 : (left 2).val = (right 2).val := by omega
  have h3 : (left 3).val = (right 3).val := by omega
  funext o
  fin_cases o
  · exact Fin.ext h0
  · exact Fin.ext h1
  · exact Fin.ext h2
  · exact Fin.ext h3

def ballotPack (w : PrivateWitness) (participant : Fin 4) : Int :=
  ballotPackOf (w.scores participant)

/-- Participants 0 and 1, each one canonical base-256 digit. -/
def packedLow (w : PrivateWitness) : Int := ballotPack w 0 + 256 * ballotPack w 1

/-- Participants 2 and 3, each one canonical base-256 digit. -/
def packedHigh (w : PrivateWitness) : Int := ballotPack w 2 + 256 * ballotPack w 3

/-- The two committed 16-bit packs lose no private score. -/
theorem packedScores_injective {left right : PrivateWitness}
    (hlow : packedLow left = packedLow right)
    (hhigh : packedHigh left = packedHigh right) : left.scores = right.scores := by
  have ll0 : 0 ≤ ballotPack left 0 ∧ ballotPack left 0 < 256 :=
    ballotPackOf_bounds (left.scores 0)
  have ll1 : 0 ≤ ballotPack left 1 ∧ ballotPack left 1 < 256 :=
    ballotPackOf_bounds (left.scores 1)
  have rl0 : 0 ≤ ballotPack right 0 ∧ ballotPack right 0 < 256 :=
    ballotPackOf_bounds (right.scores 0)
  have rl1 : 0 ≤ ballotPack right 1 ∧ ballotPack right 1 < 256 :=
    ballotPackOf_bounds (right.scores 1)
  have h0 : ballotPack left 0 = ballotPack right 0 := by
    simp only [packedLow] at hlow
    omega
  have h1 : ballotPack left 1 = ballotPack right 1 := by
    simp only [packedLow] at hlow
    omega
  have ll2 : 0 ≤ ballotPack left 2 ∧ ballotPack left 2 < 256 :=
    ballotPackOf_bounds (left.scores 2)
  have ll3 : 0 ≤ ballotPack left 3 ∧ ballotPack left 3 < 256 :=
    ballotPackOf_bounds (left.scores 3)
  have rl2 : 0 ≤ ballotPack right 2 ∧ ballotPack right 2 < 256 :=
    ballotPackOf_bounds (right.scores 2)
  have rl3 : 0 ≤ ballotPack right 3 ∧ ballotPack right 3 < 256 :=
    ballotPackOf_bounds (right.scores 3)
  have h2 : ballotPack left 2 = ballotPack right 2 := by
    simp only [packedHigh] at hhigh
    omega
  have h3 : ballotPack left 3 = ballotPack right 3 := by
    simp only [packedHigh] at hhigh
    omega
  funext participant option
  fin_cases participant
  · exact congrFun (ballotPackOf_injective h0) option
  · exact congrFun (ballotPackOf_injective h1) option
  · exact congrFun (ballotPackOf_injective h2) option
  · exact congrFun (ballotPackOf_injective h3) option

def aggregateScore (w : PrivateWitness) (option : Nat) : Int :=
  if h : option < 4 then
    (List.ofFn (fun participant : Fin 4 => (w.scores participant ⟨option, h⟩).val)).sum
  else 0

/-- Strict-update argmax: ties retain the earlier, therefore lower, index. -/
def argmaxUpto (score : Nat → Int) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if score (argmaxUpto score n) < score (n + 1) then n + 1 else argmaxUpto score n

theorem argmaxUpto_le (score : Nat → Int) : ∀ n, argmaxUpto score n ≤ n := by
  intro n
  induction n with
  | zero => simp [argmaxUpto]
  | succ n ih =>
      simp only [argmaxUpto]
      split <;> omega

theorem argmaxUpto_max (score : Nat → Int) :
    ∀ n q, q ≤ n → score q ≤ score (argmaxUpto score n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      have : q = 0 := by omega
      subst q
      simp [argmaxUpto]
  | succ n ih =>
      intro q hq
      by_cases hnew : score (argmaxUpto score n) < score (n + 1)
      · rw [argmaxUpto, if_pos hnew]
        by_cases hqnew : q = n + 1
        · subst q; exact le_rfl
        · exact le_trans (ih q (by omega)) (le_of_lt hnew)
      · rw [argmaxUpto, if_neg hnew]
        by_cases hqnew : q = n + 1
        · subst q; omega
        · exact ih q (by omega)

theorem argmaxUpto_strict_before (score : Nat → Int) :
    ∀ n q, q < argmaxUpto score n → score q < score (argmaxUpto score n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simp [argmaxUpto] at hq
  | succ n ih =>
      intro q hq
      by_cases hnew : score (argmaxUpto score n) < score (n + 1)
      · have harg : argmaxUpto score (n + 1) = n + 1 := by simp [argmaxUpto, hnew]
        rw [harg] at hq ⊢
        exact lt_of_le_of_lt (argmaxUpto_max score n q (by omega)) hnew
      · have harg : argmaxUpto score (n + 1) = argmaxUpto score n := by
          simp [argmaxUpto, hnew]
        rw [harg] at hq ⊢
        exact ih q hq

def winner (w : PrivateWitness) : Nat := argmaxUpto (aggregateScore w) 3

theorem winner_lt (w : PrivateWitness) : winner w < OPTION_COUNT := by
  have := argmaxUpto_le (aggregateScore w) 3
  simp only [winner, OPTION_COUNT]
  omega

theorem winner_optimal (w : PrivateWitness) {q : Nat} (hq : q < OPTION_COUNT) :
    aggregateScore w q ≤ aggregateScore w (winner w) := by
  apply argmaxUpto_max (aggregateScore w) 3 q
  simp only [OPTION_COUNT] at hq
  omega

theorem winner_strict_before (w : PrivateWitness) {q : Nat} (hq : q < winner w) :
    aggregateScore w q < aggregateScore w (winner w) := by
  exact argmaxUpto_strict_before (aggregateScore w) 3 q hq

/-- Optimality plus strict dominance over lower indices uniquely characterizes
the deterministic winner.  This is the integer endpoint needed by the final
modular-to-integer descriptor lift. -/
theorem winner_eq_of_optimal_and_lowest (w : PrivateWitness) {chosen : Nat}
    (hchosen : chosen < OPTION_COUNT)
    (hmax : ∀ q < OPTION_COUNT, aggregateScore w q ≤ aggregateScore w chosen)
    (hlow : ∀ q < chosen, aggregateScore w q < aggregateScore w chosen) :
    winner w = chosen := by
  have hwlt := winner_lt w
  have hcw := hmax (winner w) hwlt
  have hwc := winner_optimal w hchosen
  by_contra hne
  have hcases : winner w < chosen ∨ chosen < winner w := by omega
  cases hcases with
  | inl h =>
      have := hlow (winner w) h
      omega
  | inr h =>
      have := winner_strict_before w h
      omega

/-- Thirteen meaningful inputs plus three explicit zero lanes select the chip's
full arity-16 seed mode. -/
def rootPreimage (session : Int) (w : PrivateWitness) : List Int :=
  [ROOT_DOMAIN_TAG, session, RULE_ID, packedLow w, packedHigh w] ++
    List.ofFn w.blinding ++ [0, 0, 0]

def ballotRoot (hash8 : List Int → Fin 8 → Int) (session : Int) (w : PrivateWitness) : Fin 8 → Int :=
  hash8 (rootPreimage session w)

def RootCollision (hash8 : List Int → Fin 8 → Int) (session : Int)
    (left right : PrivateWitness) : Prop :=
  (packedLow left ≠ packedLow right ∨ packedHigh left ≠ packedHigh right ∨
      left.blinding ≠ right.blinding) ∧
  ballotRoot hash8 session left = ballotRoot hash8 session right

def Accepts (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  pub.rule = RULE_ID ∧
  pub.ballotRoot = ballotRoot hash8 pub.session w ∧
  pub.winner = winner w

def check (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.ballotRoot == ballotRoot hash8 pub.session w) &&
  (pub.winner == winner w)

theorem check_iff (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindingCheck_iff, and_assoc]

theorem check_sound {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {w : PrivateWitness}
    (h : check hash8 pub w = true) :
    CanonicalBlinding w ∧
    pub.rule = RULE_ID ∧
    pub.ballotRoot = ballotRoot hash8 pub.session w ∧
    pub.winner < OPTION_COUNT ∧
    (∀ q < OPTION_COUNT, aggregateScore w q ≤ aggregateScore w pub.winner) ∧
    (∀ q < pub.winner, aggregateScore w q < aggregateScore w pub.winner) := by
  rcases (check_iff hash8 pub w).mp h with ⟨hcanon, hrule, hroot, hwin⟩
  rw [hwin]
  exact ⟨hcanon, hrule, hroot, winner_lt w,
    fun _ hq => winner_optimal w hq, fun _ hq => winner_strict_before w hq⟩

theorem two_distinct_openings_yield_root_collision
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : check hash8 pub left = true) (hr : check hash8 pub right = true)
    (hdiff : packedLow left ≠ packedLow right ∨ packedHigh left ≠ packedHigh right ∨
      left.blinding ≠ right.blinding) :
    RootCollision hash8 pub.session left right := by
  have al := (check_iff hash8 pub left).mp hl
  have ar := (check_iff hash8 pub right).mp hr
  exact ⟨hdiff, al.2.2.1.symm.trans ar.2.2.1⟩

/-! Non-vacuous workbook and semantic tamper teeth. -/

def fixtureScores (participant option : Fin 4) : Fin 4 :=
  match participant.val, option.val with
  | 0, 0 => 3 | 0, 1 => 2 | 0, 2 => 0 | 0, _ => 1
  | 1, 0 => 2 | 1, 1 => 3 | 1, 2 => 0 | 1, _ => 1
  | 2, 0 => 0 | 2, 1 => 3 | 2, 2 => 2 | 2, _ => 1
  | _, 0 => 1 | _, 1 => 2 | _, 2 => 3 | _, _ => 0

def fixtureWitness : PrivateWitness := ⟨fixtureScores, fun i => 900 + i.val⟩
def toyHash8 (xs : List Int) (lane : Fin 8) : Int := xs.sum + 31 + lane.val
def fixturePublic : PublicStatement where
  session := 77
  rule := RULE_ID
  ballotRoot := ballotRoot toyHash8 77 fixtureWitness
  winner := 1

def tamperedScoreWitness : PrivateWitness where
  scores := fun i o => if i = 0 ∧ o = 0 then 2 else fixtureScores i o
  blinding := fixtureWitness.blinding

def noncanonicalBlindWitness : PrivateWitness where
  scores := fixtureWitness.scores
  blinding := fun i => if i = 0 then BABYBEAR_MODULUS else fixtureWitness.blinding i

#guard aggregateScore fixtureWitness 0 == 6
#guard aggregateScore fixtureWitness 1 == 10
#guard aggregateScore fixtureWitness 2 == 5
#guard aggregateScore fixtureWitness 3 == 3
#guard winner fixtureWitness == 1
#guard check toyHash8 fixturePublic fixtureWitness
#guard !check toyHash8 { fixturePublic with winner := 0 } fixtureWitness
#guard !check toyHash8 { fixturePublic with ballotRoot := fun i => fixturePublic.ballotRoot i + 1 }
  fixtureWitness
#guard !check toyHash8 fixturePublic tamperedScoreWitness
#guard !check toyHash8 fixturePublic noncanonicalBlindWitness

/-! ## 2. Lean-authored fixed AIR descriptor. -/

/- Public columns 0..10. Private blinds 11..18, packed ballots 19..20,
sixteen score triplets 21..68, then aggregate/selection/range machinery. -/
def SESSION : Nat := 0
def RULE : Nat := 1
def ROOT_BASE : Nat := 2
def WINNER : Nat := 10
def BLINDING_BASE : Nat := 11
def PACKED_LOW : Nat := 19
def PACKED_HIGH : Nat := 20

def ROOT (lane : Nat) : Nat := ROOT_BASE + lane
def BLINDING (lane : Nat) : Nat := BLINDING_BASE + lane

def SCORE_BASE : Nat := 21
def SCORE_STRIDE : Nat := 3
def SCORE (participant option : Nat) : Nat :=
  SCORE_BASE + SCORE_STRIDE * (OPTION_COUNT * participant + option)
def SCORE_BIT (participant option bit : Nat) : Nat := SCORE participant option + 1 + bit

def TOTAL_BASE : Nat := 69
def SELECT_BASE : Nat := 73
def MAX_SCORE : Nat := 77
def MAX_DIFF_BASE : Nat := 78
def MAX_DIFF_BITS_BASE : Nat := 82
def LOW_SLACK_BASE : Nat := 98
def LOW_SLACK_BITS_BASE : Nat := 102
def TRACE_WIDTH : Nat := 118

def TOTAL (option : Nat) : Nat := TOTAL_BASE + option
def SELECT (option : Nat) : Nat := SELECT_BASE + option
def MAX_DIFF (option : Nat) : Nat := MAX_DIFF_BASE + option
def MAX_DIFF_BIT (option bit : Nat) : Nat := MAX_DIFF_BITS_BASE + TOTAL_BITS * option + bit
def LOW_SLACK (option : Nat) : Nat := LOW_SLACK_BASE + option
def LOW_SLACK_BIT (option bit : Nat) : Nat := LOW_SLACK_BITS_BASE + TOTAL_BITS * option + bit

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x

@[simp] theorem sumE_eval (a : Assignment) (xs : List EmittedExpr) :
    (sumE xs).eval a = (xs.map (fun e => e.eval a)).sum := by
  unfold sumE
  induction xs with
  | nil => simp [c, EmittedExpr.eval]
  | cons x xs ih =>
      change (List.foldr add (.const 0) xs).eval a =
        (xs.map (fun e => e.eval a)).sum at ih
      change (add x (List.foldr add (.const 0) xs)).eval a =
        x.eval a + (xs.map (fun e => e.eval a)).sum
      simp only [add, EmittedExpr.eval]
      rw [ih]

def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recompose (col : Nat) (bit : Nat → Nat) (bits : Nat) : EmittedExpr :=
  sub (sumE ((List.range bits).map (fun b => weighted ((2 : Int) ^ b) (v (bit b))))) (v col)

def ballotPackExpr (participant : Nat) : EmittedExpr :=
  sumE ((List.range OPTION_COUNT).map
    (fun option => weighted ((4 : Int) ^ option) (v (SCORE participant option))))

def totalExpr (option : Nat) : EmittedExpr :=
  sumE ((List.range PARTICIPANT_COUNT).map (fun participant => v (SCORE participant option)))

def laterSelected (option : Nat) : EmittedExpr :=
  sumE ((List.range (3 - option)).map (fun j => v (SELECT (option + 1 + j))))

def scoreBodies (participant option : Nat) : List EmittedExpr :=
  [recompose (SCORE participant option) (SCORE_BIT participant option) SCORE_BITS] ++
  (List.range SCORE_BITS).map (fun bit => binaryBody (SCORE_BIT participant option bit))

def optionBodies (option : Nat) : List EmittedExpr :=
  [ sub (v (TOTAL option)) (totalExpr option)
  , binaryBody (SELECT option)
  , sub (v (MAX_DIFF option)) (sub (v MAX_SCORE) (v (TOTAL option)))
  , recompose (MAX_DIFF option) (MAX_DIFF_BIT option) TOTAL_BITS ] ++
  (List.range TOTAL_BITS).map (fun bit => binaryBody (MAX_DIFF_BIT option bit)) ++
  [ sub (v (LOW_SLACK option)) (sub (v (MAX_DIFF option)) (laterSelected option))
  , recompose (LOW_SLACK option) (LOW_SLACK_BIT option) TOTAL_BITS ] ++
  (List.range TOTAL_BITS).map (fun bit => binaryBody (LOW_SLACK_BIT option bit))

def semanticBodies : List EmittedExpr :=
  [ sub (v RULE) (c RULE_ID)
  , sub (v PACKED_LOW) (add (ballotPackExpr 0) (weighted 256 (ballotPackExpr 1)))
  , sub (v PACKED_HIGH) (add (ballotPackExpr 2) (weighted 256 (ballotPackExpr 3))) ] ++
  ((List.range PARTICIPANT_COUNT).flatMap fun participant =>
    (List.range OPTION_COUNT).flatMap fun option => scoreBodies participant option) ++
  ((List.range OPTION_COUNT).flatMap optionBodies) ++
  [ sub (sumE ((List.range OPTION_COUNT).map (fun option => v (SELECT option)))) (c 1)
  , sub (v WINNER)
      (sumE ((List.range OPTION_COUNT).map
        (fun (option : Nat) => weighted (option : Int) (v (SELECT option)))))
  , sub (v MAX_SCORE)
      (sumE ((List.range OPTION_COUNT).map
        (fun option => mul (v (SELECT option)) (v (TOTAL option))))) ]

def rootInputExprs : List EmittedExpr :=
  [c ROOT_DOMAIN_TAG, v SESSION, v RULE, v PACKED_LOW, v PACKED_HIGH] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (BLINDING lane)) ++ [c 0, c 0, c 0]

def rootDigestCols : List Nat := (List.range DIGEST_WIDTH).map ROOT

def rootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN rootInputExprs rootDigestCols⟩

def hashLookups : List VmConstraint2 := [rootLookup]

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range DIGEST_WIDTH).map
    (fun lane => .base (.piBinding .first (ROOT lane) (2 + lane))) ++
  [ .base (.piBinding .first WINNER 10) ]

/-- Transition gates plus exact last-row copies prevent a height-one/last-row
semantic escape. -/
def privatePreferenceN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "private-preference-n4k4::score2-wide-poseidon2-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 11
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privatePreferenceN4K4Descriptor.traceWidth == 118
#guard privatePreferenceN4K4Descriptor.piCount == 11
#guard hashLookups.length == 1
#guard privatePreferenceN4K4Descriptor.constraints.length == 1 + 2 * semanticBodies.length + 11
#guard !(emitVmJson2 privatePreferenceN4K4Descriptor).contains "1347571253"

/-! ## 3. Emitted-AIR extraction boundary.

`Satisfied2` yields every semantic gate modulo BabyBear, every public binding,
and the genuine 16-lane Poseidon lookup result.  The sections below carry that
boundary through the complete finite modular-to-integer lift: bit decoding,
bounded affine equalities, semantic winner identification, exact root input and
output identification, and finally `privatePreferenceN4K4_descriptor_to_accepts`.
-/

def ppM0 : Int → Int := fun _ => 0
def ppF0 : Int → Int × Nat := fun _ => (0, 0)

def publicCols : List Nat := [SESSION, RULE] ++ rootDigestCols ++ [WINNER]

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
    VmConstraint2.base (.gate body) ∈ privatePreferenceN4K4Descriptor.constraints := by
  simp [privatePreferenceN4K4Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privatePreferenceN4K4Descriptor.constraints := by
  simp [privatePreferenceN4K4Descriptor, hpin]

theorem root_lookup_mem : rootLookup ∈ privatePreferenceN4K4Descriptor.constraints := by
  simp [privatePreferenceN4K4Descriptor, hashLookups]

theorem semantic_gate_vanishes {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem public_pin_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h


theorem wide_root_lookup_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  canonicalCells : CanonicalAssignment a
  semanticGates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  wideRoot : rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

theorem privatePreferenceN4K4_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   wide_root_lookup_sound permOut hChip hsat,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

theorem binaryBody_zero_iff (a : Assignment) (col : Nat) :
    (binaryBody col).eval a = 0 ↔ a col = 0 ∨ a col = 1 := by
  simp [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
  omega

/-! ## 4. Integer-decode progress: all private bits close unconditionally.

The first version stopped at modular gate extraction.  The next rung below is
stronger: BabyBear primality plus canonical cells turns every binary gate into
an actual integer bit, directly from `Satisfied2`.  It also packages the exact
generic no-wrap lift for every affine residual.  Thus the named finishing
residual no longer contains "prove bithood"; it is specifically the bounded
total/pack/select/max/root identification described after these theorems. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-- The unique integer window containing only the zero residue. -/
def InZeroResidueWindow (x : Int) : Prop :=
  -BABYBEAR_MODULUS < x ∧ x < BABYBEAR_MODULUS

def SemanticNoWrap (a : Assignment) : Prop :=
  ∀ body ∈ semanticBodies, InZeroResidueWindow (body.eval a)

theorem eq_zero_of_modEq_zero_of_window {x : Int}
    (hmod : x ≡ 0 [ZMOD BABYBEAR_MODULUS])
    (hwindow : InZeroResidueWindow x) : x = 0 := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod
  rcases hwindow with ⟨hlo, hhi⟩
  simp only [BABYBEAR_MODULUS] at hk hlo hhi
  omega

/-- `Satisfied2` plus an explicit complete-residual bound gives the exact
integer equation for every authored semantic body. -/
theorem semantic_gate_exact {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (hnowrap : SemanticNoWrap a)
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a = 0 :=
  eq_zero_of_modEq_zero_of_window (semantic_gate_vanishes hsat hbody) (hnowrap body hbody)

/-- Canonicality and BabyBear primality make a modular binary gate an honest
integer bit.  No separate residual window is needed for multiplicative
booleanity. -/
theorem binary_of_modular_gate {a : Assignment} {col : Nat}
    (hcanon : CanonicalAssignment a)
    (hmod : (binaryBody col).eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]) :
    a col = 0 ∨ a col = 1 := by
  have hev : (binaryBody col).eval a = a col * (a col - 1) := by
    simp only [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
    ring
  rw [hev] at hmod
  have hd : (2013265921 : Int) ∣ a col * (a col - 1) := by
    simpa [BABYBEAR_MODULUS] using Int.modEq_zero_iff_dvd.mp hmod
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    left
    omega
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    right
    omega

theorem score_bit_body_mem (participant option : Fin 4) (bit : Fin 2) :
    binaryBody (SCORE_BIT participant.val option.val bit.val) ∈ semanticBodies := by
  fin_cases participant <;> fin_cases option <;> fin_cases bit <;> decide

theorem select_body_mem (option : Fin 4) :
    binaryBody (SELECT option.val) ∈ semanticBodies := by
  fin_cases option <;> decide

theorem max_diff_bit_body_mem (option : Fin 4) (bit : Fin 4) :
    binaryBody (MAX_DIFF_BIT option.val bit.val) ∈ semanticBodies := by
  fin_cases option <;> fin_cases bit <;> decide

theorem low_slack_bit_body_mem (option : Fin 4) (bit : Fin 4) :
    binaryBody (LOW_SLACK_BIT option.val bit.val) ∈ semanticBodies := by
  fin_cases option <;> fin_cases bit <;> decide

structure DecodedPrivateBits (a : Assignment) : Prop where
  score : ∀ participant option : Fin 4, ∀ bit : Fin 2,
    a (SCORE_BIT participant.val option.val bit.val) = 0 ∨
      a (SCORE_BIT participant.val option.val bit.val) = 1
  select : ∀ option : Fin 4,
    a (SELECT option.val) = 0 ∨ a (SELECT option.val) = 1
  maxDiff : ∀ option bit : Fin 4,
    a (MAX_DIFF_BIT option.val bit.val) = 0 ∨
      a (MAX_DIFF_BIT option.val bit.val) = 1
  lowSlack : ∀ option bit : Fin 4,
    a (LOW_SLACK_BIT option.val bit.val) = 0 ∨
      a (LOW_SLACK_BIT option.val bit.val) = 1

/-- **BITHOOD IS CLOSED FROM THE DEPLOYED DESCRIPTOR.** Every score,
winner-selector, max-difference, and lowest-index slack bit is an actual integer
`0/1` in any canonical satisfying trace. -/
theorem privatePreferenceN4K4_private_bits_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    DecodedPrivateBits a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro participant option bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (score_bit_body_mem participant option bit))
  · intro option
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (select_body_mem option))
  · intro option bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (max_diff_bit_body_mem option bit))
  · intro option bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (low_slack_bit_body_mem option bit))

/-- Two canonical representatives of one BabyBear residue are the same integer. -/
theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD BABYBEAR_MODULUS])
    (hx : 0 ≤ x ∧ x < BABYBEAR_MODULUS)
    (hy : 0 ≤ y ∧ y < BABYBEAR_MODULUS) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx hy
  omega

theorem score_recompose_body_mem (participant option : Fin 4) :
    recompose (SCORE participant.val option.val)
      (SCORE_BIT participant.val option.val) SCORE_BITS ∈ semanticBodies := by
  fin_cases participant <;> fin_cases option <;> decide

theorem max_diff_recompose_body_mem (option : Fin 4) :
    recompose (MAX_DIFF option.val) (MAX_DIFF_BIT option.val) TOTAL_BITS ∈ semanticBodies := by
  fin_cases option <;> decide

theorem low_slack_recompose_body_mem (option : Fin 4) :
    recompose (LOW_SLACK option.val) (LOW_SLACK_BIT option.val) TOTAL_BITS ∈ semanticBodies := by
  fin_cases option <;> decide

/-- The score recompose gate is exact over integers once its two bits have been
decoded.  In particular every private score column is honestly in `[0,3]`. -/
theorem score_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant option : Fin 4) :
    a (SCORE participant.val option.val) =
      a (SCORE_BIT participant.val option.val 0) +
        2 * a (SCORE_BIT participant.val option.val 1) := by
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.score participant option 0
  have hb1 := hbits.score participant option 1
  have hgate := semantic_gate_vanishes hsat (score_recompose_body_mem participant option)
  have hres :
      (a (SCORE_BIT participant.val option.val 0) +
          2 * a (SCORE_BIT participant.val option.val 1)) -
        a (SCORE participant.val option.val) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, weighted, sub, neg, mul, add, v, c, SCORE_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg] using hgate
  have hcong :
      a (SCORE_BIT participant.val option.val 0) +
          2 * a (SCORE_BIT participant.val option.val 1) ≡
        a (SCORE participant.val option.val) [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a (SCORE participant.val option.val))
  have hsmall :
      0 ≤ a (SCORE_BIT participant.val option.val 0) +
          2 * a (SCORE_BIT participant.val option.val 1) ∧
      a (SCORE_BIT participant.val option.val 0) +
          2 * a (SCORE_BIT participant.val option.val 1) < BABYBEAR_MODULUS := by
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      simp_all [BABYBEAR_MODULUS]
  exact (eq_of_modEq_of_canonical hcong hsmall
    (hcanon (SCORE participant.val option.val))).symm

theorem score_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant option : Fin 4) :
    0 ≤ a (SCORE participant.val option.val) ∧
      a (SCORE participant.val option.val) < 4 := by
  rw [score_recompose_exact hcanon hsat participant option]
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.score participant option 0
  have hb1 := hbits.score participant option 1
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;> simp_all

/-- Generic exact four-bit recompose for the two bounded difference families. -/
theorem four_bit_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (col : Nat) (bit : Nat → Nat)
    (hbody : recompose col bit TOTAL_BITS ∈ semanticBodies)
    (hbits : ∀ b : Fin 4, a (bit b.val) = 0 ∨ a (bit b.val) = 1) :
    a col = a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) := by
  have hb0 := hbits 0; have hb1 := hbits 1
  have hb2 := hbits 2; have hb3 := hbits 3
  have hgate := semantic_gate_vanishes hsat hbody
  have hres :
      (a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3)) - a col ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, weighted, sub, neg, mul, add, v, c, TOTAL_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) ≡
        a col [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a col)
  have hsmall :
      0 ≤ a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) ∧
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) <
        BABYBEAR_MODULUS := by
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
      simp_all [BABYBEAR_MODULUS]
  exact (eq_of_modEq_of_canonical hcong hsmall (hcanon col)).symm

theorem max_diff_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    a (MAX_DIFF option.val) =
      a (MAX_DIFF_BIT option.val 0) + 2 * a (MAX_DIFF_BIT option.val 1) +
      4 * a (MAX_DIFF_BIT option.val 2) + 8 * a (MAX_DIFF_BIT option.val 3) := by
  apply four_bit_recompose_exact hcanon hsat
    (MAX_DIFF option.val) (MAX_DIFF_BIT option.val)
    (max_diff_recompose_body_mem option)
  exact (privatePreferenceN4K4_private_bits_decoded hcanon hsat).maxDiff option

theorem low_slack_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    a (LOW_SLACK option.val) =
      a (LOW_SLACK_BIT option.val 0) + 2 * a (LOW_SLACK_BIT option.val 1) +
      4 * a (LOW_SLACK_BIT option.val 2) + 8 * a (LOW_SLACK_BIT option.val 3) := by
  apply four_bit_recompose_exact hcanon hsat
    (LOW_SLACK option.val) (LOW_SLACK_BIT option.val)
    (low_slack_recompose_body_mem option)
  exact (privatePreferenceN4K4_private_bits_decoded hcanon hsat).lowSlack option

/-! ## 5. Full affine decode. -/

/-- Total, proof-independent score decoder. The `% 4` is only a totalization;
`decoded_score_value` proves it disappears on every canonical satisfying trace. -/
def decodedScore (a : Assignment) (participant option : Fin 4) : Fin 4 :=
  ⟨(a (SCORE participant.val option.val)).toNat % 4, Nat.mod_lt _ (by decide)⟩

def decodedWitness (a : Assignment) : PrivateWitness where
  scores := decodedScore a
  blinding := fun lane => a (BLINDING lane.val)

def columnPublic (a : Assignment) : PublicStatement where
  session := a SESSION
  rule := a RULE
  ballotRoot := fun lane => a (ROOT lane.val)
  winner := (a WINNER).toNat

def piPublic (pis : Assignment) : PublicStatement where
  session := pis 0
  rule := pis 1
  ballotRoot := fun lane => pis (2 + lane.val)
  winner := (pis 10).toNat

def permHash8 (permOut : List Int → List Int) (xs : List Int) (lane : Fin 8) : Int :=
  (permOut xs).getD lane.val 0

theorem decoded_score_value
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant option : Fin 4) :
    ((decodedWitness a).scores participant option).val =
      (a (SCORE participant.val option.val)).toNat := by
  simp only [decodedWitness, decodedScore]
  apply Nat.mod_eq_of_lt
  have h := score_column_bounds hcanon hsat participant option
  exact (Int.toNat_lt h.1).2 h.2

theorem decoded_score_coe
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant option : Fin 4) :
    (((decodedWitness a).scores participant option).val : Int) =
      a (SCORE participant.val option.val) := by
  rw [decoded_score_value hcanon hsat]
  exact Int.toNat_of_nonneg (score_column_bounds hcanon hsat participant option).1

theorem decoded_blinding_canonical (a : Assignment) (hcanon : CanonicalAssignment a) :
    CanonicalBlinding (decodedWitness a) := by
  intro lane
  simpa [decodedWitness, BLINDING, BABYBEAR_MODULUS] using hcanon (BLINDING lane.val)

theorem rule_body_mem : sub (v RULE) (c RULE_ID) ∈ semanticBodies := by decide

theorem total_body_mem (option : Fin 4) :
    sub (v (TOTAL option.val)) (totalExpr option.val) ∈ semanticBodies := by
  fin_cases option <;> decide

theorem packed_low_body_mem :
    sub (v PACKED_LOW) (add (ballotPackExpr 0) (weighted 256 (ballotPackExpr 1))) ∈
      semanticBodies := by decide

theorem packed_high_body_mem :
    sub (v PACKED_HIGH) (add (ballotPackExpr 2) (weighted 256 (ballotPackExpr 3))) ∈
      semanticBodies := by decide

theorem rule_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a RULE = RULE_ID := by
  have hgate := semantic_gate_vanishes hsat rule_body_mem
  have hres : a RULE - RULE_ID ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, ← sub_eq_add_neg] using hgate
  have hcong : a RULE ≡ RULE_ID [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right RULE_ID
  exact eq_of_modEq_of_canonical hcong (hcanon RULE) (by
    norm_num [RULE_ID, BABYBEAR_MODULUS])

theorem total_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    a (TOTAL option.val) =
      a (SCORE 0 option.val) + a (SCORE 1 option.val) +
        a (SCORE 2 option.val) + a (SCORE 3 option.val) := by
  have hs0 : 0 ≤ a (SCORE 0 option.val) ∧ a (SCORE 0 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (0 : Fin 4) option
  have hs1 : 0 ≤ a (SCORE 1 option.val) ∧ a (SCORE 1 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (1 : Fin 4) option
  have hs2 : 0 ≤ a (SCORE 2 option.val) ∧ a (SCORE 2 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (2 : Fin 4) option
  have hs3 : 0 ≤ a (SCORE 3 option.val) ∧ a (SCORE 3 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (3 : Fin 4) option
  have hgate := semantic_gate_vanishes hsat (total_body_mem option)
  have hres :
      a (TOTAL option.val) -
        (a (SCORE 0 option.val) + a (SCORE 1 option.val) +
          a (SCORE 2 option.val) + a (SCORE 3 option.val)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [totalExpr, PARTICIPANT_COUNT, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (TOTAL option.val) ≡
        a (SCORE 0 option.val) + a (SCORE 1 option.val) +
          a (SCORE 2 option.val) + a (SCORE 3 option.val)
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (SCORE 0 option.val) + a (SCORE 1 option.val) +
        a (SCORE 2 option.val) + a (SCORE 3 option.val))
  apply eq_of_modEq_of_canonical hcong (hcanon (TOTAL option.val))
  simp only [BABYBEAR_MODULUS]
  omega

theorem aggregateScore_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    aggregateScore (decodedWitness a) option.val = a (TOTAL option.val) := by
  rw [total_column_exact hcanon hsat option]
  simp [aggregateScore, option.isLt, decoded_score_coe hcanon hsat,
    List.ofFn_succ, add_assoc]

def ballotPackCols (a : Assignment) (participant : Nat) : Int :=
  a (SCORE participant 0) + 4 * a (SCORE participant 1) +
    16 * a (SCORE participant 2) + 64 * a (SCORE participant 3)

theorem ballotPackCols_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant : Fin 4) :
    0 ≤ ballotPackCols a participant.val ∧ ballotPackCols a participant.val < 256 := by
  have hs0 : 0 ≤ a (SCORE participant.val 0) ∧ a (SCORE participant.val 0) < 4 := by
    simpa using score_column_bounds hcanon hsat participant (0 : Fin 4)
  have hs1 : 0 ≤ a (SCORE participant.val 1) ∧ a (SCORE participant.val 1) < 4 := by
    simpa using score_column_bounds hcanon hsat participant (1 : Fin 4)
  have hs2 : 0 ≤ a (SCORE participant.val 2) ∧ a (SCORE participant.val 2) < 4 := by
    simpa using score_column_bounds hcanon hsat participant (2 : Fin 4)
  have hs3 : 0 ≤ a (SCORE participant.val 3) ∧ a (SCORE participant.val 3) < 4 := by
    simpa using score_column_bounds hcanon hsat participant (3 : Fin 4)
  simp only [ballotPackCols]
  omega

theorem ballotPack_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (participant : Fin 4) :
    ballotPack (decodedWitness a) participant = ballotPackCols a participant.val := by
  simp [ballotPack, ballotPackOf, ballotPackCols, decoded_score_coe hcanon hsat]

theorem packed_low_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a PACKED_LOW = ballotPackCols a 0 + 256 * ballotPackCols a 1 := by
  have hb0 : 0 ≤ ballotPackCols a 0 ∧ ballotPackCols a 0 < 256 := by
    simpa using ballotPackCols_bounds hcanon hsat (0 : Fin 4)
  have hb1 : 0 ≤ ballotPackCols a 1 ∧ ballotPackCols a 1 < 256 := by
    simpa using ballotPackCols_bounds hcanon hsat (1 : Fin 4)
  have hgate := semantic_gate_vanishes hsat packed_low_body_mem
  have hres :
      a PACKED_LOW - (ballotPackCols a 0 + 256 * ballotPackCols a 1) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [ballotPackExpr, ballotPackCols, OPTION_COUNT, weighted, sub, neg, mul, add, v, c,
      EmittedExpr.eval, List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [ballotPackCols, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a PACKED_LOW ≡ ballotPackCols a 0 + 256 * ballotPackCols a 1
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (ballotPackCols a 0 + 256 * ballotPackCols a 1)
  apply eq_of_modEq_of_canonical hcong (hcanon PACKED_LOW)
  simp only [BABYBEAR_MODULUS]
  omega

theorem packed_high_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a PACKED_HIGH = ballotPackCols a 2 + 256 * ballotPackCols a 3 := by
  have hb2 : 0 ≤ ballotPackCols a 2 ∧ ballotPackCols a 2 < 256 := by
    simpa using ballotPackCols_bounds hcanon hsat (2 : Fin 4)
  have hb3 : 0 ≤ ballotPackCols a 3 ∧ ballotPackCols a 3 < 256 := by
    simpa using ballotPackCols_bounds hcanon hsat (3 : Fin 4)
  have hgate := semantic_gate_vanishes hsat packed_high_body_mem
  have hres :
      a PACKED_HIGH - (ballotPackCols a 2 + 256 * ballotPackCols a 3) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [ballotPackExpr, ballotPackCols, OPTION_COUNT, weighted, sub, neg, mul, add, v, c,
      EmittedExpr.eval, List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [ballotPackCols, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a PACKED_HIGH ≡ ballotPackCols a 2 + 256 * ballotPackCols a 3
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (ballotPackCols a 2 + 256 * ballotPackCols a 3)
  apply eq_of_modEq_of_canonical hcong (hcanon PACKED_HIGH)
  simp only [BABYBEAR_MODULUS]
  omega

theorem packed_columns_decode
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a PACKED_LOW = packedLow (decodedWitness a) ∧
      a PACKED_HIGH = packedHigh (decodedWitness a) := by
  constructor
  · have h0 := ballotPack_decoded hcanon hsat (0 : Fin 4)
    have h1 := ballotPack_decoded hcanon hsat (1 : Fin 4)
    have h0' : ballotPack (decodedWitness a) 0 = ballotPackCols a 0 := by simpa using h0
    have h1' : ballotPack (decodedWitness a) 1 = ballotPackCols a 1 := by simpa using h1
    rw [packed_low_column_exact hcanon hsat, packedLow, h0', h1']
  · have h2 := ballotPack_decoded hcanon hsat (2 : Fin 4)
    have h3 := ballotPack_decoded hcanon hsat (3 : Fin 4)
    have h2' : ballotPack (decodedWitness a) 2 = ballotPackCols a 2 := by simpa using h2
    have h3' : ballotPack (decodedWitness a) 3 = ballotPackCols a 3 := by simpa using h3
    rw [packed_high_column_exact hcanon hsat, packedHigh, h2', h3']

theorem select_sum_body_mem :
    sub (sumE ((List.range OPTION_COUNT).map (fun option => v (SELECT option)))) (c 1) ∈
      semanticBodies := by decide

theorem winner_body_mem :
    sub (v WINNER)
      (sumE ((List.range OPTION_COUNT).map
        (fun (option : Nat) => weighted (option : Int) (v (SELECT option))))) ∈
      semanticBodies := by decide

theorem max_score_body_mem :
    sub (v MAX_SCORE)
      (sumE ((List.range OPTION_COUNT).map
        (fun option => mul (v (SELECT option)) (v (TOTAL option))))) ∈ semanticBodies := by decide

theorem max_diff_relation_body_mem (option : Fin 4) :
    sub (v (MAX_DIFF option.val)) (sub (v MAX_SCORE) (v (TOTAL option.val))) ∈
      semanticBodies := by
  fin_cases option <;> decide

theorem low_slack_relation_body_mem (option : Fin 4) :
    sub (v (LOW_SLACK option.val))
      (sub (v (MAX_DIFF option.val)) (laterSelected option.val)) ∈ semanticBodies := by
  fin_cases option <;> decide

theorem total_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    0 ≤ a (TOTAL option.val) ∧ a (TOTAL option.val) ≤ 12 := by
  rw [total_column_exact hcanon hsat option]
  have hs0 : 0 ≤ a (SCORE 0 option.val) ∧ a (SCORE 0 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (0 : Fin 4) option
  have hs1 : 0 ≤ a (SCORE 1 option.val) ∧ a (SCORE 1 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (1 : Fin 4) option
  have hs2 : 0 ≤ a (SCORE 2 option.val) ∧ a (SCORE 2 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (2 : Fin 4) option
  have hs3 : 0 ≤ a (SCORE 3 option.val) ∧ a (SCORE 3 option.val) < 4 := by
    simpa using score_column_bounds hcanon hsat (3 : Fin 4) option
  omega

theorem max_diff_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    0 ≤ a (MAX_DIFF option.val) ∧ a (MAX_DIFF option.val) ≤ 15 := by
  rw [max_diff_recompose_exact hcanon hsat option]
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.maxDiff option 0; have hb1 := hbits.maxDiff option 1
  have hb2 := hbits.maxDiff option 2; have hb3 := hbits.maxDiff option 3
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;> simp_all

theorem low_slack_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    0 ≤ a (LOW_SLACK option.val) ∧ a (LOW_SLACK option.val) ≤ 15 := by
  rw [low_slack_recompose_exact hcanon hsat option]
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.lowSlack option 0; have hb1 := hbits.lowSlack option 1
  have hb2 := hbits.lowSlack option 2; have hb3 := hbits.lowSlack option 3
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;> simp_all

theorem select_sum_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3) = 1 := by
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.select 0; have hb1 := hbits.select 1
  have hb2 := hbits.select 2; have hb3 := hbits.select 3
  have hgate := semantic_gate_vanishes hsat select_sum_body_mem
  have hres :
      (a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3)) - 1 ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [OPTION_COUNT, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3) ≡
      1 [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right 1
  apply eq_of_modEq_of_canonical hcong
  · rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
      simp_all [BABYBEAR_MODULUS]
  · norm_num [BABYBEAR_MODULUS]

theorem winner_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a WINNER = a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3) := by
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb1 := hbits.select 1; have hb2 := hbits.select 2; have hb3 := hbits.select 3
  have hgate := semantic_gate_vanishes hsat winner_body_mem
  have hres :
      a WINNER - (a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [OPTION_COUNT, weighted, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a WINNER ≡ a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3))
  apply eq_of_modEq_of_canonical hcong (hcanon WINNER)
  rcases hb1 with hb1 | hb1 <;> rcases hb2 with hb2 | hb2 <;>
    rcases hb3 with hb3 | hb3 <;> simp_all [BABYBEAR_MODULUS]

theorem max_score_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    a MAX_SCORE =
      a (SELECT 0) * a (TOTAL 0) + a (SELECT 1) * a (TOTAL 1) +
        a (SELECT 2) * a (TOTAL 2) + a (SELECT 3) * a (TOTAL 3) := by
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hs0 := hbits.select 0; have hs1 := hbits.select 1
  have hs2 := hbits.select 2; have hs3 := hbits.select 3
  have ht0 : 0 ≤ a (TOTAL 0) ∧ a (TOTAL 0) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (0 : Fin 4)
  have ht1 : 0 ≤ a (TOTAL 1) ∧ a (TOTAL 1) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (1 : Fin 4)
  have ht2 : 0 ≤ a (TOTAL 2) ∧ a (TOTAL 2) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (2 : Fin 4)
  have ht3 : 0 ≤ a (TOTAL 3) ∧ a (TOTAL 3) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (3 : Fin 4)
  have hgate := semantic_gate_vanishes hsat max_score_body_mem
  have hres :
      a MAX_SCORE -
        (a (SELECT 0) * a (TOTAL 0) + a (SELECT 1) * a (TOTAL 1) +
          a (SELECT 2) * a (TOTAL 2) + a (SELECT 3) * a (TOTAL 3)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [OPTION_COUNT, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a MAX_SCORE ≡
      a (SELECT 0) * a (TOTAL 0) + a (SELECT 1) * a (TOTAL 1) +
        a (SELECT 2) * a (TOTAL 2) + a (SELECT 3) * a (TOTAL 3)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (SELECT 0) * a (TOTAL 0) + a (SELECT 1) * a (TOTAL 1) +
        a (SELECT 2) * a (TOTAL 2) + a (SELECT 3) * a (TOTAL 3))
  apply eq_of_modEq_of_canonical hcong (hcanon MAX_SCORE)
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
    rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;>
    simp_all [BABYBEAR_MODULUS] <;> omega

theorem max_diff_relation_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    a (MAX_DIFF option.val) = a MAX_SCORE - a (TOTAL option.val) := by
  have hd := max_diff_column_bounds hcanon hsat option
  have ht := total_column_bounds hcanon hsat option
  have hsel := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hs0 := hsel.select 0; have hs1 := hsel.select 1
  have hs2 := hsel.select 2; have hs3 := hsel.select 3
  have hsum := select_sum_exact hcanon hsat
  have hm := max_score_column_exact hcanon hsat
  have ht0 : 0 ≤ a (TOTAL 0) ∧ a (TOTAL 0) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (0 : Fin 4)
  have ht1 : 0 ≤ a (TOTAL 1) ∧ a (TOTAL 1) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (1 : Fin 4)
  have ht2 : 0 ≤ a (TOTAL 2) ∧ a (TOTAL 2) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (2 : Fin 4)
  have ht3 : 0 ≤ a (TOTAL 3) ∧ a (TOTAL 3) ≤ 12 := by
    simpa using total_column_bounds hcanon hsat (3 : Fin 4)
  have hmBound : 0 ≤ a MAX_SCORE ∧ a MAX_SCORE ≤ 12 := by
    rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
      rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;> simp_all
  have hgate := semantic_gate_vanishes hsat (max_diff_relation_body_mem option)
  have hres :
      a (MAX_DIFF option.val) - (a MAX_SCORE - a (TOTAL option.val)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  apply sub_eq_zero.mp
  exact eq_zero_of_modEq_zero_of_window hres (by
    simp only [InZeroResidueWindow, BABYBEAR_MODULUS]
    omega)

theorem low_slack_relation_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    (option : Fin 4) :
    a (LOW_SLACK option.val) =
      a (MAX_DIFF option.val) - (laterSelected option.val).eval a := by
  have hl := low_slack_column_bounds hcanon hsat option
  have hd := max_diff_column_bounds hcanon hsat option
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hs0 := hbits.select 0; have hs1 := hbits.select 1
  have hs2 := hbits.select 2; have hs3 := hbits.select 3
  have hlater : 0 ≤ (laterSelected option.val).eval a ∧
      (laterSelected option.val).eval a ≤ 3 := by
    fin_cases option <;>
      norm_num [laterSelected, OPTION_COUNT, sub, neg, mul, add, v, c,
        EmittedExpr.eval, List.range_succ, Function.comp_apply, add_assoc] <;>
      rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
      rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;> simp_all
  have hgate := semantic_gate_vanishes hsat (low_slack_relation_body_mem option)
  have hres :
      a (LOW_SLACK option.val) -
        (a (MAX_DIFF option.val) - (laterSelected option.val).eval a) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  apply sub_eq_zero.mp
  exact eq_zero_of_modEq_zero_of_window hres (by
    simp only [InZeroResidueWindow, BABYBEAR_MODULUS]
    omega)

/-- The decoded public winner column is the semantic lowest-index aggregate
argmax of the decoded private ballots. -/
theorem column_winner_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    (columnPublic a).winner = winner (decodedWitness a) := by
  have hbits := privatePreferenceN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.select (0 : Fin 4); have hb1 := hbits.select (1 : Fin 4)
  have hb2 := hbits.select (2 : Fin 4); have hb3 := hbits.select (3 : Fin 4)
  have hsum := select_sum_exact hcanon hsat
  have hwin := winner_column_exact hcanon hsat
  have hmax := max_score_column_exact hcanon hsat
  have hd0 := max_diff_relation_exact hcanon hsat (0 : Fin 4)
  have hd1 := max_diff_relation_exact hcanon hsat (1 : Fin 4)
  have hd2 := max_diff_relation_exact hcanon hsat (2 : Fin 4)
  have hd3 := max_diff_relation_exact hcanon hsat (3 : Fin 4)
  have hdb0 := max_diff_column_bounds hcanon hsat (0 : Fin 4)
  have hdb1 := max_diff_column_bounds hcanon hsat (1 : Fin 4)
  have hdb2 := max_diff_column_bounds hcanon hsat (2 : Fin 4)
  have hdb3 := max_diff_column_bounds hcanon hsat (3 : Fin 4)
  have hl0 := low_slack_relation_exact hcanon hsat (0 : Fin 4)
  have hl1 := low_slack_relation_exact hcanon hsat (1 : Fin 4)
  have hl2 := low_slack_relation_exact hcanon hsat (2 : Fin 4)
  have hl3 := low_slack_relation_exact hcanon hsat (3 : Fin 4)
  have hlb0 := low_slack_column_bounds hcanon hsat (0 : Fin 4)
  have hlb1 := low_slack_column_bounds hcanon hsat (1 : Fin 4)
  have hlb2 := low_slack_column_bounds hcanon hsat (2 : Fin 4)
  have hlb3 := low_slack_column_bounds hcanon hsat (3 : Fin 4)
  have ha0 := aggregateScore_decoded hcanon hsat (0 : Fin 4)
  have ha1 := aggregateScore_decoded hcanon hsat (1 : Fin 4)
  have ha2 := aggregateScore_decoded hcanon hsat (2 : Fin 4)
  have ha3 := aggregateScore_decoded hcanon hsat (3 : Fin 4)
  norm_num [laterSelected, sumE, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply, add_assoc] at hl0 hl1 hl2 hl3
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;> simp_all
  all_goals
    symm
    apply winner_eq_of_optimal_and_lowest
    · simp [columnPublic, hwin, OPTION_COUNT]
    · intro q hq
      simp only [OPTION_COUNT] at hq
      have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [columnPublic]
    · intro q hq
      have hcases : q = 0 ∨ q = 1 ∨ q = 2 := by
        change q < (a WINNER).toNat at hq
        rw [hwin] at hq
        omega
      rcases hcases with rfl | rfl | rfl <;> simp_all [columnPublic] <;> omega

/-- The emitted 16-lane Poseidon seed is exactly the semantic commitment
preimage of the decoded witness. -/
theorem root_input_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    rootInputExprs.map (·.eval a) =
      rootPreimage (columnPublic a).session (decodedWitness a) := by
  have hp := packed_columns_decode hcanon hsat
  have hr := rule_column_exact hcanon hsat
  simp only [rootInputExprs, rootPreimage, columnPublic, decodedWitness, BLINDING,
    ROOT_DOMAIN_TAG, List.ofFn_succ, v, c, DIGEST_WIDTH, BLINDING_BASE]
  norm_num [List.range_succ, Function.comp_apply, EmittedExpr.eval]
  exact ⟨hr, by simpa [decodedWitness, BLINDING, BLINDING_BASE] using hp.1,
    by simpa [decodedWitness, BLINDING, BLINDING_BASE] using hp.2⟩

/-- Chip-table soundness identifies every emitted digest column with the
semantic full-width ballot root. -/
theorem column_root_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    (columnPublic a).ballotRoot =
      ballotRoot (permHash8 permOut) (columnPublic a).session (decodedWitness a) := by
  have hwide := wide_root_lookup_sound permOut hChip hsat
  rw [root_input_decoded hcanon hsat] at hwide
  funext lane
  have h := congrArg (fun xs : List Int => xs.getD lane.val 0) hwide
  fin_cases lane <;>
    simpa [columnPublic, ballotRoot, permHash8, rootDigestCols,
      DIGEST_WIDTH, ROOT, List.range_succ] using h

/-- Canonical satisfying trace columns themselves form an accepted semantic
private-preference statement. -/
theorem privatePreferenceN4K4_column_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Accepts (permHash8 permOut) (columnPublic a) (decodedWitness a) := by
  refine ⟨decoded_blinding_canonical a hcanon, ?_, ?_, ?_⟩
  · simpa [columnPublic] using rule_column_exact hcanon hsat
  · exact column_root_semantic permOut hcanon hChip hsat
  · exact column_winner_semantic hcanon hsat

/-- With canonical representatives on both sides of the public bindings, the
external PI statement is exactly the public statement decoded from the trace.
The PI canonicality premise is necessary because `Satisfied2` pins residues. -/
theorem pi_public_eq_column
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    piPublic pis = columnPublic a := by
  have hs : pis 0 = a SESSION :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon SESSION) (hcanonPis 0)).symm
  have hr : pis 1 = a RULE :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon RULE) (hcanonPis 1)).symm
  have hroot : (fun lane : Fin 8 => pis (2 + lane.val)) =
      fun lane => a (ROOT lane.val) := by
    funext lane
    apply (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      fin_cases lane <;>
        simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
        (hcanon (ROOT lane.val)) (hcanonPis (2 + lane.val))).symm
  have hwinner : pis 10 = a WINNER :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon WINNER) (hcanonPis 10)).symm
  simp only [piPublic, columnPublic]
  rw [hs, hr, hroot, hwinner]

/-- **`PrivatePreferenceDescriptorToAccepts` is closed.** Satisfaction of the
Lean-emitted AIR, canonical trace and PI representatives, and soundness of the
wide Poseidon chip imply the exact semantic `Accepts` relation. -/
theorem privatePreferenceN4K4_descriptor_to_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Accepts (permHash8 permOut) (piPublic pis) (decodedWitness a) := by
  rw [pi_public_eq_column hcanon hcanonPis hsat]
  exact privatePreferenceN4K4_column_accepts permOut hcanon hChip hsat

#assert_all_clean [
  Dregg2.Games.PrivatePreferenceDescriptor.ballotPackOf_injective,
  Dregg2.Games.PrivatePreferenceDescriptor.packedScores_injective,
  Dregg2.Games.PrivatePreferenceDescriptor.argmaxUpto_max,
  Dregg2.Games.PrivatePreferenceDescriptor.argmaxUpto_strict_before,
  Dregg2.Games.PrivatePreferenceDescriptor.winner_eq_of_optimal_and_lowest,
  Dregg2.Games.PrivatePreferenceDescriptor.check_sound,
  Dregg2.Games.PrivatePreferenceDescriptor.two_distinct_openings_yield_root_collision,
  Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4_emitted_air_sound,
  Dregg2.Games.PrivatePreferenceDescriptor.binaryBody_zero_iff,
  Dregg2.Games.PrivatePreferenceDescriptor.semantic_gate_exact,
  Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4_private_bits_decoded,
  Dregg2.Games.PrivatePreferenceDescriptor.score_recompose_exact,
  Dregg2.Games.PrivatePreferenceDescriptor.four_bit_recompose_exact,
  Dregg2.Games.PrivatePreferenceDescriptor.column_winner_semantic,
  Dregg2.Games.PrivatePreferenceDescriptor.root_input_decoded,
  Dregg2.Games.PrivatePreferenceDescriptor.column_root_semantic,
  Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4_column_accepts,
  Dregg2.Games.PrivatePreferenceDescriptor.pi_public_eq_column,
  Dregg2.Games.PrivatePreferenceDescriptor.privatePreferenceN4K4_descriptor_to_accepts]

end Dregg2.Games.PrivatePreferenceDescriptor
