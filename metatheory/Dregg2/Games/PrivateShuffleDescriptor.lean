/-
# Dregg2.Games.PrivateShuffleDescriptor

Lean author for a fixed-eight private shuffle/deal proof organ.

The private witness assigns the canonical cards `0..7` to the public seat
indices `0..7`.  The public statement is only `(session, rule, root8)`.  Exact
permutation correctness is part of the relation: the assignment is bijective,
so no card is duplicated and no card is omitted.

Each seat has its own full-arity-16 Poseidon2 leaf:

`[domain, session, rule, seat, card, blind0..blind7, 0, 0, 0]`.

The eight leaf digests are folded through seven full-width `node8`
compressions.  This permits a recipient to receive one card, its eight-felt
blind, and a depth-three sibling path without learning any other card.

This relation proves permutation correctness, NOT unbiased randomness.  A
coordinator may choose any valid permutation.  Distributed randomness, an MPC
shuffle, or a verifiable mix is a separate protocol layer.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Games.PrivateShuffleDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact semantic relation. -/

def CARD_COUNT : Nat := 8
def SEAT_COUNT : Nat := 8
def DIGEST_WIDTH : Nat := 8
def BABYBEAR_MODULUS : Int := 2013265921

/-- ASCII `SHF8`, the leaf-commitment domain for this exact framing. -/
def LEAF_DOMAIN_TAG : Int := 1397245496

/-- ASCII `PER8`, the fixed `N=8`, canonical-card permutation rule. -/
def RULE_ID : Int := 1346720312

structure PrivateWitness where
  cards : Fin 8 → Fin 8
  blinding : Fin 8 → Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  dealRoot : Fin 8 → Int
  deriving DecidableEq, Repr

def CanonicalBlinding (w : PrivateWitness) : Prop :=
  ∀ seat lane, 0 ≤ w.blinding seat lane ∧ w.blinding seat lane < BABYBEAR_MODULUS

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  (List.finRange 8).all fun seat =>
    (List.finRange 8).all fun lane =>
      decide (0 ≤ w.blinding seat lane ∧ w.blinding seat lane < BABYBEAR_MODULUS)

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]

/-- Exact shuffle correctness.  Because source and target are both `Fin 8`,
injectivity already forces surjectivity; we retain both faces explicitly. -/
def ExactPermutation (w : PrivateWitness) : Prop := Function.Bijective w.cards

def exactPermutationCheck (w : PrivateWitness) : Bool :=
  decide (Function.Injective w.cards)

theorem exactPermutationCheck_iff (w : PrivateWitness) :
    exactPermutationCheck w = true ↔ ExactPermutation w := by
  rw [exactPermutationCheck, decide_eq_true_eq]
  exact Finite.injective_iff_bijective

theorem exactPermutation_no_duplicate {w : PrivateWitness} (h : ExactPermutation w) :
    Function.Injective w.cards := h.1

theorem exactPermutation_no_omission {w : PrivateWitness} (h : ExactPermutation w) :
    Function.Surjective w.cards := h.2

/-- Exactly sixteen inputs.  The explicit three-zero suffix is framing, not
unused capacity: arity 16 selects the full-width chip seed mode. -/
def leafPreimage (session : Int) (w : PrivateWitness) (seat : Fin 8) : List Int :=
  [LEAF_DOMAIN_TAG, session, RULE_ID, seat.val, (w.cards seat).val] ++
    List.ofFn (w.blinding seat) ++ [0, 0, 0]

def leafDigest (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (seat : Fin 8) : Fin 8 → Int :=
  hash8 (leafPreimage session w seat)

/-- Full-width internal compression: `perm(left8 ++ right8)[0..8]`. -/
def node8 (hash8 : List Int → Fin 8 → Int)
    (left right : Fin 8 → Int) : Fin 8 → Int :=
  hash8 (List.ofFn left ++ List.ofFn right)

def level1 (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (pair : Fin 4) : Fin 8 → Int :=
  node8 hash8
    (leafDigest hash8 session w ⟨2 * pair.val, by omega⟩)
    (leafDigest hash8 session w ⟨2 * pair.val + 1, by omega⟩)

def level2 (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) (pair : Fin 2) : Fin 8 → Int :=
  node8 hash8
    (level1 hash8 session w ⟨2 * pair.val, by omega⟩)
    (level1 hash8 session w ⟨2 * pair.val + 1, by omega⟩)

def dealRoot (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) : Fin 8 → Int :=
  node8 hash8 (level2 hash8 session w 0) (level2 hash8 session w 1)

def RootCollision (hash8 : List Int → Fin 8 → Int) (session : Int)
    (left right : PrivateWitness) : Prop :=
  (left.cards ≠ right.cards ∨ left.blinding ≠ right.blinding) ∧
    dealRoot hash8 session left = dealRoot hash8 session right

def Accepts (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  ExactPermutation w ∧
  pub.rule = RULE_ID ∧
  pub.dealRoot = dealRoot hash8 pub.session w

def check (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  exactPermutationCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.dealRoot == dealRoot hash8 pub.session w)

theorem check_iff (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindingCheck_iff, exactPermutationCheck_iff, and_assoc]

theorem check_sound {hash8 : List Int → Fin 8 → Int}
    {pub : PublicStatement} {w : PrivateWitness}
    (h : check hash8 pub w = true) :
    CanonicalBlinding w ∧
    Function.Injective w.cards ∧
    Function.Surjective w.cards ∧
    pub.rule = RULE_ID ∧
    pub.dealRoot = dealRoot hash8 pub.session w := by
  rcases (check_iff hash8 pub w).mp h with ⟨hb, hp, hr, hroot⟩
  exact ⟨hb, hp.1, hp.2, hr, hroot⟩

theorem two_distinct_openings_yield_root_collision
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement}
    {left right : PrivateWitness}
    (hl : check hash8 pub left = true) (hr : check hash8 pub right = true)
    (hdiff : left.cards ≠ right.cards ∨ left.blinding ≠ right.blinding) :
    RootCollision hash8 pub.session left right := by
  have al := (check_iff hash8 pub left).mp hl
  have ar := (check_iff hash8 pub right).mp hr
  exact ⟨hdiff, al.2.2.2.symm.trans ar.2.2.2⟩

/-! The bias boundary is deliberately formal and non-vacuous: the relation
admits more than one valid permutation.  It says nothing about the probability
with which a producer chooses among them. -/

def identityWitness : PrivateWitness where
  cards := fun seat => seat
  blinding := fun seat lane => 1000 + 8 * seat.val + lane.val

def swap01 : Equiv.Perm (Fin 8) := Equiv.swap 0 1

def swap01Witness : PrivateWitness where
  cards := swap01
  blinding := identityWitness.blinding

theorem coordinator_choice_bias_residual :
    ∃ left right : PrivateWitness,
      ExactPermutation left ∧ ExactPermutation right ∧ left.cards ≠ right.cards := by
  refine ⟨identityWitness, swap01Witness, ?_, ?_, ?_⟩
  · exact ⟨Function.injective_id, Function.surjective_id⟩
  · exact swap01.bijective
  · intro h
    have h0 := congrFun h 0
    norm_num [identityWitness, swap01Witness, swap01] at h0

def toyHash8 (xs : List Int) (lane : Fin 8) : Int :=
  (xs.zipIdx.map (fun p => ((p.2 : Int) + 1) * p.1)).sum + 17 * lane.val + 31

def identityPublic : PublicStatement where
  session := 77
  rule := RULE_ID
  dealRoot := dealRoot toyHash8 77 identityWitness

#guard (leafPreimage 77 identityWitness 0).length == 16
#guard exactPermutationCheck identityWitness
#guard exactPermutationCheck swap01Witness
#guard check toyHash8 identityPublic identityWitness
#guard !check toyHash8 identityPublic swap01Witness

/-! ## 2. Lean-authored fixed AIR descriptor. -/

def SESSION : Nat := 0
def RULE : Nat := 1
def ROOT_BASE : Nat := 2
def CARD_BASE : Nat := 10
def BLIND_BASE : Nat := 18
def SELECT_BASE : Nat := 82
def LEAF_BASE : Nat := 146
def LEVEL1_BASE : Nat := 210
def LEVEL2_BASE : Nat := 242
def TRACE_WIDTH : Nat := 258

def ROOT (lane : Nat) : Nat := ROOT_BASE + lane
def CARD (seat : Nat) : Nat := CARD_BASE + seat
def BLIND (seat lane : Nat) : Nat := BLIND_BASE + DIGEST_WIDTH * seat + lane
def SELECT (seat card : Nat) : Nat := SELECT_BASE + CARD_COUNT * seat + card
def LEAF (seat lane : Nat) : Nat := LEAF_BASE + DIGEST_WIDTH * seat + lane
def LEVEL1 (pair lane : Nat) : Nat := LEVEL1_BASE + DIGEST_WIDTH * pair + lane
def LEVEL2 (pair lane : Nat) : Nat := LEVEL2_BASE + DIGEST_WIDTH * pair + lane

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x
def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def selectorBodies : List EmittedExpr :=
  ((List.range SEAT_COUNT).flatMap fun seat =>
    (List.range CARD_COUNT).map fun card => binaryBody (SELECT seat card))

def rowOneBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).map fun seat =>
    sub (sumE ((List.range CARD_COUNT).map fun card => v (SELECT seat card))) (c 1)

def columnOneBodies : List EmittedExpr :=
  (List.range CARD_COUNT).map fun card =>
    sub (sumE ((List.range SEAT_COUNT).map fun seat => v (SELECT seat card))) (c 1)

def cardRecomposeBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).map fun seat =>
    sub (v (CARD seat))
      (sumE ((List.range CARD_COUNT).map fun (card : Nat) =>
        weighted (card : Int) (v (SELECT seat card))))

def semanticBodies : List EmittedExpr :=
  [sub (v RULE) (c RULE_ID)] ++ selectorBodies ++ rowOneBodies ++
    columnOneBodies ++ cardRecomposeBodies

def leafInputExprs (seat : Nat) : List EmittedExpr :=
  [c LEAF_DOMAIN_TAG, v SESSION, v RULE, c seat, v (CARD seat)] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (BLIND seat lane)) ++ [c 0, c 0, c 0]

def leafDigestCols (seat : Nat) : List Nat :=
  (List.range DIGEST_WIDTH).map (LEAF seat)

def digestExprs (f : Nat → Nat) : List EmittedExpr :=
  (List.range DIGEST_WIDTH).map (fun lane => v (f lane))

def digestCols (f : Nat → Nat) : List Nat :=
  (List.range DIGEST_WIDTH).map f

def leafLookups : List VmConstraint2 :=
  (List.range SEAT_COUNT).map fun seat =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN (leafInputExprs seat) (leafDigestCols seat)⟩

def level1Lookups : List VmConstraint2 :=
  (List.range 4).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (LEAF (2 * pair)) ++ digestExprs (LEAF (2 * pair + 1)))
        (digestCols (LEVEL1 pair))⟩

def level2Lookups : List VmConstraint2 :=
  (List.range 2).map fun pair =>
    .lookup ⟨TableId.poseidon2,
      chipLookupTupleN
        (digestExprs (LEVEL1 (2 * pair)) ++ digestExprs (LEVEL1 (2 * pair + 1)))
        (digestCols (LEVEL2 pair))⟩

def rootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN
      (digestExprs (LEVEL2 0) ++ digestExprs (LEVEL2 1))
      ((List.range DIGEST_WIDTH).map ROOT)⟩

def hashLookups : List VmConstraint2 :=
  leafLookups ++ level1Lookups ++ level2Lookups ++ [rootLookup]

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range DIGEST_WIDTH).map fun lane =>
    .base (.piBinding .first (ROOT lane) (2 + lane))

/-- Eight leaves + seven `node8` compressions, plus exact permutation gates.
Last-row copies close the height-one/last-row semantic escape. -/
def privateShuffleN8Descriptor : EffectVmDescriptor2 :=
  { name := "private-shuffle-n8::leaf16-node8-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 10
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privateShuffleN8Descriptor.traceWidth == 258
#guard privateShuffleN8Descriptor.piCount == 10
#guard leafLookups.length == 8
#guard level1Lookups.length == 4
#guard level2Lookups.length == 2
#guard hashLookups.length == 15
#guard semanticBodies.length == 89
#guard privateShuffleN8Descriptor.constraints.length == 15 + 2 * 89 + 10
#guard !(emitVmJson2 privateShuffleN8Descriptor).contains "1346720313"

/-! ## 3. Emitted-AIR extraction boundary.

The descriptor exposes all 15 genuine full-width chip lookups and all 89
permutation gates.  `EmittedAirFacts` extracts those modular facts.  The finite
modular-to-integer lift (binary selectors and sums at most eight, far below
BabyBear) is deliberately named rather than smuggling global field injectivity
into the theorem.
-/

def shuffleM0 : Int → Int := fun _ => 0
def shuffleF0 : Int → Int × Nat := fun _ => (0, 0)

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
    VmConstraint2.base (.gate body) ∈ privateShuffleN8Descriptor.constraints := by
  simp [privateShuffleN8Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privateShuffleN8Descriptor.constraints := by
  simp [privateShuffleN8Descriptor, hpin]

theorem hash_lookup_mem {lookup : VmConstraint2} (hlookup : lookup ∈ hashLookups) :
    lookup ∈ privateShuffleN8Descriptor.constraints := by
  simp [privateShuffleN8Descriptor, hlookup]

theorem semantic_gate_vanishes {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateShuffleN8Descriptor shuffleM0 shuffleF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem public_pin_sound {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateShuffleN8Descriptor shuffleM0 shuffleF0 []
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
    (hsat : Satisfied2 hash privateShuffleN8Descriptor shuffleM0 shuffleF0 []
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
  hashTree : ∀ (inputs : List EmittedExpr) (outputs : List Nat)
    (hadm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted inputs.length),
    VmConstraint2.lookup ⟨TableId.poseidon2, chipLookupTupleN inputs outputs hadm⟩ ∈ hashLookups →
    outputs.map a = permOut (inputs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

theorem privateShuffleN8_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateShuffleN8Descriptor shuffleM0 shuffleF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   fun _ _ hinlen hmem => chip_lookup_sound_of_mem permOut hChip hsat hinlen hmem,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

#assert_all_clean [
  Dregg2.Games.PrivateShuffleDescriptor.exactPermutationCheck_iff,
  Dregg2.Games.PrivateShuffleDescriptor.exactPermutation_no_duplicate,
  Dregg2.Games.PrivateShuffleDescriptor.exactPermutation_no_omission,
  Dregg2.Games.PrivateShuffleDescriptor.check_sound,
  Dregg2.Games.PrivateShuffleDescriptor.two_distinct_openings_yield_root_collision,
  Dregg2.Games.PrivateShuffleDescriptor.coordinator_choice_bias_residual,
  Dregg2.Games.PrivateShuffleDescriptor.privateShuffleN8_emitted_air_sound]

end Dregg2.Games.PrivateShuffleDescriptor
