/-
# Market.DarkAmmPrivateDescriptor

Lean-authored IR-v2 descriptor for one fixed, hiding AMM transition family.

The exact public ABI is `(session, rule, k, oldRoot[0..8), newRoot[0..8))`.
The private witness is `(x,y,dx,dy,oldBlind[0..8),newBlind[0..8))`; post-state
reserves are derived inside the AIR.  All four source scalars are ten-bit,
`postX` is eleven-bit, `postY` is ten-bit, both amounts are nonzero, and the
old and new products must equal the same public `k`.  Two full-arity Poseidon2
lookups implement exactly the state-commitment preimages in
`Market.DarkAmmPrivateReceipt`.

This is a Tier-1/operator-visible proof family: a hiding FRI proof conceals the
witness from proof consumers, but the process constructing the trace sees it.
It does not prove a BFV same-opening statement and does not by itself provide
no-single-viewer custody or a ledger/state-cell weld.
-/

import Market.DarkAmmPrivateReceipt
import Market.DarkBazaarPrivateDescriptor
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics
import Mathlib.Tactic

namespace Market.DarkAmmPrivateDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

def DIGEST_WIDTH : Nat := Market.DarkAmmPrivateReceipt.DIGEST_WIDTH
def RULE_ID : Int := Market.DarkAmmPrivateReceipt.RULE_ID
def OLD_ROOT_DOMAIN_TAG : Int := Market.DarkAmmPrivateReceipt.OLD_ROOT_DOMAIN_TAG
def NEW_ROOT_DOMAIN_TAG : Int := Market.DarkAmmPrivateReceipt.NEW_ROOT_DOMAIN_TAG
def BABYBEAR_MODULUS : Int := Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS

/-! ## Fixed column and public-input ABI. -/

def SESSION : Nat := 0
def RULE : Nat := 1
def K : Nat := 2
def OLD_ROOT_BASE : Nat := 3
def NEW_ROOT_BASE : Nat := 11
def X : Nat := 19
def Y : Nat := 20
def DX : Nat := 21
def DY : Nat := 22
def POST_X : Nat := 23
def POST_Y : Nat := 24
def DX_INV : Nat := 25
def DY_INV : Nat := 26
def OLD_BLIND_BASE : Nat := 27
def NEW_BLIND_BASE : Nat := 35
def X_BITS : Nat := 43
def Y_BITS : Nat := 53
def DX_BITS : Nat := 63
def DY_BITS : Nat := 73
def POST_X_BITS : Nat := 83
def POST_Y_BITS : Nat := 94
def TRACE_WIDTH : Nat := 104
def PI_COUNT : Nat := 19

def OLD_ROOT (lane : Nat) : Nat := OLD_ROOT_BASE + lane
def NEW_ROOT (lane : Nat) : Nat := NEW_ROOT_BASE + lane
def OLD_BLIND (lane : Nat) : Nat := OLD_BLIND_BASE + lane
def NEW_BLIND (lane : Nat) : Nat := NEW_BLIND_BASE + lane

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (left right : EmittedExpr) : EmittedExpr := .add left right
def mul (left right : EmittedExpr) : EmittedExpr := .mul left right
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (left right : EmittedExpr) : EmittedExpr := add left (neg right)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (weight : Int) (x : EmittedExpr) : EmittedExpr := mul (c weight) x

def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recompose (col bitBase bits : Nat) : EmittedExpr :=
  sub (sumE ((List.range bits).map
    (fun bit => weighted ((2 : Int) ^ bit) (v (bitBase + bit))))) (v col)

def rangeBodies (col bitBase bits : Nat) : List EmittedExpr :=
  [recompose col bitBase bits] ++
    (List.range bits).map (fun bit => binaryBody (bitBase + bit))

def semanticBodies : List EmittedExpr :=
  [ sub (v RULE) (c RULE_ID)
  , sub (v POST_X) (add (v X) (v DX))
  , sub (v Y) (add (v POST_Y) (v DY))
  , sub (mul (v X) (v Y)) (v K)
  , sub (mul (v POST_X) (v POST_Y)) (v K)
  , sub (mul (v DX) (v DX_INV)) (c 1)
  , sub (mul (v DY) (v DY_INV)) (c 1) ] ++
  rangeBodies X X_BITS 10 ++
  rangeBodies Y Y_BITS 10 ++
  rangeBodies DX DX_BITS 10 ++
  rangeBodies DY DY_BITS 10 ++
  rangeBodies POST_X POST_X_BITS 11 ++
  rangeBodies POST_Y POST_Y_BITS 10

def oldRootInputExprs : List EmittedExpr :=
  [c OLD_ROOT_DOMAIN_TAG, v SESSION, c RULE_ID, v K, v X, v Y] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (OLD_BLIND lane)) ++ [c 0, c 0]

def newRootInputExprs : List EmittedExpr :=
  [c NEW_ROOT_DOMAIN_TAG, v SESSION, c RULE_ID, v K, v POST_X, v POST_Y] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (NEW_BLIND lane)) ++ [c 0, c 0]

def oldRootDigestCols : List Nat := (List.range DIGEST_WIDTH).map OLD_ROOT
def newRootDigestCols : List Nat := (List.range DIGEST_WIDTH).map NEW_ROOT

def oldRootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN oldRootInputExprs oldRootDigestCols⟩

def newRootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN newRootInputExprs newRootDigestCols⟩

def hashLookups : List VmConstraint2 := [oldRootLookup, newRootLookup]

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1)
  , .base (.piBinding .first K 2) ] ++
  (List.range DIGEST_WIDTH).map
    (fun lane => .base (.piBinding .first (OLD_ROOT lane) (3 + lane))) ++
  (List.range DIGEST_WIDTH).map
    (fun lane => .base (.piBinding .first (NEW_ROOT lane) (11 + lane)))

/-- The exact Lean-authored fixed-family descriptor.  Transition gates are
repeated on the last row so a height-one/last-row semantic drop cannot erase
the relation. -/
def darkAmmPrivateDescriptor : EffectVmDescriptor2 :=
  { name := "dark-amm-private-v1::wide-poseidon2-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard darkAmmPrivateDescriptor.traceWidth == 104
#guard darkAmmPrivateDescriptor.piCount == 19
#guard oldRootInputExprs.length == 16
#guard newRootInputExprs.length == 16
#guard hashLookups.length == 2
#guard darkAmmPrivateDescriptor.constraints.length == 2 + 2 * semanticBodies.length + 19

/-! ## Direct extraction from `Satisfied2`. -/

def ammM0 : Int → Int := fun _ => 0
def ammF0 : Int → Int × Nat := fun _ => (0, 0)

def constTrace (a pis : Assignment) (tf : TraceFamily) : VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).loc = a := by
  funext col
  simp [envAt, constTrace]

@[simp] theorem constTrace_pub0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).pub = pis := rfl

@[simp] theorem constTrace_tf (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).tf = tf := rfl

abbrev CanonicalAssignment :=
  Market.DarkBazaarPrivateDescriptor.CanonicalAssignment

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ darkAmmPrivateDescriptor.constraints := by
  simp [darkAmmPrivateDescriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ darkAmmPrivateDescriptor.constraints := by
  simp [darkAmmPrivateDescriptor, hpin]

theorem old_root_lookup_mem : oldRootLookup ∈ darkAmmPrivateDescriptor.constraints := by
  simp [darkAmmPrivateDescriptor, hashLookups]

theorem new_root_lookup_mem : newRootLookup ∈ darkAmmPrivateDescriptor.constraints := by
  simp [darkAmmPrivateDescriptor, hashLookups]

theorem semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS,
    Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS] using h

theorem public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS,
    Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS] using h

theorem old_root_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    oldRootDigestCols.map a = permOut (oldRootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) oldRootLookup old_root_lookup_mem
  have hlookup :
      (chipLookupTupleN oldRootInputExprs oldRootDigestCols).map (·.eval a) ∈
        tf TableId.poseidon2 := by
    simpa [oldRootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    oldRootInputExprs oldRootDigestCols (by decide) hlookup

theorem new_root_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    newRootDigestCols.map a = permOut (newRootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) newRootLookup new_root_lookup_mem
  have hlookup :
      (chipLookupTupleN newRootInputExprs newRootDigestCols).map (·.eval a) ∈
        tf TableId.poseidon2 := by
    simpa [newRootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    newRootInputExprs newRootDigestCols (by decide) hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  canonicalCells : CanonicalAssignment a
  semanticGates : ∀ body ∈ semanticBodies,
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  oldWideRoot : oldRootDigestCols.map a = permOut (oldRootInputExprs.map (·.eval a))
  newWideRoot : newRootDigestCols.map a = permOut (newRootInputExprs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

theorem darkAmmPrivate_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   old_root_lookup_sound permOut hChip hsat,
   new_root_lookup_sound permOut hChip hsat,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

/-! ## Exact decoded relation. -/

open Market.DarkBazaarPrivateDescriptor
  (binary_of_modular_gate eq_of_modEq_of_canonical)

theorem bit_body_mem_10 (col bitBase : Nat) (hgroup : rangeBodies col bitBase 10 ⊆ semanticBodies)
    (bit : Fin 10) : binaryBody (bitBase + bit.val) ∈ semanticBodies := by
  apply hgroup
  simp only [rangeBodies, List.mem_append, List.mem_singleton, List.mem_map, List.mem_range]
  right
  exact ⟨bit.val, bit.isLt, rfl⟩

theorem bit_body_mem_11 (col bitBase : Nat) (hgroup : rangeBodies col bitBase 11 ⊆ semanticBodies)
    (bit : Fin 11) : binaryBody (bitBase + bit.val) ∈ semanticBodies := by
  apply hgroup
  simp only [rangeBodies, List.mem_append, List.mem_singleton, List.mem_map, List.mem_range]
  right
  exact ⟨bit.val, bit.isLt, rfl⟩

theorem recompose_body_mem (col bitBase bits : Nat)
    (hgroup : rangeBodies col bitBase bits ⊆ semanticBodies) :
    recompose col bitBase bits ∈ semanticBodies := by
  apply hgroup
  simp [rangeBodies]

theorem x_range_subset : rangeBodies X X_BITS 10 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop
theorem y_range_subset : rangeBodies Y Y_BITS 10 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop
theorem dx_range_subset : rangeBodies DX DX_BITS 10 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop
theorem dy_range_subset : rangeBodies DY DY_BITS 10 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop
theorem post_x_range_subset : rangeBodies POST_X POST_X_BITS 11 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop
theorem post_y_range_subset : rangeBodies POST_Y POST_Y_BITS 10 ⊆ semanticBodies := by
  intro body hbody
  simp only [semanticBodies, List.mem_append, List.mem_cons]
  aesop

theorem bit_bounds {z : Int} (h : z = 0 ∨ z = 1) : 0 ≤ z ∧ z ≤ 1 := by omega

def bits10Value (a : Assignment) (base : Nat) : Int :=
  a base + 2 * a (base + 1) + 4 * a (base + 2) + 8 * a (base + 3) +
  16 * a (base + 4) + 32 * a (base + 5) + 64 * a (base + 6) +
  128 * a (base + 7) + 256 * a (base + 8) + 512 * a (base + 9)

def bits11Value (a : Assignment) (base : Nat) : Int :=
  bits10Value a base + 1024 * a (base + 10)

theorem recompose10_eval (a : Assignment) (col base : Nat) :
    (recompose col base 10).eval a = bits10Value a base - a col := by
  norm_num [recompose, bits10Value, sumE, weighted, sub, neg, mul, add, v, c,
    EmittedExpr.eval, List.range_succ, Function.comp_apply, sub_eq_add_neg, add_assoc]

theorem recompose11_eval (a : Assignment) (col base : Nat) :
    (recompose col base 11).eval a = bits11Value a base - a col := by
  norm_num [recompose, bits11Value, bits10Value, sumE, weighted, sub, neg, mul, add, v, c,
    EmittedExpr.eval, List.range_succ, Function.comp_apply, sub_eq_add_neg, add_assoc]

theorem decode10
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf))
    (col base : Nat)
    (hgroup : rangeBodies col base 10 ⊆ semanticBodies) :
    a col = bits10Value a base ∧ 0 ≤ a col ∧ a col < 1024 := by
  have hb (bit : Fin 10) : a (base + bit.val) = 0 ∨ a (base + bit.val) = 1 :=
    binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (bit_body_mem_10 col base hgroup bit))
  have h0 := bit_bounds (hb 0); have h1 := bit_bounds (hb 1)
  have h2 := bit_bounds (hb 2); have h3 := bit_bounds (hb 3)
  have h4 := bit_bounds (hb 4); have h5 := bit_bounds (hb 5)
  have h6 := bit_bounds (hb 6); have h7 := bit_bounds (hb 7)
  have h8 := bit_bounds (hb 8); have h9 := bit_bounds (hb 9)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hgate := semantic_gate_vanishes hsat (recompose_body_mem col base 10 hgroup)
  rw [recompose10_eval] at hgate
  have hcong : bits10Value a base ≡ a col [ZMOD BABYBEAR_MODULUS] := by
    simpa using hgate.add_right (a col)
  have hsmall : 0 ≤ bits10Value a base ∧ bits10Value a base < BABYBEAR_MODULUS := by
    simp only [bits10Value, BABYBEAR_MODULUS,
      Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS]
    omega
  have heq := (eq_of_modEq_of_canonical hcong hsmall (hcanon col)).symm
  refine ⟨heq, ?_, ?_⟩ <;> rw [heq]
  · exact hsmall.1
  · simp only [bits10Value]
    omega

theorem decode11
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf))
    (col base : Nat)
    (hgroup : rangeBodies col base 11 ⊆ semanticBodies) :
    a col = bits11Value a base ∧ 0 ≤ a col ∧ a col < 2048 := by
  have hb (bit : Fin 11) : a (base + bit.val) = 0 ∨ a (base + bit.val) = 1 :=
    binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (bit_body_mem_11 col base hgroup bit))
  have h0 := bit_bounds (hb 0); have h1 := bit_bounds (hb 1)
  have h2 := bit_bounds (hb 2); have h3 := bit_bounds (hb 3)
  have h4 := bit_bounds (hb 4); have h5 := bit_bounds (hb 5)
  have h6 := bit_bounds (hb 6); have h7 := bit_bounds (hb 7)
  have h8 := bit_bounds (hb 8); have h9 := bit_bounds (hb 9)
  have h10 := bit_bounds (hb 10)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hgate := semantic_gate_vanishes hsat (recompose_body_mem col base 11 hgroup)
  rw [recompose11_eval] at hgate
  have hcong : bits11Value a base ≡ a col [ZMOD BABYBEAR_MODULUS] := by
    simpa using hgate.add_right (a col)
  have hsmall : 0 ≤ bits11Value a base ∧ bits11Value a base < BABYBEAR_MODULUS := by
    simp only [bits11Value, bits10Value, BABYBEAR_MODULUS,
      Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS]
    omega
  have heq := (eq_of_modEq_of_canonical hcong hsmall (hcanon col)).symm
  refine ⟨heq, ?_, ?_⟩ <;> rw [heq]
  · exact hsmall.1
  · simp only [bits11Value, bits10Value]
    omega

structure ScalarBounds (a : Assignment) : Prop where
  x : 0 ≤ a X ∧ a X < 1024
  y : 0 ≤ a Y ∧ a Y < 1024
  dx : 0 ≤ a DX ∧ a DX < 1024
  dy : 0 ≤ a DY ∧ a DY < 1024
  postX : 0 ≤ a POST_X ∧ a POST_X < 2048
  postY : 0 ≤ a POST_Y ∧ a POST_Y < 1024

theorem scalar_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : ScalarBounds a := by
  exact ⟨(decode10 hcanon hsat X X_BITS x_range_subset).2,
    (decode10 hcanon hsat Y Y_BITS y_range_subset).2,
    (decode10 hcanon hsat DX DX_BITS dx_range_subset).2,
    (decode10 hcanon hsat DY DY_BITS dy_range_subset).2,
    (decode11 hcanon hsat POST_X POST_X_BITS post_x_range_subset).2,
    (decode10 hcanon hsat POST_Y POST_Y_BITS post_y_range_subset).2⟩

def decodedWitness (a : Assignment) : Market.DarkAmmPrivateReceipt.PrivateWitness where
  x := ⟨(a X).toNat % 1024, Nat.mod_lt _ (by decide)⟩
  y := ⟨(a Y).toNat % 1024, Nat.mod_lt _ (by decide)⟩
  dx := ⟨(a DX).toNat % 1024, Nat.mod_lt _ (by decide)⟩
  dy := ⟨(a DY).toNat % 1024, Nat.mod_lt _ (by decide)⟩
  oldBlind := fun lane => a (OLD_BLIND lane.val)
  newBlind := fun lane => a (NEW_BLIND lane.val)

def columnPublic (a : Assignment) : Market.DarkAmmPrivateReceipt.PublicStatement where
  session := a SESSION
  rule := a RULE
  k := (a K).toNat
  oldRoot := oldRootDigestCols.map a
  newRoot := newRootDigestCols.map a

def piPublic (pis : Assignment) : Market.DarkAmmPrivateReceipt.PublicStatement where
  session := pis 0
  rule := pis 1
  k := (pis 2).toNat
  oldRoot := (List.range DIGEST_WIDTH).map (fun lane => pis (3 + lane))
  newRoot := (List.range DIGEST_WIDTH).map (fun lane => pis (11 + lane))

theorem decoded_blinds_canonical (a : Assignment) (hcanon : CanonicalAssignment a) :
    Market.DarkAmmPrivateReceipt.CanonicalBlind (decodedWitness a).oldBlind ∧
      Market.DarkAmmPrivateReceipt.CanonicalBlind (decodedWitness a).newBlind := by
  constructor <;> intro lane
  · simpa [decodedWitness, OLD_BLIND, BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
      Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS] using hcanon (OLD_BLIND lane.val)
  · simpa [decodedWitness, NEW_BLIND, BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
      Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS] using hcanon (NEW_BLIND lane.val)

theorem darkAmmPrivate_decoded_scalars_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    (((decodedWitness a).x.val : Int) = a X) ∧
    (((decodedWitness a).y.val : Int) = a Y) ∧
    (((decodedWitness a).dx.val : Int) = a DX) ∧
    (((decodedWitness a).dy.val : Int) = a DY) := by
  have hb := scalar_bounds hcanon hsat
  simp only [decodedWitness]
  constructor
  · rw [Nat.mod_eq_of_lt ((Int.toNat_lt hb.x.1).2 hb.x.2)]
    exact Int.toNat_of_nonneg hb.x.1
  constructor
  · rw [Nat.mod_eq_of_lt ((Int.toNat_lt hb.y.1).2 hb.y.2)]
    exact Int.toNat_of_nonneg hb.y.1
  constructor
  · rw [Nat.mod_eq_of_lt ((Int.toNat_lt hb.dx.1).2 hb.dx.2)]
    exact Int.toNat_of_nonneg hb.dx.1
  · rw [Nat.mod_eq_of_lt ((Int.toNat_lt hb.dy.1).2 hb.dy.2)]
    exact Int.toNat_of_nonneg hb.dy.1

/-! ## The arithmetic gates are exact integers, not merely field residues. -/

theorem rule_body_mem : sub (v RULE) (c RULE_ID) ∈ semanticBodies := by decide
theorem post_x_body_mem : sub (v POST_X) (add (v X) (v DX)) ∈ semanticBodies := by decide
theorem post_y_body_mem : sub (v Y) (add (v POST_Y) (v DY)) ∈ semanticBodies := by decide
theorem old_product_body_mem : sub (mul (v X) (v Y)) (v K) ∈ semanticBodies := by decide
theorem new_product_body_mem : sub (mul (v POST_X) (v POST_Y)) (v K) ∈ semanticBodies := by decide
theorem dx_inverse_body_mem : sub (mul (v DX) (v DX_INV)) (c 1) ∈ semanticBodies := by decide
theorem dy_inverse_body_mem : sub (mul (v DY) (v DY_INV)) (c 1) ∈ semanticBodies := by decide

theorem rule_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a RULE = RULE_ID := by
  have hgate := semantic_gate_vanishes hsat rule_body_mem
  have hres : a RULE - RULE_ID ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, ← sub_eq_add_neg] using hgate
  have hcong : a RULE ≡ RULE_ID [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right RULE_ID
  exact eq_of_modEq_of_canonical hcong (hcanon RULE) (by
    norm_num [RULE_ID, BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.RULE_ID,
      Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
      Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS])

theorem post_x_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a POST_X = a X + a DX := by
  have hb := scalar_bounds hcanon hsat
  have hgate := semantic_gate_vanishes hsat post_x_body_mem
  have hres : a POST_X - (a X + a DX) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a POST_X ≡ a X + a DX [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a X + a DX)
  apply eq_of_modEq_of_canonical hcong (hcanon POST_X)
  norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
    Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS]
  have hx_nonneg := hb.x.1
  have hx_lt := hb.x.2
  have hdx_nonneg := hb.dx.1
  have hdx_lt := hb.dx.2
  omega

theorem post_y_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a Y = a POST_Y + a DY := by
  have hb := scalar_bounds hcanon hsat
  have hgate := semantic_gate_vanishes hsat post_y_body_mem
  have hres : a Y - (a POST_Y + a DY) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a Y ≡ a POST_Y + a DY [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a POST_Y + a DY)
  apply eq_of_modEq_of_canonical hcong (hcanon Y)
  norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
    Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS]
  have hpost_nonneg := hb.postY.1
  have hpost_lt := hb.postY.2
  have hdy_nonneg := hb.dy.1
  have hdy_lt := hb.dy.2
  omega

theorem old_product_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a X * a Y = a K := by
  have hb := scalar_bounds hcanon hsat
  have hgate := semantic_gate_vanishes hsat old_product_body_mem
  have hres : a X * a Y - a K ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a X * a Y ≡ a K [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a K)
  apply eq_of_modEq_of_canonical hcong
  · norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
      Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS]
    have hxlt := hb.x.2
    have hylt := hb.y.2
    have hxle : a X ≤ 1023 := by omega
    have hyle : a Y ≤ 1023 := by omega
    have hxy_nonneg : 0 ≤ a X * a Y := mul_nonneg hb.x.1 hb.y.1
    have hxy_le_x : a X * a Y ≤ a X * 1023 :=
      mul_le_mul_of_nonneg_left hyle hb.x.1
    have hx_le_max : a X * 1023 ≤ 1023 * 1023 :=
      mul_le_mul_of_nonneg_right hxle (by norm_num)
    omega
  · exact hcanon K

theorem new_product_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a POST_X * a POST_Y = a K := by
  have hb := scalar_bounds hcanon hsat
  have hgate := semantic_gate_vanishes hsat new_product_body_mem
  have hres : a POST_X * a POST_Y - a K ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg, add_assoc] using hgate
  have hcong : a POST_X * a POST_Y ≡ a K [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a K)
  apply eq_of_modEq_of_canonical hcong
  · norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS,
      Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS]
    have hxlt := hb.postX.2
    have hylt := hb.postY.2
    have hxle : a POST_X ≤ 2047 := by omega
    have hyle : a POST_Y ≤ 1023 := by omega
    have hxy_nonneg : 0 ≤ a POST_X * a POST_Y := mul_nonneg hb.postX.1 hb.postY.1
    have hxy_le_x : a POST_X * a POST_Y ≤ a POST_X * 1023 :=
      mul_le_mul_of_nonneg_left hyle hb.postX.1
    have hx_le_max : a POST_X * 1023 ≤ 2047 * 1023 :=
      mul_le_mul_of_nonneg_right hxle (by norm_num)
    omega
  · exact hcanon K

theorem amount_columns_positive
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : 0 < a DX ∧ 0 < a DY := by
  have hb := scalar_bounds hcanon hsat
  have hdx := semantic_gate_vanishes hsat dx_inverse_body_mem
  have hdy := semantic_gate_vanishes hsat dy_inverse_body_mem
  have hdx' : a DX * a DX_INV - 1 ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hdx
  have hdy' : a DY * a DY_INV - 1 ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hdy
  constructor
  · by_contra hn
    have hnonneg := hb.dx.1
    have hz : a DX = 0 := by omega
    rw [hz] at hdx'
    have hzero : (-1 : Int) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by simpa using hdx'
    have hd : BABYBEAR_MODULUS ∣ (-1 : Int) := Int.modEq_zero_iff_dvd.mp hzero
    norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS] at hd
  · by_contra hn
    have hnonneg := hb.dy.1
    have hz : a DY = 0 := by omega
    rw [hz] at hdy'
    have hzero : (-1 : Int) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by simpa using hdy'
    have hd : BABYBEAR_MODULUS ∣ (-1 : Int) := Int.modEq_zero_iff_dvd.mp hzero
    norm_num [BABYBEAR_MODULUS, Market.DarkAmmPrivateReceipt.BABYBEAR_MODULUS] at hd

theorem amount_not_overdrawn
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : a DY ≤ a Y := by
  have hb := scalar_bounds hcanon hsat
  have hy := post_y_column_exact hcanon hsat
  have hpost_nonneg := hb.postY.1
  omega

/-! ## Exact root and public-input identification. -/

theorem old_root_input_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    oldRootInputExprs.map (·.eval a) =
      Market.DarkAmmPrivateReceipt.oldPreimage (columnPublic a) (decodedWitness a) := by
  have hb := scalar_bounds hcanon hsat
  have hk : (((a K).toNat : Nat) : Int) = a K := Int.toNat_of_nonneg (hcanon K).1
  simp [oldRootInputExprs, Market.DarkAmmPrivateReceipt.oldPreimage,
    columnPublic, decodedWitness, OLD_BLIND, OLD_BLIND_BASE, DIGEST_WIDTH,
    Market.DarkAmmPrivateReceipt.DIGEST_WIDTH, List.ofFn_succ,
    List.range_succ, v, c, OLD_ROOT_DOMAIN_TAG,
    Market.DarkAmmPrivateReceipt.OLD_ROOT_DOMAIN_TAG, RULE_ID,
    Market.DarkAmmPrivateReceipt.RULE_ID, hk]
  norm_num [EmittedExpr.eval]
  constructor
  · rw [max_eq_left hb.x.1, Int.emod_eq_of_lt hb.x.1 hb.x.2]
  · rw [max_eq_left hb.y.1, Int.emod_eq_of_lt hb.y.1 hb.y.2]

theorem new_root_input_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    newRootInputExprs.map (·.eval a) =
      Market.DarkAmmPrivateReceipt.newPreimage (columnPublic a) (decodedWitness a) := by
  rcases darkAmmPrivate_decoded_scalars_exact hcanon hsat with ⟨hx, hy, hdx, hdy⟩
  have hpostx := post_x_column_exact hcanon hsat
  have hposty := post_y_column_exact hcanon hsat
  have hover := amount_not_overdrawn hcanon hsat
  have hpostxDecoded :
      ((Market.DarkAmmPrivateReceipt.postX (decodedWitness a) : Nat) : Int) = a POST_X := by
    simp only [Market.DarkAmmPrivateReceipt.postX]
    push_cast
    rw [hx, hdx, ← hpostx]
  have hpostyDecoded :
      ((Market.DarkAmmPrivateReceipt.postY (decodedWitness a) : Nat) : Int) = a POST_Y := by
    have hoverNat : (decodedWitness a).dy.val ≤ (decodedWitness a).y.val := by
      have hover' := hover
      rw [← hdy, ← hy] at hover'
      exact_mod_cast hover'
    simp only [Market.DarkAmmPrivateReceipt.postY]
    push_cast [hoverNat]
    rw [hy, hdy]
    omega
  have hk : (((a K).toNat : Nat) : Int) = a K := Int.toNat_of_nonneg (hcanon K).1
  simp [newRootInputExprs, Market.DarkAmmPrivateReceipt.newPreimage,
    columnPublic, decodedWitness, NEW_BLIND, NEW_BLIND_BASE, DIGEST_WIDTH,
    Market.DarkAmmPrivateReceipt.DIGEST_WIDTH, List.ofFn_succ,
    List.range_succ, v, c, NEW_ROOT_DOMAIN_TAG,
    Market.DarkAmmPrivateReceipt.NEW_ROOT_DOMAIN_TAG, RULE_ID,
    Market.DarkAmmPrivateReceipt.RULE_ID, hk]
  norm_num [EmittedExpr.eval]
  exact ⟨hpostxDecoded.symm, hpostyDecoded.symm⟩

theorem column_old_root_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    (columnPublic a).oldRoot =
      Market.DarkAmmPrivateReceipt.oldRoot permOut (columnPublic a) (decodedWitness a) := by
  have hwide := old_root_lookup_sound permOut hChip hsat
  rw [old_root_input_decoded hcanon hsat] at hwide
  simpa [columnPublic, Market.DarkAmmPrivateReceipt.oldRoot] using hwide

theorem column_new_root_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    (columnPublic a).newRoot =
      Market.DarkAmmPrivateReceipt.newRoot permOut (columnPublic a) (decodedWitness a) := by
  have hwide := new_root_lookup_sound permOut hChip hsat
  rw [new_root_input_decoded hcanon hsat] at hwide
  simpa [columnPublic, Market.DarkAmmPrivateReceipt.newRoot] using hwide

theorem pi_public_eq_column
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) : piPublic pis = columnPublic a := by
  have pinEq {col pi : Nat}
      (hmem : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
      pis pi = a col :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat hmem)
      (hcanon col) (hcanonPis pi)).symm
  have hs : pis 0 = a SESSION := pinEq (by simp [publicPins])
  have hr : pis 1 = a RULE := pinEq (by simp [publicPins])
  have hk : pis 2 = a K := pinEq (by simp [publicPins])
  have hold (lane : Fin 8) : pis (3 + lane.val) = a (OLD_ROOT lane.val) := by
    apply pinEq
    simp only [publicPins, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    left
    right
    exact ⟨lane.val, by
      change lane.val < 8
      exact lane.isLt, rfl⟩
  have hnew (lane : Fin 8) : pis (11 + lane.val) = a (NEW_ROOT lane.val) := by
    apply pinEq
    simp only [publicPins, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    right
    exact ⟨lane.val, by
      change lane.val < 8
      exact lane.isLt, rfl⟩
  simp [piPublic, columnPublic, oldRootDigestCols, newRootDigestCols,
    DIGEST_WIDTH, Market.DarkAmmPrivateReceipt.DIGEST_WIDTH, List.range_succ,
    OLD_ROOT, NEW_ROOT, hs, hr, hk]
  exact ⟨⟨hold 0, hold 1, hold 2, hold 3, hold 4, hold 5, hold 6, hold 7⟩,
    hnew 0, hnew 1, hnew 2, hnew 3, hnew 4, hnew 5, hnew 6, hnew 7⟩

/-- The closed semantic theorem for the actual emitted descriptor.  Canonical
trace/PI representatives plus a sound wide Poseidon table turn `Satisfied2`
into the exact private AMM receipt relation. -/
theorem darkAmmPrivate_column_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    Market.DarkAmmPrivateReceipt.Accepts permOut (columnPublic a) (decodedWitness a) := by
  rcases decoded_blinds_canonical a hcanon with ⟨holdBlind, hnewBlind⟩
  rcases darkAmmPrivate_decoded_scalars_exact hcanon hsat with ⟨hx, hy, hdx, hdy⟩
  have hb := scalar_bounds hcanon hsat
  have hpos := amount_columns_positive hcanon hsat
  have hover := amount_not_overdrawn hcanon hsat
  have holdProduct := old_product_column_exact hcanon hsat
  have hnewProduct := new_product_column_exact hcanon hsat
  have hpostx := post_x_column_exact hcanon hsat
  have hposty := post_y_column_exact hcanon hsat
  have hdxPosInt : (0 : Int) < ((decodedWitness a).dx.val : Int) := by simpa [hdx] using hpos.1
  have hdyPosInt : (0 : Int) < ((decodedWitness a).dy.val : Int) := by simpa [hdy] using hpos.2
  have hoverNat : (decodedWitness a).dy.val ≤ (decodedWitness a).y.val := by
    have hover' := hover
    rw [← hdy, ← hy] at hover'
    exact_mod_cast hover'
  have hpostxDecoded :
      ((Market.DarkAmmPrivateReceipt.postX (decodedWitness a) : Nat) : Int) = a POST_X := by
    simp only [Market.DarkAmmPrivateReceipt.postX]
    push_cast
    rw [hx, hdx, ← hpostx]
  have hpostyDecoded :
      ((Market.DarkAmmPrivateReceipt.postY (decodedWitness a) : Nat) : Int) = a POST_Y := by
    simp only [Market.DarkAmmPrivateReceipt.postY]
    push_cast [hoverNat]
    rw [hy, hdy]
    omega
  refine ⟨holdBlind, hnewBlind, ?_, ?_, ?_, ?_, ?_, hoverNat, ?_, ?_⟩
  · simpa [columnPublic, RULE_ID] using rule_column_exact hcanon hsat
  · exact column_old_root_semantic permOut hcanon hChip hsat
  · exact column_new_root_semantic permOut hcanon hChip hsat
  · exact_mod_cast hdxPosInt
  · exact_mod_cast hdyPosInt
  · change (decodedWitness a).x.val * (decodedWitness a).y.val = (a K).toNat
    apply Int.ofNat_inj.mp
    push_cast
    rw [hx, hy, Int.toNat_of_nonneg (hcanon K).1]
    exact holdProduct
  · change Market.DarkAmmPrivateReceipt.postX (decodedWitness a) *
      Market.DarkAmmPrivateReceipt.postY (decodedWitness a) = (a K).toNat
    apply Int.ofNat_inj.mp
    push_cast
    rw [hpostxDecoded, hpostyDecoded, Int.toNat_of_nonneg (hcanon K).1]
    exact hnewProduct

theorem darkAmmPrivate_descriptor_to_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkAmmPrivateDescriptor ammM0 ammF0 []
      (constTrace a pis tf)) :
    Market.DarkAmmPrivateReceipt.Accepts permOut (piPublic pis) (decodedWitness a) := by
  rw [pi_public_eq_column hcanon hcanonPis hsat]
  exact darkAmmPrivate_column_accepts permOut hcanon hChip hsat

#assert_all_clean [
  Market.DarkAmmPrivateDescriptor.darkAmmPrivate_emitted_air_sound,
  Market.DarkAmmPrivateDescriptor.decode10,
  Market.DarkAmmPrivateDescriptor.decode11,
  Market.DarkAmmPrivateDescriptor.scalar_bounds,
  Market.DarkAmmPrivateDescriptor.darkAmmPrivate_decoded_scalars_exact,
  Market.DarkAmmPrivateDescriptor.rule_column_exact,
  Market.DarkAmmPrivateDescriptor.post_x_column_exact,
  Market.DarkAmmPrivateDescriptor.post_y_column_exact,
  Market.DarkAmmPrivateDescriptor.old_product_column_exact,
  Market.DarkAmmPrivateDescriptor.new_product_column_exact,
  Market.DarkAmmPrivateDescriptor.amount_columns_positive,
  Market.DarkAmmPrivateDescriptor.amount_not_overdrawn,
  Market.DarkAmmPrivateDescriptor.old_root_input_decoded,
  Market.DarkAmmPrivateDescriptor.new_root_input_decoded,
  Market.DarkAmmPrivateDescriptor.column_old_root_semantic,
  Market.DarkAmmPrivateDescriptor.column_new_root_semantic,
  Market.DarkAmmPrivateDescriptor.pi_public_eq_column,
  Market.DarkAmmPrivateDescriptor.darkAmmPrivate_column_accepts,
  Market.DarkAmmPrivateDescriptor.darkAmmPrivate_descriptor_to_accepts]

end Market.DarkAmmPrivateDescriptor
