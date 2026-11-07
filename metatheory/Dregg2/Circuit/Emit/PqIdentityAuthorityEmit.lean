/-
# Dregg2.Circuit.Emit.PqIdentityAuthorityEmit -- Lean-authored PQ rotation row

This is the additive IR2 authority certificate for `Effect::RotatePqIdentity`.
It is intentionally NOT inserted into the deployed EffectVM registry yet: the
runtime converter continues to refuse the effect until the outer ML-DSA proof
boundary is composed with this row.

The public row is lossless:

* target cell id: 16 canonical `u16` limbs (32 exact bytes);
* target Ed25519 identity: 16 canonical `u16` limbs (32 exact bytes), exactly
  the extra field covered by the runtime possession transcript;
* old / expected / new epochs: four canonical `u16` limbs each (exact `u64`);
* old / new ML-DSA key commitments: 16 canonical `u16` limbs each;
* old-authorization / new-possession evidence commitments: 16 canonical `u16`
  limbs each.

The row proves expected=old, new=old+1 without overflow, and old-key !=
new-key.  It binds every public datum through a first-row PI.  It does NOT
pretend to verify ML-DSA with a prover-selected boolean: the cryptographic
premise remains `PqIdentityAuthority.CryptoBoundary` over these exact images.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.PqIdentityAuthority
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.PqIdentityAuthorityEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.PqIdentityAuthority
open Dregg2.Circuit.CommitmentTreeWide
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRange)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-! ## Layout -/

def TARGET : Nat := 0
def TARGET_ED25519 : Nat := 16
def OLD_EPOCH : Nat := 32
def EXPECTED_EPOCH : Nat := 36
def NEW_EPOCH : Nat := 40
def OLD_KEY : Nat := 44
def NEW_KEY : Nat := 60
def OLD_AUTH_EVIDENCE : Nat := 76
def NEW_POSSESSION_EVIDENCE : Nat := 92

/-- All public data occupies columns/PIs `0..107` in the same order. -/
def PUBLIC_WIDTH : Nat := 108

/-- Three binary carry witnesses for the four-limb `+1`; absence of a fourth
carry is the no-overflow tooth. -/
def CARRY : Nat := 108

/-- Sixteen unrestricted Bezout witnesses.  `sum (new-old)*z = 1` proves the
two canonical key-commitment vectors are not equal. -/
def KEY_NEQ_COEFF : Nat := 111

def TRACE_WIDTH : Nat := 127

def ev (c : Nat) : EmittedExpr := .var c
def ek (k : ℤ) : EmittedExpr := .const k
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (ek (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)

/-! ## Exact epoch and key-change algebra -/

def expectedBody (i : Nat) : EmittedExpr :=
  esub (ev (EXPECTED_EPOCH + i)) (ev (OLD_EPOCH + i))

/-- Limb 0: `new0 + 2^16*c0 = old0 + 1`. -/
def succBody0 : EmittedExpr :=
  esub (eadd (ev NEW_EPOCH) (emul (ek 65536) (ev CARRY)))
    (eadd (ev OLD_EPOCH) (ek 1))

/-- Limb 1: `new1 + 2^16*c1 = old1 + c0`. -/
def succBody1 : EmittedExpr :=
  esub
    (eadd (ev (NEW_EPOCH + 1)) (emul (ek 65536) (ev (CARRY + 1))))
    (eadd (ev (OLD_EPOCH + 1)) (ev CARRY))

/-- Limb 2: `new2 + 2^16*c2 = old2 + c1`. -/
def succBody2 : EmittedExpr :=
  esub
    (eadd (ev (NEW_EPOCH + 2)) (emul (ek 65536) (ev (CARRY + 2))))
    (eadd (ev (OLD_EPOCH + 2)) (ev (CARRY + 1)))

/-- Top limb: `new3 = old3 + c2`.  There is no carry-out witness, so epoch
`2^64-1` cannot rotate to zero. -/
def succBody3 : EmittedExpr :=
  esub (ev (NEW_EPOCH + 3)) (eadd (ev (OLD_EPOCH + 3)) (ev (CARRY + 2)))

def carryBoolBody (i : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf (CARRY + i)))

theorem carryBoolBody_eq (i : Nat) :
    carryBoolBody i = emul (ev (CARRY + i)) (esub (ev (CARRY + i)) (ek 1)) := rfl

def keyDiffTerm (i : Nat) : EmittedExpr :=
  emul (esub (ev (NEW_KEY + i)) (ev (OLD_KEY + i)))
    (ev (KEY_NEQ_COEFF + i))

def keyNeqBody : EmittedExpr :=
  (List.range 16).foldl (fun acc i => eadd acc (keyDiffTerm i)) (ek (-1))

/-- Boundary-first is the correct row form: this descriptor certifies ONE
rotation statement.  The prover may pad the trace, but no later row participates
in the claim. -/
def firstGate (body : EmittedExpr) : VmConstraint2 :=
  .base (.boundary .first body)

def expectedGates : List VmConstraint2 :=
  (List.range 4).map (fun i => firstGate (expectedBody i))

def successorGates : List VmConstraint2 :=
  [firstGate succBody0, firstGate succBody1, firstGate succBody2, firstGate succBody3]

def carryBoolGates : List VmConstraint2 :=
  (List.range 3).map (fun i => firstGate (carryBoolBody i))

def keyNeqGate : VmConstraint2 := firstGate keyNeqBody

def publicPins : List VmConstraint2 :=
  (List.range PUBLIC_WIDTH).map (fun c => .base (.piBinding .first c c))

def rotationConstraints : List VmConstraint2 :=
  publicPins ++ expectedGates ++ successorGates ++ carryBoolGates ++ [keyNeqGate]

/-- Every public datum is a canonical `u16`; carries are canonical bits.  The
Bezout witnesses are intentionally unrestricted field elements. -/
def rotationRanges : List VmRange :=
  (List.range PUBLIC_WIDTH).map (fun c => ⟨c, 16⟩) ++
    (List.range 3).map (fun i => ⟨CARRY + i, 1⟩)

/-- The Lean-authored, additive PQ identity rotation descriptor. -/
def pqIdentityRotationDesc : EffectVmDescriptor2 :=
  { name := "dregg-pq-identity-rotation::v1"
  , traceWidth := TRACE_WIDTH
  , piCount := PUBLIC_WIDTH
  , tables := []
  , constraints := rotationConstraints
  , hashSites := []
  , ranges := rotationRanges }

/-- Exact emitted IR2 wire artifact.  This is drift detection for the
Lean-authored object; semantic faithfulness is supplied by the refinement
theorems below, not inferred from byte identity. -/
def PQ_IDENTITY_ROTATION_GOLDEN : String := r#"{"name":"dregg-pq-identity-rotation::v1","ir":2,"trace_width":127,"public_input_count":108,"challenges":0,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"first","col":13,"pi_index":13},{"t":"pi_binding","row":"first","col":14,"pi_index":14},{"t":"pi_binding","row":"first","col":15,"pi_index":15},{"t":"pi_binding","row":"first","col":16,"pi_index":16},{"t":"pi_binding","row":"first","col":17,"pi_index":17},{"t":"pi_binding","row":"first","col":18,"pi_index":18},{"t":"pi_binding","row":"first","col":19,"pi_index":19},{"t":"pi_binding","row":"first","col":20,"pi_index":20},{"t":"pi_binding","row":"first","col":21,"pi_index":21},{"t":"pi_binding","row":"first","col":22,"pi_index":22},{"t":"pi_binding","row":"first","col":23,"pi_index":23},{"t":"pi_binding","row":"first","col":24,"pi_index":24},{"t":"pi_binding","row":"first","col":25,"pi_index":25},{"t":"pi_binding","row":"first","col":26,"pi_index":26},{"t":"pi_binding","row":"first","col":27,"pi_index":27},{"t":"pi_binding","row":"first","col":28,"pi_index":28},{"t":"pi_binding","row":"first","col":29,"pi_index":29},{"t":"pi_binding","row":"first","col":30,"pi_index":30},{"t":"pi_binding","row":"first","col":31,"pi_index":31},{"t":"pi_binding","row":"first","col":32,"pi_index":32},{"t":"pi_binding","row":"first","col":33,"pi_index":33},{"t":"pi_binding","row":"first","col":34,"pi_index":34},{"t":"pi_binding","row":"first","col":35,"pi_index":35},{"t":"pi_binding","row":"first","col":36,"pi_index":36},{"t":"pi_binding","row":"first","col":37,"pi_index":37},{"t":"pi_binding","row":"first","col":38,"pi_index":38},{"t":"pi_binding","row":"first","col":39,"pi_index":39},{"t":"pi_binding","row":"first","col":40,"pi_index":40},{"t":"pi_binding","row":"first","col":41,"pi_index":41},{"t":"pi_binding","row":"first","col":42,"pi_index":42},{"t":"pi_binding","row":"first","col":43,"pi_index":43},{"t":"pi_binding","row":"first","col":44,"pi_index":44},{"t":"pi_binding","row":"first","col":45,"pi_index":45},{"t":"pi_binding","row":"first","col":46,"pi_index":46},{"t":"pi_binding","row":"first","col":47,"pi_index":47},{"t":"pi_binding","row":"first","col":48,"pi_index":48},{"t":"pi_binding","row":"first","col":49,"pi_index":49},{"t":"pi_binding","row":"first","col":50,"pi_index":50},{"t":"pi_binding","row":"first","col":51,"pi_index":51},{"t":"pi_binding","row":"first","col":52,"pi_index":52},{"t":"pi_binding","row":"first","col":53,"pi_index":53},{"t":"pi_binding","row":"first","col":54,"pi_index":54},{"t":"pi_binding","row":"first","col":55,"pi_index":55},{"t":"pi_binding","row":"first","col":56,"pi_index":56},{"t":"pi_binding","row":"first","col":57,"pi_index":57},{"t":"pi_binding","row":"first","col":58,"pi_index":58},{"t":"pi_binding","row":"first","col":59,"pi_index":59},{"t":"pi_binding","row":"first","col":60,"pi_index":60},{"t":"pi_binding","row":"first","col":61,"pi_index":61},{"t":"pi_binding","row":"first","col":62,"pi_index":62},{"t":"pi_binding","row":"first","col":63,"pi_index":63},{"t":"pi_binding","row":"first","col":64,"pi_index":64},{"t":"pi_binding","row":"first","col":65,"pi_index":65},{"t":"pi_binding","row":"first","col":66,"pi_index":66},{"t":"pi_binding","row":"first","col":67,"pi_index":67},{"t":"pi_binding","row":"first","col":68,"pi_index":68},{"t":"pi_binding","row":"first","col":69,"pi_index":69},{"t":"pi_binding","row":"first","col":70,"pi_index":70},{"t":"pi_binding","row":"first","col":71,"pi_index":71},{"t":"pi_binding","row":"first","col":72,"pi_index":72},{"t":"pi_binding","row":"first","col":73,"pi_index":73},{"t":"pi_binding","row":"first","col":74,"pi_index":74},{"t":"pi_binding","row":"first","col":75,"pi_index":75},{"t":"pi_binding","row":"first","col":76,"pi_index":76},{"t":"pi_binding","row":"first","col":77,"pi_index":77},{"t":"pi_binding","row":"first","col":78,"pi_index":78},{"t":"pi_binding","row":"first","col":79,"pi_index":79},{"t":"pi_binding","row":"first","col":80,"pi_index":80},{"t":"pi_binding","row":"first","col":81,"pi_index":81},{"t":"pi_binding","row":"first","col":82,"pi_index":82},{"t":"pi_binding","row":"first","col":83,"pi_index":83},{"t":"pi_binding","row":"first","col":84,"pi_index":84},{"t":"pi_binding","row":"first","col":85,"pi_index":85},{"t":"pi_binding","row":"first","col":86,"pi_index":86},{"t":"pi_binding","row":"first","col":87,"pi_index":87},{"t":"pi_binding","row":"first","col":88,"pi_index":88},{"t":"pi_binding","row":"first","col":89,"pi_index":89},{"t":"pi_binding","row":"first","col":90,"pi_index":90},{"t":"pi_binding","row":"first","col":91,"pi_index":91},{"t":"pi_binding","row":"first","col":92,"pi_index":92},{"t":"pi_binding","row":"first","col":93,"pi_index":93},{"t":"pi_binding","row":"first","col":94,"pi_index":94},{"t":"pi_binding","row":"first","col":95,"pi_index":95},{"t":"pi_binding","row":"first","col":96,"pi_index":96},{"t":"pi_binding","row":"first","col":97,"pi_index":97},{"t":"pi_binding","row":"first","col":98,"pi_index":98},{"t":"pi_binding","row":"first","col":99,"pi_index":99},{"t":"pi_binding","row":"first","col":100,"pi_index":100},{"t":"pi_binding","row":"first","col":101,"pi_index":101},{"t":"pi_binding","row":"first","col":102,"pi_index":102},{"t":"pi_binding","row":"first","col":103,"pi_index":103},{"t":"pi_binding","row":"first","col":104,"pi_index":104},{"t":"pi_binding","row":"first","col":105,"pi_index":105},{"t":"pi_binding","row":"first","col":106,"pi_index":106},{"t":"pi_binding","row":"first","col":107,"pi_index":107},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":38},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":39},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":35}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":40},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":108}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":1}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":41},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":109}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"var","v":108}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":42},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":110}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"var","v":109}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":43},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":35},"r":{"t":"var","v":110}}}}},{"t":"boundary","row":"first","body":{"t":"mul","l":{"t":"var","v":108},"r":{"t":"add","l":{"t":"var","v":108},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"boundary","row":"first","body":{"t":"mul","l":{"t":"var","v":109},"r":{"t":"add","l":{"t":"var","v":109},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"boundary","row":"first","body":{"t":"mul","l":{"t":"var","v":110},"r":{"t":"add","l":{"t":"var","v":110},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":60},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":44}}},"r":{"t":"var","v":111}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":61},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":45}}},"r":{"t":"var","v":112}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":62},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":46}}},"r":{"t":"var","v":113}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":63},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":47}}},"r":{"t":"var","v":114}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":64},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":48}}},"r":{"t":"var","v":115}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":65},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":49}}},"r":{"t":"var","v":116}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":66},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":50}}},"r":{"t":"var","v":117}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":67},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":51}}},"r":{"t":"var","v":118}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":68},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":52}}},"r":{"t":"var","v":119}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":69},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":53}}},"r":{"t":"var","v":120}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":70},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":54}}},"r":{"t":"var","v":121}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":71},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"var","v":122}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":72},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":56}}},"r":{"t":"var","v":123}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":73},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":57}}},"r":{"t":"var","v":124}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":74},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":58}}},"r":{"t":"var","v":125}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"var","v":75},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":59}}},"r":{"t":"var","v":126}}}}],"hash_sites":[],"ranges":[{"wire":0,"bits":16},{"wire":1,"bits":16},{"wire":2,"bits":16},{"wire":3,"bits":16},{"wire":4,"bits":16},{"wire":5,"bits":16},{"wire":6,"bits":16},{"wire":7,"bits":16},{"wire":8,"bits":16},{"wire":9,"bits":16},{"wire":10,"bits":16},{"wire":11,"bits":16},{"wire":12,"bits":16},{"wire":13,"bits":16},{"wire":14,"bits":16},{"wire":15,"bits":16},{"wire":16,"bits":16},{"wire":17,"bits":16},{"wire":18,"bits":16},{"wire":19,"bits":16},{"wire":20,"bits":16},{"wire":21,"bits":16},{"wire":22,"bits":16},{"wire":23,"bits":16},{"wire":24,"bits":16},{"wire":25,"bits":16},{"wire":26,"bits":16},{"wire":27,"bits":16},{"wire":28,"bits":16},{"wire":29,"bits":16},{"wire":30,"bits":16},{"wire":31,"bits":16},{"wire":32,"bits":16},{"wire":33,"bits":16},{"wire":34,"bits":16},{"wire":35,"bits":16},{"wire":36,"bits":16},{"wire":37,"bits":16},{"wire":38,"bits":16},{"wire":39,"bits":16},{"wire":40,"bits":16},{"wire":41,"bits":16},{"wire":42,"bits":16},{"wire":43,"bits":16},{"wire":44,"bits":16},{"wire":45,"bits":16},{"wire":46,"bits":16},{"wire":47,"bits":16},{"wire":48,"bits":16},{"wire":49,"bits":16},{"wire":50,"bits":16},{"wire":51,"bits":16},{"wire":52,"bits":16},{"wire":53,"bits":16},{"wire":54,"bits":16},{"wire":55,"bits":16},{"wire":56,"bits":16},{"wire":57,"bits":16},{"wire":58,"bits":16},{"wire":59,"bits":16},{"wire":60,"bits":16},{"wire":61,"bits":16},{"wire":62,"bits":16},{"wire":63,"bits":16},{"wire":64,"bits":16},{"wire":65,"bits":16},{"wire":66,"bits":16},{"wire":67,"bits":16},{"wire":68,"bits":16},{"wire":69,"bits":16},{"wire":70,"bits":16},{"wire":71,"bits":16},{"wire":72,"bits":16},{"wire":73,"bits":16},{"wire":74,"bits":16},{"wire":75,"bits":16},{"wire":76,"bits":16},{"wire":77,"bits":16},{"wire":78,"bits":16},{"wire":79,"bits":16},{"wire":80,"bits":16},{"wire":81,"bits":16},{"wire":82,"bits":16},{"wire":83,"bits":16},{"wire":84,"bits":16},{"wire":85,"bits":16},{"wire":86,"bits":16},{"wire":87,"bits":16},{"wire":88,"bits":16},{"wire":89,"bits":16},{"wire":90,"bits":16},{"wire":91,"bits":16},{"wire":92,"bits":16},{"wire":93,"bits":16},{"wire":94,"bits":16},{"wire":95,"bits":16},{"wire":96,"bits":16},{"wire":97,"bits":16},{"wire":98,"bits":16},{"wire":99,"bits":16},{"wire":100,"bits":16},{"wire":101,"bits":16},{"wire":102,"bits":16},{"wire":103,"bits":16},{"wire":104,"bits":16},{"wire":105,"bits":16},{"wire":106,"bits":16},{"wire":107,"bits":16},{"wire":108,"bits":1},{"wire":109,"bits":1},{"wire":110,"bits":1}]}"#

#guard emitVmJson2 pqIdentityRotationDesc == PQ_IDENTITY_ROTATION_GOLDEN

#guard pqIdentityRotationDesc.traceWidth == 127
#guard pqIdentityRotationDesc.piCount == 108
#guard pqIdentityRotationDesc.constraints.length == 120
#guard pqIdentityRotationDesc.ranges.length == 111

/-! ## Semantic readout -/

/-- Exact correspondence between the descriptor's first row and one semantic
claim.  The evidence commitments are part of the readout even though the
non-cryptographic `ExactRotation` law does not inspect their contents. -/
structure RotationReadout (a : Assignment) (c : RotationClaim) : Prop where
  targetBefore : ∀ i : Fin 16,
    a (TARGET + i.1) = (commitmentToLanes16 c.before.target i).1
  targetAfter : ∀ i : Fin 16,
    a (TARGET + i.1) = (commitmentToLanes16 c.after.target i).1
  targetEd25519 : ∀ i : Fin 16,
    a (TARGET_ED25519 + i.1) = (commitmentToLanes16 c.targetEd25519 i).1
  oldEpoch : ∀ i : Fin 4, a (OLD_EPOCH + i.1) = (c.before.epoch i).1
  expectedEpoch : ∀ i : Fin 4,
    a (EXPECTED_EPOCH + i.1) = (c.expectedEpoch i).1
  newEpoch : ∀ i : Fin 4, a (NEW_EPOCH + i.1) = (c.after.epoch i).1
  oldKey : ∀ i : Fin 16,
    a (OLD_KEY + i.1) = (commitmentToLanes16 c.before.keyCommitment i).1
  newKey : ∀ i : Fin 16,
    a (NEW_KEY + i.1) = (commitmentToLanes16 c.after.keyCommitment i).1
  oldEvidence : ∀ i : Fin 16,
    a (OLD_AUTH_EVIDENCE + i.1) =
      (commitmentToLanes16 c.oldAuthorizationEvidence i).1
  newEvidence : ∀ i : Fin 16,
    a (NEW_POSSESSION_EVIDENCE + i.1) =
      (commitmentToLanes16 c.newPossessionEvidence i).1

private def firstRow (t : VmTrace) : Assignment := t.rows.getD 0 Dregg2.Circuit.DescriptorIR2.zeroAsg

private theorem first_body_holds
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (body : EmittedExpr)
    (hmem : firstGate body ∈ pqIdentityRotationDesc.constraints) :
    body.eval (firstRow t) ≡ 0 [ZMOD 2013265921] := by
  have hzero : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  have h := hsat.rowConstraints 0 hzero (firstGate body) hmem
  simp only [firstGate, VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
  simpa only [firstRow] using h (by decide)

private theorem carry_range
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (i : Nat) (hi : i < 3) :
    0 ≤ firstRow t (CARRY + i) ∧ firstRow t (CARRY + i) < 2 := by
  have hzero : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  have hr : (⟨CARRY + i, 1⟩ : VmRange) ∈ pqIdentityRotationDesc.ranges := by
    simp [pqIdentityRotationDesc, rotationRanges, hi]
  have h := hsat.rowRanges 0 hzero ⟨CARRY + i, 1⟩ hr
  simpa [VmRange.holds, envAt, firstRow] using h

private theorem expected_gate_mem (i : Nat) (hi : i < 4) :
    firstGate (expectedBody i) ∈ pqIdentityRotationDesc.constraints := by
  have hx : firstGate (expectedBody i) ∈ expectedGates := by
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  change firstGate (expectedBody i) ∈ rotationConstraints
  unfold rotationConstraints
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hx)))

private theorem successor_gate_mem (i : Nat) (hi : i < 4) :
    firstGate (match i with
      | 0 => succBody0
      | 1 => succBody1
      | 2 => succBody2
      | _ => succBody3) ∈ pqIdentityRotationDesc.constraints := by
  interval_cases i <;> simp_all [pqIdentityRotationDesc, rotationConstraints,
    successorGates]

private theorem key_neq_gate_mem :
    keyNeqGate ∈ pqIdentityRotationDesc.constraints := by
  simp [pqIdentityRotationDesc, rotationConstraints]

private theorem eq_of_modEq_canon {a b : ℤ}
    (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] at h

/-! ## Extraction and hostile teeth -/

/-- The emitted expected-epoch gates force exact limb equality. -/
private theorem expected_exact
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    ∀ i, i < 4 → firstRow t (EXPECTED_EPOCH + i) = firstRow t (OLD_EPOCH + i) := by
  intro i hi
  have h := first_body_holds hsat hne (expectedBody i) (expected_gate_mem i hi)
  simp only [expectedBody, esub, eadd, eneg, emul, ev, ek, EmittedExpr.eval] at h
  have hm : firstRow t (EXPECTED_EPOCH + i) ≡ firstRow t (OLD_EPOCH + i)
      [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp h
  have hzero : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  have rangeAt : ∀ c, c < PUBLIC_WIDTH →
      0 ≤ firstRow t c ∧ firstRow t c < 65536 := by
    intro col hcol
    have hr : (⟨col, 16⟩ : VmRange) ∈ pqIdentityRotationDesc.ranges := by
      simp [pqIdentityRotationDesc, rotationRanges, hcol]
    simpa [VmRange.holds, envAt, firstRow,
      Dregg2.Circuit.DescriptorIR2.zeroAsg] using hsat.rowRanges 0 hzero _ hr
  have heBound : EXPECTED_EPOCH + i < PUBLIC_WIDTH := by
    have h40 : 36 + i < 36 + 4 := Nat.add_lt_add_left hi 36
    exact lt_trans h40 (by decide)
  have hoBound : OLD_EPOCH + i < PUBLIC_WIDTH := by
    have h36 : 32 + i < 32 + 4 := Nat.add_lt_add_left hi 32
    exact lt_trans h36 (by decide)
  have he := rangeAt (EXPECTED_EPOCH + i) heBound
  have ho := rangeAt (OLD_EPOCH + i) hoBound
  exact eq_of_modEq_canon ⟨he.1, lt_trans he.2 (by decide)⟩
    ⟨ho.1, lt_trans ho.2 (by decide)⟩ hm

/-- The four successor equations lift from field congruences to exact integer
equalities because every epoch/carry side is below `2^17 < BabyBear.p`. -/
private theorem successor_exact
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    let a := firstRow t
    a NEW_EPOCH + 65536 * a CARRY = a OLD_EPOCH + 1 ∧
    a (NEW_EPOCH + 1) + 65536 * a (CARRY + 1) =
      a (OLD_EPOCH + 1) + a CARRY ∧
    a (NEW_EPOCH + 2) + 65536 * a (CARRY + 2) =
      a (OLD_EPOCH + 2) + a (CARRY + 1) ∧
    a (NEW_EPOCH + 3) = a (OLD_EPOCH + 3) + a (CARRY + 2) := by
  dsimp
  have hc0 := carry_range hsat hne 0 (by omega)
  have hc1 := carry_range hsat hne 1 (by omega)
  have hc2 := carry_range hsat hne 2 (by omega)
  have hc0' : 0 ≤ firstRow t CARRY ∧ firstRow t CARRY < 2 := by simpa using hc0
  have hc1' : 0 ≤ firstRow t (CARRY + 1) ∧ firstRow t (CARRY + 1) < 2 := by
    simpa using hc1
  have hc2' : 0 ≤ firstRow t (CARRY + 2) ∧ firstRow t (CARRY + 2) < 2 := by
    simpa using hc2
  have rangeAt : ∀ c, c < PUBLIC_WIDTH →
      0 ≤ firstRow t c ∧ firstRow t c < 65536 := by
    intro c hc
    have hzero : 0 < t.rows.length := by
      cases hr : t.rows with
      | nil => exact absurd hr hne
      | cons _ _ => simp
    have hr : (⟨c, 16⟩ : VmRange) ∈ pqIdentityRotationDesc.ranges := by
      simp [pqIdentityRotationDesc, rotationRanges, hc]
    simpa [VmRange.holds, envAt, firstRow] using hsat.rowRanges 0 hzero _ hr
  have hn0 := rangeAt NEW_EPOCH (by decide)
  have hn1 := rangeAt (NEW_EPOCH + 1) (by decide)
  have hn2 := rangeAt (NEW_EPOCH + 2) (by decide)
  have hn3 := rangeAt (NEW_EPOCH + 3) (by decide)
  have ho0 := rangeAt OLD_EPOCH (by decide)
  have ho1 := rangeAt (OLD_EPOCH + 1) (by decide)
  have ho2 := rangeAt (OLD_EPOCH + 2) (by decide)
  have ho3 := rangeAt (OLD_EPOCH + 3) (by decide)
  have h0 := first_body_holds hsat hne succBody0 (successor_gate_mem 0 (by omega))
  have h1 := first_body_holds hsat hne succBody1 (successor_gate_mem 1 (by omega))
  have h2 := first_body_holds hsat hne succBody2 (successor_gate_mem 2 (by omega))
  have h3 := first_body_holds hsat hne succBody3 (successor_gate_mem 3 (by omega))
  simp only [succBody0, succBody1, succBody2, succBody3, esub, eadd, eneg, emul, ev, ek,
    EmittedExpr.eval] at h0 h1 h2 h3
  have hm0 : firstRow t NEW_EPOCH + 65536 * firstRow t CARRY
      ≡ firstRow t OLD_EPOCH + 1 [ZMOD 2013265921] :=
    (gate_modEq_iff (x := firstRow t NEW_EPOCH + 65536 * firstRow t CARRY +
        -1 * (firstRow t OLD_EPOCH + 1))
      (a := firstRow t NEW_EPOCH + 65536 * firstRow t CARRY)
      (b := firstRow t OLD_EPOCH + 1) (by ring)).mp h0
  have hm1 : firstRow t (NEW_EPOCH + 1) + 65536 * firstRow t (CARRY + 1)
      ≡ firstRow t (OLD_EPOCH + 1) + firstRow t CARRY [ZMOD 2013265921] :=
    (gate_modEq_iff
      (x := firstRow t (NEW_EPOCH + 1) + 65536 * firstRow t (CARRY + 1) +
        -1 * (firstRow t (OLD_EPOCH + 1) + firstRow t CARRY))
      (a := firstRow t (NEW_EPOCH + 1) + 65536 * firstRow t (CARRY + 1))
      (b := firstRow t (OLD_EPOCH + 1) + firstRow t CARRY) (by ring)).mp h1
  have hm2 : firstRow t (NEW_EPOCH + 2) + 65536 * firstRow t (CARRY + 2)
      ≡ firstRow t (OLD_EPOCH + 2) + firstRow t (CARRY + 1) [ZMOD 2013265921] :=
    (gate_modEq_iff
      (x := firstRow t (NEW_EPOCH + 2) + 65536 * firstRow t (CARRY + 2) +
        -1 * (firstRow t (OLD_EPOCH + 2) + firstRow t (CARRY + 1)))
      (a := firstRow t (NEW_EPOCH + 2) + 65536 * firstRow t (CARRY + 2))
      (b := firstRow t (OLD_EPOCH + 2) + firstRow t (CARRY + 1)) (by ring)).mp h2
  have hm3 : firstRow t (NEW_EPOCH + 3)
      ≡ firstRow t (OLD_EPOCH + 3) + firstRow t (CARRY + 2) [ZMOD 2013265921] :=
    (gate_modEq_iff
      (x := firstRow t (NEW_EPOCH + 3) +
        -1 * (firstRow t (OLD_EPOCH + 3) + firstRow t (CARRY + 2)))
      (a := firstRow t (NEW_EPOCH + 3))
      (b := firstRow t (OLD_EPOCH + 3) + firstRow t (CARRY + 2)) (by ring)).mp h3
  constructor
  · exact eq_of_modEq_canon
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hm0
  constructor
  · exact eq_of_modEq_canon
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hm1
  constructor
  · exact eq_of_modEq_canon
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hm2
  · exact eq_of_modEq_canon
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hm3

/-- The Bezout gate makes equality of all old/new key limbs impossible. -/
private theorem key_lanes_differ
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    ¬ (∀ i, i < 16 → firstRow t (NEW_KEY + i) = firstRow t (OLD_KEY + i)) := by
  intro hall
  have h := first_body_holds hsat hne keyNeqBody key_neq_gate_mem
  have h0 : keyNeqBody.eval (firstRow t) = -1 := by
    have hz : ∀ i, i ∈ List.range 16 →
        (keyDiffTerm i).eval (firstRow t) = 0 := by
      intro i hi
      have hil : i < 16 := by simpa using hi
      simp [keyDiffTerm, esub, eadd, eneg, emul, ev, ek, EmittedExpr.eval,
        hall i hil]
    have hfold : ∀ (xs : List Nat) (acc : EmittedExpr),
        (∀ i ∈ xs, (keyDiffTerm i).eval (firstRow t) = 0) →
        (xs.foldl (fun z i => eadd z (keyDiffTerm i)) acc).eval (firstRow t)
          = acc.eval (firstRow t) := by
      intro xs
      induction xs with
      | nil => intro acc _; rfl
      | cons x xs ih =>
          intro acc hx
          simp only [List.foldl_cons]
          rw [ih (eadd acc (keyDiffTerm x)) (by
            intro i hi
            exact hx i (by simp [hi]))]
          simp [eadd, EmittedExpr.eval, hx x (by simp)]
    exact (hfold (List.range 16) (ek (-1)) hz).trans (by
      simp [ek, EmittedExpr.eval])
  rw [h0] at h
  norm_num [Int.ModEq] at h

/-- **THE ROW REFINEMENT.** A satisfying descriptor row plus an exact readout
forces the semantic non-cryptographic rotation law: same target, exact expected
epoch, exact one-step increment without overflow, and changed key commitment. -/
theorem satisfied_implies_exact_rotation
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} {c : RotationClaim}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (rd : RotationReadout (firstRow t) c) :
    ExactRotation c := by
  have htarget : c.after.target = c.before.target := by
    apply commitmentToLanes16_injective
    funext i
    apply Fin.ext
    have hb := rd.targetBefore i
    have ha := rd.targetAfter i
    omega
  have hexp : c.expectedEpoch = c.before.epoch := by
    funext i
    apply Fin.ext
    have h := expected_exact hsat hne i.1 i.2
    have he := rd.expectedEpoch i
    have ho := rd.oldEpoch i
    omega
  have hs := successor_exact hsat hne
  have hepoch : epochValue c.after.epoch = epochValue c.before.epoch + 1 := by
    have h0 := hs.1
    have h1 := hs.2.1
    have h2 := hs.2.2.1
    have h3 := hs.2.2.2
    have ro0 : firstRow t OLD_EPOCH = (c.before.epoch 0).1 := by
      simpa using rd.oldEpoch 0
    have ro1 : firstRow t (OLD_EPOCH + 1) = (c.before.epoch 1).1 := by
      simpa using rd.oldEpoch 1
    have ro2 : firstRow t (OLD_EPOCH + 2) = (c.before.epoch 2).1 := by
      simpa using rd.oldEpoch 2
    have ro3 : firstRow t (OLD_EPOCH + 3) = (c.before.epoch 3).1 := by
      simpa using rd.oldEpoch 3
    have rn0 : firstRow t NEW_EPOCH = (c.after.epoch 0).1 := by
      simpa using rd.newEpoch 0
    have rn1 : firstRow t (NEW_EPOCH + 1) = (c.after.epoch 1).1 := by
      simpa using rd.newEpoch 1
    have rn2 : firstRow t (NEW_EPOCH + 2) = (c.after.epoch 2).1 := by
      simpa using rd.newEpoch 2
    have rn3 : firstRow t (NEW_EPOCH + 3) = (c.after.epoch 3).1 := by
      simpa using rd.newEpoch 3
    rw [rn0, ro0] at h0
    rw [rn1, ro1] at h1
    rw [rn2, ro2] at h2
    rw [rn3, ro3] at h3
    have hInt : (epochValue c.after.epoch : ℤ) =
        (epochValue c.before.epoch : ℤ) + 1 := by
      simp only [epochValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      linear_combination h0 + 65536 * h1 + 4294967296 * h2 +
        281474976710656 * h3
    exact_mod_cast hInt
  have hkey : c.after.keyCommitment ≠ c.before.keyCommitment := by
    intro heq
    apply key_lanes_differ hsat hne
    intro i hi
    have hfi : i < 16 := hi
    let fi : Fin 16 := ⟨i, hfi⟩
    have ho := rd.oldKey fi
    have hn := rd.newKey fi
    calc
      firstRow t (NEW_KEY + i) =
          (commitmentToLanes16 c.after.keyCommitment fi).1 := hn
      _ = (commitmentToLanes16 c.before.keyCommitment fi).1 := by rw [heq]
      _ = firstRow t (OLD_KEY + i) := ho.symm
  exact ⟨htarget, hexp, hepoch, hkey⟩

/-- **Stale-epoch descriptor tooth.** No satisfying readout can carry an
expected epoch different from the committed old authority image. -/
theorem stale_epoch_unsat
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} {c : RotationClaim}
    (hne : t.rows ≠ []) (rd : RotationReadout (firstRow t) c)
    (hStale : c.expectedEpoch ≠ c.before.epoch) :
    ¬ Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t := by
  intro hsat
  exact stale_epoch_refused c hStale (satisfied_implies_exact_rotation hsat hne rd)

/-- **Wrong-key descriptor tooth.** A readout that keeps the same key cannot
satisfy the emitted Bezout gate. -/
theorem unchanged_key_unsat
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} {c : RotationClaim}
    (hne : t.rows ≠ []) (rd : RotationReadout (firstRow t) c)
    (hSame : c.after.keyCommitment = c.before.keyCommitment) :
    ¬ Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t := by
  intro hsat
  exact unchanged_key_refused c hSame (satisfied_implies_exact_rotation hsat hne rd)

/-- All 108 exact-image columns are PI-bound in the emitted object.  Public-input
canonicality upgrades these field equalities to integer equalities. -/
theorem public_image_bound
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash pqIdentityRotationDesc minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hpub : ∀ i, i < PUBLIC_WIDTH → 0 ≤ t.pub i ∧ t.pub i < 2013265921) :
    ∀ i, i < PUBLIC_WIDTH → firstRow t i = t.pub i := by
  intro i hi
  have hzero : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  have hm := hsat.rowConstraints 0 hzero
    (.base (.piBinding .first i i)) (by
      simp [pqIdentityRotationDesc, rotationConstraints, publicPins, hi])
  simp only [VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at hm
  have hc := hsat.rowRanges 0 hzero (⟨i, 16⟩ : VmRange) (by
    simp [pqIdentityRotationDesc, rotationRanges, hi])
  have hmod : firstRow t i ≡ t.pub i [ZMOD 2013265921] := by
    simpa only [firstRow] using hm (by decide)
  have hcanon16 : 0 ≤ firstRow t i ∧ firstRow t i < 65536 := by
    simpa [VmRange.holds, envAt, firstRow,
      Dregg2.Circuit.DescriptorIR2.zeroAsg] using hc
  have hcanon : 0 ≤ firstRow t i ∧ firstRow t i < 2013265921 :=
    ⟨hcanon16.1, by omega⟩
  unfold Int.ModEq at hmod
  rw [Int.emod_eq_of_lt hcanon.1 hcanon.2,
    Int.emod_eq_of_lt (hpub i hi).1 (hpub i hi).2] at hmod
  exact hmod

#assert_axioms satisfied_implies_exact_rotation
#assert_axioms stale_epoch_unsat
#assert_axioms unchanged_key_unsat
#assert_axioms public_image_bound

end Dregg2.Circuit.Emit.PqIdentityAuthorityEmit
