/-
# Dregg2.Crypto.PrivateGraphRewriteDescriptor

Lean-authored IR2 for one bounded private graph-rewrite step.  Rust is only a
witness filler for this object.  The public ABI is

  [domain, session, version, shape, index,
   ruleset_root8, old_graph_root8, new_graph_root8].

The old/new root octets are adjacent history endpoints.  The hidden relation
carries an arbitrary bounded rule (two LHS + two RHS slots), four-variable
injective substitution, two preserved context slots, a complete private
two-rule ruleset opening, and a six-step controlled-swap network for matching
the old graph in arbitrary order.  The fixed adjacent swap schedule
`[01,12,23,01,12,01]` realizes every permutation of four slots; the AIR proves
each swap/copy.  The new graph is intentionally canonical
`context ++ instantiated RHS`, so its public root names the exact generic
`RewriteStep` endpoint used by later history linkage.

Semantically this is injective match-driven bounded hyperedge replacement, not
categorical DPO.  In particular the v1 AIR does not assert RHS-only freshness or
the dangling condition for LHS-only variables; those remain named follow-on
teeth rather than being hidden behind the word "rewrite".
-/
import Dregg2.Crypto.PrivateGraphRewrite
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.GateExpr

namespace Dregg2.Crypto.PrivateGraphRewriteDescriptor

open Dregg2.Crypto.PrivateGraphRewrite
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
   ChipTableSoundN chipLookupTupleN chip_lookup_sound_N emitVmJson2
   rangeTableDef ChipArityAdmitted)

set_option autoImplicit false
set_option maxRecDepth 10000

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))
def eqBody (left right : EmittedExpr) : EmittedExpr := sub left right

def DOMAIN : Nat := 0
def SESSION : Nat := 1
def VERSION : Nat := 2
def SHAPE : Nat := 3
def RULE_SLOT : Nat := 4
def OLD_BLIND_BASE : Nat := 5
def NEW_BLIND_BASE : Nat := 9
def RULE_BLIND_BASE : Nat := 13
def SIGMA_BASE : Nat := 21
def SIGMA_INV_BASE : Nat := 25
def RULE_BASE : Nat := 31
def CONTEXT_BASE : Nat := 95
def OLD_STAGE_BASE : Nat := 103
def NEW_STAGE_BASE : Nat := 215
def OLD_SWAP_BASE : Nat := 231
def OLD_CORE_BASE : Nat := 237
def OLD_ROOT_BASE : Nat := 245
def NEW_CORE_BASE : Nat := 253
def NEW_ROOT_BASE : Nat := 261
def RULE0_CORE_BASE : Nat := 269
def RULE0_LEAF_BASE : Nat := 277
def RULE1_CORE_BASE : Nat := 285
def RULE1_LEAF_BASE : Nat := 293
def RULESET_ROOT_BASE : Nat := 301
def INDEX : Nat := 309
def TRACE_WIDTH : Nat := 310
def PI_COUNT : Nat := 29

def blindCol (base lane : Nat) : Nat := base + lane
def ruleBlindCol (rule lane : Nat) : Nat := RULE_BLIND_BASE + 4 * rule + lane
def sigmaCol (i : Nat) : Nat := SIGMA_BASE + i
def sigmaInvCol (pair : Nat) : Nat := SIGMA_INV_BASE + pair

def ruleCol (rule slot field : Nat) : Nat := RULE_BASE + 32 * rule + 8 * slot + field
def R_ACTIVE : Nat := 0
def R_LABEL : Nat := 1
def R_SRC : Nat := 2
def R_DST : Nat := 3
def R_SRC_B0 : Nat := 4
def R_SRC_B1 : Nat := 5
def R_DST_B0 : Nat := 6
def R_DST_B1 : Nat := 7

def contextCol (slot field : Nat) : Nat := CONTEXT_BASE + 4 * slot + field
def E_ACTIVE : Nat := 0
def E_LABEL : Nat := 1
def E_SRC : Nat := 2
def E_DST : Nat := 3

def stageCol (base stage slot field : Nat) : Nat :=
  base + 16 * stage + 4 * slot + field

def oldStage := stageCol OLD_STAGE_BASE
def newStage := stageCol NEW_STAGE_BASE

def swapPair : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (2, 3)
  | 3 => (0, 1)
  | 4 => (1, 2)
  | 5 => (0, 1)

/-- Semantic form of one controlled swap in the fixed six-comparator network.
The descriptor applies the same control bit to all four fields of a slot. -/
def controlledSwap4 {α : Type} (stage : Fin 6) (bit : Bool)
    (xs : Fin 4 → α) (slot : Fin 4) : α :=
  if bit then
    if slot = (swapPair stage).1 then xs (swapPair stage).2
    else if slot = (swapPair stage).2 then xs (swapPair stage).1
    else xs slot
  else xs slot

/-- Each comparator preserves the exact four-slot multiset.  This is the
finite permutation kernel used by the final AIR-to-`BoundedOneStep` packaging. -/
theorem controlledSwap4_perm {α : Type} (stage : Fin 6) (bit : Bool)
    (xs : Fin 4 → α) :
    (List.ofFn xs).Perm (List.ofFn (controlledSwap4 stage bit xs)) := by
  fin_cases stage <;> cases bit <;>
    change [xs 0, xs 1, xs 2, xs 3].Perm [_, _, _, _] <;>
    simp [controlledSwap4, swapPair]
  all_goals exact List.Perm.swap _ _ _

/-- Chaining all six authored comparators cannot create, delete, or duplicate
a host-edge slot. -/
theorem six_controlled_swaps_perm {α : Type}
    (x0 x1 x2 x3 x4 x5 x6 : Fin 4 → α) (b0 b1 b2 b3 b4 b5 : Bool)
    (h1 : x1 = controlledSwap4 0 b0 x0)
    (h2 : x2 = controlledSwap4 1 b1 x1)
    (h3 : x3 = controlledSwap4 2 b2 x2)
    (h4 : x4 = controlledSwap4 3 b3 x3)
    (h5 : x5 = controlledSwap4 4 b4 x4)
    (h6 : x6 = controlledSwap4 5 b5 x5) :
    (List.ofFn x0).Perm (List.ofFn x6) := by
  have hp1 : (List.ofFn x0).Perm (List.ofFn x1) := by
    rw [h1]; exact controlledSwap4_perm 0 b0 x0
  have hp2 : (List.ofFn x1).Perm (List.ofFn x2) := by
    rw [h2]; exact controlledSwap4_perm 1 b1 x1
  have hp3 : (List.ofFn x2).Perm (List.ofFn x3) := by
    rw [h3]; exact controlledSwap4_perm 2 b2 x2
  have hp4 : (List.ofFn x3).Perm (List.ofFn x4) := by
    rw [h4]; exact controlledSwap4_perm 3 b3 x3
  have hp5 : (List.ofFn x4).Perm (List.ofFn x5) := by
    rw [h5]; exact controlledSwap4_perm 4 b4 x4
  have hp6 : (List.ofFn x5).Perm (List.ofFn x6) := by
    rw [h6]; exact controlledSwap4_perm 5 b5 x5
  exact hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans hp6))))

def ruleFieldExprs (rule : Nat) : List EmittedExpr :=
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field => v (ruleCol rule slot field)

def stageFieldExprs (base : Nat) (stage : Nat) : List EmittedExpr :=
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field => v (stageCol base stage slot field)

def digestExprs (base : Nat) : List EmittedExpr :=
  (List.range 8).map fun lane => v (base + lane)

def blindExprs (base : Nat) : List EmittedExpr :=
  (List.range 4).map fun lane => v (base + lane)

def graphRootInputExprs (coreBase blindBase : Nat) (sideTag : Int) : List EmittedExpr :=
  digestExprs coreBase ++ blindExprs blindBase ++
    [v DOMAIN, v SESSION, v VERSION, c sideTag]

def ruleLeafInputExprs (coreBase rule : Nat) : List EmittedExpr :=
  digestExprs coreBase ++ (List.range 4).map (fun lane => v (ruleBlindCol rule lane)) ++
    [v DOMAIN, v VERSION, v SHAPE, c rule]

/-- ⚑ Was this file's own re-derivation of the mux; now `gMux` (`Dregg2.Circuit.GateExpr`),
byte-identical (`choose_eq_old`) — no re-emit. `bit`/`zero`/`one` are arbitrary already-built
`EmittedExpr` sub-terms (not bare leaves), so the embed/render roundtrip (`ofEmitted`/`render
toEmitted`) is the right shape: it is the identity on every closed term, `render_ofEmitted`. -/
def choose (bit zero one : EmittedExpr) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gMux (Dregg2.Circuit.GateExpr.ofEmitted bit)
      (Dregg2.Circuit.GateExpr.ofEmitted zero) (Dregg2.Circuit.GateExpr.ofEmitted one))

/-- Byte-identical to the old hand-written body, for every input — the embedding round-trips
(`render_ofEmitted`), so `gMux` applied through it is exactly the old `add zero (mul bit (sub one
zero))`. -/
theorem choose_eq_old (bit zero one : EmittedExpr) :
    choose bit zero one = add zero (mul bit (sub one zero)) := by
  simp only [choose, Dregg2.Circuit.GateExpr.gMux, Dregg2.Circuit.GateExpr.render,
    Dregg2.Circuit.GateExpr.render_ofEmitted, add, mul, sub, neg, c]

def rulesetInputExprs : List EmittedExpr :=
  digestExprs RULE0_LEAF_BASE ++ digestExprs RULE1_LEAF_BASE

def graphCoreLookup (stageBase stage outBase : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN (stageFieldExprs stageBase stage) (List.range 8 |>.map (outBase + ·))⟩

/-- A wide hash site. The admitted-arity side condition rides through to `chipLookupTupleN`, so a
caller handing this an absorb block the chip AIR refuses fails to elaborate here rather than
emitting an unprovable lookup. -/
def hashLookup (inputs : List EmittedExpr) (outBase : Nat)
    (hAdm : ChipArityAdmitted inputs.length := by chip_arity_admitted) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN inputs (List.range 8 |>.map (outBase + ·)) hAdm⟩

def hashLookups : List VmConstraint2 :=
  [ graphCoreLookup OLD_STAGE_BASE 6 OLD_CORE_BASE
  , hashLookup (graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE GRAPH_STATE_TAG) OLD_ROOT_BASE
  , graphCoreLookup NEW_STAGE_BASE 0 NEW_CORE_BASE
  , hashLookup (graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE GRAPH_STATE_TAG) NEW_ROOT_BASE
  , hashLookup (ruleFieldExprs 0) RULE0_CORE_BASE
  , hashLookup (ruleLeafInputExprs RULE0_CORE_BASE 0) RULE0_LEAF_BASE
  , hashLookup (ruleFieldExprs 1) RULE1_CORE_BASE
  , hashLookup (ruleLeafInputExprs RULE1_CORE_BASE 1) RULE1_LEAF_BASE
  , hashLookup rulesetInputExprs RULESET_ROOT_BASE ]

def bitCols : List Nat :=
  [RULE_SLOT] ++
  ((List.range 2).flatMap fun rule =>
    (List.range 4).map fun slot => ruleCol rule slot R_ACTIVE) ++
  ((List.range 2).flatMap fun rule =>
    (List.range 4).flatMap fun slot =>
      [ruleCol rule slot R_SRC_B0, ruleCol rule slot R_SRC_B1,
       ruleCol rule slot R_DST_B0, ruleCol rule slot R_DST_B1]) ++
  ((List.range 2).map fun slot => contextCol slot E_ACTIVE) ++
  ((List.range 7).flatMap fun stage =>
    (List.range 4).map fun slot => oldStage stage slot E_ACTIVE) ++
  ((List.range 4).map fun slot => newStage 0 slot E_ACTIVE) ++
  (List.range 6 |>.map (OLD_SWAP_BASE + ·)) ++
  []

def binaryBodies : List EmittedExpr := bitCols.map binaryBody

def ruleVarBodies : List EmittedExpr :=
  (List.range 2).flatMap fun rule =>
    (List.range 4).flatMap fun slot =>
      [ eqBody (v (ruleCol rule slot R_SRC))
          (add (v (ruleCol rule slot R_SRC_B0))
            (mul (c 2) (v (ruleCol rule slot R_SRC_B1))))
      , eqBody (v (ruleCol rule slot R_DST))
          (add (v (ruleCol rule slot R_DST_B0))
            (mul (c 2) (v (ruleCol rule slot R_DST_B1)))) ]

def paddingBodies : List EmittedExpr :=
  ((List.range 2).flatMap fun rule =>
    (List.range 4).flatMap fun slot =>
      (List.range 3).map fun k =>
        mul (sub (c 1) (v (ruleCol rule slot R_ACTIVE)))
          (v (ruleCol rule slot (1 + k)))) ++
  ((List.range 2).flatMap fun slot =>
    (List.range 3).map fun k =>
      mul (sub (c 1) (v (contextCol slot E_ACTIVE))) (v (contextCol slot (1 + k))))

def sigmaPairs : List (Nat × Nat) := [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def sigmaInjectiveBodies : List EmittedExpr :=
  sigmaPairs.zipIdx.map fun (pair, idx) =>
    sub (mul (sub (v (sigmaCol pair.1)) (v (sigmaCol pair.2))) (v (sigmaInvCol idx))) (c 1)

def lhsNonemptyBody : EmittedExpr :=
  choose (v RULE_SLOT)
    (mul (sub (c 1) (v (ruleCol 0 0 R_ACTIVE)))
      (sub (c 1) (v (ruleCol 0 1 R_ACTIVE))))
    (mul (sub (c 1) (v (ruleCol 1 0 R_ACTIVE)))
      (sub (c 1) (v (ruleCol 1 1 R_ACTIVE))))

def muxSigma (rule slot : Nat) (src : Bool) : EmittedExpr :=
  let b0 := v (ruleCol rule slot (if src then R_SRC_B0 else R_DST_B0))
  let b1 := v (ruleCol rule slot (if src then R_SRC_B1 else R_DST_B1))
  let low := choose b0 (v (sigmaCol 0)) (v (sigmaCol 1))
  let high := choose b0 (v (sigmaCol 2)) (v (sigmaCol 3))
  choose b1 low high

def selectedRuleActive (slot : Nat) : EmittedExpr :=
  choose (v RULE_SLOT)
    (v (ruleCol 0 slot R_ACTIVE))
    (v (ruleCol 1 slot R_ACTIVE))

def sourceBodies (stageBase : Nat) (rhs : Bool) : List EmittedExpr :=
  let ruleOff := if rhs then 2 else 0
  ((List.range 2).flatMap fun slot =>
    (List.range 4).map fun field =>
      eqBody (v (stageCol stageBase 0 slot field)) (v (contextCol slot field))) ++
  ((List.range 2).flatMap fun slot =>
    [ eqBody (v (stageCol stageBase 0 (2 + slot) E_ACTIVE))
        (choose (v RULE_SLOT)
          (v (ruleCol 0 (ruleOff + slot) R_ACTIVE))
          (v (ruleCol 1 (ruleOff + slot) R_ACTIVE)))
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_LABEL))
        (choose (v RULE_SLOT)
          (v (ruleCol 0 (ruleOff + slot) R_LABEL))
          (v (ruleCol 1 (ruleOff + slot) R_LABEL)))
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_SRC))
        (mul (selectedRuleActive (ruleOff + slot))
          (choose (v RULE_SLOT)
            (muxSigma 0 (ruleOff + slot) true)
            (muxSigma 1 (ruleOff + slot) true)))
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_DST))
        (mul (selectedRuleActive (ruleOff + slot))
          (choose (v RULE_SLOT)
            (muxSigma 0 (ruleOff + slot) false)
            (muxSigma 1 (ruleOff + slot) false))) ])

def swapStageBodies (stageBase swapBase : Nat) (stage : Fin 6) : List EmittedExpr :=
  let pair := swapPair stage
  let bit := v (swapBase + stage.val)
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field =>
      let source := v (stageCol stageBase stage.val slot field)
      let partner :=
        if slot = pair.1.val then v (stageCol stageBase stage.val pair.2.val field)
        else if slot = pair.2.val then v (stageCol stageBase stage.val pair.1.val field)
        else source
      eqBody (v (stageCol stageBase (stage.val + 1) slot field)) (choose bit source partner)

def swapBodies (stageBase swapBase : Nat) : List EmittedExpr :=
  (List.ofFn fun stage : Fin 6 => swapStageBodies stageBase swapBase stage).flatten

def metadataBodies : List EmittedExpr :=
  [eqBody (v VERSION) (c PROTOCOL_VERSION), eqBody (v SHAPE) (c SHAPE_ID)]

def semanticBodies : List EmittedExpr :=
  metadataBodies ++ binaryBodies ++ ruleVarBodies ++ paddingBodies ++
  sigmaInjectiveBodies ++ [lhsNonemptyBody] ++
  sourceBodies OLD_STAGE_BASE false ++ sourceBodies NEW_STAGE_BASE true ++
  swapBodies OLD_STAGE_BASE OLD_SWAP_BASE

def rangeCols : List Nat :=
  (List.range 2).flatMap (fun rule =>
    (List.range 4).flatMap (fun slot => [ruleCol rule slot R_LABEL])) ++
  (List.range 2).flatMap (fun slot =>
    [contextCol slot E_LABEL, contextCol slot E_SRC, contextCol slot E_DST]) ++
  (List.range 4).map sigmaCol

def rangeLookups : List VmConstraint2 :=
  rangeCols.map fun col => .lookup ⟨TableId.range, [v col]⟩

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first DOMAIN 0)
  , .base (.piBinding .first SESSION 1)
  , .base (.piBinding .first VERSION 2)
  , .base (.piBinding .first SHAPE 3)
  , .base (.piBinding .first INDEX 4) ] ++
  ((List.range 8).map fun lane => .base (.piBinding .first (RULESET_ROOT_BASE + lane) (5 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (OLD_ROOT_BASE + lane) (13 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (NEW_ROOT_BASE + lane) (21 + lane)))

def privateGraphRewriteDescriptor : EffectVmDescriptor2 :=
  { name := "private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [rangeTableDef 4]
  , constraints := hashLookups ++ rangeLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privateGraphRewriteDescriptor.traceWidth == 310
#guard privateGraphRewriteDescriptor.piCount == 29
#guard hashLookups.length == 9
#guard publicPins.length == 29
#guard rangeLookups.length == 18
#guard (emitVmJson2 privateGraphRewriteDescriptor).contains
  "private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1"
#guard !(emitVmJson2 privateGraphRewriteDescriptor).contains "1347571253"

def zeroAsg : Assignment := fun _ => 0
def emptyTf : TraceFamily := fun _ => []
def emptyTrace : VmTrace where
  rows := [zeroAsg, zeroAsg, zeroAsg, zeroAsg]
  pub := zeroAsg
  tf := emptyTf

def ppM0 : Int → Int := fun _ => 0
def ppF0 : Int → Int × Nat := fun _ => (0, 0)

def constTrace (a pis : Assignment) (tf : TraceFamily) :
    VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_pub0 (a pis : Assignment) (tf : TraceFamily) :
    (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0).pub = pis := rfl

@[simp] theorem constTrace_tf (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).tf = tf := rfl

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := rfl

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < 2013265921

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, hpin]

theorem hash_lookup_mem {lookup : VmConstraint2} (h : lookup ∈ hashLookups) :
    lookup ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, h]

theorem semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

theorem public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

theorem constraint_holds_at_zero
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {constraint : VmConstraint2}
    (hmem : constraint ∈ privateGraphRewriteDescriptor.constraints) :
    constraint.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) constraint hmem
  simpa using h

structure EmittedRewriteFacts (hash : List Int → Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  gates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD 2013265921]
  pins : ∀ col pi, VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD 2013265921]
  hashes : ∀ lookup ∈ hashLookups,
    lookup.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false
  ranges : ∀ lookup ∈ rangeLookups,
    lookup.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false

/-- First Satisfied2→semantics bridge: satisfaction exposes every authored
match/delete/glue, permutation-network, padding, injectivity and ABI equation.
The next theorem layer lifts these modular equations and the seven chip lookups
into `PrivateGraphRewrite.Accepts`. -/
theorem privateGraphRewrite_emitted_facts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    EmittedRewriteFacts hash a pis tf :=
  ⟨fun _ hb => semantic_gate_vanishes hsat hb,
   fun _ _ hp => public_pin_sound hsat hp,
   fun _ hl => constraint_holds_at_zero hsat (hash_lookup_mem hl),
   fun _ hl => constraint_holds_at_zero hsat (by
     simp [privateGraphRewriteDescriptor, hl])⟩

/-! ## Exact finite decode boundary

The raw facts above are deliberately stated at the `Satisfied2` interface.
This next layer discharges three easy-to-overlook parts of the semantic lift:

* every authored bit is an actual integer `0` or `1`, not merely a residue;
* every label/node/substitution cell routed through the four-bit table is
  genuinely in `[0,16)`;
* all nine eight-felt digest blocks are the full wide chip output, and public
  pins are exact canonical integers.

What remains after this layer is purely the finite structural decode: turn the
controlled-swap equations into `List.Perm`, package the padded columns as the
bounded witness, and identify those nine wide outputs with `Accepts`.  No
cryptographic or range-table assumption is hidden in that residual.
-/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD 2013265921])
    (hx : 0 ≤ x ∧ x < 2013265921)
    (hy : 0 ≤ y ∧ y < 2013265921) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  omega

theorem binary_of_modular_gate {a : Assignment} {col : Nat}
    (hcanon : CanonicalAssignment a)
    (hmod : (binaryBody col).eval a ≡ 0 [ZMOD 2013265921]) :
    a col = 0 ∨ a col = 1 := by
  have hev : (binaryBody col).eval a = a col * (a col - 1) := by
    simp only [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
    ring
  rw [hev] at hmod
  have hd : (2013265921 : Int) ∣ a col * (a col - 1) := by
    simpa using Int.modEq_zero_iff_dvd.mp hmod
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx
    left
    have hc := hcanon col
    omega
  · obtain ⟨k, hk⟩ := hx
    right
    have hc := hcanon col
    omega

theorem binary_body_mem_of_bit_col {col : Nat} (hcol : col ∈ bitCols) :
    binaryBody col ∈ semanticBodies := by
  have hb : binaryBody col ∈ binaryBodies := List.mem_map_of_mem hcol
  simp only [semanticBodies, List.mem_append]
  aesop

/-- Every boolean control in the deployed descriptor is an honest integer bit. -/
theorem privateGraphRewrite_bits_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    ∀ col ∈ bitCols, a col = 0 ∨ a col = 1 := by
  intro col hcol
  exact binary_of_modular_gate hcanon
    (semantic_gate_vanishes hsat (binary_body_mem_of_bit_col hcol))

theorem range_lookup_mem_of_col {col : Nat} (hcol : col ∈ rangeCols) :
    VmConstraint2.lookup ⟨TableId.range, [v col]⟩ ∈ rangeLookups := by
  exact List.mem_map.mpr ⟨col, hcol, rfl⟩

/-- Against the descriptor's faithful four-bit table, every range-routed cell
is a genuine small integer. -/
theorem privateGraphRewrite_range_col_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hrange : tf TableId.range = Dregg2.Circuit.DescriptorIR2.rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) {col : Nat} (hcol : col ∈ rangeCols) :
    0 ≤ a col ∧ a col < 16 := by
  have hrow := hsat.rowConstraints 0 (by simp [constTrace]) _
    (show VmConstraint2.lookup ⟨TableId.range, [v col]⟩ ∈
      privateGraphRewriteDescriptor.constraints from by
        simp [privateGraphRewriteDescriptor, range_lookup_mem_of_col hcol])
  have hmem : [a col] ∈ tf TableId.range := by
    simpa [VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, constTrace,
      Dregg2.Circuit.DescriptorIR2.envAt, v, EmittedExpr.eval] using hrow
  rw [hrange] at hmem
  have hb := (Dregg2.Circuit.DescriptorIR2.range_row_mem_iff (a col) 4).mp hmem
  norm_num at hb ⊢
  exact hb

/-- Generic full-width extraction for any of this descriptor's nine Poseidon
lookups.  The arity-tagged chip row identifies all eight output lanes. -/
theorem wide_hash_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {inputs : List EmittedExpr} {outCols : List Nat}
    (hlen : ChipArityAdmitted inputs.length)
    (hlookup : VmConstraint2.lookup
      ⟨TableId.poseidon2, chipLookupTupleN inputs outCols hlen⟩ ∈ hashLookups) :
    outCols.map a = permOut (inputs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp [constTrace]) _
    (hash_lookup_mem hlookup)
  have hmem : (chipLookupTupleN inputs outCols).map (·.eval a) ∈
      tf TableId.poseidon2 := by
    simpa [VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, constTrace,
      Dregg2.Circuit.DescriptorIR2.envAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    inputs outCols hlen hmem

structure WideHashFacts (permOut : List Int → List Int) (a : Assignment) : Prop where
  oldCore : (digestExprs OLD_CORE_BASE).map (fun e => e.eval a) =
    permOut ((stageFieldExprs OLD_STAGE_BASE 6).map (fun e => e.eval a))
  oldRoot : (digestExprs OLD_ROOT_BASE).map (fun e => e.eval a) =
    permOut ((graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE GRAPH_STATE_TAG).map
      (fun e => e.eval a))
  newCore : (digestExprs NEW_CORE_BASE).map (fun e => e.eval a) =
    permOut ((stageFieldExprs NEW_STAGE_BASE 0).map (fun e => e.eval a))
  newRoot : (digestExprs NEW_ROOT_BASE).map (fun e => e.eval a) =
    permOut ((graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE GRAPH_STATE_TAG).map
      (fun e => e.eval a))
  rule0Core : (digestExprs RULE0_CORE_BASE).map (fun e => e.eval a) =
    permOut ((ruleFieldExprs 0).map (fun e => e.eval a))
  rule0Leaf : (digestExprs RULE0_LEAF_BASE).map (fun e => e.eval a) =
    permOut ((ruleLeafInputExprs RULE0_CORE_BASE 0).map (fun e => e.eval a))
  rule1Core : (digestExprs RULE1_CORE_BASE).map (fun e => e.eval a) =
    permOut ((ruleFieldExprs 1).map (fun e => e.eval a))
  rule1Leaf : (digestExprs RULE1_LEAF_BASE).map (fun e => e.eval a) =
    permOut ((ruleLeafInputExprs RULE1_CORE_BASE 1).map (fun e => e.eval a))
  rulesetRoot : (digestExprs RULESET_ROOT_BASE).map (fun e => e.eval a) =
    permOut (rulesetInputExprs.map (·.eval a))

theorem privateGraphRewrite_wide_hashes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) : WideHashFacts permOut a := by
  constructor
  · simpa [digestExprs, graphCoreLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := stageFieldExprs OLD_STAGE_BASE 6)
        (outCols := (List.range 8).map (OLD_CORE_BASE + ·))
        (by decide) (by simp [hashLookups, graphCoreLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE GRAPH_STATE_TAG)
        (outCols := (List.range 8).map (OLD_ROOT_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, graphCoreLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := stageFieldExprs NEW_STAGE_BASE 0)
        (outCols := (List.range 8).map (NEW_CORE_BASE + ·))
        (by decide) (by simp [hashLookups, graphCoreLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE GRAPH_STATE_TAG)
        (outCols := (List.range 8).map (NEW_ROOT_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := ruleFieldExprs 0)
        (outCols := (List.range 8).map (RULE0_CORE_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := ruleLeafInputExprs RULE0_CORE_BASE 0)
        (outCols := (List.range 8).map (RULE0_LEAF_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := ruleFieldExprs 1)
        (outCols := (List.range 8).map (RULE1_CORE_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := ruleLeafInputExprs RULE1_CORE_BASE 1)
        (outCols := (List.range 8).map (RULE1_LEAF_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))
  · simpa [digestExprs, hashLookup, v, Function.comp_def, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using
      (wide_hash_lookup_sound permOut hChip hsat
        (inputs := rulesetInputExprs)
        (outCols := (List.range 8).map (RULESET_ROOT_BASE + ·))
        (by decide) (by simp [hashLookups, hashLookup]))

theorem public_pin_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a) (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col = pis pi :=
  eq_of_modEq_of_canonical (public_pin_sound hsat hpin)
    (hcanon col) (hcanonPis pi)

structure DecodedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) : Prop where
  bits : ∀ col ∈ bitCols, a col = 0 ∨ a col = 1
  ranges : ∀ col ∈ rangeCols, 0 ≤ a col ∧ a col < 16
  hashes : WideHashFacts permOut a
  pins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins → a col = pis pi

/-- Strong theorem-first checkpoint toward `Satisfied2 → Accepts`: the field,
range, wide-chip, and canonical-PI parts of the bridge are fully discharged.
Only the finite list/permutation packaging remains. -/
theorem privateGraphRewrite_decoded_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a) (hcanonPis : CanonicalAssignment pis)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hrange : tf TableId.range = Dregg2.Circuit.DescriptorIR2.rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) : DecodedAirFacts permOut a pis :=
  ⟨privateGraphRewrite_bits_decoded hcanon hsat,
   fun _ hc => privateGraphRewrite_range_col_bounds hrange hsat hc,
   privateGraphRewrite_wide_hashes permOut hChip hsat,
   fun _ _ hp => public_pin_exact hcanon hcanonPis hsat hp⟩

#assert_all_clean [
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.controlledSwap4_perm,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.six_controlled_swaps_perm,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.semantic_gate_vanishes,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.public_pin_sound,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.constraint_holds_at_zero,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_emitted_facts,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_bits_decoded,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_range_col_bounds,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.wide_hash_lookup_sound,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_wide_hashes,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.public_pin_exact,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_decoded_air_sound]

end Dregg2.Crypto.PrivateGraphRewriteDescriptor
