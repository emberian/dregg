/-
# ExactFieldsRefusalEmit — exact FLD2/FLN2 refusal audit update

The deployed refusal changes the protocol-reserved overflow-field at raw key `2^32`.  This emitter
replaces the legacy scalar `mapOp` leaf with the exact fields-root V2 schema:

* leaf `FLD2 || occupancy || key_u16_le[4] || value_u16_le[16]`;
* node `FLN2 || left8 || right8`;
* the live rate-four `hash_many_8` schedule through the full state16 permutation bus;
* one shared sibling/direction path for the before leaf and its in-place after update;
* sixteen verifier-known audit limbs, bound as public inputs to the after leaf byte-for-byte.

The EffectVM trace is taller than the 16-level fields tree.  `active,count` define a forced monotone
prefix: first `(1,0)`, last `(0,16)`, `nextCount = count + active`, and active may never rise.  Thus
exactly rows 0..15 recompose the path; the falling edge pins both node digests to the committed
before/after fields-root groups.  State16 lookups remain unconditional, so inactive rows carry a
genuine repeated tuple rather than relying on a dummy table row.
-/
import Dregg2.Circuit.FullStateChip
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.ExactFieldsRefusalEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.GateExpr (gCols gVars toEmitted gEsub gSwapLeft gSwapRight idOps render)

set_option autoImplicit false

def DIGEST : Nat := 8
def STATE_LANES : Nat := 16
def VALUE_LIMBS : Nat := 16
def DEPTH : Nat := 16
def LEAF_STATE_STEPS : Nat := 7
def NODE_STATE_STEPS : Nat := 6

def FLD2 : Int := 0x464c4432
def FLN2 : Int := 0x464c4e32

/-! Column geometry; kept definitionally aligned with Rust `trace_rotated::REFUSAL_EXACT_*`. -/

/-- The exact-refusal appendix starts EXACTLY where the graduated rotated refusal host ends —
`refusalV3.traceWidth = (188 + APPENDIX_SPAN) + 7·(4 + |rotV3Appendix|)`. The literal is kept so the
whole column ladder below stays `rfl`-shaped, but the `#guard` under the ladder now WELDS it to that
host width: at the 178 → 184 ninth-lane flag day this moved 1647 → 1691 (`APPENDIX_SPAN` 521 → 537
and four more appendix sites, `+16 + 28 = +44`), and at the rc-FOLD flag day 1691 → 1707
(`APPENDIX_SPAN` 537 → 539 and two more appendix sites, `+2 + 14 = +16`), and at the FIELDS-CANONICITY
flag day 1707 → 1819 (`APPENDIX_SPAN` 539 → 651 — the 112 aux columns of
`Emit.FieldsCanonicity9Emit`; no new appendix site, so the graduation multiplier is unchanged), and
at the KEY-NONET flag day (2026-08-01, `rotatedNumPreLimbs` 184 → 187) 1819 → 1841 (`APPENDIX_SPAN`
651 → 659 and two more appendix sites, `+8 + 14 = +22` — the identical delta `CUSTOM_COMMIT_TEETH_COL`
took, 1791 → 1813, as at all three previous flag days). The guard went RED rather than silent all
four times — which is the whole reason the literal is allowed to exist, and the fourth time it went
red it stayed red for a day, because this file was not re-pinned with the rest of the flag day.
At the IROOT-WIDENING flag day (2026-11-07, 187 → 196) 1841 → 1907: `APPENDIX_SPAN` 659 → 683 and six
more appendix sites, `+24 + 42 = +66`, the delta `CUSTOM_COMMIT_TEETH_COL` took (1813 → 1879). -/
def BEFORE_BASE : Nat := 1907
def OCC_COL : Nat := BEFORE_BASE
def OLD_VALUE_BASE : Nat := OCC_COL + 1
def OLD_LEAF_STATE_BASE : Nat := OLD_VALUE_BASE + VALUE_LIMBS
def OLD_CUR_BASE : Nat := OLD_LEAF_STATE_BASE + LEAF_STATE_STEPS * STATE_LANES
def SIBLING_BASE : Nat := OLD_CUR_BASE + DIGEST
def OLD_LEFT_BASE : Nat := SIBLING_BASE + DIGEST
def OLD_RIGHT_BASE : Nat := OLD_LEFT_BASE + DIGEST
def OLD_NODE_STATE_BASE : Nat := OLD_RIGHT_BASE + DIGEST
def DIR_COL : Nat := OLD_NODE_STATE_BASE + NODE_STATE_STEPS * STATE_LANES
def AFTER_BASE : Nat := DIR_COL + 1
def NEW_VALUE_BASE : Nat := AFTER_BASE
def NEW_LEAF_STATE_BASE : Nat := NEW_VALUE_BASE + VALUE_LIMBS
def NEW_CUR_BASE : Nat := NEW_LEAF_STATE_BASE + LEAF_STATE_STEPS * STATE_LANES
def NEW_LEFT_BASE : Nat := NEW_CUR_BASE + DIGEST
def NEW_RIGHT_BASE : Nat := NEW_LEFT_BASE + DIGEST
def NEW_NODE_STATE_BASE : Nat := NEW_RIGHT_BASE + DIGEST
def ACTIVE_COL : Nat := NEW_NODE_STATE_BASE + NODE_STATE_STEPS * STATE_LANES
def COUNT_COL : Nat := ACTIVE_COL + 1
def TRACE_WIDTH : Nat := COUNT_COL + 1

def AUDIT_PI_BASE : Nat := 47
def AUDIT_PI_COUNT : Nat := 16

#guard BEFORE_BASE == 1907    -- ⚑ +66 at the IROOT-WIDENING flag day (was 1841; +22 at the KEY-NONET one)
#guard BEFORE_BASE == refusalV3.traceWidth   -- ⚑ the reality gate: no independent literal
#guard AFTER_BASE == 2165
#guard ACTIVE_COL == 2413
#guard TRACE_WIDTH == 2415
#guard AUDIT_PI_BASE == 39 + 8

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : Int) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (ek (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)
def activeGate (body : EmittedExpr) : EmittedExpr := emul (ev ACTIVE_COL) body

/-- ⚑ Column-reader family, factored: `gCols`/`gVars toEmitted` at `Dregg2.Circuit.GateExpr`. -/
def stateCols (base step : Nat) : List Nat := gCols (base + STATE_LANES * step) STATE_LANES
def chunks4 {alpha : Type} (xs : List alpha) : List (List alpha) := xs.toChunks 4

def initialStateExpr (inputLength : Nat) : List EmittedExpr :=
  (List.range STATE_LANES).map fun i => if i = 4 then .const inputLength else .const 0

def padChunk (chunk : List EmittedExpr) : List EmittedExpr :=
  chunk ++ List.replicate (4 - chunk.length) (.const 0)

def priorStateExpr (stateBase stage : Nat) : List EmittedExpr :=
  if stage = 0 then [] else (stateCols stateBase (stage - 1)).map .var

def absorbInputExpr (stateBase inputLength stage : Nat) (chunk : List EmittedExpr) :
    List EmittedExpr :=
  let prior := if stage = 0 then initialStateExpr inputLength else priorStateExpr stateBase stage
  let rate := padChunk chunk
  (List.range STATE_LANES).map fun i =>
    if i < 4 then eadd (prior.getD i (.const 0)) (rate.getD i (.const 0))
    else prior.getD i (.const 0)

structure State16Step where
  input : List EmittedExpr
  outputCols : List Nat
  /-- ⚑ **The state16 bus width, as a CHECKED construction obligation.** The lookup's arity tag IS
  `input.length` (`chipLookupTupleN`), and the deployed chip AIR admits only
  `{0, 2, 3, 4, 7, 11, 16}` — so a step built with anything but a full 16-lane state would emit a
  chip row no witness can satisfy, silently. Carrying the width here means such a step cannot be
  constructed at all. Both step kinds discharge it by reduction: an absorb input maps over
  `List.range STATE_LANES` and a squeeze input maps over `stateCols`, whose spines are literal. -/
  width : input.length = STATE_LANES := by exact of_decide_eq_true (Eq.refl true)
  deriving Repr

def spongePlan (stateBase : Nat) (preimage : List EmittedExpr) : List State16Step :=
  let chunks := chunks4 preimage
  let absorb := chunks.mapIdx fun stage chunk =>
    ⟨absorbInputExpr stateBase preimage.length stage chunk, stateCols stateBase stage,
      by exact of_decide_eq_true (Eq.refl true)⟩
  let squeeze :=
    ⟨(stateCols stateBase (chunks.length - 1)).map .var, stateCols stateBase chunks.length,
      by exact of_decide_eq_true (Eq.refl true)⟩
  absorb ++ [squeeze]

def spongeDigestCols (stateBase inputLength : Nat) : List Nat :=
  let absorbs := (inputLength + 3) / 4
  gCols (stateBase + STATE_LANES * (absorbs - 1)) 4 ++
    gCols (stateBase + STATE_LANES * absorbs) 4

def auditKeyLimbs : List EmittedExpr := [ek 0, ek 0, ek 1, ek 0]

def oldLeafPreimage : List EmittedExpr :=
  [ek FLD2, ev OCC_COL] ++ auditKeyLimbs ++ gVars toEmitted OLD_VALUE_BASE VALUE_LIMBS

def newLeafPreimage : List EmittedExpr :=
  [ek FLD2, ek 1] ++ auditKeyLimbs ++ gVars toEmitted NEW_VALUE_BASE VALUE_LIMBS

def oldLeafDigestCols : List Nat := spongeDigestCols OLD_LEAF_STATE_BASE oldLeafPreimage.length
def newLeafDigestCols : List Nat := spongeDigestCols NEW_LEAF_STATE_BASE newLeafPreimage.length

def oldNodePreimage : List EmittedExpr :=
  ek FLN2 :: (gVars toEmitted OLD_LEFT_BASE DIGEST ++ gVars toEmitted OLD_RIGHT_BASE DIGEST)

def newNodePreimage : List EmittedExpr :=
  ek FLN2 :: (gVars toEmitted NEW_LEFT_BASE DIGEST ++ gVars toEmitted NEW_RIGHT_BASE DIGEST)

def oldNodeDigestCols : List Nat := spongeDigestCols OLD_NODE_STATE_BASE oldNodePreimage.length
def newNodeDigestCols : List Nat := spongeDigestCols NEW_NODE_STATE_BASE newNodePreimage.length

#guard oldLeafPreimage.length == 22
#guard newLeafPreimage.length == 22
#guard oldNodePreimage.length == 17
#guard newNodePreimage.length == 17
#guard (spongePlan OLD_LEAF_STATE_BASE oldLeafPreimage).length == LEAF_STATE_STEPS
#guard (spongePlan OLD_NODE_STATE_BASE oldNodePreimage).length == NODE_STATE_STEPS

def state16Lookups : List VmConstraint2 :=
  (spongePlan OLD_LEAF_STATE_BASE oldLeafPreimage ++
    spongePlan NEW_LEAF_STATE_BASE newLeafPreimage ++
    spongePlan OLD_NODE_STATE_BASE oldNodePreimage ++
    spongePlan NEW_NODE_STATE_BASE newNodePreimage).map fun step =>
      .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols step.width⟩

/-- ⚑ Byte-identical to the old body via `GateExpr.gBoolEnc2` — this file's `esub` is the
`(−1)·1` encoding (`gEsub`'s shape, not `gBool`'s elided `.const (−1)`), so the byte-preserving
shared home is `gBoolEnc2`, not `gBool`. -/
def dirBinary : EmittedExpr :=
  activeGate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf DIR_COL)))

theorem dirBinary_eq : dirBinary = activeGate (emul (ev DIR_COL) (esub (ev DIR_COL) (ek 1))) := rfl

def occBinary : EmittedExpr :=
  activeGate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf OCC_COL)))

theorem occBinary_eq : occBinary = activeGate (emul (ev OCC_COL) (esub (ev OCC_COL) (ek 1))) := rfl

def activeBinary : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf ACTIVE_COL))

theorem activeBinary_eq : activeBinary = emul (ev ACTIVE_COL) (esub (ev ACTIVE_COL) (ek 1)) := rfl

def oldReservedCanonical (i : Fin VALUE_LIMBS) : EmittedExpr :=
  activeGate (emul (esub (ek 1) (ev OCC_COL)) (ev (OLD_VALUE_BASE + i.val)))

/-- `active · (left − the Merkle sibling-swap)`. ⚑ Byte-identical to the old body — this file
already wrote the compact `esub`/`eadd`/`emul` form, which IS `gEsub`/`gSwapLeft`'s shape, `rfl`. -/
def leftSelect (cur sibling left : Nat) : EmittedExpr :=
  activeGate (render toEmitted
    (gEsub idOps (.leaf left) (gSwapLeft (.leaf DIR_COL) (.leaf cur) (.leaf sibling))))

/-- Same re-derivation as `leftSelect`, `gSwapRight`. -/
def rightSelect (cur sibling right : Nat) : EmittedExpr :=
  activeGate (render toEmitted
    (gEsub idOps (.leaf right) (gSwapRight (.leaf DIR_COL) (.leaf cur) (.leaf sibling))))

def wl (c : Nat) : WindowExpr := .loc c
def wn (c : Nat) : WindowExpr := .nxt c
def wk (x : Int) : WindowExpr := .const x
def wa (a b : WindowExpr) : WindowExpr := .add a b
def wm (a b : WindowExpr) : WindowExpr := .mul a b
def wneg (a : WindowExpr) : WindowExpr := wm (wk (-1)) a
def ws (a b : WindowExpr) : WindowExpr := wa a (wneg b)

def progressConstraints : List VmConstraint2 :=
  [ .base (.gate activeBinary)
  , .base (.boundary .first (esub (ev ACTIVE_COL) (ek 1)))
  , .base (.boundary .first (ev COUNT_COL))
  , .base (.boundary .last (ev ACTIVE_COL))
  , .base (.boundary .last (esub (ev COUNT_COL) (ek DEPTH)))
  , .windowGate ⟨ws (wn COUNT_COL) (wa (wl COUNT_COL) (wl ACTIVE_COL)), true⟩
  , .windowGate ⟨wm (wn ACTIVE_COL) (ws (wk 1) (wl ACTIVE_COL)), true⟩ ]

def pathConstraints : List VmConstraint2 :=
  [ .base (.gate occBinary), .base (.gate dirBinary) ] ++
  (List.finRange VALUE_LIMBS).map (fun i => .base (.gate (oldReservedCanonical i))) ++
  (List.finRange DIGEST).flatMap (fun i =>
    [ .base (.gate (leftSelect (OLD_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (OLD_LEFT_BASE + i.val)))
    , .base (.gate (rightSelect (OLD_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (OLD_RIGHT_BASE + i.val)))
    , .base (.gate (leftSelect (NEW_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (NEW_LEFT_BASE + i.val)))
    , .base (.gate (rightSelect (NEW_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (NEW_RIGHT_BASE + i.val))) ]) ++
  (List.finRange DIGEST).flatMap (fun i =>
    [ .base (.boundary .first
        (esub (ev (OLD_CUR_BASE + i.val)) (ev (oldLeafDigestCols.getD i.val 0))))
    , .base (.boundary .first
        (esub (ev (NEW_CUR_BASE + i.val)) (ev (newLeafDigestCols.getD i.val 0))))
    , .windowGate ⟨wm (wn ACTIVE_COL)
        (ws (wn (OLD_CUR_BASE + i.val)) (wl (oldNodeDigestCols.getD i.val 0))), true⟩
    , .windowGate ⟨wm (wn ACTIVE_COL)
        (ws (wn (NEW_CUR_BASE + i.val)) (wl (newNodeDigestCols.getD i.val 0))), true⟩
    , .windowGate ⟨wm (wm (wl ACTIVE_COL) (ws (wk 1) (wn ACTIVE_COL)))
        (ws (wl (oldNodeDigestCols.getD i.val 0))
          (wl (fieldsRootGroupCol EFFECT_VM_WIDTH i))), true⟩
    , .windowGate ⟨wm (wm (wl ACTIVE_COL) (ws (wk 1) (wn ACTIVE_COL)))
        (ws (wl (newNodeDigestCols.getD i.val 0))
          (wl (fieldsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i))), true⟩ ])

def auditPins (piBase : Nat) : List VmConstraint2 :=
  (List.range VALUE_LIMBS).map fun i =>
    .base (.piBinding .first (NEW_VALUE_BASE + i) (piBase + i))

/-- Exact refusal host before the uniform DFA tail and faithful-wide append.  It deliberately starts
from `refusalV3` rather than `refusalFieldsWriteV3`: the legacy scalar map-op is absent. -/
def refusalExactFieldsV4 : EffectVmDescriptor2 :=
  let base := withRecordPin8Headroom2 refusalV3
  { base with
    name := "dregg-effectvm-refusal-v2-rot24-v4-write-exact-fields"
    traceWidth := TRACE_WIDTH
    piCount := base.piCount + AUDIT_PI_COUNT
    tables := v2Tables TRACE_WIDTH ++ [poseidon2State16ChipTableDef]
    constraints := base.constraints ++ state16Lookups ++ progressConstraints ++ pathConstraints ++
      auditPins base.piCount }

def withState16Table (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with tables := d.tables ++ [poseidon2State16ChipTableDef] }

/-- The exact bare-wide host used by both registry probes.  `wideAppend` rebuilds the common table
list, so the state16 declaration is restored after it. -/
def refusalExactFieldsWide : EffectVmDescriptor2 :=
  withState16Table
    (Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend
      (withDfaRcPins refusalExactFieldsV4)
      EffectVmEmitRefusal.refusalVmDescriptor.traceWidth
      (EffectVmEmitRefusal.refusalVmDescriptor.traceWidth + B_SPAN))

#guard refusalExactFieldsV4.traceWidth == TRACE_WIDTH
#guard refusalExactFieldsV4.piCount == 63
#guard (withRecordPin8Headroom2 refusalV3).piCount == AUDIT_PI_BASE
-- ⚑ KEY-NONET: 992 → 1008. Two wide blocks of `wideNumCarriers` 8-felt carriers, 62 → 63.
#guard refusalExactFieldsWide.traceWidth == TRACE_WIDTH + 1056
-- and the same fact WELDED to the producer's derived span, so the next carrier move reds the literal.
#guard refusalExactFieldsWide.traceWidth
  == TRACE_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppendixSpan
#guard refusalExactFieldsWide.piCount == 83
#guard ((refusalExactFieldsV4.constraints.filter fun c =>
  match c with | .lookup l => l.table == poseidon2state16 | _ => false).length) == 26
#guard ((refusalExactFieldsV4.constraints.filter fun c =>
  match c with | .mapOp _ => true | _ => false).length) == 0

/-- The raw audit limbs are genuine public inputs, not witness-only spare params. -/
theorem auditPin_mem (i : Nat) (hi : i < VALUE_LIMBS) :
    VmConstraint2.base (.piBinding .first (NEW_VALUE_BASE + i) (AUDIT_PI_BASE + i))
      ∈ refusalExactFieldsV4.constraints := by
  have hpi : (withRecordPin8Headroom2 refusalV3).piCount = AUDIT_PI_BASE := by rfl
  simp [refusalExactFieldsV4, auditPins, hpi, hi]

#assert_axioms auditPin_mem

end Dregg2.Circuit.Emit.ExactFieldsRefusalEmit
