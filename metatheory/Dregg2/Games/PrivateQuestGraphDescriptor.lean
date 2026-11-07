/-
# Dregg2.Games.PrivateQuestGraphDescriptor

Game-specific specialization of the reusable private graph-rewrite AIR.  The
generic relation deliberately permits an arbitrary privately committed pair of
rules.  That is the correct reusable primitive, but it is not enough to attest
the Warden quest: a producer could otherwise commit a different, easier
ruleset and still present a valid generic rewrite receipt.

This wrapper retains the exact 29-public-input history ABI and every constraint
of `PrivateGraphRewriteDescriptor`, then pins all 64 private rule-field columns
to the two authored quest reductions:

  sealed approach -> revealed trail + engaged warden -> broken seal.

Graphs, the selected rule, substitution, context, and all blindings remain
private.  The rules themselves are hidden in the proof transcript but fixed by
the AIR, rather than merely trusted in producer code.
-/
import Dregg2.Crypto.PrivateGraphRewriteDescriptor

namespace Dregg2.Games.PrivateQuestGraphDescriptor

open Dregg2.Crypto.PrivateGraphRewriteDescriptor
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TraceFamily VmTrace Satisfied2 emitVmJson2
   rangeTableDef)

set_option autoImplicit false
set_option maxRecDepth 10000

def LABEL_SEALED_APPROACH : Int := 1
def LABEL_REVEALED_TRAIL : Int := 2
def LABEL_ENGAGED_WARDEN : Int := 3
def LABEL_BROKEN_SEAL : Int := 8
def PRIVATE_QUEST_DOMAIN : Int := 0x51_55_45_53

/-- One rule slot in the descriptor's exact
`[active,label,src,dst,srcBit0,srcBit1,dstBit0,dstBit1]` layout. -/
def edgeFields (active label src dst : Int) : List Int :=
  [active, label, src, dst, src % 2, src / 2, dst % 2, dst / 2]

def paddingFields : List Int := edgeFields 0 0 0 0

/-- Exact 2 rules × 4 slots × 8 columns, in the base descriptor's private
rule-column order: `lhs0,lhs1,rhs0,rhs1` for each rule. -/
def questRuleFields : List Int :=
  edgeFields 1 LABEL_SEALED_APPROACH 0 1 ++ paddingFields ++
  edgeFields 1 LABEL_REVEALED_TRAIL 0 1 ++
  edgeFields 1 LABEL_ENGAGED_WARDEN 1 2 ++
  edgeFields 1 LABEL_REVEALED_TRAIL 0 1 ++
  edgeFields 1 LABEL_ENGAGED_WARDEN 1 2 ++
  edgeFields 1 LABEL_BROKEN_SEAL 0 2 ++ paddingFields

def fixedRuleBodies : List EmittedExpr :=
  questRuleFields.zipIdx.map fun (value, offset) =>
    eqBody (v (RULE_BASE + offset)) (c value)

def questContextFields : List Int :=
  [1, 12, 7, 8, 1, 13, 8, 9]

def fixedContextBodies : List EmittedExpr :=
  questContextFields.zipIdx.map fun (value, offset) =>
    eqBody (v (CONTEXT_BASE + offset)) (c value)

def questSigmaFields : List Int := [4, 5, 6, 7]

def fixedSigmaBodies : List EmittedExpr :=
  questSigmaFields.zipIdx.map fun (value, offset) =>
    eqBody (v (SIGMA_BASE + offset)) (c value)

/-- Index zero must use rule zero and index one rule one.  Making INDEX binary
also prevents a valid fixed-rule proof from inventing a third quest phase. -/
def questProtocolBodies : List EmittedExpr :=
  [ eqBody (v DOMAIN) (c PRIVATE_QUEST_DOMAIN)
  , binaryBody INDEX
  , eqBody (v RULE_SLOT) (v INDEX) ]

def fixedQuestBodies : List EmittedExpr :=
  fixedRuleBodies ++ fixedContextBodies ++ fixedSigmaBodies ++ questProtocolBodies

def questSemanticBodies : List EmittedExpr := semanticBodies ++ fixedQuestBodies

/-- The game verifier: byte-for-byte the reusable relation plus the 64 fixed
rule equations.  Public history linkage therefore remains the reusable 29-PI
ABI while the hidden ruleset can no longer be substituted by the producer. -/
def privateQuestGraphDescriptor : EffectVmDescriptor2 :=
  { name := "private-quest-graph-4x2::warden-fixed-rules-hiding-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [rangeTableDef 4]
  , constraints := hashLookups ++ rangeLookups ++
      questSemanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      questSemanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard questRuleFields.length == 64
#guard fixedRuleBodies.length == 64
#guard fixedContextBodies.length == 8
#guard fixedSigmaBodies.length == 4
#guard questProtocolBodies.length == 3
#guard fixedQuestBodies.length == 79
#guard privateQuestGraphDescriptor.traceWidth == 310
#guard privateQuestGraphDescriptor.piCount == 29
#guard (emitVmJson2 privateQuestGraphDescriptor).contains
  "private-quest-graph-4x2::warden-fixed-rules-hiding-v1"

theorem base_constraint_mem_quest {constraint : VmConstraint2}
    (h : constraint ∈ privateGraphRewriteDescriptor.constraints) :
    constraint ∈ privateQuestGraphDescriptor.constraints := by
  simp only [privateGraphRewriteDescriptor, privateQuestGraphDescriptor,
    questSemanticBodies, List.mem_append, List.mem_map] at h ⊢
  aesop

/-- The specialization cannot weaken the reusable graph-rewrite relation:
every satisfying quest trace is a satisfying base trace with the same public
statement, lookup tables, and witness assignment. -/
theorem privateQuest_satisfied_to_base_satisfied
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateQuestGraphDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf) := by
  -- The two descriptors declare the same memory and map ops and the traces share their rows,
  -- so the logs coincide; stated once and closed by rfl, not re-simplified per leg.
  have hmem : Dregg2.Circuit.DescriptorIR2.memLog privateGraphRewriteDescriptor
      (constTrace a pis tf) =
      Dregg2.Circuit.DescriptorIR2.memLog privateQuestGraphDescriptor (constTrace a pis tf) := rfl
  have hmap : Dregg2.Circuit.DescriptorIR2.mapLog privateGraphRewriteDescriptor
      (constTrace a pis tf) =
      Dregg2.Circuit.DescriptorIR2.mapLog privateQuestGraphDescriptor (constTrace a pis tf) := rfl
  constructor
  · intro i hi constraint hc
    exact hsat.rowConstraints i hi constraint (base_constraint_mem_quest hc)
  · intro i hi
    simpa [privateGraphRewriteDescriptor, privateQuestGraphDescriptor, constTrace,
      Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll,
      Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll.go]
      using hsat.rowHashes i hi
  · intro i hi r hr
    simp [privateGraphRewriteDescriptor] at hr
  · exact hsat.memAddrsNodup
  · rw [hmem]; exact hsat.memClosed
  · rw [hmem]; exact hsat.memDisciplined
  · rw [hmem]; exact hsat.memBalanced
  · rw [hmem]; exact hsat.memTableFaithful
  · rw [hmap]; exact hsat.mapTableFaithful

theorem fixed_rule_gate_mem {body : EmittedExpr} (hbody : body ∈ fixedRuleBodies) :
    VmConstraint2.base (.gate body) ∈ privateQuestGraphDescriptor.constraints := by
  simp [privateQuestGraphDescriptor, questSemanticBodies, fixedQuestBodies, hbody]

theorem fixed_quest_gate_mem {body : EmittedExpr} (hbody : body ∈ fixedQuestBodies) :
    VmConstraint2.base (.gate body) ∈ privateQuestGraphDescriptor.constraints := by
  simp [privateQuestGraphDescriptor, questSemanticBodies, hbody]

/-- Every one of the 64 rule-field pin equations is enforced by satisfaction;
this is the producer-substituted-rules exclusion at the descriptor boundary. -/
theorem privateQuest_fixed_rules_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateQuestGraphDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ fixedRuleBodies) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (fixed_rule_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

/-- The whole fixed game shell—rules, context, substitution, domain, and
two-step index/rule order—is enforced, not just the generic rewrite relation. -/
theorem privateQuest_fixed_game_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateQuestGraphDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ fixedQuestBodies) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (fixed_quest_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

#assert_all_clean [
  Dregg2.Games.PrivateQuestGraphDescriptor.base_constraint_mem_quest,
  Dregg2.Games.PrivateQuestGraphDescriptor.privateQuest_satisfied_to_base_satisfied,
  Dregg2.Games.PrivateQuestGraphDescriptor.privateQuest_fixed_rules_sound,
  Dregg2.Games.PrivateQuestGraphDescriptor.privateQuest_fixed_game_sound]

end Dregg2.Games.PrivateQuestGraphDescriptor
