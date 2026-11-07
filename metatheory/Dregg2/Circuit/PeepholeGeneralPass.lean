/-
# Dregg2.Circuit.PeepholeGeneralPass — a GENERAL syntactic peephole recognizer over the
constraint list, plus the certified single-site rule it drives, on ARBITRARY descriptors.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint;
the recognizer READS the constraint list that `TypedLinearPredicateDescriptorIR2.descriptor` emits,
and the certified rule is the already-proven `PeepholePassCertified.rwPass` /
`PeepholeR2Certified.rwR2Pass` on the EMITTED descriptor.

## What this closes — the program-specificity of the batch

`PeepholeBatchCertified` collapses the whole pilot spine in one certified pass, but it FIRES via
`pilot_holds_iff` — a lemma that unfolds `prog.source` and indexes the pilot's own atom registry
(`atomTerms_bool`). It is therefore keyed to that ONE program. E1
(`EffectVmDescriptor2PassiveOptimization`) is the opposite: a general `EffectVmDescriptor2 →
EffectVmDescriptor2` pass whose recognizer (`deadColsE1`) reads the descriptor. This module supplies
the missing general RECOGNIZER for the peephole family, matching E1's architecture:

`recognizePeephole : EffectVmDescriptor2 → List PeepholeSite` scans `d.constraints` and pattern-
matches, purely syntactically and independent of any source program:

* the R1 SHAPE — a zero-test's distinctive gate `x · out = 0` (`.mul (.loc x) (.loc out)`), which no
  other emitted node produces at top level (an ∧-node's product is wrapped in `subW`, `bitBody`'s
  product has an `.add` right factor); it records `.zeroTest x out`;
* the R2 SHAPE — an ∨-node's distinctive gate `out − ((l+r) − l·r) = 0`, whose fully-unfolded
  `WindowExpr` is a fixed tree; it records `.orNode out`.

The elided-site data (the tested column `x`, the disjunction bit `out`) is READ OFF THE CONSTRAINT
SHAPE, exactly as the batch's per-site rebuild values are determined by the shape and not the source
program.

## What is PROVEN here

* `recognize_sees_r1_site` / `recognize_sees_r2_site` — for ARBITRARY `terms/a/rest` (resp.
  `terms/c0/c1/rest`), the recognizer applied to the EMITTED descriptor
  `descriptor (rootProgram …)` returns a list CONTAINING the R1 (resp. R2) site the certified rule
  rewrites. This is the general "the recognizer sees the site" bridge, over every program of the
  family, not one pilot.
* `generalR1Preservation` / `generalR2Preservation` — the certified single-site rule, re-exposed as
  a `SatisfiabilityPreservation` on the descriptor the recognizer's site names; and the E1
  composition (`generalR1WithE1`).
* GENERALITY (the lane's demonstration): the recognizer FIRES with the correct counts on the
  field-delta pilot descriptor (62 zero-test sites + 30 ∨-sites) AND on a second, independently
  built `Program 1 1 3` (one asserted equality + one asserted booleanity → 3 zero-test sites + 1
  ∨-site), and the certified R1 rule certifies on that second descriptor (`second_r1_roundtrip`).

## Named residuals (no `sorry`, no stand-in)

* CANDIDATE, not frontier-qualified. `recognizePeephole` returns EVERY zero-test / ∨ shape,
  including the load-bearing zero-tests UNDER a disjunction (which R1 must not elide). The
  asserted-FRONTIER qualification (only the zero-test whose bit feeds the accept path) is what the
  certified rule's site selects; enforcing it syntactically — a reachability scan from the accept
  gate — is the named next leg. Over-recognition cannot make any rewrite unsound: the certified rule
  carries the real gate and is proved against the emitted descriptor regardless.
* ONE-PASS ALL-SITES. The certified rule here fires at ONE recognized site (`rwPass` / `rwR2Pass`).
  Folding all recognized sites into a single pass with a full `SecurityRefinement` — the
  program-INDEPENDENT generalization of `PeepholeBatchCertified.batch_security` — is the remaining
  leg; the batch already does the all-at-once collapse, but via the program-specific
  `pilot_holds_iff`. The recognizer + per-site certified rule here is the general half.

Standalone and additive: imports the R1/R2 certified modules and the pilot; changes none of them.
-/
import Dregg2.Circuit.PeepholeR2Certified
import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Circuit.PeepholeGeneralPass

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (Node Wire gate bitBody subW negW nodesAt)

set_option autoImplicit false

/-! ## 1. The syntactic recognizer — reads the emitted constraint SHAPES. -/

/-- A recognized peephole site, with the data read off the constraint shape. `zeroTest x out` is an
R1 candidate (input residual `x`, one-means-zero bit `out`); `orNode out` is an R2 candidate
(disjunction bit `out`). -/
inductive PeepholeSite where
  | zeroTest (x out : Nat)
  | orNode (out : Nat)
  deriving DecidableEq, Repr

/-- Match a single constraint against the emitted R1 / R2 gate shapes.

* R1: a zero-test node emits, as its second gate, `.mul (.loc x) (.loc out)` — the ONLY emitted
  gate that is a bare product of two `loc`s at top level (`bitBody` has an `.add` right factor;
  an ∧-node's product is inside a `subW`).
* R2: an ∨-node emits, as its second gate, `subW out (subW (l+r) (l·r))`, whose unfolded body is
  `.add (.loc out) (.mul (.const −1) (.add (.add l r) (.mul (.const −1) (.mul l' r'))))`. -/
def recSiteOf : VmConstraint2 → Option PeepholeSite
  | .windowGate w =>
      match w.body with
      | .mul (.loc x) (.loc out) => some (.zeroTest x out)
      | .add (.loc out)
          (.mul (.const c) (.add (.add _ _) (.mul (.const c2) (.mul _ _)))) =>
          if c == (-1 : Int) && c2 == (-1 : Int) then some (.orNode out) else none
      | _ => none
  | _ => none

/-- THE RECOGNIZER: the recognized sites of a descriptor, read off its constraint list, in order. -/
def recognizePeephole (d : EffectVmDescriptor2) : List PeepholeSite :=
  d.constraints.filterMap recSiteOf

/-- The recognized zero-test (R1-candidate) sites. -/
def r1Sites (d : EffectVmDescriptor2) : List PeepholeSite :=
  (recognizePeephole d).filter fun s => match s with | .zeroTest .. => true | _ => false

/-- The recognized ∨-node (R2-candidate) sites. -/
def r2Sites (d : EffectVmDescriptor2) : List PeepholeSite :=
  (recognizePeephole d).filter fun s => match s with | .orNode .. => true | _ => false

/-! ## 2. The recognizer SEES the site the certified rule rewrites — for ANY program in the family.

These are `∀`-theorems over the whole `rootProgram` / `rootProgramR2` family (arbitrary atom terms,
atom indices, and residual formula), not a pilot computation. -/

open Dregg2.Circuit.PeepholePassCertified (rootProgram zt_mem_src)
open Dregg2.Circuit.PeepholeR2Certified (rootProgramR2 srcR2_nodesAt)

section R1
variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms) (rest : Formula atoms)

/-- The zero-test's distinctive gate is a member of the emitted descriptor's constraint list. -/
theorem r1_gate_mem :
    gate (.mul (.loc a.val) (.loc (boolBase pub sec atoms))) ∈
      (descriptor (rootProgram terms a rest)).constraints :=
  graph_node_constraint_mem (rootProgram terms a rest)
    (Node.zeroTest a.val (boolBase pub sec atoms) (boolBase pub sec atoms + 1))
    (zt_mem_src terms a rest)
    (gate (.mul (.loc a.val) (.loc (boolBase pub sec atoms))))
    (by simp [Node.constraints])

/-- `recSiteOf` reads exactly `.zeroTest a.val B` off that gate. -/
theorem recSiteOf_r1_gate :
    recSiteOf (gate (.mul (.loc a.val) (.loc (boolBase pub sec atoms)))) =
      some (.zeroTest a.val (boolBase pub sec atoms)) := rfl

/-- THE R1 BRIDGE: for arbitrary `terms/a/rest`, the recognizer sees the R1 site of the emitted
descriptor — the site whose zero-test the certified `rwPass` elides. -/
theorem recognize_sees_r1_site :
    PeepholeSite.zeroTest a.val (boolBase pub sec atoms) ∈
      recognizePeephole (descriptor (rootProgram terms a rest)) :=
  List.mem_filterMap.2
    ⟨gate (.mul (.loc a.val) (.loc (boolBase pub sec atoms))),
      r1_gate_mem terms a rest, recSiteOf_r1_gate (a := a)⟩

end R1

section R2
variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

/-- The root ∨-node is emitted by `rootProgramR2`. -/
theorem or_node_mem_src :
    Node.or (.col (boolBase pub sec atoms)) (.col (boolBase pub sec atoms + 2))
        (boolBase pub sec atoms + 4) ∈
      nodesAt (boolBase pub sec atoms) (rootProgramR2 terms c0 c1 rest).source := by
  rw [srcR2_nodesAt]; simp

/-- The ∨-node's distinctive second gate is a member of the emitted constraint list. -/
theorem r2_gate_mem :
    gate (subW (.loc (boolBase pub sec atoms + 4))
        (subW (.add (.loc (boolBase pub sec atoms)) (.loc (boolBase pub sec atoms + 2)))
          (.mul (.loc (boolBase pub sec atoms)) (.loc (boolBase pub sec atoms + 2))))) ∈
      (descriptor (rootProgramR2 terms c0 c1 rest)).constraints :=
  graph_node_constraint_mem (rootProgramR2 terms c0 c1 rest)
    (Node.or (.col (boolBase pub sec atoms)) (.col (boolBase pub sec atoms + 2))
      (boolBase pub sec atoms + 4))
    (or_node_mem_src terms c0 c1 rest) _
    (by simp [Node.constraints, Wire.expr, subW, negW])

/-- `recSiteOf` reads exactly `.orNode (B+4)` off that gate. -/
theorem recSiteOf_r2_gate :
    recSiteOf (gate (subW (.loc (boolBase pub sec atoms + 4))
        (subW (.add (.loc (boolBase pub sec atoms)) (.loc (boolBase pub sec atoms + 2)))
          (.mul (.loc (boolBase pub sec atoms)) (.loc (boolBase pub sec atoms + 2)))))) =
      some (.orNode (boolBase pub sec atoms + 4)) := rfl

/-- THE R2 BRIDGE: for arbitrary `terms/c0/c1/rest`, the recognizer sees the R2 site of the emitted
descriptor — the site whose disjunction the certified `rwR2Pass` collapses. -/
theorem recognize_sees_r2_site :
    PeepholeSite.orNode (boolBase pub sec atoms + 4) ∈
      recognizePeephole (descriptor (rootProgramR2 terms c0 c1 rest)) :=
  List.mem_filterMap.2
    ⟨_, r2_gate_mem terms c0 c1 rest,
      recSiteOf_r2_gate (pub := pub) (sec := sec) (atoms := atoms)⟩

end R2

/-! ## 3. The certified rule the recognizer drives, re-exposed over the recognized site. -/

open Dregg2.Circuit.PeepholePassCertified
  (rwPass rw_preservation peepholePass peephole_preservation rwDescriptor)
open Dregg2.Circuit.PeepholeR2Certified (rwR2Pass rwR2_preservation rwR2Descriptor)

section Certified
variable {pub sec atoms : Nat}

/-- THE CERTIFIED R1 RULE, over the recognized site: rewriting the recognized zero-test yields
`rwDescriptor`, and the pass is a genuine `SatisfiabilityPreservation`. General over the whole
family. -/
theorem generalR1Preservation (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms)
    (rest : Formula atoms) : SatisfiabilityPreservation (rwPass terms a rest) :=
  rw_preservation terms a rest

/-- THE CERTIFIED R1 RULE COMPOSED WITH E1, over the recognized site — end to end. The hypothesis is
E1's own cheap transition-ceiling certificate on the rewritten descriptor. -/
theorem generalR1WithE1 (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms)
    (rest : Formula atoms) (floor : Nat)
    (hceiling :
      Dregg2.Circuit.Emit.RotWideCompactE1.transitionCeilingOk
        (rwDescriptor pub sec atoms terms a rest) floor = true) :
    SatisfiabilityPreservation (peepholePass terms a rest floor) :=
  peephole_preservation terms a rest floor hceiling

/-- THE CERTIFIED R2 RULE, over the recognized site. General over the whole family. -/
theorem generalR2Preservation (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms)
    (rest : Formula atoms)
    (hbase : (Dregg2.Circuit.PeepholeBooleanityRule.peelConst (terms c0)).1 =
      (Dregg2.Circuit.PeepholeBooleanityRule.peelConst (terms c1)).1) :
    SatisfiabilityPreservation (rwR2Pass terms c0 c1 rest hbase) :=
  rwR2_preservation terms c0 c1 rest hbase

end Certified

/-! ## 4. GENERALITY leg #1 — the recognizer FIRES on the field-delta pilot descriptor.

The pilot's source `atom0 ∧ atom1 ∧ ⋀_{j<30}(b_j=0 ∨ b_j=1)` materializes 62 zero-test nodes (2 on
the asserted frontier + 2 per disjunction × 30) and 30 ∨-nodes; the recognizer counts exactly those
off `descriptor prog`'s constraint list. Compiled `==`, no kernel `decide`. -/

open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)

#guard (recognizePeephole (descriptor prog)).length == 92
#guard (r1Sites (descriptor prog)).length == 62
#guard (r2Sites (descriptor prog)).length == 30

/-! ## 5. GENERALITY leg #2 — a SECOND, independent descriptor.

`secondProgram : Program 1 1 3`: one asserted frontier equality `input0 − input1` (R1) conjoined
with one asserted booleanity `secret = 0 ∨ secret = 1` (R2). The recognizer fires on it too — 3
zero-test sites (the frontier + the two under the ∨) and 1 ∨-site — demonstrating the recognizer is
NOT pilot-specific. -/

/-- Atom terms: atom0 = `input0 − input1` (asserted equality); atom1 = `input1` (`secret = 0`);
atom2 = `input1 − 1` (`secret = 1`). -/
def secondTerms : Fin 3 → AffineTerm (1 + 1)
  | ⟨0, _⟩ => .add (.input ⟨0, by omega⟩) (.neg (.input ⟨1, by omega⟩))
  | ⟨1, _⟩ => .input ⟨1, by omega⟩
  | ⟨2, _⟩ => AffineTerm.eqConst ⟨1, by omega⟩ 1
  | ⟨_, _⟩ => .const 1

def secondA : Fin 3 := ⟨0, by omega⟩

/-- `(secret = 0) ∨ (secret = 1)`. -/
def secondRest : Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula 3 :=
  .or (.atom ⟨1, by omega⟩) (.atom ⟨2, by omega⟩)

/-- The second descriptor: `atom0 ∧ ((secret=0) ∨ (secret=1))`. -/
def secondDescriptor : EffectVmDescriptor2 :=
  descriptor (rootProgram secondTerms secondA secondRest)

-- The recognizer FIRES on the second descriptor: 3 zero-tests + 1 ∨-node.
#guard (recognizePeephole secondDescriptor).length == 4
#guard (r1Sites secondDescriptor).length == 3
#guard (r2Sites secondDescriptor).length == 1

/-- On the second descriptor, the recognizer sees the R1 frontier site (an instance of the general
bridge). `boolBase 1 1 3 = 5`. -/
theorem second_recognizes_r1 :
    PeepholeSite.zeroTest secondA.val (boolBase 1 1 3) ∈ recognizePeephole secondDescriptor :=
  recognize_sees_r1_site secondTerms secondA secondRest

/-- And the R2 site is recognized too, via the general R2 bridge on the same second-descriptor
family (built here as an explicit `rootProgramR2`). -/
def secondR2Descriptor : EffectVmDescriptor2 :=
  descriptor (rootProgramR2 secondTerms ⟨1, by omega⟩ ⟨2, by omega⟩ (.top))

#guard (r2Sites secondR2Descriptor).length == 1

theorem second_recognizes_r2 :
    PeepholeSite.orNode (boolBase 1 1 3 + 4) ∈ recognizePeephole secondR2Descriptor :=
  recognize_sees_r2_site secondTerms ⟨1, by omega⟩ ⟨2, by omega⟩ (.top)

/-! ## 6. The certified R1 rule CERTIFIES on the second descriptor (non-vacuous).

The pass relates two genuinely inhabited relations: an accepting witness for the source expands to
one for the rewritten target and back. `secondGoodInput := 0` satisfies the source. -/

open Dregg2.Circuit.PeepholePassCertified (rw_satisfiable_iff)

noncomputable def secondGoodInput : Fin (1 + 1) → ZMod 2013265921 := fun _ => 0

theorem second_good_holds : (rootProgram secondTerms secondA secondRest).Holds secondGoodInput := by
  refine ⟨?_, ?_⟩
  · show (AffineTerm.add (.input ⟨0, by omega⟩) (.neg (.input ⟨1, by omega⟩)) :
        AffineTerm (1 + 1)).evalField secondGoodInput = 0
    simp [secondGoodInput, AffineTerm.evalField]
  · left
    show (AffineTerm.input ⟨1, by omega⟩ : AffineTerm (1 + 1)).evalField secondGoodInput = 0
    simp [secondGoodInput, AffineTerm.evalField]

open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (canonicalTrace canonical_complete)

theorem second_source_satisfiable (hash : List ℤ → ℤ) :
    ∃ s, Satisfied2 hash (descriptor (rootProgram secondTerms secondA secondRest))
      (fun _ => 0) (fun _ => (0, 0)) [] s :=
  ⟨canonicalTrace (rootProgram secondTerms secondA secondRest) secondGoodInput,
    canonical_complete hash (rootProgram secondTerms secondA secondRest) secondGoodInput
      second_good_holds⟩

/-- NON-VACUITY on the second descriptor: the R1-rewritten descriptor is satisfiable, the witness
carried across the certified pass, and the security leg carries an accepting target trace back to an
accepting source trace. -/
theorem second_r1_roundtrip (hash : List ℤ → ℤ) :
    (∃ u, Satisfied2 hash (rwDescriptor 1 1 3 secondTerms secondA secondRest)
      (fun _ => 0) (fun _ => (0, 0)) [] u) ∧
    (∃ s, Satisfied2 hash (descriptor (rootProgram secondTerms secondA secondRest))
      (fun _ => 0) (fun _ => (0, 0)) [] s) := by
  have hfwd := (rw_satisfiable_iff secondTerms secondA secondRest hash _ _ _).1
    (second_source_satisfiable hash)
  exact ⟨hfwd, (rw_satisfiable_iff secondTerms secondA secondRest hash _ _ _).2 hfwd⟩

/-! ## 7. Axiom hygiene — every new theorem is kernel-clean (no `sorryAx`). -/

#assert_all_clean [
  recognize_sees_r1_site,
  recognize_sees_r2_site,
  generalR1Preservation,
  generalR2Preservation,
  second_recognizes_r1,
  second_recognizes_r2,
  second_good_holds,
  second_source_satisfiable,
  second_r1_roundtrip
]

end Dregg2.Circuit.PeepholeGeneralPass
