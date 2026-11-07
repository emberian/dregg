/-
# Dregg2.Circuit.PeepholeR2Certified — the booleanity collapse R2 as a CERTIFIED passive pass.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. The source descriptor is the one the Lean
compiler `TypedLinearPredicateDescriptorIR2.descriptor` emits for a program whose Boolean source is
a root conjunction with an ASSERTED disjunction `(x = c₀) ∨ (x = c₁)` on the left; the target is
that SAME `EffectVmDescriptor2` value with only its constraint list rewritten by R2's booleanity
lowering. Nothing here is a separately reconstructed look-alike descriptor: `rwR2Descriptor` is a
record-UPDATE of `descriptor (rootProgramR2 …)`, and every surviving constraint is the same object
at the same column address.

## What this module closes

`PeepholeBooleanityRule` proved R2's LOCAL leg (`pairGate_iff_or`: the single quadratic
`(x+k₀)(x+k₁)=0` gate holds iff the two elided zero-tests-under-the-`∨` did) but its
`loweredDescriptor` was HAND-AUTHORED — asserted to be R2's post-image, with no
`Program → EffectVmDescriptor2` transform and no `SatisfiabilityPreservation`. This module lifts R2
to a genuine `PassiveDescriptorOptimization` pass on the EMITTED descriptor, mirroring
`PeepholePassCertified`'s R1 exactly:

For source `p.source = ((atom c₀) ∨ (atom c₁)) ∧ rest` with the two atom terms peeling to the SAME
affine base with DISTINCT shifts (R2's `recognizes` condition, `hbase` below), the emitted
descriptor carries, at `B = boolBase pub sec atoms`:

* `zeroTest c₀ B (B+1)` and `zeroTest c₁ (B+2) (B+3)` — 6 quadratic gates, 4 witness columns;
* `or (col B) (col (B+2)) (B+4)` — 2 gates, 1 witness column (`B+4` = the disjunction bit);
* the whole materialization of `rest` at base `B+5`;
* `and (col (B+4)) (outputAt (B+5) rest) (B+5+W)` — 2 gates, 1 witness column (`W = witnessCount rest`);
* the accept gate `col (B+5+W) = 1`.

Acceptance forces the and-tree output to 1, hence the disjunction bit to 1, hence `x=c₀ ∨ x=c₁`. R2
therefore replaces those 10 gates by the SINGLE degree-2 gate `(x+k₀)(x+k₁) = 0` over the raw-input
columns and re-points the accept gate at `rest`'s output. Columns `B, B+1, B+2, B+3, B+4, B+5+W` are
left unread; E1's derived dead-column deletion removes them.

## The two contract legs

* `rwR2_completeness` (`CompletenessPreservation`), `toTarget = id`: DERIVES `(x+k₀)(x+k₁)=0` and
  `outputAt (B+5) rest = 1` from the source's zero-test / disjunction / conjunction / accept
  equations, via the graph soundness `graph_of_node_constraints` + `graph_sound` and R2's local
  `pairGate_iff_or`.

* `rwR2_security` (`SecurityRefinement`), the load-bearing direction: an accepting TARGET trace has
  NOTHING in the elided witness columns, so `r2RebuildRow` restores the canonical postorder witness
  of the disjunction — `field_nodes_valid_of_matches` supplies `zeroBit`/`zeroInv` for each atom and
  the disjunction bit `1`, `mul_eq_zero` (BabyBear FIELD-ness, load-bearing) gives the disjunction
  from the pair gate — and the and-spine output is rebuilt as `1`, while every surviving constraint
  (public pins, atom links, `rest`'s whole materialization) is provably blind to the six rebuilt
  columns (`node_holdsAt_congr`, `nodesAt_nodeCols` from the R1 module).

Composition with E1 is the framework's own `preservation_comp` over the derived E1 pass.

## Named residuals — what is NOT proven here (no `sorry`, no stand-in)

* ITERATION (inherited from R1). Each pass fires ONCE, at one site. The pilot's source is
  `atom0 ∧ atom1 ∧ ⋀_{j<30}(b_j=0 ∨ b_j=1)`, so reaching the 35/33/30 hand-parity object needs R1
  applied twice and R2 applied thirty times, each to the ALREADY-REWRITTEN descriptor whose
  constraint list is no longer of the form `descriptor p'`. That 32-fold iteration is the same wall
  R1 named; it is not attempted here, and no theorem below claims the pilot's full collapse. What IS
  new: one R2 site is now a CERTIFIED pass whose OUTPUT (`rwR2Descriptor`, measured in §7) is the
  same object the preservation legs are proved for — the "hand-built object" gap is closed at the
  site.
* The E1 composition takes `transitionCeilingOk (rwR2Descriptor …) floor = true` as an explicit
  decidable hypothesis, exactly as R1's does.

Standalone and additive: imports R1 (for the reusable general lemmas), R2's rule (for `pairGate_iff_or`),
the contracts, and the typed front end; changes none of them.
-/
import Dregg2.Circuit.PeepholePassCertified
import Dregg2.Circuit.PeepholeBooleanityRule

namespace Dregg2.Circuit.PeepholeR2Certified

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node witnessCount outputAt nodesAt gate bitBody bitBody_eq subW negW fieldWindow
   fieldAssignment fieldWire fieldWindow_eq_cast fieldWire_expr field_zero_of_gate
   graph_of_node_constraints node_constraint_degree graphConstraints)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Circuit.PeepholeBooleanityRule (peelConst peelConst_evalField recognizes pairBody
  pairGate pairBody_zero_iff pairGate_iff_or nonlinearMuls)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula (Holds graphEval_iff_holds)

set_option autoImplicit false

/-! ## 0. Gate-denotation transfer (bodies are flag/hash/table-independent). -/

theorem gate_holds_iff (hash hash' : List ℤ → ℤ) (tf tf' : TraceFamily) (env : VmRowEnv)
    (f l f' l' : Bool) (body : WindowExpr) :
    (gate body).holdsAt hash tf env f l ↔ (gate body).holdsAt hash' tf' env f' l' := by
  rw [PeepholePassCertified.gate_holdsAt_iff, PeepholePassCertified.gate_holdsAt_iff]

/-- A field-zero gate body holds under ANY hash/table/flags. -/
theorem gate_holds_any (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (f l : Bool) {body : WindowExpr} (h : fieldWindow env body = 0) :
    (gate body).holdsAt hash tf env f l :=
  (gate_holds_iff (fun _ => 0) hash (fun _ => []) tf env false true f l body).mp
    (gate_holds_of_field_zero h)

theorem fieldRep_cast (x : BabyBear) : ((fieldRep x : ℤ) : BabyBear) = x := by
  have := fieldAssignment_fieldRep x
  simpa [fieldAssignment] using this

/-- A source/target gate constraint that holds under any hash/table/flags forces its body to vanish
in the field. -/
theorem field_of_src_gate {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    {body : WindowExpr} (h : (gate body).holdsAt hash tf env f l) : fieldWindow env body = 0 :=
  field_zero_of_gate
    ((gate_holds_iff hash (fun _ => 0) tf (fun _ => []) env f l false true body).mp h)

/-! ## 1. The R2 site: the emitted source descriptor and the rewritten target. -/

section Site

variable {pub sec atoms : Nat}

/-- A typed program whose Boolean source is a root conjunction with an asserted disjunction of two
affine zero-tests on the left: the exact shape R2 fires on. -/
def rootProgramR2 (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms)
    (rest : Formula atoms) : Program pub sec atoms :=
  { atomTerms := terms, source := .and (.or (.atom c0) (.atom c1)) rest }

/-- The surviving materialization of the conjunction's right operand, at its emitted base
`B + 5` (the disjunction subtree consumes 5 witness columns). -/
def midNodes (pub sec atoms : Nat) (rest : Formula atoms) : List Node :=
  nodesAt (boolBase pub sec atoms + 5) rest

def midConstraints (pub sec atoms : Nat) (rest : Formula atoms) : List VmConstraint2 :=
  (midNodes pub sec atoms rest).flatMap Node.constraints

def restOut (pub sec atoms : Nat) (rest : Formula atoms) : Wire :=
  outputAt (boolBase pub sec atoms + 5) rest

/-- R2's replacement for the elided disjunction: the single degree-2 gate `(x+k₀)(x+k₁) = 0` over
the raw-input columns, with base/shifts exactly those `peelConst` extracts from the two atom terms. -/
def pairGateR2 (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) : VmConstraint2 :=
  gate (pairBody (rawBase atoms) (peelConst (terms c0)).1 (peelConst (terms c0)).2
    (peelConst (terms c1)).2)

/-- The accept gate, re-pointed at the right operand's output. -/
def restAccept (pub sec atoms : Nat) (rest : Formula atoms) : VmConstraint2 :=
  gate (subW (restOut pub sec atoms rest).expr (.const 1))

def rwR2Constraints (pub sec atoms : Nat) (terms : Fin atoms → AffineTerm (pub + sec))
    (c0 c1 : Fin atoms) (rest : Formula atoms) : List VmConstraint2 :=
  publicPins pub sec atoms ++ atomLinks (rootProgramR2 terms c0 c1 rest) ++
    [pairGateR2 terms c0 c1] ++ midConstraints pub sec atoms rest ++
    [restAccept pub sec atoms rest]

/-- THE REWRITTEN DESCRIPTOR — the emitted record with only its constraints rewritten. -/
def rwR2Descriptor (pub sec atoms : Nat) (terms : Fin atoms → AffineTerm (pub + sec))
    (c0 c1 : Fin atoms) (rest : Formula atoms) : EffectVmDescriptor2 :=
  { descriptor (rootProgramR2 terms c0 c1 rest) with
    constraints := rwR2Constraints pub sec atoms terms c0 c1 rest }

variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

theorem rwR2Descriptor_traceWidth :
    (rwR2Descriptor pub sec atoms terms c0 c1 rest).traceWidth =
      (descriptor (rootProgramR2 terms c0 c1 rest)).traceWidth := rfl

theorem rwR2Descriptor_piCount :
    (rwR2Descriptor pub sec atoms terms c0 c1 rest).piCount =
      (descriptor (rootProgramR2 terms c0 c1 rest)).piCount := rfl

/-- The emitted node list at the root, split at the R2 site. -/
theorem srcR2_nodesAt :
    nodesAt (boolBase pub sec atoms) (rootProgramR2 terms c0 c1 rest).source =
      [Node.zeroTest c0.val (boolBase pub sec atoms) (boolBase pub sec atoms + 1),
       Node.zeroTest c1.val (boolBase pub sec atoms + 2) (boolBase pub sec atoms + 3),
       Node.or (.col (boolBase pub sec atoms)) (.col (boolBase pub sec atoms + 2))
         (boolBase pub sec atoms + 4)] ++
      midNodes pub sec atoms rest ++
      [Node.and (.col (boolBase pub sec atoms + 4)) (restOut pub sec atoms rest)
        (boolBase pub sec atoms + 5 + witnessCount rest)] := rfl

/-- The coarse split of the emitted node list — disjunction subtree, then `rest`'s materialization,
then the collapsing and-node — without expanding the disjunction subtree. -/
theorem srcR2_nodesAt_split :
    nodesAt (boolBase pub sec atoms) (rootProgramR2 terms c0 c1 rest).source =
      nodesAt (boolBase pub sec atoms) (.or (.atom c0) (.atom c1)) ++
        midNodes pub sec atoms rest ++
        [Node.and (.col (boolBase pub sec atoms + 4)) (restOut pub sec atoms rest)
          (boolBase pub sec atoms + 5 + witnessCount rest)] := rfl

theorem srcR2_accept :
    acceptConstraintAt (rootProgramR2 terms c0 c1 rest) =
      gate (subW (WindowExpr.loc (boolBase pub sec atoms + 5 + witnessCount rest))
        (.const 1)) := rfl

theorem atoms_le_boolBase : atoms ≤ boolBase pub sec atoms := by
  simp [boolBase]

/-! ### Membership plumbing -/

theorem pin_mem_rw {c : VmConstraint2} (h : c ∈ publicPins pub sec atoms) :
    c ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints := by
  simp [rwR2Descriptor, rwR2Constraints, h]

theorem link_mem_rw {c : VmConstraint2} (h : c ∈ atomLinks (rootProgramR2 terms c0 c1 rest)) :
    c ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints := by
  simp [rwR2Descriptor, rwR2Constraints, h]

theorem pairGate_mem_rw :
    pairGateR2 terms c0 c1 ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints := by
  simp [rwR2Descriptor, rwR2Constraints]

theorem mid_mem_rw {c : VmConstraint2} (h : c ∈ midConstraints pub sec atoms rest) :
    c ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints := by
  simp [rwR2Descriptor, rwR2Constraints, h]

theorem restAccept_mem_rw :
    restAccept pub sec atoms rest ∈
      (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints := by
  simp [rwR2Descriptor, rwR2Constraints]

theorem mid_mem_src {node : Node} (h : node ∈ midNodes pub sec atoms rest) :
    node ∈ nodesAt (boolBase pub sec atoms) (rootProgramR2 terms c0 c1 rest).source := by
  rw [srcR2_nodesAt]; simp [h]

theorem mid_constraint_mem_src {c : VmConstraint2}
    (h : c ∈ midConstraints pub sec atoms rest) :
    c ∈ (descriptor (rootProgramR2 terms c0 c1 rest)).constraints := by
  simp only [midConstraints, List.mem_flatMap] at h
  obtain ⟨node, hnode, hc⟩ := h
  exact graph_node_constraint_mem _ node (mid_mem_src terms c0 c1 rest hnode) c hc

end Site

/-! ## 2. Carrier bookkeeping: neither descriptor declares a memory or map op. -/

section Carriers

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

theorem memOps_rwR2_nil : memOpsOf (rwR2Descriptor pub sec atoms terms c0 c1 rest) = [] := by
  simp [memOpsOf, rwR2Descriptor, rwR2Constraints, List.filterMap_append, publicPins,
    atomLinks, atomLink, gate, pairGateR2, restAccept, midConstraints]
  intro c n _ hc
  obtain ⟨body, rfl, _⟩ :=
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.node_constraint_degree n c hc
  rfl

theorem mapOps_rwR2_nil : mapOpsOf (rwR2Descriptor pub sec atoms terms c0 c1 rest) = [] := by
  simp [mapOpsOf, rwR2Descriptor, rwR2Constraints, List.filterMap_append, publicPins,
    atomLinks, atomLink, gate, pairGateR2, restAccept, midConstraints]
  intro c n _ hc
  obtain ⟨body, rfl, _⟩ :=
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.node_constraint_degree n c hc
  rfl

end Carriers

/-! ## 3. Public ABI: the pass moves no PI binding. -/

section ABI

variable {pub sec atoms : Nat}

private theorem node_bindingSlot_nil (node : Node) :
    node.constraints.filterMap bindingSlot? = [] := by
  cases node <;> rfl

private theorem nodes_bindingSlot_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap bindingSlot? = [] := by
  induction nodes with
  | nil => rfl
  | cons n ns ih =>
      simp [List.flatMap_cons, List.filterMap_append, node_bindingSlot_nil, ih]

private theorem atomLinks_bindingSlot_nil (p : Program pub sec atoms) :
    (atomLinks p).filterMap bindingSlot? = [] := by
  simp [atomLinks, atomLink]

variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

theorem publicBindingSlots_src :
    publicBindingSlots (descriptor (rootProgramR2 terms c0 c1 rest)) =
      (publicPins pub sec atoms).filterMap bindingSlot? := by
  simp [publicBindingSlots, descriptor, List.filterMap_append, atomLinks_bindingSlot_nil,
    graphConstraintsAt, nodes_bindingSlot_nil, acceptConstraintAt]

theorem publicBindingSlots_rw :
    publicBindingSlots (rwR2Descriptor pub sec atoms terms c0 c1 rest) =
      (publicPins pub sec atoms).filterMap bindingSlot? := by
  simp only [publicBindingSlots, rwR2Descriptor, rwR2Constraints, List.filterMap_append,
    atomLinks_bindingSlot_nil, midConstraints, nodes_bindingSlot_nil]
  simp [pairGateR2, restAccept]

end ABI

/-! ## 4. The witness rebuild — the elided disjunction region, as canonical field values.

An accepting TARGET trace says nothing about columns `B, B+1, B+2, B+3, B+4, B+5+W`; R2 deleted every
constraint that mentioned them. `r2RebuildRow` restores the canonical postorder witness of the
disjunction: each atom's `out` bit is its residual's `zeroBit`, its `inv` witness is `zeroInv`, the
disjunction `out` is `evalBit` of the `∨` (which the pair gate forces to 1), and the collapsed
and-spine output is `1`. Values are field elements embedded through `fieldRep`. -/

section Rebuild

variable {pub sec atoms : Nat}

noncomputable def r2RebuildRow (c0 c1 : Fin atoms) (B W : Nat) (row : Assignment) : Assignment :=
  fun c =>
    if c = B then fieldRep (zeroBit (fieldAssignment row c0.val))
    else if c = B + 1 then fieldRep (zeroInv (fieldAssignment row c0.val))
    else if c = B + 2 then fieldRep (zeroBit (fieldAssignment row c1.val))
    else if c = B + 3 then fieldRep (zeroInv (fieldAssignment row c1.val))
    else if c = B + 4 then
      fieldRep (evalBit (fun a : Fin atoms => fieldAssignment row a.val)
        (.or (.atom c0) (.atom c1)))
    else if c = B + 5 + W then 1
    else row c

noncomputable def r2RebuildTrace (c0 c1 : Fin atoms) (B W : Nat) (t : VmTrace) : VmTrace :=
  { rows := t.rows.map (r2RebuildRow c0 c1 B W), pub := t.pub, tf := t.tf }

variable (c0 c1 : Fin atoms) (B W : Nat) (row : Assignment)

theorem r2RebuildRow_untouched {c : Nat}
    (h0 : c ≠ B) (h1 : c ≠ B + 1) (h2 : c ≠ B + 2) (h3 : c ≠ B + 3) (h4 : c ≠ B + 4)
    (h5 : c ≠ B + 5 + W) : r2RebuildRow c0 c1 B W row c = row c := by
  simp [r2RebuildRow, h0, h1, h2, h3, h4, h5]

theorem r2RebuildRow_B : r2RebuildRow c0 c1 B W row B = fieldRep (zeroBit (fieldAssignment row c0.val)) := by
  simp [r2RebuildRow]

theorem r2RebuildRow_B1 : r2RebuildRow c0 c1 B W row (B + 1) = fieldRep (zeroInv (fieldAssignment row c0.val)) := by
  simp [r2RebuildRow]

theorem r2RebuildRow_B2 : r2RebuildRow c0 c1 B W row (B + 2) = fieldRep (zeroBit (fieldAssignment row c1.val)) := by
  simp [r2RebuildRow]

theorem r2RebuildRow_B3 : r2RebuildRow c0 c1 B W row (B + 3) = fieldRep (zeroInv (fieldAssignment row c1.val)) := by
  simp [r2RebuildRow]

theorem r2RebuildRow_B4 :
    r2RebuildRow c0 c1 B W row (B + 4) =
      fieldRep (evalBit (fun a : Fin atoms => fieldAssignment row a.val)
        (.or (.atom c0) (.atom c1))) := by
  simp [r2RebuildRow]

theorem r2RebuildRow_top : r2RebuildRow c0 c1 B W row (B + 5 + W) = 1 := by
  have h0 : B + 5 + W ≠ B := by omega
  have h1 : B + 5 + W ≠ B + 1 := by omega
  have h2 : B + 5 + W ≠ B + 2 := by omega
  have h3 : B + 5 + W ≠ B + 3 := by omega
  have h4 : B + 5 + W ≠ B + 4 := by omega
  simp [r2RebuildRow, h0, h1, h2, h3, h4]

theorem r2RebuildTrace_rows_length (t : VmTrace) :
    (r2RebuildTrace c0 c1 B W t).rows.length = t.rows.length := by simp [r2RebuildTrace]

theorem r2RebuildTrace_loc (t : VmTrace) (i : Nat) (h : i < t.rows.length) :
    (envAt (r2RebuildTrace c0 c1 B W t) i).loc = r2RebuildRow c0 c1 B W ((envAt t i).loc) := by
  simp only [envAt, r2RebuildTrace]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

theorem r2RebuildTrace_pub (t : VmTrace) (i : Nat) :
    (envAt (r2RebuildTrace c0 c1 B W t) i).pub = (envAt t i).pub := rfl

/-! ### Field values of the rebuilt columns, and the disjunction's witness match. -/

theorem fa_B : fieldAssignment (r2RebuildRow c0 c1 B W row) B = zeroBit (fieldAssignment row c0.val) := by
  show ((r2RebuildRow c0 c1 B W row B : ℤ) : BabyBear) = _
  rw [r2RebuildRow_B, fieldRep_cast]

theorem fa_B1 : fieldAssignment (r2RebuildRow c0 c1 B W row) (B + 1) = zeroInv (fieldAssignment row c0.val) := by
  show ((r2RebuildRow c0 c1 B W row (B + 1) : ℤ) : BabyBear) = _
  rw [r2RebuildRow_B1, fieldRep_cast]

theorem fa_B2 : fieldAssignment (r2RebuildRow c0 c1 B W row) (B + 2) = zeroBit (fieldAssignment row c1.val) := by
  show ((r2RebuildRow c0 c1 B W row (B + 2) : ℤ) : BabyBear) = _
  rw [r2RebuildRow_B2, fieldRep_cast]

theorem fa_B3 : fieldAssignment (r2RebuildRow c0 c1 B W row) (B + 3) = zeroInv (fieldAssignment row c1.val) := by
  show ((r2RebuildRow c0 c1 B W row (B + 3) : ℤ) : BabyBear) = _
  rw [r2RebuildRow_B3, fieldRep_cast]

theorem fa_B4 : fieldAssignment (r2RebuildRow c0 c1 B W row) (B + 4) =
    evalBit (fun a : Fin atoms => fieldAssignment row a.val) (.or (.atom c0) (.atom c1)) := by
  show ((r2RebuildRow c0 c1 B W row (B + 4) : ℤ) : BabyBear) = _
  rw [r2RebuildRow_B4, fieldRep_cast]

theorem fa_top : fieldAssignment (r2RebuildRow c0 c1 B W row) (B + 5 + W) = 1 := by
  show ((r2RebuildRow c0 c1 B W row (B + 5 + W) : ℤ) : BabyBear) = _
  rw [r2RebuildRow_top]; norm_num

/-- The rebuilt row matches the canonical postorder field witness of the disjunction at base `B`. -/
theorem r2_fieldMatch :
    FieldWitnessesMatch (fun a : Fin atoms => fieldAssignment row a.val) B
      (.or (.atom c0) (.atom c1))
      (fun c => fieldAssignment (r2RebuildRow c0 c1 B W row) c) := by
  intro k hk
  simp only [witnessCount] at hk
  interval_cases k <;>
    simp only [Nat.add_zero, fieldWitness, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, fa_B, fa_B1, fa_B2, fa_B3, fa_B4]

end Rebuild

/-! ## 5. The two per-row contract legs. -/

section Rows

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

/-- THE COMPLETENESS LEG, per row (`toTarget = id`).  R2's replacement gate `(x+k₀)(x+k₁)=0` and the
re-pointed accept are DERIVED from the source's disjunction / conjunction / accept equations via the
graph soundness and R2's local `pairGate_iff_or`. -/
theorem rwR2_completeness_row (hash : List ℤ → ℤ) (tf : TraceFamily) (isFirst isLast : Bool)
    (env : VmRowEnv)
    (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (hsrc : ∀ c ∈ (descriptor (rootProgramR2 terms c0 c1 rest)).constraints,
      c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints,
      c.holdsAt hash tf env isFirst isLast := by
  have hnodes : ∀ node ∈ nodesAt (boolBase pub sec atoms)
      (rootProgramR2 terms c0 c1 rest).source, Node.HoldsAt env node := by
    intro node hn c hc
    have hmem := graph_node_constraint_mem (rootProgramR2 terms c0 c1 rest) node hn c hc
    obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
    exact (gate_holds_iff hash (fun _ => 0) tf (fun _ => []) env isFirst isLast false true body).mp
      (hsrc _ hmem)
  have hgraph := graph_of_node_constraints env (boolBase pub sec atoms)
    (rootProgramR2 terms c0 c1 rest).source hnodes
  have hout : fieldWire env.loc
      (outputAt (boolBase pub sec atoms) (rootProgramR2 terms c0 c1 rest).source) = 1 := by
    have hz := field_of_src_gate (hsrc (acceptConstraintAt (rootProgramR2 terms c0 c1 rest))
      (by simp [descriptor]))
    simp only [subW, negW, fieldWindow] at hz
    rw [fieldWire_expr] at hz
    linear_combination hz
  have heval := (Dregg2.Logic.BoolGraph.graph_sound hgraph).2.mp hout
  have hrow : Holds (fun a => fieldAssignment env.loc a.val = 0)
      (rootProgramR2 terms c0 c1 rest).source :=
    (graphEval_iff_holds (fun a : Fin atoms => fieldAssignment env.loc a.val)
      (rootProgramR2 terms c0 c1 rest).source).mp heval
  simp only [rootProgramR2, Holds] at hrow
  obtain ⟨hD, hRest⟩ := hrow
  -- atom links bridge the residual columns to the raw-input evaluation
  have hlink : ∀ a : Fin atoms, fieldAssignment env.loc a.val =
      (terms a).evalField (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) := by
    intro a
    have hz := field_of_src_gate (hsrc (atomLink (rootProgramR2 terms c0 c1 rest) a)
      (atom_link_mem (rootProgramR2 terms c0 c1 rest) a))
    simp only [atomLinkBody, subW, negW, fieldWindow, rootProgramR2] at hz
    rw [AffineTerm.fieldWindow_toWindowAt] at hz
    linear_combination hz
  -- the disjunction, transported to the raw-input residuals
  have hor : (terms c0).evalField (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) = 0 ∨
      (terms c1).evalField (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) = 0 := by
    rcases hD with h0 | h1
    · exact Or.inl (by rw [← hlink c0]; exact h0)
    · exact Or.inr (by rw [← hlink c1]; exact h1)
  have hpair : fieldWindow env (pairBody (rawBase atoms) (peelConst (terms c0)).1
      (peelConst (terms c0)).2 (peelConst (terms c1)).2) = 0 :=
    (pairGate_iff_or env (rawBase atoms) (terms c0) (terms c1) hbase).mpr hor
  -- rest's output is 1
  have hnodesRest : ∀ node ∈ nodesAt (boolBase pub sec atoms + 5) rest, Node.HoldsAt env node := by
    intro node hn
    exact hnodes node (mid_mem_src terms c0 c1 rest hn)
  have hgraphRest := graph_of_node_constraints env (boolBase pub sec atoms + 5) rest hnodesRest
  have hEvalRest := (graphEval_iff_holds
    (fun a : Fin atoms => fieldAssignment env.loc a.val) rest).mpr hRest
  have hrestout : fieldWire env.loc (outputAt (boolBase pub sec atoms + 5) rest) = 1 :=
    (Dregg2.Logic.BoolGraph.graph_sound hgraphRest).2.mpr hEvalRest
  -- assemble the target constraints
  intro c hc
  simp only [rwR2Descriptor, rwR2Constraints, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((((hpin | hlink) | rfl) | hmid) | rfl)
  · exact hsrc c (by simp [descriptor, hpin])
  · exact hsrc c (by simp [descriptor, hlink])
  · exact gate_holds_any hash tf env isFirst isLast hpair
  · exact hsrc c (mid_constraint_mem_src terms c0 c1 rest hmid)
  · refine gate_holds_any hash tf env isFirst isLast ?_
    simp only [restOut, subW, negW, fieldWindow]
    rw [fieldWire_expr, hrestout]; ring

/-- THE SECURITY LEG, per row.  Every source constraint holds on the REBUILT row: the disjunction
region is discharged by the canonical postorder field witness (`field_nodes_valid_of_matches`), the
and-spine output is rebuilt as `1`, and every surviving constraint is provably blind to the six
rebuilt columns. -/
theorem rwR2_security_row (hash : List ℤ → ℤ) (tf : TraceFamily) (isFirst isLast : Bool)
    (env env' : VmRowEnv)
    (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (hpub : env'.pub = env.pub)
    (hagree : ∀ c, c ≠ boolBase pub sec atoms → c ≠ boolBase pub sec atoms + 1 →
      c ≠ boolBase pub sec atoms + 2 → c ≠ boolBase pub sec atoms + 3 →
      c ≠ boolBase pub sec atoms + 4 → c ≠ boolBase pub sec atoms + 5 + witnessCount rest →
      env'.loc c = env.loc c)
    (hmatch : FieldWitnessesMatch (fun a : Fin atoms => fieldAssignment env.loc a.val)
      (boolBase pub sec atoms) (.or (.atom c0) (.atom c1))
      (fun c => fieldAssignment env'.loc c))
    (hAndOut : fieldAssignment env'.loc (boolBase pub sec atoms + 5 + witnessCount rest) = 1)
    (htgt : ∀ c ∈ (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints,
      c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ (descriptor (rootProgramR2 terms c0 c1 rest)).constraints,
      c.holdsAt hash tf env' isFirst isLast := by
  have hlow : ∀ k, k < boolBase pub sec atoms → env'.loc k = env.loc k := by
    intro k hk
    exact hagree k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hatomcol : ∀ b : Fin atoms, env'.loc b.val = env.loc b.val := by
    intro b
    exact hlow b.val (lt_of_lt_of_le b.isLt (atoms_le_boolBase))
  have hraw : ∀ i : Fin (pub + sec),
      env'.loc (rawBase atoms + i.val) = env.loc (rawBase atoms + i.val) := by
    intro i
    have hi := i.isLt
    refine hlow _ ?_
    simp only [rawBase, boolBase]; omega
  have hfieldatom : ∀ b : Fin atoms,
      fieldAssignment env'.loc b.val = fieldAssignment env.loc b.val := by
    intro b; simp only [fieldAssignment, hatomcol b]
  -- residual bridge (from the target atom links)
  have hlink : ∀ a : Fin atoms, fieldAssignment env.loc a.val =
      (terms a).evalField (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) := by
    intro a
    have hz := field_of_src_gate (htgt (atomLink (rootProgramR2 terms c0 c1 rest) a)
      (link_mem_rw terms c0 c1 rest (by simp [atomLinks])))
    simp only [atomLinkBody, subW, negW, fieldWindow, rootProgramR2] at hz
    rw [AffineTerm.fieldWindow_toWindowAt] at hz
    linear_combination hz
  -- the pair gate holds on env, giving the disjunction
  have hpair := field_of_src_gate (htgt (pairGateR2 terms c0 c1)
    (pairGate_mem_rw terms c0 c1 rest))
  have hor := (pairGate_iff_or env (rawBase atoms) (terms c0) (terms c1) hbase).mp hpair
  have hEvalBitD : evalBit (fun a : Fin atoms => fieldAssignment env.loc a.val)
      (.or (.atom c0) (.atom c1)) = 1 := by
    refine (evalBit_one_iff (fun a : Fin atoms => fieldAssignment env.loc a.val)
      (.or (.atom c0) (.atom c1))).mpr ?_
    simp only [Holds]
    rcases hor with h0 | h1
    · exact Or.inl (by rw [hlink c0]; exact h0)
    · exact Or.inr (by rw [hlink c1]; exact h1)
  -- the disjunction region: field-valid postorder witness
  have hatom' : ∀ a : Fin atoms,
      (fun c => fieldAssignment env'.loc c) a.val =
        (fun a : Fin atoms => fieldAssignment env.loc a.val) a := by
    intro a; exact hfieldatom a
  have hvalid := field_nodes_valid_of_matches (fun a : Fin atoms => fieldAssignment env.loc a.val)
    (boolBase pub sec atoms) (.or (.atom c0) (.atom c1)) (fun c => fieldAssignment env'.loc c)
    hatom' hmatch
  -- col B+4 field value = 1
  have hcolB4 : fieldAssignment env'.loc (boolBase pub sec atoms + 4) = 1 := by
    have h := hmatch 4 (by simp only [witnessCount]; omega)
    simp only [fieldWitness, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero] at h
    rw [h, hEvalBitD]
  -- rest output on env' equals 1
  have hrestout : fieldWire env'.loc (restOut pub sec atoms rest) = 1 := by
    have hz := field_of_src_gate (htgt (restAccept pub sec atoms rest)
      (restAccept_mem_rw terms c0 c1 rest))
    simp only [subW, negW, fieldWindow] at hz
    rw [fieldWire_expr] at hz
    have hcongr : (restOut pub sec atoms rest).expr.eval env' =
        (restOut pub sec atoms rest).expr.eval env := by
      refine PeepholePassCertified.wire_eval_congr _ ?_
      intro k hk
      rcases PeepholePassCertified.outputAt_wireCols (boolBase pub sec atoms + 5) rest k hk
        with ⟨h1, h2⟩
      exact hagree k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hcongr' : fieldWire env'.loc (restOut pub sec atoms rest)
        = fieldWire env.loc (restOut pub sec atoms rest) := by
      rw [← fieldWire_expr, ← fieldWire_expr, fieldWindow_eq_cast, fieldWindow_eq_cast, hcongr]
    rw [hcongr']
    linear_combination hz
  intro c hc
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((hpin | hlinkc) | hgraph) | rfl
  · -- public pins: read raw cols (< B), invariant
    have hh := htgt c (pin_mem_rw terms c0 c1 rest hpin)
    simp only [publicPins, List.mem_map] at hpin
    obtain ⟨i, hi, rfl⟩ := hpin
    have hil : i < pub := List.mem_range.mp hi
    have hcol : env'.loc (rawBase atoms + i) = env.loc (rawBase atoms + i) := by
      refine hlow _ ?_
      simp only [rawBase, boolBase]; omega
    simp only [VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at hh ⊢
    intro hf; rw [hcol, hpub]; exact hh hf
  · -- atom links: read atom col (< B) + raw cols, invariant
    have hh := htgt c (link_mem_rw terms c0 c1 rest hlinkc)
    simp only [atomLinks, List.mem_map] at hlinkc
    obtain ⟨b, _, rfl⟩ := hlinkc
    simp only [atomLink] at hh ⊢
    rw [PeepholePassCertified.gate_dvd_iff] at hh ⊢
    have hbody : (atomLinkBody (rootProgramR2 terms c0 c1 rest) b).eval env'
        = (atomLinkBody (rootProgramR2 terms c0 c1 rest) b).eval env := by
      simp only [atomLinkBody, subW, negW, WindowExpr.eval, rootProgramR2]
      rw [hatomcol b, PeepholePassCertified.toWindowAt_eval_congr (rawBase atoms) _ hraw]
    rw [hbody]; exact hh
  · -- graph constraints
    simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
    obtain ⟨node, hnode, hcn⟩ := hgraph
    rw [srcR2_nodesAt_split] at hnode
    simp only [List.mem_append, List.mem_singleton] at hnode
    rcases hnode with (hInD | hmid) | rfl
    · -- disjunction subtree (zeroTest c0, zeroTest c1, or): canonical field witness
      have hfv := hvalid node hInD
      have hnh := node_constraints_hold_of_field_valid env' node hfv
      obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcn
      exact (gate_holds_iff (fun _ => 0) hash (fun _ => []) tf env' false true isFirst isLast body).mp
        (hnh (gate body) hcn)
    · -- rest region: untouched
      refine PeepholePassCertified.node_holdsAt_congr hash tf env env' isFirst isLast node ?_ ?_ c hcn
      · intro k hk
        rcases PeepholePassCertified.nodesAt_nodeCols (boolBase pub sec atoms + 5) rest node hmid k hk
          with h | h
        · exact hlow k (lt_of_lt_of_le h (atoms_le_boolBase))
        · exact hagree k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · intro c' hc'
        refine htgt c' (mid_mem_rw terms c0 c1 rest ?_)
        simp only [midConstraints]
        exact List.mem_flatMap.mpr ⟨node, hmid, hc'⟩
    · -- and node: rebuilt output 1 = 1 · restOut(=1)
      have hcn' := hcn
      simp only [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints,
        List.mem_cons, List.not_mem_nil, or_false] at hcn'
      rcases hcn' with rfl | rfl
      · refine gate_holds_any hash tf env' isFirst isLast ?_
        simp only [bitBody_eq, Wire.expr, fieldWindow]
        rw [hAndOut]; ring
      · refine gate_holds_any hash tf env' isFirst isLast ?_
        simp only [subW, negW, fieldWindow]
        rw [fieldWire_expr, fieldWire_expr, hrestout]
        simp only [fieldWire]
        rw [hAndOut, hcolB4]
        push_cast; ring
  · -- accept gate re-pointed at the and-spine output (rebuilt 1)
    refine gate_holds_any hash tf env' isFirst isLast ?_
    simp only [subW, negW, fieldWindow, rootProgramR2]
    show fieldAssignment env'.loc (boolBase pub sec atoms + 5 + witnessCount rest)
      + (-1) * ((1 : BabyBear)) = 0
    rw [hAndOut]; ring

end Rows

/-! ## 6. The certified pass and its two contract legs. -/

section Pass

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

/-- THE R2 PASS.  `toTarget` is the identity — R2 changes no column — and `toSource` rebuilds the
elided disjunction witness region canonically. -/
noncomputable def rwR2Pass (_hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1) :
    PassiveOptimization (descriptor (rootProgramR2 terms c0 c1 rest))
      (rwR2Descriptor pub sec atoms terms c0 c1 rest) where
  toTarget := id
  toSource := r2RebuildTrace c0 c1 (boolBase pub sec atoms) (witnessCount rest)
  publicABI :=
    { piCount_eq := rfl
      bindingSlots_eq := by rw [publicBindingSlots_src, publicBindingSlots_rw] }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

theorem rwR2_security (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1) :
    SecurityRefinement (rwR2Pass terms c0 c1 rest hbase) := by
  intro hash minit mfin maddrs t hsat
  refine PeepholePassCertified.satisfied2_transfer (t := t)
    (u := (rwR2Pass terms c0 c1 rest hbase).toSource t)
    (memOps_descriptor_nil _) (mapOps_descriptor_nil _)
    (memOps_rwR2_nil terms c0 c1 rest) (mapOps_rwR2_nil terms c0 c1 rest) rfl rfl rfl hsat ?_
  intro i hi c hc
  have hlen : ((rwR2Pass terms c0 c1 rest hbase).toSource t).rows.length = t.rows.length :=
    r2RebuildTrace_rows_length _ _ _ _ t
  rw [hlen] at hi
  rw [hlen]
  refine rwR2_security_row terms c0 c1 rest hash t.tf (i == 0) (i + 1 == t.rows.length)
    (envAt t i)
    (envAt (r2RebuildTrace c0 c1 (boolBase pub sec atoms) (witnessCount rest) t) i)
    hbase rfl ?_ ?_ ?_ (hsat.rowConstraints i hi) c hc
  · -- hagree
    intro k hk0 hk1 hk2 hk3 hk4 hk5
    rw [r2RebuildTrace_loc _ _ _ _ t i hi]
    exact r2RebuildRow_untouched _ _ _ _ _ hk0 hk1 hk2 hk3 hk4 hk5
  · -- hmatch
    intro k hk
    have := r2_fieldMatch c0 c1 (boolBase pub sec atoms) (witnessCount rest) ((envAt t i).loc) k hk
    rw [r2RebuildTrace_loc _ _ _ _ t i hi]
    simpa using this
  · -- hAndOut
    rw [r2RebuildTrace_loc _ _ _ _ t i hi]
    exact fa_top c0 c1 (boolBase pub sec atoms) (witnessCount rest) _

theorem rwR2_completeness (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1) :
    CompletenessPreservation (rwR2Pass terms c0 c1 rest hbase) := by
  intro hash minit mfin maddrs t hsat
  refine PeepholePassCertified.satisfied2_transfer (t := t)
    (u := (rwR2Pass terms c0 c1 rest hbase).toTarget t)
    (memOps_rwR2_nil terms c0 c1 rest) (mapOps_rwR2_nil terms c0 c1 rest)
    (memOps_descriptor_nil _) (mapOps_descriptor_nil _) rfl rfl rfl hsat ?_
  intro i hi c hc
  exact rwR2_completeness_row terms c0 c1 rest hash t.tf (i == 0) (i + 1 == t.rows.length)
    (envAt t i) hbase (hsat.rowConstraints i hi) c hc

/-- BOTH LEGS: R2 is a genuine equisatisfiability-preserving passive pass on the EMITTED descriptor,
not a hand-authored `loweredDescriptor`. -/
theorem rwR2_preservation (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1) :
    SatisfiabilityPreservation (rwR2Pass terms c0 c1 rest hbase) :=
  ⟨rwR2_security terms c0 c1 rest hbase, rwR2_completeness terms c0 c1 rest hbase⟩

theorem rwR2_satisfiable_iff (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor (rootProgramR2 terms c0 c1 rest)) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (rwR2Descriptor pub sec atoms terms c0 c1 rest) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (rwR2_preservation terms c0 c1 rest hbase) hash minit mfin maddrs

/-! ## 7. Composition with the already-certified E1 dead-column deletion. -/

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- R2 then E1, end to end, through the framework's own composition. -/
noncomputable def peepholeR2Pass (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (floor : Nat) :
    PassiveOptimization (descriptor (rootProgramR2 terms c0 c1 rest))
      (compactE1 (rwR2Descriptor pub sec atoms terms c0 c1 rest)
        (deadColsE1 (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor)) :=
  (rwR2Pass terms c0 c1 rest hbase).comp
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPass
      (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- END TO END: the composed R2 + E1 pass preserves satisfaction in both directions. -/
theorem peepholeR2_preservation (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (floor : Nat)
    (hceiling : transitionCeilingOk (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor = true) :
    SatisfiabilityPreservation (peepholeR2Pass terms c0 c1 rest hbase floor) :=
  preservation_comp (rwR2_preservation terms c0 c1 rest hbase)
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation
      (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor hceiling)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
theorem peepholeR2_satisfiable_iff (hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1)
    (floor : Nat)
    (hceiling : transitionCeilingOk (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor = true)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor (rootProgramR2 terms c0 c1 rest)) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash
        (compactE1 (rwR2Descriptor pub sec atoms terms c0 c1 rest)
          (deadColsE1 (rwR2Descriptor pub sec atoms terms c0 c1 rest) floor)) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (peepholeR2_preservation terms c0 c1 rest hbase floor hceiling)
    hash minit mfin maddrs

end Pass

/-! ## 8. Exact cost recovery — the CERTIFIED object is the object we measure.

The disjunction subtree (`zeroTest`×2 + `∨`, 8 gates) and the collapsing `∧`-node (2 gates) — 10
gates in all — are replaced by the single quadratic pair gate and the re-pointed accept: exactly
`-9` constraints. This is proved of `rwR2Descriptor`, the SAME record whose `SatisfiabilityPreservation`
is proved above; there is no separate hand-built `loweredDescriptor` in the loop. -/

section Cost

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (c0 c1 : Fin atoms) (rest : Formula atoms)

theorem graphConstraintsR2_split :
    (graphConstraintsAt (rootProgramR2 terms c0 c1 rest)).length =
      (midConstraints pub sec atoms rest).length + 10 := by
  unfold graphConstraintsAt
  rw [srcR2_nodesAt]
  simp [List.flatMap_append, midConstraints, midNodes,
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints]

/-- THE COST LEG: the certified rewritten descriptor carries exactly nine fewer constraints. -/
theorem rwR2_constraints_recovery :
    (rwR2Descriptor pub sec atoms terms c0 c1 rest).constraints.length + 9 =
      (descriptor (rootProgramR2 terms c0 c1 rest)).constraints.length := by
  simp only [rwR2Descriptor, rwR2Constraints, descriptor, List.length_append, List.length_cons,
    List.length_nil]
  rw [graphConstraintsR2_split]
  omega

end Cost

/-! ## 9. A concrete, non-vacuous instance, with parity MEASURED on the certified output.

`(sec = 0) ∨ (sec = 1)` conjoined with `.top` — one asserted booleanity disjunction on the frontier,
exactly the pilot's per-component shape.  R2 fires (`hbase` holds by `rfl`), the satisfying witness
is carried across the pass by the completeness leg (non-vacuous), and the resource numbers are
`#guard`ed on `rwR2Descriptor` — the SAME object `rwR2_preservation` is proved for. -/

namespace Demo

def terms : Fin 2 → AffineTerm (1 + 1)
  | ⟨0, _⟩ => .input ⟨1, by omega⟩
  | ⟨1, _⟩ => AffineTerm.eqConst ⟨1, by omega⟩ 1
  | ⟨_, _⟩ => .const 0

def c0 : Fin 2 := ⟨0, by omega⟩
def c1 : Fin 2 := ⟨1, by omega⟩
def rest : Formula 2 := .top

theorem demo_hbase : (peelConst (terms c0)).1 = (peelConst (terms c1)).1 := rfl

noncomputable def goodInput : Fin (1 + 1) → ZMod 2013265921 := fun _ => 0

theorem good_holds : (rootProgramR2 terms c0 c1 rest).Holds goodInput := by
  refine ⟨?_, ?_⟩
  · left
    show (AffineTerm.input ⟨1, by omega⟩ : AffineTerm (1 + 1)).evalField goodInput = 0
    simp [goodInput, AffineTerm.evalField]
  · trivial

theorem demo_source_satisfiable (hash : List ℤ → ℤ) :
    ∃ s, Satisfied2 hash (descriptor (rootProgramR2 terms c0 c1 rest))
      (fun _ => 0) (fun _ => (0, 0)) [] s :=
  ⟨canonicalTrace (rootProgramR2 terms c0 c1 rest) goodInput,
    canonical_complete hash (rootProgramR2 terms c0 c1 rest) goodInput good_holds⟩

/-- NON-VACUITY: the CERTIFIED rewritten descriptor is satisfiable, via the completeness leg. -/
theorem demo_rw_satisfiable (hash : List ℤ → ℤ) :
    ∃ u, Satisfied2 hash (rwR2Descriptor 1 1 2 terms c0 c1 rest)
      (fun _ => 0) (fun _ => (0, 0)) [] u :=
  (rwR2_satisfiable_iff terms c0 c1 rest demo_hbase hash _ _ _).1 (demo_source_satisfiable hash)

/-- And back: an accepting target trace expands to an accepting SOURCE trace (the security leg). -/
theorem demo_security_roundtrip (hash : List ℤ → ℤ) :
    ∃ s, Satisfied2 hash (descriptor (rootProgramR2 terms c0 c1 rest))
      (fun _ => 0) (fun _ => (0, 0)) [] s :=
  (rwR2_satisfiable_iff terms c0 c1 rest demo_hbase hash _ _ _).2 (demo_rw_satisfiable hash)

-- Resources MEASURED on the certified objects (compiled `==`, no kernel `decide`).
#guard (descriptor (rootProgramR2 terms c0 c1 rest)).constraints.length == 14
#guard (rwR2Descriptor 1 1 2 terms c0 c1 rest).constraints.length == 5
#guard (rwR2Descriptor 1 1 2 terms c0 c1 rest).traceWidth ==
  (descriptor (rootProgramR2 terms c0 c1 rest)).traceWidth
#guard (rwR2Descriptor 1 1 2 terms c0 c1 rest).constraints.length + 9 ==
  (descriptor (rootProgramR2 terms c0 c1 rest)).constraints.length

end Demo

#assert_all_clean [
  gate_holds_iff,
  gate_holds_any,
  field_of_src_gate,
  fa_B, fa_B1, fa_B2, fa_B3, fa_B4, fa_top,
  r2_fieldMatch,
  rwR2_completeness_row,
  rwR2_security_row,
  rwR2_security,
  rwR2_completeness,
  rwR2_preservation,
  rwR2_satisfiable_iff,
  peepholeR2_preservation,
  graphConstraintsR2_split,
  rwR2_constraints_recovery,
  Demo.good_holds,
  Demo.demo_rw_satisfiable,
  Demo.demo_security_roundtrip
]

end Dregg2.Circuit.PeepholeR2Certified
