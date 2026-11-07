/-
# Dregg2.Circuit.PeepholeEmitMembership — THE LOWERING EMITS ITS OWN MEMBERSHIP FACTS.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint. Every
theorem below is a statement ABOUT the constraint list that `TypedLinearPredicateDescriptorIR2.descriptor`
emits from a `Formula`, proved by induction ON THE FORMULA — no constraint list is ever re-evaluated,
no `decide`, no `native_decide`.

## The wall this removes

`PeepholeFrontierScanSound.frontier_preservation_S` is a ∀-d theorem: the frontier collapse is a
genuine `SatisfiabilityPreservation` on every `FrontierCertifiedS` descriptor. Instantiating it on a
CONCRETE descriptor needed `out ∈ acceptReachableS (kept)` as a KERNEL Prop — and kernel-reducing the
pilot's 374-constraint fixpoint scan is exactly the OOM class. Four lanes left that concrete
certification open. Bespoke per-descriptor membership arguments do not scale either.

## The fix — three structural moves, none of which evaluates a scan

1. **The repair theorem** (§5, `forcedS_kept_of_forced`). `acceptReachable_sound` already hands us a
   `Forced` certificate over the FULL constraint list for free (a collapse site is recognised only if
   its output is accept-reachable). The ONLY thing that can break when re-running such a derivation
   over the SURVIVING list is a dropped BIT gate: accept gates and and-gates are never dropped
   (`frontierKeep_acceptGate`, `frontierKeep_andGate`, both `rfl`). So `Forced cs c` upgrades to
   `ForcedS kept c` under ONE side condition:

       (H)  every and-gate `out − l·r` in the list has a child whose bit gate SURVIVES.

   `ForcedS`'s own-bit constructors (`andLself`/`andRself`) and its sibling constructors together
   cover both ways the surviving gate can sit.

2. **(H) is discharged BY THE LOWERING** (§4, §6). An and-gate in the emitted list can only have come
   from an emitted `.and` node (§4 inverts the emission: public pins are `.base`; an atom link's body
   is `x − affine` and an affine window is NEVER `l·r`, `AffineTerm.toWindowAt_ne_mul_loc`; the accept
   gate's second factor is a constant; `.or`/`.not`/zeroTest bodies have different heads). That node's
   children are the OUTPUT WIRES of the two subformulas, and every subformula emits its own booleanity
   gate (`bitGate_of_outputAt`). So the right child's bit gate is in the list; it survives unless the
   right child's column is a COLLAPSED output — and a collapsed output is always a zeroTest output
   (§4, via the inverse-gate inversion), while an `.and`/`.or`/`.not` subformula's output column is an
   OP output. §3 proves those two column classes DISJOINT by the allocation ranges
   (`opOut_not_ztOut`), by induction on the formula. Hence: if every `.and` node's RIGHT child is an
   op-node (`AndRightOp`, a purely syntactic property of the SOURCE FORMULA), (H) holds.

3. **The concrete certifications** (§7). `AndRightOp` is proved for the field-delta pilot's source
   (`andAll [atom0, atom1, boolAtom 0, …, boolAtom 29]`, by induction on the conjunct list — the
   `andAll` recursion, not by unfolding 31 nodes) and for `secondDescriptor`. That yields, as PROVEN
   Props on the REAL descriptors:

       pilot_frontierCertifiedS   : FrontierCertifiedS (descriptor prog)
       pilot_frontier_preservation : SatisfiabilityPreservation (frontierPass (descriptor prog))
       second_frontier_preservation : SatisfiabilityPreservation (frontierPass secondDescriptor)

   No `#guard` carries any of these; a `#guard` proves no Prop.

## `AndRightOp` is a REAL precondition, not a proof artifact

The frontier collapse is UNSOUND on `.and (.atom i) (.atom j)`: both zero-tests are accept-reachable,
so both collapse, and the target then retains NO constraint pinning either output to a bit — take
`out_i = 2`, `out_j = 2⁻¹`, `x_i = x_j = 0`: every surviving gate holds while the source's booleanity
gate fails. A certificate for that shape cannot exist, and the hypothesis that at least one child of
each conjunction is an op-node is exactly what rules it out. Both real descriptors satisfy it.

## Named residual (no `sorry`, no stand-in)

* The certification is for descriptors emitted by `TypedLinearPredicateDescriptorIR2.descriptor`
  (equivalently the `DirectLogicBoolGraph` lowering it wraps). A descriptor from a DIFFERENT emitter
  gets nothing here; it needs its own emission-inversion lemmas (§4 is where they would go).
* `AndRightOp` is sufficient, not necessary: an `.and` whose LEFT child is an op-node is equally
  certifiable (swap `andLsib`/`andRself` for `andLself`/`andRsib` in §5). The stated form is the one
  both real descriptors satisfy; the general "some child is an op-node" variant is the obvious
  strengthening and is not proved here.
* Everything inherits the undischarged FRI/STARK floor: this is a refinement between two constraint
  systems, not a proof that the deployed prover is sound.

Standalone and additive: imports `PeepholeFrontierScanSound`; changes none of it.
-/
import Dregg2.Circuit.PeepholeFrontierScanSound

namespace Dregg2.Circuit.PeepholeEmitMembership

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node gate bitBody bitBody_eq subW negW witnessCount outputAt nodesAt)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
  (Program AffineTerm descriptor boolBase rawBase atomLink atomLinkBody atomLinks
    graphConstraintsAt acceptConstraintAt)
open Dregg2.Circuit.PeepholeFrontierScan
open Dregg2.Circuit.PeepholeFrontierScanSound

set_option autoImplicit false

/-- The source formula language of the lowering. -/
abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

/-! ## 1. Wire / gate inversion helpers. -/

/-- The output wire of a materialized node determines its column. -/
theorem wire_expr_eq_loc {w : Wire} {c : Nat} (h : w.expr = .loc c) : w = .col c := by
  cases w <;> simp [Wire.expr] at h ⊢
  · exact h

/-- An AFFINE atom-link window is never a bare product of two columns: every `mul` the affine lowering
emits has a CONSTANT left factor. This is what keeps atom links out of the and-edge recogniser. -/
theorem toWindowAt_ne_mul_loc {m : Nat} (rawB : Nat) (t : AffineTerm m) (l r : Nat) :
    t.toWindowAt rawB ≠ .mul (.loc l) (.loc r) := by
  cases t <;> simp [AffineTerm.toWindowAt]

/-! ## 2. Column classes of the lowering — zeroTest outputs vs op-node outputs. -/

/-- The columns the lowering pins as ZERO-TEST outputs (one per atom, at the atom's base). -/
def ztOuts {n : Nat} (b : Nat) : Formula n → List Nat
  | .atom _ => [b]
  | .top | .bot => []
  | .not p => ztOuts b p
  | .and p q => ztOuts b p ++ ztOuts (b + witnessCount p) q
  | .or p q => ztOuts b p ++ ztOuts (b + witnessCount p) q

/-- The columns the lowering pins as OP-NODE (`not`/`and`/`or`) outputs — the last column of each
non-atom block. -/
def opOuts {n : Nat} (b : Nat) : Formula n → List Nat
  | .atom _ => []
  | .top | .bot => []
  | .not p => opOuts b p ++ [b + witnessCount p]
  | .and p q =>
      opOuts b p ++ opOuts (b + witnessCount p) q ++ [b + witnessCount p + witnessCount q]
  | .or p q =>
      opOuts b p ++ opOuts (b + witnessCount p) q ++ [b + witnessCount p + witnessCount q]

/-- A zeroTest output occupies two columns strictly inside its block. -/
theorem ztOuts_range {n : Nat} : ∀ (F : Formula n) (b c : Nat), c ∈ ztOuts b F →
    b ≤ c ∧ c + 2 ≤ b + witnessCount F := by
  intro F
  induction F with
  | atom a =>
      intro b c hc
      simp only [ztOuts, List.mem_singleton] at hc
      subst hc
      simp only [witnessCount]
      omega
  | top => intro b c hc; simp [ztOuts] at hc
  | bot => intro b c hc; simp [ztOuts] at hc
  | not p ih =>
      intro b c hc
      simp only [ztOuts] at hc
      have := ih b c hc
      simp only [witnessCount]
      omega
  | and p q ihp ihq =>
      intro b c hc
      simp only [ztOuts, List.mem_append] at hc
      simp only [witnessCount]
      rcases hc with h | h
      · have := ihp b c h; omega
      · have := ihq (b + witnessCount p) c h; omega
  | or p q ihp ihq =>
      intro b c hc
      simp only [ztOuts, List.mem_append] at hc
      simp only [witnessCount]
      rcases hc with h | h
      · have := ihp b c h; omega
      · have := ihq (b + witnessCount p) c h; omega

/-- An op-node output is the last column of its block. -/
theorem opOuts_range {n : Nat} : ∀ (F : Formula n) (b c : Nat), c ∈ opOuts b F →
    b ≤ c ∧ c + 1 ≤ b + witnessCount F := by
  intro F
  induction F with
  | atom a => intro b c hc; simp [opOuts] at hc
  | top => intro b c hc; simp [opOuts] at hc
  | bot => intro b c hc; simp [opOuts] at hc
  | not p ih =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [witnessCount]
      rcases hc with h | h
      · have := ih b c h; omega
      · omega
  | and p q ihp ihq =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [witnessCount]
      rcases hc with (h | h) | h
      · have := ihp b c h; omega
      · have := ihq (b + witnessCount p) c h; omega
      · omega
  | or p q ihp ihq =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [witnessCount]
      rcases hc with (h | h) | h
      · have := ihp b c h; omega
      · have := ihq (b + witnessCount p) c h; omega
      · omega

/-- THE DISJOINTNESS. No column is both a zeroTest output and an op-node output — the allocation
ranges keep them apart, by induction on the formula. -/
theorem opOut_not_ztOut {n : Nat} : ∀ (F : Formula n) (b c : Nat), c ∈ opOuts b F →
    c ∉ ztOuts b F := by
  intro F
  induction F with
  | atom a => intro b c hc; simp [opOuts] at hc
  | top => intro b c hc; simp [opOuts] at hc
  | bot => intro b c hc; simp [opOuts] at hc
  | not p ih =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [ztOuts]
      rcases hc with h | h
      · exact ih b c h
      · intro hz
        have := ztOuts_range p b c hz
        omega
  | and p q ihp ihq =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [ztOuts, List.mem_append, not_or]
      rcases hc with (h | h) | h
      · refine ⟨ihp b c h, ?_⟩
        intro hz
        have h1 := opOuts_range p b c h
        have h2 := ztOuts_range q (b + witnessCount p) c hz
        omega
      · refine ⟨?_, ihq (b + witnessCount p) c h⟩
        intro hz
        have h1 := opOuts_range q (b + witnessCount p) c h
        have h2 := ztOuts_range p b c hz
        omega
      · subst h
        refine ⟨?_, ?_⟩
        · intro hz; have := ztOuts_range p b _ hz; omega
        · intro hz; have := ztOuts_range q (b + witnessCount p) _ hz; omega
  | or p q ihp ihq =>
      intro b c hc
      simp only [opOuts, List.mem_append, List.mem_singleton] at hc
      simp only [ztOuts, List.mem_append, not_or]
      rcases hc with (h | h) | h
      · refine ⟨ihp b c h, ?_⟩
        intro hz
        have h1 := opOuts_range p b c h
        have h2 := ztOuts_range q (b + witnessCount p) c hz
        omega
      · refine ⟨?_, ihq (b + witnessCount p) c h⟩
        intro hz
        have h1 := opOuts_range q (b + witnessCount p) c h
        have h2 := ztOuts_range p b c hz
        omega
      · subst h
        refine ⟨?_, ?_⟩
        · intro hz; have := ztOuts_range p b _ hz; omega
        · intro hz; have := ztOuts_range q (b + witnessCount p) _ hz; omega

/-- An emitted zeroTest node's output really is a zeroTest column. -/
theorem zeroTest_mem_ztOuts {n : Nat} : ∀ (F : Formula n) (b x out inv : Nat),
    Node.zeroTest x out inv ∈ nodesAt b F → out ∈ ztOuts b F := by
  intro F
  induction F with
  | atom a =>
      intro b x out inv h
      simp only [nodesAt, List.mem_singleton] at h
      have : out = b := by
        have := congrArg (fun nd => match nd with | Node.zeroTest _ o _ => o | _ => 0) h
        simpa using this
      simp [ztOuts, this]
  | top => intro b x out inv h; simp [nodesAt] at h
  | bot => intro b x out inv h; simp [nodesAt] at h
  | not p ih =>
      intro b x out inv h
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact ih b x out inv h
      · exact absurd h (by simp)
  | and p q ihp ihq =>
      intro b x out inv h
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      simp only [ztOuts, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (ihp b x out inv h)
      · exact Or.inr (ihq (b + witnessCount p) x out inv h)
      · exact absurd h (by simp)
  | or p q ihp ihq =>
      intro b x out inv h
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      simp only [ztOuts, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (ihp b x out inv h)
      · exact Or.inr (ihq (b + witnessCount p) x out inv h)
      · exact absurd h (by simp)

/-! ## 3. `AndRightOp` — the syntactic side condition on the SOURCE FORMULA. -/

/-- The formula materializes an op node (`not`/`and`/`or`), i.e. its output column carries an emitted
booleanity gate that the frontier collapse never drops. -/
def IsOp {n : Nat} : Formula n → Prop
  | .atom _ => False
  | .top => False
  | .bot => False
  | .not _ => True
  | .and _ _ => True
  | .or _ _ => True

/-- Every conjunction in the formula has an OP-NODE right operand. This is exactly what makes the
frontier collapse certifiable: at each and-node the right child's booleanity gate survives. -/
def AndRightOp {n : Nat} : Formula n → Prop
  | .atom _ => True
  | .top => True
  | .bot => True
  | .not p => AndRightOp p
  | .and p q => IsOp q ∧ AndRightOp p ∧ AndRightOp q
  | .or p q => AndRightOp p ∧ AndRightOp q

/-- An op formula's output is a column, and it is an OP column. -/
theorem opOut_of_isOp {n : Nat} (b : Nat) (F : Formula n) (h : IsOp F) :
    ∃ c, outputAt b F = Wire.col c ∧ c ∈ opOuts b F := by
  cases F with
  | atom a => exact absurd h (by simp [IsOp])
  | top => exact absurd h (by simp [IsOp])
  | bot => exact absurd h (by simp [IsOp])
  | not p => exact ⟨b + witnessCount p, rfl, by simp [opOuts]⟩
  | and p q => exact ⟨b + witnessCount p + witnessCount q, rfl, by simp [opOuts]⟩
  | or p q => exact ⟨b + witnessCount p + witnessCount q, rfl, by simp [opOuts]⟩

/-- EVERY materialized subformula pins its own output column with a booleanity gate — the emission
carries its own bit-gate membership fact. -/
theorem bitGate_of_outputAt {n : Nat} (b : Nat) (F : Formula n) (c : Nat)
    (h : outputAt b F = Wire.col c) :
    bitGate c ∈ (nodesAt b F).flatMap Node.constraints := by
  cases F with
  | atom a =>
      have hc : c = b := by simpa [outputAt] using h.symm
      subst hc
      exact List.mem_flatMap.2 ⟨Node.zeroTest a.val c (c + 1), by simp [nodesAt],
        by simp [Node.constraints, bitGate]⟩
  | top => exact absurd h (by simp [outputAt])
  | bot => exact absurd h (by simp [outputAt])
  | not p =>
      have hc : c = b + witnessCount p := by simpa [outputAt] using h.symm
      subst hc
      exact List.mem_flatMap.2 ⟨Node.not (outputAt b p) (b + witnessCount p),
        by simp [nodesAt], by simp [Node.constraints, bitGate]⟩
  | and p q =>
      have hc : c = b + witnessCount p + witnessCount q := by simpa [outputAt] using h.symm
      subst hc
      exact List.mem_flatMap.2
        ⟨Node.and (outputAt b p) (outputAt (b + witnessCount p) q)
            (b + witnessCount p + witnessCount q),
          by simp [nodesAt], by simp [Node.constraints, bitGate]⟩
  | or p q =>
      have hc : c = b + witnessCount p + witnessCount q := by simpa [outputAt] using h.symm
      subst hc
      exact List.mem_flatMap.2
        ⟨Node.or (outputAt b p) (outputAt (b + witnessCount p) q)
            (b + witnessCount p + witnessCount q),
          by simp [nodesAt], by simp [Node.constraints, bitGate]⟩

/-- THE STRUCTURAL CERTIFICATE, by induction ON THE FORMULA: every emitted and-node's right child is
an OP column carrying an emitted booleanity gate. No constraint list is evaluated. -/
theorem and_node_right {n : Nat} : ∀ (F : Formula n) (b l r out : Nat), AndRightOp F →
    Node.and (Wire.col l) (Wire.col r) out ∈ nodesAt b F →
      r ∈ opOuts b F ∧ bitGate r ∈ (nodesAt b F).flatMap Node.constraints := by
  intro F
  induction F with
  | atom a => intro b l r out _ h; simp [nodesAt] at h
  | top => intro b l r out _ h; simp [nodesAt] at h
  | bot => intro b l r out _ h; simp [nodesAt] at h
  | not p ih =>
      intro b l r out hok h
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := ih b l r out hok h
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl h1
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _ h2
      · exact absurd h (by simp)
  | and p q ihp ihq =>
      intro b l r out hok h
      obtain ⟨hq, hp', hq'⟩ := hok
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | h
      · obtain ⟨h1, h2⟩ := ihp b l r out hp' h
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl (Or.inl h1)
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _ (List.mem_append_left _ h2)
      · obtain ⟨h1, h2⟩ := ihq (b + witnessCount p) l r out hq' h
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl (Or.inr h1)
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _ (List.mem_append_right _ h2)
      · obtain ⟨c, hc1, hc2⟩ := opOut_of_isOp (b + witnessCount p) q hq
        have hr : outputAt (b + witnessCount p) q = Wire.col r := by
          have := congrArg (fun nd => match nd with
            | Node.and _ rw _ => rw
            | _ => Wire.zero) h
          simpa using this.symm
        have hrc : r = c := by
          rw [hr] at hc1
          simpa using hc1
        subst hrc
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl (Or.inr hc2)
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _
            (List.mem_append_right _ (bitGate_of_outputAt (b + witnessCount p) q r hr))
  | or p q ihp ihq =>
      intro b l r out hok h
      obtain ⟨hp', hq'⟩ := hok
      simp only [nodesAt, List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | h
      · obtain ⟨h1, h2⟩ := ihp b l r out hp' h
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl (Or.inl h1)
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _ (List.mem_append_left _ h2)
      · obtain ⟨h1, h2⟩ := ihq (b + witnessCount p) l r out hq' h
        refine ⟨?_, ?_⟩
        · simp only [opOuts, List.mem_append]; exact Or.inl (Or.inr h1)
        · simp only [nodesAt, List.flatMap_append]
          exact List.mem_append_left _ (List.mem_append_right _ h2)
      · exact absurd h (by simp)

/-! ## 4. Emission inversion — which emitted constraint can a gate SHAPE have come from. -/

/-- The four families of the emitted constraint list. -/
theorem descriptor_mem_split {pub sec atoms : Nat} (p : Program pub sec atoms)
    (c : VmConstraint2) (h : c ∈ (descriptor p).constraints) :
    (∃ i : Nat, c = .base (.piBinding .first (rawBase atoms + i) i)) ∨
    (∃ a : Fin atoms, c = atomLink p a) ∨
    (c ∈ (nodesAt (boolBase pub sec atoms) p.source).flatMap Node.constraints) ∨
    (c = acceptConstraintAt p) := by
  simp only [descriptor, List.mem_append, List.mem_singleton] at h
  rcases h with ((hpin | hlink) | hgraph) | hacc
  · left
    simp only [Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.publicPins,
      List.mem_map, List.mem_range] at hpin
    obtain ⟨i, -, rfl⟩ := hpin
    exact ⟨i, rfl⟩
  · right; left
    simp only [atomLinks, List.mem_map] at hlink
    obtain ⟨a, -, rfl⟩ := hlink
    exact ⟨a, rfl⟩
  · right; right; left
    simpa [graphConstraintsAt] using hgraph
  · right; right; right; exact hacc

/-- An and-gate in a materialized node list comes from an emitted `.and` node with COLUMN children. -/
theorem andGate_mem_nodes {n : Nat} (b : Nat) (F : Formula n) (out l r : Nat)
    (h : andGate out l r ∈ (nodesAt b F).flatMap Node.constraints) :
    Node.and (Wire.col l) (Wire.col r) out ∈ nodesAt b F := by
  obtain ⟨node, hnode, hc⟩ := List.mem_flatMap.1 h
  cases node with
  | zeroTest x o i =>
      exact absurd hc (by simp [Node.constraints, andGate, gate, subW, negW, bitBody_eq, Wire.expr])
  | not w o =>
      exact absurd hc (by simp [Node.constraints, andGate, gate, subW, negW, bitBody_eq, Wire.expr])
  | or lw rw o =>
      exact absurd hc (by simp [Node.constraints, andGate, gate, subW, negW, bitBody_eq, Wire.expr])
  | and lw rw o =>
      simp only [Node.constraints, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · exact absurd hc (by simp [andGate, gate, subW, negW, bitBody_eq, Wire.expr])
      · have hbody : subW (Wire.col out).expr (.mul (Wire.col l).expr (Wire.col r).expr)
            = subW (.loc o) (.mul lw.expr rw.expr) := by
          have := congrArg (fun cc => match cc with
            | VmConstraint2.windowGate w => w.body
            | _ => WindowExpr.const 0) hc
          simpa [gate, andGate] using this
        simp only [subW, negW, Wire.expr, WindowExpr.add.injEq, WindowExpr.mul.injEq,
          WindowExpr.loc.injEq] at hbody
        obtain ⟨ho, -, hl, hr⟩ := hbody
        subst ho
        rw [wire_expr_eq_loc hl.symm, wire_expr_eq_loc hr.symm] at hnode
        exact hnode

/-- An and-gate in the EMITTED DESCRIPTOR comes from an emitted `.and` node. Public pins are `.base`;
an atom link's product factor would have to be an affine window (impossible, §1); the accept gate's
second factor is a constant. -/
theorem andGate_mem_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms)
    (out l r : Nat) (h : andGate out l r ∈ (descriptor p).constraints) :
    Node.and (Wire.col l) (Wire.col r) out ∈ nodesAt (boolBase pub sec atoms) p.source := by
  rcases descriptor_mem_split p _ h with ⟨i, hi⟩ | ⟨a, ha⟩ | hg | hacc
  · exact absurd hi (by simp [andGate, gate])
  · exfalso
    have hbody : subW (Wire.col out).expr (.mul (Wire.col l).expr (Wire.col r).expr)
        = atomLinkBody p a := by
      have := congrArg (fun cc => match cc with
        | VmConstraint2.windowGate w => w.body
        | _ => WindowExpr.const 0) ha
      simpa [gate, andGate, atomLink] using this
    simp only [atomLinkBody, subW, negW, Wire.expr, WindowExpr.add.injEq,
      WindowExpr.mul.injEq] at hbody
    exact toWindowAt_ne_mul_loc (rawBase atoms) (p.atomTerms a) l r hbody.2.2.symm
  · exact andGate_mem_nodes _ _ _ _ _ hg
  · exfalso
    have hbody : subW (Wire.col out).expr (.mul (Wire.col l).expr (Wire.col r).expr)
        = subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1) := by
      have := congrArg (fun cc => match cc with
        | VmConstraint2.windowGate w => w.body
        | _ => WindowExpr.const 0) hacc
      simpa [gate, andGate, acceptConstraintAt] using this
    simp only [subW, negW, Wire.expr, WindowExpr.add.injEq, WindowExpr.mul.injEq] at hbody
    exact absurd hbody.2.2 (by simp)

/-- An inverse gate in a materialized node list comes from an emitted zeroTest node. -/
theorem invGate_mem_nodes {n : Nat} (b : Nat) (F : Formula n) (x out inv : Nat)
    (h : invGate x out inv ∈ (nodesAt b F).flatMap Node.constraints) :
    Node.zeroTest x out inv ∈ nodesAt b F := by
  obtain ⟨node, hnode, hc⟩ := List.mem_flatMap.1 h
  cases node with
  | not w o =>
      exact absurd hc (by simp [Node.constraints, invGate, gate, bitBody_eq, Wire.expr])
  | and lw rw o =>
      exact absurd hc (by simp [Node.constraints, invGate, gate, subW, negW, bitBody_eq, Wire.expr])
  | or lw rw o =>
      exact absurd hc (by simp [Node.constraints, invGate, gate, subW, negW, bitBody_eq, Wire.expr])
  | zeroTest x' o i =>
      simp only [Node.constraints, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc
      · exact absurd hc (by simp [invGate, gate, bitBody_eq, Wire.expr])
      · exact absurd hc (by simp [invGate, gate])
      · have hbody : (WindowExpr.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))
            = .add (.add (.mul (.loc x') (.loc i)) (.loc o)) (.const (-1)) := by
          have := congrArg (fun cc => match cc with
            | VmConstraint2.windowGate w => w.body
            | _ => WindowExpr.const 0) hc
          simpa [gate, invGate] using this
        simp only [WindowExpr.add.injEq, WindowExpr.mul.injEq, WindowExpr.loc.injEq] at hbody
        obtain ⟨⟨⟨hx, hi⟩, ho⟩, -⟩ := hbody
        subst hx; subst hi; subst ho
        exact hnode

/-- An inverse gate in the EMITTED DESCRIPTOR comes from an emitted zeroTest node: no atom link,
public pin, or accept gate has that shape. -/
theorem invGate_mem_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms)
    (x out inv : Nat) (h : invGate x out inv ∈ (descriptor p).constraints) :
    Node.zeroTest x out inv ∈ nodesAt (boolBase pub sec atoms) p.source := by
  rcases descriptor_mem_split p _ h with ⟨i, hi⟩ | ⟨a, ha⟩ | hg | hacc
  · exact absurd hi (by simp [invGate, gate])
  · exfalso
    have hbody : (WindowExpr.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))
        = atomLinkBody p a := by
      have := congrArg (fun cc => match cc with
        | VmConstraint2.windowGate w => w.body
        | _ => WindowExpr.const 0) ha
      simpa [gate, atomLink, invGate] using this
    simp only [atomLinkBody, subW, negW] at hbody
    exact absurd hbody (by simp)
  · exact invGate_mem_nodes _ _ _ _ _ hg
  · exfalso
    have hbody : (WindowExpr.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))
        = subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1) := by
      have := congrArg (fun cc => match cc with
        | VmConstraint2.windowGate w => w.body
        | _ => WindowExpr.const 0) hacc
      simpa [gate, acceptConstraintAt, invGate] using this
    simp only [subW, negW, Wire.expr, WindowExpr.add.injEq] at hbody
    exact absurd hbody.2 (by simp)

/-- A recognised collapse site really carries its inverse gate in the list (the inversion the scan's
recogniser condition hides). -/
theorem invGate_of_mem_collapseSites {cs : List VmConstraint2} {x out inv : Nat}
    (h : (x, out, inv) ∈ collapseSites cs) : invGate x out inv ∈ cs := by
  obtain ⟨c, hc, hmatch⟩ := List.mem_filterMap.1 h
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · exact absurd hmatch (by simp)
    · rename_i honT
      have honT' : onT = false := by cases onT <;> simp_all
      subst honT'
      split at hmatch
      · rename_i x' inv' out' k
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hmatch
          obtain ⟨hx, hout, hinv⟩ := hmatch
          subst hx; subst hout; subst hinv
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨hk, -⟩, -⟩ := hcond
          subst hk
          exact hc
        · exact absurd hmatch (by simp)
      · exact absurd hmatch (by simp)
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch
  | chalGate _ => simp at hmatch

/-- Consequently EVERY collapsed output column of an emitted descriptor is a zeroTest column. -/
theorem collapsedOut_mem_ztOuts {pub sec atoms : Nat} (p : Program pub sec atoms) {c : Nat}
    (h : c ∈ collapsedOuts (descriptor p).constraints) :
    c ∈ ztOuts (boolBase pub sec atoms) p.source := by
  obtain ⟨x, inv, hs⟩ := collapsedOut_site h
  exact zeroTest_mem_ztOuts p.source (boolBase pub sec atoms) x c inv
    (invGate_mem_descriptor p x c inv (invGate_of_mem_collapseSites hs))

/-! ## 5. THE REPAIR THEOREM — a full-list `Forced` certificate re-derived over the KEPT list. -/

/-- And-gates are never dropped by the frontier collapse (their body is not a bit / product / inverse
shape). -/
theorem frontierKeep_andGate (cs : List VmConstraint2) (out l r : Nat) :
    frontierKeep cs (andGate out l r) = true := rfl

/-- A bit gate survives exactly when its column is not a collapsed output. -/
theorem frontierKeep_bitGate {cs : List VmConstraint2} {c : Nat}
    (h : c ∉ collapsedOuts cs) : frontierKeep cs (bitGate c) = true := by
  simp only [frontierKeep, bitGate, gate, bitBody_eq, Wire.expr]
  simp [h]

/-- THE REPAIR. A `Forced` derivation over the FULL list re-derives as a `ForcedS` derivation over the
SURVIVING list, under one side condition: every and-gate has a child whose booleanity gate survives.
Accept gates and and-gates are never dropped, so the bit gate is the only thing that can break, and
`ForcedS`'s own-bit constructors absorb whichever child survives. -/
theorem forcedS_kept_of_forced {d : EffectVmDescriptor2}
    (hbit : ∀ out l r, andGate out l r ∈ d.constraints →
      bitGate l ∈ keptOf d ∨ bitGate r ∈ keptOf d)
    {c : Nat} (cert : Forced d.constraints c) : ForcedS (keptOf d) c := by
  induction cert with
  | accept c h =>
      exact .accept c (List.mem_filter.2 ⟨h, frontierKeep_acceptGate d.constraints c⟩)
  | andL out l r hpar hg hrb ih =>
      have hgk : andGate out l r ∈ keptOf d :=
        List.mem_filter.2 ⟨hg, frontierKeep_andGate d.constraints out l r⟩
      rcases hbit out l r hg with hl | hr
      · exact .andLself out l r ih hgk hl
      · exact .andLsib out l r ih hgk hr
  | andR out l r hpar hg hlb ih =>
      have hgk : andGate out l r ∈ keptOf d :=
        List.mem_filter.2 ⟨hg, frontierKeep_andGate d.constraints out l r⟩
      rcases hbit out l r hg with hl | hr
      · exact .andRsib out l r ih hgk hl
      · exact .andRself out l r ih hgk hr

/-! ## 6. THE MAIN THEOREM — the lowering certifies its own frontier collapse. -/

/-- (H) DISCHARGED BY THE EMISSION: on a descriptor emitted from an `AndRightOp` source, every
and-gate's RIGHT child carries a SURVIVING booleanity gate. -/
theorem right_bitGate_kept {pub sec atoms : Nat} (p : Program pub sec atoms)
    (hp : AndRightOp p.source) (out l r : Nat)
    (h : andGate out l r ∈ (descriptor p).constraints) :
    bitGate r ∈ keptOf (descriptor p) := by
  obtain ⟨hop, hmem⟩ :=
    and_node_right p.source (boolBase pub sec atoms) l r out hp (andGate_mem_descriptor p out l r h)
  have hnotzt : r ∉ ztOuts (boolBase pub sec atoms) p.source :=
    opOut_not_ztOut p.source (boolBase pub sec atoms) r hop
  have hnotcol : r ∉ collapsedOuts (descriptor p).constraints := fun hc =>
    hnotzt (collapsedOut_mem_ztOuts p hc)
  have hin : bitGate r ∈ (descriptor p).constraints := by
    simp only [descriptor, List.mem_append]
    exact Or.inl (Or.inr (by simpa [graphConstraintsAt] using hmem))
  exact List.mem_filter.2 ⟨hin, frontierKeep_bitGate hnotcol⟩

/-- THE STRUCTURAL CERTIFICATION. Every descriptor the typed-linear lowering emits from a source
formula whose every conjunction has an op-node right operand is `FrontierCertifiedS` — with no scan
re-evaluated, no `decide`, and no per-descriptor bespoke argument. -/
theorem frontierCertifiedS_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms)
    (hp : AndRightOp p.source) : FrontierCertifiedS (descriptor p) := by
  intro x out inv hs
  exact forcedS_kept_of_forced
    (fun o l r hg => Or.inr (right_bitGate_kept p hp o l r hg))
    (acceptReachable_sound (collapseSites_out_reachable hs))

/-- BOTH LEGS on such a descriptor: the frontier collapse is a genuine equisatisfiability-preserving
passive pass on it. -/
theorem frontier_preservation_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms)
    (hp : AndRightOp p.source) :
    SatisfiabilityPreservation (frontierPass (descriptor p)) :=
  frontier_preservation_S (descriptor p) (frontierCertifiedS_descriptor p hp)

/-- …and the source/target satisfiability equivalence it yields. -/
theorem frontier_satisfiable_iff_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms)
    (hp : AndRightOp p.source) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor p) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (frontierCollapse (descriptor p)) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (frontier_preservation_descriptor p hp) hash minit mfin maddrs

/-! ## 7. THE CONCRETE INSTANCES — the field-delta pilot and the second descriptor. -/

/-- The conjunct list's LAST entry is an op formula (mirrors `andAll`'s own recursion). -/
def OpLast {n : Nat} : List (Formula n) → Prop
  | [] => True
  | [f] => IsOp f
  | _ :: rest => OpLast rest

@[simp] theorem opLast_cons_cons {n : Nat} (a b : Formula n) (l : List (Formula n)) :
    OpLast (a :: b :: l) = OpLast (b :: l) := rfl

theorem opLast_map {α : Type} {n : Nat} (f : α → Formula n) (hf : ∀ x, IsOp (f x)) :
    ∀ (l : List α), OpLast (l.map f)
  | [] => trivial
  | [x] => hf x
  | _ :: y :: rest => opLast_map f hf (y :: rest)

section Pilot

open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog source andAll boolAtom)

/-- A conjunct list with an op-node last entry folds to an op formula. -/
theorem isOp_andAll : ∀ (l : List (Formula 62)), l ≠ [] → OpLast l → IsOp (andAll l)
  | [], h, _ => absurd rfl h
  | [f], _, h => by simp only [andAll]; exact h
  | _ :: _ :: _, _, _ => by simp [andAll, IsOp]

/-- THE SPINE LEMMA: `andAll` of conjuncts that are individually `AndRightOp`, with an op-node LAST
conjunct, is `AndRightOp`. Proved by induction on the CONJUNCT LIST — the pilot's 31-node spine is
never unfolded. -/
theorem andRightOp_andAll : ∀ (l : List (Formula 62)), (∀ g ∈ l, AndRightOp g) → OpLast l →
    AndRightOp (andAll l)
  | [], _, _ => by simp [andAll, AndRightOp]
  | [f], hall, _ => by simpa [andAll] using hall f (by simp)
  | f :: g :: rest, hall, hlast => by
      have hrec : AndRightOp (andAll (g :: rest)) :=
        andRightOp_andAll (g :: rest) (fun x hx => hall x (by simp [hx])) hlast
      have hop : IsOp (andAll (g :: rest)) := isOp_andAll (g :: rest) (by simp) hlast
      have hf : AndRightOp f := hall f (by simp)
      show AndRightOp (andAll (f :: g :: rest))
      rw [show andAll (f :: g :: rest) = .and f (andAll (g :: rest)) by simp [andAll]]
      exact ⟨hop, hf, hrec⟩

theorem isOp_boolAtom (j : Fin 30) : IsOp (boolAtom j) := trivial

theorem andRightOp_boolAtom (j : Fin 30) : AndRightOp (boolAtom j) := ⟨trivial, trivial⟩

/-- The pilot's source formula satisfies the side condition: its conjunction spine's right operands
are all `.and`/`.or` nodes (the 30 booleanity disjunctions and the nested conjunctions). -/
theorem pilot_source_andRightOp : AndRightOp prog.source := by
  have hsrc : source = andAll (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] :
      List (Formula 62)) ++ (List.finRange 30).map boolAtom) := rfl
  show AndRightOp source
  rw [hsrc]
  refine andRightOp_andAll _ ?_ ?_
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hg
    rcases hg with (rfl | rfl) | ⟨j, -, rfl⟩
    · trivial
    · trivial
    · exact andRightOp_boolAtom j
  · simp only [List.cons_append, List.nil_append]
    rw [opLast_cons_cons]
    cases hfr : List.finRange 30 with
    | nil =>
        exfalso
        have hlen := congrArg List.length hfr
        simp [List.length_finRange] at hlen
    | cons a t =>
        rw [List.map_cons, opLast_cons_cons]
        exact opLast_map boolAtom isOp_boolAtom (a :: t)

/-- ⚑ THE CERTIFICATION THAT WAS OPEN THROUGH FOUR LANES — a PROVEN Prop on the REAL pilot
descriptor (374 constraints, 2 recognised frontier zero-tests, a 31-and right-nested spine), with no
`decide`, no `native_decide`, and no `#guard` carrying it. -/
theorem pilot_frontierCertifiedS : FrontierCertifiedS (descriptor prog) :=
  frontierCertifiedS_descriptor prog pilot_source_andRightOp

/-- BOTH LEGS on the pilot: the frontier collapse is a genuine equisatisfiability-preserving passive
pass on the field-delta pilot descriptor. -/
theorem pilot_frontier_preservation :
    SatisfiabilityPreservation (frontierPass (descriptor prog)) :=
  frontier_preservation_descriptor prog pilot_source_andRightOp

/-- The pilot's source/target satisfiability equivalence, discharged. -/
theorem pilot_frontier_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor prog) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (frontierCollapse (descriptor prog)) minit mfin maddrs u) :=
  frontier_satisfiable_iff_descriptor prog pilot_source_andRightOp hash minit mfin maddrs

end Pilot

section Second

open Dregg2.Circuit.PeepholeGeneralPass (secondTerms secondA secondRest secondDescriptor)
open Dregg2.Circuit.PeepholePassCertified (rootProgram)

/-- The second descriptor's source is `atom0 ∧ ((secret=0) ∨ (secret=1))`: one conjunction, right
operand an `.or` node. -/
theorem second_source_andRightOp :
    AndRightOp (rootProgram secondTerms secondA secondRest).source :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- ⚑ THE SECOND CONCRETE CERTIFICATION — an INDEPENDENT descriptor, same structural route. -/
theorem second_frontierCertifiedS : FrontierCertifiedS secondDescriptor :=
  frontierCertifiedS_descriptor (rootProgram secondTerms secondA secondRest)
    second_source_andRightOp

theorem second_frontier_preservation :
    SatisfiabilityPreservation (frontierPass secondDescriptor) :=
  frontier_preservation_descriptor (rootProgram secondTerms secondA secondRest)
    second_source_andRightOp

end Second

/-! ## 8. The side condition is LOAD-BEARING, and the certified collapse is NOT vacuous.

`AndRightOp` is refutable on exactly the shape where the collapse is unsound (`atom ∧ atom`): both
zero-tests are accept-reachable, so both collapse, and the target then pins NEITHER output to a bit —
`out_i = 2`, `out_j = 2⁻¹`, `x_i = x_j = 0` satisfies every surviving gate while the source's
booleanity gate fails. So this is a real precondition, not a proof convenience. -/

theorem andRightOp_atom_and_atom_false {n : Nat} (i j : Fin n) :
    ¬ AndRightOp ((.and (.atom i) (.atom j)) : Formula n) := by
  rintro ⟨h, -, -⟩
  exact h

/-! The collapse genuinely FIRES on both certified descriptors — pilot 374 → 370 constraints
(2 recognised frontier zero-tests, 6 gates dropped, 2 raw affine gates appended), second descriptor
18 → 16. Compiled `==` (evaluation, NOT the kernel): these are CONTEXT for the theorems above and
prove no Prop by themselves. -/
section NonVacuity
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Circuit.PeepholeGeneralPass (secondDescriptor)

#guard (collapseSites (descriptor prog).constraints).length == 2
#guard (descriptor prog).constraints.length == 374
#guard (frontierCollapse (descriptor prog)).constraints.length == 370
#guard (collapseSites secondDescriptor.constraints).length == 1
#guard secondDescriptor.constraints.length == 18
#guard (frontierCollapse secondDescriptor).constraints.length == 16

end NonVacuity

/-! ## 9. Kernel-cleanliness. -/

#assert_all_clean [
  wire_expr_eq_loc,
  toWindowAt_ne_mul_loc,
  ztOuts_range,
  opOuts_range,
  opOut_not_ztOut,
  zeroTest_mem_ztOuts,
  opOut_of_isOp,
  bitGate_of_outputAt,
  and_node_right,
  descriptor_mem_split,
  andGate_mem_nodes,
  andGate_mem_descriptor,
  invGate_mem_nodes,
  invGate_mem_descriptor,
  invGate_of_mem_collapseSites,
  collapsedOut_mem_ztOuts,
  frontierKeep_andGate,
  frontierKeep_bitGate,
  forcedS_kept_of_forced,
  right_bitGate_kept,
  frontierCertifiedS_descriptor,
  frontier_preservation_descriptor,
  frontier_satisfiable_iff_descriptor,
  andRightOp_andAll,
  pilot_source_andRightOp,
  pilot_frontierCertifiedS,
  pilot_frontier_preservation,
  pilot_frontier_satisfiable_iff,
  second_source_andRightOp,
  second_frontierCertifiedS,
  second_frontier_preservation,
  andRightOp_atom_and_atom_false
]

end Dregg2.Circuit.PeepholeEmitMembership
