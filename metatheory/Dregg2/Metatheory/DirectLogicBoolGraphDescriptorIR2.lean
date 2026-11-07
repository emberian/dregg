/-
# Materialized Boolean graphs in the live descriptor IR v2

`FiniteLogicDescriptorIR2` deliberately emits one nested polynomial.  This
module emits the other backend promised by the direct-logic optimizer: every
zero test and Boolean connective gets explicit witness columns and a flat list
of degree-at-most-two `windowGate`s.

The optimizer ledger counts the relation which exposes a Boolean output.  A
live accepting descriptor needs one additional, linear `output = 1` equation.
Consequently the headline specimen is 30 -> 13 graph equations and 31 -> 14
actual descriptor constraints.  Multiplications and auxiliary witnesses remain
26 -> 13 and 17 -> 8 respectively.  This correction is stated and proved
below; it is not hidden in a benchmark convention.

Standalone additive module.  No integration imports are changed.
-/

import Dregg2.Metatheory.DirectLogicOptimizerCertificate
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.GateExpr

namespace Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.ArithmetizationCost

set_option autoImplicit false

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

/-! ## 1. Explicit wires, nodes, and quadratic gates -/

inductive Wire where
  | zero
  | one
  | col (index : Nat)
  deriving DecidableEq, Repr

namespace Wire

def expr : Wire -> WindowExpr
  | .zero => .const 0
  | .one => .const 1
  | .col c => .loc c

def eval (a : Assignment) : Wire -> Int
  | .zero => 0
  | .one => 1
  | .col c => a c

@[simp] theorem eval_zero (a : Assignment) : Wire.zero.eval a = 0 := rfl
@[simp] theorem eval_one (a : Assignment) : Wire.one.eval a = 1 := rfl
@[simp] theorem eval_col (a : Assignment) (c : Nat) : (Wire.col c).eval a = a c := rfl

@[simp] theorem expr_eval (env : VmRowEnv) (w : Wire) :
    w.expr.eval env = w.eval env.loc := by
  cases w <;> rfl

end Wire

inductive Node where
  /-- `out` is the one-means-zero bit for input residual `x`; `inv` is the
  inverse witness in the nonzero branch. -/
  | zeroTest (x out inv : Nat)
  | not (input : Wire) (out : Nat)
  | and (left right : Wire) (out : Nat)
  | or (left right : Wire) (out : Nat)
  deriving DecidableEq, Repr

def negW (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x

def subW (x y : WindowExpr) : WindowExpr := .add x (negW y)

def bitBody (w : Wire) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (Dregg2.Circuit.GateExpr.ofWindow w.expr))

/-- ⚑ THE BYTE PIN. `bitBody` is `GateExpr.gBool` at the window view, for every `Wire` — the same
object `AirBuilder.gBin`, `AutomataflResolveEmit.gBin`, `AutomataflStepEmit.gBin`, `DyckStackEmit.
gBin` and `DyckStackRefine.gBin` each wrote out separately, at the two-row alphabet instead of the
one-row one. `rfl` per constructor, since `w.expr` is only concrete once `w` is. -/
theorem bitBody_eq (w : Wire) :
    bitBody w = .mul w.expr (.add w.expr (.const (-1))) := by
  cases w <;> rfl

def gate (body : WindowExpr) : VmConstraint2 :=
  .windowGate { body := body, onTransition := false }

namespace Node

/-- The exact equations of the relational `BoolGraph` primitives.  Inputs are
not redundantly Booleanized at each parent; each materialized output is. -/
def constraints : Node -> List VmConstraint2
  | .zeroTest x out inv =>
      [ gate (bitBody (.col out))
      , gate (.mul (.loc x) (.loc out))
      , gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))) ]
  | .not input out =>
      [ gate (bitBody (.col out))
      , gate (.add (.add (.loc out) input.expr) (.const (-1))) ]
  | .and left right out =>
      [ gate (bitBody (.col out))
      , gate (subW (.loc out) (.mul left.expr right.expr)) ]
  | .or left right out =>
      [ gate (bitBody (.col out))
      , gate (subW (.loc out)
          (subW (.add left.expr right.expr) (.mul left.expr right.expr))) ]

/-- Multiplications in the optimizer ledger: constant scaling is linear and
does not count as a nonlinear multiplication. -/
def multiplications : Node -> Nat
  | .zeroTest .. => 3
  | .not .. => 1
  | .and .. | .or .. => 2

@[simp] theorem constraints_length (node : Node) :
    node.constraints.length = match node with
      | .zeroTest .. => 3
      | .not .. => 2
      | .and .. | .or .. => 2 := by
  cases node <;> rfl

end Node

/-! ## 2. Deterministic postorder materialization -/

def witnessCount {n : Nat} : Formula n -> Nat
  | .atom _ => 2
  | .top | .bot => 0
  | .not p => witnessCount p + 1
  | .and p q | .or p q => witnessCount p + witnessCount q + 1

def outputAt {n : Nat} (base : Nat) : Formula n -> Wire
  | .atom _ => .col base
  | .top => .one
  | .bot => .zero
  | .not p => .col (base + witnessCount p)
  | .and p q | .or p q => .col (base + witnessCount p + witnessCount q)

def nodesAt {n : Nat} (base : Nat) : Formula n -> List Node
  | .atom a => [.zeroTest a.val base (base + 1)]
  | .top | .bot => []
  | .not p =>
      nodesAt base p ++ [.not (outputAt base p) (base + witnessCount p)]
  | .and p q =>
      nodesAt base p ++ nodesAt (base + witnessCount p) q ++
        [.and (outputAt base p) (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)]
  | .or p q =>
      nodesAt base p ++ nodesAt (base + witnessCount p) q ++
        [.or (outputAt base p) (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)]

def graphConstraints {n : Nat} (p : Formula n) : List VmConstraint2 :=
  (nodesAt n p).flatMap Node.constraints

def acceptConstraint {n : Nat} (p : Formula n) : VmConstraint2 :=
  gate (subW (outputAt n p).expr (.const 1))

def descriptor {n : Nat} (p : Formula n) : EffectVmDescriptor2 :=
  { name := "dregg-materialized-boolgraph-v2-" ++ toString n
  , traceWidth := n + witnessCount p
  , piCount := 0
  , tables := [mainTableDef (n + witnessCount p)]
  , constraints := graphConstraints p ++ [acceptConstraint p]
  , hashSites := []
  , ranges := [] }

def emittedMultiplications {n : Nat} (p : Formula n) : Nat :=
  (nodesAt n p).map Node.multiplications |>.sum

/-! ## 3. Exact agreement with the optimizer ledger -/

theorem witnessCount_eq_graphCost_witnesses {n : Nat} (p : Formula n) :
    witnessCount p = p.graphCost.witnesses := by
  induction p <;>
    simp [witnessCount, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, zeroTestGateCost,
      booleanNotGateCost, booleanBinaryGateCost, BackendCost.combine, *]

theorem nodesAt_constraint_length {n : Nat} (base : Nat) (p : Formula n) :
    ((nodesAt base p).flatMap Node.constraints).length = p.graphCost.equations := by
  induction p generalizing base <;>
    simp [nodesAt, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, Node.constraints,
      zeroTestGateCost, booleanNotGateCost, booleanBinaryGateCost,
      BackendCost.combine, *] <;> omega

theorem graphConstraints_length_eq_graphCost_equations {n : Nat} (p : Formula n) :
    (graphConstraints p).length = p.graphCost.equations := by
  exact nodesAt_constraint_length n p

theorem nodesAt_multiplications {n : Nat} (base : Nat) (p : Formula n) :
    ((nodesAt base p).map Node.multiplications).sum = p.graphCost.multiplications := by
  induction p generalizing base <;>
    simp [nodesAt, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, Node.multiplications,
      zeroTestGateCost, booleanNotGateCost, booleanBinaryGateCost,
      BackendCost.combine, *] <;> omega

theorem emittedMultiplications_eq_graphCost {n : Nat} (p : Formula n) :
    emittedMultiplications p = p.graphCost.multiplications := by
  exact nodesAt_multiplications n p

def exprDegree : WindowExpr -> Nat
  | .loc _ | .nxt _ => 1
  | .const _ => 0
  | .add x y => max (exprDegree x) (exprDegree y)
  | .mul x y => exprDegree x + exprDegree y

theorem wire_expr_degree (w : Wire) : exprDegree w.expr ≤ 1 := by
  cases w <;> simp [Wire.expr, exprDegree]

theorem node_constraint_degree (node : Node) (c : VmConstraint2)
    (hc : c ∈ node.constraints) :
    exists body, c = gate body /\ exprDegree body ≤ 2 := by
  cases node with
  | zeroTest x out inv =>
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl | rfl
      · refine ⟨bitBody (.col out), rfl, ?_⟩
        simp [bitBody_eq, exprDegree, Wire.expr]
      · exact ⟨.mul (.loc x) (.loc out), rfl, by simp [exprDegree]⟩
      · exact ⟨.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)),
          rfl, by simp [exprDegree]⟩
  | not input out =>
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · refine ⟨bitBody (.col out), rfl, ?_⟩
        simp [bitBody_eq, exprDegree, Wire.expr]
      · refine ⟨.add (.add (.loc out) input.expr) (.const (-1)), rfl, ?_⟩
        have h := wire_expr_degree input
        simp [exprDegree]
        omega
  | and left right out =>
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · refine ⟨bitBody (.col out), rfl, ?_⟩
        simp [bitBody_eq, exprDegree, Wire.expr]
      · refine ⟨subW (.loc out) (.mul left.expr right.expr), rfl, ?_⟩
        have hl := wire_expr_degree left
        have hr := wire_expr_degree right
        simp [subW, negW, exprDegree]
        omega
  | or left right out =>
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · refine ⟨bitBody (.col out), rfl, ?_⟩
        simp [bitBody_eq, exprDegree, Wire.expr]
      · refine ⟨subW (.loc out)
          (subW (.add left.expr right.expr) (.mul left.expr right.expr)), rfl, ?_⟩
        have hl := wire_expr_degree left
        have hr := wire_expr_degree right
        simp [subW, negW, exprDegree]
        omega

theorem descriptor_constraint_degree {n : Nat} (p : Formula n) (c : VmConstraint2)
    (hc : c ∈ (descriptor p).constraints) :
    exists body, c = gate body /\ exprDegree body ≤ 2 := by
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · simp only [graphConstraints, List.mem_flatMap] at hc
    obtain ⟨node, hnode, hc⟩ := hc
    exact node_constraint_degree node c hc
  · refine ⟨subW (outputAt n p).expr (.const 1), rfl, ?_⟩
    have h := wire_expr_degree (outputAt n p)
    simp [subW, negW, exprDegree]
    omega

theorem descriptor_constraint_count {n : Nat} (p : Formula n) :
    (descriptor p).constraints.length = p.graphCost.equations + 1 := by
  simp [descriptor, graphConstraints_length_eq_graphCost_equations]

theorem descriptor_aux_width {n : Nat} (p : Formula n) :
    (descriptor p).traceWidth - n = p.graphCost.witnesses := by
  rw [descriptor, Nat.add_sub_cancel_left, witnessCount_eq_graphCost_witnesses]

/-! ## 4. Executable canonical one-row witness -/

def eval {n : Nat} (truth : Fin n -> Bool) : Formula n -> Bool
  | .atom a => truth a
  | .top => true
  | .bot => false
  | .not p => !(eval truth p)
  | .and p q => eval truth p && eval truth q
  | .or p q => eval truth p || eval truth q

theorem eval_eq_true_iff_holds {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    eval truth p = true <-> Formula.Holds (fun a => truth a = true) p := by
  induction p with
  | atom a => simp [eval, Formula.Holds]
  | top => simp [eval, Formula.Holds]
  | bot => simp [eval, Formula.Holds]
  | not p ih =>
      cases h : eval truth p <;>
        simp [eval, Formula.Holds, h] at ih ⊢ <;> assumption
  | and p q ihp ihq => simp [eval, Formula.Holds, ihp, ihq]
  | or p q ihp ihq => simp [eval, Formula.Holds, ihp, ihq]

def bitInt (b : Bool) : Int := if b then 1 else 0

/-- Postorder witness values in exactly the same order as `nodesAt` allocates
columns.  For an atom, the second value is a valid inverse for the canonical
residual `0`/`1`. -/
def witnessBits {n : Nat} (truth : Fin n -> Bool) : Formula n -> List Bool
  | .atom a => [truth a, !(truth a)]
  | .top | .bot => []
  | .not p => witnessBits truth p ++ [eval truth (.not p)]
  | .and p q => witnessBits truth p ++ witnessBits truth q ++ [eval truth (.and p q)]
  | .or p q => witnessBits truth p ++ witnessBits truth q ++ [eval truth (.or p q)]

@[simp] theorem witnessBits_length {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    (witnessBits truth p).length = witnessCount p := by
  induction p <;> simp [witnessBits, witnessCount, *] <;> omega

def residualInput {n : Nat} (truth : Fin n -> Bool) (a : Fin n) : Int :=
  if truth a then 0 else 1

def canonicalRow {n : Nat} (truth : Fin n -> Bool) (p : Formula n) : Assignment :=
  fun c => if h : c < n then residualInput truth ⟨c, h⟩
    else bitInt ((witnessBits truth p).getD (c - n) false)

def canonicalTrace {n : Nat} (truth : Fin n -> Bool) (p : Formula n) : VmTrace :=
  { rows := [canonicalRow truth p], pub := zeroAsg, tf := fun _ => [] }

def InputsMatch {n : Nat} (truth : Fin n -> Bool) (a : Assignment) : Prop :=
  forall x : Fin n, a x.val = residualInput truth x

def WitnessesMatch {n : Nat} (truth : Fin n -> Bool) (base : Nat)
    (p : Formula n) (a : Assignment) : Prop :=
  forall k, k < witnessCount p ->
    a (base + k) = bitInt ((witnessBits truth p).getD k false)

private theorem getD_append_lt {A : Type*} (xs ys : List A) (i : Nat) (d : A)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right {A : Type*} (xs ys : List A) (k : Nat) (d : A) :
    (xs ++ ys).getD (xs.length + k) d = ys.getD k d := by
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right xs.length k)]

theorem canonical_inputs_match {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    InputsMatch truth (canonicalRow truth p) := by
  intro x
  simp [canonicalRow, x.isLt]

theorem canonical_witnesses_match {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    WitnessesMatch truth n p (canonicalRow truth p) := by
  intro k hk
  simp [canonicalRow]

theorem witnesses_not_child {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.not p) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by simpa using hk)] at hp
  exact hp

theorem witnesses_and_left {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.and p q) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega), getD_append_lt _ _ _ _ (by simpa [witnessBits_length] using hk)] at hp
  exact hp

theorem witnesses_or_left {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.or p q) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega), getD_append_lt _ _ _ _ (by simpa [witnessBits_length] using hk)] at hp
  exact hp

theorem witnesses_and_right {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.and p q) a) :
    WitnessesMatch truth (base + witnessCount p) q a := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega)] at hp
  rw [show witnessCount p = (witnessBits truth p).length by simp,
    getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

theorem witnesses_or_right {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.or p q) a) :
    WitnessesMatch truth (base + witnessCount p) q a := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega)] at hp
  rw [show witnessCount p = (witnessBits truth p).length by simp,
    getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

/-- The output wire of a matched materialization contains exactly the Boolean
source value. -/
theorem output_eval_of_matches {n : Nat} (truth : Fin n -> Bool) (base : Nat)
    (p : Formula n) (a : Assignment) (h : WitnessesMatch truth base p a) :
    (outputAt base p).eval a = bitInt (eval truth p) := by
  cases p with
  | atom x =>
      have hx := h 0 (by simp [witnessCount])
      simpa [outputAt, witnessBits, eval] using hx
  | top => rfl
  | bot => rfl
  | not p =>
      have hx := h (witnessCount p) (by simp [witnessCount])
      rw [witnessBits, show witnessCount p = (witnessBits truth p).length by simp] at hx
      have hlast := getD_append_right (witnessBits truth p)
        [eval truth (.not p)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, Nat.add_assoc] using hx
  | and p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [witnessBits,
        show witnessCount p + witnessCount q =
          (witnessBits truth p ++ witnessBits truth q).length by simp] at hx
      have hlast := getD_append_right
        (witnessBits truth p ++ witnessBits truth q)
        [eval truth (.and p q)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, Nat.add_assoc] using hx
  | or p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [witnessBits,
        show witnessCount p + witnessCount q =
          (witnessBits truth p ++ witnessBits truth q).length by simp] at hx
      have hlast := getD_append_right
        (witnessBits truth p ++ witnessBits truth q)
        [eval truth (.or p q)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, Nat.add_assoc] using hx

namespace Node

def HoldsAt (env : VmRowEnv) (node : Node) : Prop :=
  forall c, c ∈ node.constraints ->
    c.holdsAt (fun _ => 0) (fun _ => []) env false true

end Node

theorem nodes_hold_of_matches {n : Nat} (truth : Fin n -> Bool) (base : Nat)
    (p : Formula n) (env : VmRowEnv)
    (hinputs : InputsMatch truth env.loc)
    (hwitness : WitnessesMatch truth base p env.loc) :
    forall node, node ∈ nodesAt base p -> Node.HoldsAt env node := by
  induction p generalizing base with
  | atom x =>
      intro node hnode
      simp only [nodesAt, List.mem_singleton] at hnode
      subst node
      have hx := hinputs x
      have hb := hwitness 0 (by simp [witnessCount])
      have hi := hwitness 1 (by simp [witnessCount])
      cases ht : truth x <;> simp [witnessBits, bitInt, ht] at hb hi <;>
        simp [residualInput, ht] at hx <;>
          simp [Node.HoldsAt, Node.constraints, gate, bitBody_eq,
            VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
          hx, hb, hi]
  | top => simp [nodesAt]
  | bot => simp [nodesAt]
  | not p ih =>
      intro node hnode
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with hchild | rfl
      · exact ih base (witnesses_not_child hwitness) node hchild
      · have hin := output_eval_of_matches truth base p env.loc
          (witnesses_not_child hwitness)
        have hout := output_eval_of_matches truth base (.not p) env.loc hwitness
        have hinE : (outputAt base p).expr.eval env = bitInt (eval truth p) := by
          rw [Wire.expr_eval]
          exact hin
        cases hv : eval truth p <;>
          simp [eval, bitInt, hv, outputAt] at hout <;>
          simp [bitInt, hv] at hinE <;>
          simp [Node.HoldsAt, Node.constraints, gate, bitBody_eq,
            VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
            hinE, hout]
  | and p q ihp ihq =>
      intro node hnode
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with (hp | hq) | rfl
      · exact ihp base (witnesses_and_left hwitness) node hp
      · exact ihq (base + witnessCount p) (witnesses_and_right hwitness) node hq
      · have hl := output_eval_of_matches truth base p env.loc
          (witnesses_and_left hwitness)
        have hr := output_eval_of_matches truth (base + witnessCount p) q env.loc
          (witnesses_and_right hwitness)
        have hout := output_eval_of_matches truth base (.and p q) env.loc hwitness
        have hlE : (outputAt base p).expr.eval env = bitInt (eval truth p) := by
          rw [Wire.expr_eval]; exact hl
        have hrE : (outputAt (base + witnessCount p) q).expr.eval env =
            bitInt (eval truth q) := by
          rw [Wire.expr_eval]; exact hr
        cases hpv : eval truth p <;> cases hqv : eval truth q <;>
          simp [eval, bitInt, hpv, hqv, outputAt, Nat.add_assoc] at hout <;>
          simp [bitInt, hpv] at hlE <;> simp [bitInt, hqv] at hrE <;>
          simp [Node.HoldsAt, Node.constraints, gate, bitBody_eq, subW, negW,
            VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
            Nat.add_assoc, hlE, hrE, hout]
  | or p q ihp ihq =>
      intro node hnode
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with (hp | hq) | rfl
      · exact ihp base (witnesses_or_left hwitness) node hp
      · exact ihq (base + witnessCount p) (witnesses_or_right hwitness) node hq
      · have hl := output_eval_of_matches truth base p env.loc
          (witnesses_or_left hwitness)
        have hr := output_eval_of_matches truth (base + witnessCount p) q env.loc
          (witnesses_or_right hwitness)
        have hout := output_eval_of_matches truth base (.or p q) env.loc hwitness
        have hlE : (outputAt base p).expr.eval env = bitInt (eval truth p) := by
          rw [Wire.expr_eval]; exact hl
        have hrE : (outputAt (base + witnessCount p) q).expr.eval env =
            bitInt (eval truth q) := by
          rw [Wire.expr_eval]; exact hr
        cases hpv : eval truth p <;> cases hqv : eval truth q <;>
          simp [eval, bitInt, hpv, hqv, outputAt, Nat.add_assoc] at hout <;>
          simp [bitInt, hpv] at hlE <;> simp [bitInt, hqv] at hrE <;>
          simp [Node.HoldsAt, Node.constraints, gate, bitBody_eq, subW, negW,
            VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
            Nat.add_assoc, hlE, hrE, hout]

/-! The semantic proof is completed below the fail-closed certificate because
its final theorem uses the exact reconstructed descriptor. -/

/-! ## 5. Fail-closed layout and byte certificate -/

def liveVersion : Nat := 1

structure Layout where
  inputs : Nat
  auxiliaries : Nat
  traceWidth : Nat
  graphEquations : Nat
  acceptingEquations : Nat
  multiplications : Nat
  deriving DecidableEq, Repr

def layoutOf {n : Nat} (p : Formula n) : Layout :=
  { inputs := n
  , auxiliaries := witnessCount p
  , traceWidth := n + witnessCount p
  , graphEquations := (graphConstraints p).length
  , acceptingEquations := (descriptor p).constraints.length
  , multiplications := emittedMultiplications p }

structure LiveCertificate (n : Nat) where
  version : Nat
  source : Formula n
  optimized : Formula n
  optimizer : Certificate n
  layout : Layout
  descriptorBytes : String
  deriving Repr

def checkLive {n : Nat} (c : LiveCertificate n) : Bool :=
  decide (c.version = liveVersion) &&
    c.optimizer.check &&
    decide (c.optimizer.source = c.source) &&
    decide (c.optimizer.target = c.optimized) &&
    decide (c.layout = layoutOf c.optimized) &&
    decide (c.descriptorBytes = emitVmJson2 (descriptor c.optimized))

def certify {n : Nat} (source : Formula n) : LiveCertificate n :=
  let result := optimize source
  { version := liveVersion
  , source := source
  , optimized := result.1
  , optimizer := result.2
  , layout := layoutOf result.1
  , descriptorBytes := emitVmJson2 (descriptor result.1) }

theorem checkLive_spec {n : Nat} (c : LiveCertificate n) :
    checkLive c = true <->
      c.version = liveVersion /\
      c.optimizer.check = true /\
      c.optimizer.source = c.source /\
      c.optimizer.target = c.optimized /\
      c.layout = layoutOf c.optimized /\
      c.descriptorBytes = emitVmJson2 (descriptor c.optimized) := by
  simp [checkLive, and_assoc]

theorem checkLive_certify {n : Nat} (source : Formula n) :
    checkLive (certify source) = true := by
  rw [checkLive_spec]
  simp [certify, optimize_checked, optimize_source, optimize_target]

/-! ## 6. The actual 30 -> 13 specimen, with the accepting correction -/

abbrev factorBefore : Formula 4 := factorSpecimen
abbrev factorAfter : Formula 4 := (optimize factorSpecimen).1

theorem factor_emitted_exact :
    (graphConstraints factorBefore).length = 30 /\
    (graphConstraints factorAfter).length = 13 /\
    (descriptor factorBefore).constraints.length = 31 /\
    (descriptor factorAfter).constraints.length = 14 /\
    emittedMultiplications factorBefore = 26 /\
    emittedMultiplications factorAfter = 13 /\
    (descriptor factorBefore).traceWidth - 4 = 17 /\
    (descriptor factorAfter).traceWidth - 4 = 8 := by
  decide

def factorCertificate : LiveCertificate 4 := certify factorSpecimen

def tamperedLayoutCertificate : LiveCertificate 4 :=
  { factorCertificate with
    layout := { factorCertificate.layout with acceptingEquations := 13 } }

def tamperedBytesCertificate : LiveCertificate 4 :=
  { factorCertificate with descriptorBytes := factorCertificate.descriptorBytes ++ " " }

def tamperedEndpointCertificate : LiveCertificate 4 :=
  { factorCertificate with optimized := atom3 }

#guard checkLive factorCertificate
#guard !checkLive tamperedLayoutCertificate
#guard !checkLive tamperedBytesCertificate
#guard !checkLive tamperedEndpointCertificate

/-! ## 7. Exact source semantics of the live canonical trace -/

theorem canonical_env_loc {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    (envAt (canonicalTrace truth p) 0).loc = canonicalRow truth p := by
  simp [canonicalTrace, envAt]

theorem canonical_nodes_hold {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    forall node, node ∈ nodesAt n p ->
      Node.HoldsAt (envAt (canonicalTrace truth p) 0) node := by
  apply nodes_hold_of_matches truth n p
  · rw [canonical_env_loc]
    exact canonical_inputs_match truth p
  · rw [canonical_env_loc]
    exact canonical_witnesses_match truth p

theorem canonical_graph_constraints_hold {n : Nat} (truth : Fin n -> Bool)
    (p : Formula n) : forall c, c ∈ graphConstraints p ->
      c.holdsAt (fun _ => 0) (fun _ => [])
        (envAt (canonicalTrace truth p) 0) true true := by
  intro c hc
  simp only [graphConstraints, List.mem_flatMap] at hc
  obtain ⟨node, hnode, hc⟩ := hc
  have hn := canonical_nodes_hold truth p node hnode c hc
  obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
  simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
    WindowConstraint.holdsAt] using hn

theorem canonical_output {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    (outputAt n p).expr.eval (envAt (canonicalTrace truth p) 0) =
      bitInt (eval truth p) := by
  rw [Wire.expr_eval, canonical_env_loc]
  exact output_eval_of_matches truth n p (canonicalRow truth p)
    (canonical_witnesses_match truth p)

theorem canonical_accept_iff {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    (acceptConstraint p).holdsAt (fun _ => 0) (fun _ => [])
        (envAt (canonicalTrace truth p) 0) true true
      <-> eval truth p = true := by
  have hout := canonical_output truth p
  have houtW : (outputAt n p).eval (envAt (canonicalTrace truth p) 0).loc =
      bitInt (eval truth p) := by
    simpa only [Wire.expr_eval] using hout
  constructor
  · intro hacc
    simp [acceptConstraint, gate, subW, negW, VmConstraint2.holdsAt,
      WindowConstraint.holdsAt, WindowExpr.eval] at hacc
    cases h : eval truth p
    · rw [houtW] at hacc
      simp [h, bitInt] at hacc
      rw [Int.modEq_zero_iff_dvd] at hacc
      norm_num at hacc
    · rfl
  · intro heval
    simp [acceptConstraint, gate, subW, negW, VmConstraint2.holdsAt,
      WindowConstraint.holdsAt, WindowExpr.eval]
    rw [houtW]
    simp [heval, bitInt]

private theorem node_memFilter_nil (node : Node) :
    node.constraints.filterMap (fun c => match c with
      | .memOp m => some m
      | _ => none) = [] := by
  cases node <;> rfl

private theorem node_mapFilter_nil (node : Node) :
    node.constraints.filterMap (fun c => match c with
      | .mapOp m => some m
      | _ => none) = [] := by
  cases node <;> rfl

private theorem nodes_memFilter_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap (fun c => match c with
      | .memOp m => some m
      | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      simp [node_memFilter_nil, ih]

private theorem nodes_mapFilter_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap (fun c => match c with
      | .mapOp m => some m
      | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      simp [node_mapFilter_nil, ih]

theorem memOps_descriptor_nil {n : Nat} (p : Formula n) :
    memOpsOf (descriptor p) = [] := by
  change ((graphConstraints p ++ [acceptConstraint p]).filterMap
    (fun c => match c with | .memOp m => some m | _ => none)) = []
  rw [List.filterMap_append]
  have hg := nodes_memFilter_nil (nodesAt n p)
  change (graphConstraints p).filterMap
    (fun c => match c with | .memOp m => some m | _ => none) = [] at hg
  rw [hg]
  rfl

theorem mapOps_descriptor_nil {n : Nat} (p : Formula n) :
    mapOpsOf (descriptor p) = [] := by
  change ((graphConstraints p ++ [acceptConstraint p]).filterMap
    (fun c => match c with | .mapOp m => some m | _ => none)) = []
  rw [List.filterMap_append]
  have hg := nodes_mapFilter_nil (nodesAt n p)
  change (graphConstraints p).filterMap
    (fun c => match c with | .mapOp m => some m | _ => none) = [] at hg
  rw [hg]
  rfl

theorem memLog_descriptor_nil {n : Nat} (p : Formula n) (t : VmTrace) :
    memLog (descriptor p) t = [] := by
  simp [memLog, memOps_descriptor_nil]

theorem mapLog_descriptor_nil {n : Nat} (p : Formula n) (t : VmTrace) :
    mapLog (descriptor p) t = [] := by
  simp [mapLog, mapOps_descriptor_nil]

set_option maxHeartbeats 2000000 in
/-- Exact correctness against the live `Satisfied2` denotation on the
compiler's executable one-row witness.  This is not a shadow constraint
relation: the descriptor, its JSON bytes, and this theorem share the same
`EffectVmDescriptor2` value. -/
theorem canonical_trace_satisfied_iff (hash : List Int -> Int) {n : Nat}
    (truth : Fin n -> Bool) (p : Formula n) :
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace truth p)
      <-> Formula.Holds (fun a => truth a = true) p := by
  rw [← eval_eq_true_iff_holds]
  constructor
  · intro hsat
    have haccept := hsat.rowConstraints 0 (by simp [canonicalTrace])
      (acceptConstraint p) (by simp [descriptor])
    exact canonical_accept_iff truth p |>.mp (by
      simpa [VmConstraint2.holdsAt, acceptConstraint, gate, WindowConstraint.holdsAt] using haccept)
  · intro heval
    refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi c hc
      have hi0 : i = 0 := by simp [canonicalTrace] at hi; omega
      subst i
      simp only [descriptor, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · have hzero := canonical_graph_constraints_hold truth p c hc
        simp only [graphConstraints, List.mem_flatMap] at hc
        obtain ⟨node, _, hcnode⟩ := hc
        obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcnode
        simpa [gate, VmConstraint2.holdsAt, WindowConstraint.holdsAt] using hzero
      · exact (canonical_accept_iff truth p).mpr heval
    · intro i hi
      trivial
    · intro i hi r hr
      simp [descriptor] at hr
    · intro op hop
      rw [memLog_descriptor_nil p] at hop
      cases hop
    · rw [memLog_descriptor_nil p]
      trivial
    · rw [memLog_descriptor_nil p]
      exact memCheck_nil _ _
    · rw [memLog_descriptor_nil p]
      rfl
    · rw [mapLog_descriptor_nil p]
      rfl

/-- An accepted optimizer/live certificate transports the live optimized
descriptor all the way back to the certificate's unoptimized source.  Both
endpoints, the layout ledger, and the exact JSON string have been reconstructed
by `checkLive` before this theorem is available. -/
theorem checked_source_canonical_iff (hash : List Int -> Int) {n : Nat}
    (truth : Fin n -> Bool) (c : LiveCertificate n)
    (hcheck : checkLive c = true) :
    Satisfied2 hash (descriptor c.optimized) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace truth c.optimized)
      <-> Formula.Holds (fun a => truth a = true) c.source := by
  have hs := (checkLive_spec c).mp hcheck
  rw [canonical_trace_satisfied_iff]
  have hsem := c.optimizer.check_sound (fun a => truth a = true) hs.2.1
  rw [hs.2.2.1, hs.2.2.2.1] at hsem
  exact hsem.symm

/-! ## 8. Standalone public-statement variant

The internal descriptor above is useful as a subrelation whose residual
columns are supplied by a surrounding circuit.  It is not by itself a
standalone statement: those columns are witness-authored.  The public variant
below binds residual column `a` to public input `a` on the first row. -/

def publicPins (n : Nat) : List VmConstraint2 :=
  (List.range n).map fun a => .base (.piBinding .first a a)

def publicDescriptor {n : Nat} (p : Formula n) : EffectVmDescriptor2 :=
  { name := "dregg-public-materialized-boolgraph-v2-" ++ toString n
  , traceWidth := n + witnessCount p
  , piCount := n
  , tables := [mainTableDef (n + witnessCount p)]
  , constraints := publicPins n ++ graphConstraints p ++ [acceptConstraint p]
  , hashSites := []
  , ranges := [] }

theorem public_pin_mem {n : Nat} (p : Formula n) (a : Fin n) :
    .base (.piBinding .first a.val a.val) ∈ (publicDescriptor p).constraints := by
  simp [publicDescriptor, publicPins, a.isLt]

/-- Statement binding adds exactly `n` linear constraints and `n` public
inputs.  It adds no nonlinear multiplication and no auxiliary witness. -/
theorem public_descriptor_exact_overhead {n : Nat} (p : Formula n) :
    (publicDescriptor p).piCount = n /\
    (publicDescriptor p).traceWidth = (descriptor p).traceWidth /\
    (publicDescriptor p).constraints.length = n + p.graphCost.equations + 1 /\
    emittedMultiplications p = p.graphCost.multiplications /\
    (publicDescriptor p).traceWidth - n = p.graphCost.witnesses := by
  simp [publicDescriptor, descriptor, publicPins,
    graphConstraints_length_eq_graphCost_equations,
    emittedMultiplications_eq_graphCost, witnessCount_eq_graphCost_witnesses]
  omega

abbrev BabyBear : Type := ZMod 2013265921

noncomputable def fieldAssignment (a : Assignment) (c : Nat) : BabyBear :=
  (a c : BabyBear)

noncomputable def fieldWire (a : Assignment) : Wire -> BabyBear
  | .zero => 0
  | .one => 1
  | .col c => fieldAssignment a c

noncomputable def fieldWindow (env : VmRowEnv) : WindowExpr -> BabyBear
  | .loc c => fieldAssignment env.loc c
  | .nxt c => fieldAssignment env.nxt c
  | .const k => (k : BabyBear)
  | .add x y => fieldWindow env x + fieldWindow env y
  | .mul x y => fieldWindow env x * fieldWindow env y

theorem fieldWindow_eq_cast (env : VmRowEnv) (e : WindowExpr) :
    fieldWindow env e = (e.eval env : BabyBear) := by
  induction e <;> simp [fieldWindow, WindowExpr.eval, fieldAssignment, *]

theorem fieldWire_expr (env : VmRowEnv) (w : Wire) :
    fieldWindow env w.expr = fieldWire env.loc w := by
  cases w <;> rfl

theorem field_zero_of_gate {env : VmRowEnv} {body : WindowExpr}
    (h : (gate body).holdsAt (fun _ => 0) (fun _ => []) env false true) :
    fieldWindow env body = 0 := by
  simp only [gate, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    Bool.false_eq_true, if_false] at h
  rw [fieldWindow_eq_cast]
  exact (ZMod.intCast_eq_intCast_iff (body.eval env) 0 2013265921).2 h

theorem zeroTest_of_constraints (env : VmRowEnv) (x out inv : Nat)
    (h : Node.HoldsAt env (.zeroTest x out inv)) :
    Dregg2.Logic.BoolGraph.ZeroGate
      (fieldAssignment env.loc x) (fieldAssignment env.loc out)
      (fieldAssignment env.loc inv) := by
  have hbit := field_zero_of_gate
    (h (gate (bitBody (.col out))) (by simp [Node.constraints]))
  have hzero := field_zero_of_gate
    (h (gate (.mul (.loc x) (.loc out))) (by simp [Node.constraints]))
  have hinv := field_zero_of_gate
    (h (gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))))
      (by simp [Node.constraints]))
  simp only [bitBody_eq, fieldWindow, Wire.expr] at hbit
  simp only [fieldWindow] at hzero hinv
  have hb : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc out) := by
    simpa [Dregg2.Logic.BoolGraph.IsBit, sub_eq_add_neg] using hbit
  have hz : fieldAssignment env.loc x * fieldAssignment env.loc out = 0 := hzero
  have hi : fieldAssignment env.loc x * fieldAssignment env.loc inv =
      1 - fieldAssignment env.loc out := by
    linear_combination hinv
  exact ⟨hb, hz, hi⟩

theorem not_of_constraints (env : VmRowEnv) (input : Wire) (out : Nat)
    (h : Node.HoldsAt env (.not input out)) :
    Dregg2.Logic.BoolGraph.NotGate
      (fieldWire env.loc input) (fieldAssignment env.loc out) := by
  have hbit := field_zero_of_gate
    (h (gate (bitBody (.col out))) (by simp [Node.constraints]))
  have heq := field_zero_of_gate
    (h (gate (.add (.add (.loc out) input.expr) (.const (-1))))
      (by simp [Node.constraints]))
  simp only [bitBody_eq, fieldWindow, Wire.expr] at hbit
  have hout : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc out) := by
    simpa [Dregg2.Logic.BoolGraph.IsBit, sub_eq_add_neg] using hbit
  have heq' : fieldAssignment env.loc out = 1 - fieldWire env.loc input := by
    simp only [fieldWindow] at heq
    rw [fieldWire_expr] at heq
    linear_combination heq
  have hin : Dregg2.Logic.BoolGraph.IsBit (fieldWire env.loc input) := by
    rw [Dregg2.Logic.BoolGraph.isBit_iff]
    rcases Dregg2.Logic.BoolGraph.bit_zero_or_one hout with hout0 | hout1
    · right
      rw [hout0] at heq'
      linear_combination heq'
    · left
      rw [hout1] at heq'
      linear_combination heq'
  exact ⟨hin, hout, heq'⟩

theorem and_of_constraints (env : VmRowEnv) (left right : Wire) (out : Nat)
    (h : Node.HoldsAt env (.and left right out))
    (hl : Dregg2.Logic.BoolGraph.IsBit (fieldWire env.loc left))
    (hr : Dregg2.Logic.BoolGraph.IsBit (fieldWire env.loc right)) :
    Dregg2.Logic.BoolGraph.AndGate (fieldWire env.loc left)
      (fieldWire env.loc right) (fieldAssignment env.loc out) := by
  have hbit := field_zero_of_gate
    (h (gate (bitBody (.col out))) (by simp [Node.constraints]))
  have heq := field_zero_of_gate
    (h (gate (subW (.loc out) (.mul left.expr right.expr)))
      (by simp [Node.constraints]))
  simp only [bitBody_eq, fieldWindow, Wire.expr] at hbit
  have hout : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc out) := by
    simpa [Dregg2.Logic.BoolGraph.IsBit, sub_eq_add_neg] using hbit
  have heq' : fieldAssignment env.loc out =
      fieldWire env.loc left * fieldWire env.loc right := by
    simp only [subW, negW, fieldWindow] at heq
    rw [fieldWire_expr, fieldWire_expr] at heq
    linear_combination heq
  exact ⟨hl, hr, hout, heq'⟩

theorem or_of_constraints (env : VmRowEnv) (left right : Wire) (out : Nat)
    (h : Node.HoldsAt env (.or left right out))
    (hl : Dregg2.Logic.BoolGraph.IsBit (fieldWire env.loc left))
    (hr : Dregg2.Logic.BoolGraph.IsBit (fieldWire env.loc right)) :
    Dregg2.Logic.BoolGraph.OrGate (fieldWire env.loc left)
      (fieldWire env.loc right) (fieldAssignment env.loc out) := by
  have hbit := field_zero_of_gate
    (h (gate (bitBody (.col out))) (by simp [Node.constraints]))
  have heq := field_zero_of_gate
    (h (gate (subW (.loc out)
      (subW (.add left.expr right.expr) (.mul left.expr right.expr))))
      (by simp [Node.constraints]))
  simp only [bitBody_eq, fieldWindow, Wire.expr] at hbit
  have hout : Dregg2.Logic.BoolGraph.IsBit (fieldAssignment env.loc out) := by
    simpa [Dregg2.Logic.BoolGraph.IsBit, sub_eq_add_neg] using hbit
  have heq' : fieldAssignment env.loc out = fieldWire env.loc left +
      fieldWire env.loc right - fieldWire env.loc left * fieldWire env.loc right := by
    simp only [subW, negW, fieldWindow] at heq
    rw [fieldWire_expr, fieldWire_expr] at heq
    linear_combination heq
  exact ⟨hl, hr, hout, heq'⟩

theorem graph_of_node_constraints {n : Nat} (env : VmRowEnv) (base : Nat)
    (p : Formula n)
    (hnodes : forall node, node ∈ nodesAt base p -> Node.HoldsAt env node) :
    Dregg2.Logic.BoolGraph.Graph
      (fun a : Fin n => fieldAssignment env.loc a.val) p.toGraph
      (fieldWire env.loc (outputAt base p)) := by
  induction p generalizing base with
  | atom a =>
      apply Dregg2.Logic.BoolGraph.Graph.atom a
      exact zeroTest_of_constraints env a.val base (base + 1)
        (hnodes _ (by simp [nodesAt]))
  | top => exact Dregg2.Logic.BoolGraph.Graph.top
  | bot => exact Dregg2.Logic.BoolGraph.Graph.bot
  | not p ih =>
      have hp : forall node, node ∈ nodesAt base p -> Node.HoldsAt env node := by
        intro node hnode
        exact hnodes node (by simp [nodesAt, hnode])
      have hgraph := ih base hp
      have hroot : Node.HoldsAt env
          (.not (outputAt base p) (base + witnessCount p)) :=
        hnodes _ (by simp [nodesAt])
      exact Dregg2.Logic.BoolGraph.Graph.not hgraph
        (not_of_constraints env _ _ hroot)
  | and p q ihp ihq =>
      have hp : forall node, node ∈ nodesAt base p -> Node.HoldsAt env node := by
        intro node hnode
        exact hnodes node (by simp [nodesAt, hnode])
      have hq : forall node, node ∈ nodesAt (base + witnessCount p) q ->
          Node.HoldsAt env node := by
        intro node hnode
        exact hnodes node (by simp [nodesAt, hnode])
      have hgp := ihp base hp
      have hgq := ihq (base + witnessCount p) hq
      have hroot : Node.HoldsAt env (.and (outputAt base p)
          (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)) :=
        hnodes _ (by simp [nodesAt])
      exact Dregg2.Logic.BoolGraph.Graph.and hgp hgq
        (and_of_constraints env _ _ _ hroot
          (Dregg2.Logic.BoolGraph.graph_sound hgp).1
          (Dregg2.Logic.BoolGraph.graph_sound hgq).1)
  | or p q ihp ihq =>
      have hp : forall node, node ∈ nodesAt base p -> Node.HoldsAt env node := by
        intro node hnode
        exact hnodes node (by simp [nodesAt, hnode])
      have hq : forall node, node ∈ nodesAt (base + witnessCount p) q ->
          Node.HoldsAt env node := by
        intro node hnode
        exact hnodes node (by simp [nodesAt, hnode])
      have hgp := ihp base hp
      have hgq := ihq (base + witnessCount p) hq
      have hroot : Node.HoldsAt env (.or (outputAt base p)
          (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)) :=
        hnodes _ (by simp [nodesAt])
      exact Dregg2.Logic.BoolGraph.Graph.or hgp hgq
        (or_of_constraints env _ _ _ hroot
          (Dregg2.Logic.BoolGraph.graph_sound hgp).1
          (Dregg2.Logic.BoolGraph.graph_sound hgq).1)

def PublicTruth {n : Nat} (pub : Assignment) (a : Fin n) : Prop :=
  fieldAssignment pub a.val = 0

theorem formula_holds_congr {n : Nat} (left right : Fin n -> Prop)
    (h : forall a, left a <-> right a) (p : Formula n) :
    Formula.Holds left p <-> Formula.Holds right p := by
  induction p <;> simp [Formula.Holds, *]

theorem public_pin_field {hash : List Int -> Int} {n : Nat} {p : Formula n}
    {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor p) (fun _ => 0)
      (fun _ => (0, 0)) [] t) (a : Fin n) :
    fieldAssignment (envAt t 0).loc a.val = fieldAssignment t.pub a.val := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hpin := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first a.val a.val)) (public_pin_mem p a)
  have hmod : (envAt t 0).loc a.val ≡ t.pub a.val [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, envAt] using hpin
  exact (ZMod.intCast_eq_intCast_iff _ _ 2013265921).2 hmod

theorem public_nodes_hold {hash : List Int -> Int} {n : Nat} {p : Formula n}
    {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor p) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    forall node, node ∈ nodesAt n p -> Node.HoldsAt (envAt t 0) node := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  intro node hnode c hc
  have hmem : c ∈ (publicDescriptor p).constraints := by
    simp only [publicDescriptor, List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨node, hnode, hc⟩))
  have hgate := hsat.rowConstraints 0 hpos c hmem
  obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
  simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
    WindowConstraint.holdsAt] using hgate

theorem public_accepts_output_one {hash : List Int -> Int} {n : Nat}
    {p : Formula n} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor p) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    fieldWire (envAt t 0).loc (outputAt n p) = 1 := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hmem : acceptConstraint p ∈ (publicDescriptor p).constraints := by
    simp [publicDescriptor]
  have hgate := hsat.rowConstraints 0 hpos (acceptConstraint p) hmem
  have hz := field_zero_of_gate (env := envAt t 0) (body :=
    subW (outputAt n p).expr (.const 1)) (by
      simpa [acceptConstraint, VmConstraint2.holdsAt, gate, WindowConstraint.holdsAt] using hgate)
  simp [subW, negW, fieldWindow] at hz
  rw [fieldWire_expr] at hz
  linear_combination hz

/-- Arbitrary nonempty satisfying-trace soundness.  Atom truth is derived from
the verifier's public residual vector, not from hidden witness columns. -/
theorem public_statement_sound (hash : List Int -> Int) {n : Nat}
    (p : Formula n) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor p) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    Formula.Holds (PublicTruth t.pub) p := by
  have hgraph := graph_of_node_constraints (envAt t 0) n p
    (public_nodes_hold hne hsat)
  have hout := public_accepts_output_one hne hsat
  have heval : Dregg2.Logic.BoolGraph.Eval
      (fun a : Fin n => fieldAssignment (envAt t 0).loc a.val) p.toGraph :=
    (Dregg2.Logic.BoolGraph.graph_sound hgraph).2.mp hout
  have hrow : Formula.Holds
      (fun a : Fin n => fieldAssignment (envAt t 0).loc a.val = 0) p :=
    (Formula.graphEval_iff_holds
      (F := BabyBear) (fun a : Fin n => fieldAssignment (envAt t 0).loc a.val) p).mp heval
  apply (formula_holds_congr _ _ (fun a => ?_) p).mp hrow
  rw [public_pin_field hne hsat a]
  rfl

def canonicalPublic {n : Nat} (truth : Fin n -> Bool) : Assignment :=
  fun c => if h : c < n then residualInput truth ⟨c, h⟩ else 0

def publicCanonicalTrace {n : Nat} (truth : Fin n -> Bool)
    (p : Formula n) : VmTrace :=
  { rows := [canonicalRow truth p]
  , pub := canonicalPublic truth
  , tf := fun _ => [] }

@[simp] theorem publicCanonicalTrace_loc {n : Nat} (truth : Fin n -> Bool)
    (p : Formula n) :
    (envAt (publicCanonicalTrace truth p) 0).loc = canonicalRow truth p := by
  simp [publicCanonicalTrace, envAt]

@[simp] theorem publicCanonicalTrace_pub {n : Nat} (truth : Fin n -> Bool)
    (p : Formula n) : (publicCanonicalTrace truth p).pub = canonicalPublic truth := rfl

theorem publicTruth_canonical_iff {n : Nat} (truth : Fin n -> Bool) (a : Fin n) :
    PublicTruth (canonicalPublic truth) a <-> truth a = true := by
  cases h : truth a <;>
    simp [PublicTruth, fieldAssignment, canonicalPublic, residualInput, a.isLt, h]

private theorem publicPins_memFilter_nil (n : Nat) :
    (publicPins n).filterMap (fun c => match c with
      | .memOp m => some m
      | _ => none) = [] := by
  simp [publicPins]

private theorem publicPins_mapFilter_nil (n : Nat) :
    (publicPins n).filterMap (fun c => match c with
      | .mapOp m => some m
      | _ => none) = [] := by
  simp [publicPins]

theorem memOps_publicDescriptor_nil {n : Nat} (p : Formula n) :
    memOpsOf (publicDescriptor p) = [] := by
  change ((publicPins n ++ graphConstraints p ++ [acceptConstraint p]).filterMap
    (fun c => match c with | .memOp m => some m | _ => none)) = []
  simp only [List.filterMap_append]
  have hp := publicPins_memFilter_nil n
  have hg := nodes_memFilter_nil (nodesAt n p)
  change (graphConstraints p).filterMap
    (fun c => match c with | .memOp m => some m | _ => none) = [] at hg
  rw [hp, hg]
  rfl

theorem mapOps_publicDescriptor_nil {n : Nat} (p : Formula n) :
    mapOpsOf (publicDescriptor p) = [] := by
  change ((publicPins n ++ graphConstraints p ++ [acceptConstraint p]).filterMap
    (fun c => match c with | .mapOp m => some m | _ => none)) = []
  simp only [List.filterMap_append]
  have hp := publicPins_mapFilter_nil n
  have hg := nodes_mapFilter_nil (nodesAt n p)
  change (graphConstraints p).filterMap
    (fun c => match c with | .mapOp m => some m | _ => none) = [] at hg
  rw [hp, hg]
  rfl

theorem memLog_publicDescriptor_nil {n : Nat} (p : Formula n) (t : VmTrace) :
    memLog (publicDescriptor p) t = [] := by
  simp [memLog, memOps_publicDescriptor_nil]

theorem mapLog_publicDescriptor_nil {n : Nat} (p : Formula n) (t : VmTrace) :
    mapLog (publicDescriptor p) t = [] := by
  simp [mapLog, mapOps_publicDescriptor_nil]

theorem public_canonical_nodes_hold {n : Nat} (truth : Fin n -> Bool)
    (p : Formula n) : forall node, node ∈ nodesAt n p ->
      Node.HoldsAt (envAt (publicCanonicalTrace truth p) 0) node := by
  apply nodes_hold_of_matches truth n p
  · rw [publicCanonicalTrace_loc]
    exact canonical_inputs_match truth p
  · rw [publicCanonicalTrace_loc]
    exact canonical_witnesses_match truth p

set_option maxHeartbeats 2000000 in
theorem public_canonical_trace_complete (hash : List Int -> Int) {n : Nat}
    (truth : Fin n -> Bool) (p : Formula n)
    (htrue : Formula.Holds (fun a => truth a = true) p) :
    Satisfied2 hash (publicDescriptor p) (fun _ => 0) (fun _ => (0, 0)) []
      (publicCanonicalTrace truth p) := by
  have heval := (eval_eq_true_iff_holds truth p).2 htrue
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [publicCanonicalTrace] at hi; omega
    subst i
    simp only [publicDescriptor, List.mem_append, List.mem_singleton] at hc
    rcases hc with (hpin | hgraph) | rfl
    · simp only [publicPins, List.mem_map] at hpin
      obtain ⟨a, ha, rfl⟩ := hpin
      have halt : a < n := List.mem_range.mp ha
      simp [VmConstraint2.holdsAt, publicCanonicalTrace, envAt, canonicalRow,
        canonicalPublic, halt]
    · simp only [graphConstraints, List.mem_flatMap] at hgraph
      obtain ⟨node, hnode, hcnode⟩ := hgraph
      have hgate := public_canonical_nodes_hold truth p node hnode c hcnode
      obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcnode
      simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
        WindowConstraint.holdsAt] using hgate
    · have hout : (outputAt n p).expr.eval
          (envAt (publicCanonicalTrace truth p) 0) = 1 := by
        rw [Wire.expr_eval, publicCanonicalTrace_loc]
        have hv := output_eval_of_matches truth n p (canonicalRow truth p)
          (canonical_witnesses_match truth p)
        simpa [heval, bitInt] using hv
      simp [acceptConstraint, gate, subW, negW, VmConstraint2.holdsAt,
        WindowConstraint.holdsAt, WindowExpr.eval, hout]
  · intro i hi
    trivial
  · intro i hi r hr
    simp [publicDescriptor] at hr
  · intro op hop
    rw [memLog_publicDescriptor_nil p] at hop
    cases hop
  · rw [memLog_publicDescriptor_nil p]
    trivial
  · rw [memLog_publicDescriptor_nil p]
    exact memCheck_nil _ _
  · rw [memLog_publicDescriptor_nil p]
    rfl
  · rw [mapLog_publicDescriptor_nil p]
    rfl

/-- Constructive exactness on the canonical public trace.  The forward
direction is an instance of arbitrary-trace statement soundness. -/
theorem public_canonical_trace_iff (hash : List Int -> Int) {n : Nat}
    (truth : Fin n -> Bool) (p : Formula n) :
    Satisfied2 hash (publicDescriptor p) (fun _ => 0) (fun _ => (0, 0)) []
        (publicCanonicalTrace truth p)
      <-> Formula.Holds (fun a => truth a = true) p := by
  constructor
  · intro hsat
    have hpub := public_statement_sound hash p (publicCanonicalTrace truth p)
      (by simp [publicCanonicalTrace]) hsat
    exact (formula_holds_congr _ _
      (fun a => publicTruth_canonical_iff truth a) p).mp hpub
  · exact public_canonical_trace_complete hash truth p

/-! ## 9. Public layout and exact-byte certificate -/

def publicPiLayout (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun a => (a, a)

structure PublicLayout where
  piLayout : List (Nat × Nat)
  piCount : Nat
  traceWidth : Nat
  bindingEquations : Nat
  graphEquations : Nat
  acceptingEquations : Nat
  multiplications : Nat
  auxiliaries : Nat
  deriving DecidableEq, Repr

def publicLayoutOf {n : Nat} (p : Formula n) : PublicLayout :=
  { piLayout := publicPiLayout n
  , piCount := n
  , traceWidth := n + witnessCount p
  , bindingEquations := n
  , graphEquations := (graphConstraints p).length
  , acceptingEquations := (publicDescriptor p).constraints.length
  , multiplications := emittedMultiplications p
  , auxiliaries := witnessCount p }

def publicLiveVersion : Nat := 1

structure PublicLiveCertificate (n : Nat) where
  version : Nat
  source : Formula n
  optimized : Formula n
  optimizer : Certificate n
  layout : PublicLayout
  descriptorBytes : String
  deriving Repr

def checkPublicLive {n : Nat} (c : PublicLiveCertificate n) : Bool :=
  decide (c.version = publicLiveVersion) &&
    c.optimizer.check &&
    decide (c.optimizer.source = c.source) &&
    decide (c.optimizer.target = c.optimized) &&
    decide (c.layout = publicLayoutOf c.optimized) &&
    decide (c.descriptorBytes = emitVmJson2 (publicDescriptor c.optimized))

def certifyPublic {n : Nat} (source : Formula n) : PublicLiveCertificate n :=
  let result := optimize source
  { version := publicLiveVersion
  , source := source
  , optimized := result.1
  , optimizer := result.2
  , layout := publicLayoutOf result.1
  , descriptorBytes := emitVmJson2 (publicDescriptor result.1) }

theorem checkPublicLive_spec {n : Nat} (c : PublicLiveCertificate n) :
    checkPublicLive c = true <->
      c.version = publicLiveVersion /\
      c.optimizer.check = true /\
      c.optimizer.source = c.source /\
      c.optimizer.target = c.optimized /\
      c.layout = publicLayoutOf c.optimized /\
      c.descriptorBytes = emitVmJson2 (publicDescriptor c.optimized) := by
  simp [checkPublicLive, and_assoc]

theorem checkPublicLive_certify {n : Nat} (source : Formula n) :
    checkPublicLive (certifyPublic source) = true := by
  rw [checkPublicLive_spec]
  simp [certifyPublic, optimize_checked, optimize_source, optimize_target]

/-- An accepted public certificate plus any nonempty satisfying trace proves
the original, pre-optimization public statement. -/
theorem checked_public_statement_sound (hash : List Int -> Int) {n : Nat}
    (c : PublicLiveCertificate n) (hcheck : checkPublicLive c = true)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor c.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    Formula.Holds (PublicTruth t.pub) c.source := by
  have hs := (checkPublicLive_spec c).mp hcheck
  have hopt := public_statement_sound hash c.optimized t hne hsat
  have hsem := c.optimizer.check_sound (PublicTruth t.pub) hs.2.1
  rw [hs.2.2.1, hs.2.2.2.1] at hsem
  exact hsem.mpr hopt

theorem public_factor_emitted_exact :
    (publicDescriptor factorBefore).constraints.length = 35 /\
    (publicDescriptor factorAfter).constraints.length = 18 /\
    (publicDescriptor factorAfter).piCount = 4 /\
    emittedMultiplications factorBefore = 26 /\
    emittedMultiplications factorAfter = 13 /\
    (publicDescriptor factorBefore).traceWidth - 4 = 17 /\
    (publicDescriptor factorAfter).traceWidth - 4 = 8 := by
  decide

def factorPublicCertificate : PublicLiveCertificate 4 := certifyPublic factorSpecimen

/-- Stable carrier consumed by cross-language tests.  The certificate checker
reconstructs this exact string from the optimized source. -/
def factorPublicDescriptorJson : String := factorPublicCertificate.descriptorBytes

/-- Independently written exact wire image for cross-language consumers.  This
literal catches changes to the descriptor name, IR version, PI ordering,
column allocation, gate ordering, expression trees, or empty carrier lists. -/
def factorPublicDescriptorJsonLiteral : String :=
  "{\"name\":\"dregg-public-materialized-boolgraph-v2-4\",\"ir\":2,\"trace_width\":12,\"public_input_count\":4,\"challenges\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":12,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"loc\",\"c\":4}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"loc\",\"c\":5}},\"r\":{\"t\":\"loc\",\"c\":4}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"loc\",\"c\":6}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"loc\",\"c\":7}},\"r\":{\"t\":\"loc\",\"c\":6}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"loc\",\"c\":8}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"loc\",\"c\":9}},\"r\":{\"t\":\"loc\",\"c\":8}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"loc\",\"c\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"loc\",\"c\":8}}}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"loc\",\"c\":10}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard factorPublicDescriptorJson == factorPublicDescriptorJsonLiteral

def tamperedPiCertificate : PublicLiveCertificate 4 :=
  { factorPublicCertificate with
    layout := { factorPublicCertificate.layout with piLayout := [(0, 1)] } }

def tamperedPublicLayoutCertificate : PublicLiveCertificate 4 :=
  { factorPublicCertificate with
    layout := { factorPublicCertificate.layout with bindingEquations := 3 } }

def tamperedPublicBytesCertificate : PublicLiveCertificate 4 :=
  { factorPublicCertificate with
    descriptorBytes := factorPublicCertificate.descriptorBytes ++ " " }

#guard checkPublicLive factorPublicCertificate
#guard !checkPublicLive tamperedPiCertificate
#guard !checkPublicLive tamperedPublicLayoutCertificate
#guard !checkPublicLive tamperedPublicBytesCertificate

#assert_all_clean [
  Wire.expr_eval,
  witnessCount_eq_graphCost_witnesses,
  nodesAt_constraint_length,
  graphConstraints_length_eq_graphCost_equations,
  nodesAt_multiplications,
  emittedMultiplications_eq_graphCost,
  node_constraint_degree,
  descriptor_constraint_degree,
  descriptor_constraint_count,
  descriptor_aux_width,
  eval_eq_true_iff_holds,
  witnessBits_length,
  output_eval_of_matches,
  nodes_hold_of_matches,
  checkLive_spec,
  checkLive_certify,
  factor_emitted_exact,
  canonical_graph_constraints_hold,
  canonical_accept_iff,
  canonical_trace_satisfied_iff,
  checked_source_canonical_iff,
  public_descriptor_exact_overhead,
  fieldWindow_eq_cast,
  field_zero_of_gate,
  zeroTest_of_constraints,
  not_of_constraints,
  and_of_constraints,
  or_of_constraints,
  graph_of_node_constraints,
  public_pin_field,
  public_nodes_hold,
  public_accepts_output_one,
  public_statement_sound,
  public_canonical_trace_complete,
  public_canonical_trace_iff,
  checkPublicLive_spec,
  checkPublicLive_certify,
  checked_public_statement_sound,
  public_factor_emitted_exact
]

end Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
