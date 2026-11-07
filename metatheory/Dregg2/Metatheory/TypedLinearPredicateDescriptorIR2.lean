/-
# A typed predicate front end for the live DescriptorIR2 backend

The earlier direct-logic workload certificates stopped at an explicit atom
boundary: callers had to supply a `hatoms` hypothesis relating published truth
bits to the DREGG predicate.  This module removes that boundary for a useful,
nontrivial fragment.  Programs have typed public and secret field inputs, a
finite registry of affine zero-test atoms, and a Boolean AST over that registry.
The compiler emits, in one live `EffectVmDescriptor2`:

* public-input pins for the public prefix;
* one affine residual equation for every registered atom;
* exact inverse-witness zero tests and quadratic Boolean gates; and
* the accepting equation `output = 1`.

Atom semantics is definitionally the zero set of its typed affine term.  There
is therefore no external atom-truth equivalence in either soundness theorem.
The registry is shared (an atom term is emitted once), while the Boolean source
remains a natural AST over registry references rather than a DNF expansion.

The final section instantiates the compiler with the production interchain
trust-rung decision shape: `tag = 0`, or a nonzero payload at tag `1`/`2`.

Standalone and additive: no umbrella import is changed here.
-/

import Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
import Dregg2.Bridge.InterchainAdapterDecision

namespace Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
open Dregg2.Metatheory.DirectLogicOptimizerCertificate

set_option autoImplicit false

abbrev BabyBear : Type := ZMod 2013265921
abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

/-! ## 1. Typed affine atoms and their intrinsic semantics -/

/-- An affine field term over exactly `inputCount` typed inputs.  Keeping
multiplication out of this atom language makes every atom-link equation linear;
nonlinear gadgets can be added later as new semantics-carrying constructors. -/
inductive AffineTerm (inputCount : Nat) where
  | const (value : Int)
  | input (index : Fin inputCount)
  | neg (term : AffineTerm inputCount)
  | add (left right : AffineTerm inputCount)
  | scale (k : Int) (term : AffineTerm inputCount)
  deriving DecidableEq, Repr

namespace AffineTerm

def evalInt {m : Nat} (input : Fin m -> Int) : AffineTerm m -> Int
  | .const k => k
  | .input i => input i
  | .neg x => -(evalInt input x)
  | .add x y => evalInt input x + evalInt input y
  | .scale k x => k * evalInt input x

noncomputable def evalField {m : Nat} (input : Fin m -> BabyBear) : AffineTerm m -> BabyBear
  | .const k => (k : BabyBear)
  | .input i => input i
  | .neg x => -(evalField input x)
  | .add x y => evalField input x + evalField input y
  | .scale k x => (k : BabyBear) * evalField input x

/-- Wire expression at a chosen raw-input base column. -/
def toWindowAt {m : Nat} (rawBase : Nat) : AffineTerm m -> WindowExpr
  | .const k => .const k
  | .input i => .loc (rawBase + i.val)
  | .neg x => .mul (.const (-1)) (toWindowAt rawBase x)
  | .add x y => .add (toWindowAt rawBase x) (toWindowAt rawBase y)
  | .scale k x => .mul (.const k) (toWindowAt rawBase x)

def eqConst {m : Nat} (i : Fin m) (k : Int) : AffineTerm m :=
  .add (.input i) (.const (-k))

def eqInput {m : Nat} (i j : Fin m) : AffineTerm m :=
  .add (.input i) (.neg (.input j))

def additions {m : Nat} : AffineTerm m -> Nat
  | .const _ | .input _ => 0
  | .neg x => additions x
  | .add x y => additions x + additions y + 1
  | .scale _ x => additions x

theorem fieldWindow_toWindowAt {m : Nat} (env : VmRowEnv) (rawBase : Nat)
    (term : AffineTerm m) :
    fieldWindow env (term.toWindowAt rawBase) =
      term.evalField (fun i => fieldAssignment env.loc (rawBase + i.val)) := by
  induction term <;> simp [toWindowAt, evalField, fieldWindow, *]

theorem toWindowAt_degree {m : Nat} (rawBase : Nat) (term : AffineTerm m) :
    exprDegree (term.toWindowAt rawBase) ≤ 1 := by
  induction term <;> simp [toWindowAt, exprDegree, *]

end AffineTerm

/-! ## 1b. Nonlinear (bilinear) atom terms.

`AffineTerm` keeps every atom link degree ≤ 1.  `QuadTerm` adds ONE controlled
degree-2 form: `mul` of two *affine* children.  The grammar is closed under
`add`/`scale`/`neg` over such products (and injects `AffineTerm` via `lin`), so a
`QuadTerm` denotes any sum of `affine · affine` products plus an affine part —
degree at most two, never more, because `mul` takes only affine children and no
constructor multiplies two `QuadTerm`s.  This is exactly the shape of a BabyBear
extension-multiply output limb (a sum of coordinate products with the X⁴−11
coupling), so one `QuadTerm` atom lowers to one degree-2 gate. -/
inductive QuadTerm (inputCount : Nat) where
  | lin (term : AffineTerm inputCount)
  | mul (left right : AffineTerm inputCount)
  | neg (term : QuadTerm inputCount)
  | add (left right : QuadTerm inputCount)
  | scale (k : Int) (term : QuadTerm inputCount)
  deriving Repr

namespace QuadTerm

noncomputable def evalField {m : Nat} (input : Fin m -> BabyBear) : QuadTerm m -> BabyBear
  | .lin t => t.evalField input
  | .mul a b => a.evalField input * b.evalField input
  | .neg x => -(evalField input x)
  | .add x y => evalField input x + evalField input y
  | .scale k x => (k : BabyBear) * evalField input x

/-- Wire expression at a chosen raw-input base column.  The sole degree-2 form
is `mul`, lowering to a single `WindowExpr.mul` of two affine (degree ≤ 1)
window expressions. -/
def toWindowAt {m : Nat} (rawBase : Nat) : QuadTerm m -> WindowExpr
  | .lin t => t.toWindowAt rawBase
  | .mul a b => .mul (a.toWindowAt rawBase) (b.toWindowAt rawBase)
  | .neg x => .mul (.const (-1)) (toWindowAt rawBase x)
  | .add x y => .add (toWindowAt rawBase x) (toWindowAt rawBase y)
  | .scale k x => .mul (.const k) (toWindowAt rawBase x)

def additions {m : Nat} : QuadTerm m -> Nat
  | .lin t => t.additions
  | .mul a b => a.additions + b.additions
  | .neg x => additions x
  | .add x y => additions x + additions y + 1
  | .scale _ x => additions x

@[simp] theorem evalField_lin {m : Nat} (input : Fin m -> BabyBear) (t : AffineTerm m) :
    (QuadTerm.lin t).evalField input = t.evalField input := rfl

theorem fieldWindow_toWindowAt {m : Nat} (env : VmRowEnv) (rawBase : Nat)
    (term : QuadTerm m) :
    fieldWindow env (term.toWindowAt rawBase) =
      term.evalField (fun i => fieldAssignment env.loc (rawBase + i.val)) := by
  induction term with
  | lin t =>
      simpa [toWindowAt, evalField] using
        AffineTerm.fieldWindow_toWindowAt env rawBase t
  | mul a b =>
      simp [toWindowAt, evalField, fieldWindow, AffineTerm.fieldWindow_toWindowAt]
  | neg x ih => simp [toWindowAt, evalField, fieldWindow, ih]
  | add x y ihx ihy => simp [toWindowAt, evalField, fieldWindow, ihx, ihy]
  | scale k x ih => simp [toWindowAt, evalField, fieldWindow, ih]

/-- The bilinear widening stays low-degree: every `QuadTerm` lowers to a window
expression of degree at most two. -/
theorem toWindowAt_degree {m : Nat} (rawBase : Nat) (term : QuadTerm m) :
    exprDegree (term.toWindowAt rawBase) ≤ 2 := by
  induction term with
  | lin t =>
      have h := AffineTerm.toWindowAt_degree (m := m) rawBase t
      simp only [toWindowAt]; omega
  | mul a b =>
      have ha := AffineTerm.toWindowAt_degree (m := m) rawBase a
      have hb := AffineTerm.toWindowAt_degree (m := m) rawBase b
      simp only [toWindowAt, exprDegree]; omega
  | neg x ih => simp only [toWindowAt, exprDegree]; omega
  | add x y ihx ihy => simp only [toWindowAt, exprDegree]; omega
  | scale k x ih => simp only [toWindowAt, exprDegree]; omega

end QuadTerm

/-- A reusable gadget contract: `atomTerms` is both executable compiler input
and the semantic definition of every atom.  No proposition or correctness
proof is supplied by a caller and hence none can drift from the emitted wire. -/
structure Program (publicCount secretCount atomCount : Nat) where
  atomTerms : Fin atomCount -> AffineTerm (publicCount + secretCount)
  source : Formula atomCount

namespace Program

def inputCount {pub sec atoms : Nat} (_ : Program pub sec atoms) : Nat := pub + sec

noncomputable def AtomTruth {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (a : Fin atoms) : Prop :=
  (p.atomTerms a).evalField input = 0

noncomputable def Holds {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : Prop :=
  Formula.Holds (p.AtomTruth input) p.source

/-- The public statement existentially quantifies the typed secret suffix and
pins the public prefix to the verifier's field-valued inputs. -/
noncomputable def PublicHolds {pub sec atoms : Nat} (p : Program pub sec atoms)
    (publicInput : Fin pub -> BabyBear) : Prop :=
  exists input : Fin (pub + sec) -> BabyBear,
    (forall i : Fin pub, input (Fin.castAdd sec i) = publicInput i) /\ p.Holds input

end Program

/-! ## 2. Exact live layout and compositional compiler -/

def rawBase (atomCount : Nat) : Nat := atomCount

def boolBase (publicCount secretCount atomCount : Nat) : Nat :=
  atomCount + (publicCount + secretCount)

def publicPins (publicCount _secretCount atomCount : Nat) : List VmConstraint2 :=
  (List.range publicCount).map fun i =>
    .base (.piBinding .first (rawBase atomCount + i) i)

def atomLinkBody {pub sec atoms : Nat} (p : Program pub sec atoms)
    (a : Fin atoms) : WindowExpr :=
  subW (.loc a.val) ((p.atomTerms a).toWindowAt (rawBase atoms))

def atomLink {pub sec atoms : Nat} (p : Program pub sec atoms)
    (a : Fin atoms) : VmConstraint2 := gate (atomLinkBody p a)

def atomLinks {pub sec atoms : Nat} (p : Program pub sec atoms) : List VmConstraint2 :=
  (List.finRange atoms).map (atomLink p)

def graphConstraintsAt {pub sec atoms : Nat} (p : Program pub sec atoms) :
    List VmConstraint2 :=
  (nodesAt (boolBase pub sec atoms) p.source).flatMap Node.constraints

def acceptConstraintAt {pub sec atoms : Nat} (p : Program pub sec atoms) :
    VmConstraint2 :=
  gate (subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1))

/-- The compiler target is the exact live Rust-consumed descriptor schema. -/
def descriptor {pub sec atoms : Nat} (p : Program pub sec atoms) :
    EffectVmDescriptor2 :=
  { name := "dregg-typed-linear-predicate-v2-p" ++ toString pub ++
      "-s" ++ toString sec ++ "-a" ++ toString atoms
  , traceWidth := boolBase pub sec atoms + witnessCount p.source
  , piCount := pub
  , tables := [mainTableDef (boolBase pub sec atoms + witnessCount p.source)]
  , constraints := publicPins pub sec atoms ++ atomLinks p ++
      graphConstraintsAt p ++ [acceptConstraintAt p]
  , hashSites := []
  , ranges := [] }

structure Layout where
  publicInputs : Nat
  secretInputs : Nat
  atomResiduals : Nat
  booleanWitnesses : Nat
  traceWidth : Nat
  publicBindingEquations : Nat
  atomLinkEquations : Nat
  graphEquations : Nat
  totalEquations : Nat
  nonlinearMultiplications : Nat
  atomTermAdditions : Nat
  deriving DecidableEq, Repr

def layoutOf {pub sec atoms : Nat} (p : Program pub sec atoms) : Layout :=
  { publicInputs := pub
  , secretInputs := sec
  , atomResiduals := atoms
  , booleanWitnesses := witnessCount p.source
  , traceWidth := (descriptor p).traceWidth
  , publicBindingEquations := pub
  , atomLinkEquations := atoms
  , graphEquations := (graphConstraintsAt p).length
  , totalEquations := (descriptor p).constraints.length
  , nonlinearMultiplications := emittedMultiplications p.source
  , atomTermAdditions := (List.finRange atoms).map
      (fun a => (p.atomTerms a).additions) |>.sum }

theorem graphConstraintsAt_length {pub sec atoms : Nat} (p : Program pub sec atoms) :
    (graphConstraintsAt p).length = p.source.graphCost.equations := by
  exact nodesAt_constraint_length (boolBase pub sec atoms) p.source

theorem descriptor_exact_resources {pub sec atoms : Nat} (p : Program pub sec atoms) :
    (descriptor p).piCount = pub /\
    (descriptor p).traceWidth = atoms + (pub + sec) + witnessCount p.source /\
    (descriptor p).constraints.length = pub + atoms + p.source.graphCost.equations + 1 /\
    layoutOf p =
      { publicInputs := pub
      , secretInputs := sec
      , atomResiduals := atoms
      , booleanWitnesses := witnessCount p.source
      , traceWidth := atoms + (pub + sec) + witnessCount p.source
      , publicBindingEquations := pub
      , atomLinkEquations := atoms
      , graphEquations := p.source.graphCost.equations
      , totalEquations := pub + atoms + p.source.graphCost.equations + 1
      , nonlinearMultiplications := p.source.graphCost.multiplications
      , atomTermAdditions := (List.finRange atoms).map
          (fun a => (p.atomTerms a).additions) |>.sum } := by
  simp [descriptor, boolBase, publicPins, atomLinks, layoutOf,
    graphConstraintsAt_length, emittedMultiplications_eq_graphCost]
  omega

/-- Every emitted constraint is either a linear public pin or a window gate of
degree at most two.  In particular, the typed front end cannot accidentally
reintroduce a high-degree formula polynomial. -/
theorem descriptor_constraint_low_degree {pub sec atoms : Nat}
    (p : Program pub sec atoms) (c : VmConstraint2)
    (hc : c ∈ (descriptor p).constraints) :
    (exists row col pi, c = .base (.piBinding row col pi)) \/
      (exists body, c = gate body /\ exprDegree body ≤ 2) := by
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((hpin | hlink) | hgraph) | rfl
  · simp only [publicPins, List.mem_map] at hpin
    obtain ⟨i, _, rfl⟩ := hpin
    exact Or.inl ⟨.first, rawBase atoms + i, i, rfl⟩
  · simp only [atomLinks, List.mem_map] at hlink
    obtain ⟨a, _, rfl⟩ := hlink
    right
    refine ⟨atomLinkBody p a, rfl, ?_⟩
    have ht := AffineTerm.toWindowAt_degree (rawBase atoms) (p.atomTerms a)
    simp [atomLinkBody, subW, negW, exprDegree]
    omega
  · simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
    obtain ⟨node, hn, hcn⟩ := hgraph
    right
    exact node_constraint_degree node c hcn
  · right
    refine ⟨subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1), rfl, ?_⟩
    have hout := wire_expr_degree (outputAt (boolBase pub sec atoms) p.source)
    simp [subW, negW, exprDegree]
    omega

/-! ## 3. Arbitrary-trace soundness, with the atom boundary closed -/

noncomputable def rowInput {pub sec atoms : Nat} (_p : Program pub sec atoms)
    (t : VmTrace) : Fin (pub + sec) -> BabyBear :=
  fun i => fieldAssignment (envAt t 0).loc (rawBase atoms + i.val)

theorem public_pin_mem {pub sec atoms : Nat} (p : Program pub sec atoms)
    (i : Fin pub) :
    .base (.piBinding .first (rawBase atoms + i.val) i.val) ∈
      (descriptor p).constraints := by
  simp [descriptor, publicPins, List.mem_map, List.mem_range, i.isLt]

theorem atom_link_mem {pub sec atoms : Nat} (p : Program pub sec atoms)
    (a : Fin atoms) : atomLink p a ∈ (descriptor p).constraints := by
  simp [descriptor, atomLinks]

theorem graph_node_constraint_mem {pub sec atoms : Nat} (p : Program pub sec atoms)
    (node : Node) (hn : node ∈ nodesAt (boolBase pub sec atoms) p.source)
    (c : VmConstraint2) (hc : c ∈ node.constraints) :
    c ∈ (descriptor p).constraints := by
  simp [descriptor, graphConstraintsAt]
  exact Or.inr (Or.inr (Or.inl ⟨node, hn, hc⟩))

theorem public_pin_field (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : Program pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t)
    (i : Fin pub) :
    fieldAssignment (envAt t 0).loc (rawBase atoms + i.val) =
      fieldAssignment t.pub i.val := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hpin := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first (rawBase atoms + i.val) i.val)) (public_pin_mem p i)
  have hmod : (envAt t 0).loc (rawBase atoms + i.val) ≡ t.pub i.val
      [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, envAt] using hpin
  exact (ZMod.intCast_eq_intCast_iff _ _ 2013265921).2 hmod

theorem atom_link_field (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : Program pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t)
    (a : Fin atoms) :
    fieldAssignment (envAt t 0).loc a.val =
      (p.atomTerms a).evalField (rowInput p t) := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hgate := hsat.rowConstraints 0 hpos (atomLink p a) (atom_link_mem p a)
  have hz := field_zero_of_gate (env := envAt t 0) (body := atomLinkBody p a) (by
    simpa [atomLink, VmConstraint2.holdsAt, gate, WindowConstraint.holdsAt] using hgate)
  simp only [atomLinkBody, subW, negW, fieldWindow] at hz
  rw [AffineTerm.fieldWindow_toWindowAt] at hz
  have hz' : fieldAssignment (envAt t 0).loc a.val -
      (p.atomTerms a).evalField (rowInput p t) = 0 := by
    show fieldAssignment (envAt t 0).loc a.val - (p.atomTerms a).evalField
      (fun i => fieldAssignment (envAt t 0).loc (rawBase atoms + i.val)) = 0
    simpa [sub_eq_add_neg] using hz
  linear_combination hz'

theorem graph_nodes_hold (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : Program pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    forall node, node ∈ nodesAt (boolBase pub sec atoms) p.source ->
      Node.HoldsAt (envAt t 0) node := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  intro node hn c hc
  have hgate := hsat.rowConstraints 0 hpos c (graph_node_constraint_mem p node hn c hc)
  obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
  simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
    WindowConstraint.holdsAt] using hgate

theorem accepts_output_one (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : Program pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    fieldWire (envAt t 0).loc (outputAt (boolBase pub sec atoms) p.source) = 1 := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hmem : acceptConstraintAt p ∈ (descriptor p).constraints := by
    simp [descriptor]
  have hgate := hsat.rowConstraints 0 hpos (acceptConstraintAt p) hmem
  have hz := field_zero_of_gate (env := envAt t 0)
    (body := subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1)) (by
      simpa [acceptConstraintAt, VmConstraint2.holdsAt, gate, WindowConstraint.holdsAt] using hgate)
  simp [subW, negW, fieldWindow] at hz
  rw [fieldWire_expr] at hz
  linear_combination hz

/-- Any nonempty satisfying trace proves the source predicate on the actual
typed row inputs.  Unlike the prior workload theorem, there is no `hatoms`. -/
theorem sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.Holds (rowInput p t) := by
  have hgraph := graph_of_node_constraints (envAt t 0) (boolBase pub sec atoms)
    p.source (graph_nodes_hold hash hne hsat)
  have hout := accepts_output_one hash hne hsat
  have heval : Dregg2.Logic.BoolGraph.Eval
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val)
      p.source.toGraph :=
    (Dregg2.Logic.BoolGraph.graph_sound hgraph).2.mp hout
  have hrow : Formula.Holds
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val = 0) p.source :=
    (Formula.graphEval_iff_holds (F := BabyBear)
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val) p.source).mp heval
  apply (formula_holds_congr _ _ (fun a => ?_) p.source).mp hrow
  rw [atom_link_field hash hne hsat a]
  rfl

/-- Standalone statement soundness: public inputs are verifier-bound and the
secret suffix is existentially witnessed by the satisfying trace. -/
theorem public_sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.PublicHolds (fun i => fieldAssignment t.pub i.val) := by
  refine ⟨rowInput p t, ?_, sound hash p t hne hsat⟩
  intro i
  change fieldAssignment (envAt t 0).loc
      (rawBase atoms + (Fin.castAdd sec i).val) = fieldAssignment t.pub i.val
  simpa using public_pin_field hash hne hsat i

/-! ## 4. Total canonical witness and constructive completeness -/

noncomputable def zeroBit (x : BabyBear) : BabyBear := if x = 0 then 1 else 0

noncomputable def zeroInv (x : BabyBear) : BabyBear := if x = 0 then 0 else x⁻¹

theorem zero_witness_gate (x : BabyBear) :
    Dregg2.Logic.BoolGraph.ZeroGate x (zeroBit x) (zeroInv x) := by
  by_cases hx : x = 0
  · simp [zeroBit, zeroInv, hx, Dregg2.Logic.BoolGraph.ZeroGate,
      Dregg2.Logic.BoolGraph.IsBit]
  · simp [zeroBit, zeroInv, hx, Dregg2.Logic.BoolGraph.ZeroGate,
      Dregg2.Logic.BoolGraph.IsBit]

noncomputable def evalBit {n : Nat} (residual : Fin n -> BabyBear) :
    Formula n -> BabyBear
  | .atom a => zeroBit (residual a)
  | .top => 1
  | .bot => 0
  | .not p => 1 - evalBit residual p
  | .and p q => evalBit residual p * evalBit residual q
  | .or p q => evalBit residual p + evalBit residual q -
      evalBit residual p * evalBit residual q

theorem evalBit_isBit {n : Nat} (residual : Fin n -> BabyBear) (p : Formula n) :
    Dregg2.Logic.BoolGraph.IsBit (evalBit residual p) := by
  induction p with
  | atom a => exact (zero_witness_gate (residual a)).1
  | top => simp [evalBit, Dregg2.Logic.BoolGraph.IsBit]
  | bot => simp [evalBit, Dregg2.Logic.BoolGraph.IsBit]
  | not p ih => exact (Dregg2.Logic.BoolGraph.notGate_complete ih).2.1
  | and p q ihp ihq => exact (Dregg2.Logic.BoolGraph.andGate_complete ihp ihq).2.2.1
  | or p q ihp ihq => exact (Dregg2.Logic.BoolGraph.orGate_complete ihp ihq).2.2.1

theorem evalBit_one_iff {n : Nat} (residual : Fin n -> BabyBear) (p : Formula n) :
    evalBit residual p = 1 <->
      Formula.Holds (fun a => residual a = 0) p := by
  induction p with
  | atom a =>
      exact Dregg2.Logic.BoolGraph.zeroGate_sound (zero_witness_gate (residual a))
  | top => simp [evalBit, Formula.Holds]
  | bot => simp [evalBit, Formula.Holds]
  | not p ih =>
      have hg := Dregg2.Logic.BoolGraph.notGate_complete (evalBit_isBit residual p)
      simp only [evalBit, Formula.Holds]
      rw [Dregg2.Logic.BoolGraph.notGate_one_iff hg]
      rw [Dregg2.Logic.BoolGraph.bit_zero_iff_not_one (evalBit_isBit residual p)]
      exact not_congr ih
  | and p q ihp ihq =>
      have hg := Dregg2.Logic.BoolGraph.andGate_complete
        (evalBit_isBit residual p) (evalBit_isBit residual q)
      simp only [evalBit, Formula.Holds]
      rw [Dregg2.Logic.BoolGraph.andGate_one_iff hg, ihp, ihq]
  | or p q ihp ihq =>
      have hg := Dregg2.Logic.BoolGraph.orGate_complete
        (evalBit_isBit residual p) (evalBit_isBit residual q)
      simp only [evalBit, Formula.Holds]
      rw [Dregg2.Logic.BoolGraph.orGate_one_iff hg, ihp, ihq]

/-- Postorder field witnesses in exactly the allocation order of `nodesAt`.
Unlike the earlier Boolean-only canonical witness, atom inverse witnesses are
genuine inverses of arbitrary nonzero field residuals. -/
noncomputable def fieldWitness {n : Nat} (residual : Fin n -> BabyBear) :
    Formula n -> List BabyBear
  | .atom a => [zeroBit (residual a), zeroInv (residual a)]
  | .top | .bot => []
  | .not p => fieldWitness residual p ++ [evalBit residual (.not p)]
  | .and p q => fieldWitness residual p ++ fieldWitness residual q ++
      [evalBit residual (.and p q)]
  | .or p q => fieldWitness residual p ++ fieldWitness residual q ++
      [evalBit residual (.or p q)]

@[simp] theorem fieldWitness_length {n : Nat} (residual : Fin n -> BabyBear)
    (p : Formula n) : (fieldWitness residual p).length = witnessCount p := by
  induction p <;> simp [fieldWitness, witnessCount, *] <;> omega

private theorem field_getD_append_lt {A : Type*} (xs ys : List A) (i : Nat) (d : A)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem field_getD_append_right {A : Type*} (xs ys : List A) (k : Nat)
    (d : A) : (xs ++ ys).getD (xs.length + k) d = ys.getD k d := by
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right xs.length k)]

def FieldWitnessesMatch {n : Nat} (residual : Fin n -> BabyBear) (base : Nat)
    (p : Formula n) (row : Nat -> BabyBear) : Prop :=
  forall k, k < witnessCount p ->
    row (base + k) = (fieldWitness residual p).getD k 0

noncomputable def fieldWireValue (row : Nat -> BabyBear) : Wire -> BabyBear
  | .zero => 0
  | .one => 1
  | .col c => row c

theorem field_matches_not_child {n : Nat} {residual : Fin n -> BabyBear} {base : Nat}
    {p : Formula n} {row : Nat -> BabyBear}
    (h : FieldWitnessesMatch residual base (.not p) row) :
    FieldWitnessesMatch residual base p row := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [fieldWitness, field_getD_append_lt _ _ _ _ (by simpa using hk)] at hp
  exact hp

theorem field_matches_and_left {n : Nat} {residual : Fin n -> BabyBear} {base : Nat}
    {p q : Formula n} {row : Nat -> BabyBear}
    (h : FieldWitnessesMatch residual base (.and p q) row) :
    FieldWitnessesMatch residual base p row := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [fieldWitness, field_getD_append_lt _ _ _ _ (by
    simp [fieldWitness_length]; omega), field_getD_append_lt _ _ _ _ (by
      simpa [fieldWitness_length] using hk)] at hp
  exact hp

theorem field_matches_or_left {n : Nat} {residual : Fin n -> BabyBear} {base : Nat}
    {p q : Formula n} {row : Nat -> BabyBear}
    (h : FieldWitnessesMatch residual base (.or p q) row) :
    FieldWitnessesMatch residual base p row := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [fieldWitness, field_getD_append_lt _ _ _ _ (by
    simp [fieldWitness_length]; omega), field_getD_append_lt _ _ _ _ (by
      simpa [fieldWitness_length] using hk)] at hp
  exact hp

theorem field_matches_and_right {n : Nat} {residual : Fin n -> BabyBear}
    {base : Nat} {p q : Formula n} {row : Nat -> BabyBear}
    (h : FieldWitnessesMatch residual base (.and p q) row) :
    FieldWitnessesMatch residual (base + witnessCount p) q row := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [fieldWitness, field_getD_append_lt _ _ _ _ (by
    simp [fieldWitness_length]; omega)] at hp
  rw [show witnessCount p = (fieldWitness residual p).length by simp,
    field_getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

theorem field_matches_or_right {n : Nat} {residual : Fin n -> BabyBear}
    {base : Nat} {p q : Formula n} {row : Nat -> BabyBear}
    (h : FieldWitnessesMatch residual base (.or p q) row) :
    FieldWitnessesMatch residual (base + witnessCount p) q row := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [fieldWitness, field_getD_append_lt _ _ _ _ (by
    simp [fieldWitness_length]; omega)] at hp
  rw [show witnessCount p = (fieldWitness residual p).length by simp,
    field_getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

theorem field_output_of_matches {n : Nat} (residual : Fin n -> BabyBear) (base : Nat)
    (p : Formula n) (row : Nat -> BabyBear)
    (h : FieldWitnessesMatch residual base p row) :
    fieldWireValue row (outputAt base p) = evalBit residual p := by
  cases p with
  | atom a =>
      have hx := h 0 (by simp [witnessCount])
      simpa [outputAt, fieldWireValue, evalBit, fieldWitness] using hx
  | top => rfl
  | bot => rfl
  | not p =>
      have hx := h (witnessCount p) (by simp [witnessCount])
      rw [fieldWitness,
        show witnessCount p = (fieldWitness residual p).length by simp] at hx
      have hlast := field_getD_append_right (fieldWitness residual p)
        [evalBit residual (.not p)] 0 0
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, fieldWireValue, evalBit, Nat.add_assoc] using hx
  | and p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [fieldWitness,
        show witnessCount p + witnessCount q =
          (fieldWitness residual p ++ fieldWitness residual q).length by simp] at hx
      have hlast := field_getD_append_right
        (fieldWitness residual p ++ fieldWitness residual q)
        [evalBit residual (.and p q)] 0 0
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, fieldWireValue, evalBit, Nat.add_assoc] using hx
  | or p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [fieldWitness,
        show witnessCount p + witnessCount q =
          (fieldWitness residual p ++ fieldWitness residual q).length by simp] at hx
      have hlast := field_getD_append_right
        (fieldWitness residual p ++ fieldWitness residual q)
        [evalBit residual (.or p q)] 0 0
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, fieldWireValue, evalBit, Nat.add_assoc] using hx

namespace Node

noncomputable def FieldValid (row : Nat -> BabyBear) : Node -> Prop
  | .zeroTest x out inv =>
      Dregg2.Logic.BoolGraph.ZeroGate (row x) (row out) (row inv)
  | .not input out =>
      Dregg2.Logic.BoolGraph.NotGate (fieldWireValue row input) (row out)
  | .and left right out =>
      Dregg2.Logic.BoolGraph.AndGate (fieldWireValue row left)
        (fieldWireValue row right) (row out)
  | .or left right out =>
      Dregg2.Logic.BoolGraph.OrGate (fieldWireValue row left)
        (fieldWireValue row right) (row out)

end Node

/-- The postorder witness materializes a valid primitive gate at every node,
for arbitrary field residuals (not merely residuals `0`/`1`). -/
theorem field_nodes_valid_of_matches {n : Nat} (residual : Fin n -> BabyBear)
    (base : Nat) (p : Formula n) (row : Nat -> BabyBear)
    (hatom : forall a : Fin n, row a.val = residual a)
    (hmatch : FieldWitnessesMatch residual base p row) :
    forall node, node ∈ nodesAt base p -> Node.FieldValid row node := by
  induction p generalizing base with
  | atom a =>
      intro node hn
      simp only [nodesAt, List.mem_singleton] at hn
      subst node
      have hb := hmatch 0 (by simp [witnessCount])
      have hi := hmatch 1 (by simp [witnessCount])
      simp [fieldWitness] at hb hi
      simpa [Node.FieldValid, hatom a, hb, hi] using zero_witness_gate (residual a)
  | top => simp [nodesAt]
  | bot => simp [nodesAt]
  | not p ih =>
      intro node hn
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hn
      rcases hn with hchild | rfl
      · exact ih base (field_matches_not_child hmatch) node hchild
      · have hin := field_output_of_matches residual base p row
          (field_matches_not_child hmatch)
        have hout := field_output_of_matches residual base (.not p) row hmatch
        have hg := Dregg2.Logic.BoolGraph.notGate_complete (evalBit_isBit residual p)
        have hout' : row (base + witnessCount p) = evalBit residual (.not p) := by
          simpa [outputAt, fieldWireValue, evalBit] using hout
        change Dregg2.Logic.BoolGraph.NotGate
          (fieldWireValue row (outputAt base p)) (row (base + witnessCount p))
        rw [hin, hout']
        simpa [evalBit] using hg
  | and p q ihp ihq =>
      intro node hn
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hn
      rcases hn with (hp | hq) | rfl
      · exact ihp base (field_matches_and_left hmatch) node hp
      · exact ihq (base + witnessCount p) (field_matches_and_right hmatch) node hq
      · have hl := field_output_of_matches residual base p row
          (field_matches_and_left hmatch)
        have hr := field_output_of_matches residual (base + witnessCount p) q row
          (field_matches_and_right hmatch)
        have hout := field_output_of_matches residual base (.and p q) row hmatch
        have hg := Dregg2.Logic.BoolGraph.andGate_complete
          (evalBit_isBit residual p) (evalBit_isBit residual q)
        have hout' : row (base + witnessCount p + witnessCount q) =
            evalBit residual (.and p q) := by
          simpa [outputAt, fieldWireValue, evalBit, Nat.add_assoc] using hout
        change Dregg2.Logic.BoolGraph.AndGate
          (fieldWireValue row (outputAt base p))
          (fieldWireValue row (outputAt (base + witnessCount p) q))
          (row (base + witnessCount p + witnessCount q))
        rw [hl, hr, hout']
        simpa [evalBit] using hg
  | or p q ihp ihq =>
      intro node hn
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hn
      rcases hn with (hp | hq) | rfl
      · exact ihp base (field_matches_or_left hmatch) node hp
      · exact ihq (base + witnessCount p) (field_matches_or_right hmatch) node hq
      · have hl := field_output_of_matches residual base p row
          (field_matches_or_left hmatch)
        have hr := field_output_of_matches residual (base + witnessCount p) q row
          (field_matches_or_right hmatch)
        have hout := field_output_of_matches residual base (.or p q) row hmatch
        have hg := Dregg2.Logic.BoolGraph.orGate_complete
          (evalBit_isBit residual p) (evalBit_isBit residual q)
        have hout' : row (base + witnessCount p + witnessCount q) =
            evalBit residual (.or p q) := by
          simpa [outputAt, fieldWireValue, evalBit, Nat.add_assoc] using hout
        change Dregg2.Logic.BoolGraph.OrGate
          (fieldWireValue row (outputAt base p))
          (fieldWireValue row (outputAt (base + witnessCount p) q))
          (row (base + witnessCount p + witnessCount q))
        rw [hl, hr, hout']
        simpa [evalBit] using hg

theorem gate_holds_of_field_zero {env : VmRowEnv} {body : WindowExpr}
    (hz : fieldWindow env body = 0) :
    (gate body).holdsAt (fun _ => 0) (fun _ => []) env false true := by
  have hcast : (body.eval env : BabyBear) = (0 : BabyBear) := by
    simpa only [fieldWindow_eq_cast] using hz
  have hmod : body.eval env ≡ 0 [ZMOD 2013265921] :=
    (ZMod.intCast_eq_intCast_iff _ _ 2013265921).1 hcast
  simpa [gate, VmConstraint2.holdsAt, WindowConstraint.holdsAt] using hmod

theorem fieldWireValue_assignment (a : Assignment) (w : Wire) :
    fieldWireValue (fun c => fieldAssignment a c) w = fieldWire a w := by
  cases w <;> rfl

theorem isBit_add_neg_one {b : BabyBear}
    (h : Dregg2.Logic.BoolGraph.IsBit b) : b * (b + (-1)) = 0 := by
  simpa only [Dregg2.Logic.BoolGraph.IsBit, sub_eq_add_neg] using h

set_option maxRecDepth 10000 in
/-- A valid field primitive discharges the exact emitted live constraints. -/
theorem node_constraints_hold_of_field_valid (env : VmRowEnv) (node : Node)
    (hvalid : Node.FieldValid (fun c => fieldAssignment env.loc c) node) :
    Node.HoldsAt env node := by
  intro c hc
  cases node with
  | zeroTest x out inv =>
      rcases hvalid with ⟨hbit, hzero, hinv⟩
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl | rfl
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out * (fieldAssignment env.loc out + (-1)) = 0
        exact isBit_add_neg_one hbit
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc x * fieldAssignment env.loc out = 0
        exact hzero
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc x * fieldAssignment env.loc inv +
          fieldAssignment env.loc out + (-1) = 0
        linear_combination hinv
  | not input out =>
      rcases hvalid with ⟨hin, hout, heq⟩
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out * (fieldAssignment env.loc out + (-1)) = 0
        exact isBit_add_neg_one hout
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out + fieldWindow env input.expr + (-1) = 0
        rw [fieldWireValue_assignment] at heq
        rw [fieldWire_expr]
        linear_combination heq
  | and left right out =>
      rcases hvalid with ⟨hl, hr, hout, heq⟩
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out * (fieldAssignment env.loc out + (-1)) = 0
        exact isBit_add_neg_one hout
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out + (-1) *
          (fieldWindow env left.expr * fieldWindow env right.expr) = 0
        rw [fieldWireValue_assignment, fieldWireValue_assignment] at heq
        rw [fieldWire_expr, fieldWire_expr]
        linear_combination heq
  | or left right out =>
      rcases hvalid with ⟨hl, hr, hout, heq⟩
      simp [Node.constraints] at hc
      rcases hc with rfl | rfl
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out * (fieldAssignment env.loc out + (-1)) = 0
        exact isBit_add_neg_one hout
      · apply gate_holds_of_field_zero
        change fieldAssignment env.loc out + (-1) *
          ((fieldWindow env left.expr + fieldWindow env right.expr) +
            (-1) * (fieldWindow env left.expr * fieldWindow env right.expr)) = 0
        rw [fieldWireValue_assignment, fieldWireValue_assignment] at heq
        rw [fieldWire_expr, fieldWire_expr]
        linear_combination heq

noncomputable def residuals {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : Fin atoms -> BabyBear :=
  fun a => (p.atomTerms a).evalField input

/-- Canonical field row: shared atom residuals, typed raw inputs, then the
postorder Boolean/inverse witness region. -/
noncomputable def canonicalFieldRow {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (c : Nat) : BabyBear :=
  if ha : c < atoms then residuals p input ⟨c, ha⟩
  else if hr : c < boolBase pub sec atoms then
    input ⟨c - atoms, by simp [boolBase] at hr; omega⟩
  else (fieldWitness (residuals p input) p.source).getD
    (c - boolBase pub sec atoms) 0

def fieldRep (x : BabyBear) : Int := Int.ofNat x.val

noncomputable def canonicalRow {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : Assignment :=
  fun c => fieldRep (canonicalFieldRow p input c)

noncomputable def canonicalPublic {pub sec atoms : Nat} (_p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : Assignment :=
  fun c => if h : c < pub then fieldRep (input (Fin.castAdd sec ⟨c, h⟩)) else 0

noncomputable def canonicalTrace {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : VmTrace :=
  { rows := [canonicalRow p input]
  , pub := canonicalPublic p input
  , tf := fun _ => [] }

theorem fieldAssignment_fieldRep (x : BabyBear) :
    fieldAssignment (fun _ => fieldRep x) 0 = x := by
  simpa [fieldAssignment, fieldRep] using ZMod.natCast_zmod_val x

theorem fieldAssignment_canonicalRow {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (c : Nat) :
    fieldAssignment (canonicalRow p input) c = canonicalFieldRow p input c := by
  simpa [fieldAssignment, canonicalRow, fieldRep] using
    ZMod.natCast_zmod_val (canonicalFieldRow p input c)

theorem canonicalFieldRow_atom {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (a : Fin atoms) :
    canonicalFieldRow p input a.val = residuals p input a := by
  simp [canonicalFieldRow, a.isLt]

theorem canonicalFieldRow_raw {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (i : Fin (pub + sec)) :
    canonicalFieldRow p input (rawBase atoms + i.val) = input i := by
  simp [canonicalFieldRow, rawBase, boolBase, i.isLt]

theorem canonicalFieldRow_witness {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (k : Nat) :
    canonicalFieldRow p input (boolBase pub sec atoms + k) =
      (fieldWitness (residuals p input) p.source).getD k 0 := by
  rw [canonicalFieldRow]
  split
  · rename_i h
    simp [boolBase] at h
    omega
  · split
    · rename_i h
      simp [boolBase] at h
    · simp [boolBase]

theorem canonical_field_witnesses_match {pub sec atoms : Nat}
    (p : Program pub sec atoms) (input : Fin (pub + sec) -> BabyBear) :
    FieldWitnessesMatch (residuals p input) (boolBase pub sec atoms) p.source
      (canonicalFieldRow p input) := by
  intro k hk
  exact canonicalFieldRow_witness p input k

theorem canonical_nodes_hold {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) :
    forall node, node ∈ nodesAt (boolBase pub sec atoms) p.source ->
      Node.HoldsAt (envAt (canonicalTrace p input) 0) node := by
  intro node hn
  apply node_constraints_hold_of_field_valid
  have hvalid := field_nodes_valid_of_matches (residuals p input)
    (boolBase pub sec atoms) p.source (canonicalFieldRow p input)
    (canonicalFieldRow_atom p input) (canonical_field_witnesses_match p input) node hn
  simpa [canonicalTrace, envAt, fieldAssignment_canonicalRow] using hvalid

theorem canonical_atom_link_holds {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (a : Fin atoms) :
    (atomLink p a).holdsAt (fun _ => 0) (fun _ => [])
      (envAt (canonicalTrace p input) 0) false true := by
  apply gate_holds_of_field_zero
  simp only [atomLinkBody, subW, negW, fieldWindow]
  rw [AffineTerm.fieldWindow_toWindowAt]
  simp only [canonicalTrace, envAt, List.getD_cons_zero]
  rw [fieldAssignment_canonicalRow, canonicalFieldRow_atom]
  have heval : (p.atomTerms a).evalField
      (fun i => fieldAssignment (canonicalRow p input) (rawBase atoms + i.val)) =
      residuals p input a := by
    change (p.atomTerms a).evalField
      (fun i => fieldAssignment (canonicalRow p input) (rawBase atoms + i.val)) =
      (p.atomTerms a).evalField input
    apply congrArg (p.atomTerms a).evalField
    funext i
    rw [fieldAssignment_canonicalRow, canonicalFieldRow_raw]
  rw [heval]
  ring

theorem fieldAssignment_canonicalPublic {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (i : Fin pub) :
    fieldAssignment (canonicalPublic p input) i.val = input (Fin.castAdd sec i) := by
  simpa [canonicalPublic, fieldAssignment, fieldRep, i.isLt] using
    ZMod.natCast_zmod_val (input (Fin.castAdd sec i))

theorem canonical_public_pin_holds {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (i : Fin pub) :
    (VmConstraint2.base (.piBinding .first (rawBase atoms + i.val) i.val)).holdsAt
      (fun _ => 0) (fun _ => []) (envAt (canonicalTrace p input) 0) true true := by
  have hfield : fieldAssignment (canonicalRow p input) (rawBase atoms + i.val) =
      fieldAssignment (canonicalPublic p input) i.val := by
    rw [fieldAssignment_canonicalRow]
    have hraw := canonicalFieldRow_raw p input (Fin.castAdd sec i)
    rw [show (Fin.castAdd sec i).val = i.val by rfl] at hraw
    rw [hraw, fieldAssignment_canonicalPublic]
  have hmod : (canonicalRow p input) (rawBase atoms + i.val) ≡
      (canonicalPublic p input) i.val [ZMOD 2013265921] :=
    (ZMod.intCast_eq_intCast_iff _ _ 2013265921).1 hfield
  simpa [VmConstraint2.holdsAt, Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
    canonicalTrace, envAt] using hmod

theorem canonical_accept_holds {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (hholds : p.Holds input) :
    (acceptConstraintAt p).holdsAt (fun _ => 0) (fun _ => [])
      (envAt (canonicalTrace p input) 0) false true := by
  apply gate_holds_of_field_zero
  have hout := field_output_of_matches (residuals p input)
    (boolBase pub sec atoms) p.source (canonicalFieldRow p input)
    (canonical_field_witnesses_match p input)
  have hone : evalBit (residuals p input) p.source = 1 :=
    (evalBit_one_iff (residuals p input) p.source).2 hholds
  simp only [subW, negW, fieldWindow]
  rw [fieldWire_expr]
  rw [← fieldWireValue_assignment]
  simp only [canonicalTrace, envAt, List.getD_cons_zero]
  simp_rw [fieldAssignment_canonicalRow]
  rw [hout, hone]
  norm_num

private theorem node_mem_filter_nil (node : Node) :
    node.constraints.filterMap (fun c => match c with
      | .memOp m => some m | _ => none) = [] := by
  cases node <;> rfl

private theorem node_map_filter_nil (node : Node) :
    node.constraints.filterMap (fun c => match c with
      | .mapOp m => some m | _ => none) = [] := by
  cases node <;> rfl

private theorem nodes_mem_filter_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap (fun c => match c with
      | .memOp m => some m | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [node_mem_filter_nil, ih]

private theorem nodes_map_filter_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap (fun c => match c with
      | .mapOp m => some m | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [node_map_filter_nil, ih]

theorem memOps_descriptor_nil {pub sec atoms : Nat} (p : Program pub sec atoms) :
    memOpsOf (descriptor p) = [] := by
  change ((publicPins pub sec atoms ++ atomLinks p ++ graphConstraintsAt p ++
    [acceptConstraintAt p]).filterMap (fun c => match c with
      | .memOp m => some m | _ => none)) = []
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append]
  have hpins : (publicPins pub sec atoms).filterMap (fun c => match c with
      | .memOp m => some m | _ => none) = [] := by
    simp [publicPins]
  have hlinks : (atomLinks p).filterMap (fun c => match c with
      | .memOp m => some m | _ => none) = [] := by
    simp [atomLinks, atomLink, gate]
  have hgraph := nodes_mem_filter_nil (nodesAt (boolBase pub sec atoms) p.source)
  change (graphConstraintsAt p).filterMap (fun c => match c with
      | .memOp m => some m | _ => none) = [] at hgraph
  rw [hpins, hlinks, hgraph]
  rfl

theorem mapOps_descriptor_nil {pub sec atoms : Nat} (p : Program pub sec atoms) :
    mapOpsOf (descriptor p) = [] := by
  change ((publicPins pub sec atoms ++ atomLinks p ++ graphConstraintsAt p ++
    [acceptConstraintAt p]).filterMap (fun c => match c with
      | .mapOp m => some m | _ => none)) = []
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append]
  have hpins : (publicPins pub sec atoms).filterMap (fun c => match c with
      | .mapOp m => some m | _ => none) = [] := by
    simp [publicPins]
  have hlinks : (atomLinks p).filterMap (fun c => match c with
      | .mapOp m => some m | _ => none) = [] := by
    simp [atomLinks, atomLink, gate]
  have hgraph := nodes_map_filter_nil (nodesAt (boolBase pub sec atoms) p.source)
  change (graphConstraintsAt p).filterMap (fun c => match c with
      | .mapOp m => some m | _ => none) = [] at hgraph
  rw [hpins, hlinks, hgraph]
  rfl

theorem memLog_descriptor_nil {pub sec atoms : Nat} (p : Program pub sec atoms)
    (t : VmTrace) : memLog (descriptor p) t = [] := by
  simp [memLog, memOps_descriptor_nil]

theorem mapLog_descriptor_nil {pub sec atoms : Nat} (p : Program pub sec atoms)
    (t : VmTrace) : mapLog (descriptor p) t = [] := by
  simp [mapLog, mapOps_descriptor_nil]

set_option maxHeartbeats 2000000 in
/-- Constructive completeness for arbitrary public and secret field inputs.
Every affine residual, inverse witness, Boolean wire, public pin, and accepting
wire is constructed by this module. -/
theorem canonical_complete (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (input : Fin (pub + sec) -> BabyBear)
    (hholds : p.Holds input) :
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) []
      (canonicalTrace p input) := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro rowIndex hrow c hc
    have hzero : rowIndex = 0 := by simp [canonicalTrace] at hrow; omega
    subst rowIndex
    simp only [descriptor, List.mem_append, List.mem_singleton] at hc
    rcases hc with ((hpin | hlink) | hgraph) | rfl
    · simp only [publicPins, List.mem_map] at hpin
      obtain ⟨i, hi, rfl⟩ := hpin
      have hil : i < pub := List.mem_range.mp hi
      exact canonical_public_pin_holds p input ⟨i, hil⟩
    · simp only [atomLinks, List.mem_map] at hlink
      obtain ⟨a, _, rfl⟩ := hlink
      exact canonical_atom_link_holds p input a
    · simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
      obtain ⟨node, hn, hcn⟩ := hgraph
      have hgate := canonical_nodes_hold p input node hn c hcn
      obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcn
      simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
        WindowConstraint.holdsAt] using hgate
    · exact canonical_accept_holds p input hholds
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

/-- Exact semantic equivalence on the compiler's canonical trace. -/
theorem canonical_iff (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (input : Fin (pub + sec) -> BabyBear) :
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p input) <-> p.Holds input := by
  constructor
  · intro hsat
    have hs := sound hash p (canonicalTrace p input) (by simp [canonicalTrace]) hsat
    have hrow : rowInput p (canonicalTrace p input) = input := by
      funext i
      change fieldAssignment (envAt (canonicalTrace p input) 0).loc
        (rawBase atoms + i.val) = input i
      simp only [canonicalTrace, envAt, List.getD_cons_zero]
      rw [fieldAssignment_canonicalRow, canonicalFieldRow_raw]
    apply (formula_holds_congr _ _ (fun a => ?_) p.source).mp hs
    rw [hrow]
  · exact canonical_complete hash p input

/-! ## 5. Reconstructible layout/byte artifact -/

def artifactVersion : Nat := 1

structure Artifact {pub sec atoms : Nat} (p : Program pub sec atoms) where
  version : Nat
  layout : Layout
  descriptorBytes : String
  deriving Repr

def checkArtifact {pub sec atoms : Nat} {p : Program pub sec atoms}
    (artifact : Artifact p) : Bool :=
  decide (artifact.version = artifactVersion) &&
    decide (artifact.layout = layoutOf p) &&
    decide (artifact.descriptorBytes = emitVmJson2 (descriptor p))

def certify {pub sec atoms : Nat} (p : Program pub sec atoms) : Artifact p :=
  { version := artifactVersion
  , layout := layoutOf p
  , descriptorBytes := emitVmJson2 (descriptor p) }

theorem checkArtifact_spec {pub sec atoms : Nat} {p : Program pub sec atoms}
    (artifact : Artifact p) :
    checkArtifact artifact = true <->
      artifact.version = artifactVersion /\
      artifact.layout = layoutOf p /\
      artifact.descriptorBytes = emitVmJson2 (descriptor p) := by
  simp [checkArtifact, and_assoc]

theorem checkArtifact_certify {pub sec atoms : Nat} (p : Program pub sec atoms) :
    checkArtifact (certify p) = true := by
  simp [checkArtifact, certify]

/-! ## 6. Production-shaped DREGG trust-rung instance -/

namespace InterchainRung

open Dregg2.Bridge.InterchainAdapterDecision

private def input0 : Fin 2 := ⟨0, by omega⟩
private def input1 : Fin 2 := ⟨1, by omega⟩
private def atom0 : Formula 4 := .atom ⟨0, by omega⟩
private def atom1 : Formula 4 := .atom ⟨1, by omega⟩
private def atom2 : Formula 4 := .atom ⟨2, by omega⟩
private def atom3 : Formula 4 := .atom ⟨3, by omega⟩

/-- Shared affine atom registry: three tag equalities and payload-zero.  These
are residual computations in the descriptor, not published truth bits. -/
def atomTerms : Fin 4 -> AffineTerm 2
  | ⟨0, _⟩ => .eqConst input0 0
  | ⟨1, _⟩ => .eqConst input0 1
  | ⟨2, _⟩ => .eqConst input0 2
  | ⟨3, _⟩ => .eqConst input1 0
  | ⟨_, _⟩ => .const 1

/-- Natural source AST for `proof ∨ (payload≠0 ∧ (watchtower ∨ committee))`.
It is not expanded into DNF. -/
def source : Formula 4 :=
  .or atom0 (.and (.not atom3) (.or atom1 atom2))

def program : Program 2 0 4 :=
  { atomTerms := atomTerms
  , source := source }

def Reaches (tag payload : BabyBear) : Prop :=
  tag = 0 \/ (payload ≠ 0 /\ (tag = 1 \/ tag = 2))

noncomputable def inputOf (tag payload : BabyBear) : Fin 2 -> BabyBear
  | ⟨0, _⟩ => tag
  | ⟨1, _⟩ => payload
  | ⟨_, _⟩ => 0

theorem add_neg_one_zero_iff (x : BabyBear) : x + (-1) = 0 <-> x = 1 := by
  constructor <;> intro h <;> linear_combination h

theorem add_neg_two_zero_iff (x : BabyBear) : x + (-2) = 0 <-> x = 2 := by
  constructor <;> intro h <;> linear_combination h

theorem two_ne_zero : (2 : BabyBear) ≠ 0 := by
  intro h
  have hmod : (2 : Int) ≡ 0 [ZMOD 2013265921] :=
    (ZMod.intCast_eq_intCast_iff (2 : Int) 0 2013265921).1 (by simpa using h)
  norm_num [Int.ModEq] at hmod

theorem three_ne_zero : (3 : BabyBear) ≠ 0 := by
  intro h
  have hmod : (3 : Int) ≡ 0 [ZMOD 2013265921] :=
    (ZMod.intCast_eq_intCast_iff (3 : Int) 0 2013265921).1 (by simpa using h)
  norm_num [Int.ModEq] at hmod

theorem program_holds_iff (tag payload : BabyBear) :
    program.Holds (inputOf tag payload) <-> Reaches tag payload := by
  simp only [program, Program.Holds, Program.AtomTruth, source, atom0, atom1, atom2, atom3, input0, input1, Formula.Holds]
  simp only [atomTerms, AffineTerm.eqConst, AffineTerm.evalField, input0, input1, inputOf]
  simp [Reaches, add_neg_one_zero_iff, add_neg_two_zero_iff]

/-- Embed the production `(tag,payload)` wire in BabyBear.  This front end is
field-native: arbitrary unbounded integers must be range/canonicality checked
before casting, or distinct integers separated by the field modulus alias. -/
noncomputable def encodedInput (r : TrustRung) : Fin 2 -> BabyBear :=
  inputOf ((encodeRung r).1 : BabyBear) ((encodeRung r).2 : BabyBear)

/-- The typed field program agrees with the existing verified DREGG decision
on every valid production wire encoding. -/
theorem encoded_program_exact (r : TrustRung) :
    program.Holds (encodedInput r) <-> reachedConsensusCore r = true := by
  cases r with
  | proof => norm_num [program_holds_iff, encodedInput, inputOf, Reaches,
      two_ne_zero, three_ne_zero, ZMod.intCast_eq_intCast_iff,
      encodeRung, reachedConsensusCore]
  | optimisticWatchtower rv =>
      cases rv <;> norm_num [program_holds_iff, encodedInput, inputOf, Reaches,
        two_ne_zero, three_ne_zero, ZMod.intCast_eq_intCast_iff,
        encodeRung, reachedConsensusCore]
  | committee hq =>
      cases hq <;> norm_num [program_holds_iff, encodedInput, inputOf, Reaches,
        two_ne_zero, three_ne_zero, ZMod.intCast_eq_intCast_iff,
        encodeRung, reachedConsensusCore]
  | rpc => norm_num [program_holds_iff, encodedInput, inputOf, Reaches,
      two_ne_zero, three_ne_zero, ZMod.intCast_eq_intCast_iff,
      encodeRung, reachedConsensusCore]

/-- Explicit anti-overclaim at the integer/field boundary: the field modulus
aliases tag zero, while the unbounded integer wire correctly treats it as an
unknown tag.  `encoded_program_exact` is intentionally scoped to canonical
`TrustRung` encodings until a range/canonicalization gadget is composed. -/
theorem modulus_tag_alias_frontier :
    Reaches ((2013265921 : Int) : BabyBear) 0 /\
      reachedConsensusWire 2013265921 0 = false := by
  have hzero : ((2013265921 : Int) : BabyBear) = 0 := by
    apply (ZMod.intCast_eq_intCast_iff (2013265921 : Int) 0 2013265921).2
    norm_num [Int.ModEq]
  constructor
  · left
    exact hzero
  · exact unknown_tag_refuses 2013265921 0 (by norm_num) (by norm_num) (by norm_num)

/-- The dual alias: a modulus-sized integer payload is nonzero as an integer
but zero after field casting.  This is why the direct production replacement
requires canonical wire inputs, not merely the affine/Boolean compiler. -/
theorem modulus_payload_alias_frontier :
    (¬ Reaches 1 ((2013265921 : Int) : BabyBear)) /\
      reachedConsensusWire 1 2013265921 = true := by
  have hzero : ((2013265921 : Int) : BabyBear) = 0 := by
    apply (ZMod.intCast_eq_intCast_iff (2013265921 : Int) 0 2013265921).2
    norm_num [Int.ModEq]
  constructor
  · rw [hzero]
    simp [Reaches]
  · simp [reachedConsensusWire]

def artifact : Artifact program := certify program

def descriptorJson : String := artifact.descriptorBytes

theorem exact_live_ledger :
    (descriptor program).piCount = 2 /\
    (descriptor program).traceWidth = 18 /\
    (graphConstraintsAt program).length = 20 /\
    (descriptor program).constraints.length = 27 /\
    emittedMultiplications program.source = 19 /\
    (layoutOf program).publicInputs = 2 /\
    (layoutOf program).secretInputs = 0 /\
    (layoutOf program).atomResiduals = 4 /\
    (layoutOf program).booleanWitnesses = 12 /\
    (layoutOf program).atomTermAdditions = 4 := by
  decide

theorem descriptor_bytes_exact :
    descriptorJson = emitVmJson2 (descriptor program) := by
  exact (checkArtifact_spec artifact |>.mp (checkArtifact_certify program)).2.2

def badBytes : Artifact program :=
  { artifact with descriptorBytes := artifact.descriptorBytes ++ " " }

def badLayout : Artifact program :=
  { artifact with layout := { artifact.layout with secretInputs := 1 } }

#guard checkArtifact artifact
#guard !checkArtifact badBytes
#guard !checkArtifact badLayout

/-- Arbitrary-trace soundness for the production-shaped instance, with tag and
payload read from the internally pinned/raw descriptor columns. -/
theorem live_sound (hash : List Int -> Int) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor program) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    Reaches (fieldAssignment (envAt t 0).loc 4)
      (fieldAssignment (envAt t 0).loc 5) := by
  have hs := sound hash program t hne hsat
  have hinput : rowInput program t = inputOf
      (fieldAssignment (envAt t 0).loc 4)
      (fieldAssignment (envAt t 0).loc 5) := by
    funext i
    fin_cases i <;> rfl
  rw [hinput, program_holds_iff] at hs
  exact hs

/-- Constructive completeness for every accepting field tag/payload pair. -/
theorem live_complete (hash : List Int -> Int) (tag payload : BabyBear)
    (hreaches : Reaches tag payload) :
    Satisfied2 hash (descriptor program) (fun _ => 0) (fun _ => (0, 0)) []
      (canonicalTrace program (inputOf tag payload)) := by
  apply canonical_complete
  exact (program_holds_iff tag payload).2 hreaches

end InterchainRung

/-! ## 7. Nonlinear (bilinear) atom widening: the parallel `QuadProgram` stack.

The affine `Program` fragment above is a shared interface consumed by several
downstream modules (`ArithmetizeTypedPredicate`, `BridgeSynthesis`,
`FieldDeltaRangePilot`), so it is left byte-for-byte intact.  This section adds
an ADDITIVE parallel compiler whose atom residuals are `QuadTerm`s — the same
public pins, the same materialized Boolean graph, the same accept gate — with
the sole change that an atom link lowers a degree-2 `QuadTerm` instead of a
degree-1 `AffineTerm`.  Every generic Boolean-graph lemma (`graph_of_node_constraints`,
`node_constraint_degree`, `formula_holds_congr`, …) is reused unchanged; only the
five atom-link glue lemmas are re-derived. -/

def andList {n : Nat} : List (Formula n) -> Formula n
  | [] => .top
  | [a] => a
  | a :: rest => .and a (andList rest)

structure QuadProgram (publicCount secretCount atomCount : Nat) where
  atomTerms : Fin atomCount -> QuadTerm (publicCount + secretCount)
  source : Formula atomCount

namespace QuadProgram

noncomputable def AtomTruth {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) (a : Fin atoms) : Prop :=
  (p.atomTerms a).evalField input = 0

noncomputable def Holds {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) : Prop :=
  Formula.Holds (p.AtomTruth input) p.source

noncomputable def PublicHolds {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (publicInput : Fin pub -> BabyBear) : Prop :=
  exists input : Fin (pub + sec) -> BabyBear,
    (forall i : Fin pub, input (Fin.castAdd sec i) = publicInput i) /\ p.Holds input

def atomLinkBody {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (a : Fin atoms) : WindowExpr :=
  subW (.loc a.val) ((p.atomTerms a).toWindowAt (rawBase atoms))

def atomLink {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (a : Fin atoms) : VmConstraint2 := gate (atomLinkBody p a)

def atomLinks {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) : List VmConstraint2 :=
  (List.finRange atoms).map (atomLink p)

def graphConstraintsAt {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    List VmConstraint2 :=
  (nodesAt (boolBase pub sec atoms) p.source).flatMap Node.constraints

def acceptConstraintAt {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    VmConstraint2 :=
  gate (subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1))

/-- The nonlinear compiler target: identical schema to the affine compiler, but
the atom links are degree-2 `QuadTerm` residuals. -/
def descriptor {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    EffectVmDescriptor2 :=
  { name := "dregg-typed-nonlinear-predicate-v2-p" ++ toString pub ++
      "-s" ++ toString sec ++ "-a" ++ toString atoms
  , traceWidth := boolBase pub sec atoms + witnessCount p.source
  , piCount := pub
  , tables := [mainTableDef (boolBase pub sec atoms + witnessCount p.source)]
  , constraints := publicPins pub sec atoms ++ atomLinks p ++
      graphConstraintsAt p ++ [acceptConstraintAt p]
  , hashSites := []
  , ranges := [] }

theorem graphConstraintsAt_length {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    (graphConstraintsAt p).length = p.source.graphCost.equations :=
  nodesAt_constraint_length (boolBase pub sec atoms) p.source

theorem descriptor_exact_resources {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    (descriptor p).piCount = pub /\
    (descriptor p).traceWidth = atoms + (pub + sec) + witnessCount p.source /\
    (descriptor p).constraints.length = pub + atoms + p.source.graphCost.equations + 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [descriptor, boolBase]
  · simp [descriptor, publicPins, atomLinks, graphConstraintsAt_length]
    omega

/-- Deliverable (2): the bilinear atom is degree 2, so every emitted constraint
is still a linear public pin or a degree-≤2 window gate.  The `QuadTerm` widening
provably cannot exceed the low-degree bound. -/
theorem descriptor_constraint_low_degree {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) (c : VmConstraint2)
    (hc : c ∈ (descriptor p).constraints) :
    (exists row col pi, c = .base (.piBinding row col pi)) \/
      (exists body, c = gate body /\ exprDegree body ≤ 2) := by
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((hpin | hlink) | hgraph) | rfl
  · simp only [publicPins, List.mem_map] at hpin
    obtain ⟨i, _, rfl⟩ := hpin
    exact Or.inl ⟨.first, rawBase atoms + i, i, rfl⟩
  · simp only [atomLinks, List.mem_map] at hlink
    obtain ⟨a, _, rfl⟩ := hlink
    right
    refine ⟨atomLinkBody p a, rfl, ?_⟩
    have ht := QuadTerm.toWindowAt_degree (rawBase atoms) (p.atomTerms a)
    simp [atomLinkBody, subW, negW, exprDegree]
    omega
  · simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
    obtain ⟨node, hn, hcn⟩ := hgraph
    right
    exact node_constraint_degree node c hcn
  · right
    refine ⟨subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1), rfl, ?_⟩
    have hout := wire_expr_degree (outputAt (boolBase pub sec atoms) p.source)
    simp [subW, negW, exprDegree]
    omega

noncomputable def rowInput {pub sec atoms : Nat} (_p : QuadProgram pub sec atoms)
    (t : VmTrace) : Fin (pub + sec) -> BabyBear :=
  fun i => fieldAssignment (envAt t 0).loc (rawBase atoms + i.val)

theorem public_pin_mem {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (i : Fin pub) :
    .base (.piBinding .first (rawBase atoms + i.val) i.val) ∈
      (descriptor p).constraints := by
  simp [descriptor, publicPins, List.mem_map, List.mem_range, i.isLt]

theorem atom_link_mem {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (a : Fin atoms) : atomLink p a ∈ (descriptor p).constraints := by
  simp [descriptor, atomLinks]

theorem graph_node_constraint_mem {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (node : Node) (hn : node ∈ nodesAt (boolBase pub sec atoms) p.source)
    (c : VmConstraint2) (hc : c ∈ node.constraints) :
    c ∈ (descriptor p).constraints := by
  simp [descriptor, graphConstraintsAt]
  exact Or.inr (Or.inr (Or.inl ⟨node, hn, hc⟩))

theorem public_pin_field (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : QuadProgram pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t)
    (i : Fin pub) :
    fieldAssignment (envAt t 0).loc (rawBase atoms + i.val) =
      fieldAssignment t.pub i.val := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hpin := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first (rawBase atoms + i.val) i.val)) (public_pin_mem p i)
  have hmod : (envAt t 0).loc (rawBase atoms + i.val) ≡ t.pub i.val
      [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, envAt] using hpin
  exact (ZMod.intCast_eq_intCast_iff _ _ 2013265921).2 hmod

/-- The single re-derived atom-link glue: the emitted degree-2 gate pins the
atom residual column to the `QuadTerm`'s field value. -/
theorem atom_link_field (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : QuadProgram pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t)
    (a : Fin atoms) :
    fieldAssignment (envAt t 0).loc a.val =
      (p.atomTerms a).evalField (rowInput p t) := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hgate := hsat.rowConstraints 0 hpos (atomLink p a) (atom_link_mem p a)
  have hz := field_zero_of_gate (env := envAt t 0) (body := atomLinkBody p a) (by
    simpa [atomLink, VmConstraint2.holdsAt, gate, WindowConstraint.holdsAt] using hgate)
  simp only [atomLinkBody, subW, negW, fieldWindow] at hz
  rw [QuadTerm.fieldWindow_toWindowAt] at hz
  have hz' : fieldAssignment (envAt t 0).loc a.val -
      (p.atomTerms a).evalField (rowInput p t) = 0 := by
    show fieldAssignment (envAt t 0).loc a.val - (p.atomTerms a).evalField
      (fun i => fieldAssignment (envAt t 0).loc (rawBase atoms + i.val)) = 0
    simpa [sub_eq_add_neg] using hz
  linear_combination hz'

theorem graph_nodes_hold (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : QuadProgram pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    forall node, node ∈ nodesAt (boolBase pub sec atoms) p.source ->
      Node.HoldsAt (envAt t 0) node := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  intro node hn c hc
  have hgate := hsat.rowConstraints 0 hpos c (graph_node_constraint_mem p node hn c hc)
  obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
  simpa [Node.HoldsAt, gate, VmConstraint2.holdsAt,
    WindowConstraint.holdsAt] using hgate

theorem accepts_output_one (hash : List Int -> Int) {pub sec atoms : Nat}
    {p : QuadProgram pub sec atoms} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    fieldWire (envAt t 0).loc (outputAt (boolBase pub sec atoms) p.source) = 1 := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hmem : acceptConstraintAt p ∈ (descriptor p).constraints := by
    simp [descriptor]
  have hgate := hsat.rowConstraints 0 hpos (acceptConstraintAt p) hmem
  have hz := field_zero_of_gate (env := envAt t 0)
    (body := subW (outputAt (boolBase pub sec atoms) p.source).expr (.const 1)) (by
      simpa [acceptConstraintAt, VmConstraint2.holdsAt, gate, WindowConstraint.holdsAt] using hgate)
  simp [subW, negW, fieldWindow] at hz
  rw [fieldWire_expr] at hz
  linear_combination hz

/-- Deliverable (1) payoff: arbitrary-trace soundness for the NONLINEAR
compiler.  Any nonempty satisfying trace of the emitted descriptor proves the
source predicate on the actual typed row inputs — with bilinear atoms now in the
fragment. -/
theorem sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.Holds (rowInput p t) := by
  have hgraph := graph_of_node_constraints (envAt t 0) (boolBase pub sec atoms)
    p.source (graph_nodes_hold hash hne hsat)
  have hout := accepts_output_one hash hne hsat
  have heval : Dregg2.Logic.BoolGraph.Eval
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val)
      p.source.toGraph :=
    (Dregg2.Logic.BoolGraph.graph_sound hgraph).2.mp hout
  have hrow : Formula.Holds
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val = 0) p.source :=
    (Formula.graphEval_iff_holds (F := BabyBear)
      (fun a : Fin atoms => fieldAssignment (envAt t 0).loc a.val) p.source).mp heval
  apply (formula_holds_congr _ _ (fun a => ?_) p.source).mp hrow
  rw [atom_link_field hash hne hsat a]
  rfl

theorem public_sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.PublicHolds (fun i => fieldAssignment t.pub i.val) := by
  refine ⟨rowInput p t, ?_, sound hash p t hne hsat⟩
  intro i
  change fieldAssignment (envAt t 0).loc
      (rawBase atoms + (Fin.castAdd sec i).val) = fieldAssignment t.pub i.val
  simpa using public_pin_field hash hne hsat i

end QuadProgram

/-! ## 8. Re-derivation of `quantified_absence` as a nonlinear `QuadProgram`.

`Dregg2.Circuit.Emit.QuantifiedAbsenceEmit.quantifiedAbsenceDesc` is a bespoke,
hand-authored BabyBear⁴ descriptor (`traceWidth 28`, `20 constraints`, per-limb
`_zero_iff` teeth but NO whole-descriptor soundness).  Here the same per-element
relation `diff = α−elem`, `prod = w·diff`, `sum = prod+v`, `sum = Acc_all` is
authored as a compiled `QuadProgram` — the bilinear `prod` limbs use the new
`QuadTerm` form — so it inherits the machine-checked `QuadProgram.sound`.

Scope note (honest, per the extension-field residual): the BabyBear⁴ multiply
mod (X⁴−11) is NOT a single `a·b=c` product, but each output limb IS a single
degree-2 polynomial (a sum of `w_j·d_k` products), which the `QuadTerm.mul`/`add`
grammar expresses exactly and lowers to ONE degree-2 gate per limb.  There is
therefore no unmodeled extension residual for the multiply itself; the four
limbs are the four `prodAtom*` below, term-for-term the hand AIR's `prodC*`. -/
namespace QuantifiedAbsence

private def AC (i : Fin 4) : AffineTerm 32 := .input ⟨0 + i.val, by have := i.isLt; omega⟩
private def AL (i : Fin 4) : AffineTerm 32 := .input ⟨4 + i.val, by have := i.isLt; omega⟩
private def E (i : Fin 4) : AffineTerm 32 := .input ⟨8 + i.val, by have := i.isLt; omega⟩
private def V (i : Fin 4) : AffineTerm 32 := .input ⟨16 + i.val, by have := i.isLt; omega⟩
private def D (i : Fin 4) : AffineTerm 32 := .input ⟨20 + i.val, by have := i.isLt; omega⟩
private def P (i : Fin 4) : AffineTerm 32 := .input ⟨24 + i.val, by have := i.isLt; omega⟩
private def S (i : Fin 4) : AffineTerm 32 := .input ⟨28 + i.val, by have := i.isLt; omega⟩

/-- C1 limb i: `diff_i − (α_i − elem_i)` (affine, one degree-1 gate). -/
private def diffAtom (i : Fin 4) : QuadTerm 32 :=
  .lin (.add (D i) (.add (.neg (AL i)) (E i)))
/-- C3 limb i: `sum_i − (prod_i + v_i)` (affine). -/
private def sumAtom (i : Fin 4) : QuadTerm 32 :=
  .lin (.add (S i) (.add (.neg (P i)) (.neg (V i))))
/-- Boundary limb i: `sum_i − Acc_all_i` (affine, over the public `Acc_all`). -/
private def boundAtom (i : Fin 4) : QuadTerm 32 :=
  .lin (.add (S i) (.neg (AC i)))

/-- Literal-indexed columns for the bilinear C2 teeth (so they unfold to
`input ⟨24⟩` rather than `input ⟨24 + ↑0⟩`, which keeps the faithfulness lemma's
ring atoms aligned).  `w_i = col (12+i)`, `d_i = col (20+i)`, `prod_i = col (24+i)`. -/
private def w0 : AffineTerm 32 := .input ⟨12, by omega⟩
private def w1 : AffineTerm 32 := .input ⟨13, by omega⟩
private def w2 : AffineTerm 32 := .input ⟨14, by omega⟩
private def w3 : AffineTerm 32 := .input ⟨15, by omega⟩
private def d0 : AffineTerm 32 := .input ⟨20, by omega⟩
private def d1 : AffineTerm 32 := .input ⟨21, by omega⟩
private def d2 : AffineTerm 32 := .input ⟨22, by omega⟩
private def d3 : AffineTerm 32 := .input ⟨23, by omega⟩
private def p0 : AffineTerm 32 := .input ⟨24, by omega⟩
private def p1 : AffineTerm 32 := .input ⟨25, by omega⟩
private def p2 : AffineTerm 32 := .input ⟨26, by omega⟩
private def p3 : AffineTerm 32 := .input ⟨27, by omega⟩

/-- C2 — the BILINEAR teeth: `prod_i − extmult_i`, `extmult` = `ExtElem::mul`
mod (X⁴−11) term-for-term with `QuantifiedAbsenceEmit.prodC*`. -/
private def prodAtom0 : QuadTerm 32 :=
  .add (.lin p0) (.neg (.add (.mul w0 d0)
    (.scale 11 (.add (.add (.mul w1 d3) (.mul w2 d2)) (.mul w3 d1)))))
private def prodAtom1 : QuadTerm 32 :=
  .add (.lin p1) (.neg (.add (.add (.mul w0 d1) (.mul w1 d0))
    (.scale 11 (.add (.mul w2 d3) (.mul w3 d2)))))
private def prodAtom2 : QuadTerm 32 :=
  .add (.lin p2) (.neg (.add (.add (.add (.mul w0 d2) (.mul w1 d1))
    (.mul w2 d0)) (.scale 11 (.mul w3 d3))))
private def prodAtom3 : QuadTerm 32 :=
  .add (.lin p3) (.neg (.add (.add (.add (.mul w0 d3) (.mul w1 d2))
    (.mul w2 d1)) (.mul w3 d0)))

def atomTerms : Fin 16 -> QuadTerm 32
  | ⟨0, _⟩ => diffAtom 0
  | ⟨1, _⟩ => diffAtom 1
  | ⟨2, _⟩ => diffAtom 2
  | ⟨3, _⟩ => diffAtom 3
  | ⟨4, _⟩ => prodAtom0
  | ⟨5, _⟩ => prodAtom1
  | ⟨6, _⟩ => prodAtom2
  | ⟨7, _⟩ => prodAtom3
  | ⟨8, _⟩ => sumAtom 0
  | ⟨9, _⟩ => sumAtom 1
  | ⟨10, _⟩ => sumAtom 2
  | ⟨11, _⟩ => sumAtom 3
  | ⟨12, _⟩ => boundAtom 0
  | ⟨13, _⟩ => boundAtom 1
  | ⟨14, _⟩ => boundAtom 2
  | ⟨15, _⟩ => boundAtom 3
  | ⟨_, _⟩ => .lin (.const 0)

/-- Source: the conjunction of all sixteen limb relations (four each of C1, C2,
C3, boundary).  A left-unfolded `andList` of sixteen atoms: 15 `and` nodes. -/
def source : Formula 16 :=
  andList
    [ .atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩, .atom ⟨2, by omega⟩, .atom ⟨3, by omega⟩
    , .atom ⟨4, by omega⟩, .atom ⟨5, by omega⟩, .atom ⟨6, by omega⟩, .atom ⟨7, by omega⟩
    , .atom ⟨8, by omega⟩, .atom ⟨9, by omega⟩, .atom ⟨10, by omega⟩, .atom ⟨11, by omega⟩
    , .atom ⟨12, by omega⟩, .atom ⟨13, by omega⟩, .atom ⟨14, by omega⟩, .atom ⟨15, by omega⟩ ]

def program : QuadProgram 8 24 16 := { atomTerms := atomTerms, source := source }

/- MEASURE — concrete generated resources of the compiled nonlinear descriptor.

These are MEASUREMENTS, not load-bearing proofs.  The SYMBOLIC, load-bearing
statement is `QuadProgram.descriptor_exact_resources` (proven, fast, kernel-clean,
pinned in `#assert_all_clean` and cited across the peephole tree): for any
`QuadProgram`, `piCount = pub`, `traceWidth = pub + sec + atoms + witnessCount
source`, and `constraints.length = pub + atoms + graphCost.equations + 1`.

The concrete integers for THIS program are read off below by COMPILED `Bool`
evaluation (`#guard`), which does NOT kernel-whnf-reduce the whole boolean-graph
fold.  The previous `by rfl` proofs DID force that fold through the kernel — the
source of the maxHeartbeats-1200000 band-aid and the file's slow build — while
proving nothing that any downstream theorem consumes (nothing does; grep the
tree).  Keeping them as `#guard` measurements retains the exact same checked
numbers with none of the whnf cost.

Generated: `piCount 8`, `traceWidth 95`, `103 constraints`; the source formula
has `witnessCount 47` and `graphCost.equations 78`.  Hand (`quantifiedAbsenceDesc`):
`traceWidth 28`, `20 constraints`, `piCount 8`.  The compiled form is larger
because it is a GENERAL front end carrying per-atom residual columns (16), inverse
witnesses, Boolean gates, and an accept gate — and it comes with whole-descriptor
`sound`, which the hand descriptor lacks. -/
#guard witnessCount program.source == 47
#guard program.source.graphCost.equations == 78
#guard (QuadProgram.descriptor program).piCount == 8
#guard (QuadProgram.descriptor program).traceWidth == 95
#guard (QuadProgram.descriptor program).constraints.length == 103

/-- Non-vacuous faithfulness of the BILINEAR tooth: atom 4's truth is EXACTLY the
BabyBear⁴ multiply limb-0 polynomial `prod₀ = w₀·d₀ + 11·(w₁·d₃ + w₂·d₂ + w₃·d₁)`
(the Lean analog of `QuantifiedAbsenceEmit.prodBody0_zero_iff`, here as an atom of
the compiled program rather than a hand gate). -/
theorem prod0_bilinear_faithful (input : Fin 32 -> BabyBear) :
    program.AtomTruth input ⟨4, by omega⟩ ↔
      input ⟨24, by omega⟩ =
        input ⟨12, by omega⟩ * input ⟨20, by omega⟩ +
          11 * (input ⟨13, by omega⟩ * input ⟨23, by omega⟩ +
                input ⟨14, by omega⟩ * input ⟨22, by omega⟩ +
                input ⟨15, by omega⟩ * input ⟨21, by omega⟩) := by
  have h4 : program.atomTerms ⟨4, by omega⟩ = prodAtom0 := rfl
  simp only [QuadProgram.AtomTruth, h4, prodAtom0, w0, w1, w2, w3,
    d0, d1, d2, d3, p0, QuadTerm.evalField, AffineTerm.evalField]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- The nonlinear compiler's soundness, instantiated at the quantified-absence
descriptor: every nonempty satisfying trace proves the sixteen limb relations on
the row inputs. -/
theorem program_sound (hash : List Int -> Int) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (QuadProgram.descriptor program) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    program.Holds (QuadProgram.rowInput program t) :=
  QuadProgram.sound hash program t hne hsat

end QuantifiedAbsence

#assert_all_clean [
  AffineTerm.fieldWindow_toWindowAt,
  AffineTerm.toWindowAt_degree,
  QuadTerm.fieldWindow_toWindowAt,
  QuadTerm.toWindowAt_degree,
  QuadProgram.descriptor_exact_resources,
  QuadProgram.descriptor_constraint_low_degree,
  QuadProgram.atom_link_field,
  QuadProgram.sound,
  QuadProgram.public_sound,
  QuantifiedAbsence.prod0_bilinear_faithful,
  QuantifiedAbsence.program_sound,
  graphConstraintsAt_length,
  descriptor_exact_resources,
  descriptor_constraint_low_degree,
  public_pin_field,
  atom_link_field,
  graph_nodes_hold,
  accepts_output_one,
  sound,
  public_sound,
  zero_witness_gate,
  evalBit_isBit,
  evalBit_one_iff,
  fieldWitness_length,
  field_output_of_matches,
  field_nodes_valid_of_matches,
  gate_holds_of_field_zero,
  node_constraints_hold_of_field_valid,
  canonical_nodes_hold,
  canonical_atom_link_holds,
  canonical_public_pin_holds,
  canonical_accept_holds,
  canonical_complete,
  canonical_iff,
  checkArtifact_spec,
  checkArtifact_certify,
  InterchainRung.program_holds_iff,
  InterchainRung.encoded_program_exact,
  InterchainRung.modulus_tag_alias_frontier,
  InterchainRung.modulus_payload_alias_frontier,
  InterchainRung.exact_live_ledger,
  InterchainRung.descriptor_bytes_exact,
  InterchainRung.live_sound,
  InterchainRung.live_complete
]

end Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
