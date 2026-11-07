/-
# Dregg2.Circuit.PeepholePassCertified — the peephole zero-test elision as a CERTIFIED passive pass.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. The source descriptor is the one the
Lean compiler `TypedLinearPredicateDescriptorIR2.descriptor` emits; the target descriptor is
produced BY APPLYING THE REWRITE to that exact `EffectVmDescriptor2` value (same `name`,
`traceWidth`, `piCount`, `tables`, `hashSites`, `ranges`; only the constraint list changes, and
the surviving constraints are the SAME objects, at the SAME column addresses). Nothing here is a
separately reconstructed look-alike descriptor.

## What this module closes

`PeepholeZeroTestElision` measured the R1 rule and named its wall precisely: there was no
`PassiveDescriptorOptimization` instance for the rewrite, only a resource stand-in whose
`Satisfied2`-equivalence with the emitted descriptor was never stated. This module supplies the
instance and both contract legs.

The rule (design DESIGN-peephole-layout-optimizer.md §2, R1), stated on the emitted geometry.
For a program whose source formula is a root conjunction with an asserted atom on the left,

    p.source = (atom a) ∧ rest

the emitted descriptor carries, at `B = boolBase pub sec atoms`:

* `zeroTest a.val B (B+1)`  — 3 quadratic gates, 2 witness columns (`out = B`, `inv = B+1`);
* the whole materialization of `rest` at base `B+2`;
* `and (col B) (outputAt (B+2) rest) (B+2+W)` — 2 gates, 1 witness column (`W = witnessCount rest`);
* the accept gate `col (B+2+W) = 1`.

Acceptance forces the and-tree output to 1, hence the asserted atom's bit to 1, hence its residual
to 0. R1 therefore replaces those 5 gates by the SINGLE degree-1 gate `col a.val = 0` and re-points
the accept gate at `rest`'s output. Columns `B`, `B+1`, `B+2+W` are left unread; E1's derived
dead-column deletion removes them.

## The two contract legs, and what each one required

* `rw_completeness` (`CompletenessPreservation`) — the easy direction; `toTarget = id`. It has to
  DERIVE `col a.val = 0` and `outputAt (B+2) rest = 1` from the source's bit/zero/and/accept
  equations, which is the field argument `b(b-1)=0 ∧ b·y=1 ⟹ b=1 ⟹ x = x·b = 0`.

* `rw_security` (`SecurityRefinement`) — the load-bearing direction, and the one the prior lane
  named as undelivered: an accepting TARGET trace has NOTHING in columns `B`, `B+1`, `B+2+W`, so the
  elided postorder witness region must be REBUILT as canonical values (design §5). `rebuildRow`
  does exactly that — `out := 1`, `inv := 0`, and-spine output `:= 1` — on EVERY row, and
  `rw_security_row` proves the five elided source gates plus the accept gate hold on the rebuilt
  row, while every surviving constraint (public pins, atom links, `rest`'s whole materialization)
  is untouched. The untouchedness is not asserted: §1 proves a
  column-range discipline for `nodesAt`/`outputAt` (`nodesAt_nodeCols`, `outputAt_wireCols`) and a
  gate-level congruence (`node_holdsAt_congr`), so `rest`'s materialization provably cannot read the
  three rebuilt columns.

Composition with E1 is the framework's own `preservation_comp` over
`EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation`.

## Named residuals — what is NOT proven here (no `sorry`, no stand-in)

* ITERATION. The rule fires once, at the root. The pilot's source is
  `atom0 ∧ (atom1 ∧ ⋀_j (b_j=0 ∨ b_j=1))`, so recovering BOTH asserted atoms needs R1 applied to the
  ALREADY-REWRITTEN descriptor, whose constraint list is no longer of the form `descriptor p'`. That
  generalization (an R1 site over an arbitrary untouched constraint prefix) is the next step; it is
  not attempted here, and no theorem below claims the pilot's two-atom recovery.
* The E1 composition below takes `transitionCeilingOk (rwDescriptor …) floor = true` as an explicit
  hypothesis. It is a decidable Bool check on the rewritten descriptor; discharging it for a
  concrete large descriptor is a kernel reduction this module deliberately does not run.
* Column DEATH (that `B`, `B+1`, `B+2+W` are unread in the target) is not stated as a theorem here;
  E1 derives its own kill-set from the descriptor (`deadColsE1`), so the composition does not
  depend on a hand-supplied kill-set.

Standalone and additive: imports the contracts module and the typed front end, changes neither.
-/
import Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization
import Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

namespace Dregg2.Circuit.PeepholePassCertified

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node witnessCount outputAt nodesAt gate bitBody bitBody_eq subW negW)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

set_option autoImplicit false

/-! ## 0. The gate denotation, as a divisibility statement.

Every constraint this module manipulates is a `gate` (`onTransition := false`), so its meaning is
flag- and table-independent. -/

theorem gate_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (body : WindowExpr) :
    (gate body).holdsAt hash tf env isFirst isLast ↔
      body.eval env ≡ 0 [ZMOD 2013265921] := Iff.rfl

theorem gate_dvd_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (body : WindowExpr) :
    (gate body).holdsAt hash tf env isFirst isLast ↔
      (2013265921 : ℤ) ∣ body.eval env := by
  rw [gate_holdsAt_iff, Int.modEq_zero_iff_dvd]

theorem gate_of_eval_zero {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv}
    {isFirst isLast : Bool} {body : WindowExpr} (h : body.eval env = 0) :
    (gate body).holdsAt hash tf env isFirst isLast := by
  rw [gate_dvd_iff, h]
  exact dvd_zero _

/-- The `ZMod` bridge used by the completeness leg's bit argument. -/
theorem dvd_iff_cast_zero (z : ℤ) :
    (2013265921 : ℤ) ∣ z ↔ ((z : ZMod 2013265921) = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem one_ne_zero_babybear : (1 : ZMod 2013265921) ≠ 0 := by
  intro h
  have hdvd : (2013265921 : ℤ) ∣ (1 : ℤ) := by
    rw [dvd_iff_cast_zero]
    exact_mod_cast h
  have := Int.le_of_dvd (by norm_num) hdvd
  norm_num at this

/-! ## 1. Column-read discipline for the materialized Boolean graph.

The rebuild map overwrites three columns.  Nothing may silently depend on them, so the columns a
node and a formula's output wire can read are bounded HERE, by induction over the formula — not
asserted. -/

/-- The trace columns a wire reads. -/
def wireCols : Wire → List Nat
  | .zero => []
  | .one => []
  | .col c => [c]

/-- The trace columns a materialized node reads or writes. -/
def nodeCols : Node → List Nat
  | .zeroTest x out inv => [x, out, inv]
  | .not input out => wireCols input ++ [out]
  | .and left right out => wireCols left ++ wireCols right ++ [out]
  | .or left right out => wireCols left ++ wireCols right ++ [out]

theorem wire_eval_congr {env env' : VmRowEnv} (w : Wire)
    (h : ∀ c ∈ wireCols w, env'.loc c = env.loc c) :
    w.expr.eval env' = w.expr.eval env := by
  cases w with
  | zero => rfl
  | one => rfl
  | col c =>
      have := h c (by simp [wireCols])
      simpa [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr,
        WindowExpr.eval] using this

/-- A formula's output wire lives strictly inside its own witness block. -/
theorem outputAt_wireCols {n : Nat} (base : Nat)
    (p : Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula n) :
    ∀ c ∈ wireCols (outputAt base p), base ≤ c ∧ c < base + witnessCount p := by
  cases p with
  | atom x =>
      intro c hc
      simp [outputAt, wireCols] at hc
      subst hc
      constructor
      · exact Nat.le_refl _
      · simp [witnessCount]
  | top => intro c hc; simp [outputAt, wireCols] at hc
  | bot => intro c hc; simp [outputAt, wireCols] at hc
  | not p =>
      intro c hc
      simp [outputAt, wireCols] at hc
      subst hc
      simp [witnessCount]
  | and p q =>
      intro c hc
      simp [outputAt, wireCols] at hc
      subst hc
      simp [witnessCount]
      omega
  | or p q =>
      intro c hc
      simp [outputAt, wireCols] at hc
      subst hc
      simp [witnessCount]
      omega

/-- Every node a formula materializes at `base` reads only atom-residual columns (`< n`) and
columns inside its own witness block `[base, base + witnessCount p)`. -/
theorem nodesAt_nodeCols {n : Nat} (base : Nat)
    (p : Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula n) :
    ∀ node ∈ nodesAt base p, ∀ c ∈ nodeCols node,
      c < n ∨ (base ≤ c ∧ c < base + witnessCount p) := by
  induction p generalizing base with
  | atom x =>
      intro node hnode c hc
      simp only [nodesAt, List.mem_singleton] at hnode
      subst hnode
      simp [nodeCols] at hc
      rcases hc with rfl | rfl | rfl
      · exact Or.inl x.isLt
      · exact Or.inr ⟨Nat.le_refl _, by simp [witnessCount]⟩
      · exact Or.inr ⟨by omega, by simp [witnessCount]⟩
  | top => intro node hnode; simp [nodesAt] at hnode
  | bot => intro node hnode; simp [nodesAt] at hnode
  | not p ih =>
      intro node hnode c hc
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with hchild | rfl
      · rcases ih base node hchild c hc with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by simp [witnessCount]; omega⟩
      · simp only [nodeCols, List.mem_append, List.mem_singleton] at hc
        rcases hc with hw | rfl
        · rcases outputAt_wireCols base p c hw with ⟨h1, h2⟩
          exact Or.inr ⟨h1, by simp [witnessCount]; omega⟩
        · exact Or.inr ⟨by omega, by simp [witnessCount]⟩
  | and p q ihp ihq =>
      intro node hnode c hc
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with (hp | hq) | rfl
      · rcases ihp base node hp c hc with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by simp [witnessCount] at h ⊢; omega⟩
      · rcases ihq (base + witnessCount p) node hq c hc with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by simp [witnessCount] at h ⊢; omega⟩
      · simp only [nodeCols, List.mem_append, List.mem_singleton] at hc
        rcases hc with (hl | hr) | rfl
        · rcases outputAt_wireCols base p c hl with ⟨h1, h2⟩
          exact Or.inr ⟨h1, by simp [witnessCount]; omega⟩
        · rcases outputAt_wireCols (base + witnessCount p) q c hr with ⟨h1, h2⟩
          exact Or.inr ⟨by omega, by simp [witnessCount] at h2 ⊢; omega⟩
        · exact Or.inr ⟨by omega, by simp [witnessCount]; omega⟩
  | or p q ihp ihq =>
      intro node hnode c hc
      simp only [nodesAt, List.mem_append, List.mem_singleton] at hnode
      rcases hnode with (hp | hq) | rfl
      · rcases ihp base node hp c hc with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by simp [witnessCount] at h ⊢; omega⟩
      · rcases ihq (base + witnessCount p) node hq c hc with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by simp [witnessCount] at h ⊢; omega⟩
      · simp only [nodeCols, List.mem_append, List.mem_singleton] at hc
        rcases hc with (hl | hr) | rfl
        · rcases outputAt_wireCols base p c hl with ⟨h1, h2⟩
          exact Or.inr ⟨h1, by simp [witnessCount]; omega⟩
        · rcases outputAt_wireCols (base + witnessCount p) q c hr with ⟨h1, h2⟩
          exact Or.inr ⟨by omega, by simp [witnessCount] at h2 ⊢; omega⟩
        · exact Or.inr ⟨by omega, by simp [witnessCount]; omega⟩

/-- A node's emitted constraints depend on the row ONLY through `nodeCols`. -/
theorem node_holdsAt_congr (hash : List ℤ → ℤ) (tf : TraceFamily)
    (env env' : VmRowEnv) (isFirst isLast : Bool) (node : Node)
    (hagree : ∀ c ∈ nodeCols node, env'.loc c = env.loc c)
    (h : ∀ c ∈ node.constraints, c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ node.constraints, c.holdsAt hash tf env' isFirst isLast := by
  cases node with
  | zeroTest x out inv =>
      have hx : env'.loc x = env.loc x := hagree x (by simp [nodeCols])
      have ho : env'.loc out = env.loc out := hagree out (by simp [nodeCols])
      have hi : env'.loc inv = env.loc inv := hagree inv (by simp [nodeCols])
      intro c hc
      have hh := h c hc
      have hc' := hc
      simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints] at hc'
      clear hc
      rcases hc' with rfl | rfl | rfl <;>
        rw [gate_dvd_iff] at hh ⊢ <;>
        simpa [bitBody_eq, Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr,
          WindowExpr.eval, hx, ho, hi] using hh
  | not input out =>
      have hw : input.expr.eval env' = input.expr.eval env :=
        wire_eval_congr input (fun c hc => hagree c (by simp [nodeCols, hc]))
      have ho : env'.loc out = env.loc out := hagree out (by simp [nodeCols])
      intro c hc
      have hh := h c hc
      have hc' := hc
      simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints] at hc'
      clear hc
      rcases hc' with rfl | rfl
      · rw [gate_dvd_iff] at hh ⊢
        simpa [bitBody_eq, Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr, WindowExpr.eval, ho] using hh
      · rw [gate_dvd_iff] at hh ⊢
        simp only [WindowExpr.eval, ho, hw]
        simp only [WindowExpr.eval] at hh
        exact hh
  | and left right out =>
      have hl : left.expr.eval env' = left.expr.eval env :=
        wire_eval_congr left (fun c hc => hagree c (by simp [nodeCols, hc]))
      have hr : right.expr.eval env' = right.expr.eval env :=
        wire_eval_congr right (fun c hc => hagree c (by simp [nodeCols, hc]))
      have ho : env'.loc out = env.loc out := hagree out (by simp [nodeCols])
      intro c hc
      have hh := h c hc
      have hc' := hc
      simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints] at hc'
      clear hc
      rcases hc' with rfl | rfl
      · rw [gate_dvd_iff] at hh ⊢
        simpa [bitBody_eq, Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr, WindowExpr.eval, ho] using hh
      · rw [gate_dvd_iff] at hh ⊢
        simp only [subW, negW, WindowExpr.eval, ho, hl, hr]
        simp only [subW, negW, WindowExpr.eval] at hh
        exact hh
  | or left right out =>
      have hl : left.expr.eval env' = left.expr.eval env :=
        wire_eval_congr left (fun c hc => hagree c (by simp [nodeCols, hc]))
      have hr : right.expr.eval env' = right.expr.eval env :=
        wire_eval_congr right (fun c hc => hagree c (by simp [nodeCols, hc]))
      have ho : env'.loc out = env.loc out := hagree out (by simp [nodeCols])
      intro c hc
      have hh := h c hc
      have hc' := hc
      simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints] at hc'
      clear hc
      rcases hc' with rfl | rfl
      · rw [gate_dvd_iff] at hh ⊢
        simpa [bitBody_eq, Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr, WindowExpr.eval, ho] using hh
      · rw [gate_dvd_iff] at hh ⊢
        simp only [subW, negW, WindowExpr.eval, ho, hl, hr]
        simp only [subW, negW, WindowExpr.eval] at hh
        exact hh

/-- Affine atom terms read only the raw-input block `[rawBase, rawBase + m)`. -/
theorem toWindowAt_eval_congr {m : Nat} {env env' : VmRowEnv} (rawB : Nat)
    (term : AffineTerm m)
    (h : ∀ i : Fin m, env'.loc (rawB + i.val) = env.loc (rawB + i.val)) :
    (term.toWindowAt rawB).eval env' = (term.toWindowAt rawB).eval env := by
  induction term with
  | const k => rfl
  | input i => simpa [AffineTerm.toWindowAt, WindowExpr.eval] using h i
  | neg x ih => simp [AffineTerm.toWindowAt, WindowExpr.eval, ih]
  | add x y ihx ihy => simp [AffineTerm.toWindowAt, WindowExpr.eval, ihx, ihy]
  | scale k x ih => simp [AffineTerm.toWindowAt, WindowExpr.eval, ih]


/-! ## 2. The R1 site: the emitted source descriptor and the rewritten target.

`rootProgram` is an ordinary `Program`; `descriptor (rootProgram …)` is the ordinary emitted
descriptor.  `rwDescriptor` is that SAME record with only its constraint list rewritten — every
surviving constraint is the same object at the same column, and the trace geometry is untouched. -/

section Site

variable {pub sec atoms : Nat}

/-- A typed program whose Boolean source is a root conjunction with an asserted atom on the left:
the exact shape R1 fires on. -/
def rootProgram (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms)
    (rest : Formula atoms) : Program pub sec atoms :=
  { atomTerms := terms, source := .and (.atom a) rest }

/-- The surviving materialization of the conjunction's right operand, at its emitted base. -/
def midNodes (pub sec atoms : Nat) (rest : Formula atoms) : List Node :=
  nodesAt (boolBase pub sec atoms + 2) rest

def midConstraints (pub sec atoms : Nat) (rest : Formula atoms) : List VmConstraint2 :=
  (midNodes pub sec atoms rest).flatMap Node.constraints

/-- The right operand's output wire. -/
def restOut (pub sec atoms : Nat) (rest : Formula atoms) : Wire :=
  outputAt (boolBase pub sec atoms + 2) rest

/-- R1's replacement for the elided zero test: the single degree-1 gate `col a = 0`. -/
def directGate (a : Fin atoms) : VmConstraint2 := gate (.loc a.val)

/-- The accept gate, re-pointed at the right operand's output. -/
def restAccept (pub sec atoms : Nat) (rest : Formula atoms) : VmConstraint2 :=
  gate (subW (restOut pub sec atoms rest).expr (.const 1))

def rwConstraints (pub sec atoms : Nat) (terms : Fin atoms → AffineTerm (pub + sec))
    (a : Fin atoms) (rest : Formula atoms) : List VmConstraint2 :=
  publicPins pub sec atoms ++ atomLinks (rootProgram terms a rest) ++ [directGate a] ++
    midConstraints pub sec atoms rest ++ [restAccept pub sec atoms rest]

/-- THE REWRITTEN DESCRIPTOR — the emitted record with only its constraints rewritten. -/
def rwDescriptor (pub sec atoms : Nat) (terms : Fin atoms → AffineTerm (pub + sec))
    (a : Fin atoms) (rest : Formula atoms) : EffectVmDescriptor2 :=
  { descriptor (rootProgram terms a rest) with
    constraints := rwConstraints pub sec atoms terms a rest }

variable (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms) (rest : Formula atoms)

theorem rwDescriptor_traceWidth :
    (rwDescriptor pub sec atoms terms a rest).traceWidth =
      (descriptor (rootProgram terms a rest)).traceWidth := rfl

theorem rwDescriptor_piCount :
    (rwDescriptor pub sec atoms terms a rest).piCount =
      (descriptor (rootProgram terms a rest)).piCount := rfl

/-- The emitted node list at the root, split at the R1 site. -/
theorem src_nodesAt :
    nodesAt (boolBase pub sec atoms) (rootProgram terms a rest).source =
      [Node.zeroTest a.val (boolBase pub sec atoms) (boolBase pub sec atoms + 1)] ++
        midNodes pub sec atoms rest ++
        [Node.and (.col (boolBase pub sec atoms)) (restOut pub sec atoms rest)
          (boolBase pub sec atoms + 2 + witnessCount rest)] := rfl

theorem src_accept :
    acceptConstraintAt (rootProgram terms a rest) =
      gate (subW (WindowExpr.loc (boolBase pub sec atoms + 2 + witnessCount rest))
        (.const 1)) := rfl

theorem atoms_le_boolBase : atoms ≤ boolBase pub sec atoms := by
  simp [boolBase]

/-! ### Membership plumbing -/

theorem zt_mem_src :
    Node.zeroTest a.val (boolBase pub sec atoms) (boolBase pub sec atoms + 1) ∈
      nodesAt (boolBase pub sec atoms) (rootProgram terms a rest).source := by
  rw [src_nodesAt]; simp

theorem andNode_mem_src :
    Node.and (.col (boolBase pub sec atoms)) (restOut pub sec atoms rest)
        (boolBase pub sec atoms + 2 + witnessCount rest) ∈
      nodesAt (boolBase pub sec atoms) (rootProgram terms a rest).source := by
  rw [src_nodesAt]; simp

theorem mid_mem_src {node : Node} (h : node ∈ midNodes pub sec atoms rest) :
    node ∈ nodesAt (boolBase pub sec atoms) (rootProgram terms a rest).source := by
  rw [src_nodesAt]; simp [h]

theorem mid_constraint_mem_src {c : VmConstraint2}
    (h : c ∈ midConstraints pub sec atoms rest) :
    c ∈ (descriptor (rootProgram terms a rest)).constraints := by
  simp only [midConstraints, List.mem_flatMap] at h
  obtain ⟨node, hnode, hc⟩ := h
  exact graph_node_constraint_mem _ node (mid_mem_src terms a rest hnode) c hc

theorem pin_mem_rw {c : VmConstraint2} (h : c ∈ publicPins pub sec atoms) :
    c ∈ (rwDescriptor pub sec atoms terms a rest).constraints := by
  simp [rwDescriptor, rwConstraints, h]

theorem link_mem_rw {c : VmConstraint2} (h : c ∈ atomLinks (rootProgram terms a rest)) :
    c ∈ (rwDescriptor pub sec atoms terms a rest).constraints := by
  simp [rwDescriptor, rwConstraints, h]

theorem directGate_mem_rw :
    directGate a ∈ (rwDescriptor pub sec atoms terms a rest).constraints := by
  simp [rwDescriptor, rwConstraints]

theorem mid_mem_rw {c : VmConstraint2} (h : c ∈ midConstraints pub sec atoms rest) :
    c ∈ (rwDescriptor pub sec atoms terms a rest).constraints := by
  simp [rwDescriptor, rwConstraints, h]

theorem restAccept_mem_rw :
    restAccept pub sec atoms rest ∈
      (rwDescriptor pub sec atoms terms a rest).constraints := by
  simp [rwDescriptor, rwConstraints]

/-! ## 3. Exact cost recovery, in closed form.

R1 removes the 3 zero-test gates and the 2 and-spine gates and adds one degree-1 gate and one
re-pointed accept gate: exactly `-4` constraints and `-5` nonlinear multiplications. -/

def nodeMults (nodes : List Node) : Nat := (nodes.map Node.multiplications).sum

theorem graphConstraints_split :
    (graphConstraintsAt (rootProgram terms a rest)).length =
      (midConstraints pub sec atoms rest).length + 5 := by
  unfold graphConstraintsAt
  rw [src_nodesAt]
  simp [List.flatMap_append, midConstraints, midNodes,
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints]

/-- THE COST LEG: the rewritten descriptor carries exactly four fewer constraints. -/
theorem rw_constraints_recovery :
    (rwDescriptor pub sec atoms terms a rest).constraints.length + 4 =
      (descriptor (rootProgram terms a rest)).constraints.length := by
  simp only [rwDescriptor, rwConstraints, descriptor, List.length_append, List.length_cons,
    List.length_nil]
  rw [graphConstraints_split]
  omega

/-- The elided gates were the only nonlinear ones R1 touches: `-5` multiplications. -/
theorem rw_multiplications_recovery :
    nodeMults (midNodes pub sec atoms rest) + 5 =
      nodeMults (nodesAt (boolBase pub sec atoms) (rootProgram terms a rest).source) := by
  unfold nodeMults
  rw [src_nodesAt]
  simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.multiplications]
  omega

/-! ## 4. Public ABI: the pass moves no PI binding. -/

@[simp] theorem bindingSlot?_gate (b : WindowExpr) : bindingSlot? (gate b) = none := rfl

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

theorem publicBindingSlots_src :
    publicBindingSlots (descriptor (rootProgram terms a rest)) =
      (publicPins pub sec atoms).filterMap bindingSlot? := by
  simp [publicBindingSlots, descriptor, List.filterMap_append, atomLinks_bindingSlot_nil,
    graphConstraintsAt, nodes_bindingSlot_nil, acceptConstraintAt]

theorem publicBindingSlots_rw :
    publicBindingSlots (rwDescriptor pub sec atoms terms a rest) =
      (publicPins pub sec atoms).filterMap bindingSlot? := by
  simp only [publicBindingSlots, rwDescriptor, rwConstraints, List.filterMap_append,
    atomLinks_bindingSlot_nil, midConstraints, nodes_bindingSlot_nil]
  simp [directGate, restAccept]

/-! ## 5. The witness rebuild — the elided postorder region, as canonical values.

An accepting TARGET trace says nothing about columns `B`, `B+1`, `B+2+W`; R1 deleted every
constraint that mentioned them.  `rebuildRow` restores exactly the canonical postorder witness of
the elided region: the asserted atom's `out` bit is `1`, its `inv` witness is `0` (a legal inverse
witness for the residual `0`), and the collapsed and-spine output is `1`. -/

def rebuildRow (B W : Nat) (row : Assignment) : Assignment :=
  fun c => if c = B then 1 else if c = B + 1 then 0 else if c = B + 2 + W then 1 else row c

def rebuildTrace (B W : Nat) (t : VmTrace) : VmTrace :=
  { rows := t.rows.map (rebuildRow B W), pub := t.pub, tf := t.tf }

theorem rebuildRow_untouched (B W : Nat) (row : Assignment) {c : Nat}
    (h1 : c ≠ B) (h2 : c ≠ B + 1) (h3 : c ≠ B + 2 + W) :
    rebuildRow B W row c = row c := by
  simp [rebuildRow, h1, h2, h3]

theorem rebuildRow_base (B W : Nat) (row : Assignment) : rebuildRow B W row B = 1 := by
  simp [rebuildRow]

theorem rebuildRow_inv (B W : Nat) (row : Assignment) : rebuildRow B W row (B + 1) = 0 := by
  simp [rebuildRow]

theorem rebuildRow_top (B W : Nat) (row : Assignment) :
    rebuildRow B W row (B + 2 + W) = 1 := by
  have h1 : B + 2 + W ≠ B := by omega
  have h2 : B + 2 + W ≠ B + 1 := by omega
  simp [rebuildRow, h1, h2]

theorem rebuildTrace_rows_length (B W : Nat) (t : VmTrace) :
    (rebuildTrace B W t).rows.length = t.rows.length := by simp [rebuildTrace]

theorem rebuildTrace_loc (B W : Nat) (t : VmTrace) (i : Nat) (h : i < t.rows.length) :
    (envAt (rebuildTrace B W t) i).loc = rebuildRow B W ((envAt t i).loc) := by
  simp only [envAt, rebuildTrace]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

theorem rebuildTrace_pub (B W : Nat) (t : VmTrace) (i : Nat) :
    (envAt (rebuildTrace B W t) i).pub = (envAt t i).pub := rfl

end Site


/-! ## 6. Carrier bookkeeping: neither descriptor declares a memory or map op. -/

section Carriers

variable {pub sec atoms : Nat}

private theorem node_memOp_nil (node : Node) :
    node.constraints.filterMap
      (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  cases node <;> rfl

private theorem node_mapOp_nil (node : Node) :
    node.constraints.filterMap
      (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  cases node <;> rfl

private theorem nodes_memOp_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap
      (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons n ns ih => simp [List.flatMap_cons, List.filterMap_append, node_memOp_nil, ih]

private theorem nodes_mapOp_nil (nodes : List Node) :
    (nodes.flatMap Node.constraints).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  induction nodes with
  | nil => rfl
  | cons n ns ih => simp [List.flatMap_cons, List.filterMap_append, node_mapOp_nil, ih]

variable (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms) (rest : Formula atoms)

theorem memOps_rw_nil : memOpsOf (rwDescriptor pub sec atoms terms a rest) = [] := by
  simp [memOpsOf, rwDescriptor, rwConstraints, List.filterMap_append, publicPins,
    atomLinks, atomLink, gate, directGate, restAccept, midConstraints]
  intro c n _ hc
  obtain ⟨body, rfl, _⟩ :=
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.node_constraint_degree n c hc
  rfl

theorem mapOps_rw_nil : mapOpsOf (rwDescriptor pub sec atoms terms a rest) = [] := by
  simp [mapOpsOf, rwDescriptor, rwConstraints, List.filterMap_append, publicPins,
    atomLinks, atomLink, gate, directGate, restAccept, midConstraints]
  intro c n _ hc
  obtain ⟨body, rfl, _⟩ :=
    Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.node_constraint_degree n c hc
  rfl

end Carriers

theorem memLog_nil_of_memOps_nil {d : EffectVmDescriptor2} (h : memOpsOf d = [])
    (t : VmTrace) : memLog d t = [] := by
  simp [memLog, h]

theorem mapLog_nil_of_mapOps_nil {d : EffectVmDescriptor2} (h : mapOpsOf d = [])
    (t : VmTrace) : mapLog d t = [] := by
  simp [mapLog, h]

/-- Both descriptors are memory-free, hash-site-free and range-free, so every global
`Satisfied2` leg transports verbatim and the whole content of a pass is its per-row constraint
obligation. -/
theorem satisfied2_transfer {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {src tgt : EffectVmDescriptor2} {t u : VmTrace}
    (hsrcMem : memOpsOf src = []) (hsrcMap : mapOpsOf src = [])
    (htgtMem : memOpsOf tgt = []) (htgtMap : mapOpsOf tgt = [])
    (hhash : src.hashSites = []) (hrange : src.ranges = [])
    (htf : u.tf = t.tf)
    (hsat : Satisfied2 hash tgt minit mfin maddrs t)
    (hrow : ∀ i < u.rows.length, ∀ c ∈ src.constraints,
      c.holdsAt hash u.tf (envAt u i) (i == 0) (i + 1 == u.rows.length)) :
    Satisfied2 hash src minit mfin maddrs u := by
  refine ⟨hrow, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hhash]; trivial
  · intro i hi r hr; rw [hrange] at hr; cases hr
  · intro op hop; rw [memLog_nil_of_memOps_nil hsrcMem] at hop; cases hop
  · have h := hsat.memDisciplined
    rw [memLog_nil_of_memOps_nil htgtMem] at h
    rw [memLog_nil_of_memOps_nil hsrcMem]
    exact h
  · have h := hsat.memBalanced
    rw [memLog_nil_of_memOps_nil htgtMem] at h
    rw [memLog_nil_of_memOps_nil hsrcMem]
    exact h
  · have h := hsat.memTableFaithful
    rw [memLog_nil_of_memOps_nil htgtMem] at h
    rw [memLog_nil_of_memOps_nil hsrcMem, htf]
    exact h
  · have h := hsat.mapTableFaithful
    rw [mapLog_nil_of_mapOps_nil htgtMap] at h
    rw [mapLog_nil_of_mapOps_nil hsrcMap, htf]
    exact h

/-! ## 7. The two per-row contract legs. -/

@[simp] theorem wire_col_expr (c : Nat) :
    (Wire.col c).expr = WindowExpr.loc c := rfl

section Rows

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms) (rest : Formula atoms)

/-- THE SECURITY LEG, per row.  Every source constraint holds on the REBUILT row: the four gates
R1 elided are discharged by the canonical witness values, and every surviving constraint is
provably blind to the three rebuilt columns. -/
theorem rw_security_row (hash : List ℤ → ℤ) (tf : TraceFamily) (isFirst isLast : Bool)
    (env env' : VmRowEnv)
    (hpub : env'.pub = env.pub)
    (hagree : ∀ c, c ≠ boolBase pub sec atoms → c ≠ boolBase pub sec atoms + 1 →
      c ≠ boolBase pub sec atoms + 2 + witnessCount rest → env'.loc c = env.loc c)
    (hB : env'.loc (boolBase pub sec atoms) = 1)
    (hB1 : env'.loc (boolBase pub sec atoms + 1) = 0)
    (hTop : env'.loc (boolBase pub sec atoms + 2 + witnessCount rest) = 1)
    (htgt : ∀ c ∈ (rwDescriptor pub sec atoms terms a rest).constraints,
      c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ (descriptor (rootProgram terms a rest)).constraints,
      c.holdsAt hash tf env' isFirst isLast := by
  have hlow : ∀ k, k < boolBase pub sec atoms → env'.loc k = env.loc k := by
    intro k hk
    exact hagree k (by omega) (by omega) (by omega)
  have hatomcol : ∀ b : Fin atoms, env'.loc b.val = env.loc b.val := by
    intro b
    exact hlow b.val (lt_of_lt_of_le b.isLt atoms_le_boolBase)
  have hraw : ∀ i : Fin (pub + sec),
      env'.loc (rawBase atoms + i.val) = env.loc (rawBase atoms + i.val) := by
    intro i
    refine hlow _ ?_
    have hi := i.isLt
    simp only [rawBase, boolBase]
    omega
  intro c hc
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((hpin | hlink) | hgraph) | rfl
  · have hh := htgt c (pin_mem_rw terms a rest hpin)
    simp only [publicPins, List.mem_map] at hpin
    obtain ⟨i, hi, rfl⟩ := hpin
    have hil : i < pub := List.mem_range.mp hi
    have hcol : env'.loc (rawBase atoms + i) = env.loc (rawBase atoms + i) := by
      refine hlow _ ?_
      simp only [rawBase, boolBase]
      omega
    simp only [VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at hh ⊢
    intro hf
    rw [hcol, hpub]
    exact hh hf
  · have hh := htgt c (link_mem_rw terms a rest hlink)
    simp only [atomLinks, List.mem_map] at hlink
    obtain ⟨b, _, rfl⟩ := hlink
    simp only [atomLink] at hh ⊢
    rw [gate_dvd_iff] at hh ⊢
    have hbody : (atomLinkBody (rootProgram terms a rest) b).eval env'
        = (atomLinkBody (rootProgram terms a rest) b).eval env := by
      simp only [atomLinkBody, subW, negW, WindowExpr.eval]
      rw [hatomcol b, toWindowAt_eval_congr (rawBase atoms) _ hraw]
    rw [hbody]
    exact hh
  · simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
    obtain ⟨node, hnode, hcn⟩ := hgraph
    rw [src_nodesAt] at hnode
    simp only [List.mem_append, List.mem_singleton] at hnode
    rcases hnode with (rfl | hmid) | rfl
    · have hcn' := hcn
      simp only [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints,
        List.mem_cons, List.not_mem_nil, or_false] at hcn'
      rcases hcn' with rfl | rfl | rfl
      · exact gate_of_eval_zero (by simp [bitBody_eq, WindowExpr.eval, hB])
      · have hd := htgt (directGate a) (directGate_mem_rw terms a rest)
        simp only [directGate] at hd
        rw [gate_dvd_iff] at hd ⊢
        simp only [WindowExpr.eval] at hd ⊢
        rw [hB, hatomcol a]
        simpa using hd
      · exact gate_of_eval_zero (by simp [WindowExpr.eval, hB, hB1])
    · refine node_holdsAt_congr hash tf env env' isFirst isLast node ?_ ?_ c hcn
      · intro k hk
        rcases nodesAt_nodeCols (boolBase pub sec atoms + 2) rest node hmid k hk with h | h
        · exact hlow k (lt_of_lt_of_le h atoms_le_boolBase)
        · exact hagree k (by omega) (by omega) (by omega)
      · intro c' hc'
        refine htgt c' (mid_mem_rw terms a rest ?_)
        simp only [midConstraints]
        exact List.mem_flatMap.mpr ⟨node, hmid, hc'⟩
    · have hout : (restOut pub sec atoms rest).expr.eval env'
          = (restOut pub sec atoms rest).expr.eval env := by
        refine wire_eval_congr _ ?_
        intro k hk
        rcases outputAt_wireCols (boolBase pub sec atoms + 2) rest k hk with ⟨h1, h2⟩
        exact hagree k (by omega) (by omega) (by omega)
      have hcn' := hcn
      simp only [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints,
        List.mem_cons, List.not_mem_nil, or_false] at hcn'
      rcases hcn' with rfl | rfl
      · exact gate_of_eval_zero (by simp [bitBody_eq, WindowExpr.eval, hTop])
      · have hra := htgt (restAccept pub sec atoms rest) (restAccept_mem_rw terms a rest)
        simp only [restAccept] at hra
        rw [gate_dvd_iff] at hra ⊢
        simp only [subW, negW, wire_col_expr, WindowExpr.eval] at hra ⊢
        rw [hout, hTop, hB]
        have hcalc : (1 : ℤ) + (-1) * (1 * (restOut pub sec atoms rest).expr.eval env)
            = -((restOut pub sec atoms rest).expr.eval env + (-1) * 1) := by ring
        rw [hcalc]
        exact dvd_neg.mpr hra
  · rw [src_accept]
    exact gate_of_eval_zero (by simp [subW, negW, WindowExpr.eval, hTop])

/-- THE COMPLETENESS LEG, per row.  R1's two new gates are DERIVED from the source's bit /
zero-test / and-spine / accept equations: acceptance forces the spine output to 1, hence the
asserted atom's bit to 1, hence its residual to 0. -/
theorem rw_completeness_row (hash : List ℤ → ℤ) (tf : TraceFamily) (isFirst isLast : Bool)
    (env : VmRowEnv)
    (hsrc : ∀ c ∈ (descriptor (rootProgram terms a rest)).constraints,
      c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ (rwDescriptor pub sec atoms terms a rest).constraints,
      c.holdsAt hash tf env isFirst isLast := by
  have h1 := hsrc (gate (bitBody (.col (boolBase pub sec atoms))))
    (graph_node_constraint_mem _ _ (zt_mem_src terms a rest) _
      (by simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints]))
  have h2 := hsrc (gate (.mul (.loc a.val) (.loc (boolBase pub sec atoms))))
    (graph_node_constraint_mem _ _ (zt_mem_src terms a rest) _
      (by simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints]))
  have h4 := hsrc (gate (subW (.loc (boolBase pub sec atoms + 2 + witnessCount rest))
      (.mul (Wire.col (boolBase pub sec atoms)).expr (restOut pub sec atoms rest).expr)))
    (graph_node_constraint_mem _ _ (andNode_mem_src terms a rest) _
      (by simp [Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Node.constraints]))
  have h5 := hsrc (acceptConstraintAt (rootProgram terms a rest)) (by simp [descriptor])
  rw [src_accept] at h5
  rw [gate_dvd_iff] at h1 h2 h4 h5
  simp only [bitBody_eq, wire_col_expr, subW, negW, WindowExpr.eval] at h1 h2 h4 h5
  have f1 := (dvd_iff_cast_zero _).1 h1
  have f2 := (dvd_iff_cast_zero _).1 h2
  have f4 := (dvd_iff_cast_zero _).1 h4
  have f5 := (dvd_iff_cast_zero _).1 h5
  push_cast at f1 f2 f4 f5
  have hbit : Dregg2.Logic.BoolGraph.IsBit
      ((env.loc (boolBase pub sec atoms) : ℤ) : ZMod 2013265921) := by
    show _ * (_ - 1) = 0
    linear_combination f1
  have ho : ((env.loc (boolBase pub sec atoms + 2 + witnessCount rest) : ℤ) :
      ZMod 2013265921) = 1 := by linear_combination f5
  have hby : ((env.loc (boolBase pub sec atoms) : ℤ) : ZMod 2013265921) *
      (((restOut pub sec atoms rest).expr.eval env : ℤ) : ZMod 2013265921) = 1 := by
    linear_combination ho - f4
  have hb1 : ((env.loc (boolBase pub sec atoms) : ℤ) : ZMod 2013265921) = 1 := by
    rcases Dregg2.Logic.BoolGraph.bit_zero_or_one hbit with h0 | h1'
    · exfalso
      rw [h0, zero_mul] at hby
      exact one_ne_zero_babybear hby.symm
    · exact h1'
  have hx : ((env.loc a.val : ℤ) : ZMod 2013265921) = 0 := by
    rw [hb1, mul_one] at f2
    exact f2
  have hy : (((restOut pub sec atoms rest).expr.eval env : ℤ) : ZMod 2013265921) = 1 := by
    rw [hb1, one_mul] at hby
    exact hby
  intro c hc
  simp only [rwDescriptor, rwConstraints, List.mem_append, List.mem_singleton] at hc
  rcases hc with (((hpin | hlink) | rfl) | hmid) | rfl
  · exact hsrc c (by simp [descriptor, hpin])
  · exact hsrc c (by simp [descriptor, hlink])
  · simp only [directGate]
    rw [gate_dvd_iff]
    simp only [WindowExpr.eval]
    exact (dvd_iff_cast_zero _).2 hx
  · exact hsrc c (mid_constraint_mem_src terms a rest hmid)
  · simp only [restAccept]
    rw [gate_dvd_iff]
    simp only [subW, negW, WindowExpr.eval]
    refine (dvd_iff_cast_zero _).2 ?_
    push_cast
    rw [hy]
    ring

end Rows

/-! ## 8. The certified pass and its two contract legs. -/

section Pass

variable {pub sec atoms : Nat}
variable (terms : Fin atoms → AffineTerm (pub + sec)) (a : Fin atoms) (rest : Formula atoms)

/-- THE PASS.  `toTarget` is the identity — R1 changes no column — and `toSource` rebuilds the
elided postorder witness region. -/
def rwPass : PassiveOptimization (descriptor (rootProgram terms a rest))
    (rwDescriptor pub sec atoms terms a rest) where
  toTarget := id
  toSource := rebuildTrace (boolBase pub sec atoms) (witnessCount rest)
  publicABI :=
    { piCount_eq := rfl
      bindingSlots_eq := by
        rw [publicBindingSlots_src, publicBindingSlots_rw] }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

theorem rw_security : SecurityRefinement (rwPass terms a rest) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_transfer (t := t) (u := (rwPass terms a rest).toSource t)
    (memOps_descriptor_nil _) (mapOps_descriptor_nil _)
    (memOps_rw_nil terms a rest) (mapOps_rw_nil terms a rest) rfl rfl rfl hsat ?_
  intro i hi c hc
  have hlen : ((rwPass terms a rest).toSource t).rows.length = t.rows.length :=
    rebuildTrace_rows_length _ _ t
  rw [hlen] at hi
  rw [hlen]
  refine rw_security_row terms a rest hash t.tf (i == 0) (i + 1 == t.rows.length)
    (envAt t i)
    (envAt (rebuildTrace (boolBase pub sec atoms) (witnessCount rest) t) i)
    rfl ?_ ?_ ?_ ?_ (hsat.rowConstraints i hi) c hc
  · intro k hk1 hk2 hk3
    rw [rebuildTrace_loc _ _ t i hi]
    exact rebuildRow_untouched _ _ _ hk1 hk2 hk3
  · rw [rebuildTrace_loc _ _ t i hi]
    exact rebuildRow_base _ _ _
  · rw [rebuildTrace_loc _ _ t i hi]
    exact rebuildRow_inv _ _ _
  · rw [rebuildTrace_loc _ _ t i hi]
    exact rebuildRow_top _ _ _

theorem rw_completeness : CompletenessPreservation (rwPass terms a rest) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_transfer (t := t) (u := (rwPass terms a rest).toTarget t)
    (memOps_rw_nil terms a rest) (mapOps_rw_nil terms a rest)
    (memOps_descriptor_nil _) (mapOps_descriptor_nil _) rfl rfl rfl hsat ?_
  intro i hi c hc
  exact rw_completeness_row terms a rest hash t.tf (i == 0) (i + 1 == t.rows.length)
    (envAt t i) (hsat.rowConstraints i hi) c hc

/-- BOTH LEGS: R1 is a genuine equisatisfiability-preserving passive pass on the EMITTED
descriptor, not a resource stand-in. -/
theorem rw_preservation : SatisfiabilityPreservation (rwPass terms a rest) :=
  ⟨rw_security terms a rest, rw_completeness terms a rest⟩

theorem rw_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor (rootProgram terms a rest)) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (rwDescriptor pub sec atoms terms a rest) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (rw_preservation terms a rest) hash minit mfin maddrs

/-! ## 9. Composition with the already-certified E1 dead-column deletion. -/

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- R1 then E1, end to end, through the framework's own composition. -/
def peepholePass (floor : Nat) :
    PassiveOptimization (descriptor (rootProgram terms a rest))
      (compactE1 (rwDescriptor pub sec atoms terms a rest)
        (deadColsE1 (rwDescriptor pub sec atoms terms a rest) floor)) :=
  (rwPass terms a rest).comp
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPass
      (rwDescriptor pub sec atoms terms a rest) floor)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- END TO END: the composed R1 + E1 pass preserves satisfaction in both directions.  The
hypothesis is E1's own cheap transition-ceiling certificate on the REWRITTEN descriptor. -/
theorem peephole_preservation (floor : Nat)
    (hceiling : transitionCeilingOk (rwDescriptor pub sec atoms terms a rest) floor = true) :
    SatisfiabilityPreservation (peepholePass terms a rest floor) :=
  preservation_comp (rw_preservation terms a rest)
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation
      (rwDescriptor pub sec atoms terms a rest) floor hceiling)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
theorem peephole_satisfiable_iff (floor : Nat)
    (hceiling : transitionCeilingOk (rwDescriptor pub sec atoms terms a rest) floor = true)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor (rootProgram terms a rest)) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash
        (compactE1 (rwDescriptor pub sec atoms terms a rest)
          (deadColsE1 (rwDescriptor pub sec atoms terms a rest) floor))
        minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (peephole_preservation terms a rest floor hceiling)
    hash minit mfin maddrs

end Pass

/-! ## 10. A concrete, non-vacuous instance.

`pub = sec` conjoined with the booleanity disjunction `sec = 0 ∨ sec = 1` — the pilot's shape in
miniature: one asserted equality on the frontier (R1 fires) plus one disjunction whose zero tests
are load-bearing (R1 correctly leaves them).  The satisfying witness is carried across the pass by
the completeness leg, so neither contract is vacuous. -/

namespace Demo

def terms : Fin 3 → AffineTerm (1 + 1)
  | ⟨0, _⟩ => .add (.input ⟨0, by omega⟩) (.neg (.input ⟨1, by omega⟩))
  | ⟨1, _⟩ => .input ⟨1, by omega⟩
  | ⟨2, _⟩ => AffineTerm.eqConst ⟨1, by omega⟩ 1
  | ⟨_, _⟩ => .const 1

def a0 : Fin 3 := ⟨0, by omega⟩

/-- `(sec = 0) ∨ (sec = 1)` — the residual R1 cannot touch. -/
def rest : Formula 3 := .or (.atom ⟨1, by omega⟩) (.atom ⟨2, by omega⟩)

noncomputable def goodInput : Fin (1 + 1) → ZMod 2013265921 := fun _ => 0

theorem good_holds : (rootProgram terms a0 rest).Holds goodInput := by
  constructor
  · show (AffineTerm.add (.input ⟨0, by omega⟩) (.neg (.input ⟨1, by omega⟩))).evalField
      goodInput = 0
    simp [goodInput, AffineTerm.evalField]
  · left
    show (AffineTerm.input ⟨1, by omega⟩ : AffineTerm (1 + 1)).evalField goodInput = 0
    simp [goodInput, AffineTerm.evalField]

theorem demo_source_satisfiable (hash : List ℤ → ℤ) :
    ∃ s, Satisfied2 hash (descriptor (rootProgram terms a0 rest))
      (fun _ => 0) (fun _ => (0, 0)) [] s :=
  ⟨canonicalTrace (rootProgram terms a0 rest) goodInput,
    canonical_complete hash (rootProgram terms a0 rest) goodInput good_holds⟩

/-- NON-VACUITY: the REWRITTEN descriptor is satisfiable, and the witness comes across the
completeness leg — the contract relates two genuinely inhabited relations. -/
theorem demo_rw_satisfiable (hash : List ℤ → ℤ) :
    ∃ u, Satisfied2 hash (rwDescriptor 1 1 3 terms a0 rest)
      (fun _ => 0) (fun _ => (0, 0)) [] u :=
  (rw_satisfiable_iff terms a0 rest hash _ _ _).1 (demo_source_satisfiable hash)

/-- And back: an accepting target trace expands to an accepting SOURCE trace. -/
theorem demo_security_roundtrip (hash : List ℤ → ℤ) :
    ∃ s, Satisfied2 hash (descriptor (rootProgram terms a0 rest))
      (fun _ => 0) (fun _ => (0, 0)) [] s :=
  (rw_satisfiable_iff terms a0 rest hash _ _ _).2 (demo_rw_satisfiable hash)

-- Concrete recovery on this instance (compiled `==`, no kernel `decide`).
#guard (descriptor (rootProgram terms a0 rest)).constraints.length == 18
#guard (rwDescriptor 1 1 3 terms a0 rest).constraints.length == 14
#guard (rwDescriptor 1 1 3 terms a0 rest).traceWidth ==
  (descriptor (rootProgram terms a0 rest)).traceWidth

end Demo

#assert_all_clean [
  outputAt_wireCols,
  nodesAt_nodeCols,
  node_holdsAt_congr,
  toWindowAt_eval_congr,
  graphConstraints_split,
  rw_constraints_recovery,
  rw_multiplications_recovery,
  publicBindingSlots_src,
  publicBindingSlots_rw,
  satisfied2_transfer,
  rw_security_row,
  rw_completeness_row,
  rw_security,
  rw_completeness,
  rw_preservation,
  rw_satisfiable_iff,
  peephole_preservation,
  peephole_satisfiable_iff,
  Demo.good_holds,
  Demo.demo_rw_satisfiable,
  Demo.demo_security_roundtrip
]

end Dregg2.Circuit.PeepholePassCertified
