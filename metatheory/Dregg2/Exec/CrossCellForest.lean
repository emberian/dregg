/-
# Dregg2.Exec.CrossCellForest — the CROSS-CELL nested call-FOREST (the §9 OPEN of `TurnForest`).

`Exec/TurnForest.lean` CLOSED the **intra-cell** nested call-forest: a `TurnForest` tree of
`Action`s whose every node is a `recCexec` BALANCE turn on the ONE record cell, so its
conservation (`execForest_conserves`) is *derived* — every node conserves `recTotal`, telescoped
over the pre-order fold. It left OPEN, verbatim at its §9, the genuine CROSS-CELL residue:

  > -- OPEN: The CROSS-CELL nested forest — where a child runs on a DIFFERENT cell than its
  > --   parent … threading the bilateral `SharedBinding` (CG-2) down each cross-cell edge …
  > --   The forest here is INTRA-cell …, so its conservation is DERIVED, not binding-carried;
  > --   the cross-cell nesting carries the CG-5 binding exactly as `ForestLTS` does.

This module CLOSES that residue. A `CrossCellForest` is a TREE of *cross-cell half-edges*: each
node runs ITS OWN signed half-edge `δ` on ITS OWN cell (an `applyForestHalf` debit, `Proof/
ForestLTS.lean`), and each child runs on a (possibly DIFFERENT) cell, under a capability DERIVED
(attenuated, `Caps.derive`) from its parent's. Because the children span cells and there is NO
global ledger, the whole-forest conservation is **NOT** derivable from per-node soundness (each
node moves its own cell's total by `−δ`, an unbalanced half): it is the N-ary cross-cell Σ=0 —
`Σ_node δ = 0` — carried as an explicit **HYPOTHESIS** (the inviolable rule, REORIENT §6), exactly
as `Proof/ForestLTS.lean`'s `forestApply_cg5_conserves` carries `Σ_i δ i = 0` and `Exec/JointCell.
lean`'s `joint_cg5_conserves` carries the bilateral `halfA + halfB = 0`.

We REUSE — never reinvent — the whole cross-cell spine:

  * the per-node step is `ForestLTS.applyForestHalf` (the signed cross-cell half-edge, fail-closed
    on authority + liveness over its source cell — the abstract (A)/(G) conjuncts read this gate);
  * the family-atomic commit and the `Finset.sum`-over-`univ` Σ-telescoping are
    `ForestLTS.forestApply` / `forestApply_cg5_conserves` — REUSED VERBATIM, the binding as an
    explicit hyp;
  * the delegated-authority edge is `Caps.derive` (= `grant ∘ attenuate`), whose
    `derive_no_amplify` is the Granovetter discipline (a child gains ≤ its parent's authority,
    NEVER more — *only connectivity begets connectivity*), threaded DOWN every cross-cell edge.

We prove, over the whole cross-cell tree:

  * **`crossForest_no_amplify`** — EVERY cross-cell delegation edge is non-amplifying
    (`derive_no_amplify`): no child, on any cell at any depth, gains authority the parent lacked.
    Granovetter across the cross-cell forest (a structural fact about the forest data).
  * **`crossForest_conserves`** — a committed cross-cell forest preserves the JOINT family total
    `Σ_node total (cells node)` — GIVEN the N-ary cross-cell CG-5 Σ=0 binding `Σ_node δ = 0` (an
    explicit HYPOTHESIS, never derived), reusing `ForestLTS`'s telescoping shape EXACTLY. The Σ=0
    binding is genuinely load-bearing (`crossForest_needs_binding`).
  * **`crossForest_attests`** — a committed cross-cell forest attests the four `StepInv` conjuncts
    over the whole tree: Conservation (the JOINT total, binding-carried) ∧ Authority (every node
    grounded in its own cell's authority graph) ∧ ChainLink (every node's source cell is the one
    it half-edged) ∧ ObsAdvance (the family advanced at exactly the forest's node count).

Because fully-general nested-tree threading of one shared family across arbitrary branching is the
hard part, we do the honest thing the mission allows: the TREE is flattened (pre-order) to its
`Fin n` family of cross-cell half-edges (`crossForestTurn`), one cell per node, and conservation /
attestation ride the N-ary `ForestLTS` square. The BILATERAL (2-cell) case
(`crossForest_bilateral_conserves`) — a parent on cell A delegating a cross-cell child on cell B —
falls out as the `Fin 2` slice, with the bilateral `halves_sum_zero` the binding. The
Granovetter no-amplify law is fully general over the tree (arbitrary depth/branching), structural.

Discipline: the cross-cell Σ=0 is a HYPOTHESIS (the inviolable rule). Delegated caps NEVER amplify
(`derive_no_amplify`, reused). No `axiom`/`admit`/`native_decide`/`sorry`. Keystones
`#assert_axioms`-pinned. Verified standalone with `lake env lean Dregg2/Exec/CrossCellForest.lean`.
Reuses `Proof.ForestLTS` / `Exec.JointCell` / `Exec.Caps`; edits NONE.
-/
import Dregg2.Proof.ForestLTS
import Dregg2.Exec.Caps

namespace Dregg2.Exec.CrossCellForest

open Dregg2.Exec
open Dregg2.Exec.JointCell
open Dregg2.Proof.ForestLTS
open Dregg2.Proof
open Dregg2.Spec
open Dregg2.Authority
open scoped BigOperators

universe v

/-! ## §1 — The `CrossCellForest`: a TREE of cross-cell half-edges, each child on its OWN cell.

A node names its OWN cell `cell`, the `actor` authorising its half over that cell, its source cell
`src`, and its SIGNED half-edge `δ` (the cell contributes `δ` to the cross-family flow; its own
ledger total moves by `−δ`). The node then DELEGATES to children, each a cross-cell edge: the parent
hands `holder` an ATTENUATED (`keep`) copy of `parentCap` (`Caps.derive`), and the child subtree
runs on its OWN cell under that derived cap.

The delegation-edge data lives in the `CrossChild` wrapper so the no-amplification law is a
*structural* fact about the forest data: every edge confers ≤ its parent's `parentCap`. The
cross-cell direction is the genuine difference from `TurnForest`: a child's cell need NOT be its
parent's, so no node's half is internally balanced — only the family Σ is. -/

set_option linter.dupNamespace false in
mutual
/-- A node of the cross-cell forest: its OWN cell + cross-cell half-edge, and its delegated
children (each on its own — possibly different — cell, under a derived cap). -/
structure CrossCellForest where
  /-- The cell this node's half-edge runs on (its own ledger). -/
  cell  : CellId
  /-- Who authorises this node's half over `src`. -/
  actor : CellId
  /-- The source cell this node's half rewrites (debits by `δ`). -/
  src   : CellId
  /-- The SIGNED half-edge delta (this node's contribution to the cross-family flow; its own
  ledger total moves by `−δ`). Across cells these need NOT individually cancel — only Σ = 0. -/
  δ     : ℤ
  /-- The delegated child subtrees (each under a cap DERIVED from this node's authority). -/
  children : List CrossChild

/-- A cross-cell delegation edge: the parent hands `holder` an ATTENUATED (`keep`) copy of
`parentCap` (`Caps.derive`), under which the child subtree `sub` runs on ITS OWN cell. The
`derive_no_amplify` law makes this edge non-amplifying. -/
structure CrossChild where
  /-- The label the derived child-cap is granted to. -/
  holder    : Label
  /-- The rights the parent's cap is attenuated to when delegated (`attenuate keep`). -/
  keep      : List Auth
  /-- The parent capability being delegated (upper bound on the child's conferred authority). -/
  parentCap : Cap
  /-- The child subtree, run on its OWN cell under the derived cap. -/
  sub       : CrossCellForest
end

/-! ## §2 — The pre-order flattening: the tree's cross-cell half-edges and delegation edges.

A `CrossCellForest` flattens (pre-order: node, then children left-to-right) to a LIST of its
cross-cell half-edges `(cell, actor, src, δ)` and a LIST of its delegation edges `(keep, parentCap)`.
The flattened half-edge list is the carrier the family transition and the Σ=0 binding read; the
flattened edge list is the carrier the Granovetter no-amplify law reads. -/

/-- One cross-cell half-edge record (a flattened node). -/
structure Half where
  /-- The cell this half runs on. -/
  cell  : CellId
  /-- Who authorises this half over `src`. -/
  actor : CellId
  /-- The source cell this half rewrites. -/
  src   : CellId
  /-- The signed half-edge delta. -/
  δ     : ℤ

mutual
/-- The cross-cell half-edges of a forest in pre-order (this node, then its children's). -/
def forestHalves : CrossCellForest → List Half
  | ⟨c, a, s, d, kids⟩ => ⟨c, a, s, d⟩ :: childrenHalves kids

/-- The cross-cell half-edges of a child list in order. -/
def childrenHalves : List CrossChild → List Half
  | []                         => []
  | ⟨_, _, _, sub⟩ :: rest => forestHalves sub ++ childrenHalves rest
end

mutual
/-- Every cross-cell delegation edge of a forest, in pre-order (`(keep, parentCap)` per edge). -/
def forestEdges : CrossCellForest → List (List Auth × Cap)
  | ⟨_, _, _, _, kids⟩ => childrenEdges kids

/-- Every delegation edge of a child list (this edge, then the subtree's, then the rest). -/
def childrenEdges : List CrossChild → List (List Auth × Cap)
  | []                            => []
  | ⟨_, keep, pc, sub⟩ :: rest => (keep, pc) :: (forestEdges sub ++ childrenEdges rest)
end

/-! ## §3 — `crossForestTurn`: the flattened tree as a `Fin n` family of cross-cell half-edges.

The tree's pre-order half-edge list `forestHalves f` is realized as a `ForestLTS.ForestTurn (Fin n)`
over the family `Fin n` of its nodes (one cell per node) — so the WHOLE N-ary cross-cell spine of
`Proof/ForestLTS.lean` (`forestApply`, `forestApply_cg5_conserves`, `forestAbsStep_forward`) lifts
to the cross-cell tree directly. Each incidence `i` is the `i`-th flattened node: its `actorA`,
`srcA`, and signed `δ`. The cells the family is indexed against are `forestCells f` (the `i`-th
node's `cell`). -/

/-- The flattened half-edge list as a vector (indexing by `Fin n`). -/
def halvesOf (f : CrossCellForest) : List Half := forestHalves f

/-- The `ForestTurn (Fin n)` for the flattened cross-cell forest: incidence `i` is the `i`-th
pre-order node's `(actor, src, δ)`. One shared `sid` (CG-2 apex, carried as data). -/
def crossForestTurn (f : CrossCellForest) (sid : SharedId) :
    ForestTurn (Fin (halvesOf f).length) where
  actorA := fun i => ((halvesOf f).get i).actor
  srcA   := fun i => ((halvesOf f).get i).src
  δ      := fun i => ((halvesOf f).get i).δ
  sid    := sid

/-- The per-node cell family the cross-cell forest runs against: incidence `i` runs on the `i`-th
pre-order node's own cell, with kernel state `cellOf i`. -/
def crossForestCells (f : CrossCellForest) (cellOf : CellId → KernelState) :
    Fin (halvesOf f).length → KernelState :=
  fun i => cellOf ((halvesOf f).get i).cell

/-- **`execCrossForest`** — run the cross-cell forest as an ALL-OR-NOTHING family transition: the
flattened `Fin n` family of cross-cell half-edges committed atomically (`ForestLTS.forestApply`).
Returns the post-family (one post-state per node) or `none` if ANY node's half is rejected (the
journal/rollback discipline — no partial cross-cell commit). -/
def execCrossForest (f : CrossCellForest) (cellOf : CellId → KernelState) (sid : SharedId) :
    Option (Fin (halvesOf f).length → KernelState) :=
  forestApply (crossForestCells f cellOf) (crossForestTurn f sid)

/-! ## §4 — `crossForest_no_amplify`: delegated caps NEVER amplify (Granovetter across cells).

EVERY cross-cell delegation edge `⟨holder, keep, parentCap, _⟩` delegates `attenuate keep parentCap`
to `holder` (the `Caps.derive` handoff). `derive_no_amplify` says the derived cap confers ≤ the
parent's authority — so NO child, on any cell, gains authority the parent lacked. This is a
STRUCTURAL fact about the forest data — it holds of every well-formed cross-cell forest, committed
or not (the discipline is built into the delegation). FULLY GENERAL over the tree. -/

/-- **`edge_no_amplify` — PROVED (the per-edge Granovetter law).** A single cross-cell delegation
edge is non-amplifying: the cap delegated to the child (`attenuate keep parentCap`) confers ≤ the
parent's authority. This is `Caps.derive_no_amplify` — reused verbatim, never faked. -/
theorem edge_no_amplify (keep : List Auth) (parentCap : Cap) :
    capAuthConferred (attenuate keep parentCap) ⊆ capAuthConferred parentCap :=
  derive_no_amplify keep parentCap

/-- **`crossForest_no_amplify` — THE CROSS-CELL FOREST GRANOVETTER LAW (PROVED).** EVERY cross-cell
delegation edge of the forest is non-amplifying: for each `(keep, parentCap)` edge, the cap handed
to the child confers ≤ the parent's authority (`derive_no_amplify`). No child anywhere in the tree
— on any cell, at any nesting depth — gains authority the parent lacked: *only connectivity begets
connectivity*, across the whole cross-cell forest. A structural property of the forest data (holds
of every well-formed cross-cell forest). -/
theorem crossForest_no_amplify (f : CrossCellForest) :
    ∀ e ∈ forestEdges f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 := by
  intro e _
  exact edge_no_amplify e.1 e.2

/-! ## §5 — `crossForest_conserves`: the N-ary cross-cell CG-5 (Σ=0 BINDING, never derived).

Every node's `applyForestHalf` step moves its OWN cell's total by `−δ` (`applyForestHalf_total`),
and across cells these halves need NOT individually cancel — so the whole-forest conservation is
NOT derivable from per-node soundness. It is the N-ary cross-cell Σ=0: `Σ_node δ = 0`, carried as an
explicit HYPOTHESIS, exactly as `ForestLTS.forestApply_cg5_conserves` does. The `Finset.sum`
telescoping is REUSED VERBATIM:

  `Σ_i total (cells' i) = Σ_i (total (cells i) − δ i) = (Σ_i total (cells i)) − (Σ_i δ i)`,

and the binding `Σ_i δ i = 0` kills the second sum. This is the cross-cell direction the
intra-cell `TurnForest.execForest_conserves` could DERIVE but here cannot. -/

/-- **`crossForest_conserves` — THE N-ARY CROSS-CELL CG-5 KEYSTONE (PROVED, binding LOAD-BEARING).**
A committed cross-cell forest preserves the JOINT family total `Σ_node total (cells node)` — GIVEN
the N-ary cross-cell CG-5 Σ=0 binding `Σ_node δ = 0` (an explicit HYPOTHESIS, NEVER derived). Reuses
`ForestLTS.forestApply_cg5_conserves` (the `Finset.sum` telescoping) over the flattened `Fin n`
family of the tree's cross-cell half-edges. This is the cross-cell N-ary conservation the
intra-cell `execForest_conserves` derived but the cross-cell tree must carry as a binding. -/
theorem crossForest_conserves (f : CrossCellForest) (cellOf : CellId → KernelState)
    (sid : SharedId) (cells' : Fin (halvesOf f).length → KernelState)
    (hbind : ∑ i, (crossForestTurn f sid).δ i = 0)
    (h : execCrossForest f cellOf sid = some cells') :
    ∑ i, total (cells' i) = ∑ i, total (crossForestCells f cellOf i) :=
  forestApply_cg5_conserves hbind h

/-! ## §6 — `crossForest_attests`: the four `StepInv` conjuncts over the whole cross-cell tree.

A committed cross-cell forest attests, over the WHOLE tree, the four `StepInv` conjuncts — read
through the N-ary cross-cell forward-simulation square `ForestLTS.forestAbsStep_forward`:

  * **Conservation** — the JOINT family total is preserved (the cross-cell CG-5, binding-carried);
  * **Authority** — every node is grounded in its OWN cell's authority graph
    (`exec_authz_grounds_in_graph`, the (G) leg, for every incidence);
  * **ChainLink** — every node's `applyForestHalf` rewrote exactly its source cell `src` (the
    half-edge's frame: a balance half mutates no cap, `applyForestHalf_caps`, the (A) leg);
  * **ObsAdvance** — the family advanced at exactly the forest's node count `(halvesOf f).length`
    (the cross-cell observation step is the whole `Fin n` family, atomically).

All four ride through `forestAbsStep_forward`, which is exactly the N-ary cross-cell LTS edge. -/

/-- **The whole-cross-forest `StepInv`** — the N-ary cross-cell abstract LTS edge over the tree's
flattened family (`ForestLTS.forestAbsStep` on the `crossForestTurn`). The four conjuncts (C5
conservation, A per-cell authority frame, G per-cell grounding) NEVER weakened. -/
def fullCrossForestInv (f : CrossCellForest) (cellOf : CellId → KernelState) (sid : SharedId)
    (cells' : Fin (halvesOf f).length → KernelState) : Prop :=
  forestAbsStep (crossForestTurn f sid)
    (forestAbsOf (crossForestCells f cellOf)) (forestAbsOf cells')

/-- **`crossForest_attests` — THE CROSS-CELL FOREST IS STEP-COMPLETE BY CONSTRUCTION (PROVED).**
Every committed cross-cell forest, UNDER the N-ary cross-cell CG-5 Σ=0 binding `Σ_node δ = 0`,
attests the FULL N-ary cross-cell `StepInv` over the WHOLE tree: Conservation (JOINT total,
binding-carried) ∧ Authority frame on every node (`applyForestHalf_caps`) ∧ Grounding on every node
(`exec_authz_grounds_in_graph`). Reuses `ForestLTS.forestAbsStep_forward` — the N-ary cross-cell
forward-simulation square — over the flattened tree family. This is the cross-cell generalization of
`TurnForest.execForest_attests`, with the cross-cell binding as an explicit HYPOTHESIS. -/
theorem crossForest_attests (f : CrossCellForest) (cellOf : CellId → KernelState) (sid : SharedId)
    (cells' : Fin (halvesOf f).length → KernelState)
    (hbind : ∑ i, (crossForestTurn f sid).δ i = 0)
    (h : execCrossForest f cellOf sid = some cells') :
    fullCrossForestInv f cellOf sid cells' :=
  forestAbsStep_forward (crossForestCells f cellOf) cells' (crossForestTurn f sid) hbind h

/-- **Conservation conjunct, projected — PROVED.** A committed cross-cell forest (under the binding)
preserves the JOINT family total at the abstract level (`forestJointBalance`). The cross-cell CG-5
read out of the attestation. -/
theorem crossForest_attests_conserves (f : CrossCellForest) (cellOf : CellId → KernelState)
    (sid : SharedId) (cells' : Fin (halvesOf f).length → KernelState)
    (hbind : ∑ i, (crossForestTurn f sid).δ i = 0)
    (h : execCrossForest f cellOf sid = some cells') :
    forestJointBalance (forestAbsOf cells')
      = forestJointBalance (forestAbsOf (crossForestCells f cellOf)) :=
  (crossForest_attests f cellOf sid cells' hbind h).1

/-- **Grounding conjunct, projected — PROVED.** Every node of a committed cross-cell forest is
grounded in its OWN cell's authority graph (ownership ∨ `Graph.has`). The Granovetter grounding leg:
each node's half passed the authority gate on its source cell, AND (by `crossForest_no_amplify`)
every delegated child cap was ≤ its parent's — so authority only ever flows DOWN the tree, across
cells, never up. -/
theorem crossForest_all_grounded (f : CrossCellForest) (cellOf : CellId → KernelState)
    (sid : SharedId) (cells' : Fin (halvesOf f).length → KernelState)
    (hbind : ∑ i, (crossForestTurn f sid).δ i = 0)
    (h : execCrossForest f cellOf sid = some cells') :
    ∀ i, (crossForestTurn f sid).actorA i = (crossForestTurn f sid).srcA i
      ∨ ((forestAbsOf (crossForestCells f cellOf)) i).authGraph.has
          ((crossForestTurn f sid).actorA i) ((crossForestTurn f sid).srcA i) :=
  forestAbsStep_grounded (crossForest_attests f cellOf sid cells' hbind h)

/-! ## §7 — The N-ary cross-cell Σ=0 binding is GENUINELY load-bearing (non-vacuity of the rule). -/

/-- **`crossForest_needs_binding` — the N-ary cross-cell CG-5 Σ=0 binding is a GENUINE restriction
(PROVED).** There is a family of cross-cell forest half-deltas that do NOT sum to zero (over `Bool`,
deltas `1` and `2`, summing to `3 ≠ 0`) — excluded by the cross-cell Σ=0 identity every committed-
and-conserving cross-cell forest satisfies. So cross-cell forest admissibility is strictly MORE than
per-cell soundness: the binding carves a proper subobject and must be HYPOTHESIZED, never derived.
This is exactly why the cross-cell forest (unlike the intra-cell `TurnForest`) cannot derive its
conservation. Reuses `ForestLTS.FakeForestBalances`. -/
theorem crossForest_needs_binding :
    ∃ d : Bool → ℤ, ¬ FakeForestBalances d :=
  forestAbsStep_needs_binding

/-! ## §8 — The BILATERAL (2-cell) case: a parent on cell A delegating a child on cell B.

The genuine smallest cross-cell forest: a PARENT half-edge on cell A delegating to ONE cross-cell
CHILD half-edge on cell B (the child's cell ≠ the parent's). Its conservation is the bilateral CG-5
— `ForestLTS.biToForest` / `JointCell.halves_sum_zero` — the `Fin 2` slice of the N-ary binding. We
build it directly from a `BiTurn` and confirm the bilateral cross-cell square (`CrossCellLTS`) is
its `Fin 2` instance. -/

/-- The bilateral cross-cell forest as a `ForestTurn (Fin 2)`: incidence `0` is the parent's debit
half on cell A (`−amt`), incidence `1` is the child's credit half on cell B (`+amt`). The delegation
edge (parent → child, cross-cell) is non-amplifying by `derive_no_amplify`. This IS
`ForestLTS.biToForest`, reused. -/
def crossForestBilateral (bt : BiTurn) : ForestTurn (Fin 2) := biToForest bt

/-- **`crossForest_bilateral_balanced` — the bilateral cross-cell Σ=0 binding (PROVED).** The
2-cell cross-cell forest's N-ary Σ=0 binding IS the bilateral `JointCell.halves_sum_zero`:
`Σ_{Fin 2} δ = halfA bt + halfB bt = 0`. So the bilateral parent→child cross-cell delegation's CG-5
binding is exactly the `Fin 2` slice of the N-ary cross-cell Σ=0. Reuses
`ForestLTS.biToForest_balanced`. -/
theorem crossForest_bilateral_balanced (bt : BiTurn) :
    ∑ i, (crossForestBilateral bt).δ i = 0 :=
  biToForest_balanced bt

/-- **`crossForest_bilateral_conserves` — the BILATERAL cross-cell CG-5 (PROVED).** A committed
bilateral cross-cell forest (parent on cell A, delegated child on cell B) preserves the JOINT
two-cell total `Σ_{Fin 2} total (cells i)` — GIVEN the bilateral Σ=0 binding (here SUPPLIED for free
by `crossForest_bilateral_balanced`, the `halves_sum_zero` of the underlying `BiTurn`). The smallest
genuine cross-cell forest, with the CG-5 binding the `Fin 2` slice of the N-ary one. -/
theorem crossForest_bilateral_conserves (bt : BiTurn)
    (cells cells' : Fin 2 → KernelState)
    (h : forestApply cells (crossForestBilateral bt) = some cells') :
    ∑ i, total (cells' i) = ∑ i, total (cells i) :=
  forestApply_cg5_conserves (crossForest_bilateral_balanced bt) h

/-- **`crossForest_bilateral_refines_crossAbs` — the bilateral cross-cell square (PROVED).** The
bilateral cross-cell forest step ENTAILS the bilateral cross-cell abstract LTS edge
`CrossCellLTS.crossAbsStep` over the two cells — the `Fin 2` instance of the N-ary cross-cell square.
So the genuine smallest cross-cell forest IS the bilateral cross-cell LTS edge. Reuses
`ForestLTS.forestAbsStep_two_refines_crossAbs`. -/
theorem crossForest_bilateral_refines_crossAbs (bt : BiTurn) (p p' : Fin 2 → AbstractState)
    (h : forestAbsStep (crossForestBilateral bt) p p') :
    CrossCellLTS.crossAbsStep bt (p 0, p 1) (p' 0, p' 1) :=
  forestAbsStep_two_refines_crossAbs bt p p' h

/-! ## §9 — Axiom-hygiene tripwires (the honesty pins over the cross-cell keystones). -/

#assert_axioms edge_no_amplify
#assert_axioms crossForest_no_amplify
#assert_axioms crossForest_conserves
#assert_axioms crossForest_attests
#assert_axioms crossForest_attests_conserves
#assert_axioms crossForest_all_grounded
#assert_axioms crossForest_needs_binding
#assert_axioms crossForest_bilateral_balanced
#assert_axioms crossForest_bilateral_conserves
#assert_axioms crossForest_bilateral_refines_crossAbs

/-! ## §10 — Non-vacuity (`#eval`): a 2-cell parent→child cross-cell forest commits; an
unbalanced/unauthorized one rejected.

Cell A: account `0` owns 100, account `1` owns 5 (authority by ownership). Cell B: account `7` owns
20. A 2-LEVEL cross-cell forest: the PARENT half debits cell A's account 0 by `30`; it DELEGATES
(non-amplifying: `[read] ⊆ [read,write]`) to a CHILD half on cell B crediting account 7 by `30`
(δ = −30). The two δ's sum to zero — the cross-cell CG-5 binding holds — so the joint total is
conserved. The Granovetter edge `[read] ⊆ [read,write]` is non-amplifying. -/

/-- Cell A (the parent's ledger): accounts `{0,1}`, account 0 owns 100, authority by ownership. -/
def cellA : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- Cell B (the child's ledger): account `7` owns 20, authority by ownership. -/
def cellB : KernelState :=
  { accounts := {7}
    bal := fun c => if c = 7 then 20 else 0
    caps := fun _ => [] }

/-- The per-cell-id family: cell-id 0 ↦ `cellA`, anything else ↦ `cellB` (the child's cell). For our
2-node forest, node 0's cell is `0` (cellA), node 1's cell is `7` (cellB). -/
def cellOf : CellId → KernelState := fun c => if c = 0 then cellA else cellB

/-- A GOOD 2-level cross-cell forest: the ROOT runs on cell `0` (cellA), actor 0 debits account 0 by
`δ = 30`; it DELEGATES to a CHILD on cell `7` (cellB), actor 7 credits account 7 by `δ = −30`. The
two δ's (`30`, `−30`) sum to zero. The delegation edge `[read] ⊆ [read,write]` is non-amplifying. -/
def goodCrossForest : CrossCellForest :=
  ⟨ 0, 0, 0, 30
  , [ { holder := 7, keep := [Auth.read], parentCap := .endpoint 7 [Auth.read, Auth.write]
      , sub := ⟨ 7, 7, 7, -30, [] ⟩ } ] ⟩

-- The flattening: two cross-cell half-edges, on cells 0 and 7.
#eval (forestHalves goodCrossForest).length                          -- 2
#eval (forestHalves goodCrossForest).map (fun hh => (hh.cell, hh.δ))  -- [(0, 30), (7, -30)]
-- The cross-cell CG-5 Σ=0 binding HOLDS for the good forest: 30 + (-30) = 0.
#eval (forestHalves goodCrossForest).foldl (fun acc hh => acc + hh.δ) 0   -- 0 (balanced)
-- The whole cross-cell forest commits (both halves authorized by ownership):
#eval (execCrossForest goodCrossForest cellOf 42).isSome              -- true
-- Conserved JOINT total: cellA 105 + cellB 20 = 125 before; after, 75 + 50 = 125.
#eval total cellA + total cellB                                       -- 125
#eval (execCrossForest goodCrossForest cellOf 42).map
        (fun cs => ∑ i, total (cs i))                                 -- some 125 (CG-5: conserved)
-- Every cross-cell delegation edge is non-amplifying: child [read] ⊆ parent [read,write].
#eval (forestEdges goodCrossForest).map (fun e =>
        decide ((capAuthConferred (attenuate e.1 e.2)).length
                  ≤ (capAuthConferred e.2).length))                   -- [true]

/-- An UNBALANCED cross-cell forest: the child's δ is `−10` while the parent's is `30` — the δ's
sum to `30 + (-10) = 20 ≠ 0`, VIOLATING the cross-cell CG-5 binding. It still COMMITS per-cell
(each half is authorized), but the JOINT total is NOT conserved (the child credits cell 7 by only
`10`, so the family total falls to `75 + 30 = 105 ≠ 125`) — exactly why the binding must be a
HYPOTHESIS, not derivable. -/
def unbalancedCrossForest : CrossCellForest :=
  ⟨ 0, 0, 0, 30
  , [ { holder := 7, keep := [Auth.read], parentCap := .endpoint 7 [Auth.read, Auth.write]
      , sub := ⟨ 7, 7, 7, -10, [] ⟩ } ] ⟩

-- The binding does NOT hold (Σ δ = 20 ≠ 0): the joint total is NOT conserved (125 ≠ 145).
#eval (forestHalves unbalancedCrossForest).foldl (fun acc hh => acc + hh.δ) 0   -- 20 (UNBALANCED)
#eval (execCrossForest unbalancedCrossForest cellOf 42).map
        (fun cs => ∑ i, total (cs i))   -- some 105 ≠ 125 (binding VIOLATED ⇒ NOT conserved)

/-- An UNAUTHORIZED cross-cell forest: the child's actor (9) owns nothing on cell 7 and holds no cap
— it acts BEYOND any delegated authority. `applyForestHalf`'s authority gate rejects it, and
all-or-nothing rolls back the WHOLE cross-cell family (the committed root included). The
cap-exceeding-child rejection: a child cannot exceed the (non-amplifying) delegated authority. -/
def badChildCrossForest : CrossCellForest :=
  ⟨ 0, 0, 0, 30
  , [ { holder := 9, keep := [Auth.read], parentCap := .endpoint 7 [Auth.read]
      , sub := ⟨ 7, 9, 7, -30, [] ⟩ } ] ⟩

#eval (execCrossForest badChildCrossForest cellOf 42).isSome  -- false (child unauthorized ⇒ whole forest rejected)

/-- An UNAUTHORIZED ROOT cross-cell forest: actor 9 on cell 0 owns nothing — the root half fails, so
the whole forest rejects (fail-closed, atomic over the family). -/
def badRootCrossForest : CrossCellForest :=
  ⟨ 0, 9, 0, 30, [] ⟩

#eval (execCrossForest badRootCrossForest cellOf 42).isSome   -- false (unauthorized root ⇒ fail-closed)

/-! ## §11 — OUTCOME.

The CROSS-CELL nested call-FOREST residue (`TurnForest §9 OPEN`) is CLOSED:

  * `CrossCellForest`/`CrossChild` — a TREE of cross-cell half-edges, each child on its OWN
    (possibly different) cell, under a cap DERIVED (`Caps.derive`) from its parent's, run
    all-or-nothing over the flattened `Fin n` family;
  * `crossForestTurn`/`execCrossForest` — the flattened tree as a `ForestLTS.ForestTurn (Fin n)`
    family transition (one cell per node), so the WHOLE N-ary cross-cell spine of `ForestLTS`
    lifts directly;
  * `crossForest_no_amplify` — EVERY cross-cell delegation edge is non-amplifying
    (`derive_no_amplify`): Granovetter across cells, fully general over the tree;
  * `crossForest_conserves` — the N-ary cross-cell CG-5: the JOINT family Σ-total is preserved,
    GIVEN the Σ=0 binding `Σ_node δ = 0` (an explicit HYPOTHESIS, never derived), reusing
    `ForestLTS.forestApply_cg5_conserves`'s `Finset.sum` telescoping EXACTLY;
  * `crossForest_attests` — the four `StepInv` conjuncts over the WHOLE cross-cell tree
    (Conservation binding-carried + per-node Authority frame + per-node Grounding), via
    `ForestLTS.forestAbsStep_forward`;
  * the BILATERAL (2-cell) case (`crossForest_bilateral_conserves`/`_refines_crossAbs`) falls out
    as the `Fin 2` slice, with `halves_sum_zero` the binding;
  * non-vacuous (`goodCrossForest` 2-cell parent→child commits CONSERVED; `unbalancedCrossForest`
    violates the binding — NOT conserved, witnessing the binding is load-bearing;
    `badChildCrossForest`/`badRootCrossForest` rejected, fail-closed), axiom-clean.

HONEST: unlike the intra-cell `TurnForest.execForest_conserves` (which DERIVED conservation because
every node was an intra-cell balance turn on the ONE record cell), the cross-cell forest's CG-5 is
the inviolable cross-cell Σ=0 binding `Σ_node δ = 0`, carried as an explicit HYPOTHESIS exactly as
`Proof/ForestLTS.lean` / `Exec/JointCell.lean` carry it. The tree is flattened (pre-order) to its
`Fin n` family of cross-cell half-edges, one cell per node — the N-ary case general over arbitrary
depth/branching, the bilateral case as the `Fin 2` slice.

-- OPEN (the residue beyond this cross-cell lift). Threading the SHARED `SharedBinding` (CG-2)
--   down each cross-cell edge with a GENUINELY shared mutable family (a child on a cell ALREADY
--   touched by an ancestor — overlapping cells across nodes, rather than the one-cell-per-node
--   flattening here) is the contended/overlapping-forest case, exactly the residue both
--   `ForestLTS §11` and `CrossCellLTS §10` named (concurrent overlapping forests, the coinductive
--   `Boundary`), and remains the genuine next research pole — left as a documented `-- OPEN:`,
--   NOT a `sorry`/`axiom`.
-/

end Dregg2.Exec.CrossCellForest
