/-
# Dregg2.Crypto.PrivateGraphRewrite

The bounded semantic relation for the first private graph-rewrite leaf.  This
is not the old `A → BC` example: the rule, injective substitution, preserved
context, old/new graphs, permutations, and commitment openings are all witness
data.  Bounds are deliberately small and canonical for a first devnet slice:

* four host-edge slots;
* two LHS and two RHS rule-edge slots;
* two preserved-context slots;
* four pattern variables;
* nodes and labels in `Fin 16`;
* a two-leaf ruleset commitment opening.

Padding is explicit (`active = false`) and canonical.  Live edges erase the
padding before interpreting the witness as the existing generic
`GraphRewrite.RewriteStep`.  The bounded relation strengthens that generic
relation with an injective substitution and a nonempty LHS; the current generic
`RewriteStep` itself only carries a homomorphism despite older "embedding"
prose.  Precisely, this first primitive is **injective match-driven bounded
hyperedge replacement**.  It is not yet categorical DPO: RHS-only variables are
not forced fresh and LHS-only variables do not yet carry a dangling-condition
check against the preserved context.  Those are explicit next-layer teeth, not
claims silently attributed to this relation.
-/
import Dregg2.Crypto.GraphRewrite
import Mathlib.Data.List.FinRange
import Dregg2.Tactics

namespace Dregg2.Crypto.PrivateGraphRewrite

open Dregg2.Crypto.Hypergraph
open Dregg2.Crypto.GraphRewrite

abbrev Node := Fin 16
abbrev Label := Fin 16
abbrev Var := Fin 4

def GRAPH_SLOTS : Nat := 4
def PATTERN_SLOTS : Nat := 2
def CONTEXT_SLOTS : Nat := 2
def DIGEST_WIDTH : Nat := 8
def PROTOCOL_VERSION : Int := 1
def SHAPE_ID : Int := 4216242
def GRAPH_STATE_TAG : Int := 7301

structure HostEdgeSlot where
  active : Bool
  label : Label
  src : Node
  dst : Node
  deriving DecidableEq, Repr

structure RuleEdgeSlot where
  active : Bool
  label : Label
  src : Var
  dst : Var
  deriving DecidableEq, Repr

def HostEdgeSlot.canonicalPadding (e : HostEdgeSlot) : Prop :=
  e.active = false → e.label = 0 ∧ e.src = 0 ∧ e.dst = 0

def RuleEdgeSlot.canonicalPadding (e : RuleEdgeSlot) : Prop :=
  e.active = false → e.label = 0 ∧ e.src = 0 ∧ e.dst = 0

def HostEdgeSlot.edge (e : HostEdgeSlot) : Hyperedge Label Node :=
  (e.label, [e.src, e.dst])

def RuleEdgeSlot.edge (e : RuleEdgeSlot) : Hyperedge Label Var :=
  (e.label, [e.src, e.dst])

def liveHostEdges {n : Nat} (slots : Fin n → HostEdgeSlot) : List (Hyperedge Label Node) :=
  (List.ofFn slots).filterMap fun e => if e.active then some e.edge else none

def liveRuleEdges (slots : Fin 2 → RuleEdgeSlot) : List (Hyperedge Label Var) :=
  (List.ofFn slots).filterMap fun e => if e.active then some e.edge else none

structure BoundedGraph where
  slots : Fin 4 → HostEdgeSlot
  canonicalPadding : ∀ i, (slots i).canonicalPadding

structure BoundedPattern where
  slots : Fin 2 → RuleEdgeSlot
  canonicalPadding : ∀ i, (slots i).canonicalPadding

structure BoundedRule where
  lhs : BoundedPattern
  rhs : BoundedPattern

structure BoundedContext where
  slots : Fin 2 → HostEdgeSlot
  canonicalPadding : ∀ i, (slots i).canonicalPadding

def BoundedGraph.toHypergraph (g : BoundedGraph) : Hypergraph Label Node :=
  ⟨liveHostEdges g.slots⟩

def BoundedPattern.toHypergraph (p : BoundedPattern) : Hypergraph Label Var :=
  ⟨liveRuleEdges p.slots⟩

def BoundedRule.toRule (r : BoundedRule) : Rule Var Label :=
  ⟨r.lhs.toHypergraph, r.rhs.toHypergraph⟩

def BoundedContext.edges (ctx : BoundedContext) : List (Hyperedge Label Node) :=
  liveHostEdges ctx.slots

def instantiate (sigma : Var → Node) (p : BoundedPattern) : List (Hyperedge Label Node) :=
  instEdges sigma p.toHypergraph.edges

/-- An injective match-driven bounded hyperedge replacement step: selected rule membership, injective
match, nonempty deletion pattern, exact old decomposition up to permutation,
and a canonically ordered new context-plus-glue result.  Canonicalizing the new
endpoint is load-bearing: the committed public `newRoot` names the exact generic
`RewriteStep` target used by history linkage.  This relation deliberately does
not claim DPO freshness or the dangling condition. -/
def BoundedOneStep (rules : List BoundedRule)
    (oldGraph newGraph : BoundedGraph) (rule : BoundedRule)
    (sigma : Var → Node) (context : BoundedContext) : Prop :=
  rule ∈ rules ∧ Function.Injective sigma ∧
  liveRuleEdges rule.lhs.slots ≠ [] ∧
  oldGraph.toHypergraph.edges.Perm (context.edges ++ instantiate sigma rule.lhs) ∧
  newGraph.toHypergraph.edges = context.edges ++ instantiate sigma rule.rhs

/-- The bounded semantics really is an existing generic match-driven graph
rewrite step.  Its exact canonical committed `newGraph` is the generic step's
target; there is no order-changing endpoint substitution. -/
theorem boundedOneStep_to_rewriteStep
    {rules : List BoundedRule} {oldGraph newGraph : BoundedGraph}
    {rule : BoundedRule} {sigma : Var → Node} {context : BoundedContext}
    (h : BoundedOneStep rules oldGraph newGraph rule sigma context) :
    RewriteStep (rules.map BoundedRule.toRule) oldGraph.toHypergraph
      newGraph.toHypergraph := by
  rcases h with ⟨hr, hinj, hnonempty, hold, hnew⟩
  refine RewriteStep.step rule.toRule (List.mem_map_of_mem hr)
    sigma context.edges oldGraph.toHypergraph
    newGraph.toHypergraph ?_ ?_
  · simpa [BoundedRule.toRule, BoundedPattern.toHypergraph, instantiate] using hold
  · simpa [BoundedRule.toRule, BoundedPattern.toHypergraph, instantiate] using hnew

/-- The stronger fact omitted by the generic constructor: this slice's match
is an injective subgraph embedding. -/
theorem boundedOneStep_embeds
    {rules : List BoundedRule} {oldGraph newGraph : BoundedGraph}
    {rule : BoundedRule} {sigma : Var → Node} {context : BoundedContext}
    (h : BoundedOneStep rules oldGraph newGraph rule sigma context) :
    Embeds rule.lhs.toHypergraph oldGraph.toHypergraph := by
  rcases h with ⟨hr, hinj, hnonempty, hold, hnew⟩
  refine ⟨sigma, ?_, hinj⟩
  intro e he
  have hmapped : mapEdge sigma e ∈ instantiate sigma rule.lhs := by
    exact List.mem_map_of_mem he
  exact hold.mem_iff.mpr (List.mem_append_right _ hmapped)

abbrev Digest8 := Fin 8 → Int
abbrev Blind4 := Fin 4 → Int

def boolInt (b : Bool) : Int := if b then 1 else 0

def hostSlotFields (e : HostEdgeSlot) : List Int :=
  [boolInt e.active, e.label.val, e.src.val, e.dst.val]

def ruleSlotFields (e : RuleEdgeSlot) : List Int :=
  [boolInt e.active, e.label.val, e.src.val, e.dst.val]

def graphCoreInputs (g : BoundedGraph) : List Int :=
  (List.ofFn g.slots).flatMap hostSlotFields

def ruleCoreInputs (r : BoundedRule) : List Int :=
  (List.ofFn r.lhs.slots).flatMap ruleSlotFields ++
    (List.ofFn r.rhs.slots).flatMap ruleSlotFields

/-- The eight lanes of `H xs`. The hash is bound once, outside the lane function: a lane
function that called `H xs` itself recomputes the hash at every lane read, and a digest whose
inputs are other digests' lanes then costs 8^depth hash calls when evaluated (the `#guard`s of
`HierarchicalGraphCommitment` spent 40 s there). The same term up to `let` (zeta). -/
def digest8 (H : List Int → List Int) (xs : List Int) : Digest8 :=
  let out := H xs
  fun i => out.getD i.val 0

def graphRootInputs (core : Digest8) (blind : Blind4)
    (domain session version side : Int) : List Int :=
  List.ofFn core ++ List.ofFn blind ++ [domain, session, version, side]

def ruleLeafInputs (core : Digest8) (blind : Blind4)
    (domain version shape slot : Int) : List Int :=
  List.ofFn core ++ List.ofFn blind ++ [domain, version, shape, slot]

def rulesetNodeInputs (leaf0 leaf1 : Digest8) : List Int :=
  List.ofFn leaf0 ++ List.ofFn leaf1

structure PublicStatement where
  domain : Int
  session : Int
  version : Int
  shape : Int
  index : Int
  rulesetRoot : Digest8
  oldRoot : Digest8
  newRoot : Digest8

structure PrivateWitness where
  oldGraph : BoundedGraph
  newGraph : BoundedGraph
  rules : Fin 2 → BoundedRule
  sigma : Var → Node
  context : BoundedContext
  oldBlind : Blind4
  newBlind : Blind4
  ruleBlinds : Fin 2 → Blind4
  ruleSlot : Bool

def PrivateWitness.selectedRule (w : PrivateWitness) : BoundedRule :=
  if w.ruleSlot then w.rules 1 else w.rules 0

def ruleLeafDigest (H : List Int → List Int) (pub : PublicStatement)
    (w : PrivateWitness) (slot : Fin 2) : Digest8 :=
  digest8 H (ruleLeafInputs (digest8 H (ruleCoreInputs (w.rules slot)))
    (w.ruleBlinds slot) pub.domain pub.version pub.shape slot.val)

def CanonicalBlind (b : Blind4) : Prop :=
  ∀ i, 0 ≤ b i ∧ b i < 2013265921

/-- The public statement of the private leaf.  The graph roots are adjacent
8-felt endpoints for later history folding; the two-leaf ruleset root proves
membership of the privately selected rule. -/
structure Accepts (H : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : Prop where
  version : pub.version = PROTOCOL_VERSION
  shape : pub.shape = SHAPE_ID
  oldBlindCanonical : CanonicalBlind w.oldBlind
  newBlindCanonical : CanonicalBlind w.newBlind
  ruleBlindsCanonical : ∀ slot, CanonicalBlind (w.ruleBlinds slot)
  step : BoundedOneStep (List.ofFn w.rules) w.oldGraph w.newGraph
    w.selectedRule w.sigma w.context
  oldRoot :
    pub.oldRoot = digest8 H (graphRootInputs (digest8 H (graphCoreInputs w.oldGraph))
      w.oldBlind pub.domain pub.session pub.version GRAPH_STATE_TAG)
  newRoot :
    pub.newRoot = digest8 H (graphRootInputs (digest8 H (graphCoreInputs w.newGraph))
      w.newBlind pub.domain pub.session pub.version GRAPH_STATE_TAG)
  rulesetRoot :
    pub.rulesetRoot = digest8 H
      (rulesetNodeInputs (ruleLeafDigest H pub w 0) (ruleLeafDigest H pub w 1))

/-- The actual old-graph root preimage, parameterized by the core hash.  Keeping
this constructor explicit makes the collision boundary honest: a finite sponge
is never assumed mathematically injective. -/
def oldGraphRootPreimage (H : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  graphRootInputs (digest8 H (graphCoreInputs w.oldGraph))
    w.oldBlind pub.domain pub.session pub.version GRAPH_STATE_TAG

def newGraphRootPreimage (H : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  graphRootInputs (digest8 H (graphCoreInputs w.newGraph))
    w.newBlind pub.domain pub.session pub.version GRAPH_STATE_TAG

def rulesetRootPreimage (H : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  rulesetNodeInputs (ruleLeafDigest H pub w 0) (ruleLeafDigest H pub w 1)

def DigestCollision (H : List Int → List Int) : Prop :=
  ∃ left right, left ≠ right ∧ digest8 H left = digest8 H right

/-- Two distinct accepted old-graph root openings for one public statement are
an explicit full-eight-lane digest collision. -/
theorem two_accepting_old_openings_yield_collision
    {H : List Int → List Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : Accepts H pub left) (hr : Accepts H pub right)
    (hdiff : oldGraphRootPreimage H pub left ≠ oldGraphRootPreimage H pub right) :
    DigestCollision H := by
  refine ⟨oldGraphRootPreimage H pub left, oldGraphRootPreimage H pub right, hdiff, ?_⟩
  exact hl.oldRoot.symm.trans hr.oldRoot

/-- The same binding reduction for the exact committed new endpoint. -/
theorem two_accepting_new_openings_yield_collision
    {H : List Int → List Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : Accepts H pub left) (hr : Accepts H pub right)
    (hdiff : newGraphRootPreimage H pub left ≠ newGraphRootPreimage H pub right) :
    DigestCollision H := by
  refine ⟨newGraphRootPreimage H pub left, newGraphRootPreimage H pub right, hdiff, ?_⟩
  exact hl.newRoot.symm.trans hr.newRoot

/-- Opening the complete two-rule private ruleset in two distinct ways under
one accepted public root likewise produces a concrete digest collision. -/
theorem two_accepting_ruleset_openings_yield_collision
    {H : List Int → List Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : Accepts H pub left) (hr : Accepts H pub right)
    (hdiff : rulesetRootPreimage H pub left ≠ rulesetRootPreimage H pub right) :
    DigestCollision H := by
  refine ⟨rulesetRootPreimage H pub left, rulesetRootPreimage H pub right, hdiff, ?_⟩
  exact hl.rulesetRoot.symm.trans hr.rulesetRoot

theorem accepts_rewriteStep {H : List Int → List Int}
    {pub : PublicStatement} {w : PrivateWitness} (h : Accepts H pub w) :
    RewriteStep ((List.ofFn w.rules).map BoundedRule.toRule)
      w.oldGraph.toHypergraph w.newGraph.toHypergraph := by
  simpa using boundedOneStep_to_rewriteStep h.step

theorem accepts_embeds {H : List Int → List Int}
    {pub : PublicStatement} {w : PrivateWitness} (h : Accepts H pub w) :
    Embeds w.selectedRule.lhs.toHypergraph w.oldGraph.toHypergraph := by
  simpa using boundedOneStep_embeds h.step

#assert_all_clean [
  Dregg2.Crypto.PrivateGraphRewrite.boundedOneStep_to_rewriteStep,
  Dregg2.Crypto.PrivateGraphRewrite.boundedOneStep_embeds,
  Dregg2.Crypto.PrivateGraphRewrite.accepts_rewriteStep,
  Dregg2.Crypto.PrivateGraphRewrite.accepts_embeds,
  Dregg2.Crypto.PrivateGraphRewrite.two_accepting_old_openings_yield_collision,
  Dregg2.Crypto.PrivateGraphRewrite.two_accepting_new_openings_yield_collision,
  Dregg2.Crypto.PrivateGraphRewrite.two_accepting_ruleset_openings_yield_collision]

end Dregg2.Crypto.PrivateGraphRewrite
