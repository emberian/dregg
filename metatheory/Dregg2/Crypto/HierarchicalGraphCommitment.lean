/-
# Dregg2.Crypto.HierarchicalGraphCommitment

An isolated prototype for locally opening and updating the bounded private
graph commitment.  This module deliberately stops before any ZK/PCD claim:

* four graph-edge slots are committed as a depth-two, domain-separated tree;
* a leaf opening exposes one local edge (including its endpoint interface) and
  the two sibling digests needed to authenticate it;
* an ancestor update reuses the same path for an old and a new leaf, proving
  that only the authenticated leaf position changes;
* the semantic root is stable, while an occurrence wrapper separately binds a
  session, step index, and fresh blinding;
* a fold-use ledger consumes occurrence ids, not semantic proof ids.  The same
  memoized semantic proof can therefore be rebound at distinct occurrences,
  while consuming one occurrence twice fails closed.

## ⚑ The semantic-root binding is a REDUCTION on the keyed-ROM floor (07-24)

The former "collision-explicit faithfulness" section exported bare disjunctions
(`digest_eq_preimage_or_collision`, `genericRoot_eq_preimages_or_collision`,
`semanticRoot_eq_graph_or_collision`) whose escape branch was `DigestCollision H = ∃ collision`.
At any deployed compressing hash a collision EXISTS by pigeonhole, so each disjunction was
satisfiable through the collides branch with the binding never holding — a statement about
SOLUTIONS where hardness quantifies over EFFICIENT ADVERSARIES.  They are DELETED, replaced by
the §RomSuccessor reduction: the two-level tree commitment is restated at a SAMPLED keyed oracle
(roles LEAF/PAIR/ROOT as the key space), a root equivocation between two DISTINCT bounded graphs
is a first-class `RomForgery`, the extractor re-walks the fixed 14-node tree paying 12 queries
(`bindComp`, additive budget), and `semanticRoot_binds_rom` closes from the PROVED birthday floor
(`KeyedRomFloor.keyedRom_hard` via `romCarrier_binds`) — no floor hypothesis, no escape branch.

⚑ THE MODELLING STEP, STATED (`RomCarrierSites` header discipline): the sampled
`H : Role × Msg → Fin (2 ^ l)` idealises the fixed deployed eight-lane digest at an ASYMPTOTIC
width; nothing is claimed about the fixed public hash — CR of a fixed function is a conjecture,
not a Lean theorem.  What the reduction buys over the deleted disjunctions: the floor under it is
a THEOREM about the model instead of an escape branch that is unconditionally available at the
deployed object.

The retained `two_occurrence_openings_yield_collision` / `occurrenceId_alias_yields_collision`
are extraction teeth (they PRODUCE the collision witness from deployed check-passes), not
exported bindings; the flat occurrence absorb is a single-carrier site of
`SpongeForgeReduction.codeForge_binds_rom`'s generic shape.
-/
import Dregg2.Crypto.PrivateGraphRewrite
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics
import Mathlib.Tactic.FinCases

namespace Dregg2.Crypto.HierarchicalGraphCommitment

open Dregg2.Crypto.PrivateGraphRewrite

abbrev Hash := List Int → List Int
abbrev NodeId := Digest8

def LEAF_TAG : Int := 7401
def PAIR_TAG : Int := 7402
def ROOT_TAG : Int := 7403
def OCCURRENCE_TAG : Int := 7404
def OCCURRENCE_ID_TAG : Int := 7405

/-! ## Fixed-width encodings -/

def digestFields (d : Digest8) : List Int :=
  [d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7]

theorem digestFields_injective : Function.Injective digestFields := by
  intro a b h
  funext i
  fin_cases i <;> simp_all [digestFields]

def leafInputs (index : Fin 4) (slot : HostEdgeSlot) : List Int :=
  [LEAF_TAG, index.val, boolInt slot.active, slot.label.val, slot.src.val, slot.dst.val]

theorem boolInt_injective : Function.Injective boolInt := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolInt]

theorem leafInputs_injective (index : Fin 4) : Function.Injective (leafInputs index) := by
  intro a b h
  have hactive : boolInt a.active = boolInt b.active := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 2 0) h
  have hlabel : a.label.val = b.label.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 3 0) h
  have hsrc : a.src.val = b.src.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 4 0) h
  have hdst : a.dst.val = b.dst.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 5 0) h
  cases a
  cases b
  simp only at hactive hlabel hsrc hdst ⊢
  congr
  · exact boolInt_injective hactive
  · exact Fin.ext hlabel
  · exact Fin.ext hsrc
  · exact Fin.ext hdst

def nodeInputs (tag : Int) (left right : Digest8) : List Int :=
  [tag] ++ digestFields left ++ digestFields right

theorem nodeInputs_injective (tag : Int) :
    Function.Injective (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) := by
  intro a b h
  have hleft : digestFields a.1 = digestFields b.1 := by
    simpa [nodeInputs, digestFields] using congrArg (fun xs => (xs.drop 1).take 8) h
  have hright : digestFields a.2 = digestFields b.2 := by
    simpa [nodeInputs, digestFields] using congrArg (fun xs => xs.drop 9) h
  exact Prod.ext (digestFields_injective hleft) (digestFields_injective hright)

def leafDigest (H : Hash) (index : Fin 4) (slot : HostEdgeSlot) : Digest8 :=
  digest8 H (leafInputs index slot)

def nodeDigest (H : Hash) (tag : Int) (left right : Digest8) : Digest8 :=
  digest8 H (nodeInputs tag left right)

def canonicalSlotB (slot : HostEdgeSlot) : Bool :=
  if slot.active then true
  else slot.label == 0 && slot.src == 0 && slot.dst == 0

theorem canonicalSlotB_iff (slot : HostEdgeSlot) :
    canonicalSlotB slot = true ↔ slot.canonicalPadding := by
  cases hactive : slot.active <;>
    simp [canonicalSlotB, HostEdgeSlot.canonicalPadding, hactive, and_assoc]

/-! ## A four-leaf hierarchical semantic commitment -/

def leftPair (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1))

def rightPair (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3))

/-- A stable semantic root.  Session, step index, and hiding randomness are
bound separately by `occurrenceRoot`; they do not poison the memo key. -/
def semanticRoot (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g)

structure Path4 where
  /-- The other leaf in the selected leaf's pair. -/
  siblingLeaf : Digest8
  /-- The complete sibling pair at the root. -/
  siblingPair : Digest8
  deriving DecidableEq

def rootFromPath (H : Hash) (index : Fin 4) (leaf : Digest8) (path : Path4) : Digest8 :=
  match index.val with
  | 0 => nodeDigest H ROOT_TAG
      (nodeDigest H PAIR_TAG leaf path.siblingLeaf) path.siblingPair
  | 1 => nodeDigest H ROOT_TAG
      (nodeDigest H PAIR_TAG path.siblingLeaf leaf) path.siblingPair
  | 2 => nodeDigest H ROOT_TAG path.siblingPair
      (nodeDigest H PAIR_TAG leaf path.siblingLeaf)
  | _ => nodeDigest H ROOT_TAG path.siblingPair
      (nodeDigest H PAIR_TAG path.siblingLeaf leaf)

def pathFor (H : Hash) (g : BoundedGraph) (index : Fin 4) : Path4 :=
  match index.val with
  | 0 => ⟨leafDigest H 1 (g.slots 1), rightPair H g⟩
  | 1 => ⟨leafDigest H 0 (g.slots 0), rightPair H g⟩
  | 2 => ⟨leafDigest H 3 (g.slots 3), leftPair H g⟩
  | _ => ⟨leafDigest H 2 (g.slots 2), leftPair H g⟩

theorem pathFor_reconstructs (H : Hash) (g : BoundedGraph) (index : Fin 4) :
    rootFromPath H index (leafDigest H index (g.slots index)) (pathFor H g index) =
      semanticRoot H g := by
  fin_cases index <;> rfl

structure LeafOpening where
  index : Fin 4
  slot : HostEdgeSlot
  path : Path4
  deriving DecidableEq

def LeafOpening.canonical (opening : LeafOpening) : Prop :=
  opening.slot.canonicalPadding

def LeafOpening.check (H : Hash) (claimedRoot : Digest8) (opening : LeafOpening) : Bool :=
  canonicalSlotB opening.slot && decide
    (digestFields (rootFromPath H opening.index (leafDigest H opening.index opening.slot) opening.path) =
      digestFields claimedRoot)

def openLeaf (H : Hash) (g : BoundedGraph) (index : Fin 4) : LeafOpening :=
  ⟨index, g.slots index, pathFor H g index⟩

theorem openLeaf_checks (H : Hash) (g : BoundedGraph) (index : Fin 4) :
    (openLeaf H g index).check H (semanticRoot H g) = true := by
  rw [LeafOpening.check, Bool.and_eq_true]
  constructor
  · exact (canonicalSlotB_iff _).mpr (g.canonicalPadding index)
  · change decide
      (digestFields
        (rootFromPath H index (leafDigest H index (g.slots index)) (pathFor H g index)) =
          digestFields (semanticRoot H g)) = true
    exact decide_eq_true (congrArg digestFields (pathFor_reconstructs H g index))

/-- The opened active edge exposes its two endpoint nodes as the local rewrite
interface.  No unrelated graph slot is revealed. -/
structure InterfaceOpening where
  leaf : LeafOpening
  src : Node
  dst : Node
  deriving DecidableEq

def InterfaceOpening.check (H : Hash) (claimedRoot : Digest8)
    (opening : InterfaceOpening) : Bool :=
  opening.leaf.check H claimedRoot &&
    decide (opening.leaf.slot.active = true ∧
      opening.src = opening.leaf.slot.src ∧ opening.dst = opening.leaf.slot.dst)

def openInterface (H : Hash) (g : BoundedGraph) (index : Fin 4) : InterfaceOpening :=
  ⟨openLeaf H g index, (g.slots index).src, (g.slots index).dst⟩

theorem openInterface_checks (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (hactive : (g.slots index).active = true) :
    (openInterface H g index).check H (semanticRoot H g) = true := by
  rw [InterfaceOpening.check, Bool.and_eq_true]
  constructor
  · exact openLeaf_checks H g index
  · simp [openInterface, openLeaf, hactive]

/-- A two-edge local redex.  The distinct-index tooth prevents presenting one
authenticated graph leaf twice as a two-edge redex. -/
structure Redex2Opening where
  first : InterfaceOpening
  second : InterfaceOpening
  deriving DecidableEq

def Redex2Opening.check (H : Hash) (claimedRoot : Digest8)
    (opening : Redex2Opening) : Bool :=
  opening.first.check H claimedRoot && opening.second.check H claimedRoot &&
    decide (opening.first.leaf.index ≠ opening.second.leaf.index)

def openRedex2 (H : Hash) (g : BoundedGraph) (first second : Fin 4) : Redex2Opening :=
  ⟨openInterface H g first, openInterface H g second⟩

theorem openRedex2_checks (H : Hash) (g : BoundedGraph) (first second : Fin 4)
    (hfirst : (g.slots first).active = true) (hsecond : (g.slots second).active = true)
    (hdistinct : first ≠ second) :
    (openRedex2 H g first second).check H (semanticRoot H g) = true := by
  rw [Redex2Opening.check]
  simp only [openRedex2]
  rw [openInterface_checks H g first hfirst, openInterface_checks H g second hsecond]
  simp [openInterface, openLeaf]
  exact decide_eq_true hdistinct

/-! ## Same-path authenticated ancestor updates -/

structure AncestorUpdate where
  index : Fin 4
  before : HostEdgeSlot
  after : HostEdgeSlot
  path : Path4
  deriving DecidableEq

def AncestorUpdate.check (H : Hash) (beforeRoot afterRoot : Digest8)
    (update : AncestorUpdate) : Bool :=
  canonicalSlotB update.before && canonicalSlotB update.after &&
    decide (digestFields
      (rootFromPath H update.index (leafDigest H update.index update.before) update.path) =
        digestFields beforeRoot) &&
    decide (digestFields
      (rootFromPath H update.index (leafDigest H update.index update.after) update.path) =
        digestFields afterRoot)

def replaceSlot (g : BoundedGraph) (index : Fin 4) (slot : HostEdgeSlot)
    (hcanonical : slot.canonicalPadding) : BoundedGraph where
  slots := Function.update g.slots index slot
  canonicalPadding := by
    intro i
    by_cases h : i = index
    · subst i
      simpa using hcanonical
    · simpa [Function.update, h] using g.canonicalPadding i

theorem pathFor_replaceSlot (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (slot : HostEdgeSlot) (hcanonical : slot.canonicalPadding) :
    pathFor H (replaceSlot g index slot hcanonical) index = pathFor H g index := by
  fin_cases index <;> simp [pathFor, replaceSlot, leftPair, rightPair, Function.update]

def updateLeaf (H : Hash) (g : BoundedGraph) (index : Fin 4) (after : HostEdgeSlot) :
    AncestorUpdate :=
  ⟨index, g.slots index, after, pathFor H g index⟩

theorem updateLeaf_checks (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (after : HostEdgeSlot) (hcanonical : after.canonicalPadding) :
    (updateLeaf H g index after).check H (semanticRoot H g)
      (semanticRoot H (replaceSlot g index after hcanonical)) = true := by
  have hbeforeCanonical : canonicalSlotB (g.slots index) = true :=
    (canonicalSlotB_iff _).mpr (g.canonicalPadding index)
  have hafterCanonical : canonicalSlotB after = true :=
    (canonicalSlotB_iff _).mpr hcanonical
  have hbeforeRoot := pathFor_reconstructs H g index
  have hafterRoot := pathFor_reconstructs H (replaceSlot g index after hcanonical) index
  have hpath := pathFor_replaceSlot H g index after hcanonical
  have hafterRoot' :
      rootFromPath H index (leafDigest H index after) (pathFor H g index) =
        semanticRoot H (replaceSlot g index after hcanonical) := by
    rw [← hpath]
    simpa [replaceSlot] using hafterRoot
  simp only [AncestorUpdate.check, updateLeaf, hbeforeCanonical, hafterCanonical,
    Bool.true_and]
  rw [Bool.and_eq_true]
  constructor
  · exact decide_eq_true (congrArg digestFields hbeforeRoot)
  · exact decide_eq_true (congrArg digestFields hafterRoot')

/-! ## ⚑ §RomSuccessor — the semantic-root binding, DISCHARGED on the PROVED keyed-ROM floor.

The deleted `digest_eq_preimage_or_collision` → `genericRoot_eq_preimages_or_collision` →
`semanticRoot_eq_graph_or_collision` chain exported `binds ∨ DigestCollision H` — an escape
branch that is unconditionally available at any deployed compressing hash (pigeonhole), so the
exported binding held through the collides branch without binding anything.  The successor is a
REDUCTION (header): the forger is an ORACLE PROGRAM over the sampled role-keyed oracle, the
extractor re-walks the fixed two-level tree paying 12 queries, and the floor is
`keyedRom_hard` — the birthday bound, a THEOREM. -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

/-- The three deployed domain-separation roles of the two-level tree — the key space of the
sampled oracle (the ROM face of the absorbed `LEAF_TAG`/`PAIR_TAG`/`ROOT_TAG` prefixes). -/
abbrev HgcRole : Type := Fin 3

/-- The leaf role (`LEAF_TAG`'s key). -/
def hgcLeafRole : HgcRole := 0
/-- The pair-node role (`PAIR_TAG`'s key). -/
def hgcPairRole : HgcRole := 1
/-- The root-node role (`ROOT_TAG`'s key). -/
def hgcRootRole : HgcRole := 2

/-- One committed edge slot as finite data — exactly the `leafInputs` payload after the tag and
index: activity bit, label, and the two endpoints. -/
abbrev SlotEnc : Type := Bool × Label × Node × Node

/-- The lossless slot encoding (the `leafInputs` fields, minus the constant tag). -/
def slotEnc (s : HostEdgeSlot) : SlotEnc := (s.active, s.label, s.src, s.dst)

/-- `slotEnc` loses nothing — the ROM leaf payload identifies the deployed slot. -/
theorem slotEnc_injective : Function.Injective slotEnc := by
  intro a b h
  cases a; cases b
  simp only [slotEnc, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp_all

/-- A bounded graph's committed payload: its four indexed slots. -/
abbrev GraphSlots : Type := Fin 4 → SlotEnc

/-- The graph payload encoding — the four slots, in leaf order. -/
def graphEnc (g : BoundedGraph) : GraphSlots := fun i => slotEnc (g.slots i)

/-- `graphEnc` loses nothing: two distinct bounded graphs stay distinct ROM payloads (the
canonical-padding field is propositional, so the slots determine the graph). -/
theorem graphEnc_injective : Function.Injective graphEnc := by
  intro g₁ g₂ h
  cases g₁ with
  | mk s₁ c₁ =>
    cases g₂ with
    | mk s₂ c₂ =>
      have hs : s₁ = s₂ := funext fun i => slotEnc_injective (congrFun h i)
      subst hs
      rfl

/-- **THE ORACLE MESSAGE DOMAIN** — the deployed absorb schedule, domain-separated by
constructor: `inl` an indexed leaf block (the `leafInputs` payload), `inr` a two-child node
block (a pair of digests — the `nodeInputs` payload; whether it is a PAIR or the ROOT absorb is
carried by the KEY).  ⚑ The digest space `Fin (2 ^ l)` is the labelled modelling step: the
deployed eight-lane digest is idealised at asymptotic width. -/
abbrev HgcRomMsg (l : ℕ) : Type := (Fin 4 × SlotEnc) ⊕ (Fin (2 ^ l) × Fin (2 ^ l))

/-- **THE TREE'S KEYED ROM FAMILY** — keyed by the three deployed roles. -/
def hgcRomFamily : KeyedRomFamily :=
  flatFamily HgcRole inferInstance inferInstance ⟨0⟩ HgcRomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (0, false, 0, 0, 0)⟩)

/-- The family's width obligation, closed by construction. -/
theorem hgcRomFamily_card_R (l : ℕ) :
    letI := hgcRomFamily.rFin l
    Fintype.card (hgcRomFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE TREE CARRIER** — the identity carrier over the tree's own message shape, tag in the
context: one commitment = one oracle query at a role-tagged block.  All three tree layers
(leaf, pair, root) are equivocations of THIS carrier at their role. -/
def hgcRomCarrier : RomCarrier hgcRomFamily :=
  taggedCarrier _ (fun _ => Unit) (fun l => HgcRomMsg l)
    (fun _ => inferInstance)
    (fun _ _ v => v)
    (fun _ _ _ _ h => h)

/-- **THE SEMANTIC ROOT AT THE SAMPLED ORACLE** — the ROM restatement of `semanticRoot`:
`H (ROOT, [H (PAIR, [H (LEAF, leaf₀), H (LEAF, leaf₁)]), H (PAIR, [H (LEAF, leaf₂),
H (LEAF, leaf₃)])])`, the two-level tree with the inner digests genuinely re-absorbed. -/
def hgcRomRoot (l : ℕ) (H : HgcRole × HgcRomMsg l → Fin (2 ^ l)) (g : GraphSlots) :
    Fin (2 ^ l) :=
  H (hgcRootRole, Sum.inr
    (H (hgcPairRole, Sum.inr
        (H (hgcLeafRole, Sum.inl (0, g 0)), H (hgcLeafRole, Sum.inl (1, g 1)))),
     H (hgcPairRole, Sum.inr
        (H (hgcLeafRole, Sum.inl (2, g 2)), H (hgcLeafRole, Sum.inl (3, g 3))))))

/-- **THE SEMANTIC-ROOT FORGERY** — two DISTINCT graph payloads whose tree roots agree at the
sampled oracle.  The break is IN the win relation, checked against the sampled oracle. -/
def hgcRomForgery : RomForgery hgcRomFamily where
  Ans := fun _ => GraphSlots × GraphSlots
  wins := fun l H p => p.1 ≠ p.2 ∧ hgcRomRoot l H p.1 = hgcRomRoot l H p.2
  winsDec := fun _ _ _ => instDecidableAnd

/-- The semantic-root break game. -/
abbrev hgcRomBreakGame : Game := hgcRomForgery.game

/-- **⚑ THE OBJECT-LEVEL FORGERY IS A WIN** — two DISTINCT `BoundedGraph`s whose ROM semantic
roots agree are a game win (`graphEnc_injective` keeps them distinct as payloads).  The successor
shape of the deleted `semanticRoot_eq_graph_or_collision`'s binding branch. -/
theorem hgcRom_graph_forgery_is_break (l : ℕ) (H : hgcRomBreakGame.Inst l)
    {g₁ g₂ : BoundedGraph} (hne : g₁ ≠ g₂)
    (heq : hgcRomRoot l H (graphEnc g₁) = hgcRomRoot l H (graphEnc g₂)) :
    hgcRomBreakGame.wins l H (graphEnc g₁, graphEnc g₂) :=
  ⟨fun h => hne (graphEnc_injective h), heq⟩

/-- **THE TREE-WALK SELECTION** — given the forger's two payloads and the re-queried digests of
both trees, name the shallowest layer at which the two trees' absorbed blocks differ.  Pure: the
queries were already paid by `hgcExtractComp`. -/
def hgcSelect (l : ℕ) (a : GraphSlots × GraphSlots)
    (l0 l1 l2 l3 m0 m1 m2 m3 pL pR qL qR : Fin (2 ^ l)) :
    hgcRomCarrier.Ctx l × hgcRomCarrier.Val l × hgcRomCarrier.Val l :=
  if ((pL, pR) : Fin (2 ^ l) × Fin (2 ^ l)) ≠ (qL, qR) then
    ((hgcRootRole, ()), Sum.inr (pL, pR), Sum.inr (qL, qR))
  else if ((l0, l1) : Fin (2 ^ l) × Fin (2 ^ l)) ≠ (m0, m1) then
    ((hgcPairRole, ()), Sum.inr (l0, l1), Sum.inr (m0, m1))
  else if ((l2, l3) : Fin (2 ^ l) × Fin (2 ^ l)) ≠ (m2, m3) then
    ((hgcPairRole, ()), Sum.inr (l2, l3), Sum.inr (m2, m3))
  else if a.1 0 ≠ a.2 0 then ((hgcLeafRole, ()), Sum.inl (0, a.1 0), Sum.inl (0, a.2 0))
  else if a.1 1 ≠ a.2 1 then ((hgcLeafRole, ()), Sum.inl (1, a.1 1), Sum.inl (1, a.2 1))
  else if a.1 2 ≠ a.2 2 then ((hgcLeafRole, ()), Sum.inl (2, a.1 2), Sum.inl (2, a.2 2))
  else ((hgcLeafRole, ()), Sum.inl (3, a.1 3), Sum.inl (3, a.2 3))

/-- **THE EXTRACTOR, AS AN ORACLE PROGRAM** — run the forger's program, then RE-WALK both trees
(eight leaf queries, four pair queries — the fixed 12-query overhead), then select the colliding
layer.  `bindComp` keeps the accounting additive: a `Q`-query forger yields a `Q + 12`-query
carrier equivocator. -/
def hgcExtractComp
    (M : ∀ l, OracleComp (hgcRomFamily.toRomFamily.D l) (hgcRomFamily.toRomFamily.R l)
      (hgcRomForgery.Ans l)) :
    RomCarrierComp hgcRomFamily hgcRomCarrier :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.1 0)) (fun l0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.1 1)) (fun l1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.1 2)) (fun l2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.1 3)) (fun l3 =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.2 0)) (fun m0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.2 1)) (fun m1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.2 2)) (fun m2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.2 3)) (fun m3 =>
    OracleComp.query (hgcPairRole, Sum.inr (l0, l1)) (fun pL =>
    OracleComp.query (hgcPairRole, Sum.inr (l2, l3)) (fun pR =>
    OracleComp.query (hgcPairRole, Sum.inr (m0, m1)) (fun qL =>
    OracleComp.query (hgcPairRole, Sum.inr (m2, m3)) (fun qR =>
    OracleComp.pure (hgcSelect l a l0 l1 l2 l3 m0 m1 m2 m3 pL pR qL qR))))))))))))))

/-- **⚑⚑ THE SEMANTIC-ROOT BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the
deleted `semanticRoot_eq_graph_or_collision` (and through `hgcRom_graph_forgery_is_break`, of
the whole deleted `_or_collision` chain): every query-bounded forger that equivocates the
two-level tree root between two DISTINCT bounded-graph payloads has NEGLIGIBLE advantage.

The peel is the tree walk: the root absorb differs (a root-role carrier equivocation), or the
root absorb agrees and some pair absorb differs (a pair-role equivocation through the shared
root digest), or all node absorbs agree and the first differing slot is a leaf-role
equivocation through the shared leaf digest.  Every case is a win of ONE carrier at the SAMPLED
oracle, and `romCarrier_binds` (hence `keyedRom_hard`, the birthday bound) kills it.  NO floor
hypothesis, NO escape branch. -/
theorem semanticRoot_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary hgcRomBreakGame)
    (hA : RomForgeryEff hgcRomFamily hgcRomForgery Q A) :
    Negl (gameAdv hgcRomBreakGame A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le (fun l => (gameAdv_mem_unit hgcRomBreakGame A l).1)
    (fun l => ?_)
    (romCarrier_binds hgcRomFamily hgcRomCarrier
      (fun l => Q l + 2 + 2 + 2 + 2 + 2 + 2)
      (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
        (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ hQ))))))
      hgcRomFamily_card_R
      (romCarrierAdv _ _ (hgcExtractComp M))
      ⟨hgcExtractComp M,
        fun l => (OracleComp.bindComp_queryBounded (hM l)
          (fun a => QueryBounded.query 11 _ _ (fun _ => QueryBounded.query 10 _ _
            (fun _ => QueryBounded.query 9 _ _ (fun _ => QueryBounded.query 8 _ _
            (fun _ => QueryBounded.query 7 _ _ (fun _ => QueryBounded.query 6 _ _
            (fun _ => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
            (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
            (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
            (fun _ => QueryBounded.pure 0 _)))))))))))))).mono
          (by show Q l + 12 ≤ Q l + 2 + 2 + 2 + 2 + 2 + 2; omega),
        fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ (hgcRomBreakGame.instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  have hBrun : (romCarrierAdv _ _ (hgcExtractComp M)).run l H
      = hgcSelect l a
          (H (hgcLeafRole, Sum.inl (0, a.1 0))) (H (hgcLeafRole, Sum.inl (1, a.1 1)))
          (H (hgcLeafRole, Sum.inl (2, a.1 2))) (H (hgcLeafRole, Sum.inl (3, a.1 3)))
          (H (hgcLeafRole, Sum.inl (0, a.2 0))) (H (hgcLeafRole, Sum.inl (1, a.2 1)))
          (H (hgcLeafRole, Sum.inl (2, a.2 2))) (H (hgcLeafRole, Sum.inl (3, a.2 3)))
          (H (hgcPairRole, Sum.inr
            (H (hgcLeafRole, Sum.inl (0, a.1 0)), H (hgcLeafRole, Sum.inl (1, a.1 1)))))
          (H (hgcPairRole, Sum.inr
            (H (hgcLeafRole, Sum.inl (2, a.1 2)), H (hgcLeafRole, Sum.inl (3, a.1 3)))))
          (H (hgcPairRole, Sum.inr
            (H (hgcLeafRole, Sum.inl (0, a.2 0)), H (hgcLeafRole, Sum.inl (1, a.2 1)))))
          (H (hgcPairRole, Sum.inr
            (H (hgcLeafRole, Sum.inl (2, a.2 2)), H (hgcLeafRole, Sum.inl (3, a.2 3))))) := by
    show (hgcExtractComp M l).eval H = _
    unfold hgcExtractComp
    erw [OracleComp.bindComp_eval, ← hArun]
    rfl
  rw [hBrun]
  unfold hgcSelect
  split_ifs with hRoot hL hR h0 h1 h2
  · -- root absorbs DIFFER under the shared root digest (`heq` IS the root equality).
    exact ⟨fun hc => hRoot (Sum.inr_injective hc), heq⟩
  · -- left pair absorb DIFFERS under the shared left-pair digest.
    exact ⟨fun hc => hL (Sum.inr_injective hc), congrArg Prod.fst (not_not.mp hRoot)⟩
  · -- right pair absorb DIFFERS under the shared right-pair digest.
    exact ⟨fun hc => hR (Sum.inr_injective hc), congrArg Prod.snd (not_not.mp hRoot)⟩
  · -- slot 0 differs under the shared leaf-0 digest.
    exact ⟨fun hc => h0 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hL)⟩
  · -- slot 1 differs under the shared leaf-1 digest.
    exact ⟨fun hc => h1 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.snd (not_not.mp hL)⟩
  · -- slot 2 differs under the shared leaf-2 digest.
    exact ⟨fun hc => h2 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hR)⟩
  · -- slots 0-2 agree, so slot 3 must differ (the payloads are distinct).
    have h3 : a.1 3 ≠ a.2 3 := by
      intro hc
      apply hne
      funext i
      fin_cases i
      · exact not_not.mp h0
      · exact not_not.mp h1
      · exact not_not.mp h2
      · exact hc
    exact ⟨fun hc => h3 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.snd (not_not.mp hR)⟩

/-- **(TOOTH — the game is WINNABLE and the admitted refuter-shape is DEFANGED.)** The `0`-query
constant answerer with two DISTINCT fixed payloads is IN the class, WINS at the constant oracle
(every digest coincides, so the two roots agree), and its advantage is NEGLIGIBLE by the bound —
the binding prices something genuinely nonzero, and the pigeonhole strategy that made the deleted
disjunction a free pass dies at the sampled oracle. -/
theorem hgcRom_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (v w : GraphSlots) (hvw : v ≠ w) :
    (RomForgeryEff hgcRomFamily hgcRomForgery Q
        ⟨fun l _ => ((v, w) : hgcRomForgery.Ans l)⟩)
      ∧ (∀ l, 0 < gameAdv hgcRomBreakGame ⟨fun l _ => ((v, w) : hgcRomForgery.Ans l)⟩ l)
      ∧ Negl (gameAdv hgcRomBreakGame ⟨fun l _ => ((v, w) : hgcRomForgery.Ans l)⟩) := by
  have hmem : RomForgeryEff hgcRomFamily hgcRomForgery Q
      ⟨fun l _ => ((v, w) : hgcRomForgery.Ans l)⟩ :=
    ⟨fun l => OracleComp.pure (v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, semanticRoot_binds_rom Q hQ _ hmem⟩
  obtain ⟨r₀⟩ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, by positivity⟩⟩
  refine @winProb_pos_of_witness _ (hgcRomBreakGame.instFin l) _ (fun _ => r₀) ?_
  exact (Adversary.hit_eq_true _ l _ ).mpr ⟨hvw, rfl⟩

/-- **(TOOTH — a non-negligible root equivocator is OUTSIDE the class.)** -/
theorem hgcRom_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary hgcRomBreakGame)
    (hnn : ¬ Negl (gameAdv hgcRomBreakGame A)) :
    ¬ RomForgeryEff hgcRomFamily hgcRomForgery Q A :=
  fun hA => hnn (semanticRoot_binds_rom Q hQ A hA)

end RomSuccessor

/-! ## Session-bound occurrence wrappers -/

def occurrenceInputs (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : List Int :=
  [OCCURRENCE_TAG, domain, session, version, index] ++ digestFields semantic ++ List.ofFn blind

def occurrenceRoot (H : Hash) (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : Digest8 :=
  digest8 H (occurrenceInputs semantic blind domain session version index)

structure OccurrenceOpening where
  semantic : Digest8
  blind : Blind4
  domain : Int
  session : Int
  version : Int
  index : Int

def canonicalBlindB (blind : Blind4) : Bool :=
  decide (0 ≤ blind 0 ∧ blind 0 < 2013265921) &&
  decide (0 ≤ blind 1 ∧ blind 1 < 2013265921) &&
  decide (0 ≤ blind 2 ∧ blind 2 < 2013265921) &&
  decide (0 ≤ blind 3 ∧ blind 3 < 2013265921)

theorem canonicalBlindB_iff (blind : Blind4) :
    canonicalBlindB blind = true ↔ CanonicalBlind blind := by
  simp only [canonicalBlindB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

def OccurrenceOpening.check (H : Hash) (claimedRoot : Digest8)
    (opening : OccurrenceOpening) : Bool :=
  canonicalBlindB opening.blind && decide
    (digestFields (occurrenceRoot H opening.semantic opening.blind
      opening.domain opening.session opening.version opening.index) = digestFields claimedRoot)

def openOccurrence (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : OccurrenceOpening :=
  ⟨semantic, blind, domain, session, version, index⟩

theorem openOccurrence_checks (H : Hash) (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) (hcanonical : CanonicalBlind blind) :
    (openOccurrence semantic blind domain session version index).check H
      (occurrenceRoot H semantic blind domain session version index) = true := by
  rw [OccurrenceOpening.check, Bool.and_eq_true]
  exact ⟨(canonicalBlindB_iff blind).mpr hcanonical, decide_eq_true rfl⟩

theorem two_occurrence_openings_yield_collision (H : Hash) {claimedRoot : Digest8}
    {left right : OccurrenceOpening}
    (hl : left.check H claimedRoot = true) (hr : right.check H claimedRoot = true)
    (hdiff : occurrenceInputs left.semantic left.blind left.domain left.session left.version left.index ≠
      occurrenceInputs right.semantic right.blind right.domain right.session right.version right.index) :
    DigestCollision H := by
  rw [OccurrenceOpening.check, Bool.and_eq_true] at hl hr
  have hlroot : occurrenceRoot H left.semantic left.blind left.domain left.session left.version left.index =
      claimedRoot := digestFields_injective (of_decide_eq_true hl.2)
  have hrroot : occurrenceRoot H right.semantic right.blind right.domain right.session right.version right.index =
      claimedRoot := digestFields_injective (of_decide_eq_true hr.2)
  exact ⟨_, _, hdiff, hlroot.trans hrroot.symm⟩

/-- The consumed fold identity is occurrence-specific and deliberately does
not depend on the cached semantic proof id.  Otherwise one occurrence could be
consumed twice merely by presenting two semantic proof ids. -/
def occurrenceIdInputs (occurrence : Digest8) : List Int :=
  [OCCURRENCE_ID_TAG] ++ digestFields occurrence

def occurrenceId (H : Hash) (occurrence : Digest8) : NodeId :=
  digest8 H (occurrenceIdInputs occurrence)

structure FoldUse where
  semanticProofId : NodeId
  occurrenceRoot : Digest8
  useId : NodeId
  deriving DecidableEq

def FoldUse.check (H : Hash) (use : FoldUse) : Bool :=
  decide (digestFields use.useId =
    digestFields (occurrenceId H use.occurrenceRoot))

/-- Distinct occurrence roots with the same consumed id expose the exact hash
collision that can otherwise cause an alias/refusal. -/
theorem occurrenceId_alias_yields_collision (H : Hash) {left right : Digest8}
    (hid : occurrenceId H left = occurrenceId H right)
    (hdiff : occurrenceIdInputs left ≠ occurrenceIdInputs right) : DigestCollision H :=
  ⟨occurrenceIdInputs left, occurrenceIdInputs right, hdiff, hid⟩

abbrev UseLedger := List NodeId

/-- Consume an occurrence exactly once.  The semantic proof id is intentionally
not inserted into the ledger, so memoized semantics can be rebound safely. -/
def consume (H : Hash) (ledger : UseLedger) (use : FoldUse) : Option UseLedger :=
  if use.check H then
    if use.useId ∈ ledger then none else some (use.useId :: ledger)
  else none

theorem consume_fresh {H : Hash} {ledger next : UseLedger} {use : FoldUse}
    (hledger : ledger.Nodup) (h : consume H ledger use = some next) :
    next.Nodup ∧ use.useId ∈ next := by
  unfold consume at h
  split at h
  next hcheck =>
    split at h
    next hmem => contradiction
    next hnotmem =>
      simp only [Option.some.injEq] at h
      subst next
      exact ⟨List.nodup_cons.mpr ⟨hnotmem, hledger⟩, List.mem_cons_self⟩
  next => contradiction

theorem consume_duplicate_refused (H : Hash) (ledger : UseLedger) (use : FoldUse)
    (hcheck : use.check H = true) :
    consume H (use.useId :: ledger) use = none := by
  simp [consume, hcheck]

theorem consume_fresh_occurrence_succeeds (H : Hash) (ledger : UseLedger) (use : FoldUse)
    (hcheck : use.check H = true) (hfresh : use.useId ∉ ledger) :
    consume H ledger use = some (use.useId :: ledger) := by
  simp [consume, hcheck, hfresh]

/-! ## Executable non-vacuity and refusal teeth -/

namespace Reference

def toyHash (xs : List Int) : List Int :=
  List.ofFn fun lane : Fin 8 =>
    xs.foldl (fun acc item =>
      (acc * (Int.ofNat lane.val + 19) + item + Int.ofNat lane.val) % 1000003)
      (Int.ofNat lane.val + 17)

def graph : BoundedGraph where
  slots
    | 0 => ⟨true, 1, 1, 2⟩
    | 1 => ⟨true, 2, 2, 3⟩
    | 2 => ⟨true, 3, 3, 4⟩
    | _ => ⟨false, 0, 0, 0⟩
  canonicalPadding := by
    intro i
    fin_cases i <;> simp [HostEdgeSlot.canonicalPadding]

def replacement : HostEdgeSlot := ⟨true, 7, 1, 3⟩

#guard (openLeaf toyHash graph 1).check toyHash (semanticRoot toyHash graph)
#guard (openInterface toyHash graph 1).check toyHash (semanticRoot toyHash graph)
#guard (openRedex2 toyHash graph 0 1).check toyHash (semanticRoot toyHash graph)
#guard (updateLeaf toyHash graph 1 replacement).check toyHash (semanticRoot toyHash graph)
  (semanticRoot toyHash (replaceSlot graph 1 replacement (by
    simp [replacement, HostEdgeSlot.canonicalPadding])))

def badDuplicateRedex : Redex2Opening :=
  let opened := openInterface toyHash graph 1
  ⟨opened, opened⟩

#guard !(badDuplicateRedex.check toyHash (semanticRoot toyHash graph))

def blind : Blind4 := fun i => i.val + 11

def occurrenceA : Digest8 :=
  occurrenceRoot toyHash (semanticRoot toyHash graph) blind 9 100 1 4

def occurrenceB : Digest8 :=
  occurrenceRoot toyHash (semanticRoot toyHash graph) blind 9 100 1 5

def semanticProof : NodeId := digest8 toyHash [991, 992, 993]

def wrapperA : OccurrenceOpening :=
  openOccurrence (semanticRoot toyHash graph) blind 9 100 1 4

def wrapperWrongIndex : OccurrenceOpening :=
  openOccurrence (semanticRoot toyHash graph) blind 9 100 1 5

#guard wrapperA.check toyHash occurrenceA
#guard !(wrapperWrongIndex.check toyHash occurrenceA)

def useA : FoldUse :=
  ⟨semanticProof, occurrenceA, occurrenceId toyHash occurrenceA⟩

def useB : FoldUse :=
  ⟨semanticProof, occurrenceB, occurrenceId toyHash occurrenceB⟩

def alternateSemanticProof : NodeId := digest8 toyHash [881, 882, 883]

def useAAlternateProof : FoldUse :=
  ⟨alternateSemanticProof, occurrenceA, occurrenceId toyHash occurrenceA⟩

#guard (consume toyHash [] useA).isSome
#guard (consume toyHash [useA.useId] useA).isNone
#guard (consume toyHash [useA.useId] useAAlternateProof).isNone
#guard (consume toyHash [useA.useId] useB).isSome

end Reference

#assert_all_clean [
  digestFields_injective,
  leafInputs_injective,
  nodeInputs_injective,
  pathFor_reconstructs,
  openLeaf_checks,
  openInterface_checks,
  openRedex2_checks,
  pathFor_replaceSlot,
  updateLeaf_checks,
  slotEnc_injective,
  graphEnc_injective,
  hgcRomFamily_card_R,
  hgcRom_graph_forgery_is_break,
  semanticRoot_binds_rom,
  hgcRom_constAnswer_defanged,
  hgcRom_nonNegl_forger_excluded,
  openOccurrence_checks,
  two_occurrence_openings_yield_collision,
  occurrenceId_alias_yields_collision,
  consume_fresh,
  consume_duplicate_refused,
  consume_fresh_occurrence_succeeds]

end Dregg2.Crypto.HierarchicalGraphCommitment
