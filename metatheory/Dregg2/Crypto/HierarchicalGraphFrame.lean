/-

⚠ ADVERSARIAL VERIFY: **THE JOIN IS NOW SUPPLIED (§2b); READ WHAT IT DOES AND DOES NOT BUY.**

The previous state of this file was two halves that never met:

* §1 (`frame_of_absorbInjective`, `afterGraph_eq_replaceSlot`) IS over the real `AncestorUpdate.check`
  and the real `semanticRoot` — but it is conditional on `TreeAbsorbInjective`, and THIS FILE ITSELF
  REFUTES that hypothesis for every bounded-lane digest (`not_treeAbsorbInjective_of_boundedLanes`,
  a pinned keystone). §1's price is ZERO and §1 is UNCHANGED: it stays a statement about the LAYOUT.
* §2 (`frame_binds_rom`) has no such assumption — but its objects (`romRootFromPath`, `hgcRomRoot`,
  `GraphSlots`, `romPathFor`) were hand-written ROM ANALOGUES with no lemma anywhere in `Dregg2/`
  relating them to `rootFromPath` / `pathFor` / `semanticRoot` / `AncestorUpdate`.

**§2b closes that gap**, in the shape the sibling `HierarchicalGraphCommitment.lean` uses for its own
game (`hgcRom_graph_forgery_is_break`). `romHash l H : Hash` instantiates the DEPLOYED `Hash` interface
with the sampled role-keyed oracle (tag dispatch + round-tripping decoders), and the three named-missing
bridges are proved — `romHash_semanticRoot` (hgcRomRoot ↔ semanticRoot), `romHash_pathFor` (romPathFor ↔
pathFor), `romHash_rootFromPath` (romRootFromPath ↔ rootFromPath, for an ARBITRARY adversarial path).
`frame_object_break_is_win` then turns an accepted-but-non-framing deployed `AncestorUpdate` into a
CONCRETE `frameForgery` win, and `objFrame_binds_rom` prices it: every query-bounded adversary producing
an accepted `AncestorUpdate` whose committed graphs violate the frame conclusion has NEGLIGIBLE
advantage — NO `TreeAbsorbInjective`, NO floor hypothesis, NO `∨ ∃ collision`.
`objFrame_constAnswer_defanged` exhibits an oracle where the deployed check ACCEPTS while the frame
fails, so the priced event is nonempty and the statement is not satisfied by "the check never accepts".

⚠ WHAT REMAINS OPEN, PRECISELY. (a) `romHash l H` is the SAMPLED oracle wearing the deployed `Hash`
type, not Poseidon2 — the `RomCarrierSites` modelling step is inherited verbatim and is now visible at
the `Hash` interface itself; nothing is claimed about the fixed public digest. (b) the eight-lane digest
is collapsed to ONE `λ`-growing lane on BOTH sides — `embedDig` writes lane 0 and `toRomDig` reads lane
0 — so the deployed ~31-bit felt width is NOT modelled, and the modelled hash is strictly WEAKER than
the deployed one on lanes 1-7 (a forger may vary them freely). The converse is proved against that
weaker object, which is the conservative direction, but it is not the deployed eight-lane digest.
(c) §1's hypothesis is still refuted and §1
is still priced at zero — §2b does not rescue it, it replaces its role. (d) `GRAPH_SLOTS = 4` throughout;
§3's counts are instances, not a theorem over `n`. (e) Nothing here touches the deployed AIR, which
still absorbs the whole graph core every step.

⚑ WHAT THE BRIDGE NEEDED FROM THE TREE, AND FOUND: (i) the three absorb shapes distinguishable from the
limb list — the distinct `LEAF_TAG`/`PAIR_TAG`/`ROOT_TAG` heads give this; (ii) the leaf message to
carry its POSITION and the node message its CHILD ORDER — `leafInputs`/`nodeInputs` already do. NO
missing structural property: no per-position tag and no extra domain separation had to be added, which
matches §1's own finding that the obstruction was entirely the hash, never the layout.
# Dregg2.Crypto.HierarchicalGraphFrame — ⚑ THE FRAME CONVERSE of the hierarchical graph commitment.

`Crypto.HierarchicalGraphCommitment` builds the depth-two domain-separated tree over the four
deployed graph slots and proves, for every opening it defines, exactly ONE direction:

    (honest opening).check … = true      (`openLeaf_checks`, `openInterface_checks`,
                                          `openRedex2_checks`, `updateLeaf_checks`)

That is COMPLETENESS.  The theorem the hypergraph VM actually needs is the CONVERSE, and it is the
FRAME theorem:

    an ACCEPTED `AncestorUpdate` at index `u` forces the committed graph to change ONLY at `u`
    — and to change there EXACTLY to the authenticated slot.

Without it, `AncestorUpdate.check` is a check that authenticates one path and says nothing about the
other slots, so a step is only sound if the AIR re-hashes the WHOLE graph — which is exactly what
the deployed `privateGraphRewriteDescriptor` does (`GRAPH_SLOTS := 4`, a Θ(|G|) absorb every step,
112 of its 310 columns permutation staging).  The frame problem there is AVOIDED by smallness, not
solved.  This file proves the converse, at two resolutions, and states what it buys.

## §1 — the PURE STRUCTURAL core, and the named hypothesis it needs

`frame_of_absorbInjective`: if the deployed digest is injective on the three absorb SHAPES the tree
feeds it (`TreeAbsorbInjective`), then an accepted update at `u` gives

    g_before.slots u = update.before   ∧   g_after.slots = Function.update g_before.slots u update.after

— the full frame plus exactness, with NO hypothesis about the semantics and NO escape branch.

⚑ WHAT THE TREE NEEDS, PRECISELY, AND WHAT IT ALREADY HAS.  The converse needs a POSITIONAL binding:
a leaf digest must not be re-usable at another position, and a node digest must not be re-usable with
its children swapped.  The tree HAS both, and the proof shows where: the leaf absorb carries the slot
INDEX (`leafInputs index slot`, `leafInputs_injective` at a FIXED index), and the node absorb carries
its two children IN ORDER (`nodeInputs_injective` as a map out of `Digest8 × Digest8`).  Nothing else
is needed — in particular the peel never compares a LEAF absorb with a PAIR absorb or a PAIR with the
ROOT, so the `LEAF_TAG`/`PAIR_TAG`/`ROOT_TAG` domain separation is NOT what makes the frame work
(it is doing other work: keeping the memo/occurrence layers apart).  There is no missing structural
injectivity: the obstruction to the converse is ENTIRELY the hash, not the layout.

⚠ `TreeAbsorbInjective` is an ASSUMPTION, and at the deployed sponge it is FALSE — the node absorb is
17 limbs wide and the digest is 8 bounded lanes, so `not_treeAbsorbInjective_of_boundedLanes` REFUTES
it for every bounded-lane digest (no pigeonhole hand-waving: an infinite family of node absorbs into a
finite lane space).  So §1 is a statement about the LAYOUT, priced at zero, and it is NOT the deployed
statement.  It is also not vacuous: `exists_treeAbsorbInjective` exhibits a hash satisfying it.

## §2 — the DEPLOYED-RESOLUTION converse: a reduction on the SAME keyed-ROM floor

The exported frame converse is `frame_binds_rom`, in the shape `semanticRoot_binds_rom` already uses,
and for the reason its header records: the old `GraphRewriteHistory` / `HierarchicalGraphCommitment`
`_or_collision` disjunctions were DELETED because `∃ collision` is UNCONDITIONALLY TRUE at a
compressing root, so a `binds ∨ ∃ collision` theorem is satisfiable through the escape branch with the
binding never holding.  This file therefore ships NO such disjunction.  Instead:

  * `frameForgery` is a first-class `RomForgery hgcRomFamily`: the adversary outputs an index, a
    before/after slot, a PATH, and the two graph payloads its two roots commit to; it WINS iff both
    reconstructions check at the sampled role-keyed oracle AND the after-graph is NOT the before-graph
    with slot `u` replaced (the EXACTNESS break — strictly stronger than a frame violation, and
    `frame_violation_wins` proves a frame violation is one of these);
  * `frameExtractComp` is the extractor as an ORACLE PROGRAM: run the forger, then re-walk the path
    layer (8 queries) and both trees (12 queries), and `frameSelect` names the shallowest layer that
    equivocates — a `bindComp`, so the budget is ADDITIVE (`Q + 20`), never answer size;
  * `frame_binds_rom` closes from `romCarrier_binds` (hence `keyedRom_hard`, the birthday bound — a
    THEOREM).  NO floor hypothesis, NO escape branch.

The peel is: the ROOT absorb of the path differs from the before-graph's (a root-role equivocation),
or it agrees and the PAIR absorb differs (a pair-role equivocation through the shared root digest),
or both agree — in which case the path IS the before-graph's honest path, so the after-root commits to
`before-graph with slot u replaced` (`romRootFromPath_honest`), and disagreeing with the after-graph
payload is a root equivocation between two DISTINCT graphs, killed by the tree-walk of
`hgcSelect_wins` (the standalone form of `semanticRoot_binds_rom`'s own extractor argument).

⚑ THE MODELLING STEP IS INHERITED, NOT NEW: the sampled `H : Role × Msg → Fin (2 ^ l)` idealises the
fixed deployed eight-lane digest at an asymptotic width (`RomCarrierSites` header).  Nothing is
claimed about the fixed public hash.

## §2b — the ROM↔OBJECT BRIDGE: §2's price, landed on §1's objects

`romHash l H : Hash` answers a deployed limb list by dispatching on its absorbed tag onto the matching
role of `hgcRomFamily` and returning the oracle's `Fin (2 ^ l)` in lane 0.  It IS a `Hash`, so every
deployed definition applies to it unchanged, and the decoders round-trip the tree's own encodings.
Three bridges follow (`romHash_leafDigest` / `romHash_pairDigest` / `romHash_rootDigest`), then the
three the converse needs: `romHash_semanticRoot`, `romHash_pathFor`, `romHash_rootFromPath` (the last
for an ARBITRARY offered path — the forger's path is never assumed honest).

`frame_object_break_is_win` is the join, mirroring `hgcRom_graph_forgery_is_break`: an accepted
`AncestorUpdate` at the modelled hash whose authenticated before-slot is not the committed one, OR whose
after-graph is not the before-graph with that one slot replaced, IS a win of `frameForgery`.  Both
failure modes are covered by ONE game — a wrong before-slot is caught by re-presenting the before-graph
against itself, which is already an exactness break.  `objFrameGame` states the break entirely in
deployed objects (two `BoundedGraph`s and an `AncestorUpdate`), `objFrameToRom` extracts at ZERO extra
queries (pure post-processing), and `objFrame_binds_rom` closes on the same proved keyed-ROM floor.

## §3 — what the converse BUYS: Θ(|G|) absorbs → depth+1 absorbs, as a proposition

`update_rehashes_only_ancestor_path`: the root of the updated graph is the digest of the LAST of
`updateAbsorbs`, a THREE-block list determined by `(u, new slot, the two path digests)` alone;
`afterRoot_depends_only_on_path`: two graphs with the same path at `u` produce the same updated root,
so the update reads the rest of the graph NOT AT ALL.  Counted against the full recompute:
`(updateAbsorbs …).length = 3` with `2 ^ (3 - 1) = GRAPH_SLOTS` (depth + 1) versus
`(semanticRootAbsorbs …).length = 7 = 2 * GRAPH_SLOTS - 1`.  `single_slot_step_logarithmic_update`
puts the two together on a REAL rewrite step: a `BoundedOneStep` that touches only slot `u` is a
`RewriteStep` whose committed endpoints are joined by ONE accepted `AncestorUpdate` costing three
absorbs instead of seven.

⚠ HONEST SCOPE.  This is `GRAPH_SLOTS = 4`: `3 = log₂ 4 + 1` and `7 = 2·4 − 1` are INSTANCES of the
depth-vs-size counts, not a theorem over `n`.  The general Θ(log n) statement needs a depth-parametric
tree, which this prototype does not have — that generalisation, and the two-slot (redex-2) composition
where the two updates share a pair node, are named residuals, not claims.  Nothing here touches the
deployed AIR: `privateGraphRewriteDescriptor` still absorbs the whole graph core, so the frame converse
is the PREREQUISITE for shrinking it, not a measurement of a shrunken circuit.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`, no `decide`-discharged Props.
-/
import Dregg2.Crypto.HierarchicalGraphCommitment
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.HierarchicalGraphFrame

open Dregg2.Crypto.PrivateGraphRewrite
open Dregg2.Crypto.GraphRewrite
open Dregg2.Crypto.HierarchicalGraphCommitment

set_option autoImplicit false

/-! ## §0 — four-way case analysis on `Fin 4`, without `decide`. -/

/-- The four deployed slot indices, enumerated. -/
theorem fin4_cases (u : Fin 4) : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by
  have hlt : u.val < 4 := u.isLt
  have h : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using h))))

/-! ## §1 — the PURE STRUCTURAL frame converse.

The hypothesis is about the three absorb SHAPES only, and it is stated per FIXED index / per FIXED
tag: that is exactly the positional binding the tree's own encodings provide. -/

/-- **THE LAYOUT HYPOTHESIS THE FRAME CONVERSE NEEDS.** The digest is injective on the leaf absorbs
at a fixed slot index, and on the node absorbs at a fixed tag (jointly in both children).

⚠ This is an ASSUMPTION about the deployed digest, and `not_treeAbsorbInjective_of_boundedLanes`
proves it FALSE for every bounded-lane digest — the deployed statement is §2's reduction.  What it
isolates is the LAYOUT's contribution: given absorb injectivity, the tree frames with no further
structure (no per-position domain separation is missing). -/
structure TreeAbsorbInjective (H : Hash) : Prop where
  /-- A leaf digest at a FIXED index determines its slot (`leafInputs` carries the index). -/
  leaf : ∀ (i : Fin 4) (s t : HostEdgeSlot), leafDigest H i s = leafDigest H i t → s = t
  /-- A node digest at a FIXED tag determines BOTH children, IN ORDER. -/
  node : ∀ (tag : Int) (x y x' y' : Digest8),
    nodeDigest H tag x y = nodeDigest H tag x' y' → x = x' ∧ y = y'

/-- **THE PATH PEEL.** A reconstruction that hits the committed root forces the authenticated leaf to
be the graph's own slot at `u` AND the offered path to be the graph's own path at `u`.  This is the
whole structural content of the converse: two peels (root absorb, then the pair absorb), where the
child ORDER pins which side of the pair `u` sits on and the leaf INDEX pins which leaf it is. -/
theorem path_peel {H : Hash} (hinj : TreeAbsorbInjective H) (u : Fin 4) (s : HostEdgeSlot)
    (p : Path4) (g : BoundedGraph)
    (h : rootFromPath H u (leafDigest H u s) p = semanticRoot H g) :
    s = g.slots u ∧ p = pathFor H g u := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · have h' : nodeDigest H ROOT_TAG
        (nodeDigest H PAIR_TAG (leafDigest H 0 s) p.siblingLeaf) p.siblingPair
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hnode, hpair⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG (leafDigest H 0 s) p.siblingLeaf
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)) := hnode
    obtain ⟨hleaf, hsib⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 0 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 1 (g.slots 1), rightPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 1 (g.slots 1), rightPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG
        (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 1 s)) p.siblingPair
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hnode, hpair⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 1 s)
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)) := hnode
    obtain ⟨hsib, hleaf⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 1 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 0 (g.slots 0), rightPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 0 (g.slots 0), rightPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG p.siblingPair
        (nodeDigest H PAIR_TAG (leafDigest H 2 s) p.siblingLeaf)
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hpair, hnode⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG (leafDigest H 2 s) p.siblingLeaf
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)) := hnode
    obtain ⟨hleaf, hsib⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 2 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 3 (g.slots 3), leftPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 3 (g.slots 3), leftPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG p.siblingPair
        (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 3 s))
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hpair, hnode⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 3 s)
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)) := hnode
    obtain ⟨hsib, hleaf⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 3 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 2 (g.slots 2), leftPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 2 (g.slots 2), leftPair H g⟩ := by rw [hsib, hpair]

/-- **OFF-INDEX AGREEMENT.** Two graphs whose paths at `u` coincide agree at every OTHER slot: the
sibling leaf pins the co-leaf of `u`'s pair, and the sibling pair digest pins the other two leaves. -/
theorem slots_agree_off_index {H : Hash} (hinj : TreeAbsorbInjective H) (u : Fin 4)
    (g₁ g₂ : BoundedGraph) (hpp : pathFor H g₁ u = pathFor H g₂ u) :
    ∀ i, i ≠ u → g₁.slots i = g₂.slots i := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · have hsl : leafDigest H 1 (g₁.slots 1) = leafDigest H 1 (g₂.slots 1) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 2 (g₁.slots 2)) (leafDigest H 3 (g₁.slots 3))
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g₂.slots 2)) (leafDigest H 3 (g₂.slots 3)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h2, h3⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · exact hinj.leaf 1 _ _ hsl
    · exact hinj.leaf 2 _ _ h2
    · exact hinj.leaf 3 _ _ h3
  · have hsl : leafDigest H 0 (g₁.slots 0) = leafDigest H 0 (g₂.slots 0) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 2 (g₁.slots 2)) (leafDigest H 3 (g₁.slots 3))
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g₂.slots 2)) (leafDigest H 3 (g₂.slots 3)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h2, h3⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ hsl
    · exact absurd rfl hi
    · exact hinj.leaf 2 _ _ h2
    · exact hinj.leaf 3 _ _ h3
  · have hsl : leafDigest H 3 (g₁.slots 3) = leafDigest H 3 (g₂.slots 3) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 0 (g₁.slots 0)) (leafDigest H 1 (g₁.slots 1))
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g₂.slots 0)) (leafDigest H 1 (g₂.slots 1)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h0, h1⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ h0
    · exact hinj.leaf 1 _ _ h1
    · exact absurd rfl hi
    · exact hinj.leaf 3 _ _ hsl
  · have hsl : leafDigest H 2 (g₁.slots 2) = leafDigest H 2 (g₂.slots 2) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 0 (g₁.slots 0)) (leafDigest H 1 (g₁.slots 1))
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g₂.slots 0)) (leafDigest H 1 (g₂.slots 1)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h0, h1⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ h0
    · exact hinj.leaf 1 _ _ h1
    · exact hinj.leaf 2 _ _ hsl
    · exact absurd rfl hi

/-- **⚑⚑ THE FRAME CONVERSE, PURE CORE.** An ACCEPTED `AncestorUpdate` at index `u` between two
committed graphs forces the before-graph's slot at `u` to be the authenticated `before`, and the
after-graph to be the before-graph with slot `u` replaced by the authenticated `after` — hence
unchanged at every other slot.  The converse of `updateLeaf_checks`, at zero price under the LAYOUT
hypothesis. -/
theorem frame_of_absorbInjective {H : Hash} (hinj : TreeAbsorbInjective H)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcheck : upd.check H (semanticRoot H g₁) (semanticRoot H g₂) = true) :
    g₁.slots upd.index = upd.before ∧
      g₂.slots = Function.update g₁.slots upd.index upd.after := by
  rw [AncestorUpdate.check, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨_, _⟩, hb⟩, ha⟩ := hcheck
  have h1 : rootFromPath H upd.index (leafDigest H upd.index upd.before) upd.path
      = semanticRoot H g₁ := digestFields_injective (of_decide_eq_true hb)
  have h2 : rootFromPath H upd.index (leafDigest H upd.index upd.after) upd.path
      = semanticRoot H g₂ := digestFields_injective (of_decide_eq_true ha)
  obtain ⟨hs1, hp1⟩ := path_peel hinj upd.index upd.before upd.path g₁ h1
  obtain ⟨hs2, hp2⟩ := path_peel hinj upd.index upd.after upd.path g₂ h2
  have hoff := slots_agree_off_index hinj upd.index g₁ g₂ (hp1.symm.trans hp2)
  refine ⟨hs1.symm, ?_⟩
  funext i
  by_cases hi : i = upd.index
  · subst hi
    simpa using hs2.symm
  · simpa [Function.update, hi] using (hoff i hi).symm

/-- **THE FRAME CONVERSE AT GRAPH GRANULARITY.** Packaged as the very `replaceSlot` the completeness
direction uses: the accepted update's after-graph IS `replaceSlot` of the before-graph.  (`hcanonical`
is derivable from the check's own `canonicalSlotB update.after` tooth; it is an argument only so the
`replaceSlot` term in the statement stays readable.) -/
theorem afterGraph_eq_replaceSlot {H : Hash} (hinj : TreeAbsorbInjective H)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcanonical : upd.after.canonicalPadding)
    (hcheck : upd.check H (semanticRoot H g₁) (semanticRoot H g₂) = true) :
    g₂ = replaceSlot g₁ upd.index upd.after hcanonical := by
  obtain ⟨_, hslots⟩ := frame_of_absorbInjective hinj g₁ g₂ upd hcheck
  cases g₁ with
  | mk s₁ c₁ =>
    cases g₂ with
    | mk s₂ c₂ =>
      simp only at hslots
      subst hslots
      rfl

/-! ### §1 teeth — the layout hypothesis is INHABITED, and FALSE at the deployed digest. -/

/-- A lossless reference digest: absorb the limb list into ONE unbounded lane.  Only a witness that
`TreeAbsorbInjective` is satisfiable — it is not a hash. -/
def injHash (xs : List Int) : List Int := [((Encodable.encode xs : ℕ) : Int)]

theorem injHash_digest8_injective : Function.Injective (digest8 injHash) := by
  intro a b h
  have h0 : digest8 injHash a 0 = digest8 injHash b 0 := congrFun h 0
  have h1 : ((Encodable.encode a : ℕ) : Int) = ((Encodable.encode b : ℕ) : Int) := h0
  exact Encodable.encode_injective (by exact_mod_cast h1)

/-- Absorb injectivity follows from injectivity of the digest, through the tree's OWN encoding
injectivities (`leafInputs_injective` at a fixed index, `nodeInputs_injective` at a fixed tag). -/
theorem treeAbsorbInjective_of_digest8_injective {H : Hash}
    (h : Function.Injective (digest8 H)) : TreeAbsorbInjective H where
  leaf := fun i s t hst => leafInputs_injective i (h hst)
  node := fun tag x y x' y' hxy => by
    have h2 : (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) (x, y)
        = (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) (x', y') := h hxy
    have h3 : ((x, y) : Digest8 × Digest8) = (x', y') := nodeInputs_injective tag h2
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-- **(TOOTH — §1 is not vacuous.)** Some digest satisfies the layout hypothesis. -/
theorem exists_treeAbsorbInjective : ∃ H : Hash, TreeAbsorbInjective H :=
  ⟨injHash, treeAbsorbInjective_of_digest8_injective injHash_digest8_injective⟩

/-- **(TOOTH — §1's hypothesis is FALSE at the deployed digest, so §1 is NOT the deployed claim.)**
Every digest whose lanes are nonnegative and bounded fails absorb injectivity: the node absorbs
`nodeInputs ROOT_TAG (const n) (const n)` form an INFINITE family, the lane space is FINITE, so two
distinct node absorbs collide and `node` is refuted.  No pigeonhole hand-wave — the counting is
`Finite.exists_ne_map_eq_of_infinite`. -/
theorem not_treeAbsorbInjective_of_boundedLanes (H : Hash) (B : ℕ)
    (hlo : ∀ (xs : List Int) (i : Fin 8), 0 ≤ digest8 H xs i)
    (hhi : ∀ (xs : List Int) (i : Fin 8), digest8 H xs i < (B : Int)) :
    ¬ TreeAbsorbInjective H := by
  intro hinj
  have hB : 0 < B := by
    have h0 := hlo [] 0
    have h1 := hhi [] 0
    omega
  let const : ℕ → Digest8 := fun n => fun _ => (n : Int)
  let φ : ℕ → (Fin 8 → Fin B) := fun n i =>
    ⟨(nodeDigest H ROOT_TAG (const n) (const n) i).toNat, by
      have h1 : nodeDigest H ROOT_TAG (const n) (const n) i < (B : Int) :=
        hhi (nodeInputs ROOT_TAG (const n) (const n)) i
      omega⟩
  obtain ⟨n, m, hnm, hφ⟩ := Finite.exists_ne_map_eq_of_infinite φ
  have hdig : nodeDigest H ROOT_TAG (const n) (const n)
      = nodeDigest H ROOT_TAG (const m) (const m) := by
    funext i
    have hi : ((nodeDigest H ROOT_TAG (const n) (const n) i).toNat : ℕ)
        = ((nodeDigest H ROOT_TAG (const m) (const m) i).toNat : ℕ) :=
      congrArg Fin.val (congrFun hφ i)
    have hn : 0 ≤ nodeDigest H ROOT_TAG (const n) (const n) i :=
      hlo (nodeInputs ROOT_TAG (const n) (const n)) i
    have hm : 0 ≤ nodeDigest H ROOT_TAG (const m) (const m) i :=
      hlo (nodeInputs ROOT_TAG (const m) (const m)) i
    omega
  obtain ⟨hx, _⟩ := hinj.node _ _ _ _ _ hdig
  have : (n : Int) = (m : Int) := congrFun hx 0
  exact hnm (by exact_mod_cast this)

/-! ## §2 — the frame converse at the SAMPLED role-keyed oracle: a REDUCTION on the PROVED floor.

Same family, same carrier, same floor as `semanticRoot_binds_rom`.  Nothing new is assumed; the only
new content is the peel and the extractor. -/

section RomFrame

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

/-- The ideal digest space. -/
abbrev RomDig (l : ℕ) : Type := Fin (2 ^ l)

/-- One leaf absorb at the sampled oracle — the index is IN the message (positional binding). -/
def romLeaf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (i : Fin 4) (s : SlotEnc) : RomDig l :=
  H (hgcLeafRole, Sum.inl (i, s))

/-- One pair-node absorb at the sampled oracle, children IN ORDER. -/
def romPairOf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (q : RomDig l × RomDig l) : RomDig l :=
  H (hgcPairRole, Sum.inr q)

/-- The root absorb at the sampled oracle. -/
def romRootOf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (q : RomDig l × RomDig l) : RomDig l :=
  H (hgcRootRole, Sum.inr q)

/-- The left pair digest of a payload. -/
def romLeftPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) : RomDig l :=
  romPairOf l H (romLeaf l H 0 (g 0), romLeaf l H 1 (g 1))

/-- The right pair digest of a payload. -/
def romRightPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) : RomDig l :=
  romPairOf l H (romLeaf l H 2 (g 2), romLeaf l H 3 (g 3))

/-- `hgcRomRoot` in the vocabulary of this section — the same absorb schedule, unchanged. -/
theorem hgcRomRoot_eq (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) :
    hgcRomRoot l H g = romRootOf l H (romLeftPair l H g, romRightPair l H g) := rfl

/-- The ROM face of `Path4`: the sibling leaf digest and the sibling pair digest. -/
abbrev RomPath (l : ℕ) : Type := RomDig l × RomDig l

/-- The ROM face of `pathFor`. -/
def romPathFor (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) (u : Fin 4) :
    RomPath l :=
  match u.val with
  | 0 => (romLeaf l H 1 (g 1), romRightPair l H g)
  | 1 => (romLeaf l H 0 (g 0), romRightPair l H g)
  | 2 => (romLeaf l H 3 (g 3), romLeftPair l H g)
  | _ => (romLeaf l H 2 (g 2), romLeftPair l H g)

/-- **THE PAIR ABSORB OF A PATH RECONSTRUCTION** — the authenticated leaf and the sibling leaf, in
the order `u`'s parity dictates. -/
def framePairBlock (l : ℕ) (u : Fin 4) (leaf : RomDig l) (p : RomPath l) : RomDig l × RomDig l :=
  if u.val % 2 = 0 then (leaf, p.1) else (p.1, leaf)

/-- **THE ROOT ABSORB OF A PATH RECONSTRUCTION** — the reconstructed pair digest and the sibling pair
digest, in the order `u`'s half dictates. -/
def frameRootBlock (l : ℕ) (u : Fin 4) (pathPair : RomDig l) (p : RomPath l) :
    RomDig l × RomDig l :=
  if u.val < 2 then (pathPair, p.2) else (p.2, pathPair)

/-- **THE COMMITTED PAIR ABSORB `u` SITS UNDER** — the two leaf digests of `u`'s own pair. -/
def frameGraphPairBlock (l : ℕ) (u : Fin 4) (b0 b1 b2 b3 : RomDig l) : RomDig l × RomDig l :=
  if u.val < 2 then (b0, b1) else (b2, b3)

/-- The ROM face of `rootFromPath`: three absorbs — the leaf, `u`'s pair, the root. -/
def romRootFromPath (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (u : Fin 4) (leaf : RomDig l)
    (p : RomPath l) : RomDig l :=
  romRootOf l H (frameRootBlock l u (romPairOf l H (framePairBlock l u leaf p)) p)

/-- The ROM face of `replaceSlot`. -/
def romReplace (g : GraphSlots) (u : Fin 4) (s : SlotEnc) : GraphSlots :=
  Function.update g u s

/-- **THE HONEST PATH RECONSTRUCTS THE UPDATED ROOT** — the ROM face of
`pathFor_replaceSlot ∘ pathFor_reconstructs`: reconstructing along the OLD path with a NEW leaf is
exactly the root of the graph with that ONE slot replaced. -/
theorem romRootFromPath_honest (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots)
    (u : Fin 4) (s : SlotEnc) :
    romRootFromPath l H u (romLeaf l H u s) (romPathFor l H g u)
      = hgcRomRoot l H (romReplace g u s) := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    simp [romRootFromPath, romPathFor, romReplace, hgcRomRoot, romRootOf, romPairOf, romLeaf,
      romLeftPair, romRightPair, framePairBlock, frameRootBlock]

/-! ### The forgery, the extractor, and the binding. -/

/-- **WHAT A FRAME FORGER OUTPUTS** — an index, the authenticated before/after slots, a PATH of its
own choosing, and the two graph payloads its before/after roots commit to. -/
structure FrameAns (l : ℕ) where
  /-- The authenticated slot index. -/
  index : Fin 4
  /-- The authenticated old slot. -/
  before : SlotEnc
  /-- The authenticated new slot. -/
  after : SlotEnc
  /-- The offered path — adversarial, NOT assumed honest. -/
  path : RomPath l
  /-- The payload the before-root commits to. -/
  beforeGraph : GraphSlots
  /-- The payload the after-root commits to. -/
  afterGraph : GraphSlots

/-- **THE FRAME FORGERY** — the adversary wins iff BOTH reconstructions check at the sampled oracle
and the after-graph is NOT the before-graph with slot `index` replaced by `after`.  The break is IN
the win relation: it is exactly "an accepted ancestor update that did something else". -/
def frameForgery : RomForgery hgcRomFamily where
  Ans := FrameAns
  wins := fun l H a =>
    romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path = hgcRomRoot l H a.beforeGraph
      ∧ romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
          = hgcRomRoot l H a.afterGraph
      ∧ a.afterGraph ≠ romReplace a.beforeGraph a.index a.after
  winsDec := fun _ _ _ => by infer_instance

/-- The frame break game. -/
abbrev frameBreakGame : Game := frameForgery.game

/-- **A FRAME VIOLATION IS A WIN** — the weaker break (some slot OFF the authenticated index moved)
is dominated by the exactness break the game states, so the binding covers it. -/
theorem frame_violation_wins (l : ℕ) (H : frameBreakGame.Inst l) (a : FrameAns l)
    (hb : romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path
      = hgcRomRoot l H a.beforeGraph)
    (haf : romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
      = hgcRomRoot l H a.afterGraph)
    (i : Fin 4) (hi : i ≠ a.index) (hne : a.beforeGraph i ≠ a.afterGraph i) :
    frameBreakGame.wins l H a := by
  refine ⟨hb, haf, fun hEq => hne ?_⟩
  have := congrFun hEq i
  simpa [romReplace, Function.update, hi] using this.symm

/-- **THE ROOT-EQUIVOCATION TOOTH, STANDALONE** — the tree walk of `semanticRoot_binds_rom`, stated
as a lemma about `hgcSelect`: two DISTINCT payloads with EQUAL tree roots make the re-walked
selection a win of the tree's single carrier.  (Same argument as
`HierarchicalGraphCommitment.semanticRoot_binds_rom`'s final peel; factored out here because the frame
reduction consumes it at an interior branch.) -/
theorem hgcSelect_wins (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (a : GraphSlots × GraphSlots)
    (hne : a.1 ≠ a.2) (heq : hgcRomRoot l H a.1 = hgcRomRoot l H a.2) :
    (romCarrierGame hgcRomFamily hgcRomCarrier).wins l H
      (hgcSelect l a
        (romLeaf l H 0 (a.1 0)) (romLeaf l H 1 (a.1 1))
        (romLeaf l H 2 (a.1 2)) (romLeaf l H 3 (a.1 3))
        (romLeaf l H 0 (a.2 0)) (romLeaf l H 1 (a.2 1))
        (romLeaf l H 2 (a.2 2)) (romLeaf l H 3 (a.2 3))
        (romLeftPair l H a.1) (romRightPair l H a.1)
        (romLeftPair l H a.2) (romRightPair l H a.2)) := by
  unfold hgcSelect
  split_ifs with hRoot hL hR h0 h1 h2
  · exact ⟨fun hc => hRoot (Sum.inr_injective hc), heq⟩
  · exact ⟨fun hc => hL (Sum.inr_injective hc), congrArg Prod.fst (not_not.mp hRoot)⟩
  · exact ⟨fun hc => hR (Sum.inr_injective hc), congrArg Prod.snd (not_not.mp hRoot)⟩
  · exact ⟨fun hc => h0 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hL)⟩
  · exact ⟨fun hc => h1 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.snd (not_not.mp hL)⟩
  · exact ⟨fun hc => h2 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hR)⟩
  · have h3 : a.1 3 ≠ a.2 3 := by
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

/-- **THE FRAME SELECTION** — from the forger's answer and the re-walked digests, name the shallowest
layer that equivocates: the ROOT absorb of the offered path against the committed one, then `u`'s PAIR
absorb, and otherwise (the path IS honest) the root equivocation between the correctly-updated payload
and the offered after-payload.  Pure: every query was already paid by `frameExtractComp`. -/
def frameSelect (l : ℕ) (a : FrameAns l)
    (b0 b1 b2 b3 bL bR Lb pathPair : RomDig l)
    (d0 d1 d2 d3 rL rR c0 c1 c2 c3 cL cR : RomDig l) :
    hgcRomCarrier.Ctx l × hgcRomCarrier.Val l × hgcRomCarrier.Val l :=
  if frameRootBlock l a.index pathPair a.path ≠ (bL, bR) then
    ((hgcRootRole, ()), Sum.inr (frameRootBlock l a.index pathPair a.path), Sum.inr (bL, bR))
  else if framePairBlock l a.index Lb a.path ≠ frameGraphPairBlock l a.index b0 b1 b2 b3 then
    ((hgcPairRole, ()), Sum.inr (framePairBlock l a.index Lb a.path),
      Sum.inr (frameGraphPairBlock l a.index b0 b1 b2 b3))
  else
    hgcSelect l (romReplace a.beforeGraph a.index a.after, a.afterGraph)
      d0 d1 d2 d3 c0 c1 c2 c3 rL rR cL cR

/-- **⚑ WIN-PRESERVATION — the whole mathematical content of the frame converse.** A frame forgery at
the sampled oracle makes the selected triple a genuine equivocation of the tree's carrier. -/
theorem frameSelect_wins (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (a : FrameAns l)
    (hb : romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path
      = hgcRomRoot l H a.beforeGraph)
    (haf : romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
      = hgcRomRoot l H a.afterGraph)
    (hbreak : a.afterGraph ≠ romReplace a.beforeGraph a.index a.after) :
    (romCarrierGame hgcRomFamily hgcRomCarrier).wins l H
      (frameSelect l a
        (romLeaf l H 0 (a.beforeGraph 0)) (romLeaf l H 1 (a.beforeGraph 1))
        (romLeaf l H 2 (a.beforeGraph 2)) (romLeaf l H 3 (a.beforeGraph 3))
        (romLeftPair l H a.beforeGraph) (romRightPair l H a.beforeGraph)
        (romLeaf l H a.index a.before)
        (romPairOf l H (framePairBlock l a.index (romLeaf l H a.index a.before) a.path))
        (romLeaf l H 0 (romReplace a.beforeGraph a.index a.after 0))
        (romLeaf l H 1 (romReplace a.beforeGraph a.index a.after 1))
        (romLeaf l H 2 (romReplace a.beforeGraph a.index a.after 2))
        (romLeaf l H 3 (romReplace a.beforeGraph a.index a.after 3))
        (romLeftPair l H (romReplace a.beforeGraph a.index a.after))
        (romRightPair l H (romReplace a.beforeGraph a.index a.after))
        (romLeaf l H 0 (a.afterGraph 0)) (romLeaf l H 1 (a.afterGraph 1))
        (romLeaf l H 2 (a.afterGraph 2)) (romLeaf l H 3 (a.afterGraph 3))
        (romLeftPair l H a.afterGraph) (romRightPair l H a.afterGraph)) := by
  obtain ⟨u, before, after, path, bg, ag⟩ := a
  simp only [frameSelect]
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((romPairOf l H (framePairBlock l 0 (romLeaf l H 0 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.fst hr⟩
    · have hr : ((romPairOf l H (framePairBlock l 0 (romLeaf l H 0 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((romLeaf l H 0 before, path.1) : RomDig l × RomDig l)
          = (romLeaf l H 0 (bg 0), romLeaf l H 1 (bg 1)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 0 := by
        have e1 : path.1 = romLeaf l H 1 (bg 1) := congrArg Prod.snd hp
        have e2 : path.2 = romRightPair l H bg := congrArg Prod.snd hr
        show path = (romLeaf l H 1 (bg 1), romRightPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 0 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 0 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 0 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((romPairOf l H (framePairBlock l 1 (romLeaf l H 1 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.fst hr⟩
    · have hr : ((romPairOf l H (framePairBlock l 1 (romLeaf l H 1 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((path.1, romLeaf l H 1 before) : RomDig l × RomDig l)
          = (romLeaf l H 0 (bg 0), romLeaf l H 1 (bg 1)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 1 := by
        have e1 : path.1 = romLeaf l H 0 (bg 0) := congrArg Prod.fst hp
        have e2 : path.2 = romRightPair l H bg := congrArg Prod.snd hr
        show path = (romLeaf l H 0 (bg 0), romRightPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 1 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 1 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 1 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 2 (romLeaf l H 2 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.snd hr⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 2 (romLeaf l H 2 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((romLeaf l H 2 before, path.1) : RomDig l × RomDig l)
          = (romLeaf l H 2 (bg 2), romLeaf l H 3 (bg 3)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 2 := by
        have e1 : path.1 = romLeaf l H 3 (bg 3) := congrArg Prod.snd hp
        have e2 : path.2 = romLeftPair l H bg := congrArg Prod.fst hr
        show path = (romLeaf l H 3 (bg 3), romLeftPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 2 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 2 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 2 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 3 (romLeaf l H 3 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.snd hr⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 3 (romLeaf l H 3 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((path.1, romLeaf l H 3 before) : RomDig l × RomDig l)
          = (romLeaf l H 2 (bg 2), romLeaf l H 3 (bg 3)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 3 := by
        have e1 : path.1 = romLeaf l H 2 (bg 2) := congrArg Prod.fst hp
        have e2 : path.2 = romLeftPair l H bg := congrArg Prod.fst hr
        show path = (romLeaf l H 2 (bg 2), romLeftPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 3 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 3 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 3 after, ag) (Ne.symm hbreak) heq

/-- **THE EXTRACTOR, AS AN ORACLE PROGRAM** — run the forger, re-walk the path layer (four committed
leaves, two committed pairs, the authenticated leaf, the path's pair absorb) and both trees (eight
leaves, four pairs), then select the equivocating layer.  `bindComp` keeps the accounting additive: a
`Q`-query forger yields a `Q + 20`-query carrier equivocator. -/
def frameExtractComp
    (M : ∀ l, OracleComp (hgcRomFamily.toRomFamily.D l) (hgcRomFamily.toRomFamily.R l)
      (frameForgery.Ans l)) :
    RomCarrierComp hgcRomFamily hgcRomCarrier :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.beforeGraph 0)) (fun b0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.beforeGraph 1)) (fun b1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.beforeGraph 2)) (fun b2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.beforeGraph 3)) (fun b3 =>
    OracleComp.query (hgcPairRole, Sum.inr (b0, b1)) (fun bL =>
    OracleComp.query (hgcPairRole, Sum.inr (b2, b3)) (fun bR =>
    OracleComp.query (hgcLeafRole, Sum.inl (a.index, a.before)) (fun Lb =>
    OracleComp.query (hgcPairRole, Sum.inr (framePairBlock l a.index Lb a.path)) (fun pathPair =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, romReplace a.beforeGraph a.index a.after 0))
      (fun d0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, romReplace a.beforeGraph a.index a.after 1))
      (fun d1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, romReplace a.beforeGraph a.index a.after 2))
      (fun d2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, romReplace a.beforeGraph a.index a.after 3))
      (fun d3 =>
    OracleComp.query (hgcPairRole, Sum.inr (d0, d1)) (fun rL =>
    OracleComp.query (hgcPairRole, Sum.inr (d2, d3)) (fun rR =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.afterGraph 0)) (fun c0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.afterGraph 1)) (fun c1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.afterGraph 2)) (fun c2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.afterGraph 3)) (fun c3 =>
    OracleComp.query (hgcPairRole, Sum.inr (c0, c1)) (fun cL =>
    OracleComp.query (hgcPairRole, Sum.inr (c2, c3)) (fun cR =>
    OracleComp.pure (frameSelect l a b0 b1 b2 b3 bL bR Lb pathPair
      d0 d1 d2 d3 rL rR c0 c1 c2 c3 cL cR))))))))))))))))))))))

/-- **⚑⚑ THE FRAME CONVERSE, DISCHARGED ON THE PROVED KEYED-ROM FLOOR.**

Every query-bounded forger that produces an ACCEPTED ancestor update whose after-graph is NOT the
before-graph with the authenticated slot replaced has NEGLIGIBLE advantage.  Equivalently: except with
negligible probability, an accepted `AncestorUpdate` at index `u` changes the committed graph ONLY at
`u`, and there exactly to the authenticated slot.  This is the theorem `updateLeaf_checks` was missing,
and it is what lets a step re-hash the ancestor path instead of the whole graph.

NO floor hypothesis, NO escape branch: the peel produces a CONCRETE equivocation of the tree's single
carrier at a NAMED role, and `romCarrier_binds` (hence `keyedRom_hard`, the birthday bound) kills it. -/
theorem frame_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary frameBreakGame)
    (hA : RomForgeryEff hgcRomFamily frameForgery Q A) :
    Negl (gameAdv frameBreakGame A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le (fun l => (gameAdv_mem_unit frameBreakGame A l).1)
    (fun l => ?_)
    (romCarrier_binds hgcRomFamily hgcRomCarrier
      (fun l => Q l + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2)
      (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
        (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
          (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
            (polyBounded_sq_add_two _ hQ))))))))))
      hgcRomFamily_card_R
      (romCarrierAdv _ _ (frameExtractComp M))
      ⟨frameExtractComp M,
        fun l => (OracleComp.bindComp_queryBounded (hM l)
          (fun a => QueryBounded.query 19 _ _ (fun _ => QueryBounded.query 18 _ _
            (fun _ => QueryBounded.query 17 _ _ (fun _ => QueryBounded.query 16 _ _
            (fun _ => QueryBounded.query 15 _ _ (fun _ => QueryBounded.query 14 _ _
            (fun _ => QueryBounded.query 13 _ _ (fun _ => QueryBounded.query 12 _ _
            (fun _ => QueryBounded.query 11 _ _ (fun _ => QueryBounded.query 10 _ _
            (fun _ => QueryBounded.query 9 _ _ (fun _ => QueryBounded.query 8 _ _
            (fun _ => QueryBounded.query 7 _ _ (fun _ => QueryBounded.query 6 _ _
            (fun _ => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
            (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
            (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
            (fun _ => QueryBounded.pure 0 _)))))))))))))))))))))).mono
          (by show Q l + 20 ≤ Q l + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2; omega),
        fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ (frameBreakGame.instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hb, haf, hbreak⟩ := hH
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  have hBrun : (romCarrierAdv _ _ (frameExtractComp M)).run l H
      = frameSelect l a
        (romLeaf l H 0 (a.beforeGraph 0)) (romLeaf l H 1 (a.beforeGraph 1))
        (romLeaf l H 2 (a.beforeGraph 2)) (romLeaf l H 3 (a.beforeGraph 3))
        (romLeftPair l H a.beforeGraph) (romRightPair l H a.beforeGraph)
        (romLeaf l H a.index a.before)
        (romPairOf l H (framePairBlock l a.index (romLeaf l H a.index a.before) a.path))
        (romLeaf l H 0 (romReplace a.beforeGraph a.index a.after 0))
        (romLeaf l H 1 (romReplace a.beforeGraph a.index a.after 1))
        (romLeaf l H 2 (romReplace a.beforeGraph a.index a.after 2))
        (romLeaf l H 3 (romReplace a.beforeGraph a.index a.after 3))
        (romLeftPair l H (romReplace a.beforeGraph a.index a.after))
        (romRightPair l H (romReplace a.beforeGraph a.index a.after))
        (romLeaf l H 0 (a.afterGraph 0)) (romLeaf l H 1 (a.afterGraph 1))
        (romLeaf l H 2 (a.afterGraph 2)) (romLeaf l H 3 (a.afterGraph 3))
        (romLeftPair l H a.afterGraph) (romRightPair l H a.afterGraph) := by
    show (frameExtractComp M l).eval H = _
    unfold frameExtractComp
    erw [OracleComp.bindComp_eval, ← hArun]
    rfl
  rw [hBrun]
  exact frameSelect_wins l H a hb haf hbreak

/-! ### §2 teeth — the game is WINNABLE, the admitted refuter-shape is DEFANGED, and a non-negligible
frame forger is OUTSIDE the class. -/

/-- A padding slot. -/
def slotPad : SlotEnc := (false, 0, 0, 0)

/-- An ACTIVE slot, distinct from the padding slot. -/
def slotLive : SlotEnc := (true, 0, 0, 0)

theorem slotPad_ne_slotLive : slotPad ≠ slotLive := by
  intro h
  exact absurd (congrArg Prod.fst h) (by simp [slotPad, slotLive])

/-- The `0`-query constant frame answer: it re-authenticates the padding slot at index `0` while
claiming an after-graph of live slots — an EXACTNESS break at every oracle that maps everything to one
digest. -/
def constFrameAns (l : ℕ) : FrameAns l where
  index := 0
  before := slotPad
  after := slotPad
  path := (⟨0, by positivity⟩, ⟨0, by positivity⟩)
  beforeGraph := fun _ => slotPad
  afterGraph := fun _ => slotLive

/-- **(TOOTH — the frame game is WINNABLE and the admitted refuter-shape is DEFANGED.)** The `0`-query
constant answerer is IN the class, WINS at the constant oracle (every absorb collapses to one digest,
so both reconstructions "check" while the after-graph is wrong), and its advantage is NEGLIGIBLE by
`frame_binds_rom` — the frame converse prices something genuinely nonzero, and the pigeonhole strategy
that made a `∨ ∃ collision` disjunction a free pass dies at the sampled oracle. -/
theorem frame_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    (RomForgeryEff hgcRomFamily frameForgery Q ⟨fun l _ => constFrameAns l⟩)
      ∧ (∀ l, 0 < gameAdv frameBreakGame ⟨fun l _ => constFrameAns l⟩ l)
      ∧ Negl (gameAdv frameBreakGame ⟨fun l _ => constFrameAns l⟩) := by
  have hmem : RomForgeryEff hgcRomFamily frameForgery Q ⟨fun l _ => constFrameAns l⟩ :=
    ⟨fun l => OracleComp.pure (constFrameAns l), fun l => QueryBounded.pure (Q l) _,
      fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, frame_binds_rom Q hQ _ hmem⟩
  obtain ⟨r₀⟩ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, by positivity⟩⟩
  refine @winProb_pos_of_witness _ (frameBreakGame.instFin l) _ (fun _ => r₀) ?_
  refine (Adversary.hit_eq_true _ l _).mpr ⟨rfl, rfl, ?_⟩
  intro hEq
  have h1 := congrFun hEq 1
  simp only [constFrameAns, romReplace] at h1
  rw [Function.update_apply] at h1
  simp only [if_neg (show (1 : Fin 4) ≠ 0 from Fin.ne_of_val_ne (by omega))] at h1
  exact slotPad_ne_slotLive h1.symm

/-- **(TOOTH — a non-negligible frame forger is OUTSIDE the class.)** -/
theorem frame_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary frameBreakGame) (hnn : ¬ Negl (gameAdv frameBreakGame A)) :
    ¬ RomForgeryEff hgcRomFamily frameForgery Q A :=
  fun hA => hnn (frame_binds_rom Q hQ A hA)

/-! ### §2b — ⚑⚑ THE ROM↔OBJECT BRIDGE: §2's price lands on §1's DEPLOYED objects.

Everything above §2b has the defect the header records: §1 is over the real `AncestorUpdate.check` but
under a hypothesis this file itself refutes, and §2 is unconditional but over hand-written ROM
ANALOGUES.  This section supplies the join, in the shape `HierarchicalGraphCommitment` uses for its own
game (`hgcRom_graph_forgery_is_break`): an INSTANTIATION of the deployed `Hash` interface by the sampled
role-keyed oracle, four correspondence lemmas, and then the object-level statement.

* `romHash l H : Hash` answers a deployed limb list by DISPATCHING on the absorbed tag —
  `LEAF_TAG` → the leaf role at `(index, slot)`, `PAIR_TAG`/`ROOT_TAG` → the pair/root role at the two
  child digests — and returns the oracle's `Fin (2 ^ l)` answer in lane 0.  The dispatch is total and the
  decoders (`decIndex`, `decSlot`, `decLeft`, `decRight`) round-trip the tree's OWN encodings, because
  `leafInputs` carries the index and `nodeInputs` carries its children in order.  ⚑ NOTHING STRUCTURAL IS
  MISSING: the bridge needs exactly (i) the three absorb shapes distinguishable from the limb list — the
  three distinct head tags give this — and (ii) the leaf message to carry its position and the node
  message its child order — `leafInputs`/`nodeInputs` already do.  No per-position tag, no extra domain
  separation had to be added.
* `romHash_leafDigest` / `romHash_pairDigest` / `romHash_rootDigest` are the three layer bridges, and
  `romHash_semanticRoot` (⟷ `hgcRomRoot`), `romHash_pathFor` (⟷ `romPathFor`) and
  `romHash_rootFromPath` (⟷ `romRootFromPath`) are the three the header named as missing.  The path
  bridge holds for an ARBITRARY adversarial `Path4`, not just honest ones.
* `frame_object_break_is_win` is the join: an ACCEPTED `AncestorUpdate` at the modelled hash whose
  before-slot is wrong, OR whose after-graph is not the before-graph with that one slot replaced, IS a
  concrete win of `frameForgery` — so `frame_binds_rom` prices it.  `objFrame_binds_rom` states that
  with no `TreeAbsorbInjective`, no escape branch, and no `∃ collision`: the escape is a GAME WIN whose
  probability the birthday floor bounds, and `objFrame_constAnswer_defanged` exhibits an instance where
  that win actually happens, so the price is nonzero.

⚠ WHAT IS STILL NOT CLOSED.  `romHash l H` is the sampled oracle wearing the deployed `Hash` interface,
not Poseidon2: the modelling step of `RomCarrierSites` is INHERITED here verbatim and is now visible at
the `Hash` type itself.  Two consequences worth saying out loud: (a) nothing is claimed about the fixed
public digest — CR of a fixed function is a conjecture, not a theorem; (b) `embedDig` puts the whole
`λ`-bit answer in ONE lane, so the eight-lane deployed digest is idealised as a single `λ`-growing value
and the ~31-bit felt width of the real lanes is NOT modelled.  §1's `TreeAbsorbInjective` remains
refuted and §1 remains a layout statement; the deployed AIR still absorbs the whole graph core. -/

/-- The ROM digest, as a deployed `Digest8`: lane 0 carries the value, lanes 1-7 are zero. -/
def embedDig (l : ℕ) (r : RomDig l) : Digest8 := fun i => if i.val = 0 then (r.val : Int) else 0

/-- The retraction, TOTAL — an ADVERSARIAL `Digest8` is NOT assumed to be in `embedDig`'s image. -/
def toRomDig (l : ℕ) (d : Digest8) : RomDig l :=
  ⟨(d 0).toNat % 2 ^ l, Nat.mod_lt _ (by positivity)⟩

theorem toRomDig_embedDig (l : ℕ) (r : RomDig l) : toRomDig l (embedDig l r) = r := by
  apply Fin.ext
  show (embedDig l r 0).toNat % 2 ^ l = r.val
  have h0 : embedDig l r 0 = (r.val : Int) := rfl
  rw [h0]
  simp [Nat.mod_eq_of_lt r.isLt]

theorem embedDig_injective (l : ℕ) : Function.Injective (embedDig l) := by
  intro a b h
  rw [← toRomDig_embedDig l a, h, toRomDig_embedDig]

/-- The deployed `Hash` output carrying one ROM digest: lane 0, then seven zeros. -/
def romOut (l : ℕ) (r : RomDig l) : List Int := [(r.val : Int), 0, 0, 0, 0, 0, 0, 0]

theorem digest8_eq_embed_of_out {K : Hash} {xs : List Int} {l : ℕ} {r : RomDig l}
    (h : K xs = romOut l r) : digest8 K xs = embedDig l r := by
  funext i
  show (K xs).getD i.val 0 = embedDig l r i
  rw [h]
  fin_cases i <;> simp [romOut, embedDig]

/-! #### The decoders — they round-trip the tree's OWN encodings. -/

/-- Decode a `Fin 16` field (a `Label` or a `Node`) from its absorbed limb. -/
def decFin16 (x : Int) : Node := ⟨x.toNat % 16, Nat.mod_lt _ (by norm_num)⟩

theorem decFin16_val (n : Fin 16) : decFin16 ((n.val : ℕ) : Int) = n :=
  Fin.ext (by simp [decFin16, Nat.mod_eq_of_lt n.isLt])

/-- Decode an activity bit from its absorbed limb. -/
def decBool (x : Int) : Bool := decide (x ≠ 0)

theorem decBool_boolInt (b : Bool) : decBool (boolInt b) = b := by
  cases b <;> simp [decBool, boolInt]

/-- Decode a leaf absorb's slot INDEX — `leafInputs` carries it at position 1. -/
def decIndex (xs : List Int) : Fin 4 := ⟨(xs.getD 1 0).toNat % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Decode a leaf absorb's slot payload — positions 2-5 of `leafInputs`. -/
def decSlot (xs : List Int) : SlotEnc :=
  (decBool (xs.getD 2 0), decFin16 (xs.getD 3 0), decFin16 (xs.getD 4 0), decFin16 (xs.getD 5 0))

/-- Decode a node absorb's LEFT child — `nodeInputs` puts it at positions 1-8, in order. -/
def decLeft (xs : List Int) : Digest8 := fun i => xs.getD (1 + i.val) 0

/-- Decode a node absorb's RIGHT child — positions 9-16. -/
def decRight (xs : List Int) : Digest8 := fun i => xs.getD (9 + i.val) 0

theorem decIndex_leafInputs (i : Fin 4) (s : HostEdgeSlot) : decIndex (leafInputs i s) = i := by
  apply Fin.ext
  show ((leafInputs i s).getD 1 0).toNat % 4 = i.val
  have h : (leafInputs i s).getD 1 0 = ((i.val : ℕ) : Int) := rfl
  rw [h]
  simp [Nat.mod_eq_of_lt i.isLt]

theorem decSlot_leafInputs (i : Fin 4) (s : HostEdgeSlot) : decSlot (leafInputs i s) = slotEnc s := by
  show (decBool (boolInt s.active), decFin16 ((s.label.val : ℕ) : Int),
      decFin16 ((s.src.val : ℕ) : Int), decFin16 ((s.dst.val : ℕ) : Int)) = slotEnc s
  rw [decBool_boolInt, decFin16_val, decFin16_val, decFin16_val]
  rfl

theorem decLeft_nodeInputs (tag : Int) (x y : Digest8) : decLeft (nodeInputs tag x y) = x := by
  funext i
  fin_cases i <;> rfl

theorem decRight_nodeInputs (tag : Int) (x y : Digest8) : decRight (nodeInputs tag x y) = y := by
  funext i
  fin_cases i <;> rfl

/-! #### The instantiation, and the three layer bridges. -/

/-- **⚑ THE DEPLOYED `Hash` INTERFACE, ANSWERED BY THE SAMPLED ORACLE.** A limb list is dispatched on
its absorbed tag onto the matching role of `hgcRomFamily`, and the oracle's answer is returned in lane
0.  This is where the `RomCarrierSites` modelling step becomes visible at the deployed type: the object
below IS a `Hash`, and every deployed definition (`leafDigest`, `semanticRoot`, `rootFromPath`,
`pathFor`, `AncestorUpdate.check`) applies to it unchanged. -/
def romHash (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) : Hash := fun xs =>
  if xs.getD 0 0 = LEAF_TAG then
    romOut l (H (hgcLeafRole, Sum.inl (decIndex xs, decSlot xs)))
  else if xs.getD 0 0 = PAIR_TAG then
    romOut l (H (hgcPairRole, Sum.inr (toRomDig l (decLeft xs), toRomDig l (decRight xs))))
  else if xs.getD 0 0 = ROOT_TAG then
    romOut l (H (hgcRootRole, Sum.inr (toRomDig l (decLeft xs), toRomDig l (decRight xs))))
  else romOut l (H (hgcLeafRole, Sum.inl (0, (false, 0, 0, 0))))

theorem romHash_leafInputs (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (i : Fin 4)
    (s : HostEdgeSlot) :
    romHash l H (leafInputs i s) = romOut l (romLeaf l H i (slotEnc s)) := by
  have hhead : (leafInputs i s).getD 0 0 = LEAF_TAG := rfl
  unfold romHash
  rw [if_pos hhead, decIndex_leafInputs, decSlot_leafInputs]
  rfl

theorem romHash_pairInputs (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (x y : Digest8) :
    romHash l H (nodeInputs PAIR_TAG x y)
      = romOut l (romPairOf l H (toRomDig l x, toRomDig l y)) := by
  have hhead : (nodeInputs PAIR_TAG x y).getD 0 0 = PAIR_TAG := rfl
  unfold romHash
  rw [if_neg (by rw [hhead]; norm_num [PAIR_TAG, LEAF_TAG]), if_pos hhead,
    decLeft_nodeInputs, decRight_nodeInputs]
  rfl

theorem romHash_rootInputs (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (x y : Digest8) :
    romHash l H (nodeInputs ROOT_TAG x y)
      = romOut l (romRootOf l H (toRomDig l x, toRomDig l y)) := by
  have hhead : (nodeInputs ROOT_TAG x y).getD 0 0 = ROOT_TAG := rfl
  unfold romHash
  rw [if_neg (by rw [hhead]; norm_num [ROOT_TAG, LEAF_TAG]),
    if_neg (by rw [hhead]; norm_num [ROOT_TAG, PAIR_TAG]), if_pos hhead,
    decLeft_nodeInputs, decRight_nodeInputs]
  rfl

/-- **BRIDGE 1 — the LEAF layer.** The deployed `leafDigest` at the modelled hash IS the ROM leaf
absorb of the same index and the same (losslessly encoded) slot. -/
theorem romHash_leafDigest (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (i : Fin 4)
    (s : HostEdgeSlot) :
    leafDigest (romHash l H) i s = embedDig l (romLeaf l H i (slotEnc s)) :=
  digest8_eq_embed_of_out (romHash_leafInputs l H i s)

/-- **BRIDGE 2 — the PAIR layer**, for ARBITRARY (adversarial) children. -/
theorem romHash_pairDigest (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (x y : Digest8) :
    nodeDigest (romHash l H) PAIR_TAG x y
      = embedDig l (romPairOf l H (toRomDig l x, toRomDig l y)) :=
  digest8_eq_embed_of_out (romHash_pairInputs l H x y)

/-- **BRIDGE 3 — the ROOT layer**, for ARBITRARY (adversarial) children. -/
theorem romHash_rootDigest (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (x y : Digest8) :
    nodeDigest (romHash l H) ROOT_TAG x y
      = embedDig l (romRootOf l H (toRomDig l x, toRomDig l y)) :=
  digest8_eq_embed_of_out (romHash_rootInputs l H x y)

theorem romHash_leftPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : BoundedGraph) :
    leftPair (romHash l H) g = embedDig l (romLeftPair l H (graphEnc g)) := by
  rw [leftPair, romHash_pairDigest, romHash_leafDigest, romHash_leafDigest, toRomDig_embedDig,
    toRomDig_embedDig]
  rfl

theorem romHash_rightPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : BoundedGraph) :
    rightPair (romHash l H) g = embedDig l (romRightPair l H (graphEnc g)) := by
  rw [rightPair, romHash_pairDigest, romHash_leafDigest, romHash_leafDigest, toRomDig_embedDig,
    toRomDig_embedDig]
  rfl

/-- **⚑ BRIDGE — `hgcRomRoot` ↔ `semanticRoot`.** The header's first named missing lemma. -/
theorem romHash_semanticRoot (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : BoundedGraph) :
    semanticRoot (romHash l H) g = embedDig l (hgcRomRoot l H (graphEnc g)) := by
  rw [semanticRoot, romHash_rootDigest, romHash_leftPair, romHash_rightPair, toRomDig_embedDig,
    toRomDig_embedDig]
  rfl

/-- The ROM face of a deployed `Path4`, applied to an ARBITRARY (adversarial) path. -/
def toRomPath (l : ℕ) (p : Path4) : RomPath l :=
  (toRomDig l p.siblingLeaf, toRomDig l p.siblingPair)

/-- **⚑ BRIDGE — `romPathFor` ↔ `pathFor`.** The header's second named missing lemma. -/
theorem romHash_pathFor (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : BoundedGraph)
    (u : Fin 4) :
    toRomPath l (pathFor (romHash l H) g u) = romPathFor l H (graphEnc g) u := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    simp [toRomPath, pathFor, romPathFor, romHash_leafDigest, romHash_leftPair, romHash_rightPair,
      toRomDig_embedDig, graphEnc]

/-- **⚑ BRIDGE — `romRootFromPath` ↔ `rootFromPath`.** The header's third named missing lemma, and the
one that has to hold for an ARBITRARY offered path: the forger's path is not assumed honest. -/
theorem romHash_rootFromPath (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (u : Fin 4)
    (leaf : Digest8) (p : Path4) :
    rootFromPath (romHash l H) u leaf p
      = embedDig l (romRootFromPath l H u (toRomDig l leaf) (toRomPath l p)) := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    simp [rootFromPath, romRootFromPath, framePairBlock, frameRootBlock, romHash_rootDigest,
      romHash_pairDigest, toRomDig_embedDig, toRomPath]

/-- The bridge as the forger consumes it: the deployed reconstruction from the AUTHENTICATED leaf. -/
theorem romHash_rootFromPath_leaf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (u : Fin 4)
    (s : HostEdgeSlot) (p : Path4) :
    rootFromPath (romHash l H) u (leafDigest (romHash l H) u s) p
      = embedDig l (romRootFromPath l H u (romLeaf l H u (slotEnc s)) (toRomPath l p)) := by
  rw [romHash_rootFromPath, romHash_leafDigest, toRomDig_embedDig]

/-! #### The join: the DEPLOYED `AncestorUpdate.check`, with NO `TreeAbsorbInjective`. -/

/-- **THE ANSWER AN OBJECT-LEVEL FRAME BREAK HANDS THE ROM FORGER.** Two shapes, because the deployed
frame conclusion has two conjuncts and the game's win relation is the exactness break: if the
authenticated `before` really is the committed slot, the break is the after-graph (first branch); if it
is not, re-presenting the before-graph against itself is already an exactness break (second branch). -/
def objFrameAns (l : ℕ) (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate) : FrameAns l :=
  if g₁.slots upd.index = upd.before then
    ⟨upd.index, slotEnc upd.before, slotEnc upd.after, toRomPath l upd.path,
      graphEnc g₁, graphEnc g₂⟩
  else
    ⟨upd.index, slotEnc upd.before, slotEnc upd.before, toRomPath l upd.path,
      graphEnc g₁, graphEnc g₁⟩

/-- **⚑⚑ THE JOIN — the mirror of `hgcRom_graph_forgery_is_break`, at the FRAME game.** An accepted
`AncestorUpdate` at the modelled hash that does NOT frame — the authenticated before-slot is not the
committed one, or the after-graph is not the before-graph with that ONE slot replaced — is a CONCRETE
win of `frameForgery`.  No `TreeAbsorbInjective`, no collision disjunction: the object-level break
becomes a game the birthday floor prices. -/
theorem frame_object_break_is_win (l : ℕ) (H : frameBreakGame.Inst l)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcheck : upd.check (romHash l H) (semanticRoot (romHash l H) g₁)
      (semanticRoot (romHash l H) g₂) = true)
    (hbreak : ¬ (g₁.slots upd.index = upd.before
      ∧ g₂.slots = Function.update g₁.slots upd.index upd.after)) :
    frameBreakGame.wins l H (objFrameAns l g₁ g₂ upd) := by
  rw [AncestorUpdate.check, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨_, _⟩, hbd⟩, had⟩ := hcheck
  have h1 : rootFromPath (romHash l H) upd.index
      (leafDigest (romHash l H) upd.index upd.before) upd.path
      = semanticRoot (romHash l H) g₁ := digestFields_injective (of_decide_eq_true hbd)
  have h2 : rootFromPath (romHash l H) upd.index
      (leafDigest (romHash l H) upd.index upd.after) upd.path
      = semanticRoot (romHash l H) g₂ := digestFields_injective (of_decide_eq_true had)
  have hb : romRootFromPath l H upd.index (romLeaf l H upd.index (slotEnc upd.before))
      (toRomPath l upd.path) = hgcRomRoot l H (graphEnc g₁) := by
    apply embedDig_injective l
    erw [← romHash_rootFromPath_leaf, ← romHash_semanticRoot]
    exact h1
  have ha : romRootFromPath l H upd.index (romLeaf l H upd.index (slotEnc upd.after))
      (toRomPath l upd.path) = hgcRomRoot l H (graphEnc g₂) := by
    apply embedDig_injective l
    erw [← romHash_rootFromPath_leaf, ← romHash_semanticRoot]
    exact h2
  unfold objFrameAns
  split_ifs with hidx
  · refine ⟨hb, ha, fun hEq => hbreak ⟨hidx, ?_⟩⟩
    funext i
    have h := congrFun hEq i
    rw [romReplace, Function.update_apply] at h
    rw [Function.update_apply]
    by_cases hi : i = upd.index
    · rw [if_pos hi] at h ⊢
      exact slotEnc_injective h
    · rw [if_neg hi] at h ⊢
      exact slotEnc_injective h
  · refine ⟨hb, hb, fun hEq => hidx ?_⟩
    have h := congrFun hEq upd.index
    rw [romReplace, Function.update_apply, if_pos rfl] at h
    exact slotEnc_injective h

/-- **⚑ THE DEPLOYED-OBJECT FRAME CONVERSE, PRICED.** At the modelled hash, an accepted
`AncestorUpdate` between two committed graphs EITHER frames exactly — the authenticated before-slot is
the committed one and the after-graph is the before-graph with only that slot replaced — OR the update
IS a genuine `frameForgery` win, whose probability `frame_binds_rom` bounds by the birthday floor.

⚠ This is NOT a `∨ ∃ collision`: the right disjunct is a WIN OF A GAME at the SAMPLED instance, so it
is an event with a proved negligible measure (`objFrame_binds_rom`), not a proposition that is
unconditionally true at any compressing hash. -/
theorem frame_of_check_at_modelled_hash (l : ℕ) (H : frameBreakGame.Inst l)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcheck : upd.check (romHash l H) (semanticRoot (romHash l H) g₁)
      (semanticRoot (romHash l H) g₂) = true) :
    (g₁.slots upd.index = upd.before
        ∧ g₂.slots = Function.update g₁.slots upd.index upd.after)
      ∨ frameBreakGame.wins l H (objFrameAns l g₁ g₂ upd) := by
  by_cases h : g₁.slots upd.index = upd.before
      ∧ g₂.slots = Function.update g₁.slots upd.index upd.after
  · exact Or.inl h
  · exact Or.inr (frame_object_break_is_win l H g₁ g₂ upd hcheck h)

/-! #### The deployed-object break, as a GAME on the same sampled oracle — and its price. -/

/-- **THE OBJECT-LEVEL FRAME BREAK, AS A `Game`.** Instance: the SAME sampled role-keyed oracle.
Answer: two `BoundedGraph`s and a deployed `AncestorUpdate`.  Win: the deployed
`AncestorUpdate.check` ACCEPTS at the modelled hash and the frame conclusion FAILS.  Nothing in this
game mentions the ROM analogues — it is stated entirely in the objects §1 is about. -/
def objFrameGame : Game where
  Inst := fun l => HgcRole × HgcRomMsg l → RomDig l
  Ans := fun _ => BoundedGraph × BoundedGraph × AncestorUpdate
  instFin := fun l => frameBreakGame.instFin l
  instNe := fun l => frameBreakGame.instNe l
  wins := fun l H a =>
    a.2.2.check (romHash l H) (semanticRoot (romHash l H) a.1)
        (semanticRoot (romHash l H) a.2.1) = true
      ∧ ¬ (a.1.slots a.2.2.index = a.2.2.before
        ∧ a.2.1.slots = Function.update a.1.slots a.2.2.index a.2.2.after)
  winsDec := fun _ _ _ => by infer_instance

/-- The ROM forger an object-level frame breaker induces — a PURE post-processing of its output. -/
def objFrameToRom (B : Adversary objFrameGame) : Adversary frameBreakGame where
  run := fun l H => objFrameAns l (B.run l H).1 (B.run l H).2.1 (B.run l H).2.2

/-- **WIN PRESERVATION, OBJECT → ROM.** Every oracle at which the object-level breaker wins is one at
which the extracted ROM forger wins, so its advantage is dominated. -/
theorem objFrame_adv_le (B : Adversary objFrameGame) (l : ℕ) :
    gameAdv objFrameGame B l ≤ gameAdv frameBreakGame (objFrameToRom B) l := by
  refine @winProb_le_of_imp _ (objFrameGame.instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hcheck, hbreak⟩ := hH
  exact frame_object_break_is_win l H _ _ _ hcheck hbreak

/-- **THE QUERY-BOUNDED OBJECT-LEVEL BREAKER CLASS** — the same `Eff` as everywhere else: the breaker
factors through a `Q`-query tree fixed before the oracle is sampled. -/
def ObjFrameEff (Q : ℕ → ℕ) (B : Adversary objFrameGame) : Prop :=
  ∃ M : ∀ l, OracleComp (hgcRomFamily.toRomFamily.D l) (hgcRomFamily.toRomFamily.R l)
      (BoundedGraph × BoundedGraph × AncestorUpdate),
    (∀ l, QueryBounded (Q l) (M l)) ∧
      ∀ l (H : objFrameGame.Inst l), B.run l H = (M l).eval H

/-- The extraction costs NOTHING: `objFrameAns` is pure post-processing, so the budget is unchanged. -/
theorem objFrameToRom_eff (Q : ℕ → ℕ) (B : Adversary objFrameGame) (hB : ObjFrameEff Q B) :
    RomForgeryEff hgcRomFamily frameForgery Q (objFrameToRom B) := by
  obtain ⟨M, hM, hrun⟩ := hB
  refine ⟨fun l => OracleComp.bindComp (M l)
      (fun a => OracleComp.pure (objFrameAns l a.1 a.2.1 a.2.2)),
    fun l => (OracleComp.bindComp_queryBounded (hM l)
      (fun a => QueryBounded.pure 0 _)).mono (by omega),
    fun l H => ?_⟩
  show objFrameAns l (B.run l H).1 (B.run l H).2.1 (B.run l H).2.2 = _
  erw [OracleComp.bindComp_eval, hrun l H]
  rfl

/-- **⚑⚑ THE FRAME CONVERSE ON THE DEPLOYED OBJECTS, DISCHARGED ON THE PROVED KEYED-ROM FLOOR.**

Every query-bounded adversary that produces an ACCEPTED deployed `AncestorUpdate` at the modelled hash
whose committed graphs do NOT satisfy the frame conclusion has NEGLIGIBLE advantage.  Equivalently:
except with negligible probability, an accepted `AncestorUpdate` at index `u` authenticates the graph's
OWN slot at `u` and changes the committed graph ONLY there.

This is the statement §1 could only make under `TreeAbsorbInjective` — which this file REFUTES for
every bounded-lane digest — now carrying §2's unconditional price.  NO layout hypothesis, NO floor
hypothesis, NO escape branch, NO `∃ collision`. -/
theorem objFrame_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (B : Adversary objFrameGame) (hB : ObjFrameEff Q B) :
    Negl (gameAdv objFrameGame B) :=
  negl_of_le (fun l => (gameAdv_mem_unit objFrameGame B l).1) (objFrame_adv_le B)
    (frame_binds_rom Q hQ (objFrameToRom B) (objFrameToRom_eff Q B hB))

/-! #### §2b teeth — the OBJECT-LEVEL game is genuinely winnable, so the price is nonzero. -/

/-- The all-padding bounded graph. -/
def padGraph : BoundedGraph where
  slots := fun _ => ⟨false, 0, 0, 0⟩
  canonicalPadding := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The bounded graph that differs from `padGraph` at slot `0` only. -/
def liveGraph : BoundedGraph where
  slots := fun i => if i = 0 then ⟨true, 0, 0, 0⟩ else ⟨false, 0, 0, 0⟩
  canonicalPadding := by
    intro i
    by_cases hi : i = 0 <;> simp [hi, HostEdgeSlot.canonicalPadding]

/-- A deployed break witness: an update that re-authenticates the PADDING slot at index `0` (so it
claims nothing changed) while the after-graph has slot `0` LIVE. -/
def objBreakWitness : BoundedGraph × BoundedGraph × AncestorUpdate :=
  (padGraph, liveGraph, ⟨0, ⟨false, 0, 0, 0⟩, ⟨false, 0, 0, 0⟩, ⟨fun _ => 0, fun _ => 0⟩⟩)

theorem romHash_const (l : ℕ) (r : RomDig l) (xs : List Int) :
    romHash l (fun _ => r) xs = romOut l r := by
  unfold romHash
  split_ifs <;> rfl

/-- **(TOOTH — the OBJECT-LEVEL frame game is WINNABLE.)** At the constant oracle every absorb
collapses to one digest, so the deployed `AncestorUpdate.check` ACCEPTS while the after-graph is not
the before-graph with slot `0` replaced.  The deployed statement therefore prices something genuinely
nonzero — it is not satisfied by "the check never accepts". -/
theorem objBreakWitness_wins (l : ℕ) (r : RomDig l) :
    objFrameGame.wins l (fun _ => r) objBreakWitness := by
  have hd : ∀ xs, digest8 (romHash l (fun _ => r)) xs = embedDig l r := fun xs =>
    digest8_eq_embed_of_out (romHash_const l r xs)
  have hroot : ∀ (u : Fin 4) (leaf : Digest8) (p : Path4),
      rootFromPath (romHash l (fun _ => r)) u leaf p = embedDig l r := by
    intro u leaf p
    rcases fin4_cases u with rfl | rfl | rfl | rfl <;> exact hd _
  have hsem : ∀ g, semanticRoot (romHash l (fun _ => r)) g = embedDig l r := fun _ => hd _
  refine ⟨?_, ?_⟩
  · simp only [objBreakWitness, AncestorUpdate.check, Bool.and_eq_true, decide_eq_true_eq,
      hroot, hsem]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> trivial
  · rintro ⟨-, h⟩
    have h0 := congrFun h 0
    simp only [objBreakWitness, liveGraph, padGraph, Function.update_self] at h0
    exact absurd (congrArg HostEdgeSlot.active h0) (by simp)

/-- The `0`-query object-level breaker that always outputs `objBreakWitness`. -/
def constObjAdv : Adversary objFrameGame where
  run := fun _ _ => objBreakWitness

/-- **(TOOTH — the deployed-object price is REAL and the constant breaker is DEFANGED.)** The `0`-query
constant breaker is IN the class, WINS at the constant oracle, and its advantage is NEGLIGIBLE by
`objFrame_binds_rom`.  Both poles, on the DEPLOYED objects. -/
theorem objFrame_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    ObjFrameEff Q constObjAdv
      ∧ (∀ l, 0 < gameAdv objFrameGame constObjAdv l)
      ∧ Negl (gameAdv objFrameGame constObjAdv) := by
  have hmem : ObjFrameEff Q constObjAdv :=
    ⟨fun _ => OracleComp.pure objBreakWitness, fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, objFrame_binds_rom Q hQ _ hmem⟩
  obtain ⟨r₀⟩ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, by positivity⟩⟩
  refine @winProb_pos_of_witness _ (objFrameGame.instFin l) _ (fun _ => r₀) ?_
  exact (Adversary.hit_eq_true _ l _).mpr (objBreakWitness_wins l r₀)

end RomFrame

/-! ## §3 — WHAT THE CONVERSE BUYS: the update's absorb schedule is the ancestor path.

Counted at the deployed shape, as propositions about the commitment — not benchmarks. -/

/-- The absorb schedule of a FULL root recomputation: four leaves, two pairs, the root. -/
def semanticRootAbsorbs (H : Hash) (g : BoundedGraph) : List (List Int) :=
  [leafInputs 0 (g.slots 0), leafInputs 1 (g.slots 1), leafInputs 2 (g.slots 2),
    leafInputs 3 (g.slots 3),
    nodeInputs PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)),
    nodeInputs PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)),
    nodeInputs ROOT_TAG (leftPair H g) (rightPair H g)]

/-- The absorb schedule of an ANCESTOR UPDATE: the new leaf, `u`'s pair, the root — and nothing else.
Its arguments are the index, the new slot and the two path digests; no other slot can appear. -/
def updateAbsorbs (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) : List (List Int) :=
  match u.val with
  | 0 => [leafInputs u s, nodeInputs PAIR_TAG (leafDigest H u s) p.siblingLeaf,
      nodeInputs ROOT_TAG (nodeDigest H PAIR_TAG (leafDigest H u s) p.siblingLeaf) p.siblingPair]
  | 1 => [leafInputs u s, nodeInputs PAIR_TAG p.siblingLeaf (leafDigest H u s),
      nodeInputs ROOT_TAG (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H u s)) p.siblingPair]
  | 2 => [leafInputs u s, nodeInputs PAIR_TAG (leafDigest H u s) p.siblingLeaf,
      nodeInputs ROOT_TAG p.siblingPair (nodeDigest H PAIR_TAG (leafDigest H u s) p.siblingLeaf)]
  | _ => [leafInputs u s, nodeInputs PAIR_TAG p.siblingLeaf (leafDigest H u s),
      nodeInputs ROOT_TAG p.siblingPair (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H u s))]

theorem updateAbsorbs_length (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) :
    (updateAbsorbs H u s p).length = 3 := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;> rfl

theorem semanticRootAbsorbs_length (H : Hash) (g : BoundedGraph) :
    (semanticRootAbsorbs H g).length = 7 := rfl

/-- The reconstructed root IS the digest of the schedule's last absorb. -/
theorem rootFromPath_eq_last_absorb (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) :
    rootFromPath H u (leafDigest H u s) p = digest8 H ((updateAbsorbs H u s p).getD 2 []) := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;> rfl

/-- The full root is the digest of the full schedule's last absorb. -/
theorem semanticRoot_eq_last_absorb (H : Hash) (g : BoundedGraph) :
    semanticRoot H g = digest8 H ((semanticRootAbsorbs H g).getD 6 []) := rfl

/-- **⚑⚑ THE Θ(|G|) → depth+1 STATEMENT.** The root of the graph with slot `u` replaced is the digest
of the LAST of THREE absorbs, and those three absorbs are determined by `(u, the new slot, the two
path digests)` — the ancestor path — alone.  The rest of the graph is not read. -/
theorem update_rehashes_only_ancestor_path (H : Hash) (g : BoundedGraph) (u : Fin 4)
    (s : HostEdgeSlot) (hc : s.canonicalPadding) :
    semanticRoot H (replaceSlot g u s hc)
      = digest8 H ((updateAbsorbs H u s (pathFor H g u)).getD 2 []) := by
  have hslot : (replaceSlot g u s hc).slots u = s := by
    simp [replaceSlot]
  have h1 := pathFor_reconstructs H (replaceSlot g u s hc) u
  rw [hslot, pathFor_replaceSlot H g u s hc] at h1
  rw [← h1]
  exact rootFromPath_eq_last_absorb H u s (pathFor H g u)

/-- **THE UPDATE READS THE OLD GRAPH ONLY THROUGH ITS PATH.** Two graphs with the same ancestor path
at `u` have the same updated root — the frame, from the COST side. -/
theorem afterRoot_depends_only_on_path (H : Hash) (g g' : BoundedGraph) (u : Fin 4)
    (s : HostEdgeSlot) (hc : s.canonicalPadding) (h : pathFor H g u = pathFor H g' u) :
    semanticRoot H (replaceSlot g u s hc) = semanticRoot H (replaceSlot g' u s hc) := by
  rw [update_rehashes_only_ancestor_path H g u s hc,
    update_rehashes_only_ancestor_path H g' u s hc, h]

/-- **THE COUNT, AT THE DEPLOYED SHAPE.** Three absorbs is depth + 1 (`2 ^ (3 - 1) = GRAPH_SLOTS`),
seven is the full tree (`2 * GRAPH_SLOTS - 1`).  ⚠ These are INSTANCES at `GRAPH_SLOTS = 4`, not a
theorem over `n`: the general depth-`d` statement needs a depth-parametric tree this prototype does
not have. -/
theorem frame_cost_at_deployed_slots (H : Hash) (g : BoundedGraph) (u : Fin 4) (s : HostEdgeSlot)
    (p : Path4) :
    2 ^ ((updateAbsorbs H u s p).length - 1) = GRAPH_SLOTS
      ∧ (semanticRootAbsorbs H g).length = 2 * GRAPH_SLOTS - 1
      ∧ (updateAbsorbs H u s p).length < (semanticRootAbsorbs H g).length := by
  rw [updateAbsorbs_length, semanticRootAbsorbs_length]
  refine ⟨by norm_num [GRAPH_SLOTS], by norm_num [GRAPH_SLOTS], by norm_num⟩

/-- **⚑⚑ WHAT IT BUYS, ON A REAL REWRITE STEP.** A bounded rewrite step that touches only slot `u`
is a generic `RewriteStep`, its committed endpoints are joined by ONE ACCEPTED `AncestorUpdate`, and
that update's root recomputation is THREE absorbs against the full recompute's SEVEN.  With
`frame_binds_rom`, acceptance is not merely necessary but (except with negligible probability)
sufficient: nothing outside slot `u` can have moved. -/
theorem single_slot_step_logarithmic_update (H : Hash) (rules : List BoundedRule)
    (g : BoundedGraph) (u : Fin 4) (s : HostEdgeSlot) (hc : s.canonicalPadding)
    (rule : BoundedRule) (sigma : Var → Node) (context : BoundedContext)
    (hstep : BoundedOneStep rules g (replaceSlot g u s hc) rule sigma context) :
    RewriteStep (rules.map BoundedRule.toRule) g.toHypergraph (replaceSlot g u s hc).toHypergraph
      ∧ (updateLeaf H g u s).check H (semanticRoot H g)
          (semanticRoot H (replaceSlot g u s hc)) = true
      ∧ semanticRoot H (replaceSlot g u s hc)
          = digest8 H ((updateAbsorbs H u s (pathFor H g u)).getD 2 [])
      ∧ (updateAbsorbs H u s (pathFor H g u)).length = 3
      ∧ (semanticRootAbsorbs H (replaceSlot g u s hc)).length = 7 :=
  ⟨boundedOneStep_to_rewriteStep hstep,
    updateLeaf_checks H g u s hc,
    update_rehashes_only_ancestor_path H g u s hc,
    updateAbsorbs_length H u s (pathFor H g u),
    semanticRootAbsorbs_length H (replaceSlot g u s hc)⟩

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  fin4_cases,
  path_peel,
  slots_agree_off_index,
  frame_of_absorbInjective,
  afterGraph_eq_replaceSlot,
  injHash_digest8_injective,
  treeAbsorbInjective_of_digest8_injective,
  exists_treeAbsorbInjective,
  not_treeAbsorbInjective_of_boundedLanes,
  hgcRomRoot_eq,
  romRootFromPath_honest,
  frame_violation_wins,
  hgcSelect_wins,
  frameSelect_wins,
  frame_binds_rom,
  frame_constAnswer_defanged,
  frame_nonNegl_forger_excluded,
  updateAbsorbs_length,
  semanticRootAbsorbs_length,
  rootFromPath_eq_last_absorb,
  semanticRoot_eq_last_absorb,
  update_rehashes_only_ancestor_path,
  afterRoot_depends_only_on_path,
  frame_cost_at_deployed_slots,
  single_slot_step_logarithmic_update,
  -- §2b — the ROM↔object bridge and the deployed-object converse.
  toRomDig_embedDig,
  embedDig_injective,
  digest8_eq_embed_of_out,
  decFin16_val,
  decBool_boolInt,
  decIndex_leafInputs,
  decSlot_leafInputs,
  decLeft_nodeInputs,
  decRight_nodeInputs,
  romHash_leafInputs,
  romHash_pairInputs,
  romHash_rootInputs,
  romHash_leafDigest,
  romHash_pairDigest,
  romHash_rootDigest,
  romHash_leftPair,
  romHash_rightPair,
  romHash_semanticRoot,
  romHash_pathFor,
  romHash_rootFromPath,
  romHash_rootFromPath_leaf,
  frame_object_break_is_win,
  frame_of_check_at_modelled_hash,
  objFrame_adv_le,
  objFrameToRom_eff,
  objFrame_binds_rom,
  romHash_const,
  objBreakWitness_wins,
  objFrame_constAnswer_defanged]

end Dregg2.Crypto.HierarchicalGraphFrame
