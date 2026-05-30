/-
# Dregg2.Authority.CDT — the capability-derivation-tree as the authority spine.

This is **candidate C's primary structural object** (`cand-C §1`, `dregg2 §1.1`): one
append-only, content-addressed partial order of `(parent → child)` edges, each edge a
**monotone attenuation**. The same structure, viewed three ways (the deepest collapse,
`cand-C §1`):

  * as a **cap graph** it is the seL4 CDT (`Mint`/`Copy`/`Revoke`);
  * as a **strand log** it is the blocklace (per-strand append-only causal DAG);
  * as a **biscuit delegation graph** it is the `Authority.Caveat` token chain.

> **CDT ≡ strand-log ≡ biscuit-graph.** A capability *is* a derivation node; appending a
> turn *is* minting/exercising an edge. There is no second data structure.

Here the CDT is modelled abstractly: a node carries its `authority` as a **set of rights**
(`Finset Authority.Auth`, ordered by ⊆ — the rights-lattice). A `CapHash` is an **opaque,
content-address id** — kept abstract (its injectivity / collision-resistance is a §8
crypto-interface obligation, NEVER a Lean law; see `REORIENT §6`).

The load-bearing content:
- a **`CapNode`** = `(self : CapHash, parent : Option CapHash, authority : Finset Auth)`;
- the **attenuation-edge invariant** `attenuates child parent := child.authority ⊆
  parent.authority` — the ONE rule the whole system rests on (`dregg2 §1.1`);
- a **`WellFormedCDT`**: every non-root node attenuates its (present) parent;
- **THE KEYSTONE — `path_attenuates`**: authority down ANY root-to-node `DerivationPath`
  in a well-formed CDT only SHRINKS (leaf.authority ⊆ root.authority), by induction on the
  path (transitivity of ⊆). "Authority never grows along a derivation chain" — the
  seL4-integrity / LossyMorphism backbone;
- the **bridge to `Caveat`**: a `Token`'s attenuation chain (`Token.attenuate` /
  `attenuate_narrows`) IS the biscuit rendering of a CDT path — `chain_renders_path`
  exhibits both as one append-only, monotone-narrowing order;
- a **binding / non-vacuity witness**: an *amplifying* edge is rejected by `WellFormedCDT`
  (the invariant has teeth) — `amplifying_rejected`.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Positional
import Dregg2.Authority.Caveat
import Mathlib.Data.Finset.Basic

namespace Dregg2.Authority.CDT

open Dregg2.Authority

/-! ## The opaque content-address id -/

/-- **`CapHash`** — the content-address identity of a derivation node:
`H(canonical{root, target, authority, facet, caveats, parent, delta})` (`cand-C §1`). It is
an **opaque id** — modelled as a `Nat` so the CDT is concrete and `#eval`-able, but treated
abstractly: NO Lean theorem here depends on any property of hashing. Collision-resistance /
injectivity is a §8 crypto-interface obligation, discharged by the circuit + Rust cascade,
never merged into this semantic law (`REORIENT §6`). -/
abbrev CapHash := Nat

/-- The rights set a node confers — the authority lattice, ordered by ⊆. Reuses
`Authority.Auth` (the l4v auth labels) as the carrier; a `Finset` gives decidable ⊆ and the
order along which attenuation narrows. -/
abbrev Rights := Finset Auth

/-! ## The derivation node + the append-only collection -/

/-- **A `CapNode`** — one derivation node of the CDT. `self` is its content-address;
`parent = none` marks a **root** (a cell minting a root cap whose facet is its full
interface); `parent = some h` is a `(child → parent)` attenuation edge; `authority` is the
rights this node confers. -/
structure CapNode where
  self      : CapHash
  parent    : Option CapHash
  authority : Rights
  deriving DecidableEq

/-- **The CDT collection** — an append-only set of nodes (a finite map `CapHash → CapNode`,
represented as an association list keyed by `self`; the c-list cache over the gossiped DAG,
`cand-C §2.1`). Lookup walks to the first node with a matching `self`. (Named `Tree` to keep
the enclosing `CDT` namespace clean.) -/
abbrev Tree := List CapNode

/-- Resolve a `CapHash` to its node in the CDT (the content-address dereference). -/
def Tree.lookup (g : Tree) (h : CapHash) : Option CapNode :=
  g.find? (fun n => n.self = h)

/-! ## The attenuation edge invariant — the ONE rule -/

/-- **`attenuates child parent`** — the edge invariant (`dregg2 §1.1`): a child confers no
more authority than its parent. A child caps's rights are a **subset** of its parent's. This
is the lattice form of `attenuate_narrows` (the `Caveat` chain) and the LossyMorphism
`in_le`/`out_le` — attenuation only narrows. -/
def attenuates (child parent : CapNode) : Prop :=
  child.authority ⊆ parent.authority

instance (child parent : CapNode) : Decidable (attenuates child parent) := by
  unfold attenuates; exact inferInstance

/-- A node is a **root** iff it has no parent (a cell's full-interface mint). -/
def CapNode.isRoot (n : CapNode) : Prop := n.parent = none

/-- **`WellFormedCDT g`** — every non-root node attenuates its (resolvable) parent. The
single structural invariant the entire authority spine rests on: for any node with
`parent = some p`, the parent resolves in `g` and the edge is a monotone attenuation. (A
dangling parent ref — `lookup` returns `none` — is rejected: an edge must name a present
parent, the append-only / content-addressed discipline.) -/
def WellFormedCDT (g : Tree) : Prop :=
  ∀ n ∈ g, ∀ p, n.parent = some p →
    ∃ pn, g.lookup p = some pn ∧ attenuates n pn

/-! ## The derivation path — root-to-node -/

/-- **A `DerivationPath g leaf root`** — an explicit chain of nodes in `g` from `leaf` up to
`root`, each step a present `(child → parent)` edge. This is the *path* whose traversal an
exercise's proof *is* ("proof-is-truth is native", `cand-C §2.4`): the witness that `leaf`
descends from `root` by a sequence of edges.

* `refl`: the trivial path — `leaf` to itself (length 0).
* `step`: extend a path `mid ⤳ root` by a present edge `child → mid` (`child.parent = mid.self`,
  and `mid` resolves in `g`). -/
inductive DerivationPath (g : Tree) : CapNode → CapNode → Prop where
  /-- The empty path: any node derives from itself. -/
  | refl (n : CapNode) : DerivationPath g n n
  /-- Prepend a present edge `child → mid` to a path `mid ⤳ root`. -/
  | step {child mid root : CapNode}
      (hedge : child.parent = some mid.self)
      (hpresent : g.lookup mid.self = some mid)
      (rest : DerivationPath g mid root) :
      DerivationPath g child root

/-! ## THE KEYSTONE — authority only shrinks down a derivation path. -/

/-- **`edge_attenuates` (PROVED)** — in a well-formed CDT, any present edge `child → mid`
(i.e. `child.parent = some mid.self` with `mid` resolving to itself) is a monotone
attenuation: `child.authority ⊆ mid.authority`. The well-formedness invariant, *applied* to
one edge — the inductive step's engine. -/
theorem edge_attenuates {g : Tree} (wf : WellFormedCDT g)
    {child mid : CapNode} (hchild : child ∈ g)
    (hedge : child.parent = some mid.self)
    (hpresent : g.lookup mid.self = some mid) :
    child.authority ⊆ mid.authority := by
  obtain ⟨pn, hlk, hatt⟩ := wf child hchild mid.self hedge
  -- `lookup mid.self` is single-valued, so the well-formedness parent `pn` IS `mid`.
  rw [hpresent] at hlk
  cases hlk
  exact hatt

/-- **`path_attenuates` (PROVED) — THE KEYSTONE.** Authority down ANY root-to-node
derivation path in a well-formed CDT only SHRINKS: the leaf confers no more than the root
(`leaf.authority ⊆ root.authority`). Proved by induction on the path, chaining
`edge_attenuates` (each edge narrows) through transitivity of ⊆.

This is "authority never grows along a derivation chain" — the seL4-integrity property
carried across the net (`cand-C §0`), the lattice realization of the LossyMorphism backbone.
It requires only that the *leaf* lives in `g` (so well-formedness applies, and every higher
node on the path resolves to a present node by the path's `hpresent` edges). -/
theorem path_narrows {g : Tree} (wf : WellFormedCDT g) :
    ∀ {leaf root : CapNode}, DerivationPath g leaf root →
      leaf ∈ g →
      leaf.authority ⊆ root.authority := by
  intro leaf root path
  induction path with
  | refl n => intro _; exact Finset.Subset.refl _
  | step hedge hpresent rest ih =>
      rename_i child mid root
      intro hchild
      -- child → mid is a present edge: it narrows.
      have hstep : child.authority ⊆ mid.authority :=
        edge_attenuates wf hchild hedge hpresent
      -- mid is present in g (it resolved to itself), so the IH applies.
      have hmidmem : mid ∈ g := List.mem_of_find?_eq_some hpresent
      exact Finset.Subset.trans hstep (ih hmidmem)

/-- **`path_attenuates` (PROVED) — THE KEYSTONE, directly-usable form.** Along ANY root-to-node
derivation path in a well-formed CDT, the leaf confers no more authority than the root:
`leaf.authority ⊆ root.authority`. A thin re-statement of `path_narrows` with arguments
positional rather than under a `∀` — "authority never grows along a derivation chain." -/
theorem path_attenuates {g : Tree} (wf : WellFormedCDT g)
    {leaf root : CapNode} (path : DerivationPath g leaf root) (hleaf : leaf ∈ g) :
    leaf.authority ⊆ root.authority :=
  path_narrows wf path hleaf

/-! ## A binding / non-vacuity witness — the invariant has teeth. -/

/-- An **amplifying** edge: the child claims a right its parent does not hold. -/
def amplifies (child parent : CapNode) : Prop :=
  ¬ child.authority ⊆ parent.authority

instance (child parent : CapNode) : Decidable (amplifies child parent) := by
  unfold amplifies; exact inferInstance

/-- **`amplifying_rejected` (PROVED)** — the invariant is not vacuous: if a node's parent
resolves in `g` but the edge to it *amplifies* (the child grabs a right the parent lacks),
then `g` is NOT well-formed. A node that does not attenuate its parent is rejected — the ONE
rule has teeth (it can fail, it is not satisfied-by-everything). -/
theorem amplifying_rejected {g : Tree} {n pn : CapNode}
    (hn : n ∈ g) (hpar : n.parent = some pn.self)
    (hlk : g.lookup pn.self = some pn)
    (hamp : amplifies n pn) :
    ¬ WellFormedCDT g := by
  intro wf
  obtain ⟨pn', hlk', hatt⟩ := wf n hn pn.self hpar
  rw [hlk] at hlk'
  cases hlk'
  exact hamp hatt

/-! ## The bridge to `Caveat`: a CDT path IS the biscuit token chain.

The `Authority.Caveat` `Token` is a root + an **append-only attenuation chain of caveats**;
`Token.attenuate` appends one (narrows), and `attenuate_narrows` PROVES the admissible set
can only shrink. That chain is the **biscuit rendering of a CDT path**: each `Token.attenuate`
edge is one CDT `(child → parent)` attenuation edge, viewed on the *admissible-request*
lattice (`Set Ctx` under ⊆) instead of the *rights* lattice (`Finset Auth` under ⊆). One
append-only, monotone-narrowing partial order, two faces. -/

/-- **`chain_renders_path` (PROVED) — the CDT ⟷ biscuit bridge.** A `Token`'s attenuation
chain narrows on EXACTLY the lattice `path_attenuates`/`amplifying_rejected` narrow on (⊆,
fail-closed). We exhibit the correspondence as the shared narrowing law: appending an edge
(`Token.attenuate`, the biscuit face) admits a subset of what the parent admitted —
the same monotone-narrowing edge the CDT's `attenuates` (the rights face) enforces. So the
token chain and a CDT path are one append-only, monotone-attenuation order. -/
theorem chain_renders_path {Ctx Gateway : Type}
    (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate c).admits ctx d = true → tok.admits ctx d = true :=
  attenuate_narrows tok c ctx d

/-- The same correspondence at the set level: the biscuit-chain edge's admissible set is a
**subset** of its parent's — structurally identical to a CDT edge's `attenuates`
(`child.authority ⊆ parent.authority`). Both are ⊆ on a lattice; the chain and the path are
the same append-only narrowing order. **PROVED.** -/
theorem chain_edge_is_subset {Ctx Gateway : Type}
    (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (d : Discharges Gateway) :
    {ctx | (tok.attenuate c).admits ctx d = true} ⊆ {ctx | tok.admits ctx d = true} :=
  attenuate_subset tok c d

/-- And the CDT edge invariant, as a `Subset` on the rights lattice, to make the parallel
literal: a well-formed edge `attenuates child parent` IS `child.authority ⊆ parent.authority`
— the same shape as `chain_edge_is_subset`, on the rights face instead of the request face.
**PROVED** (definitional). -/
theorem cdt_edge_is_subset {child parent : CapNode} (h : attenuates child parent) :
    child.authority ⊆ parent.authority := h

/-! ## It runs (`#eval`) — a CDT root → child → grandchild, each narrowing. -/

/-- The full rights set a root might confer (read/write/grant). -/
def fullRights : Rights := {Auth.read, Auth.write, Auth.grant}

/-- **Root** (hash 0): full authority, no parent — a cell's root-cap mint. -/
def root : CapNode := { self := 0, parent := none, authority := fullRights }

/-- **Child** (hash 1 → 0): drops `grant` (read/write only) — a monotone attenuation. -/
def child : CapNode := { self := 1, parent := some 0, authority := {Auth.read, Auth.write} }

/-- **Grandchild** (hash 2 → 1): drops `write` (read only) — narrows again. -/
def grandchild : CapNode := { self := 2, parent := some 1, authority := {Auth.read} }

/-- A well-formed three-node CDT: root ← child ← grandchild, authority shrinking each step. -/
def goodCDT : Tree := [grandchild, child, root]

/-- An **amplifying** node (hash 3 → 1): claims `grant`, which its parent `child` dropped —
the edge AMPLIFIES, so any CDT containing it (with its parent) is rejected. -/
def amplifier : CapNode := { self := 3, parent := some 1, authority := {Auth.read, Auth.grant} }

/-- A CDT with the amplifying edge spliced in — NOT well-formed. -/
def badCDT : Tree := [amplifier, child, root]

#eval goodCDT.lookup 0 == some root            -- true  (root resolves)
#eval decide (attenuates child root)           -- true  (read/write ⊆ read/write/grant)
#eval decide (attenuates grandchild child)     -- true  (read ⊆ read/write)
#eval decide (attenuates amplifier child)      -- false (grant ∉ child's rights — amplifies!)
#eval decide (amplifies amplifier child)       -- true  (the edge would grow authority)

-- The grandchild's rights are a subset of the root's — the keystone, computed: authority
-- shrank all the way down the derivation chain (read ⊆ read/write/grant).
#eval decide (grandchild.authority ⊆ root.authority)   -- true

/-! ## The demo CDT, PROVED well-formed, and the keystone exercised on a concrete path. -/

/-- **`goodCDT_wellFormed` (PROVED)** — the three-node `root ← child ← grandchild` CDT
satisfies the structural invariant: every non-root node attenuates its resolved parent. The
amplifying `badCDT` could never be proved here (its `child→child`? no — its `amplifier→child`
edge fails ⊆); this shows the invariant *can* be satisfied and is not vacuous. -/
theorem goodCDT_wellFormed : WellFormedCDT goodCDT := by
  intro n hn p hpar
  -- `goodCDT = [grandchild, child, root]`; case on which node `n` is.
  simp only [goodCDT, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · -- grandchild → child: `hpar` pins `p = 1`.
    simp only [grandchild, Option.some.injEq] at hpar; subst hpar
    exact ⟨child, by rfl, by decide⟩
  · -- child → root: `hpar` pins `p = 0`.
    simp only [child, Option.some.injEq] at hpar; subst hpar
    exact ⟨root, by rfl, by decide⟩
  · -- root has no parent: `hpar : none = some p` is impossible.
    simp only [root] at hpar; exact absurd hpar (by simp)

/-- A concrete root-to-leaf derivation path in `goodCDT`: `grandchild ⤳ child ⤳ root`, each
edge present in the store. Witnesses that `path_attenuates` applies to a real traversal. -/
def goodPath : DerivationPath goodCDT grandchild root :=
  .step (mid := child) (by rfl) (by decide)
    (.step (mid := root) (by rfl) (by decide) (.refl root))

/-- **`goodCDT_keystone` (PROVED)** — the keystone on the concrete CDT: descending the real
`grandchild ⤳ child ⤳ root` path, authority shrinks — `grandchild.authority ⊆ root.authority`.
The `#eval` above *computes* the inclusion; this *derives* it from `path_attenuates` (the
inductive shrink law) on a genuine, store-resolved path. -/
theorem goodCDT_keystone : grandchild.authority ⊆ root.authority :=
  path_attenuates goodCDT_wellFormed goodPath (by decide)

/-- **`badCDT_rejected` (PROVED)** — the teeth, on the concrete CDT: `badCDT` (the amplifying
edge spliced in) is NOT well-formed, because `amplifier → child` grabs `grant` the parent
dropped. A node that does not attenuate its parent is rejected. -/
theorem badCDT_rejected : ¬ WellFormedCDT badCDT :=
  amplifying_rejected
    (n := amplifier) (pn := child)
    (by simp [badCDT]) (by rfl) (by decide) (by decide)

end Dregg2.Authority.CDT
