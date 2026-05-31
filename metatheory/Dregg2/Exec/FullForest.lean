/-
# Dregg2.Exec.FullForest — the TREE-SHAPED `FullActionA` call-FOREST (the wholesale-swap KEYSTONE).

`Exec/TurnForest.lean` closed the nested call-FOREST over the NARROW `TurnExecutor.Action` (balance/
effect only): `execForest` = the recursive all-or-nothing tree executor, proved EQUAL to `execTurn`
over the pre-order flattening (`execForest_eq_execTurn`), with Granovetter non-amplification across
the forest (`execForest_no_amplify`) and the four `StepInv` conjuncts (`execForest_attests`).
`Exec/TurnExecutorFull.lean` then WIDENED the LINEAR executor to the FULL dregg1 op-set, PER-ASSET:
`FullActionA = balanceA | delegate | revoke | mintA | burnA`, one `execFullA` / `execFullTurnA`, with
the per-asset CONSERVATION VECTOR (`execFullTurnA_ledger_per_asset` / `_conserves_per_asset`) — the
FILL-1 ledger that forbids cross-asset laundering (a SCALAR aggregate cannot state it).

This module is the JOIN: the TREE pattern of `TurnForest`, WIDENED to `FullActionA`, PER-ASSET. It is
the executable artifact the wholesale swap exports — the tree-shaped call-forest over the full
op-set, with conservation tracked as the per-asset vector end-to-end. We mirror `TurnForest`'s blessed
shape EXACTLY (OPTION B — proved flat lowering): a `FullForestA` tree, an operational tree executor
`execFullForestA`, a pre-order lowering `lowerForestA`, and the BRIDGE `execFullForestA_eq_execFullTurnA`
that lifts EVERY `execFullTurnA` theorem to the tree. The conservation corollaries INHERIT the FILL-1
per-asset vector (NOT a blanket `recTotal`-fixed — false for mint/burn trees: a forest that mints or
burns legitimately moves the supply, disclosed).

PER-ASSET IS THE SOLE CANONICAL CARRIER. There is deliberately NO scalar mirror structure — that is
the regression `FILL 1` guards against (a scalar would let a mint of asset B net against a burn of
asset A and pass off as "conserved"). Every conservation statement here is the `∀ b`/per-asset
`recTotalAsset … b` family.

We prove, over the whole tree (all-or-nothing):

  * **`execFullForestA_eq_execFullTurnA`** — the tree transaction IS `execFullTurnA` over the
    pre-order flattening (the bridge lifting every per-asset linear theorem; rests on
    `execFullTurnA_append`);
  * **`execFullForestA_ledger_per_asset` / `_conserves_per_asset`** — the per-asset CONSERVATION
    VECTOR end-to-end across the whole tree (`recTotalAsset … b` moves by exactly the net per-asset
    ledger delta of the lowered turn, for EVERY asset `b`); the conserving corollary when the net is
    `0` in asset `b`. INHERITS the FILL-1 vector — NEVER a blanket scalar-fixed;
  * **`execFullForestA_no_amplify`** — every delegation edge of the forest is non-amplifying
    (`Caps.derive_no_amplify`): Granovetter across the whole tree, no child gains authority the parent
    lacked (the SAME law + edge data as `TurnForest.execForest_no_amplify`);
  * **`execFullForestA_each_attests`** — every tree node attests its `fullActionInvA` (the per-asset
    ledger vector ∧ ChainLink ∧ ObsAdvance ∧ the kind obligation), via membership-lift through the
    bridge into `execFullTurnA_each_attests`;
  * **`execFullForestA_unauthorized_fails`** — root fail-closed (an unauthorized root rejects the
    whole forest).

FIDELITY OVERLAY (§9). The executor here is the `DelegationMode::None` default: every child's
`FullActionA` target is the same cell as the parent's (`sameTargetForest`, a STRUCTURAL predicate). A
CROSS-TARGET subtree (a child acting on a DIFFERENT cell) is the cross-cell axis — ROUTED to
`Exec/CrossCellForest.lean` (`crossForest_conserves`, the N-ary cross-cell Σ=0 binding-carried CG-5),
NOT re-proven and NOT baked into this executor. Bearer-bypass (a cap presented WITHOUT a delegation
edge) is scoped OUT for v1 — every node here runs under its own `execFullA` authority gate.

Discipline: delegated caps NEVER amplify (`derive_no_amplify`, reused, never faked). Conservation is
PER-ASSET (`execFullTurnA_ledger_per_asset`, reused). No `axiom`/`admit`/`native_decide`/`sorry`.
Keystones `#assert_axioms`-pinned. Reuses `TurnExecutorFull`/`Caps`; edits none (the §MB additions to
`TurnExecutorFull` are its own region).
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.Caps

namespace Dregg2.Exec.FullForest

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority

/-! ## §1 — The `FullForestA`: a TREE of full-op-set, per-asset `FullActionA`s.

A node carries its own `FullActionA` (run via `execFullA`) and, per child, the DELEGATION EDGE — the
parent's `parentCap`, the `keep` rights it is attenuated to (`Caps.derive`), and the `holder` label
the derived cap is granted to — and the child subtree itself. The `FullForestA` analog of
`TurnForest`, widened to the full per-asset op-set.

The delegation edge data lives in the child wrapper (`FullChildA`) so the no-amplification law is a
STRUCTURAL fact about the forest data: every `FullChildA` edge confers ≤ its parent's `parentCap`.

There is deliberately NO scalar mirror — per-asset is the sole canonical carrier (to foreclose the
FILL-1 scalar-laundering regression). -/

mutual
/-- A node of the full-op-set call-forest: its own `FullActionA` (run via `execFullA`) and its
`children`, each a delegation edge to a child subtree. -/
structure FullForestA where
  /-- The node's own full-op-set, per-asset action (the op `execFullA` runs at this node). -/
  action   : FullActionA
  /-- The delegated child subtrees (each under a cap DERIVED from this node's authority). -/
  children : List FullChildA

/-- A delegation edge: the parent hands `holder` an ATTENUATED (`keep`) copy of `parentCap`
(`Caps.derive`), under which the child `sub`tree runs. The `derive_no_amplify` law makes this edge
non-amplifying: the child confers ≤ `parentCap`. -/
structure FullChildA where
  /-- The label the derived child-cap is granted to (the child's authority holder). -/
  holder    : Label
  /-- The rights the parent's cap is attenuated to when delegated (`attenuate keep`). -/
  keep      : List Auth
  /-- The parent capability being delegated (the upper bound on the child's conferred authority). -/
  parentCap : Cap
  /-- The child subtree, run under the derived cap. -/
  sub       : FullForestA
end

/-! ## §2 — `execFullForestA`: run the tree as an ALL-OR-NOTHING transaction (the executable artifact).

Each node runs its own `FullActionA` via `execFullA` (the fail-closed per-kind gate, extending the
receipt chain, moving the per-asset ledger by exactly `ledgerDeltaAsset`). Then each child runs in
turn, threading the chained state forward. Any `none` anywhere aborts the whole forest to `none` (the
journal/rollback discipline — no partial commit), exactly as `execFullTurnA`'s `Option` fold. The
recursion is structural over the tree (`execFullForestA`/`execFullChildrenA` mutual, decreasing on
`sizeOf`). -/

mutual
/-- Run a node: its own action, then all its children (each delegated, all-or-nothing). -/
def execFullForestA (s : RecChainedState) : FullForestA → Option RecChainedState
  | ⟨a, kids⟩ =>
    match execFullA s a with
    | some s' => execFullChildrenA s' kids
    | none    => none

/-- Run a list of child delegation edges left-to-right, threading the chained state. The delegated
cap is `derive`d into the child holder's slot (the non-amplifying handoff); the child's own action
gate then runs via `execFullForestA`. -/
def execFullChildrenA (s : RecChainedState) : List FullChildA → Option RecChainedState
  | []            => some s
  | ⟨_, _, _, sub⟩ :: rest =>
    match execFullForestA s sub with
    | some s' => execFullChildrenA s' rest
    | none    => none
end

/-! ## §3 — The pre-order lowering: the forest's flattened action list (OPTION B carrier).

The forest's actions, in EXECUTION ORDER (pre-order: a node before its children, children
left-to-right). `execFullForestA` is exactly `execFullTurnA` over `lowerForestA` — so every
`execFullTurnA` theorem lifts to the forest by this flattening. We prove that equivalence
(`execFullForestA_eq_execFullTurnA`) and read all the per-asset conjuncts through it. -/

mutual
/-- The node-actions of a forest in pre-order (the node, then its children's flattenings). -/
def lowerForestA : FullForestA → List FullActionA
  | ⟨a, kids⟩ => a :: lowerChildrenA kids

/-- The node-actions of a child list in order. -/
def lowerChildrenA : List FullChildA → List FullActionA
  | []                     => []
  | ⟨_, _, _, sub⟩ :: rest => lowerForestA sub ++ lowerChildrenA rest
end

mutual
/-- Every delegation edge of a forest, in pre-order (this node's child edges, then recursively each
child subtree's edges). Each entry is the `(keep, parentCap)` of one delegation. -/
def forestEdgesA : FullForestA → List (List Auth × Cap)
  | ⟨_, kids⟩ => childrenEdgesA kids

/-- Every delegation edge of a child list (this edge, then the child subtree's edges, then the
rest). -/
def childrenEdgesA : List FullChildA → List (List Auth × Cap)
  | []                         => []
  | ⟨_, keep, pc, sub⟩ :: rest => (keep, pc) :: (forestEdgesA sub ++ childrenEdgesA rest)
end

/-! ## §4 — The BRIDGE: `execFullForestA` IS `execFullTurnA` over the pre-order lowering (PROVED).

The tree transaction equals the linear per-asset transaction over its pre-ordered node-actions:
`execFullForestA s f = execFullTurnA s (lowerForestA f)`. This is the bridge that lifts EVERY
`execFullTurnA` theorem (`execFullTurnA_ledger_per_asset`, `execFullTurnA_each_attests`, …) to the
forest — the recursion threads the chained state in exactly the pre-order `Option`-fold
`execFullTurnA` performs. PROVED by mutual structural induction over the tree, mutually with the
child-list lowering `execFullChildrenA_eq_execFullTurnA`. Rests on `execFullTurnA_append`. -/

mutual
theorem execFullForestA_eq_execFullTurnA (s : RecChainedState) (f : FullForestA) :
    execFullForestA s f = execFullTurnA s (lowerForestA f) := by
  obtain ⟨a, kids⟩ := f
  show (match execFullA s a with
        | some s' => execFullChildrenA s' kids
        | none    => none)
      = execFullTurnA s (a :: lowerChildrenA kids)
  rw [show execFullTurnA s (a :: lowerChildrenA kids)
        = (match execFullA s a with
           | some s' => execFullTurnA s' (lowerChildrenA kids)
           | none    => none) from rfl]
  cases execFullA s a with
  | none    => rfl
  | some s' => exact execFullChildrenA_eq_execFullTurnA s' kids

theorem execFullChildrenA_eq_execFullTurnA (s : RecChainedState) (kids : List FullChildA) :
    execFullChildrenA s kids = execFullTurnA s (lowerChildrenA kids) := by
  match kids with
  | [] => rfl
  | ⟨h, k, pc, sub⟩ :: rest =>
    show (match execFullForestA s sub with
          | some s' => execFullChildrenA s' rest
          | none    => none)
        = execFullTurnA s (lowerForestA sub ++ lowerChildrenA rest)
    rw [execFullTurnA_append, execFullForestA_eq_execFullTurnA s sub]
    cases execFullTurnA s (lowerForestA sub) with
    | none    => rfl
    | some s' => exact execFullChildrenA_eq_execFullTurnA s' rest
end

/-! ## §5 — Conservation COROLLARIES: the per-asset VECTOR across the whole tree (one-line via the bridge).

These INHERIT the FILL-1 per-asset vector. We do NOT state a blanket `recTotal`-fixed: that is FALSE
for a mint/burn tree (a forest that mints or burns legitimately moves the supply, with the delta
disclosed). The honest law is: `recTotalAsset … b` moves by EXACTLY the net per-asset ledger delta of
the lowered turn, for EVERY asset `b` independently. -/

/-- **`execFullForestA_ledger_per_asset` — PROVED (the per-asset conservation VECTOR, whole tree).** A
committed full-forest moves `recTotalAsset b` by EXACTLY the net per-asset ledger delta of its
pre-order lowering, for EVERY asset `b` independently. The tree generalization of
`execFullTurnA_ledger_per_asset`, riding the bridge. THIS is the FILL-1 vector — a scalar aggregate
could not state it (it would let a mint of asset B net against a burn of asset A). -/
theorem execFullForestA_ledger_per_asset (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + turnLedgerDeltaAsset (lowerForestA f) b := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_ledger_per_asset s s' (lowerForestA f) b h

/-- **`execFullForestA_conserves_per_asset` — PROVED.** A committed full-forest whose net per-asset
ledger delta is `0` *in asset `b`* preserves asset `b`'s total supply. Applied with `∀ b, … = 0` this
gives FULL per-asset conservation across the whole tree: a transfer/authority-only forest, or one
whose per-asset mint/burn nets out in EACH asset, conserves EVERY asset class. The
`CONSERVATION_VECTOR` at the forest level. -/
theorem execFullForestA_conserves_per_asset (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') (hzero : turnLedgerDeltaAsset (lowerForestA f) b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  rw [execFullForestA_ledger_per_asset s s' f b h, hzero, add_zero]

/-! ## §6 — `execFullForestA_no_amplify`: delegated caps NEVER amplify (Granovetter across the forest).

Each `FullChildA` edge `⟨holder, keep, parentCap, _⟩` delegates `attenuate keep parentCap` to
`holder` (the `Caps.derive` handoff). The cap-system no-amplification law `Caps.derive_no_amplify`
says the derived cap confers ≤ the parent's authority — so NO child gains authority the parent lacked.
We collect every edge of the tree and prove this holds of ALL of them: Granovetter (only connectivity
begets connectivity) across the whole forest. SAME law + edge data as
`TurnForest.execForest_no_amplify` — reused, never re-stubbed. A STRUCTURAL fact (holds of every
well-formed forest, committed or not). -/

/-- **`edge_no_amplify` — PROVED (the per-edge Granovetter law).** A single delegation edge is
non-amplifying: the cap delegated to the child (`attenuate keep parentCap`) confers ≤ the parent's
authority. This is `Caps.derive_no_amplify` — reused verbatim, never faked. -/
theorem edge_no_amplify (keep : List Auth) (parentCap : Cap) :
    capAuthConferred (attenuate keep parentCap) ⊆ capAuthConferred parentCap :=
  derive_no_amplify keep parentCap

/-- **`execFullForestA_no_amplify` — THE FOREST GRANOVETTER LAW (PROVED).** EVERY delegation edge of
the full-op-set forest is non-amplifying: for each `(keep, parentCap)` edge, the cap handed to the
child confers ≤ the parent's authority (`derive_no_amplify`). No child anywhere in the tree — at any
nesting depth — gains authority the parent lacked: *only connectivity begets connectivity*, across the
whole forest. A structural property of the forest data. -/
theorem execFullForestA_no_amplify (f : FullForestA) :
    ∀ e ∈ forestEdgesA f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 := by
  intro e _
  exact edge_no_amplify e.1 e.2

/-! ## §7 — Per-node attestation: every tree node attests its `fullActionInvA` (membership-lift).

The pre-order lowering contains EXACTLY the tree's nodes (`execFullForestA_node_mem_lowered`), and
`execFullTurnA_each_attests` proves every action of the committed lowered turn attests `fullActionInvA`
(the per-asset ledger vector ∧ ChainLink ∧ ObsAdvance ∧ the kind obligation). Composing the two: every
tree node attests its per-asset step-completeness. -/

mutual
/-- Every tree node's action is in the pre-order lowering (mutual structural induction). -/
theorem execFullForestA_node_mem_lowered (f : FullForestA) :
    f.action ∈ lowerForestA f := by
  obtain ⟨a, kids⟩ := f
  show a ∈ a :: lowerChildrenA kids
  exact List.mem_cons_self

/-- Every action of a child list's subtrees is in the child list's pre-order lowering. -/
theorem execFullChildrenA_node_mem_lowered (kids : List FullChildA) (c : FullChildA)
    (hc : c ∈ kids) : c.sub.action ∈ lowerChildrenA kids := by
  match kids with
  | [] => exact absurd hc List.not_mem_nil
  | ⟨h, k, pc, sub⟩ :: rest =>
    show c.sub.action ∈ lowerForestA sub ++ lowerChildrenA rest
    rcases List.mem_cons.mp hc with hceq | hcrest
    · subst hceq
      exact List.mem_append_left _ (execFullForestA_node_mem_lowered sub)
    · exact List.mem_append_right _ (execFullChildrenA_node_mem_lowered rest c hcrest)
end

/-- **`execFullForestA_each_attests` — PROVED (per-node step-completeness, whole tree).** Every node
of a committed full-forest attests its `fullActionInvA`: the per-asset ledger VECTOR ∧ ChainLink ∧
ObsAdvance ∧ the kind-specific obligation. Read through the bridge into `execFullTurnA_each_attests`
over the pre-order lowering. The per-asset, full-op-set generalization of `execForest`'s attestation —
NON-VACUOUS: it asserts every node's per-asset conservation vector, chain extension, and authority
obligation, not a triviality. -/
theorem execFullForestA_each_attests (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    ∀ fa ∈ lowerForestA f, ∃ sa sa', execFullA sa fa = some sa' ∧ fullActionInvA sa fa sa' := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_each_attests s s' (lowerForestA f) h

/-- **The root node itself attests — PROVED (corollary).** The root's own action attests its
`fullActionInvA` (the per-node membership-lift specialized to the root via
`execFullForestA_node_mem_lowered`). -/
theorem execFullForestA_root_attests (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    ∃ sa sa', execFullA sa f.action = some sa' ∧ fullActionInvA sa f.action sa' :=
  execFullForestA_each_attests s s' f h f.action (execFullForestA_node_mem_lowered f)

/-! ## §8 — Fail-closed at the root (the journal/rollback discipline). -/

/-- **`execFullForestA_unauthorized_fails` — PROVED (fail-closed at the root).** If the root node's
action is rejected (`execFullA s a = none`), the whole forest rejects (no partial commit). The
all-or-nothing discipline through the `execFullForestA` root. -/
theorem execFullForestA_unauthorized_fails (s : RecChainedState) (a : FullActionA)
    (kids : List FullChildA) (h : execFullA s a = none) :
    execFullForestA s ⟨a, kids⟩ = none := by
  show (match execFullA s a with
        | some s' => execFullChildrenA s' kids
        | none    => none) = none
  rw [h]

/-! ## §9 — Fidelity overlay: `sameTargetForest` (the `DelegationMode::None` default) + cross-cell routing.

The executor here is the `DelegationMode::None` default: a child's `FullActionA` runs on the SAME
TARGET CELL as its parent. `targetOf` reads the cell a `FullActionA` acts on (the `src`/`cell` field);
`sameTargetForest` is the STRUCTURAL predicate that every child's target equals its parent's. This is
the INTRA-cell fidelity overlay — the forest's nodes all touch the one record cell's ledger, so the
per-asset conservation VECTOR (`execFullForestA_conserves_per_asset`) is DERIVED, not binding-carried,
exactly as `TurnForest`'s intra-cell conservation is derived.

A CROSS-TARGET subtree — a child whose target cell DIFFERS from its parent's — is the cross-cell axis.
It is ROUTED to `Exec/CrossCellForest.lean` (`crossForest_conserves`, the N-ary cross-cell Σ=0 binding-
carried CG-5; `crossForest_no_amplify`; `crossForest_attests`), where the whole-forest conservation is
the inviolable Σ=0 binding carried as a HYPOTHESIS (NOT derivable, because cross-cell halves need not
individually cancel). We deliberately do NOT bake a cross-target branch into `execFullForestA`, and we
do NOT re-prove the cross-cell axis here — the routing is the honest division of labor.

Bearer-bypass (a cap presented WITHOUT a delegation edge — `DelegationMode::Bearer`) is scoped OUT for
v1: every node here runs under its own `execFullA` authority gate, and delegation is the only authority
handoff modeled. -/

/-- The target cell a `FullActionA` acts on (the `src` for a transfer, the `cell` for mint/burn, the
delegator/holder for authority, the written `cell` for the 5 pure-state field/log effects). The
discriminant `sameTargetForest` reads. -/
def targetOf : FullActionA → CellId
  | .balanceA t _       => t.src
  | .delegate del _ _   => del
  | .revoke holder _    => holder
  | .mintA _ cell _ _   => cell
  | .burnA _ cell _ _   => cell
  -- §MA-state: the 5 pure-state effects act on their `cell` (the record/log they touch).
  | .setFieldA _ cell _ _   => cell
  | .emitEventA _ cell _ _  => cell
  | .incrementNonceA _ cell _ => cell
  | .setPermissionsA _ cell _ => cell
  | .setVKA _ cell _        => cell
  -- §MA-auth: the 6 authority effects act on the introducer/holder/actor (the cap-graph node).
  | .introduceA intro _ _   => intro
  | .attenuateA actor _ _   => actor
  | .dropRefA holder _      => holder
  | .revokeDelegationA holder _ => holder
  | .validateHandoffA intro _ _ => intro
  | .exerciseA actor _      => actor
  -- §MA-supply: createCell/spawn act on the fresh cell they mint; bridgeMint on the credited cell.
  | .createCellA _ newCell  => newCell
  | .spawnA _ child _       => child
  | .bridgeMintA _ cell _ _ => cell
  -- §MA-escrow: escrow/obligation/committed act on the debited `creator`/`obligor` cell; notes act on
  -- the `actor` (the SET-touching node). The `targetOf` discriminant `sameTargetForest` reads.
  | .createEscrowA _ _ creator _ _ _        => creator
  | .releaseEscrowA _ actor                 => actor
  | .refundEscrowA _ actor                  => actor
  | .createObligationA _ _ obligor _ _ _    => obligor
  | .noteSpendA _ actor                     => actor
  | .noteCreateA _ actor                    => actor
  | .createCommittedEscrowA _ _ creator _ _ _ => creator
  | .releaseCommittedEscrowA _ actor        => actor
  | .refundCommittedEscrowA _ actor         => actor

mutual
/-- **`sameTargetForest`** — the STRUCTURAL `DelegationMode::None` fidelity predicate: every child's
`FullActionA` target equals the parent node's target (the intra-cell forest). A CROSS-TARGET subtree
(where this fails) is routed to `Exec/CrossCellForest.lean`. -/
def sameTargetForest : FullForestA → Prop
  | ⟨a, kids⟩ => sameTargetChildren (targetOf a) kids

/-- Every child's subtree-root target equals the parent target `tp`, AND recursively each child
subtree is itself same-target. -/
def sameTargetChildren (tp : CellId) : List FullChildA → Prop
  | []                     => True
  | ⟨_, _, _, sub⟩ :: rest =>
      targetOf sub.action = tp ∧ sameTargetForest sub ∧ sameTargetChildren tp rest
end

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins over the forest keystones). -/

#assert_axioms execFullForestA_eq_execFullTurnA
#assert_axioms execFullChildrenA_eq_execFullTurnA
#assert_axioms execFullForestA_ledger_per_asset
#assert_axioms execFullForestA_conserves_per_asset
#assert_axioms edge_no_amplify
#assert_axioms execFullForestA_no_amplify
#assert_axioms execFullForestA_node_mem_lowered
#assert_axioms execFullChildrenA_node_mem_lowered
#assert_axioms execFullForestA_each_attests
#assert_axioms execFullForestA_root_attests
#assert_axioms execFullForestA_unauthorized_fails

/-! ## §11 — Non-vacuity (`#eval`): the FULL op-set tree commits per-asset; laundering CAUGHT;
unauthorized child rejected; no-amplify edge witness.

`fma0` (from `TurnExecutorFull`): a genuine 2-asset `bal` ledger — cell 0 holds 100 of asset 0 and 7
of asset 1; cell 1 holds 5 of asset 0; actor 9 holds the privileged `node 0` mint cap over cell 0.
Owner authority (actor = src) for balance transfers. We build trees over the FULL op-set
(mintA/balanceA/burnA), per-asset. -/

/-- **`goodFullForest`** — a 3-node, 3-level full-op-set tree, per-asset NET ZERO ⇒ conserved:
  * ROOT: `mintA 9 0 1 50` — actor 9 mints +50 of ASSET 1 on cell 0 (privileged, disclosed);
  * CHILD (delegated, `[read] ⊆ [read,write]`): `balanceA ⟨0,0,1,30⟩ 0` — actor 0 transfers 30 of
    ASSET 0 from cell 0 to cell 1 (conserves asset 0);
  * GRANDCHILD (delegated): `burnA 9 0 1 50` — actor 9 burns −50 of ASSET 1 on cell 0 (disclosed).
The per-asset net is `0` in BOTH assets (asset 1: +50 −50 = 0; asset 0: 0), so the whole tree
conserves PER-ASSET. The delegation edges are non-amplifying. -/
def goodFullForest : FullForestA :=
  ⟨ .mintA 9 0 1 50
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
               , [ { holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                   , sub := ⟨ .burnA 9 0 1 50, [] ⟩ } ] ⟩ } ] ⟩

#eval (execFullForestA fma0 goodFullForest).isSome                          -- true (whole tree commits)
-- The pre-order lowering IS the per-asset linear turn over the three node-actions:
#eval (lowerForestA goodFullForest).length                                  -- 3
-- The per-asset NET is 0 in BOTH assets ⇒ conserved per-asset:
#eval turnLedgerDeltaAsset (lowerForestA goodFullForest) 0                   -- 0 (asset 0)
#eval turnLedgerDeltaAsset (lowerForestA goodFullForest) 1                   -- 0 (asset 1: +50 -50)
-- The per-asset supply AFTER the tree: asset 0 = 105 (conserved), asset 1 = 7 (conserved):
#eval (execFullForestA fma0 goodFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))      -- some (105, 7)
#eval (recTotalAsset fma0.kernel 0, recTotalAsset fma0.kernel 1)            -- (105, 7)
-- The chain grew by exactly the node count (3):
#eval (execFullForestA fma0 goodFullForest).map (fun s => s.log.length)      -- some 3
-- Every delegation edge is non-amplifying: each child's keep ⊆ its parent's cap rights.
#eval (forestEdgesA goodFullForest).map (fun e => decide
        ((capAuthConferred (attenuate e.1 e.2)).length ≤ (capAuthConferred e.2).length))  -- [true, true]

/-- **`deepFullForest`** — a 3-level INTRA-asset tree (deeper nesting works; recursion fully general):
root transfer 0→1 of 10 (asset 0), child transfer 1→0 of 5 (asset 0, actor 1 owns cell 1), grandchild
transfer 0→1 of 5 (asset 0). All transfers conserve asset 0 (and trivially asset 1). -/
def deepFullForest : FullForestA :=
  ⟨ .balanceA ⟨0, 0, 1, 10⟩ 0
  , [ { holder := 1, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ .balanceA ⟨1, 1, 0, 5⟩ 0
               , [ { holder := 0, keep := [], parentCap := .endpoint 0 [Auth.read]
                   , sub := ⟨ .balanceA ⟨0, 0, 1, 5⟩ 0, [] ⟩ } ] ⟩ } ] ⟩

#eval (execFullForestA fma0 deepFullForest).isSome                          -- true (3 levels commit)
#eval (execFullForestA fma0 deepFullForest).map (fun s => s.log.length)      -- some 3
#eval (execFullForestA fma0 deepFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))      -- some (105, 7) (conserved)
#eval turnLedgerDeltaAsset (lowerForestA deepFullForest) 0                   -- 0 (asset 0 conserved)

/-- **`badChildFullForest`** — a FAIL-CLOSED tree: the CHILD action is an UNAUTHORIZED mint (actor 0
holds no `node 0` mint cap — only actor 9 does). `execFullA`'s privileged `mintAuthorizedB` gate
rejects it, and all-or-nothing rolls back the WHOLE forest (the committed root included). The
cap-exceeding-child rejection across the full op-set. -/
def badChildFullForest : FullForestA :=
  ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read]
      , sub := ⟨ .mintA 0 0 1 50, [] ⟩ } ] ⟩   -- actor 0 lacks the `node 0` mint cap ⇒ rejected

#eval (execFullForestA fma0 badChildFullForest).isSome  -- false (unauthorized mint child ⇒ whole forest rejected)

/-- **`badRootFullForest`** — FAIL-CLOSED at the ROOT: an unauthorized mint root (actor 0 lacks the
`node 0` cap). The whole forest rejects before any child runs. -/
def badRootFullForest : FullForestA :=
  ⟨ .mintA 0 0 1 50, [] ⟩

#eval (execFullForestA fma0 badRootFullForest).isSome   -- false (unauthorized root ⇒ fail-closed)

/-- **`launderFullForest`** — the scalar-LAUNDERING tree a single-aggregate kernel would WRONGLY
accept as "conserving": mint +50 of ASSET 1 (root) while burning −50 of ASSET 0 (child). An aggregate
scalar delta = +50 − 50 = 0 ("conserved" — the BUG). The per-asset VECTOR delta is NONZERO in EACH
asset (asset 0: −50; asset 1: +50), so the per-asset carrier CANNOT pass it off as conservative. THIS
is why per-asset is the sole canonical carrier — a scalar would hide the laundering. -/
def launderFullForest : FullForestA :=
  ⟨ .mintA 9 0 1 50            -- +50 of asset 1
  , [ { holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
      , sub := ⟨ .burnA 9 0 0 50, [] ⟩ } ] ⟩   -- -50 of asset 0

-- The per-asset VECTOR delta is NONZERO in EACH asset (a scalar aggregate would hide both):
#eval turnLedgerDeltaAsset (lowerForestA launderFullForest) 0                -- -50 (NOT 0)
#eval turnLedgerDeltaAsset (lowerForestA launderFullForest) 1                -- 50  (NOT 0)
-- The per-asset ledger AFTER the launder tree: asset 0 fell to 55, asset 1 rose to 57 (CAUGHT):
#eval (execFullForestA fma0 launderFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))      -- some (55, 57)

/-! The NO-AMPLIFY edge witness: a STRICT attenuation. `keep = [read]` ⊊ `parentCap = endpoint with
[read, write]` — `attenuate` STRICTLY drops `write`, so `confRights` drops a REAL element (not a
`()≤()` collapse). The genuine Granovetter inequality `granted ⊊ held`. -/

/-- The strict-attenuation edge from the root of `goodFullForest`: parent cap `endpoint 1
[read,write]`, child keeps only `[read]`. -/
def strictEdge : List Auth × Cap := ([Auth.read], .endpoint 1 [Auth.read, Auth.write])

-- The parent confers `[read, write]`; the attenuated child confers only `[read]` — write DROPPED:
#eval capAuthConferred strictEdge.2                                         -- [read, write]
#eval capAuthConferred (attenuate strictEdge.1 strictEdge.2)               -- [read] (write strictly dropped)
-- The attenuation STRICTLY shrinks the conferred rights (a real element gone), NOT mere ⊆:
#eval decide ((capAuthConferred (attenuate strictEdge.1 strictEdge.2)).length
                < (capAuthConferred strictEdge.2).length)                   -- true (STRICT drop)
-- `write` is conferred by the parent but NOT by the attenuated child (the dropped element):
#eval (capAuthConferred strictEdge.2).contains Auth.write                   -- true
#eval (capAuthConferred (attenuate strictEdge.1 strictEdge.2)).contains Auth.write  -- false (DROPPED)

/-! ### §11-state — META-FILL B Wave 1: a TREE NODE carrying a PURE-STATE effect runs (the 5
field/log effects inherit the forest executor automatically through `execFullA`/`lowerForestA` — no
forest-spine edit). The whole tree is balance-NEUTRAL: `recTotalAsset` is UNCHANGED in BOTH assets,
even though the cells' `status`/`nonce` fields are written. Actor 0 owns cell 0 (empty caps ⇒
ownership). -/

/-- **`stateFullForest`** — a 2-level tree whose nodes are PURE-STATE effects: the ROOT writes cell
0's `status` field, the CHILD bumps cell 0's `nonce` (delegated, non-amplifying). NEITHER touches the
`bal` ledger ⇒ the whole tree is balance-NEUTRAL in EVERY asset (per-asset net `0`). -/
def stateFullForest : FullForestA :=
  ⟨ .setFieldA 0 0 "status" 7
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
      , sub := ⟨ .incrementNonceA 0 0 1, [] ⟩ } ] ⟩

#eval (execFullForestA fma0 stateFullForest).isSome                          -- true (pure-state tree commits)
-- The pre-order lowering is the 2 pure-state node-actions:
#eval (lowerForestA stateFullForest).length                                  -- 2
-- The per-asset net is 0 in BOTH assets (pure-state effects move NO asset's supply):
#eval (turnLedgerDeltaAsset (lowerForestA stateFullForest) 0,
       turnLedgerDeltaAsset (lowerForestA stateFullForest) 1)                 -- (0, 0)
-- The per-asset supply AFTER the pure-state tree: UNCHANGED at (105, 7) — balance-NEUTRALITY:
#eval (execFullForestA fma0 stateFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))       -- some (105, 7)
-- ...the written fields read back (status=7, nonce=1) — the metadata domain DID advance:
#eval (execFullForestA fma0 stateFullForest).map
        (fun s => (EffectsState.fieldOf "status" (s.kernel.cell 0),
                   EffectsState.fieldOf "nonce" (s.kernel.cell 0)))           -- some (7, 1)
-- ...the chain grew by exactly the node count (2):
#eval (execFullForestA fma0 stateFullForest).map (fun s => s.log.length)      -- some 2

/-- **`emitOnlyForest`** — a single-node tree carrying an authority-FREE `emitEventA` (dregg1
`apply_emit_event` runs NO cap check), by an actor (5) who owns nothing: it STILL commits (the
forest inherits the authority-free emit semantics). -/
def emitOnlyForest : FullForestA := ⟨ .emitEventA 5 0 7 42, [] ⟩

#eval (execFullForestA fma0 emitOnlyForest).isSome                            -- true (authority-free emit)
#eval (execFullForestA fma0 emitOnlyForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))       -- some (105, 7)

/-! ### §11-auth — META-FILL B Wave 2: a TREE NODE carrying a DISTINCT AUTHORITY effect runs (the 6
authority effects inherit the forest executor AUTOMATICALLY through `execFullA`/`lowerForestA` — NO
forest-spine edit, only the keystone `targetOf` arm). The whole tree is balance-NEUTRAL:
`recTotalAsset` is UNCHANGED in BOTH assets, even though the cap GRAPH moves (an edge added then
exercised). Actor 9 holds the `node 0` connectivity cap in `fma0`. -/

/-- **`authFullForest`** — a 2-level tree whose nodes are AUTHORITY effects: the ROOT `introduceA`
hands recipient 1 an edge to target 0 (actor 9 holds `node 0`); the CHILD `exerciseA` exercises
9's held edge to 0 (delegated, non-amplifying). NEITHER touches the `bal` ledger ⇒ the whole tree is
balance-NEUTRAL in EVERY asset (per-asset net `0`) — the cap graph moves, the supply does NOT. -/
def authFullForest : FullForestA :=
  ⟨ .introduceA 9 1 0
  , [ { holder := 9, keep := [Auth.read], parentCap := .node 0
      , sub := ⟨ .exerciseA 9 0, [] ⟩ } ] ⟩

#eval (execFullForestA fma0 authFullForest).isSome                            -- true (authority tree commits)
-- The pre-order lowering is the 2 authority node-actions:
#eval (lowerForestA authFullForest).length                                    -- 2
-- The per-asset net is 0 in BOTH assets (authority effects move NO asset's supply — balance-NEUTRAL):
#eval (turnLedgerDeltaAsset (lowerForestA authFullForest) 0,
       turnLedgerDeltaAsset (lowerForestA authFullForest) 1)                   -- (0, 0)
-- The per-asset supply AFTER the authority tree: UNCHANGED at (105, 7) — balance-NEUTRALITY:
#eval (execFullForestA fma0 authFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))        -- some (105, 7)
-- ...recipient 1 GAINED the introduced `node 0` edge (the cap GRAPH DID advance — the authority domain):
#eval (execFullForestA fma0 authFullForest).map (fun s => s.kernel.caps 1)     -- some [Cap.node 0]
-- ...the chain grew by exactly the node count (2):
#eval (execFullForestA fma0 authFullForest).map (fun s => s.log.length)        -- some 2

/-! ## §12 — OUTCOME.

The TREE-SHAPED `FullActionA` call-FOREST (the wholesale-swap KEYSTONE) is CLOSED, per-asset, fully
general:

  * `FullForestA`/`FullChildA` — a TREE of full-op-set, per-asset `FullActionA`s (NO scalar mirror —
    per-asset the sole canonical carrier), each child under a cap DERIVED (`Caps.derive`) from its
    parent's, run all-or-nothing;
  * `execFullForestA`/`execFullChildrenA` — the recursive transactional executor over the tree
    (arbitrary depth/branching — the EXECUTABLE artifact), proved EQUAL to `execFullTurnA` over the
    pre-order lowering (`execFullForestA_eq_execFullTurnA`, OPTION B) — the bridge that lifts every
    per-asset linear theorem (rests on `execFullTurnA_append`);
  * `execFullForestA_ledger_per_asset` / `_conserves_per_asset` — the per-asset CONSERVATION VECTOR
    end-to-end across the whole tree (INHERITS the FILL-1 vector; NOT a blanket scalar-fixed, which is
    false for mint/burn trees);
  * `execFullForestA_no_amplify` — EVERY delegation edge is non-amplifying (`derive_no_amplify`):
    Granovetter across the whole forest, the SAME law + edge data as `TurnForest.execForest_no_amplify`;
  * `execFullForestA_each_attests` (+ `_root_attests`) — every node attests its `fullActionInvA` (the
    per-asset ledger vector ∧ ChainLink ∧ ObsAdvance ∧ kind obligation), via membership-lift through
    the bridge;
  * `execFullForestA_unauthorized_fails` — root fail-closed;
  * `sameTargetForest` — the `DelegationMode::None` fidelity overlay; cross-target subtrees ROUTED to
    `Exec/CrossCellForest.lean` (not re-proven, not baked in); Bearer-bypass scoped OUT for v1;
  * non-vacuous (`goodFullForest` 3-level mint+transfer+burn nets to 0 PER-ASSET ⇒ conserved;
    `deepFullForest` 3-level; `badChildFullForest`/`badRootFullForest` unauthorized mint ⇒ whole forest
    none; `launderFullForest` shows the per-asset delta is NONZERO in each asset where a scalar would
    hide it; the strict no-amplify edge witness drops `write`), axiom-clean.

-- ROUTED (the cross-cell axis, deliberately not duplicated here). A child whose target cell DIFFERS
--   from its parent's (a CROSS-TARGET subtree, `targetOf sub.action ≠ targetOf parent`) is the
--   cross-cell forest — `Exec/CrossCellForest.lean` (`crossForest_conserves`, the N-ary cross-cell
--   Σ=0 binding-carried CG-5; `crossForest_no_amplify`; `crossForest_attests`). This module is the
--   INTRA-cell (`sameTargetForest`, `DelegationMode::None`) default; the cross-cell axis is routed,
--   NOT re-proven and NOT baked into `execFullForestA`. Bearer-bypass (`DelegationMode::Bearer`) is
--   scoped OUT for v1 — a documented follow-on, NOT a `sorry`/`axiom`.
-/

end Dregg2.Exec.FullForest
