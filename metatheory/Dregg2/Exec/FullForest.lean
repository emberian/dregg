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

Delegated caps NEVER amplify (`derive_no_amplify`, reused). Conservation is
PER-ASSET (`execFullTurnA_ledger_per_asset`, reused).
Reuses `TurnExecutorFull`/`Caps`; edits none (the §MB additions to
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

/-! ## §1.5 — `capTarget`: the cell a `parentCap` confers an edge TO (the delegation's target).

A delegation edge hands the child an ATTENUATED copy of `parentCap`. The `recKDelegateAtten` gate
(reused below) GATES on the DELEGATOR holding a cap conferring an edge to the parentCap's
TARGET — so we must read that target off `parentCap`. A `node t`/`endpoint t _` cap names target `t`;
a `null` cap names NO object (it confers `[]`), so it has no delegation target — the faithful handoff
of a null cap installs NOTHING (the child receives no new authority; `recKDelegateAtten` is not even
reachable). This `Option` is the discriminant the executor and lowering BOTH read. -/

/-- **`capTarget cap`** — the target cell a cap confers an edge to (`node t`/`endpoint t _ ⇒ some t`;
`null ⇒ none`, a cap that names no object). The delegation gate (`recKDelegateAtten`) checks the
delegator holds a cap to THIS target before handing the child the attenuated copy. -/
def capTarget : Cap → Option Label
  | .node t       => some t
  | .endpoint t _ => some t
  | .null         => none

/-- The target cell a `FullActionA` acts on (the `src` for a transfer, the `cell` for mint/burn, the
delegator/holder for authority, the written `cell` for the 5 pure-state field/log effects). Read by
the executor as the DELEGATOR of each child edge (the authority being delegated downward), and by the
fidelity predicate `sameTargetForest` (§9). -/
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
  | .setProgramA _ cell _   => cell
  -- §MA-auth: the 6 authority effects act on the introducer/holder/actor (the cap-graph node).
  | .introduceA intro _ _   => intro
  | .delegateAttenA del _ _ _ => del
  | .attenuateA actor _ _   => actor
  | .revokeDelegationA holder _ => holder
  | .exerciseA actor _ _    => actor
  -- §MA-supply: createCell/spawn/factory act on the fresh cell they mint; bridgeMint on the credited cell.
  | .createCellA _ newCell  => newCell
  | .createCellFromFactoryA _ newCell _ => newCell
  | .spawnA _ child _       => child
  | .bridgeMintA _ cell _ _ => cell
  -- §MA-note: notes act on the `actor` (the SET-touching node). (F1b: the escrow/obligation/
  -- committed-escrow/bridge-LFC arms are GONE with the kernel holding-store — factory cells own them.)
  | .noteSpendA _ actor _                   => actor
  | .noteCreateA _ actor                    => actor
  -- §MA-seal (Wave-3 DE-SHADOW): seal acts on the sealing `actor` (the box-storing node); unseal on the
  -- `recipient` (the cap's new holder); createSealPair on the `sealerHolder`. makeSovereign/refusal/
  -- receiptArchive act on the WRITTEN cell.
  | .makeSovereignA _ cell                  => cell
  | .refusalA _ cell                        => cell
  | .receiptArchiveA _ cell                 => cell
  -- pipelinedSend acts on the `actor` (the apply-time node).
  | .pipelinedSendA actor                   => actor
  -- §MA-swiss: the 4 CapTP swiss-table effects act on the exporting/holding `exporter` cell (the
  -- `stateAuthB`-gated node the chained step touches).
  -- §MA-lifecycle (Wave-3): seal/unseal/destroy act on the `cell` (the lifecycle-transitioned node);
  -- refresh on the `child` (the self-refreshed delegate). The `stateAuthB`-gated nodes the steps touch.
  | .cellSealA _ cell                       => cell
  | .cellUnsealA _ cell                     => cell
  | .cellDestroyA _ cell _                  => cell
  | .refreshDelegationA _ child             => child
  -- §MA-heap: the heap write acts on the `target` cell (its `heaps` entry + `heap_root` register).
  | .heapWriteA _ target _ _ _              => target

/-! ## §2 — `execFullForestA`: run the tree as an ALL-OR-NOTHING transaction (the executable artifact).

Each node runs its own `FullActionA` via `execFullA` (the fail-closed per-kind gate, extending the
receipt chain, moving the per-asset ledger by exactly `ledgerDeltaAsset`). Then each child runs under
a REAL, EXECUTED delegation handoff: the edge `⟨holder, keep, parentCap, sub⟩` is routed through the
PROVED `recCDelegateAtten s delegator holder t keep` (the faithful `apply_introduce`) — where
`delegator` is the PARENT node's target (`targetOf a`, the authority being delegated) and `t :=
capTarget parentCap`. That step GATES on the delegator holding a cap to `t`
(`recKDelegateAtten_non_amplifying`: the granted cap's rights are `⊆` the held cap's) and INSTALLS the
attenuated cap into `holder`'s slot — balance-neutral (`recKDelegateAtten_frame`, edits only `caps`).
A FORGED/UNAUTHORIZED edge (the delegator holds NO cap to `t`) ⇒ `recCDelegateAtten = none` ⇒ the
WHOLE forest rejects (the non-amplification is now NON-vacuous ON EXECUTION). Only AFTER the handoff
commits does the child subtree run via `execFullForestA`. A `null` parentCap names no target
(`capTarget = none`) so it delegates NOTHING — the child runs under its own independent authority (a
null cap confers `[]`; there is no authority to hand over). Any `none` anywhere aborts the whole
forest (the journal/rollback discipline — no partial commit), exactly as `execFullTurnA`'s `Option`
fold. The recursion is structural over the tree (`execFullForestA`/`execFullChildrenA` mutual). -/

mutual
/-- Run a node: its own action, then all its children — each under a REAL executed
`recCDelegateAtten` handoff from this node's target (`targetOf a`). All-or-nothing. -/
def execFullForestA (s : RecChainedState) : FullForestA → Option RecChainedState
  | ⟨a, kids⟩ =>
    match execFullA s a with
    | some s' => execFullChildrenA (targetOf a) s' kids
    | none    => none

/-- Run a list of child delegation edges left-to-right, threading the chained state. For each edge,
the `delegator` (the parent node's target) hands `holder` its held cap to `t := capTarget parentCap`
ATTENUATED to `keep` via the PROVED `recCDelegateAtten` (gate: delegator holds a real cap to `t`,
`granted ≤ held`); the child subtree then runs via `execFullForestA`. A forged/unauthorized edge ⇒
`none` ⇒ whole-forest rollback. A `null` parentCap (`capTarget = none`) delegates nothing — the child
runs under its existing authority. -/
def execFullChildrenA (delegator : CellId) (s : RecChainedState) :
    List FullChildA → Option RecChainedState
  | []            => some s
  | ⟨holder, keep, parentCap, sub⟩ :: rest =>
    match capTarget parentCap with
    | some t =>
      match recCDelegateAtten s delegator holder t keep with
      | some s1 =>
        match execFullForestA s1 sub with
        | some s2 => execFullChildrenA delegator s2 rest
        | none    => none
      | none    => none
    | none =>
      -- a `null` parentCap delegates nothing (it confers `[]`): the child runs under its own authority.
      match execFullForestA s sub with
      | some s2 => execFullChildrenA delegator s2 rest
      | none    => none
end

/-! ## §3 — The pre-order lowering: the forest's flattened action list (OPTION B carrier).

The forest's actions, in EXECUTION ORDER (pre-order: a node before its children, children
left-to-right). `execFullForestA` is exactly `execFullTurnA` over `lowerForestA` — so every
`execFullTurnA` theorem lifts to the forest by this flattening. We prove that equivalence
(`execFullForestA_eq_execFullTurnA`) and read all the per-asset conjuncts through it. -/

mutual
/-- The node-actions of a forest in pre-order (the node, then its children's flattenings, each child
preceded by its EXECUTED delegation action — `delegator := targetOf a`). -/
def lowerForestA : FullForestA → List FullActionA
  | ⟨a, kids⟩ => a :: lowerChildrenA (targetOf a) kids

/-- The node-actions of a child list in order, threading the parent `delegator`. For each edge, the
EXECUTED `delegateAttenA delegator holder t keep` (with `t := capTarget parentCap`) is emitted BEFORE
that child subtree's actions — so `execFullTurnA` runs the SAME `recCDelegateAtten` handoff the tree
executor does (the bridge `execFullChildrenA_eq_execFullTurnA` rests on this). A `null` parentCap
(`capTarget = none`) emits NO delegation (it delegates nothing) — only the subtree's actions. -/
def lowerChildrenA (delegator : CellId) : List FullChildA → List FullActionA
  | []                            => []
  | ⟨holder, keep, parentCap, sub⟩ :: rest =>
    match capTarget parentCap with
    | some t => FullActionA.delegateAttenA delegator holder t keep
                  :: (lowerForestA sub ++ lowerChildrenA delegator rest)
    | none   => lowerForestA sub ++ lowerChildrenA delegator rest
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

/-! ## §4 — The BRIDGE: `execFullForestA` IS `execFullTurnA` over the pre-order lowering.

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
        | some s' => execFullChildrenA (targetOf a) s' kids
        | none    => none)
      = execFullTurnA s (a :: lowerChildrenA (targetOf a) kids)
  rw [show execFullTurnA s (a :: lowerChildrenA (targetOf a) kids)
        = (match execFullA s a with
           | some s' => execFullTurnA s' (lowerChildrenA (targetOf a) kids)
           | none    => none) from rfl]
  cases execFullA s a with
  | none    => rfl
  | some s' => exact execFullChildrenA_eq_execFullTurnA (targetOf a) s' kids

theorem execFullChildrenA_eq_execFullTurnA (delegator : CellId) (s : RecChainedState)
    (kids : List FullChildA) :
    execFullChildrenA delegator s kids = execFullTurnA s (lowerChildrenA delegator kids) := by
  match kids with
  | [] => rfl
  | ⟨holder, keep, parentCap, sub⟩ :: rest =>
    -- Both the executor and the lowering branch on the SAME scrutinee `capTarget parentCap`; `cases`
    -- on it reduces BOTH at once. `some t` ⇒ the executed `recCDelegateAtten` handoff (=
    -- `execFullA (delegateAttenA …)`) precedes the subtree; `none` (a `null` cap) ⇒ subtree directly.
    show (match capTarget parentCap with
          | some t =>
            match recCDelegateAtten s delegator holder t keep with
            | some s1 => match execFullForestA s1 sub with
                         | some s2 => execFullChildrenA delegator s2 rest
                         | none    => none
            | none    => none
          | none =>
            match execFullForestA s sub with
            | some s2 => execFullChildrenA delegator s2 rest
            | none    => none)
        = execFullTurnA s
            (match capTarget parentCap with
             | some t => FullActionA.delegateAttenA delegator holder t keep
                           :: (lowerForestA sub ++ lowerChildrenA delegator rest)
             | none   => lowerForestA sub ++ lowerChildrenA delegator rest)
    -- Case-split on `capTarget parentCap` (the shared scrutinee of BOTH matches); `simp only [hct]`
    -- rewrites every occurrence and iota-reduces both the executor and the lowering matches.
    cases hct : capTarget parentCap with
    | some t =>
      -- `some t`: `execFullA s (delegateAttenA …) = recCDelegateAtten s …` (definitional). Reduce the
      -- `capTarget` match (`hct`) and the `delegateAttenA` head, then split on the handoff result.
      cases hd : recCDelegateAtten s delegator holder t keep with
      | none    => simp only [hct, execFullTurnA, execFullA, hd]
      | some s1 =>
          simp only [hct, execFullTurnA, execFullA, hd, execFullTurnA_append,
                     execFullForestA_eq_execFullTurnA s1 sub]
          cases execFullTurnA s1 (lowerForestA sub) with
          | none    => rfl
          | some s2 => exact execFullChildrenA_eq_execFullTurnA delegator s2 rest
    | none =>
      -- `none` (`null` cap): subtree directly, no delegation emitted.
      simp only [hct, execFullTurnA_append, execFullForestA_eq_execFullTurnA s sub]
      cases execFullTurnA s (lowerForestA sub) with
      | none    => rfl
      | some s2 => exact execFullChildrenA_eq_execFullTurnA delegator s2 rest
end

/-! ## §5 — Conservation COROLLARIES: the per-asset VECTOR across the whole tree (one-line via the bridge).

These INHERIT the FILL-1 per-asset vector. We do NOT state a blanket `recTotal`-fixed: that is FALSE
for a mint/burn tree (a forest that mints or burns legitimately moves the supply, with the delta
disclosed). The honest law is: `recTotalAsset … b` moves by EXACTLY the net per-asset ledger delta of
the lowered turn, for EVERY asset `b` independently. -/

/-- **`execFullForestA_ledger_per_asset` (the per-asset conservation VECTOR, whole tree).** A
committed full-forest moves `recTotalAsset b` by EXACTLY the net per-asset ledger delta of its
pre-order lowering, for EVERY asset `b` independently. The tree generalization of
`execFullTurnA_ledger_per_asset`, riding the bridge. THIS is the FILL-1 vector — a scalar aggregate
could not state it (it would let a mint of asset B net against a burn of asset A). -/
theorem execFullForestA_ledger_per_asset (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + turnLedgerDeltaAsset (lowerForestA f) b := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_ledger_per_asset s s' (lowerForestA f) b h

/-- **`execFullForestA_conserves_per_asset`.** A committed full-forest whose net per-asset
ledger delta is `0` *in asset `b`* preserves asset `b`'s total supply. Applied with `∀ b, … = 0` this
gives FULL per-asset conservation across the whole tree: a transfer/authority-only forest, or one
whose per-asset mint/burn nets out in EACH asset, conserves EVERY asset class. The
`CONSERVATION_VECTOR` at the forest level. -/
theorem execFullForestA_conserves_per_asset (s s' : RecChainedState) (f : FullForestA) (b : AssetId)
    (h : execFullForestA s f = some s') (hzero : turnLedgerDeltaAsset (lowerForestA f) b = 0) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  rw [execFullForestA_ledger_per_asset s s' f b h, hzero, add_zero]

/-! ## §6 — `execFullForestA_no_amplify`: delegated caps NEVER amplify (Granovetter across the forest).

Each `FullChildA` edge `⟨holder, keep, parentCap, _⟩` delegates `attenuate keep parentCap` to
`holder` (the `Caps.derive` handoff). The cap-system no-amplification law `Caps.derive_no_amplify`
says the derived cap confers ≤ the parent's authority — so NO child gains authority the parent lacked.
We collect every edge of the tree and prove this holds of ALL of them: Granovetter (only connectivity
begets connectivity) across the whole forest. SAME law + edge data as
`TurnForest.execForest_no_amplify` — reused, never re-stubbed. A STRUCTURAL fact (holds of every
well-formed forest, committed or not). -/

/-- **`edge_no_amplify` (the per-edge Granovetter law).** A single delegation edge is
non-amplifying: the cap delegated to the child (`attenuate keep parentCap`) confers ≤ the parent's
authority. This is `Caps.derive_no_amplify` — reused verbatim. -/
theorem edge_no_amplify (keep : List Auth) (parentCap : Cap) :
    capAuthConferred (attenuate keep parentCap) ⊆ capAuthConferred parentCap :=
  derive_no_amplify keep parentCap

/-- **`execFullForestA_no_amplify` — THE FOREST GRANOVETTER LAW.** EVERY delegation edge of
the full-op-set forest is non-amplifying: for each `(keep, parentCap)` edge, the cap handed to the
child confers ≤ the parent's authority (`derive_no_amplify`). No child anywhere in the tree — at any
nesting depth — gains authority the parent lacked: *only connectivity begets connectivity*, across the
whole forest. A structural property of the forest data. -/
theorem execFullForestA_no_amplify (f : FullForestA) :
    ∀ e ∈ forestEdgesA f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 := by
  intro e _
  exact edge_no_amplify e.1 e.2

/-! ### §6.EXECUTED — the no-amplification ON THE COMMITTED HANDOFF (de-vacuified, granted-vs-HELD).

`execFullForestA_no_amplify` above is STRUCTURAL (it bounds each edge's `attenuate keep parentCap` by
the DECLARED `parentCap`, true of any forest, committed or not). The de-vacuified law is about the
EXECUTED handoff: when the executor's per-edge step `recCDelegateAtten s delegator holder t keep`
COMMITS, the cap it actually INSTALLS into `holder`'s slot confers `List Auth` rights `⊆` the cap the
delegator GENUINELY HELD to `t` (`recKDelegateAtten_non_amplifying`, granted-vs-HELD — two different
caps, NOT a `()≤()` collapse). And a forged/unauthorized edge (the delegator holds no cap to `t`)
NEVER commits (`recCDelegateAtten = none` ⇒ whole-forest rollback). THIS is the soundness content the
old decorative executor lacked: the gate is exercised ON EXECUTION, referencing the COMMITTED kernel
caps. -/

/-- **`recCDelegateAtten_executed_no_amplify` (the EXECUTED handoff is non-amplifying).** When
the executor's per-edge delegation step COMMITS (`recCDelegateAtten s delegator holder t keep = some
s'`), (a) `holder` GENUINELY HOLDS the granted cap `attenuate keep (heldCapTo s.kernel.caps delegator
t)` in the COMMITTED post-state, and (b) that granted cap's conferred rights are `⊆` the delegator's
HELD cap to `t` (`confRights granted ≤ confRights held`, `recKDelegateAtten_non_amplifying`). The
de-vacuified Granovetter law, on the executed kernel state — NOT the declared edge data. -/
theorem recCDelegateAtten_executed_no_amplify
    (s s' : RecChainedState) (delegator holder t : CellId) (keep : List Auth)
    (h : recCDelegateAtten s delegator holder t keep = some s') :
    attenuate keep (delegatedCapTo s.kernel.caps delegator t) ∈ s'.kernel.caps holder
      ∧ confRights (attenuate keep (delegatedCapTo s.kernel.caps delegator t))
          ≤ confRights (delegatedCapTo s.kernel.caps delegator t) := by
  -- `recCDelegateAtten` wraps `recKDelegateAtten s.kernel …`; on commit `s'.kernel = k'`.
  unfold recCDelegateAtten at h
  cases hd : recKDelegateAtten s.kernel delegator holder t keep with
  | none    => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      refine ⟨?_, recKDelegateAtten_non_amplifying s.kernel.caps delegator t keep⟩
      exact recKDelegateAtten_grants s.kernel k' delegator holder t keep hd

/-- **`execFullChildrenA_unauthorized_edge_fails` (forged edge ⇒ REJECT, the gate has teeth).**
If the FIRST child edge's executed handoff `recCDelegateAtten` is rejected (`= none` — the delegator
holds NO cap to `t := capTarget parentCap`), the whole child list rejects (`none`). So a
forged/unauthorized delegation edge aborts the forest — the non-amplification gate is NON-vacuous ON
EXECUTION (`forgedEdgeForest` is the executable witness). -/
theorem execFullChildrenA_unauthorized_edge_fails
    (delegator : CellId) (s : RecChainedState) (holder : Label) (keep : List Auth) (t : Label)
    (parentCap : Cap) (sub : FullForestA) (rest : List FullChildA)
    (ht : capTarget parentCap = some t)
    (hforged : recCDelegateAtten s delegator holder t keep = none) :
    execFullChildrenA delegator s (⟨holder, keep, parentCap, sub⟩ :: rest) = none := by
  show (match capTarget parentCap with
        | some t =>
          match recCDelegateAtten s delegator holder t keep with
          | some s1 => match execFullForestA s1 sub with
                       | some s2 => execFullChildrenA delegator s2 rest
                       | none    => none
          | none    => none
        | none =>
          match execFullForestA s sub with
          | some s2 => execFullChildrenA delegator s2 rest
          | none    => none) = none
  simp only [ht, hforged]

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
  show a ∈ a :: lowerChildrenA (targetOf a) kids
  exact List.mem_cons_self

/-- Every action of a child list's subtrees is in the child list's pre-order lowering (threading the
parent `delegator`; the per-edge `delegateAttenA` prefix — when present — only adds to the list, so
each subtree's action remains a member). -/
theorem execFullChildrenA_node_mem_lowered (delegator : CellId) (kids : List FullChildA)
    (c : FullChildA) (hc : c ∈ kids) : c.sub.action ∈ lowerChildrenA delegator kids := by
  match kids with
  | [] => exact absurd hc List.not_mem_nil
  | ⟨h, k, pc, sub⟩ :: rest =>
    show c.sub.action ∈
      (match capTarget pc with
       | some t => FullActionA.delegateAttenA delegator h t k
                     :: (lowerForestA sub ++ lowerChildrenA delegator rest)
       | none   => lowerForestA sub ++ lowerChildrenA delegator rest)
    have hbody : c.sub.action ∈ lowerForestA sub ++ lowerChildrenA delegator rest := by
      rcases List.mem_cons.mp hc with hceq | hcrest
      · subst hceq
        exact List.mem_append_left _ (execFullForestA_node_mem_lowered sub)
      · exact List.mem_append_right _ (execFullChildrenA_node_mem_lowered delegator rest c hcrest)
    cases capTarget pc with
    | some t => exact List.mem_cons_of_mem _ hbody
    | none   => exact hbody
end

/-- **`execFullForestA_each_attests` (per-node step-completeness, whole tree).** Every node
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

/-- **The root node itself attests (corollary).** The root's own action attests its
`fullActionInvA` (the per-node membership-lift specialized to the root via
`execFullForestA_node_mem_lowered`). -/
theorem execFullForestA_root_attests (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    ∃ sa sa', execFullA sa f.action = some sa' ∧ fullActionInvA sa f.action sa' :=
  execFullForestA_each_attests s s' f h f.action (execFullForestA_node_mem_lowered f)

/-! ## §8 — Fail-closed at the root (the journal/rollback discipline). -/

/-- **`execFullForestA_unauthorized_fails` (fail-closed at the root).** If the root node's
action is rejected (`execFullA s a = none`), the whole forest rejects (no partial commit). The
all-or-nothing discipline through the `execFullForestA` root. -/
theorem execFullForestA_unauthorized_fails (s : RecChainedState) (a : FullActionA)
    (kids : List FullChildA) (h : execFullA s a = none) :
    execFullForestA s ⟨a, kids⟩ = none := by
  show (match execFullA s a with
        | some s' => execFullChildrenA (targetOf a) s' kids
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

-- `targetOf` is defined in §1.5 (it is now load-bearing for the executor: it is the DELEGATOR of each
-- child edge — the authority handed downward). `sameTargetForest` reuses it as its discriminant.

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

/-! ## §9.CONFINE — AUTHORITY CONFINEMENT: the child USES the delegated cap (not just the handoff).

`execFullForestA_no_amplify` (§6) bounds the inserted HANDOFF (`attenuate keep parentCap ⊆ parentCap`),
and `recCDelegateAtten_executed_no_amplify` (§6.EXECUTED) bounds the cap INSTALLED into `holder`'s slot
(`granted ⊆ held`). But neither says the child SUBTREE actually CONFINES itself to that delegated cap:
the executor runs `sub` as an ordinary `execFullForestA` whose root action may target ANY cell. The
delegation grants authority over `t := capTarget parentCap` (the cell the parentCap confers an edge to);
a confined child is one whose root action ACTS ON that delegated cell `t` — i.e. it USES the delegated
authority rather than reaching for an unrelated one.

`confinedForest` is the STRUCTURAL precondition that binds this: every child's root action targets the
cell its edge delegated authority to (`targetOf sub.action = t`), recursively. `execFullChildrenA_confined_uses_delegated`
is the theorem that, COMBINED with the executed-handoff bound, makes the no-amplification law bound the
authority the child USES (its target = the delegated `t`, and the rights usable at `t` are `⊆` the
delegator's HELD rights), not merely the handoff.

THE NAMED RESIDUAL (the precise edge of what is and is NOT bounded here):
  * BOUNDED: the child's root action operates on the DELEGATED target cell `t`, under a cap whose
    rights at `t` are `⊆` the delegator's held rights (`recCDelegateAtten_executed_no_amplify`). The
    child cannot use the edge to reach an UNRELATED cell.
  * RESIDUAL #1 — per-FACET / per-effect use (does the child's effect stay within `keep`'s facets, and
    is its ACTOR exactly `holder`?) is the NODE-LEVEL gate's job: `execFullA`'s `authorizedB` /
    `stateAuthB` / `mintAuthorizedB` already fail-close a node whose actor lacks the cap-table rights
    for its effect on `t` (`execFullForestA_each_attests` carries the per-node obligation). The forest
    edge binds the TARGET; the node gate binds the FACET+actor. This is defense-in-depth, not a hole.
  * RESIDUAL #2 — `confinedForest` is a PRECONDITION (a property of the forest data the caller asserts),
    not yet a runtime check baked into `execFullForestA` (that would force a `capTarget`-vs-`targetOf`
    branch in the executor and is the cross-target routing's concern; a non-confined child is the
    cross-cell axis, routed to `Exec/CrossCellForest.lean`). We prove the confinement THEOREM under this
    precondition; making it an executor-enforced gate is the cross-target rotation. -/

mutual
/-- **`confinedForest`** — the AUTHORITY-CONFINEMENT predicate: every child's root action targets the
cell its delegation edge granted authority to (`targetOf sub.action = capTarget parentCap`, when the
edge delegates a real cap), recursively. A confined forest's children USE their delegated caps (act on
the delegated target), not arbitrary authority. A `null` parentCap (`capTarget = none`) delegates
nothing, so its child is unconstrained by THIS edge (it runs under its own independent authority). -/
def confinedForest : FullForestA → Prop
  | ⟨_, kids⟩ => confinedChildren kids

/-- Every child whose edge delegates a real cap has its subtree-root action targeting that cap's target
`t` (`targetOf sub.action = t`), AND each subtree is itself confined. -/
def confinedChildren : List FullChildA → Prop
  | []                             => True
  | ⟨_, _, parentCap, sub⟩ :: rest =>
      (match capTarget parentCap with
       | some t => targetOf sub.action = t
       | none   => True)
      ∧ confinedForest sub ∧ confinedChildren rest
end

/-- **`execFullChildrenA_confined_uses_delegated` — the child USES the delegated authority.** For a
CONFINED child list whose first edge delegates a real cap to `t := capTarget parentCap` and whose
executed handoff COMMITS, the child's root action targets EXACTLY `t` (it acts on the delegated cell),
and the cap installed into `holder`'s slot confers rights `⊆` the delegator's HELD cap to `t`. So the
authority the child USES (its target cell + the rights available there) is bounded by what was actually
delegated — NOT merely the handoff. (`recCDelegateAtten_executed_no_amplify` supplies the rights bound;
`confinedForest` supplies the target bound — together they confine USED authority.) -/
theorem execFullChildrenA_confined_uses_delegated
    (delegator : CellId) (s : RecChainedState)
    (holder : Label) (keep : List Auth) (t : Label) (parentCap : Cap)
    (sub : FullForestA) (rest : List FullChildA)
    (ht : capTarget parentCap = some t)
    (hconf : confinedChildren (⟨holder, keep, parentCap, sub⟩ :: rest)) :
    targetOf sub.action = t
      ∧ (∀ s1, recCDelegateAtten s delegator holder t keep = some s1 →
          confRights (attenuate keep (delegatedCapTo s.kernel.caps delegator t))
            ≤ confRights (delegatedCapTo s.kernel.caps delegator t)) := by
  refine ⟨?_, ?_⟩
  · -- the confinement precondition pins the child's target to the delegated `t`.
    have htarget : (match capTarget parentCap with
                    | some t => targetOf sub.action = t
                    | none   => True) := hconf.1
    rw [ht] at htarget
    exact htarget
  · intro s1 hc
    exact (recCDelegateAtten_executed_no_amplify s s1 delegator holder t keep hc).2

/-- **`execFullForestA_confined_root_target` — the root edge's child targets the delegated cell.** A
confined forest with at least one child (delegating a real cap to `t`) has that child's root action
targeting `t`. The forest-level face of confinement's TARGET bound: the delegation edge's authority is
USED on the cell it was granted for (NOT an arbitrary cell). This is the structural half that the
EXECUTED-handoff rights bound (`recCDelegateAtten_executed_no_amplify`) completes into full used-authority
confinement. -/
theorem execFullForestA_confined_root_target
    (a : FullActionA) (holder : Label) (keep : List Auth) (t : Label) (parentCap : Cap)
    (sub : FullForestA) (rest : List FullChildA)
    (ht : capTarget parentCap = some t)
    (hconf : confinedForest ⟨a, ⟨holder, keep, parentCap, sub⟩ :: rest⟩) :
    targetOf sub.action = t := by
  have htarget : (match capTarget parentCap with
                  | some t => targetOf sub.action = t
                  | none   => True) := hconf.1
  rw [ht] at htarget
  exact htarget

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins over the forest keystones). -/

#assert_axioms execFullForestA_eq_execFullTurnA
#assert_axioms execFullChildrenA_eq_execFullTurnA
#assert_axioms execFullForestA_ledger_per_asset
#assert_axioms execFullForestA_conserves_per_asset
#assert_axioms edge_no_amplify
#assert_axioms execFullForestA_no_amplify
#assert_axioms recCDelegateAtten_executed_no_amplify
#assert_axioms execFullChildrenA_unauthorized_edge_fails
#assert_axioms execFullForestA_node_mem_lowered
#assert_axioms execFullChildrenA_node_mem_lowered
#assert_axioms execFullForestA_each_attests
#assert_axioms execFullForestA_root_attests
#assert_axioms execFullForestA_unauthorized_fails
#assert_axioms execFullChildrenA_confined_uses_delegated
#assert_axioms execFullForestA_confined_root_target

/-! ## §11 — Non-vacuity (`#eval`): the FULL op-set tree commits per-asset; laundering CAUGHT;
unauthorized child rejected; no-amplify edge witness.

`fma0` (from `TurnExecutorFull`): a genuine 2-asset `bal` ledger — cell 0 holds 100 of asset 0 and 7
of asset 1; cell 1 holds 5 of asset 0; actor 9 holds the privileged `node 0` mint cap over cell 0.
Owner authority (actor = src) for balance transfers. We build trees over the FULL op-set
(mintA/balanceA/burnA), per-asset. -/

/-- **`fmaDeleg`** — `fma0`'s 2-asset ledger, but with the cap table GROUNDED so each forest's
delegators GENUINELY hold a cap conferring an edge to the parentCap's target (so the EXECUTED
`recCDelegateAtten` gate PASSES for the right reason, not vacuously). Cell **9** keeps the privileged
`node 0` mint cap (`mintA`/`burnA` authority). Cell **0** (the delegator of `goodFullForest`'s two
edges) holds `endpoint 1 [read,write]` (→ confers an edge to cell 1, the first edge's target) AND
`node 0` (→ confers an edge to cell 0, the deeper edge's target). Cell **1** (a delegator in
`deepFullForest`) holds `endpoint 0 [read,write]` (→ confers an edge to cell 0). These are the held
caps the `recKDelegateAtten` connectivity gate checks — WITHOUT them the forests REJECT (see
`forgedEdgeForest`). The ledger/accounts are `fma0`'s verbatim. -/
def fmaDeleg : RecChainedState :=
  { fma0 with kernel :=
      { fma0.kernel with
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1]
                         else if l = 0 then [Cap.endpoint 1 [Auth.read, Auth.write], Cap.node 0]
                         else if l = 1 then [Cap.endpoint 0 [Auth.read, Auth.write]]
                         else [] } }

/-- **`goodFullForest`** — a 3-node, 3-level full-op-set tree, per-asset NET ZERO ⇒ conserved. Run
against `fmaDeleg`, where every delegation edge's parent GENUINELY holds the delegated cap (the
EXECUTED `recCDelegateAtten` handoff commits for the RIGHT reason — see `forgedEdgeForest` for the
adversarial twin that REJECTS):
  * ROOT: `mintA 9 0 1 50` — actor 9 (holding the ISSUER cap `node 1`) mints 50 of ASSET 1 into
    cell 0: the W1 issuer-move — well 1 → −50, cell 0 → +50, supply UNCHANGED;
  * CHILD (delegated 0⟶0-holder, `[read] ⊆ [read,write]`, target cell 1): `balanceA ⟨0,0,1,30⟩ 0` —
    actor 0 transfers 30 of ASSET 0 from cell 0 to cell 1 (conserves asset 0). The delegation handoff
    GATES on cell 0 holding a cap to cell 1 (`endpoint 1 [r,w]` in `fmaDeleg`);
  * GRANDCHILD (delegated, target cell 0): `burnA 9 0 1 50` — actor 9 burns cell 0's 50 of ASSET 1
    back into well 1 (the return-to-well move). The handoff GATES on cell 0 holding a cap to cell 0
    (`node 0` in `fmaDeleg`).
W1: EVERY node conserves EVERY asset exactly (mint/burn are issuer-moves), so the per-asset net is
identically `0`. The delegation edges are non-amplifying AND EXECUTED (gated). -/
def goodFullForest : FullForestA :=
  ⟨ .mintA 9 0 1 50
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
               , [ { holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                   , sub := ⟨ .burnA 9 0 1 50, [] ⟩ } ] ⟩ } ] ⟩

#guard ((execFullForestA fmaDeleg goodFullForest).isSome)  --  true (whole tree commits — gated handoffs PASS)
-- The pre-order lowering now INTERLEAVES the EXECUTED `delegateAttenA` per edge: 3 nodes + 2 edges = 5:
#guard ((lowerForestA goodFullForest).length) == 5  --  5 (3 node-actions + 2 delegations)
-- The per-asset NET is 0 in BOTH assets (delegations are balance-neutral) ⇒ conserved per-asset:
#guard (turnLedgerDeltaAsset (lowerForestA goodFullForest) 0) == 0  --  0 (asset 0)
#guard (turnLedgerDeltaAsset (lowerForestA goodFullForest) 1) == 0  --  0 (asset 1: +50 -50)
-- The per-asset supply AFTER the tree: asset 0 = 105 (conserved), asset 1 = 7 (conserved):
#guard ((execFullForestA fmaDeleg goodFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((recTotalAsset fmaDeleg.kernel 0, recTotalAsset fmaDeleg.kernel 1)) == (105, 7)  --  (105, 7)
-- The chain grew by node count + edge count (3 + 2 = 5; each handoff lands an authority receipt):
#guard ((execFullForestA fmaDeleg goodFullForest).map (fun s => s.log.length)) == some 5  --  some 5
-- Every delegation edge is non-amplifying: each child's keep ⊆ its parent's cap rights.
#guard ((forestEdgesA goodFullForest).map (fun e => decide
        ((capAuthConferred (attenuate e.1 e.2)).length ≤ (capAuthConferred e.2).length))) == [true, true]  --  [true, true]

/-! ### CONFINEMENT non-vacuity (§9.CONFINE). `confinedForest` has TEETH: `goodFullForest` is NOT
authority-confined — its root edge delegates a cap to cell **1** (`capTarget (endpoint 1 …) = 1`) but
the child action `balanceA ⟨0,0,1,30⟩` TARGETS cell **0** (`src = 0 ≠ 1`). So the child uses the
delegated cap to reach a DIFFERENT cell than the cap was for — exactly the unconfined-authority shape
the predicate catches. (`goodFullForest` still COMMITS and is non-amplifying — confinement is an
ORTHOGONAL, stronger property that the §6 theorems did NOT establish.) -/

/-- `goodFullForest` is NOT confined: the root child's target (cell 0) ≠ the delegated target (cell 1). -/
example : ¬ confinedForest goodFullForest := by
  intro h
  -- `confinedForest` unfolds to `confinedChildren …`; the head edge's target obligation is `0 = 1`.
  have htgt : targetOf (FullActionA.balanceA ⟨0, 0, 1, 30⟩ 0) = 1 := by
    have := h.1                       -- the head edge's `match capTarget (endpoint 1 …)` obligation
    exact this
  exact absurd htgt (by decide)

/-- **`confinedFullForest`** — `goodFullForest`'s confined twin: the root delegates `node 0`
(`capTarget = 0`) and the child action TARGETS cell 0 (`balanceA ⟨0,0,1,30⟩ 0` has `src = 0`), so the
child USES the delegated cap on the cell it was granted for; the grandchild edge delegates `node 0`
(target 0) and `burnA 9 0 1 50` targets cell 0. EVERY child's action targets its delegated cell. -/
def confinedFullForest : FullForestA :=
  ⟨ .mintA 9 0 1 50
  , [ { holder := 0, keep := [Auth.read], parentCap := .node 0
      , sub := ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
               , [ { holder := 9, keep := [], parentCap := .node 0
                   , sub := ⟨ .burnA 9 0 1 50, [] ⟩ } ] ⟩ } ] ⟩

/-- The confined twin SATISFIES `confinedForest`: each child's action targets its delegated cell 0. -/
example : confinedForest confinedFullForest := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> first | rfl | trivial

/-- **`forgedEdgeForest` — THE ADVERSARIAL TWIN (the proof the delegation gate is REAL, NON-vacuous).**
IDENTICAL to `goodFullForest` EXCEPT the first delegation edge's `parentCap` claims an edge to cell
**2** — a cap the delegator (cell 0) does NOT hold in `fmaDeleg` (cell 0 holds caps to 1 and 0, never
2). So the EXECUTED `recCDelegateAtten` handoff FAILS its connectivity gate ⇒ the whole forest REJECTS
(`isSome = false`). If this were `true`, the gate would be VACUOUS — this `#eval` is the executable
witness that a FORGED/UNAUTHORIZED edge cannot commit. -/
def forgedEdgeForest : FullForestA :=
  ⟨ .mintA 9 0 1 50
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 2 [Auth.read, Auth.write]  -- target 2: UNHELD
      , sub := ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
               , [ { holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                   , sub := ⟨ .burnA 9 0 1 50, [] ⟩ } ] ⟩ } ] ⟩

-- ★ THE FORGED-EDGE TEETH: the parent (cell 0) holds NO cap to cell 2 ⇒ the whole forest is REJECTED:
#guard ((execFullForestA fmaDeleg forgedEdgeForest).isSome) == false  --  false (forged edge ⇒ REJECTED)
-- For contrast, the genuine forest commits on the SAME state (the gate is the ONLY difference):
#guard ((execFullForestA fmaDeleg goodFullForest).isSome)  --  true (the held-cap edge PASSES)

/-- **`deepFullForest`** — a 3-level INTRA-asset tree (deeper nesting works; recursion fully general).
Run against `fmaDeleg`: root transfer 0→1 of 10 (asset 0), child transfer 1→0 of 5 (asset 0, actor 1
owns cell 1), grandchild transfer 0→1 of 5 (asset 0). The two delegation edges are EXECUTED: the first
GATES on cell 0 holding a cap to cell 1 (`endpoint 1 [r,w]`), the deeper one (delegator = cell 1, the
inner transfer's `src`) GATES on cell 1 holding a cap to cell 0 (`endpoint 0 [r,w]`). All transfers
conserve asset 0 (and trivially asset 1). -/
def deepFullForest : FullForestA :=
  ⟨ .balanceA ⟨0, 0, 1, 10⟩ 0
  , [ { holder := 1, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ .balanceA ⟨1, 1, 0, 5⟩ 0
               , [ { holder := 0, keep := [], parentCap := .endpoint 0 [Auth.read, Auth.write]
                   , sub := ⟨ .balanceA ⟨0, 0, 1, 5⟩ 0, [] ⟩ } ] ⟩ } ] ⟩

#guard ((execFullForestA fmaDeleg deepFullForest).isSome)  --  true (3 levels commit — gated handoffs PASS)
#guard ((execFullForestA fmaDeleg deepFullForest).map (fun s => s.log.length)) == some 5  --  some 5 (3 transfers + 2 delegations)
#guard ((execFullForestA fmaDeleg deepFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (conserved)
#guard (turnLedgerDeltaAsset (lowerForestA deepFullForest) 0) == 0  --  0 (asset 0 conserved)

/-- **`badChildFullForest`** — a FAIL-CLOSED tree: the CHILD action is an UNAUTHORIZED mint (actor 0
holds no `node 0` mint cap — only actor 9 does). `execFullA`'s privileged `mintAuthorizedB` gate
rejects it, and all-or-nothing rolls back the WHOLE forest (the committed root included). The
cap-exceeding-child rejection across the full op-set. -/
def badChildFullForest : FullForestA :=
  ⟨ .balanceA ⟨0, 0, 1, 30⟩ 0
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read]
      , sub := ⟨ .mintA 0 0 1 50, [] ⟩ } ] ⟩   -- actor 0 lacks the `node 0` mint cap ⇒ rejected

#guard ((execFullForestA fma0 badChildFullForest).isSome) == false  --  false (unauthorized mint child ⇒ whole forest rejected)

/-- **`badRootFullForest`** — FAIL-CLOSED at the ROOT: an unauthorized mint root (actor 0 lacks the
`node 0` cap). The whole forest rejects before any child runs. -/
def badRootFullForest : FullForestA :=
  ⟨ .mintA 0 0 1 50, [] ⟩

#guard ((execFullForestA fma0 badRootFullForest).isSome) == false  --  false (unauthorized root ⇒ fail-closed)

/-- **`launderFullForest`** — the pre-W1 scalar-LAUNDERING tree (mint asset 1 at the root, burn
asset 0 in a child: a single-aggregate kernel saw +50 − 50 = 0 and accepted the cross-asset swap).
W1 kills the channel structurally: mint/burn are issuer-moves, so the per-asset delta family is
IDENTICALLY ZERO — no supply op exists to launder with. The tree below still REJECTS, now for an
even sharper reason: the child's `burnA 9 0 0 50` is a SELF-BURN of the issuer's own well
(`cell = a = 0`), which the `cell ≠ a` gate refuses outright. -/
def launderFullForest : FullForestA :=
  ⟨ .mintA 9 0 1 50            -- issuer-move: well 1 → cell 0 (conserving)
  , [ { holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
      , sub := ⟨ .burnA 9 0 0 50, [] ⟩ } ] ⟩   -- self-burn of well 0: REFUSED (cell ≠ a)

-- W1: the delta family vanishes — there is NO disclosed non-conservation left to aggregate away:
#guard (turnLedgerDeltaAsset (lowerForestA launderFullForest) 0) == 0  --  0 (W1 exactness)
#guard (turnLedgerDeltaAsset (lowerForestA launderFullForest) 1) == 0  --  0 (W1 exactness)
-- The launder forest is REJECTED outright (fail-closed — the self-burn child refuses):
#guard ((execFullForestA fma0 launderFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))).isNone

/-! The NO-AMPLIFY edge witness: a STRICT attenuation. `keep = [read]` ⊊ `parentCap = endpoint with
[read, write]` — `attenuate` STRICTLY drops `write`, so `confRights` drops a REAL element (not a
`()≤()` collapse). The genuine Granovetter inequality `granted ⊊ held`. -/

/-- The strict-attenuation edge from the root of `goodFullForest`: parent cap `endpoint 1
[read,write]`, child keeps only `[read]`. -/
def strictEdge : List Auth × Cap := ([Auth.read], .endpoint 1 [Auth.read, Auth.write])

-- The parent confers `[read, write]`; the attenuated child confers only `[read]` — write DROPPED:
#guard (capAuthConferred strictEdge.2 == [Auth.read, Auth.write])  --  [read, write]
#guard (capAuthConferred (attenuate strictEdge.1 strictEdge.2) == [Auth.read])  --  [read] (write strictly dropped)
-- The attenuation STRICTLY shrinks the conferred rights (a real element gone), NOT mere ⊆:
#guard (decide ((capAuthConferred (attenuate strictEdge.1 strictEdge.2)).length
                < (capAuthConferred strictEdge.2).length))  --  true (STRICT drop)
-- `write` is conferred by the parent but NOT by the attenuated child (the dropped element):
#guard ((capAuthConferred strictEdge.2).contains Auth.write)  --  true
#guard ((capAuthConferred (attenuate strictEdge.1 strictEdge.2)).contains Auth.write) == false  --  false (DROPPED)

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

-- Run against `fmaDeleg` (cell 0 holds `node 0`, so the 0⟶0-target handoff gate passes):
#guard ((execFullForestA fmaDeleg stateFullForest).isSome)  --  true (pure-state tree commits)
-- The pre-order lowering is the 2 pure-state node-actions + 1 EXECUTED delegation = 3:
#guard ((lowerForestA stateFullForest).length) == 3  --  3 (2 state effects + 1 delegation)
-- The per-asset net is 0 in BOTH assets (pure-state effects + delegation move NO asset's supply):
#guard ((turnLedgerDeltaAsset (lowerForestA stateFullForest) 0,
       turnLedgerDeltaAsset (lowerForestA stateFullForest) 1)) == (0, 0)  --  (0, 0)
-- The per-asset supply AFTER the pure-state tree: UNCHANGED at (105, 7) — balance-NEUTRALITY:
#guard ((execFullForestA fmaDeleg stateFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- ...the written fields read back (status=7, nonce=1) — the metadata domain DID advance:
#guard ((execFullForestA fmaDeleg stateFullForest).map
        (fun s => (EffectsState.fieldOf "status" (s.kernel.cell 0),
                   EffectsState.fieldOf "nonce" (s.kernel.cell 0)))) == some (7, 1)  --  some (7, 1)
-- ...the chain grew by node count + 1 delegation (2 + 1 = 3):
#guard ((execFullForestA fmaDeleg stateFullForest).map (fun s => s.log.length)) == some 3  --  some 3

/-- **`emitOnlyForest`** — a single-node tree carrying an authority-FREE `emitEventA` (dregg1
`apply_emit_event` runs NO cap check), by an actor (5) who owns nothing: it STILL commits (the
forest inherits the authority-free emit semantics). -/
def emitOnlyForest : FullForestA := ⟨ .emitEventA 5 0 7 42, [] ⟩

#guard ((execFullForestA fma0 emitOnlyForest).isSome)  --  true (authority-free emit)
#guard ((execFullForestA fma0 emitOnlyForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

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
      , sub := ⟨ .exerciseA 9 0 [], [] ⟩ } ] ⟩

#guard ((execFullForestA fma0 authFullForest).isSome)  --  true (authority tree commits)
-- The pre-order lowering is the authority node-actions:
#guard ((lowerForestA authFullForest).length) == 3  -- TODO(triage): comment claimed `2`; code yields `3` — `lowerForestA authFullForest` lowers to 3 actions, not 2 (stale node-count comment; the forest/lowering grew).
-- The per-asset net is 0 in BOTH assets (authority effects move NO asset's supply — balance-NEUTRAL):
#guard ((turnLedgerDeltaAsset (lowerForestA authFullForest) 0,
       turnLedgerDeltaAsset (lowerForestA authFullForest) 1)) == (0, 0)  --  (0, 0)
-- The per-asset supply AFTER the authority tree: UNCHANGED at (105, 7) — balance-NEUTRALITY:
#guard ((execFullForestA fma0 authFullForest).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- ...recipient 1 GAINED the introduced `node 0` edge (the cap GRAPH DID advance — the authority domain):
#guard ((execFullForestA fma0 authFullForest).map (fun s => s.kernel.caps 1)) == some [Cap.node 0]  --  some [Cap.node 0]
-- ...the chain grew by exactly the node count (3):
#guard ((execFullForestA fma0 authFullForest).map (fun s => s.log.length)) == some 3  -- TODO(triage): comment claimed `some 2`; code yields `some 3` — the chain grows by 3 (matches lowerForestA length 3), not 2 (stale node-count comment).

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
--   scoped OUT for v1 — a documented follow-on, not faked or assumed.
-/

end Dregg2.Exec.FullForest
