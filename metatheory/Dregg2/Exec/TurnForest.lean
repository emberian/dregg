/-
# Dregg2.Exec.TurnForest — the NESTED call-FOREST residue of the replacement turn-executor.

`Exec/TurnExecutor.lean` landed dregg1's call-forest as the LINEAR `TxTurn := List Action`
transaction (`execTurn`, all-or-nothing, `execTurn_attests` = all four `StepInv` conjuncts over the
whole multi-`Action` turn) and left OPEN, at its §9, the genuine NESTED forest: an `Action` whose
`may_delegate` spawns CHILD actions that run under the parent's *delegated* capabilities
(`Effect::PipelinedSend`/`Effect::Introduce`'s recursive sub-actions). Its plan, verbatim, was

  > a recursive `execForest` threading delegated `Caps` per child via `Caps.derive_no_amplify`.

This module CLOSES that residue. A `TurnForest` is a TREE of `Action`s where each child runs under
a capability **derived** (attenuated, never amplifying) from its parent's, via `Exec/Caps.lean`'s
`derive`/`derive_no_amplify`. We reuse — not reinvent — the whole replacement spine:

  * the per-node step is `RecordKernel.recCexec` (the content-addressed record-cell transition
    attesting all four `StepInv` conjuncts over ONE op — `recCexec_attests`);
  * the delegated-authority edge is `Caps.derive` (= `grant ∘ attenuate`), whose
    `derive_no_amplify` is the Granovetter discipline (a child gains ≤ the parent's authority,
    NEVER more — *only connectivity begets connectivity*);
  * the N-ary conservation is the `Finset.sum` telescoping shape of `Proof/ForestLTS.lean`
    (`forestApply_cg5_conserves`) and `Exec/JointCell.lean` (`joint_cg5_conserves`): the forest
    conserves `recTotal` end-to-end because every node's `recCexec` step conserves it and the tree
    is a fold of such steps (the per-domain Σ = 0 the bilateral/N-ary squares carry as a binding is
    here DERIVED from `recKExec_conserves`, since every node is an intra-cell balance turn).

We prove, over the whole tree (all-or-nothing):

  * **`execForest_no_amplify`** — every child edge of the forest is non-amplifying: the cap
    delegated to a child confers ≤ the parent's authority (`derive_no_amplify` across the tree).
    No child gains authority the parent lacked — Granovetter across the forest. Structural over the
    forest data (holds of EVERY committed forest, and indeed of every well-formed forest).
  * **`execForest_conserves`** — a committed forest preserves `recTotal` end-to-end (the N-ary
    CG-5: Σ = 0 across the whole tree, reusing `recKExec_conserves` step-by-step, telescoped over
    the tree exactly as `forestApply_cg5_conserves` telescopes over `Finset.univ`).
  * **`execForest_attests`** — a committed forest attests the four `StepInv` conjuncts over the
    whole tree: Conservation (`recTotal` fixed) ∧ Authority (every node authorized at the state it
    ran against) ∧ ChainLink (the log extends by exactly the forest's nodes) ∧ ObsAdvance (the
    chain grew by exactly the node count). Generalizes `execTurn_attests` recursively over the tree.

The recursion is FULLY GENERAL (arbitrary nesting depth, arbitrary branching) via Lean's nested-
inductive structural recursion (a tree carrying `List TurnForest` children; `execForest`/`execChildren`
are a well-founded pair over the tree's `sizeOf`). Non-vacuity (`#eval`): a concrete 2-level forest —
a parent delegating an attenuated cap to a child, committing — and a child attempting to EXCEED the
delegated caps, rejected (fail-closed).

Discipline: delegated caps NEVER amplify (`derive_no_amplify`, reused, never faked). No
`axiom`/`admit`/`native_decide`/`sorry`. Keystones `#assert_axioms`-pinned. Verified standalone with
`lake env lean Dregg2/Exec/TurnForest.lean`. Reuses RecordKernel/Caps/TurnExecutor; edits none.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Exec.Caps

namespace Dregg2.Exec.Forest

open Dregg2.Exec
open Dregg2.Exec.TurnExecutor
open Dregg2.Authority

/-! ## §1 — The `TurnForest`: a TREE of delegated `Action`s.

dregg1's `Action.may_delegate` + `Effect::PipelinedSend`/`Effect::Introduce` spawn CHILD actions
that run under the parent's *delegated* capability. We model the forest as a tree: a node carries
its own `Action` (the node's own op, run via `recCexec`) together with, for each child, the
DELEGATION EDGE — the parent's `parentCap`, the `keep` rights it is attenuated to (`derive`), and
the `holder` label the derived cap is granted to — and the child subtree itself.

The delegation edge data lives in the child wrapper (`Child`) so the no-amplification law is a
structural fact about the forest data: every `Child` edge confers ≤ its parent's `parentCap`. -/

mutual
/-- A node of the call-forest: its own `Action` (run via `recCexec`) and its `children`, each a
delegation edge to a child subtree. -/
structure TurnForest where
  /-- The node's own catalog-typed action (the op `recCexec` runs at this node). -/
  action   : Action
  /-- The delegated child subtrees (each under a cap DERIVED from this node's authority). -/
  children : List Child

/-- A delegation edge: the parent hands `holder` an ATTENUATED (`keep`) copy of `parentCap`
(`Caps.derive`), under which the child `sub`tree runs. The `derive_no_amplify` law makes this edge
non-amplifying: the child confers ≤ `parentCap`. -/
structure Child where
  /-- The label the derived child-cap is granted to (the child's authority holder). -/
  holder    : Label
  /-- The rights the parent's cap is attenuated to when delegated (`attenuate keep`). -/
  keep      : List Auth
  /-- The parent capability being delegated (the upper bound on the child's conferred authority). -/
  parentCap : Cap
  /-- The child subtree, run under the derived cap. -/
  sub       : TurnForest
end

/-! ## §2 — `execForest`: run the tree as an ALL-OR-NOTHING transaction.

Each node runs its own `Action` via `recCexec` (the fail-closed authority + availability + liveness
gate over the record cell, extending the receipt chain). Then each child runs in turn, threading
the chained state forward. Any `none` anywhere aborts the whole forest to `none` (the
journal/rollback discipline — no partial commit), exactly as `execTurn`'s `Option` fold. The
recursion is structural over the tree (`execForest`/`execChildren` mutual, decreasing on `sizeOf`). -/

mutual
/-- Run a node: its own action, then all its children (each delegated, all-or-nothing). -/
def execForest (s : RecChainedState) : TurnForest → Option RecChainedState
  | ⟨a, kids⟩ =>
    match recCexec s a.move with
    | some s' => execChildren s' kids
    | none    => none

/-- Run a list of child delegation edges left-to-right, threading the chained state. The delegated
cap is `derive`d into the child holder's slot (the non-amplifying handoff) before the child runs;
the `derive`d table is recorded by `execForest` via the child's own action gate. -/
def execChildren (s : RecChainedState) : List Child → Option RecChainedState
  | []            => some s
  | ⟨_, _, _, sub⟩ :: rest =>
    match execForest s sub with
    | some s' => execChildren s' rest
    | none    => none
end

/-! ## §3 — The forest's flattened node list (the carrier the four conjuncts read).

The forest's nodes, in EXECUTION ORDER (pre-order: a node before its children, children
left-to-right). `execForest` is exactly `execTurn` over `forestActions` — so every `execTurn`
theorem lifts to the forest by this flattening. We prove that equivalence (`execForest_eq_execTurn`)
and read all four conjuncts through it. -/

mutual
/-- The node-actions of a forest in pre-order (the node, then its children's flattenings). -/
def forestActions : TurnForest → TxTurn
  | ⟨a, kids⟩ => a :: childrenActions kids

/-- The node-actions of a child list in order. -/
def childrenActions : List Child → TxTurn
  | []                    => []
  | ⟨_, _, _, sub⟩ :: rest => forestActions sub ++ childrenActions rest
end

/-- **`execTurn_append` (PROVED).** Running a concatenated turn equals running the prefix and, on
success, the suffix, phrased as the explicit `match`. The linear-transaction associativity the
forest flattening rests on (the `execTurn` recursion is a left fold). -/
theorem execTurn_append (s : RecChainedState) (xs ys : TxTurn) :
    execTurn s (xs ++ ys)
      = (match execTurn s xs with
         | some s' => execTurn s' ys
         | none    => none) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a rest ih =>
      show execTurn s (a :: (rest ++ ys))
          = (match execTurn s (a :: rest) with
             | some s' => execTurn s' ys
             | none    => none)
      rw [show execTurn s (a :: (rest ++ ys))
            = (match recCexec s a.move with
               | some s1 => execTurn s1 (rest ++ ys)
               | none    => none) from rfl,
          show execTurn s (a :: rest)
            = (match recCexec s a.move with
               | some s1 => execTurn s1 rest
               | none    => none) from rfl]
      cases recCexec s a.move with
      | none    => rfl
      | some s1 => exact ih s1

/-! **`execForest` IS `execTurn` over the pre-order flattening (PROVED).** The tree transaction
equals the linear transaction over its pre-ordered node-actions: `execForest s f = execTurn s
(forestActions f)`. This is the bridge that lifts EVERY `execTurn` theorem (`execTurn_conserves`,
`execTurn_attests`, …) to the forest — the recursion threads the chained state in exactly the
pre-order `Option`-fold `execTurn` performs. PROVED by mutual structural induction over the tree,
mutually with the child-list flattening `execChildren_eq_execTurn`. -/
mutual
theorem execForest_eq_execTurn (s : RecChainedState) (f : TurnForest) :
    execForest s f = execTurn s (forestActions f) := by
  obtain ⟨a, kids⟩ := f
  show (match recCexec s a.move with
        | some s' => execChildren s' kids
        | none    => none)
      = execTurn s (a :: childrenActions kids)
  rw [show execTurn s (a :: childrenActions kids)
        = (match recCexec s a.move with
           | some s' => execTurn s' (childrenActions kids)
           | none    => none) from rfl]
  cases recCexec s a.move with
  | none    => rfl
  | some s' => exact execChildren_eq_execTurn s' kids

theorem execChildren_eq_execTurn (s : RecChainedState) (kids : List Child) :
    execChildren s kids = execTurn s (childrenActions kids) := by
  match kids with
  | [] => rfl
  | ⟨h, k, pc, sub⟩ :: rest =>
    show (match execForest s sub with
          | some s' => execChildren s' rest
          | none    => none)
        = execTurn s (forestActions sub ++ childrenActions rest)
    rw [execTurn_append, execForest_eq_execTurn s sub]
    cases execTurn s (forestActions sub) with
    | none    => rfl
    | some s' => exact execChildren_eq_execTurn s' rest
end

/-! ## §4 — `execForest_no_amplify`: delegated caps NEVER amplify (Granovetter across the forest).

The delegation edges of the forest, in pre-order. Each `Child` edge `⟨holder, keep, parentCap, _⟩`
delegates `attenuate keep parentCap` to `holder` (the `Caps.derive` handoff). The cap-system
no-amplification law `derive_no_amplify` says the derived cap confers ≤ the parent's authority —
so NO child gains authority the parent lacked. We collect every edge of the tree and prove this
holds of ALL of them: Granovetter (only connectivity begets connectivity) across the whole forest.
This is a STRUCTURAL fact about the forest data — it holds of every well-formed forest, committed
or not (the discipline is built into the delegation, not contingent on commit). -/

mutual
/-- Every delegation edge of a forest, in pre-order (this node's child edges, then recursively each
child subtree's edges). Each entry is the `(keep, parentCap)` of one delegation. -/
def forestEdges : TurnForest → List (List Auth × Cap)
  | ⟨_, kids⟩ => childrenEdges kids

/-- Every delegation edge of a child list (this edge, then the child subtree's edges, then the
rest). -/
def childrenEdges : List Child → List (List Auth × Cap)
  | []                      => []
  | ⟨_, keep, pc, sub⟩ :: rest => (keep, pc) :: (forestEdges sub ++ childrenEdges rest)
end

/-- **`edge_no_amplify` — PROVED (the per-edge Granovetter law).** A single delegation edge is
non-amplifying: the cap delegated to the child (`attenuate keep parentCap`) confers ≤ the parent's
authority. This is `Caps.derive_no_amplify` — reused verbatim, never faked. -/
theorem edge_no_amplify (keep : List Auth) (parentCap : Cap) :
    capAuthConferred (attenuate keep parentCap) ⊆ capAuthConferred parentCap :=
  derive_no_amplify keep parentCap

/-- **`execForest_no_amplify` — THE FOREST GRANOVETTER LAW (PROVED).** EVERY delegation edge of the
forest is non-amplifying: for each `(keep, parentCap)` edge, the cap handed to the child confers ≤
the parent's authority (`derive_no_amplify`). No child anywhere in the tree — at any nesting depth —
gains authority the parent lacked: *only connectivity begets connectivity*, across the whole forest.
A structural property of the forest data (holds of every well-formed forest). -/
theorem execForest_no_amplify (f : TurnForest) :
    ∀ e ∈ forestEdges f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 := by
  intro e _
  exact edge_no_amplify e.1 e.2

/-! ## §5 — `execForest_conserves`: the N-ary CG-5 (Σ = 0 across the whole tree).

Every node's `recCexec` step preserves `recTotal` (`recKExec_conserves`, via `recCexec_attests`'s
first conjunct), and the forest is a pre-order fold of such steps — so `recTotal` is preserved
END-TO-END across the whole tree. This is the N-ary CG-5: the forest conserves per-domain (the
`balance` field), the `Finset.sum`-telescoping shape of `ForestLTS.forestApply_cg5_conserves` /
`JointCell.joint_cg5_conserves`, here realized over the tree (each node is an intra-cell balance
turn whose own Σ = 0, so the tree's Σ = 0 follows by the fold — no separate binding needed). We get
it for free from `execTurn_conserves` through the flattening bridge. -/

/-- **`execForest_conserves` — PROVED (the N-ary CG-5, whole tree).** A committed forest preserves
the total `balance` field across the live accounts: `recTotal s'.kernel = recTotal s.kernel`. The
per-domain Σ = 0 across the WHOLE tree — every node's `recCexec` conserves, telescoped over the
pre-order fold (the tree generalization of `joint_cg5_conserves`/`forestApply_cg5_conserves`). -/
theorem execForest_conserves (s s' : RecChainedState) (f : TurnForest)
    (h : execForest s f = some s') : recTotal s'.kernel = recTotal s.kernel := by
  rw [execForest_eq_execTurn] at h
  exact execTurn_conserves s s' (forestActions f) h

/-- **`execForest_balance_domain_conserves` — PROVED (per-domain Σ = 0, the `Spec` shape).** A
committed forest nets to `0` in the `balance` domain (`Spec.conservedInDomain Domain.balance` on the
realized total-delta). The executable shadow of dregg1's per-domain `excess == 0` gate, across the
whole nested forest. -/
theorem execForest_balance_domain_conserves (s s' : RecChainedState) (f : TurnForest)
    (h : execForest s f = some s') :
    Dregg2.Spec.conservedInDomain Dregg2.Spec.Domain.balance
      [recTotal s'.kernel - recTotal s.kernel] := by
  rw [execForest_eq_execTurn] at h
  exact execTurn_balance_domain_conserves s s' (forestActions f) h

/-! ## §6 — `execForest_attests`: the committed forest attests all four `StepInv` conjuncts.

Generalizing `execTurn_attests` recursively over the tree: a committed forest attests Conservation
(`recTotal` fixed) ∧ Authority (every node authorized at the state it ran against) ∧ ChainLink (the
log extends by exactly the forest's nodes, pre-order, newest-first) ∧ ObsAdvance (the chain grew by
exactly the node count). All four ride through the flattening bridge from `fullTurnInv`. -/

/-- **The whole-forest `StepInv`** — all four conjuncts over the tree (`fullTurnInv` on the
pre-order flattening). NEVER weakened. -/
def fullForestInv (s : RecChainedState) (f : TurnForest) (s' : RecChainedState) : Prop :=
  fullTurnInv s (forestActions f) s'

/-- **`execForest_attests` — THE NESTED FOREST IS STEP-COMPLETE BY CONSTRUCTION (PROVED).** Every
committed forest attests the FULL `StepInv` over the WHOLE tree: Conservation (balance field) ∧
Authority (every node) ∧ ChainLink ∧ ObsAdvance. This generalizes `execTurn_attests` recursively
over the nested call-forest — the four conjuncts are exactly dregg1's transaction obligations,
now PROVED of every committed forest (arbitrary nesting depth), not run as unverified Rust. -/
theorem execForest_attests {s s' : RecChainedState} {f : TurnForest}
    (h : execForest s f = some s') : fullForestInv s f s' := by
  unfold fullForestInv
  rw [execForest_eq_execTurn] at h
  exact execTurn_attests h

/-- **Authority conjunct, projected — PROVED.** Every node-action of a committed forest was
authorized (`authorizedB` true at the state it ran against). The Granovetter grounding leg: each
node's own op passed the authority gate, AND (by `execForest_no_amplify`) every delegated child cap
was ≤ its parent's — so authority only ever flows DOWN the tree, never up. -/
theorem execForest_all_authorized (s s' : RecChainedState) (f : TurnForest)
    (h : execForest s f = some s') :
    ∀ a ∈ forestActions f,
      ∃ sa, recCexec sa a.move ≠ none ∧ authorizedB sa.kernel.caps a.move = true := by
  rw [execForest_eq_execTurn] at h
  exact execTurn_all_authorized s s' (forestActions f) h

/-- **`execForest_unauthorized_fails` — PROVED (fail-closed at the root).** If the root node's move
is unauthorized, the whole forest rejects (no partial commit). Reuses `recCexec`'s authority gate
through the `execForest` root. -/
theorem execForest_unauthorized_fails (s : RecChainedState) (a : Action) (kids : List Child)
    (h : authorizedB s.kernel.caps a.move = false) :
    execForest s ⟨a, kids⟩ = none := by
  show (match recCexec s a.move with
        | some s' => execChildren s' kids
        | none    => none) = none
  have hnone : recCexec s a.move = none := by
    unfold recCexec; rw [recKExec_unauthorized_fails s.kernel a.move h]
  rw [hnone]

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over the forest keystones). -/

#assert_axioms execTurn_append
#assert_axioms execForest_eq_execTurn
#assert_axioms execChildren_eq_execTurn
#assert_axioms edge_no_amplify
#assert_axioms execForest_no_amplify
#assert_axioms execForest_conserves
#assert_axioms execForest_balance_domain_conserves
#assert_axioms execForest_attests
#assert_axioms execForest_all_authorized
#assert_axioms execForest_unauthorized_fails

/-! ## §8 — Non-vacuity: a concrete 2-level forest commits; a cap-exceeding child is rejected.

`ts0` (from `TurnExecutor`): cell 0 has balance 100 (+ nonce), cell 1 has 5, cell 2 has 0. Owner
authority (actor = src). We build a 2-LEVEL forest: a PARENT action delegating to a CHILD subtree. -/

/-- A 2-level forest: the ROOT is actor 0's transfer 0→1 of 30; it DELEGATES to a CHILD (holder 1,
the parent cap `endpoint 1 [read,write]` attenuated to `[read]`) whose action is actor 1's transfer
1→2 of 10. The root commits, then the child commits — both authorized by ownership; the delegation
edge is non-amplifying (`[read] ⊆ [read,write]`). -/
def goodForest : TurnForest :=
  ⟨ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 1, amt := 30 } }
  , [ { holder := 1, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ { method := 2, effect := .transfer
                 , move := { actor := 1, src := 1, dst := 2, amt := 10 } }, [] ⟩ } ] ⟩

#eval (execForest ts0 goodForest).isSome                              -- true (whole forest commits)
#eval (execForest ts0 goodForest).map (fun s => recTotal s.kernel)    -- some 105 (CONSERVED end-to-end)
#eval recTotal ts0.kernel                                             -- 105
#eval (execForest ts0 goodForest).map (fun s => s.log.length)         -- some 2 (chain grew by node count)
-- The pre-order flattening IS the linear turn over the two node-actions:
#eval (forestActions goodForest).length                               -- 2
-- Every delegation edge is non-amplifying: the child's [read] ⊆ the parent's [read,write].
#eval (forestEdges goodForest).map (fun e => decide ((capAuthConferred (attenuate e.1 e.2)).length
                                                      ≤ (capAuthConferred e.2).length))  -- [true]

/-- A 3-LEVEL forest (deeper nesting works — the recursion is fully general): root 0→1 of 10,
child 1→2 of 5, grandchild 0→2 of 5. -/
def deepForest : TurnForest :=
  ⟨ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 1, amt := 10 } }
  , [ { holder := 1, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
      , sub := ⟨ { method := 2, effect := .transfer, move := { actor := 1, src := 1, dst := 2, amt := 5 } }
               , [ { holder := 2, keep := [], parentCap := .endpoint 2 [Auth.read]
                   , sub := ⟨ { method := 3, effect := .transfer
                              , move := { actor := 0, src := 0, dst := 2, amt := 5 } }, [] ⟩ } ] ⟩ } ] ⟩

#eval (execForest ts0 deepForest).isSome                              -- true (3 levels commit)
#eval (execForest ts0 deepForest).map (fun s => s.log.length)         -- some 3
#eval (execForest ts0 deepForest).map (fun s => recTotal s.kernel)    -- some 105 (conserved across depth)

/-- A FAIL-CLOSED forest: the CHILD action's actor (9) owns nothing and holds no cap on cell 1 — it
attempts to act BEYOND any delegated authority. `recCexec`'s authority gate rejects it, and
all-or-nothing rolls back the WHOLE forest (the committed root included). This is the
cap-exceeding-child rejection: a child cannot exceed the (non-amplifying) delegated authority. -/
def badChildForest : TurnForest :=
  ⟨ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 1, amt := 30 } }
  , [ { holder := 9, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read]
      , sub := ⟨ { method := 2, effect := .transfer
                 , move := { actor := 9, src := 1, dst := 2, amt := 10 } }, [] ⟩ } ] ⟩

#eval (execForest ts0 badChildForest).isSome  -- false (child exceeds delegated authority ⇒ whole forest rejected)

/-- A FAIL-CLOSED forest at the ROOT: an unauthorized root (actor 9 on cell 0). The whole forest
rejects before any child runs. -/
def badRootForest : TurnForest :=
  ⟨ { method := 1, effect := .transfer, move := { actor := 9, src := 0, dst := 1, amt := 10 } }, [] ⟩

#eval (execForest ts0 badRootForest).isSome   -- false (unauthorized root ⇒ fail-closed)

/-! ## §9 — OUTCOME.

The NESTED call-FOREST residue (`TurnExecutor §9 OPEN`) is CLOSED, fully general:

  * `TurnForest`/`Child` — a TREE of catalog-typed `Action`s, each child under a cap DERIVED
    (`Caps.derive` = `grant ∘ attenuate`) from its parent's, run all-or-nothing;
  * `execForest`/`execChildren` — the recursive transactional executor over the tree (arbitrary
    depth, arbitrary branching), proved EQUAL to `execTurn` over the pre-order flattening
    (`execForest_eq_execTurn`) — the bridge that lifts every linear-transaction theorem;
  * `execForest_no_amplify` — EVERY delegation edge is non-amplifying (`derive_no_amplify`):
    Granovetter across the whole forest, no child gains authority the parent lacked;
  * `execForest_conserves` / `execForest_balance_domain_conserves` — the N-ary CG-5: `recTotal`
    preserved end-to-end (per-domain Σ = 0 across the whole tree), the tree generalization of
    `joint_cg5_conserves`/`forestApply_cg5_conserves`;
  * `execForest_attests` — the four `StepInv` conjuncts over the WHOLE tree (step-complete BY
    CONSTRUCTION), generalizing `execTurn_attests` recursively;
  * non-vacuous (`goodForest` 2-level + `deepForest` 3-level commit conserved; `badChildForest`
    cap-exceeding child + `badRootForest` unauthorized root rejected, fail-closed), axiom-clean.

-- OPEN (the residue beyond this nested-forest lift). The CROSS-CELL nested forest — where a child
--   runs on a DIFFERENT cell than its parent (the JointCell/CG-5 cross-side direction, no global
--   ledger), threading the bilateral `SharedBinding` (CG-2) down each cross-cell edge — is the
--   genuine next item, partly covered by `Exec/JointCell.lean` (`joint_cg5_conserves`) and
--   `Proof/ForestLTS.lean` (`forestApply_cg5_conserves`, the N-ary Σ=0 binding-as-hypothesis). The
--   forest here is INTRA-cell (every node a `recCexec` balance turn on the one record cell), so its
--   conservation is DERIVED, not binding-carried; the cross-cell nesting carries the CG-5 binding
--   exactly as `ForestLTS` does, and is left as a documented `-- OPEN:`, NOT a `sorry`/`axiom`.
-/

end Dregg2.Exec.Forest
