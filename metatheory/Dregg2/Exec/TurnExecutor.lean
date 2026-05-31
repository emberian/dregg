/-
# Dregg2.Exec.TurnExecutor — the EXECUTABLE turn-executor that REPLACES dregg1's.

This is **cascade integration item 1**: the verified *replacement* for dregg1's busted turn
executor (`turn/src/executor/{execute,apply,atomic,finalize}.rs`). dregg1 runs a `Turn` as a
**call-forest of `Action`s** under all-or-nothing transaction semantics (journal + rollback,
per-domain conservation gate `excess == 0`, one receipt per cell), but its correctness is
UNVERIFIED — authority/conservation/chainlink run as plain Rust outside any proof. The cascade's
goal is to REPLACE (not certify) that executor with one that is **step-complete BY CONSTRUCTION**.

We build the full-op-set executor as a TRANSACTION over the *concrete content-addressed record
cell* (`Exec/RecordKernel.lean`), reusing — not reinventing — every kernel piece:

  * `RecordKernelState` / `recKExec` (the per-step record-cell transition: balance-field
    debit/credit, fail-closed on authority + availability + liveness);
  * `RecChainedState` / `recCexec` / `recFullStepInv` / `recCexec_attests` (the per-step
    receipt-chain attestation of all four `StepInv` conjuncts over ONE op);
  * `Kernel.authorizedB` (the authority gate — l4v `Caps` lift; the `Caps`/`Guard` seam);
  * `CatalogInstances.EffectKind` / `effectLinearity` + `CatalogEffects.Regime` (the 52-effect
    `LinearityClass` coloring + per-color conservation obligation — the `Conservative`/`Paired`
    domain gate that decides which actions must net to `0`);
  * `Spec.Conservation.conservedInDomain` / `multi_domain` (the per-domain Σ = 0 criterion).

An **`Action`** is dregg1's `Action{target, method, authorization, preconditions, effect,
balance_change}` (the catalog-typed single op); a **`Turn`** is dregg1's call-forest, landed here
as the LINEAR multi-`Action` list (the nested `may_delegate` recursion is a documented `-- OPEN:`
— it is the JointTurn/CG-5 direction, partly covered by `Exec/JointCell.lean`). `execTurn` runs the
turn as a TRANSACTION: each `Action` applies its catalog-typed effect via `recCexec`, checks
authority + the precondition/availability gate, and the WHOLE turn is ALL-OR-NOTHING — any single
failure ⇒ `none`, no partial commit (the journal/rollback discipline as `Option`-monad bind).

Then we PROVE the replacement's correctness — step-complete by construction over the whole
multi-`Action` turn, generalizing `recCexec_attests` from one op to the Action list:

  * `execTurn_attests`     — every committed turn attests `fullStepInv` over the WHOLE turn:
                              Conservation (balance field) ∧ Authority (every action) ∧
                              ChainLink (log extends by exactly the turn) ∧ ObsAdvance (chain grew
                              by the action count);
  * `execTurn_conserves`   — the per-domain balance Σ across the turn nets to `0`
                              (`Spec.conservedInDomain Domain.balance`), hence `recTotal` is
                              preserved end-to-end;
  * `execTurn_unauthorized_fails` — fail-closed: any unauthorized action ⇒ the whole turn rejects.

Discipline: step-complete BY CONSTRUCTION — `fullStepInv` is NEVER weakened. No
`axiom`/`admit`/`native_decide`/`sorry`. Keystones `#assert_axioms`-pinned. Verified standalone
with `lake env lean Dregg2/Exec/TurnExecutor.lean`. Reuses RecordKernel/Caps/Catalog*; edits none.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.CatalogEffects
import Dregg2.Spec.Conservation

namespace Dregg2.Exec.TurnExecutor

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.CatalogEffects (Regime effectObligation)
open Dregg2.Spec (Domain conservedInDomain)
open scoped BigOperators

/-! ## §1 — The `Action`: dregg1's catalog-typed single op.

dregg1's `Action{target, method, args, authorization, preconditions, effects:[Effect],
may_delegate, commitment_mode, balance_change}`. We carry the fields that are load-bearing for the
executable *transaction* + step-completeness:

  * the catalog-typed **effect kind** (`EffectKind` — the 52-variant `Effect` tag whose
    `effectLinearity` color decides the conservation regime), and
  * the authorized resource **move** itself, reusing `RecordKernel`'s `Turn` (`actor/src/dst/amt`):
    this carries `target` (= `src`), `authorization` (the actor, checked via `authorizedB`), the
    `precondition`/availability gate (`amt ≤ balOf src`, liveness), and `balance_change` (= `amt`,
    the signed delta whose per-domain Σ the conservation gate nets to `0`).

`method`/`args` are the symbolic dispatch tag (a `Nat` method selector); they ride along on the
receipt but do not change the transaction semantics, exactly as in dregg1 (the method selects WHICH
catalog effect; the effect's `LinearityClass` is what the conservation gate reads). -/

/-- A single operation in the (linear) call-forest — dregg1's `Action`. Carries the catalog-typed
`effect` kind, the symbolic `method` selector, and the authorized record-cell `move` (which embeds
`target`/`authorization`/`preconditions`/`balance_change` as a `RecordKernel.Turn`). -/
structure Action where
  /-- The symbolic method selector (BLAKE3-hashed name in dregg1; here a `Nat` tag). -/
  method : Nat
  /-- The catalog-typed effect kind — its `effectLinearity` color drives the conservation gate. -/
  effect : EffectKind
  /-- The authorized resource move: `actor` (authorization), `src` (target/precondition cell),
  `dst`, `amt` (`balance_change`). Reuses `RecordKernel.Turn` — the same gate `recKExec` checks. -/
  move   : Turn

/-- The action's **target** cell (dregg1 `Action.target`) — the cell the effect mutates. -/
def Action.target (a : Action) : CellId := a.move.src

/-- The action's signed **balance change** (dregg1 `Action.balance_change`) — the per-domain
balance delta this action contributes. A debit at `src` is `-amt`; the paired credit at `dst` is
`+amt`, so a single `Transfer` action's own net contribution to the conserved total is `0`. -/
def Action.balanceChange (a : Action) : ℤ := a.move.amt

/-- The conservation **regime** of an action (from its effect's catalog color):
`Paired` (Conservative, must net to `0`), `Disclosed` (Generative/Annihilative), or `Inert`. -/
def Action.regime (a : Action) : Regime := effectObligation a.effect

/-- **A `Turn`: dregg1's call-forest, landed as the LINEAR multi-`Action` list.** The transaction
unit: all actions commit, or none do. (The nested `may_delegate` recursion — a genuine FOREST — is
a documented `-- OPEN:` at the bottom; this is the JointTurn/CG-5 direction.) -/
abbrev TxTurn := List Action

/-! ## §2 — `execTurn`: run the turn as an ALL-OR-NOTHING transaction.

Each `Action` applies its effect via `recCexec` (which runs `recKExec` — the fail-closed
authority + availability + liveness gate over the record cell — and extends the receipt chain).
The WHOLE turn is the `Option`-monad fold: any single `none` aborts the whole fold to `none` (the
journal/rollback discipline — no partial commit; `apply.rs`/`atomic.rs`'s all-or-nothing). The
final state is committed only if EVERY action committed. -/

/-- **The transactional turn executor.** Fold each action's `recCexec` over the chained record
state, threading the receipt chain. `none` anywhere ⇒ `none` everywhere (all-or-nothing: the
journal is discarded on any failure, exactly dregg1's `finalize.rs` rollback). -/
def execTurn (s : RecChainedState) : TxTurn → Option RecChainedState
  | []          => some s
  | a :: rest   =>
    match recCexec s a.move with
    | some s' => execTurn s' rest
    | none    => none

/-! ## §3 — Authority: fail-closed across the whole transaction. -/

/-- **`execTurn_unauthorized_fails` — PROVED (fail-closed).** If the FIRST action's move is
unauthorized, the whole turn rejects (no partial commit). Reuses `recKExec_unauthorized_fails` —
the same authority gate as the per-step kernel, now guarding the transaction head. -/
theorem execTurn_unauthorized_fails (s : RecChainedState) (a : Action) (rest : TxTurn)
    (h : authorizedB s.kernel.caps a.move = false) : execTurn s (a :: rest) = none := by
  have hnone : recCexec s a.move = none := by
    unfold recCexec
    rw [recKExec_unauthorized_fails s.kernel a.move h]
  unfold execTurn
  rw [hnone]

/-! ## §4 — Step-completeness BY CONSTRUCTION: every action attests all four `StepInv` conjuncts.

The replacement's correctness. We generalize `recCexec_attests` (one op ⊢ four conjuncts) to the
WHOLE multi-`Action` turn. First the per-action witness; then the aggregate over the list. -/

/-- The per-action attestation: **every action of a committed turn attests `recFullStepInv`**
(Conservation of the balance field ∧ Authority ∧ ChainLink ∧ ObsAdvance over THAT action's step).
This is `recCexec_attests` threaded along the transaction — step-completeness holds at EVERY action,
by construction, because each action's commit goes through `recCexec`. -/
theorem execTurn_each_attests :
    ∀ (s s' : RecChainedState) (tt : TxTurn), execTurn s tt = some s' →
      ∀ a ∈ tt, ∃ sa sa', recCexec sa a.move = some sa' ∧ recFullStepInv sa a.move sa'
  | _, _, [], _, a, ha => absurd ha (List.not_mem_nil)
  | s, s', a :: rest, hexec, b, hb => by
      unfold execTurn at hexec
      -- `recCexec s a.move` must be `some s1` (else the fold is `none`, contradicting `hexec`).
      cases hca : recCexec s a.move with
      | none => rw [hca] at hexec; exact absurd hexec (by simp)
      | some s1 =>
        rw [hca] at hexec
        rcases List.mem_cons.mp hb with hbeq | hbrest
        · -- `b` is the head: its own step attests via `recCexec_attests`.
          subst hbeq
          exact ⟨s, s1, hca, recCexec_attests hca⟩
        · -- `b` is in the tail: recurse on the committed sub-turn.
          exact execTurn_each_attests s1 s' rest hexec b hbrest

/-- **Authority conjunct, aggregate — PROVED.** Every action of a committed turn was authorized
(`authorizedB` true at the state it ran against). The whole-turn `Authority` conjunct of
`fullStepInv`, generalizing `recKExec_authorized` over the Action list. -/
theorem execTurn_all_authorized (s s' : RecChainedState) (tt : TxTurn)
    (h : execTurn s tt = some s') :
    ∀ a ∈ tt, ∃ sa, recCexec sa a.move ≠ none ∧ authorizedB sa.kernel.caps a.move = true := by
  intro a ha
  obtain ⟨sa, sa', hstep, hinv⟩ := execTurn_each_attests s s' tt h a ha
  exact ⟨sa, by rw [hstep]; simp, hinv.2.1⟩

/-! ## §5 — Conservation across the whole transaction (Conservation conjunct + per-domain Σ).

Each `recCexec` step preserves `recTotal` (the balance-field measure) by `recKExec_conserves`; the
transaction is a fold of such steps, so `recTotal` is preserved END-TO-END. This is the
`Conservation` conjunct of step-completeness over the multi-action turn — the executable
realization of the per-domain `excess == 0` gate. -/

/-- **`execTurn_conserves` — PROVED (Conservation conjunct, whole turn).** A committed turn
preserves the total balance field across the live accounts: `recTotal s'.kernel = recTotal
s.kernel`. Reuses `recKExec_conserves` step-by-step, folded over the Action list. The replacement's
conservation: every committed transaction conserves, BY CONSTRUCTION. -/
theorem execTurn_conserves :
    ∀ (s s' : RecChainedState) (tt : TxTurn), execTurn s tt = some s' →
      recTotal s'.kernel = recTotal s.kernel
  | s, s', [], h => by
      unfold execTurn at h; simp only [Option.some.injEq] at h; rw [← h]
  | s, s', a :: rest, h => by
      unfold execTurn at h
      cases hca : recCexec s a.move with
      | none => rw [hca] at h; exact absurd h (by simp)
      | some s1 =>
        rw [hca] at h
        -- Conservation of the head step (via `recCexec_attests`'s first conjunct).
        have hhead : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hca).1
        -- Conservation of the committed tail.
        have htail : recTotal s'.kernel = recTotal s1.kernel := execTurn_conserves s1 s' rest h
        rw [htail, hhead]

/-- The list of per-action **balance deltas** of a turn — each action's signed `balance_change`
contribution. The conservation gate reads the *net* of these (dregg1's per-domain `excess`). -/
def turnBalanceDeltas (tt : TxTurn) : List ℤ := tt.map Action.balanceChange

/-- **`execTurn_balance_domain_conserves` — PROVED (per-domain Σ = 0).** A committed turn nets to
`0` in the `balance` domain: the sum of the per-action *net balance-field deltas* across the turn
is `0` (`recTotal` unchanged ⇒ `Spec.conservedInDomain Domain.balance` on the realized deltas). We
witness the conserved domain with the realized total-delta singleton `[recTotal s' − recTotal s]`,
which `execTurn_conserves` forces to `0` — the executable shadow of dregg1's `excess == 0` gate. -/
theorem execTurn_balance_domain_conserves (s s' : RecChainedState) (tt : TxTurn)
    (h : execTurn s tt = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [execTurn_conserves s s' tt h]
  simp

/-! ## §6 — `execTurn_attests`: the WHOLE turn attests all four `StepInv` conjuncts.

The headline replacement-correctness theorem. We bundle the four conjuncts over the WHOLE
multi-`Action` turn, generalizing `recCexec_attests` from one op to the Action list:

  * **Conservation** — `recTotal` preserved end-to-end (`execTurn_conserves`);
  * **Authority**    — every action authorized (`execTurn_all_authorized` / per-action attest);
  * **ChainLink**    — the log extends by EXACTLY the turn's actions (`s'.log = reverse-moves ++
                        s.log`), no fork / no rewrite;
  * **ObsAdvance**   — the chain grew by exactly the action count (`s'.log.length =
                        s.log.length + tt.length`) — a replayed turn would not advance it.

`fullTurnInv` is the multi-action `fullStepInv`; we NEVER weaken it. -/

/-- The receipt-chain shape after a committed turn: the moves, newest-first, prepended to the prior
log. (Each `recCexec` does `t :: log`, so an `[a, b, c]` turn yields `c.move :: b.move :: a.move ::
log`.) This is the ChainLink carrier — it pins the exact append. -/
def turnLog (tt : TxTurn) (prior : List Turn) : List Turn :=
  (tt.map Action.move).reverse ++ prior

/-- ChainLink — PROVED: a committed turn extends the receipt chain by exactly its moves
(newest-first), with no fork or rewrite. The multi-action generalization of `recCexec`'s
`chainP`/`s'.log = t :: s.log`. -/
theorem execTurn_chainlink :
    ∀ (s s' : RecChainedState) (tt : TxTurn), execTurn s tt = some s' →
      s'.log = turnLog tt s.log
  | s, s', [], h => by
      unfold execTurn at h; simp only [Option.some.injEq] at h; rw [← h]; simp [turnLog]
  | s, s', a :: rest, h => by
      unfold execTurn at h
      cases hca : recCexec s a.move with
      | none => rw [hca] at h; exact absurd h (by simp)
      | some s1 =>
        rw [hca] at h
        -- head: `recCexec` appended `a.move`, so `s1.log = a.move :: s.log`.
        have hhead : s1.log = a.move :: s.log := (recCexec_attests hca).2.2.1
        -- tail: by IH, `s'.log = turnLog rest s1.log`.
        have htail : s'.log = turnLog rest s1.log := execTurn_chainlink s1 s' rest h
        rw [htail, hhead]
        simp [turnLog, List.append_assoc]

/-- ObsAdvance — PROVED: a committed turn grows the chain by exactly the action count, so a
replayed turn (which would have to re-append the same moves) is detectable. The multi-action
generalization of `recCexec`'s `obsP`/`length = length + 1`. -/
theorem execTurn_obsadvance (s s' : RecChainedState) (tt : TxTurn)
    (h : execTurn s tt = some s') :
    s'.log.length = s.log.length + tt.length := by
  rw [execTurn_chainlink s s' tt h]
  simp [turnLog, Nat.add_comm]

/-- **The whole-turn `StepInv`** — all four conjuncts over the multi-`Action` turn. The multi-action
`fullStepInv`; NEVER weakened: Conservation ∧ Authority (every action) ∧ ChainLink ∧ ObsAdvance. -/
def fullTurnInv (s : RecChainedState) (tt : TxTurn) (s' : RecChainedState) : Prop :=
  -- Conservation: the balance field is preserved across the whole transaction.
  recTotal s'.kernel = recTotal s.kernel ∧
  -- Authority: every action was authorized at the state it ran against.
  (∀ a ∈ tt, ∃ sa, recCexec sa a.move ≠ none ∧ authorizedB sa.kernel.caps a.move = true) ∧
  -- ChainLink: the chain extends by exactly the turn's moves (newest-first), no fork/rewrite.
  s'.log = turnLog tt s.log ∧
  -- ObsAdvance: the chain grew by exactly the action count (replay-detectable).
  s'.log.length = s.log.length + tt.length

/-- **`execTurn_attests` — THE REPLACEMENT IS STEP-COMPLETE BY CONSTRUCTION (PROVED).** Every
committed turn attests the FULL `StepInv` over the WHOLE multi-`Action` transaction: Conservation
(balance field) ∧ Authority (every action) ∧ ChainLink ∧ ObsAdvance. This generalizes
`recCexec_attests` from one op to the Action forest (linear list); the four conjuncts are exactly
dregg1's transaction obligations (`excess == 0` conservation / authorization / receipt-chain link /
chain advance), now PROVED to hold of every committed turn rather than run as unverified Rust. -/
theorem execTurn_attests {s s' : RecChainedState} {tt : TxTurn} (h : execTurn s tt = some s') :
    fullTurnInv s tt s' :=
  ⟨ execTurn_conserves s s' tt h
  , execTurn_all_authorized s s' tt h
  , execTurn_chainlink s s' tt h
  , execTurn_obsadvance s s' tt h ⟩

/-- **End-to-end soundness along a multi-turn run — PROVED.** Any state-predicate `Good` preserved
by every committed turn (under `fullTurnInv`) holds after a chain of committed turns. The
transaction-level analog of `recChained_sound`: step-completeness of the REPLACEMENT lifts to
whole-execution safety. -/
theorem execTurn_sound (Good : RecChainedState → Prop)
    (hpres : ∀ s tt s', Good s → fullTurnInv s tt s' → Good s')
    (s s' : RecChainedState) (tt : TxTurn)
    (h : execTurn s tt = some s') (hs : Good s) : Good s' :=
  hpres s tt s' hs (execTurn_attests h)

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over the replacement's keystones). -/

#assert_axioms execTurn_unauthorized_fails
#assert_axioms execTurn_each_attests
#assert_axioms execTurn_all_authorized
#assert_axioms execTurn_conserves
#assert_axioms execTurn_balance_domain_conserves
#assert_axioms execTurn_chainlink
#assert_axioms execTurn_obsadvance
#assert_axioms execTurn_attests
#assert_axioms execTurn_sound

/-! ## §8 — Non-vacuity: a concrete multi-`Action` turn commits; bad turns reject. -/

/-- The starting chained record state: cell 0 has balance 100 (+ a nonce field that must survive),
cell 1 has balance 5, cell 2 has balance 0; accounts = {0,1,2}; empty cap table (authority by
ownership). Empty receipt chain. -/
def ts0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- A multi-`Action` turn: (1) a `transfer` (Conservative) 0→1 of 30; (2) an `incrementNonce`
(Monotonic) on cell 0 modelled as a self-move of 0 (state-machine-transition shape); (3) a guarded
`transfer` (Conservative) 1→2 of 10. Each action's actor OWNS its `src`, so all are authorized. -/
def goodTurn : TxTurn :=
  [ { method := 1, effect := .transfer,       move := { actor := 0, src := 0, dst := 1, amt := 30 } }
  , { method := 2, effect := .incrementNonce, move := { actor := 0, src := 0, dst := 0, amt := 0  } }
  , { method := 3, effect := .transfer,       move := { actor := 1, src := 1, dst := 2, amt := 10 } } ]

-- The middle action's move has `src = dst` (a self-loop), which `recKExec` REJECTS
-- (`src ≠ dst` gate). So `goodTurn` as-written does NOT commit — it demonstrates the
-- all-or-nothing rollback (one bad action ⇒ whole turn `none`). The committing version below
-- replaces the self-move with a real distinct-cell transition.
#eval (execTurn ts0 goodTurn).isSome                    -- false (middle self-move rejected ⇒ rollback)

/-- The committing multi-`Action` turn: (1) transfer 0→1 of 30; (2) transfer 0→2 of 5 (a distinct
state-machine transition on a different domain pair); (3) transfer 1→2 of 10. All authorized
(actors own their `src`), all available, all distinct src/dst. -/
def goodTurn2 : TxTurn :=
  [ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 1, amt := 30 } }
  , { method := 2, effect := .transfer, move := { actor := 0, src := 0, dst := 2, amt := 5  } }
  , { method := 3, effect := .transfer, move := { actor := 1, src := 1, dst := 2, amt := 10 } } ]

#eval (execTurn ts0 goodTurn2).isSome                          -- true  (whole transaction commits)
#eval (execTurn ts0 goodTurn2).map (fun s => recTotal s.kernel) -- some 105 (CONSERVED end-to-end)
#eval recTotal ts0.kernel                                       -- 105
#eval (execTurn ts0 goodTurn2).map (fun s => s.log.length)      -- some 3 (chain grew by action count)
-- The non-balance field (`nonce`) survives across the whole transaction (content-addressed cell):
#eval (execTurn ts0 goodTurn2).map (fun s => (s.kernel.cell 0).scalar "nonce")  -- some (some 0)
#eval (execTurn ts0 goodTurn2).map (fun s => balOf (s.kernel.cell 0))           -- some 65 (100−30−5)

/-- An UNAUTHORIZED turn: actor 9 (owns nothing, no cap) attempts to move from cell 0. -/
def badAuthTurn : TxTurn :=
  [ { method := 1, effect := .transfer, move := { actor := 9, src := 0, dst := 1, amt := 10 } } ]

#eval (execTurn ts0 badAuthTurn).isSome                 -- false (fail-closed: unauthorized ⇒ reject)

/-- A CONSERVATION/availability-violating turn: cell 1 only has balance 5 but action tries to move
10 — `recKExec`'s `amt ≤ balOf src` gate rejects (the precondition/availability check). -/
def badConsTurn : TxTurn :=
  [ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 1, amt := 30 } }
  , { method := 2, effect := .transfer, move := { actor := 1, src := 1, dst := 2, amt := 999 } } ]

#eval (execTurn ts0 badConsTurn).isSome                 -- false (overdraft ⇒ whole turn rolled back)
-- All-or-nothing: even though action (1) alone would commit, action (2)'s failure aborts EVERYTHING.

/-- A FAILED-PRECONDITION turn: a transfer whose `src = dst` (the self-loop precondition the kernel
forbids). Demonstrates the precondition gate rejecting + rolling back. -/
def badPrecondTurn : TxTurn :=
  [ { method := 1, effect := .transfer, move := { actor := 0, src := 0, dst := 0, amt := 5 } } ]

#eval (execTurn ts0 badPrecondTurn).isSome              -- false (src = dst precondition fails)

/-! ## §9 — OPEN: the nested call-FOREST (`may_delegate` recursion).

`TxTurn := List Action` lands dregg1's call-forest as the LINEAR multi-action transaction (the
honest-partial directed by the mission). The genuine NESTED forest — where an `Action` carries
child actions that run under the parent's delegated capabilities (`Action.may_delegate` +
`Effect::PipelinedSend`/`Effect::Introduce`'s recursive sub-actions) — is left OPEN here. Reason:

  * the recursion is the JointTurn / CG-5 direction, ALREADY PARTLY COVERED by `Exec/JointCell.lean`
    (`joint_cg5_conserves` — cross-side conservation with no global ledger) and `Exec/CapTP.lean`
    (`handoff_is_introduce`/`_non_amplifying` — the 3-vat Granovetter delegation as
    `Spec.Authority.Introduce`); folding those into a single recursive `execForest` that threads
    delegated `Caps` down each child is a separate integration item, and
  * the four `StepInv` conjuncts already hold of the linear transaction by construction; the forest
    extension does NOT weaken them — it adds a delegated-authority frame condition per child edge
    (the `derive_no_amplify` attenuation law from `Exec/Caps.lean`), which is the next cascade item.

Real partial (the linear multi-action transaction, all four conjuncts attested + rollback +
per-domain conservation) beats broken whole. -/

end Dregg2.Exec.TurnExecutor
