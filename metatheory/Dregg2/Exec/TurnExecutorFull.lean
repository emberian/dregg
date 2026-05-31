/-
# Dregg2.Exec.TurnExecutorFull — WIDENING the replacement executor to the FULL dregg1 op-set.

`Exec/TurnExecutor.lean`'s `execTurn` runs dregg1's call-forest of catalog-typed *balance/effect*
`Action`s as an all-or-nothing transaction, step-complete by construction (`execTurn_attests`: the
four `StepInv` conjuncts over the whole multi-`Action` turn). But dregg1's turn-executor does MORE
than balance/effect moves: it also runs **authority ops** (grant/revoke caps — the Granovetter
delegate / target-revoke) and **supply ops** (mint/burn — the only ops that legitimately move the
conserved total). For the replacement to SUBSUME every dregg1 turn kind, it must cover those too.

This module widens the executor. We introduce a single sum

  `FullAction = balance (a `TurnExecutor.Action`)
              | delegate / revoke  (an AUTHORITY turn, via `AuthTurn`'s `recKDelegate` /
                                    `recKRevokeTarget`)
              | mint / burn        (a SUPPLY turn, the record-cell refinement of
                                    `Generators.execMint` / `execBurn` over the `balance` FIELD)`

and one executor `execFull : RecChainedState → FullAction → Option RecChainedState`, all over the
SAME content-addressed record world (`RecChainedState` / `recTotal` / `balOf`) that `TurnExecutor`
and `AuthTurn` already share — so the widening is genuinely ONE executor, not three. Each kind is
all-or-nothing (fail-closed gates, `Option`-monad). A whole turn is a list of `FullAction`s run as
a transaction (`execFullTurn`), exactly `execTurn`'s discipline lifted to the wider op-set.

We then PROVE that EVERY kind attests its `StepInv` obligations, packaged as `fullActionInv`:

  * **balance/effect** — Conservation (the `balance` field) ∧ Authority ∧ ChainLink ∧ ObsAdvance,
    delegated VERBATIM to `recCexec_attests` (the `TurnExecutor` spine, one op);
  * **authority (delegate/revoke)** — the FRAME-FIX: `recTotal` is UNCHANGED (conservation trivially
    preserved — `recKDelegate_frame` / `recKRevokeTarget_frame`), and the cap graph is EDITED per
    `AuthTurn` (`recKDelegate_execGraph` / `recKRevokeTarget_execGraph` = `Spec.addEdge`/`removeEdge`
    = `Introduce`/`Revoke` `result`); a delegation is moreover AUTHORIZED (`recKDelegate_grounds`:
    the delegator holds the source edge — "only connectivity begets connectivity");
  * **mint/burn** — the supply MOVES by exactly `±amt` (`recMint_delta` / `recBurn_delta`, the
    record-cell refinement of `Generators.mint_delta`/`burn_delta`) with the
    Generative/Annihilative DISCLOSURE obligation discharged off `CatalogEffects`
    (`g_bridgeMint`/`a_burn` color ⇒ `is_disclosed_non_conservation`), and mint/burn are AUTHORIZED
    (the privileged `mintAuthorizedB` gate — a cell cannot coin its own supply).

The headline `execFull_attests` bundles these per-kind: every committed `FullAction` attests the
relevant `StepInv` content for its kind, so the replacement executor is **step-complete across EVERY
dregg1 turn kind** — not just balance/effect. (`fullActionInv` is never weakened: each kind carries
exactly its sound obligations, with conservation tracked EXACTLY — `0` for balance/authority, `±amt`
for mint/burn — via the `ledgerDelta` book-keeping, the executable shadow of dregg1's per-domain
`excess`.)

Discipline (REORIENT §6): no `axiom`/`admit`/`native_decide`/`sorry`. `#assert_axioms` on every
keystone. Pure, computable, `#eval`-able. Reuses `TurnExecutor`/`AuthTurn`/`Generators`/
`CatalogEffects`/`RecordKernel`; edits none. Verified standalone:
`lake env lean Dregg2/Exec/TurnExecutorFull.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.Generators
import Dregg2.CatalogEffects

namespace Dregg2.Exec.TurnExecutorFull

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.CatalogEffects (Regime effectObligation)
open Dregg2.Spec (Domain conservedInDomain LinearityClass)
open Dregg2.Exec.TurnExecutor (Action)
open scoped BigOperators

/-! ## §1 — Record-cell MINT/BURN: the supply generators over the `balance` FIELD.

`Exec/Generators.lean` proves `execMint`/`execBurn` over the *scalar* `KernelState` (`bal : CellId →
ℤ`, measure `total`). The full executor lives in the *record* world (`RecordKernelState`, measure
`recTotal` over the `balance` field). So we re-found the two supply generators here over the record
cell — the EXACT analog of `Generators` but writing the named `balance` field via `setBalance` —
reusing `Generators.mintAuthorizedB` (the privileged `node`/`control` gate; bare ownership is NOT
enough to coin supply) and `Kernel.sum_indicator` (the single-point-sum technique). -/

/-- Credit cell `cell`'s `balance` field by `amt` (record-cell mint write). Touches only `cell`'s
record (and only its `balance` field — every other field of the content-addressed record survives,
by `setBalance`); every other cell is untouched. -/
def recCreditCell (st : CellId → Value) (cell : CellId) (amt : ℤ) : CellId → Value :=
  fun c => if c = cell then setBalance (st c) (balOf (st c) + amt) else st c

/-- **Executable record-cell mint.** Fail-closed: credits `cell`'s `balance` field by `amt` only
when the actor is authorized to mint over `cell` (`mintAuthorizedB` — a `node`/`control` cap, NOT
mere ownership), the amount is non-negative, and `cell` is a live account. The record-cell
refinement of `Generators.execMint` over the `balance` field. -/
def recKMint (k : RecordKernelState) (actor cell : CellId) (amt : ℤ) : Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with cell := recCreditCell k.cell cell amt }
  else
    none

/-- **Executable record-cell burn.** Fail-closed: debits `cell`'s `balance` field by `amt` only when
authorized, the amount is non-negative and available (`amt ≤ balOf (cell)`), and `cell` is live. The
record-cell refinement of `Generators.execBurn`. -/
def recKBurn (k : RecordKernelState) (actor cell : CellId) (amt : ℤ) : Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts then
    some { k with cell := recCreditCell k.cell cell (-amt) }
  else
    none

/-- The `balance`-field delta of a single-cell credit, as a debit/credit indicator (the named-field
analog of `Generators.sum_update_add`'s pointwise step). -/
theorem recCreditCell_balOf_delta (st : CellId → Value) (cell : CellId) (amt : ℤ) (c : CellId) :
    balOf (recCreditCell st cell amt c) - balOf (st c) = (if c = cell then amt else 0) := by
  unfold recCreditCell
  rcases eq_or_ne c cell with h | h
  · rw [if_pos h, setBalance_balOf, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- **Single-cell supply delta over `recTotal`.** Crediting exactly the live cell `cell ∈ acc` by
`v` (writing the `balance` field) changes the total `balance` measure by exactly `v`. Reuses
`Kernel.sum_indicator`, the same single-point-sum technique the scalar generators use. -/
theorem recCreditCell_recTotal_delta (acc : Finset CellId) (st : CellId → Value) (cell : CellId)
    (v : ℤ) (hc : cell ∈ acc) :
    (∑ c ∈ acc, balOf (recCreditCell st cell v c)) = (∑ c ∈ acc, balOf (st c)) + v := by
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, balOf (recCreditCell st cell v c) - balOf (st c)
      = (if c = cell then v else 0) := fun c _ => recCreditCell_balOf_delta st cell v c
  rw [Finset.sum_congr rfl hg, sum_indicator acc cell v hc]

/-- **Record-cell mint inflow — PROVED.** A committed record mint raises the total `balance` by
exactly `amt`: `recTotal k' = recTotal k + amt`. The record-cell refinement of
`Core.mint_delta`/`Generators.execMint_delta`. -/
theorem recKMint_delta (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKMint k actor cell amt = some k') : recTotal k' = recTotal k + amt := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    simpa [recTotal] using recCreditCell_recTotal_delta k.accounts k.cell cell amt hcell
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Record-cell burn outflow — PROVED.** A committed record burn lowers the total `balance` by
exactly `amt`: `recTotal k' = recTotal k - amt`. The refinement of `Generators.execBurn_delta`. -/
theorem recKBurn_delta (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKBurn k actor cell amt = some k') : recTotal k' = recTotal k - amt := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hcell⟩ := hg
    have := recCreditCell_recTotal_delta k.accounts k.cell cell (-amt) hcell
    simpa [recTotal, sub_eq_add_neg] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No mint without authority — PROVED** (the integrity shadow of the privileged supply
generator). A committed record mint implies the actor held mint authority over `cell`. -/
theorem recKMint_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKMint k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No burn without authority — PROVED.** A committed record burn implies mint authority. -/
theorem recKBurn_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKBurn k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed (record mint) — PROVED.** Without mint authority, no record mint commits. -/
theorem recKMint_unauthorized_fails (k : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : recKMint k actor cell amt = none := by
  unfold recKMint; rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **Fail-closed (record burn) — PROVED.** Without mint authority, no record burn commits. -/
theorem recKBurn_unauthorized_fails (k : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : recKBurn k actor cell amt = none := by
  unfold recKBurn; rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-! ## §2 — The DISCLOSURE obligation for mint/burn (the Generative/Annihilative gate).

A supply move legitimately breaks `Σδ = 0`, but its delta is FORCED into the receipt — the
`is_disclosed_non_conservation` obligation `CatalogEffects` proves of the Generative
(`bridgeMint`/mint) and Annihilative (`burn`) colors. We tie each record-cell supply op to its
catalog color so the disclosure obligation is discharged for the executable op, not just abstractly.
-/

/-- A `mint`'s catalog effect kind (dregg1's `Effect::BridgeMint` — Generative). -/
def mintEffect : EffectKind := .bridgeMint

/-- A `burn`'s catalog effect kind (dregg1's `Effect::Burn` — Annihilative). -/
def burnEffect : EffectKind := .burn

/-- **Mint discloses — PROVED.** The mint effect is Generative, hence carries the disclosed
non-conservation obligation: its supply delta must be revealed in the receipt. Discharged off
`CatalogEffects.generative_discloses` + `g_bridgeMint`. -/
theorem mint_discloses : (effectLinearity mintEffect).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses mintEffect Dregg2.CatalogEffects.g_bridgeMint

/-- **Burn discloses — PROVED.** The burn effect is Annihilative, hence disclosed: its destroyed
amount must be revealed. Discharged off `CatalogEffects.annihilative_discloses` + `a_burn`. -/
theorem burn_discloses : (effectLinearity burnEffect).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.annihilative_discloses burnEffect Dregg2.CatalogEffects.a_burn

/-- Mint/burn carry the `Disclosed` regime (NOT `Paired`): they break conservation BY DESIGN, with
the delta disclosed — the supply ops are exactly the non-`Paired` half of the catalog. PROVED. -/
theorem mint_regime_disclosed : effectObligation mintEffect = Regime.Disclosed := rfl
theorem burn_regime_disclosed : effectObligation burnEffect = Regime.Disclosed := rfl

/-! ## §3 — Authority turns lifted to `RecChainedState` (the chained delegate / revoke).

`AuthTurn`'s `recKDelegate`/`recKRevokeTarget` edit `RecordKernelState.caps`. To run them inside the
unified chained executor we lift each onto `RecChainedState`, threading the receipt chain exactly as
`recCexec` does (newest move first), but carrying an authority "move" marker rather than a balance
`Turn`. The conserved measure is FIXED across an authority turn (the dual frame). -/

/-- A synthetic receipt marker for an authority turn (a self-`Turn` on the actor, amount `0`), so the
authority edit lands a row on the SAME receipt chain (`List Turn`) as balance/supply ops. It carries
no balance delta (`amt := 0`) — the chain entry records THAT an authority edit happened, while the
graph change itself is proven separately (`AuthTurn`'s `execGraph` match). -/
def authReceipt (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-- **Chained delegate.** Run `recKDelegate`; on commit, append an authority receipt. -/
def recCDelegate (s : RecChainedState) (delegator recipient t : CellId) :
    Option RecChainedState :=
  match recKDelegate s.kernel delegator recipient t with
  | some k' => some { kernel := k', log := authReceipt delegator :: s.log }
  | none    => none

/-- **Chained revoke.** `recKRevokeTarget` always commits (revocation only subtracts authority);
append an authority receipt. -/
def recCRevoke (s : RecChainedState) (holder t : CellId) : RecChainedState :=
  { kernel := recKRevokeTarget s.kernel holder t, log := authReceipt holder :: s.log }

/-- **Chained mint.** Run `recKMint`; on commit, append a supply receipt (a self-`Turn` carrying the
minted `amt` as its `balance_change` — the disclosed delta on the chain). -/
def recCMint (s : RecChainedState) (actor cell : CellId) (amt : ℤ) : Option RecChainedState :=
  match recKMint s.kernel actor cell amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := amt } :: s.log }
  | none    => none

/-- **Chained burn.** Run `recKBurn`; on commit, append a supply receipt carrying `-amt`. -/
def recCBurn (s : RecChainedState) (actor cell : CellId) (amt : ℤ) : Option RecChainedState :=
  match recKBurn s.kernel actor cell amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := -amt } :: s.log }
  | none    => none

/-! ## §4 — `FullAction` and `execFull`: ONE executor over the FULL op-set. -/

/-- **The FULL dregg1 op-set, as one sum.** A single `FullAction` is one of:
  * `balance a` — a catalog-typed balance/effect `Action` (dregg1's `Action`; runs via `recCexec`);
  * `delegate delegator recipient t` — a Granovetter authority grant (runs via `recKDelegate`);
  * `revoke holder t` — a target revocation (runs via `recKRevokeTarget`);
  * `mint actor cell amt` / `burn actor cell amt` — the privileged supply generators.
This widens `TurnExecutor.Action` (balance/effect only) to subsume EVERY dregg1 turn kind. -/
inductive FullAction where
  /-- A catalog-typed balance/effect action (dregg1's `Action`). -/
  | balance  (a : Action)
  /-- A Granovetter delegation: `delegator` hands `recipient` connectivity to `t`. -/
  | delegate (delegator recipient t : CellId)
  /-- A target revocation: `holder` loses every cap conferring an edge to `t`. -/
  | revoke   (holder t : CellId)
  /-- A privileged supply mint: credit `cell`'s `balance` by `amt`. -/
  | mint     (actor cell : CellId) (amt : ℤ)
  /-- A privileged supply burn: debit `cell`'s `balance` by `amt`. -/
  | burn     (actor cell : CellId) (amt : ℤ)

/-- **The ledger delta of a `FullAction`** — its exact effect on the conserved `recTotal`. Balance,
authority (delegate/revoke), are conservation-trivial (`0`); mint adds `amt`, burn subtracts. The
executable shadow of dregg1's per-domain `excess` book-keeping. -/
def ledgerDelta : FullAction → ℤ
  | .balance _        => 0
  | .delegate _ _ _   => 0
  | .revoke _ _       => 0
  | .mint _ _ amt     => amt
  | .burn _ _ amt     => -amt

/-- **The full executor.** Dispatch each `FullAction` kind to its (reused, already-proven) chained
primitive. All-or-nothing per kind (each is `Option`); `revoke` always commits. ONE executor over
the full op-set — balance/effect ∪ authority ∪ supply. -/
def execFull (s : RecChainedState) : FullAction → Option RecChainedState
  | .balance a              => recCexec s a.move
  | .delegate del rec t     => recCDelegate s del rec t
  | .revoke holder t        => some (recCRevoke s holder t)
  | .mint actor cell amt    => recCMint s actor cell amt
  | .burn actor cell amt    => recCBurn s actor cell amt

/-- **The full turn executor.** A turn is a list of `FullAction`s run as an ALL-OR-NOTHING
transaction (the `Option`-monad fold; any `none` aborts the whole turn). The wider analog of
`TurnExecutor.execTurn`. -/
def execFullTurn (s : RecChainedState) : List FullAction → Option RecChainedState
  | []        => some s
  | a :: rest =>
    match execFull s a with
    | some s' => execFullTurn s' rest
    | none    => none

/-! ## §5 — Conservation, EXACTLY: every committed `FullAction` moves `recTotal` by `ledgerDelta`.

The unified conservation law (the record-world analog of `Unified.step_delta`): balance and
authority kinds are conservation-trivial (`0`); mint/burn move the supply by exactly `±amt`. Proved
by `cases` over the kinds, reusing each primitive's already-proven delta fact. -/

/-- **`execFull_ledger` — PROVED (unified conservation).** Every committed `FullAction` moves the
conserved `recTotal` by EXACTLY `ledgerDelta`: `0` for balance/authority, `+amt` for mint, `-amt`
for burn. The single law subsuming `recCexec`'s conservation (`0`), `recKDelegate_frame`/
`recKRevokeTarget_frame` (`0`), and `recKMint_delta`/`recKBurn_delta` (`±amt`). -/
theorem execFull_ledger (s s' : RecChainedState) (fa : FullAction) (h : execFull s fa = some s') :
    recTotal s'.kernel = recTotal s.kernel + ledgerDelta fa := by
  cases fa with
  | balance a =>
      -- balance: `recCexec` conserves (`recTotal` fixed); `ledgerDelta = 0`.
      simp only [execFull, ledgerDelta] at h ⊢
      rw [(recCexec_attests h).1]; ring
  | delegate del rec t =>
      -- delegate: the dual frame fixes `recTotal`; `ledgerDelta = 0`.
      simp only [execFull, recCDelegate, ledgerDelta] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          rw [(recKDelegate_frame s.kernel k' del rec t hd).1]; ring
  | revoke holder t =>
      -- revoke: the dual frame fixes `recTotal`; `ledgerDelta = 0`.
      simp only [execFull, recCRevoke, ledgerDelta] at h ⊢
      simp only [Option.some.injEq] at h; subst h
      rw [(recKRevokeTarget_frame s.kernel holder t).1]; ring
  | mint actor cell amt =>
      -- mint: `recTotal` rises by `amt`; `ledgerDelta = +amt`.
      simp only [execFull, recCMint, ledgerDelta] at h ⊢
      cases hm : recKMint s.kernel actor cell amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          exact recKMint_delta s.kernel k' actor cell amt hm
  | burn actor cell amt =>
      -- burn: `recTotal` falls by `amt`; `ledgerDelta = -amt`.
      simp only [execFull, recCBurn, ledgerDelta] at h ⊢
      cases hb : recKBurn s.kernel actor cell amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          rw [recKBurn_delta s.kernel k' actor cell amt hb]; ring

/-- A `FullAction` is **balance-conserving** when its delta is `0` (everything but mint/burn — the
balance/effect and authority kinds). -/
def Conserving : FullAction → Prop
  | .balance _      => True
  | .delegate _ _ _ => True
  | .revoke _ _     => True
  | .mint _ _ _     => False
  | .burn _ _ _     => False

/-- A conserving `FullAction` has zero ledger delta — PROVED. -/
theorem ledgerDelta_eq_zero_of_conserving (fa : FullAction) (hc : Conserving fa) :
    ledgerDelta fa = 0 := by cases fa <;> simp_all [Conserving, ledgerDelta]

/-- **A conserving `FullAction` preserves `recTotal` — PROVED** (corollary of `execFull_ledger`):
balance/effect and authority turns leave the conserved supply FIXED. -/
theorem execFull_conserves (s s' : RecChainedState) (fa : FullAction)
    (hc : Conserving fa) (h : execFull s fa = some s') : recTotal s'.kernel = recTotal s.kernel := by
  rw [execFull_ledger s s' fa h, ledgerDelta_eq_zero_of_conserving fa hc, add_zero]

/-- **`execFull_balance_domain_conserves` — PROVED (per-domain Σ = 0 for conserving kinds).** A
committed conserving `FullAction` nets to `0` in the `balance` domain (the realized total-delta
singleton is `0`), the executable shadow of dregg1's `excess == 0` gate. -/
theorem execFull_balance_domain_conserves (s s' : RecChainedState) (fa : FullAction)
    (hc : Conserving fa) (h : execFull s fa = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [execFull_conserves s s' fa hc h]; simp

/-! ## §6 — Authority: every committed kind that gates on authority WAS authorized.

Balance/effect actions go through `recCexec`'s `authorizedB` gate; delegations ground in the
Granovetter source edge (`recKDelegate_grounds`); mint/burn go through the privileged
`mintAuthorizedB` gate. (Revoke needs no authority — it only subtracts; this is the SAME asymmetry
as `AuthTurn`'s "revocation always commits".) -/

/-- **Balance action authorized — PROVED.** A committed balance `FullAction` was authorized
(`authorizedB` at the pre-state), via `recCexec_attests`. -/
theorem execFull_balance_authorized (s s' : RecChainedState) (a : Action)
    (h : execFull s (.balance a) = some s') : authorizedB s.kernel.caps a.move = true :=
  (recCexec_attests (by simpa [execFull] using h)).2.1

/-- **Delegation grounds — PROVED.** A committed delegation HOLDS the Granovetter source edge
`delegator ⟶ ⟨t,()⟩` on `execGraph` (only connectivity begets connectivity), via
`recKDelegate_grounds`. -/
theorem execFull_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Mint authorized — PROVED.** A committed mint implies the actor held the privileged mint
authority over `cell` (a `node`/`control` cap — not mere ownership). -/
theorem execFull_mint_authorized (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.mint actor cell amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFull, recCMint] at h
  cases hm : recKMint s.kernel actor cell amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMint_authorized s.kernel k' actor cell amt hm

/-- **Burn authorized — PROVED.** A committed burn implies privileged mint authority over `cell`. -/
theorem execFull_burn_authorized (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.burn actor cell amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFull, recCBurn] at h
  cases hb : recKBurn s.kernel actor cell amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurn_authorized s.kernel k' actor cell amt hb

/-! ## §7 — The authority GRAPH change: a delegate/revoke IS `Spec.addEdge`/`removeEdge`.

The authority conjunct of step-completeness for the authority kinds: the cap edit's abstract image
is exactly a `Spec.AuthStep` edit of the connectivity graph — `recKDelegate_execGraph` /
`recKRevokeTarget_execGraph` from `AuthTurn`, here read off the committed `FullAction`. -/

/-- **Delegation IS `addEdge` — PROVED.** After a committed delegation, the reconstructed authority
graph is the pre-graph with the single Spec edge `recipient ⟶ ⟨t,()⟩` ADDED — `Spec.Introduce`'s
`result` verbatim. The authority conjunct for the delegate kind. -/
theorem execFull_delegate_addEdge (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      -- `recKDelegate` commits ⟹ it took the `grant` branch, so `k'.caps = grant …`.
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps rec t
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **Revocation IS `removeEdge` — PROVED.** After a committed revocation, the reconstructed graph
is the pre-graph with the single Spec edge `holder ⟶ ⟨t,()⟩` REMOVED — `Spec.Revoke`'s `result`
verbatim. The authority conjunct for the revoke kind. -/
theorem execFull_revoke_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFull s (.revoke holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-! ## §8 — ChainLink / ObsAdvance: every committed kind appends EXACTLY one receipt.

The chain-link / replay-detection conjuncts. Each kind extends the receipt chain by exactly one row
(newest-first), so the chain grows by exactly one per `FullAction` — a replayed action would have to
re-append, and is detectable. -/

/-- The receipt a committed `FullAction` appends (newest-first): the balance kind appends its move;
authority appends its `authReceipt`; mint/burn append a self-`Turn` carrying the supply delta. -/
def fullReceipt : FullAction → Turn
  | .balance a            => a.move
  | .delegate del _ _     => authReceipt del
  | .revoke holder _      => authReceipt holder
  | .mint actor cell amt  => { actor := actor, src := cell, dst := cell, amt := amt }
  | .burn actor cell amt  => { actor := actor, src := cell, dst := cell, amt := -amt }

/-- **ChainLink — PROVED.** A committed `FullAction` extends the receipt chain by EXACTLY its
`fullReceipt`, newest-first, with no fork or rewrite: `s'.log = fullReceipt fa :: s.log`. The
per-action generalization of `recCexec`'s `s'.log = t :: s.log` across the whole op-set. -/
theorem execFull_chainlink (s s' : RecChainedState) (fa : FullAction)
    (h : execFull s fa = some s') : s'.log = fullReceipt fa :: s.log := by
  cases fa with
  | balance a =>
      simp only [execFull, fullReceipt] at h ⊢
      exact (recCexec_attests h).2.2.1
  | delegate del rec t =>
      simp only [execFull, recCDelegate, fullReceipt] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | revoke holder t =>
      simp only [execFull, recCRevoke, fullReceipt] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | mint actor cell amt =>
      simp only [execFull, recCMint, fullReceipt] at h ⊢
      cases hm : recKMint s.kernel actor cell amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | burn actor cell amt =>
      simp only [execFull, recCBurn, fullReceipt] at h ⊢
      cases hb : recKBurn s.kernel actor cell amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' => rw [hb] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- **ObsAdvance — PROVED.** A committed `FullAction` grows the chain by exactly one row, so a
replayed action (which would re-append the same receipt) is detectable. -/
theorem execFull_obsadvance (s s' : RecChainedState) (fa : FullAction)
    (h : execFull s fa = some s') : s'.log.length = s.log.length + 1 := by
  rw [execFull_chainlink s s' fa h]; simp

/-! ## §9 — `fullActionInv`: the per-kind step-completeness obligation, bundled.

The headline invariant: every committed `FullAction` attests EXACTLY its sound `StepInv` content for
its kind. Conservation is tracked EXACTLY (`ledgerDelta`); ChainLink + ObsAdvance hold for ALL kinds;
the authority/disclosure obligations are carried per kind. `fullActionInv` is never weakened — each
kind carries its full, sound obligations (the supply kinds correctly DISCLOSE rather than conserve,
the asymmetry dregg1's catalog forces). -/

/-- **The per-`FullAction` `StepInv`** — true of every committed action, across all kinds:
  * **Ledger** — `recTotal` moved by EXACTLY `ledgerDelta` (conservation tracked precisely:
    `0`/`±amt`);
  * **ChainLink** — the chain extends by exactly `fullReceipt fa` (newest-first), no fork/rewrite;
  * **ObsAdvance** — the chain grew by exactly one row (replay-detectable);
  * **KindObligation** — the kind-specific integrity content: balance ⇒ `authorizedB`; delegate ⇒
    grounds in the source edge AND edits the graph by `addEdge`; revoke ⇒ edits by `removeEdge`;
    mint/burn ⇒ `mintAuthorizedB` AND the Generative/Annihilative `is_disclosed_non_conservation`. -/
def fullActionInv (s : RecChainedState) (fa : FullAction) (s' : RecChainedState) : Prop :=
  -- Ledger: conservation tracked EXACTLY.
  (recTotal s'.kernel = recTotal s.kernel + ledgerDelta fa) ∧
  -- ChainLink: exactly the kind's receipt, newest-first.
  (s'.log = fullReceipt fa :: s.log) ∧
  -- ObsAdvance: exactly one row.
  (s'.log.length = s.log.length + 1) ∧
  -- KindObligation: the kind-specific authority/graph/disclosure content.
  (match fa with
   | .balance a          => authorizedB s.kernel.caps a.move = true
   | .delegate del rec t =>
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩
   | .revoke holder t    =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .mint actor cell _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   | .burn actor cell _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity burnEffect).is_disclosed_non_conservation = true)

/-- **`execFull_attests` — THE FULL OP-SET IS STEP-COMPLETE BY CONSTRUCTION (PROVED).** Every
committed `FullAction` — balance/effect, authority (delegate/revoke), OR supply (mint/burn) — attests
its full `StepInv` content: exact ledger conservation (`ledgerDelta`) ∧ ChainLink ∧ ObsAdvance ∧ the
kind-specific obligation (authority / graph-edit / disclosure). So the replacement executor is
step-complete across EVERY dregg1 turn kind, not just balance/effect. -/
theorem execFull_attests {s s' : RecChainedState} {fa : FullAction} (h : execFull s fa = some s') :
    fullActionInv s fa s' := by
  refine ⟨execFull_ledger s s' fa h, execFull_chainlink s s' fa h, execFull_obsadvance s s' fa h, ?_⟩
  cases fa with
  | balance a => exact execFull_balance_authorized s s' a h
  | delegate del rec t =>
      exact ⟨execFull_delegate_grounds s s' del rec t h, execFull_delegate_addEdge s s' del rec t h⟩
  | revoke holder t => exact execFull_revoke_removeEdge s s' holder t h
  | mint actor cell amt => exact ⟨execFull_mint_authorized s s' actor cell amt h, mint_discloses⟩
  | burn actor cell amt => exact ⟨execFull_burn_authorized s s' actor cell amt h, burn_discloses⟩

/-! ## §10 — The whole-turn law: ledger across a transaction of `FullAction`s.

The transaction-level conservation: a committed `execFullTurn` moves `recTotal` by the SUM of the
per-action `ledgerDelta`s (mints add, burns subtract, the rest contribute `0`) — the executable
ledger equation across the FULL op-set, the record-world analog of `Unified.unified_ledger`. -/

/-- The net ledger delta of a turn = sum of per-action deltas. -/
def turnLedgerDelta (tt : List FullAction) : ℤ := (tt.map ledgerDelta).sum

/-- **`execFullTurn_ledger` — PROVED (transaction ledger).** A committed full-turn moves `recTotal`
by exactly the net of all per-action ledger deltas: `recTotal s'.kernel = recTotal s.kernel +
turnLedgerDelta tt`. Proved by induction on the turn, reusing `execFull_ledger`. -/
theorem execFullTurn_ledger :
    ∀ (s s' : RecChainedState) (tt : List FullAction), execFullTurn s tt = some s' →
      recTotal s'.kernel = recTotal s.kernel + turnLedgerDelta tt
  | s, s', [], h => by
      simp only [execFullTurn, Option.some.injEq] at h; subst h; simp [turnLedgerDelta]
  | s, s', a :: rest, h => by
      simp only [execFullTurn] at h
      cases ha : execFull s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotal s1.kernel = recTotal s.kernel + ledgerDelta a :=
            execFull_ledger s s1 a ha
          have htail : recTotal s'.kernel = recTotal s1.kernel + turnLedgerDelta rest :=
            execFullTurn_ledger s1 s' rest h
          rw [htail, hhead]
          simp only [turnLedgerDelta, List.map_cons, List.sum_cons]; ring

/-- **`execFullTurn_conserves` — PROVED.** A committed full-turn whose net ledger delta is `0`
(balance/authority only, or balanced mint/burn) preserves `recTotal`. The all-or-nothing transaction
conserves when the supply nets out. -/
theorem execFullTurn_conserves (s s' : RecChainedState) (tt : List FullAction)
    (h : execFullTurn s tt = some s') (hzero : turnLedgerDelta tt = 0) :
    recTotal s'.kernel = recTotal s.kernel := by
  rw [execFullTurn_ledger s s' tt h, hzero, add_zero]

/-- **Every action of a committed full-turn attests `fullActionInv` — PROVED.** Step-completeness
holds at EVERY action of the transaction, across all kinds: the per-action witness threaded along
the fold. The full-op-set generalization of `TurnExecutor.execTurn_each_attests`. -/
theorem execFullTurn_each_attests :
    ∀ (s s' : RecChainedState) (tt : List FullAction), execFullTurn s tt = some s' →
      ∀ fa ∈ tt, ∃ sa sa', execFull sa fa = some sa' ∧ fullActionInv sa fa sa'
  | _, _, [], _, fa, hfa => absurd hfa List.not_mem_nil
  | s, s', a :: rest, h, b, hb => by
      simp only [execFullTurn] at h
      cases ha : execFull s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          rcases List.mem_cons.mp hb with hbeq | hbrest
          · subst hbeq; exact ⟨s, s1, ha, execFull_attests ha⟩
          · exact execFullTurn_each_attests s1 s' rest h b hbrest

/-! ## §MA — The PER-ASSET full turn executor (the `CONSERVATION_VECTOR` wired into a transaction).

§4–§10 conserve ONE scalar (`recTotal`, the `balance` field). The genuine per-asset law
(`RecordKernel.recKExecAsset_conserves_per_asset`, §MULTI-ASSET) lives over `RecordKernelState.bal`.
Here we build the full-turn executor over THAT ledger — `balanceA`/`delegate`/`revoke`/`mintA`/`burnA`
— and prove the all-or-nothing transaction moves `recTotalAsset b` by EXACTLY the net per-asset
ledger delta, for EVERY asset `b` independently. This is the executable turn whose FFI export
(`dregg_exec_full_turn`) conserves PER-ASSET (`DREGG2-GAP-MAP.md FILL 1`), not the scalar. The
`delegate`/`revoke` kinds are REUSED verbatim (`recCDelegate`/`recCRevoke`); authority is
asset-orthogonal (it edits `caps`, leaving `bal` fixed), so it contributes `0` to every asset. -/

/-- **Single-cell, single-asset credit** on the per-asset ledger: add `amt` to cell `cell`'s asset
`a`, leaving every other (cell, asset) pair untouched. The per-asset analog of `recCreditCell`. -/
def recBalCredit (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun c b => if c = cell ∧ b = a then bal c b + amt else bal c b

/-- The per-asset ledger delta of a single-cell credit: asset `a`'s supply rises by `amt` (when
`cell` is live), every OTHER asset is literally untouched. The per-asset analog of
`recCreditCell_recTotal_delta`, reusing `sum_indicator`. PROVED. -/
theorem recBalCredit_recTotalAsset (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (cell : CellId) (a : AssetId) (amt : ℤ) (hc : cell ∈ acc) (b : AssetId) :
    (∑ c ∈ acc, recBalCredit bal cell a amt c b)
      = (∑ c ∈ acc, bal c b) + (if b = a then amt else 0) := by
  by_cases hb : b = a
  · rw [if_pos hb]
    have key : (∑ c ∈ acc, recBalCredit bal cell a amt c b) - (∑ c ∈ acc, bal c b) = amt := by
      rw [← Finset.sum_sub_distrib]
      have hg : ∀ c ∈ acc, recBalCredit bal cell a amt c b - bal c b = (if c = cell then amt else 0) := by
        intro c _
        unfold recBalCredit
        by_cases hcc : c = cell
        · rw [if_pos ⟨hcc, hb⟩, if_pos hcc]; ring
        · rw [if_neg (by rintro ⟨h, _⟩; exact hcc h), if_neg hcc]; ring
      rw [Finset.sum_congr rfl hg, sum_indicator acc cell amt hc]
    omega
  · rw [if_neg hb, add_zero]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold recBalCredit; rw [if_neg (by rintro ⟨_, h⟩; exact hb h)]

/-- **The privileged per-asset MINT** over the `bal` ledger. Same `mintAuthorizedB` gate as the
scalar mint (a `node`/`control` cap, not ownership); credits cell `cell`'s asset `a` by `amt`. -/
def recKMintAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a amt }
  else
    none

/-- **The privileged per-asset BURN** over the `bal` ledger. Debits cell `cell`'s asset `a` by `amt`
(a credit of `-amt`), gated on availability *in that asset* + mint authority. -/
def recKBurnAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a (-amt) }
  else
    none

/-- **Per-asset mint inflow — PROVED.** A committed per-asset mint raises asset `a`'s supply by
`amt` and leaves EVERY OTHER asset untouched: `recTotalAsset k' b = recTotalAsset k b + (if b = a
then amt else 0)`. The per-asset refinement of `recKMint_delta` (which moved one scalar). -/
theorem recKMintAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKMintAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then amt else 0) := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    show (∑ c ∈ k.accounts, recBalCredit k.bal cell a amt c b)
        = (∑ c ∈ k.accounts, k.bal c b) + (if b = a then amt else 0)
    exact recBalCredit_recTotalAsset k.accounts k.bal cell a amt hcell b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn outflow — PROVED.** A committed per-asset burn lowers asset `a`'s supply by
`amt` and leaves EVERY OTHER asset untouched: `recTotalAsset k' b = recTotalAsset k b + (if b = a
then -amt else 0)`. -/
theorem recKBurnAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKBurnAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then (-amt) else 0) := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hcell⟩ := hg
    show (∑ c ∈ k.accounts, recBalCredit k.bal cell a (-amt) c b)
        = (∑ c ∈ k.accounts, k.bal c b) + (if b = a then (-amt) else 0)
    exact recBalCredit_recTotalAsset k.accounts k.bal cell a (-amt) hcell b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- No per-asset mint without authority — PROVED. -/
theorem recKMintAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKMintAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor cell = true := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The chained per-asset transfer/mint/burn** (thread the receipt chain, newest-first, exactly as
`recCexec`/`recCMint`/`recCBurn` do for the scalar kernel). -/
def recCexecAsset (s : RecChainedState) (t : Turn) (a : AssetId) : Option RecChainedState :=
  match recKExecAsset s.kernel t a with
  | some k' => some { kernel := k', log := t :: s.log }
  | none    => none

/-- Chained per-asset mint. -/
def recCMintAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKMintAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := amt } :: s.log }
  | none    => none

/-- Chained per-asset burn (the receipt discloses `-amt`). -/
def recCBurnAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKBurnAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := -amt } :: s.log }
  | none    => none

/-- **The FULL per-asset op-set, as one sum.** `balanceA t a` (a per-asset transfer of asset `a`);
`delegate`/`revoke` (authority, asset-orthogonal); `mintA`/`burnA` (the per-asset supply
generators). The asset-typed analog of `FullAction`. -/
inductive FullActionA where
  /-- A per-asset balance transfer: move asset `asset` per `turn`. -/
  | balanceA (turn : Turn) (asset : AssetId)
  /-- A Granovetter delegation (authority; bal-orthogonal). -/
  | delegate (delegator recipient t : CellId)
  /-- A target revocation (authority; bal-orthogonal). -/
  | revoke   (holder t : CellId)
  /-- A privileged per-asset supply mint. -/
  | mintA    (actor cell : CellId) (asset : AssetId) (amt : ℤ)
  /-- A privileged per-asset supply burn. -/
  | burnA    (actor cell : CellId) (asset : AssetId) (amt : ℤ)

/-- **The per-asset ledger delta of a `FullActionA`, indexed by asset `b`.** Transfer and authority
are conservation-trivial (`0` for every asset); `mintA a` adds `amt` to asset `a` only; `burnA a`
subtracts from asset `a` only. A FAMILY indexed by `AssetId` — never one aggregate scalar. -/
def ledgerDeltaAsset : FullActionA → AssetId → ℤ
  | .balanceA _ _,     _ => 0
  | .delegate _ _ _,   _ => 0
  | .revoke _ _,       _ => 0
  | .mintA _ _ a amt,  b => if b = a then amt else 0
  | .burnA _ _ a amt,  b => if b = a then (-amt) else 0

/-- **The per-asset full executor.** Dispatch each kind to its chained per-asset primitive. ONE
executor over the per-asset op-set; the asset-typed analog of `execFull`. -/
def execFullA (s : RecChainedState) : FullActionA → Option RecChainedState
  | .balanceA t a           => recCexecAsset s t a
  | .delegate del rec t      => recCDelegate s del rec t
  | .revoke holder t         => some (recCRevoke s holder t)
  | .mintA actor cell a amt   => recCMintAsset s actor cell a amt
  | .burnA actor cell a amt   => recCBurnAsset s actor cell a amt

/-- **`execFullA_ledger_per_asset` — PROVED (the per-asset conservation vector).** Every committed
`FullActionA` moves `recTotalAsset b` by EXACTLY `ledgerDeltaAsset fa b`, for EVERY asset `b`
independently: `0` for transfer/authority (the moved asset cancels by
`recKExecAsset_conserves_per_asset`; authority leaves `bal` fixed), `±amt` at the targeted asset for
mint/burn, `0` at every other asset. THIS is the law a SCALAR kernel cannot state — it would let a
mint of asset B net against a burn of asset A. The per-asset family forbids that laundering. -/
theorem execFullA_ledger_per_asset (s s' : RecChainedState) (fa : FullActionA) (b : AssetId)
    (h : execFullA s fa = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset fa b := by
  cases fa with
  | balanceA t a =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCexecAsset at h
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' =>
          rw [hx] at h; simp only [Option.some.injEq] at h; subst h
          rw [recKExecAsset_conserves_per_asset s.kernel k' t a hx b]; ring
  | delegate del rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          -- `recKDelegate` commits ⟹ it returns `{s.kernel with caps := grant …}` — `bal`/`accounts` fixed.
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | revoke holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      -- `recKRevokeTarget` is `{s.kernel with caps := …}` — `bal`/`accounts` fixed.
      simp only [recTotalAsset, recKRevokeTarget]; ring
  | mintA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          exact recKMintAsset_delta s.kernel k' actor cell a amt hm b
  | burnA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCBurnAsset at h
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          exact recKBurnAsset_delta s.kernel k' actor cell a amt hb b

/-- **The per-asset full turn executor.** A transaction of `FullActionA`s, all-or-nothing. -/
def execFullTurnA (s : RecChainedState) : List FullActionA → Option RecChainedState
  | []        => some s
  | a :: rest =>
    match execFullA s a with
    | some s' => execFullTurnA s' rest
    | none    => none

/-- The net per-asset ledger delta of a turn, for asset `b`: the SUM of the per-action deltas. -/
def turnLedgerDeltaAsset (tt : List FullActionA) (b : AssetId) : ℤ :=
  (tt.map (fun fa => ledgerDeltaAsset fa b)).sum

/-- **`execFullTurnA_ledger_per_asset` — PROVED (the transaction conservation vector).** A committed
per-asset full-turn moves `recTotalAsset b` by exactly the net of all per-action deltas in asset `b`,
for EVERY asset `b`. Proved by induction on the turn, reusing `execFullA_ledger_per_asset`. The
asset-indexed analog of `execFullTurn_ledger`. -/
theorem execFullTurnA_ledger_per_asset :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId), execFullTurnA s tt = some s' →
      recTotalAsset s'.kernel b = recTotalAsset s.kernel b + turnLedgerDeltaAsset tt b
  | s, s', [], b, h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; simp [turnLedgerDeltaAsset]
  | s, s', a :: rest, b, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotalAsset s1.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset a b :=
            execFullA_ledger_per_asset s s1 a b ha
          have htail : recTotalAsset s'.kernel b = recTotalAsset s1.kernel b + turnLedgerDeltaAsset rest b :=
            execFullTurnA_ledger_per_asset s1 s' rest b h
          rw [htail, hhead]
          simp only [turnLedgerDeltaAsset, List.map_cons, List.sum_cons]; ring

/-- **`execFullTurnA_conserves_per_asset` — PROVED.** A committed per-asset full-turn whose net
ledger delta is `0` *in asset `b`* preserves asset `b`'s total supply. Applied with `∀ b, … = 0`
this gives FULL per-asset conservation: a transfer/authority-only turn (or one whose per-asset
mint/burn nets out in EACH asset) conserves EVERY asset class. The `CONSERVATION_VECTOR` at the
transaction level. -/
theorem execFullTurnA_conserves_per_asset (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId)
    (h : execFullTurnA s tt = some s') (hzero : turnLedgerDeltaAsset tt b = 0) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  rw [execFullTurnA_ledger_per_asset s s' tt b h, hzero, add_zero]

/-! ## §MB — `execFullTurnA_append` + the per-asset PER-NODE attestation carrier.

The forest lift in `Exec/FullForest.lean` rests on the same `execTurn_append` shape `TurnForest.lean`
uses for the narrow executor — here re-founded for the per-asset `execFullTurnA`. We then build the
per-asset analog of `fullActionInv` (`fullActionInvA`) whose **Ledger** conjunct is the full per-asset
VECTOR (`∀ b, recTotalAsset … = … + ledgerDeltaAsset fa b`, never one aggregate scalar — the FILL-1
no-laundering carrier), with ChainLink/ObsAdvance/KindObligation reused per-kind (these are
asset-orthogonal: they edit the log / `caps`, not the `bal` ledger). `execFullTurnA_each_attests`
then threads the per-node witness along the all-or-nothing fold, so the forest's per-node
attestation (`FullForest.execFullForestA_each_attests`) lifts straight off the bridge. -/

/-- **`execFullTurnA_append` — PROVED.** Running a concatenated per-asset turn equals running the
prefix and, on success, the suffix (the `execTurn_append` shape for `execFullTurnA`). The
associativity the forest pre-order flattening rests on. Mirrors `TurnForest.execTurn_append` verbatim
with `recCexec`→`execFullA`, induction on `xs`. -/
theorem execFullTurnA_append (s : RecChainedState) (xs ys : List FullActionA) :
    execFullTurnA s (xs ++ ys)
      = (match execFullTurnA s xs with
         | some s' => execFullTurnA s' ys
         | none    => none) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a rest ih =>
      show execFullTurnA s (a :: (rest ++ ys))
          = (match execFullTurnA s (a :: rest) with
             | some s' => execFullTurnA s' ys
             | none    => none)
      rw [show execFullTurnA s (a :: (rest ++ ys))
            = (match execFullA s a with
               | some s1 => execFullTurnA s1 (rest ++ ys)
               | none    => none) from rfl,
          show execFullTurnA s (a :: rest)
            = (match execFullA s a with
               | some s1 => execFullTurnA s1 rest
               | none    => none) from rfl]
      cases execFullA s a with
      | none    => rfl
      | some s1 => exact ih s1

/-- The receipt a committed `FullActionA` appends (newest-first): a per-asset transfer appends its
`turn`; authority appends its `authReceipt`; mint/burn append a self-`Turn` carrying the disclosed
per-asset supply delta. The per-asset analog of `fullReceipt`. -/
def fullReceiptA : FullActionA → Turn
  | .balanceA t _          => t
  | .delegate del _ _      => authReceipt del
  | .revoke holder _       => authReceipt holder
  | .mintA actor cell _ amt  => { actor := actor, src := cell, dst := cell, amt := amt }
  | .burnA actor cell _ amt  => { actor := actor, src := cell, dst := cell, amt := -amt }

/-- **`execFullA_chainlink` — PROVED.** A committed `FullActionA` extends the receipt chain by EXACTLY
its `fullReceiptA`, newest-first, with no fork or rewrite. The per-action generalization across the
per-asset op-set (asset-orthogonal: it touches only the `log`). -/
theorem execFullA_chainlink (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s'.log = fullReceiptA fa :: s.log := by
  cases fa with
  | balanceA t a =>
      simp only [execFullA, recCexecAsset, fullReceiptA] at h ⊢
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | delegate del rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | revoke holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset, fullReceiptA] at h ⊢
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset, fullReceiptA] at h ⊢
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' => rw [hb] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- **`execFullA_obsadvance` — PROVED.** A committed `FullActionA` grows the chain by exactly one
row, so a replayed action (which would re-append the same receipt) is detectable. -/
theorem execFullA_obsadvance (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s'.log.length = s.log.length + 1 := by
  rw [execFullA_chainlink s s' fa h]; simp

/-- **Per-asset balance authorized — PROVED.** A committed per-asset transfer was authorized
(`authorizedB` at the pre-state), via `recKExecAsset_authorized`. -/
theorem execFullA_balance_authorized (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execFullA s (.balanceA t a) = some s') : authorizedB s.kernel.caps t = true := by
  simp only [execFullA, recCexecAsset] at h
  cases hx : recKExecAsset s.kernel t a with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some k' => exact recKExecAsset_authorized s.kernel k' t a hx

/-- **Per-asset delegation grounds — PROVED.** A committed per-asset-turn delegation HOLDS the
Granovetter source edge `delegator ⟶ ⟨t,()⟩` on `execGraph` (REUSES the same `recCDelegate`/
`recKDelegate_grounds` the scalar executor does). -/
theorem execFullA_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Per-asset delegation IS `addEdge` — PROVED.** REUSES `recKDelegate_execGraph`. -/
theorem execFullA_delegate_addEdge (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps rec t
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **Per-asset revocation IS `removeEdge` — PROVED.** REUSES `recKRevokeTarget_execGraph`. -/
theorem execFullA_revoke_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.revoke holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **Per-asset mint authorized — PROVED.** A committed per-asset mint implies the privileged mint
authority (`recKMintAsset_authorized`). -/
theorem execFullA_mintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.mintA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a amt hm

/-- **`recKBurnAsset_authorized` — PROVED.** A committed per-asset burn implies the privileged mint
authority (the per-asset analog of `recKBurn_authorized`). -/
theorem recKBurnAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKBurnAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor cell = true := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn authorized — PROVED.** A committed per-asset burn implies the privileged mint
authority over `cell`. -/
theorem execFullA_burnA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.burnA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCBurnAsset] at h
  cases hb : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurnAsset_authorized s.kernel k' actor cell a amt hb

/-- **The per-`FullActionA` `StepInv`** — the per-asset analog of `fullActionInv`, true of every
committed per-asset action across all kinds. Its **Ledger** conjunct is the full per-asset VECTOR (a
`∀ b`, never an aggregate scalar — the FILL-1 carrier that forbids cross-asset laundering):
  * **Ledger (vector)** — for EVERY asset `b`, `recTotalAsset … b` moved by EXACTLY `ledgerDeltaAsset
    fa b` (`0` for transfer/authority, `±amt` at the targeted asset only for mint/burn);
  * **ChainLink** — the chain extends by exactly `fullReceiptA fa` (newest-first), no fork/rewrite;
  * **ObsAdvance** — the chain grew by exactly one row (replay-detectable);
  * **KindObligation** — the kind-specific integrity content (asset-orthogonal): balanceA ⇒
    `authorizedB`; delegate ⇒ grounds in the source edge AND edits the graph by `addEdge`; revoke ⇒
    `removeEdge`; mintA/burnA ⇒ `mintAuthorizedB` AND the Generative/Annihilative disclosure. -/
def fullActionInvA (s : RecChainedState) (fa : FullActionA) (s' : RecChainedState) : Prop :=
  -- Ledger: the per-asset conservation VECTOR (∀ b — never one aggregate scalar).
  (∀ b, recTotalAsset s'.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset fa b) ∧
  -- ChainLink: exactly the kind's receipt, newest-first.
  (s'.log = fullReceiptA fa :: s.log) ∧
  -- ObsAdvance: exactly one row.
  (s'.log.length = s.log.length + 1) ∧
  -- KindObligation: the kind-specific authority/graph/disclosure content (asset-orthogonal).
  (match fa with
   | .balanceA t _       => authorizedB s.kernel.caps t = true
   | .delegate del rec t =>
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩
   | .revoke holder t    =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .mintA actor cell _ _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   | .burnA actor cell _ _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity burnEffect).is_disclosed_non_conservation = true)

/-- **`execFullA_attests_per_asset` — THE PER-ASSET OP-SET IS STEP-COMPLETE BY CONSTRUCTION
(PROVED).** Every committed `FullActionA` attests its full `StepInv` content: the per-asset ledger
VECTOR ∧ ChainLink ∧ ObsAdvance ∧ the kind-specific obligation. The per-asset analog of
`execFull_attests`, carrying the conservation VECTOR (not the scalar). -/
theorem execFullA_attests_per_asset {s s' : RecChainedState} {fa : FullActionA}
    (h : execFullA s fa = some s') : fullActionInvA s fa s' := by
  refine ⟨fun b => execFullA_ledger_per_asset s s' fa b h,
          execFullA_chainlink s s' fa h, execFullA_obsadvance s s' fa h, ?_⟩
  cases fa with
  | balanceA t a => exact execFullA_balance_authorized s s' t a h
  | delegate del rec t =>
      exact ⟨execFullA_delegate_grounds s s' del rec t h, execFullA_delegate_addEdge s s' del rec t h⟩
  | revoke holder t => exact execFullA_revoke_removeEdge s s' holder t h
  | mintA actor cell a amt => exact ⟨execFullA_mintA_authorized s s' actor cell a amt h, mint_discloses⟩
  | burnA actor cell a amt => exact ⟨execFullA_burnA_authorized s s' actor cell a amt h, burn_discloses⟩

/-- **`execFullTurnA_each_attests` — PROVED.** Step-completeness holds at EVERY action of a committed
per-asset transaction, across all kinds: the per-node `fullActionInvA` witness threaded along the
all-or-nothing fold. The per-asset analog of `execFullTurn_each_attests` — the carrier the forest's
per-node attestation (`FullForest.execFullForestA_each_attests`) lifts off the bridge. -/
theorem execFullTurnA_each_attests :
    ∀ (s s' : RecChainedState) (tt : List FullActionA), execFullTurnA s tt = some s' →
      ∀ fa ∈ tt, ∃ sa sa', execFullA sa fa = some sa' ∧ fullActionInvA sa fa sa'
  | _, _, [], _, fa, hfa => absurd hfa List.not_mem_nil
  | s, s', a :: rest, h, b, hb => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          rcases List.mem_cons.mp hb with hbeq | hbrest
          · subst hbeq; exact ⟨s, s1, ha, execFullA_attests_per_asset ha⟩
          · exact execFullTurnA_each_attests s1 s' rest h b hbrest

/-! ## §11 — Axiom-hygiene tripwires (the honesty pins over the widened replacement's keystones). -/

#assert_axioms recKMint_delta
#assert_axioms recKBurn_delta
#assert_axioms recKMint_authorized
#assert_axioms recKBurn_authorized
#assert_axioms recKMint_unauthorized_fails
#assert_axioms recKBurn_unauthorized_fails
#assert_axioms mint_discloses
#assert_axioms burn_discloses
#assert_axioms execFull_ledger
#assert_axioms execFull_conserves
#assert_axioms execFull_balance_domain_conserves
#assert_axioms execFull_balance_authorized
#assert_axioms execFull_delegate_grounds
#assert_axioms execFull_mint_authorized
#assert_axioms execFull_burn_authorized
#assert_axioms execFull_delegate_addEdge
#assert_axioms execFull_revoke_removeEdge
#assert_axioms execFull_chainlink
#assert_axioms execFull_obsadvance
#assert_axioms execFull_attests
#assert_axioms execFullTurn_ledger
#assert_axioms execFullTurn_conserves
#assert_axioms execFullTurn_each_attests
-- The PER-ASSET conservation-vector keystones (FILL 1, phase 2) over the executable turn:
#assert_axioms recBalCredit_recTotalAsset
#assert_axioms recKMintAsset_delta
#assert_axioms recKBurnAsset_delta
#assert_axioms recKMintAsset_authorized
#assert_axioms execFullA_ledger_per_asset
#assert_axioms execFullTurnA_ledger_per_asset
#assert_axioms execFullTurnA_conserves_per_asset
-- The per-asset PER-NODE attestation carrier (the forest lift, §MB) keystones:
#assert_axioms execFullTurnA_append
#assert_axioms execFullA_chainlink
#assert_axioms execFullA_obsadvance
#assert_axioms execFullA_balance_authorized
#assert_axioms execFullA_delegate_grounds
#assert_axioms execFullA_delegate_addEdge
#assert_axioms execFullA_revoke_removeEdge
#assert_axioms execFullA_mintA_authorized
#assert_axioms recKBurnAsset_authorized
#assert_axioms execFullA_burnA_authorized
#assert_axioms execFullA_attests_per_asset
#assert_axioms execFullTurnA_each_attests

/-! ## §12 — Non-vacuity: each kind commits with the right invariant; unauthorized rejected.

Reuses `AuthTurn.rsCap` (delegator 0 holds a `node 7` cap) lifted to a `RecChainedState`, and a
minting state where actor 9 holds the privileged `node 0` cap. -/

/-- A chained record state: cells 0,1 with balances 100,5; actor 9 holds a `node 0` mint cap;
delegator 0 holds a `node 7` connectivity cap. Empty receipt chain. -/
def fs0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0]
                         else if l = 0 then [Cap.node 7] else [] }
    log := [] }

-- A DELEGATE turn commits (delegator 0 holds a `node 7` cap ⇒ can delegate connectivity to 7):
#eval (execFull fs0 (.delegate 0 1 7)).isSome                       -- true
-- ...is conservation-trivial (`recTotal` unchanged) and grows the chain by one:
#eval (execFull fs0 (.delegate 0 1 7)).map (fun s => recTotal s.kernel)  -- some 105 (FIXED)
#eval (execFull fs0 (.delegate 0 1 7)).map (fun s => s.log.length)       -- some 1
-- ...and recipient 1 now holds the `node 7` cap (the new authority edge):
#eval ((execFull fs0 (.delegate 0 1 7)).map (fun s => s.kernel.caps 1)).getD []  -- [Cap.node 7]
-- A delegator with no connectivity to the target cannot delegate it (fail-closed):
#eval (execFull fs0 (.delegate 5 1 9)).isSome                       -- false

-- A MINT turn commits (actor 9 holds the privileged `node 0` cap ⇒ may coin cell 0's supply):
#eval (execFull fs0 (.mint 9 0 50)).isSome                          -- true
-- ...raises `recTotal` by exactly +50 (disclosed non-conservation), chain grows by one:
#eval (execFull fs0 (.mint 9 0 50)).map (fun s => recTotal s.kernel)  -- some 155 (= 105 + 50)
#eval (execFull fs0 (.mint 9 0 50)).map (fun s => s.log.length)       -- some 1
-- ...and the minted receipt carries the disclosed delta +50:
#eval ((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0  -- 50
-- An actor without the privileged mint cap cannot mint (bare ownership is NOT enough):
#eval (execFull fs0 (.mint 0 0 50)).isSome                          -- false (actor 0 lacks `node 0`)

-- A BURN turn commits (actor 9 authorized; cell 0 has ≥ 40 balance):
#eval (execFull fs0 (.burn 9 0 40)).isSome                          -- true
-- ...lowers `recTotal` by exactly -40 (disclosed), chain grows by one:
#eval (execFull fs0 (.burn 9 0 40)).map (fun s => recTotal s.kernel)  -- some 65 (= 105 - 40)
-- Over-burn (more than available) is rejected (availability gate):
#eval (execFull fs0 (.burn 9 0 999)).isSome                         -- false
-- Unauthorized burn rejected:
#eval (execFull fs0 (.burn 0 0 10)).isSome                          -- false

-- A REVOKE turn always commits (it only subtracts authority) and is conservation-trivial:
#eval (execFull fs0 (.revoke 0 7)).isSome                           -- true
#eval (execFull fs0 (.revoke 0 7)).map (fun s => recTotal s.kernel)   -- some 105 (FIXED)
-- ...after which holder 0's `node 7` cap is gone:
#eval ((execFull fs0 (.revoke 0 7)).map (fun s => s.kernel.caps 0)).getD []  -- []

-- A BALANCE turn (reusing the catalog-typed `Action`) commits and conserves:
#eval (execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).isSome           -- true
#eval (execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).map (fun s => recTotal s.kernel)  -- some 105

-- A MIXED full-turn: mint +50, then transfer (conserves), then burn -50 → nets to 0, conserves.
def mixedTurn : List FullAction :=
  [ .mint 9 0 50
  , .balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩
  , .burn 9 0 50 ]

#eval (execFullTurn fs0 mixedTurn).isSome                           -- true (all-or-nothing commits)
#eval turnLedgerDelta mixedTurn                                     -- 0 (+50 +0 -50)
#eval (execFullTurn fs0 mixedTurn).map (fun s => recTotal s.kernel)   -- some 105 (CONSERVED: net 0)
#eval (execFullTurn fs0 mixedTurn).map (fun s => s.log.length)        -- some 3 (chain grew by count)

-- An all-or-nothing transaction with a bad action ROLLS BACK the whole turn:
def badMixedTurn : List FullAction :=
  [ .mint 9 0 50, .burn 0 0 10 ]   -- second action unauthorized ⇒ whole turn none
#eval (execFullTurn fs0 badMixedTurn).isSome                        -- false (rollback)

/-! ## §13 — Non-vacuity for the PER-ASSET executor: conservation holds, laundering is CAUGHT. -/

/-- A chained state with a genuine 2-asset `bal` ledger: cell 0 holds 100 of asset 0 and 7 of asset
1; cell 1 holds 5 of asset 0. Actor 9 holds the privileged `node 0` mint cap over cell 0. -/
def fma0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

#eval recTotalAsset fma0.kernel 0     -- 105 (asset 0 supply)
#eval recTotalAsset fma0.kernel 1     -- 7   (asset 1 supply)
-- A pure per-asset TRANSFER of asset 0 (actor 0 owns src 0) conserves BOTH assets:
#eval (execFullTurnA fma0 [.balanceA ⟨0, 0, 1, 30⟩ 0]).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))   -- some (105, 7)

/-- The scalar-LAUNDERING turn a single-aggregate kernel would WRONGLY accept as conserving: mint 50
of asset 1 while burning 50 of asset 0 (cell 0). Aggregate scalar delta = -50 + 50 = 0 ("conserved"
— the BUG). The per-asset VECTOR delta is nonzero in EACH asset, so it cannot be passed off as a
conservative turn. -/
def launderTurn : List FullActionA :=
  [ .mintA 9 0 1 50      -- +50 of asset 1
  , .burnA 9 0 0 50 ]    -- -50 of asset 0

#eval turnLedgerDeltaAsset launderTurn 0     -- -50 (NOT 0 — a scalar aggregate would hide this)
#eval turnLedgerDeltaAsset launderTurn 1     -- 50  (NOT 0)
-- the per-asset ledger AFTER the launder turn: asset 0 fell to 55, asset 1 rose to 57 (CAUGHT):
#eval (execFullTurnA fma0 launderTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))   -- some (55, 57)

end Dregg2.Exec.TurnExecutorFull
