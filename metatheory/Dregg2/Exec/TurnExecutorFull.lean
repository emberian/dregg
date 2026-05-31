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
import Dregg2.Exec.EffectsState

namespace Dregg2.Exec.TurnExecutorFull

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.CatalogEffects (Regime effectObligation)
open Dregg2.Spec (Domain conservedInDomain LinearityClass)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.Exec.EffectsState (setField fieldOf writeField stateAuthB stateStep stateStep_factors
  setField_balOf state_caps_unchanged state_authGraph_unchanged state_authorized state_obsadvance
  state_field_written)
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

/-! ### §MA-supply — ACCOUNT-GROWTH on the per-asset dispatch: `createCell` (born EMPTY) + `spawn`.

dregg1's `Effect::CreateCell` (`turn/src/executor/apply.rs:748`) is the PRIVILEGED creation of a FRESH
cell, born with `balance == 0` (`apply.rs:757` rejects `CreateCellNonZeroBalance`) — so on the per-asset
ledger it is conservation-NEUTRAL (`ledgerDeltaAsset = 0` for EVERY asset). `Effect::SpawnWithDelegation`
(`apply.rs` / `EffectsSupply.spawnStep`) is `createCell` PLUS a delegated cap to the spawned child
(`Cap.node target`); the create leg is neutral and the cap grant is bal-orthogonal, so spawn is neutral
too. We reuse the `EffectsSupply` GATE shape verbatim (`mintAuthorizedB` — creation is privileged supply —
AND the freshness gate `newCell ∉ accounts`), but found the growth on `RecordKernel.createCellIntoAsset`
(grow `accounts` + RESET the fresh `bal` column to `0`), so neutrality is PROVED via
`recTotalAsset_insert_fresh`, NOT assumed. -/

/-- **`createCellChainA` — `CreateCell`'s per-asset chained semantics.** Fail-closed: an authorized
creator (`mintAuthorizedB actor newCell` — creation coins a fresh cell, privileged like mint) AND a FRESH
id (`newCell ∉ accounts`, the exact `hfresh` the conservation lemma consumes). On commit, insert the fresh
cell (born EMPTY in every asset via `createCellIntoAsset`) and append the creation receipt (newest-first).
The dregg1-faithful born-`balance == 0`: NO amount param, conservation-NEUTRAL. -/
def createCellChainA (s : RecChainedState) (actor newCell : CellId) : Option RecChainedState :=
  if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts then
    some { kernel := createCellIntoAsset s.kernel newCell
           log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }
  else
    none

/-- **`createCellChainA` factors through its gate — PROVED.** A committed creation implies the two gate
conjuncts held and pins the post-state. -/
theorem createCellChainA_factors {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧
      s' = { kernel := createCellIntoAsset s.kernel newCell
             log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log } := by
  unfold createCellChainA at h
  by_cases hg : mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts
  · rw [if_pos hg, Option.some.injEq] at h; exact ⟨hg.1, hg.2, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`spawnChainA` — `SpawnWithDelegation`'s per-asset chained semantics.** Fail-closed via
`createCellChainA` (the authorized, fresh-id child, born EMPTY), and on commit ALSO grant the child a
delegated `Cap.node target` cap (the disclosed authority snapshot). The cap edit is bal-orthogonal — it
touches `caps`, never `bal`/`accounts` — so the per-asset measure is unmoved (neutral). Reuses the
`EffectsSupply.spawnStep` grant shape. -/
def spawnChainA (s : RecChainedState) (actor child target : CellId) : Option RecChainedState :=
  match createCellChainA s actor child with
  | some s1 =>
      some { s1 with kernel :=
        { s1.kernel with caps := fun l => if l = child then Cap.node target :: s1.kernel.caps l
                                          else s1.kernel.caps l } }
  | none => none

/-- **`spawnChainA` factors through `createCellChainA` — PROVED.** A committed spawn is a committed
`createCellChainA` (into `s1`) followed by the child-cap grant. -/
theorem spawnChainA_factors {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    ∃ s1, createCellChainA s actor child = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with caps := fun l => if l = child then Cap.node target :: s1.kernel.caps l
                                          else s1.kernel.caps l } } := by
  unfold spawnChainA at h
  cases hc : createCellChainA s actor child with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 => rw [hc] at h; simp only [Option.some.injEq] at h; exact ⟨s1, rfl, h.symm⟩

/-- **`createCellChainA_neutral` — ACCOUNT-GROWTH IS CONSERVATION-NEUTRAL (PROVED).** A committed
`createCellChainA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`: the index set `accounts`
genuinely GREW (`createCellChainA_grows_accounts`), but the fresh cell is born EMPTY (`bal`-reset), so its
contribution is exactly `0` (`recTotalAsset_insert_fresh`, with `hfresh` from the freshness gate). The
account-growth neutrality the per-asset dispatch demands. -/
theorem createCellChainA_neutral {s s' : RecChainedState} {actor newCell : CellId} (b : AssetId)
    (h : createCellChainA s actor newCell = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors h
  subst hs'
  exact recTotalAsset_insert_fresh s.kernel newCell b hfresh

/-- **`createCellChainA_grows_accounts` — the GROWTH has teeth (PROVED).** After a committed
`createCellChainA`, the new cell IS a live account (`newCell ∈ accounts`) — the index set genuinely grew,
so the neutrality theorem is NOT a no-op. -/
theorem createCellChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') : newCell ∈ s'.kernel.accounts := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'; exact createCellIntoAsset_grows_accounts s.kernel newCell

/-- **`createCellChainA_authorized` — PROVED (fail-closed integrity).** A committed creation implies the
creator held the privileged creation authority over the new cell (`mintAuthorizedB` — bare ownership is
NOT enough; creation coins a fresh cell). -/
theorem createCellChainA_authorized {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  (createCellChainA_factors h).1

/-- **`createCellChainA_unauthorized_fails` — PROVED (fail-closed).** Without creation authority, no cell
is minted. The confinement core. -/
theorem createCellChainA_unauthorized_fails (s : RecChainedState) (actor newCell : CellId)
    (h : mintAuthorizedB s.kernel.caps actor newCell = false) :
    createCellChainA s actor newCell = none := by
  unfold createCellChainA
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`createCellChainA_chainlink` — PROVED.** A committed creation extends the receipt chain by EXACTLY
the (balance-`0`) creation row, newest-first. -/
theorem createCellChainA_chainlink {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    s'.log = { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h; subst hs'; rfl

/-- The spawn cap grant is bal-orthogonal — it edits `caps`, never `bal`/`accounts` — so the per-asset
measure is literally unchanged (PROVED). The per-asset analog of `EffectsSupply.spawn_grant_recTotal`. -/
theorem spawnGrant_recTotalAsset (k : RecordKernelState) (child target : CellId) (b : AssetId) :
    recTotalAsset { k with caps := fun l => if l = child then Cap.node target :: k.caps l else k.caps l } b
      = recTotalAsset k b := rfl

/-- **`spawnChainA_neutral` — PROVED.** A committed spawn leaves `recTotalAsset` UNCHANGED for EVERY asset:
the create leg is neutral (born EMPTY), the cap grant is bal-orthogonal. -/
theorem spawnChainA_neutral {s s' : RecChainedState} {actor child target : CellId} (b : AssetId)
    (h : spawnChainA s actor child target = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨s1, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  rw [spawnGrant_recTotalAsset s1.kernel child target b]
  exact createCellChainA_neutral b hc

/-- **`spawnChainA_authorized` — PROVED.** A committed spawn implies the spawner held creation authority
over the child. -/
theorem spawnChainA_authorized {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    mintAuthorizedB s.kernel.caps actor child = true := by
  obtain ⟨s1, hc, _⟩ := spawnChainA_factors h
  exact createCellChainA_authorized hc

/-- **`spawnChainA_provenance` (the DISCLOSED-AUTHORITY keystone — PROVED).** The spawned child carries
EXACTLY the delegated snapshot cap `Cap.node target` at the head of its cap list (its disclosed authority
provenance). The generative resource is created with disclosed authority. -/
theorem spawnChainA_provenance {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    ∃ rest, s'.kernel.caps child = Cap.node target :: rest := by
  obtain ⟨s1, _, hs'⟩ := spawnChainA_factors h
  subst hs'
  exact ⟨s1.kernel.caps child, by simp⟩

/-- **`spawnChainA_chainlink` — PROVED.** A committed spawn extends the receipt chain by EXACTLY the
child's (balance-`0`) creation row (the cap grant edits only `caps`, not the log). -/
theorem spawnChainA_chainlink {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    s'.log = { actor := actor, src := child, dst := child, amt := 0 } :: s.log := by
  obtain ⟨s1, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  show s1.log = { actor := actor, src := child, dst := child, amt := 0 } :: s.log
  exact createCellChainA_chainlink hc

/-! ### §MA-state — the 5 PURE-STATE (field/log) effects on the per-asset dispatch.

dregg1's `turn/src/executor/apply.rs` runs FIVE effects that write the cell-RECORD (a named field)
or the LOG, and NEVER touch the per-asset `bal` ledger:

  * `SetField { cell, index, value }` (`apply_set_field` ~:497) — a state-slot write, gated by the
    `idx < STATE_SLOTS` bound + (for a cross-cell target) the `SetState` permission;
  * `EmitEvent { cell, event }` (`apply_emit_event` ~:703) — a journal append, gated ONLY by
    cell-existence (NO authority/cross-cell check — the integrity-free observation move);
  * `IncrementNonce { cell }` (`apply_increment_nonce` ~:719) — a monotone counter bump, gated by
    the `IncrementNonce` permission (cross-cell);
  * `SetPermissions { cell, new_permissions }` (`apply_set_permissions` ~:775) — the permission
    snapshot write, gated by the `SetPermissions` permission (dregg1 applies it LAST off the ORIGINAL
    permission snapshot — see the per-effect `stateAuthB` gate below);
  * `SetVerificationKey { cell, new_vk }` (`apply_set_verification_key` ~:803) — the VK-field write,
    gated by `SetVerificationKey` permission (the VK hash-integrity check is a §8 Prop-carrier
    portal, off this executable layer).

ALL FIVE carry `Effect::linearity ∈ {Neutral, Monotonic}` (`EffectsState §7`: `setField`/`emitEvent`/
`setPermissions`/`setVerificationKey` Neutral; `incrementNonce` Monotonic) — the NON-balance regime.
Their per-asset semantics are ALREADY proven in `Exec/EffectsState.lean` (`stateStep` + the
neutrality lemmas): the chained `stateStep` writes ONLY `kernel.cell` (a named field) + appends a
receipt, leaving `kernel.bal` and `kernel.accounts` literally untouched. So their `ledgerDeltaAsset`
is `0` for EVERY asset and `recTotalAsset` is UNCHANGED — balance-NEUTRALITY, proved (not assumed)
below. Here we WIRE those proven steps into the executed `execFullA` dispatch (we do NOT re-prove the
per-effect semantics). -/

/-- **Balance-NEUTRALITY of a field write over the per-asset ledger — PROVED (the load-bearing
keystone for the 5 pure-state effects).** `EffectsState.writeField` updates ONLY the record map
`cell` of the kernel; it touches NEITHER `bal` NOR `accounts`. So `recTotalAsset` (= `∑ c ∈
accounts, bal c b`) is LITERALLY UNCHANGED for EVERY asset `b`. THIS is what makes the 5 pure-state
effects per-asset conservation-trivial: a `nonce`/`status`/`permissions`/`vk` write cannot move ANY
asset's supply. (Contrast `recBalCredit_recTotalAsset`, which DOES move `bal` — these effects never
write `bal`.) -/
theorem writeField_recTotalAsset (k : RecordKernelState) (f : FieldName) (target : CellId)
    (v : Value) (b : AssetId) : recTotalAsset (writeField k f target v) b = recTotalAsset k b := by
  -- `writeField k f target v = { k with cell := … }`; `bal` and `accounts` are the SAME projections.
  rfl

/-- **Balance-NEUTRALITY of a committed `stateStep` over the per-asset ledger — PROVED.** A committed
`EffectsState.stateStep` (the chained field-write the 5 pure-state effects run) leaves `recTotalAsset
b` UNCHANGED for EVERY asset `b`: it writes a named record field, never the `bal` ledger. The
per-asset analog of `EffectsState.state_conserves` (which preserved the scalar `recTotal`); here it
holds for the asset VECTOR with NO side-condition on the field name (a write to ANY field, even
`balance`, leaves the `bal` ledger fixed — the `bal` ledger is independent of the `cell` record). -/
theorem stateStep_recTotalAsset {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'
  exact writeField_recTotalAsset s.kernel f target v b

/-- **The `EmitEvent` chained step — log-only, authority-FREE (dregg1 `apply_emit_event` ~:703).**
Unlike the field-writing effects, `EmitEvent` runs NO authority/cross-cell check (in dregg1 the only
gate is cell-existence) and writes NO state — it appends an event receipt to the chain and nothing
else. We model the observation faithfully: a self-`Turn` receipt (amount `0`) carrying the event,
with the kernel UNCHANGED (so `bal`/`cell`/`caps`/`accounts` are all fixed). The `topic`/`data`
ride the receipt's `src`/`dst` as the event payload markers. ALWAYS commits (no gate). -/
def emitStep (s : RecChainedState) (actor cell : CellId) (topic data : Int) : RecChainedState :=
  { kernel := s.kernel,
    log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }

/-- **`emitStep` is balance-NEUTRAL — PROVED.** `EmitEvent` leaves the kernel (hence `recTotalAsset
b` for EVERY asset `b`) UNCHANGED — it only appends a receipt. -/
theorem emitStep_recTotalAsset (s : RecChainedState) (actor cell : CellId) (topic data : Int)
    (b : AssetId) : recTotalAsset (emitStep s actor cell topic data).kernel b = recTotalAsset s.kernel b := rfl

/-- **`emitStep` advances the chain by exactly one row — PROVED** (the observation/replay clock). -/
theorem emitStep_obsadvance (s : RecChainedState) (actor cell : CellId) (topic data : Int) :
    (emitStep s actor cell topic data).log.length = s.log.length + 1 := by simp [emitStep]

/-- **The canonical field names the 4 field-writing pure-state effects target** (the metatheory's
named-field model of dregg1's `state.fields[index]` slot / `permissions` / `verification_key`). -/
def nonceField : FieldName := "nonce"
def permsField : FieldName := "permissions"
def vkField    : FieldName := "verification_key"

/-! ### §MA-auth — the 6 DISTINCT AUTHORITY effects on the per-asset dispatch.

dregg1's `turn/src/executor/apply.rs` runs a cluster of capability-graph effects BEYOND the bare
`delegate`/`revoke` already wired above. Each EDITS (or merely CHECKS) the `caps` cap-graph and
NEVER the `bal` ledger — so `ledgerDeltaAsset = 0` for EVERY asset and `recTotalAsset` is UNCHANGED
(balance-NEUTRAL). The HEADLINE obligation for this cluster is NON-AMPLIFICATION — the genuine
`capAuthConferred ⊆` over the REAL `List Auth` lattice (`attenuate_subset`), not a `()≤()` collapse.

  * `Introduce { introducer, recipient, target, permissions }` (`apply.rs:2791`, `:2835`
    "amplification denied") — the 3-party Granovetter introduce. Reuses the proven `recCDelegate`
    connectivity spine; the rights it confers are an ATTENUATION of a held cap (`attenuate_subset`).
  * `AttenuateCapability { cell, slot, narrower_permissions }` (`apply.rs:4377`) — monotonically
    NARROW a held cap in the actor's c-list (widening rejected). The purest non-amplification.
  * `DropRef { ref_id }` (`apply.rs:4034`) — a CapTP GC decrement: the holder drops its edge to the
    target. Reuses `recKRevokeTarget` (`removeEdge`); authority strictly shrinks.
  * `RevokeDelegation { child }` (`apply.rs:3044`) — a parent revokes a child's delegation. Reuses
    `recKRevokeTarget` (`removeEdge`). (Distinct dregg1 op from `DropRef`; same graph move.)
  * `ValidateHandoff { … }` (`apply.rs:4069`) — accept a two-signature CapTP handoff certificate.
    The handoff IS a Granovetter introduce, so the conferred (attenuated) cap is non-amplifying
    (`granted ⊆ held`, `attenuate_subset`). The two-signature crypto is a §8 Prop-carrier portal.
  * `ExerciseViaCapability { cap_slot, inner_effects }` (`apply.rs:2441`) — exercise a HELD cap. The
    cap graph is UNCHANGED (only connectivity begets connectivity); gated on holding the edge.

These REUSE the proofs of `Exec.EffectsAuthority` (which we cannot import — it sits DOWNSTREAM of
this module — so we re-found the two missing chained wrappers `attenuateStepA`/`exerciseStepA` here,
mirroring `recCDelegate`, and discharge the non-amplification directly from `Caps.attenuate_subset`,
the SAME proof `EffectsAuthority.attenuate_non_amplifying`/`introduce_non_amplifying` reuse). -/

/-- **`IsNonAmplifyingF held granted`** — the genuine non-amplification predicate over the REAL
rights lattice: the granted cap confers a `List Auth` SUBSET of the held cap's authority
(`is_attenuation(held, granted)`, `apply.rs:2835`). NOT a `()≤()` skeleton; an amplifying grant
(`granted ⊄ held`) makes it FALSE — the predicate has teeth (`amplifyingF_rejected`). The local twin
of `EffectsAuthority.IsNonAmplifying`. -/
def IsNonAmplifyingF (held granted : Cap) : Prop :=
  capAuthConferred granted ⊆ capAuthConferred held

/-- **`amplifyingF_rejected` — THE TEETH (PROVED).** A `granted` cap conferring an authority `a` the
`held` cap does NOT confer is REJECTED (`¬ IsNonAmplifyingF held granted`). So the non-amplification
gate genuinely discriminates — it is not vacuously true. -/
theorem amplifyingF_rejected (held granted : Cap) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted) (hheld : a ∉ capAuthConferred held) :
    ¬ IsNonAmplifyingF held granted := fun hsub => hheld (hsub hgranted)

/-- **`attenuateF_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The narrowed cap confers a
genuine `List Auth` SUBSET of the original: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred
c`, via `Caps.attenuate_subset`. This is the executable `is_narrower_or_equal` (widening denied) —
the SAME proof `EffectsAuthority.attenuate_non_amplifying`/`introduce_non_amplifying` carry. -/
theorem attenuateF_non_amplifying (keep : List Auth) (c : Cap) :
    IsNonAmplifyingF c (attenuate keep c) :=
  Dregg2.Exec.attenuate_subset keep c

/-- Narrow the actor's slot in-place: replace the `idx`-th cap of `actor` with its `keep`-attenuation
(other caps/slots untouched). The executable `attenuate_in_place` (`apply.rs:4377`). -/
def attenuateSlotF (caps : Caps) (actor : CellId) (idx : Nat) (keep : List Auth) : Caps :=
  fun l => if l = actor then (caps l).modify idx (attenuate keep) else caps l

/-- **Chained attenuate.** Narrow the actor's `idx`-th cap to `keep`, append an authority receipt.
Always commits (attenuation cannot fail — at worst the identity, still narrower-or-equal). Mirrors
`recCDelegate`'s receipt threading; the local twin of `EffectsAuthority.attenuateStep`. -/
def attenuateStepA (s : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) :
    RecChainedState :=
  { kernel := { s.kernel with caps := attenuateSlotF s.kernel.caps actor idx keep },
    log := authReceipt actor :: s.log }

/-- **Chained exercise.** Gate on the actor HOLDING an edge to `target` (the resolved c-list slot —
the SAME `confersEdgeTo` test `recKDelegate` uses), then append the receipt. The cap table is
UNCHANGED (exercising reads, never edits, the c-list). Fail-closed: no held edge ⇒ no exercise. The
local twin of `EffectsAuthority.exerciseStep`. -/
def exerciseStepA (s : RecChainedState) (actor target : CellId) : Option RecChainedState :=
  if (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true then
    some { s with log := authReceipt actor :: s.log }
  else
    none

theorem exerciseStepA_factors {s s' : RecChainedState} {actor target : CellId}
    (h : exerciseStepA s actor target = some s') :
    (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
      ∧ s' = { s with log := authReceipt actor :: s.log } := by
  unfold exerciseStepA at h
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §MA-escrow — the COMBINED PER-ASSET holding-store on the executed dispatch (`META-FILL C`).

dregg1's escrow/obligation/committed-escrow are NOT balance-conserving two-cell transfers: they DEBIT
ONE cell and park the value in an off-ledger side-table, conserving only the COMBINED total across the
create+settle PAIR (`RecordKernel §ESCROW`). On the per-asset `bal` ledger this is
`RecordKernel.createEscrowKAsset`/`releaseEscrowKAsset`/`refundEscrowKAsset`, which conserve the
COMBINED per-asset measure `recTotalAssetWithEscrow`. We re-found their CHAINED wrappers HERE (mirroring
`attenuateStepA`/`exerciseStepA`, since `EffectsPaired` sits parallel and is not imported), and wire
them into the executed `execFullA` dispatch. The escrow legs move the BARE `recTotalAsset` by ∓amount at
the locked asset (`ledgerDeltaAsset`), but conserve the COMBINED measure (`combinedDeltaAsset = 0`).
Note effects move SETS (nullifier/commitment), not `bal`, so both deltas are `0`. -/

/-- The escrow receipt (a self-`Turn` on the actor, amount `0` — the metadata clock row; the parked
amount/asset live in the off-ledger record, not the receipt). -/
def escrowReceiptA (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-- **Chained per-asset escrow create.** Run `RecordKernel.createEscrowKAsset` (single-cell, single-asset
debit at `asset` + park the asset-typed record), and on success extend the receipt chain. -/
def createEscrowChainA (s : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecChainedState :=
  match createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset escrow release** (single-cell credit to the recipient at the record's asset). -/
def releaseEscrowChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match releaseEscrowKAsset s.kernel id with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset escrow refund** (single-cell credit back to the creator at the record's asset). -/
def refundEscrowChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match refundEscrowKAsset s.kernel id with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained note-create** — grow the commitment SET (the §8 range-proof portal is the THEOREM-level
hypothesis, like bridgeMint's foreign finality; the ledger move is the grow-only insert). Always
commits at the ledger layer (a fresh commitment cannot conflict). -/
def noteCreateChainA (s : RecChainedState) (cm : Nat) (actor : CellId) : RecChainedState :=
  { kernel := noteCreateCommitment s.kernel cm, log := escrowReceiptA actor :: s.log }

/-- **Chained note-spend** — the ledger-side double-spend gate (`noteSpendNullifier`, fail-closed on a
repeated nullifier). The §8 STARK spending proof is the THEOREM-level portal. -/
def noteSpendChainA (s : RecChainedState) (nf : Nat) (actor : CellId) : Option RecChainedState :=
  match noteSpendNullifier s.kernel nf with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-! ### §MA-bridge — the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store
(Wave-5 `PHASE-BRIDGE`). The chained wrappers over `RecordKernel`'s `bridgeLockKAsset` (≈ escrow-create,
combined-conserving), `bridgeFinalizeKAsset` (a no-credit resolve — the value LEFT for the other chain,
COMBINED DROPS by the bridged amount, a disclosed OUTFLOW like burn) and `bridgeCancelKAsset` (≈
escrow-refund, combined-conserving). bridgeMint (the inbound side) was already wired (reuses
`recCMintAsset`). The §8 confirmation receipt (the destination signature) is the THEOREM-level portal,
exactly as bridgeMint's foreign finality. -/

/-- **Chained per-asset bridge LOCK.** Run `RecordKernel.bridgeLockKAsset` (single-cell, single-asset
debit at `asset` + park the bridge-tagged record), and on success extend the receipt chain. -/
def bridgeLockChainA (s : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecChainedState :=
  match bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset bridge FINALIZE** (the §8 confirmation arrived — the no-credit resolve; the
value LEFT for the other chain, COMBINED measure DROPS by the DISCLOSED bridged `(asset, amount)`; the
executor gates on the parked record matching). -/
def bridgeFinalizeChainA (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId) (amount : ℤ) :
    Option RecChainedState :=
  match bridgeFinalizeKAsset s.kernel id asset amount with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset bridge CANCEL** (timeout/failure — single-cell credit back to the originator at
the record's asset; combined CONSERVED). -/
def bridgeCancelChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match bridgeCancelKAsset s.kernel id with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **`bridgeLockChainA_combined_neutral` — PROVED.** A committed bridge lock conserves the COMBINED
per-asset measure at EVERY asset `b` (the bal debit at `asset` is offset by the holding-store rise).
Reads off `RecordKernel.bridge_lock_conserves_combined_per_asset`. -/
theorem bridgeLockChainA_combined_neutral {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact bridge_lock_conserves_combined_per_asset b hc

/-- **`bridgeLockChainA_bal_debits` — PROVED.** A committed bridge lock DROPS the BARE per-asset ledger
`recTotalAsset asset` by `amount` (a real per-asset debit — the value is now INACCESSIBLE in the lock,
awaiting the other chain). -/
theorem bridgeLockChainA_bal_debits {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    recTotalAsset s'.kernel asset = recTotalAsset s.kernel asset - amount := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact (bridge_lock_debits_per_asset hc).1

/-- **`bridgeFinalizeChainA_burns_combined` — THE BRIDGE HEADLINE (PROVED).** A committed bridge finalize
MOVES the COMBINED per-asset measure DOWN by EXACTLY the DISCLOSED `amount` at the disclosed `asset`
(`b = asset`), leaving every OTHER asset LITERALLY FIXED — the value genuinely LEFT for the other chain.
Reads off `RecordKernel.bridgeFinalizeKAsset_moves_combined_per_asset`. NON-VACUOUS: the drop is a
per-asset DISCLOSED OUTFLOW guarded by `b = asset` (no cross-asset laundering at the bridge boundary). -/
theorem bridgeFinalizeChainA_burns_combined {s s' : RecChainedState} {id : Nat} {actor : CellId}
    {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeFinalizeChainA s id actor asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0) := by
  unfold bridgeFinalizeChainA at h
  cases hc : bridgeFinalizeKAsset s.kernel id asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact bridgeFinalizeKAsset_moves_combined_per_asset b hc

/-- **`bridgeCancelChainA_combined_neutral` — PROVED (the refund round-trip).** A committed bridge cancel
conserves the COMBINED per-asset measure at EVERY asset (value returns to the LIVE, gate-checked
originator). Reads off `RecordKernel.bridge_cancel_conserves_combined_per_asset`. -/
theorem bridgeCancelChainA_combined_neutral {s s' : RecChainedState} {id : Nat} {actor : CellId}
    (b : AssetId) (h : bridgeCancelChainA s id actor = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold bridgeCancelChainA at h
  cases hc : bridgeCancelKAsset s.kernel id with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact bridge_cancel_conserves_combined_per_asset b hc

/-- **`bridgeLockChainA_authorized` — PROVED.** A committed bridge lock required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`). -/
theorem bridgeLockChainA_authorized {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' => exact bridgeLockKAsset_authorized hc

/-- **`createEscrowChainA_combined_neutral` — PROVED.** A committed per-asset escrow create conserves
the COMBINED per-asset measure at EVERY asset `b` (the bal debit at `asset` is offset by the
holding-store rise). Reads off `RecordKernel.escrow_create_conserves_combined_per_asset`. -/
theorem createEscrowChainA_combined_neutral {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_create_conserves_combined_per_asset b hc

/-- **`createEscrowChainA_bal_debits` — PROVED.** A committed per-asset escrow create DROPS the BARE
per-asset ledger `recTotalAsset asset` by `amount` (a real per-asset debit) — the bare-bal delta the
`ledgerDeltaAsset` arm discloses (combined-conserving, bare-debiting). -/
theorem createEscrowChainA_bal_debits {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAsset s'.kernel asset = recTotalAsset s.kernel asset - amount := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact (escrow_create_debits_per_asset hc).1

/-- The bare-bal per-asset delta of a committed escrow create, for an arbitrary asset `b`: `−amount` at
`asset`, `0` elsewhere. (The other-asset legs of `createEscrowKAsset` are frame-untouched.) PROVED. -/
theorem createEscrowChainA_bal_delta {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = asset then (-amount) else 0) := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      unfold createEscrowKAsset at hc
      by_cases hg : authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
          ∧ 0 ≤ amount ∧ amount ≤ s.kernel.bal creator asset ∧ creator ∈ s.kernel.accounts
          ∧ ¬ (∃ r ∈ s.kernel.escrows, r.id = id)
      · rw [if_pos hg] at hc; simp only [Option.some.injEq] at hc; subst hc
        obtain ⟨_, _, _, hlive, _⟩ := hg
        show (∑ x ∈ s.kernel.accounts, recBalCreditCell s.kernel.bal creator asset (-amount) x b) = _
        have := recBalCreditCell_recTotalAsset s.kernel.accounts s.kernel.bal creator asset (-amount) hlive b
        simpa [recTotalAsset] using this
      · rw [if_neg hg] at hc; exact absurd hc (by simp)

/-- The FULL per-asset op-set, as one sum (`META-FILL A`/`B`/`C`). The asset-typed analog of
`FullAction`. -/
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
  -- §MA-state: the 5 PURE-STATE (field/log) effects — they write the `cell` record or the LOG,
  -- NEVER the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset (balance-NEUTRAL).
  /-- `SetField { cell, index→field, value }` (dregg1 `apply_set_field`): write `actor`-authorized
  cell `cell`'s named state field `field` to `v`. Authority: `actor` holds authority over `cell`. -/
  | setFieldA       (actor cell : CellId) (field : FieldName) (v : Int)
  /-- `EmitEvent { cell, event }` (dregg1 `apply_emit_event`): append an event receipt. NO state
  write, NO authority gate (dregg1's only gate is cell-existence). -/
  | emitEventA      (actor cell : CellId) (topic data : Int)
  /-- `IncrementNonce { cell }` (dregg1 `apply_increment_nonce`): monotone nonce bump. The bumped
  counter value `newNonce` is written to the `nonce` field; `actor` holds authority over `cell`. -/
  | incrementNonceA (actor cell : CellId) (newNonce : Int)
  /-- `SetPermissions { cell, new_permissions }` (dregg1 `apply_set_permissions`, applied LAST off
  the ORIGINAL permission snapshot): write the `permissions` field to `perms`; `actor` holds
  authority over `cell`. -/
  | setPermissionsA (actor cell : CellId) (perms : Int)
  /-- `SetVerificationKey { cell, new_vk }` (dregg1 `apply_set_verification_key`): write the
  `verification_key` field to `vk`; `actor` holds authority over `cell` (the VK hash-integrity check
  is the §8 Prop-carrier portal, off this executable layer). -/
  | setVKA          (actor cell : CellId) (vk : Int)
  -- §MA-auth: the 6 DISTINCT AUTHORITY effects — they EDIT (or CHECK) the `caps` cap-graph, NEVER
  -- the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset (balance-NEUTRAL). The HEADLINE
  -- obligation is NON-AMPLIFICATION (genuine `capAuthConferred ⊆` / `removeEdge ⊆` / `addEdge`).
  /-- `Introduce { introducer, recipient, target }` (dregg1 `apply_introduce`, `apply.rs:2791`): the
  3-party Granovetter introduce. `introducer` (holding connectivity to `target`) hands `recipient` a
  NON-AMPLIFYING edge to `target`. Reuses the `recCDelegate` connectivity spine. -/
  | introduceA      (introducer recipient target : CellId)
  /-- `AttenuateCapability { cell→actor, slot→idx, narrower_permissions→keep }` (dregg1
  `apply_attenuate_capability`, `apply.rs:4377`): monotonically NARROW the actor's `idx`-th held cap
  to `keep` (widening rejected). The purest non-amplification (`capAuthConferred ⊆`). -/
  | attenuateA      (actor : CellId) (idx : Nat) (keep : List Auth)
  /-- `DropRef { ref_id }` (dregg1 `apply_drop_ref`, `apply.rs:4034`): a CapTP GC decrement — the
  `holder` drops its edge to `target`. Reuses `recKRevokeTarget` (`removeEdge`); authority shrinks. -/
  | dropRefA        (holder target : CellId)
  /-- `RevokeDelegation { child→holder }` (dregg1 `apply_revoke_delegation`, `apply.rs:3044`): a
  parent revokes a child's delegation — the `holder` loses its edge to `target`. Reuses
  `recKRevokeTarget` (`removeEdge`). A DISTINCT dregg1 op from `DropRef` (parent-revocation vs.
  holder-GC), sharing the graph move. -/
  | revokeDelegationA (holder target : CellId)
  /-- `ValidateHandoff { … }` (dregg1 `apply_validate_handoff`, `apply.rs:4069`): accept a
  two-signature CapTP handoff certificate. The handoff IS a Granovetter introduce — so it runs the
  `recCDelegate` connectivity spine and the conferred (attenuated) cap is non-amplifying
  (`granted ⊆ held`). The two-signature crypto is the §8 Prop-carrier portal. -/
  | validateHandoffA (introducer recipient target : CellId)
  /-- `ExerciseViaCapability { cap_slot→target }` (dregg1 `apply_exercise_via_capability`,
  `apply.rs:2441`): exercise a HELD cap. The cap graph is UNCHANGED (only connectivity begets
  connectivity); gated on `actor` HOLDING the edge to `target`. -/
  | exerciseA       (actor target : CellId)
  -- §MA-supply: the 3 ACCOUNT-GROWTH / SUPPLY effects (`META-FILL C`). createCell/spawn GROW
  -- `accounts` (born EMPTY ⇒ conservation-NEUTRAL, `ledgerDeltaAsset = 0`); bridgeMint is the §8
  -- PORTAL inflow (disclosed `+value` at ONE asset).
  /-- `CreateCell { public_key, token_id, balance }` (dregg1 `apply_create_cell`, `apply.rs:748`):
  PRIVILEGED creation of a FRESH live cell, born `balance == 0` (`apply.rs:757` rejects
  `CreateCellNonZeroBalance`) — born EMPTY in every asset, so conservation-NEUTRAL. NO amount param
  (the dregg1-faithful choice); authority: `mintAuthorizedB actor newCell` + the freshness gate. -/
  | createCellA     (actor newCell : CellId)
  /-- `SpawnWithDelegation { … }` (dregg1 `apply_spawn_with_delegation`): `createCell` (born EMPTY) PLUS
  a delegated `Cap.node target` cap to the spawned child — the disclosed authority snapshot. The create
  leg is neutral; the cap grant is bal-orthogonal, so spawn is conservation-NEUTRAL too. -/
  | spawnA          (actor child target : CellId)
  /-- `BridgeMint { cell, value, asset_type, nullifier }` (dregg1 `apply_bridge_mint`, `apply.rs:1106`):
  the §8 PORTAL inflow — credit `cell`'s asset `asset` by a disclosed `value` observed off a FOREIGN
  chain. GENERATIVE (disclosed `+value` at asset `asset` ONLY). dregg2 cannot verify foreign consensus,
  so foreign finality is the §8 `Prop` carrier (off this executable layer); the LOCAL credit reuses the
  per-asset mint `recCMintAsset` verbatim. -/
  | bridgeMintA     (actor cell : CellId) (asset : AssetId) (value : ℤ)
  -- §MA-escrow: the off-ledger holding-store + commitment/nullifier SET effects (`META-FILL C`,
  -- closing `#121`). escrow/obligation/committed-escrow DEBIT one cell at one asset and PARK the value
  -- (combined per-asset conserving, bare-bal debiting); notes move the nullifier/commitment SET (not
  -- `bal`). The §8 crypto (committed-escrow opening, note range/spending proofs) is the THEOREM-level
  -- portal (off this executable layer, exactly as bridgeMint's foreign finality).
  /-- `CreateEscrow { id, creator, recipient, asset, amount }` (dregg1 `apply_create_escrow`): lock
  `amount` of `asset` from `creator` into the off-ledger holding-store (single-cell debit + parked
  record). Combined per-asset conserving; bare per-asset ledger DEBITED at `asset`. -/
  | createEscrowA   (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
  /-- `ReleaseEscrow { id }` (dregg1 `apply_release_escrow`): credit the recipient at the record's asset
  + mark resolved. Combined per-asset conserving. -/
  | releaseEscrowA  (id : Nat) (actor : CellId)
  /-- `RefundEscrow { id }` (dregg1 `apply_refund_escrow`): credit the creator (refund target) + mark
  resolved. Combined per-asset conserving. -/
  | refundEscrowA   (id : Nat) (actor : CellId)
  /-- `CreateObligation { id, obligor, beneficiary, stake }` (dregg1 `apply_create_obligation`): the
  SAME holding-store as escrow (single-cell stake debit + parked record). Dispatch-ALIASED to
  `createEscrowA` (obligor=creator, beneficiary=recipient, stake=amount). -/
  | createObligationA (id : Nat) (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
  /-- `NoteSpend { nullifier }` (dregg1 `apply_note_spend`): the nullifier-SET insert with double-spend
  rejection (the ledger anti-replay gate). The §8 STARK spending proof is the THEOREM-level portal.
  bal-NEUTRAL. -/
  | noteSpendA      (nf : Nat) (actor : CellId)
  /-- `NoteCreate { commitment }` (dregg1 `apply_note_create`): the grow-only commitment-SET insert (the
  dual of noteSpend). The §8 range proof is the THEOREM-level portal. bal-NEUTRAL. -/
  | noteCreateA     (cm : Nat) (actor : CellId)
  /-- `CreateCommittedEscrow { id, …, asset, amount }` (`#121`): a PRIVACY escrow whose amount is hidden
  behind a Pedersen commitment (the record `id` is the commitment key). The lock automaton is identical
  to plain escrow, so it inherits the per-asset combined-conservation; the opening predicate is the §8
  THEOREM-level portal. -/
  | createCommittedEscrowA (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
  /-- `ReleaseCommittedEscrow { id }` (`#121`): portal-gated release of a committed escrow. -/
  | releaseCommittedEscrowA (id : Nat) (actor : CellId)
  /-- `RefundCommittedEscrow { id }` (`#121`): portal-gated refund of a committed escrow. -/
  | refundCommittedEscrowA  (id : Nat) (actor : CellId)
  -- §MA-bridge: the cross-chain two-phase bridge (Wave-5 `PHASE-BRIDGE`) on the SHARED escrow
  -- holding-store (a `bridge := true`-tagged record). bridgeMint (the INBOUND side) is already done
  -- (`bridgeMintA`, above — reuses `recCMintAsset`). These are the OUTBOUND legs:
  /-- `BridgeLock { nullifier, destination, value, asset_type, timeout_height, spending_proof }`
  (dregg1 `apply_bridge_lock`, `cell/src/note_bridge.rs::initiate_bridge`): lock `amount` of `asset`
  from `originator` into the off-ledger holding-store — value INACCESSIBLE, AWAITING the other-chain
  confirmation (single-cell debit + parked bridge-tagged record). Combined per-asset CONSERVING; bare
  per-asset ledger DEBITED at `asset` (≈ escrow create). The §8 spending proof is the THEOREM-level
  portal. -/
  | bridgeLockA     (id : Nat) (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
  /-- `BridgeFinalize { nullifier, receipt }` (dregg1 `apply_bridge_finalize`,
  `cell/src/note_bridge.rs::finalize_bridge`): the §8 confirmation receipt arrived (the
  destination-federation signature — `verify_bridge_receipt`, the §8 portal); the lock RESOLVES and the
  value LEAVES for the other chain — a BURN on this side (no credit). COMBINED per-asset measure DROPS by
  the bridged amount (a disclosed OUTFLOW). The ONE holding-store resolution that does NOT conserve, and
  honestly so. The receipt DISCLOSES the bridged `(asset, amount)` — carried on the action so the
  per-asset conservation VECTOR can state the `-amount` move at `asset`; the executor gates on the parked
  record's `(asset, amount)` MATCHING the disclosed pair (fail-closed otherwise, exactly as dregg1's
  finalize checks the receipt against the pending bridge). -/
  | bridgeFinalizeA (id : Nat) (actor : CellId) (asset : AssetId) (amount : ℤ)
  /-- `BridgeCancel { nullifier }` (dregg1 `apply_bridge_cancel`,
  `cell/src/note_bridge.rs::cancel_bridge`): the timeout was reached without a receipt; the note is
  UNLOCKED and the value REFUNDED to the originator (single-cell credit + resolve). COMBINED per-asset
  CONSERVING (≈ escrow refund). The timeout gate is carried at the theorem layer. -/
  | bridgeCancelA   (id : Nat) (actor : CellId)

/-- **The per-asset COMBINED ledger delta of a `FullActionA`, indexed by asset `b`** — the move of the
COMBINED measure `recTotalAssetWithEscrow` (= `bal`-ledger + per-asset holding-store). Transfer and
authority are conservation-trivial (`0` for every asset); `mintA a` adds `amt` to asset `a` only;
`burnA a` subtracts from asset `a` only. The 5 PURE-STATE effects write the `cell` record / the LOG,
never `bal` — so `0`. The escrow/obligation/committed-escrow legs DEBIT the bare `bal` ledger by
∓amount at the locked asset BUT park exactly that into the per-asset holding-store, so their COMBINED
delta is `0` (combined-conserving, even though the bare ledger genuinely moves — that bare debit is
witnessed by `createEscrowChainA_bal_debits`). Notes move the nullifier/commitment SET, not `bal`, so
`0`. A FAMILY indexed by `AssetId` — never one aggregate scalar. -/
def ledgerDeltaAsset : FullActionA → AssetId → ℤ
  | .balanceA _ _,        _ => 0
  | .delegate _ _ _,      _ => 0
  | .revoke _ _,          _ => 0
  | .mintA _ _ a amt,     b => if b = a then amt else 0
  | .burnA _ _ a amt,     b => if b = a then (-amt) else 0
  | .setFieldA _ _ _ _,   _ => 0
  | .emitEventA _ _ _ _,  _ => 0
  | .incrementNonceA _ _ _, _ => 0
  | .setPermissionsA _ _ _, _ => 0
  | .setVKA _ _ _,        _ => 0
  -- §MA-auth: the 6 authority effects EDIT/CHECK `caps`, NEVER `bal` — so `0` for EVERY asset.
  | .introduceA _ _ _,    _ => 0
  | .attenuateA _ _ _,    _ => 0
  | .dropRefA _ _,        _ => 0
  | .revokeDelegationA _ _, _ => 0
  | .validateHandoffA _ _ _, _ => 0
  | .exerciseA _ _,       _ => 0
  -- §MA-supply: createCell/spawn GROW `accounts` but the fresh cell is born EMPTY (bal-reset) — so `0`
  -- for EVERY asset (account-growth NEUTRALITY). bridgeMint discloses `+value` at the targeted asset ONLY.
  | .createCellA _ _,     _ => 0
  | .spawnA _ _ _,        _ => 0
  | .bridgeMintA _ _ a value, b => if b = a then value else 0
  -- §MA-escrow: escrow/obligation/committed-escrow are COMBINED-conserving (bal debit offset by the
  -- holding-store park), so their COMBINED delta is `0`; notes move SETs, not `bal`, so `0`.
  | .createEscrowA _ _ _ _ _ _,   _ => 0
  | .releaseEscrowA _ _,          _ => 0
  | .refundEscrowA _ _,           _ => 0
  | .createObligationA _ _ _ _ _ _, _ => 0
  | .noteSpendA _ _,              _ => 0
  | .noteCreateA _ _,             _ => 0
  | .createCommittedEscrowA _ _ _ _ _ _, _ => 0
  | .releaseCommittedEscrowA _ _, _ => 0
  | .refundCommittedEscrowA _ _,  _ => 0
  -- §MA-bridge: LOCK is COMBINED-conserving (bal debit offset by the holding-store park), so its COMBINED
  -- delta is `0`; CANCEL refunds the originator (combined fixed), so `0`; FINALIZE is the ONE disclosed
  -- OUTFLOW — the value LEFT for the other chain, so the COMBINED measure DROPS by the DISCLOSED `amount`
  -- at the disclosed `asset` ONLY (like burn, `-amount`), every other asset fixed.
  | .bridgeLockA _ _ _ _ _ _,     _ => 0
  | .bridgeFinalizeA _ _ a amount, b => if b = a then (-amount) else 0
  | .bridgeCancelA _ _,           _ => 0

/-- **The per-asset full executor.** Dispatch each kind to its chained per-asset primitive. ONE
executor over the per-asset op-set; the asset-typed analog of `execFull`. The 5 pure-state effects
route to `EffectsState.stateStep` (the authority-gated field write — `setFieldA`/`incrementNonceA`/
`setPermissionsA`/`setVKA`) or to `emitStep` (the authority-free log append — `emitEventA`), the
ALREADY-PROVEN per-effect steps. -/
def execFullA (s : RecChainedState) : FullActionA → Option RecChainedState
  | .balanceA t a           => recCexecAsset s t a
  | .delegate del rec t      => recCDelegate s del rec t
  | .revoke holder t         => some (recCRevoke s holder t)
  | .mintA actor cell a amt   => recCMintAsset s actor cell a amt
  | .burnA actor cell a amt   => recCBurnAsset s actor cell a amt
  | .setFieldA actor cell f v        => stateStep s f actor cell (.int v)
  | .emitEventA actor cell topic data => some (emitStep s actor cell topic data)
  | .incrementNonceA actor cell n     => stateStep s nonceField actor cell (.int n)
  | .setPermissionsA actor cell p     => stateStep s permsField actor cell (.int p)
  | .setVKA actor cell vk             => stateStep s vkField actor cell (.int vk)
  -- §MA-auth: the 6 authority effects route to the (reused/re-founded) chained authority steps.
  | .introduceA intro rec t          => recCDelegate s intro rec t
  | .attenuateA actor idx keep       => some (attenuateStepA s actor idx keep)
  | .dropRefA holder t               => some (recCRevoke s holder t)
  | .revokeDelegationA holder t      => some (recCRevoke s holder t)
  | .validateHandoffA intro rec t    => recCDelegate s intro rec t
  | .exerciseA actor t               => exerciseStepA s actor t
  -- §MA-supply: createCell/spawn route to the account-growth chained steps (born EMPTY); bridgeMint
  -- reuses the per-asset mint `recCMintAsset` verbatim (the §8 portal hypothesis is carried on the
  -- conservation keystone, not checked here).
  | .createCellA actor newCell       => createCellChainA s actor newCell
  | .spawnA actor child target       => spawnChainA s actor child target
  | .bridgeMintA actor cell a value  => recCMintAsset s actor cell a value
  -- §MA-escrow: escrow/obligation/committed route to the chained per-asset holding-store steps;
  -- obligation/committed are dispatch-ALIASED to the escrow steps (same automaton, §8 portal at the
  -- theorem layer). Notes route to the SET-insert steps.
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowChainA s id actor creator recipient asset amount
  | .releaseEscrowA id actor          => releaseEscrowChainA s id actor
  | .refundEscrowA id actor           => refundEscrowChainA s id actor
  | .createObligationA id actor obligor beneficiary asset stake =>
      createEscrowChainA s id actor obligor beneficiary asset stake
  | .noteSpendA nf actor              => noteSpendChainA s nf actor
  | .noteCreateA cm actor             => some (noteCreateChainA s cm actor)
  | .createCommittedEscrowA id actor creator recipient asset amount =>
      createEscrowChainA s id actor creator recipient asset amount
  | .releaseCommittedEscrowA id actor => releaseEscrowChainA s id actor
  | .refundCommittedEscrowA id actor  => refundEscrowChainA s id actor
  -- §MA-bridge: lock/finalize/cancel route to the chained per-asset bridge steps over the SHARED escrow
  -- holding-store. bridgeMint (the inbound side) routes to `recCMintAsset` (already done, above).
  | .bridgeLockA id actor originator destination asset amount =>
      bridgeLockChainA s id actor originator destination asset amount
  | .bridgeFinalizeA id actor asset amount => bridgeFinalizeChainA s id actor asset amount
  | .bridgeCancelA id actor                => bridgeCancelChainA s id actor

/-- **`execFullA_ledger_per_asset` — PROVED (the COMBINED per-asset conservation VECTOR).** Every
committed `FullActionA` moves the COMBINED per-asset measure `recTotalAssetWithEscrow b` (= `bal`-ledger
+ per-asset holding-store) by EXACTLY `ledgerDeltaAsset fa b`, for EVERY asset `b` independently: `0`
for transfer/authority (the moved asset cancels; authority/notes leave `bal` AND `escrows` fixed), `±amt`
at the targeted asset for mint/burn/bridge (escrows fixed ⇒ combined = bare-bal), and `0` for the
escrow/obligation/committed-escrow legs — they DEBIT the bare `bal` by ∓amount but PARK exactly that into
the per-asset holding-store, so the COMBINED measure is fixed (combined-conserving). THIS is the law a
SCALAR kernel cannot state — it would let a mint of asset B net against a burn of asset A, or an escrow
of asset A launder into asset B. The per-asset COMBINED family forbids both. -/
theorem execFullA_ledger_per_asset (s s' : RecChainedState) (fa : FullActionA) (b : AssetId)
    (h : execFullA s fa = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset fa b := by
  -- For the NON-holding-store kinds, the post-state leaves `escrows` fixed, so `escrowHeldAsset` is
  -- unchanged and the combined move equals the bare-`bal` move; for the escrow/note legs we read the
  -- combined-conservation off the per-asset holding-store lemmas (combined delta `0`).
  cases fa with
  | balanceA t a =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCexecAsset at h
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' =>
          rw [hx] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recTransferBal s.kernel.bal t.src t.dst a t.amt } from by
                      unfold recKExecAsset at hx; split at hx
                      · simpa only [Option.some.injEq] using hx.symm
                      · exact absurd hx (by simp)]; rfl,
              recKExecAsset_conserves_per_asset s.kernel k' t a hx b]; ring
  | delegate del rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | revoke holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | mintA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a amt } from by
                      unfold recKMintAsset at hm; split at hm
                      · simpa only [Option.some.injEq] using hm.symm
                      · exact absurd hm (by simp)]; rfl,
              recKMintAsset_delta s.kernel k' actor cell a amt hm b]; ring
  | burnA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCBurnAsset at h
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a (-amt) } from by
                      unfold recKBurnAsset at hb; split at hb
                      · simpa only [Option.some.injEq] using hb.symm
                      · exact absurd hb (by simp)]; rfl,
              recKBurnAsset_delta s.kernel k' actor cell a amt hb b]; ring
  | setFieldA actor cell f v =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel f cell (.int v)) b + escrowHeldAsset (writeField s.kernel f cell (.int v)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel f cell (.int v) b,
          show escrowHeldAsset (writeField s.kernel f cell (.int v)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | emitEventA actor cell topic data =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, emitStep]; ring
  | incrementNonceA actor cell n =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel nonceField cell (.int n)) b + escrowHeldAsset (writeField s.kernel nonceField cell (.int n)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel nonceField cell (.int n) b,
          show escrowHeldAsset (writeField s.kernel nonceField cell (.int n)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | setPermissionsA actor cell p =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel permsField cell (.int p)) b + escrowHeldAsset (writeField s.kernel permsField cell (.int p)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel permsField cell (.int p) b,
          show escrowHeldAsset (writeField s.kernel permsField cell (.int p)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | setVKA actor cell vk =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel vkField cell (.int vk)) b + escrowHeldAsset (writeField s.kernel vkField cell (.int vk)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel vkField cell (.int vk) b,
          show escrowHeldAsset (writeField s.kernel vkField cell (.int vk)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | introduceA intro rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | attenuateA actor idx keep =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      simp only [attenuateStepA, recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
  | dropRefA holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | revokeDelegationA holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | validateHandoffA intro rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | exerciseA actor t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := exerciseStepA_factors h; subst hs'
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
  | createCellA actor newCell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      -- combined = recTotalAsset (escrows unchanged by the fresh-cell insert) + neutral recTotalAsset.
      have hesc : escrowHeldAsset s'.kernel b = escrowHeldAsset s.kernel b := by
        obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
        subst hs'; rfl
      unfold recTotalAssetWithEscrow
      rw [hesc, createCellChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | spawnA actor child target =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      have hesc : escrowHeldAsset s'.kernel b = escrowHeldAsset s.kernel b := by
        obtain ⟨s1, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
        subst hs'
        obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
      unfold recTotalAssetWithEscrow
      rw [hesc, spawnChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | bridgeMintA actor cell a value =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a value } from by
                      unfold recKMintAsset at hm; split at hm
                      · simpa only [Option.some.injEq] using hm.symm
                      · exact absurd hm (by simp)]; rfl,
              recKMintAsset_delta s.kernel k' actor cell a value hm b]; ring
  -- §MA-escrow: the holding-store legs are COMBINED-conserving (combined delta `0`); notes are bal-NEUTRAL.
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createEscrowChainA_combined_neutral b h, add_zero]
  | releaseEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [releaseEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | refundEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [refundEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createEscrowChainA_combined_neutral b h, add_zero]
  | noteSpendA nf actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          -- noteSpend grows ONLY `nullifiers` — `bal` and `escrows` fixed.
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
          rw [show k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } from by
                unfold noteSpendNullifier at hk; split at hk
                · exact absurd hk (by simp)
                · simpa only [Option.some.injEq] using hk.symm]
          simp only [recTotalAsset, escrowHeldAsset]; ring
  | noteCreateA cm actor =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      -- noteCreate grows ONLY `commitments` — `bal` and `escrows` fixed.
      simp only [noteCreateChainA, noteCreateCommitment, recTotalAssetWithEscrow, recTotalAsset,
                 escrowHeldAsset]; ring
  | createCommittedEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createEscrowChainA_combined_neutral b h, add_zero]
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [releaseEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [refundEscrowKAsset_conserves_combined_per_asset b hk]; ring
  -- §MA-bridge: lock/cancel are COMBINED-conserving (combined delta `0`); finalize is the disclosed
  -- OUTFLOW (combined DROPS by `-amount` at the disclosed asset — the value LEFT for the other chain).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeLockChainA_combined_neutral b h, add_zero]
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeFinalizeChainA_burns_combined b h]
      by_cases hba : b = asset <;> simp only [hba, if_true, if_false] <;> ring
  | bridgeCancelA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeCancelChainA_combined_neutral b h, add_zero]

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

/-- **`execFullTurnA_ledger_per_asset` — PROVED (the transaction COMBINED conservation vector).** A
committed per-asset full-turn moves the COMBINED measure `recTotalAssetWithEscrow b` by exactly the net
of all per-action deltas in asset `b`, for EVERY asset `b`. Proved by induction on the turn, reusing
`execFullA_ledger_per_asset`. The asset-indexed analog of `execFullTurn_ledger`. -/
theorem execFullTurnA_ledger_per_asset :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId), execFullTurnA s tt = some s' →
      recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + turnLedgerDeltaAsset tt b
  | s, s', [], b, h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; simp [turnLedgerDeltaAsset]
  | s, s', a :: rest, b, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotalAssetWithEscrow s1.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset a b :=
            execFullA_ledger_per_asset s s1 a b ha
          have htail : recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s1.kernel b + turnLedgerDeltaAsset rest b :=
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
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
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
  -- §MA-state: every pure-state effect appends a balance-`0` self-`Turn` on the target `cell` (the
  -- metadata clock row that `stateStep`/`emitStep` thread; no balance delta).
  | .setFieldA actor cell _ _   => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .emitEventA actor cell _ _  => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .incrementNonceA actor cell _ => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .setPermissionsA actor cell _ => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .setVKA actor cell _        => { actor := actor, src := cell, dst := cell, amt := 0 }
  -- §MA-auth: each authority effect appends exactly its `authReceipt` (a self-`Turn`, amount `0`).
  | .introduceA intro _ _       => authReceipt intro
  | .attenuateA actor _ _       => authReceipt actor
  | .dropRefA holder _          => authReceipt holder
  | .revokeDelegationA holder _ => authReceipt holder
  | .validateHandoffA intro _ _ => authReceipt intro
  | .exerciseA actor _          => authReceipt actor
  -- §MA-supply: createCell/spawn append the fresh cell's (balance-`0`) creation row; bridgeMint
  -- appends a self-`Turn` carrying the disclosed `+value`.
  | .createCellA actor newCell  => { actor := actor, src := newCell, dst := newCell, amt := 0 }
  | .spawnA actor child _       => { actor := actor, src := child, dst := child, amt := 0 }
  | .bridgeMintA actor cell _ value => { actor := actor, src := cell, dst := cell, amt := value }
  -- §MA-escrow: every escrow/obligation/committed/note effect appends a self-`Turn` on the `actor`
  -- (the metadata clock row; the parked amount/asset live in the off-ledger record/SET, not the receipt).
  | .createEscrowA _ actor _ _ _ _   => escrowReceiptA actor
  | .releaseEscrowA _ actor          => escrowReceiptA actor
  | .refundEscrowA _ actor           => escrowReceiptA actor
  | .createObligationA _ actor _ _ _ _ => escrowReceiptA actor
  | .noteSpendA _ actor              => escrowReceiptA actor
  | .noteCreateA _ actor             => escrowReceiptA actor
  | .createCommittedEscrowA _ actor _ _ _ _ => escrowReceiptA actor
  | .releaseCommittedEscrowA _ actor => escrowReceiptA actor
  | .refundCommittedEscrowA _ actor  => escrowReceiptA actor
  -- §MA-bridge: each bridge leg appends a self-`Turn` on the `actor` (the metadata clock row; the
  -- bridged amount/asset live in the off-ledger record / the disclosed action params, not the receipt).
  | .bridgeLockA _ actor _ _ _ _     => escrowReceiptA actor
  | .bridgeFinalizeA _ actor _ _     => escrowReceiptA actor
  | .bridgeCancelA _ actor           => escrowReceiptA actor

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
  -- §MA-state: each pure-state effect appends exactly the metadata clock row (`stateStep`/`emitStep`).
  | setFieldA actor cell f v =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | emitEventA actor cell topic data =>
      simp only [execFullA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  | incrementNonceA actor cell n =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setPermissionsA actor cell p =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setVKA actor cell vk =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §MA-auth: each authority effect appends exactly its `authReceipt` (the metadata clock row).
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | exerciseA actor t =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := exerciseStepA_factors h; subst hs'; rfl
  -- §MA-supply: createCell/spawn append the fresh cell's creation row; bridgeMint the disclosed credit.
  | createCellA actor newCell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      exact createCellChainA_chainlink h
  | spawnA actor child target =>
      simp only [execFullA, fullReceiptA] at h ⊢
      exact spawnChainA_chainlink h
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset, fullReceiptA] at h ⊢
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-escrow: each escrow/note effect appends exactly its `escrowReceiptA` (the metadata clock row).
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA, fullReceiptA] at h ⊢
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | releaseEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA, fullReceiptA] at h ⊢
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | refundEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA, fullReceiptA] at h ⊢
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA, fullReceiptA] at h ⊢
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA, fullReceiptA] at h ⊢
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA, fullReceiptA] at h ⊢
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA, fullReceiptA] at h ⊢
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA, fullReceiptA] at h ⊢
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-bridge: each bridge leg appends exactly its `escrowReceiptA` (the metadata clock row).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA, fullReceiptA] at h ⊢
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA, fullReceiptA] at h ⊢
      cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA, fullReceiptA] at h ⊢
      cases hk : bridgeCancelKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl

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

/-! ### §MA-supply authority obligations — `bridgeMint` is PRIVILEGED supply (`mintAuthorizedB`), the
LOCAL gate independent of the §8 foreign-finality portal; `createCell`/`spawn` carry their privileged
creation authority + the freshness gate (proved earlier as `createCellChainA_authorized` /
`spawnChainA_authorized`). -/

/-- **`execFullA_bridgeMintA_authorized` — PROVED.** A committed per-asset bridge-mint implies the
privileged mint authority over `cell` (the LOCAL gate — the foreign finality is the §8 portal,
discharged outside Lean). REUSES `recKMintAsset_authorized`. -/
theorem execFullA_bridgeMintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a value hm

/-- **`execFullA_bridgeMintA_unauthorized_fails` — PROVED (fail-closed).** Without mint authority, no
bridge-mint commits (regardless of foreign finality). The confinement core. -/
theorem execFullA_bridgeMintA_unauthorized_fails (s : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (h : mintAuthorizedB s.kernel.caps actor cell = false) :
    execFullA s (.bridgeMintA actor cell a value) = none := by
  simp only [execFullA, recCMintAsset, recKMintAsset]
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`execFullA_createCellA_neutral_per_asset` — THE ACCOUNT-GROWTH NEUTRALITY KEYSTONE (PROVED).** A
committed `createCellA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`. NON-VACUOUS: the index set
`accounts` genuinely GREW (`execFullA_createCellA_grows_accounts` — the new cell IS live afterward), yet
supply is conserved BECAUSE the fresh cell is born EMPTY (the `bal`-reset). This is the createCell
account-growth neutrality META-FILL C demands — the dregg1-faithful `balance == 0` creation as a
conservation-NEUTRAL move on the per-asset ledger. -/
theorem execFullA_createCellA_neutral_per_asset (s s' : RecChainedState) (actor newCell : CellId)
    (b : AssetId) (h : execFullA s (.createCellA actor newCell) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_createCellA_grows_accounts` — the GROWTH has teeth (PROVED).** After a committed
`createCellA`, the new cell IS a live account: `newCell ∈ s'.kernel.accounts`. Witnesses that the
neutrality keystone is NOT a no-op — the conserved-measure index set genuinely grew. -/
theorem execFullA_createCellA_grows_accounts (s s' : RecChainedState) (actor newCell : CellId)
    (h : execFullA s (.createCellA actor newCell) = some s') :
    newCell ∈ s'.kernel.accounts :=
  createCellChainA_grows_accounts (by simpa only [execFullA] using h)

/-- **`execFullA_spawnA_neutral_per_asset` — PROVED.** A committed `spawnA` (createCell born EMPTY + a
bal-orthogonal cap grant) is likewise conservation-NEUTRAL for EVERY asset. -/
theorem execFullA_spawnA_neutral_per_asset (s s' : RecChainedState) (actor child target : CellId)
    (b : AssetId) (h : execFullA s (.spawnA actor child target) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  spawnChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_bridgeMintA_discloses_per_asset` — PROVED (the §8 portal disclosed delta).** A committed
`bridgeMintA actor cell a value` raises asset `a`'s supply by EXACTLY the disclosed `value` and leaves
EVERY OTHER asset literally UNCHANGED: `recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = a
then value else 0)`. The disclosed generative inflow (NOT a conservation claim) — the per-asset
no-cross-asset-laundering content at the bridge boundary. -/
theorem execFullA_bridgeMintA_discloses_per_asset (s s' : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (b : AssetId)
    (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = a then value else 0) := by
  -- bridgeMint reuses the per-asset mint kernel step (`recKMintAsset_delta`) over the BARE `bal` ledger.
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h; subst h
      exact recKMintAsset_delta s.kernel k' actor cell a value hm b

/-! ### §MA-state authority obligations — the 4 field-writing pure-state effects WERE authorized;
`emitEventA` is authority-FREE (dregg1 `apply_emit_event` runs NO cap check). The field-writing
effects reuse `EffectsState.state_authorized` (the `stateAuthB` gate over the target cell — the
faithful model of dregg1's `check_cross_cell_permission`/ownership), so the gate is REAL, not
vacuous: an actor without authority over `cell` cannot commit a field write (see the fail-closed
`#eval`s in §13-state). -/

/-- **`setFieldA` authorized — PROVED.** A committed `setFieldA` implies the actor held authority over
`cell` (`stateAuthB` — the faithful model of dregg1's `SetState` cross-cell / ownership gate). -/
theorem execFullA_setFieldA_authorized (s s' : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`incrementNonceA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`IncrementNonce` cross-cell / ownership gate). -/
theorem execFullA_incrementNonceA_authorized (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setPermissionsA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`SetPermissions` gate; dregg1 applies the permission write LAST off the ORIGINAL snapshot, so the
gate is evaluated against the PRE-state caps — exactly `stateAuthB s.kernel.caps`, the pre-state). -/
theorem execFullA_setPermissionsA_authorized (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setVKA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`SetVerificationKey` gate). -/
theorem execFullA_setVKA_authorized (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (h : execFullA s (.setVKA actor cell vk) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-! ### §MA-auth authority obligations — the 6 distinct authority effects carry their REAL,
NON-VACUOUS integrity content (grounding / `addEdge` / `removeEdge` / non-amplification / held-cap).
These REUSE the `recKDelegate`/`recKRevokeTarget` spine lemmas and `Caps.attenuate_subset` — exactly
the proofs `Exec.EffectsAuthority` carries (which we cannot import, being downstream). -/

/-- **`execFullA_introduceA_grounds` — PROVED.** A committed introduce HOLDS the Granovetter source
edge `introducer ⟶ ⟨target,()⟩` (only connectivity begets connectivity). REUSES `recKDelegate_grounds`. -/
theorem execFullA_introduceA_grounds (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps intro (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' intro rec t hd

/-- **`execFullA_introduceA_addEdge` — PROVED.** A committed introduce edits the graph by EXACTLY
`addEdge … rec ⟨t,()⟩`. REUSES `recKDelegate_execGraph`. -/
theorem execFullA_introduceA_addEdge (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps rec t
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_introduceA_holds_real_cap` — PROVED.** A committed introduce WITNESSES the concrete
held cap behind the connectivity edge: the introducer holds, in its real c-list, an `Authority.Cap`
`held` conferring an edge to `target`. This recovers the REAL `List Auth` rights the genuine
non-amplification reads (the seam `EffectsAuthority.exercise_holds_real_cap` opens). -/
theorem execFullA_introduceA_holds_real_cap (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [List.any_eq_true] at hg
        obtain ⟨held, hmem, hconf⟩ := hg
        exact ⟨held, hmem, hconf⟩
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_introduceA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** Whatever rights an
introduce confers are bounded by a held cap: it WITNESSES a concrete held cap `held`, and the
conferred (attenuated) cap is a GENUINE `List Auth` SUBSET — `IsNonAmplifyingF held (attenuate keep
held)` for any `keep` — via `Caps.attenuate_subset`. This is `is_attenuation(held, granted)`,
"amplification denied" (`apply.rs:2835`), over the REAL lattice. NOT a `()≤()` skeleton — an
amplifying grant is rejected (`amplifyingF_rejected`). -/
theorem execFullA_introduceA_non_amplifying (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true
      ∧ ∀ keep : List Auth, IsNonAmplifyingF held (attenuate keep held) := by
  obtain ⟨held, hmem, hconf⟩ := execFullA_introduceA_holds_real_cap s s' intro rec t h
  exact ⟨held, hmem, hconf, fun keep => attenuateF_non_amplifying keep held⟩

/-- **`execFullA_attenuateA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** Whatever cap the
actor narrows, the narrowed cap confers a genuine `List Auth` SUBSET of the original:
`∀ c, IsNonAmplifyingF c (attenuate keep c)`, via `Caps.attenuate_subset`. The executable
`is_narrower_or_equal` (widening denied). -/
theorem execFullA_attenuateA_non_amplifying (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ c : Cap, IsNonAmplifyingF c (attenuate keep c) :=
  fun c => attenuateF_non_amplifying keep c

/-- **`execFullA_attenuateA_confined` — PROVED.** Attenuation edits ONLY the actor's OWN slot; every
OTHER holder's slot is untouched (the confinement face of "you can only narrow what you hold"). -/
theorem execFullA_attenuateA_confined (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ l, l ≠ actor → s'.kernel.caps l = s.kernel.caps l := by
  simp only [execFullA, attenuateStepA, Option.some.injEq] at h
  subst h
  intro l hl; simp only [attenuateSlotF, if_neg hl]

/-- **`execFullA_dropRefA_removeEdge` — PROVED.** A committed DropRef edits the graph by EXACTLY
`removeEdge … holder ⟨t,()⟩` (the GC of a remote reference). REUSES `recKRevokeTarget_execGraph`. -/
theorem execFullA_dropRefA_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.dropRefA holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **`execFullA_revokeDelegationA_removeEdge` — PROVED.** A committed RevokeDelegation edits the
graph by EXACTLY `removeEdge … holder ⟨t,()⟩` (the parent drops the child's edge). REUSES
`recKRevokeTarget_execGraph`. -/
theorem execFullA_revokeDelegationA_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.revokeDelegationA holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **`execFullA_validateHandoffA_grounds` — PROVED.** A committed handoff HOLDS the Granovetter
source edge `introducer ⟶ ⟨target,()⟩` (the handoff IS an introduce). REUSES `recKDelegate_grounds`. -/
theorem execFullA_validateHandoffA_grounds (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.validateHandoffA intro rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps intro (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' intro rec t hd

/-- **`execFullA_validateHandoffA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The conferred
(attenuated) cap of a handoff is a genuine `List Auth` SUBSET of a held cap (`granted ⊆ held`,
EXACTLY the `is_attenuation(held, granted)` check dregg1's `verify_captp_delivered` was MISSING) —
it WITNESSES the introducer's held cap and the non-amplification of its attenuation. -/
theorem execFullA_validateHandoffA_non_amplifying (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.validateHandoffA intro rec t) = some s') :
    ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true
      ∧ ∀ keep : List Auth, IsNonAmplifyingF held (attenuate keep held) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [List.any_eq_true] at hg
        obtain ⟨held, hmem, hconf⟩ := hg
        exact ⟨held, hmem, hconf, fun keep => attenuateF_non_amplifying keep held⟩
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_exerciseA_authorized` — PROVED.** A committed exercise HOLDS the source edge:
`actor ⟶ ⟨target,()⟩` on `execGraph` (the resolved c-list slot — only the holder may exercise). -/
theorem execFullA_exerciseA_authorized (s s' : RecChainedState) (actor t : CellId)
    (h : execFullA s (.exerciseA actor t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  obtain ⟨hg, _⟩ := exerciseStepA_factors (by simpa only [execFullA] using h)
  rw [execGraph_eq_any]; exact hg

/-- **`execFullA_exerciseA_graph_unchanged` — PROVED.** Exercising a cap leaves the reconstructed
authority graph UNCHANGED — it reads the c-list, never edits it. The graph-preserving frame. -/
theorem execFullA_exerciseA_graph_unchanged (s s' : RecChainedState) (actor t : CellId)
    (h : execFullA s (.exerciseA actor t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps = Dregg2.Spec.execGraph s.kernel.caps := by
  obtain ⟨_, hs'⟩ := exerciseStepA_factors (by simpa only [execFullA] using h)
  subst hs'; rfl

/-! ### §MA-escrow authority/membership obligations — the create-side carries the REAL `authorizedB`
creator gate (over the debited cell); noteSpend/noteCreate carry the genuine SET-membership witness. -/

/-- **`execFullA_createEscrowA_authorized` — PROVED.** A committed escrow create required the actor to be
authorized over the debited `creator` cell (the SAME `authorizedB` gate as `transfer`). -/
theorem execFullA_createEscrowA_authorized (s s' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA s (.createEscrowA id actor creator recipient asset amount) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  simp only [execFullA, createEscrowChainA] at h
  cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' => exact createEscrowKAsset_authorized hk

/-- **`execFullA_createObligationA_authorized` — PROVED** (the obligation alias of the create gate). -/
theorem execFullA_createObligationA_authorized (s s' : RecChainedState) (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
    (h : execFullA s (.createObligationA id actor obligor beneficiary asset stake) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := obligor, dst := beneficiary, amt := stake } = true := by
  simp only [execFullA, createEscrowChainA] at h
  cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' => exact createEscrowKAsset_authorized hk

/-- **`execFullA_noteSpendA_inserts` — PROVED.** A committed noteSpend inserts `nf` into the nullifier
SET (so a subsequent spend of `nf` fails-closed — the anti-replay teeth). -/
theorem execFullA_noteSpendA_inserts (s s' : RecChainedState) (nf : Nat) (actor : CellId)
    (h : execFullA s (.noteSpendA nf actor) = some s') : nf ∈ s'.kernel.nullifiers := by
  simp only [execFullA, noteSpendChainA] at h
  cases hk : noteSpendNullifier s.kernel nf with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact note_spend_inserts hk

/-- **`execFullA_noteCreateA_inserts` — PROVED.** A committed noteCreate inserts `cm` into the grow-only
commitment SET. -/
theorem execFullA_noteCreateA_inserts (s s' : RecChainedState) (cm : Nat) (actor : CellId)
    (h : execFullA s (.noteCreateA cm actor) = some s') : cm ∈ s'.kernel.commitments := by
  simp only [execFullA, noteCreateChainA, Option.some.injEq] at h
  subst h; exact noteCreate_inserts s.kernel cm

/-! ### §MA-bridge authority/portal obligations (Wave-5). The bridge LOCK carries the REAL `authorizedB`
originator gate (over the debited cell — the §8 spending proof is the THEOREM-level portal); FINALIZE
carries the disclosed OUTFLOW witness (combined DROPS by the disclosed `-amount` — the §8 confirmation
receipt is the THEOREM-level portal, a genuine portal on a REACHABLE path, exactly as bridgeMint's foreign
finality); CANCEL carries the refund-conservation witness. -/

/-- **`execFullA_bridgeLockA_authorized` — PROVED.** A committed bridge lock required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`/escrow-create). The
LOCAL gate independent of the §8 spending-proof portal (carried at the theorem layer). -/
theorem execFullA_bridgeLockA_authorized (s s' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA s (.bridgeLockA id actor originator destination asset amount) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  simp only [execFullA] at h
  exact bridgeLockChainA_authorized h

/-- **`execFullA_bridgeLockA_unauthorized_fails` — PROVED (fail-closed).** Without authority over the
originator, no bridge lock commits (regardless of the §8 spending proof). The confinement core: the value
cannot be locked-and-bridged out of a cell the actor does not control. -/
theorem execFullA_bridgeLockA_unauthorized_fails (s : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = false) :
    execFullA s (.bridgeLockA id actor originator destination asset amount) = none := by
  simp only [execFullA, bridgeLockChainA, bridgeLockKAsset]
  rw [if_neg (by rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp))]

/-- **`execFullA_bridgeFinalizeA_burns_per_asset` — THE BRIDGE OUTFLOW WITNESS (PROVED).** A committed
bridge finalize DROPS the COMBINED per-asset measure by EXACTLY the disclosed `amount` at the disclosed
`asset` and leaves EVERY OTHER asset literally fixed — the value genuinely LEFT for the other chain (a
disclosed OUTFLOW, NOT a conservation claim). The §8 confirmation receipt is the THEOREM-level portal. -/
theorem execFullA_bridgeFinalizeA_burns_per_asset (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) (b : AssetId)
    (h : execFullA s (.bridgeFinalizeA id actor asset amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0) :=
  bridgeFinalizeChainA_burns_combined b (by simpa only [execFullA] using h)

/-- **`execFullA_bridgeCancelA_conserves_per_asset` — PROVED (the refund round-trip).** A committed bridge
cancel conserves the COMBINED per-asset measure at EVERY asset (the value returns to the LIVE, gate-checked
originator). The timeout gate is carried at the theorem layer. -/
theorem execFullA_bridgeCancelA_conserves_per_asset (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (b : AssetId) (h : execFullA s (.bridgeCancelA id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  bridgeCancelChainA_combined_neutral b (by simpa only [execFullA] using h)

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
  -- Ledger: the per-asset COMBINED conservation VECTOR (∀ b — never one aggregate scalar). The UNIFORM
  -- measure across ALL kinds is `recTotalAssetWithEscrow` (= `bal`-ledger + per-asset holding-store);
  -- non-escrow kinds leave `escrows` fixed so their combined delta = bare-`bal` delta, escrow/note legs
  -- are combined-conserving (combined delta `0`) — the FILL-1/META-FILL-C no-laundering carrier.
  (∀ b, recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset fa b) ∧
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
       (effectLinearity burnEffect).is_disclosed_non_conservation = true
   -- §MA-state: the field-writing pure-state effects carry their REAL authority gate
   -- (`stateAuthB` over the cell) ∧ their `Neutral`/`Monotonic` linearity coloring (the
   -- faithful-mirror tripwire). `emitEventA` is authority-FREE (dregg1 runs no cap check), so its
   -- obligation is JUST the `Neutral` coloring — honestly NOT an authority claim.
   | .setFieldA actor cell _ _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setField = LinearityClass.Neutral
   | .emitEventA _ _ _ _ =>
       effectLinearity .emitEvent = LinearityClass.Neutral
   | .incrementNonceA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .incrementNonce = LinearityClass.Monotonic
   | .setPermissionsA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setPermissions = LinearityClass.Neutral
   | .setVKA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setVerificationKey = LinearityClass.Neutral
   -- §MA-auth: the 6 authority effects carry their REAL, NON-VACUOUS obligation. The HEADLINE is
   -- NON-AMPLIFICATION — the GENUINE `capAuthConferred ⊆` over the real `List Auth` lattice
   -- (`IsNonAmplifyingF`, witnessed against a HELD cap), NOT a `()≤()` collapse — and the `addEdge`/
   -- `removeEdge`/graph-unchanged graph move + grounding in held connectivity.
   | .introduceA intro rec t =>
       -- (a) grounds in held connectivity, (b) edits the graph by `addEdge`, (c) GENUINE rights
       -- non-amplification: the conferred (attenuated) cap of a HELD cap confers a `List Auth` SUBSET.
       Dregg2.Spec.execGraph s.kernel.caps intro
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩ ∧
       ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true
         ∧ ∀ keep : List Auth, IsNonAmplifyingF held (attenuate keep held)
   | .attenuateA _ idx keep =>
       -- GENUINE non-amplification: narrowing to `keep` confers a `List Auth` SUBSET of ANY cap.
       ∀ c : Cap, IsNonAmplifyingF c (attenuate keep c)
   | .dropRefA holder t =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .revokeDelegationA holder t =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .validateHandoffA intro _ t =>
       -- (a) grounds in held connectivity, (b) the conferred (attenuated) cap is non-amplifying
       -- (`granted ⊆ held`) — the `is_attenuation` check dregg1's `verify_captp_delivered` missed.
       Dregg2.Spec.execGraph s.kernel.caps intro
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true
         ∧ ∀ keep : List Auth, IsNonAmplifyingF held (attenuate keep held)
   | .exerciseA actor t =>
       -- authorized BY the held edge AND confers NO new authority (graph UNCHANGED).
       Dregg2.Spec.execGraph s.kernel.caps actor
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps = Dregg2.Spec.execGraph s.kernel.caps
   -- §MA-supply: createCell/spawn carry the REAL privileged-creation gate (`mintAuthorizedB` — bare
   -- ownership is NOT enough) AND the REAL freshness gate (`newCell ∉ accounts`, fail-closed: a
   -- non-fresh id is rejected) AND the Generative disclosure coloring; bridgeMint carries the
   -- privileged mint gate AND the §8 Generative disclosure. NOT `True` — every conjunct has teeth.
   | .createCellA actor newCell =>
       mintAuthorizedB s.kernel.caps actor newCell = true ∧
       newCell ∉ s.kernel.accounts ∧
       newCell ∈ s'.kernel.accounts ∧
       (effectLinearity .createCell).is_disclosed_non_conservation = true
   | .spawnA actor child target =>
       mintAuthorizedB s.kernel.caps actor child = true ∧
       child ∉ s.kernel.accounts ∧
       (∃ rest, s'.kernel.caps child = Cap.node target :: rest) ∧
       (effectLinearity .spawnWithDelegation).is_disclosed_non_conservation = true
   | .bridgeMintA actor cell _ _ =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   -- §MA-escrow: create-side obligations carry the REAL `authorizedB` creator gate (over the debited
   -- cell) ∧ the `Conservative` coloring; the settle-side and notes carry the genuine SET/store
   -- membership witness — every conjunct has teeth (NOT `True`).
   | .createEscrowA _ actor creator recipient _ amount =>
       authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true ∧
       effectLinearity .createEscrow = LinearityClass.Conservative
   | .releaseEscrowA _ _ =>
       effectLinearity .releaseEscrow = LinearityClass.Conservative
   | .refundEscrowA _ _ =>
       effectLinearity .refundEscrow = LinearityClass.Conservative
   | .createObligationA _ actor obligor beneficiary _ stake =>
       authorizedB s.kernel.caps { actor := actor, src := obligor, dst := beneficiary, amt := stake } = true ∧
       effectLinearity .createObligation = LinearityClass.Conservative
   | .noteSpendA nf _ =>
       -- anti-replay: the spent nullifier is now IN the set (a subsequent spend fails-closed).
       nf ∈ s'.kernel.nullifiers ∧ effectLinearity .noteSpend = LinearityClass.Conservative
   | .noteCreateA cm _ =>
       -- the fresh commitment is now IN the grow-only commitment set.
       cm ∈ s'.kernel.commitments ∧ effectLinearity .noteCreate = LinearityClass.Conservative
   | .createCommittedEscrowA _ actor creator recipient _ amount =>
       authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true ∧
       effectLinearity .createEscrow = LinearityClass.Conservative
   | .releaseCommittedEscrowA _ _ =>
       effectLinearity .releaseEscrow = LinearityClass.Conservative
   | .refundCommittedEscrowA _ _ =>
       effectLinearity .refundEscrow = LinearityClass.Conservative
   -- §MA-bridge: LOCK carries the REAL `authorizedB` originator gate (over the debited cell) ∧ the
   -- `Conservative` coloring (combined-conserving lock). FINALIZE carries the genuine DISCLOSED-OUTFLOW
   -- witness — the COMBINED measure MOVED DOWN by the disclosed `-amount` at the disclosed `asset`
   -- (`∀ b`, the §8 confirmation portal having fired; NOT a `True`, the move has teeth) ∧ the
   -- `Conservative` coloring. CANCEL carries the refund-CONSERVATION witness (combined fixed `∀ b`) ∧
   -- the coloring. Every conjunct has teeth.
   | .bridgeLockA _ actor originator destination _ amount =>
       authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true ∧
       effectLinearity .bridgeLock = LinearityClass.Conservative
   | .bridgeFinalizeA _ _ asset amount =>
       (∀ b, recTotalAssetWithEscrow s'.kernel b
          = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0)) ∧
       effectLinearity .bridgeFinalize = LinearityClass.Conservative
   | .bridgeCancelA _ _ =>
       (∀ b, recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b) ∧
       effectLinearity .bridgeCancel = LinearityClass.Conservative)

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
  -- §MA-state: discharge the field-writing effects' (authority ∧ coloring) obligation; emitEvent's
  -- coloring-only obligation (authority-free, dregg1-faithful).
  | setFieldA actor cell f v => exact ⟨execFullA_setFieldA_authorized s s' actor cell f v h, rfl⟩
  | emitEventA actor cell topic data => exact rfl
  | incrementNonceA actor cell n => exact ⟨execFullA_incrementNonceA_authorized s s' actor cell n h, rfl⟩
  | setPermissionsA actor cell p => exact ⟨execFullA_setPermissionsA_authorized s s' actor cell p h, rfl⟩
  | setVKA actor cell vk => exact ⟨execFullA_setVKA_authorized s s' actor cell vk h, rfl⟩
  -- §MA-auth: discharge the 6 authority effects' REAL obligation (grounding/addEdge/removeEdge/
  -- graph-unchanged ∧ the GENUINE `capAuthConferred ⊆` non-amplification).
  | introduceA intro rec t =>
      exact ⟨execFullA_introduceA_grounds s s' intro rec t h,
             execFullA_introduceA_addEdge s s' intro rec t h,
             execFullA_introduceA_non_amplifying s s' intro rec t h⟩
  | attenuateA actor idx keep => exact execFullA_attenuateA_non_amplifying s s' actor idx keep h
  | dropRefA holder t => exact execFullA_dropRefA_removeEdge s s' holder t h
  | revokeDelegationA holder t => exact execFullA_revokeDelegationA_removeEdge s s' holder t h
  | validateHandoffA intro rec t =>
      exact ⟨execFullA_validateHandoffA_grounds s s' intro rec t h,
             execFullA_validateHandoffA_non_amplifying s s' intro rec t h⟩
  | exerciseA actor t =>
      exact ⟨execFullA_exerciseA_authorized s s' actor t h,
             execFullA_exerciseA_graph_unchanged s s' actor t h⟩
  -- §MA-supply: discharge createCell/spawn's (privileged-creation gate ∧ freshness ∧ growth/provenance
  -- ∧ Generative disclosure) and bridgeMint's (privileged mint gate ∧ §8 Generative disclosure).
  | createCellA actor newCell =>
      simp only [execFullA] at h
      obtain ⟨hauth, hfresh, _⟩ := createCellChainA_factors h
      exact ⟨hauth, hfresh, createCellChainA_grows_accounts h,
             Dregg2.CatalogEffects.generative_discloses .createCell Dregg2.CatalogEffects.g_createCell⟩
  | spawnA actor child target =>
      simp only [execFullA] at h
      obtain ⟨s1, hc, _⟩ := spawnChainA_factors h
      exact ⟨createCellChainA_authorized hc, (createCellChainA_factors hc).2.1,
             spawnChainA_provenance (by simpa only [execFullA] using h),
             Dregg2.CatalogEffects.generative_discloses .spawnWithDelegation
               Dregg2.CatalogEffects.g_spawnWithDelegation⟩
  | bridgeMintA actor cell a value =>
      exact ⟨execFullA_bridgeMintA_authorized s s' actor cell a value h, mint_discloses⟩
  -- §MA-escrow: discharge the create-side `authorizedB` gate + Conservative coloring, the settle-side
  -- coloring, and the noteSpend/noteCreate SET-membership witness.
  | createEscrowA id actor creator recipient asset amount =>
      exact ⟨execFullA_createEscrowA_authorized s s' id actor creator recipient asset amount h, rfl⟩
  | releaseEscrowA id actor => exact rfl
  | refundEscrowA id actor => exact rfl
  | createObligationA id actor obligor beneficiary asset stake =>
      exact ⟨execFullA_createObligationA_authorized s s' id actor obligor beneficiary asset stake h, rfl⟩
  | noteSpendA nf actor => exact ⟨execFullA_noteSpendA_inserts s s' nf actor h, rfl⟩
  | noteCreateA cm actor => exact ⟨execFullA_noteCreateA_inserts s s' cm actor h, rfl⟩
  | createCommittedEscrowA id actor creator recipient asset amount =>
      exact ⟨execFullA_createEscrowA_authorized s s' id actor creator recipient asset amount h, rfl⟩
  | releaseCommittedEscrowA id actor => exact rfl
  | refundCommittedEscrowA id actor => exact rfl
  -- §MA-bridge: discharge LOCK's (authority ∧ Conservative coloring), FINALIZE's (disclosed-OUTFLOW
  -- move ∧ coloring), CANCEL's (refund-conservation ∧ coloring).
  | bridgeLockA id actor originator destination asset amount =>
      exact ⟨execFullA_bridgeLockA_authorized s s' id actor originator destination asset amount h, rfl⟩
  | bridgeFinalizeA id actor asset amount =>
      exact ⟨fun b => execFullA_bridgeFinalizeA_burns_per_asset s s' id actor asset amount b h, rfl⟩
  | bridgeCancelA id actor =>
      exact ⟨fun b => execFullA_bridgeCancelA_conserves_per_asset s s' id actor b h, rfl⟩

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
-- META-FILL B Wave 1: the 5 PURE-STATE (field/log) effects on the per-asset dispatch.
-- The balance-NEUTRALITY keystone (a field/log write moves NO asset's supply) + the per-effect
-- authority gates + the (re-extended) per-asset spine arms all pinned kernel-clean.
#assert_axioms writeField_recTotalAsset
#assert_axioms stateStep_recTotalAsset
#assert_axioms emitStep_recTotalAsset
#assert_axioms emitStep_obsadvance
#assert_axioms execFullA_setFieldA_authorized
#assert_axioms execFullA_incrementNonceA_authorized
#assert_axioms execFullA_setPermissionsA_authorized
#assert_axioms execFullA_setVKA_authorized
-- META-FILL B Wave 2: the 6 DISTINCT AUTHORITY effects on the per-asset dispatch. The headline
-- NON-AMPLIFICATION (genuine `capAuthConferred ⊆` over the real `List Auth` lattice) + the
-- teeth (amplifying grant rejected) + grounding/addEdge/removeEdge/graph-unchanged graph moves,
-- all pinned kernel-clean. The keystone `execFullA_attests_per_asset` (re-extended above) carries
-- ALL of these into the forest by construction (FullForestA spine UNCHANGED).
#assert_axioms amplifyingF_rejected
#assert_axioms attenuateF_non_amplifying
#assert_axioms exerciseStepA_factors
#assert_axioms execFullA_introduceA_grounds
#assert_axioms execFullA_introduceA_addEdge
#assert_axioms execFullA_introduceA_holds_real_cap
#assert_axioms execFullA_introduceA_non_amplifying
#assert_axioms execFullA_attenuateA_non_amplifying
#assert_axioms execFullA_attenuateA_confined
#assert_axioms execFullA_dropRefA_removeEdge
#assert_axioms execFullA_revokeDelegationA_removeEdge
#assert_axioms execFullA_validateHandoffA_grounds
#assert_axioms execFullA_validateHandoffA_non_amplifying
#assert_axioms execFullA_exerciseA_authorized
#assert_axioms execFullA_exerciseA_graph_unchanged
-- META-FILL C Wave 3: accounts-GROWTH (`createCell`/`spawn`, born EMPTY ⇒ conservation-NEUTRAL) +
-- the SUPPLY inflow (`bridgeMint`, §8-portal disclosed `+value` at ONE asset). The account-growth
-- NEUTRALITY keystone (`recTotalAsset` unchanged BECAUSE the fresh cell is born empty, the index set
-- genuinely grew) + the disclosed bridge inflow + the per-effect gates, all pinned kernel-clean. The
-- keystone `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by
-- construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms recTotalAsset_insert_fresh
#assert_axioms createCellIntoAsset_grows_accounts
#assert_axioms createCellChainA_factors
#assert_axioms createCellChainA_neutral
#assert_axioms createCellChainA_grows_accounts
#assert_axioms createCellChainA_authorized
#assert_axioms createCellChainA_unauthorized_fails
#assert_axioms createCellChainA_chainlink
#assert_axioms spawnChainA_factors
#assert_axioms spawnChainA_neutral
#assert_axioms spawnChainA_authorized
#assert_axioms spawnChainA_provenance
#assert_axioms spawnChainA_chainlink
#assert_axioms execFullA_bridgeMintA_authorized
#assert_axioms execFullA_bridgeMintA_unauthorized_fails
#assert_axioms execFullA_createCellA_neutral_per_asset
#assert_axioms execFullA_createCellA_grows_accounts
#assert_axioms execFullA_spawnA_neutral_per_asset
#assert_axioms execFullA_bridgeMintA_discloses_per_asset
-- META-FILL C: the COMBINED per-asset escrow/note chained wrappers + the executed-dispatch obligations.
#assert_axioms createEscrowChainA_combined_neutral
#assert_axioms createEscrowChainA_bal_debits
#assert_axioms createEscrowChainA_bal_delta
#assert_axioms execFullA_createEscrowA_authorized
#assert_axioms execFullA_createObligationA_authorized
#assert_axioms execFullA_noteSpendA_inserts
#assert_axioms execFullA_noteCreateA_inserts
-- Wave-5 PHASE-BRIDGE: the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store.
-- LOCK is COMBINED-conserving (bal debit offset by the holding-store park); FINALIZE is the disclosed
-- OUTFLOW (COMBINED DROPS by the disclosed -amount at the bridged asset — the value LEFT for the other
-- chain, like burn); CANCEL refunds the originator (combined conserved). The §8 confirmation receipt is
-- the THEOREM-level portal. The keystone `execFullA_attests_per_asset` (re-extended above) carries ALL of
-- these into the forest by construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms bridge_lock_conserves_combined_per_asset
#assert_axioms bridge_lock_debits_per_asset
#assert_axioms bridgeLockKAsset_authorized
#assert_axioms bridge_finalize_moves_combined_per_asset
#assert_axioms bridgeFinalizeKAsset_moves_combined_per_asset
#assert_axioms bridge_cancel_conserves_combined_per_asset
#assert_axioms bridgeLockChainA_combined_neutral
#assert_axioms bridgeLockChainA_bal_debits
#assert_axioms bridgeFinalizeChainA_burns_combined
#assert_axioms bridgeCancelChainA_combined_neutral
#assert_axioms bridgeLockChainA_authorized
#assert_axioms execFullA_bridgeLockA_authorized
#assert_axioms execFullA_bridgeLockA_unauthorized_fails
#assert_axioms execFullA_bridgeFinalizeA_burns_per_asset
#assert_axioms execFullA_bridgeCancelA_conserves_per_asset

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

/-! ## §13-state — Non-vacuity for the 5 PURE-STATE effects: the cell record/log moves, but
`recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); authority is REAL
(an unauthorized field write fails-closed); `emitEvent` is authority-FREE. -/

/-- A genuine 2-asset state whose cells ALSO carry a `nonce`/`status`/`permissions`/`verification_key`
record (so the pure-state field writes are OBSERVABLE). Cell 0 holds 100 of asset 0 + 7 of asset 1;
cell 1 holds 5 of asset 0. Empty cap table ⇒ authority is by OWNERSHIP (actor = cell). -/
def fmaS : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), ("nonce", .int 0),
                                                ("status", .int 0), ("permissions", .int 0),
                                                ("verification_key", .int 0)]
                         else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#eval (recTotalAsset fmaS.kernel 0, recTotalAsset fmaS.kernel 1)                     -- (105, 7)

-- ★ THE KEYSTONE WITNESS: a `setFieldA` that changes cell 0's `nonce` field to 42 COMMITS,
--   yet `recTotalAsset` is UNCHANGED at (105, 7) for BOTH assets (balance-NEUTRALITY):
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).isSome                            -- true
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => fieldOf "nonce" (s.kernel.cell 0))                                 -- some 42 (CHANGED)
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (UNCHANGED)
-- ...and grows the receipt chain by exactly one row (the metadata clock):
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map (fun s => s.log.length)       -- some 1
-- An UNAUTHORIZED actor (9 owns nothing, empty caps) cannot write cell 0's field (fail-closed):
#eval (execFullA fmaS (.setFieldA 9 0 "nonce" 42)).isSome                            -- false

-- IncrementNonce (Monotonic): bump cell 0's nonce 0→1, balance-neutral:
#eval (execFullA fmaS (.incrementNonceA 0 0 1)).map (fun s => fieldOf "nonce" (s.kernel.cell 0))  -- some 1
#eval (execFullA fmaS (.incrementNonceA 0 0 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)

-- SetPermissions / SetVerificationKey (Neutral): field writes, balance-neutral:
#eval (execFullA fmaS (.setPermissionsA 0 0 3)).map (fun s => fieldOf "permissions" (s.kernel.cell 0))  -- some 3
#eval (execFullA fmaS (.setVKA 0 0 99)).map (fun s => fieldOf "verification_key" (s.kernel.cell 0))     -- some 99
#eval (execFullA fmaS (.setVKA 0 0 99)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)

-- EmitEvent: authority-FREE (even actor 9, who owns nothing, commits — dregg1 runs NO cap check),
--   writes NO state, grows the chain by one, balance-neutral:
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).isSome                                -- true (authority-free)
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).map (fun s => s.log.length)           -- some 1
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)

-- A MIXED per-asset turn interleaving pure-state effects with a transfer: ALL balance-neutral
--   (the transfer conserves; the field writes/emit move no asset) ⇒ (105, 7) preserved:
def stateMixedTurn : List FullActionA :=
  [ .setFieldA 0 0 "status" 5
  , .balanceA ⟨0, 0, 1, 30⟩ 0     -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)
  , .incrementNonceA 0 0 1
  , .emitEventA 0 0 1 0
  , .setVKA 0 0 7 ]

#eval (execFullTurnA fmaS stateMixedTurn).isSome                                     -- true (all commit)
#eval (turnLedgerDeltaAsset stateMixedTurn 0, turnLedgerDeltaAsset stateMixedTurn 1) -- (0, 0)
#eval (execFullTurnA fmaS stateMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (CONSERVED)
#eval (execFullTurnA fmaS stateMixedTurn).map (fun s => s.log.length)                -- some 5 (chain grew by node count)

/-! ## §13-auth — Non-vacuity for the 6 DISTINCT AUTHORITY effects: the cap-graph moves (or is
checked), but `recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); the
HEADLINE non-amplification has TEETH (an attenuation STRICTLY drops a right; an amplifying grant is
REJECTED); fail-closed (introduce/exercise without held connectivity ⇒ none). -/

/-- A 2-asset state whose actor 0 ALSO holds REAL caps: `node 7` (connectivity, for introduce/
exercise/handoff to target 7) and `endpoint 9 [read, write]` (rights-carrying, for attenuation
teeth; the `write` makes it confer connectivity to 9 too). Asset 0 = 105, asset 1 = 7. -/
def fmaA : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 9 [Auth.read, Auth.write]] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#eval (recTotalAsset fmaA.kernel 0, recTotalAsset fmaA.kernel 1)                      -- (105, 7)

-- (1) INTRODUCE: actor 0 (holds `node 7`) introduces recipient 1 to target 7. COMMITS, and
--   `recTotalAsset` is UNCHANGED in BOTH assets (caps change, bal does NOT — balance-NEUTRALITY):
#eval (execFullA fmaA (.introduceA 0 1 7)).isSome                                     -- true
#eval (execFullA fmaA (.introduceA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (UNCHANGED)
-- ...and recipient 1 now holds the `node 7` cap (the new authority EDGE — caps DID move):
#eval ((execFullA fmaA (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []   -- [Cap.node 7]
-- An introducer with NO connectivity to the target cannot introduce it (FAIL-CLOSED ⇒ none):
#eval (execFullA fmaA (.introduceA 5 1 7)).isSome                                     -- false

-- (1') THE TEETH — genuine rights NON-AMPLIFICATION over the real `List Auth` lattice.
-- Attenuating the held `endpoint 9 [read, write]` to keep only `[read]` STRICTLY DROPS `write`:
#eval capAuthConferred (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write]))  -- [read] ⊊ [read,write]
-- the genuine non-amplification fires on this concrete held cap (granted ⊆ held, REAL rights):
example : IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write])
    (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) :=
  attenuateF_non_amplifying [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])
-- ...and an AMPLIFYING grant is genuinely REJECTED: a `node 9` cap confers `control`, which the
-- held `endpoint 9 [read, write]` cap does NOT confer ⇒ it FAILS the non-amplification predicate:
example : ¬ IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9) :=
  amplifyingF_rejected (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9)
    Auth.control (by decide) (by decide)

-- (2) ATTENUATE: narrow actor 0's slot-1 cap (`endpoint 9 [read, write]`) to keep only `read`.
--   COMMITS, balance-neutral, and the slot's cap is genuinely narrowed:
#eval (execFullA fmaA (.attenuateA 0 1 [Auth.read])).isSome                           -- true
#eval ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map (fun s => s.kernel.caps 0)).getD []
--                                                       -- [node 7, endpoint 9 [read]] (write DROPPED)
#eval (execFullA fmaA (.attenuateA 0 1 [Auth.read])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (UNCHANGED)

-- (3) DROP-REF: holder 0 GC-drops its reference to 7. Always commits, balance-neutral, edge gone:
#eval (execFullA fmaA (.dropRefA 0 7)).isSome                                         -- true
#eval (execFullA fmaA (.dropRefA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)

-- (4) REVOKE-DELEGATION: parent drops child 0's edge to 7. Always commits, balance-neutral:
#eval (execFullA fmaA (.revokeDelegationA 0 7)).isSome                                -- true
#eval (execFullA fmaA (.revokeDelegationA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)

-- (5) VALIDATE-HANDOFF: actor 0 (holds connectivity to 7) accepts a handoff introducing 1 to 7.
--   COMMITS (the handoff IS a Granovetter introduce), balance-neutral. An AMPLIFYING handoff (no
--   held connectivity) is REJECTED ⇒ none (the `granted ≤ held` gate dregg1 was missing):
#eval (execFullA fmaA (.validateHandoffA 0 1 7)).isSome                               -- true
#eval (execFullA fmaA (.validateHandoffA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)
#eval (execFullA fmaA (.validateHandoffA 5 1 7)).isSome                               -- false (FAIL-CLOSED)

-- (6) EXERCISE: actor 0 (holds `node 7`) exercises its cap to target 7. COMMITS; the cap GRAPH is
--   UNCHANGED (exercise reads, never edits); balance-neutral. An actor without the edge FAILS:
#eval (execFullA fmaA (.exerciseA 0 7)).isSome                                        -- true
#eval ((execFullA fmaA (.exerciseA 0 7)).map (fun s => s.kernel.caps 0)).getD []
--                                                       -- [node 7, endpoint 9 [read,write]] (UNCHANGED)
#eval (execFullA fmaA (.exerciseA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)
#eval (execFullA fmaA (.exerciseA 5 7)).isSome                                        -- false (FAIL-CLOSED)

-- A MIXED authority turn: introduce (adds edge) + attenuate (narrows) + exercise (reads) +
--   revoke-delegation (removes) — ALL balance-neutral ⇒ (105, 7) preserved across the turn:
def authMixedTurn : List FullActionA :=
  [ .introduceA 0 1 7
  , .attenuateA 0 1 [Auth.read]
  , .exerciseA 0 7
  , .revokeDelegationA 0 7 ]

#eval (execFullTurnA fmaA authMixedTurn).isSome                                       -- true (all commit)
#eval (turnLedgerDeltaAsset authMixedTurn 0, turnLedgerDeltaAsset authMixedTurn 1)    -- (0, 0)
#eval (execFullTurnA fmaA authMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (CONSERVED)

/-! ## §13-supply (META-FILL C Wave 3) — Non-vacuity for ACCOUNT-GROWTH + SUPPLY: `createCell` GROWS
`accounts` yet `recTotalAsset` is UNCHANGED (born EMPTY ⇒ NEUTRAL); `bridgeMint` discloses `+value` at
ONE asset and leaves every other asset FIXED (no cross-asset laundering); unauthorized create/mint
FAIL-CLOSED. A 2-asset state where actor 9 holds the privileged `node 0`/`node 1`/`node 2` caps (can mint
into live cells 0,1 and create the fresh cell 2). -/

/-- The supply fixture: accounts {0,1}; cell 0 = 100 of asset 0 + 7 of asset 1, cell 1 = 5 of asset 0.
Actor 9 holds `node 0`,`node 1`,`node 2` (create/mint authority over cells 0,1 and the fresh 2). -/
def fmaSup : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply + account set: asset 0 = 105, asset 1 = 7, accounts {0,1}.
#eval (recTotalAsset fmaSup.kernel 0, recTotalAsset fmaSup.kernel 1)                  -- (105, 7)
#eval (decide (0 ∈ fmaSup.kernel.accounts), decide (1 ∈ fmaSup.kernel.accounts),
       decide (2 ∈ fmaSup.kernel.accounts))                                          -- (true, true, false)

-- ★ THE ACCOUNT-GROWTH WITNESS: actor 9 (holds `node 2`) creates the FRESH cell 2 — COMMITS,
--   `accounts` GROWS {0,1} → {0,1,2} (cell 2 now live), YET `recTotalAsset` is UNCHANGED at (105, 7)
--   for BOTH assets (born EMPTY ⇒ conservation-NEUTRAL):
#eval (execFullA fmaSup (.createCellA 9 2)).isSome                                    -- true
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => decide (2 ∈ s.kernel.accounts))  -- some true (GREW)
#eval (execFullA fmaSup (.createCellA 9 2)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (NEUTRAL)
-- ...and the fresh cell 2 is born EMPTY in every asset (bal-reset):
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => (s.kernel.bal 2 0, s.kernel.bal 2 1))  -- some (0, 0)
-- ...and grows the receipt chain by exactly one row:
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => s.log.length)               -- some 1
-- An UNAUTHORIZED creator (actor 0 holds no create cap) is REJECTED (fail-closed):
#eval (execFullA fmaSup (.createCellA 0 2)).isSome                                    -- false
-- A NON-FRESH id (cell 1 already live) is REJECTED (the freshness gate has TEETH):
#eval (execFullA fmaSup (.createCellA 9 1)).isSome                                    -- false

-- SPAWN: actor 9 spawns child 2 (born EMPTY) with a delegated `node 7` cap — COMMITS, NEUTRAL,
--   and the child carries its disclosed authority snapshot (`node 7` at the head):
#eval (execFullA fmaSup (.spawnA 9 2 7)).isSome                                       -- true
#eval (execFullA fmaSup (.spawnA 9 2 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (NEUTRAL)
#eval ((execFullA fmaSup (.spawnA 9 2 7)).map (fun s => s.kernel.caps 2)).getD []     -- [Cap.node 7]
#eval (execFullA fmaSup (.spawnA 9 2 7)).map (fun s => decide (2 ∈ s.kernel.accounts))  -- some true (GREW)

-- ★ THE BRIDGE-MINT DISCLOSURE WITNESS: actor 9 (holds `node 0`) bridge-mints +40 of ASSET 1 into the
--   live cell 0 — COMMITS, asset 1 RISES by exactly 40 (7 → 47) while asset 0 is LEFT FIXED (105):
#eval (execFullA fmaSup (.bridgeMintA 9 0 1 40)).isSome                               -- true
#eval (execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 47) (+40 at asset 1 ONLY)
-- ...the disclosed delta is `+40` at asset 1, `0` everywhere else (no cross-asset laundering):
#eval (ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 0, ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 1)  -- (0, 40)
-- ...and the bridge receipt discloses the +40 inflow:
#eval ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0  -- 40
-- An UNAUTHORIZED bridge-mint (actor 0, no mint cap) is REJECTED (the LOCAL gate, independent of the
--   §8 foreign-finality portal):
#eval (execFullA fmaSup (.bridgeMintA 0 0 1 40)).isSome                               -- false

-- A MIXED supply turn: createCell 2 (neutral growth) + bridgeMint +40 of asset 1 into cell 0
--   (disclosed) → asset 0 conserved (105), asset 1 rises by exactly 40 (7 → 47):
def supplyMixedTurn : List FullActionA :=
  [ .createCellA 9 2
  , .bridgeMintA 9 0 1 40 ]

#eval (execFullTurnA fmaSup supplyMixedTurn).isSome                                   -- true (all commit)
#eval (turnLedgerDeltaAsset supplyMixedTurn 0, turnLedgerDeltaAsset supplyMixedTurn 1)  -- (0, 40)
#eval (execFullTurnA fmaSup supplyMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 47)

/-! ### §MA-escrow #eval — the COMBINED per-asset holding-store on the executed dispatch (`META-FILL C`,
closing `#121`): a committed-escrow lock+settle conserves `recTotalAssetWithEscrow` per-asset (with the
held value genuinely non-zero at the locked asset, the OTHER asset untouched); noteCreate→noteSpend
round-trip; double-spend fail-closed. -/

-- ★ COMMITTED-ESCROW LOCK of 5 of ASSET 1 from cell 0 (holds 7 of asset 1) → recipient 1 (id 9),
--   actor 9 authorized over 0: bare ledger DROPS at asset 1 (7→2), held RISES to 5, COMBINED FIXED at 7.
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5)).isSome                  -- true
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5)).map
        (fun s => (recTotalAsset s.kernel 1, escrowHeldAsset s.kernel 1))             -- some (2, 5) — bare DOWN, held UP at asset 1
-- ...the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0 (no cross-asset laundering):
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0))  -- some (7, 105) — CONSERVED both
-- ...the COMBINED ledgerDeltaAsset is 0 at every asset (combined-conserving, NOT bare-bal-conserving):
#eval (ledgerDeltaAsset (.createCommittedEscrowA 9 9 0 1 1 5) 0,
       ledgerDeltaAsset (.createCommittedEscrowA 9 9 0 1 1 5) 1)                      -- (0, 0)
-- ★ SETTLE (release to recipient 1, live): COMBINED stays (105, 7), held returns to 0.
#eval ((execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5)).bind
        (fun s => execFullA s (.releaseCommittedEscrowA 9 9))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1))                                       -- some (7, 105, 0) — round-trip CONSERVED
-- ...the held value at asset 1 is GENUINELY non-zero mid-flight while asset 0 is untouched (guard):
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5)).map
        (fun s => (escrowHeldAsset s.kernel 1, escrowHeldAsset s.kernel 0))           -- some (5, 0)
-- ★ NOTE CREATE→SPEND round-trip: create grows commitments (42), spend grows nullifiers (77) — distinct sets;
--   the executed dispatch is bal-NEUTRAL (combined fixed):
#eval ((execFullA fmaSup (.noteCreateA 42 9)).bind (fun s => execFullA s (.noteSpendA 77 9))).map
        (fun s => (s.kernel.commitments.contains 42, s.kernel.nullifiers.contains 77,
                   recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (true, true, 105, 7)
-- ★ DOUBLE-SPEND fail-closed: spending nullifier 77 twice on the executed dispatch REJECTS:
#eval ((execFullA fmaSup (.noteSpendA 77 9)).bind (fun s => execFullA s (.noteSpendA 77 9))).isSome  -- false

/-! ### §MA-bridge #eval (Wave-5 PHASE-BRIDGE) — the cross-chain bridge lock/finalize/cancel on the
executed dispatch over the SHARED escrow holding-store. LOCK conserves the COMBINED measure (debit + park
the bridge-tagged record); FINALIZE BURNS it (the value LEFT for the other chain — COMBINED DROPS by the
disclosed amount at the bridged asset, the OTHER asset fixed); CANCEL refunds (combined conserved);
unauthorized/double-finalize fail-closed. `fmaSup`: cell 0 holds 100 of asset 0 + 7 of asset 1; actor 9
holds `node 0` (authority over cell 0). -/

-- ★ BRIDGE LOCK of 30 of ASSET 1 from cell 0 → destination 1 (bridge id 7), actor 9 authorized over 0:
--   bare ledger DROPS at asset 1 (7→ wait: cell0 has 7 of asset1, lock 5), held RISES, COMBINED FIXED.
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).isSome                              -- true
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => (recTotalAsset s.kernel 1, escrowHeldAsset s.kernel 1))              -- some (2, 5) — bare DOWN, held UP at asset 1
-- ...the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0 (the lock is combined-neutral):
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0))  -- some (7, 105) — CONSERVED both
-- ...the parked record carries the BRIDGE tag (it is in the SHARED escrow store, tagged true):
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => s.kernel.escrows.map (fun r => (r.id, r.amount, r.asset, r.bridge)))  -- some [(7, 5, 1, true)]
-- ...the LOCK's COMBINED ledgerDeltaAsset is 0 at every asset (combined-conserving):
#eval (ledgerDeltaAsset (.bridgeLockA 7 9 0 1 1 5) 0, ledgerDeltaAsset (.bridgeLockA 7 9 0 1 1 5) 1)  -- (0, 0)
-- ★ LOCK then CANCEL (refund to originator 0, live): COMBINED stays (105, 7); held returns to 0; the
--   bare bal at asset 1 returns to 7 (the value came BACK):
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeCancelA 7 9))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1, recTotalAsset s.kernel 1))             -- some (7, 105, 0, 7) — REFUND round-trip CONSERVED
-- ★ LOCK then FINALIZE (the §8 confirmation arrived — the value LEFT for the other chain): COMBINED
--   DROPS by exactly 5 at asset 1 (7→2), asset 0 FIXED at 105; held drops to 0; bare bal stays at 2:
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1, recTotalAsset s.kernel 1))             -- some (2, 105, 0, 2) — COMBINED -5 at asset 1, asset 0 FIXED
-- ...the FINALIZE's disclosed delta is -5 at asset 1, 0 at asset 0 (the disclosed OUTFLOW, no laundering):
#eval (ledgerDeltaAsset (.bridgeFinalizeA 7 9 1 5) 0, ledgerDeltaAsset (.bridgeFinalizeA 7 9 1 5) 1)  -- (0, -5)
-- DOUBLE-FINALIZE fail-closed (the record is already resolved):
#eval (((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).isSome                      -- false
-- MISMATCHED-amount finalize fail-closed (disclosed 99 ≠ parked 5 — the receipt-vs-pending check):
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 99))).isSome                     -- false
-- UNAUTHORIZED lock fail-closed (actor 0 holds no authority over... actually owns itself; use actor 5):
#eval (execFullA fmaSup (.bridgeLockA 7 5 0 1 1 5)).isSome                             -- false (actor 5 unauthorized over cell 0)
-- A MIXED bridge turn: lock 5 of asset 1 then finalize it → asset 1 net -5 (7→2), asset 0 conserved:
def bridgeMixedTurn : List FullActionA :=
  [ .bridgeLockA 7 9 0 1 1 5
  , .bridgeFinalizeA 7 9 1 5 ]

#eval (execFullTurnA fmaSup bridgeMixedTurn).isSome                                    -- true (all commit)
#eval (turnLedgerDeltaAsset bridgeMixedTurn 0, turnLedgerDeltaAsset bridgeMixedTurn 1) -- (0, -5)
#eval (execFullTurnA fmaSup bridgeMixedTurn).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (105, 2) — asset 0 fixed, asset 1 -5

end Dregg2.Exec.TurnExecutorFull
