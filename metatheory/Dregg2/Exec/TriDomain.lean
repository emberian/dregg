/-
# Dregg2.Exec.TriDomain — THREE-DOMAIN conservation, the executable analog of dregg1's `atomic.rs`.

`Spec/Conservation.lean` proves the per-domain `Σδ = 0` law generically (over an `AddCommMonoid`),
and `Exec/TurnExecutorFull.lean` proves the executable `execFull` tracks the BALANCE domain EXACTLY
(`execFull_ledger`: `recTotal` moves by `ledgerDelta`). But dregg1's turn executor
(`turn/src/executor/atomic.rs`) runs an `excess == 0` check in THREE INDEPENDENT domains, and a
turn fails if ANY of them fails:

  1. **BALANCE** (fungible value, `ℤ`) — already modelled as `recTotal` / `ledgerDelta`.
  2. **AUTHORITY** (capabilities / delegations) — a grant CREATES an edge, a revoke DESTROYS one;
     the authority "ledger" is now a REAL on-state count of the edge-bearing caps actually present
     in `s.kernel.caps` (the same table `execGraph` reads), folded over a finite holder domain.
  3. **METADATA** (nonces / timestamps / the receipt chain) — monotone-advance, DISCLOSED. Every
     committed action advances the observation chain by exactly one row (`execFull_obsadvance`);
     metadata never retreats.

This module LIFTS conservation from the one balance domain to all three, as a single
`TriMeasure` (three `ℤ`-valued readings of a `RecChainedState`) and a `TriConserved` predicate
whose per-domain obligations are DRIVEN BY THE `LinearityClass` COLOR of the action. The headline
`triConserved_of_execFull` proves EVERY committed `FullAction` satisfies its three per-domain
obligations simultaneously — the executable 3-domain analog of `atomic.rs`'s three `excess` gates.
It reuses the already-proven `execFull_ledger` / `execFull_delegate_addEdge` /
`execFull_revoke_removeEdge` / `execFull_chainlink` / `execFull_obsadvance` spine verbatim.

## The authority measure is now a FUNCTION OF THE ACTUAL CAP TABLE (de-vacuified)

The earlier draft carried `authorityCount` as a FREE `ℤ` parameter, so the authority conjunct of
`triConserved_of_execFull` reduced to `x = x` and said nothing — the count was never read off the
state. This is fixed here. `authMeasure s H` reads the REAL `s.kernel.caps` table: it sums, over a
FINITE holder domain `H : Finset CellId`, the number of *edge-bearing* cap entries each holder holds
(`capConfersEdge` = "this cap confers a connectivity edge to its target", the exact entry
`execGraph` reconstructs into a graph edge). Because the cap graph is over an infinite `Label` (no
free cardinality), the measure folds over the finite on-state list data — the faithful, non-vacuous
choice the audit prescribes.

The authority conjunct is now a GENUINE fact tied to the cap-graph edit:
  * **frame kinds** (`balance` / `mint` / `burn`) leave `caps` UNCHANGED, so the measure is
    UNCHANGED — `authMeasure s' H = authMeasure s H` (a real `Δ = 0`, proved from the raw-`caps`
    frame, not from `rfl` on a free param);
  * **`delegate _ rec _`** runs `grant` which conses ONE `node t` cap (an edge-bearing entry) onto
    `rec`'s slot, so the measure rises by EXACTLY `1` when `rec ∈ H` (and is unchanged off-domain) —
    the disclosed `+1` authority inflow, pinned to the structural `addEdge`;
  * **`revoke holder _`** filters OUT the `t`-conferring caps from `holder`, so the measure does NOT
    increase — `authMeasure s' H ≤ authMeasure s H`, the one-way terminal subtraction, pinned to the
    structural `removeEdge`.

## Why each domain's color obligation is what it is (the under-modelling this closes)

A turn could previously pass balance-`Σ = 0` while silently diverging in authority: nothing in the
balance ledger SEES a stray grant. Here the three domains conserve INDEPENDENTLY (the
`Spec.multi_domain_independent` discipline), so a grant that does not advance the authority measure
by its disclosed `+1`, or a balance move that perturbs the authority measure, is a 3-domain
violation even when balance alone checks out — and the authority measure is now READ OFF THE STATE.

  * **Conservative** (`transfer`, the balance/effect kind) ⇒ balance `Σδ = 0` AND authority measure
    UNCHANGED AND metadata advances by one.
  * **Generative / grant** (`delegate`) ⇒ authority measure INCREASES by the disclosed `+1` (a fresh
    edge-bearing cap, `addEdge`), balance UNCHANGED, metadata advances.
  * **Terminal / revoke** (`revoke`) ⇒ authority measure does NOT increase (`removeEdge`), balance
    UNCHANGED, metadata advances. One-way subtraction.
  * **Generative / Annihilative supply** (`mint` / `burn`) ⇒ balance moves by the disclosed `±amt`,
    authority measure UNCHANGED, metadata advances.
  * **Monotonic (metadata, all kinds)** ⇒ the metadata measure strictly advances and NEVER retreats.

## Discipline (REORIENT §6)
No `axiom`/`admit`/`native_decide`/`sorry`. `#assert_axioms` on every keystone. Pure, computable,
`#eval`-able non-vacuity. Reuses `TurnExecutorFull` / `AuthTurn` / `Spec.Conservation`; edits nothing.
Verified standalone: `lake env lean Dregg2/Exec/TriDomain.lean`.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.TriDomain

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps)
open Dregg2.Exec (grant confersEdgeTo)
open Dregg2.CatalogInstances (effectLinearity)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.Spec (Domain conservedInDomain LinearityClass execGraph ExecRights addEdge removeEdge)

/-- Pointwise monotonicity of a finite `ℤ`-sum (a local re-derivation by `Finset.induction`, so this
module stays self-contained over the minimal `BigOperators` import). Used to lift the per-holder
`≤` of a revoke to the whole `authMeasure` fold. -/
private theorem sum_le_sum_local (H : Finset CellId) (f g : CellId → ℤ)
    (hfg : ∀ i ∈ H, f i ≤ g i) : (∑ i ∈ H, f i) ≤ ∑ i ∈ H, g i := by
  classical
  induction H using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      have h1 : f x ≤ g x := hfg x (Finset.mem_insert_self x s)
      have h2 : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i :=
        ih (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
      omega

/-! ## §0 — The AUTHORITY MEASURE: a real fold over the on-state cap table.

The cap graph is over an infinite `Label`, so there is no free cardinality. But the *data* the graph
is reconstructed from is finite per holder (`caps h : List Cap`), and we fold over a finite holder
domain. `capConfersEdge c` decides whether the cap entry `c` is one `execGraph` turns into an edge
(a `node t`, or an `endpoint t` carrying `write`); `authMeasure s H` counts those entries over `H`.
This IS a reading of the real `s.kernel.caps`, not a free parameter. -/

/-- **`capConfersEdge c`** — does the cap entry `c` confer a connectivity edge to its OWN target (the
`execGraph` test applied to `c.target`)? A `node t` cap and an `endpoint t`-with-`write` cap do; a
`null` cap (and a write-less endpoint) do not. This is exactly the per-entry predicate `execGraph`
uses (`confersEdgeTo c.target c`), so counting these entries counts the graph's edge witnesses. -/
def capConfersEdge : Dregg2.Authority.Cap → Bool
  | .null            => false
  | .node _          => true
  | .endpoint _ r    => r.contains Dregg2.Authority.Auth.write

/-- A freshly granted `node t` cap is edge-bearing (it is what `grant` conses for a delegation, and
what `addEdge` adds): `capConfersEdge (.node t) = true`. -/
@[simp] theorem capConfersEdge_node (t : CellId) :
    capConfersEdge (.node t) = true := rfl

/-- **`authMeasure s H`** — the AUTHORITY-domain measure: the number of edge-bearing cap entries the
holders in the finite domain `H` actually hold, read straight off `s.kernel.caps`. The on-state,
non-vacuous count the authority `excess` gate ranges over (grants raise it, revokes lower it, value
and supply leave it fixed). -/
def authMeasure (s : RecChainedState) (H : Finset CellId) : ℤ :=
  ∑ h ∈ H, (((s.kernel.caps h).filter (fun c => capConfersEdge c)).length : ℤ)

/-! ## §1 — `TriMeasure`: the three `ℤ`-valued domain readings of a chained state.

`atomic.rs` carries an `excess` accumulator per domain. We read a `RecChainedState` into three
`ℤ` measures — the conserved quantities the three `excess` gates range over. -/

/-- **The three conserved measures of a chained state**, one per dregg1 conservation domain:
  * `balanceCount`  — the total `balance` field across live accounts (`recTotal`, the fungible value);
  * `authorityCount`— the on-state count of edge-bearing caps (`authMeasure`), grants raise, revokes lower;
  * `metadataAdvance`— the receipt-chain length (the monotone observation/nonce clock).
These are the executable shadows of `atomic.rs`'s three per-domain `excess` accumulators. -/
structure TriMeasure where
  /-- BALANCE domain: total `balance` field (`recTotal`). -/
  balanceCount    : ℤ
  /-- AUTHORITY domain: on-state edge-bearing cap count (`authMeasure`). -/
  authorityCount  : ℤ
  /-- METADATA domain: receipt-chain length (the monotone clock). -/
  metadataAdvance : ℤ
  deriving DecidableEq, Repr

/-- Read the three domain measures off a chained state, over a finite holder domain `H`. The
authority count is `authMeasure s H` — a REAL function of `s.kernel.caps`, NOT a free parameter:
this is the de-vacuification, the authority reading is now tied to the actual cap graph. -/
def measure (s : RecChainedState) (H : Finset CellId) : TriMeasure where
  balanceCount    := recTotal s.kernel
  authorityCount  := authMeasure s H
  metadataAdvance := (s.log.length : ℤ)

/-! ## §2 — Per-`FullAction` per-domain deltas, DRIVEN BY THE LINEARITY COLOR.

Each `FullAction` carries a color (`triColor`); the color DICTATES its delta in each domain. This is
where the coloring of `CatalogEffects` / `Spec.Conservation` becomes a per-domain obligation. -/

/-- **The linearity color of a `FullAction`** — the color that drives its per-domain obligations. -/
def triColor : FullAction → LinearityClass
  | .balance _      => .Conservative
  | .delegate _ _ _ => .Generative
  | .revoke _ _     => .Terminal
  | .mint _ _ _     => .Generative
  | .burn _ _ _     => .Annihilative

/-- **BALANCE-domain delta** — exactly `TurnExecutorFull.ledgerDelta`. -/
def balanceDelta : FullAction → ℤ := ledgerDelta

/-- **AUTHORITY-domain delta** — `+1` for a grant (`delegate`), `−1` for a revoke (`Terminal`), `0`
for every value/supply kind (authority FRAMED). For `delegate`/`revoke` this is the DISCLOSED color
delta; the realized on-state measure move is pinned to it by the theorems below (`= +1` for a grant
whose recipient is in domain; `≤ 0` for a revoke — the one-way terminal subtraction). -/
def authorityDelta : FullAction → ℤ
  | .balance _      => 0
  | .delegate _ _ _ => 1
  | .revoke _ _     => -1
  | .mint _ _ _     => 0
  | .burn _ _ _     => 0

/-- **METADATA-domain advance** — `+1` for EVERY committed action. -/
def metadataDelta : FullAction → ℤ := fun _ => 1

/-! ## §3 — `TriConserved`: the per-color, per-domain obligation bundle.

The 3-domain analog of `TurnExecutorFull.fullActionInv`: a committed action must move EACH domain
measure by its color-dictated delta. The AUTHORITY conjunct is now a GENUINE relation on the
on-state `authorityCount` (not `x = x`): for generative grants the count rises by the disclosed
`+1`, for everything non-revoke the count moves by `authorityDelta` exactly, and for the terminal
revoke the count does NOT increase. -/

/-- **The tri-domain conservation obligation for one committed `FullAction`.**
  * BALANCE: `post.balanceCount = pre.balanceCount + balanceDelta fa`;
  * AUTHORITY: `post.authorityCount = pre.authorityCount + authorityDelta fa` for the non-terminal
    kinds (balance / delegate / mint / burn — an EXACT on-state move), and
    `post.authorityCount ≤ pre.authorityCount` for the terminal `revoke` (one-way subtraction);
  * METADATA: `post.metadataAdvance = pre.metadataAdvance + 1` AND strictly advances.
The authority conjunct now READS the on-state measure, so it is non-vacuous. -/
def TriConserved (pre post : TriMeasure) (fa : FullAction) : Prop :=
  (post.balanceCount = pre.balanceCount + balanceDelta fa) ∧
  (match fa with
   | .revoke _ _ => post.authorityCount ≤ pre.authorityCount
   | _           => post.authorityCount = pre.authorityCount + authorityDelta fa) ∧
  (post.metadataAdvance = pre.metadataAdvance + 1 ∧
   pre.metadataAdvance < post.metadataAdvance)

/-! ## §4 — The AUTHORITY-domain frame / edit facts (pinning the measure to the cap-table edit). -/

/-- A committed `balance` action leaves the cap table UNCHANGED (`recKExec` rewrites only the
`balance` field — `recKExec_frame` gives `caps` equality). PROVED. -/
theorem balance_caps_eq (s s' : RecChainedState) (a : Action)
    (h : execFull s (.balance a) = some s') : s'.kernel.caps = s.kernel.caps := by
  simp only [execFull] at h
  unfold recCexec at h
  cases hk : recKExec s.kernel a.move with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact (recKExec_frame s.kernel k' a.move hk).2

/-- A committed `mint` leaves the cap table UNCHANGED (`recKMint` rewrites only the `cell` field). PROVED. -/
theorem mint_caps_eq (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.mint actor cell amt) = some s') : s'.kernel.caps = s.kernel.caps := by
  simp only [execFull, recCMint] at h
  cases hm : recKMint s.kernel actor cell amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKMint at hm
      by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ s.kernel.accounts
      · rw [if_pos hg] at hm; simp only [Option.some.injEq] at hm; rw [← hm]
      · rw [if_neg hg] at hm; exact absurd hm (by simp)

/-- A committed `burn` leaves the cap table UNCHANGED (`recKBurn` rewrites only the `cell` field). PROVED. -/
theorem burn_caps_eq (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.burn actor cell amt) = some s') : s'.kernel.caps = s.kernel.caps := by
  simp only [execFull, recCBurn] at h
  cases hb : recKBurn s.kernel actor cell amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKBurn at hb
      by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ amt
          ∧ amt ≤ balOf (s.kernel.cell cell) ∧ cell ∈ s.kernel.accounts
      · rw [if_pos hg] at hb; simp only [Option.some.injEq] at hb; rw [← hb]
      · rw [if_neg hg] at hb; exact absurd hb (by simp)

/-- The cap-table FRAME ⇒ the authority MEASURE is unchanged (the `Δ = 0` reading is HONEST: it reads
the same table). The on-state version of the framing facts — `caps` equal ⇒ the fold is equal. -/
theorem authMeasure_of_caps_eq (s s' : RecChainedState) (H : Finset CellId)
    (hc : s'.kernel.caps = s.kernel.caps) : authMeasure s' H = authMeasure s H := by
  unfold authMeasure; rw [hc]

/-- **`delegate` raises the measure by exactly `1` when the recipient is in domain.** `recKDelegate`
commits by `grant`-ing a fresh `node t` cap (edge-bearing) onto `rec`'s slot; the filtered length of
`rec`'s slot rises by one, every other holder is untouched. The on-state realization of the disclosed
`+1` grant inflow — pinned to the structural `addEdge` (`execFull_delegate_addEdge`). PROVED. -/
theorem delegate_authMeasure (s s' : RecChainedState) (del rec t : CellId) (H : Finset CellId)
    (hrec : rec ∈ H) (h : execFull s (.delegate del rec t) = some s') :
    authMeasure s' H = authMeasure s H + 1 := by
  -- Extract the committed caps edit: `s'.kernel.caps = grant s.kernel.caps rec (.node t)`.
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      have hcaps : k'.caps = grant s.kernel.caps rec (.node t) := by
        unfold recKDelegate at hd
        by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
        · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; rw [← hd]
        · rw [if_neg hg] at hd; exact absurd hd (by simp)
      -- The measure splits off `rec`'s summand; on `rec` the filtered length is `+1`, elsewhere equal.
      unfold authMeasure
      simp only [hcaps]
      -- pointwise: `grant caps rec (.node t) h = if h = rec then (.node t) :: caps h else caps h`.
      have hpt : ∀ h : CellId,
          (((grant s.kernel.caps rec (.node t) h).filter (fun c => capConfersEdge c)).length : ℤ)
            = (((s.kernel.caps h).filter (fun c => capConfersEdge c)).length : ℤ)
              + (if h = rec then 1 else 0) := by
        intro h
        unfold grant
        by_cases hh : h = rec
        · subst hh
          rw [if_pos rfl, List.filter_cons]
          simp only [capConfersEdge_node, if_true, List.length_cons]
          push_cast; ring
        · simp only [if_neg hh, add_zero]
      rw [Finset.sum_congr rfl (fun h _ => hpt h)]
      rw [Finset.sum_add_distrib]
      rw [Dregg2.Exec.sum_indicator H rec 1 hrec]

/-- **`revoke` does NOT raise the measure** (the one-way terminal subtraction). `recKRevokeTarget`
FILTERS `holder`'s slot (dropping the `t`-conferring caps), keeping every other slot; a filtered
list is no longer, so each summand is `≤` its old value. The on-state realization of `removeEdge`'s
subtraction — `authMeasure s' H ≤ authMeasure s H`. PROVED. -/
theorem revoke_authMeasure (s s' : RecChainedState) (holder t : CellId) (H : Finset CellId)
    (h : execFull s (.revoke holder t) = some s') :
    authMeasure s' H ≤ authMeasure s H := by
  simp only [execFull, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  unfold authMeasure recKRevokeTarget
  apply sum_le_sum_local
  intro x _
  by_cases hh : x = holder
  · subst hh
    -- filtering the slot first by the revoke predicate only SHRINKS the subsequent
    -- `capConfersEdge`-filtered length: the pre-filtered slot is a sublist of the slot, and
    -- `capConfersEdge`-filtering preserves sublists, so the count cannot rise.
    simp only [if_true]
    exact_mod_cast (List.Sublist.filter (fun c => capConfersEdge c) List.filter_sublist).length_le
  · simp only [if_neg hh]; exact le_refl _

/-- **The authority-domain edit, per kind — PROVED.** The cap graph after a committed `FullAction`:
UNCHANGED for value/supply (`Δ = 0`), `addEdge` for a grant (`+1`), `removeEdge` for a revoke (`−1`).
This is what makes the signed `authorityDelta` an honest count of the structural edit. -/
theorem authority_graph_edit (s s' : RecChainedState) (fa : FullAction) (h : execFull s fa = some s') :
    (match fa with
     | .balance _          => execGraph s'.kernel.caps = execGraph s.kernel.caps
     | .delegate _ rec t   => execGraph s'.kernel.caps
                                = addEdge (execGraph s.kernel.caps) rec ⟨t, ()⟩
     | .revoke holder t    => execGraph s'.kernel.caps
                                = removeEdge (execGraph s.kernel.caps) holder ⟨t, ()⟩
     | .mint _ _ _         => execGraph s'.kernel.caps = execGraph s.kernel.caps
     | .burn _ _ _         => execGraph s'.kernel.caps = execGraph s.kernel.caps) := by
  cases fa with
  | balance a           => exact congrArg execGraph (balance_caps_eq s s' a h)
  | delegate del rec t  => exact execFull_delegate_addEdge s s' del rec t h
  | revoke holder t     => exact execFull_revoke_removeEdge s s' holder t h
  | mint actor cell amt => exact congrArg execGraph (mint_caps_eq s s' actor cell amt h)
  | burn actor cell amt => exact congrArg execGraph (burn_caps_eq s s' actor cell amt h)

/-! ## §5 — THE HEADLINE: every committed `FullAction` is tri-domain conserved.

The executable 3-domain analog of `atomic.rs`'s three `excess == 0` gates: a single committed action
moves all three measures by their color-dictated deltas at once. Reuses `execFull_ledger` (balance)
and `execFull_obsadvance` (metadata) verbatim; the authority delta is now the REAL on-state
`authMeasure` move (§4), NOT a free parameter. -/

/-- The metadata measure (chain length) advances by exactly one on any committed action. PROVED. -/
theorem metadata_advance (s s' : RecChainedState) (fa : FullAction) (h : execFull s fa = some s') :
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 := by
  have := execFull_obsadvance s s' fa h
  rw [this]; push_cast; ring

/-- **`triConserved_of_execFull` — THE 3-DOMAIN CONSERVATION LAW (PROVED, NON-VACUOUS).** For any
committed `FullAction` and any finite holder domain `H` containing the would-be recipient `rec` of a
delegation, the post-state's three domain measures relate to the pre-state's by the color-dictated
per-domain facts: balance by `balanceDelta` (`execFull_ledger`), AUTHORITY by the REAL on-state
`authMeasure` move (`= +authorityDelta` for non-revoke kinds, `≤` for the terminal revoke — §4),
metadata by `+1` strictly monotone (`execFull_obsadvance`). The authority conjunct now READS
`s.kernel.caps` (it is `authMeasure`, a fold over the actual table) — the `x = x` vacuity is gone.

The `recipientInDomain` hypothesis is `True` for every non-delegate kind (their authority deltas do
not depend on a recipient) and is exactly `rec ∈ H` for a delegation — the natural "the recipient is
among the counted holders" side condition that lets the `+1` grant be REALIZED on the measure. -/
theorem triConserved_of_execFull (s s' : RecChainedState) (fa : FullAction) (H : Finset CellId)
    (recipientInDomain : match fa with | .delegate _ rec _ => rec ∈ H | _ => True)
    (h : execFull s fa = some s') :
    TriConserved (measure s H) (measure s' H) fa := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- BALANCE: `recTotal` moves by `ledgerDelta = balanceDelta`.
    simp only [measure, balanceDelta]
    exact execFull_ledger s s' fa h
  · -- AUTHORITY: the REAL on-state `authMeasure` move, per kind.
    cases fa with
    | balance a =>
        simp only [measure, authorityDelta]
        rw [authMeasure_of_caps_eq s s' H (balance_caps_eq s s' a h)]; ring
    | delegate del rec t =>
        simp only [measure, authorityDelta]
        exact delegate_authMeasure s s' del rec t H recipientInDomain h
    | revoke holder t =>
        simp only [measure]
        exact revoke_authMeasure s s' holder t H h
    | mint actor cell amt =>
        simp only [measure, authorityDelta]
        rw [authMeasure_of_caps_eq s s' H (mint_caps_eq s s' actor cell amt h)]; ring
    | burn actor cell amt =>
        simp only [measure, authorityDelta]
        rw [authMeasure_of_caps_eq s s' H (burn_caps_eq s s' actor cell amt h)]; ring
  · -- METADATA advance-by-one.
    simp only [measure]
    exact metadata_advance s s' fa h
  · -- METADATA strict monotonicity.
    simp only [measure]
    have := metadata_advance s s' fa h
    omega

/-! ## §6 — Per-color obligation specializations (the color → domain dictionary, PROVED).

The headline carries all three deltas for any kind; here we read off, per color, the precise
obligation each domain incurs — now with the AUTHORITY obligation stated on the REAL `authMeasure`. -/

/-- **Conservative (`balance`/transfer): balance Σ=0 ∧ authority measure unchanged ∧ metadata advances.**
The value move is paired, the cap table is FRAMED so the authority MEASURE is preserved (read off the
identical table), the chain grows. PROVED. -/
theorem conservative_obligation (s s' : RecChainedState) (a : Action) (H : Finset CellId)
    (h : execFull s (.balance a) = some s') :
    recTotal s'.kernel = recTotal s.kernel ∧
    authMeasure s' H = authMeasure s H ∧
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 := by
  refine ⟨?_, authMeasure_of_caps_eq s s' H (balance_caps_eq s s' a h), metadata_advance s s' (.balance a) h⟩
  have := execFull_ledger s s' (.balance a) h
  simpa [ledgerDelta] using this

/-- **Generative/grant (`delegate`): authority measure INCREASES by the disclosed `+1` (a fresh
`addEdge`) ∧ balance unchanged ∧ metadata advances** (for a recipient in the counted domain). The
disclosed authority inflow, REALIZED on the on-state count. PROVED. -/
theorem generative_grant_obligation (s s' : RecChainedState) (del rec t : CellId) (H : Finset CellId)
    (hrec : rec ∈ H) (h : execFull s (.delegate del rec t) = some s') :
    authorityDelta (.delegate del rec t) = 1 ∧
    authMeasure s' H = authMeasure s H + 1 ∧
    execGraph s'.kernel.caps = addEdge (execGraph s.kernel.caps) rec ⟨t, ()⟩ ∧
    recTotal s'.kernel = recTotal s.kernel ∧
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 := by
  refine ⟨rfl, delegate_authMeasure s s' del rec t H hrec h,
          execFull_delegate_addEdge s s' del rec t h, ?_, metadata_advance s s' _ h⟩
  have := execFull_ledger s s' (.delegate del rec t) h
  simpa [ledgerDelta] using this

/-- **Terminal/revoke (`revoke`): authority measure does NOT increase (a `removeEdge`) ∧ balance
unchanged ∧ metadata advances.** One-way authority subtraction, REALIZED on the on-state count. PROVED. -/
theorem terminal_revoke_obligation (s s' : RecChainedState) (holder t : CellId) (H : Finset CellId)
    (h : execFull s (.revoke holder t) = some s') :
    authorityDelta (.revoke holder t) = -1 ∧
    authMeasure s' H ≤ authMeasure s H ∧
    execGraph s'.kernel.caps = removeEdge (execGraph s.kernel.caps) holder ⟨t, ()⟩ ∧
    recTotal s'.kernel = recTotal s.kernel ∧
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 := by
  refine ⟨rfl, revoke_authMeasure s s' holder t H h,
          execFull_revoke_removeEdge s s' holder t h, ?_, metadata_advance s s' _ h⟩
  have := execFull_ledger s s' (.revoke holder t) h
  simpa [ledgerDelta] using this

/-- **Generative/Annihilative supply (`mint`/`burn`): balance moves by the disclosed `±amt` ∧
authority measure unchanged ∧ metadata advances ∧ the supply effect is a DISCLOSED non-conservation.**
The supply ops break balance-conservation by design, and leave the authority MEASURE fixed (the cap
table is framed). PROVED. -/
theorem supply_disclosed_obligation_mint (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (H : Finset CellId) (h : execFull s (.mint actor cell amt) = some s') :
    recTotal s'.kernel = recTotal s.kernel + amt ∧
    authMeasure s' H = authMeasure s H ∧
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 ∧
    (effectLinearity mintEffect).is_disclosed_non_conservation = true := by
  refine ⟨?_, authMeasure_of_caps_eq s s' H (mint_caps_eq s s' actor cell amt h),
          metadata_advance s s' _ h, mint_discloses⟩
  have := execFull_ledger s s' (.mint actor cell amt) h
  simpa [ledgerDelta] using this

/-- Burn analog of `supply_disclosed_obligation_mint`. PROVED. -/
theorem supply_disclosed_obligation_burn (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (H : Finset CellId) (h : execFull s (.burn actor cell amt) = some s') :
    recTotal s'.kernel = recTotal s.kernel - amt ∧
    authMeasure s' H = authMeasure s H ∧
    (s'.log.length : ℤ) = (s.log.length : ℤ) + 1 ∧
    (effectLinearity burnEffect).is_disclosed_non_conservation = true := by
  refine ⟨?_, authMeasure_of_caps_eq s s' H (burn_caps_eq s s' actor cell amt h),
          metadata_advance s s' _ h, burn_discloses⟩
  have := execFull_ledger s s' (.burn actor cell amt) h
  have hb : recTotal s'.kernel = recTotal s.kernel + (-amt) := by simpa [ledgerDelta] using this
  rw [hb]; ring

/-! ## §7 — Independence: the three domains conserve INDEPENDENTLY (no cross-domain leakage).

`atomic.rs`'s three gates are AND-ed: a turn passes iff balance ∧ authority ∧ metadata each pass; a
surplus in one cannot cover a deficit in another. We re-package the (non-revoke) deltas as a
`Domain → List ℤ` and read `TriConserved` back as the per-domain `Σ = 0` form of
`Spec.multi_domain_independent`. The authority residual is read on the REAL `authMeasure`. -/

/-- The per-domain realized-minus-expected residual of a committed action, as a singleton delta list
per domain — the executable `excess` of `atomic.rs`. -/
def triResiduals (pre post : TriMeasure) (fa : FullAction) : Domain → List ℤ
  | .balance   => [post.balanceCount    - (pre.balanceCount    + balanceDelta fa)]
  | .gas       => [post.metadataAdvance - (pre.metadataAdvance + metadataDelta fa)]
  | .note      => [post.authorityCount  - (pre.authorityCount  + authorityDelta fa)]
  | .crossCell => [0]

/-- **`triConserved_iff_all_domains_zero` — INDEPENDENCE for the NON-REVOKE (exact-authority) kinds
(PROVED).** For a `fa` that is not a revoke, `TriConserved` IFF every domain's residual nets to `0` —
the `Spec.multi_domain_independent` discipline realized over the three executable measures, the
authority residual now on the REAL `authMeasure`. (Revoke's authority obligation is the one-way `≤`,
not an exact `Σ = 0`, so it is handled by `terminal_revoke_obligation` directly.) -/
theorem triConserved_iff_all_domains_zero (pre post : TriMeasure) (fa : FullAction)
    (hfa : ∀ holder t, fa ≠ .revoke holder t) :
    TriConserved pre post fa ↔
      ∀ dom : Domain, conservedInDomain dom (triResiduals pre post fa dom) := by
  -- The revoke case is excluded by `hfa`; for every other constructor the authority branch of
  -- `TriConserved`'s match reduces DEFINITIONALLY to the exact equality, so the iff is uniform.
  unfold TriConserved conservedInDomain triResiduals
  -- a single tactic block discharges the four non-revoke constructors; revoke is impossible.
  cases fa with
  | revoke holder t => exact absurd rfl (hfa holder t)
  | balance a =>
      constructor
      · rintro ⟨hb, ha, hm, _⟩ dom; cases dom <;> simp_all [metadataDelta]
      · intro hall
        have hbal := hall .balance; have hnote := hall .note; have hgas := hall .gas
        simp only [List.sum_cons, List.sum_nil, add_zero, metadataDelta] at hbal hnote hgas
        refine ⟨by omega, by omega, by omega, by omega⟩
  | delegate del rec t =>
      constructor
      · rintro ⟨hb, ha, hm, _⟩ dom; cases dom <;> simp_all [metadataDelta]
      · intro hall
        have hbal := hall .balance; have hnote := hall .note; have hgas := hall .gas
        simp only [List.sum_cons, List.sum_nil, add_zero, metadataDelta] at hbal hnote hgas
        refine ⟨by omega, by omega, by omega, by omega⟩
  | mint actor cell amt =>
      constructor
      · rintro ⟨hb, ha, hm, _⟩ dom; cases dom <;> simp_all [metadataDelta]
      · intro hall
        have hbal := hall .balance; have hnote := hall .note; have hgas := hall .gas
        simp only [List.sum_cons, List.sum_nil, add_zero, metadataDelta] at hbal hnote hgas
        refine ⟨by omega, by omega, by omega, by omega⟩
  | burn actor cell amt =>
      constructor
      · rintro ⟨hb, ha, hm, _⟩ dom; cases dom <;> simp_all [metadataDelta]
      · intro hall
        have hbal := hall .balance; have hnote := hall .note; have hgas := hall .gas
        simp only [List.sum_cons, List.sum_nil, add_zero, metadataDelta] at hbal hnote hgas
        refine ⟨by omega, by omega, by omega, by omega⟩

/-- **`triConserved_of_execFull_all_domains` — the headline in independence form for the non-revoke
kinds (PROVED).** Every committed non-revoke `FullAction` (with the recipient in domain, for a
delegation) passes ALL THREE `excess` gates independently: each `Spec.Domain` residual nets to `0`,
the authority residual on the REAL `authMeasure`. -/
theorem triConserved_of_execFull_all_domains (s s' : RecChainedState) (fa : FullAction)
    (H : Finset CellId)
    (recipientInDomain : match fa with | .delegate _ rec _ => rec ∈ H | _ => True)
    (hfa : ∀ holder t, fa ≠ .revoke holder t)
    (h : execFull s fa = some s') :
    ∀ dom : Domain,
      conservedInDomain dom (triResiduals (measure s H) (measure s' H) fa dom) :=
  (triConserved_iff_all_domains_zero _ _ fa hfa).1 (triConserved_of_execFull s s' fa H recipientInDomain h)

/-! ## §8 — Axiom-hygiene tripwires (the honesty pins over every tri-domain keystone). -/

#assert_axioms balance_caps_eq
#assert_axioms mint_caps_eq
#assert_axioms burn_caps_eq
#assert_axioms authMeasure_of_caps_eq
#assert_axioms delegate_authMeasure
#assert_axioms revoke_authMeasure
#assert_axioms authority_graph_edit
#assert_axioms metadata_advance
#assert_axioms triConserved_of_execFull
#assert_axioms conservative_obligation
#assert_axioms generative_grant_obligation
#assert_axioms terminal_revoke_obligation
#assert_axioms supply_disclosed_obligation_mint
#assert_axioms supply_disclosed_obligation_burn
#assert_axioms triConserved_iff_all_domains_zero
#assert_axioms triConserved_of_execFull_all_domains

/-! ## §9 — NON-VACUITY: a concrete turn where the AUTHORITY measure genuinely MOVES.

Reusing `TurnExecutorFull.fs0`. We instantiate the tri-domain law at a DELEGATE (the authority
measure RISES by `+1`, read off the actual cap table), a MINT (balance moves, authority fixed), and
a TRANSFER (authority fixed) — showing the on-state `authMeasure` is genuinely read and moved. -/

/-- A DELEGATE: authority measure `+1` (a fresh edge-bearing cap on `rec = 1`), balance fixed,
metadata `+1`. The three deltas `(0, +1, +1)`. -/
example : ((execFull fs0 (.delegate 0 1 7)).map (fun s' => recTotal s'.kernel)) = some (recTotal fs0.kernel)
    ∧ balanceDelta (.delegate 0 1 7) = 0 ∧ authorityDelta (.delegate 0 1 7) = 1
    ∧ metadataDelta (.delegate 0 1 7) = 1 := by
  refine ⟨?_, rfl, rfl, rfl⟩; rfl

/-- A MINT of +50: balance `+50` (disclosed), authority fixed, metadata `+1`. Deltas `(+50, 0, +1)`. -/
example : ((execFull fs0 (.mint 9 0 50)).map (fun s' => recTotal s'.kernel)) = some (recTotal fs0.kernel + 50)
    ∧ balanceDelta (.mint 9 0 50) = 50 ∧ authorityDelta (.mint 9 0 50) = 0
    ∧ metadataDelta (.mint 9 0 50) = 1 := by
  refine ⟨?_, rfl, rfl, rfl⟩; rfl

-- The `authMeasure` genuinely READS the cap table and MOVES: over the holder domain `{0,1}`, slot
-- `0` already holds an edge-bearing `node 7` cap (measure `1`); a delegate to `1` grants `1` a fresh
-- `node 7` cap, raising the measure to `2`; a mint leaves it fixed at `1` (authority framed).
#eval authMeasure fs0 {0, 1}                                        -- 1 (slot 0 holds `node 7`)
#eval (execFull fs0 (.delegate 0 1 7)).map (fun s' => authMeasure s' {0, 1})  -- some 2
#eval (execFull fs0 (.mint 9 0 50)).map (fun s' => authMeasure s' {0, 1})     -- some 1 (authority framed)

/-- The authority measure of `fs0` over `{0,1}` is `1` (slot `0` holds the edge-bearing `node 7`
cap), and a delegate to `1` raises it to `2` — the on-state count genuinely reads and moves. PROVED
by `rfl` (the measure computes on the real cap table). -/
example : authMeasure fs0 {0, 1} = 1 := by rfl

/-- **Non-vacuity of the headline at a concrete delegate** — `triConserved_of_execFull` instantiated:
the AUTHORITY measure moves by `+1` (read off the actual cap table), balance stays, metadata advances,
ALL three tracked at once over the holder domain `{0,1}` with recipient `1` in domain. -/
example (s' : RecChainedState) (h : execFull fs0 (.delegate 0 1 7) = some s') :
    TriConserved (measure fs0 {0, 1}) (measure s' {0, 1}) (.delegate 0 1 7) :=
  triConserved_of_execFull fs0 s' (.delegate 0 1 7) {0, 1} (by decide) h

end Dregg2.Exec.TriDomain
