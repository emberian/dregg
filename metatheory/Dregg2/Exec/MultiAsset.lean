/-
# Dregg2.Exec.MultiAsset — multi-asset conservation, the TYPED per-asset law.

The single-asset `Exec.Kernel` conserves ONE scalar (`total : KernelState → ℤ`). Real
dregg1 cells hold MANY assets (`AssetId`), and conservation is **per-asset, never one
aggregate scalar** (`dregg2.md §2.1`; `gaps-2 (c)`). A turn that moves 5 of asset 0 must
leave the supply of asset 1 *literally untouched*; folding all assets into a single sum
would let a cell silently swap one asset for another while the aggregate stays put. So the
conserved quantity is a *family* `maTotal k a` indexed by `AssetId`, and the keystone is
that **every** asset's total is preserved by **every** committed transfer.

This is a NEW structure built PARALLEL to `KernelState` (it does not touch `Kernel.lean`):
balances are a total `CellId → AssetId → ℤ` (ℤ so debt is representable; a *function*, not
`Finsupp`, whose `+` is noncomputable), summed with `Finset.sum` over the live `accounts`.
The proof mirrors `Kernel.transfer_sum_conserve` (debit/credit cancel for the moved asset),
generalized: for the moved asset the cancellation runs per-cell; for every *other* asset the
balance is unchanged pointwise, so the sum is unchanged trivially.

The camera bridge (`Resource.lean`): per-asset conservation is the `(ℕ,+)`/`(ℤ,+)` sum-
shadow of the frame-preserving update, replicated once per `AssetId`. We connect the moved
asset's debit/credit to `Resource.Fpu` over the `Auth` camera as a corollary.

Pure executable Lean, `#eval`-able. Crypto/Rust stay out (`dregg2 §8`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Dregg2.Resource

namespace Dregg2.Exec.MultiAsset

open scoped BigOperators

/-- A cell identity (kept local + `Nat`-valued so this file is self-contained and cannot
clash with `Kernel.CellId`). -/
abbrev MACellId := Nat

/-- An asset identity — dregg cells hold many assets; conservation is indexed by this. -/
abbrev AssetId := Nat

/-- **Multi-asset kernel state:** the finite set of live `accounts`, and a total balance
function giving, for each cell and each asset, an (ℤ-valued, debt-capable) amount.
Computable: `bal` is an ordinary function, NOT a `Finsupp`. -/
structure MultiState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset MACellId
  /-- Per-cell, per-asset balance. -/
  bal      : MACellId → AssetId → ℤ
  /-- The set of cells the actor is currently authorized to debit (a minimal, executable
  stand-in for the cap table: ownership/authority is membership here). -/
  authedBy : MACellId → MACellId → Bool

/-- **A multi-asset turn:** the `actor` moves `amt` of asset `asset` from `src` to `dst`. -/
structure MultiTurn where
  actor : MACellId
  src   : MACellId
  dst   : MACellId
  asset : AssetId
  amt   : ℤ

/-- **The authority check (computable).** Authorized over `src` iff the actor owns it
(`actor = src`) or the auth table grants the actor authority over `src`. Fail-closed. -/
def maAuthorizedB (k : MultiState) (turn : MultiTurn) : Bool :=
  (turn.actor == turn.src) || k.authedBy turn.actor turn.src

/-- The balance function after a transfer: only the `(·, asset)` column is touched — debit
`src`, credit `dst`; every other cell and **every other asset** is returned unchanged. -/
def maTransferBal (bal : MACellId → AssetId → ℤ) (src dst : MACellId) (a : AssetId)
    (amt : ℤ) : MACellId → AssetId → ℤ :=
  fun c b =>
    if b = a then
      (if c = src then bal c b - amt else if c = dst then bal c b + amt else bal c b)
    else bal c b

/-- **The executable multi-asset transition.** Fail-closed: commits only when the actor is
authorized over `src`, the amount is non-negative and available *in that asset*, `src ≠ dst`,
and both cells are live accounts. -/
def maExec (k : MultiState) (turn : MultiTurn) : Option MultiState :=
  if maAuthorizedB k turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src turn.asset
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with bal := maTransferBal k.bal turn.src turn.dst turn.asset turn.amt }
  else
    none

/-- **Total supply of a single asset** `a` over the live accounts — the conserved family,
indexed by `AssetId` (NOT collapsed to one scalar). -/
def maTotal (k : MultiState) (a : AssetId) : ℤ := ∑ c ∈ k.accounts, k.bal c a

/-! ## The kernel satisfies the per-asset law (the refinement, PROVED). -/

/-- Sum of a single-point indicator over a set containing the point (the `Kernel`
analog, restated locally). -/
theorem maSumIndicator (acc : Finset MACellId) (p : MACellId) (v : ℤ) (hp : p ∈ acc) :
    (∑ c ∈ acc, (if c = p then v else 0)) = v := by
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (fun h => absurd hp h)]
  simp

/-- **Per-asset conservation core (moved asset):** for the *moved* asset `a`, a transfer
between two distinct live accounts preserves the column sum (debit and credit cancel). -/
theorem maTransfer_sum_conserve_moved (acc : Finset MACellId)
    (bal : MACellId → AssetId → ℤ) (src dst : MACellId) (a : AssetId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, maTransferBal bal src dst a amt c a) = ∑ c ∈ acc, bal c a := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, maTransferBal bal src dst a amt c a - bal c a
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    unfold maTransferBal
    rw [if_pos rfl]
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      maSumIndicator acc src (-amt) hsrc, maSumIndicator acc dst amt hdst]
  ring

/-- **Per-asset conservation core (untouched asset):** for any asset `b ≠ a`, the transfer
of asset `a` leaves the entire column literally unchanged — pointwise, hence the sum. -/
theorem maTransfer_untouched (bal : MACellId → AssetId → ℤ) (src dst : MACellId)
    (a b : AssetId) (amt : ℤ) (hb : b ≠ a) (c : MACellId) :
    maTransferBal bal src dst a amt c b = bal c b := by
  unfold maTransferBal
  rw [if_neg hb]

/-- **THE KEYSTONE — per-asset conservation, PROVED of the executable multi-asset kernel.**
Every committed transfer preserves `maTotal k a` for EVERY asset `a`: the moved asset by the
debit/credit cancellation, every other asset because its column is untouched. This is the
typed per-asset law (`dregg2 §2.1`), the multi-asset refinement of `Kernel.exec_conserves`. -/
theorem maExec_conserves_per_asset (k k' : MultiState) (turn : MultiTurn)
    (h : maExec k turn = some k') (a : AssetId) : maTotal k' a = maTotal k a := by
  unfold maExec at h
  by_cases hg : maAuthorizedB k turn = true ∧ 0 ≤ turn.amt
      ∧ turn.amt ≤ k.bal turn.src turn.asset ∧ turn.src ≠ turn.dst
      ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    unfold maTotal
    show (∑ c ∈ k.accounts, maTransferBal k.bal turn.src turn.dst turn.asset turn.amt c a)
        = ∑ c ∈ k.accounts, k.bal c a
    rcases eq_or_ne a turn.asset with ha | ha
    · subst ha
      exact maTransfer_sum_conserve_moved k.accounts k.bal turn.src turn.dst turn.asset
        turn.amt hsrc hdst hne
    · exact Finset.sum_congr rfl
        (fun c _ => maTransfer_untouched k.bal turn.src turn.dst turn.asset a turn.amt ha c)
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** (the integrity/confinement shadow: the
multi-asset kernel never moves a cell's resource for an unauthorized actor). -/
theorem maExec_authorized (k k' : MultiState) (turn : MultiTurn)
    (h : maExec k turn = some k') : maAuthorizedB k turn = true := by
  unfold maExec at h
  by_cases hg : maAuthorizedB k turn = true ∧ 0 ≤ turn.amt
      ∧ turn.amt ≤ k.bal turn.src turn.asset ∧ turn.src ≠ turn.dst
      ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized turn does NOT commit. -/
theorem maExec_unauthorized_fails (k : MultiState) (turn : MultiTurn)
    (h : maAuthorizedB k turn = false) : maExec k turn = none := by
  unfold maExec
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-! ## The camera bridge (`Resource.lean`): per-asset conservation = the FPU shadow.

For the moved asset, the per-cell effect (debit `src` by `amt`, credit `dst` by `amt`) is
the `(ℤ,+)` shadow of a frame-preserving update on the `Auth` camera: under a *fixed*
authoritative total `T` (the asset's supply), rearranging the held fragment `f → f'` is an
FPU whenever it does not enlarge what any frame needs. The conserved column-sum is exactly
the invariant the authoritative slot `● T` pins. -/

open Dregg2.Resource

/-- **Camera corollary (moved asset):** a *withdrawal* of the moved asset's fragment
(`f' ≼ f`, the held amount only shrinks) is a frame-preserving update on the `Auth ℤ`
camera under the fixed asset supply `T`. This instantiates `conservation_is_fpu`: the debit
side of `maTransferBal` is conservative against any third party's holding, which is the
camera-tier meaning of "the asset total `T` is preserved" (`maExec_conserves_per_asset`). -/
theorem maMovedAsset_debit_is_fpu (T f f' : ℤ) (_hle : f' ≤ f) :
    Fpu (R := Auth ℤ) (.mk (some T) f) (.mk (some T) f') := by
  apply conservation_is_fpu
  intro g hfits
  obtain ⟨c, hc⟩ := hfits
  -- the held fragment only shrinks (`_hle`), so the slack `(f - f') + c` re-fits f' + g
  -- under the same authority T: f' + ((f - f') + c) = f + c = T + g shifted.
  exact ⟨(f - f') + c, by rw [hc]; ring⟩

/-! ## It runs (`#eval`). -/

/-- A 2-cell, 2-asset ledger: cell 0 holds 100 of asset 0 and 7 of asset 1; cell 1 holds 5
of asset 0 and 0 of asset 1. accounts = {0,1}; actor authority is by ownership only. -/
def ms0 : MultiState :=
  { accounts := {0, 1}
    bal := fun c a =>
      if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
      else if c = 1 then (if a = 0 then 5 else 0)
      else 0
    authedBy := fun _ _ => false }

/-- Actor 0 transfers 30 of asset 0 to cell 1 (owns src 0). -/
def mt1 : MultiTurn := { actor := 0, src := 0, dst := 1, asset := 0, amt := 30 }
/-- Actor 2 attempts the same — unauthorized (no ownership, no auth-table grant). -/
def mtBad : MultiTurn := { actor := 2, src := 0, dst := 1, asset := 0, amt := 30 }

#eval (maExec ms0 mt1).isSome                    -- true
#eval (maExec ms0 mtBad).isSome                  -- false
#eval maTotal ms0 0                              -- 105  (asset 0 supply)
#eval maTotal ms0 1                              -- 7    (asset 1 supply)
#eval (maExec ms0 mt1).map (fun k => maTotal k 0) -- some 105 (asset 0 conserved: 70 + 35)
#eval (maExec ms0 mt1).map (fun k => maTotal k 1) -- some 7   (asset 1 untouched)
-- the committed cell-0 balances: 70 of asset 0, still 7 of asset 1.
#eval (maExec ms0 mt1).map (fun k => (k.bal 0 0, k.bal 0 1, k.bal 1 0, k.bal 1 1))
                                                  -- some (70, 7, 35, 0)

end Dregg2.Exec.MultiAsset
