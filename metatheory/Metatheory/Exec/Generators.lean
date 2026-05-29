/-
# Metatheory.Exec.Generators — the executable mint/burn **conservation generators**.

`Exec/Kernel.lean` builds the kernel whose ordinary turns CONSERVE total supply
(`exec_conserves`, Law 1). This module adds the ONLY two operations permitted to move
the conserved quantity: `execMint` (an inflow) and `execBurn` (an outflow). They are the
concrete, **computable** refinements of `Core.mint_delta` / `Core.burn_delta` (the abstract
typed generators that — uniquely — change `Σ`).

Both are fail-closed and require authority over the target cell (mirroring `Kernel.exec`):
a mint/burn is privileged, so the actor must hold a `node` cap on the cell (or an
`endpoint` cap carrying `Auth.control`) — bare ownership is NOT enough to coin or destroy
supply. We then PROVE the exact deltas on `total`:
- `execMint_delta` : `total k' = total k + amt`,
- `execBurn_delta` : `total k' = total k - amt`,
and the authority shadows
- `execMint_authorized` / `execBurn_authorized` : no inflow/outflow without authority.

Pure executable Lean (`#eval`-able). Reuses `Kernel`'s `KernelState`/`total` and the
`sum_indicator` single-point-sum technique; the balance is a total `CellId → ℤ` over a
`Finset accounts` (Finsupp is noncomputable here).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Metatheory.Exec.Kernel

namespace Metatheory.Exec

open Metatheory.Authority

/-- **The mint/burn authority check (computable).** Minting or burning a cell's supply is
privileged: the actor must hold a `node` cap on the cell (the `Control`-conferring cap, l4v
`CNodeCap`/`ThreadCap`) OR an `endpoint` cap on the cell carrying `Auth.control`. Bare
ownership (`actor = cell`) is deliberately NOT sufficient — a cell cannot coin its own
supply. -/
def mintAuthorizedB (caps : Caps) (actor cell : CellId) : Bool :=
  (caps actor).any (fun c =>
    (c == Cap.node cell) ||
    (match c with
     | .endpoint t rights => (t == cell) && rights.contains Auth.control
     | _ => false))

/-- **Executable mint.** Fail-closed: credits `cell` by `amt` only when the actor is
authorized to mint over `cell`, the amount is non-negative, and `cell` is a live account. -/
def execMint (k : KernelState) (actor cell : CellId) (amt : ℤ) : Option KernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with bal := fun c => if c = cell then k.bal c + amt else k.bal c }
  else
    none

/-- **Executable burn.** Fail-closed: debits `cell` by `amt` only when the actor is
authorized over `cell`, the amount is non-negative and available (`amt ≤ bal cell`), and
`cell` is a live account. -/
def execBurn (k : KernelState) (actor cell : CellId) (amt : ℤ) : Option KernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell
      ∧ cell ∈ k.accounts then
    some { k with bal := fun c => if c = cell then k.bal c - amt else k.bal c }
  else
    none

/-! ## The single-cell delta helper (mirrors `Kernel.transfer_sum_conserve`). -/

/-- **Single-cell credit delta.** Adding `v` to exactly the cell `a ∈ acc` changes the sum
by exactly `v`. Proved by the `sum_indicator` technique (split off the indicator, reuse
`Kernel.sum_indicator`). -/
theorem sum_update_add (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (v : ℤ)
    (ha : a ∈ acc) :
    (∑ c ∈ acc, (if c = a then bal c + v else bal c)) = (∑ c ∈ acc, bal c) + v := by
  have hg : ∀ c ∈ acc, (if c = a then bal c + v else bal c)
      = bal c + (if c = a then v else 0) := by
    intro c _
    rcases eq_or_ne c a with h | h
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg h, add_zero]
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib, sum_indicator acc a v ha]

/-- **Single-cell debit delta.** Subtracting `v` from exactly `a ∈ acc` changes the sum by
`-v`. -/
theorem sum_update_sub (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (v : ℤ)
    (ha : a ∈ acc) :
    (∑ c ∈ acc, (if c = a then bal c - v else bal c)) = (∑ c ∈ acc, bal c) - v := by
  rw [sub_eq_add_neg, ← sum_update_add acc bal a (-v) ha]
  apply Finset.sum_congr rfl
  intro c _
  rcases eq_or_ne c a with h | h
  · subst h; rw [if_pos rfl, if_pos rfl]; ring
  · rw [if_neg h, if_neg h]

/-! ## The generators refine `Core.mint_delta` / `Core.burn_delta` (PROVED). -/

/-- **Mint inflow (Law-1 generator) — PROVED.** A committed mint increases total supply by
exactly `amt`; the concrete refinement of `Core.mint_delta`. -/
theorem execMint_delta (k k' : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : execMint k actor cell amt = some k') : total k' = total k + amt := by
  unfold execMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    simpa [total] using sum_update_add k.accounts k.bal cell amt hcell
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Burn outflow (Law-1 generator) — PROVED.** A committed burn decreases total supply by
exactly `amt`; the concrete refinement of `Core.burn_delta`. -/
theorem execBurn_delta (k k' : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : execBurn k actor cell amt = some k') : total k' = total k - amt := by
  unfold execBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hcell⟩ := hg
    simpa [total] using sum_update_sub k.accounts k.bal cell amt hcell
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No inflow without authority — PROVED.** A committed mint implies the actor was
authorized over `cell` (the integrity shadow for the privileged supply-creation generator). -/
theorem execMint_authorized (k k' : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : execMint k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold execMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No outflow without authority — PROVED.** A committed burn implies the actor was
authorized over `cell`. -/
theorem execBurn_authorized (k k' : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : execBurn k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold execBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed (mint) — PROVED.** Without mint authority, no mint commits. -/
theorem execMint_unauthorized_fails (k : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : execMint k actor cell amt = none := by
  unfold execMint
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **Fail-closed (burn) — PROVED.** Without mint authority, no burn commits. -/
theorem execBurn_unauthorized_fails (k : KernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : execBurn k actor cell amt = none := by
  unfold execBurn
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-! ## It runs (`#eval`). -/

/-- A minting authority: actor 9 holds a `node` cap on cell 0 (may mint/burn cell 0). -/
def sMint : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun a => if a = 9 then [Cap.node 0] else [] }

#eval (execMint sMint 9 0 50).map total       -- some 155 (100+5+50)
#eval (execMint sMint 7 0 50).isSome           -- false (actor 7 unauthorized)
#eval (execBurn sMint 9 0 40).map total        -- some 65  (100+5-40)
#eval (execBurn sMint 9 0 200).isSome          -- false (insufficient balance)
#eval total sMint                              -- 105

end Metatheory.Exec
