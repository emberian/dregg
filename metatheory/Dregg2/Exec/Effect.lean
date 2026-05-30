/-
# Dregg2.Exec.Effect — the typed `CellEffect` taxonomy + `LinearityClass`:
# **conservation as the TYPED, folded, per-class law** (`dregg2 §2.1`).

`Exec/Unified.lean` already unifies the kernel *operations* (`KernelOp`) under one `delta`
and proves the ledger law `total = initial + Σ deltas`. This module sharpens the *discipline*
that makes that law trustworthy as the effect catalog grows: it mirrors dregg1's
`turn/src/action.rs`, where every `Effect` constructor MUST answer conservation by declaring a
`LinearityClass` through an **exhaustive, no-default `match`**. The point is structural: a new
effect **cannot silently skip its conservation answer** — Lean's exhaustiveness check is the
enforcement (drop a case and the `match` does not type-check), exactly as Rust's no-`_`-arm
`match` is in dregg1.

The folded per-class law:
- the *conserved fungible total* moves by `Σ (effects.map delta)`;
- ordinary effects (`transfer`/`grantCap`/`revokeCap`/`setField`/`emitEvent`/`incrementNonce`/
  `createCell`) contribute `delta = 0` — they move/relabel/account but never coin or destroy
  units of the conserved resource;
- the *only* effects that move the total are the **disclosed non-conservations**: `mint`
  (`+amt`, the `generative` ex-nihilo inflow) and `burn` (`−amt`, the `annihilative` outflow).

So `delta e ≠ 0 ↔ (linearity e = generative ∨ linearity e = annihilative)` — the disclosure
is *forced*: an effect that moves the total is exactly a mint or a burn, and conversely a
conservation-neutral turn (every effect `delta 0`) preserves the total. These are PROVED
below by induction over the effect list, mirroring `Unified.unified_ledger` / `MultiAsset`.

> Faithfulness note. In dregg1 `linearity()`, `GrantCapability`/`CreateCell` are *also*
> `Generative` (they create a capability / a cell ex nihilo). That is a *different* resource
> axis (authority / cell-existence), not the conserved *fungible* total this module folds.
> Here the conserved total is the token supply, so in this representative taxonomy the only
> total-moving effects are `mint` (generative) and `burn` (annihilative); `grantCap` is kept
> `monotonic` and `createCell` `monotonic` to keep "moves the fungible total" ⇔ "is a disclosed
> mint/burn" a clean, provable bi-implication. The exhaustiveness discipline — the real subject
> — is identical to dregg1's.

Pure executable Lean, `#eval`-able. Crypto/Rust stay out (`dregg2 §8`). Imports only Mathlib;
defines everything under a fresh namespace, redefining nothing from `Core`/`Unified`/`action.rs`.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

namespace Dregg2.Exec.Effect

/-! ## The linearity lattice (mirrors `action.rs::LinearityClass`, uniquely namespaced). -/

/-- **`LinearityClass`** — every effect's *conservation answer*, the six classes from dregg1
`turn/src/action.rs`:
- `conservative` — paired-sibling; the Σ of a conservative effect's own deltas is `0` (e.g. a
  transfer's debit+credit). It is the only class that `requiresPairedSibling`.
- `monotonic` — a scalar that only goes up (nonces, refcounts, refusals); no fungible delta.
- `terminal` — a one-way state transition with no inverse (revoke, drop, destroy); no delta.
- `generative` — creates a unit of the conserved resource ex nihilo (the disclosed mint).
- `annihilative` — destroys a unit of the conserved resource (the disclosed burn).
- `neutral` — no resource delta at all (set-field, emit-event). -/
inductive LinearityClass where
  | conservative
  | monotonic
  | terminal
  | generative
  | annihilative
  | neutral
  deriving Repr, DecidableEq

/-- **`requiresPairedSibling`** — true for exactly `conservative` (dregg1
`LinearityClass::requires_paired_sibling`): a conservative effect must come with a sibling that
cancels its delta so the pair sums to `0`. Mints/burns are *disclosed* non-conservations and do
NOT require a sibling; the rest carry no fungible delta to pair. -/
def requiresPairedSibling : LinearityClass → Bool
  | .conservative => true
  | .monotonic    => false
  | .terminal     => false
  | .generative   => false
  | .annihilative => false
  | .neutral      => false

/-- **The disclosed non-conservations** are exactly `generative` and `annihilative` (dregg1
`LinearityClass::discloses_non_conservation`): the two classes an operator must explicitly opt
into because they move the conserved total. -/
def disclosesNonConservation : LinearityClass → Bool
  | .generative   => true
  | .annihilative => true
  | .conservative => false
  | .monotonic    => false
  | .terminal     => false
  | .neutral      => false

/-! ## The effect taxonomy (a representative slice of `action.rs::Effect`). -/

/-- A cell identity, kept local + `Nat`-valued so this module is self-contained and cannot clash
with `Kernel.CellId` / `MultiAsset.MACellId`. -/
abbrev EffCellId := Nat

/-- **`CellEffect`** — a representative slice of dregg1's `Effect` enum: a state-field write, a
fungible `transfer`, the two supply generators `mint`/`burn`, capability `grantCap`/`revokeCap`,
an `emitEvent`, a nonce bump, and a `createCell`. Each carries just the data this module's
conservation fold needs (amounts for the fungible movers; `EffCellId`s for routing). -/
inductive CellEffect where
  | setField        (cell : EffCellId) (field : Nat) (value : Int)
  | transfer        (src dst : EffCellId) (amt : Int)
  | mint            (cell : EffCellId) (amt : Int)
  | burn            (cell : EffCellId) (amt : Int)
  | grantCap        (holder target : EffCellId)
  | revokeCap       (holder target : EffCellId)
  | emitEvent       (cell : EffCellId) (topic : Nat)
  | incrementNonce  (cell : EffCellId)
  | createCell      (parent child : EffCellId)
  deriving Repr, DecidableEq

/-- **`linearity` — the EXHAUSTIVE, no-default per-effect conservation answer.** This is the
keystone of the discipline: there is **no `| _ => …` fall-through**, so adding a constructor to
`CellEffect` makes this `match` non-exhaustive and the file stops compiling until the new effect
declares its class. A new effect therefore *cannot* silently skip its conservation answer — the
same guarantee dregg1's no-`_`-arm `match` gives in Rust.

- `transfer` is `conservative` (its debit+credit are a paired delta);
- `mint`/`burn` are the disclosed `generative`/`annihilative`;
- `grantCap`/`createCell`/`incrementNonce` are `monotonic` (a counter / set only grows);
- `revokeCap` is `terminal` (one-way, no inverse);
- `setField`/`emitEvent` are `neutral` (no resource delta). -/
def linearity : CellEffect → LinearityClass
  | .setField _ _ _      => .neutral
  | .transfer _ _ _      => .conservative
  | .mint _ _            => .generative
  | .burn _ _            => .annihilative
  | .grantCap _ _        => .monotonic
  | .revokeCap _ _       => .terminal
  | .emitEvent _ _       => .neutral
  | .incrementNonce _    => .monotonic
  | .createCell _ _      => .monotonic

/-- **`delta` — the effect's signed contribution to the conserved fungible total.** Everything
that moves/relabels/accounts contributes `0`; `mint` adds `+amt`; `burn` subtracts `amt`. (A
`transfer`'s internal debit and credit cancel, so its *net* contribution to the total is `0` —
the paired-sibling cancellation is internal; see `MultiAsset.maExec_conserves_per_asset` for the
per-cell version.) -/
def delta : CellEffect → Int
  | .setField _ _ _      => 0
  | .transfer _ _ _      => 0
  | .mint _ amt          => amt
  | .burn _ amt          => -amt
  | .grantCap _ _        => 0
  | .revokeCap _ _       => 0
  | .emitEvent _ _       => 0
  | .incrementNonce _    => 0
  | .createCell _ _      => 0

/-! ## The per-effect disclosure law (PROVED): `delta ≠ 0` ⇔ disclosed mint/burn. -/

/-- A `mint` is the `generative` disclosure — PROVED (definitional). -/
theorem mint_is_generative (cell : EffCellId) (amt : Int) :
    linearity (.mint cell amt) = .generative := rfl

/-- A `burn` is the `annihilative` disclosure — PROVED (definitional). -/
theorem burn_is_annihilative (cell : EffCellId) (amt : Int) :
    linearity (.burn cell amt) = .annihilative := rfl

/-- **A neutral-delta effect is never a disclosed non-conservation — PROVED.** If an effect's
linearity does NOT disclose a non-conservation, then its delta is `0`: the conservative,
monotonic, terminal and neutral effects all leave the total untouched. (By exhaustive `cases`.) -/
theorem delta_zero_of_not_disclosed (e : CellEffect)
    (h : disclosesNonConservation (linearity e) = false) : delta e = 0 := by
  cases e <;> simp_all [linearity, delta, disclosesNonConservation]

/-- **The disclosure is FORCED — PROVED.** Any effect that moves the conserved total is a
disclosed non-conservation: `delta e ≠ 0 → disclosesNonConservation (linearity e)`. The
contrapositive is `delta_zero_of_not_disclosed`; so an undisclosed (conservative/monotonic/
terminal/neutral) effect provably cannot move the total. (The converse fails *honestly*: a
mint/burn of amount `0` discloses a non-conservation while contributing `delta 0`, so disclosure
is necessary but the *amount* may be zero — see `disclosed_iff_mint_or_burn` for the structural
characterization that IS a bi-implication.) -/
theorem moves_total_disclosed (e : CellEffect)
    (hne : delta e ≠ 0) : disclosesNonConservation (linearity e) = true := by
  by_contra hd
  simp only [Bool.not_eq_true] at hd
  exact hne (delta_zero_of_not_disclosed e hd)

/-- **The disclosed classes are EXACTLY the mint/burn effects — PROVED (bi-implication).** An
effect discloses a non-conservation iff it is structurally a `mint` (generative) or a `burn`
(annihilative). This is the clean two-way characterization the amount-sensitive
`moves_total_disclosed` cannot give. -/
theorem disclosed_iff_mint_or_burn (e : CellEffect) :
    disclosesNonConservation (linearity e) = true ↔
      (∃ cell amt, e = .mint cell amt) ∨ (∃ cell amt, e = .burn cell amt) := by
  cases e <;> simp [linearity, disclosesNonConservation]

/-- **`disclosed_non_conservation` — the named keystone of disclosure.** The effects that move
the conserved total force a `was_mint`/`was_burn` disclosure: `delta e ≠ 0` forces `linearity e`
to be one of the two disclosed classes, and each disclosed class is realized by a `mint`/`burn`
effect carrying the right-signed delta. The `was_mint`/`was_burn` witnesses are *forced* out by
the `generative`/`annihilative` hypotheses. -/
theorem disclosed_non_conservation (e : CellEffect) :
    (delta e ≠ 0 → linearity e = .generative ∨ linearity e = .annihilative)
    ∧ (linearity e = .generative → ∃ cell amt, e = .mint cell amt ∧ delta e = amt)
    ∧ (linearity e = .annihilative → ∃ cell amt, e = .burn cell amt ∧ delta e = -amt) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    have hd := moves_total_disclosed e hne
    cases e <;> simp_all [linearity, disclosesNonConservation]
  · intro hg
    cases e <;> simp_all [linearity, delta]
  · intro ha
    cases e <;> simp_all [linearity, delta]

/-! ## The folded per-class ledger law over a turn's effect list (PROVED).

A *turn* fires an ordered list of effects; its net contribution to the conserved total is the
fold `Σ (effects.map delta)`. This mirrors `Unified.traceDelta` / `MultiAsset`'s sum shape, but
folds over the **typed effect catalog** rather than the kernel-op enum. -/

/-- **The folded ledger delta of a turn** — the sum of its effects' deltas (mints add, burns
subtract, all else contributes `0`). This is the "folded per-class" total of `dregg2 §2.1`. -/
def turnDelta (effects : List CellEffect) : Int := (effects.map delta).sum

/-- **A conservation-neutral turn** — one whose every effect contributes `delta 0` (no mint, no
burn). Stated as a `Prop` over the list so it lifts cleanly through the fold. -/
def AllNeutral (effects : List CellEffect) : Prop := ∀ e ∈ effects, delta e = 0

/-- A neutral turn has folded delta `0` — PROVED by induction over the effect list (mirrors the
`MultiAsset` / `unified_ledger` induction shape). -/
theorem turnDelta_neutral (effects : List CellEffect) (h : AllNeutral effects) :
    turnDelta effects = 0 := by
  unfold turnDelta AllNeutral at *
  induction effects with
  | nil => simp
  | cons e es ih =>
      have he : delta e = 0 := h e (by simp)
      have hes : ∀ x ∈ es, delta x = 0 := fun x hx => h x (List.mem_cons_of_mem e hx)
      simp [List.map_cons, List.sum_cons, he, ih hes]

/-! The conserved total is modelled as a running scalar that each effect updates by its `delta`
(the fungible-supply shadow of `Unified.step_delta`; the per-cell version is `MultiAsset`). -/

/-- Apply a turn's effects to a running conserved `total`, folding in each `delta` in order. -/
def applyTurn (total : Int) (effects : List CellEffect) : Int :=
  effects.foldl (fun t e => t + delta e) total

/-- **THE KEYSTONE — `conservation_of_effects`.** The general ledger law of a turn:
`total' = total + Σ (effects.map delta)`. The conserved total after firing a turn equals the
total before, plus the folded per-class delta — mints add, burns subtract, every conservative /
monotonic / terminal / neutral effect contributes `0`. Proved by induction over the effect list
(the `Unified.unified_ledger` / `MultiAsset` shape, lifted to the typed effect catalog). -/
theorem conservation_of_effects (total : Int) (effects : List CellEffect) :
    applyTurn total effects = total + turnDelta effects := by
  unfold applyTurn turnDelta
  induction effects generalizing total with
  | nil => simp
  | cons e es ih =>
      rw [List.foldl_cons, ih (total + delta e), List.map_cons, List.sum_cons]
      ring

/-- **Conservation of a neutral turn — PROVED** (the headline corollary). A turn whose effects
are all conservation-neutral (`delta 0`) preserves the conserved total exactly. -/
theorem neutral_turn_conserves (total : Int) (effects : List CellEffect)
    (h : AllNeutral effects) : applyTurn total effects = total := by
  rw [conservation_of_effects, turnDelta_neutral effects h, add_zero]

/-- **A pure-transfer turn conserves — PROVED.** A turn of only `transfer` effects (all
`conservative`, all `delta 0`) preserves the total — the paired-sibling law at the fold level. -/
theorem transfers_conserve (total : Int) (effects : List CellEffect)
    (h : ∀ e ∈ effects, ∃ s d a, e = .transfer s d a) :
    applyTurn total effects = total := by
  apply neutral_turn_conserves
  intro e he
  obtain ⟨s, d, a, rfl⟩ := h e he
  rfl

/-! ## It runs (`#eval`). -/

/-- A pure-transfer turn: move 30 then 5 — conservation-neutral. -/
def transferTurn : List CellEffect := [.transfer 0 1 30, .transfer 1 2 5]
/-- A mint turn: coin 50 into cell 0 (the disclosed `generative` inflow). -/
def mintTurn : List CellEffect := [.mint 0 50]
/-- A burn turn: destroy 40 from cell 0 (the disclosed `annihilative` outflow). -/
def burnTurn : List CellEffect := [.burn 0 40]
/-- A mixed turn: set a field, mint 50, transfer 30, burn 20, emit an event — net `+30`. -/
def mixedTurn : List CellEffect :=
  [.setField 0 1 7, .mint 0 50, .transfer 0 1 30, .burn 0 20, .emitEvent 0 3]

#eval linearity (.transfer 0 1 30)            -- Dregg2.Exec.Effect.LinearityClass.conservative
#eval linearity (.mint 0 50)                  -- ...generative
#eval linearity (.burn 0 40)                  -- ...annihilative
#eval requiresPairedSibling (linearity (.transfer 0 1 30))  -- true
#eval requiresPairedSibling (linearity (.mint 0 50))        -- false (disclosed, not paired)

#eval turnDelta transferTurn                  -- 0   (transfers conserve)
#eval turnDelta mintTurn                       -- 50  (mint adds)
#eval turnDelta burnTurn                       -- -40 (burn subtracts)
#eval turnDelta mixedTurn                      -- 30  (= 0 + 50 + 0 - 20 + 0)

#eval applyTurn 105 transferTurn              -- 105 (a transfer turn conserves)
#eval applyTurn 105 mintTurn                   -- 155 (a mint turn adds 50)
#eval applyTurn 105 burnTurn                   -- 65  (a burn turn subtracts 40)
#eval applyTurn 105 mixedTurn                  -- 135 (the ledger law over a mixed turn: 105 + 30)

end Dregg2.Exec.Effect
