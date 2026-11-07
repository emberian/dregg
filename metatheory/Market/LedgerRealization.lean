/-
# Market.LedgerRealization — DrEX: WELDING the priced tower (rung 5) to the REAL kernel executor.

**The seam this closes (named by the scope audit, `docs/deos/DREX-DESIGN.md` §2/§6 and
`DREGGFI-VISION.md` §7, committed in `03a5bad91`).** DrEX's rungs split into two grades of
groundedness:

  * **rung 1 (`Market/{Clearing,Fairness}.lean`) is LEDGER-REALIZED** — its conservation is the REAL
    executor's. `cycleValid_fulfilled_respects_limits` is stated over `settleRing k (settlementsOf ns)
    = some k'` and asserts `recTotalAsset k' b = recTotalAsset k b` (the per-asset ledger measure the
    `@[export] recKExec` FFI actually runs, `Dregg2/Intent/RingFFI.lean`);
  * **rungs 4/5/6 (`Market/{Optimality,Priced,Liquidity}.lean`) were MODEL-VERIFIED** — proved over
    the priced `Fill`/reserve MODEL (`netFlow = 0` over ℚ, `Priced.lean`), a self-contained
    bookkeeping identity NOT welded to `settleRing`/`recKExec`. The `netFlow` was a LOCAL sum, not the
    kernel's `recTotalAsset`/`toBal`.

This module drives rung 5's conservation DOWN to the kernel for the case where it cleanly lowers: the
**full-fill uniform-price clearing** (the degeneration `PricedOrder.ofMatchNode` /
`ofMatchNode_full_fill_meets_wantMin` already support — a full fill at the limit price recovers
rung-1's exact-book leg). For such a clearing over a solver-admitted cycle, the priced model's
`netFlow = 0` and the KERNEL's `recTotalAsset`-preservation are two readings of ONE settlement — the
priced conservation IS the kernel conservation.

## What is proved (and its EXACT scope)

  * **`fullFill_cycle_ledger_realized` (THE BRIDGE).** For a `CycleValid ns` whose legs are TIGHT
    (`TightCycle ns` — every sender's full offer is exactly the next party's minimum, the full-fill /
    exact-swap regime), with positive offers, that settles through the verified executor
    (`settleRing k (settlementsOf ns) = some k'`):
      1. **(kernel-real)** `∀ b, recTotalAsset k' b = recTotalAsset k b` — the REAL ledger preserves
         every asset's supply. This IS rung-1's `settleRing_conserves` tie (the same clause
         `cycleValid_fulfilled_respects_limits` carries);
      2. **(model)** `Conserves (pricedFullFills ns)` — the priced full-fill lowering has `netFlow = 0`
         over ℚ on EVERY asset, PROVED (from tightness + chaining, by the rotation reindexing
         `offerContrib_sum_eq_wantContrib_sum`), not assumed;
      3. **(model ↔ kernel)** each priced fill spends EXACTLY its kernel settlement leg's amount
         (`fullFill … .filledIn = ((settlementsOf ns).getD j default).amount`). The priced fills ARE the
         kernel legs, quantity for quantity.
    So (2) and (1) are the SAME trades (3): rung 5 is ledger-realized for the full-fill case.

  * **SCOPE, stated plainly.** This welds the **full-fill / tight-cycle** case (where the priced
    clearing recovers the `MatchNode` cycle). **Genuine partial-fill ledger-realization** — a fill
    that spends LESS than the offer, at a strictly interior price, does NOT lower to a single
    `settleRing` cycle (the settled leg amount is the RECEIVER's `wantMin`, and the ofMatchNode limit
    price only reproduces the executed rate at a full give) — that is the NEXT sub-rung, NAMED not
    claimed (`partial-fill ledger-realization`). Rung 6's portfolio `pool_solvent_forever` is a
    ∀-schedule reserve invariant over `Pool = AssetId → ℚ`, not a ring settlement, so it does NOT
    lower to `settleRing` at all — its kernel weld is a SEPARATE reserve-column readback, also NAMED.

NON-VACUITY, both polarities: a concrete TIGHT valid triangle (`tightTriangle`) has its full-fill
lowering CONSERVE (`netFlow = 0`, `#guard`-computed) with the per-leg correspondence pinned, and — the
tooth — the full-fill lowering of a NON-tight cycle (`Fairness.validTriangle`, offers 8/9/7 against
wants 4/6/5) does NOT conserve (`netFlow · 10 = -2 ≠ 0`): a full-fill of a non-tight cycle would mint
value, so it is NOT ledger-realized. Tightness is load-bearing.

Pure.
-/
import Market.Priced
import Market.Fairness
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Market

open Dregg2.Intent.Ring
open Dregg2.Exec (AssetId CellId RecordKernelState recTotalAsset)
open Dregg2.Intent.Ring (MatchNode)

/-! ## 1. The full-fill lowering of a `MatchNode` cycle to a priced `Fill` batch. -/

/-- **`fullFill n`** — the FULL fill of `n` at its limit price: spend the ENTIRE `offerAmount` at the
rate `ofMatchNode` carries (`limitPrice = wantMin / offerAmount`), so the fill delivers exactly `wantMin`
of `wantAsset` (`ofMatchNode_full_fill_meets_wantMin`). This is the priced Fill the exact-book leg
degenerates to — the connection point rung 5 already built. -/
def fullFill (n : MatchNode) : Fill where
  orderId   := n.creator
  order     := PricedOrder.ofMatchNode n
  filledIn  := (n.offerAmount : ℚ)
  execPrice := (PricedOrder.ofMatchNode n).limitPrice

/-- **`pricedFullFills ns`** — the priced Fill batch obtained by full-filling every node of the cycle.
The rung-5 `Fill`-model image of the rung-1/2 `MatchNode` cycle `ns`. -/
def pricedFullFills (ns : List MatchNode) : List Fill := ns.map fullFill

/-- **`TightCycle ns`** — every leg is FULL: the sender's whole `offerAmount` equals the next party's
`wantMin` (the amount the kernel leg actually settles, `chainedLeg … .amount`). This is the exact-swap
regime `CycleValid`'s `wantMin ≤ offerAmount` (`cycleValid_chains`) degenerates to at equality — the
case where a full fill at the limit price reproduces the executed leg exactly. -/
def TightCycle (ns : List MatchNode) : Prop :=
  ∀ k, k < ns.length →
    (ns.getD k default).offerAmount = (ns.getD ((k + 1) % ns.length) default).wantMin

/-! ## 2. The per-asset contributions of the full-fill lowering. -/

/-- What node `n`'s full fill CREDITS to asset `a`: `wantMin` if `a` is what `n` wants, else `0`. -/
def wantContrib (a : AssetId) (n : MatchNode) : ℚ :=
  if n.wantAsset = a then (n.wantMin : ℚ) else 0

/-- What node `n`'s full fill DEBITS from asset `a`: `offerAmount` if `a` is what `n` offers, else `0`. -/
def offerContrib (a : AssetId) (n : MatchNode) : ℚ :=
  if n.offerAsset = a then (n.offerAmount : ℚ) else 0

/-- **A full fill's `legDelta` is `wantContrib − offerContrib`.** The full fill delivers exactly
`wantMin` of `wantAsset` (by `ofMatchNode_full_fill_meets_wantMin`, needs `offerAmount ≠ 0`) and spends
`offerAmount` of `offerAsset` — so its per-asset net change is the credit minus the debit. -/
theorem legDelta_fullFill (a : AssetId) (n : MatchNode) (hne : (n.offerAmount : ℚ) ≠ 0) :
    legDelta (fullFill n) a = wantContrib a n - offerContrib a n := by
  have hout : (fullFill n).filledOut = (n.wantMin : ℚ) :=
    ofMatchNode_full_fill_meets_wantMin n hne
  unfold legDelta wantContrib offerContrib
  rw [hout]
  simp [fullFill, PricedOrder.ofMatchNode]
  -- v4.35: the two sides' `if`s carry different `Decidable` instances; `congr` identifies them.
  congr

/-- `(l.map (fun x => f x − g x)).sum = (l.map f).sum − (l.map g).sum` over ℚ. The additive split that
turns the batch's `netFlow` into (Σ credits) − (Σ debits). -/
theorem sum_map_sub {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ## 3. THE REINDEXING — the Σ of debits equals the Σ of credits (a rotation of the cycle). -/

/-- **`offerContrib_sum_eq_wantContrib_sum` — the debit total equals the credit total.** For a tight
valid cycle, `Σ offerContrib = Σ wantContrib` on every asset. The proof is the cycle's OWN rotation:
leg `k`'s debit (`offerContrib ns[k]`) equals node `(k+1) % m`'s credit (`wantContrib ns[(k+1)%m]`) —
by `cycleValid_chains` (`offerAsset[k] = wantAsset[(k+1)%m]`, the asset matches) and `TightCycle`
(`offerAmount[k] = wantMin[(k+1)%m]`, the amount matches). So `ns.map offerContrib` is
`(ns.rotate 1).map wantContrib`, whose sum is `(ns.map wantContrib)`'s by `rotate_perm`. This is the
telescoping that makes a full-fill clearing conserve. -/
theorem offerContrib_sum_eq_wantContrib_sum {ns : List MatchNode} (h : CycleValid ns)
    (htight : TightCycle ns) (a : AssetId) :
    (ns.map (offerContrib a)).sum = (ns.map (wantContrib a)).sum := by
  have hpos : 0 < ns.length := by have := h.len; omega
  have hlisteq : ns.map (offerContrib a) = (ns.rotate 1).map (wantContrib a) := by
    apply List.ext_getElem
    · simp [List.length_rotate]
    · intro k hk _hk2
      have hk' : k < ns.length := by simpa using hk
      have hj1 : (k + 1) % ns.length < ns.length := Nat.mod_lt _ hpos
      rw [List.getElem_map, List.getElem_map, List.getElem_rotate]
      -- goal: offerContrib a ns[k] = wantContrib a ns[(k+1) % ns.length]
      have hchain : (ns[k]'hk').offerAsset = (ns[(k + 1) % ns.length]'hj1).wantAsset := by
        have hc := (cycleValid_chains h k hk').1
        rwa [List.getD_eq_getElem ns default hk',
             List.getD_eq_getElem ns default hj1] at hc
      have htightk : (ns[k]'hk').offerAmount = (ns[(k + 1) % ns.length]'hj1).wantMin := by
        have hc := htight k hk'
        rwa [List.getD_eq_getElem ns default hk',
             List.getD_eq_getElem ns default hj1] at hc
      unfold offerContrib wantContrib
      rw [hchain, htightk]
  rw [hlisteq, List.map_rotate]
  exact (List.rotate_perm (ns.map (wantContrib a)) 1).sum_eq

/-! ## 4. THE MODEL SIDE — the full-fill lowering CONSERVES per asset (netFlow = 0 over ℚ). -/

/-- **`pricedFullFills_conserves` — a tight valid cycle's full-fill lowering conserves EVERY asset.**
`netFlow (pricedFullFills ns) a = 0` for all `a`: the priced model neither mints nor burns. The
rung-5 `Conserves` predicate, PROVED (not assumed) for the lowering of a solver-admitted tight cycle —
the model conservation the bridge realizes on the kernel. -/
theorem pricedFullFills_conserves {ns : List MatchNode} (h : CycleValid ns)
    (htight : TightCycle ns) (hoff : ∀ n ∈ ns, (n.offerAmount : ℚ) ≠ 0) :
    Conserves (pricedFullFills ns) := by
  intro a
  unfold netFlow pricedFullFills
  rw [List.map_map]
  have hmapeq : ns.map ((fun f => legDelta f a) ∘ fullFill)
      = ns.map (fun n => wantContrib a n - offerContrib a n) :=
    List.map_congr_left (fun n hn => legDelta_fullFill a n (hoff n hn))
  rw [hmapeq, sum_map_sub, offerContrib_sum_eq_wantContrib_sum h htight a, sub_self]

/-! ## 5. THE MODEL ↔ KERNEL CORRESPONDENCE — a priced fill spends its settlement leg's amount. -/

/-- **`fullFill_filledIn_eq_settleLeg` — the priced fill's spend IS the kernel leg's debit.** For a
tight valid cycle, node `j`'s full fill spends `offerAmount[j]`, and the `settleRing` leg `j` debits
exactly that (`chainedLeg`'s amount is the receiver's `wantMin`, which tightness equates to
`offerAmount[j]`). So the priced batch and the kernel ring move the SAME quantities — the fills ARE the
legs. -/
theorem fullFill_filledIn_eq_settleLeg {ns : List MatchNode} (htight : TightCycle ns)
    (j : ℕ) (hj : j < ns.length) :
    (fullFill (ns.getD j default)).filledIn
      = (((settlementsOf ns).getD j default).amount : ℚ) := by
  have hlen : (settlementsOf ns).length = ns.length := by
    simp [settlementsOf, chainedRing, List.length_map, List.length_range]
  have hj1 : (j + 1) % ns.length < ns.length := by
    have : 0 < ns.length := by omega
    exact Nat.mod_lt _ this
  have hgetD : (settlementsOf ns).getD j default = chainedLeg (ns.map MatchNode.toRingNode) j := by
    rw [List.getD_eq_getElem (settlementsOf ns) default (by rw [hlen]; exact hj)]
    simp [settlementsOf, chainedRing, List.getElem_map, List.getElem_range]
  have hamt : (chainedLeg (ns.map MatchNode.toRingNode) j).amount
      = (ns.getD ((j + 1) % ns.length) default).wantMin := by
    simp only [chainedLeg, map_toRingNode_length]
    rw [getD_map_toRingNode ns _ hj1]
    rfl
  have htightj := htight j hj
  rw [hgetD, hamt, ← htightj]
  simp [fullFill]

/-! ## 6. THE BRIDGE — the full-fill clearing is LEDGER-REALIZED on the verified executor. -/

/-- **`fullFill_cycle_ledger_realized` — THE WELD (full-fill case).** A tight valid cycle that settles
through the VERIFIED executor is realized on the real ledger:

  1. **(kernel-real)** `∀ b, recTotalAsset k' b = recTotalAsset k b` — the REAL executor preserves
     every asset's supply (`settleRing_conserves`, the SAME tie rung 1's
     `cycleValid_fulfilled_respects_limits` carries);
  2. **(model)** `Conserves (pricedFullFills ns)` — the priced full-fill lowering has `netFlow = 0`
     over ℚ (PROVED, §4);
  3. **(model ↔ kernel)** each priced fill spends EXACTLY its kernel settlement leg's amount (§5).

So the priced model's `netFlow = 0` (2) and the kernel's `recTotalAsset`-preservation (1) are two
readings of the SAME trades (3). Rung 5's conservation is LEDGER-REALIZED for the full-fill / tight
case — no longer a self-contained ℚ bookkeeping identity but the verified executor's own conservation.

SCOPE (honest): this is the full-fill / tight-cycle case only. Genuine partial fills (interior price,
spend < offer) do not lower to a single `settleRing` cycle — `partial-fill ledger-realization` is the
NAMED next sub-rung. The refusing power: a full-fill of a NON-tight cycle does NOT `Conserves`
(`nonTight_fullFill_not_conserving` below), so it is not realized. -/
theorem fullFill_cycle_ledger_realized {ns : List MatchNode}
    (h : CycleValid ns) (htight : TightCycle ns)
    (hoff : ∀ n ∈ ns, (n.offerAmount : ℚ) ≠ 0)
    (k k' : RecordKernelState)
    (hsettle : settleRing k (settlementsOf ns) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧
      Conserves (pricedFullFills ns) ∧
      (∀ j, j < ns.length →
        (fullFill (ns.getD j default)).filledIn
          = (((settlementsOf ns).getD j default).amount : ℚ)) :=
  ⟨settleRing_conserves (settlementsOf ns) k k' hsettle,
   pricedFullFills_conserves h htight hoff,
   fun j hj => fullFill_filledIn_eq_settleLeg htight j hj⟩

/-! ## 7. NON-VACUITY, positive polarity — a concrete TIGHT triangle is realized. -/

/-- A TIGHT 3-party cycle: everyone offers 6 and wants 6, chaining assets 10 → 11 → 12 → 10. Every
sender's full offer (6) is exactly the next party's minimum (6) — the full-fill regime. -/
def tightTriangle : List MatchNode :=
  [ { creator := 1, offerAsset := 10, offerAmount := 6, wantAsset := 12, wantMin := 6 },
    { creator := 2, offerAsset := 11, offerAmount := 6, wantAsset := 10, wantMin := 6 },
    { creator := 3, offerAsset := 12, offerAmount := 6, wantAsset := 11, wantMin := 6 } ]

/-- The tight triangle is a cycle the solver's graph admits (length 3, every edge compatible, creators
distinct). -/
theorem tightTriangle_valid : CycleValid tightTriangle where
  len := by decide
  edges := by decide
  distinct := by
    intro i j hi hj hij
    have hlen : tightTriangle.length = 3 := rfl
    rw [hlen] at hi hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi3 with rfl | rfl | rfl <;> rcases hj3 with rfl | rfl | rfl <;>
      first
      | (exact absurd rfl hij)
      | decide

/-- The triangle is TIGHT — every leg's full offer is the next party's minimum. -/
theorem tightTriangle_tight : TightCycle tightTriangle := by
  intro k hk
  have hk3 : k < 3 := hk
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl <;> decide

/-- Every offer is positive (`≠ 0` over ℚ), so the full-fill delivers exactly `wantMin`. -/
theorem tightTriangle_offerNZ : ∀ n ∈ tightTriangle, (n.offerAmount : ℚ) ≠ 0 := by
  intro n hn
  fin_cases hn <;> norm_num

/-- **The tight triangle's full-fill lowering CONSERVES every asset.** A real priced/full-fill
clearing that neither mints nor burns — the model side of the realization, computed. -/
theorem tightTriangle_model_conserves : Conserves (pricedFullFills tightTriangle) :=
  pricedFullFills_conserves tightTriangle_valid tightTriangle_tight tightTriangle_offerNZ

/-- **THE BRIDGE, INSTANTIATED — the tight triangle is LEDGER-REALIZED.** For ANY settlement of it
through the verified executor: the kernel preserves every asset's supply, the priced full-fill lowering
conserves, and the fills spend exactly the settlement legs' amounts. The full-fill clearing, realized
on the real ledger (modulo the settlement hypothesis, exactly as rung 1's
`cycleValid_fulfilled_respects_limits`). -/
theorem tightTriangle_ledger_realized (k k' : RecordKernelState)
    (hsettle : settleRing k (settlementsOf tightTriangle) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧
      Conserves (pricedFullFills tightTriangle) ∧
      (∀ j, j < tightTriangle.length →
        (fullFill (tightTriangle.getD j default)).filledIn
          = (((settlementsOf tightTriangle).getD j default).amount : ℚ)) :=
  fullFill_cycle_ledger_realized tightTriangle_valid tightTriangle_tight
    tightTriangle_offerNZ k k' hsettle

/-! ### `#guard` smoke — the model conserves and the fills match the legs, computed. -/

-- the full-fill lowering nets to zero on every traded asset (conservation, computed):
#guard netFlow (pricedFullFills tightTriangle) 10 == (0 : ℚ)
#guard netFlow (pricedFullFills tightTriangle) 11 == (0 : ℚ)
#guard netFlow (pricedFullFills tightTriangle) 12 == (0 : ℚ)
-- each fill spends 6 = the kernel settlement leg's amount (the model↔kernel correspondence):
#guard (fullFill (tightTriangle.getD 0 default)).filledIn == (6 : ℚ)
#guard ((settlementsOf tightTriangle).getD 0 default).amount == 6
#guard (fullFill (tightTriangle.getD 1 default)).filledIn == (6 : ℚ)
#guard ((settlementsOf tightTriangle).getD 1 default).amount == 6
#guard (fullFill (tightTriangle.getD 2 default)).filledIn == (6 : ℚ)
#guard ((settlementsOf tightTriangle).getD 2 default).amount == 6
-- each full fill delivers exactly its wanted minimum (6), in its wanted asset:
#guard (fullFill (tightTriangle.getD 0 default)).filledOut == (6 : ℚ)

/-! ## 8. NON-VACUITY, negative polarity — a full-fill of a NON-tight cycle is NOT realized. -/

/-- **TOOTH: a full-fill of a NON-tight cycle does NOT conserve.** `Fairness.validTriangle` is a valid
cycle but NOT tight (offers 8/9/7 against wants 4/6/5 — strict surplus). Filling every node to its FULL
offer would spend 8/9/7 while delivering only 4/6/5, minting/burning value: `netFlow · 10 = 6 − 8 =
−2 ≠ 0`. So the full-fill model does NOT `Conserves` a non-tight cycle — it is NOT ledger-realized.
Tightness is load-bearing; the realization refuses a non-conserving full clearing. (The kernel's OWN
settlement of `validTriangle` settles the RECEIVER's `wantMin` per leg, not the full offer — that is
the genuine partial fill this module NAMES as the next sub-rung.) -/
theorem nonTight_fullFill_not_conserving : ¬ Conserves (pricedFullFills validTriangle) := by
  intro hc
  have h10 := hc 10
  simp only [netFlow, pricedFullFills, validTriangle, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, fullFill, PricedOrder.ofMatchNode, legDelta, Fill.filledOut] at h10
  norm_num at h10

/-- **TOOTH: an over-debiting cycle never even forms** (echo of `Fairness.overdebit_refused`). Ring's
`underfundCycle` (node 1 demands 50 of an offer of 3) is not `CycleValid`, so no `settlementsOf` /
`settleRing` — and hence no ledger realization — is ever constructed from it. A clearing that would
breach a limit is refused at formation, before any lowering. -/
theorem underfund_not_realizable : ¬ CycleValid underfundCycle :=
  overdebit_refused

/-! ### Axiom hygiene — the ledger-realization bridge pinned to the three kernel axioms. -/

#assert_all_clean [Market.legDelta_fullFill, Market.sum_map_sub,
  Market.offerContrib_sum_eq_wantContrib_sum, Market.pricedFullFills_conserves,
  Market.fullFill_filledIn_eq_settleLeg, Market.fullFill_cycle_ledger_realized,
  Market.tightTriangle_valid, Market.tightTriangle_tight, Market.tightTriangle_offerNZ,
  Market.tightTriangle_model_conserves, Market.tightTriangle_ledger_realized,
  Market.nonTight_fullFill_not_conserving, Market.underfund_not_realizable]

end Market
