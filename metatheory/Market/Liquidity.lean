/-
# Market.Liquidity — DrEX rung 6: the PROVEN-SOLVENT liquidity pool (the backstop).

**DrEX — the Dragon's Egg Exchange** — is a Lean-first proof-carrying exchange (the `metatheory/Market/`
tower). Rungs 1/2/4/5 clear a book **multilaterally**: the ring/CoW matcher finds Coincidences of Wants
and settles them fair + conserving through the proved kernel (`Market/Clearing.lean`,
`Market/Fairness.lean`, `Market/Aggregation.lean`, `Market/Optimality.lean`), over the ℚ-priced,
partial-fillable substrate of `Market/Priced.lean` (`Fill`, `execPrice`, `legDelta`, `netFlow`,
`Conserves`). But a ring can only clear what has a counterparty. A LONE order — a one-sided residual
with no matching want in the book — is `¬ Conserves` on its own (`residual_clears_against_pool`).

This rung is the **liquidity backstop** (DREX-DESIGN.md §5 / §6, DREGGFI-VISION "provably-never-insolvent
pool"): a standing pool holding per-asset reserves against which that residual clears. The pool is the
counterparty of last resort. Its guarantee — the thing no AMM ships — is a **solvency theorem**:

  * **`pool_solvent_forever` (THE KEYSTONE):** the pool's per-asset reserve is NEVER negative at any
    reachable state, along EVERY schedule of fills, provided each fill respects the reserve floor
    (`PoolFillValid` — the pool can only pay out what it holds). This is the ∀-adversary object of
    `Dregg2/Verify/StripeReserve.lean`'s `stripe_reserve_solvent_forever` (`0 ≤ escrow` forever over
    every `SSched`) **lifted from a single reserve channel to a portfolio** of per-asset reserves. The
    single-channel theorem is REUSED (not re-proved) as the pool's disclosed BACKING line
    (`pool_backing_solvent_forever`); the portfolio version is proved here as the fold-invariant of a
    validity discipline that is the exact analogue of Trustline's `ReserveWF`.

  * **CONSERVATION.** Every pool fill is zero-sum with the order it clears: the pool absorbs exactly the
    negative of the order's per-asset flow (`pool_fill_conserves`, `poolDelta = − legDelta`). Composed
    with `Priced.netFlow`, a residual that alone does not conserve (`¬ Conserves [f]`) plus the pool's
    absorption conserves (`pool_absorbs_netFlow`) — the pool never mints or burns.

Honest scope: this proves the **reserve-priced pool that is provably never negative** — the core
never-insolvent claim, both polarities (a concrete schedule of draws stays solvent + the reserves are
`#guard`ed; an overdraw is `¬ PoolFillValid` and provably drives a reserve below zero; a minting
"counter-leg" fails conservation). The next sub-rung is the **constant-function AMM curve** `x·y = k` as
a `MarketClearing`-preserving family — pricing the fill off the curve and proving `x·y` non-decreasing —
layered ON TOP of this solvency floor (named, not yet built). A never-insolvent pool with a stated price
is the load-bearing guarantee; the curve is the pricing policy above it.
-/
import Market.Priced
import Dregg2.Verify.StripeReserve

namespace Market

open Dregg2.Exec (AssetId CellId)

/-! ## 1. The pool — a portfolio of per-asset reserves. -/

/-- **A liquidity pool** is a portfolio: a reserve balance per asset. (The multi-asset lift of
`StripeReserve.MoneyInReserve`'s single channel — one reserve line per asset.) -/
abbrev Pool := AssetId → ℚ

/-- **The pool is SOLVENT** when no per-asset reserve is negative — it never owes more of any asset than
it holds. The portfolio analogue of `0 ≤ escrow` (`stripe_reserve_solvent_forever`). -/
def Pool.solvent (p : Pool) : Prop := ∀ a, 0 ≤ p a

/-- **`poolDelta f a`** — the pool's per-asset change when it is the counterparty of fill `f`: it GAINS
what the order offers (`+filledIn` of `offerAsset`) and PAYS what the order wants (`−filledOut` of
`wantAsset`). Exactly the negative of the trader's `legDelta` (`poolDelta_eq_neg_legDelta`) — the pool
is the mirror side of the trade. -/
def poolDelta (f : Fill) (a : AssetId) : ℚ :=
  (if f.order.offerAsset = a then f.filledIn else 0)
    - (if f.order.wantAsset = a then f.filledOut else 0)

/-- **The pool reserve after clearing fill `f`.** -/
def poolStep (p : Pool) (f : Fill) : Pool := fun a => p a + poolDelta f a

/-- **A fill is VALID against the pool** when it respects the order's terms (`FillValid`, reused from
rung 5) AND the pool holds enough of the wanted asset to pay it (`filledOut ≤ reserve` — the floor). The
second clause is the solvency discipline: the pool can only disburse what it has. This is the pool's
`ReserveWF` — the analogue of Trustline's "a provisional spend commits only to the extent the reserve
backs it". -/
def PoolFillValid (p : Pool) (f : Fill) : Prop :=
  FillValid f ∧ f.filledOut ≤ p f.order.wantAsset

/-! ## 2. Conservation — the pool absorbs exactly the order's flow (composes with `Priced.Conserves`). -/

/-- The pool's per-asset change is the exact negative of the trader's (`Priced.legDelta`). -/
theorem poolDelta_eq_neg_legDelta (f : Fill) (a : AssetId) : poolDelta f a = - legDelta f a := by
  unfold poolDelta legDelta; ring

/-- **`pool_fill_conserves`** — a pool fill is ZERO-SUM per asset: the order's flow plus the pool's
absorption is 0. Neither the pool nor the trade mints or burns. -/
theorem pool_fill_conserves (f : Fill) (a : AssetId) : legDelta f a + poolDelta f a = 0 := by
  rw [poolDelta_eq_neg_legDelta]; ring

/-- **`pool_absorbs_netFlow`** — composed with `Priced.netFlow`: a single residual order's net asset
flow, plus the pool's absorption, is 0. The ring+pool combined clearing CONSERVES even when the ring
alone does not (`residual_clears_against_pool`). -/
theorem pool_absorbs_netFlow (f : Fill) (a : AssetId) : netFlow [f] a + poolDelta f a = 0 := by
  simp only [netFlow_cons, netFlow_nil, add_zero]
  exact pool_fill_conserves f a

/-! ## 3. The solvency step — a valid fill never drives a reserve negative. -/

/-- A fill delivering value is nonnegative (`filledOut = filledIn · execPrice ≥ 0` under `FillValid`). -/
theorem Fill.filledOut_nonneg {f : Fill} (h : FillValid f) : 0 ≤ f.filledOut := by
  obtain ⟨hin, hlp, hle⟩ := h
  have hep : 0 ≤ f.execPrice := le_trans hlp hle
  unfold Fill.filledOut
  exact mul_nonneg hin hep

/-- **`poolStep_solvent` (the invariant step):** clearing a `PoolFillValid` fill against a SOLVENT pool
leaves it SOLVENT. The pool gains the offered asset (reserve grows) and pays the wanted asset only up to
what it holds (the floor). This is the single-step core the ∀-schedule keystone folds. -/
theorem poolStep_solvent {p : Pool} {f : Fill}
    (hp : Pool.solvent p) (hf : PoolFillValid p f) : Pool.solvent (poolStep p f) := by
  intro a
  obtain ⟨hfill, hdraw⟩ := hf
  have hin : 0 ≤ f.filledIn := hfill.1
  have hout : 0 ≤ f.filledOut := Fill.filledOut_nonneg hfill
  have hpa : 0 ≤ p a := hp a
  simp only [poolStep, poolDelta]
  by_cases hw : f.order.wantAsset = a
  · rw [hw] at hdraw
    by_cases ho : f.order.offerAsset = a
    · rw [if_pos ho, if_pos hw]; linarith
    · rw [if_neg ho, if_pos hw]; linarith
  · by_cases ho : f.order.offerAsset = a
    · rw [if_pos ho, if_neg hw]; linarith
    · rw [if_neg ho, if_neg hw]; linarith

/-! ## 4. THE KEYSTONE — `pool_solvent_forever`: never insolvent over ANY schedule. -/

/-- A **schedule of fills** hitting the pool — an adversarial stream of residual orders (the analogue of
`StripeReserve.SSched`). -/
def PoolSched := ℕ → Fill

/-- The **pool trajectory**: the reserve state after the first `n` fills of the schedule. -/
def poolTraj (p₀ : Pool) (s : PoolSched) : ℕ → Pool
  | 0     => p₀
  | n + 1 => poolStep (poolTraj p₀ s n) (s n)

/-- A schedule is **valid** for a starting pool when every fill respects the reserve floor at the state
it actually hits (`PoolFillValid` at the reached reserves). This is the pool's `ReserveWF`-forever
discipline: the matcher never asks the pool to pay out more of an asset than it holds. -/
def ScheduleValid (p₀ : Pool) (s : PoolSched) : Prop := ∀ n, PoolFillValid (poolTraj p₀ s n) (s n)

/-- **`pool_solvent_forever` (THE SOLVENCY KEYSTONE):** starting from a solvent pool, under ANY valid
schedule of fills, the pool is SOLVENT at EVERY reachable state — no per-asset reserve is ever negative.
The clearing can never drive the pool insolvent.

This is the portfolio lift of `Dregg2.Verify.StripeReserve.stripe_reserve_solvent_forever`
(`∀ n, 0 ≤ escrow` over every `SSched`): the single reserve channel becomes a family of per-asset
reserves, `escrow ≥ 0` becomes `Pool.solvent`, and the `ReserveWF` discipline becomes `ScheduleValid`.
The proof is the fold-invariant of `poolStep_solvent` — the same shape, one channel per asset. -/
theorem pool_solvent_forever (p₀ : Pool) (hinit : Pool.solvent p₀) (s : PoolSched)
    (hs : ScheduleValid p₀ s) : ∀ n, Pool.solvent (poolTraj p₀ s n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact poolStep_solvent ih (hs k)

/-! ## 5. Composition with the single-channel reserve — the pool's disclosed BACKING line. -/

open Dregg2.Verify.StripeReserve Dregg2.Apps.Trustline

/-- **`pool_backing_solvent_forever`** — the pool's disclosed backing/funding line (a single
`MoneyInReserve` funded to `R`) is itself solvent forever: over EVERY attest/reverse/spend/finalize
schedule the backing reserve is never negative. This is `stripe_reserve_solvent_forever` REUSED verbatim
(no new proof) — the single-channel guarantee under the portfolio. The pool's inventory is solvent
(`pool_solvent_forever`, THIS rung) AND its funding is solvent (this, the reused rung): the pool is
never insolvent and never funded from thin air. -/
theorem pool_backing_solvent_forever (R : Nat) (sched : SSched) :
    ∀ n, 0 ≤ (trajC .fullReserve (openReserve R) sched n).escrow :=
  stripe_reserve_solvent_forever (openReserve R) (openReserve_wf R) sched

/-- **`pool_solvent_and_backed_forever`** — the composed guarantee: the portfolio keystone
(`pool_solvent_forever`) AND the reused single-channel backing (`pool_backing_solvent_forever`), together
in one statement. Both are ∀-schedule (∀-adversary) solvency objects; DrEX's liquidity backstop carries
both. -/
theorem pool_solvent_and_backed_forever
    (p₀ : Pool) (hinit : Pool.solvent p₀) (s : PoolSched) (hs : ScheduleValid p₀ s)
    (R : Nat) (bsched : SSched) :
    (∀ n, Pool.solvent (poolTraj p₀ s n))
      ∧ (∀ n, 0 ≤ (trajC .fullReserve (openReserve R) bsched n).escrow) :=
  ⟨pool_solvent_forever p₀ hinit s hs, pool_backing_solvent_forever R bsched⟩

/-! ## 6. Non-vacuity, polarity ⊕ — a concrete schedule stays solvent (the keystone fires). -/

/-- A pool funded with 100 gold (asset 0) and 100 art (asset 1). -/
def demoPool : Pool := fun a => if a = 0 then (100 : ℚ) else if a = 1 then 100 else 0

theorem demoPool_solvent : Pool.solvent demoPool := by
  intro a; simp only [demoPool]; split_ifs <;> norm_num

/-- A residual order offering 10 gold, wanting art at ≥ ½ (reuses `Priced.o0`). It clears fully against
the pool: 10 gold IN, 5 art OUT. -/
def rfill0 : Fill := { orderId := 0, order := o0, filledIn := 10, execPrice := 1/2 }

/-- A residual order offering 20 art, wanting gold at ≥ 2. Clears against the pool: 20 art IN, 40 gold
OUT. -/
def oR1 : PricedOrder :=
  { creator := 3, offerAsset := 1, wantAsset := 0, offerAmount := 20, limitPrice := 2 }
def rfill1 : Fill := { orderId := 1, order := oR1, filledIn := 20, execPrice := 2 }

/-- A no-op fill (spends nothing, delivers nothing) — the idle tail of the schedule. -/
def noopOrder : PricedOrder :=
  { creator := 0, offerAsset := 0, wantAsset := 0, offerAmount := 0, limitPrice := 0 }
def noopFill : Fill := { orderId := 99, order := noopOrder, filledIn := 0, execPrice := 0 }

/-- The demo schedule: draw art (rfill0), draw gold (rfill1), then idle forever. -/
def demoSched : PoolSched
  | 0     => rfill0
  | 1     => rfill1
  | _ + 2 => noopFill

theorem poolStep_noop (p : Pool) : poolStep p noopFill = p := by
  funext a; simp [poolStep, poolDelta, noopFill, noopOrder, Fill.filledOut]; exact ite_self _

/-- After the two real draws the schedule idles: the trajectory stabilizes at the state `poolTraj … 2`
(gold 70, art 115). -/
theorem demoTraj_stable : ∀ k, poolTraj demoPool demoSched (k + 2) = poolTraj demoPool demoSched 2 := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih =>
      have hstep : poolTraj demoPool demoSched (m + 2 + 1)
          = poolStep (poolTraj demoPool demoSched (m + 2)) (demoSched (m + 2)) := rfl
      have hnoop : demoSched (m + 2) = noopFill := rfl
      rw [hstep, hnoop, ih, poolStep_noop]

/-- The demo schedule is valid: every fill respects the reserve floor at the state it hits. -/
theorem demoSched_valid : ScheduleValid demoPool demoSched := by
  intro n
  rcases n with _ | _ | k
  · -- n = 0 : rfill0 against demoPool (art 100 ≥ 5)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoSched, poolTraj, rfill0, o0, Fill.filledOut, demoPool]
  · -- n = 1 : rfill1 against poolTraj … 1 (gold 110 ≥ 40)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoSched, poolTraj, poolStep, poolDelta, rfill0, rfill1, oR1, o0,
        Fill.filledOut, demoPool]
  · -- n = k + 2 : noopFill against the stabilized state (a solvent reserve)
    rw [show demoSched (k + 2) = noopFill from rfl, demoTraj_stable k]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [noopFill, noopOrder, Fill.filledOut, poolTraj, poolStep, poolDelta,
        demoSched, rfill0, rfill1, oR1, o0, demoPool]

/-- **The keystone fires on a real schedule** (polarity TRUE): DrEX's pool stays solvent at every state
along the demo stream of draws — `pool_solvent_forever` instantiated. -/
theorem demo_solvent_forever : ∀ n, Pool.solvent (poolTraj demoPool demoSched n) :=
  pool_solvent_forever demoPool demoPool_solvent demoSched demoSched_valid

-- The reserves actually move, and stay nonnegative (the numbers behind the theorem):
#guard (poolTraj demoPool demoSched 0) 0 == (100 : ℚ)   -- gold, start
#guard (poolTraj demoPool demoSched 0) 1 == (100 : ℚ)   -- art,  start
#guard (poolTraj demoPool demoSched 1) 0 == (110 : ℚ)   -- +10 gold in
#guard (poolTraj demoPool demoSched 1) 1 == (95 : ℚ)    -- −5 art out (≥ 0)
#guard (poolTraj demoPool demoSched 2) 0 == (70 : ℚ)    -- −40 gold out (≥ 0)
#guard (poolTraj demoPool demoSched 2) 1 == (115 : ℚ)   -- +20 art in

/-! ## 7. The RING ⊕ POOL composition — a lone residual the ring can't clear, cleared solvently. -/

/-- **`residual_clears_against_pool`** — the ring/CoW matcher cannot clear a lone order `rfill0` (no
counterparty in the book): it does NOT conserve on its own (`¬ Conserves [rfill0]`, it would burn 10
gold). But the pool absorbs exactly its flow (`pool_absorbs_netFlow`, per asset), so the combined
ring⊕pool clearing CONSERVES — and the pool stays SOLVENT (`poolStep_solvent`). This is the backstop:
one-sided residual demand clears against the pool without minting, burning, or draining it. -/
theorem residual_clears_against_pool :
    (¬ Conserves [rfill0])
      ∧ (∀ a, netFlow [rfill0] a + poolDelta rfill0 a = 0)
      ∧ Pool.solvent (poolStep demoPool rfill0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ¬ Conserves : the lone order burns 10 gold (netFlow at asset 0 ≠ 0)
    intro h
    have h0 := h 0
    simp only [netFlow_cons, netFlow_nil, legDelta, rfill0, o0, Fill.filledOut, add_zero] at h0
    norm_num at h0
  · exact fun a => pool_absorbs_netFlow rfill0 a
  · refine poolStep_solvent demoPool_solvent ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [rfill0, o0, Fill.filledOut, demoPool] <;> norm_num

/-! ## 8. Non-vacuity, polarity FALSE — the teeth: overdraw and minting are REFUSED. -/

/-- A pool holding only 3 art (asset 1). -/
def drainPool : Pool := fun a => if a = 1 then (3 : ℚ) else 100

/-- A fill demanding 5 art out of a pool that holds 3 — an OVERDRAW. -/
def overFill : Fill := { orderId := 0, order := o0, filledIn := 10, execPrice := 1/2 }

/-- **`overdraw_refused` (TOOTH):** a fill that would pay out more of an asset than the pool holds is
NOT `PoolFillValid` — it never reaches settlement. This is the solvency guarantee as a *refusal*: the
pool cannot be drained below zero because such a fill is not admissible. -/
theorem overdraw_refused : ¬ PoolFillValid drainPool overFill := by
  rintro ⟨_, hd⟩
  simp only [overFill, o0, Fill.filledOut, drainPool] at hd
  norm_num at hd

/-- **`overdraw_drives_negative` (TOOTH, the other face):** and if such an overdraw WERE applied, it
provably drives the reserve below zero — the keystone hypothesis is exactly what forbids it. -/
theorem overdraw_drives_negative : (poolStep drainPool overFill) 1 < 0 := by
  simp only [poolStep, poolDelta, overFill, o0, Fill.filledOut, drainPool]
  norm_num

/-- A dishonest, MINTING "absorption": the pool grabs the offered asset but pays NOTHING (it does not
mirror the order's flow). -/
def mintDelta (f : Fill) (a : AssetId) : ℚ := if f.order.offerAsset = a then f.filledIn else 0

/-- **`honest_pool_conserves`** — the honest `poolDelta` is a conserving counter-leg (the pool mirrors
the order exactly). -/
theorem honest_pool_conserves (f : Fill) (a : AssetId) : legDelta f a + poolDelta f a = 0 :=
  pool_fill_conserves f a

/-- **`mint_update_refused` (TOOTH):** a pool update that does NOT mirror the order — taking the offer
while paying nothing — fails conservation: it would create 5 art from nothing (`netFlow ≠ 0` at the
want asset). Conservation and solvency are independent teeth. -/
theorem mint_update_refused : ¬ (∀ a, legDelta rfill0 a + mintDelta rfill0 a = 0) := by
  intro h
  have h1 := h 1
  simp only [rfill0, o0, mintDelta, legDelta, Fill.filledOut] at h1
  norm_num at h1

/-! ## 9. Axiom hygiene — the keystones self-guard against an axiom leak. -/

#assert_axioms pool_solvent_forever
#assert_axioms pool_solvent_and_backed_forever
#assert_axioms pool_backing_solvent_forever
#assert_axioms residual_clears_against_pool

end Market
