/-
# Dregg2.Verify.StripeKernelRefine — grounding the reserve in the KERNEL state (kernel refinement).

The reserve apex + the money-in bridge live over the abstract Trustline `ChannelC` register model.
This module begins the forward-simulation refinement that grounds those registers in the real kernel
`RecordKernelState` cells (where `StripeBridgeV2`'s `Intent/Lifecycle` mint actually moves value).

The projection constructs a WELL-FORMED reserve from two kernel cell balances — the exposure cell
(holding `drawn`, the spent-provisional) and the settled cell (holding `settled`, the realized loss).
`ChannelC`/`Line`'s structural invariants (`holderAcct = drawn`, `issuerWell = −drawn`,
`escrow = ceiling − settled`, `draws.Nodup`) are set by the projection by construction, so
well-formedness reduces to the two order facts `drawn ≤ R ∧ settled ≤ drawn` (the "reserve-shaped"
predicate on the kernel state).

This module (COMPLETE): (1) the projection + its well-formedness + the loss-bound instantiated FROM the
kernel projection; (2) the per-op forward simulation — `mint_refines`/`finalize_refines`/`reverse_refines`
prove each kernel op tracks the money-in op under `Refines`, and `kernel_run_loss_bounded` transfers the
bound to the kernel's OWN trajectory: realized loss ≤ R at every reachable kernel state, for any
adversarial run of attested mints / finalizes / reverses.
-/
import Dregg2.Verify.StripeMoneyIn
import Dregg2.Intent.Lifecycle

namespace Dregg2.Verify.StripeKernelRefine

open Dregg2.Apps.Trustline
open Dregg2.Verify.StripeReserve
open Dregg2.Verify.StripeMoneyIn
open Dregg2.Exec (RecordKernelState CellId AssetId)

/-- Construct a reserve `Line` from `(R, drawn)`: the derived registers (`holderAcct = +drawn`,
`issuerWell = −drawn`, no committed digests) are set by construction. -/
def mkLine (R d : Nat) : Line :=
  { ceiling := R, drawn := d, draws := [], holderAcct := (d : Int), issuerWell := -(d : Int) }

/-- Construct a fullReserve `ChannelC` from `(R, drawn, settled)` — the escrow tracks the unredeemed
line `R − settled` by construction; the hard columns are level. -/
def mkReserve (R d settled : Nat) : MoneyInReserve :=
  { s := { tl := mkLine R d, settled := settled }, escrow := (R : Int) - (settled : Int),
    issuerHard := 0, holderHard := 0 }

/-- The projection is well-formed exactly when `drawn ≤ R` and `settled ≤ drawn`; every other
`ReserveWF` conjunct holds by construction. -/
theorem mkReserve_WF (R d settled : Nat) (h1 : d ≤ R) (h2 : settled ≤ d) :
    (mkReserve R d settled).ReserveWF :=
  ⟨⟨⟨h1, rfl, rfl, List.nodup_nil⟩, h2⟩, rfl⟩

/-- **The projection** — read the kernel's exposure/settled cell balances into a reserve `ChannelC`.
`exposureCell` holds the spent-provisional (`drawn`); `settledCell` holds the realized loss
(`settled`); `R` is the disclosed reserve line. -/
def kToReserve (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) : MoneyInReserve :=
  mkReserve R (k.bal exposureCell asset).toNat (k.bal settledCell asset).toNat

/-- A kernel state is **reserve-shaped** for these cells iff its exposure ≤ R and its settled ≤ its
exposure — the two order facts the projection needs (all structural invariants are then automatic). -/
def ReserveShaped (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) : Prop :=
  (k.bal exposureCell asset).toNat ≤ R ∧
    (k.bal settledCell asset).toNat ≤ (k.bal exposureCell asset).toNat

/-- **`kToReserve_WF`** — a reserve-shaped kernel state projects to a well-formed reserve. The
foothold: the kernel state is now a valid starting point for the reserve apex. -/
theorem kToReserve_WF (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) (h : ReserveShaped exposureCell settledCell asset R k) :
    (kToReserve exposureCell settledCell asset R k).ReserveWF :=
  mkReserve_WF R _ _ h.1 h.2

/-- **`kernel_reserve_loss_bounded`** — the money-in loss-bound applies FROM the kernel projection:
for ANY money-in schedule started at the projection of a reserve-shaped kernel state, dregg's realized
loss never exceeds the disclosed reserve R (`net ≥ −R`). Grounds the abstract reserve in the real
kernel state's exposure/settled cells (refinement step 1; step 2 = the per-op kernel simulation). -/
theorem kernel_reserve_loss_bounded (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) (h : ReserveShaped exposureCell settledCell asset R k) (m : MISched) :
    ∀ n, ((miTraj (kToReserve exposureCell settledCell asset R k) m n).s.settled : Int)
          ≤ ((miTraj (kToReserve exposureCell settledCell asset R k) m n).s.tl.ceiling : Int) :=
  stripe_money_in_loss_bounded_e2e _ (kToReserve_WF exposureCell settledCell asset R k h) m

/-! ## Step 2 — the forward simulation: the kernel's OWN op tracks the reserve under `Refines`. -/

/-- **The refinement relation.** Matches the two kernel cell balances to the reserve's `drawn`/`settled`
and pins the ceiling + well-formedness. It is up-to-`Refines` (not equality): the projection forgets the
Trustline digest registry, which a `RecordKernelState` does not carry. -/
def Refines (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) (c : MoneyInReserve) : Prop :=
  (k.bal exposureCell asset).toNat = c.s.tl.drawn ∧
    (k.bal settledCell asset).toNat = c.s.settled ∧
    c.s.tl.ceiling = R ∧ c.ReserveWF

/-- The projection of a reserve-shaped kernel state refines it. -/
theorem kToReserve_Refines (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) (h : ReserveShaped exposureCell settledCell asset R k) :
    Refines exposureCell settledCell asset R k (kToReserve exposureCell settledCell asset R k) :=
  ⟨rfl, rfl, rfl, kToReserve_WF exposureCell settledCell asset R k h⟩

/-- **`mint_refines` — the mint simulation (closes the fidelity concern).** A kernel provisional-mint
that credits the exposure cell by `amt` — within the reserve, with a fresh draw digest — tracks the
money-in `mint` op under `Refines`: the op advances `drawn` by *exactly* the minted `amt`, so the
abstract exposure equals the real kernel exposure-cell balance. Settled is untouched; well-formedness
comes free from `stepC_preserves_ReserveWF`. -/
theorem mint_refines
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k k' : RecordKernelState) (c : MoneyInReserve) (pi d amt : Nat)
    (hR : Refines exposureCell settledCell asset R k c)
    (hfresh : d ∉ c.s.tl.draws)
    (hwithin : amt ≤ R - c.s.tl.drawn)
    (hexp : (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat + amt)
    (hset : (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat) :
    Refines exposureCell settledCell asset R k' (miStep c (.mint pi d amt)) := by
  obtain ⟨he, hs, hc, hwf⟩ := hR
  have hlt : amt ≤ c.s.tl.ceiling - c.s.tl.drawn := by omega
  have hfire : miStep c (MIOp.mint pi d amt)
      = c.withS { c.s with tl :=
          { c.s.tl with drawn := c.s.tl.drawn + amt, draws := d :: c.s.tl.draws
                      , holderAcct := c.s.tl.holderAcct + (amt : Int)
                      , issuerWell := c.s.tl.issuerWell - (amt : Int) } } := by
    show ((drawS c.s d amt).map c.withS).getD c = _
    unfold drawS draw
    rw [if_neg hfresh, if_pos hlt]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfire]; show (k'.bal exposureCell asset).toNat = c.s.tl.drawn + amt; rw [hexp, he]
  · rw [hfire]; show (k'.bal settledCell asset).toNat = c.s.settled; rw [hset, hs]
  · rw [hfire]; exact hc
  · exact stepC_preserves_ReserveWF c (.draw d amt) hwf

/-- **`finalize_refines`** — a kernel finalize that debits the exposure cell by `amt` (within the
outstanding draw) tracks the money-in `finalize` op: `drawn` drops by exactly `amt`, `settled` fixed. -/
theorem finalize_refines
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k k' : RecordKernelState) (c : MoneyInReserve) (amt : Nat)
    (hR : Refines exposureCell settledCell asset R k c)
    (hwithin : amt ≤ c.s.outstanding)
    (hexp : (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat - amt)
    (hset : (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat) :
    Refines exposureCell settledCell asset R k' (miStep c (.finalize amt)) := by
  obtain ⟨he, hs, hc, hwf⟩ := hR
  obtain ⟨s', hsome⟩ := Option.isSome_iff_exists.mp ((repayS_fires_iff c.s amt).mpr hwithin)
  have hstep : miStep c (MIOp.finalize amt) = c.withS s' := by
    show ((repayS c.s amt).map c.withS).getD c = _
    rw [hsome]; rfl
  obtain ⟨-, tl', hrepay, rfl⟩ := repayS_spec hsome
  obtain ⟨-, rfl⟩ := repay_spec hrepay
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep]; show (k'.bal exposureCell asset).toNat = c.s.tl.drawn - amt; rw [hexp, he]
  · rw [hstep]; show (k'.bal settledCell asset).toNat = c.s.settled; rw [hset, hs]
  · rw [hstep]; exact hc
  · exact stepC_preserves_ReserveWF c (.repay amt) hwf

/-- **`reverse_refines`** — a kernel reverse that credits the settled cell by `loss` (within the
outstanding draw) tracks the money-in `reverse` op: `settled` rises by exactly `loss`, `drawn` fixed;
the reserve fund `escrow` drops by `loss`, all under the `settleC` fullReserve step. -/
theorem reverse_refines
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k k' : RecordKernelState) (c : MoneyInReserve) (loss : Nat)
    (hR : Refines exposureCell settledCell asset R k c)
    (hwithin : loss ≤ c.s.outstanding)
    (hexp : (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat)
    (hset : (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat + loss) :
    Refines exposureCell settledCell asset R k' (miStep c (.reverse loss)) := by
  obtain ⟨he, hs, hc, hwf⟩ := hR
  obtain ⟨s', hsome⟩ := Option.isSome_iff_exists.mp ((settleS_fires_iff c.s loss).mpr hwithin)
  have hstep : miStep c (MIOp.reverse loss)
      = { c with s := s', escrow := c.escrow - (loss : Int), holderHard := c.holderHard + (loss : Int) } := by
    show (settleC .fullReserve c loss).getD c = _
    simp [settleC, hsome]
  obtain ⟨-, rfl⟩ := settleS_spec hsome
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep]; show (k'.bal exposureCell asset).toNat = c.s.tl.drawn; rw [hexp, he]
  · rw [hstep]; show (k'.bal settledCell asset).toNat = c.s.settled + loss; rw [hset, hs]
  · rw [hstep]; exact hc
  · exact stepC_preserves_ReserveWF c (.settle loss) hwf

/-- **`refines_loss_bounded`** — any kernel state that refines the reserve has realized loss ≤ R.
Directly from `solvency` (`settled ≤ ceiling`) on the reserve well-formedness. -/
theorem refines_loss_bounded
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (k : RecordKernelState) (c : MoneyInReserve)
    (hR : Refines exposureCell settledCell asset R k c) :
    (k.bal settledCell asset).toNat ≤ R := by
  obtain ⟨he, hs, hc, hwf⟩ := hR
  rw [hs, ← hc]; exact solvency hwf.1

/-- A valid kernel money-in step: the kernel cell-balance changes + gate for the op it realizes. -/
def ValidKernelStep (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (c : MoneyInReserve) (k : RecordKernelState) (op : MIOp) (k' : RecordKernelState) : Prop :=
  match op with
  | .mint _ d amt => d ∉ c.s.tl.draws ∧ amt ≤ R - c.s.tl.drawn ∧
      (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat + amt ∧
      (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat
  | .finalize amt => amt ≤ c.s.outstanding ∧
      (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat - amt ∧
      (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat
  | .reverse loss => loss ≤ c.s.outstanding ∧
      (k'.bal exposureCell asset).toNat = (k.bal exposureCell asset).toNat ∧
      (k'.bal settledCell asset).toNat = (k.bal settledCell asset).toNat + loss

/-- **`valid_kstep_preserves_refines`** — a valid kernel step preserves `Refines` (dispatches to the
three op simulations). -/
theorem valid_kstep_preserves_refines
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (c : MoneyInReserve) (k : RecordKernelState) (op : MIOp) (k' : RecordKernelState)
    (hR : Refines exposureCell settledCell asset R k c)
    (hv : ValidKernelStep exposureCell settledCell asset R c k op k') :
    Refines exposureCell settledCell asset R k' (miStep c op) := by
  cases op with
  | mint pi d amt => obtain ⟨hf, hw, he, hs⟩ := hv; exact mint_refines _ _ _ _ _ _ _ pi d amt hR hf hw he hs
  | finalize amt => obtain ⟨hw, he, hs⟩ := hv; exact finalize_refines _ _ _ _ _ _ _ amt hR hw he hs
  | reverse loss => obtain ⟨hw, he, hs⟩ := hv; exact reverse_refines _ _ _ _ _ _ _ loss hR hw he hs

/-- **`kernel_run_loss_bounded` — the closed loss-bound over the KERNEL's own dynamics.** For any
kernel run whose every step is a valid money-in step (from a reserve-shaped start), dregg's realized
loss (the settled cell balance) never exceeds the disclosed reserve R — `net ≥ −R` — at every
reachable kernel state, for ANY adversarial sequence of attested mints / finalizes / reverses. -/
theorem kernel_run_loss_bounded
    (exposureCell settledCell : CellId) (asset : AssetId) (R : Nat)
    (kt : Nat → RecordKernelState) (c₀ : MoneyInReserve) (m : MISched)
    (hR0 : Refines exposureCell settledCell asset R (kt 0) c₀)
    (hrun : ∀ n, ValidKernelStep exposureCell settledCell asset R (miTraj c₀ m n) (kt n) (m n) (kt (n + 1))) :
    ∀ n, ((kt n).bal settledCell asset).toNat ≤ R := by
  have hRn : ∀ n, Refines exposureCell settledCell asset R (kt n) (miTraj c₀ m n) := by
    intro n
    induction n with
    | zero => exact hR0
    | succ j ih =>
        have := valid_kstep_preserves_refines exposureCell settledCell asset R
          (miTraj c₀ m j) (kt j) (m j) (kt (j + 1)) ih (hrun j)
        exact this
  intro n; exact refines_loss_bounded exposureCell settledCell asset R (kt n) (miTraj c₀ m n) (hRn n)

/-! ## Non-vacuity: the projection is well-formed on a concrete reserve-shaped state. -/

#guard decide (mkReserve 100 40 20).ReserveWF

end Dregg2.Verify.StripeKernelRefine
