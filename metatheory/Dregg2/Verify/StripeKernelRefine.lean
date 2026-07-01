/-
# Dregg2.Verify.StripeKernelRefine — grounding the reserve in the KERNEL state (refinement, step 1).

The reserve apex + the money-in bridge live over the abstract Trustline `ChannelC` register model.
This module begins the forward-simulation refinement that grounds those registers in the real kernel
`RecordKernelState` cells (where `StripeBridgeV2`'s `Intent/Lifecycle` mint actually moves value).

Impedance: `ChannelC`/`Line` carry structural invariants (`holderAcct = drawn`, `issuerWell = −drawn`,
`escrow = ceiling − settled`, `draws.Nodup`) a `RecordKernelState` does not natively have. The
projection constructs a WELL-FORMED reserve from two kernel cell balances — the exposure cell (holding
`drawn`, the spent-provisional) and the settled cell (holding `settled`, the realized loss) — setting
the derived registers by construction, so well-formedness reduces to the two order facts
`drawn ≤ R ∧ settled ≤ drawn` (the "reserve-shaped" predicate on the kernel state).

STEP 1 (here): the projection + its well-formedness + the loss-bound instantiated FROM the kernel
projection — so a reserve-shaped kernel state is a valid starting point for `net ≥ −R`. STEP 2 (next):
the per-op simulation (a kernel mint/finalize/reverse on `RecordKernelState` maps to the money-in op
under the projection), transferring the bound to the kernel's OWN trajectory.
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

/-! ## Non-vacuity: the projection is well-formed on a concrete reserve-shaped state. -/

#guard decide (mkReserve 100 40 20).ReserveWF

end Dregg2.Verify.StripeKernelRefine
