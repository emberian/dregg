/-
# Dregg2.Verify.StripeBridge — the Stripe-attested bridge release (K2/K3 weld).

Welds the Stripe payment witness (`StripeAttest.stripe_attest_sound`) onto the proved abstract
gated-release primitive (`EscrowFactoryProbe.escrowReleaseGated`, §HARD-iii). The mint = a release
gated by the Stripe registry discharge; conservation, fail-closed, and the state-machine keystones
are inherited from §HARD-iii FOR ANY gate, and the discharge composes `stripe_attest_sound` to prove
a committed mint corresponds to a VERIFIED Stripe payment.

K2 (the attested transition) + K3 (the gated lifecycle) of docs/STRIPE-KERNEL-BUILD-PLAN.md.
The §8 crypto soundness of the witness (the DECO zkTLS proof) stays the CryptoKernel oracle.
-/
import Dregg2.Verify.StripeAttest
import Dregg2.Verify.EscrowFactoryProbe

namespace Dregg2.Verify.StripeBridge

open Dregg2.Exec
open Dregg2.Verify.EscrowFactoryProbe
open Dregg2.Verify.StripeAttest
open Dregg2.Authority.Predicate
open Dregg2.Laws

variable {Wit : Type}

/-- **The Stripe gate** — the abstract `Int→Int→Bool` release gate (§HARD-iii) realized by the Stripe
registry discharge: the condition slot `c` encodes the payment `Claim` (`encClaim`), the witness slot
`w` encodes the DECO proof (`encWit`), and the gate is the registry's accept bit. -/
def stripeGate (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim) (encWit : Int → Wit) :
    Int → Int → Bool :=
  fun w c => registryVerify reg (stripeKind vk) (encClaim c) (encWit w)

/-- **The Stripe-attested release (= the mint leg).** `escrowReleaseGated` at the Stripe gate. -/
def stripeAttestedRelease (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (witness : Int) : Option RecordKernelState :=
  escrowReleaseGated (stripeGate reg vk encClaim encWit) k e beneficiary asset witness

/-- **K2 — `stripe_release_conserves`.** A committed Stripe-attested release conserves every asset
(inherited from §HARD-iii `gated_release_conserves`, orthogonal to the discharge kind). -/
theorem stripe_release_conserves (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int}
    (h : stripeAttestedRelease reg vk encClaim encWit k e beneficiary asset witness = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b := by
  unfold stripeAttestedRelease at h
  exact gated_release_conserves _ h b

/-- **K2 — `stripe_release_requires_attestation` (fail-closed).** No accepted Stripe witness ⇒ no
mint. Inherited from §HARD-iii `gated_release_requires_discharge`. -/
theorem stripe_release_requires_attestation (reg : Registry Claim Wit) (vk : Nat)
    (encClaim : Int → Claim) (encWit : Int → Wit) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (witness : Int)
    (hbad : registryVerify reg (stripeKind vk) (encClaim (escrowCondition k e)) (encWit witness)
              = false) :
    stripeAttestedRelease reg vk encClaim encWit k e beneficiary asset witness = none := by
  unfold stripeAttestedRelease
  exact gated_release_requires_discharge _ k e beneficiary asset witness hbad

/-- **K1∘K2 — `stripe_release_discharges_claim` (the keystone): a committed mint corresponds to a
VERIFIED Stripe payment.** From a committed release the gate held, so the registry accepted the
witness for the encoded claim; `stripe_attest_sound` then discharges the payment `Claim`. -/
theorem stripe_release_discharges_claim (reg : Registry Claim Wit) (vk : Nat)
    (encClaim : Int → Claim) (encWit : Int → Wit) {k k' : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {witness : Int}
    (h : stripeAttestedRelease reg vk encClaim encWit k e beneficiary asset witness = some k') :
    @Discharged Claim Wit (verifiableOfRegistry reg (stripeKind vk))
      (encClaim (escrowCondition k e)) (encWit witness) := by
  unfold stripeAttestedRelease escrowReleaseGated at h
  by_cases hg : escrowState k e = sOpen ∧
      stripeGate reg vk encClaim encWit witness (escrowCondition k e) = true
  · exact stripe_attest_sound reg vk (encClaim (escrowCondition k e)) (encWit witness) hg.2
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## Non-vacuity: the Stripe gate accepts the matching attestation, rejects a wrong one. -/

private def encC : Int → Claim :=
  fun c => { amountCents := 0, currency := 0, recipient := 0, paymentIntentId := c.toNat }
private def encW : Int → Nat := fun w => w.toNat

#guard (stripeGate (refRegistry 7) 7 encC encW 99 99)     -- attestation binds pi=99 → accept (mint)
#guard (! stripeGate (refRegistry 7) 7 encC encW 88 99)   -- wrong witness → reject (no mint)
#guard (! stripeGate (refRegistry 8) 7 encC encW 99 99)   -- wrong kind/vk → fail-closed

end Dregg2.Verify.StripeBridge
