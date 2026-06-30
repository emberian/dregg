/-
# Dregg2.Verify.StripeAttest — the Stripe payment WITNESS as a WitnessedPredicate (K1).

The Stripe-payment attestation plugged into the proved `Authority.Predicate` registry seam.
A `Claim` (the bound payment facts) is discharged by a witness the registry ACCEPTS for the
Stripe kind — `stripe_attest_sound` is the K1 soundness-by-verification, composing the proved
`Authority.Predicate.registry_sound`.

The witness itself is a DECO zkTLS proof of Stripe's TLS-authenticated API; its CRYPTO soundness
is the §8 `CryptoKernel.verify` oracle, NEVER a Lean law (per `Authority.Predicate`'s §8 portal).
This module models DISPATCH + soundness-by-verification only; the concrete DECO verifier (K5)
plugs in as the registered `Verifier` and is verified by the crypto oracle.

K1 of `docs/STRIPE-KERNEL-BUILD-PLAN.md`; composes with `Apps.BridgeCell`'s proved
finalize/cancel lifecycle (the `witnessed(vk)` finality-gate IS this discharge).
-/
import Dregg2.Authority.Predicate

namespace Dregg2.Verify.StripeAttest

open Dregg2.Authority.Predicate
open Dregg2.Laws

/-- **The Stripe payment CLAIM** — the bound facts a verified payment asserts, the *statement* the
witness must discharge. Faithful to `bridge/src/stripe_mirror.rs::StripePaymentAttestation`: amount
(cents), currency (ISO-4217 numeric code), recipient (the dregg cell id), and the payment-intent id
(the replay nonce / `payment_nullifier` seed). -/
structure Claim where
  amountCents : Nat
  currency : Nat
  recipient : Nat
  paymentIntentId : Nat
  deriving DecidableEq, Repr

/-- The Stripe witnessed-predicate kind: an app-registered, content-addressed verifier keyed by `vk`
(the DECO verification key). Uses the registry's open `custom` extension point. -/
def stripeKind (vk : Nat) : WitnessedKind := .custom vk

/-- **K1 — `stripe_attest_sound`.** A witness the registry ACCEPTS for the Stripe kind discharges the
payment claim. Soundness-by-verification, composing `Authority.Predicate.registry_sound`: the TCB is
the registered `Verify` (the DECO zkTLS check via the §8 oracle); the prover/`find` is untrusted. -/
theorem stripe_attest_sound {Wit : Type} (reg : Registry Claim Wit) (vk : Nat)
    (claim : Claim) (wit : Wit)
    (haccept : registryVerify reg (stripeKind vk) claim wit = true) :
    @Discharged Claim Wit (verifiableOfRegistry reg (stripeKind vk)) claim wit :=
  registry_sound reg (stripeKind vk) claim wit haccept

/-! ## Non-vacuity: a toy reference verifier (the DECO §8 oracle plugs in HERE later). -/

/-- A TOY reference verifier (placeholder for the DECO zkTLS §8 oracle): accepts `w : Nat` iff it
equals the claim's `paymentIntentId` (stand-in for "the proof binds this exact payment"). The REAL
verifier (K5) is the DECO check routed through `CryptoKernel.verify`. -/
def refVerifier : Verifier Claim Nat := fun c w => decide (w = c.paymentIntentId)

/-- A registry that installs the toy verifier under the Stripe kind at `vk`. -/
def refRegistry (vk : Nat) : Registry Claim Nat :=
  fun k => if k = stripeKind vk then some refVerifier else none

/-- The matching witness discharges the claim (K1 soundness, instantiated). -/
example (vk : Nat) (c : Claim)
    (h : registryVerify (refRegistry vk) (stripeKind vk) c c.paymentIntentId = true) :
    @Discharged Claim Nat (verifiableOfRegistry (refRegistry vk) (stripeKind vk)) c c.paymentIntentId :=
  stripe_attest_sound (refRegistry vk) vk c c.paymentIntentId h

-- the registry accepts the matching witness, rejects a wrong one, and fail-closes on the wrong kind:
#guard (registryVerify (refRegistry 7) (stripeKind 7) ⟨2500, 840, 1, 999⟩ 999)
#guard (! registryVerify (refRegistry 7) (stripeKind 7) ⟨2500, 840, 1, 999⟩ 123)
#guard (! registryVerify (refRegistry 7) (.custom 8) ⟨2500, 840, 1, 999⟩ 999)

end Dregg2.Verify.StripeAttest
