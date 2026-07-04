/-
# Dregg2.Verify.StripeAttest — the Stripe payment WITNESS as a WitnessedPredicate (K1).

The Stripe-payment attestation plugged into the proved `Authority.Predicate` registry seam.
A `Claim` (the bound payment facts) is discharged by a witness the registry ACCEPTS for the
Stripe kind — `stripe_attest_sound` is the K1 soundness-by-verification, composing the proved
`Authority.Predicate.registry_sound`.

The witness is a DECO zkTLS proof of Stripe's TLS-authenticated API. That verification is now a
CONSTRUCTED relation, not an opaque oracle: `Crypto/Deco.lean` models the DECO session-authentication
chain as an in-circuit relation (`DecoRelation`) and PROVES the both-directions bridge, so an accepting
proof PROVES the payment facts modulo the base §8 primitives (ed25519 EUF-CMA, HMAC unforgeability,
Poseidon2 CR, STARK extractability) and the external Web-PKI / honest-Stripe floor. `stripe_deco_attest_sound`
plugs that constructed verifier in at the Stripe kind: the registry-accept premise of `stripe_attest_sound`
is now the accepting bit of a proved-sound relation. The prover/`find` stays untrusted.

K1/K5 of `docs/STRIPE-KERNEL-BUILD-PLAN.md`; composes with `Apps.BridgeCell`'s proved finalize/cancel
lifecycle (the `witnessed(vk)` finality-gate IS this discharge).
-/
import Dregg2.Crypto.Deco

namespace Dregg2.Verify.StripeAttest

open Dregg2.Authority.Predicate
open Dregg2.Laws
open Dregg2.Crypto.Deco

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
the registered `Verify` (the DECO zkTLS check), the prover/`find` is untrusted. `stripe_deco_attest_sound`
below shows that registered check is now the CONSTRUCTED `DecoRelation`, not a bare oracle. -/
theorem stripe_attest_sound {Wit : Type} (reg : Registry Claim Wit) (vk : Nat)
    (claim : Claim) (wit : Wit)
    (haccept : registryVerify reg (stripeKind vk) claim wit = true) :
    @Discharged Claim Wit (verifiableOfRegistry reg (stripeKind vk)) claim wit :=
  registry_sound reg (stripeKind vk) claim wit haccept

/-! ## K5 — the CONSTRUCTED DECO verifier plugged in at the Stripe kind.

The payment `Claim` maps to the DECO disclosed statement under Stripe's Web-PKI-anchored server key; the
DECO §8 verify oracle is installed at `stripeKind vk`. An accepting DECO proof both discharges the claim
(K1) and proves the DECO relation binds the payment facts to a Stripe-authenticated transcript (K5). -/

/-- Map the payment `Claim` to the DECO disclosed payment facts (field-for-field). -/
def claimToFacts (c : Claim) : PaymentFacts :=
  { amountCents := c.amountCents, currency := c.currency,
    recipient := c.recipient, paymentIntentId := c.paymentIntentId }

/-- The DECO disclosed statement for a `Claim` under Stripe's Web-PKI-anchored server key (the trusted
registration parameter — WHICH TLS endpoint the proof must authenticate against). -/
def claimToStmt {Dg : Type} (serverKey : Dg) (c : Claim) : Statement Dg :=
  { serverKey := serverKey, facts := claimToFacts c }

/-- **The DECO-backed `Verifier` over `Claim`** — build the disclosed statement (fixed Stripe server key)
and run the DECO §8 verify oracle. This REPLACES the former toy verifier: the registered check is now the
CONSTRUCTED DECO zkTLS relation (`Crypto/Deco.lean`), sound modulo the §8 floor. -/
def decoClaimVerifier {Dg P : Type} [K : DecoVerifierKernel Dg P] (serverKey : Dg) : Verifier Claim P :=
  fun c proof => K.verify (claimToStmt serverKey c) proof

/-- The Stripe registry with the DECO verifier installed at `stripeKind vk`. -/
def stripeDecoReg {Dg P : Type} [DecoVerifierKernel Dg P] (vk : Nat) (serverKey : Dg)
    (base : Registry Claim P) : Registry Claim P :=
  fun j => if j = stripeKind vk then some (decoClaimVerifier serverKey) else base j

/-- **K5/K1 — `stripe_deco_attest_sound`.** With the CONSTRUCTED DECO verifier registered at the Stripe
kind, an accepting DECO proof both (1) discharges the payment `Claim` (K1, via `registry_sound`) and
(2) proves the DECO relation binds the payment facts to a Stripe-authenticated transcript (K5, via
`deco_verify_sound`). The registry-accept premise of `stripe_attest_sound` is now the accepting bit of a
proved-sound relation, not a bare oracle assumption. Trust base: `extractable` (STARK) + the §8 gate
carriers (`deco_binds_payment`: ed25519 EUF-CMA + HMAC + Poseidon2 CR) + the external Web-PKI/Stripe floor. -/
theorem stripe_deco_attest_sound {Dg P : Type} [K : DecoVerifierKernel Dg P]
    (vk : Nat) (serverKey : Dg) (base : Registry Claim P)
    (c : Claim) (proof : P) (hext : K.extractable)
    (haccept : K.verify (claimToStmt serverKey c) proof = true) :
    (@Discharged Claim P
        (verifiableOfRegistry (stripeDecoReg vk serverKey base) (stripeKind vk)) c proof)
      ∧ ∃ w : CircuitIR Dg,
          DecoRelation K.sigVerify K.macVerify K.compress K.encode (claimToStmt serverKey c) w := by
  refine ⟨?_, deco_verify_sound hext (claimToStmt serverKey c) proof haccept⟩
  apply registry_sound (stripeDecoReg vk serverKey base) (stripeKind vk) c proof
  show registryVerify (stripeDecoReg vk serverKey base) (stripeKind vk) c proof = true
  unfold registryVerify stripeDecoReg
  simp only [stripeKind, ↓reduceIte]
  exact haccept

/-! ## Non-vacuity: the DECO reference kernel discharges a real Stripe-shaped claim.

The DECO reference kernel (`Crypto/Deco.lean`) is a `def`, not a global instance (to avoid silent
auto-resolution); we make it a LOCAL instance here to witness the DECO-backed cascade over `Claim`. -/

attribute [local instance] Reference.refKernel

/-- A concrete claim: a $25.00 USD payment to cell 1, intent 999. -/
def sampleClaim : Claim := ⟨2500, 840, 1, 999⟩

/-- The empty base registry over the toy `ℤ`-keyed DECO kernel (`Unit` proofs). -/
def emptyBase : Registry Claim Unit := fun _ => none

/-- **`stripe_deco_cascade_nonvacuous`** — at the DECO reference kernel (server key 11), an accepting proof
both `Discharged`s `sampleClaim` at the Stripe kind AND proves the DECO relation binds its facts. A NAMED
witness so the axiom footprint is checkable — the constructed DECO verifier, fully lit at the Stripe kind. -/
theorem stripe_deco_cascade_nonvacuous :
    (@Discharged Claim Unit
        (verifiableOfRegistry (stripeDecoReg 42 (11 : Int) emptyBase) (stripeKind 42))
        sampleClaim ())
      ∧ ∃ w : CircuitIR Int,
          DecoRelation Reference.refKernel.sigVerify Reference.refKernel.macVerify
            Reference.refKernel.compress Reference.refKernel.encode
            (claimToStmt (11 : Int) sampleClaim) w :=
  stripe_deco_attest_sound 42 (11 : Int) emptyBase sampleClaim () trivial (by decide)

-- Non-vacuity axiom footprint: rests only on the standard kernel axioms.
#print axioms stripe_deco_cascade_nonvacuous

-- the DECO verifier accepts a valid attested claim, rejects a zero-amount (non-succeeded) claim, and the
-- registry fail-closes on the wrong kind:
#guard (decoClaimVerifier (11 : Int) sampleClaim ())
#guard (! decoClaimVerifier (11 : Int) (⟨0, 840, 1, 999⟩ : Claim) ())
#guard (! registryVerify (stripeDecoReg 42 (11 : Int) emptyBase) (.custom 8) sampleClaim ())

end Dregg2.Verify.StripeAttest
