/-
# Dregg2.Verify.StripeLightClient — G1: the light client witnesses "this mint = a verified payment".

The weld that closes G1. `Circuit/Emit/EffectVmEmitBridgeMintDeco` publishes the bridge-mint's payment
commitment + minted value as PUBLIC INPUTS (the gated descriptor `decoBridgeMintVmDescriptor`, additive
over the deployed one). `Crypto/Deco` proves an accepting DECO/zkTLS proof authenticates a real Stripe
payment. This module JOINS them: a `satisfiedVm` witness of the gated descriptor, an accepted DECO proof,
and the verifier's anchor (the value PI = the DECO-disclosed amount) together force —

  the ledger credits EXACTLY the Stripe-attested, non-zero amount, published as a public input the light
  client reads, and there EXISTS an accepted DECO proof binding a Stripe-authenticated transcript whose
  commitment opens to exactly those disclosed facts.

So a pure light client, reading only the recursive aggregate's public inputs, witnesses that this mint IS
a verified Stripe payment — no access to the witness, no trust beyond the §8 floor + the external
Web-PKI/Stripe floor + the named PI anchor.

Trust base: STARK extractability + ed25519 EUF-CMA + HMAC + Poseidon2 CR (the §8 carriers of
`deco_authenticates_payment`) + the value-PI anchor (the honest verifier binds the published value to the
DECO-disclosed amount, the deployment analog of the record-pin family's anchors) + the external
Web-PKI/Stripe floor. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMintDeco
import Dregg2.Crypto.Deco

namespace Dregg2.Verify.StripeLightClient

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitBridgeMintDeco
open Dregg2.Crypto.Deco
open Dregg2.Crypto.PortalFloor

set_option autoImplicit false

/-- **`PaymentValueAnchored env facts`** — the deployed verifier ANCHORS the published value PI to the
DECO-disclosed amount (it recomputes the payment-value PI from the trusted DECO statement before
`verify_vm_descriptor`, exactly as the record-pin family anchors `dpis[38]` from the trusted post-cell).
NAMED, realizable (the honest verifier holds the DECO statement), the deployment analog of the turn/record
anchors. -/
def PaymentValueAnchored (env : VmRowEnv) (facts : PaymentFacts) : Prop :=
  env.pub PI_PAYMENT_VALUE = (facts.amountCents : ℤ)

/-- **`stripe_light_client_witnesses_payment` — G1.** With the gated bridge-mint descriptor satisfied on
the first row, an accepted DECO proof for `stmt`, and the verifier's value anchor, a pure light client
witnesses that this mint IS a verified Stripe payment:

  1. Stripe's server key genuinely signed the session key (ed25519 EUF-CMA), and the committed transcript
     opens to the encoding of exactly the disclosed facts (Poseidon2 CR) — a Stripe-authenticated payment;
  2. the trace's minted-value column equals the DECO-attested amount;
  3. that amount is strictly positive (the payment succeeded);
  4. the payment commitment is a PUBLIC INPUT (it flows into the recursive aggregate root the light client
     verifies).

Every hypothesis is a §8 carrier, the value anchor, or the coincidence of the DECO kernel's gates with the
§8 oracles. The conclusion is the light-client-witnessable "mint = verified payment". -/
theorem stripe_light_client_witnesses_payment {Proof : Type}
    [KD : DecoVerifierKernel ℤ Proof] [SK : SignatureKernel ℤ ℤ ℤ] [MK : MacKernelE ℤ ℤ ℤ]
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (stmt : Statement ℤ) (proof : Proof) (haccept : KD.verify stmt proof = true)
    (hash : List ℤ → ℤ) (env : VmRowEnv) (isLast : Bool)
    (hcirc : satisfiedVm hash decoBridgeMintVmDescriptor env true isLast)
    (hanchor : PaymentValueAnchored env stmt.facts) :
    (∃ w : CircuitIR ℤ,
        SK.Signed stmt.serverKey w.sessionKey
        ∧ w.transcriptCommit = KD.compress (KD.encode stmt.facts) w.salt)
    ∧ env.loc paymentValueCol = (stmt.facts.amountCents : ℤ)
    ∧ (0 : ℤ) < env.loc paymentValueCol
    ∧ env.loc paymentCommitCol = env.pub PI_PAYMENT_COMMIT := by
  -- (A) the DECO proof authenticates a Stripe payment (STARK + §8 carriers).
  obtain ⟨w, hSigned, _hTagged, hOpens, hAmt⟩ :=
    deco_authenticates_payment hsigEq hmacEq hext hsig hmac stmt proof haccept
  -- (B) the circuit publishes the payment commitment + value on the first row.
  obtain ⟨hPubCommit, hPubValue⟩ := decoBridgeMint_publishes hash env isLast hcirc
  -- (2) the minted-value column equals the attested amount: publish ∘ anchor.
  have hValEq : env.loc paymentValueCol = (stmt.facts.amountCents : ℤ) :=
    hPubValue.trans hanchor
  -- (3) the attested amount is positive.
  have hPos : (0 : ℤ) < env.loc paymentValueCol := by
    have h1 : (1 : ℤ) ≤ (stmt.facts.amountCents : ℤ) := by exact_mod_cast hAmt
    rw [hValEq]; omega
  exact ⟨⟨w, hSigned, hOpens⟩, hValEq, hPos, hPubCommit⟩

#assert_axioms stripe_light_client_witnesses_payment

/-! ## Non-vacuity: the whole G1 chain inhabited at the reference kernels + a canonical bridge-mint row.

The value anchor + the circuit witness are the deployment residuals; here we exhibit the DECO half end to
end at the reference kernels (over `ℤ`), so the G1 conclusion's DECO conjunct is non-vacuous. -/

/-- The DECO half of G1 is inhabited: at the reference kernels an accepting proof authenticates the sample
payment (Stripe signed the session, the commitment opens to the encoded facts). -/
theorem g1_deco_half_nonvacuous :
    ∃ w : CircuitIR ℤ,
      Reference.refSigKernel.Signed Reference.sampleStmt.serverKey w.sessionKey
      ∧ w.transcriptCommit
          = Reference.refKernel.compress (Reference.refKernel.encode Reference.sampleStmt.facts) w.salt := by
  obtain ⟨w, hS, _hT, hO, _hA⟩ :=
    deco_authenticates_payment (KD := Reference.refKernel) (SK := Reference.refSigKernel)
      (MK := Reference.refMacKernel) rfl rfl trivial (fun _ _ _ h => of_decide_eq_true h) trivial
      Reference.sampleStmt () (by decide)
  exact ⟨w, hS, hO⟩

#print axioms g1_deco_half_nonvacuous

end Dregg2.Verify.StripeLightClient
