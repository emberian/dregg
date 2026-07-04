/-
# Dregg2.Circuit.DecoBackingAttack — ADVERSARIAL soundness audit of the deployed Stripe/DECO
  money-in mint's PAYMENT backing (the DECO analog of `BridgeBackingAttack`, the 8th carrier).

This module attacks the deployed `stripeMint`/`decoMint` member head-on, IN LEAN, importing
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

A Stripe money-in mint (`bridge/src/stripe_mirror.rs` → `Effect::Mint`) credits the recipient
cell by the verified `amount_cents` and publishes a `payment_hash` — the felt-domain identity
[`dregg_circuit::dsl::deco_payment::deco_payment_hash_felt`] binding the payment facts
(amountCents, currency, recipient, paymentIntentId). The OFF-AIR verifier
(`StripeWebhookEvent::verify`, HMAC-SHA256 over the raw body) authenticates the payment and
consumes the `payment_nullifier` (`bridge_ledger.rs::bridge_mint_against_lock`, the same
committed `note_nullifiers` set bridge rides) — but those checks live OUTSIDE the deployed
effect-vm AIR.

The deployed `stripeMint` descriptor gates ONLY the balance credit + frame freeze + nonce tick.
It has NO commitment-binding op and reads `payment_hash` in NONE of its constraints — so for a
PURE LIGHT CLIENT (one that only verifies the per-turn recursion tree) a Stripe mint credits
balance with NO witnessed payment backing. This is the SAME vacuity CLASS `BridgeBackingAttack`
proves for the inbound bridge mint: real as executor-verified, vacuous as deployed-light-client.

## Grounding

The `DecoEngine.paymentDigest` models the felt `payment_hash` a VERIFYING DECO/zkTLS attestation
exposes; `Dregg2.Crypto.Deco` proves such an attestation authenticates the payment
(`deco_authenticates_payment`, modulo the §8 carriers). This attack shows the deployed AIR ALONE
does not FORCE that a mint's published `payment_hash` is backed by any such attestation — the
repair (the backing from the per-turn FOLD over the re-proved DECO commitment leaf) is
`DecoBindingFromFold`.

## What is proved here

§A `deployed_admits_unbacked_deco` — an HONEST-looking Stripe-mint row that SATISFIES the deployed
   row intent (credit a positive amount) while its published `payment_hash` is backed by NO
   verifying DECO commitment.
§B `deployed_intent_does_not_force_backing` — no uniform "deployed-accepts ⟹ backed".
§C `deployed_admits_consumed_payment` — even a `payment_hash` a verifying attestation backs is
   accepted when the paymentIntentId is ALREADY consumed: the consume-once guard is the RE-EXEC
   tooth (`bridge_mint_against_lock`, atomic contains-then-insert on the committed
   `note_nullifiers`), NOT a light-client one.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new
axiom, NO `sorry`. NEW file; all imports read-only. The deployed `stripeMint` effect-vm EMIT
model (a Lean twin of `EffectVmEmitBridgeMint.goodBridgeMintRow`) rides the coordinated big-bang
descriptor regen; this attack states the omission over the abstract deployed row, upgradeable to
the concrete emit model when it lands (exactly as `BridgeBackingAttack` refined the bridge row).
-/
import Dregg2.Crypto.Deco

namespace Dregg2.Circuit.DecoBackingAttack

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the DECO attestation engine + the (staged) backing predicate.

A `DecoEngine` abstracts the DECO/zkTLS + Stripe-webhook attestation the off-AIR verifier runs:
`verify` is its accepting bit, `paymentDigest` is the felt `payment_hash` a VERIFYING attestation
exposes (the identity binding amountCents/currency/recipient/paymentIntentId), and `paymentIntent`
is the consume-once `paymentIntentId` (the replay nonce the executor dedups). The DECO analog of
`BridgeBackingAttack.NoteSpendEngine` (`verify` + `spendDigest` + `nullifier`). -/
structure DecoEngine where
  /-- The proof type of the DECO/zkTLS + Stripe attestation. -/
  Proof : Type
  /-- The verifier's accepting bit (`StripeWebhookEvent::verify` + the DECO proof check). -/
  verify : Proof → Bool
  /-- The felt `payment_hash` a VERIFYING attestation exposes (binds the payment facts). -/
  paymentDigest : Proof → ℤ
  /-- The paymentIntentId (the consume-once replay nonce the bridge ledger dedups). -/
  paymentIntent : Proof → ℤ

/-- The deployed Stripe-mint row a light client sees: the published felt `payment_hash` and the
credited amount. The effect-vm EMIT twin is the coordinated big-bang piece; this is the abstract
carrier of the published identity + the row intent. -/
structure DecoMintRow where
  /-- The felt payment identity the mint row publishes (the `withPaymentHashPin` PI). -/
  publishedPaymentHash : ℤ
  /-- The minted amount (the row's balance-credit intent, `Effect::Mint.amount`). -/
  creditAmount : ℤ

/-- The `payment_hash` a row publishes (the felt the off-AIR verifier checks the DECO attestation
against). -/
def paymentHashOf (row : DecoMintRow) : ℤ := row.publishedPaymentHash

/-- The deployed row intent the AIR DOES enforce: a positive balance credit (the Stripe mint's
`amount ≥ 1` — the money-in conservation gate `live_supply ≤ total_verified_payments` bounds the
credit, `stripe_mirror.rs:179`). The DECO analog of `BridgeMintRowIntent`. -/
def DecoMintRowIntent (row : DecoMintRow) : Prop := 1 ≤ row.creditAmount

/-- **`BackedAt E consumed row`** — the STAGED backing predicate the deployed descriptor SHOULD
(but does not) enforce: the row's published `payment_hash` is the digest of SOME verifying DECO
attestation whose paymentIntentId is NOT already consumed. The content the deployed AIR omits (the
DECO analog of `BridgeBackingAttack.BackedAt`). -/
def BackedAt (E : DecoEngine) (consumed : ℤ → Prop) (row : DecoMintRow) : Prop :=
  ∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = paymentHashOf row ∧ ¬ consumed (E.paymentIntent q)

/-! ## §A — the forged Stripe mint: deployed-accepts what the backing predicate rejects. -/

/-- A demo DECO attestation engine: the only verifying proof (`true`) exposes payment-digest `123`
and paymentIntentId `7` (the one-verifying-proof shape `BridgeBackingAttack.demoSpend` uses). -/
def demoDeco : DecoEngine where
  Proof := Bool
  verify := fun b => b
  paymentDigest := fun _ => 123
  paymentIntent := fun _ => 7

/-- No paymentIntentId is consumed (the honest fresh-mint baseline). -/
def noneConsumed : ℤ → Prop := fun _ => False

/-- The forged Stripe-mint row: published `payment_hash = 0` (a digest NO verifying attestation of
`demoDeco` exposes) while crediting `500` cents. -/
def forgedDecoMintRow : DecoMintRow := { publishedPaymentHash := 0, creditAmount := 500 }

/-- **The deployed descriptor ACCEPTS the forged row** — it realizes the deployed row intent
(a positive credit). -/
theorem forged_deployed_accepts : DecoMintRowIntent forgedDecoMintRow := by
  norm_num [DecoMintRowIntent, forgedDecoMintRow]

/-- **The forged row is REJECTED by the (staged) backing predicate.** Its `payment_hash` is `0`;
the only verifying attestation of `demoDeco` exposes `123`, so no verifying attestation backs it.
The deployed descriptor cannot detect this: it never reads `payment_hash`. -/
theorem forged_not_backed : ¬ BackedAt demoDeco noneConsumed forgedDecoMintRow := by
  rintro ⟨q, _hv, hd, _hfresh⟩
  simp only [demoDeco, forgedDecoMintRow, paymentHashOf] at hd
  exact absurd hd (by decide)

/-- **§A keystone — `deployed_admits_unbacked_deco`.** ∃ a DECO engine and a Stripe-mint row that
SATISFIES the deployed descriptor's row intent (a positive credit) yet whose published
`payment_hash` is backed by NO verifying DECO attestation: the deployed AIR admits a Stripe mint
whose payment backing does not verify — the explicit forged mint a pure light client cannot detect
(the DECO analog of `BridgeBackingAttack.deployed_admits_unbacked_bridge`). -/
theorem deployed_admits_unbacked_deco :
    ∃ (E : DecoEngine) (consumed : ℤ → Prop) (row : DecoMintRow),
      DecoMintRowIntent row ∧ ¬ BackedAt E consumed row :=
  ⟨demoDeco, noneConsumed, forgedDecoMintRow, forged_deployed_accepts, forged_not_backed⟩

/-! ## §B — the deployed Stripe-mint AIR does not force the backing. -/

/-- **§B keystone — `deployed_intent_does_not_force_backing`.** There is NO uniform "deployed
Stripe-mint row intent ⟹ the payment is backed": §A is the counterexample. So a light client that
only checks the deployed AIR learns NOTHING about the DECO/Stripe attestation. The real backing
must come from the per-turn FOLD over the re-proved DECO commitment leaf
(`circuit-prove::deco_leaf_adapter`) connected to the published `payment_hash` PI — see
`DecoBindingFromFold`. -/
theorem deployed_intent_does_not_force_backing :
    ¬ ∀ (E : DecoEngine) (consumed : ℤ → Prop) (row : DecoMintRow),
        DecoMintRowIntent row → BackedAt E consumed row := by
  intro hall
  exact forged_not_backed (hall demoDeco noneConsumed forgedDecoMintRow forged_deployed_accepts)

/-! ## §C — the consumed-payment corollary + the repair pointer. -/

/-- A row whose published `payment_hash` IS the verifying attestation's digest `123` (so the digest
binds) — crediting `500`. -/
def goodDigestRow : DecoMintRow := { publishedPaymentHash := 123, creditAmount := 500 }

/-- The paymentIntentId `7` (the demo attestation's replay nonce) is already consumed. -/
def sevenConsumed : ℤ → Prop := fun x => x = 7

/-- **`deployed_admits_consumed_payment`.** Even a row whose published `payment_hash` a verifying
attestation backs (digest `123`) is accepted by the deployed descriptor when the attestation's
paymentIntentId `7` is already consumed: the deployed AIR does not witness the consume-once guard
(the RE-EXEC `bridge_mint_against_lock` tooth over the committed `note_nullifiers`). -/
theorem deployed_admits_consumed_payment :
    DecoMintRowIntent goodDigestRow ∧ ¬ BackedAt demoDeco sevenConsumed goodDigestRow := by
  refine ⟨by norm_num [DecoMintRowIntent, goodDigestRow], ?_⟩
  rintro ⟨q, _hv, _hd, hfresh⟩
  exact hfresh rfl

/-! ## §D — Axiom audit — every load-bearing arm. -/

#assert_axioms forged_deployed_accepts
#assert_axioms forged_not_backed
#assert_axioms deployed_admits_unbacked_deco
#assert_axioms deployed_intent_does_not_force_backing
#assert_axioms deployed_admits_consumed_payment

end Dregg2.Circuit.DecoBackingAttack
