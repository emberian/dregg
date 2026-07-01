/-
# Dregg2.Verify.StripeBridgeV2 — the Stripe witness gating the PROVISIONAL MINT (K2/K3 re-weld).

The v1 `Verify/StripeBridge.lean` welded the Stripe attestation onto an escrow *release*
(`escrowReleaseGated`) — releasing pre-escrowed funds silently assumes the money is already
in hand, so it is the WRONG primitive for "money-in". Per the reserve design (theorem 17,
`docs/STRIPE-RESERVE-DESIGN-AND-PROOF-STRATEGY.md §2.2`), the chosen model is
**mint-against-backing**: the attestation gates the *admission of a provisional batch*
(liveness — recognizing a payment), never its *finality* (soundness).

This module re-targets the K2/K3 weld from the escrow release onto the **provisional-mint step**
of the intent-escrow lifecycle. The mint-provisional IS `Intent.Lifecycle.publish` (a real
verified, conserving publisher→escrow lock into a provisional cell), GATED by the K1 discharge
`StripeAttest.stripe_attest_sound`. The provisional credit then resolves EXACTLY ONCE — `fulfill`
(finalize) XOR `refund` (reverse) — by the lifecycle's one-shot teeth.

Anchors reused verbatim (NOT re-proved here):
  * K1 — `StripeAttest.stripe_attest_sound` — an accepted witness discharges the payment `Claim`.
  * `Intent.Lifecycle.publish` / `publish_conserves` / `publish_locks_exactly` — mint-provisional.
  * `Intent.Lifecycle.fulfilled_then_no_refund` / `refunded_then_no_fulfill` — finalize XOR reverse.

The mint anchor is the `Intent/Lifecycle.publish`-gated-by-attestation model (the dregg-native
"book the obligation as a real conserved balance" shape): `publish_conserves` carries conservation
and the one-shot teeth carry exactly-once. The §8 zkTLS crypto stays the `CryptoKernel` oracle
(the opaque witness routed through the registered verifier), NEVER a Lean law.

Creates ONE new file; edits nothing else. K2 (attested transition) + K3 (gated lifecycle),
re-welded onto the provisional mint per theorem 17.
-/
import Dregg2.Verify.StripeAttest
import Dregg2.Intent.Lifecycle

namespace Dregg2.Verify.StripeBridgeV2

open Dregg2.Exec (RecordKernelState AssetId recTotalAsset)
open Dregg2.Intent.Lifecycle
open Dregg2.Verify.StripeAttest
open Dregg2.Authority.Predicate
open Dregg2.Laws

variable {Wit : Type}

/-! ## §1 — The attest-gated provisional MINT (the primitive, for ANY gate).

The mint-provisional is the lifecycle `publish` leg — a verified, conserving publisher→escrow
lock of `c.amount` into the provisional escrow cell — GATED by an abstract decidable discharge
`g : Int → Int → Bool` ("does the witness discharge the encoded payment claim?"). Setting
`g := stripeGate` recovers the Stripe-attested mint (§2). The gate sits at exactly ONE position;
conservation and the one-shot teeth are ORTHOGONAL to which discharge realizes it. -/

/-- **`provisionalMintGated g c k condition witness`** — admit the provisional batch `c` (a
`publish` into the provisional escrow) IFF the gate `g` discharges the encoded claim. Fail-closed:
no discharge ⇒ `none`, and the credit is never minted. -/
def provisionalMintGated (g : Int → Int → Bool) (c : Contract) (k : RecordKernelState)
    (condition witness : Int) : Option RecordKernelState :=
  if g witness condition = true then publish c k else none

/-- **`gated_mint_conserves` — a committed provisional mint CONSERVES every asset, for ANY gate.**
The mint is a `publish` leg, so the per-asset move law `publish_conserves` applies verbatim: the
backing is a real move (publisher debited, escrow credited), nothing minted on the hard column. -/
theorem gated_mint_conserves (g : Int → Int → Bool) (c : Contract) (k : RecordKernelState)
    {k' : RecordKernelState} {condition witness : Int}
    (h : provisionalMintGated g c k condition witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold provisionalMintGated at h
  by_cases hg : g witness condition = true
  · rw [if_pos hg] at h; exact publish_conserves c k k' h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`gated_mint_requires_discharge` — no discharge ⇒ NO mint (fail-closed), for ANY gate.** -/
theorem gated_mint_requires_discharge (g : Int → Int → Bool) (c : Contract) (k : RecordKernelState)
    (condition witness : Int) (hbad : g witness condition = false) :
    provisionalMintGated g c k condition witness = none := by
  unfold provisionalMintGated
  rw [if_neg (by simp [hbad])]

/-! ## §2 — The Stripe instantiation: the K1 discharge is the gate.

`stripeGate` is the abstract `Int→Int→Bool` gate realized by the Stripe registry discharge: the
condition slot `c` encodes the payment `Claim` (`encClaim`), the witness slot `w` encodes the DECO
proof (`encWit`), and the gate is the registry's accept bit. Kept in the same shape as the v1
`StripeBridge.stripeGate`; only the gated primitive changed (release → provisional mint). -/

/-- **The Stripe gate** — the registry accept bit at the Stripe kind `vk`. -/
def stripeGate (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim) (encWit : Int → Wit) :
    Int → Int → Bool :=
  fun w c => registryVerify reg (stripeKind vk) (encClaim c) (encWit w)

/-- **The Stripe-attested provisional mint (= the mint leg).** `provisionalMintGated` at the
Stripe gate: a mint of `c.amount` provisional units into the provisional escrow, admissible IFF the
registry accepts the DECO witness for the encoded payment claim. -/
def stripeProvisionalMint (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) (k : RecordKernelState) (condition witness : Int) :
    Option RecordKernelState :=
  provisionalMintGated (stripeGate reg vk encClaim encWit) c k condition witness

/-- **K2 — `stripe_mint_admits_conserves`.** A committed provisional mint conserves every asset's
total supply (inherited from `gated_mint_conserves`; the backing is a real move, the provisional
supply is the disclosed boundary tracked outside the conserved column). -/
theorem stripe_mint_admits_conserves (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) (k : RecordKernelState) {k' : RecordKernelState}
    {condition witness : Int}
    (h : stripeProvisionalMint reg vk encClaim encWit c k condition witness = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b := by
  unfold stripeProvisionalMint at h
  exact gated_mint_conserves (stripeGate reg vk encClaim encWit) c k h b

/-- **K2 — `stripe_mint_requires_attestation` (fail-closed).** No accepted Stripe witness for the
encoded claim ⇒ NO provisional mint. Inherited from `gated_mint_requires_discharge`. -/
theorem stripe_mint_requires_attestation (reg : Registry Claim Wit) (vk : Nat)
    (encClaim : Int → Claim) (encWit : Int → Wit) (c : Contract) (k : RecordKernelState)
    (condition witness : Int)
    (hbad : registryVerify reg (stripeKind vk) (encClaim condition) (encWit witness) = false) :
    stripeProvisionalMint reg vk encClaim encWit c k condition witness = none := by
  unfold stripeProvisionalMint
  exact gated_mint_requires_discharge (stripeGate reg vk encClaim encWit) c k condition witness hbad

/-! ## §3 — A committed mint corresponds to a VERIFIED (but non-final) attestation, and is PROVISIONAL. -/

/-- From a committed mint, the gate held: the registry accepted the witness for the encoded claim. -/
theorem stripe_mint_gate_held (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) (k : RecordKernelState) {k' : RecordKernelState}
    {condition witness : Int}
    (h : stripeProvisionalMint reg vk encClaim encWit c k condition witness = some k') :
    registryVerify reg (stripeKind vk) (encClaim condition) (encWit witness) = true := by
  unfold stripeProvisionalMint provisionalMintGated at h
  by_cases hg : stripeGate reg vk encClaim encWit witness condition = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **K1∘K2 — a committed mint DISCHARGES the payment claim.** The gate held, so the registry
accepted the witness; `stripe_attest_sound` then discharges the `Claim`. Soundness-by-verification:
the TCB is the registered DECO verifier via the §8 oracle; no *finality* is claimed. -/
theorem stripe_mint_discharges_claim (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) (k : RecordKernelState) {k' : RecordKernelState}
    {condition witness : Int}
    (h : stripeProvisionalMint reg vk encClaim encWit c k condition witness = some k') :
    @Discharged Claim Wit (verifiableOfRegistry reg (stripeKind vk))
      (encClaim condition) (encWit witness) :=
  stripe_attest_sound reg vk (encClaim condition) (encWit witness)
    (stripe_mint_gate_held reg vk encClaim encWit c k h)

/-- A committed mint is a committed `publish` leg (the gate held; the lock ran on the real ledger). -/
theorem stripe_mint_commits_publish (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) (k : RecordKernelState) {k' : RecordKernelState}
    {condition witness : Int}
    (h : stripeProvisionalMint reg vk encClaim encWit c k condition witness = some k') :
    publish c k = some k' := by
  unfold stripeProvisionalMint provisionalMintGated at h
  by_cases hg : stripeGate reg vk encClaim encWit witness condition = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **K3 — `stripe_mint_is_provisional`.** A committed mint (from a FRESH provisional cell, funded
`amount > 0`) corresponds to a **verified but non-final** Stripe attestation, and the minted credit
enters the **provisional** state — LOCKED in the escrow cell, resolvable ONLY via finalize XOR
reverse (never a free/finalized balance). Concretely, the conjunction:

  1. the attestation discharges the payment `Claim` (K1∘K2 — verified, NOT final);
  2. the escrow cell holds EXACTLY the funded `amount` (locked-provisional, not free);
  3. once finalized (`fulfill`) it can no longer be reversed (`refund = none`);
  4. once reversed (`refund`) it can no longer be finalized (`fulfill = none`).

(3)+(4) are the lifecycle one-shot teeth: finality is the window closing without a reversal
(`fulfill`), and the two fates are mutually exclusive — provisional, exactly once. -/
theorem stripe_mint_is_provisional (reg : Registry Claim Wit) (vk : Nat) (encClaim : Int → Claim)
    (encWit : Int → Wit) (c : Contract) {k k' : RecordKernelState} {condition witness : Int}
    (h : stripeProvisionalMint reg vk encClaim encWit c k condition witness = some k')
    (hne : c.publisher ≠ c.escrow) (hfresh : k.bal c.escrow c.asset = 0) (hpos : 0 < c.amount) :
    (@Discharged Claim Wit (verifiableOfRegistry reg (stripeKind vk))
       (encClaim condition) (encWit witness))
    ∧ k'.bal c.escrow c.asset = c.amount
    ∧ (∀ k'', fulfill c k' = some k'' → refund c k'' = none)
    ∧ (∀ k'', refund c k' = some k'' → fulfill c k'' = none) := by
  have hpub : publish c k = some k' :=
    stripe_mint_commits_publish reg vk encClaim encWit c k h
  have hlock : k'.bal c.escrow c.asset = k.bal c.escrow c.asset + c.amount :=
    publish_locks_exactly c k k' hpub hne
  have hfunded : k'.bal c.escrow c.asset = c.amount := by rw [hlock, hfresh]; omega
  refine ⟨stripe_mint_discharges_claim reg vk encClaim encWit c k h, hfunded, ?_, ?_⟩
  · intro k'' hf
    exact fulfilled_then_no_refund c k' k'' hfunded hpos hf
  · intro k'' hr
    exact refunded_then_no_fulfill c k' k'' hfunded hpos hr

/-! ## §4 — NON-VACUITY: attestation present ⇒ mint admits + conserves + locks; absent ⇒ refused.

Built on the lifecycle demo world (`demoState`: publisher cell 1 holds 100; escrow cell 2 fresh;
`demoContract`: 1 →40→ escrow 2) and the K1 toy registry (`refRegistry`; the DECO §8 oracle plugs in
HERE later). The toy verifier accepts `w` iff it equals the claim's `paymentIntentId`. -/

/-- A toy claim encoder: the condition slot IS the payment-intent id (other facts 0). -/
def encC : Int → Claim :=
  fun c => { amountCents := 0, currency := 0, recipient := 0, paymentIntentId := c.toNat }
/-- A toy witness encoder (the DECO proof value carried as a `Nat`). -/
def encW : Int → Nat := fun w => w.toNat

/-- A concrete provisional mint over the demo ledger/contract at the toy Stripe registry (vk 7),
supplying `witness` against the encoded claim `condition`. -/
def demoMint (witness condition : Int) : Option RecordKernelState :=
  stripeProvisionalMint (refRegistry 7) 7 encC encW demoContract demoState condition witness

-- ATTESTATION PRESENT (witness 99 discharges the encoded claim 99) ⇒ the mint ADMITS:
#guard (demoMint 99 99).isSome
-- ...and CONSERVES asset-0 total supply (publish moves the backing, mints nothing on the hard column):
#guard ((demoMint 99 99).map (fun s => recTotalAsset s 0)) == some (recTotalAsset demoState 0)
-- ...and the minted credit is LOCKED-PROVISIONAL: the escrow cell (2) holds EXACTLY the funded 40:
#guard ((demoMint 99 99).map (fun s => s.bal 2 0)) == some 40
-- ATTESTATION ABSENT (wrong witness 88 ≠ claim 99) ⇒ the mint is REFUSED (fail-closed, no credit):
#guard (! (demoMint 88 99).isSome)
-- WRONG kind/vk (registry installed under vk 8, queried at vk 7) ⇒ fail-closed:
#guard (! (stripeProvisionalMint (refRegistry 8) 7 encC encW demoContract demoState 99 99).isSome)

/-- Non-vacuity at the PROOF level: on the demo world an attested mint's escrow cell (2) ends
holding exactly the funded `40` — the provisional locked state, read off `stripe_mint_is_provisional`. -/
example : ∀ k', demoMint 99 99 = some k' → k'.bal 2 0 = 40 := by
  intro k' h
  have hp := stripe_mint_is_provisional (refRegistry 7) 7 encC encW demoContract
    (k := demoState) (k' := k') (condition := 99) (witness := 99) h
    (by decide) (by decide) (by decide)
  simpa [demoContract] using hp.2.1

/-! ## §5 — Axiom hygiene: the re-weld is pinned to the kernel triple (via the reused organs). -/

#assert_axioms stripe_mint_admits_conserves
#assert_axioms stripe_mint_requires_attestation
#assert_axioms stripe_mint_is_provisional

end Dregg2.Verify.StripeBridgeV2
