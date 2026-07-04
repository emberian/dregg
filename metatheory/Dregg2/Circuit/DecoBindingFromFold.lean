/-
# Dregg2.Circuit.DecoBindingFromFold — the DEPLOYED Stripe/DECO money-in mint's PAYMENT backing,
  proven from the FOLD (the 8th carrier's flip: `DecoBackingAttack` → `DecoBindingFromFold`).

## Why this file exists (the flip)

`DecoBackingAttack` proved the deployed Stripe-mint's payment backing INVISIBLE to a pure light
client: the deployed row credits balance and publishes a `payment_hash` PI, but reads it in NO
constraint — a credit with no witnessed DECO/zkTLS attestation
(`deployed_admits_unbacked_deco`, `deployed_intent_does_not_force_backing`). The repair it named
(§B: "the backing must come from the per-turn FOLD over the re-proved DECO commitment leaf
connected to the published `payment_hash` PI") is the felt-domain `payment_hash` thread:

  * THE ANCHOR (`dregg_circuit::dsl::deco_payment::deco_payment_hash_felt`) — the FELT-domain
    identity `hash_fact(hash_fact(amountCents, [currency, recipient]), [paymentIntentId])`, NOT
    the executor's byte-domain BLAKE3 `payment_nullifier` (the exact mistake the attack catches).
  * THE LEAF (`circuit-prove::deco_leaf_adapter::prove_deco_leaf_with_claim`) — a Poseidon2-only
    commitment AIR that recomputes the identity IN-AIR from its PI-pinned PaymentFacts columns
    (gates 3/4/5 of `Deco.lean::DecoRelation`) and exposes it at lane 4; the leaf-level tooth
    (`forged_payment_hash_does_not_fold`) refuses a forged identity AT THE LEAF.
  * THE FOLD (`prove_deco_payment_binding_node_segmented`) — the in-circuit `connect` ties the
    leaf's exposed identity to the deployed leg's published `payment_hash` PI. ed25519/HMAC/
    SHA-256/Web-PKI/the DECO handshake/Stripe's schema stay OFF-AIR (the named §8 carriers,
    `Deco.lean::deco_binds_payment`), exactly bridge's posture (ed25519 + nullifier-set off-fold).

This module proves the REAL deployed guarantee from premises that HOLD for the deployed aggregate
— the DECO mirror of `BridgeBindingFromFold` (the universal sub-proof-folding primitive):

  * **`deco_binding_from_fold`** — a verifying AGGREGATE FORCES, for the leg's published identity
    `f.paymentHash`: (binding) ∃ a verifying DECO attestation `q` with `E.paymentDigest q =
    f.paymentHash`, AND (anti-double-mint linkage) the consumed paymentIntentId is DETERMINED by
    `f.paymentHash` — any two verifying attestations exposing the identity agree on their
    paymentIntentId (the identity is a Poseidon2 sponge of the payment tuple, CR ⇒ tuple-
    determined). Premises = {the FRI floor (`AggAirSound.FriExtract`), `Poseidon2SpongeCR`, the
    identity factoring, the connect}. No staged-AIR carrier, no DECO axiom.
  * **`backedAt_from_fold`** — the GROUNDING onto `DecoBackingAttack.BackedAt`: a satisfying fold
    connected to the leg's published `payment_hash` DISCHARGES the backing predicate the deployed
    AIR omits. ⚑ FRESHNESS STAYS EXECUTOR-SIDE: the ¬consumed half rides `hfresh` (the RE-EXEC
    `bridge_mint_against_lock` tooth over the committed `note_nullifiers`); `DecoBackingAttack`'s
    §C `deployed_admits_consumed_payment` STANDS. The fold ADDS the paymentIntentId LINKAGE.
  * **`deco_authenticates_from_fold`** — the GROUNDING onto `Deco.lean`: over the engine whose
    verifying proofs ARE `DecoRelation` witnesses, a satisfying fold's published identity is a
    GENUINE Stripe-authenticated payment (Stripe's key signed the session key, the transcript is
    MAC'd, it opens to the encoded non-zero facts) — via `deco_binds_payment` + the §8 carriers.

## Non-vacuity (BOTH polarities, mirroring the Rust leaf tooth)
`honest_companion_fires` — on an honest Stripe-mint turn the binding FIRES.
`forged_payment_hash_unsat_demo` — a fold whose published identity is the `DecoBackingAttack` §A
forgery (`forgedDecoMintRow`'s `payment_hash = 0`, backed by NO verifying attestation of
`demoDeco`) CANNOT satisfy: the aggregate is UNSAT.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
`DecoBackingAttack` STANDS beside it (the deployed-AIR facts remain true).
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.DecoBackingAttack

namespace Dregg2.Circuit.DecoBindingFromFold

open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DecoBackingAttack (DecoEngine BackedAt paymentHashOf demoDeco noneConsumed
  forgedDecoMintRow forged_not_backed)
open Dregg2.Crypto.Deco
open Dregg2.Crypto.PortalFloor

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the DECO-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`DecoLeafFriFloor E LeafSat`** — the localized FRI-extraction floor for the re-proved DECO
commitment leaf: a SATISFIED in-circuit DECO-leaf verifier (pinned VK core `leafVk`, exposing the
payment identity `leafIdentity` — the leaf's lane 4, the IN-AIR-recomputed `deco_payment_hash_felt`
over its own PI-pinned PaymentFacts) yields a GENUINELY VERIFYING DECO attestation of engine `E`
whose `paymentDigest` IS the exposed identity. The DECO instance of `AggAirSound.FriExtract` (one
child of one node), NOT a new dregg axiom — see `decoLeafFriFloor_of_aggFriExtract`. -/
def DecoLeafFriFloor (E : DecoEngine) (LeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafIdentity : ℤ, LeafSat leafVk leafIdentity →
    ∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = leafIdentity

/-- The DECO leaf's exposed segment projection: the leaf carries its payment-identity claim `x` in
the ordered-digest lane `acc`. -/
def segOfIdentity (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`decoLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** Given the
aggregation's per-child `FriExtract` over the DECO engine — pinned VK core constant `leafPre`, the
child exposing its payment-identity claim in `acc` — the DECO-leaf floor follows. -/
theorem decoLeafFriFloor_of_aggFriExtract
    (E : DecoEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfIdentity (E.paymentDigest q)) ChildVerifierSat) :
    DecoLeafFriFloor E
      (fun leafVk leafIdentity => ChildVerifierSat leafVk (segOfIdentity leafIdentity)) := by
  intro leafVk leafIdentity hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfIdentity leafIdentity) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfIdentity] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`DecoFold E`** — the per-turn fold's DECO face: the DECO-leaf's pinned preprocessed
commitment `leafVk` (its VK core), the payment-identity claim `leafIdentity` the leaf exposes
(lane 4), and the effect-vm leg's published payment identity `paymentHash` (the `withPaymentHashPin`
PI slot — the felt `deco_payment_hash_felt` the producer filled). -/
structure DecoFold (E : DecoEngine) where
  /-- the DECO-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk       : ℤ
  /-- the payment-identity claim the folded DECO leaf exposes (lane 4). -/
  leafIdentity : ℤ
  /-- the effect-vm leg's published felt payment identity (the pin carrier). -/
  paymentHash  : ℤ

/-- **`SatDecoFold E LeafSat f`** — a SATISFYING per-turn fold over its DECO face: `leafCV` (the
in-circuit DECO-leaf verifier subcircuit is satisfied) + `connect` (the aggregate's combine
constraint TIES the leaf's exposed identity to the leg's published identity —
`prove_deco_payment_binding_node_segmented`'s in-circuit connect). -/
structure SatDecoFold (E : DecoEngine) (LeafSat : ℤ → ℤ → Prop) (f : DecoFold E) : Prop where
  leafCV  : LeafSat f.leafVk f.leafIdentity
  connect : f.leafIdentity = f.paymentHash

/-! ## §3 — THE REPAIR: the deployed Stripe-mint backing, from the FOLD. -/

/-- **`deco_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn fold
including the re-proved DECO commitment leaf — FORCES, for the leg's published identity
`f.paymentHash`:

  (binding) ∃ a verifying DECO attestation `q` of `E` with `E.paymentDigest q = f.paymentHash`;
  AND (anti-double-mint linkage) the consumed paymentIntentId is DETERMINED by `f.paymentHash` —
  any two verifying attestations exposing the identity agree on their paymentIntentId.

The premise set is EXACTLY the `bridge_binding_from_fold` set: the FRI floor, `Poseidon2SpongeCR`,
and the identity FACTORING — the published digest of a verifying attestation is the sponge of its
payment tuple (`deco_payment_hash_felt`'s `hash_fact` chain over `(amountCents, currency,
recipient, paymentIntentId)`; `henc` recovers the paymentIntentId from the tuple encoding). A
forged identity with no backing attestation makes the aggregate UNSAT. -/
theorem deco_binding_from_fold
    (E : DecoEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop)
    (hfri : DecoLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.paymentDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q →
        E.paymentIntent p = E.paymentIntent q)
    (f : DecoFold E) (hsat : SatDecoFold E LeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = f.paymentHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.paymentDigest p = f.paymentHash → E.paymentDigest q = f.paymentHash →
        E.paymentIntent p = E.paymentIntent q) := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  have hhash : hash (enc p) = hash (enc q') := by
    rw [← hfactor p hp, ← hfactor q' hq', hpc, hq'c]
  exact henc p q' hp hq' (hCR _ _ hhash)

/-- **`backedAt_from_fold` — the GROUNDING onto `DecoBackingAttack.BackedAt`.** A satisfying fold
whose published identity is the row's (`hpub` — the `withPaymentHashPin` pin welds the PI to the
row's published `payment_hash`) DISCHARGES the (staged) backing predicate the deployed AIR omits:
the row IS `BackedAt`.

⚑ HONEST SCOPE — the ¬consumed half rides `hfresh`: the consume-once guard is the RE-EXEC tooth
(`bridge_mint_against_lock`'s atomic contains-then-insert over the committed `note_nullifiers`),
supplied HERE as "every attestation the engine still verifies is unconsumed" — the attack's §C
(`deployed_admits_consumed_payment`) STANDS; the fold's own freshness contribution is the
paymentIntentId LINKAGE (`deco_binding_from_fold`'s second half). -/
theorem backedAt_from_fold
    (E : DecoEngine) (LeafSat : ℤ → ℤ → Prop)
    (hfri : DecoLeafFriFloor E LeafSat)
    (consumed : ℤ → Prop)
    (hfresh : ∀ q : E.Proof, E.verify q = true → ¬ consumed (E.paymentIntent q))
    (f : DecoFold E) (hsat : SatDecoFold E LeafSat f)
    (row : Dregg2.Circuit.DecoBackingAttack.DecoMintRow)
    (hpub : f.paymentHash = paymentHashOf row) :
    BackedAt E consumed row := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect, hpub] at hqc
  exact ⟨q, hq, hqc, hfresh q hq⟩

/-! ## §3b — the GROUNDING onto `Dregg2.Crypto.Deco` — the fold authenticates the payment. -/

/-- The DECO engine whose verifying proofs ARE `DecoRelation` witnesses at a fixed disclosed
statement: `Proof` is a witness bundled with its relation proof, `verify` is always `true`
(the relation IS the FRI-extracted content), `paymentDigest`/`paymentIntent` are the caller's
felt projections of the witnessed facts. This is the concrete instance that ties the abstract fold
to `Deco.lean`. -/
def decoRelEngine {Digest : Type}
    [SK : SignatureKernel Digest Digest Digest] [MK : MacKernelE Digest Digest Digest]
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (stmt : Statement Digest)
    (identOf intentOf : CircuitIR Digest → ℤ) : DecoEngine where
  Proof := { w : CircuitIR Digest //
    DecoRelation SK.sigVerify MK.verifyTag compress encode stmt w }
  verify := fun _ => true
  paymentDigest := fun q => identOf q.1
  paymentIntent := fun q => intentOf q.1

/-- **`deco_authenticates_from_fold`** — over `decoRelEngine`, a SATISFYING per-turn fold forces a
GENUINE Stripe-authenticated payment for its published identity: Stripe's key signed the session
key (ed25519 EUF-CMA carrier), the response transcript was MAC'd under it (HMAC carrier), and the
committed transcript opens to the encoding of exactly the disclosed non-zero facts. The
light-client witness of `Deco.lean::deco_authenticates_payment`, delivered by the fold. The trust
base is exactly the named §8 carriers (`hsig`, `hmac`) — the ed25519/HMAC/SHA-256/Web-PKI floor. -/
theorem deco_authenticates_from_fold {Digest : Type}
    [SK : SignatureKernel Digest Digest Digest] [MK : MacKernelE Digest Digest Digest]
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (stmt : Statement Digest) (identOf intentOf : CircuitIR Digest → ℤ)
    (LeafSat : ℤ → ℤ → Prop)
    (hfri : DecoLeafFriFloor (decoRelEngine compress encode stmt identOf intentOf) LeafSat)
    (f : DecoFold (decoRelEngine compress encode stmt identOf intentOf))
    (hsat : SatDecoFold (decoRelEngine compress encode stmt identOf intentOf) LeafSat f) :
    ∃ w : CircuitIR Digest,
      SK.Signed stmt.serverKey w.sessionKey ∧
      MK.Tagged w.sessionKey w.transcriptCommit w.tag ∧
      w.transcriptCommit = compress (encode stmt.facts) w.salt ∧
      1 ≤ stmt.facts.amountCents := by
  obtain ⟨q, _hq, _hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  exact ⟨q.1, deco_binds_payment compress encode hsig hmac stmt q.1 q.2⟩

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest DECO attestation engine over the sponge: a payment is `(paymentIntent, rest)`, every
proof verifies, its digest is the sponge of the tuple, its paymentIntent the first lane — the
`honestSpend` shape at the `DecoEngine` signature. -/
def honestDeco (hash : List ℤ → ℤ) : DecoEngine where
  Proof := ℤ × ℤ
  verify := fun _ => true
  paymentDigest := fun p => hash [p.1, p.2]
  paymentIntent := fun p => p.1

/-- The honest DECO face over `honestDeco`: the folded leaf exposes the identity of the honest
payment `(7, 7)`, and the connect publishes that same identity as the leg's payment-hash PI. -/
def honestFold (hash : List ℤ → ℤ) : DecoFold (honestDeco hash) :=
  { leafVk := 100, leafIdentity := hash [7, 7], paymentHash := hash [7, 7] }

/-- The honest DECO-leaf verifier predicate: satisfied exactly when a backing verifying attestation
exposes the exposed identity claim. -/
def honestNLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafIdentity => ∃ q : ℤ × ℤ,
    (honestDeco hash).verify q = true ∧ (honestDeco hash).paymentDigest q = leafIdentity

theorem honestFloor (hash : List ℤ → ℤ) :
    DecoLeafFriFloor (honestDeco hash) (honestNLS hash) :=
  fun _leafVk _leafIdentity h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatDecoFold (honestDeco hash) (honestNLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest Stripe-mint turn the binding
FIRES: the published identity is BACKED by a verifying DECO attestation whose paymentIntentId is
uniquely determined by the identity — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (honestDeco hash).verify q = true ∧
        (honestDeco hash).paymentDigest q = (honestFold hash).paymentHash) ∧
    (∀ p q : ℤ × ℤ, (honestDeco hash).verify p = true → (honestDeco hash).verify q = true →
        (honestDeco hash).paymentDigest p = (honestFold hash).paymentHash →
        (honestDeco hash).paymentDigest q = (honestFold hash).paymentHash →
        (honestDeco hash).paymentIntent p = (honestDeco hash).paymentIntent q) :=
  deco_binding_from_fold (honestDeco hash) hash (fun p => [p.1, p.2]) (honestNLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by
      intro p q _ _ henc
      have h1 : p.1 = q.1 := by injection henc
      exact h1)
    (honestFold hash) (honestSat hash)

/-- **The honest fold DISCHARGES `BackedAt`** — the grounded close is itself non-vacuous: against
the fresh baseline (`noneConsumed`), the honest fold backs ANY row whose published `payment_hash`
is the honest identity. -/
theorem honest_backedAt (hash : List ℤ → ℤ)
    (row : Dregg2.Circuit.DecoBackingAttack.DecoMintRow)
    (hpub : (honestFold hash).paymentHash = paymentHashOf row) :
    BackedAt (honestDeco hash) noneConsumed row :=
  backedAt_from_fold (honestDeco hash) (honestNLS hash) (honestFloor hash)
    _ (fun _q _ h => h) (honestFold hash) (honestSat hash) row hpub

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged payment identity ⟹ UNSAT).** A per-turn fold
whose published identity `f.paymentHash` is backed by NO verifying DECO attestation CANNOT satisfy:
the fold re-verifies the leaf (`hfri`) and the connect ties its claim to `f.paymentHash`, so a
satisfying fold would PRODUCE a backing attestation — contradiction. The circuit twin of the Rust
`forged_payment_hash_does_not_fold`. -/
theorem forged_unsat {E : DecoEngine} {LeafSat : ℤ → ℤ → Prop}
    (hfri : DecoLeafFriFloor E LeafSat) {f : DecoFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = f.paymentHash) :
    ¬ SatDecoFold E LeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The DECO-leaf predicate over `demoDeco` (the only verifying attestation exposes digest `123`). -/
def demoNLS : ℤ → ℤ → Prop :=
  fun _leafVk leafIdentity =>
    ∃ q : Bool, demoDeco.verify q = true ∧ demoDeco.paymentDigest q = leafIdentity

theorem demoFloor : DecoLeafFriFloor demoDeco demoNLS :=
  fun _leafVk _leafIdentity h => h

/-- The `DecoBackingAttack` §A forgery lifted onto the fold: the published identity is
`forgedDecoMintRow`'s published `payment_hash` (= 0), which NO verifying attestation of `demoDeco`
exposes. -/
def forgedFold : DecoFold demoDeco :=
  { leafVk := 0, leafIdentity := paymentHashOf forgedDecoMintRow,
    paymentHash := paymentHashOf forgedDecoMintRow }

/-- **`forged_payment_hash_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the
fold).** The forged fold (published identity = the `deployed_admits_unbacked_deco` row's
`payment_hash = 0`, unbacked) does NOT satisfy: what the deployed AIR alone admitted, the aggregate
REFUSES. -/
theorem forged_payment_hash_unsat_demo : ¬ SatDecoFold demoDeco demoNLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, hq, hc⟩
  -- forgedFold.paymentHash = 0 (defeq); demoDeco.paymentDigest q = 123; 123 = 0 is false.
  have hc' : (123 : ℤ) = 0 := by
    simpa [forgedFold, paymentHashOf, forgedDecoMintRow, demoDeco] using hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms decoLeafFriFloor_of_aggFriExtract
#assert_axioms deco_binding_from_fold
#assert_axioms backedAt_from_fold
#assert_axioms deco_authenticates_from_fold
#assert_axioms honest_companion_fires
#assert_axioms honest_backedAt
#assert_axioms forged_unsat
#assert_axioms forged_payment_hash_unsat_demo

end Dregg2.Circuit.DecoBindingFromFold
