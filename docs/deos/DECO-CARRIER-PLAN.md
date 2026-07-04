# The DECO Carrier — making the Stripe/zkTLS money-in crown light-client-live

**Status: BUILT** (Option B, the recommended path) — the carrier's own layer is live and its
tooth bites; the ONE deployed-descriptor emit rides the coordinated big-bang regen (by design,
§2 finale — "it does not fire independently"). What landed:

- **Step 1a — the felt anchor:** `dregg_circuit::dsl::deco_payment::deco_payment_hash_felt` =
  `hash_fact(hash_fact(amountCents, [currency, recipient]), [paymentIntentId])` + the byte-domain
  `stripe_payment_hash_felt` projector (the bridge `note_spend_mint_hash_felt`/`bridge_mint_hash_felt`
  twins). ⚑ FELT-domain, NOT the executor byte-domain BLAKE3 `payment_nullifier` (the anti-vacuity law).
- **Steps 3/4 — the DECO commitment leaf:** `circuit-prove::deco_leaf_adapter` — a Poseidon2-only
  IR-v2 leaf recomputing the identity IN-AIR from PI-pinned PaymentFacts (gates 3/4/5 of
  `Deco.lean::DecoRelation`), exposing `payment_hash` at claim lane 4. **Teeth bite (real recursion,
  green):** honest → foldable leaf + exposed claim; forged `payment_hash` → constraint #4 UNSAT;
  forged amount → constraint #0 UNSAT. Plus `prove_deco_payment_binding_node_segmented` (deployed
  connect) + `prove_deco_binding_node`; **fold-connect tooth bites:** honest identity connects+proves,
  mismatched identity → UNSAT.
- **Step 2 — the socket:** `CarrierWitness::Deco(DecoWitnessBundle)` + `from_retained_deco`
  (fail-closed off-wire).
- **Step 5 — the fold arm:** the `Deco` arm in `prove_chain_core_rotated` (`DECO_PAYMENT_HASH_PI`,
  fail-closed admission — a Stripe `Effect::Mint` leg with no payment-hash pin is REFUSED until the
  descriptor regen lands).
- **Step 5 — the Lean floor:** `Dregg2.Circuit.DecoBackingAttack` + `Dregg2.Circuit.DecoBindingFromFold`
  (`deco_binding_from_fold`, `backedAt_from_fold`, `deco_authenticates_from_fold` grounding onto
  `Deco.lean::deco_binds_payment`; non-vacuous both poles; `forged_payment_hash_unsat_demo`). Both
  `#assert_axioms`-clean ⊆ {propext, Classical.choice, Quot.sound}. `DecoBackingAttack` STANDS.
- **The named big-bang remainder (Step 1 deployed emit):** the deployed `stripeMint` descriptor
  `withPaymentHashPin` + the `generate_rotated_stripe_mint_wide` producer + the TSV regen ride the
  ONE coordinated descriptor big-bang (§2 finale, shared with every other carrier's regen), NOT a
  solo VK flip. Until it lands the fold arm is fail-closed. Drift PASS (no descriptor moved yet).
- **Terminal §8 carriers (off-AIR, executor-checked):** ed25519 EUF-CMA (Stripe's Web-PKI TLS key),
  HMAC-SHA256 (webhook + transcript MAC), SHA-256, the DECO 3-party handshake, Web-PKI, Stripe's
  `encode` schema, and the standard STARK/FRI + Poseidon2-CR floor — all named, identical to bridge.

**Ground:** repo `/Users/ember/dev/breadstuffs` @ `d459bd7c7` (HEAD at authoring).
**Provenance:** PR23-A metabolized the DECO/Stripe *verification* onto HEAD (commit
`f35b930fe`). It is **PROVEN but NOT DEPLOYED as a carrier** — no `CarrierWitness` arm
folds a DECO leaf. This doc scopes the forward work: fold DECO into the light client so a
ledgerless verifier witnesses a Stripe-backed mint instead of trusting it.

The DECO carrier is the **fiat twin of the bridge carrier**. Bridge folds a foreign
note-spend STARK re-proven in-AIR and connects its recomputed `mint_hash` to the deployed
mint row's PI (`BridgeBindingFromFold.lean`, `note_spend_leaf_adapter.rs`, the
`CarrierWitness::Bridge` arm at `ivc_turn_chain.rs:3114`). DECO folds a **DECO/TLS
attestation of a Stripe payment** in the same shape: a re-proven leaf exposing a
commitment, connected to a deployed `stripeMint` row's tail PI, with the heavy TLS crypto
handled exactly as bridge handles its ed25519/nullifier legs.

---

## 0. What exists today (the two halves, grounded)

**The Lean verification crown (proven, off-carrier):**

- `metatheory/Dregg2/Crypto/Deco.lean` — `DecoRelation` (Deco.lean:103), a 4-link
  session-auth chain + amount range gadget: (1) `sigVerify serverKey sessionKey sig`
  (ed25519 EUF-CMA), (2) `macVerify sessionKey transcriptCommit tag` (HMAC), (3)
  `transcriptCommit = compress fieldsDigest salt` (Poseidon2 CR opening), (4)
  `fieldsDigest = encode facts` (schema), (5) `1 ≤ amountCents` (range). Capstone
  `deco_authenticates_payment` (Deco.lean:315). `#assert_axioms`-clean ⊆ {propext,
  Classical.choice, Quot.sound}. `PaymentFacts{amountCents, currency, recipient,
  paymentIntentId}` at Deco.lean:48.
- `metatheory/Dregg2/Verify/StripeReserve.lean` — the reserve solvency apex:
  `stripe_money_in_loss_bounded` (StripeReserve.lean:58), `minted ≤ reserve` forever,
  a symbol-binding instance of the Trustline `ChannelC`.
- `metatheory/Dregg2/Verify/StripeMoneyIn.lean` — the end-to-end money-in bridge:
  `MIOp.toSOp` (mint↦draw, finalize↦repay, reverse↦settle, StripeMoneyIn.lean:42),
  `stripe_money_in_loss_bounded_e2e` (StripeMoneyIn.lean:77), `mintAuthorized` gate
  (StripeMoneyIn.lean:97) tying a mint to `stripe_attest_sound`.

**The Rust money-in mechanism (real, trusted-oracle, NOT light-client-witnessed):**

- `bridge/src/stripe_mirror.rs` — the deployed Stripe mirror. `StripeWebhookEvent::verify`
  is HMAC-SHA256 over `"{t}.{body}"` (stripe_mirror.rs:42-47, using the `hmac`/`sha2`
  crates OFF-circuit). Produces `Effect::Mint`. The **double-mint gate already exists**:
  `payment_nullifier(asset, payment_intent_id) = H(domain ‖ asset ‖ payment_intent_id)`
  (stripe_mirror.rs:73), consumed against the executor's committed `note_nullifiers` set.
- `turn/src/executor/bridge_ledger.rs` — `bridge_mint_against_lock` (bridge_ledger.rs:261),
  the **atomic contains-then-insert** on the committed `note_nullifiers` set
  (bridge_ledger.rs:294) — the SAME set `Effect::NoteSpend`/`Effect::BridgeMint` ride. The
  Stripe payment nullifier is already routed through it.
- The conservation invariant `live_supply ≤ total_verified_payments` is a LIVE gate in
  `StripeMirrorState.mint_against_payment` (stripe_mirror.rs:179-235) — the Rust twin of
  `StripeReserve.stripe_money_in_loss_bounded`.

**The gap:** the executor verifies the HMAC-SHA256 webhook and the conservation/nullifier
gates, but **a pure light client sees none of it** — it reads only the mint proof, which
today (like the pre-repair bridge) does not bind the payment facts to the mint. The DECO
carrier closes exactly this gap, at the aggregate/fold level, mirroring
`BridgeBindingFromFold`.

---

## 1. THE CRUX — which of DecoRelation's gates can be verified IN-AIR

To fold DECO into the light client, some form of DECO's soundness must be an in-AIR
foldable IR2 leaf. `DecoRelation` needs five gate families. Grounded gadget census:

| DecoRelation gate | Primitive | In-AIR gadget at HEAD? |
|---|---|---|
| (1) `sigVerify serverKey sessionKey sig` | ed25519 over Curve25519 | **NO ed25519 AIR.** The one in-AIR curve-signature verifier is **Schnorr over BabyBear^8** (`circuit/src/schnorr_curve.rs`, prime-order 248-bit curve, ~124-bit) driven by `circuit/src/turn_auth_signature_air.rs`. Deployed turn-auth ed25519 is verified **off-circuit** (`turn_auth_signature_air.rs:8`) — the Ed25519↔Schnorr scale obligation is a **named terminal seam** (`turn_auth_signature_air.rs:25-31`). |
| (2) `macVerify sessionKey transcriptCommit tag` | HMAC-SHA256 | **NO HMAC AIR. NO SHA-256 AIR.** (`sha256` in `effect_vm_descriptors.rs` is a build-time cache-freshness pin on TSV files, not a circuit gadget.) |
| (3) `transcriptCommit = compress fieldsDigest salt` | Poseidon2 compression | **YES.** Poseidon2 is the system's native in-AIR hash (`circuit/src/faithful8.rs`, `note_spending_air.rs`, `poseidon2::hash_fact`), the `hash_fact`/`TID_P2` chip the note-spend leaf already uses (`note_spend_leaf_adapter.rs:107,168`). |
| (4) `fieldsDigest = encode facts` | Poseidon2 sponge over the felt-encoded facts | **YES** (same Poseidon2 chip) — *if* `encode` is a Poseidon2 sponge of the felt-decomposed PaymentFacts rather than Stripe's raw JSON/byte schema. |
| (5) `1 ≤ amountCents` | range gadget | **YES.** `Exec/RecordCircuit.range` in Lean; the general range/comparison gadget exists in-AIR (`lean_descriptor_air.rs`, `effect_vm/vault_weld.rs`). DecoRelation already rides it seam-free (Deco.lean:150-164). |

Additionally the "byte/JSON parser extracting PaymentFacts" the PR body names has **no AIR
gadget** — parsing raw TLS records/JSON in-circuit is a bespoke build.

**Bottom line: gates (3), (4), (5) are in-AIR-ready today with the existing Poseidon2 +
range chips. Gates (1) ed25519, (2) HMAC-SHA256, and the byte/JSON parser are NOT — they
are the exact set the PR body flagged as "§8 carriers, not constructed."**

### Option A — Full-in-AIR DECO leaf

Build SHA-256 AIR, HMAC-SHA256 AIR (= two SHA-256 blocks + key padding), an ed25519
verification AIR (Edwards-curve point decompression + scalar-mul, *or* discharge the
Ed25519↔Schnorr scale obligation named at `turn_auth_signature_air.rs:25`), and a TLS
record / JSON byte-parser AIR, then verify **all five** DecoRelation gates in a single
foldable leaf. The light client would then witness the entire zkTLS session
authentication with zero off-circuit trust beyond Web-PKI and the DECO handshake.

- **Soundness ceiling:** highest. Only Web-PKI + the DECO 3-party handshake stay terminal.
- **Cost:** SHA-256 AIR alone is thousands of constrained rows per block; HMAC is two
  compressions; ed25519 is a full foreign-curve scalar-mul AIR (BabyBear^8 Schnorr is
  ~124-bit and the *wrong curve* — the deployed anchor is Curve25519, so a real ed25519
  AIR is required, not the existing Schnorr). A byte/JSON parser AIR is bespoke. **None of
  these gadgets exist in the tree.** This is 4 new heavy AIRs.
- **Verdict:** a genuine **multi-epoch build** — bigger than any carrier shipped this
  session and bigger than a v-epoch. It also does NOT match the discipline the rest of the
  system uses for foreign signatures: bridge keeps ed25519 **off-AIR + executor-checked**
  (`BridgeBindingFromFold.lean:56-63`, freshness stays executor-side); sovereign names
  in-AIR Ed25519 as its *terminal* route (`WELD-STATE.md:632`). Building an ed25519/SHA-256
  AIR here would be doing the single highest-cost thing the whole carrier program has so
  far deliberately deferred, for one carrier.

### Option B — Bridge-style commitment-fold DECO leaf (RECOMMENDED)

Mirror the bridge carrier exactly. The heavy TLS crypto — gates (1) ed25519, (2)
HMAC-SHA256, and the byte/JSON parse — is verified **OFF-circuit, executor-side** (it
already is: `StripeWebhookEvent::verify` HMAC-SHA256, stripe_mirror.rs:42), with its
soundness carried as **named §8 carriers** (ed25519 EUF-CMA + HMAC unforgeability + the
Web-PKI/schema floor — exactly the base already surfaced in `deco_binds_payment`,
Deco.lean:228). The **in-AIR foldable leaf verifies only the Poseidon2 commitment binding**
gates (3)+(4)+(5): the leaf recomputes, in-AIR, `fieldsDigest = Poseidon2-sponge(facts)`,
`transcriptCommit = compress(fieldsDigest, salt)`, and the amount range, and exposes a
**felt-domain payment identity** `payment_hash = hash_fact(...)` over the PaymentFacts
tuple `(amountCents, currency, recipient, paymentIntentId)`. The deployed `stripeMint` row
pins that same felt at a tail PI; the fold's `connect` makes a published payment identity
that no verified DECO commitment backs UNSAT.

- **What the light client witnesses:** "a DECO/zkTLS attestation committing to *these*
  PaymentFacts was verified, and the mint published exactly this payment identity" — the
  facts→commitment→mint binding is in-circuit; the TLS session-auth soundness is a named
  carrier. This is precisely bridge's posture: bridge folds the note-spend
  (key-knowledge + Merkle-membership + commitment) in-AIR and keeps the
  nullifier-consume/freshness executor-side (`BridgeBindingFromFold.lean:56`,
  `backedAt_from_fold` at :200, "¬consumed half rides `hfresh`").
- **Soundness ceiling:** the DecoRelation crown ALREADY factors this way. `deco_binds_payment`
  (Deco.lean:228) treats gates (1)/(2) as `SK.unforgeable`/`MK.unforgeable` **carriers** and
  proves gates (3)/(4) as the CR-bound opening. Option B is the *deployment* of the exact
  trust factoring Deco.lean already proved. `deco_commitment_binds` (Deco.lean:249) is the
  in-AIR-checkable half; `deco_authenticates_payment`'s ed25519/HMAC hypotheses are the
  off-AIR carriers.
- **Cost:** one Poseidon2-commitment leaf adapter (reuses the `hash_fact`/`TID_P2` chip
  machinery `note_spend_leaf_adapter.rs` already builds) + one deployed `stripeMint`
  descriptor tail-PI pin + one `CarrierWitness::Deco` arm. **Bridge-sized.**
- **Verdict: RECOMMENDED.** It is faithful to the system's uniform carrier discipline, it
  is the deployment of a trust factoring already *proven* in Deco.lean, and it reuses the
  bridge/custom leaf+node adapters wholesale. The terminal floor it names (ed25519/HMAC/
  SHA-256/Web-PKI) is honest and identical to what the executor already relies on and to
  what sovereign/bridge already name as terminal.

**Recommendation: Option B.** Option A is a separate, later, deliberately-gated epoch (the
in-AIR ed25519+SHA-256+HMAC family), justified only if/when the whole system decides to
retire off-AIR signature verification — a decision far larger than the DECO carrier, and
shared with sovereign's terminal route (`WELD-STATE.md:632`). Build B now; A can later
*strengthen* the same carrier by swapping the off-AIR carriers for in-AIR gadgets without
changing the fold shape.

---

## 2. The recommended build — the uniform 5-step carrier recipe, DECO-instantiated

Following `docs/WELD-STATE.md` §6 (WELD-STATE.md:541) and the bridge precedent term-for-term.

### Step 1 — teeth-emit + THE THIRD EDGE (the deployed `stripeMint` descriptor)

A new deployed `stripeMint`/`decoMint` descriptor, twin of `mintV3BridgeHash`
(`EffectVmEmitRotationV3.lean`, keystone `withMintHashPin_publishes`). It publishes the
**felt-domain payment identity** at a TAIL PI via `withMintHashPin`-shaped
`PiBinding{First}` on the mint row's `param0` (`param::MINT_HASH = 0`,
`circuit/src/effect_vm/columns.rs:500`; the bridge pin rides `PARAM_BASE + param::MINT_HASH`
at PI 46, `ivc_turn_chain.rs:2865`, `:3123`).

**THE THIRD EDGE (fail-open law):** the connect alone is vacuous. The emitted payment-
identity PI must be tied in-AIR to the descriptor's FAITHFUL committed anchor. The mint
row's `param0` must carry the executor-derived payment identity
`payment_hash = hash_fact(hash_fact(amountCents, [currency, recipient]), [paymentIntentId])`
(shape mirrors `note_spend_mint_hash_felt`, `note_spend_leaf_adapter.rs:154-168`), and the
producer (`effect_vm/trace_rotated.rs`, the `BridgeMint` arm's twin) fills it from the
executor's `VerifiedPayment` (stripe_mirror.rs:85). **⚑ Anti-vacuity, decisive for DECO:**
the anchor must be the FAITHFUL felt-domain payment identity, NOT the executor's
byte-domain BLAKE3 `payment_nullifier` (stripe_mirror.rs:73) — that is the exact mistake
`BridgeBackingAttack` caught for bridge (a BLAKE3 byte-domain fold "a circuit could not
recompute", `BridgeBindingFromFold.lean:8-12`). The felt-domain `payment_hash` must be
Poseidon2 over the PaymentFacts felts, recomputable in-AIR by the leaf.

Blast radius: bump only this descriptor's `public_input_count`; append at TAIL
`[DECO_PAYMENT_HASH_PI..]`; never touch the shared `[0..46)` prefix (WELD-STATE.md:564).

### Step 2 — the witness socket (`CarrierWitness::Deco`)

Add a `Deco(DecoWitnessBundle)` variant to the `CarrierWitness` enum
(`joint_turn_aggregation.rs:150`), mirroring `Bridge(BridgeWitnessBundle)`
(joint_turn_aggregation.rs:163,253). The bundle carries:

```
pub struct DecoWitnessBundle {
    payment_facts: PaymentFacts,   // amountCents, currency, recipient, paymentIntentId
    salt: BabyBear,                // the transcript-commitment opening blinding
    public_inputs: Vec<BabyBear>,  // the claim tuple: the felt facts + payment_hash
}
```

Plus `carrier_name()` → `"deco"` (joint_turn_aggregation.rs:196) and the **production
projection** `from_retained_deco(retained: Option<&VerifiedPayment>) -> Option<Self>`,
the fail-closed off-wire twin of `BridgeWitnessBundle::from_retained_bridge`
(joint_turn_aggregation.rs:283): the turn-build path RETAINS the `VerifiedPayment` the
webhook verify produced (stripe_mirror.rs, `StripeMirrorState::verify_payment`); a
wire-rehydrated turn retains nothing (`None`) → the re-exec rung, FAIL-CLOSED not
fabricated. ONE shared restructure of `joint_turn_aggregation.rs` (clobber hazard —
main-loop owned).

### Step 3/4 — the leaf + connect (a new `deco_leaf_adapter.rs`)

A new-file adapter `circuit-prove/src/deco_leaf_adapter.rs`, structurally the
`note_spend_leaf_adapter.rs` shape but with a **Poseidon2-commitment AIR** instead of the
note-spend STARK. Functions (mirroring note_spend_leaf_adapter.rs:462,543,768):

- `deco_leaf_public_inputs(facts, salt) -> Vec<BabyBear>` — the claim tuple
  `[amountCents, currency, recipient, paymentIntentId, fieldsDigest, transcriptCommit,
  payment_hash]`, with `payment_hash` at a fixed claim lane (twin of
  `NOTE_SPEND_MINT_HASH_PI = 6`, note_spend_leaf_adapter.rs:132).
- `prove_deco_leaf_with_claim(bundle, config)` — proves the in-AIR commitment leaf: a trace
  that (a) recomputes `fieldsDigest = Poseidon2-sponge(facts felts)` (gate 4), (b)
  recomputes `transcriptCommit = compress(fieldsDigest, salt)` (gate 3), (c) the amount
  range gadget `1 ≤ amountCents` (gate 5, `range`), (d) recomputes and exposes
  `payment_hash` at its claim lane — all via the `gated_fact_site`/`TID_P2` chip pattern
  (note_spend_leaf_adapter.rs:196). Passing a mismatched claim tuple is UNSAT (the
  leaf-level tooth, note_spend_leaf_adapter.rs:530).
- `prove_deco_payment_binding_node_segmented(dual, leaf, config)` — the segment-preserving
  binding node, twin of `prove_note_spend_mint_binding_node_segmented`
  (note_spend_leaf_adapter.rs:768), whose in-AIR `connect` ties the leaf's exposed
  `payment_hash` to the leg's published payment-identity PI.

Reuse is near-total: the leaf is a Poseidon2-only circuit (gates 3/4/5), strictly *simpler*
than the note-spend leaf (no Merkle membership, no spending-key knowledge). Zero new hash
mechanism — the `hash_fact`/`TID_P2` chip is exactly what note-spend already uses.

### Step 5 — wire + tooth + the positive floor

- **Wire:** add the `Some(CarrierWitness::Deco(bundle))` arm to
  `prove_chain_core_rotated` (ivc_turn_chain.rs, beside the Bridge arm at :3114). The arm:
  (1) `carrier_claim_pins_admitted(descriptor, pis, DECO_PAYMENT_HASH_PI, 1, "deco",
  Some((PARAM_BASE + param::MINT_HASH, VmRow::First)))` — fail-closed on a pin-less or
  wrong-column descriptor (twin of ivc_turn_chain.rs:3117); (2)
  `prove_descriptor_leaf_dual_expose_at(..., DECO_PAYMENT_HASH_PI, 1)`; (3)
  `prove_deco_leaf_with_claim(bundle, config)`; (4)
  `prove_deco_payment_binding_node_segmented(dual, leaf, config)`. THE shared edit of
  `ivc_turn_chain.rs` (clobber hazard). Add `DECO_PAYMENT_HASH_PI` / `DECO_CLAIM_LEN`
  consts beside the bridge ones (ivc_turn_chain.rs:2865).
- **Tooth:** a `circuit-prove/tests/deco_binding_deployed_tooth.rs`, twin of
  `bridge_binding_deployed_tooth.rs`, exercising honest / forged-payment-identity poles on
  the native committed `stripeMint` row + the regen-tie geometry + the paymentIntentId
  linkage.
- **Positive floor (Lean):** a new
  `metatheory/Dregg2/Circuit/DecoBindingFromFold.lean`, term-for-term twin of
  `BridgeBindingFromFold.lean`. `DecoFold`/`SatDecoFold` (mirror BridgeFold at :134,
  SatBridgeFold at :146). `deco_binding_from_fold` (mirror :167): a verifying aggregate
  FORCES, for the leg's published `payment_hash`, (binding) ∃ a verified DECO commitment
  with `commitDigest = payment_hash`, AND (anti-double-mint linkage) the consumed
  **paymentIntentId is DETERMINED by `payment_hash`** — any two verifying attestations
  exposing the identity agree on their paymentIntentId (Poseidon2 CR ⇒ tuple-determined),
  the exact anti-double-mint half bridge proves for the nullifier. `backedAt_from_fold`
  twin grounding onto the attack predicate, with the **freshness half riding `hfresh`**:
  the consume-once guard is the executor's `bridge_mint_against_lock` atomic
  contains-then-insert on `note_nullifiers` (bridge_ledger.rs:294) — the fold ADDS the
  linkage (which paymentIntentId was minted against), so the executor's set-uniqueness
  ranges over a light-client-visible key. Plus a **BackingAttack** (mirror
  `BridgeBackingAttack`) + `honest_companion_fires` / `forged_unsat` non-vacuity both
  polarities, all `#assert_axioms`-clean.

### The finale (shared with the carrier program, NOT DECO-specific)

The Step-1 descriptor regen + emit + ONE apex re-verify (`lightclient_unfoolable` + the 5
AssuranceCase guarantees clean under the new VK) + the gated flip. DECO's descriptor rides
the same coordinated one-shot as the other carriers' regens (WELD-STATE.md:557); it does
not fire independently.

---

## 3. The descriptor + PI layout (geometry / VK cost)

- **New PIs:** ONE tail felt — `DECO_PAYMENT_HASH_PI` (`DECO_CLAIM_LEN = 1`), the felt-
  domain payment identity, exactly like `BRIDGE_MINT_HASH_CLAIM_LEN = 1`
  (ivc_turn_chain.rs:2867). The full PaymentFacts tuple (amountCents, currency, recipient,
  paymentIntentId — 4 fields, each 1 felt if <2^31, else 2 felts for amount/id split) is
  carried in the **claim tuple of the leaf's own PIs**, not the deployed-leg PIs. ONE lane
  binds the whole tuple: the payment identity is the leaf's in-AIR `hash_fact` chain over
  its own PI-pinned facts, exactly bridge's "ONE lane binds the whole spend tuple"
  (ivc_turn_chain.rs:2862). So the deployed descriptor grows by **one PI**.
- **VK-affecting:** yes — a new `stripeMint` descriptor with a bumped
  `public_input_count` regenerates that descriptor's VK. Per WELD-STATE.md:564 the blast
  radius is per-descriptor: append at TAIL, never touch `[0..46)`, the descriptor touches
  only {its bare + wide + welded variants} + 3 registry fingerprints. It rides the ONE
  coordinated big-bang regen with the other carriers, not a solo VK flip.
- **Geometry:** no pre-limb / `B_SPAN` widening. Unlike factory/sovereign/membership (whose
  third edges need a geometry widening because the faithful anchor does not exist —
  WELD-STATE.md:599,625,636), DECO's faithful anchor is a felt the executor *computes and
  writes to the mint row's param0* (like bridge's mint_hash) — no new committed limb is
  needed. This makes DECO a **SHALLOW carrier** in the WELD-STATE depth ranking (tie to an
  existing writable committed slot), NOT a deepest new binding.

---

## 4. Money-in semantics (fiat → dregg mint)

- **The mint ties to reserve solvency:** the deployed `stripeMint` effect IS a gated
  `Effect::Mint` (stripe_mirror.rs:9,46), and the reserve bound is the LIVE conservation
  gate `live_supply ≤ total_verified_payments` (stripe_mirror.rs:179). The Lean apex
  `stripe_money_in_loss_bounded` (StripeReserve.lean:58) and its e2e form
  (StripeMoneyIn.lean:77) prove `settled ≤ R` for ANY adversarial mint/finalize/reverse
  schedule. The DECO carrier does not change the reserve math — it makes the *mint's
  authorization* (that this mint corresponds to a real attested payment) light-client-
  visible. `mintAuthorized`/`authorized_mint_discharges_payment` (StripeMoneyIn.lean:97,103)
  is the executor-side gate; the fold is its light-client witness.
- **Executor's role:** verify the Stripe webhook (HMAC-SHA256, stripe_mirror.rs:42),
  produce the `VerifiedPayment` (stripe_mirror.rs:85), consume the `payment_nullifier`
  against `note_nullifiers` (bridge_ledger.rs:294), check conservation
  (stripe_mirror.rs:179), apply the `Effect::Mint`, and RETAIN the `VerifiedPayment` for
  the fold projection (`from_retained_deco`).
- **Light-client's role:** witness the fold — the `stripeMint` leg's proof verifies, its
  published `payment_hash` PI is backed by a re-proven in-AIR DECO commitment leaf, and the
  paymentIntentId is uniquely determined by `payment_hash` (the anti-double-mint linkage).
  It does NOT re-verify the TLS session (that is the named carrier).
- **Double-mint / replay:** **already solved and reused.** The Stripe `payment_nullifier =
  H(domain ‖ asset ‖ paymentIntentId)` (stripe_mirror.rs:73) rides the SAME committed
  `note_nullifiers` set as bridge (bridge_ledger.rs:24,294), with the same atomic
  contains-then-insert double-mint prevention (bridge_ledger.rs:226). The DECO carrier's
  contribution is the **linkage**: the fold pins WHICH paymentIntentId the mint was against
  (the anti-double-mint half of `deco_binding_from_fold`), so the executor's set-uniqueness
  ranges over a light-client-visible key — exactly bridge's freshness posture
  (`BridgeBindingFromFold.lean:56-63`). Freshness itself STAYS executor-side (the honest
  scope), identical to bridge.

---

## 5. The terminal floor (named honestly)

**Genuinely terminal for the RECOMMENDED Option B (carried as §8 carriers, off-AIR):**

- **ed25519 EUF-CMA** (Stripe's Web-PKI-anchored TLS server key signs the session key) —
  gate (1). Off-circuit, exactly as deployed turn-auth ed25519 (turn_auth_signature_air.rs:8)
  and bridge's ed25519 leg. `SK.unforgeable` in `deco_binds_payment` (Deco.lean:229).
- **HMAC (SHA-256) unforgeability** (the transcript MAC / the Stripe webhook signature) —
  gate (2). Off-circuit (stripe_mirror.rs:42). `MK.unforgeable` (Deco.lean:229).
- **SHA-256** (TLS record hashing + the HMAC compression) — no AIR; folded into the HMAC
  carrier off-circuit.
- **Web-PKI** — the honest-endpoint assumption: `serverKey` IS Stripe's genuine
  Web-PKI-anchored TLS key. A **trusted registration parameter** (Deco.lean:60,467), the
  `custom vk` the DECO kind registers under (Deco.lean:354). This is real and terminal:
  dregg trusts that the disclosed `serverKey` authenticates the genuine Stripe endpoint
  (stripe_mirror.rs:29, "Stripe is the payment oracle").
- **The DECO 3-party-handshake trust** — the zkTLS protocol's assumption that the prover
  cannot forge the verifier's view of the session (the standard DECO/TLSNotary trust model).
  Terminal by protocol design.
- **Stripe's `encode` schema** — that `encode` is genuinely Stripe's response field
  encoding (Deco.lean:28,278). A registration parameter, terminal.
- **STARK/FRI extractability + Poseidon2-CR** — the standard crypto carriers under every
  dregg fold (`AggAirSound`, `Poseidon2SpongeCR`), shared with bridge and identical.

**Buildable-as-AIR (would move from terminal → in-circuit under the later Option A epoch):**

- SHA-256 AIR, HMAC-SHA256 AIR, ed25519 verification AIR (or the Ed25519↔Schnorr scale
  discharge, `turn_auth_signature_air.rs:25`), and the TLS/JSON byte-parser AIR. These are
  the "§8 carriers, not constructed." They are buildable but are a separate multi-epoch
  program shared with sovereign's in-AIR-Ed25519 terminal route (WELD-STATE.md:632). NOT
  DECO-specific and NOT on the recommended path.

**NOT terminal (in-circuit under the recommended Option B):** the facts→fieldsDigest
encoding (gate 4), the transcript-commitment opening (gate 3), the amount range (gate 5),
the payment-identity recomputation, and the connect to the deployed mint PI — all in-AIR in
the DECO commitment leaf.

---

## 6. Size estimate

**Bridge-sized carrier (Option B) — the SHALLOW class.** Concretely:

- **Smaller than bridge in the leaf**, because the DECO commitment leaf is Poseidon2-only
  (gates 3/4/5) — no Merkle membership, no spending-key knowledge, no 28-limb note preimage.
  It reuses the `hash_fact`/`TID_P2` chip + `range` gadget that already exist; the leaf
  adapter is a *simplification* of `note_spend_leaf_adapter.rs`.
- **Equal to bridge in the plumbing:** one `CarrierWitness::Deco` variant + projection
  (Step 2), one deployed descriptor tail-PI pin twinning `mintV3BridgeHash` (Step 1), one
  fold arm twinning the Bridge arm (Step 5 wire), one deployed tooth, one
  `DecoBindingFromFold.lean` + BackingAttack (Step 5 floor).
- **NO geometry/pre-limb widening** (unlike factory/sovereign/membership) — the faithful
  anchor is an executor-written mint-row felt, so DECO is a shallow "tie to an existing
  writable committed slot" carrier, the cheapest depth class.
- **The money-in half is already built:** the reserve conservation, the paymentIntentId
  double-mint gate, and the `Effect::Mint` production all exist in Rust
  (stripe_mirror.rs, bridge_ledger.rs) and are proven in Lean (StripeReserve/StripeMoneyIn).
  The carrier work is purely the **light-client witness of the facts→mint binding.**

**NOT a v-epoch-scale build, and explicitly NOT the TLS-gadgets build.** The one thing that
WOULD make it bigger — verifying the ed25519/HMAC/SHA-256/JSON-parse in-AIR (Option A) — is
deliberately kept off the recommended path and named as a later, system-wide, ember-gated
epoch shared with sovereign.

**Recommended order:** build the DECO commitment leaf + `DecoBindingFromFold.lean` first
(new files, no shared-tree churn, exercises the Poseidon2-commitment-leaf pattern), then
the witness socket (Step 2, shared-file, main-loop-owned), then the descriptor pin + fold
arm + tooth (Steps 1/5), then flip the refutation to the positive floor. The descriptor
regen rides the coordinated one-shot big-bang, not a solo flip.

---

## Appendix — the mirror table (bridge → DECO)

| Bridge (built) | DECO (to build) |
|---|---|
| `note_spend_leaf_adapter.rs` (note-spend STARK leaf) | `deco_leaf_adapter.rs` (Poseidon2 commitment leaf) |
| `note_spend_mint_hash_felt` (note_spend_leaf_adapter.rs:154) | `payment_hash` = `hash_fact` over PaymentFacts |
| `BridgeWitnessBundle` (joint_turn_aggregation.rs:253) | `DecoWitnessBundle` (payment_facts, salt, pis) |
| `from_retained_bridge` (joint_turn_aggregation.rs:283) | `from_retained_deco(VerifiedPayment)` |
| `CarrierWitness::Bridge` arm (ivc_turn_chain.rs:3114) | `CarrierWitness::Deco` arm |
| `BRIDGE_MINT_HASH_PI = 46` (ivc_turn_chain.rs:2865) | `DECO_PAYMENT_HASH_PI` (tail) |
| `mintV3BridgeHash` / `withMintHashPin` (EffectVmEmitRotationV3.lean) | `stripeMint` / `withPaymentHashPin` |
| nullifier double-spend (bridge_ledger.rs:294) | paymentIntentId double-mint — **same set, already wired** (stripe_mirror.rs:73) |
| `BridgeBindingFromFold.lean` | `DecoBindingFromFold.lean` |
| `BridgeBackingAttack.lean` (STANDS) | `DecoBackingAttack.lean` (the deployed-AIR-alone omission) |
| freshness rides `hfresh` (BridgeBindingFromFold.lean:56) | freshness rides `hfresh` (identical) |
| ed25519 off-AIR + executor-checked | ed25519/HMAC/SHA-256 off-AIR + executor-checked (§8 carriers) |
