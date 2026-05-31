# GROUND-AUTH-ATTESTATION — the authorization + attestation dimension, Rust as ground truth

READ-ONLY grounding pass. No code changed. Every claim cites `file:line`. The
mission: establish the **Rust** semantics of dregg's authorization/attestation
layer as ground truth, audit the Lean's fidelity against it, and analyze the
repudiation/deniability/designated-verifier concern. This is the dimension an
effect-VM-centric view under-weights: caveats *gate* effects and attestation is
the turn *output*, so the real turn vocabulary is **effects ⊕ caveat-gates ⊕
attestation**, not effects alone.

Bottom line up front:
- The Rust is **substantially richer** than the Lean on this axis. The Lean
  Authority modules model the *algebraic discipline* (attenuation-only,
  discharge-monotone, issued-and-not-revoked, six-mode dispatch soundness) at a
  high level of faithfulness — and in one place (CapTP non-amplification) the
  Lean models the *correct* semantics the Rust is *missing*. But the Lean
  **overlooks** the cryptographic substance of the most advanced Rust features:
  the HMAC caveat chain, the third-party discharge protocol (encrypted
  ticket/VID, bind-to-parent, freshness), credential selective-disclosure +
  predicate proofs + blinded multi-show, the stealth one-time-key auth mode, and
  the StarkDelegation anonymous-delegation public-input binding.
- On Part 2: dregg's proofs/attestations are **hardwired to maximal
  transferability** (publicly-verifiable STARK + Ed25519 signatures ⇒
  non-repudiable). dregg HAS strong **anonymity** (who-hiding) and has it modeled
  in Lean; it has **zero deniability** and **zero designated-verifier**
  machinery in either Rust or Lean. There is no mode/dial for non-transferable
  proof today.

---

# PART 1 — THE CAVEAT / TOKEN / ATTESTATION SYSTEM (Rust first)

## 1.1 The macaroon core (HMAC caveat chain) — `macaroon/`

The macaroon implementation is **real and complete**, not a stub.

- **HMAC chain construction**: `macaroon/src/macaroon.rs:118-142` — `Macaroon::new`
  seeds `T₀ = HMAC(root_key, nonce_bytes)`; the chain extends per caveat. The
  invariant is stated in the module header `macaroon/src/macaroon.rs:14-21`:
  `Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))`.
- **Attenuation = append-only caveat add**: `add_first_party`
  (`macaroon.rs:151-156`) advances the tail. Caveats can only *restrict*
  (`caveat.rs:2-9`, `caveat.rs:47-49`). This is the cryptographic realization of
  "a key may only narrow."
- **Verification replays the chain** (`macaroon.rs:204-262`): re-derives the tail
  from the root key, collects first-party caveats for clearing, dispatches 3P
  caveats to discharges, and does a **constant-time** final-tail compare
  (`macaroon.rs:257`). Tests prove tamper/removal/wrong-key all fail
  (`macaroon.rs:455-506`).
- **Caveat type space** (`caveat.rs:24-45`): platform `0..31`, user-registerable
  `32..47`, user-defined `48..253`, `254`=third-party, `255`=bind-to-parent.
- **Typed dregg grant vocabulary** (`token/src/dregg_caveats.rs:137-169`):
  `App{id,actions}`, `Service`, `Feature`, `ValidityWindow{not_before,not_after}`,
  `ConfineUser`, `OAuthProvider`, `OAuthScope`, `FeatureGlob{include,exclude}`,
  `Budget{...}`, and an `Unknown` passthrough. The `Attenuation → WireCaveat`
  lowering is `dregg_caveats.rs:299`.

### Advanced feature: THIRD-PARTY CAVEATS + DISCHARGE PROTOCOL — `macaroon/src/caveat_3p.rs`

This is a full Schnorr-style discharge protocol, not a flag:
- `ThirdPartyCaveat::new` (`caveat_3p.rs:71-102`): generates an ephemeral
  discharge key `r`; encrypts `{r, caveats_for_3p}` under the issuer↔3P shared key
  `KA` → **Ticket (CID)**; encrypts `r` under the *current HMAC tail* →
  **VerifierKey (VID)**. So only the verifier (who can replay the chain to that
  tail) recovers `r`, and only the 3P (who holds `KA`) recovers the ticket.
- **Discharge issuance**: `create_discharge` (`macaroon.rs:383-404`) — the 3P
  signs a fresh discharge macaroon under `r`, stamping a `created_at` timestamp.
- **bind-to-parent**: `bind_discharge` (`macaroon.rs:341-347`) adds a caveat
  carrying `SHA256(root_tail)`. `verify_discharge` (`macaroon.rs:267-332`)
  **requires** this binding (fail-closed at `macaroon.rs:324-329`, even for empty
  discharges — test `macaroon.rs:578`), preventing replay of a discharge against a
  less-attenuated root.
- **Freshness / replay protection**: discharges older than `MAX_DISCHARGE_AGE =
  300s` (`macaroon.rs:35`) are rejected; `created_at == 0` is rejected fail-closed
  (`macaroon.rs:275-289`).
- AEAD is **XChaCha20-Poly1305** (`macaroon/src/crypto.rs:5-8, 59-61`); the
  192-bit nonce removes collision concerns.
- **Cross-vat split is real**: a macaroon's root secret is held only by its
  scoping cell; a biscuit is Ed25519 public-key verifiable. (Token backends:
  `token/src/macaroon_backend.rs`, `token/src/biscuit_backend.rs`, datalog
  verification `token/src/datalog_verify.rs` 2708 lines.)

### The discharge gateway — `discharge-gateway/` + `macaroon/src/discharge_gateway.rs`

A 1096-line server (`macaroon/src/discharge_gateway.rs`) implementing the 3P that
decrypts tickets, checks the embedded caveats, and mints bound discharges. This is
the running counterpart to `Caveat.thirdParty` / `Discharge.settle` in Lean.

## 1.2 Credentials (predicate / membership / anonymous multi-show) — `credentials/`

This is the **most advanced** and most under-modeled feature. Per the module doc
(`credentials/src/lib.rs:1-57`), `dregg-credentials` promotes `bridge::present`
to the credential primitive. It provides:
- `Credential` backed by a real signed macaroon (`credentials/src/issuance.rs`).
- `Presentation` = a STARK proof of "authorization derives from a valid
  credential" **without** revealing the credential (`presentation.rs:84-109`).
- **Selective disclosure**: `PresentationOptions.disclose`
  (`presentation.rs:36-37`); only disclosed attributes are transmitted, with a
  Poseidon2 `revealed_facts_commitment` (`presentation.rs:256-270`,
  `presentation.rs:365-372`).
- **Predicate proofs** (`Gte/Lte/InRange`) over hidden attributes:
  `presentation.rs:307-351` via `prove_predicate_for_fact`.
- **Anonymous presentation / unlinkable multi-show**: `present_anonymous`
  (`presentation.rs:176-182`). The anonymous path (a) **omits the holder
  `confine_user` binding** (`presentation.rs:231-244`) and (b) uses a **real
  STARK with a fresh per-presentation blinding factor** so the public
  `blinded_leaf` differs across shows (`presentation.rs:292-299`). The
  unlinkability rationale is documented inline (`presentation.rs:204-212`).
- The wire form strips the private `AuthorizationTrace` before transmission
  (`presentation.rs:133-152`; the trace is "SECURITY: MUST NOT be transmitted",
  `bridge/src/present.rs:171-179`).
- Verification: `credentials/src/verification.rs` (`verify` / `verify_anonymous`),
  revocation via federation-attested non-revocation root
  (`credentials/src/revocation.rs`).

The underlying ZK engine is `bridge::present::BridgePresentationBuilder`
(`bridge/src/present.rs:103-137`) producing a `BridgePresentationProof`
(`bridge/src/present.rs:149-202`) — a real STARK over issuer-membership Merkle
path + fold chain, verifiable against the **public** `federation_root`
(`bridge/src/present.rs:269-308`).

## 1.3 Anonymous-auth at the turn layer — `turn/`

The `Authorization` sum (`turn/src/action.rs`) is the real per-action auth
carrier. Its `to_auth_kind` map (`action.rs:504-533`) enumerates the variants:
`Signature`, `Proof`, `Breadstuff`, `Bearer`, `Unchecked`, `CapTpDelivered`,
`Custom`, `OneOf`, **`Stealth`**, **`Token`**. Two are anonymity-bearing:

### Stealth one-time-key auth — `turn/src/executor/authorize.rs:1337-1417+`, `cell/src/stealth.rs`

- `cell/src/stealth.rs` is a **complete** Monero/EIP-5564-style stealth-address
  implementation: X25519 DH for the view exchange, Ed25519 point addition for the
  one-time key, `P = H(r·V)·G + S` (`stealth.rs:271-292`), spend key
  `k = H(shared) + s` (`stealth.rs:298-314`), view tags for fast scanning
  (`stealth.rs:220-253`). Tested end-to-end (`stealth.rs:347-533`).
- The executor verifies a stealth auth by recomputing `P' = c·G + S` where `S` is
  the *target cell's persistent key* (never on the wire) and checking an Ed25519
  signature under `P` over a domain-separated message binding federation/nonce/
  position/action-hash (`authorize.rs:1337-1417`,
  `action.rs:606-635`). Unlinkability + replay are argued inline
  (`authorize.rs:1358-1368`).

### StarkDelegation anonymous bearer delegation — `turn/src/action.rs:481-502`, `authorize.rs:1252-1333`

`DelegationProofData` has two arms (`action.rs:483-502`):
- `SignedDelegation{delegator_pk, signature, bearer_pk}` — Ed25519, **identifies**
  the delegator (verified at `authorize.rs:1150-1250`).
- `StarkDelegation{proof_bytes, root_issuer_commitment}` — a STARK proving the
  derivation chain **without** the delegator online and **deliberately hiding**
  delegator/bearer pubkeys behind `root_issuer_commitment`
  (`authorize.rs:1270-1277`). Only the public scope (perm tier, expiry,
  federation id, target) is bound into the proof's public inputs
  (`authorize.rs:1267-1321`), then `stark::verify` runs (`authorize.rs:1322-1332`).
  This is genuine anonymous delegation.

`BlindedSet` membership is the credentials-layer anonymity predicate (see §1.2);
its predicate-kind plumbing lives in `cell/src/predicate.rs` (kind enumerated
`predicate.rs:274`, real-but-soundness-gated verifier `predicate.rs:730, 797`).

## 1.4 Attestation = the turn OUTPUT (the badge) — `turn/src/witnessed_receipt.rs`

The attestation half of the dimension is the **WitnessedReceipt**
(`turn/src/witnessed_receipt.rs:245-267`): a `TurnReceipt` enriched with STARK
`proof_bytes`, flat `public_inputs`, and an optional `WitnessBundle` (inline trace
±recursive proof). It is **verifiable stand-alone** via
`verifier::verify_effect_vm_proof` (`witnessed_receipt.rs:250-251`) and carries a
witness-hash binding so a gossiped scope-2 artifact cannot detach its trace
(`witnessed_receipt.rs:289-325`). The cross-cell bilateral-chain verifier is
`verify_bilateral_chain` (`witnessed_receipt.rs:482-529`). Receipts also carry an
`executor_signature` (`witnessed_receipt.rs:571`).

## 1.5 The right turn vocabulary: effects ⊕ caveat-gates ⊕ attestation

Yes. The effect VM is only one of three faces:
1. **Effects** — what the turn *does* (the VM trace).
2. **Caveat-gates** — what the turn is *allowed* to do: the six-mode
   `verify_authorization` dispatch gates each action *before* effects run
   (`turn/src/executor/authorize.rs`), with token caveats (`Token.admits`)
   and discharge among the gates.
3. **Attestation** — what the turn *emits*: the WitnessedReceipt/STARK badge that
   travels and is independently checkable.

An effect-VM-only model captures (1), shadows part of (2) via the predicate
registry, and treats (3) as a hash. The authorization + attestation dimension is
co-equal with the effect dimension and must be carried as such.

---

## 1.6 LEAN FIDELITY AUDIT (faithful / shadow / overlooked)

Legend: **F** faithful (semantics match), **S** simplified-shadow (the shape is
present but the cryptographic/semantic substance is abstracted to an oracle or a
`Bool`), **O** overlooked-absent (no Lean counterpart).

| Rust feature (file:line) | Lean counterpart (file:line) | Verdict | Note |
|---|---|---|---|
| Attenuation = append caveat, narrowing-only (`macaroon.rs:151`, `caveat.rs:47`) | `Token.attenuate` + `attenuate_narrows` (`Authority/Caveat.lean:81-101`) | **F** | The keystone law is genuinely proved; matches Rust discipline exactly. |
| Token admits iff ALL caveats hold (`token/src/dregg_caveats.rs:388`) | `Token.admits` = `List.all` (`Authority/Caveat.lean:76`) | **F** | Conjunction/meet semantics match. |
| HMAC chain `Tᵢ=HMAC(Tᵢ₋₁,Cᵢ)`, tamper/removal detection (`macaroon.rs:204-262`) | — caveats are `Ctx→Bool` (`Authority/Caveat.lean:43-46`) | **O** | **Lean has NO chain integrity.** Caveat removal/tamper soundness is the whole point of the HMAC tail; the Lean model cannot even express it. This is a §8-oracle gap that is currently *unstated*. |
| Biscuit (pubkey, cross-vat) vs macaroon (HMAC, intra-vat) split (`token/src/{biscuit,macaroon}_backend.rs`) | `TokenKind` + `crossVatVerifiable` + `macaroon_not_crossvat` (`Authority/Caveat.lean:57-126`) | **F** (shape) / **S** (crypto) | The *policy* (macaroon not off-island) is proved; the *reason* (HMAC secret) is an unmodeled premise. |
| 3P caveat: encrypted ticket/VID, ephemeral key `r` (`caveat_3p.rs:71-102`) | `Caveat.thirdParty (gateway)` + `Discharges` flag (`Authority/Caveat.lean:43-55`) | **S→O** | The discharge *monotonicity* is beautifully modeled (`Discharge.lean`), but the **cryptographic ticket/VID protocol is entirely absent** — a gateway is a `Bool`. No model of "only the chain-replayer recovers `r`." |
| bind-to-parent + freshness (`macaroon.rs:267-332`) | — | **O** | No Lean model of discharge↔root binding or 300s freshness/replay. A discharge in Lean is an unconditional flip. |
| Discharge accumulates / resolves forward (`discharge-gateway/`) | `admits_mono_discharge`, `resolve_forward`, `settle_le` (`Authority/Discharge.lean:77-174`) | **F** | Strong, faithful: the await-authority monotonicity keystone. |
| Credential issue/present/verify/revoke (`credentials/src/{issuance,presentation,verification,revocation}.rs`) | `VC`, `issue/present/verify/revoke`, `credential_verifies_iff_issued_and_not_revoked` (`Authority/Credential.lean:55-209`) | **F** (lifecycle) | The issued-and-not-revoked discipline is faithful; revocation reuses the nullifier G-Set with real I-confluence (`Credential.lean:226-244`). |
| **Selective disclosure** (revealed-facts commitment) (`presentation.rs:256-270`) | — `VC.claim` is one opaque `Nat`; `verify` is all-or-nothing (`Credential.lean:153-155`) | **O** | The Lean credential cannot disclose a *subset* of attributes; the Poseidon2 revealed-facts commitment has no analog. (Field-tier `project`/`field_projection_hides_private` in `Privacy.lean:89-114` is the *cell-state* projection, a different object.) |
| **Predicate proofs** Gte/Lte/InRange on hidden attrs (`presentation.rs:307-351`) | `WitnessedKind` enumerated but verifier is abstract `Stmt→Wit→Bool` (`Authority/Predicate.lean:40-72`) | **S** | The *dispatch* is faithfully modeled with a real soundness-by-verification keystone (`registry_sound`, `Predicate.lean:106-111`); the *range-proof relation itself* is a §8 oracle, never characterized. |
| **Anonymous multi-show unlinkability** (fresh blinding ⇒ different `blinded_leaf`) (`presentation.rs:176-212, 292-299`) | `WitnessedKind.blindedSet` (dispatch only, `Predicate.lean:51`) **+** `BlindedMembershipKernel.blinded_membership_hides_element` / k-anonymity (`Privacy.lean:489-507`) | **S** (split) | Two halves modeled in *different* places and **not connected**: `Predicate.lean` has the dispatch but no hiding; `Privacy.lean` has the hiding law but it is not wired to the credential `present`/`verify` path. The credential module (`Credential.lean`) — the thing that actually does multi-show in Rust — has **no** unlinkability statement at all. |
| Six-mode `verify_authorization` dispatch (`authorize.rs`) | `AuthMode` + `authModeAdmits` + per-mode `*_sound` (`Exec/AuthModes.lean:135-410`) | **F+** | Faithful to OneOf recursion rules, Custom registry, Bearer/Token caveats, Unchecked-no-escalation. **And superior**: it models the *correct* CapTP `granted ≤ held` non-amplification that the Rust `verify_captp_delivered` is documented to be MISSING (`AuthModes.lean:20-25, 268-296`). |
| **Stealth one-time-key auth** (`authorize.rs:1337+`, `cell/src/stealth.rs`) | `CatalogInstances.lean:236-240` (a verify-seam stub) + `Privacy.unlinkable` (`Privacy.lean:457-461`) | **S→O** | `AuthModes.lean`'s "six modes" **omit Stealth entirely** (it lists OneOf/Custom/CapTpDelivered/Bearer/Token/Unchecked). `CatalogInstances` reduces stealth to a generic `Discharged`. The `P = c·G + S` relation and its unlinkability are *not* the same object as the `Privacy.unlinkable` payment-graph law; the auth-mode unlinkability is unmodeled. |
| **StarkDelegation** anonymous bearer (hidden delegator/bearer, scope-bound PI) (`authorize.rs:1252-1333`) | `AuthMode.bearer` carries `held/granted` *in the clear* (`AuthModes.lean:152, 305-314`) | **O** | The Lean bearer models the *non-amplification* edge but **not the anonymous variant**: there is no notion that delegator/bearer can be hidden behind a `root_issuer_commitment` while only public scope is bound. The anonymity of the delegation path is overlooked. |
| WitnessedReceipt attestation badge + bilateral chain (`witnessed_receipt.rs`) | `Exec/Receipt.lean`, `Exec/ProofForest.lean`, `Exec/TurnForest.lean` (badge/forest spine) | **S** | The forest/receipt *structure* is modeled; the STARK `proof_bytes`/witness-hash binding is a §8 oracle (correctly so), but transferability/non-repudiation as a *property* is not stated (see Part 2). |
| Pedersen committed conservation (value tier) (`wasm/src/privacy.rs:283-475`, cell commitments) | `Exec/CellPrivacy.lean` `committed_transfer_conserves` (`CellPrivacy.lean:161-169`) | **F** | Genuinely faithful homomorphic-sum conservation over hidden amounts, via the `commit_hom` interface law. |

### Where the Lean is a FICTION or an OVERLOOK (the load-bearing flags)

1. **No HMAC chain integrity** (O). The single most important macaroon property —
   "caveats can only be added, the tail proves it" — is *inexpressible* in the
   current `Caveat Ctx Gateway` (`Authority/Caveat.lean:43`). The Lean proves
   attenuation *narrows* but never that an adversary cannot *remove* a caveat. In
   Rust this is the constant-time tail compare (`macaroon.rs:257`). This is not
   wrong, but it is an *unstated* §8 obligation; it should be made explicit, like
   the credential attestation oracle is.
2. **The 3P discharge protocol is a `Bool` flip** (S→O). `Discharge.lean` models
   *when* discharges resolve a turn (monotone, forward-only) — excellent — but the
   ticket/VID encryption, the `r`-recovery-only-by-chain-replayer property, and
   bind-to-parent + freshness are absent. A reader of `Discharge.lean` would not
   know any cryptography is involved.
3. **Selective disclosure is missing from the credential model** (O). The Rust
   credential's headline feature (disclose attribute subset + predicate proofs)
   has no analog in `Credential.lean`, whose `claim` is one opaque `Nat`.
4. **Multi-show unlinkability is modeled but disconnected** (S). The hiding law
   exists (`Privacy.lean:489-507`) but is not wired to the credential
   `present`/`verify` path (`Credential.lean`) that actually performs multi-show
   in Rust. The "the same credential is unlinkable across shows" theorem is not
   stated about the credential object.
5. **Stealth and StarkDelegation anonymity are overlooked at the auth-mode layer**
   (O). `AuthModes.lean` is otherwise the best module on this axis, but it drops
   two of the real `Authorization` variants — exactly the two that carry
   actor-anonymity.

### Where the Lean LEADS the Rust (carry the Lean semantics forward)

- **CapTP non-amplification** (`AuthModes.lean:268-296`): the Lean proves
  `granted ≤ held`, which the Rust `verify_captp_delivered` is documented to omit
  (it checks signatures + facet masks but not the authority lattice). This is a
  *real bug surfaced by the Lean*. Carry the Lean's `captp_granted_le_held` gate
  into the verified kernel and **fix the Rust to match it**, per the
  improve-don't-degrade rule. (Cross-check: this is the FID-ESCROW pattern in
  reverse — here the Lean is the *better* spec.)

---

# PART 2 — REPUDIATION / DENIABILITY / DESIGNATED-VERIFIER

The severe privacy question: a publicly-verifiable STARK / WitnessedReceipt is
**transferable** ⇒ **non-repudiable**. Anyone holding the artifact can later prove
to *any* third party that a turn was authorized. Grounded in the code:

## 2.1 Confirmation: dregg's attestations ARE transferable / publicly-verifiable

Every attestation primitive is maximally transferable:

- **WitnessedReceipt** verifies stand-alone against a global VK with no verifier
  secret: `verifier::verify_effect_vm_proof` (`turn/src/witnessed_receipt.rs:250-251`);
  the artifact is explicitly designed to *travel as gossip*
  (`witnessed_receipt.rs:287-307`) and serialize to a durable
  `DWR1` envelope (`witnessed_receipt.rs:341-373`). Public inputs are extracted
  in the clear (`witnessed_receipt.rs:253-256`).
- **Credential presentation STARK** verifies against the **public**
  `federation_root` (`bridge/src/present.rs:269-308`,
  `present.rs:284-308`). No designated verifier; anyone with the federation root
  is convinced.
- **StarkDelegation** binds only public scope and verifies with the global Effect
  VM AIR (`turn/src/executor/authorize.rs:1322-1332`) — transferable.
- **SignedDelegation / HandoffCertificate** are **Ed25519 signatures**
  (`turn/src/action.rs:486-494`; `captp/src/handoff.rs:115-191, 251-257`). An
  Ed25519 signature is the canonical *non-repudiable, universally-verifiable*
  object: `verify_signature` (`handoff.rs:255-257`) convinces anyone. The
  recipient also signs (`handoff.rs:314-348`), so the presentation is a
  two-signature transferable transcript.
- **Stealth auth** is *also* a transferable Ed25519 signature under the one-time
  key `P` (`authorize.rs:1337-1417`): it hides *who* but the signature is still a
  transferable proof that *whoever holds S* authorized the action.

**Verdict: the system is hardwired to maximal transferability.** Every "yes, this
was authorized" badge is a portable, third-party-convincing object. There is no
verifier-bound nonce, no chameleon/trapdoor, no interactive ZK, anywhere.

## 2.2 What dregg HAS vs LACKS across the three properties

### (a) ANONYMITY (hide *who*) — STRONG, and partly proved

| Mechanism | Rust (file:line) | What it hides | Real? |
|---|---|---|---|
| Stealth addresses | `cell/src/stealth.rs:136-214`; auth `authorize.rs:1337-1417` | the recipient/actor's persistent key `S`; per-turn one-time `P` | Yes — real Monero/EIP-5564 construction; `S` never on the wire. |
| StarkDelegation | `authorize.rs:1252-1333` | delegator + bearer pubkeys (behind `root_issuer_commitment`) | Yes — only public scope is bound. |
| Anonymous credential present (BlindedSet) | `credentials/src/presentation.rs:176-299` | which credential / which issuer-tree leaf; multi-show unlinkable | Yes — fresh per-show blinding factor. |
| Pedersen value commitments | `wasm/src/privacy.rs:283-475`; `cell` commitments | the amount | Yes — homomorphic, range-proven. |
| Nullifiers | `cell` nullifier path; `Privacy.lean:520-556` | which note/holder spent | Yes. |

Lean coverage of anonymity is genuinely good: `Privacy.unlinkable`
(`Privacy.lean:457-461`), `stealth_anonymity_set_large` (k-anonymity, `:467-472`),
`blinded_membership_hides_element` (`:489-494`), `nullifier_hides_identity`
(`:538-541`), all stated as *view-indistinguishability* with non-vacuous
`Reference` witnesses (`:558-567`). So **anonymity is the one Part-2 property the
Lean already models honestly.**

### (b) DENIABILITY / REPUDIATION — ABSENT

A search of the entire Rust tree for `deniab|repudiat|disavow|chameleon|
RingSignature|ring.signature` returns **no implementation** (only an unrelated
mention in `turn/src/action.rs` doc and `audit/src/tests.rs`). The Lean tree has
**nothing**.

- There is **no ring signature** anywhere (the closest, "anonymity set", is the
  BlindedSet *membership* proof, which proves "I am one of the set" — it hides
  *which* member but the proof is still a transferable, publicly-verifiable STARK,
  so it gives anonymity, **not** deniability). A ring signature's deniability
  flavor ("one of us signed, you can't prove which, and any of us could have
  forged my apparent participation") is not present.
- There is no chameleon hash / trapdoor commitment that would let an authorizer
  later claim "I could have produced that for any message."
- **Net: the authorizer can NEVER deny to a suspecting verifier.** Once a
  WitnessedReceipt / signed delegation / stealth signature exists, it is a
  permanent, transferable fact. Anonymity hides *who among a set*, but for the
  *actual* signer there is no plausible-deniability mechanism.

### (c) DESIGNATED-VERIFIER / non-transferable proof — ABSENT

- No interactive / OTR-style protocol, no designated-verifier ZK (DVZK), no
  "proof valid only to holder of verifier-sk" construction exists in Rust or Lean.
- Every verifier path (`verifier::*`, `verify_issuer_stark`, `verify_signature`,
  `stark::verify`) takes only *public* inputs + a *global* VK and returns a
  universal accept/reject. None takes a verifier secret key.
- The one place that *strips* private data — `Presentation::to_wire` removing the
  `AuthorizationTrace` (`presentation.rs:133-152`) — protects the *prover's*
  witness from leaking; it does **not** make the resulting proof non-transferable.
  The stripped proof is still universally verifiable.

**Summary table:**

| Property | dregg status | Mechanism / absence (file:line) |
|---|---|---|
| Anonymity (hide who) | **HAS, strong, partly proved** | stealth `cell/src/stealth.rs`; StarkDelegation `authorize.rs:1252`; BlindedSet `credentials/src/presentation.rs:176`; Lean `Privacy.lean:457-541` |
| Deniability / repudiation | **LACKS entirely** | no ring sig / chameleon / disavowal anywhere (grep-confirmed) |
| Designated-verifier / non-transferable | **LACKS entirely** | all verifiers take public PI + global VK; no verifier-sk path |

## 2.3 The tension: verifiability ⊥ deniability — and is there a dial?

The tension is real and dregg sits at one pole:
- **Verifiability (transferable proof)** is *required* by dregg's distributed
  core: consensus/finality (`blocklace/`), the proof-carrying forest
  (`circuit/src/proof_forest.rs`, `Exec/ProofForest.lean`), bilateral cross-cell
  consistency (`witnessed_receipt.rs:482-529`), and dispute resolution
  (`app-framework/src/dispute.rs`) all need a third party to *independently
  re-verify* a turn. A non-transferable proof cannot serve these.
- **Deniability (non-transferable)** is what private bilateral interaction wants:
  "I'll prove to *you* I'm authorized, but you can't show it to anyone else."

dregg today has **no dial**: the existing disclosure controls
(`FieldVisibility::{Public, Committed, SelectivelyDisclosable}` at
`cell/src/state.rs:16-25`; presentation `disclose` at `presentation.rs:36-37`;
fully-private vs selective-disclosure `revealed_facts_commitment` at
`bridge/src/present.rs:131-136`) all dial **what is revealed** — never **to whom
the proof is convincing**. Even "fully private" is *universally* verifiable; it
just reveals fewer facts. The transferability axis is orthogonal to the disclosure
axis and is currently pinned at "maximal."

## 2.4 What a designated-verifier / deniable MODE would take (sketch)

This is a *new* capability, not a tweak. It composes *orthogonally* to the
existing disclosure dials (`acceptanceOnly`/`selective`/`fullDisclosure`): add a
third axis **transferability ∈ {public, designated, deniable}** alongside
**disclosure ∈ {acceptance-only, selective, full}**.

1. **Designated-verifier ZK (DVZK).** Replace the universally-sound STARK badge,
   *on the private path only*, with a proof of the disjunction
   `(turn is authorized) ∨ (I know verifier's secret key)`. The intended verifier
   knows their own sk so the proof is worthless to relay (they could have forged
   it); to the verifier the first disjunct is the only credible one. Compose:
   keep the public WitnessedReceipt for consensus, mint a DVZK *companion* for the
   private channel. Cost: a new circuit (an OR-composition over the existing
   presentation AIR + a Schnorr-knowledge clause); the federation-root membership
   stays as-is.
2. **Deniable authentication.** Use a SIGMA/OTR-style interactive (or
   ring-MAC) authenticator on the captp channel so the *recipient* is convinced
   live but holds no transferable transcript. This belongs at the
   `captp/handoff` layer (`handoff.rs`), replacing the Ed25519 recipient signature
   on the *private* path with a deniable MAC keyed to the session. The
   *introducer* signature (needed for authority provenance) would stay
   non-repudiable — only the *presentation* becomes deniable.
3. **Ring-based repudiation.** A true ring signature over the authorizer's
   anonymity set gives the weak deniability "one of us, you can't prove which."
   The BlindedSet machinery (`credentials/src/presentation.rs`,
   `cell/src/predicate.rs:274`) already commits an anonymity *set*; what is missing
   is making the *signature itself* (not just a membership proof) ring-structured
   and **non-transferable**. This is the smallest delta to get *some* repudiation,
   and it is the natural extension of the existing anonymity story.

In every case the **consensus/forest path keeps the transferable badge** (it must;
finality depends on it); the new mode is a *parallel private artifact* on the
bilateral channel. The Lean model would need a new `Transferable` vs `Designated`
distinction on the verify seam (`Laws.Verifiable`): today `Discharged` is a single
universal predicate; deniability requires indexing it by *which verifier* is
convinced — a genuinely new piece of theory.

---

# CARRY-FORWARD VERDICT

## Rust semantics that MUST be carried forward faithfully (currently §8-oracle'd or absent in Lean)
1. **HMAC caveat-chain integrity** — the constant-time tail compare and
   removal/tamper soundness (`macaroon.rs:204-262`). Make it an *explicit* §8
   obligation in the kernel, not an unstated one.
2. **The 3P discharge protocol's cryptographic core** — encrypted ticket/VID,
   `r`-recovery-only-by-chain-replayer, bind-to-parent, 300s freshness
   (`caveat_3p.rs:71-141`, `macaroon.rs:267-347`). The Lean's beautiful discharge
   *monotonicity* must be *paired with* this binding obligation.
3. **Credential selective disclosure + predicate proofs + anonymous multi-show**
   (`credentials/src/presentation.rs`) — the headline feature, almost entirely
   un-modeled at the credential layer.
4. **Stealth + StarkDelegation actor-anonymity** as first-class auth modes
   (`authorize.rs:1252-1417`, `cell/src/stealth.rs`).

## Where the Lean is currently a FICTION / OVERLOOK
- **Fiction-adjacent:** a reader of `Authority/Caveat.lean` + `Discharge.lean`
  would believe the token layer is fully captured; in fact *all* of the
  cryptographic substance (HMAC chain, ticket/VID, binding, freshness) is absent
  and unflagged. This is the FID-ESCROW failure mode — the Lean shape looks
  complete but the Rust does something cryptographically load-bearing the Lean
  omits. Flag and §8-rail it explicitly.
- **Overlook:** selective disclosure in `Credential.lean`; Stealth +
  StarkDelegation in `AuthModes.lean`; multi-show unlinkability is *present in
  `Privacy.lean` but not wired to the credential path it actually governs*.
- **Counter-note (Lean is BETTER):** CapTP non-amplification
  (`AuthModes.lean:268-296`) is the *correct* spec; the Rust
  `verify_captp_delivered` is the buggy side. Carry the Lean forward and fix Rust.

## Ranked advanced token/auth features that were MISSED (most → least load-bearing)
1. **HMAC caveat-chain integrity** (the macaroon's reason to exist) — unmodeled.
2. **Third-party discharge crypto** (ticket/VID/bind/freshness) — only the
   monotonicity skeleton is modeled.
3. **Credential selective disclosure + predicate proofs** — overlooked.
4. **Anonymous multi-show unlinkability bound to the credential object** —
   modeled in the wrong place, disconnected.
5. **Stealth one-time-key auth mode** — dropped from the six-mode model.
6. **StarkDelegation anonymous delegation** (hidden delegator/bearer) — bearer is
   modeled only in the clear.
7. **bind-to-parent + discharge freshness/replay** — absent.

## Part-2 verdict
dregg is **deliberately, structurally non-repudiable**: transferable proofs are
load-bearing for its distributed core, so this is not an oversight but an
architectural commitment. It has **strong, partly-proved anonymity** but **zero
deniability and zero designated-verifier** capability. A private-interaction mode
(DVZK / deniable auth / ring repudiation) is a genuinely new axis —
*transferability* orthogonal to the existing *disclosure* dials — and would
require both new circuits/protocols in Rust and a new verifier-indexed `Discharged`
in the Lean. Nothing in the current code is a stepping stone toward it except the
anonymity-set commitment, which gets you the weakest (ring) form.

---

```
( ⌐■_■ )  the badge travels. the question for the kernel is whether we ever
          want one that doesn't — and today the answer in code is "never".
```
