# AUDIT-privacy.md — What pyana claims about privacy, and what it delivers

**Scope.** A read-only walk through the privacy-shaped subsystems of pyana:
blinded endpoints, sealed-X primitives, the new `Commitment<T>` framework,
sovereign cells with field visibility, the privacy-voting app, the Midnight
bridge / `gen_midnight` DSL backend, encrypted turns and the trustless intent
engine, wire-level transport, and the side channels that survive all of it.

I write this with the existing audit lens (claim → mechanism → does it
deliver? → leak surface) and end with a property × delivered? × where-enforced
matrix plus open questions.

---

## 1. The claims, in pyana's own voice

### 1.1 The top-level pitches

`README.md` is the cleanest statement of what's promised. The relevant
claims, lifted verbatim:

- *"Intent Solving — Privacy-preserving marketplace. Commit-reveal
  frontrunning protection. Ring trades without a coordinator."* (line 17)
- *"Privacy Model: Three verification modes from the same Datalog rules:
  Trusted | Selective Disclosure | Fully Private — verifier learns 0 / chosen
  facts / one bit."* (lines 94-101)
- *"All modes work offline. Proofs are post-quantum secure (BabyBear STARK +
  FRI)."* (line 103)
- Trust-model claim 9: *"forward secrecy"* — implemented in `cell/src/seal.rs`
  via fresh ephemeral X25519 keypairs per seal call (`seal()` at line 169).

`PYANA_DESIGN.md` line 44: *"Agents broadcast needs as intents (public).
Wallets evaluate privately using local Datalog (never leaves the device).
Fulfillment is a STARK proof that leaks nothing about the satisfier."* The
**parenthetical "(public)" is the actual privacy boundary** — and it's where
most of the marketplace de-anonymisation surface lives.

`docs/unlinkability-analysis.md` is the most honest internal document. It
enumerates seven unlinkability properties (multi-show, issuer, sender/
receiver, transaction-graph, intent, network, cross-federation) and grades
five of them as "partial" or worse.

`docs/intent-privacy-assessment.md` opens with *"Short answer: No. The system
provides component-level privacy ... but the composition leaks enough metadata
to profile participants in a real marketplace."*

### 1.2 What each component-level doc claims

| Component                    | Claim                                                                                        | Source                                                                                  |
| ---------------------------- | -------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------- |
| Sealer/unsealer              | Capability transfer with forward secrecy and recipient-binding via fresh DH                  | `cell/src/seal.rs:1-17`                                                                 |
| Sealed capability commitment | Producer-signed dual-form digest; opaque without unsealer secret                             | `cell/src/seal.rs:57-70`                                                                |
| Encrypted turns              | "Hide content from federation during ordering" with bloom-filter conflict detection          | `turn/src/encrypted.rs:1-15`                                                            |
| Blinded queue                | "Operator sees commitments and nullifiers but cannot link them"                              | `storage/src/blinded.rs:8-13`                                                           |
| Private consumption          | "Hide which commitment was consumed" via in-circuit Merkle membership + nullifier derivation | `storage/src/blinded.rs:73-85`                                                          |
| Privacy-voting               | "Chosen option is hidden behind 32-byte randomness in commit phase"                          | `apps/privacy-voting/src/lib.rs:18-23`, `apps/privacy-voting/src/ballot.rs:11-17`       |
| Trustless intent engine      | "Threshold-encrypted intents — no party reads before collective decryption"                  | `intent/src/trustless.rs:5-7`                                                           |
| Note model                   | Anonymous, consume-once, "self-proving" with federation-independent nullifiers               | `cell/src/note.rs:1-12`                                                                 |
| Value commitments            | Pedersen-hiding; "executor never learns actual amounts"                                      | `cell/src/value_commitment.rs:14-21,46-66`                                              |
| Federated presentation       | Multi-show unlinkability via fresh `presentation_randomness` and blinded leaf                | `docs/unlinkability-analysis.md` §1-2, code in `bridge/src/present.rs`                  |
| Cell field visibility        | Progressive disclosure: `Public` / `Committed` / `SelectivelyDisclosable`                    | `cell/src/state.rs:13-26`                                                               |
| Wire layer                   | "TLS provides confidentiality and authentication of the transport"                           | `wire/src/lib.rs:8-15`                                                                  |
| Network layer                | (Acknowledged to have none.) Future: Dandelion++ + padding + Tor + mixnet                    | `docs/design-network-privacy.md`                                                        |
| Midnight bridge              | Observation/attestation bridge; "value privacy" delegated to Midnight                        | `docs/midnight-comparison.md`, `bridge/src/midnight.rs:1-28`                            |

The headline claim of `README.md:94-103` ("Three verification modes:
Trusted | Selective Disclosure | Fully Private") refers specifically to
**credential proof presentation** (the STARK-proven derivation chain over
Datalog rules). It does NOT mean "the whole system runs in one of three
privacy modes." This conflation is easy to make from the README and is
something I'd flag for the designer (see §10 and §12).

---

## 2. Blinded endpoints (`app-framework/src/blinded_endpoint.rs`)

**What "blinded" means here.** The endpoint exposes a four-route HTTP skin
over `BlindedQueue`: `/commit`, `/consume`, `/consume-private`, `/status`.
The blinding is **value-blinding** — the operator sees a stream of opaque
commitment bytes go into a queue and a stream of opaque nullifier bytes come
out, and (claim) cannot link them. It is NOT:

- sender-blinding (the operator sees the TCP/HTTP connection)
- argument-blinding (the *commitment value itself* is the only payload; the
  endpoint never claims to hide which commitments are being submitted)
- recipient-blinding (`/consume` reveals which commitment is being consumed —
  see line 66-71 of `storage/src/blinded.rs`: *"NOTE: this reveals WHICH
  commitment, but not the CONTENT. For full privacy (hide which commitment):
  use a ZK Merkle membership proof"*).

The honest privacy property is therefore: **commitment-content hiding +
sender-receiver unlinkability across the queue**, conditional on (a) the
caller using `/consume-private` (not `/consume`), and (b) the operator not
being able to do timing/IP correlation outside the protocol.

The post-Stage-10 migration (`storage/src/commitment.rs`, the new typed
`Commitment4<BlindedItemMarker>` type) does NOT change the privacy
properties. It only changes the *binding* (now Poseidon2 inside the circuit
+ BLAKE3 outside, both committed to the same canonical preimage at the
producer). The hiding property comes from the (unspecified, caller-chosen)
randomness in the commitment preimage, not from the dual-form structure.
That's a subtle point: the commitment framework is about *binding* and
*type discipline*, not about *hiding*. Hiding is the producer's
responsibility, per `DESIGN-commitment-framework.md` §2.1.

**Failure modes I can see in `blinded_endpoint.rs`:**

1. `handle_commit` takes a wire-side 32-byte hash and lifts it to a typed
   `Commitment4` via `canonical_32_to_felts_4` (line 209-210). There is **no
   range proof, no proof of knowledge of the preimage, no anti-flooding**
   beyond axum's defaults. An adversary can spam the queue with arbitrary
   `[u8; 32]` blobs they don't know the preimage of. They can't *consume*
   them (no nullifier they can compute), but they can DoS the queue and
   inflate the anonymity set with un-spendable items.

2. `handle_consume_private` accepts an arbitrary `spending_proof_hex` and
   the verifier-side check is `if proof.spending_proof.is_empty() { invalid
   }` (line 200-202 of `storage/src/blinded.rs`). The doc-comment at line
   195-199 is explicit: *"In a real system, we would verify the STARK proof
   here. ... For this implementation, we trust the spending_proof bytes if
   the tree root matches."* **The "fully private" path is therefore
   currently a trust-the-prover stub.** This is documented but worth
   highlighting: every claim about `consume_private` hiding which
   commitment was consumed depends on a STARK proof that this code path
   does not actually verify.

3. The endpoint has no rate-limiting, no auth, no Tor/onion routing. Every
   `/commit` and every `/consume` carries the caller's IP. Network-level
   linkability is *complete*. The README, the design docs, and the
   `docs/design-network-privacy.md` all flag this; it is not a hidden
   shortfall, but the blinded-endpoint module's docstring (lines 1-12) does
   not warn the caller about it.

---

## 3. Sealing — what it is, what it isn't

There are **two different "seal" mechanisms** in pyana, and the names
collide enough to be confusing.

### 3.1 Sealer/unsealer pairs (`cell/src/seal.rs`)

Construction: X25519 + ChaCha20-Poly1305 sealed box, with BLAKE3-`derive_key`
as the KDF (line 7-16). The privacy property is straightforward
asymmetric-encryption privacy:

- *Confidentiality*: the ciphertext is opaque without `unsealer_secret`.
- *Integrity*: ChaCha20-Poly1305 AEAD + an explicit `commitment` field
  (`SealedBox.commitment` at line 64-65) BLAKE3-binding cap-hash ||
  ephemeral_public || nonce.
- *Forward secrecy*: each seal generates a fresh ephemeral keypair
  (line 170-173). Compromising one unsealer DOES leak all *prior* seals
  (because `unsealer_secret` is static), but not the sender's other
  ephemerals. So this is *receiver-static, sender-ephemeral* — same as a
  libsodium sealed box. The README's trust-model bullet #9 ("forward
  secrecy") is overclaim if read as session forward secrecy; it's
  per-message ephemeral-sender forward secrecy.

What this DOES NOT hide:

- The *fact* that a seal was performed (the SealedBox is sent on the wire).
- The `pair_id` (`SealedBox.pair_id` at line 60-61) — this identifies which
  sealer/unsealer pair is being targeted, and so identifies the recipient.
  A passive observer who has seen the recipient's `SealerPublic` published
  anywhere can link any seal sent to that recipient.
- The size of the ciphertext (`Vec<u8>`, no padding).
- The timing of the seal.

### 3.2 SealedTurn (`intent/src/lowering.rs`)

This is a **typestate** layer, not a cryptographic seal. `SealedTurn` (line
120-145) means "every action in this turn has been promoted to a real
`Authorization` (not `Authorization::Unchecked`)." It is the third layer of
the four-layer lowering tower `Intent → EffectPlan → SealedTurn → Turn` (line
1-22). The `from_turn` constructor literally panics if any action carries
`Authorization::Unchecked` (line 138-141).

This is good engineering hygiene — the trustless intent engine emits
`SealedTurn` so that "ready for executor" is a compile-time property — but
**it is not a privacy primitive at all**. Reading "sealed turn" in the
codebase and thinking it implies encryption or hiding is the wrong mental
model. A `SealedTurn` is fully cleartext; its `Turn` field is the same
struct any other code path produces.

### 3.3 Sealed-capability commitment

`cell/src/seal.rs` also defines a BLAKE3-derive_key-tagged commitment over
`(plaintext, ephemeral_public, nonce)` (line 64-65 + `compute_commitment` at
line 250). The doc-comment frames this as binding the ciphertext to a
specific cap. The recently-introduced `Commitment<T>` framework (per
`DESIGN-commitment-framework.md` §1.5) is meant to upgrade this to a
typed dual-form commitment, but at present `SealedBox.commitment` is just
the BLAKE3 form. Migration not yet done.

---

## 4. The `Commitment<T>` framework

`DESIGN-commitment-framework.md` describes the dual-accumulator pattern in
detail. The privacy-relevant facts:

1. **Commitments are hiding *only if* the producer includes randomness in
   the preimage.** The framework does not enforce this; it's a per-marker
   convention. Notes (`cell/src/note.rs:43`) include explicit `randomness:
   [u8; 32]` and `creation_nonce: [u8; 32]` fields. Blinded queue items
   carry randomness too. But for, e.g., `TurnReceipt`, the canonical
   preimage is `turn_hash || forest_hash || pre_state || post_state || ...`
   — there is no per-commitment randomness, so the commitment is binding but
   **not** hiding for receipts. That's fine because receipts are public
   anyway, but worth being explicit about in the docstring.

2. **Binding is automatic from collision-resistance of the hash.** Both
   BLAKE3 and Poseidon2 are assumed collision-resistant (the latter at
   ~124-bit security for `Commitment4`, ~31-bit for `Commitment` — the
   one-felt variant is unsafe as a standalone identifier and the design doc
   §3.1 explicitly says so).

3. **Equivocation resistance.** If the same `Commitment<T>` were "opened"
   to two distinct values, that would be a hash collision on BLAKE3 AND
   Poseidon2 simultaneously. Practically impossible. So yes, the framework
   *is* equivocation-resistant.

4. **The one-directional binding** between BLAKE3 and Poseidon2 forms is
   the subtle bit. The framework explicitly does NOT prove
   `blake3 = BLAKE3(preimage)` inside a STARK. Instead the producer
   "ceremonially" computes both from the same canonical bytes and signs
   them together. A malicious producer can emit a `Commitment<T>` whose
   two forms commit to *different* preimages. The STARK then proves only
   what the Poseidon2 form says; the BLAKE3 form is a side-channel.

   **Privacy implication:** an adversary who breaks Poseidon2 collision
   resistance (or who's just dishonest about the production step) can have
   the BLAKE3 form bind to one note and the Poseidon2 form bind to a
   different note. The dual-form structure does not detect this without
   the preimage in hand. This is documented (`DESIGN-commitment-framework.md`
   §2.2 line 196-207: *"Cross-form divergence is detectable only by a
   third party who knows the preimage or who watches the producer's
   signature."*) and reasonable, but it means the framework's claim is
   **"binding from the producer's signature"** rather than
   **"binding from the cryptography alone."**

---

## 5. Sovereign cells: capability-secure ≠ private

`cell/src/cell.rs:17-22` defines `CellMode::Sovereign`. `cell/src/state.rs`
defines `FieldVisibility::{Public, Committed, SelectivelyDisclosable}` (line
13-26). The framing is "progressive disclosure": a cell field can be
plaintext, hidden behind a hash, or hidden but provable with a ZK predicate.

**What's actually delivered.**

- *The executor sees cleartext.* `CellState.fields[]` (line 47) is a
  `[FieldElement; STATE_SLOTS]` of 32-byte values. The visibility flag is a
  parallel array (`field_visibility[]`, line 49). A cell mutation through
  the executor passes through `executor.rs:4640-4641` which reads and
  writes `cell.state.fields[*index] = *value` *in cleartext*. The
  visibility flag only controls what `public_field_view()` returns to
  external readers (`cell/src/state.rs:286-291`):

  - `Public` → `Revealed(field_value)`
  - `Committed` | `SelectivelyDisclosable` → `Committed(hash)`

  So privacy with respect to the *executor* is exactly the same as with
  respect to a non-cap-holder: **none**. Privacy with respect to a
  *non-cap-holder reading the public state view* is real but post-hoc — the
  executor still sees the value during the turn.

- *Sovereign cells are different.* A sovereign cell carries its own state
  off-federation; the STARK proof binds the transition. In sovereign mode,
  the cell's *operator* (whoever runs the prover) sees cleartext, but the
  federation only sees the proof. This is the architectural privacy story:
  "you self-host, you self-prove, the network only sees what you publish."
  But that's not the cell *being private from its executor*; it's the cell
  *being its own executor*.

- *Hosted cells* (the default in the federation flow) have all state
  visible to the federation node hosting them. There is no encryption of
  cell state at rest, no secret-sharing across federation members, and
  nothing equivalent to a TEE. The federation node IS the executor and
  sees everything.

So the answer to "is the cell state hidden from the executor": **No, in
hosted mode the executor sees cleartext fields. The visibility flag only
hides them from external state-view consumers. In sovereign mode the
executor *is* the cell's owner, so the question is somewhat ill-posed.**

The audit hook here is `cell/src/state.rs:42-43`: *"`fields[]`,
`field_visibility[]`, and `commitments[]` remain public arrays because the
executor mutates them by index in tight loops."* That is the executor saying
"I need cleartext to do my job," which is honest but worth noting.

---

## 6. Privacy-voting (`apps/privacy-voting/`)

### 6.1 The cryptographic guarantee

`apps/privacy-voting/src/ballot.rs:11-17`: a vote commitment is

```text
commit = blake3-derive("pyana-ballot-v1" || proposal_id || option_index_le || randomness)
```

with `randomness: [u8; 32]`. The lib.rs docstring (lines 18-23) is clear:
*"The chosen `option_index` is hidden behind a 32-byte randomness during the
commit phase. Without the reveal, no observer learns who voted for what.
The voter's identity (their `delegatee` pubkey) is never persisted alongside
the commitment."*

What this delivers:

| Hidden from              | During commit phase                                                  | During reveal phase                                                       |
| ------------------------ | -------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| Executor                 | ballot choice (yes; only `commit` is stored)                         | NO — the executor reads the `BallotReveal` to validate and tally          |
| Tallier                  | ballot choice (yes; commit phase)                                    | NO — the tally is computed from cleartext reveals                         |
| Federation               | ballot choice (yes during commit)                                    | NO during reveal                                                          |
| Other voters             | ballot choice (yes during commit)                                    | NO during reveal — reveals are public per `tally.rs:14-17`                |
| Network observers (TLS)  | the commit POST body (TLS, not pyana-specific)                       | the reveal POST body                                                      |

**The privacy is therefore "commit-phase only, then fully public on reveal."**
That's the standard commit-reveal voting pattern (cf. Chaumian voting). It's
honest about what it provides — but the README phrase "privacy voting" is
a stretch: it's *unlinkable-during-commit voting with mandatory
later disclosure*. A true private vote would tally without revealing
individual votes, e.g., via threshold-decryption (Helios-style) or homomorphic
tallying (Benaloh-style). The KZG-flavored migration sketched in
`tally.rs:25-34` is positional verifiability, not vote-content privacy.

### 6.2 The eligibility surface

`apps/privacy-voting/src/eligibility.rs` requires a `DelegatedToken` from a
known authority. The token's `delegatee` pubkey is used for double-vote
prevention (`lib.rs:22-23`: *"the double-vote-prevention set is keyed by
pubkey but kept disjoint from the queue"*). The pubkey is therefore visible
to the server even if its set is kept separate from the commit/reveal log.

Anonymity-set claim: the set of pubkeys that have committed by the close of
commit phase. An adversary correlating *which pubkeys posted commits when*
with *which reveals matched which commits* learns the per-vote-choice
mapping at reveal time. The "disjoint set" structural separation doesn't
help here — both sets are public.

**This is fine** for low-stakes governance. It is not fine for a serious
private election. The docstring is honest; the README is loose.

---

## 7. The Midnight bridge — uses Midnight's value privacy?

`bridge/src/midnight.rs:1-28` and `bridge/src/midnight_observer.rs` describe
an **observation bridge**. The pattern is the same one Midnight uses with
Cardano (per `docs/midnight-comparison.md`):

1. *Pyana → Midnight*: burn a note on pyana; federation produces threshold
   attestation; Midnight contract verifies and mints.
2. *Midnight → Pyana*: lock tokens on Midnight; pyana observer sees
   finalised block; federation mints note on pyana.

Two privacy questions arise:

**(a) Does the bridge preserve Midnight's shielded semantics?** The bridge
attestation is `FederationAttestation { message_hash, signature, epoch,
federation_pubkey }` (line 47-58). The `message_hash` is BLAKE3 over
"canonical encoding of the bridge message being attested." If that message
contains a cleartext amount and nullifier, the federation knows the bridged
value. If it contains a Zswap-style coin commitment, the federation only
knows a commitment. From the code I can see, the message payload is not
fully specified in the rust module — it's whatever the caller passes to
`compute_message_hash`. So the privacy of the bridge in this direction
depends entirely on what the caller chooses to attest.

**(b) Does `gen_midnight` (DSL backend) use Midnight's shielded execution?**
`pyana-dsl/src/gen_midnight.rs:1-29` produces a ZKIR v3 JSON program
(`Scalar<BLS12-381>` inputs, instruction list). The generator targets
Midnight's *Compact/ZKIR* runtime, which is the engine Midnight uses for its
own private smart contracts. So in principle a pyana DSL constraint can be
compiled into a Midnight private circuit. But:

- The compiled output is just an `IrSource` JSON; it is submitted to
  Midnight's proof server / chain via Midnight's own client, not via the
  bridge module above.
- The pyana → Midnight bridge does not currently route value through
  shielded Zswap pools — `bridge/src/midnight.rs` describes a token-lock
  contract and a `unlockFromPyana` function with a nullifier, which is a
  standard non-shielded bridge.

So the situation is: **pyana can EMIT ZKIR programs that run on Midnight's
shielded execution layer (`gen_midnight.rs`), but the pyana ↔ Midnight
*value* bridge (`midnight.rs` + `midnight_observer.rs`) is a vanilla
attestation bridge with no Zswap involvement.** The privacy benefit of
Midnight is therefore available to *apps that target Midnight as a backend*,
not to *value flowing through the bridge*. `docs/midnight-comparison.md`
line 37-39 is honest about this: *"a pyana cell locks a note → federation
attests → Midnight contract mints shielded coin (or vice versa)"* — and
"shielded coin" is up to the contract on Midnight, not the bridge.

---

## 8. Wire-level privacy

`wire/src/lib.rs:8-15` is unambiguous: the wire crate is a *transport*, not
a trust boundary. The claimed properties are TLS confidentiality +
authentication + replay protection. The implementation
(`wire/src/server.rs:1083-1090`) prints

> *"WARNING: pyana-wire server '{...}' running WITHOUT TLS. All traffic is
> plaintext. Set tls_cert_path and tls_key_path ..."*

if TLS is not configured. This is good. TLS does provide content
confidentiality between any two peers that have done a valid TLS handshake.

What TLS does NOT do, that the privacy claim *might* be read to imply:

- *Not metadata-hiding.* The peer's IP, the connection timing, the
  approximate message size — all visible.
- *Not multi-hop privacy.* TLS is point-to-point; if traffic transits a
  federation node before reaching its destination (federation sync,
  gossip), the intermediate node decrypts and re-encrypts (or sees the
  cleartext content in postcard-framed form internally).
- *Not mix-network privacy.* No Sphinx wrapping, no Loopix delays, no Tor
  integration. `docs/design-network-privacy.md` lists this as a Phase 2-3
  roadmap; nothing is wired in today.

CapTP-level encryption of *contents*: the `wire/src/captp_routing.rs` and
related modules carry CapTP messages over the TLS-protected channel. The
messages themselves are postcard-framed cleartext (relative to the wire).
The *capability handle* is encrypted-at-construction via the sealer/unsealer
mechanism (§3.1) when transferred between parties, but the surrounding
CapTP envelope is not. So an on-path observer with TLS access (e.g., a
federation node mid-pipeline) sees: who is talking to whom, what
opcode, the size, and any non-sealed payload — but not the contents of
sealed capabilities.

This is captured in `docs/TRUST_MODEL.md` line 46-51: *"wire/: Transport
(not a trust boundary). Authenticated channels (TLS + PeerRole). Does NOT
verify payload semantics."* Honest framing.

---

## 9. Encrypted turns and trustless intents — designed but not wired in

### 9.1 `EncryptedTurn` (`turn/src/encrypted.rs`)

The structure exists (§1-15 of the file): ChaCha20-Poly1305 ciphertext +
BLAKE3 turn commitment + Bloom-filter conflict set + STARK validity proof
proving "nonce correctness + fee sufficiency." The privacy story is
attractive: the federation orders turns *without* seeing them.

**But `EncryptedTurn` is not used anywhere outside `turn/src/encrypted.rs`
and `turn/src/lib.rs:107` (a re-export).** A `rg EncryptedTurn` over the
whole tree returns hits only inside that module and one re-export. The
executor (`turn/src/executor.rs`) does not consume `EncryptedTurn` at any
point. The actual flow today is: signed `Turn` → executor → state mutation,
all in cleartext at the federation node.

So the privacy property is *designed and locally tested* but **not
delivered in production**. The `verify_metadata()` function only checks
internal consistency (line 132-153), not the actual STARK proof — line 173
explicitly has a `InvalidValidityProof` variant but no code path that
populates it. The bloom-filter conflict set itself leaks "this turn
touched approximately these cells" via false-positive rate; the doc-comment
at line 11-12 acknowledges this trade-off ("False positives ARE possible").

### 9.2 The trustless intent engine

`intent/src/trustless.rs` is more developed but has a similar gap. The
top-level docstring (line 5-13) promises *threshold-encrypted intents → no
party reads before collective decryption → STARK-proven solution validity →
challenge window with bond slashing*. The implementation:

- `EncryptedIntent { ciphertext: Vec<u8>, creator_commitment: CommitmentId,
  submitted_at: u64 }` (line 184-193) — the ciphertext is just a `Vec<u8>`
  blob; the threshold-encryption scheme is not implemented in this module.
- `DecryptionShare { validator_index, share: [u8; 32], batch_id,
  share_mac: [u8; 32] }` (line 207-217) — `share` is a 32-byte opaque blob
  with a `share_mac`; no concrete cryptosystem is selected.
- `set_decrypted_intents(intents: Vec<Intent>)` (line 564-574) is the
  function that "magically" supplies the cleartext intents after the
  ceremony. The comment at line 547-553 is explicit: *"In production, this
  is called after `combine_shares` successfully reconstructs the key... For
  the protocol layer, we mark the batch as ready for solving."*

So **the trustless intent engine is a protocol skeleton with the actual
threshold cryptography stubbed out**. The privacy claims of `trustless.rs`
depend entirely on a future integration of (probably) `federation/src/
threshold_decrypt.rs` or equivalent.

### 9.3 What this means for the marketplace privacy story

The marketplace-privacy story is a layered set of components:

| Layer                     | Status                                                                                                                       |
| ------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| Network                   | None. `docs/design-network-privacy.md` is a plan; gossip is plaintext.                                                       |
| Intent content            | SSE keyword tokens (`intent/src/sse.rs`) — `BLAKE3_derive_key("pyana-sse-token-v1", keyword \|\| epoch_le_bytes)`            |
| Intent body               | x25519 sealed box (designed; partially implemented in `intent/src/sse.rs`)                                                   |
| Threshold-encrypted intents | Stubbed in `intent/src/trustless.rs` — cryptosystem not yet selected                                                       |
| Matching                  | Wallet-local Datalog evaluation                                                                                              |
| Fulfillment commit-reveal | Implemented (`intent/src/commit_reveal_fulfillment.rs`); 60s expiry                                                          |
| Payment hiding            | Pedersen value commitments designed (`cell/src/value_commitment.rs`), partially wired (executor consumes `ValueCommitment`)  |
| Receipt chain             | Not hidden; receipt is BLAKE3-chained and the chain shape leaks turn count                                                   |

`docs/intent-privacy-assessment.md` is right: the *components* are privacy-
preserving in isolation, and the *composition* leaks.

---

## 10. Side channels we admit

These are things pyana does NOT hide, in order of severity for a real
deployment. I'm collating from `docs/intent-privacy-assessment.md`,
`docs/unlinkability-analysis.md`, and a code scan.

1. **Network metadata.** IP, connection timing, message size, message
   ordering. No mixing, no padding, no Tor, no Dandelion++. *Documented as
   future work.*

2. **Receipt chain shape.** `TurnReceipt.previous_receipt_hash` chains
   receipts (per `DESIGN-commitment-framework.md` §5). The *length* of an
   agent's receipt chain is public and reveals "how many turns this agent
   has executed." If receipts cross trust boundaries (federation sync,
   bridge presentation), this shape leaks. The IVC migration sketched in
   §6 of the design doc would mitigate this (constant-size proof) but is
   not implemented.

3. **Federation membership / federation root.** The blinded-leaf STARK
   anonymizes *which* member of a federation produced a credential, but
   reveals *which federation*. Federation roots are public.
   `docs/unlinkability-analysis.md` §2 is explicit.

4. **Turn timing.** `Turn.timestamp` is in the public receipt
   (`turn/src/turn.rs` and its receipt sibling). No batching, no Poisson
   delay, no epoch reveal. An observer with gossip access timestamps every
   turn.

5. **Cell IDs.** `CellId` is `BLAKE3(public_key || token_id)` per
   `docs/sovcell-whichone-upgrades.md`. Pseudonymous but **stable across
   turns**. The intent-privacy-assessment §1 calls this out as the
   profiling vector: "CommitmentId 0xAB posts GPU compute intents every
   Monday."

6. **Field-anonymity-set size.** A field marked `Committed` in cell state
   reveals only its hash, but the hash plus protocol-level type
   information often narrows the value to a small set. E.g., a `Committed`
   field that represents a one-of-N choice is hash-distinguishable in
   N evaluations.

7. **Nullifier-set ordering.** The append-only nullifier set
   (`cell/src/nullifier_set.rs`) reveals the *temporal ordering* of spends.
   `docs/unlinkability-analysis.md` §4 calls this "weak transaction-graph
   unlinkability."

8. **Bridge anonymity.** A bridge transfer in a low-volume cross-federation
   window is trivially deanonymized by elimination
   (`unlinkability-analysis.md` §7).

9. **Executor cleartext access.** In hosted-cell mode the federation node
   sees all turn contents in cleartext. *The whole privacy story for
   hosted cells depends on operator honesty.* Sovereign cells avoid this
   by being their own executor, but require the cell to self-host.

10. **The `pair_id` linkability.** `SealedBox.pair_id` identifies the
    intended unsealer — i.e., the recipient — if their `SealerPublic` is
    known. This is unavoidable for the unsealer to detect that the box is
    for them, but it means seals are not recipient-blinded against an
    observer who knows the pair list.

---

## 11. Inconsistencies and gaps

Places where code or docs claim more than the implementation delivers:

1. **`blinded_endpoint::handle_consume_private` advertises "ZK proof
   hides which commitment" (line 7-8 of `blinded_endpoint.rs`) but
   `BlindedQueue::consume_private` (line 195-202 of `storage/src/
   blinded.rs`) accepts any non-empty `spending_proof` byte string.** The
   actual STARK verification is "in the circuit crate" per the comment,
   but there is no call into a verifier from this code path. As shipped,
   a malicious client can publish an arbitrary nullifier with no real
   proof — privacy of the queue against double-spend is broken.

2. **`EncryptedTurn` is exported but never consumed.** The privacy claim
   of `turn/src/encrypted.rs:1-15` ("hidden from the federation during
   ordering") is unreachable from production code paths. The module is
   well-tested in isolation but disconnected from `executor.rs`.

3. **`intent::trustless` uses a placeholder threshold scheme.** The
   docstring promises threshold encryption (line 5-13); the
   `DecryptionShare.share: [u8; 32]` field is a single 32-byte
   "ciphertext" with no algebraic structure tying it to a specific
   threshold scheme. `set_decrypted_intents` is the cleartext sideband.

4. **`Note::nullifier` (BLAKE3) and the in-circuit Poseidon2 nullifier
   are not algebraically bound.** `DESIGN-commitment-framework.md` §6.3
   flags this as a migration target ("Note nullifier — Current ... not
   documented as bound to the same preimage"). Today the executor checks
   the BLAKE3 nullifier and the circuit checks the Poseidon2 nullifier
   and the binding is the producer's good faith. Privacy implication:
   minimal (both are derived from the same `(commitment, spending_key,
   creation_nonce)` triple), but the lack of a typed binding has bitten
   the executor in the past (audit P0-2).

5. **README "Privacy Model" table (lines 94-103) conflates three things.**
   The "Trusted | Selective Disclosure | Fully Private" axis is about
   *credential presentation proof verifier learnings*, NOT about pyana's
   overall privacy mode. The 80 KB "Fully Private" proof hides the
   delegation chain and the issued credential, but the surrounding turn,
   the gossip-broadcast intent, the cleartext executor state, and the
   wire IP all still leak. A new reader could reasonably believe "I can
   run pyana in fully private mode" and be wrong about ~80% of the
   metadata surface.

6. **The "Privacy-preserving marketplace" README claim is contradicted by
   `docs/intent-privacy-assessment.md`.** The latter document is, in my
   view, the correct framing. The README oversells.

7. **Wallet REST/JSON APIs probably leak via the sdk-ts client.** The
   commitment framework design (§7.4) flags this: *"the wallet's REST/JSON
   layer ... currently exposes BLAKE3 hashes as hex strings. Should it
   also expose Poseidon2 forms? Probably yes."* The leak shape is
   wallet-server visibility into which credentials are being prepared for
   presentation — out of scope for this audit but worth flagging.

8. **`SealerPublic.id` (line 28-31 of `cell/src/seal.rs`) is the
   BLAKE3 derive_key of the sealer pubkey.** This means the pair-id is a
   deterministic function of the pubkey — anyone with the sealer public
   key can compute the pair-id, and anyone with the pair-id has a
   permanent identifier for that recipient. This is fine for non-private
   capability transfer; it would be wrong for an *anonymous* drop-box
   primitive.

9. **Privacy-voting double-vote prevention is keyed by delegatee pubkey
   (`lib.rs:22`).** The "double-vote-prevention set" is structurally
   disjoint from the commit queue but is itself a public set of pubkeys
   that voted. So *which pubkeys voted* is public; *what they voted* is
   commit-private and reveal-public. This is consistent with the
   documented model and not a bug; it IS a clear admission that voter
   identity is public.

10. **The "no executor sees cleartext" framing for sovereign cells is
    technically correct but confusingly named.** Sovereign cells execute
    locally; nobody else is the executor. So "executor sees cleartext"
    is vacuously false. But this isn't really *privacy from an executor*
    — it's *self-execution avoiding the question*. The hosted-cell mode,
    which is the actual deployment story for most apps, gives the
    federation node full cleartext access.

---

## 12. Privacy properties matrix

`Yes` = delivered today by code I can read. `Stub` = designed and partially
present but not actually enforced in the executor / wire path. `No` =
explicitly absent. `N/A` = not claimed.

| Property                                          | Delivered?     | Where enforced (file:line or doc)                                                  |
| ------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------- |
| Sealer/unsealer ciphertext confidentiality         | Yes            | `cell/src/seal.rs:169-192` (X25519 + ChaCha20-Poly1305 + BLAKE3 KDF)              |
| Sealer/unsealer integrity                          | Yes            | ChaCha20-Poly1305 AEAD + commitment field (`cell/src/seal.rs:212-217`)            |
| Sealer ephemeral forward secrecy (sender side)     | Yes            | `cell/src/seal.rs:170-173` (fresh ephemeral per call)                              |
| Sealer recipient-blinding against observer         | No             | `SealedBox.pair_id` deterministically identifies recipient (`seal.rs:60-61`)      |
| Commitment hiding (note, blinded item)             | Yes (with rand)| `cell/src/note.rs:36-48`, `storage/src/commitment.rs` markers                     |
| Commitment binding                                 | Yes            | BLAKE3 + Poseidon2 collision resistance                                            |
| Equivocation resistance                            | Yes            | Implicit in collision resistance of both hashes                                    |
| Dual-form (BLAKE3 ↔ Poseidon2) binding             | Yes, producer-signed | `DESIGN-commitment-framework.md` §2.2; not in-circuit                       |
| Cell-state hidden from hosted executor             | No             | `cell/src/state.rs:42-43`, executor reads cleartext at `executor.rs:4640-4641`    |
| Cell-state hidden from external readers (Committed)| Yes            | `cell/src/state.rs:286-291` (`public_field_view`)                                  |
| Sovereign cell state hidden from federation        | Yes            | STARK only; sovereign cell self-hosts; federation sees PI only                     |
| Privacy-voting: ballot hidden during commit phase  | Yes            | `apps/privacy-voting/src/ballot.rs:38-49` (BLAKE3-derive + randomness)            |
| Privacy-voting: ballot hidden during/after reveal  | No             | `tally.rs:14-17`, reveals are public                                              |
| Privacy-voting: voter identity hidden              | No             | Double-vote set is pubkey-keyed (`lib.rs:22-23`)                                  |
| Intent content hidden from gossip network          | No             | `intent/src/lib.rs:55-56` ("Intents are public")                                  |
| Intent content hidden via threshold encryption     | Stub           | `intent/src/trustless.rs` skeleton; cryptosystem not selected                     |
| Intent matching done locally (privacy of held caps)| Yes            | Wallet-local Datalog eval (`intent/src/lib.rs:53-62`)                              |
| Fulfillment commit-reveal: hides fulfiller pre-reveal | Yes         | `intent/src/commit_reveal_fulfillment.rs`                                          |
| Fulfillment timing unlinkability                   | No             | 5s commit window + immediate reveal exposes timing (`intent-privacy-assessment.md` §3) |
| Multi-show unlinkability (presentation)            | Yes (small field) | `bridge/src/present.rs:1229`, blinded leaf STARK; BabyBear birthday at ~2^15.5  |
| Issuer unlinkability within a federation           | Yes            | `BlindedMerklePoseidon2StarkAir`; bounded by federation size                       |
| Sender-receiver unlinkability in note transfer     | Partial        | Executor sees the spend+create in the same turn; conservation check leaks mapping  |
| Anonymous note value (Pedersen hiding)             | Designed, partly wired | `cell/src/value_commitment.rs`; consumed in `executor.rs:2326,5739`         |
| Note value hidden from executor                    | Stub           | The `ValueCommitment` path exists; range-proof + Schnorr-on-excess not enforced    |
| Network IP privacy                                 | No             | TLS only; no Tor/mixnet (`docs/design-network-privacy.md`)                         |
| Network timing privacy                             | No             | No Dandelion++/Loopix; designed only                                               |
| Network size privacy                               | No             | No padding; messages range 1-432 KiB                                                |
| Encrypted-turn ordering (federation blind to body) | Stub           | `turn/src/encrypted.rs` not consumed by executor                                   |
| Wire-level confidentiality                         | Yes (if TLS)   | `wire/src/server.rs:1083` warns if TLS off                                          |
| CapTP envelope-level encryption                    | No             | Envelope is postcard cleartext over TLS                                            |
| Midnight bridge: uses Zswap shielded pools         | No             | Vanilla attestation bridge; no Zswap involvement                                   |
| Midnight DSL backend uses Midnight private VM      | Yes            | `pyana-dsl/src/gen_midnight.rs` → ZKIR v3 (`Compact`)                              |
| Cross-federation source-federation hiding          | No             | `PortableProof.source_root` reveals which federation (executor.rs:132-137)        |
| Pseudonymous-but-stable cell IDs                   | Yes (pseudonymous), No (unlinkable) | `CellId = BLAKE3(pubkey \|\| token_id)`; stable across turns          |
| Forward secrecy claim in trust model #9            | Per-message only | Sender-ephemeral; receiver-static                                                |
| Post-quantum security of credential proofs         | Yes            | BabyBear STARK + FRI                                                               |
| Post-quantum security of value commitments         | No             | Pedersen on Ristretto (discrete-log based)                                         |
| Post-quantum security of sealing                   | No             | X25519                                                                              |
| Post-quantum security of bridge attestation        | No             | Ed25519                                                                             |

---

## 13. Open questions for the designer

1. **Is the README's "Privacy Model" table (Trusted / Selective Disclosure
   / Fully Private) intended to describe the whole pyana stack, or only
   the credential-presentation proof system?** The doc reads as the former;
   the code only delivers the latter. Reframing the table to scope
   "verifier learnings during credential presentation, conditional on
   network/executor/wallet honesty" would be more honest. I'd flag
   `README.md:94-103` for a rewrite.

2. **`blinded_endpoint::handle_consume_private` currently accepts any
   non-empty spending proof.** Is the expectation that the actual circuit
   verifier will be wired in before this is exposed to untrusted clients?
   If yes, gate the route behind a feature flag. If no, the privacy
   guarantee of the route is currently false.

3. **What is the deployment plan for `EncryptedTurn`?** The infrastructure
   exists in `turn/src/encrypted.rs` but never enters the executor. If
   this is a "Phase 5" plan, it's worth annotating the module-level
   docstring; if it's deprecated, worth removing or marking experimental.

4. **For the trustless intent engine: which threshold cryptosystem is the
   target?** The current placeholder is type-erased. Once selected
   (Groth-Sahai? Shoup-Gennaro? Hybrid Pedersen?), the privacy of
   front-running prevention depends entirely on its concrete security.

5. **Should the receipt chain be IVC-aggregated by default?** Today the
   chain length leaks via `previous_receipt_hash` linkage. The IVC path
   (§6.4 of the commitment framework) gives constant-size + chain-shape
   hiding. Is this on the critical path?

6. **For hosted cells: is there any path to executor-blind state
   transitions, or is the model "if you want privacy from the executor,
   become a sovereign cell"?** This is a deliberate architectural choice
   worth being explicit about in the docs.

7. **The privacy-voting app reveals identities of voters in the
   double-vote-prevention set. Is there a roadmap for stake-based
   nullifiers (epoch-rotating) like the intent gossip path uses?** That
   would preserve double-vote prevention without publicly enumerating
   voter pubkeys.

8. **The Midnight bridge currently doesn't use Zswap. Is the long-term
   plan to bridge into shielded coins (matching the comparison doc's
   line 37-39), or to keep the bridge non-shielded and have apps
   independently use the Midnight DSL backend for their own private
   contracts?**

9. **The CapTP envelope is unencrypted within TLS. Is there a plan to
   add a Noise-style framing under CapTP, or to rely on TLS forever?**
   Sealed capabilities protect the high-value payload but not the
   metadata (who is talking to whom about what cap-id).

10. **The `Commitment<T>` framework's "producer-signed cross-form
    binding" depends on the producer's honesty. Have we considered a
    consistency-proof — a small succinct gadget proving that the BLAKE3
    and Poseidon2 forms commit to the same canonical preimage — to
    remove this trust? The design doc §2.2 rejects this on cost grounds,
    but I'd want to see the actual cost estimate written down.

11. **Network-layer privacy is the largest unmitigated leak.** The
    Dandelion++ + padding + Tor plan is well-scoped in
    `docs/design-network-privacy.md`. Is it on a real roadmap, or is the
    deployment story "users should run pyana behind their own Tor/VPN"?
    The README's bullet "All modes work offline" is not the same answer
    as "the protocol provides metadata hiding."

12. **The "Privacy-preserving marketplace" claim in `README.md:17`. Given
    `docs/intent-privacy-assessment.md`'s opening line ("Short answer:
    No"), should this README claim be softened?** A more accurate phrasing
    might be "Pseudonymous marketplace with cryptographic frontrunning
    protection."

---

## 14. Bottom line

Pyana has *real* privacy primitives — BLAKE3/Poseidon2 dual commitments
with proper hiding randomness in notes and blinded queue items, a
correctly-constructed X25519 sealed box for capability transfer,
multi-show-unlinkable STARK presentation proofs over a blinded Merkle leaf,
and Pedersen value commitments wired into the executor for conservation
checks. These are the privacy *components*.

The *system* layered above them inherits less. Hosted cells are cleartext
to their federation executor. Intents are publicly broadcast. The
network has no metadata hiding. Two of the most ambitious privacy
mechanisms — `EncryptedTurn` and the trustless intent engine's threshold
encryption — exist as well-shaped skeletons but are not connected to
production code paths. Privacy-voting hides votes only during the commit
window. The Midnight bridge does not leverage Midnight's shielded value
semantics.

The internal documentation is unusually honest about this: 
`docs/intent-privacy-assessment.md` and `docs/unlinkability-analysis.md`
are the most reliable summary. The README is more aspirational and would
benefit from a more careful description of which guarantees hold at which
trust-boundary layer.

End.
