// =============================================================================
// Section 5: Privacy Architecture
// =============================================================================

= Privacy Architecture

Dragon's Egg provides zero-knowledge authorization proofs where a prover demonstrates "I hold a valid attenuated capability chain from a federation-registered issuer that satisfies your request" without revealing the chain, intermediate states, or other capabilities. The privacy story spans many subsystems; the *boundary discipline* (@sec-boundary-discipline) is the vocabulary the codebase uses to keep them honest.

== Boundary Discipline <sec-boundary-discipline>

Cryptographic distributed systems organize around two populations: those who know a datum *by construction* (because they generated it, hold the private key, ran the prover) and those who relate to that datum through some interface (verify a signature, check membership in a set, decode a ciphertext, accept a proof). In Dragon's Egg, that boundary is *implicit, plural, and per-subsystem*. The codebase names fourteen boundaries explicitly (see BOUNDARIES.md) and adopts a four-label vocabulary that every public type with a privacy story documents:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Label*], [*Population*]),
    [Cleartext-inside], [Participants who see the plaintext datum. The hosted-cell executor is cleartext-inside every hosted cell's state, regardless of the slot's `FieldVisibility` tag.],
    [Commitment-inside], [Participants who see only the commitment (a 32-byte hash or 4-felt Poseidon2 output). External readers of `public_field_view` for a `Committed` slot; the federation for a sovereign cell's state in proof-carrying mode.],
    [Acceptance-inside], [Participants who see only proof-of-acceptance (yes/no plus public inputs). A STARK verifier; a `ThresholdQC` verifier.],
    [Out-of-band], [Participants who learn nothing. The default audience for everything not explicitly named.],
  ),
  caption: [The four boundary populations. Labels are *per-datum, per-subsystem*; a single party can be cleartext-inside one subsystem and out-of-band another.],
)

These labels do not aggregate into a global trust level. The discipline is editorial: every public type with a privacy story documents its boundary contract:

```rust
/// Boundary contract:
/// - Cleartext-inside:  <population>
/// - Commitment-inside: <population>
/// - Acceptance-inside: <population>
/// - Out-of-band:       <population>
/// Enforced by: <primitive>
/// Failure mode if violated: <description>
```

=== The fourteen boundaries

Dragon's Egg's boundaries, enumerated:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Boundary*], [*Inside (cleartext)*], [*Enforcing primitive*]),
    [Federation membership], [BLS committee members], [BLS12-381 weighted-threshold aggregate],
    [Cap-holder (swiss-number)], [Swiss bytes holder], [Possession (bearer)],
    [Turn-author (STARK soundness)], [Actor (cclerk spending key)], [STARK soundness over `EffectVmAir`],
    [Sealed-box recipient], [`unsealer_secret` holder], [X25519 + ChaCha20-Poly1305 + BLAKE3 binding],
    [Cell state field visibility], [Federation node (always); external readers per `FieldVisibility`], [`public_field_view`],
    [Sovereign cell holder vs executor], [Agent (intended); agent + executor (witness path)], [STARK (proof-carrying) or signature (witness path)],
    [`WitnessedReceipt` scope-1 vs scope-2], [Scope-1: proof verifier; Scope-2: bundle file holder], [STARK + bundle membership (no predicate today)],
    [`peer_exchange` two-party vs world], [Alice + Bob], [Ed25519 `verify_strict` + monotonic sequence + optional STARK],
    [Blocklace consensus vs external verifier], [Constitution participants], [Cordial Miners $tau$ + signatures + equivocation detection],
    [Bridge origin + destination vs world], [Source committee + destination committee + note holder], [STARK + `BridgedNullifierSet` + `AttestedRoot`],
    [Blinded credential prover vs verifier], [Credential holder], [`BlindedMerklePoseidon2StarkAir` + per-presentation randomness],
    [Sealed-box pair (intent matching)], [Two matched intent owners], [Sealer/unsealer + threshold-encrypted intent],
    [CapTP session participants], [Two peers in a `CapSession`], [Session epoch + TLS confidentiality],
    [`Authorization::CapTpDelivered` cert vs anyone], [Cert recipient (`recipient_pk` holder)], [Introducer Ed25519 sig + recipient Ed25519 sig + `KnownFederations`],
  ),
  caption: [The 14 boundaries in Dragon's Egg. Each carries a per-subsystem boundary contract (per BOUNDARIES.md).],
)

=== Boundary composition

Boundaries compose three ways:

- *Nesting*: a sealed message *to* a cap-holder who's *in* a federation produces nested boundaries. The innermost boundary is operative for the protected datum; outsiders see what the next-outer boundary permits.
- *Intersection*: a datum exposed via two different mechanisms, each with its own boundary, has an effective inside that is the smaller intersection (parties who satisfy *both*).
- *Union*: a datum sealable to either of two recipients has an effective inside that is the larger union.

Concrete example: a sovereign cell's state is *commitment-inside* the federation (only the commitment is persisted) but *cleartext-inside* the host executor during the witnessed turn. The boundary "executor blind" requires the proof-carrying path, where the AIR's `OLD_COMMIT == sovereign_commitments[cell_id]` constraint is the operative inside.

=== Boundary conflicts

The cases where two boundaries make incompatible claims (and the long-term path to resolution):

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Conflict*], [*Resolution path*]),
    [`FieldVisibility::Committed` claims commitment-inside externals, but executor sees cleartext], [Sovereign cells in proof-carrying mode; document `public_field_view` is *external* not algebraic],
    [Sovereign witness path claims executor-blind; actually executor-sees-during-turn], [Lane Hardening: proof-carrying default, witness path Phase 1 AIR teeth + Phase 2 `transition_proof` recursion],
    [Seal drops `allowed_effects` on unseal (formerly)], [Soundness sweep: v3 sealed-plaintext encodes `allowed_effects`],
    [Prior `FederationReceipt.federation_id` decoupled from `committee_pubkeys`], [Lane D: `federation_id = BLAKE3(committee_pubkeys || epoch)` (algebraic)],
    [CapTP-routed turns used `Authorization::Unchecked`], [CI-guarded carve-out list (Stage 8 P2.F); soundness sweep closing remaining],
    [Two equivocation definitions in blocklace (seq vs round)], [Unified equivocation rule (open question)],
    [Proof's outside vs witness-bundle's inside (no audience predicate)], [Sealable witness bundle (open question)],
  ),
  caption: [Boundary conflicts and resolution paths. Naming the conflict is a precondition to fixing it.],
)

== Gap Analysis: Path to Anonymous Credential Parity

Parity with Idemix/BBS+/AnonCreds requires six properties:

+ *Unlinkable multi-show*: the same credential presented N times produces N presentations that cannot be correlated.
+ *Issuer anonymity within set*: a verifier cannot determine which federation member issued the underlying credential.
+ *Predicate proofs over attributes*: "prove age >= 18" without revealing the exact value; arbitrary boolean combinations.
+ *Selective disclosure with cryptographic binding*: the prover chooses which attributes to reveal; unrevealed attributes are cryptographically guaranteed to satisfy the policy.
+ *Revocable anonymity*: credentials can be revoked without breaking unlinkability for non-revoked credentials.
+ *Offline verification*: all of the above without contacting the issuer or federation (already achieved for the STARK path).

== Current Linkability Problem

`PresentationPublicInputs` currently exposes `initial_root` and `final_root`. These are deterministic for a given token---any verifier receiving two proofs can check whether they share the same `final_root` and conclude they came from the same credential. Even with blinded issuer membership (in progress via `BlindedMerklePoseidon2StarkAir`), two presentations from the same attenuated token share the same `final_root`.

== Target: Unlinkable Presentation

A fully private, unlinkable presentation proof exposes only:

$ "PublicInputs" = ("federation_root", "request_predicate", "timestamp", "blinded_tag", "revocation_root", "revealed_commitment") $

The `initial_root` and `final_root` become private witness. The `blinded_presentation_tag` is:

$ "blinded_tag" = "Poseidon2"("final_root" || "nonce" || "randomness") $

This tag is fresh per presentation (unlinkable), but deterministic given the token and nonce (for replay detection within a session). The STARK proves correct derivation from the real `final_root` without revealing it.

== Blinded Queues <sec-blinded-queues>

A _blinded queue_ is a programmable queue where withdrawal is anonymized via nullifiers. The construction:

+ *Deposit*: any cell enqueues a message commitment $C = "Poseidon2"("msg" || "randomness")$. The commitment is public; the content and randomness are private.
+ *Withdrawal*: a cell dequeues by presenting a nullifier $nu = "Poseidon2"(C || k)$ where $k$ is the withdrawal key. A STARK proves: (a) $C$ is in the queue's KZG commitment, (b) $nu$ is correctly derived from $C$ and $k$, (c) the withdrawer knows $k$.
+ *Fairness*: each commitment can be withdrawn exactly once (nullifier uniqueness). The queue enforces FIFO ordering via the KZG polynomial structure.
+ *Unlinkability*: the nullifier reveals no information about which deposit it corresponds to (Poseidon2 preimage resistance).

In the storage-as-cell-programs view (@sec-storage-as-cell-programs), `BlindedQueue` is a cell whose `CellProgram` declares a slot layout (`commitment_set_root`, `nullifier_set_root`, ...) and a single `WitnessedPredicate { kind: Custom { vk_hash: blinded_spend_air_vk } }` enforcing the spend predicate. No new `Effect` variant.

== Private Cell Migration

Sovereign cells can migrate between federations without revealing their identity or state:

+ The migrating cell derives a stealth address for the target federation using the federation's scan key.
+ The cell registers under the stealth address.
+ An IVC proof accompanies registration, proving valid history from genesis without revealing the history.

A nullifier derived from the source registration prevents double-registration. The source federation learns only that "some cell deregistered"; the target learns only that "some cell with valid history registered."

== Fixed-Size Proof Padding

STARK proof size is proportional to trace length, which leaks information about the computation. All proofs are padded to canonical sizes: ${2^(10), 2^(12), 2^(14), 2^(16)}$ trace rows. Padding rows use the `Noop` opcode (Effect VM) or zero-valued constraint rows that satisfy all constraints trivially.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Size Class*], [*Trace Rows*], [*Proof Size*]),
    [Small], [$2^(10)$ (1024)], [$tilde$18 KiB],
    [Medium], [$2^(12)$ (4096)], [$tilde$24 KiB],
    [Large], [$2^(14)$ (16384)], [$tilde$32 KiB],
    [XLarge], [$2^(16)$ (65536)], [$tilde$40 KiB],
  ),
  caption: [Proof size classes. All proofs within a class are indistinguishable by size.],
)

== CapTP Privacy Model

=== Swiss Numbers Are Executor-Internal

Swiss numbers (256-bit bearer secrets for sturdy refs) never cross trust boundaries in cleartext. They are:

- Generated and stored within the target executor's swiss table.
- Transmitted to authorized parties via sealed boxes (X25519 authenticated encryption).
- Never included in STARK public inputs (private witness when proving CapTP effects).
- Revocable by the executor at any time.

=== Session Privacy

CapTP sessions reveal communication patterns (who talks to whom) but not content. Note that the CapTP envelope is *cleartext over TLS*: sealed capabilities protect the payload, but the metadata (who is talking to whom about what cap-id) is leaky to any peer with TLS-decrypt access. The trust-model docstring at `wire/src/lib.rs` is honest about this.

=== `Authorization::CapTpDelivered` boundary

A CapTP-delivered Turn produces an on-ledger receipt at the receiving federation. The acceptance check requires the `introducer_pk` to derive from an entry in the local `KnownFederations` registry---without that, the receiver cannot verify the introducer signature against any trusted public key. The wire handler that formerly accepted `introducer_pk` from the wire message without cross-checking (`AUDIT-distributed-semantics.md` GAP-3) now requires registry presence.

== Predicate Proofs

The predicate substrate (@sec-predicate-substrate) provides `WitnessedPredicate { kind: BridgePredicate }` for arithmetic range/comparison proofs over committed facts (Gte/Lte/Gt/Lt/Neq/InRange). A `PredicateBuilder` API composes predicates like "age >= 18 AND country IN {US, CA, UK} AND tier >= 2" into a single STARK proof. The existing multi-step AIR already supports the underlying checks.

== Revocable Unlinkability

The fundamental tension: perfect unlinkability means no party can identify a specific credential. Revocation requires the *issuer* to identify credentials without verifiers being able to do so.

Resolution (Camenisch-Lysyanskaya style adapted to STARKs):

+ At issuance, the issuer assigns $"revocation_handle" = "Poseidon2"("issuer_secret", "credential_id")$.
+ The holder proves non-membership of their revocation handle in the revocation set---the handle itself is private witness.
+ To revoke, the issuer adds the handle. The next proof attempt fails.
+ The `NonRevocationAir` proves non-membership.

This achieves "issuer-revocable, verifier-unlinkable"---the strongest achievable property without trusted hardware.

== Comparison with Existing Systems

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, center, center, center, center),
    table.header([*Property*], [*Idemix*], [*BBS+*], [*AnonCreds*], [*Dregg (target)*]),
    [Unlinkable multi-show], [Yes], [Yes], [Yes], [Yes],
    [Selective disclosure], [Yes], [Yes], [Yes], [Yes],
    [Predicate proofs], [GE only], [No], [Limited], [Arbitrary (`WitnessedPredicate`)],
    [Issuer anonymity], [No], [No], [No], [Yes (ring)],
    [Post-quantum], [No], [No], [No], [Yes (STARK)],
    [Offline verify], [No], [Yes], [Partial], [Yes],
    [Proof size], [$tilde$2 KiB], [$tilde$1 KiB], [$tilde$5 KiB], [$tilde$48--80 KiB],
    [Prove time], [$tilde$50ms], [$tilde$10ms], [$tilde$100ms], [$tilde$200--500ms],
    [Verify time], [$tilde$30ms], [$tilde$5ms], [$tilde$50ms], [$tilde$10ms],
    [Programmable policy], [No], [No], [Limited], [Full Datalog + `WitnessedPredicate`],
  ),
  caption: [Privacy comparison. Dragon's Egg trades larger proofs for post-quantum security, programmable policy, and issuer anonymity.],
)

== Privacy Migration Path

*Phase 1 (in progress):* complete issuer unlinkability via `BlindedMerklePoseidon2StarkAir`.

*Phase 2:* remove `final_root` from public inputs; add `blinded_presentation_tag`. Highest-impact single change.

*Phase 3:* `PredicateBuilder` API over the existing circuit machinery, lifted into the unified `WitnessedPredicate { kind: BridgePredicate }` shape.

*Phase 4:* unified recursive proof. Single $tilde$48--80 KiB proof covering all components via the corrected verifier-AIR-as-leaf architecture (@sec-effect-vm).

*Phase 5:* revocable unlinkability via in-circuit revocation handle derivation.

*Phase 6:* federation privacy---turns encrypted (via the threshold-decryption substrate already real in `federation::threshold_decrypt`) or proved without revealing content to validators. See @sec-federation-privacy.

== Implemented Privacy Mechanisms

Beyond the credential pipeline, several privacy mechanisms are operational today:

=== Stealth Addresses

Stealth addresses use X25519 Diffie-Hellman for shared secret derivation and Ed25519 for the recipient key:

+ Sender computes ephemeral X25519 keypair $(r, R = r dot G)$.
+ Shared secret $s = "BLAKE3"("DH"(r, "recipient_scan_key"))$.
+ Stealth address derived: $"addr" = "recipient_spend_key" + "derive_ed25519"(s)$.
+ View tag $= s[0]$ enables fast scanning.

Recipients scan by checking view tag (skip 255/256 irrelevant), then attempting full derivation.

=== Pedersen Commitments

Value commitments use Pedersen over Ristretto with per-asset-type generators:

$ C = v dot G_"value" + r dot H + a dot G_"asset" $

The asset type $a$ is hidden inside the commitment.

=== Bulletproof Range Proofs

Range proofs use Bulletproofs over Ristretto to prove $v in [0, 2^(64))$ without revealing $v$. These are verified in the executor (not merely checked for non-empty bytes).

=== Dandelion++ Stem Routing

Transaction propagation uses Dandelion++ to obscure the originator's network identity. Stem phase: $p = 0.9$ forwarding, $tilde$10 hops expected before fluff. Fluff phase: standard gossip.

=== Delay Pool and Dummy Traffic

Intent fulfillments pass through a delay pool: a 30-second batching window with dummy traffic. Prevents timing correlation between intent broadcast and fulfillment response.

=== Commitment Tree Root History

Proofs may reference any recent Merkle root (not only the latest), with a sliding TTL window. Accommodates proof generation latency.

== Private Vickrey Auction (4-Phase Protocol)

Dragon's Egg implements a fully private Vickrey auction where no party learns any bid value, the payment amount, or the winner's identity. The protocol uses Pedersen commitments, threshold-encrypted bid revelation (via real `federation::threshold_decrypt`), garbled circuit evaluation, oblivious transfer, ring proofs, and stealth addresses:

+ *Bid commitment*: $C_i = b_i dot G + r_i dot H$ with STARK range proof.
+ *Threshold-encrypted bid revelation*: bidders encrypt openings under the federation's threshold public key; $t$-of-$n$ decryption required.
+ *Garbled circuit evaluation*: the committee evaluates a garbled Vickrey-outcome circuit. Output: only winner index + payment. Individual bids never leave the secure computation.
+ *Anonymous settlement*: payment via Pedersen commitment + ring proof over bidder set + stealth address derivation.

Security properties: bid privacy (no party learns bids except second-highest price); winner privacy (hidden behind ring proof); payment privacy (Pedersen + stealth); fairness (threshold $t$ prevents coalition deanonymization); correctness (garbled circuit evaluation is verifiable via STARK). Status: end-to-end auction execution tested with up to 64 bidders, using Poseidon2-based garbling (STARK-friendly), Simplest OT over Ristretto, and Schnorr-based linkable ring signatures.

== Federation Privacy <sec-federation-privacy>

Validators in a federation currently see all turn content in cleartext (cleartext-inside the executor, per `FieldVisibility::Committed`'s caveat). The target architecture provides layered privacy:

- *Layer 1 (Conflict Set Ordering)*: Bloom filter conflict sets enable ordering without content. A lightweight STARK proves nonce correctness and fee sufficiency.
- *Layer 2 (Threshold Decryption)*: turn bodies encrypted to the federation's threshold key, decrypted *after* ordering is finalized. The substrate is real in `federation::threshold_decrypt`; the executor consumption is in flight (`EncryptedTurn` in `turn/src/encrypted.rs` is well-tested in isolation but not yet consumed by the executor's production path).
- *Layer 3 (Full Validity Proof)*: full STARK proving conservation and authorization eliminates decryption entirely. Agents generate proofs; the federation only verifies.

The medium-term path is Layer 2: validium-style blind ordering. Agents submit encrypted turns alongside STARK proofs of valid state transition. Validators see nullifiers and proofs but not turn content.

== Post-Quantum Safety

All privacy additions maintain PQ safety where they cross trust boundaries:

- Blinding uses Poseidon2 (algebraic hash, no curves)
- Presentation randomization uses Poseidon2
- Non-revocation uses Poseidon2 Merkle proofs
- Predicates use BabyBear field arithmetic
- The recursive verifier uses FRI (hash-based)
- Blinded queues use Poseidon2 nullifiers (PQ-secure)
- Stealth addresses use X25519/Ed25519 (classical; confined within peer relationships)
- Pedersen/Bulletproofs use Ristretto (classical; value privacy only)
- Threshold decryption uses ChaCha20-Poly1305 + Shamir over GF(256) (classical; confined within federation)

The non-PQ components are confined within federation trust boundaries or peer relationships. Everything that crosses a trust boundary uses hash-based (PQ-secure) proofs. The PQ migration roadmap awaits lattice threshold signature standardization for BLS replacement.
