// =============================================================================
// Section 3: Authorization Semantics
// =============================================================================

= Authorization Semantics

== Multi-Modal Authorization

Dragon's Egg supports six authorization modes, each suited to a different trust context:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Mode*], [*Mechanism*], [*Use Case*]),
    [`Signature`], [Ed25519 over canonical v3 turn message], [Standard agent-initiated turns],
    [`Proof`], [STARK proof of authorization (Datalog evaluation)], [Cross-boundary, privacy-preserving],
    [`Breadstuff`], [Macaroon HMAC chain with caveats], [Attenuated delegation within a trust domain],
    [`Bearer`], [`BearerCapProof` (signed or STARK delegation chain)], [One-shot tokens, tickets, ephemeral access],
    [`CapTpDelivered`], [Handoff certificate + recipient presentation + swiss enliven], [Cross-vat CapTP-delivered messages producing on-ledger Turns],
    [`Custom { predicate, descriptor }`], [App-defined: `WitnessedPredicate` proves authorization], [Multisig, DAO-quorum, time-locked, capability-conditional, compute-attested],
  ),
  caption: [Authorization modes. A turn declares which mode it uses; the executor dispatches accordingly. `Authorization::Unchecked` is, in current production, only allowed through a CI-guarded carve-out list (Stage 8 P2.F).],
)

The Bearer mode carries a `BearerCapProof`: either a signed Ed25519 delegation chain (fast, non-private) or a STARK proof that a valid delegation chain exists (private, post-quantum). The choice is made at delegation time based on the desired privacy/performance tradeoff.

=== `Authorization::CapTpDelivered`

CapTP-delivered messages produce algebraically-bound Turns on the receiving ledger. When federation $F_2$ receives a CapTP message originating from federation $F_1$ for cell `bob_cell`, the wire layer constructs a Turn with `Authorization::CapTpDelivered { introducer, recipient_pk, handoff_cert, swiss_proof, ... }`. The executor verifies:

+ The handoff certificate's Ed25519 introducer signature against the entry in `known_federations` for $F_1$.
+ The recipient's presentation signature against `recipient_pk`.
+ The swiss-bytes enliven against the local swiss table.
+ The certificate's `max_uses` counter is not exhausted; if `max_uses == None`, replay protection comes from the `HandoffError::ReplayDetected` ledger (per-cert nonce-seen set).

The resulting Turn produces a real `TurnReceipt`---closing the integration loop "every CapTP mutation has a corresponding on-chain receipt." The prior gap (CapTP-routed Turns were pushed to a `pending_captp_turns` queue that was never drained) is closed by `CapTpState::process_pending_turns` invoked on every executor tick.

=== `Authorization::Custom { predicate, descriptor }`

The new `Custom` variant lets apps define their own authorization modes purely through the `WitnessedPredicate` registry, without kernel changes:

```rust
Authorization::Custom {
    predicate: WitnessedPredicate,           // proves authorization
    descriptor: AuthModeDescriptor,           // (vk_hash, human_name, semver, boundary_contract)
}
```

The executor's verification path:

+ *Descriptor consistency*: if `predicate.kind == Custom { vk_hash }`, require `vk_hash == descriptor.vk_hash`; for built-in kinds (`Dfa`, `Temporal`, etc.) require `descriptor.vk_hash == canonical_vk_hash_for(kind)`.
+ *Registry lookup*: resolve the verifier via `WitnessedPredicateRegistry::lookup(descriptor.vk_hash)`. If the federation has not registered the verifier, reject with `TurnError::AuthModeNotRegistered { vk_hash }`---no silent fallback.
+ *Input binding*: compute the canonical action signing message `M = canonical_signing_message(action, position, federation_id, turn_nonce)`---the same message the `Signature` path uses---and bind it as the predicate's input.
+ *Verifier call*: `verifier.verify(commitment, input = M, proof_bytes = action.witness_blobs[predicate.proof_witness_index])`.
+ *Effect-mask check*: if the descriptor declares an `allowed_effects: Option<EffectMask>`, the same facet-attenuation check that `Bearer` performs applies.

This single variant subsumes a class of formerly-hardcoded modes: multisig (two `BridgePredicateProof`s wrapped in `WitnessedPredicate { kind: Custom { vk_hash: multisig_vk } }`), DAO-quorum (a STARK proving $k$-of-$n$ signature threshold satisfied), time-locked (a `Temporal` predicate proving block height $>=$ threshold), capability-conditional (a `MerkleMembership` predicate against the actor's c-list), compute-attested (a `Custom { vk_hash }` proof from an external zkVM). The auth mode becomes app-extensible.

== Capabilities as Datalog Facts

Authorization state is encoded as a set of Datalog facts. A fact is a ground atom $"fact" := "predicate"("term"_1, ..., "term"_k)$. Attenuation transforms a fact set $F$ into $F' subset.eq F$ by removing facts. The HMAC chain in a macaroon token makes removal of caveats cryptographically impossible---attenuation is irreversible.

== Dual-Mode Evaluation

The same Datalog rules yield the same answer in two modes:

- *Trusted mode* (local evaluation): cost $tilde 8 mu s$. Used within a trust boundary.
- *Trustless mode* (STARK proof): the prover generates a STARK proof that Datalog evaluation produced `allow`. Cost $tilde 64 mu s$ prove, $tilde 438 mu s$ verify.

Both modes evaluate identical rules over identical data. The proof attests to the computation, not to a separate protocol.

== Predicate Substrate <sec-predicate-substrate>

Authorization is one consumer of a broader predicate substrate that spans slot caveats, per-action preconditions, capability caveats, and now `Authorization::Custom`. The substrate is organized in two halves: a 21+ variant `StateConstraint` vocabulary for cleartext or commitment-bearing predicates, and a unified `WitnessedPredicate` shape for predicates that carry a witness/proof against a commitment.

=== `StateConstraint`: 21+ variants

Slot caveats (declared per-cell in the `CellProgram`, enforced by the executor on every state-modifying turn) span the following families:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Family*], [*Variants*]),
    [Static post-state], [`FieldEquals`, `FieldGte`, `FieldLte`, `SumEquals`],
    [Transition], [`WriteOnce`, `Immutable`, `Monotonic`, `StrictMonotonic`, `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`, `AllowedTransitions`],
    [Temporal/network], [`FieldGteHeight`, `FieldLteHeight`, `TemporalGate`, `MonotonicSequence`],
    [Flow conservation], [`SumEqualsAcross`, `BoundDelta` (cross-cell, $gamma$.2)],
    [Sender-bound], [`SenderAuthorized { Public | Blinded }`, `CapabilityUniqueness`],
    [Rate], [`RateLimit`, `RateLimitBySum`],
    [Witnessed (proof-bearing)], [`TemporalPredicate { dsl_hash }`, `Witnessed(WitnessedPredicate)`],
    [Composition], [`AnyOf`, `Custom { ir_hash, descriptor, reads }`],
    [Preimage], [`PreimageGate { commitment_index }`],
  ),
  caption: [21+ slot caveat variants in `StateConstraint`. The legacy `QueueConstraint` vocabulary in `storage::programmable` is aliased to these post-Lane-G Phase 1; storage primitives become *cell-program patterns* expressed in this vocabulary (see @sec-storage-as-cell-programs).],
)

=== `WitnessedPredicate`: the unification

Predicates that ship a witness/proof bound to a commitment unify under a single shape:

```rust
pub struct WitnessedPredicate {
    pub kind: WitnessedPredicateKind,        // Dfa, Temporal, MerkleMembership,
                                              // BlindedMembership, BridgePredicate,
                                              // PedersenEquality, Custom { vk_hash }
    pub commitment: [u8; 32],
    pub input_ref: InputRef,                  // Slot | Witness | PublicInput | Sender
    pub proof_witness_index: u8,
}
```

Each `WitnessedPredicateKind` registers a verifier; the registry is the only thing that grows when a new kind lands. The pattern mirrors macaroon `CaveatType`'s existing polymorphic-registry design: closed enum for platform kinds, `Custom { vk_hash }` escape for app-defined kinds.

Three surface variants embed `WitnessedPredicate`:

+ `StateConstraint::Witnessed(WP)` --- slot caveats that depend on a witness.
+ `Preconditions::witnessed: Vec<WP>` --- per-action preconditions that depend on a witness.
+ `CapabilityCaveat::Witnessed(WP)` --- capability caveats that require the holder to produce a matching proof.

After the unification, fifteen previously-distinct witness-attached predicate shapes collapse into one substrate: `StateConstraint::TemporalPredicate`, `StateConstraint::SenderAuthorized { BlindedSet }`, `PortableNoteProof.spending_proof`, `PeerStateTransition.transition_proof`, `BridgePresentationProof`, `BridgePredicateProof`, the DFA-classification predicate, the Merkle-membership gadget, the blinded-set non-revocation proof, the Pedersen `ConservationProof`, the Bulletproof `RangeProof`, and the `EvmCredentialProof`. The same registry dispatch serves every surface.

What the unification does *not* absorb: per-action static preconditions (`SlotEquals`, `NonceAtLeast`---no commitment, no proof), the capability authority lattice (`AuthRequired::is_narrower_or_equal`---order-theoretic, not witness-bearing), federation aggregate signatures (`AttestedRoot::has_quorum`---multi-party-signature algebra, not STARK), macaroon caveats (already polymorphic over `Access`), CapTP swiss enliven (possession, not knowledge of a witness). Those remain parallel.

== Capability Derivation and Revocation

=== The Capability Derivation Tree

In seL4 @sel4, every capability exists in a _Capability Derivation Tree_ (CDT): a tree rooted at the original untyped memory capability, where each child is derived from its parent. The kernel traverses this tree synchronously to revoke an entire subtree in $O(n)$ time.

Dragon's Egg maintains a distributed analog. Each delegation step records:

$ "DelegationEdge" = ("parent": "CapHash", "child": "CapHash", "attenuation": Delta, "epoch": "u64") $

These edges form a tree committed to a Merkle structure. The CDT is not enforced by a kernel---it is _proved_ by the delegator at each step.

=== The Duality: Enforce vs. Prove

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Property*], [*seL4 (kernel-enforced)*], [*Dregg (proof-carried)*]),
    [Tree structure], [In-kernel data structure], [Merkle-committed proof tree],
    [Revocation], [Kernel walks tree synchronously], [Verifiable revocation claim],
    [Latency], [Instantaneous (same address space)], [Bounded staleness],
    [Distribution], [Single machine], [Cross-federation],
    [Trust model], [Kernel is TCB], [Hash function is TCB],
    [Verification], [Hardware-enforced access], [STARK proof of non-membership],
  ),
  caption: [CDT duality: seL4 ENFORCES the tree; Dregg PROVES the tree.],
)

In seL4, revocation is authoritative because the kernel IS the tree---traversal and deletion are the same operation. In Dragon's Egg, the tree is a claim that anyone can verify: the delegator proves their capability descends from a valid root, and the revoker proves non-membership in the current valid set.

=== Delegation: Snapshot + Refresh

Delegation follows a snapshot-refresh model with bounded staleness. A child cell receives a point-in-time snapshot of its parent's c-list:

$ "DelegatedRef" = ("source", "snapshot": ["CapabilityRef"], "epoch", "refreshed_at", "max_staleness") $

The child acts offline using the snapshot. Acceptors (remote verifiers) reject presentations where $"now" - "refreshed_at" > "max_staleness"$. This creates a configurable tradeoff between availability and revocation freshness.

=== RevocationChannel: Opt-in Synchrony

For applications requiring instant revocation, Dragon's Egg provides an opt-in synchrony primitive: the _RevocationChannel_. A capability enrolled in a RevocationChannel is checked against a real-time revocation feed before acceptance. This restores seL4-like instant revocation at the cost of requiring channel liveness.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, center),
    table.header([*Mode*], [*Revocation Latency*], [*Requires Liveness*], [*Analogy*]),
    [No check], [$infinity$ (never revoked)], [No], [Bearer token],
    [Epoch-stale], [$<= "max_staleness"$], [No], [OCSP stapling],
    [Channel-sync], [Real-time], [Yes (channel)], [CRL push],
    [Kernel-sync], [Instantaneous], [Yes (kernel)], [seL4 CDT],
  ),
  caption: [Revocation modes from weakest to strongest. Dregg supports the first three; seL4 achieves the fourth by being a kernel.],
)

Two revocation mechanisms today exist disjointly in the codebase (`derivation.rs` for verifier-side CDT, `revocation_channel.rs` for executor-side $O(1)$ lookup); a CDT revocation does not trip a channel. Unifying them is open question 7 in BOUNDARIES.md.

== Provable CapTP Effects

Four CapTP operations are encoded as provable effects in the Effect VM, enabling STARK proofs of protocol correctness:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Effect*], [*What the STARK Proves*], [*Public Inputs*]),
    [`ExportSturdyRef`], [Swiss number correctly registered; capability exported with valid EffectMask], [Target hash, export epoch],
    [`EnlivenRef`], [Sturdy ref resolved; swiss number valid; live reference correctly issued], [Session ID, import slot],
    [`DropRef`], [Reference correctly released; refcount decremented; session epoch valid], [Session epoch, export ID],
    [`ValidateHandoff`], [Handoff certificate valid: Ed25519 signature verifies, recipient matches, one-time use], [Introducer key, recipient key],
  ),
  caption: [CapTP effects as provable operations. Each can be composed with authorization proofs into a single STARK. Verification that these four are *real* Merkle membership and not tautological is in-flight per Stage 7 cont P1.C.],
)

== Generalized Intent Solver

=== The Discovery Problem

Object-capability systems solve authorization but not discovery: if you need a capability to communicate, how do you find someone who holds the capability you need? Traditional answers (directories, service registries) violate the principle of least authority by publishing capability inventories.

=== Five Item Types

The intent solver operates over 5 exchangeable item types:

+ *Fungible tokens*: Computrons, stablecoins, LP tokens (divisible, interchangeable).
+ *Non-fungible tokens*: Unique identifiers (cell IDs, credential hashes).
+ *Capabilities*: Attenuated bearer tokens (service access, compute budgets).
+ *Compute*: CPU/GPU time commitments (inference slots, proof generation).
+ *Data*: Content-addressed blobs (models, datasets, query results).

=== Ring Trades

When no bilateral match exists, the solver finds multi-party cycles. A ring trade $(A -> B -> C -> A)$ satisfies all three parties simultaneously. The solver uses Johnson's algorithm bounded to cycle length $k <= 5$ over a directed compatibility graph.

=== Trustless 7-Layer Protocol (Real Threshold Decryption)

Intent fulfillment follows a 7-layer trustless protocol: SUBMIT (threshold-encrypted), BATCH (consensus-determined boundary), DECRYPT (threshold ceremony after batch seal), SOLVE (open competition with bonds), PROVE (STARK validity proof per solution), SELECT (deterministic scoring + challenge window), SETTLE (atomic compound turn). Front-running is structurally impossible: intents are encrypted until after the batch boundary is finalized.

The threshold-encryption substrate is *real* and *production-wired*: `federation::threshold_decrypt` provides Shamir-over-GF(256) secret sharing combined with ChaCha20-Poly1305 AEAD; `intent::trustless` consumes the same `combine_shares` primitive; `node::state::trustless_intent_engine` wires the full pipeline into the production node path. The prior gap (a cleartext `set_decrypted_intents` side-channel that bypassed the threshold ceremony) is replaced---validators now contribute real decryption shares to a per-batch `ThresholdCiphertext`, the canonical `combine_shares` is called once $t$ shares accumulate, and the resulting cleartext intents flow into the solver auction. See @sec-intents for the full protocol.

== Nameservice as Capability Discovery <sec-nameservice-auth>

Nameservice resolution is a form of authorization: resolving a name yields a capability reference (specifically, a sturdy ref). The petname architecture (local petnames, edge names, proposed names) provides human-readable paths to capabilities without global naming authority. Resolution through the DFA-governed namespace requires proving route validity and ACL satisfaction---making name lookup itself a provable operation, expressed as a `WitnessedPredicate { kind: Dfa }`.

== Sealer/Unsealer Pairs

E's sealer/unsealer primitive enables rights amplification: the sealer encrypts data that only the unsealer holder can read. Dragon's Egg implements this with X25519 Diffie-Hellman + ChaCha20-Poly1305 AEAD + a BLAKE3 commitment binding `(cap_hash, ephemeral_public, nonce)`. Each seal uses a fresh ephemeral X25519 keypair, providing per-message sender-side forward secrecy. The recipient's `unsealer_secret` is the long-term secret; compromise of `unsealer_secret` decrypts all prior sealed boxes to that pair.

=== Boundary contract

Boundary contract (per BOUNDARIES.md §2.4):

- *Cleartext-inside*: sender (ephemeral DH key holder) and recipient (`unsealer_secret` holder).
- *Commitment-inside*: anyone with the `pair_id` (a deterministic recipient identifier). Sees the `pair_id` and ciphertext size and timing.
- *Out-of-band*: anyone without the ciphertext.

Three known caveats: (a) `pair_id` is deterministic, so anyone who has ever seen the recipient's `SealerPublic` can link every seal to that recipient; (b) ciphertext size is not padded; (c) sealing a faceted cap (`FACET_TRANSFER_ONLY`) and unsealing it formerly produced an *unfaceted* cap---the v3 sealed-plaintext format (soundness sweep) now encodes `allowed_effects` to close the authority-amplification surface.

=== Partition-Tolerant Offline Transfer

The critical use case: transferring a capability to a party that is currently offline or unreachable. The sender seals the capability under the recipient's `sealer_public`; the sealed box can traverse untrusted channels; the recipient unseals on connection. This enables offline capability delegation that neither UCAN (requires online chain verification) nor traditional capability systems (require live introduction) support.

When the recipient is another sovereign cell on a different federation, the sealed box composes with `peer_exchange` (@sec-peer-exchange) for federation-bypass: the cell receives the cap, applies the granted authority via signed peer-exchange transitions, and only publishes to the federation when reconnection is desired.
