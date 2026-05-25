// =============================================================================
// Section 7: Capability Transport Protocol
// =============================================================================

= Capability Transport Protocol <sec-captp>

== Overview

CapTP is the network protocol by which cells exercise capabilities across trust boundaries. It is OCapN-lineage: sturdy references for offline sharing, distributed garbage collection across federations, three-party handoff for capability delegation without mutual connectivity, promise pipelining with eventual references, and store-and-forward for partition-tolerant delivery. Four effects in the Effect VM are CapTP-native, enabling STARK proofs of protocol correctness.

The integration-complete Silver Vision invariant: *a CapTP-delivered message produces a real `TurnReceipt` on the receiving cell's ledger.* This is the responsibility of `Authorization::CapTpDelivered`, which makes CapTP messages route through the executor's standard verification path and produce on-ledger receipts---closing the prior gap where the wire layer pushed CapTP turns to a `pending_captp_turns` queue that was never drained. The mirror invariant "every CapTP mutation has a corresponding on-chain receipt" is now structural.

== Sturdy References

A sturdy reference is a durable, serializable capability URI that survives disconnection and enables offline sharing:

$ "pyana://" chevron.l "federation_id" chevron.r "/" chevron.l "cell_id" chevron.r "/" chevron.l "swiss_number" chevron.r $

The swiss number is a cryptographic bearer secret (256 bits of entropy). Possession of the swiss number IS authorization---no additional proof is needed to _enliven_ the reference. The swiss table maps swiss numbers to live capabilities within a federation node.

=== Enlivenment Protocol

To convert a sturdy ref into a live reference:

+ Parse the `pyana://` URI to extract federation ID, cell ID, and swiss number.
+ Connect to the federation (via QUIC transport, identified by federation ID).
+ Present the swiss number to the target node's swiss table.
+ If valid: receive a live reference token (an import entry in the CapTP session).
+ If invalid: receive a rejection (the swiss number was revoked or never existed).

=== Security Properties

- *Bearer semantics*: No identity check beyond swiss number possession. The URI itself is the capability.
- *Unforgeability*: Swiss numbers are 256-bit random secrets. Guessing probability is $2^(-256)$.
- *Revocability*: The holder can remove the swiss table entry at any time. Outstanding URIs become inert.
- *Offline sharing*: URIs travel via any channel (QR code, email, BLE, file, NFC) without requiring connectivity to the federation during sharing.

== CapTP Sessions

A `CapSession` tracks bidirectional capability exchange between two peers:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Component*], [*Role*]),
    [Exports], [Capabilities we make available to the remote peer],
    [Imports], [Capabilities the remote peer has made available to us],
    [Promises], [Pending asynchronous resolutions (eventual references)],
    [Epoch], [Monotonic generation counter; stale messages rejected],
  ),
  caption: [CapTP session state. Each peer maintains one session per remote.],
)

Session epochs prevent replay attacks: a reconnecting peer establishes a new session with incremented epoch. Messages carrying a stale epoch are rejected without processing.

=== Promise Pipelining

When a cell sends a message to a remote capability, it receives an `EventualRef`---a promise of future response. Subsequent messages can be addressed to the eventual ref _before it resolves_, enabling pipelined execution:

$ "send"(A, B, "msg"_1) -> "promise"_1 \
  "send"("promise"_1, C, "msg"_2) -> "promise"_2 $

The second send is queued at $B$'s vat until $"promise"_1$ resolves, then forwarded to the result. This eliminates round-trip latency in multi-hop capability chains. The federation delivers pipelined messages in causal order.

== Distributed Garbage Collection

When federation $A$ exports a capability to federation $B$:

+ $A$'s `ExportGcManager` records that $B$ holds a reference (increments refcount).
+ When $B$ no longer needs the capability, $B$ sends a `DropRef` message to $A$.
+ $A$ decrements the reference count.
+ At zero references, $A$ may revoke the export (removing the swiss table entry).

=== GC Consistency

The GC protocol is _conservative_: a capability is only collected when ALL remote references are explicitly dropped. Crash recovery uses epoch-based reconciliation:

- After reconnection, the new session starts with a clean import/export table.
- The remote re-imports any capabilities it still holds (re-incrementing counts).
- Capabilities not re-imported within the reconciliation window are considered dropped.

This avoids the "lost decrement" problem where a crash after import but before acknowledgment could leak a reference indefinitely.

== Three-Party Handoff

The handoff protocol enables offline capability transfer to a third party without requiring simultaneous connectivity among all three participants:

+ *Introducer* (Alice) holds a capability at target federation $F$.
+ Alice registers a swiss entry at $F$ designated for recipient Bob.
+ Alice creates a signed `HandoffCertificate` naming Bob's public key.
+ The certificate travels out-of-band (any channel---QR code, encrypted message, file).
+ Bob presents the certificate to $F$.
+ $F$ validates Alice's Ed25519 signature and Bob's identity.
+ $F$ creates a routing entry: Bob now holds a live reference.

=== Handoff Security

- *Non-transferable*: The certificate names a specific recipient. Presenting it with the wrong key fails.
- *Unforgeable*: Requires Alice's Ed25519 private key. No party can forge a valid certificate.
- *One-time*: Each certificate is consumed on presentation. Replay is detected via `HandoffError::ReplayDetected` against a per-cert nonce-seen ledger, or via `max_uses` decrement at swiss enliven when bounded.
- *Offline*: Neither Alice nor Bob need be online simultaneously. The certificate is a proof object.
- *Trust root*: validation requires the introducer's public key to derive from an entry in the receiver's `KnownFederations` registry (the `FederationId` $arrow.r$ public-key registry). Without registry presence, the introducer-signature check fails closed.

=== Cross-federation invocation flow

When Alice on federation $F_1$ introduces Bob on federation $F_2$ to a capability at $F_2$:

+ Alice (or her cipherclerk's SDK) constructs a `HandoffCertificate` over `{target_federation: F_2, target_cell, recipient_pk: pk_B, permissions, allowed_effects, expires_at, max_uses, nonce, swiss}` and signs with $"pk"_A$.
+ The certificate travels out-of-band (any channel).
+ Bob presents the certificate to $F_2$ via a `PresentHandoff` CapTP message, signing a `HandoffPresentation` binding (nonce, target_cell, target_federation).
+ $F_2$ verifies:
  - The introducer signature against `pk_A`, which is looked up in $F_2$'s `KnownFederations` registry for `cert.introducer` (a `FederationId`).
  - The recipient signature against `recipient_pk`.
  - Expiry and `max_uses` not exhausted; nonce not in the seen-set.
  - The swiss-bytes enliven against $F_2$'s local swiss table.
+ $F_2$ constructs a Turn with `Authorization::CapTpDelivered` and routes it through the standard executor path. The Turn produces a real `TurnReceipt`.
+ The receipt is attested via `FederationReceipt` (if the committee runs one) and is portable back to $F_1$ as proof that the introduction was honored.

== Store-and-Forward

For partition-tolerant delivery, CapTP includes a store-and-forward layer:

+ Messages are encrypted to the recipient's X25519 public key.
+ Encrypted messages are stored in the recipient's MerkleQueue inbox.
+ The relay operator cannot read message content (only ciphertext).
+ Messages persist until the recipient comes online and dequeues them (or TTL expires).

The store-and-forward layer integrates with the storage economics model (Section 8): sender pays a deposit covering message storage cost, refunded upon recipient processing.

=== Forward Secrecy

Each message uses an ephemeral X25519 keypair for Diffie-Hellman key exchange with the recipient's long-term key. The ephemeral private key is discarded after encryption. Compromising the relay reveals only ciphertext; compromising the recipient's key after message delivery does not reveal messages encrypted under prior ephemeral keys.

== Four Provable Effects

The Effect VM (Section 4) includes four CapTP-native effects that can be proven in a single STARK:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Effect*], [*Proves*], [*Public Inputs*]),
    [`Send`], [Message correctly dispatched to target], [Target hash, message hash],
    [`Introduce`], [Handoff certificate correctly constructed], [Introducer, recipient, target hash],
    [`Resolve`], [Promise resolved with correct value], [Promise ID, resolution hash],
    [`DropRef`], [Reference correctly released], [Session epoch, export ID],
  ),
  caption: [CapTP effects in the Effect VM. Each can be composed with authorization proofs.],
)

A turn that exercises a remote capability generates a STARK proof covering: (1) the cell had authority to exercise the capability (authorization proof), (2) the CapTP effect was correctly constructed (protocol proof), and (3) the turn's state transition is valid (conservation proof). All three are composed into a single proof via `compose_chain`.

== Protocol Invariants

CapTP maintains the following invariants, each verifiable without trusting the executor:

*Capability confinement*: A capability cannot be accessed without knowledge of its swiss number. The swiss table is the only lookup path; brute-force is infeasible at 256 bits.

*Handoff integrity*: A handoff certificate cannot be forged without the introducer's Ed25519 private key. Validation is independently verifiable by any party holding the introducer's public key.

*Session freshness*: Messages with stale epochs are rejected. Epoch monotonicity prevents replay of messages from prior sessions.

*GC safety*: A capability is never prematurely collected. The conservative protocol errs toward leaking (harmless) rather than premature revocation (capability loss).

== Trust Model

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Component*], [*Trust Level*]),
    [Swiss table maintenance], [Executor-trusted (federation maintains mapping)],
    [Session state (import/export)], [Executor-trusted (peer tracking)],
    [Distributed GC (refcounts)], [Executor-trusted (incorrect GC leaks or over-revokes)],
    [Handoff certificates], [Trustless (Ed25519 signature verification)],
    [Store-and-forward encryption], [Trustless (X25519 authenticated encryption)],
    [Effect VM proofs], [Trustless (STARK verification)],
  ),
  caption: [CapTP trust model. Executor-trusted components are verified via federation replication; trustless components are independently verifiable.],
)

The path toward full trustlessness: as the Effect VM proves more CapTP operations, the executor-trusted surface shrinks. The target architecture proves swiss table lookups and session state transitions in the STARK, reducing the federation's role to ordering and availability. Verification that the four CapTP AIR variants (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`) are *real* Merkle membership and not tautological is in-flight per Stage 7 cont P1.C.

== Cross-Vat / Cross-Federation Composition

The cross-federation invocation flow above (§Handoff Security) is the canonical example of *proof-carrying capability* across trust boundaries:

- The bearer secret (swiss number) lives only at $F_2$ and never crosses cleartext.
- The handoff certificate is unforgeable without Alice's key.
- The receiver's `KnownFederations` registry is the trust root for the introducer's identity.
- The resulting Turn is algebraically bound to $F_2$'s federation context via `Authorization::CapTpDelivered`'s domain-separated canonical message including `federation_id`.

The Silver Vision e2e verification spec (`SILVER-VISION-E2E-VERIFICATION.md`) names the bench against which this end-to-end story is judged: *two federations, one bearer cap, one CapTP delivery, one Turn at the receiver, one receipt, one `AttestedRoot`, one `WitnessedReceipt` chain export, one independent verifier verdict.* Charlie (a third-party verifier with no shared state, holding only $F_1$'s and $F_2$'s committee descriptors out-of-band) accepts or rejects the joint record from cold.
