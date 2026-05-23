// =============================================================================
// Section 6: Federation and Consensus
// =============================================================================

= Federation and Consensus <sec-federation>

== Federation as Ordering Service (Not Execution)

The federation's role is deliberately minimal: agree on a total order of turns, deduplicate nullifiers, anchor Merkle roots, and provide discovery. The federation does NOT execute turns for sovereign cells---it verifies proofs and records commitments. State correctness is proved by the cell's own receipt chain.

For sovereign cells (the default), the federation stores only a 32-byte commitment. The cell's owner maintains full state, generates STARK proofs of valid transitions, and submits proofs + nullifiers to the federation. The federation verifies the proof and includes the new commitment in its attested root. This is the notary model: the federation witnesses that a valid transition occurred without knowing what the transition contained.

Attested roots serve as freshness anchors for offline verification. A verifier with a recent root can check any presentation without contacting the federation. There is no "call home" requirement.

== Consensus: Morpheus Adaptive BFT

Federation consensus uses Morpheus @morpheus adaptive BFT. The `MorpheusProcess<T>` provides:

- All-to-all transaction block production (high throughput in stable network)
- Leader blocks for ordering (periodic total-order checkpoints)
- Graceful degradation (falls back to single-leader when network is unstable)
- Proven safety and liveness (paper-verified BFT under partial synchrony)

A quorum certificate (QC) is a single aggregate BLS12-381 threshold signature---verification cost is constant regardless of committee size.

== Block Structure

Federation blocks commit to both ordering and execution:

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
FederationBlock {
    height, view, proposer, prev_hash,     // ordering metadata
    turns: Vec<TurnHash>,                   // ordered content
    revocations: Vec<RevocationEvent>,
    pre_state_root: [u8; 32],              // state before this block
    post_state_root: [u8; 32],             // state after execution
    note_tree_root: [u8; 32],              // note commitments
    nullifier_set_root: [u8; 32],          // spent nullifiers
    proposer_signature, block_hash,
}
```
]]

The state root is a composite: $"post_state_root" = "BLAKE3"("merkle_root" || "note_tree_root" || "nullifier_set_root")$. Voters reject blocks where `pre_state_root` disagrees with their local state, enabling divergence detection, light clients, and fraud proofs.

== Federation Lifecycle

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, left),
    table.header([*Size*], [*f*], [*Threshold*], [*Use Case*]),
    [1], [0], [1], [Solo agent (self-signed log, no BFT)],
    [3], [0], [3], [Development/testing (no fault tolerance)],
    [4], [1], [3], [Minimum BFT (one faulty node tolerated)],
    [7], [2], [5], [Production small federation],
    [13+], [4+], [9+], [Production large federation],
  ),
  caption: [Minimum viable federation sizes. A 1-node federation provides a verifiable execution log without Byzantine tolerance.],
)

== Proof-Carrying State

=== Receipt Chains as Primary State

Every committed turn produces a `TurnReceipt` containing pre/post state hashes, effects hash, and computron cost. These receipts chain: $"receipt"[n]."post_state_hash" = "receipt"[n+1]."pre_state_hash"$. The chain of receipts IS the agent's state proof---anyone can verify from genesis without contacting a federation.

=== IVC Compression

The IVC layer compresses an arbitrary-length receipt chain into a constant-size proof. A verifier needs only:

+ The `IvcProof` (proves the chain is valid from genesis).
+ The current state commitment (proves what state the chain produced).
+ A nullifier non-membership proof (proves no double-spends).

=== Federation Exit

An agent leaves a federation by simply stopping submission of nullifiers. Their proof chain is portable---it proves state validity from genesis without referencing federation-specific data. The agent can join another ordering service (presenting their chain as genesis state) or operate standalone.

== Cross-Federation Protocol

=== Discovery

Federations discover each other through relay peering. Each federation publishes a signed `FederationManifest` containing its genesis root, current members, relay endpoints, and supported capabilities. Relays exchange manifests during inter-relay QUIC handshake.

=== Federation Identity and Rotation

Federation identity is $"federation_id" = "BLAKE3"("genesis_attested_root")$---a fixed identifier derived from genesis. For key rotation, a succession chain provides continuity: each entry records an epoch transition signed by the old committee, proving derivation from the known genesis.

=== Cross-Federation Atomic Swaps

Cross-federation atomic operations use `ConditionalTurn` + `ProofObligation`:

+ Alice (Fed A) creates a `ProofObligation` with a bonded stake.
+ Bob (Fed B) creates a matching obligation.
+ Both create `ConditionalTurn`s that execute only upon receiving a valid STARK proof from the other federation.
+ Proofs are delivered via relay peering.
+ If either proof fails to arrive before timeout, the corresponding turn expires and the non-performing party's bond is slashed.

The failure mode is safe: slashing compensates the honest party. No cross-federation trust is required---only verification of proofs against the remote federation's attested root.

=== Equivocation Detection

When two relays from the same federation present conflicting attested roots at the same height, any observer can construct an equivocation proof (two valid QCs over different roots at the same height). This triggers: freeze of cross-federation operations, broadcast to peered federations, and requirement for the equivocating federation to resolve via slashing.

== Cross-Federation Routing

Authority and reachability are orthogonal. A `CapabilityRef` encodes _permission_ but not _location_. Routing uses a three-layer design:

+ *RoutingHint as metadata, not in CapabilityRef.* The `RoutingDirective` (emitted by three-party introduction) carries an optional `RoutingHint` with federation ID and relay endpoints. Hints are mutable operational state, not part of capability identity or hash.

+ *Relay-mediated cross-federation delivery.* When a node cannot locally resolve a CellId, it queries its relay. The relay maintains a federation peer table and establishes QUIC streams to remote federation relays for forwarding.

+ *CellId-hash overlay for privacy (progressive enhancement).* For cells that opt into private routing, their relay publishes $H("CellId" || "routing_nonce")$ to a lightweight gossip overlay. Senders holding the nonce (delivered at introduction time) can compute the lookup key without revealing the CellId to the overlay.

CapabilityRef is unchanged. Routing hints are operational, not committed---they do not appear in Merkle proofs or sealed boxes.

== Federation Privacy <sec-federation-privacy>

Federation validators currently see all turn content in cleartext. The target architecture provides layered privacy:

*Layer 1: Conflict Set Ordering.* Bloom filter conflict sets enable ordering without content. A lightweight STARK proves nonce correctness and fee sufficiency. The federation orders and detects conflicts without seeing turn bodies.

*Layer 2: Threshold Decryption.* Turn bodies are encrypted to a federation threshold key. Decrypted AFTER ordering is finalized. Protects against MEV and front-running.

*Layer 3: Full Validity Proof (future).* Full STARK proving conservation + authorization eliminates the need for decryption entirely. Agents generate proofs; federation only verifies.

The recommended medium-term approach is validium-style blind ordering: agents submit encrypted turns alongside STARK proofs of valid state transition. Validators see nullifiers and proofs but NOT turn content or state. This aligns with Pyana's existing receipt-chain model where `StateTransitionAir` already proves hash continuity.

== Coordination Primitives

=== Bounded Counters (Stingray)

Concurrent resource spending uses bounded counters adapted from Stingray @stingray: $"slice"(i) = "balance" dot (f+1)/(2f+1)$. Each silo debits locally up to its slice without coordination. The invariant $sum_i "spent"(i) <= "balance"$ holds even under $f$ Byzantine silos.

=== Atomic Coordination (2PC)

Cross-silo turns use two-phase commit with threshold quorum certificates. Fast unlock releases locked budget immediately upon abort.

=== Causal Ordering (DAG)

Non-atomic operations use a causal DAG of hash-linked events, providing partial ordering without global consensus.

== External Chain Interop

Pyana provides three interop bridges, each using proof translation rather than consensus bridging:

=== EVM Bridge (Ethereum/Base)

SP1 wraps Pyana STARK proofs in Groth16 for on-chain verification at ~200K gas. The bridge includes an incremental Merkle tree for deposits ($O(log n)$ insertions), a VK registry with governance-controlled parameter updates, and commit-reveal frontrunning protection. *Status:* Architecture complete; guest program regeneration against Plonky3 backend in progress.

=== Mina Bridge

Native Pickles recursion via the STARK-in-Pickles pipeline. A Pyana STARK proof is verified inside a Kimchi circuit, producing a Pickles recursive proof compatible with Mina's verification infrastructure. Assisted recursion is operational. This enables Mina zkApps to natively verify Pyana state transitions.

=== Midnight/Cardano Bridge

Observation-based bridging using the same pattern as Midnight's Cardano bridge. The DSL's ZKIR v3 backend compiles Pyana constraint programs directly into Midnight-compatible contracts, enabling a Midnight validator to verify Pyana proofs without a trust bridge. This is a proof-translation layer, not a consensus bridge.

== Network Layer

Message dissemination uses Plumtree-inspired @plumtree hybrid push over QUIC: eager push (degree 3) for spanning-tree delivery, lazy push (`IHave` notifications) for redundancy, and periodic Bloom filter anti-entropy. All inter-silo communication uses QUIC (via Quinn) with multiplexed streams and 0-RTT resumption. Transaction propagation additionally uses Dandelion++ @dandelion stem routing for network-level privacy (see Section 5).
