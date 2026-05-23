// =============================================================================
// Section 6: Federation and Consensus
// =============================================================================

= Federation and Consensus <sec-federation>

== Federation as Ordering Service (Not Execution)

The federation's role is deliberately minimal: agree on a total order of turns, deduplicate nullifiers, anchor Merkle roots, and provide discovery. The federation does NOT execute turns for sovereign cells---it verifies proofs and records commitments. State correctness is proved by the cell's own receipt chain.

For sovereign cells (the default), the federation stores only a 32-byte commitment. The cell's owner maintains full state, generates STARK proofs of valid transitions, and submits proofs + nullifiers to the federation. The federation verifies the proof and includes the new commitment in its attested root. This is the notary model: the federation witnesses that a valid transition occurred without knowing what the transition contained.

Attested roots serve as freshness anchors for offline verification. A verifier with a recent root can check any presentation without contacting the federation. There is no "call home" requirement.

== Consensus: Blocklace and Cordial Miners

Federation consensus uses the Blocklace @blocklace protocol with Cordial Miners $tau$ for total ordering. The Blocklace is a DAG-based CRDT where each block references its causal predecessors, providing:

- Equivocation detection as a structural property (conflicting blocks share a parent but are not ancestors of each other)
- Quiescent operation (no messages when idle---nodes only communicate when they have transactions)
- 3-round finality under Cordial Miners $tau$ total ordering
- No distinguished leader---every node is a miner with equal authority

A single-node federation ($n = 1$) is simply Cordial Miners with a committee of one---no separate "solo mode" exists.

=== Cordial Miners $tau$ (Total Ordering)

Cordial Miners provides BFT total ordering over a Blocklace DAG. Each round proceeds:

+ A miner creates a block referencing all known tips (cordial dissemination).
+ When $2f + 1$ blocks at the same round are observed, the round is _closed_.
+ A deterministic rule (lowest hash among round-$r$ blocks that reference $2f + 1$ round-$(r-1)$ blocks) selects the _leader_ for that round.
+ The leader's causal past, minus already-committed blocks, is appended to the total order.

Finality requires 3 communication rounds. The safety proof relies on the Blocklace's equivocation-detection property: if a node equivocates, both conflicting blocks are visible in the DAG and the node is identified as Byzantine.

=== Constitutional Consensus (Membership)

Federation membership is governed by Constitutional Consensus---a democratic membership protocol built atop the Blocklace:

- *h-rule*: A node is admitted when $h$ existing members reference its join-request block in their own blocks (where $h$ is a constitution parameter, typically $2f + 1$).
- *Timeout-leave*: A node that has not produced a block within a configured timeout is automatically removed from the active set. No explicit eviction vote is needed.
- *Democratic*: No distinguished authority controls membership. The constitution is the rule set; enforcement is structural.

This replaces traditional epoch-based reconfiguration: membership changes are continuous and take effect as soon as the Blocklace records sufficient support.

== Block Structure

Blocklace blocks are content-addressed DAG nodes:

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
BlocklaceBlock {
    author: PublicKey,                     // producing node
    parents: Vec<BlockHash>,              // DAG predecessors (all known tips)
    round: u64,                           // protocol round
    payload: Vec<TurnHash>,              // ordered content
    revocations: Vec<RevocationEvent>,
    state_root: [u8; 32],                // composite state after this block
    note_tree_root: [u8; 32],            // note commitments
    nullifier_set_root: [u8; 32],        // spent nullifiers
    signature: Signature,
    hash: [u8; 32],                      // content-addressed identity
}
```
]]

The state root is a composite: $"state_root" = "BLAKE3"("merkle_root" || "note_tree_root" || "nullifier_set_root")$. Equivocation is detected structurally: two blocks by the same author at the same round with different parents constitute a proof of misbehavior visible to all participants.

== Three-Tier Execution Model

Pyana provides three execution tiers with increasing coordination requirements:

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Tier*], [*Mechanism*], [*Latency*], [*Use Case*]),
    [Sovereign (PCO)], [Local execution + STARK proof], [Instant], [Default. Agent proves own transitions.],
    [Optimistic (Stingray COD)], [Bounded counters, commit-on-demand], [Fast], [Concurrent resource spending without ordering.],
    [Ordered (Cordial Miners)], [Blocklace DAG, 3-round BFT], [3 rounds], [When total ordering is required (nullifiers, disputes).],
  ),
  caption: [Execution tiers. Agents escalate from sovereign to ordered only when coordination requires it.],
)

Most turns execute at the sovereign tier (no federation contact). Budget-limited operations use the optimistic tier (Stingray bounded counters allow concurrent debits up to the silo's slice without global ordering). Only operations requiring total ordering---double-spend prevention, dispute resolution, shared mutable state---use the ordered tier via Cordial Miners.

== Federation Lifecycle

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, left),
    table.header([*Size*], [*f*], [*Threshold*], [*Use Case*]),
    [1], [0], [1], [Solo agent (Cordial Miners with $n=1$, self-signed log)],
    [3], [0], [3], [Development/testing (no fault tolerance)],
    [4], [1], [3], [Minimum BFT (one faulty node tolerated)],
    [7], [2], [5], [Production small federation],
    [13+], [4+], [9+], [Production large federation],
  ),
  caption: [Federation sizes. A 1-node federation is Cordial Miners with a trivial committee---same code path, no special case.],
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

The Blocklace provides structural equivocation detection: if a node produces two blocks at the same round with incompatible parent sets, both blocks are visible in the DAG and constitute an irrefutable proof of Byzantine behavior. Any observer can construct the equivocation proof (two blocks, same author, same round, different content). This triggers: freeze of cross-federation operations involving the equivocating node, broadcast to peered federations, and removal of the equivocating node via Constitutional Consensus timeout-leave.

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

The recommended medium-term approach is validium-style blind ordering: agents submit encrypted turns alongside STARK proofs of valid state transition. Validators see nullifiers and proofs but NOT turn content or state. This aligns with Pyana's existing receipt-chain model where the Effect VM already proves hash continuity and conservation in a single proof per turn.

== Coordination Primitives

=== Bounded Counters (Stingray COD)

The optimistic tier uses bounded counters adapted from Stingray @stingray commit-on-demand: $"slice"(i) = "balance" dot (f+1)/(2f+1)$. Each silo debits locally up to its slice without coordination. The invariant $sum_i "spent"(i) <= "balance"$ holds even under $f$ Byzantine silos. This is the middle tier---faster than ordered consensus, but limited to operations where conflict sets are partitionable.

=== Atomic Coordination (2PC)

Cross-silo turns use two-phase commit with threshold quorum certificates. Fast unlock releases locked budget immediately upon abort.

=== Causal Ordering (Blocklace)

The Blocklace itself provides causal ordering as a structural property: the DAG's parent references encode happened-before relationships without requiring global consensus. Non-ordered operations simply reference the causal past; Cordial Miners is engaged only when total ordering is needed.

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

Cordial dissemination (reactive push with frontier exchange) propagates Blocklace blocks: each node pushes new blocks to peers and responds to frontier queries with the missing causal history. Chunked sync delivers up to 100 blocks per push for catch-up scenarios.

== Persistence and Bootstrapping

Nodes persist state across restarts using redb (ACID, WAL, crash-safe embedded database):

- *Blocklace blocks*: Persisted incrementally as they arrive. On restart, the node reconstructs its view of the DAG from stored blocks.
- *Ledger checkpoints*: Every 100 committed blocks, the full ledger state (cell commitments, note tree, nullifier set) is checkpointed atomically.
- *Application state*: JSON atomic snapshots for hosted cells and application services.

=== Fast-Sync for New Nodes

A new node joining a federation does not replay the full Blocklace history. Instead:

+ Request the latest checkpoint from any federation peer (checkpoint serving API).
+ Verify the checkpoint's attested root against a known trust anchor.
+ Resume Blocklace participation from the checkpoint height.

This reduces sync time from $O("history")$ to $O("checkpoint_size")$---typically seconds rather than hours for a mature federation.
