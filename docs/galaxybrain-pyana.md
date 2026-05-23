# Sovereign Cells: Pyana as Coordination Infrastructure

## The Provocation

Pyana currently runs a "global ledger" model: federation nodes store all cell state, execute all turns, maintain the full Merkle tree. Agents are stateless clients -- they hold keys and tokens, submit turns, and generate proofs, but their state lives on the federation.

The original vision was different. Agents maintain their own state. The federation provides ordering, root anchoring, and proof verification -- not execution and storage.

What would pyana look like if we took that vision seriously?

## The Sovereign Cell Model

**Cells exist only on the agent's machine.** The federation tracks commitments (32 bytes per cell), not full state. Agents execute their own transitions locally and submit proofs of valid transitions. The federation verifies proofs, updates commitments, and provides ordering.

### What the federation becomes

The `Ledger` shrinks from `HashMap<CellId, Cell>` to `HashMap<CellId, [u8; 32]>`. One hash per cell. The `TurnExecutor` moves entirely to the agent side. Federation nodes become:

1. Verify proof of valid state transition (STARK verification -- already fast)
2. Update the commitment (32-byte swap)
3. Order transitions (BFT consensus or fast-path quorum locks)
4. Maintain the nullifier set (double-spend prevention stays on-chain)

### What the agent maintains

- Full cell state (their own cells only)
- Merkle witnesses for their state position in the commitment tree
- Capability sets, tokens, keys
- Nullifier witnesses for their own notes
- A local `TurnExecutor` (same code that currently runs on nodes)

### Multi-party interactions

Alice wants to transfer 100 to Bob:

1. Alice proves: "my state transitions from S_A to S_A', deducting 100" (includes commitment to Bob's cell ID and amount)
2. Bob proves: "my state transitions from S_B to S_B', receiving 100" (includes commitment to Alice's proof hash)
3. Both submit proofs to federation
4. Federation verifies: both proofs valid, net conservation holds, no double-spend, commits both new state hashes atomically

This maps directly to the existing `TurnComposer` / 2PC pattern. Both parties prove locally rather than the federation executing on their behalf. The `CommitmentMode::Partial` already lets each signer commit only to their fragment.

### Capability verification

Currently the executor checks capabilities against the ledger. In sovereign mode:

- Capabilities are part of the agent's cell state
- Exercising a capability on someone else's cell: you prove "I hold this cap" (Merkle witness into your own state) and the target proves "this cap exists in my c-list" (Merkle witness into their state)
- The federation never sees the capabilities themselves, only that both proofs verified

## What We Gain

**Privacy by default.** The federation never sees cell contents -- no balance amounts, no capability sets, no metadata fields. It sees commitments and proofs. This eliminates the "upload your entire life to the federation" problem and makes the privacy story uniform rather than split between "note layer = private, cell layer = visible."

**Scalability.** Federation storage drops from O(state_size) to O(32 * num_cells). A million cells costs 32 MB, regardless of how complex each cell's internal state is.

**Agent sovereignty.** Your state, your machine, your execution. The federation cannot censor your state (it cannot even read it). It can only refuse to order your transitions.

**Natural fit for coordination.** If pyana coordinates fleets of services, those services already maintain their own state (databases, configs, queues). They need ordering guarantees, atomicity, and capability verification from pyana -- not hosting.

## What We Lose

**Queryability.** "What's Alice's balance?" requires Alice's cooperation. No global state inspection. Shared read patterns need explicit disclosure protocols or designated "public cells."

**Shared mutable state.** A DEX orderbook, a shared registry, a public auction -- these need all participants to see and modify the same state. Solution: a hybrid model where specific cells are "hosted" (federation-maintained, globally readable) while most are sovereign.

**Revocation enforcement.** If revocation is part of a sovereign cell, the owner could hide it. The `delegation_epoch` mechanism currently works because the federation sees the cell. In sovereign mode, revocation propagation needs a separate commitment path -- perhaps revocation lists remain on-chain even when cell state does not.

**Light client inspection.** Third parties cannot audit state without the owner's proof. Compliance, debugging, and dispute resolution all require the owner to voluntarily reveal.

## How This Relates to What We Already Have

The codebase already contains half this architecture:

- **Notes are already sovereign.** The note tree stores commitments (hashes), not values. Note owners maintain their own witnesses. Spending requires proving knowledge of preimage + nullifier. This is exactly the sovereign cell pattern applied to value.
- **Turns are agent-signed.** Agents already construct and sign turns locally. The gap is: they submit turns for *execution* rather than submitting *proofs of execution*.
- **The STARK circuit already proves state transitions.** `circuit/src/presentation.rs` proves Merkle membership and capability derivation. Extending this to prove "transition from commitment_old to commitment_new is valid" is incremental.
- **The fast path is almost sovereign.** For single-owner cells, the fast path already skips consensus and just does quorum-lock + execute. Replace "execute" with "verify proof" and you have sovereign cells.
- **TurnComposer handles multi-party atomicity.** The 2PC composition pattern works identically whether the federation executes both halves or verifies both proofs.

## Migration Path

This does not require a rewrite. It can be a gradual transition:

**Phase 1: Dual-mode cells.** Add a `CellMode` enum: `Hosted` (current behavior) or `Sovereign` (commitment-only). The `Ledger` stores either full state or a 32-byte hash depending on mode. Federation nodes verify proofs for sovereign cells, execute turns for hosted cells. All existing code continues working for hosted cells.

**Phase 2: Agent-side executor.** The `TurnExecutor` already runs locally in `sdk/src/runtime.rs`. Extend the SDK to produce a STARK proof of the execution result. The agent submits (turn_hash, new_commitment, proof) instead of the raw turn.

**Phase 3: Proof-carrying turns.** Extend the `Turn` structure with an optional `execution_proof: Option<StarkProof>`. If present, the federation verifies the proof instead of re-executing. If absent, the federation executes (for hosted cells or lazy agents).

**Phase 4: Default sovereign.** New cells default to sovereign mode. Hosted cells are the exception for explicitly shared state (orderbooks, registries, public coordination objects).

**Phase 5: Commitment tree compression.** With cells as 32-byte leaves, the federation's Merkle tree becomes a pure commitment tree. Add recursive proof compression (already designed in `recursive-proof-architecture.md`) so light clients verify the entire federation state from a single proof.

## Comparison to Other Systems

| System | State Location | Proof Model | Federation Role |
|--------|---------------|-------------|-----------------|
| Pyana (current) | Federation nodes | STARK for auth only | Execute + store + order |
| Pyana (sovereign) | Agent machines | STARK for transitions | Verify + commit + order |
| Mina | zkApp storage (on-chain, 8 fields) | Recursive SNARKs | Full consensus on all state |
| ZK-Rollups | Off-chain (sequencer) | Validity proofs to L1 | L1 verifies batch proof |
| State Channels | Off-chain (parties) | Signatures + dispute | L1 for disputes only |
| Sovereign Rollups | Off-chain (nodes) | DA on L1, optional verify | DA layer, no execution |

Pyana's sovereign model is closest to a "rollup per agent" where each agent is their own sequencer, the federation is their DA + verification layer, and multi-party interactions use atomic cross-rollup proofs (which we already have as TurnComposer).

## The Radical Endpoint: Zero Federation Storage

Phase 1-5 above still assumes the federation stores ONE commitment per cell. But even that isn't necessary.

**A sovereign cell that only interacts with parties it already knows doesn't need the federation AT ALL.**

The federation's role reduces to exactly four functions:
1. **Ordering** — when two sovereign cells interact with the SAME third party and order matters
2. **Double-spend prevention** — when a sovereign cell spends a note from the shared nullifier set
3. **Discovery** — when you need to find someone you don't already know
4. **Root anchoring** — periodic checkpoints so you can prove to strangers "my state was valid as of height H"

Between two parties who already know each other? They exchange signed state transitions directly. No federation contact. No registration. No storage footprint.

### Fully offline cells

```
Sovereign cell exists NOWHERE in the federation by default.

Peer-to-peer interaction (Alice ↔ Bob, no federation):
  Alice sends: (old_commitment_A, new_commitment_A, transition_proof, signed)
  Bob verifies: proof is valid, Alice's signature matches
  Bob updates his local view of Alice's state
  Federation is never contacted. Storage cost: 0 bytes.

On-demand federation interaction (Alice needs ordering/anchoring):
  1. Alice registers her current commitment (32 bytes) — ephemeral
  2. She submits her proof-carrying turn
  3. Federation verifies, orders if needed, updates commitment
  4. Alice deregisters (or commitment expires after N blocks of inactivity)
  Storage cost: 32 bytes, temporary.
```

### Peer-to-peer state exchange protocol

For two parties who know each other:

```rust
struct PeerStateTransition {
    cell_id: CellId,
    old_commitment: [u8; 32],
    new_commitment: [u8; 32],
    transition_proof: StarkProof,  // proves validity of the transition
    signature: [u8; 64],          // signs the whole thing
}
```

Alice sends this to Bob. Bob verifies:
- Signature matches Alice's known public key
- `old_commitment` matches what Bob last saw from Alice
- `transition_proof` verifies (STARK: the state transition is valid)
- Bob stores `new_commitment` as Alice's current state

No blockchain. No consensus. No federation. Just two agents exchanging proofs.

### When do you need the federation?

| Situation | Need federation? | Why |
|-----------|-----------------|-----|
| Alice transfers private note to Bob (they know each other) | NO | Direct exchange, both verify locally |
| Alice exercises capability on Bob's cell (they know each other) | NO | Proof-carrying capability exercise |
| Alice wants to prove to a STRANGER that her state is valid | YES | Needs an attested root anchor |
| Alice spends a note from the shared note tree | YES | Nullifier ordering (double-spend) |
| Alice and Bob disagree on state (dispute) | YES | Need arbiter with ordering authority |
| Alice wants to be discoverable (intent posting) | YES | Gossip network for discovery |
| Alice trades on a public DEX (hosted cell) | YES | DEX state is federation-maintained |

Most routine agent-to-agent interactions DON'T need the federation. The federation is more like a notary or DNS server — you use it when you need to prove something to strangers or resolve disputes, not for every operation.

### Proof-carrying capability exercise (no federation)

Alice holds a capability to Bob's cell. She wants to exercise it:

```
Alice → Bob:
  "Here's my current state (commitment + proof that I hold cap to your cell).
   Here's the transition I want (effect on your cell).
   Here's my proof that my state allows this."

Bob verifies locally:
  - Alice's state commitment is what he last knew
  - Alice's proof shows she holds a valid cap (in her own c-list)
  - The requested effect is within the cap's permissions
  - Bob executes the effect on HIS cell
  - Bob sends Alice an ack with his new commitment
```

The federation never participates. Bob is the "verifier" for effects on his own cell. This is literally the E capability model: objects verify their own incoming messages.

### Eventual federation sync (insurance, not requirement)

Agents CAN periodically anchor their state:
- Every N minutes (or after K transitions): register current commitment with federation
- This creates an "attested checkpoint" provable to strangers
- Between checkpoints: peer-to-peer only

Think of it like git: you work locally, push when you want others to have a reference point. You don't push every keystroke.

### What this means for the codebase

The `Ledger` type becomes optional infrastructure, not a requirement. The core protocol is:
- `Cell` (local state)
- `StarkProof` (transition validity)
- `Signature` (authentication)
- `PeerStateTransition` (the wire format between agents)

The federation crates (federation, morpheus, coord) become a LAYER on top — used when needed, not for everything.

## Open Questions

1. **Witness freshness.** When Alice's Merkle witness is stale (someone else's cell updated, changing the root), how does she learn the new path? The federation must serve witness-update diffs, or Alice subscribes to commitment-tree changes. (NOTE: this only matters when Alice registers — which is optional/infrequent.)

2. **Revocation without revelation.** Can we build a revocation scheme where the federation enforces "this cap is revoked" without seeing the cap? Possibly via nullifier-style revocation: revoking a cap publishes a revocation-nullifier, and proofs must demonstrate non-membership in the revocation set. For peer-to-peer interactions, revocation can be communicated directly.

3. **Hybrid cell coordination.** When a sovereign cell interacts with a hosted cell (e.g., a private agent trades on a public DEX), what does the proof interface look like? The hosted cell's state is visible; the sovereign cell's is not. Asymmetric proof requirements.

4. **Recovery.** If an agent loses their local state, they lose everything. The federation stores only a hash (if registered at all). Recovery requires backups, social recovery, or encrypted state escrow.

5. **Offline conflict resolution.** If Alice sends conflicting state transitions to Bob and Carol (equivocation), they can't detect it without communicating. The federation resolves this via ordering — but only if both register. Peer-to-peer-only agents are vulnerable to equivocation until they anchor.

6. **Bootstrap.** A brand-new agent has no peers, no state, no reputation. How do they enter the system? Probably: register with the federation initially (like creating an account), then go sovereign once they have peers who know them.
