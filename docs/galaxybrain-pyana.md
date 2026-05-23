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

## Open Questions

1. **Witness freshness.** When Alice's Merkle witness is stale (someone else's cell updated, changing the root), how does she learn the new path? The federation must serve witness-update diffs, or Alice subscribes to commitment-tree changes.

2. **Revocation without revelation.** Can we build a revocation scheme where the federation enforces "this cap is revoked" without seeing the cap? Possibly via nullifier-style revocation: revoking a cap publishes a revocation-nullifier, and proofs must demonstrate non-membership in the revocation set.

3. **Hybrid cell coordination.** When a sovereign cell interacts with a hosted cell (e.g., a private agent trades on a public DEX), what does the proof interface look like? The hosted cell's state is visible; the sovereign cell's is not. Asymmetric proof requirements.

4. **Recovery.** If an agent loses their local state, they lose everything. The federation stores only a hash. Recovery requires backups, social recovery, or encrypted state escrow -- none of which currently exist.
