# Federation Architecture: Design Document

## 1. Current State

### What Exists

The federation layer consists of four crates and two binaries:

| Component | Role | Status |
|-----------|------|--------|
| `federation/` | Simplified BFT consensus, revocation trees, threshold sigs | Working, tested |
| `morpheus/` | Full DAG-based BFT (Lewis-Pye & Shapiro) | Proven sound, unused in production |
| `federation/src/morpheus_adapter.rs` | Bridge from morpheus to federation | Structural only, never drives finalization |
| `net/` | QUIC P2P, topic gossip, causal DAG | Working |
| `node/` | Federation daemon (API + gossip sync) | Working |
| `relay/` | Lightweight QUIC relay for attested roots | Working |
| `coord/` | 2PC atomic turns, causal chaining, budget channels | Working |
| `turn/src/conditional.rs` | STARK-conditional cross-fed atomic execution | Implemented |
| `turn/src/obligation.rs` | Bonded proof obligations (anti-free-option) | Implemented |
| `wire/src/federation_bridge.rs` | Wire server to consensus engine bridge | Working |

### What Works

1. **Simplified consensus** (`federation/src/consensus.rs`): Propose/vote/finalize with Ed25519 signatures. Rotating leader, view changes, epoch-based reconfiguration. Tested with 3-7 nodes.

2. **Threshold signatures** (`federation/src/threshold.rs`): BLS12-381 aggregate QCs via the `hints` crate. Constant-size quorum certificates regardless of committee size.

3. **Revocation trees** (`federation/src/revocation.rs`): Merkle-tree-based non-membership proofs for unrevoked tokens. All nodes converge on the same root after block finalization.

4. **Transport** (`federation/src/transport.rs`): Both in-memory (`LocalTransport`) and TCP (`TcpFederationTransport`) implementations with length-prefixed postcard framing.

5. **Pacemaker** (`NetworkConsensusNode`): 30-second proposal timeout with signed view-change messages. Advances view when n-f view-change votes collected.

6. **Epoch reconfiguration**: Add/remove members across epoch boundaries. Quorum of current members must approve. New config takes effect after next finalized block.

7. **Cross-federation primitives**: `ConditionalTurn` + `ProofObligation` provide STARK-conditional atomic execution with timeout abort and bonded commitments.

### What is Broken or Missing

1. **No state root in consensus blocks.** The `RevocationBlock` commits to `events`, `height`, `view`, `proposer`, and `prev_hash` -- but NOT the post-execution state root. Nodes cannot detect divergence after finalization without comparing full tree state. The `AttestedRoot` has `note_tree_root` and `nullifier_set_root` fields but they are always `None` in the consensus path.

2. **Morpheus adapter is dead code.** `MorpheusAdapter` exists but:
   - Never polls `take_finalized()` in any production loop.
   - Uses `TestTransaction` instead of a proper `RevocationEvent` wrapper.
   - No integration with `NetworkConsensusNode` or `FederationBridge`.
   - The `morpheus` feature flag is optional and typically disabled.

3. **No economic incentive.** Validators donate compute/bandwidth with no compensation. No staking, no fee distribution, no slashing beyond the `ProofObligation` bond mechanism (which is per-swap, not per-block).

4. **Validator signature forge window.** In legacy mode (empty `config.members`), vote signatures are not verified. Any node can cast votes for any voter ID. Only mitigated when explicit member keys are configured.

5. **No equivocation detection.** A Byzantine leader can propose conflicting blocks to different subsets of voters. No mechanism to detect or punish equivocation (proposing two blocks at the same height/view).

6. **Cross-federation trust has no root rotation.** `RoutingHint.federation_id` is BLAKE3(genesis attested root) -- a fixed identifier. If the federation's key material is compromised, there is no rotation ceremony that updates the federation identity across all holders of cross-fed capabilities.

7. **Gossip is unstructured.** `federation_sync.rs` uses topic-based eager-push gossip but has no protocol for state sync (catch-up after partition), block-by-block sync, or snapshot transfer for new nodes joining.

---

## 2. Target Architecture

### Design Principles

1. **Federation as ordering service.** The federation's ONLY job is to agree on a total order of turns. Execution is deterministic given the ordering. State correctness is verified via state roots in blocks.

2. **Proof-carrying state.** Agents own their state via receipt chains. Federation attestation is one verification path; receipt-chain verification is the other. The federation never holds state it cannot justify.

3. **Morpheus for safety, simplified for speed.** Use Morpheus's DAG-based BFT for the consensus core (proven sound). The simplified round-robin was a stepping stone.

4. **Economic security via stake.** Validators bond stake. Block production earns fees. Equivocation or invalid proposals forfeit stake. The incentive structure ensures honest majority is rational, not just assumed.

5. **Cross-federation composability.** Federations discover each other, verify each other's roots, and coordinate atomic swaps without trusting each other's validators.

### Block Structure (Target)

```rust
struct FederationBlock {
    // Ordering metadata
    height: u64,
    view: ViewNum,
    proposer: Identity,
    prev_hash: [u8; 32],

    // Ordered content
    turns: Vec<TurnHash>,          // ordered turn hashes (not full turns)
    revocations: Vec<RevocationEvent>,

    // State commitment (computed AFTER deterministic execution)
    pre_state_root: [u8; 32],      // state root before this block
    post_state_root: [u8; 32],     // state root after executing this block
    note_tree_root: [u8; 32],      // note commitment tree after this block
    nullifier_set_root: [u8; 32],  // nullifier set after this block

    // Proposer proof
    proposer_signature: Signature,
    block_hash: [u8; 32],
}
```

Adding `pre_state_root` and `post_state_root` enables:
- **Divergence detection**: Voters reject blocks where pre_state_root disagrees with their local state.
- **Light clients**: Verify state inclusion against the attested post_state_root without replaying all blocks.
- **Fraud proofs**: Present a valid block where pre_state + turns does not produce the claimed post_state.

### Morpheus Integration

The `MorpheusProcess<T>` becomes the consensus engine. The adapter is promoted from optional dead code to the primary path:

```
FederationNode
  └── MorpheusAdapter
        ├── MorpheusProcess<FederationTransaction>  (DAG-BFT consensus)
        ├── FederationTransport                      (QUIC message delivery)
        └── ExecutionEngine                          (deterministic state transition)
              ├── TurnExecutor                       (apply turns, produce receipts)
              ├── RevocationTree                     (apply revocations)
              └── StateRootComputer                  (Merkle root over all state)
```

**Why Morpheus over simplified:** The simplified consensus has fundamental limitations:
- Single leader per view: one stuck leader blocks all progress until timeout.
- No pipelining: one block at a time, all nodes idle during voting.
- No DAG structure: no concurrent block production across non-conflicting transactions.

Morpheus provides:
- All-to-all transaction block production (high throughput in stable network).
- Leader blocks for ordering (periodic total-order checkpoints).
- Graceful degradation (falls back to single-leader when network is unstable).
- Proven safety and liveness (paper-verified BFT under partial synchrony).

### Federation Lifecycle

```
                 ┌─────────────────────────────────────────────┐
                 │                 GENESIS                       │
                 │  (N founding members, initial stake bonds)    │
                 └─────────────┬───────────────────────────────┘
                               │
                               ▼
                 ┌─────────────────────────────────────────────┐
                 │              STEADY STATE                     │
                 │  Morpheus DAG-BFT producing blocks            │
                 │  Turns ordered, state roots attested          │
                 │  Fees collected, distributed to validators    │
                 └────────┬────────────────────────┬───────────┘
                          │                        │
                          ▼                        ▼
              ┌───────────────────┐    ┌───────────────────────┐
              │  RECONFIGURATION  │    │  CROSS-FED OPERATION  │
              │  Add/remove member│    │  Atomic swaps via      │
              │  Epoch boundary   │    │  ConditionalTurn +     │
              │  Stake adjustment │    │  ProofObligation       │
              └───────────────────┘    └───────────────────────┘
```

### Minimum Viable Federation

| Size | f | Threshold | Use Case |
|------|---|-----------|----------|
| 1 | 0 | 1 | Solo agent (self-signed, no BFT -- just a signed log) |
| 3 | 0 | 3 | Development/testing (all must agree, no fault tolerance) |
| 4 | 1 | 3 | Minimum BFT (one faulty node tolerated) |
| 7 | 2 | 5 | Production small federation |
| 13+ | 4+ | 9+ | Production large federation |

A 1-node federation is valid: it produces signed blocks that others can verify. It offers no Byzantine tolerance but provides a verifiable execution log. This is the "personal agent" mode.

---

## 3. Migration Path

### Phase 1: State Roots in Blocks (no consensus change)

**Effort:** Medium. **Risk:** Low.

1. Add `post_state_root: [u8; 32]` to `RevocationBlock`. Compute it as `BLAKE3(merkle_root || note_tree_root || nullifier_set_root)`.
2. Include `post_state_root` in `RevocationBlock::compute_hash()`.
3. Voters verify `pre_state_root` matches their local state before voting.
4. `AttestedRoot` populates `note_tree_root` and `nullifier_set_root` from the block.

This is backward-compatible: old blocks without state roots are valid (the field can be `[0; 32]` for genesis). New blocks require state root agreement.

### Phase 2: Activate Morpheus Adapter

**Effort:** High. **Risk:** Medium.

1. Define `FederationTransaction` implementing the `Transaction` trait (wraps `Vec<TurnHash>` + `Vec<RevocationEvent>`).
2. Rewrite `MorpheusAdapter` to use `FederationTransaction` instead of `TestTransaction`.
3. Implement the finalization callback: when morpheus finalizes a block, feed it into the execution engine (apply turns, update state, compute roots).
4. Wire the adapter's outbox into `FederationTransport` (QUIC message delivery).
5. Add a `consensus_mode` config: `Simplified | Morpheus`. Default to `Simplified` initially.
6. Integration test: run 4-node federation under Morpheus, verify finalization and state convergence.

### Phase 3: Economic Security

**Effort:** Medium. **Risk:** Medium (requires careful incentive design).

1. **Stake bond**: Joining a federation requires locking tokens (via a `StakeTurn`). The bond is slashable.
2. **Fee distribution**: Each block's fee pool is split among validators who voted for it (proportional to stake weight).
3. **Slashing conditions**:
   - Equivocation (two proposals at same height/view): full stake slash.
   - Unavailability (missed N consecutive blocks): partial slash + forced exit.
   - Invalid state root (fraud proof): full stake slash.
4. **Unbonding period**: After exit, stake is locked for E epochs (allows slashing for recently-discovered faults).

### Phase 4: Cross-Federation Protocol

**Effort:** High. **Risk:** Low (additive, does not change intra-federation behavior).

1. **Discovery document**: Each federation publishes a signed `FederationManifest` containing its genesis root, current members, relay endpoints, and supported capabilities.
2. **Relay peering**: Relays exchange manifests during inter-relay QUIC handshake. Populate peer table.
3. **Root attestation forwarding**: When a federation finalizes a block, its relay gossips the new `AttestedRoot` to peered relays.
4. **Cross-fed conditional execution**: The `ConditionalTurn` + `ProofObligation` primitives already exist. Wire them through the relay layer so proofs from federation B can be delivered to federation A's conditional turn pool.
5. **Root rotation ceremony**: A federation can rotate its identity key via a special reconfiguration epoch that includes a "succession proof" -- a chain `old_genesis -> ... -> new_identity` signed by supermajority of both old and new committee.

### Phase 5: Privacy-Preserving Ordering (Future)

**Effort:** Very High. **Risk:** Research-stage.

The federation could order turns without seeing their content:

1. Clients submit encrypted turns: `Enc(turn) || ZK_proof(turn is well-formed)`.
2. The ZK proof demonstrates (without revealing turn content): valid nonce, sufficient balance, valid signatures, conservation law holds.
3. Federation orders the encrypted turns by consensus.
4. After ordering, clients publish decryption keys (or a threshold decryption ceremony reveals them).
5. Nodes execute the revealed turns in the agreed order.

This is a significant research problem (encrypted mempool + ZK validity). Defer until the base protocol is stable.

---

## 4. Key Decisions with Tradeoffs

### Decision 1: Morpheus vs. Simplified Consensus

| | Morpheus | Simplified |
|---|---|---|
| **Safety** | Proven (paper + invariant checks) | Correct but manually reasoned |
| **Throughput** | O(n) tx blocks/round (all produce) | O(1) block/round (only leader) |
| **Complexity** | ~2000 LOC, DAG management, 3 vote levels | ~500 LOC, single round |
| **Latency** | 1 delta for fast path | 1 round trip (propose + vote + finalize) |
| **View change** | Integrated (end-view messages + QC chain) | Separate pacemaker (30s timeout) |

**Recommendation:** Migrate to Morpheus. The simplified consensus was scaffolding. The investment in the morpheus crate (crypto, state tracking, test harness, invariant checker, tracing) is wasted if not used. The adapter already exists -- it just needs wiring.

### Decision 2: State Root Scope

**Option A: Revocation root only** (current). Minimal commitment. No general-purpose light clients.

**Option B: Full state root** (revocations + notes + nullifiers). Enables light clients for all operations. Larger blocks, more verification per vote.

**Option C: Composite state root** (hash of all sub-roots). One 32-byte commitment covers everything. Sub-roots are available for targeted proofs.

**Recommendation:** Option C. `post_state_root = BLAKE3(merkle_root || note_tree_root || nullifier_set_root)`. The composite root is committed in the block. Individual sub-roots are available from the `AttestedRoot` struct (which already has fields for them).

### Decision 3: Block Content -- Full Turns vs. Turn Hashes

**Option A: Full turns in blocks.** Every validator stores and re-executes every turn. Simple but O(n) storage per validator.

**Option B: Turn hashes only.** Blocks contain only hashes. Turns are disseminated via gossip (already happening via `TOPIC_TURNS`). Validators must have received the turn before voting.

**Recommendation:** Option B (turn hashes). The gossip layer (`federation_sync.rs`) already disseminates full turns. Blocks should be lightweight ordering proofs. Validators who miss a turn gossip can request it from peers before voting (or abstain).

### Decision 4: Equivocation Handling

**Option A: Detect and slash** (retrospective). Any node that observes two signed proposals at the same (height, view) from the same proposer broadcasts an equivocation proof. The slashing condition is added to the next epoch.

**Option B: Prevent via threshold signing** (proactive). The proposer must obtain a threshold pre-signature to propose. Cannot forge two proposals without threshold collusion.

**Recommendation:** Option A for pragmatism. Equivocation proofs are simple (two conflicting signed blocks) and enforceable via the existing reconfiguration mechanism. Option B requires a threshold pre-signing round that adds latency.

### Decision 5: Cross-Federation Identity

**Option A: Genesis-hash identity** (current). `federation_id = BLAKE3(genesis_attested_root)`. Fixed forever.

**Option B: Rotating identity with succession chain.** `federation_id` is the hash of a chain: `genesis -> rekey_1 -> rekey_2 -> ... -> current`. Any holder of the succession chain can verify the current identity derives from the known genesis.

**Option C: DID-style self-sovereign identity.** Each federation has a DID document with versioned keys and service endpoints.

**Recommendation:** Option B. It provides key rotation (necessary for long-lived federations) without introducing external dependencies (DIDs require resolvers). The succession chain is self-contained and verifiable offline.

---

## 5. Relationship to Morpheus Integration

The morpheus crate (`pyana-morpheus`) implements the full protocol from the paper:

- **DAG structure**: Transaction blocks (produced by all processes) + Leader blocks (produced by view leader).
- **Three vote levels**: 0-QC, 1-QC, 2-QC with progressive commitment.
- **BLS threshold signatures**: `KeyBook` + `QuorumTrack<VoteData>` for aggregation.
- **View management**: `end_views`, `start_views`, timeout-based view change.
- **Finalization**: Blocks reaching 2-QC are finalized, forming a totally-ordered sequence.

### What the Adapter Must Do

The `MorpheusAdapter` currently:
- Creates a `MorpheusProcess<TestTransaction>` (wrong transaction type).
- Maintains an outbox of morpheus messages.
- Converts `RevocationEvent` to `TestTransaction` via postcard serialization.
- Never has its `take_finalized()` called.

The adapter must be reworked to:

1. **Define `FederationTransaction`**: A proper type that wraps ordered turn hashes and revocation events, implements `Transaction` (Clone + Eq + Ord + Hash + CanonicalSerialize/Deserialize).

2. **Drive the event loop**: The `NetworkConsensusNode` loop must call:
   - `adapter.set_time(now)` on each tick.
   - `adapter.try_produce_block()` when there are pending transactions.
   - `adapter.check_timeouts()` periodically.
   - `adapter.handle_incoming(msg, sender)` for each received message.
   - `adapter.take_finalized()` to consume finalized blocks.

3. **Bridge outbox to transport**: `adapter.drain_outbox()` produces morpheus protocol messages. These must be serialized and sent via the `FederationTransport`.

4. **Finalization hook**: When `take_finalized()` yields blocks, the node:
   - Deserializes the `FederationTransaction` from each finalized block.
   - Feeds the ordered turns to the execution engine.
   - Computes the post-state root.
   - Updates the `AttestedRoot`.
   - Gossips the new root.

### Coexistence Strategy

During migration, both consensus engines can coexist:

```rust
enum ConsensusEngine {
    Simplified(ConsensusOrchestrator),
    Morpheus(MorpheusAdapter),
}
```

The `FederationBridge` dispatches to whichever engine is configured. This allows per-federation choice and incremental rollout.

---

## 6. Cross-Federation Protocol Design

### Discovery

```
┌──────────────────────────────────────────────────────────────┐
│  Federation A                    Federation B                  │
│                                                              │
│  Relay A ◄───── Peering Handshake ─────► Relay B            │
│    │            (exchange manifests)           │              │
│    │                                          │              │
│    └── Gossip: AttestedRoot updates ──────────┘              │
│                                                              │
│  Node A knows: Fed B exists, its current root, its relays   │
└──────────────────────────────────────────────────────────────┘
```

**FederationManifest:**
```rust
struct FederationManifest {
    /// BLAKE3(genesis_attested_root) -- the stable identity.
    federation_id: [u8; 32],
    /// Succession chain for identity rotation.
    succession: Vec<SuccessionEntry>,
    /// Current committee public keys.
    current_members: Vec<PublicKey>,
    /// Relay endpoints for this federation.
    relays: Vec<RelayEndpoint>,
    /// Latest attested root (proof of liveness).
    latest_root: AttestedRoot,
    /// Signature over manifest by supermajority of current committee.
    committee_signature: ThresholdQC,
}

struct SuccessionEntry {
    epoch: u64,
    old_committee_root: [u8; 32],
    new_committee_root: [u8; 32],
    transition_proof: ThresholdQC,  // old committee signs the transition
}
```

### Cross-Federation Atomic Swap (Full Protocol)

```
Alice (Fed A)                          Bob (Fed B)
     │                                      │
     │  1. Create ProofObligation(P_A)      │
     │     bond: 100 computrons             │
     │     condition: prove transfer to Bob │
     │                                      │
     │  ◄─── 2. Create ProofObligation(P_B) │
     │          bond: 100 computrons        │
     │          condition: prove transfer   │
     │                                      │
     │  3. Create ConditionalTurn(T_A)      │
     │     condition: RemoteProof from B    │
     │     timeout: H_A + 500              │
     │                                      │
     │  ◄─── 4. Create ConditionalTurn(T_B) │
     │         condition: RemoteProof from A│
     │         timeout: H_B + 500          │
     │                                      │
     │  5. Execute transfer on Fed A        │
     │     Produce receipt R_A              │
     │     Generate STARK proof P_A         │
     │                                      │
     │  6. Deliver P_A to Fed B ─────────► │
     │     (via relay peering)              │
     │                                      │
     │  ◄─── 7. T_B executes (P_A valid)   │
     │         Produce receipt R_B          │
     │         Generate STARK proof P_B     │
     │                                      │
     │  8. P_B delivered to Fed A           │
     │     T_A executes (P_B valid)         │
     │     Both obligations fulfilled       │
     │     Both bonds returned              │
     └─────────────────────────────────────┘
```

**Failure mode:** If either proof fails to arrive before the timeout, the corresponding ConditionalTurn expires. The ProofObligation whose proof was not delivered gets slashed, compensating the other party.

### Routing Integration

The cross-federation routing design (from `docs/xfed-routing.md`) remains unchanged:
- `RoutingHint` carries `federation_id` + relay endpoints, stored in `RoutingDirective` (not in `CapabilityRef`).
- Relay-mediated cross-fed delivery for nodes that cannot directly reach remote federations.
- Optional privacy overlay via `H(CellId || routing_nonce)` DHT lookup.

The federation architecture adds the **trust establishment** layer on top of routing:
1. Relays exchange `FederationManifest` during peering.
2. Manifests are verified: succession chain from known genesis, committee signature valid.
3. `AttestedRoot` updates from peer federations are verified against the manifest's committee.
4. Cross-fed proofs (for ConditionalTurn resolution) are verified against the attested root from the remote federation's manifest.

### Equivocation Detection (Cross-Federation)

When two relays from the same federation present conflicting attested roots at the same height:

```rust
struct EquivocationProof {
    root_a: AttestedRoot,
    root_b: AttestedRoot,
    // Both at the same height, both with valid QCs, but different merkle_roots.
    // This proves the federation's committee equivocated.
}
```

Any node receiving an equivocation proof for a federation can:
1. Freeze cross-fed operations with that federation.
2. Broadcast the proof to other peered federations (quarantine propagation).
3. Require the equivocating federation to resolve (via slashing the equivocating proposer and publishing a succession entry).

---

## 7. Open Questions

1. **Morpheus transaction type**: Should `FederationTransaction` be opaque bytes (flexible) or strongly typed (safer)? The morpheus protocol does not inspect transaction content -- it only orders them. Opaque bytes allow future extensibility.

2. **State root computation cost**: Computing a full state root (revocations + notes + nullifiers) on every block adds latency. Should this be async (computed after finalization, attested in the next block) or synchronous (computed before voting)?

3. **Minimum stake amount**: What economic value must a validator bond? Too low = Sybil attacks. Too high = centralization. Should this be fixed or adaptive (percentage of total federation value)?

4. **Gossip protocol for block sync**: New nodes joining need to catch up. Should they download the full block history (verifiable but expensive) or just the latest state snapshot + recent blocks (faster but requires trust in the snapshot provider)?

5. **Privacy-preserving ordering timeline**: The encrypted mempool design is powerful but adds significant complexity. Should it be a "never" or a "v2" feature? Are there intermediate steps (e.g., delayed reveal without full ZK)?

6. **Federation size scaling**: Morpheus is optimal for N < ~100. For very large committees, should the protocol switch to a committee-sampled approach (random subset validates each block)? This is a v2 concern.
