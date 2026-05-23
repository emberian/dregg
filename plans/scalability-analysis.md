# Scalability Analysis: Performance Characteristics and Bottlenecks

## 1. Consensus Scalability (Blocklace / Cordial Miners)

### Protocol Structure

The Cordial Miners protocol (implemented in `blocklace/src/ordering.rs`) uses:
- **Wavelength = 3** rounds per wave (default `OrderingConfig`)
- **Round-robin leader** election per wave
- **Super-ratification**: a supermajority (floor(2n/3) + 1) of participants must have blocks at the wave's last round that ratify the leader
- **Cordiality requirement**: each block must acknowledge >2n/3 of the previous round's participants

### Message Complexity Per Wave

Each participant produces **one block per round** (from `blocklace/src/finality.rs` test structure). Each block references ALL previous round's blocks as predecessors (full cordiality).

- Per round: **n blocks produced**, each referencing **n predecessor block IDs**
- Per wave (3 rounds): **3n blocks**, each carrying ~n predecessor hashes (32 bytes each)
- **Total block data per wave**: 3n * (header + n*32 bytes predecessors + payload)
- **Dissemination**: The gossip protocol (`dissemination.rs`) uses frontier-based delta exchange, NOT all-to-all broadcast

**Actual dissemination cost** (from `dissemination.rs`):
- Nodes maintain `PeerKnowledge` maps estimating what each peer has seen
- Delta groups are causally-closed subsets sent to peers missing them
- Chunked at `MAX_BLOCKS_PER_PUSH = 100` blocks per message
- This is NOT O(n^2) per wave -- it's O(n) messages per node per round (one delta per peer)

### Scaling Estimates

| Federation Size | Blocks/wave | Predecessors/block | Wire data/wave (est.) |
|----------------|-------------|-------------------|-----------------------|
| n=4 | 12 | ~4 (128 B) | ~12 * (200 + 128) = ~4 KB |
| n=10 | 30 | ~10 (320 B) | ~30 * (200 + 320) = ~16 KB |
| n=100 | 300 | ~100 (3.2 KB) | ~300 * (200 + 3200) = ~1 MB |
| n=1000 | 3000 | ~1000 (32 KB) | ~3000 * (200 + 32000) = ~96 MB |
| n=10000 | 30000 | ~10000 (320 KB) | ~30000 * (200 + 320000) = ~9.6 GB |

**Critical observation**: Each block's `predecessors` vector grows linearly with n because cordiality requires referencing >2n/3 blocks from the previous round. At n=1000, each block carries ~32 KB of predecessor hashes alone.

### Finality Latency

- **Best case**: 1 wave = 3 rounds = 3 message delays
- **The tau function** (from `ordering.rs:410-482`) processes all finalized leaders sequentially, collecting each leader's new causal past via `xsort`
- The `xsort` function computes causal relationships via `causal_past_inclusive()` which is BFS over the DAG -- O(B) per block where B = total blocks in past

### Lightweight Participants

The constitution (`constitution.rs`) supports:
- Dynamic membership via `MembershipProposal::Join` / `MembershipProposal::Leave`
- Auto-eviction for silent nodes (`timeout_waves`)
- Partition detection (freezes eviction if >50% timeout)

There is no explicit "observer" or "light participant" mode in the consensus layer. A node either participates in block production (and is counted for cordiality/ratification) or it doesn't. Light clients would need to verify checkpoint proofs (see `plans/blocklace-validity-proof.md`) rather than participating in consensus.

### Practical Federation Size Limit

Based on predecessor vector growth and cordiality requirements:
- **n=4-20**: Excellent performance, ~KB wire data per wave
- **n=20-100**: Workable, ~MB range, still manageable on modern networks
- **n=100-1000**: Predecessor vectors dominate; 32 KB per block at n=1000
- **n>1000**: Impractical without protocol modifications (threshold acknowledgment subsets, BLS aggregate signatures, etc.)

**Sweet spot**: 4-30 participants per federation, with cross-federation bridges for wider coordination.

---

## 2. Proof Generation Costs

### Effect VM Trace Dimensions

From `circuit/src/effect_vm.rs`:
- **Trace width**: 65 columns (`EFFECT_VM_WIDTH`)
- **Columns**: 18 selectors + 14 state_before + 8 params + 14 state_after + 11 aux
- **Constraint degree**: 9 (from SetField/Seal field_idx range check: product of 8 linear factors + selector gate)
- **Trace height**: Padded to next power of 2, minimum 2 rows. One row per effect.

**Typical turn sizes**:
- Simple transfer: 1 effect = 2 rows (padded)
- Multi-effect turn (transfer + set_field + grant_cap): 4-8 effects = 8 rows
- Complex turn (8 effects + 4 custom): 16 rows

### FFT and Proving Cost

From `circuit/src/stark.rs`:
- **Blowup factor**: `blowup_for_degree(9)` = 16 (next power of two >= degree)
- **Domain size**: trace_len * 16
- **FRI queries**: 80 (`NUM_QUERIES`)
- **Extension field**: BabyBear^4 for 124-bit composition security

For a 16-row trace (typical turn):
- Evaluation domain: 16 * 16 = 256 points
- Interpolation: 65 columns * O(n log n) FFT on 16 points = ~65 * 64 field operations
- Constraint evaluation: 256 domain points * 65-wide constraint evaluation
- Merkle tree: 256 leaves, depth 8, BLAKE3 hashes
- FRI: log2(256) = 8 folding rounds, 80 queries

**Estimated BabyBear STARK proving time** (from `plans/blocklace-validity-proof.md`):
- Effect VM STARK (4-16 effects): ~300-500 ms
- Full turn proof (Effect VM + Auth + Membership + Conservation): ~600-800 ms

### IVC Folding Complexity

From `circuit/src/ivc.rs`:
- **Hash chain model**: Each fold step does one Poseidon2 hash (O(1) per step)
- **Accumulation**: O(N) where N = number of fold steps
- **MAX_FOLD_DEPTH**: 16 steps maximum per chain
- **StateTransitionAir**: 4 columns, degree 7, traces the hash chain
- **Proof size**: O(log N) via FRI compression (from `ivc_proof_size()`)

The IVC is **O(N) in proving time** (one hash per step) but produces a **constant-size proof** (~128 KiB, from `IVC_CONSTANT_PROOF_SIZE`). The STARK proof of the hash chain is what makes verification O(1).

### Can Phones Generate Proofs?

BabyBear field (p = 2^31 - 2^27 + 1):
- 32-bit arithmetic, no big-integer operations needed
- Poseidon2 permutation: ~50 multiplications per call (native 32-bit)
- A 16-row, 65-column trace requires ~16,640 field elements

**Phone feasibility estimate**:
- Modern ARM (A15+): BabyBear multiplication ~3ns
- Trace generation: ~50 us
- STARK proving (16 rows, 65 cols, blowup 16): dominant cost is 80 query Merkle proofs + FRI
- Estimated: ~500 ms - 2s on a phone for a simple transfer
- Complex turns (16+ effects): 2-5s

**Verdict**: Simple transfers are phone-provable. Complex turns may require delegation to a more powerful prover.

### Verification Cost

- STARK verification: 80 queries * (Merkle path verification + constraint check) = O(80 * log(domain_size) * width)
- For a typical 16-row trace: ~80 * 8 * 65 = ~41,600 field operations + 80 * 8 BLAKE3 hashes
- **Estimated verification time**: ~5-20 ms on a phone, ~1-5 ms on server

---

## 3. CapTP Session Overhead

### Memory Per Session

From `captp/src/session.rs`, each `CapSession` contains:
- `exports: HashMap<CellId, ExportEntry>` -- 32-byte key + (32 + enum + u32) per entry
- `imports: HashMap<CellId, ImportEntry>` -- 32-byte key + (32 + enum + bool) per entry
- `promises: HashMap<u64, PromiseState>` -- 8-byte key + enum per entry

**Per-session base memory**: ~200 bytes (structs + HashMap overhead)
**Per-export entry**: ~100 bytes
**Per-import entry**: ~100 bytes
**Per-promise**: ~80 bytes

**Scaling estimate** (1000 active exports, 500 imports, 100 promises per session):
- Per session: ~200 + 1000*100 + 500*100 + 100*80 = ~158 KB
- 100 concurrent sessions: ~16 MB
- 1000 concurrent sessions: ~160 MB

### GC Message Cost

From `captp/src/gc.rs`:
- `ExportGcManager` tracks per-federation reference counts
- A `DropRef` message is generated when all local references to an import reach zero
- GC messages are **proportional to capability sharing**, not to time
- `stale_exports()` detects idle exports for proactive cleanup

**Per-epoch GC cost**: O(number of capabilities released in that epoch). Not a periodic broadcast -- only triggered by actual drops.

### Promise Pipeline Depth

From `captp/src/pipeline.rs`:
- `pipeline_chain()` creates intermediate promises for each step
- Each step adds one entry to the `queued` HashMap and one to `promises`
- **Memory per pipeline step**: ~200 bytes (PipelinedMessage + state)
- **Maximum practical depth**: Limited by total latency. A 3-deep pipeline saves 2 round trips but adds ~200*3 = 600 bytes of state

**Latency dominance threshold**: If one-way latency is L, a pipeline of depth D saves (D-1)*2L latency. At some depth, the probability of upstream breakage exceeds the latency savings. Practical limit: 5-10 steps before cascading-break risk dominates.

### Store-and-Forward Buffering

From `captp/src/store_forward.rs`:
- `MessageRelay` has configurable `max_queue_depth` per destination and `max_total_messages`
- Default TTL: configurable per message (`ttl_blocks`)
- Each `QueuedMessage`: ~150 bytes overhead + encrypted payload size
- **Per-offline peer budget**: `max_queue_depth * avg_message_size`

At max_queue_depth=1000 and avg 500-byte messages: ~500 KB per offline peer. With 100 offline peers: ~50 MB relay storage.

---

## 4. Privacy Costs

### ZK Overhead vs Plain Execution

| Operation | Plain execution | STARK proof generation | Overhead factor |
|-----------|----------------|----------------------|-----------------|
| Transfer (1 effect) | ~1 us | ~300-500 ms | ~300,000x |
| 8-effect turn | ~10 us | ~500-800 ms | ~50,000x |
| Verification | N/A (trust executor) | ~5-20 ms | One-time cost |

The ZK tax is enormous for proving but modest for verification. The system amortizes this by:
1. Proving is asynchronous (never blocks consensus or execution)
2. One proof covers an entire turn (multiple effects)
3. IVC compresses multiple proofs into one

### Metadata Leakage

**What the gossip pattern reveals**:
- Block timing: when a node produces blocks (activity pattern)
- Block size: larger payloads indicate more complex operations
- Predecessor set: who the node is acknowledging (social graph)
- Destination of store-forward envelopes: `destination: FederationId` is visible in `BlocklaceEnvelope`

**Mitigations in the code**:
- `store_forward.rs`: Payload is end-to-end encrypted (X25519 + ChaCha20-Poly1305)
- Relay cannot read message contents
- But: `destination` field is plaintext (relay needs it for routing)

**Unmitigated leaks**:
- Block production cadence reveals online/offline patterns
- Block size correlates with transaction complexity
- Cross-federation messages reveal communication graph

**Mitigation cost** (not implemented):
- Constant-rate block production (dummy blocks when idle): O(n) bandwidth waste
- Constant-size blocks (padding): wastes storage proportional to max_block_size - actual_size
- Onion routing for destinations: adds 1+ round trip per hop

### DFA Router Pattern Leakage

From `wire/src/dfa_router.rs`:
- The DFA runs on message prefixes to classify routing
- The transition table is committed to governance (`routes_commitment` in constitution)
- **Deterministic** classification means: anyone with the DFA (which is public, committed to constitution) can classify messages the same way the router does
- Traffic analysis on classified routes reveals which cells/handlers are active

---

## 5. Communication Overhead for Common Operations

### Simple Transfer (Same Federation)

1. User constructs turn with Transfer effect
2. Executor runs turn, produces Effect VM trace
3. Block created with turn payload: ~200 bytes (1 effect, postcard encoded)
4. Block disseminated to n-1 peers: 1 delta push
5. Block finalized after 1 wave (3 rounds)

**Messages**: n blocks produced per round * 3 rounds = 3n blocks total for the wave containing the transfer. The transfer itself is 1 block among those 3n.

**Bytes for the transfer block**: ~200 (payload) + n*32 (predecessors) + 64 (signature) + 40 (header) = ~200 + 32n bytes. At n=10: ~520 bytes.

**Total wire for the wave** (all n participants): 3n * (200 + 32n) bytes. At n=10: ~30 * 520 = ~16 KB.

### Cross-Federation Transfer

Requires CapTP session + proof exchange:

1. **Session establishment** (if not cached): sturdy ref enliven + 3-party handoff
   - ExportSturdyRef effect on source federation: 1 block + proof
   - EnlivenRef on destination: 1 block + proof
   - ValidateHandoff: 1 block + proof
   - Round trips: 2-3 (if sequential)
   
2. **The transfer itself**: 
   - Source: NoteCreate effect (debit, produce commitment) -- 1 block
   - Destination: NoteSpend effect (credit, reveal nullifier) -- 1 block
   - Plus: cross-federation proof transmission (STARK proof ~48 KB per the custom STARK, or ~5-10 KB via Pickles)
   
3. **Total round trips**: 
   - With pipelining: 1 round trip (all 3 steps batched)
   - Without pipelining: 3 round trips

**Bytes estimate**:
- Session establishment (one-time): ~3 blocks * 600 bytes + 3 proofs * 48 KB = ~146 KB
- Transfer itself: 2 blocks * 600 bytes + 2 proofs * 48 KB = ~97 KB
- **Total first-time cross-fed transfer**: ~243 KB, 2-3 round trips
- **Subsequent transfers (session cached)**: ~97 KB, 1 round trip (pipelined)

### Promise Pipeline (3-Deep Chain)

**Without pipelining**: 3 sequential round trips = 6 one-way delays
**With pipelining** (from `pipeline.rs`): 1 round trip = 2 one-way delays

**Messages saved**: 4 messages (2 request + 2 response for steps 2-3)
**Latency saved**: If one-way = 100ms, saves 400ms (from 600ms to 200ms)
**Bytes**: Pipeline batch is 3 `PipelineWireMessage` structs = ~600-900 bytes total (method names + args), vs 3 separate request/response pairs of similar size but spread across time.

### Cell Migration

A cell migrating between federations requires:
1. State snapshot: balance + nonce + 8 fields + cap_root + state_commitment = ~14 * 4 bytes = 56 bytes of state
2. SovereignHistory proof (IVC proof of all prior transitions): ~48-128 KB (STARK) or ~5-10 KB (Pickles)
3. Nullifier set membership proof: ~1-5 KB (Merkle path)
4. Capability table (all capabilities the cell holds): variable, O(num_capabilities * 32 bytes)
5. Re-registration on destination federation: 1 block

**Total migration bytes**: ~50-150 KB for a typical cell with modest history.

### Federation Join (Sync Cost)

From `blocklace/src/finality.rs` -- `CheckpointData`:
- If checkpoints exist: download latest checkpoint proof (~5-10 KB) + blocks since checkpoint
- If no checkpoint: download ENTIRE blocklace history

**With checkpoint** (from `plans/blocklace-validity-proof.md`):
- Checkpoint proof: ~5 KB (Pickles) or ~48 KB (STARK)
- State snapshot at checkpoint: depends on number of cells, ~1-10 MB for a typical federation
- Blocks since checkpoint: blocks_since_checkpoint * avg_block_size

**Without checkpoint** (current implementation -- no pruning yet):
- Full DAG download: all historical blocks
- At 1 block/second/participant, n=10: ~864,000 blocks/day * ~500 bytes = ~432 MB/day of accumulation

---

## 6. Storage Scalability

### Blocklace Growth Rate

At n=10 participants, 1 block per round, 3 rounds per wave:
- Blocks/wave: 30
- Block size (avg): ~500 bytes (200 payload + 320 predecessors at n=10)
- Growth/wave: ~15 KB
- If waves complete every ~3 seconds: ~5 KB/sec = ~432 MB/day

At n=100:
- Blocks/wave: 300
- Block size: ~3400 bytes (200 payload + 3200 predecessors)
- Growth/wave: ~1 MB
- Growth rate: ~333 KB/sec = ~28 GB/day

### Pruning Story

From `plans/blocklace-validity-proof.md`:
- **Checkpoint proofs** enable pruning below checkpoint height
- Block payloads (turn data) can be deleted after checkpointing
- Block headers (~200 bytes) are retained for DAG provenance
- Checkpoint interval: 128 blocks (configurable)

**Storage modes**:
- Archive node: everything retained
- Full node: last 2 checkpoints + blocks since = bounded
- Light node: latest checkpoint proof + recent blocks = ~5-10 KB proof + small buffer

### Note Tree Growth

Each NoteCreate effect adds a commitment to the note tree. The note tree is a Merkle tree:
- Each note: 32-byte commitment
- Tree depth: log2(total_notes)
- At 1M notes: depth 20, ~32 MB for full tree
- Spent notes are tracked in a nullifier accumulator (not removed from the tree)

### Cell Accumulation

Cells are created but there is no explicit cell GC in the code. Natural cell lifecycle:
- Created via factory or genesis
- May be migrated (removed from source federation)
- Revocation: cell's nullifier is spent, preventing further use
- But the cell's historical state remains in the ledger tree

**Storage implication**: Ledger Merkle tree grows monotonically with cell count. Checkpoint proofs compress this to a single root commitment, but the state itself must be available for proof generation.

---

## 7. Bottleneck Analysis

### Where Does the System Break First?

**Load scenario**: Increasing transaction throughput in a fixed-size federation.

1. **First bottleneck: Proof generation throughput**
   - At ~700ms per block proof and 1 block/second with n=10: need 10 parallel provers to keep up
   - At higher throughput (multiple turns per block): Effect VM trace grows, proving time increases
   - The proving pipeline is explicitly designed to NOT block consensus, but checkpoint delays accumulate

2. **Second bottleneck: Predecessor vector size (n scaling)**
   - At n=100: each block carries 3.2 KB of predecessor hashes
   - Cordiality check requires all blocks to reference >2n/3 predecessors
   - This is a hard protocol requirement, not just an implementation choice
   - Mitigation: BLS aggregate signatures over predecessor sets (not implemented)

3. **Third bottleneck: State storage growth**
   - Note tree and cell accumulator grow unbounded
   - Checkpoint proofs enable header pruning but state snapshots are needed
   - At high throughput: state growth dominates storage

4. **Fourth bottleneck: Cross-federation latency**
   - Pipeline pipelining helps but doesn't eliminate physical network delays
   - Store-and-forward adds TTL-bounded buffering
   - Promise depth limited by cascading-break probability

### The Sweet Spot

Based on the analysis:

| Dimension | Sweet Spot | Justification |
|-----------|-----------|---------------|
| Federation size | 4-20 nodes | Predecessor vectors manageable, 3 rounds to finality |
| Effects per turn | 4-16 | Single power-of-2 trace, provable on commodity hardware |
| Cross-fed hops | 1-2 | Pipeline depth manageable, latency acceptable |
| Checkpoint interval | 128 blocks | 45s proving with 8 cores, matches natural epoch |
| Concurrent sessions | 100-500 | ~50 MB RAM for CapTP state, manageable |

---

## 8. Top 3 Scalability Bottlenecks and Mitigations

### Bottleneck 1: Consensus Predecessor Vectors (O(n) per block)

**Impact**: Blocks grow linearly with federation size. At n=100, each block carries 3.2 KB of hash pointers. The cordiality requirement (`>2n/3` acknowledgments per round) forces this.

**Mitigations**:
1. **Threshold acknowledgment**: Only reference a random 2n/3 subset (probabilistic cordiality). Reduces per-block overhead from O(n) to O(2n/3) -- modest improvement.
2. **Frontier compression**: Reference a Merkle root of the previous round's blocks rather than individual IDs. Reduces from n*32 bytes to 32 bytes + Merkle proof on demand.
3. **Hierarchical federations**: Keep individual federations small (4-20); use cross-federation bridges for wider coordination. This is architecturally supported by CapTP already.
4. **Sparse acknowledgment**: Reference only tips-per-creator (n entries, one per participant) rather than all blocks. This is what `Frontier` in `dissemination.rs` already does for sync -- extend to block structure.

### Bottleneck 2: Proof Generation Latency and Throughput

**Impact**: At ~700ms per block proof, a 10-node federation producing 10 blocks/second needs 7 provers running continuously. The scan state checkpoint (45s with 8 cores for 128 blocks) adds background load.

**Mitigations**:
1. **Tiered proving** (already partially implemented via `proof_tier.rs`):
   - Immediate: constraint-only verification (fast, weaker)
   - Background: full STARK proof
   - Checkpoint: folded/recursive proof
2. **Proof delegation**: Phones submit effects; a federation prover generates the STARK. The proof is still verifiable by anyone.
3. **Batched proving**: Accumulate multiple turns into one larger trace rather than proving each separately. A 64-row trace is only ~2x slower than a 16-row trace (FRI cost is logarithmic).
4. **GPU acceleration**: BabyBear NTT and Poseidon2 permutations are highly parallelizable. Plonky3 already targets GPU backends.

### Bottleneck 3: Unbounded State Growth (Notes + Cells)

**Impact**: The note commitment tree and cell ledger grow monotonically. Even with checkpoint pruning of block payloads, the state itself must persist for proof generation and verification.

**Mitigations**:
1. **State expiry**: Notes unclaimed for N epochs are expired (require re-issuance). This bounds the note tree.
2. **Cell retirement**: Cells with zero balance and no imports for N epochs are archived (state compressed to commitment only, full state evicted).
3. **Incremental state snapshots**: Only store deltas between checkpoints rather than full state at each checkpoint.
4. **Erasure coding for state distribution** (already in `storage/src/erasure.rs`): Shard state across federation members so no single node stores everything. K-of-2K availability with random sampling.
5. **State rent / metering** (already in `storage/src/metering.rs`): Computron costs for storage incentivize cleanup.

---

## Summary Table

| Dimension | Current Limit | Mitigation Path |
|-----------|--------------|-----------------|
| Federation size | ~20 nodes efficiently | Frontier compression, hierarchical federations |
| Proof generation | ~700ms per block | Batching, GPU, delegation |
| Finality latency | 3 rounds (~3s at 1s/round) | Already near-optimal for BFT |
| Cross-fed transfer | 2-3 RT first time, 1 RT pipelined | Promise pipelining (implemented) |
| Storage growth | ~432 MB/day at n=10 | Checkpoints + pruning (planned) |
| Sessions per node | ~500 before RAM dominates | Connection pooling, session eviction |
| Phone proving | 500ms-5s per simple turn | Proof delegation for complex turns |
| Note tree depth | ~20 at 1M notes | State expiry, archival |
