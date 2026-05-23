# Blocklace Validity Proof: Verified State Compression

## Problem Statement

A node joining the network today must replay all historical blocks from genesis
to validate the current state. With unbounded growth, this becomes untenable.
We want:

```
Genesis -> [N finalized turns] -> Checkpoint at height H
    -> ONE constant-size proof: "genesis -> H is valid"
    -> Delete all blocks below H
    -> New node: verify ONE proof + sync blocks since H
    -> Storage: O(proof_size + recent_blocks) instead of O(all_blocks_ever)
```

## 1. Architecture Overview

```
                         Per-Block Turn Proofs (leaves)
                         ==============================
   Block 1 proof ─┐
                   ├─ Fold(1,2) ─┐
   Block 2 proof ─┘              │
                                 ├─ Fold(1..4) ─┐
   Block 3 proof ─┐              │              │
                   ├─ Fold(3,4) ─┘              │
   Block 4 proof ─┘                             ├─ CHECKPOINT PROOF
                                                │    (genesis -> H)
   Block 5 proof ─┐                             │
                   ├─ Fold(5,6) ─┐              │
   Block 6 proof ─┘              │              │
                                 ├─ Fold(5..8) ─┘
   Block 7 proof ─┐              │
                   ├─ Fold(7,8) ─┘
   Block 8 proof ─┘
```

Three layers:

1. **Leaf proofs** -- one per finalized block, proving the turn's state transition
2. **Scan state** -- incremental binary-tree folding of adjacent proofs
3. **Checkpoint proof** -- the fully-folded root, constant-size via Pickles wrapping

### Differences from Mina

| Aspect | Mina | Breadstuffs |
|--------|------|-------------|
| Block structure | Linear chain | DAG (blocklace, Cordial Miners tau ordering) |
| Per-block content | Coinbase + txns | Turn payload (call forest of effects) |
| Ordering | Trivial (parent hash) | tau function over super-ratified leaders |
| State model | Single global state | Per-cell sovereign states + global ledger |
| Proof system | Pickles (Pasta IPA) | BabyBear STARK + Pickles wrapping |
| Per-block proof | snarked_ledger_hash | FullTurnProof (Effect VM + auth + membership + conservation) |

The key shared insight: you fold incrementally as blocks arrive, not in batch.
A new block's proof becomes a leaf; folding proceeds in the background.

## 2. Per-Block Turn Proof (Leaf)

When a block is finalized by tau, the executor runs its turn. In parallel,
a background prover generates the state transition proof:

```rust
pub struct BlockTransitionProof {
    /// The full turn proof (Effect VM + auth + membership + conservation).
    /// Already exists as `FullTurnProof` from sdk/src/full_turn_proof.rs.
    pub turn_proof: ComposedProof,

    /// The ledger state root BEFORE this block's turn executes.
    pub pre_state_root: [u8; 32],

    /// The ledger state root AFTER this block's turn executes.
    pub post_state_root: [u8; 32],

    /// The block's position in the total order (assigned by tau).
    pub height: u64,

    /// The block ID in the blocklace DAG (for provenance).
    pub block_id: [u8; 32],

    /// Commitment to the nullifier accumulator state after this block.
    pub nullifier_root: [u8; 32],
}
```

The FullTurnProof already covers:
- State transition correctness (Effect VM AIR)
- Actor authorization (Derivation chain)
- Capability membership (Merkle proof)
- Value conservation (balance check)
- Non-revocation (nullifier/revocation proof)

What we add at the block level is the binding to the global state root
(pre/post) and the position in the total order.

### State Root Commitment Structure

```
state_root = Poseidon2(
    ledger_root,          // Merkle root of all cell states
    note_tree_root,       // Merkle root of all note commitments
    nullifier_accumulator,// RSA/Poseidon accumulator of spent nullifiers
    constitution_hash     // Hash of the active constitution
)
```

The checkpoint proof covers ALL of these -- ledger, notes, nullifiers,
and governance state -- in one composite commitment.

## 3. The Fold Circuit

The fold circuit takes two adjacent proofs and merges them:

```rust
/// Proves: "blocks [start..end] correctly transition state from pre to post"
pub struct FoldedBlockProof {
    pub start_height: u64,
    pub end_height: u64,
    pub pre_state_root: [u8; 32],
    pub post_state_root: [u8; 32],
    /// Constant-size after Pickles wrapping
    pub proof: PicklesRecursiveProof,
}
```

### Fold Circuit Constraints

The fold circuit verifies (inside the SNARK):

1. **Left child valid**: Verify left proof covers `[start..mid]`
2. **Right child valid**: Verify right proof covers `[mid+1..end]`
3. **Continuity**: `left.post_state_root == right.pre_state_root`
4. **Height continuity**: `left.end_height + 1 == right.start_height`
5. **Output binding**:
   - `output.start_height = left.start_height`
   - `output.end_height = right.end_height`
   - `output.pre_state_root = left.pre_state_root`
   - `output.post_state_root = right.post_state_root`

### AIR Design

```rust
pub struct BlockFoldAir;

/// Trace width: 12 columns
/// [left_pre(4), left_post(4), right_pre(4), right_post(4),
///  left_start_h, left_end_h, right_start_h, right_end_h,
///  continuity_valid, height_valid]
///
/// Public inputs: [start_height, end_height, pre_state_root(4), post_state_root(4)]
///
/// Core constraints:
///   - continuity_valid = (left_post == right_pre) ? 1 : 0; must be 1
///   - height_valid = (left_end + 1 == right_start) ? 1 : 0; must be 1
///   - pre_state_root == left_pre (boundary)
///   - post_state_root == right_post (boundary)
```

The BabyBear STARK proves this fold, then gets wrapped via STARK-in-Pickles
for constant-size output.

## 4. The Scan State (Incremental Folding)

### Structure

```rust
pub struct ScanState {
    /// Pending proofs at each tree level. Level 0 = leaf proofs.
    levels: Vec<Option<FoldedBlockProof>>,

    /// Configuration: maximum levels before forcing a checkpoint.
    max_depth: usize,

    /// The most recent completed checkpoint proof, if any.
    last_checkpoint: Option<CheckpointProof>,
}
```

### Algorithm

When a new block proof arrives:

```
fn push_leaf(scan: &mut ScanState, block_proof: BlockTransitionProof) {
    let leaf = FoldedBlockProof {
        start_height: block_proof.height,
        end_height: block_proof.height,
        pre_state_root: block_proof.pre_state_root,
        post_state_root: block_proof.post_state_root,
        proof: wrap_to_pickles(block_proof.turn_proof),
    };

    let mut current = leaf;
    for level in 0..scan.levels.len() {
        if let Some(left) = scan.levels[level].take() {
            // Two proofs at this level -- fold them upward
            current = fold(left, current);  // background task
        } else {
            scan.levels[level] = Some(current);
            return;
        }
    }
    // Overflow: all levels were full, push a new level
    scan.levels.push(Some(current));
}
```

This is exactly a binary counter -- each new leaf triggers O(1) amortized
folds, with worst case O(log N) when all levels carry over (like
incrementing 0b111...1).

### Handling DAG Ordering

Unlike Mina's linear chain where block N always follows block N-1, the
blocklace uses tau to assign a total order. The scan state operates on
the **tau-ordered sequence**, not the DAG structure. Once tau orders a block,
it gets a monotonic height and enters the scan state as the next leaf.

If tau reorders (due to late-arriving leaders), the scan state waits for
the canonical ordering before accepting proofs. This is fine because
proving is async background work -- the scan state only processes finalized,
ordered blocks.

## 5. Checkpoint Proof

When the scan state accumulates a full tree of height log2(N):

```rust
pub struct CheckpointProof {
    /// The genesis state root.
    pub genesis_state: [u8; 32],
    /// The checkpoint state root.
    pub checkpoint_state: [u8; 32],
    /// The checkpoint height (number of finalized turns covered).
    pub checkpoint_height: u64,
    /// The nullifier accumulator at checkpoint.
    pub nullifier_root: [u8; 32],
    /// The constitution hash at checkpoint.
    pub constitution_hash: [u8; 32],
    /// One constant-size Pickles proof covering genesis -> checkpoint.
    pub validity_proof: PicklesRecursiveProof,
}
```

### Verification by a New Node

```
fn bootstrap(checkpoint: &CheckpointProof) -> Result<(), Error> {
    // 1. Verify the ONE proof
    verify_pickles(&checkpoint.validity_proof, &[
        checkpoint.genesis_state,
        checkpoint.checkpoint_state,
        checkpoint.checkpoint_height,
    ])?;

    // 2. Accept the checkpoint state as canonical
    ledger.set_state_root(checkpoint.checkpoint_state);
    nullifiers.set_root(checkpoint.nullifier_root);
    constitution.set_hash(checkpoint.constitution_hash);

    // 3. Sync only blocks since the checkpoint
    sync_from_height(checkpoint.checkpoint_height);

    Ok(())
}
```

## 6. Integration with Existing Infrastructure

### Existing Primitives Used

| Component | Role in Validity Proof |
|-----------|----------------------|
| `prove_ivc_stark` (circuit/src/ivc.rs) | Hash-chain accumulation within each fold level |
| `StateTransitionAir` | Verifies Poseidon2 hash chain of state roots |
| `FullTurnProof` (sdk/src/full_turn_proof.rs) | The leaf-level block proof content |
| `compose_aggregate` (pyana-dsl-runtime/src/composition.rs) | Combining sub-proofs into composed proof |
| `STARK-in-Pickles` (circuit/src/backends/stark_in_pickles.rs) | Wrapping BabyBear STARKs to constant-size |
| `SovereignHistory` (cell/src/ledger.rs) | Per-cell IVC accumulation (existing pattern) |
| `PicklesRecursiveProof` (circuit/src/backends/mina/) | Recursively composable constant-size proof |

### Proof Pipeline

```
[Block finalized by tau]
    |
    v
[Background: generate FullTurnProof]
    |  Effect VM + Auth + Membership + Conservation
    v
[Bind to global state: BlockTransitionProof]
    |  pre/post state roots, height, block_id
    v
[Prove with BabyBear STARK: state transition binding]
    |
    v
[Wrap via STARK-in-Pickles: constant-size leaf proof]
    |
    v
[Push into ScanState: incremental fold]
    |  Pair with sibling -> fold circuit -> new constant-size proof
    v
[When tree complete: CheckpointProof]
```

### When to Prove

- **Block proofs**: Background task, spawned after each tau-finalized block.
  Does NOT block consensus. Node operates on unproven blocks and proves
  retroactively.
- **Fold proofs**: Triggered when two adjacent proofs at the same level are
  ready. Parallelizable (independent subtrees fold concurrently).
- **Checkpoint**: Every N blocks (configurable; 128 is a natural power-of-2
  choice). The scan state naturally produces a checkpoint when level 7 fills.

### SovereignHistory Relationship

`SovereignHistory` is per-cell IVC (each cell accumulates its own state
transitions). The blocklace validity proof is the GLOBAL analog -- it
accumulates ALL cells' state transitions ordered by tau. The two are
complementary:

- SovereignHistory: "this cell's state is valid from its genesis"
- CheckpointProof: "the entire ledger's state is valid from global genesis"

A cell's SovereignHistory proof is a sub-proof within each block's
FullTurnProof. The blocklace validity proof composes all such block proofs
into one global attestation.

## 7. Pruning Strategy

### What Can Be Deleted After a Checkpoint

1. **Block payloads below the checkpoint height**: The turn data, call forests,
   effect lists. The proof attests they were valid; the data is no longer needed.
2. **Intermediate proofs in the scan state**: All leaf and fold proofs below
   the checkpoint root are superseded.
3. **Old cell SovereignHistory proofs**: Replaced by the global checkpoint
   which subsumes them.
4. **Old nullifier Merkle branches**: Only the accumulator state at checkpoint
   matters; historical membership proofs are unnecessary.

### What MUST Be Retained

1. **The CheckpointProof itself**: Verifiable statement of validity.
2. **The state snapshot at checkpoint height**: Ledger root, note tree, nullifier
   accumulator, constitution. Without this, the proof has nothing to anchor to.
3. **Block headers**: Lightweight (creator, sequence, predecessors, signature).
   Useful for provenance queries even after payload deletion. (~200 bytes each.)
4. **Blocks since the checkpoint**: Not yet proven; still needed for validation.

### Pruning Timeline

```
Height:   0      50     100    128    150    200    256
          |------|------|------|------|------|------|
          genesis              CP1                 CP2

At CP1 (height 128):
  - Retain: CP1 proof, state at 128, blocks 129..now, all headers
  - Delete: block payloads 0..127, intermediate scan state proofs

At CP2 (height 256):
  - Retain: CP2 proof, state at 256, blocks 257..now
  - Delete: CP1 proof (superseded by CP2), block payloads 128..255
  - Note: CP2's proof transitively covers genesis->256
```

### Configurable Retention Policy

Nodes choose how many checkpoint epochs to keep:

- **Archive node**: Keep everything (no pruning).
- **Full node**: Keep last 2 checkpoints + all blocks since.
- **Light node**: Keep only the latest checkpoint proof + recent blocks.
  Minimal storage: ~5 KiB (proof) + recent blocks.

## 8. Latency and Parallelism Analysis

### Per-Block Proof Timing

| Component | Estimated Time |
|-----------|---------------|
| Effect VM STARK (4-16 effects) | ~300-500 ms |
| Authorization STARK | ~100 ms |
| Membership STARK | ~100 ms |
| Conservation STARK | ~50 ms |
| Compose aggregate | ~50 ms |
| **Total per-block proof** | **~600-800 ms** |

### Fold Operation Timing

| Component | Estimated Time |
|-----------|---------------|
| Fold circuit (verify 2 proofs + continuity) | ~400-600 ms |
| STARK-in-Pickles wrapping | ~1-2 s |
| **Total per-fold** | **~1.5-2.5 s** |

### Checkpoint Generation (128-block epoch)

```
128 leaf proofs:           128 * 700ms = ~90s (parallel with 8 cores: ~11s)
64 level-1 folds:          64 * 2s     = ~128s (parallel: ~16s)
32 level-2 folds:          32 * 2s     = ~64s (parallel: ~8s)
16 level-3 folds:          16 * 2s     = ~32s (parallel: ~4s)
8 level-4 folds:           8 * 2s      = ~16s (parallel: ~2s)
4 level-5 folds:           4 * 2s      = ~8s (parallel: ~1s)
2 level-6 folds:           2 * 2s      = ~4s (parallel: ~0.5s)
1 level-7 fold:            1 * 2s      = ~2s

Total sequential:          ~344s (~5.7 min)
Total with 8 cores:        ~45s
```

With 8 cores, a checkpoint covering 128 blocks completes in under a minute
of background work. Block production at 1 block/second means the prover
has 128 seconds of real time to complete -- well within budget even with
4 cores.

### What If Proving Falls Behind?

The scan state accumulates pending leaves. If blocks arrive faster than
proofs, the pending queue grows. This is acceptable:

- Consensus is NEVER blocked by proving (proofs are async background work)
- The node operates on unproven state (validated by re-execution, not ZK)
- When proving catches up, the scan state absorbs the backlog
- Worst case: an epoch's checkpoint is delayed by the proving backlog

If sustained proving throughput cannot keep pace with block production,
the checkpoint interval should be increased (256, 512 blocks) to spread
folding work over more time.

## 9. Implementation Plan

### Phase 1: Block Transition Binding (Week 1-2)

**Goal**: Generate per-block proofs that bind FullTurnProof to global state.

1. Add `BlockTransitionProof` struct to `circuit/src/block_transition_air.rs`
   (extends the existing column layout constants)
2. Create `BlockTransitionAir` that constrains pre/post state root linkage
3. Integrate with `FullTurnProof` -- the composed proof includes state root
   binding as an additional sub-proof
4. Wire into the executor: after `apply_turn`, emit the witness for proving

### Phase 2: Scan State Data Structure (Week 2-3)

**Goal**: Binary-tree accumulator that pairs adjacent proofs.

1. Define `ScanState` struct and push/fold operations
2. Implement level-carry logic (binary counter pattern)
3. Add persistence (serialize scan state to `pyana-store`)
4. Handle edge cases: node restart, concurrent block arrival

### Phase 3: Fold Circuit (Week 3-5)

**Goal**: A STARK circuit that verifies two child proofs and outputs a merged proof.

1. Design `BlockFoldAir` implementing `StarkAir` trait
2. State root continuity constraint (left.post == right.pre)
3. Height continuity constraint (left.end + 1 == right.start)
4. Recursive verification: in-circuit verification of child proofs
   - Start with "optimistic": trust child proof hashes, verify full proof
     out-of-circuit (hybrid approach while in-circuit verification matures)
   - End goal: full in-circuit STARK verification via STARK-in-Pickles

### Phase 4: Pickles Wrapping for Constant Size (Week 5-7)

**Goal**: Fold circuit output wrapped to constant-size via STARK-in-Pickles.

1. Use existing `wrap_stark_in_pickles` from `backends/stark_in_pickles.rs`
2. Ensure fold circuit fits in Kimchi domain (target: 2^15 rows)
3. Test: fold 2 wrapped proofs -> 1 wrapped proof -> verify
4. Recursive composition: folded proof wraps and becomes input to next fold

### Phase 5: Checkpoint Generation and Verification (Week 7-8)

**Goal**: End-to-end checkpoint proof generation.

1. Define `CheckpointProof` struct with genesis/checkpoint binding
2. ScanState triggers checkpoint when tree is complete
3. Verifier API: `verify_checkpoint(proof) -> Result<CheckpointState, Error>`
4. Integration test: generate 128 mock blocks, fold to checkpoint, verify

### Phase 6: Pruning and Node Bootstrap (Week 8-10)

**Goal**: Nodes can prune historical data and bootstrap from checkpoints.

1. Pruning logic in `pyana-store`: delete block payloads below checkpoint
2. Bootstrap protocol: fetch latest checkpoint proof + blocks since
3. Header retention: keep lightweight block headers for DAG provenance
4. Retention policy configuration (archive/full/light modes)

### Phase 7: Background Proving Integration (Week 10-12)

**Goal**: Proving runs continuously as blocks are finalized, without
blocking consensus or execution.

1. Proving worker pool (configurable parallelism)
2. Priority queue: leaf proofs first, then folds bottom-up
3. Backpressure: if proving falls behind, increase checkpoint interval
4. Metrics: proving latency, queue depth, checkpoint completion time

## 10. Security Considerations

### Soundness

The checkpoint proof's soundness reduces to:
1. STARK soundness (128-bit, from FRI + boundary constraints + PoW)
2. Pickles/Kimchi soundness (IPA commitment scheme over Pasta)
3. Poseidon2 collision resistance (state root integrity)

A forged checkpoint proof requires breaking one of these.

### The Fold-Validity Gap

The existing `ValidatedIvcProof` pattern (from `circuit/src/ivc.rs`) shows
how to close the gap between "hash chain is valid" and "each step was valid":
per-step membership proofs. The same pattern applies at the block level:

- The fold circuit does NOT re-execute the turn. It verifies the
  BlockTransitionProof, which itself is a composed STARK covering the
  full turn validity.
- The leaf proof IS the FullTurnProof. No additional trust is needed.
- Continuity (left.post == right.pre) is an algebraic constraint.

### Equivocation and Reorgs

The blocklace handles equivocation via the Cordial Miners protocol. The
validity proof operates ONLY on blocks that tau has finalized (super-ratified
leaders). Finality is guaranteed by the BFT assumption (>2/3 honest); once
final, the ordering is permanent.

If a block is never finalized (orphaned in the DAG), it never enters the
scan state.

### Checkpoint Forgery

A malicious node cannot produce a valid CheckpointProof with incorrect
state because:
1. The genesis state root is a public input (hardcoded/well-known)
2. Each fold verifies child proofs cryptographically
3. State continuity is algebraically enforced
4. The final Pickles proof is constant-size but carries the full chain's
   computational integrity transitively

### Long-Range Attacks

A new node bootstrapping from a checkpoint must trust that the checkpoint
proof was generated honestly (same genesis). This is equivalent to trusting
the genesis block hash -- which is a parameter of the network. The checkpoint
proof's public inputs include the genesis state root, making long-range
substitution detectable.
