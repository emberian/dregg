# Recursive STARK Composition for Pyana

Design for O(1) history verification: proving "the entire history from genesis
to now is valid" in a single proof.

---

## 1. Architecture Overview

### The Core Idea

Every finalized block produces a STARK proof that the state transition was
correctly applied. Recursive composition chains these proofs:

```
Proof_0: "Genesis -> State_1 is valid"
Proof_1: "Proof_0 is valid AND State_1 -> State_2 is valid"
Proof_2: "Proof_1 is valid AND State_2 -> State_3 is valid"
...
Proof_N: "Proof_{N-1} is valid AND State_{N-1} -> State_N is valid"
```

`Proof_N` proves the ENTIRE history. A new node only needs `Proof_N` + current
state to bootstrap with full state transition assurance.

### What Pyana Already Has

The recursive infrastructure is partially built:

1. **Per-step IVC** (`circuit/src/ivc.rs`): Accumulates fold-step proofs via
   Poseidon2 hash chain. Produces constant-size `IvcProof` over BabyBear. Real
   STARK proofs via `StateTransitionAir`.

2. **Recursive verifier AIR** (`circuit/src/plonky3_verifier_air.rs`): True
   in-circuit STARK verification. Encodes Fiat-Shamir transcript replay, Merkle
   path verification, FRI folding, and constraint evaluation as AIR constraints.
   12-column trace, tested end-to-end with `RecursiveProver::prove_recursive()`.

3. **Proof aggregation** (`circuit/src/plonky3_recursion.rs`): Hash-chain
   aggregation of N proofs into 1 via `AggregationAir`. Supports 2-to-1 and
   tree-style compression. Currently requires inner proofs for full verification.

4. **SP1 EVM wrapping** (`chain/` crate): Wraps STARK proofs in SP1 for Groth16
   output. Mock infrastructure in place, real proving via `--features prove`.

5. **Federation blocks** (`federation/src/types.rs`): `RevocationBlock` commits
   to `pre_state_root`, `post_state_root`, `note_tree_root`, `nullifier_set_root`.
   Block hash chain already binds to state at every height.

### What Needs Building

```
┌──────────────────────────────────────────────────────────────────────┐
│                   Block N's Recursive Proof                           │
│                                                                      │
│  ┌────────────────────┐    ┌─────────────────────────────────┐     │
│  │  Verify Proof_{N-1} │    │ Prove State_{N-1} -> State_N    │     │
│  │  (recursive STARK   │    │ (nullifier insertions,          │     │
│  │   verifier AIR)     │    │  note tree updates,             │     │
│  │                     │    │  state root recomputation)      │     │
│  └─────────┬──────────┘    └───────────────┬─────────────────┘     │
│            │                                │                        │
│            └────────────────┬───────────────┘                        │
│                             │                                        │
│                    ┌────────▼────────┐                               │
│                    │  Combined Proof  │                               │
│                    │  "All history    │                               │
│                    │   is valid"      │                               │
│                    └─────────────────┘                               │
└──────────────────────────────────────────────────────────────────────┘
```

The gap is bridging the per-agent IVC (fold chain proofs) to the per-block
federation state transition proof that recursively verifies its predecessor.

---

## 2. Plonky3 Recursion: Capabilities and Costs

### What `plonky3-recursion` Provides

From our research (`docs/research-recursive-stark.md`):

- Verifies Plonky3 uni-STARK and batch-STARK proofs inside another Plonky3 STARK
- BabyBear as native recursion field (no field emulation needed)
- Full FRI PCS verification in-circuit (Merkle openings, FRI folds, Fiat-Shamir)
- Supports both linear chaining and 2-to-1 aggregation (tree-style)
- After enough layers, reaches **steady-state proof size** (~100-200 KiB)

### Cost Model

Our existing `RecursiveVerifierAir` (already tested) demonstrates the overhead:

| Component | Trace Rows | Description |
|-----------|-----------|-------------|
| Fiat-Shamir transcript | 3 rows | Absorb commitments, derive challenges |
| Merkle path verification | D rows | D = tree depth (4-16 levels) |
| FRI folding | L rows | L = number of FRI layers (4-8) |
| Constraint evaluation | 1 row | Position validity check |
| Public input binding | P rows | P = number of public inputs |

**Total verifier trace**: ~16-32 rows (current simplified, single-query)

For production (50 FRI queries):
- ~50x Merkle sections + ~50x FRI fold sections
- **Estimated**: ~800-1600 rows for the verifier alone
- Combined with the transition proof: ~2000-4000 total rows
- At BabyBear trace width 12: ~48-96 KiB trace data before FRI
- **Proof generation time**: ~0.5-2 seconds on M-series (estimated)

### Steady-State Behavior

After 2-3 levels of recursion, the proof size stabilizes:

```
Level 0: state transition proof              → ~38 KiB
Level 1: verify prev + transition            → ~100 KiB
Level 2: verify (verify prev + transition)   → ~120 KiB
Level 3+: stable at ~120-150 KiB             (verifier overhead dominates)
```

The logarithmic growth in STARK proof size (FRI requires O(log N) queries)
stabilizes because the inner verifier circuit has fixed size regardless of
what it verified. This is the key property enabling O(1) history proofs.

### Recursion Depth Limits

Unlike SNARKs (which have strict recursion stack constraints), STARK recursion
depth is limited only by proving time. Each level adds:
- One verifier trace generation (~ms)
- One STARK proving pass (~0.5-2s)

For linear chaining (one block at a time), depth = chain height. At 1 block/sec
with 1s proving time, the pipeline stays ahead. No hard depth limit.

### Current Implementation Gaps

Our `RecursiveVerifierAir` currently:
1. Verifies only a single FRI query (not 50) — reduces soundness guarantee
2. Uses simplified constraint evaluation (position validity only)
3. Has fixed Merkle depth (not variable)
4. Simulates witness extraction (does not decompose real Plonky3 proof internals)

Production requires:
- Full multi-query verification or repeated single-query proofs
- Generic constraint evaluation relay
- Integration with Plonky3's `p3-recursion` crate (when stabilized)

---

## 3. BLS-in-STARK Analysis

### The Problem

Each pyana block has a `QuorumCertificate` — a threshold BLS12-381 signature
proving supermajority agreement. Full Mina-equivalent succinctness requires
verifying this signature inside the recursive STARK.

### Cost Breakdown

BLS12-381 pairing verification over BabyBear (p = 2^31 - 2^27 + 1):

| Operation | BabyBear Constraints | Notes |
|-----------|---------------------|-------|
| BLS12-381 field element (1) | 13 limbs | 381-bit / 31-bit |
| Field multiplication (1) | ~169 limb muls | 13 x 13 cross-products + carry |
| G1 point addition | ~3000 constraints | 3 field muls + inversions |
| G2 point addition (twist) | ~12000 constraints | Over Fp2 (double cost) |
| Miller loop iteration (1) | ~50000 constraints | Line eval + sparse mul |
| Full Miller loop (64 iters) | ~3.2M constraints | 64 doublings + ~32 additions |
| Final exponentiation | ~15-30M constraints | Frobenius + powering |
| **Total pairing verification** | **~50-100M constraints** | |

### Proving Time Estimates

| Platform | Throughput | BLS Pairing Time |
|----------|-----------|-----------------|
| Apple M4 (CPU) | ~1-2M constraints/sec | 25-100 seconds |
| Apple M4 (GPU via Metal) | ~5-10M constraints/sec | 5-20 seconds |
| NVIDIA H100 (SP1 GPU cluster) | ~50-100M constraints/sec | 0.5-2 seconds |
| Custom FPGA | ~200M constraints/sec | 0.25-0.5 seconds |

### Verdict: Not Practical Today for Per-Block

At 25-100 seconds per block on commodity hardware, BLS-in-STARK is not viable
for real-time block production. However:

1. **It becomes practical with GPU acceleration** (~5-20s on M4 GPU, <2s on H100)
2. **Epoch-boundary checkpoints** can amortize: verify BLS once per epoch (128-256
   blocks), amortizing the 25-100s proving cost across many blocks
3. **SP1 with precompiles**: SP1 v4+ includes BLS12-381 precompiles that reduce
   cycle count by 10-50x (from ~80M cycles to ~2-8M cycles)

### When BLS-in-STARK Becomes Feasible

| Timeline | Hardware | Constraint Budget | Per-Block? |
|----------|----------|------------------|-----------|
| 2026 H2 | M4 GPU (Metal) | 10M/sec | No (10s) |
| 2027 H1 | SP1 v5 precompiles | 50M/sec equivalent | Borderline (1-2s) |
| 2027 H2 | Dedicated FPGA prover | 200M/sec | Yes (<1s) |
| 2028+ | Custom ASIC / proof market | 1B/sec | Yes (trivial) |

### Pragmatic Decision

**Skip BLS verification in the recursive proof for now.** The recursive STARK
proves state transition correctness. The QC signature is verified out-of-band
by bootstrapping nodes (just check the BLS signature directly). This matches the
trust model described in `docs/succinct-history.md` Section 5.4 "Option A."

The combined trust model:
- **State transitions**: proven by STARK (trustless, computationally sound)
- **Federation agreement**: verified by QC signature check (trust federation keys)
- **Together**: "these transitions are valid AND the federation agreed on them"

---

## 4. The SP1 Path: Practical Recursive Verification

### Architecture

SP1 is Succinct's production zkVM. It proves arbitrary Rust programs:

```
┌─────────────────────────────────────────────────────────────────┐
│  SP1 Guest Program (Rust, compiled to RISC-V)                   │
│                                                                 │
│  fn main() {                                                    │
│    let prev_proof = sp1_zkvm::io::read::<SP1Proof>();          │
│    let block = sp1_zkvm::io::read::<Block>();                  │
│    let pre_state = sp1_zkvm::io::read::<StateRoot>();          │
│                                                                 │
│    // Verify previous proof (recursive!)                        │
│    sp1_zkvm::lib::verify::verify_sp1_proof(&prev_proof);       │
│                                                                 │
│    // Apply block transitions                                   │
│    let post_state = apply_block(pre_state, &block);            │
│                                                                 │
│    // Commit public outputs                                     │
│    sp1_zkvm::io::commit(&post_state);                          │
│  }                                                              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
         SP1 Proving Pipeline: Core → Compress → Shrink → Groth16
                              │
                              ▼
                    ~260 bytes final proof
                    Verifiable on Ethereum (~200k gas)
```

### SP1 Recursion Pipeline

SP1 has native recursion support:

1. **Core proving**: Execute RISC-V, produce initial STARK proofs (many shards)
2. **Compress**: Aggregate shards into a single STARK proof (~1MB)
3. **Shrink**: Reduce to BN254-friendly STARK (~200KB)
4. **Wrap/Groth16**: Final constant-size proof (~260 bytes)

The `sp1_zkvm::lib::verify::verify_sp1_proof()` call inside the guest triggers
SP1's deferred proof mechanism — the recursive verification is handled
natively by the proving infrastructure.

### SP1 v4+ Features Relevant to Pyana

| Feature | Benefit |
|---------|---------|
| BLS12-381 precompile | ~10-50x speedup for BLS verification in-guest |
| Aggregation server | Compose N proofs into 1 without custom recursion |
| Continuation | Long programs split into shards, proven in parallel |
| On-chain verifier | Deployed on all major EVM chains |
| Network proving | Outsource to GPU clusters (10-100x faster) |

### Integration with Pyana's Existing `chain/` Crate

The `chain/` crate already has:
- `wrap_for_evm()` — wraps a STARK proof via SP1
- `EvmProof` — the Groth16 output structure
- Mock mode for testing, real mode with `--features prove`
- Contract addresses for Base/Ethereum

Extending to recursive federation proofs:

```rust
// New guest program: verify_block_chain.rs
fn main() {
    // Read inputs
    let prev_proof: Option<SP1Proof> = sp1_zkvm::io::read();
    let block_header: BlockHeader = sp1_zkvm::io::read();
    let pre_state_root: [u8; 32] = sp1_zkvm::io::read();
    let post_state_root: [u8; 32] = sp1_zkvm::io::read();
    let events: Vec<RevocationEvent> = sp1_zkvm::io::read();

    // Recursive step: verify previous proof if present
    if let Some(prev) = prev_proof {
        sp1_zkvm::lib::verify::verify_sp1_proof(&prev);
        // Extract previous post_state_root from prev proof's public values
        let prev_post_root = extract_post_root(&prev);
        assert_eq!(prev_post_root, pre_state_root);
    }

    // Apply state transition
    let computed_post_root = apply_events(pre_state_root, &events);
    assert_eq!(computed_post_root, post_state_root);

    // Commit: genesis_root, current_root, height
    sp1_zkvm::io::commit(&block_header.height);
    sp1_zkvm::io::commit(&post_state_root);
}
```

### SP1 Proving Time Estimates

| Operation | CPU (single core) | GPU (H100) | Network (Succinct) |
|-----------|------------------|------------|-------------------|
| Block transition (simple) | 10-30s | 1-3s | <1s |
| Block transition + recursive verify | 30-90s | 3-10s | 1-3s |
| BLS pairing (with precompile) | 5-15s | 0.5-2s | <0.5s |
| Full pipeline (transition + BLS) | 60-180s | 5-15s | 2-5s |

### Practical Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| Prototype SP1 guest | 2 weeks | Guest program verifying state transitions |
| Recursive composition | 2 weeks | Guest calling `verify_sp1_proof()` for chaining |
| GPU proving pipeline | 2 weeks | Integration with Succinct's network prover |
| Production deployment | 4 weeks | Verifier contract on Base, monitoring, fallback |
| **Total** | **10 weeks** | End-to-end recursive history → EVM verification |

---

## 5. Folding Alternative: Nova-Style Accumulation

### How Folding Works

Instead of full STARK recursion (verify previous proof inside new proof),
folding ACCUMULATES commitments without verifying:

```
Traditional recursion:
  Step i: Generate proof P_i that {P_{i-1} is valid AND T_i is valid}
  Cost: prove(verify_circuit + transition_circuit)  ← EXPENSIVE

Folding:
  Step i: Fold accumulator A_{i-1} with instance x_i → A_i
  Cost: O(group_operations)  ← CHEAP
  Final: Verify A_N once at the end
```

Per-step cost comparison:
- Full STARK recursion: ~0.5-2 seconds (verify previous STARK in new STARK)
- Nova folding: ~5-50 milliseconds (field operations + MSM, no inner verification)
- Ratio: **10-400x cheaper per step**

### Nova/HyperNova Applicability

From our research (`docs/research-nova-folding.md`):

- **Nova**: R1CS only. Our fold step is ~1000 R1CS constraints. Works perfectly.
- **HyperNova**: CCS (captures AIR directly). Could fold our AIR without R1CS conversion.
- **Folding does NOT work for arbitrary AIR/FRI**: Cannot directly fold Plonky3 proofs.

The critical distinction: **folding works for the STEP RELATION, not for proof
verification**. We can fold the state transition computation itself, but the
final accumulator still needs one STARK/SNARK verification at the end.

### How Pyana Could Use Folding

```
Block 1: Fold state_transition_1 into accumulator → A_1
Block 2: Fold state_transition_2 into accumulator → A_2
...
Block N: Fold state_transition_N into accumulator → A_N

Checkpoint: Generate ONE Spartan/STARK proof that A_N is a valid accumulator
```

The running accumulator (A_i) is O(1) size (a few group elements + field elements).
It commits to ALL prior transitions without proving them individually.

### Cost Model

| Operation | Nova (Pallas/Vesta) | HyperNova (CCS) |
|-----------|-------------------|-----------------|
| Per-step fold | ~5ms | ~10ms |
| Accumulator size | ~2 group elements + scalar | ~4 group elements |
| Final compression (Spartan) | ~2-5 seconds | ~2-5 seconds |
| Verification | ~5ms | ~5ms |
| Proof size (final) | ~10-20 KiB | ~10-20 KiB |

### Comparison: Folding vs. STARK Recursion

| Property | Nova Folding | STARK Recursion | SP1 Recursion |
|----------|-------------|-----------------|---------------|
| Per-step cost | 5ms | 500-2000ms | 30-90s (CPU) |
| Final verification cost | 2-5s (one Spartan proof) | 5ms (one STARK verify) | 200k gas (on-chain) |
| Proof size | ~10-20 KiB | ~100-200 KiB | ~260 bytes |
| Post-quantum | No (EC-based) | Yes (hash-based) | Yes (via STARK layer) |
| EVM-verifiable | With BN254 + MicroSpartan | No (need wrapping) | Yes (native) |
| Existing infra in pyana | Nova backend in circuit/ | RecursiveVerifierAir | chain/ crate |
| Complexity | Medium | High | Low (SP1 handles it) |

### Recommendation on Folding

Nova folding is **the best per-step cost** but has tradeoffs:
- Not post-quantum (Pallas/Vesta curves)
- Requires a final compression step (adds 2-5s latency at verification time)
- Not directly EVM-verifiable without BN254 curve switch

**Use folding for**: Fast per-block accumulation during normal operation.
Validators fold each block's transition in ~5ms, maintaining a running
accumulator.

**Use STARK recursion for**: Epoch-boundary checkpoint proofs and EVM
settlement. Every E blocks, generate a full recursive STARK from the
folded accumulator, then wrap via SP1 for on-chain verification.

This hybrid approach gives the best of both:
- ~5ms per-block overhead (folding)
- ~2-5 second checkpoint proof (Spartan compression)
- ~260 byte EVM proof at epoch boundaries (SP1 wrapping)

---

## 6. Comparison to Mina's Pickles

### Mina's Architecture

Mina uses **Pickles**: recursive SNARKs over the Pasta curve cycle (Pallas/Vesta):

```
Block k: Pickles proof = wrap(step(verify(Block_{k-1}.proof), transition_k))
```

Key properties:
- **Curve cycle**: Pallas and Vesta are a cycle (Pallas's scalar field = Vesta's base field).
  This allows "stepping" on one curve and "wrapping" on the other — no field emulation.
- **IPA commitments**: Inner Product Argument (not KZG). Deferred verification
  trick: accumulate IPA openings without verifying, check once at the end.
- **Constant size**: SNARK proofs are ~1 KiB regardless of circuit size.
- **No FRI**: Polynomial commitment via IPA on groups, not FRI on hash trees.

### What Transfers to Pyana

| Mina Component | Pyana Equivalent | Gap |
|---------------|-----------------|-----|
| Pickles recursion (prove proof valid) | `RecursiveVerifierAir` (prove STARK valid) | Width: Plonky3 trace 12 cols vs Pickles 15 wires |
| Step circuit (transition logic) | `StateTransitionAir` / `NullifierInsertionAir` | Pyana's is simpler (no arbitrary zkApp logic) |
| Wrap circuit (curve change) | Not needed (same field) | BabyBear is self-recursive |
| IPA deferred verification | Hash-chain accumulation | Pyana's is weaker but field-native |
| Snarked ledger | State snapshot (note tree + nullifier set) | Direct mapping |
| Bootstrap controller | `LightClientProof` + state download | Already works |
| Transition frontier (forks) | **Not needed** (BFT = instant finality) | Pyana advantage |
| Scan state (parallel snarking) | **Not needed** (simpler transition) | Pyana advantage |
| SNARK workers / proof market | Federation members prove (or SP1 network) | Different economic model |

### Key Differences

1. **BFT vs. probabilistic finality**: Pyana has NO forks. This eliminates the
   transition frontier, fork choice, and staged ledger — massive simplification
   over Mina.

2. **BabyBear vs. Pasta**: Pyana uses BabyBear (2^31 - 2^27 + 1) with FRI.
   Mina uses Pallas/Vesta with IPA. BabyBear is faster for proving (smaller
   field, hardware-friendly) but produces larger proofs (STARK = O(log N) vs
   SNARK = O(1)).

3. **Post-quantum**: Pyana's STARK path is post-quantum secure (hash-based).
   Mina's Pickles relies on discrete log hardness (broken by quantum computers).

4. **EVM compatibility**: Pyana wraps via SP1 → Groth16 (~260 bytes, ~200k gas).
   Mina wraps via Kimchi → Groth16 (similar size, similar cost, less mature
   tooling for EVM).

5. **Transition complexity**: Mina proves arbitrary zkApp execution (15-wire
   Plonkish circuit per account update). Pyana proves nullifier insertion +
   note tree update + state root computation — fundamentally simpler.

### What Pyana Gets for Free (vs. Mina)

- **No transition frontier maintenance**: BFT finality means one canonical chain always.
- **No scan state scheduling**: No need to parallelize proving across workers.
- **No staged ledger prediction**: No speculative execution of unproven blocks.
- **Simpler bootstrap**: `Proof + state_snapshot` — no fork resolution needed.
- **Faster per-block**: Simpler transition logic = smaller circuit = faster proving.

### What Pyana Must Build That Mina Already Has

- **In-circuit signature verification**: Mina's curve cycle makes Schnorr/ECDSA cheap.
  Pyana needs BLS-in-BabyBear (expensive) or a scheme change.
- **Deferred verification accumulation**: Mina's IPA trick is elegant. Pyana must use
  hash-chain or folding (less algebraically elegant, but works).
- **Proven history from genesis**: Mina has shipped this since 2021. Pyana's recursive
  STARK is still in prototype.

---

## 7. Recommendation: Pyana's Path

### Decision Framework

| Criterion | Weight | STARK Recursion (Plonky3) | SP1 Aggregation | Nova Folding |
|-----------|--------|--------------------------|-----------------|--------------|
| Time to production | High | 4-8 months | 10 weeks | 3-4 months |
| Post-quantum | Medium | Yes | Yes (STARK layer) | No |
| Per-block overhead | High | 0.5-2s | 30-90s (CPU) | 5ms |
| Proof size (final) | Medium | ~150 KiB | ~260 bytes | ~10-20 KiB |
| EVM settlement | High | Need wrapping | Native | Need wrapping |
| Existing code reuse | Medium | High (RecursiveVerifierAir) | Medium (chain/ crate) | Medium (nova backend) |
| Operational complexity | Medium | Medium (self-hosted) | Low (Succinct network) | Low (lightweight) |

### Recommended Hybrid Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Pyana Recursive Proof Architecture                     │
│                                                                         │
│  Per-Block (real-time):                                                 │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │  Nova Folding: accumulate each block's transition into A_i       │  │
│  │  Cost: ~5ms per block. Running accumulator = O(1) size.         │  │
│  │  Proves: state transitions from genesis are valid (folded).     │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                              │                                          │
│  Per-Epoch (async, every E blocks):                                    │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │  Plonky3 STARK: compress accumulated proof A_E into a STARK     │  │
│  │  Cost: ~2-5 seconds. Proves: all E blocks' transitions valid.   │  │
│  │  This is the "checkpoint proof" for fast bootstrap.             │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                              │                                          │
│  Per-Settlement (on-demand):                                           │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │  SP1 Groth16: wrap checkpoint STARK for EVM verification        │  │
│  │  Cost: ~30-90s (CPU) or ~3-10s (GPU). Output: ~260 bytes.      │  │
│  │  Verifiable on Base/Ethereum for ~200k gas.                     │  │
│  └──────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────┘
```

This gives:
- **O(1) per-block cost**: 5ms folding (negligible vs block production time)
- **O(1) bootstrap**: Download latest checkpoint proof + state snapshot
- **O(1) on-chain verification**: 260-byte Groth16 proof, 200k gas
- **Post-quantum core**: The Plonky3 STARK layer is hash-based
- **EVM compatibility**: SP1 wrapping to Groth16 (already scaffolded)

---

## 8. Three-Phase Roadmap

### Phase 1: Per-Block State Transition Proofs (Weeks 1-6)

**Goal**: Each finalized block produces a STARK proof that
`post_state_root = apply(pre_state_root, events)`.

**Work items**:

1. **NullifierInsertionAir** — Prove sorted insertion into the nullifier set.
   The nullifier set is an append-only sorted structure. Proving insertion means
   showing: (a) the nullifier is not already present (non-membership), (b) inserting
   at the correct sorted position produces the new root.

2. **NoteTreeUpdateAir** — Prove append to the note commitment tree. Reuse
   `P3MerklePoseidon2Air` (already exists and tested) for Merkle path verification
   during append.

3. **BlockTransitionAir** — Compose nullifier insertions + note tree updates
   into a single per-block proof. Public inputs: `[pre_state_root, post_state_root,
   note_tree_root, nullifier_set_root, block_hash]`.

4. **Prover integration** — Wire `BlockTransitionAir` into the consensus
   finalization path. The proposer generates the proof alongside the block.
   Validators verify the proof before voting (adds ~50ms to validation).

**Output**: Each block has an attached `BlockTransitionProof` (~38-50 KiB STARK).
Nodes can verify individual blocks without re-executing.

**Trust model change**: Validators that verify the proof before voting gain
assurance that the proposed state root is correctly computed, even if the
proposer is Byzantine (the proof is unforgeable).

### Phase 2: SP1 Aggregation + Recursive Chaining (Weeks 7-16)

**Goal**: Compose per-block proofs into a single proof covering the entire
history. EVM-verifiable via Groth16.

**Work items**:

1. **SP1 guest program (federation history)** — Write a Rust program that:
   - Reads previous SP1 proof (or genesis marker)
   - Recursively verifies it (`sp1_zkvm::lib::verify::verify_sp1_proof()`)
   - Reads the new block's transition data
   - Verifies the state transition (nullifier insertions, note tree updates)
   - Commits new `post_state_root` as public output

2. **Aggregation pipeline** — Rather than proving every block individually with
   SP1 (too expensive), batch E blocks:
   - Verify E `BlockTransitionProof` STARKs in one SP1 execution
   - SP1's continuation splits the work across shards
   - Produce one aggregated proof per epoch

3. **Chain of epochs** — Each epoch proof recursively verifies the previous epoch
   proof. After N epochs, one proof covers genesis → now.

4. **EVM contract deployment** — Deploy SP1 verifier on Base. The pyana bridge
   contract calls `ISP1Verifier.verifyProof(vkey, publicValues, proofBytes)` to
   accept state root updates.

5. **Bootstrap protocol extension** — New nodes download:
   - Latest epoch proof (verifies all history)
   - State snapshot (note tree, nullifier set)
   - Current epoch's block headers (for the gap since last epoch proof)
   - QC for the latest block (proves federation agreement)

**Output**: O(1) bootstrap with ~260 byte proof of all history. On-chain state
root bridge on Base.

**Operational model**: Epoch proofs generated asynchronously by a dedicated
prover node (or outsourced to Succinct's network). Not on the critical path
for block production.

### Phase 3: Custom Recursive STARK + Full Succinctness (Months 5-12)

**Goal**: Match Mina's guarantees. One proof proves BOTH state transitions AND
consensus validity. No trust assumptions beyond genesis config.

**Work items**:

1. **Production RecursiveVerifierAir** — Upgrade from single-query to full
   50-query FRI verification. Integrate with Plonky3's `p3-recursion` crate
   (expected to stabilize by then). Full soundness guarantee.

2. **STARK-friendly threshold signatures** — Replace BLS12-381 with a scheme
   verifiable in BabyBear:
   - **Option A: Ed25519 threshold** — ~5-10M constraints for aggregate
     verification. Feasible (~5-10 seconds per block proof). Requires changing
     the federation's signing scheme.
   - **Option B: Poseidon2-Schnorr** — ~1-2M constraints. Custom scheme, needs
     careful security analysis. Very fast in-circuit.
   - **Option C: Hash-based threshold** — Post-quantum. ~5-10M constraints.
     Largest signatures but trivial in-circuit.

3. **Full recursive composition** — Each block's STARK proves:
   - Previous block's proof was valid (via RecursiveVerifierAir)
   - State transition is valid (BlockTransitionAir)
   - QC is valid (threshold signature verification)

4. **Nova folding integration** — For the per-block fast path, use Nova to fold
   the state transition incrementally. At epoch boundaries, generate the full
   recursive STARK from the accumulated Nova instance. This reduces per-block
   proving from ~2s (full recursion) to ~5ms (folding).

5. **Self-recursive steady state** — The proof reaches steady-state size after
   2-3 recursion levels. From that point, every block's proof is the same size
   (~120-150 KiB) regardless of chain height. Wrap to Groth16 for constant
   ~260 bytes.

**Output**: Full Mina-equivalent succinctness. A single ~260 byte proof attests
to the entire history from genesis, including both state transition correctness
AND consensus validity. Trust assumption: only the genesis config.

---

## 9. Open Questions and Risks

### Risk: Plonky3 Recursion Stability

The `p3-recursion` crate is not on crates.io and is under active development.
API changes could require significant rework.

**Mitigation**: Phase 2 uses SP1 (production-grade, stable API). Phase 3
custom recursion only starts after `p3-recursion` stabilizes or pyana builds
its own (our `RecursiveVerifierAir` is a start).

### Risk: SP1 Proving Cost

SP1 CPU proving is expensive (30-90s per block for recursion). At $0.001/cycle
on Succinct's network, a block with 50M cycles costs ~$50.

**Mitigation**: Batch E blocks per SP1 proof. At E=128, cost is $50/128 = ~$0.39/block.
GPU proving reduces 10x further. Long-term: dedicated prover hardware.

### Risk: BLS Replacement Breaking Change

Changing from BLS12-381 to a STARK-friendly scheme touches the `hints` crate
and ALL QC verification paths. This is a major protocol change.

**Mitigation**: Phase 3 is 5+ months out. Ship Phases 1-2 first. BLS replacement
can be introduced via epoch-boundary reconfiguration (old validators sign off on
new scheme, new validators use new scheme from next epoch).

### Risk: Nova Security Assumptions

Nova relies on the discrete log assumption over Pallas/Vesta curves. These are
not post-quantum secure.

**Mitigation**: Nova folding is only the fast-path accumulator. The epoch-boundary
STARK (Phase 2) provides the actual post-quantum security guarantee. If Nova is
broken, fall back to per-block STARKs (slower but secure).

### Open Question: Parallel Block Production

If block production is faster than proving time, proofs fall behind.

**Solution**: Pipelined proving. Block N's proof is generated concurrently with
blocks N+1, N+2, ... Nodes accept blocks based on QC (instant finality). Proofs
catch up asynchronously. The "provable tip" trails the "finalized tip" by a
bounded number of blocks. New nodes bootstrapping during this gap verify the
most recent proof + replay the unprovable suffix.

### Open Question: Prover Incentives

Who pays for the expensive proving work?

**Options**:
- Federation members prove as part of their duty (simplest, requires hardware)
- Outsource to Succinct's network (costs money, no hardware requirement)
- Proof market (snarkers bid on proving work, like Mina)
- Only prove at epoch boundaries (reduces total work by 128x)

---

## 10. Summary

### The Path

| Phase | Time | Per-Block Cost | Bootstrap Cost | EVM Cost | PQ Secure |
|-------|------|---------------|----------------|----------|-----------|
| Today | Done | 0 | LCP + state (~1 KB) | N/A | N/A |
| Phase 1 | 6 weeks | ~50ms prove | Per-block proof (~38 KiB) | N/A | Yes |
| Phase 2 | 16 weeks | ~50ms prove | Epoch proof (~260 B) + state | 200k gas | Yes |
| Phase 3 | 12 months | ~5ms fold | Single proof (~260 B) + state | 200k gas | Yes |

### The Key Insight

Pyana's BFT finality is a massive advantage over Mina. It eliminates fork
handling, staged ledgers, and transition frontiers. The recursive proof system
only needs to handle a single canonical chain, which simplifies everything.

The recommended path — Nova folding (per-block) + STARK checkpoint (per-epoch) +
SP1 wrapping (for EVM) — gives the best cost profile at each time horizon while
maintaining post-quantum security where it matters (the STARK layer).

Full Mina-equivalence (Phase 3) is achievable but not urgent. Phases 1-2 provide
meaningful security improvements (state transition validity is proven, not just
claimed) without requiring the hardest cryptographic research (in-circuit BLS or
signature scheme replacement).
