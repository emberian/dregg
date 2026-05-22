# Succinct History for Pyana

Analysis of whether and how pyana can achieve Mina-style succinct history:
constant-size (or near-constant) proofs that allow new nodes to bootstrap
without replaying all historical blocks.

---

## 1. What "Succinct History" Means for Pyana

In Mina, "succinct" means: a new node downloads a single ~1 KiB proof that
attests "there exists a valid chain from genesis to this state." The node
trusts this proof + the current state snapshot and is fully synced.

For pyana, the question is different because the system architecture differs:

| Concern | Mina | Pyana |
|---------|------|-------|
| State ownership | Global ledger (one state for all accounts) | Per-agent proof chains (each agent owns their state) |
| Consensus | Probabilistic finality (Ouroboros Samasika) | Instant finality (BFT with QC) |
| What blocks contain | Full state transitions for all accounts | Nullifier batches + state root commitments |
| What new nodes need | Valid chain proof + snarked ledger | Federation state + latest QC + note/nullifier trees |

Pyana's "succinct history" therefore has two dimensions:

1. **Federation history**: Can a new federation observer skip replaying all
   blocks and trust a constant-size proof that the current state roots are valid?

2. **Agent history**: Can an agent present a constant-size proof that their
   current state follows from genesis via valid transitions? (This already exists
   via IVC -- see `circuit/src/ivc.rs`.)

The hard problem is (1). Agent history is already solved by design.

---

## 2. What Pyana Already Has

### 2.1 LightClientProof (Immediate Succinct Verification)

```rust
pub struct LightClientProof {
    pub block_hash: [u8; 32],
    pub post_state_root: [u8; 32],
    pub note_tree_root: [u8; 32],
    pub nullifier_set_root: [u8; 32],
    pub height: u64,
    pub qc: QuorumCertificate,
}
```

A new node that **trusts the federation's QC** can already bootstrap from:
- The latest `LightClientProof` (proves the federation agreed on these roots)
- The current note tree and nullifier set (state snapshot)
- The federation's public keys (to verify the QC)

This is SPV-equivalent. The trust assumption is: "the federation's supermajority
is honest." This is exactly the same trust assumption nodes already make when
participating.

### 2.2 IVC for Agent State

The `IvcProof` already compresses an agent's entire receipt chain into a
constant-size proof:

```
IvcProof { initial_root, final_root, step_count, accumulated_hash, stark_proof }
```

A verifier checks one STARK proof (38-128 KiB) and knows the agent's state is
valid from genesis. No historical receipts needed.

### 2.3 BLS Threshold QC

The `ThresholdQC` (via the `hints` crate) produces a constant-size aggregate
BLS signature regardless of committee size. Verification cost is O(1) --
one pairing check + one SNARK check.

### 2.4 State Roots in Blocks

Every finalized block commits to `pre_state_root`, `post_state_root`,
`note_tree_root`, `nullifier_set_root`. This means the block hash chain
already binds to the state at every height.

---

## 3. The Gap: Proving the Federation Itself Followed Consensus

The `LightClientProof` proves "the federation CLAIMS this is the current state."
It does NOT prove "the federation correctly followed its own rules to arrive
at this state."

A malicious supermajority could:
- Sign a QC for an invalid state root (skipped validation, included invalid
  nullifiers, etc.)
- Rewrite history (sign a QC at height H with a different post_state_root
  than the one at height H that was previously finalized)

For most use cases this is acceptable (you're trusting the federation anyway).
But for maximum security, you'd want a proof that:

```
"Starting from genesis config G, applying blocks B_1..B_n with valid QCs
at each step, produces state S with root R."
```

This is the "blockchain SNARK" from Mina.

---

## 4. Recursive STARK Architecture for Federation History

### 4.1 The Per-Block Proof

Each block produces a STARK proving:

```
Inputs:  (prev_state_root, prev_block_hash, block_contents)
Outputs: (post_state_root, block_hash)

Circuit proves:
1. block_hash = H(height, view, proposer, events, prev_hash, state_roots)
2. post_state_root = apply(prev_state_root, events)
3. nullifiers in events are valid (no double-spend against prev nullifier set)
4. note commitments in events are well-formed
```

This does NOT include QC verification (see below for why).

### 4.2 The Recursive Composition

Each block N produces a proof that says:
```
"Previous proof was valid (proving blocks 1..N-1)
 AND block N's transition is valid."
```

With Plonky3 recursion (already prototyped in `plonky3_verifier_air.rs`),
this is a STARK-inside-a-STARK. The steady-state proof size is:
- Plonky3 recursive: ~100-200 KiB (logarithmic growth, but reaches steady state)
- Wrapped in SP1 Groth16: ~260 bytes (constant)

### 4.3 What About the QC?

The QC proves the federation agreed. Verifying the QC inside the recursive
proof means verifying BLS signatures inside a STARK.

**This is the hard part.** See Section 5.

---

## 5. BLS Verification Cost in a STARK

### 5.1 The Problem

Pyana's `ThresholdQC` uses BLS12-381 threshold signatures via the `hints` crate.
Verification requires:
- One BLS12-381 pairing: `e(agg_pk, H(m)) == e(g1, agg_sig)`
- One SNARK proof verification (the `hints` SNARK proving weight threshold)

BLS12-381 pairing over BabyBear (p = 2^31 - 2^27 + 1) requires:
- **Field emulation**: BLS12-381 operates over a 381-bit prime. In BabyBear (31-bit),
  each BLS field element requires ~13 limbs. Each multiplication becomes ~169
  limb multiplications.
- **Pairing operation**: Miller loop + final exponentiation. The Miller loop
  involves ~64 point doublings and ~32 point additions on the G2 twist, each
  requiring multiple field multiplications.
- **Estimated constraint count**: ~50-100 million BabyBear constraints for one
  pairing verification.

### 5.2 Proof Time Estimate

At Plonky3's ~1M constraints/sec throughput on Apple M-series:
- One pairing: ~50-100 seconds of proving time
- Per block: unacceptable for real-time block production

### 5.3 Is It Feasible in SP1?

SP1 proves arbitrary Rust. Benchmarks for BLS12-381 pairing in SP1:
- SP1 cycle count for `bls12_381::pairing`: ~50-80M cycles
- SP1 throughput: ~0.5-1M cycles/sec (CPU prover), ~50M cycles/sec (GPU cluster)
- CPU proving time per pairing: ~50-160 seconds
- GPU cluster: ~1-2 seconds (acceptable but expensive)

### 5.4 Alternatives to In-Circuit BLS Verification

**Option A: Skip QC verification in the recursive proof.**

The recursive STARK proves state transitions are valid. The QC is verified
out-of-band by the bootstrapping node (just check the Ed25519/BLS signature
directly, no STARK needed). This is the pragmatic path.

The trust model becomes:
- State transitions: verified by STARK (trustless)
- Federation agreement: verified by QC signature check (trusting the federation keys)
- Combined: "these transitions are valid AND the federation agreed on them"

This is strictly weaker than Mina (where everything is in one proof) but
still much stronger than "just trust the QC."

**Option B: Replace BLS with a STARK-friendly signature scheme.**

Use a signature scheme native to BabyBear:
- Poseidon2-based signature (e.g., a variant of SPHINCS with Poseidon2 as the hash)
- Ed25519 verification in BabyBear (~2-5M constraints, feasible)

Ed25519 in BabyBear requires:
- Curve25519 field emulation: 255-bit field over 31-bit limbs (~9 limbs)
- Point multiplication: ~255 doublings + additions
- Estimated: ~5-10M constraints per signature
- For threshold (verify aggregate of t signatures): ~5-10M constraints total
  (if using Schnorr-style aggregation, not individual verification)

This is borderline feasible (~5-10 seconds per proof for the QC portion).

**Option C: Accumulate QC verification via deferred proofs.**

Use SP1's continuation model: each block's SP1 proof includes deferred
verification of the previous block's QC. The final Groth16 wrapper resolves
all deferred claims. This amortizes BLS verification across the proving pipeline.

---

## 6. What's Prunable Today (Without New Proofs)

Even without recursive proofs of consensus, pyana can prune aggressively:

### 6.1 Old Blocks (Keep Only Headers)

After a block is finalized and state roots are committed, the block body
(revocation events, encrypted turns, decryption shares) is only needed for:
- Auditing/forensics
- Catching up nodes that missed the block

A node can prune block bodies older than some retention window (e.g., 1 epoch)
and keep only: `(height, block_hash, post_state_root, note_tree_root, nullifier_set_root, qc)`.

**Required for bootstrap**: No. The latest LightClientProof + state snapshot suffices.

### 6.2 Old Receipt Chains (Keep Head + IVC Proof)

An agent's receipt chain grows unboundedly. With IVC:
- Keep: `IvcProof` (constant size) + current state
- Prune: all intermediate `TurnReceipt` objects

A verifier only needs the IVC proof to confirm the agent's history is valid.

**Already supported**: `IvcBuilder::finalize()` produces the compressed proof.

### 6.3 Old Revocation Events

The revocation tree root proves the current set of revoked tokens. Individual
revocation events are only needed for constructing non-membership proofs.

After the tree is built, old events can be pruned. The tree itself (sorted
leaves for adjacency proofs) must be retained, but the event metadata
(authority_id, signature, timestamp) can be dropped.

### 6.4 Nullifier Set

The nullifier set root proves completeness (no double-spend). Old nullifiers
can be pruned to just the sorted leaf set (for non-membership proofs).
The federation's `NullifierSet` is already append-only and minimal.

### 6.5 Note Tree

The note tree is append-only. Notes cannot be removed (only nullified). The
full tree must be retained for Merkle membership proofs during note spending.
However, spent notes (those whose nullifier is in the nullifier set) could be
marked as dead leaves -- they'll never be opened again.

---

## 7. What's Provable with Moderate Engineering

### 7.1 State Transition Proofs (No QC Verification)

**Difficulty: Medium. 2-4 weeks of engineering.**

Prove that `post_state_root = apply(pre_state_root, events)` inside a STARK.
This means:
- Encoding the nullifier insertion operation as AIR constraints
- Encoding note tree insertion as AIR constraints (Poseidon2 Merkle -- already
  have `P3MerklePoseidon2Air`)
- Producing one proof per block

The recursive composition (prove the previous proof inside the new one) uses
`plonky3_verifier_air.rs` which already exists in prototype form.

Result: A single STARK proof attesting "from genesis state S_0, applying all
block transitions produces state S_n." Does NOT prove the federation agreed --
that's checked separately via QC.

### 7.2 Receipt Chain Proofs for SP1 Settlement

**Difficulty: Low. Already scaffolded in `chain/` crate.**

The `chain/` workspace wraps pyana STARKs in SP1 for EVM verification.
Extending this to wrap the recursive state transition proof gives:
- A Groth16 proof (~260 bytes) of the entire federation history
- Verifiable on Ethereum for ~200k gas
- Suitable for bridge trust anchoring

### 7.3 Checkpoint-Based Succinct State

**Difficulty: Low. No new proofs needed.**

Define "checkpoints" every E blocks (epoch boundary):
```rust
struct Checkpoint {
    height: u64,
    post_state_root: [u8; 32],
    note_tree_root: [u8; 32],
    nullifier_set_root: [u8; 32],
    qc: QuorumCertificate,
    // Optionally: state transition proof from previous checkpoint
    transition_proof: Option<StarkProof>,
}
```

New nodes bootstrap from the most recent checkpoint. They trust the QC
(same assumption as today) and only need to replay blocks since the checkpoint.

---

## 8. What Requires Research

### 8.1 Full In-Circuit BLS Verification

Proving BLS12-381 pairing inside a BabyBear STARK. This gives the full Mina
treatment: a single proof that proves both state validity AND consensus validity.

Research challenges:
- Efficient non-native field arithmetic in Plonky3 AIR
- Pairing-friendly AIR gadgets (none exist in the ecosystem for BabyBear)
- Proving time: likely 50-100s per block with current hardware

Timeline: 3-6 months of dedicated research engineering.

### 8.2 STARK-Friendly Threshold Signature

Replace BLS12-381 with a scheme whose verification is cheap in BabyBear:
- Poseidon2-Schnorr: ~1-2M constraints for aggregate verification
- STARK-friendly MPC (hash-based threshold): ~5-10M constraints

This requires redesigning the federation's signature scheme, touching the
`hints` crate and all QC verification paths.

Timeline: 2-3 months, significant breaking change.

### 8.3 Full Recursive IVC Chain for Federation

Composing the state transition proof, the QC verification, and the previous
block's proof into a single recursive step -- matching Mina's `blockchain_snark`.

This is the holy grail but requires both (8.1) and (8.2) or a workaround.

---

## 9. Bootstrap Protocol Design

### 9.1 What a New Node Needs Today (Trust-the-QC Path)

```
1. Genesis config:
   - Federation member public keys (Ed25519 + BLS)
   - Initial state roots (all zero or genesis values)
   - Consensus parameters (threshold, epoch 0)

2. Latest LightClientProof:
   - block_hash, post_state_root, note_tree_root, nullifier_set_root
   - height
   - QuorumCertificate (verify against genesis member keys, or current epoch keys)

3. Current state snapshot:
   - Note commitment tree (full, for Merkle membership proofs)
   - Nullifier set (sorted leaves, for non-membership proofs)
   - Revocation tree (sorted leaves)

4. Epoch history (if epochs have changed):
   - Sequence of ReconfigurationProposal + votes for each epoch transition
   - Allows the new node to verify the chain of epoch configs from genesis
     to current (trust chain for the public keys)
```

**Total download**: State snapshot (~MB depending on tree sizes) + LightClientProof (~1 KB) + epoch history (~KB per epoch).

**Trust assumption**: The QC signers were honest when they signed. No proof of
state transition validity.

### 9.2 Enhanced Bootstrap (With State Transition Proofs)

```
1-3. Same as above.

4. State transition proof:
   - A STARK proof that post_state_root follows from genesis via valid
     block applications.
   - Proves: no invalid nullifiers were accepted, note tree was maintained
     correctly, state roots chain properly.
   - Does NOT prove: the federation agreed (that's still the QC's job).

5. Verification:
   - Verify QC (federation agreed on this state)
   - Verify state transition proof (this state is correctly computed)
   - Combined: "the federation agreed on a correctly-computed state"
```

**Trust assumption reduced**: Even a compromised federation supermajority cannot
sign an invalid state root (the transition proof would fail to verify).

### 9.3 Full Succinct Bootstrap (Mina-Equivalent)

```
1. Genesis config (same as above).

2. Succinct blockchain proof:
   - ONE proof (~100-200 KiB STARK, or ~260 bytes Groth16) that proves:
     "Starting from genesis config G, there exists a valid sequence of blocks
      B_1..B_n, each with a valid QC from >= threshold members, producing
      state roots (post, note, nullifier) = (R_s, R_n, R_null)."

3. Current state snapshot (same as above).
```

**Trust assumption**: Only the genesis config. No trust in any party beyond
that. This is the Mina-equivalent guarantee.

**Feasibility**: Requires solving in-circuit BLS verification (Section 5) or
switching to a STARK-friendly signature scheme (Section 8.2).

---

## 10. Comparison to Mina's Approach

### 10.1 What Mina Does

1. **Pickles recursion** over Pasta curves: each block produces a proof verifying
   the previous proof + the new block's validity. The "blockchain SNARK" is
   constant-size (~1 KiB) regardless of chain length.

2. **Bootstrap controller**: A new node connects to peers, receives the best
   tip (block + proof), verifies the proof, then sync-downloads the snarked
   ledger (the state) via a Merkle-hash-addressed protocol.

3. **Transition frontier**: Recent blocks (not yet fully proven) are kept in
   a sliding window (~290 blocks). Nodes maintain this frontier for fork choice.

4. **Staged ledger**: The predicted next state (applying pending transactions
   to the snarked ledger). This is needed because Mina's proofs are generated
   asynchronously (snarking is not instant).

### 10.2 What Transfers to Pyana

| Mina Concept | Pyana Equivalent | Applicability |
|-------------|-----------------|---------------|
| Blockchain SNARK | Recursive state transition STARK | Yes, but without BLS |
| Snarked ledger | Note tree + nullifier set snapshot | Direct mapping |
| Bootstrap from proof | Bootstrap from LightClientProof + state | Already works (weaker trust) |
| Transition frontier | Not needed (BFT = instant finality, no forks) | N/A |
| Staged ledger | Not needed (no async proving pipeline) | N/A |
| Scan state (proof work queue) | Not needed | N/A |
| Catchup protocol (fetch missing blocks) | Gossip sync (already exists) | Different mechanism |
| Epoch ledger (staking snapshot) | Epoch config history | Simpler (no staking) |

### 10.3 What Doesn't Transfer

1. **Probabilistic finality handling**: Mina needs the transition frontier because
   forks can happen. Pyana's BFT consensus provides instant finality -- once a QC
   is formed, the block is final forever. No fork choice needed.

2. **SNARK workers / proof market**: Mina has an ecosystem of snarkers racing to
   produce proofs. Pyana's federation members produce proofs as part of block
   finalization (or don't, in the trust-the-QC model).

3. **Scan state**: Mina batches transaction proofs in a tree structure that
   multiple snarkers fill in parallel. Pyana doesn't need this because its
   transition function is simpler (nullifier insertion, not arbitrary zkApp logic).

4. **Account timing/vesting**: Mina's succinct state includes vesting schedules
   that affect minimum balance. Pyana has no equivalent (cells have simpler economics).

### 10.4 Key Advantage Pyana Has

**BFT finality eliminates the transition frontier entirely.** In Mina, a significant
portion of bootstrap complexity comes from the sliding window of unfinalized blocks
and fork choice. Pyana's instant finality means:
- No forks to handle
- No "best tip" selection
- No staged ledger prediction
- Bootstrap is just: latest QC + state snapshot + done

This makes pyana's bootstrap protocol fundamentally simpler than Mina's.

---

## 11. Concrete Recommendation: The 80/20 Path

### Phase 0: Checkpoint-Based Pruning (Immediate, No New Proofs)

**What**: Define epoch-boundary checkpoints. New nodes bootstrap from the latest
checkpoint (LightClientProof + state snapshot). Historical blocks before the
checkpoint can be pruned.

**Implementation**:
- Add `Checkpoint` struct to `federation/src/types.rs`
- Modify node bootstrap to accept checkpoint + state download
- Agents prune receipt chains to IVC proof + current state

**Trust model**: Same as today (trust the QC). No new cryptography.

**Effort**: 1-2 days.

### Phase 1: State Transition Proofs per Block (Medium, Reuses Existing AIR)

**What**: Each block produces a STARK proof that `post_state_root = apply(pre_state_root, events)`.
Use the existing `P3MerklePoseidon2Air` for Merkle insertion proofs.

**Implementation**:
- Write `NullifierInsertionAir` (prove sorted insertion into nullifier set)
- Wire into the consensus finalization path (proposer generates proof with block)
- Accumulate per-block proofs via `plonky3_recursion.rs` aggregation

**Trust model**: Transition validity is proven. QC still trusted for agreement.

**Effort**: 2-4 weeks.

### Phase 2: Recursive State History (Major, Requires Plonky3-recursion)

**What**: Each block's proof recursively verifies the previous block's proof.
After N blocks, ONE proof attests to the entire history of state transitions.

**Implementation**:
- Integrate Plonky3-recursion (git dep, already in workspace) for true in-circuit
  STARK verification
- Each block's prover receives (previous_proof, new_block) and produces
  (new_proof proving "prev was valid AND this transition is valid")
- Steady-state proof size: ~100-200 KiB regardless of chain length

**Trust model**: State transitions from genesis are proven. QC still trusted.

**Effort**: 4-8 weeks.

### Phase 3: Groth16 Wrapping via SP1 (Production Settlement)

**What**: Wrap the recursive STARK into a constant-size Groth16 proof for
EVM verification and compact bootstrap.

**Implementation**:
- Extend `chain/` crate to wrap the recursive state proof (not just individual proofs)
- Produce ~260 byte proof of entire federation history
- Deploy verifier contract on Base

**Trust model**: Same as Phase 2, but proof is EVM-verifiable.

**Effort**: 2-4 weeks (scaffolding already exists).

### Phase 4: STARK-Friendly Consensus Signatures (Research)

**What**: Replace BLS12-381 with a signature scheme verifiable in BabyBear STARK.
Candidates:
- Ed25519 threshold (Schnorr aggregation) -- ~5M constraints, feasible
- Hash-based signatures (Poseidon2-SPHINCS) -- larger signatures but trivial in-circuit
- Lattice-based (post-quantum AND STARK-friendly) -- furthest out

**Implementation**:
- Design the new threshold scheme
- Implement in `hints` crate or new crate
- Integrate QC verification into the recursive proof circuit

**Trust model**: Full Mina-equivalent. One proof proves everything from genesis.
No trust in any party beyond the genesis config.

**Effort**: 3-6 months.

---

## 12. Summary

| Path | Bootstrap Proof Size | Trust Assumption | Engineering Effort |
|------|---------------------|-----------------|-------------------|
| Today (LightClientProof) | ~1 KB | Trust federation QC | Done |
| Phase 0 (Checkpoints) | ~1 KB + state snapshot | Trust federation QC | Days |
| Phase 1 (Transition proofs) | ~38 KiB per block | QC for agreement, proof for validity | Weeks |
| Phase 2 (Recursive) | ~100-200 KiB total | QC for agreement, proof for history | Months |
| Phase 3 (Groth16 wrap) | ~260 bytes total | QC for agreement, proof for history | Months |
| Phase 4 (Full succinct) | ~260 bytes total | Only genesis config | Quarters |

**The key insight**: BFT finality + state roots in blocks + LightClientProof
already gives pyana a workable succinct verification system TODAY. The gap
between "trust the QC" and "trust only genesis" is real but the intermediate
steps (Phases 1-3) provide meaningful security improvements without requiring
the hardest research (in-circuit BLS).

The 80/20 answer is **Phase 0 + Phase 1**: checkpoint-based pruning with per-block
state transition proofs. This gives new nodes O(1) bootstrap (from checkpoint)
with cryptographic assurance that state transitions are valid, while still
trusting the federation for ordering. This matches the security model pyana
already assumes (the federation is honest for ordering) while adding proof that
the state was computed correctly.

Full Mina-equivalent succinctness (Phase 4) is achievable but requires either
solving BLS-in-STARK or changing the signature scheme. It should be on the
roadmap but is not blocking for near-term utility.
