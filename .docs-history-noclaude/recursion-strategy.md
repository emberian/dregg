# Recursion Strategy: Pickles vs. Nova-over-BabyBear vs. Plonky3 Recursive Verifier

Analysis of whether to use the existing Pickles/Kimchi backend (`feature = "mina"`) for
recursive proof composition, or to continue building Nova-style folding + STARK recursion
natively over BabyBear.

---

## 1. What Each Component Actually Implements

### `circuit/src/backends/mina.rs` (1456 lines, feature = "mina")

**Status: Functional but incomplete recursion.**

Implements:
- `ProofBackend` trait (prove/verify membership + fold step) using Kimchi over Vesta
- Poseidon hash (Mina-native, width-3 sponge) for 4-ary Merkle trees
- Merkle membership circuit with Poseidon gates (depth-configurable)
- Fold-step circuit (generic gates for removals + Poseidon for root recomputation)
- `PicklesRecursiveProof`: recursive IVC over Pasta cycle (Pallas/Vesta alternation)
- `prove_recursive_step()` / `verify_recursive_proof()`: working recursive prover
- `recursive_fold()`: batch fold composition (placeholder for full Pickles wrap)

**Key gaps:**
- Verifier is structurally complete but **does not call `kimchi::verifier::verify`** yet
  (TODO comments: "requires verifier index serialization"). It deserializes the proof
  and checks public input consistency + accumulated hash, but skips IPA verification.
- The recursive circuit (lines 642-718) uses Poseidon binding for the previous proof's
  state but does NOT implement the in-circuit IPA verifier (~2000 rows of EndoMul +
  CompleteAdd gates). This is marked as a TODO.
- Proof size: IPA over Vesta produces ~5-10 KiB proofs, not the ~1-2 KiB that Pickles
  with deferred accumulation achieves.

**Integration with IVC:** The `IvcBuilder::finalize_pickles()` method (ivc.rs:1203-1237)
converts BabyBear roots to 32-byte hashes and calls `prove_recursive_step()` in a loop.
This path is functional and tested.

### `circuit/src/folding.rs` (917 lines)

**Status: Sound and fast, but NOT a ZK proof system.**

Implements:
- Simplified Nova-style folding over BabyBear with Poseidon2 commitments
- `RelaxedInstance`, `BlockInstance`, `FoldingAccumulator` types
- `fold_instance()`: O(field ops + hash) per block, ~<100us per block (measured)
- `verify_accumulator()`: replays all folds from start (requires all witnesses)
- `prove_accumulator()` / `verify_checkpoint()`: checkpoint mechanism
- Serialization roundtrips for accumulator state

**Key properties:**
- **Not hiding**: Poseidon2 commitment over BabyBear, no blinding factors
- **Verification requires witnesses**: `verify_accumulator` replays the full folding
  sequence. This is NOT succinct -- the verifier must see all block instances
- **No actual proof generation**: `AccumulatorProof` is metadata, not a cryptographic
  proof. Defers to "a STARK at checkpoint time" which does not yet exist in this module
- **Performance**: Blazing fast (~10-100us per fold on 100 blocks)

**Verdict:** This is a fast deterministic accumulator, not a proof system. It serves
as a "claim accumulator" -- you fold claims cheaply, then prove them all at once with
a STARK at epoch boundaries.

### `circuit/src/ivc.rs` (2679 lines)

**Status: The most complete recursive proof path. Real STARK proofs working.**

Implements:
- `IvcAir`: AIR constraint system proving hash-chain correctness over fold steps
- `StateTransitionAir`: Real STARK AIR for the accumulated hash chain
- `prove_ivc_stark()` / `verify_ivc_stark()`: Cryptographic STARK proof generation
  and verification using the custom BabyBear STARK backend
- `IvcBuilder`: Incremental proof construction with `.finalize()` producing real STARKs
- `ValidatedIvcProof`: Chain STARK + per-step Merkle membership STARKs (closing
  the fold-validity gap)
- `prove_validated_ivc()` / `verify_validated_ivc()`: Full sound recursive path
- Integration points: `finalize_pickles()` for Mina path, `finalize_validated()`
  for full STARK path
- `recursive_ivc` module (feature = "plonky3"): True in-circuit recursive STARK
  verification via `RecursiveIvcBuilder` + `build_recursive_ivc_chain()`

### `circuit/src/block_transition_air.rs` (677 lines)

**Status: Working, real STARK proofs for per-block state transitions.**

Implements:
- `BlockTransitionAir`: Proves Merkle tree update sequence (events applied to tree)
- `prove_block_transition()` / `verify_block_transition()`: end-to-end STARK
- Chain continuity, event ordering, hash binding constraints
- Full test coverage with tamper detection

### `circuit/src/plonky3_verifier_air.rs` + `plonky3_recursion.rs`

**Status: Working in-circuit STARK verification. The "real" recursion backend.**

- `RecursiveProver::prove_recursive()`: Generates a proof that verifies another proof
- `build_recursive_ivc_chain()`: Chains N fold proofs recursively
- `AggregationAir`: Hash-chain aggregation of N proofs into 1

---

## 2. The Three Recursion Paths (Comparison)

| Dimension | BabyBear STARK (ivc.rs) | Folding (folding.rs) | Pickles (mina.rs) |
|-----------|------------------------|---------------------|-------------------|
| **Field** | BabyBear (31-bit) | BabyBear (31-bit) | Pasta Fp/Fq (255-bit) |
| **Per-step cost** | ~1-10ms (STARK prove) | ~10-100us (hash only) | ~1-5s (Kimchi prove) |
| **Proof size** | ~2-48 KiB (FRI) | N/A (no proof) | ~5-10 KiB (IPA) |
| **Recursion** | In-circuit STARK verifier (plonky3_verifier_air) | None (replay required) | Pasta cycle (incomplete) |
| **Verification** | O(log N) STARK verify | O(N) replay | O(1) IPA verify |
| **PQ-secure** | Yes (hash-based) | N/A | No (ECDLP) |
| **Soundness** | 128-bit (FRI) | Deterministic (no ZK) | 128-bit (IPA) |
| **Completeness** | Working end-to-end | Working end-to-end | Prover works, verifier stubbed |

---

## 3. Curve Mismatch Cost: BabyBear-in-Pickles

To verify a BabyBear STARK inside a Pickles circuit:

**What's needed:**
- Emulate BabyBear field ops (p = 2^31 - 2^27 + 1) inside Pasta (p ~ 2^254)
- Each BabyBear multiply = 1 native Fp multiply (trivial -- fits in one limb)
- Each Poseidon2 round over BabyBear = ~15 Generic gates in Kimchi (x^7 S-box)
- FRI verification: ~log(N) Poseidon2 hashes + Merkle path checks

**Cost estimate:**
- BabyBear arithmetic is CHEAP inside Pasta (one 31-bit value < 255-bit field)
- A STARK verifier needs: ~O(security * log(trace)) field operations
- For 128-bit security, 64 FRI queries, trace=32 rows:
  - ~64 * 5 * (hash cost) = ~320 Poseidon hashes emulated
  - Each Poseidon2 hash (over BabyBear) emulated in Kimchi: ~100-200 gates
  - Total: ~32,000-64,000 Kimchi gates for STARK verification
  - This is FEASIBLE (Kimchi supports circuits of this size) but adds ~5-10s to
    the Pickles proving time per wrap

**Comparison to native Pickles recursion:**
- Native IPA verification in Pickles: ~2000 gates (EndoMul + CompleteAdd)
- STARK-in-Pickles: ~32,000-64,000 gates (15-30x more expensive)
- This is the "STARK-in-SNARK" penalty -- but you pay it only once at wrap time

---

## 4. Does a STARK-in-SNARK Wrapper Exist?

**Partially, across two components:**

1. `circuit/src/plonky3_verifier_air.rs` -- encodes STARK verification as an AIR
   (STARK-in-STARK). This is working but produces a STARK proof (still ~KiB-sized).

2. `chain/` crate with SP1 -- wraps STARKs into Groth16 (256-byte proof). This is
   the EVM path, not the Pickles path.

3. **No existing STARK-in-Pickles wrapper.** Building one would require encoding the
   BabyBear STARK verifier algorithm as Kimchi constraints. This is the main missing
   piece for the hybrid architecture.

---

## 5. The Optimal Architecture (Recommendation)

### Three-tier proving strategy:

```
Tier 1: Per-operation (fast, BabyBear-native)
  - BlockTransitionAir for per-block state transitions (~1-10ms)
  - FoldAir for per-fold-step validity (~1ms)
  - Output: Individual STARK proofs over BabyBear

Tier 2: Epoch aggregation (folding + checkpoint STARK)
  - folding.rs accumulates N blocks in <100us each
  - At epoch boundary: StateTransitionAir STARK proves the hash chain (~10ms)
  - ValidatedIvcProof adds per-step membership STARKs
  - Output: O(log N) sized STARK covering the epoch

Tier 3: History compression (for cross-federation sync / light clients)
  - OPTION A: Plonky3 recursive verifier (in-circuit STARK-in-STARK)
    - Already working (plonky3_verifier_air.rs)
    - Each step: ~50-100ms
    - Final proof: ~48 KiB STARK (PQ-secure)
  - OPTION B: Pickles wrap (STARK-to-SNARK)
    - NOT yet built (requires encoding STARK verifier in Kimchi gates)
    - Each wrap: ~5-10s
    - Final proof: ~5-10 KiB (NOT PQ-secure)
  - OPTION C: SP1/Groth16 wrap (for EVM chains)
    - Infrastructure exists in chain/ crate
    - Final proof: 256 bytes on-chain
```

### Recommended path: Continue with Plonky3 recursive verifier, defer Pickles.

**Rationale:**

1. **The Plonky3 recursive path is further along.** `build_recursive_ivc_chain()` works
   end-to-end. The `RecursiveProver` generates real proofs. Pickles still needs: (a) the
   in-circuit IPA verifier gates, (b) actual `kimchi::verifier::verify` integration,
   (c) the STARK-in-Pickles wrapper circuit.

2. **Post-quantum security matters.** Pyana tokens may circulate for years. BabyBear STARKs
   are hash-based and PQ-secure. Pickles relies on ECDLP over Pasta curves -- not suitable
   for long-lived authorization credentials if you care about PQ threats.

3. **The proof size difference is manageable.** STARK proofs are ~48 KiB vs Pickles ~5 KiB.
   For pyana's use case (authorization tokens exchanged between services), 48 KiB is fine.
   The 256-byte Groth16/SP1 path exists for on-chain settlement where size is critical.

4. **Building STARK-in-Pickles is high-effort for marginal gain.** The STARK verifier in
   Kimchi gates is ~32K-64K gates of non-native field emulation. This is a multi-week
   engineering effort with unclear payoff given that the native recursive path works.

5. **The folding.rs module fills its role perfectly.** It's not trying to be a proof system
   -- it's a fast claim accumulator. Keep using it between checkpoints. The architectural
   pattern is:
   - Per-block: `fold_instance()` in <100us (accumulate claims)
   - Per-epoch: `prove_ivc_stark()` in ~10ms (prove the epoch)
   - Per-history: `build_recursive_ivc_chain()` in ~50ms/step (compress history)

### When Pickles WOULD make sense:

- **Cross-system interop with Mina Protocol:** If pyana needs to post proofs to Mina L1,
  Pickles is the native format. The existing backend would serve as the bridge.
- **Extremely bandwidth-constrained channels:** If proof must be <5 KiB and PQ is not
  required, Pickles is better than STARKs.
- **Client-side verification in browsers:** Pickles verification is faster than STARK
  verification for the same security level (IPA vs FRI), which matters for web wallets.

### Keep the Mina backend as:

1. A **bridge to Mina Protocol** (if cross-chain posting is needed)
2. A **reference implementation** for testing recursive proof logic
3. A **future option** for bandwidth-constrained settings

### Do NOT invest in building Nova-over-BabyBear.

The `folding.rs` module is already a simplified Nova analogue and works well for its purpose.
Building a full Nova IVC (with committed relaxed R1CS, cross-term computation, and NIFS
decider) over BabyBear would duplicate what the Plonky3 recursive verifier already achieves,
with worse developer ergonomics (Nova requires R1CS constraint writing rather than AIR).

---

## 6. Summary Decision Matrix

| Question | Answer |
|----------|--------|
| Should we use Pickles for recursive composition? | **No** (for now). The in-circuit Pickles verifier is unfinished, and we already have a working Plonky3 recursive verifier. |
| Should we build Nova-over-BabyBear? | **No**. `folding.rs` + `StateTransitionAir` already gives us the fast-accumulate + checkpoint-STARK pattern that Nova provides, with less complexity. |
| Should we build STARK-in-Pickles wrapper? | **Not yet**. Only if Mina L1 interop or <5 KiB proofs become a hard requirement. |
| What's the production recursion path? | Plonky3 `RecursiveProver` (STARK-in-STARK via `plonky3_verifier_air.rs`). |
| What role does `folding.rs` play? | Fast per-block claim accumulator (~100us). Checked at epoch boundaries by a real STARK. |
| What role does `mina.rs` play? | Reserve option for Mina interop and bandwidth-constrained channels. |
| Is the current IVC sound? | **Yes**, when using `ValidatedIvcProof` (chain STARK + per-step membership STARKs). The hash-chain-only path requires trust in the prover. |
