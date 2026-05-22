# Recursive Verifier Status

Current state of in-circuit recursive proof verification in pyana.

---

## What Recursive Proofs Would Enable

1. **Unbounded attenuation chains**: Arbitrary-length delegation/fold chains compressed
   into a single constant-size proof. Currently, the IVC system handles bounded chains
   via hash-chain accumulation + per-step STARK proofs.

2. **Proof composition**: A verifier checks ONE proof that transitively attests to an
   entire history of state transitions, regardless of length.

3. **Constant-size credentials**: A credential derived through 100 delegation steps
   would have the same proof size as one derived through 3 steps.

---

## Current State

### Plonky3 Recursive Verifier (`circuit/src/plonky3_verifier_air.rs`)

**Status: Deprecated stub.**

The `RecursiveVerifierAir` is explicitly marked `#[deprecated]` with the note:
> "RecursiveVerifierAir is a non-functional stub. It does NOT perform actual recursive
> verification. Use Plonky3 folding/accumulation for real IVC."

What it does:
- Checks structural validity (binary flags, section tags)
- Enforces a FRI folding relation (`DATA3 = DATA0 + DATA2 * DATA1`)
- Binds the trace to a proof commitment via the last row

What it does NOT do:
- Multi-query FRI verification (only checks structure for 1 query)
- Real Merkle path verification with Poseidon2 compression
- Extension field arithmetic (BinomialExtensionField<BabyBear, 4>)
- Proof-of-work verification for the query phase

### Kimchi/Mina Backend (`circuit/src/backends/mina.rs`)

**Status: Functional proving, incomplete recursive verification.**

What works:
- Kimchi proof generation over Vesta (IPA polynomial commitments)
- `prove_recursive_step()` / `verify_recursive_proof()` produce and check proofs
- Accumulated hash computation via Poseidon (Mina-native)
- Proof size is roughly constant across chain lengths (tested)

What is missing:
- **In-circuit IPA verification gates**: The recursive step circuit binds the previous
  proof's accumulated hash via Poseidon but does NOT encode the IPA verifier equation.
  Full Pickles requires ~2000 rows of EndoMul + CompleteAdd gates per recursion step.
- **`kimchi::verifier::verify` is never called**: The verifier deserializes the proof
  and checks public input consistency but skips the actual IPA opening check.
- **Verifier index serialization**: Required for standalone verification without
  reconstructing the circuit.

### IVC Module (`circuit/src/ivc.rs`)

**Status: Working alternative for bounded-depth composition.**

The IVC module provides a functional path that does NOT require true recursion:
- Hash-chain accumulation via Poseidon2 (each step extends the running hash)
- Real STARK proofs for the hash chain (`StateTransitionAir`)
- `ValidatedIvcProof`: chain STARK + per-step Merkle membership STARKs
- `IvcBuilder` for incremental construction with `finalize()` / `finalize_validated()`
- Optional Pickles finalization via `finalize_pickles()` (feature = "mina")

This handles the common case: bounded-depth chains (e.g., max 8-16 delegation steps)
where the verifier can check a linear number of sub-proofs. For most real-world use
cases (credential delegation, capability attenuation), this is sufficient.

---

## What Would Be Needed for True Recursion

### Option A: Complete the Kimchi IPA Gadget (~500 LOC)

Add to `build_recursive_step_circuit()`:
- ~15 EndoMul gates for the MSM verification equation
- ~10 CompleteAdd gates for point accumulation
- ~50 Generic gates for polynomial evaluation checks
- RecursionChallenge absorption (IPA folding challenges)
- Wire up `kimchi::verifier::verify` in `verify_recursive_proof()`

Pros: Small constant-size proofs (~5-10 KiB), proven technique (powers Mina blockchain)
Cons: Not post-quantum secure, ~1-2s proving time per step

### Option B: Multi-Query FRI Verification in Plonky3 (~200+ LOC)

Replace `RecursiveVerifierAir` with a real verifier that handles:
- All 50 FRI query openings (parallel trace sections)
- Full Poseidon2 compression for Merkle path verification
- Extension field arithmetic for BabyBear4
- Variable-depth FRI layer handling

Pros: Post-quantum secure, fast proving (~64us base), native to the STARK stack
Cons: Large proofs (~48 KiB), more complex implementation

### Option C: Accumulation Scheme (ProtoStar/HyperNova)

Replace both with a modern folding/accumulation scheme that achieves:
- O(1) verification regardless of chain length
- Deferred final proof (accumulate first, prove once at the end)
- Compatible with the existing BabyBear field

This is the most promising long-term direction but requires the most R&D.

---

## Workaround: Bounded-Depth Composition

For bounded-depth chains (e.g., max 8 delegations), the existing `ValidatedIvcProof`
from `circuit/src/ivc.rs` works without recursion:

- The chain STARK proves hash-chain continuity (O(log N) proof size)
- Per-step membership STARKs prove each fold was valid
- Total verification: verify 1 chain STARK + N membership STARKs

At depth 8, this means 9 STARK verifications — fast enough for all practical purposes.
The proof size grows linearly but remains under 500 KiB for typical chains.

---

## Timeline

True recursive verification is **future work** and is **not blocking** current
functionality. The bounded-depth IVC path covers all current use cases:
- Credential attenuation (typically 2-5 steps)
- Capability delegation chains (typically 3-8 steps)
- Federation proof composition (bounded by federation depth)

Recursion becomes necessary only for:
- Blockchain-length proof compression (thousands of steps)
- Unbounded delegation without proof size growth
- Cross-federation proof aggregation at scale
