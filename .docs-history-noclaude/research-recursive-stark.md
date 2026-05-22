# Recursive STARK Composition — Research Summary (2026-05-20)

## Decision

**Plonky3-recursion is the path.** It's the only public implementation that directly
targets recursive STARK verification inside another STARK on BabyBear with FRI.

## Key Findings

### Plonky3-recursion (RECOMMENDED for same-stack)
- Verifies Plonky3 uni-STARK and batch-STARK proofs inside another Plonky3 STARK
- Supports BabyBear as native recursion field
- Full FRI PCS verification in-circuit (Merkle openings, FRI folds, Fiat-Shamir)
- After enough layers, reaches **steady-state size** (no unbounded growth)
- Supports both linear chaining and **2-to-1 aggregation** (tree-style)
- ~65K witness ops, ~43K public ops, ~60K ALU ops (max height 2^15-2^16)
- **NOT audited, NOT on crates.io, under active development**
- Available as git dep (already in our workspace as `plonky3`)

### SP1 / RISC Zero / OpenVM (production recursion, different stack)
- Production-grade recursion, but **not** drop-in verifiers for arbitrary external BabyBear AIR
- SP1: normalize → compress → shrink → Groth16 pipeline. ~260 bytes final, ~270k gas.
- RISC Zero: lift → join → resolve → identity_p254. ~200 KB succinct receipt before Groth16.
- OpenVM: guest library for recursive verification of OpenVM STARK proofs. Production-ready.
- All three are integrated proving stacks, not generic outer verifiers.
- Would require re-implementing our prover inside their VM.

### Nova / Sangria / ProtoStar (folding schemes — NOT for AIR/STARK)
- Nova: R1CS only. ~10K multiplication gates for verifier. Spartan compression.
- Sangria: PLONK-family only. No releases.
- ProtoStar: Halo2 research impl. "Not able to implement full IVC in time."
- **None** work directly over arbitrary AIR with FRI commitments.

### Pickles (Mina) — not transferable to FRI
- IPA-based recursive accumulation over Pasta curve cycle
- The accumulator/deferred-opening trick is specific to IPA, not FRI
- The *pattern* (step/wrap PCD) transfers, but the *mechanism* does not

## Recommendation for pyana

1. **Prototype with Plonky3-recursion** — our proofs are already Plonky3-compatible
   (BabyBear field, FRI PCS). This is the cleanest path to constant-size proofs.

2. **Use tree-style aggregation** (2-to-1) rather than linear chains — parallelizable,
   better operational profile for variable-length fold chains.

3. **For EVM settlement**: After recursive compression, wrap the final STARK proof via
   SP1 or a separate Groth16 step for cheap on-chain verification (~270k gas).

4. **Do NOT invest in Nova/folding for the STARK path** — would require re-encoding
   to R1CS, defeating the purpose.

5. **The Kimchi/Pickles backend** remains valuable for non-PQ applications where
   ~1 KiB constant-size proofs matter and Pasta curves are acceptable.

## What we need to do

- Align our AIR/FRI parameters with Plonky3's `FriRecursionConfig` interface
- Our STARK is already on BabyBear with FRI — integration should be mostly format alignment
- Implement `RecursionInput` wrapping for our fold-step proofs
- Target: one recursive proof covering N attenuation steps, steady-state size
