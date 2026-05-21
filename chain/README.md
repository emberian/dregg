# pyana-chain

EVM settlement layer for pyana. Wraps pyana STARK proofs in SP1/Groth16 for
on-chain verification at ~200K gas on Base (or any EVM chain with an SP1 verifier
gateway deployment).

## Architecture

```
pyana STARK proof (BabyBear field, FRI-based, large)
       |
       v
SP1 Guest Program (full STARK verifier running inside RISC-V zkVM)
       |
       v
SP1 Groth16 proof (constant-size, ~200K gas to verify on EVM)
       |
       v
SP1 Verifier Gateway contract (deployed by Succinct via CREATE2)
```

The guest program (`program/`) re-implements the STARK verifier from the `circuit`
crate in a form compatible with SP1's `riscv32im-succinct-zkvm-elf` target. It
verifies trace commitments, constraint consistency, Fiat-Shamir challenges, and
FRI folding -- the same checks as the native verifier.

## Status

**Structural scaffold.** The crate compiles, tests pass (in mock mode), and the
API surface is stable. It is not yet deployed to a live chain.

What works today:
- Mock mode (default): full API surface with simulated proofs for integration testing
- Guest program: complete STARK verifier for SP1's zkVM target
- On-chain verification scaffold: alloy-based contract interaction (behind `on-chain` feature)
- Proof serialization format: aligned with `circuit::stark::proof_to_bytes()`

What requires external tooling (not yet integrated in CI):
- Real SP1 proving (requires `sp1up` toolchain, `--features prove`)
- Contract deployment to Base Sepolia / Mainnet
- End-to-end proof submission and on-chain verification

## Building

```bash
# Default (mock mode) -- no external toolchain needed
cd chain && cargo check

# Run tests
cd chain && cargo test

# With real SP1 proving (requires sp1up)
cd chain && cargo build --no-default-features --features prove

# With on-chain submission (requires RPC endpoint)
cd chain && cargo build --no-default-features --features prove,on-chain
```

## SP1 Toolchain Setup

```bash
curl -L https://sp1.succinct.xyz | bash
sp1up
cd chain/program && cargo prove build
```

## API

```rust
use pyana_chain::{wrap_for_evm, verify_on_chain, EvmProof};

// Wrap a STARK proof for EVM verification
let evm_proof = wrap_for_evm(&stark_proof_bytes, &public_inputs).await?;

// Verify on-chain (calls SP1 verifier gateway)
let valid = verify_on_chain(&evm_proof, rpc_url, verifier_address).await?;
```

## Workspace Isolation

This crate lives in its own Cargo workspace (separate from the main pyana
workspace) because SP1's dependency tree pins `generic-array = 1.1.0`, which
conflicts with `nova-snark`'s requirement of `generic-array >= 1.2.0` in the
main workspace.
