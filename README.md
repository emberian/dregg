# pyana

Distributed object-capability authorization with zero-knowledge presentation.

Agents prove they are authorized to act across organizational boundaries without revealing their delegation chain, intermediate authorities, or other capabilities they hold. Combines capability-security semantics with STARKs and federated BFT consensus.

## Core idea

Capability attenuation is incrementally verifiable computation. Each delegation step narrows a capability set — monotonic state transitions that IVC was designed to prove. The authorization structure *is* the computation being proved. ZK presentation falls out for free.

## Architecture

```
SDK              AgentWallet, AgentRuntime, SiloClient
Network          TCP wire + postcard framing, STARK verification on receive
Federation       morpheus (adaptive BFT) + hints (BLS12-381 threshold sigs)
Coordination     Causal DAG, 2PC atomic, bounded counters (Stingray)
Execution        Cells (isolated accounts + c-lists), Turns (atomic txns)
Proof            BabyBear STARK + FRI + Poseidon2, IVC fold chains, Plonky3
Commitment       4-ary Merkle (BLAKE3 fast / Poseidon2 ZK), fold deltas
Policy           Datalog evaluator + derivation traces, Macaroon + Biscuit tokens
Storage          redb (ACID), encrypted keychain, note trees + nullifier sets
```

## Workspace

24 crates:

| Crate | Purpose |
|-------|---------|
| `cell` | Isolated accounts with capability lists, notes, programs, state visibility |
| `turn` | Atomic transaction executor (call forests, journal rollback, two-phase fee) |
| `circuit` | STARK prover/verifier, Poseidon2 AIR, Datalog-in-STARK, IVC, Plonky3 |
| `commit` | 4-ary Merkle trees, fold deltas, symbol table |
| `trace` | Datalog evaluator with derivation trace extraction |
| `token` | AuthToken trait — Macaroon (HMAC-SHA256) + Biscuit (Ed25519 + Datalog) |
| `tokenizer` | X25519-ChaCha20Poly1305 seal/unseal daemon |
| `macaroon` | HMAC-chain bearer tokens with constant-time verify |
| `secrets` | OS keychain + encrypted file store |
| `types` | Canonical types: CellId, Ed25519, AttestedRoot, causal DAG |
| `coord` | Multi-silo coordination: 2PC, bounded counters, budget channels |
| `federation` | Ed25519 consensus nodes, epoch reconfiguration, revocation trees |
| `morpheus` | Adaptive BFT (Lewis-Pye & Shapiro) |
| `hints` | BLS12-381 threshold signatures (KZG + SNARK) |
| `wire` | TCP wire protocol, federation bridge, multi-node demo |
| `net` | QUIC gossip (Plumtree lazy-push) |
| `store` | redb persistence, note commitment tree, nullifier set |
| `audit` | Usage logging, consistency proofs |
| `bridge` | Connects token pipeline to circuit (presentation builder) |
| `sdk` | Agent SDK: wallet, runtime, verification modes |
| `wasm` | Browser WASM bindings (12 exported functions) |
| `demo` | CLI demos |
| `demo-agent` | End-to-end scenarios (NFT, escrow, auction, atomic swap) |
| `tests` | Integration tests |

Plus `chain/` (standalone workspace for SP1/EVM settlement).

## Verification modes

| Mode | Verifier sees | Latency | Use case |
|------|--------------|---------|----------|
| Trusted | Full cleartext token + trace | ~8 μs | Same-org, same-trust-domain |
| Selective | Chosen facts + STARK proof | ~2 ms | Cross-org, partial disclosure |
| Fully Private | One bit (allow/deny) + STARK proof | ~2 ms | Zero-knowledge presentation |

## Security properties

- **Post-quantum external interface.** Everything crossing trust boundaries is hash-based (STARKs, Merkle commitments, HMAC). Classical crypto (Ed25519, BLS) confined within federation.
- **Offline verification.** No chain liveness needed. Proof + federation root = complete.
- **Monotonic attenuation.** Fold deltas can only remove capabilities, never add. Enforced by AIR constraints.
- **Position-independent nullifiers.** Notes produce the same nullifier regardless of which federation/tree they live in. Cross-federation portability.
- **Fail-closed.** STARK verification returns Err on any failure. No soft-fail mode.

## Building

```sh
cargo build                    # full workspace
cargo test                     # all 976+ tests
cargo build -p pyana-wasm --target wasm32-unknown-unknown  # browser
```

## Design documents

- [`PYANA_DESIGN.md`](PYANA_DESIGN.md) — full architecture and comparison
- [`docs/proof-carrying-state.md`](docs/proof-carrying-state.md) — federation-as-ordering-service model
- [`docs/verification-modes.md`](docs/verification-modes.md) — three-mode verification spec
- [`paper/pyana.typ`](paper/pyana.typ) — whitepaper (typst)

## License

MIT OR Apache-2.0
