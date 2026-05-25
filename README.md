# Pyana

Capability-secure distributed runtime with ZK proofs. One shared fabric, emergent reference groups, provable everything.

## The Model

Pyana is a **unified fabric**: a shared blocklace (DAG) where groups form emergently through mutual acknowledgment. There are no fixed federations to join or leave. Nodes participate in strands; reference groups crystallize from repeated interaction. Your phone is a node. A cloud cluster is a node. The sovereignty spectrum is continuous.

Cells are isolated objects. Turns are atomic state transitions. The Effect VM (24 effects) proves each turn in a single STARK. CapTP sessions carry capability references across the fabric. Intents broadcast needs; ring trades solve them trustlessly.

## Key Capabilities

- **CapTP** -- Capability transport protocol. Sessions, sturdy refs, distributed GC, three-party handoff, store-and-forward.
- **Programmable Queues** -- Merkle queues with attached DSL programs. Every enqueue/dequeue is proven in-circuit.
- **DFA Routing** -- Governance-controlled route tables compiled to prefix-trie state machines. Constitutional amendments via threshold voting.
- **Nameservice** -- Hierarchical names with rent-based anti-squatting, sub-delegation, cross-federation resolution.
- **Intent Solving** -- Privacy-preserving marketplace. Commit-reveal frontrunning protection. Ring trades without a coordinator.
- **Effect VM** -- 24-effect instruction set proven per-turn in one STARK. Transfer, seal, factory, CapTP ops, queue ops, all in circuit.

## The Sovereignty Spectrum

| Mode | Description |
|------|-------------|
| **Sovereign** | Your device runs a full node. State lives locally. Interact peer-to-peer with signed proofs. |
| **Delegated** | Snapshot a capability list to a child cell. Acts offline with bounded staleness. Epoch-based revocation. |
| **Replicated** | Participate in a reference group. Blocklace consensus orders nullifiers. Exit anytime with your proof chain. |

The fabric is a notary for ordering and discovery. Between known parties, verification is just signed proofs exchanged directly.

## Bridges

| Chain | Mechanism | Status |
|-------|-----------|--------|
| **Mina** | Level 2 proof-carrying via Kimchi/Pickles. Recursive constant-size proofs. | Assisted recursion working |
| **EVM** | SP1 sovereign cells. STARK wrapped in Groth16, ~200k gas on Base/Ethereum. VK governance. | Guest program in development |
| **Midnight** | Attestation bridge + ZKIR v3 compilation. Cardano settlement. | DSL backend operational |

## Quick Start

```sh
# Build
git clone https://github.com/emberian/pyana && cd pyana
cargo build

# Run a node
cargo run -p pyana-node run

# CLI interaction
pyana cell list
pyana cell create --name my-agent
pyana cap grant <cell-id> --service storage --actions read,write
pyana turn submit <turn-file>
pyana namespace register alice --target <cell-id>
pyana intent post --spec '{"service": "compute", "action": "execute"}'

# Run the demo agent (full pipeline: token + STARK + turn)
cargo run -p pyana-demo-agent

# 4-node devnet
cd docker && docker compose up
```

## Crate Overview

| Crate | Purpose |
|-------|---------|
| `circuit` | STARK prover/verifier, Effect VM AIR, 17+ specialized AIRs, IVC, Plonky3 |
| `turn` | TurnExecutor: call forests, journal rollback, pipeline execution, queue programs |
| `cell` | Isolated objects with c-lists, notes, programs, oblivious transfer |
| `blocklace` | Shared DAG consensus. Content-addressed blocks, causal ordering, finality |
| `captp` | Capability Transport Protocol: sessions, sturdy refs, handoff, distributed GC |
| `federation` | Ed25519 BFT, state roots in blocks, epoch reconfig, LightClientProof |
| `intent` | Gossip broadcast, local Datalog matching, commit-reveal, IT-PIR discovery |
| `storage` | Programmable queues, relay operators, inboxes, erasure-coded availability |
| `bridge` | Token-to-circuit pipeline, blinded membership, predicate proofs |
| `cli` | User-facing CLI: cell, turn, cap, namespace, route, storage, cclerk commands |
| `sdk` | AgentCipherclerk, AgentRuntime, HD keys, verification modes, IT-PIR client |
| `node` | Federation daemon: HTTP API, MCP server (15+ tools), gossip sync |
| `net` | Quinn QUIC, Plumtree gossip, topic-based dissemination |
| `commit` | 4-ary Merkle trees (BLAKE3 fast / Poseidon2 ZK), fold deltas |
| `token` | AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog |
| `trace` | Datalog evaluator with derivation trace, deny-overrides-allow |
| `coord` | Causal DAG, 2PC atomic commit, Stingray bounded counters |
| `wire` | TCP postcard framing, STARK verification on receive |
| `hints` | BLS12-381 threshold sigs via KZG + SNARK aggregate verification |
| `store` | redb ACID persistence, note commitment tree, nullifier set |
| `wasm` | Browser WASM bindings (43 exports, full simulation) |
| `pyana-dsl` | Constraint DSL: `#[pyana_caveat]`, `#[pyana_effect]`, multi-backend |
| `verification` | Typed composition checker for proof soundness |
| `app-framework` | Shared patterns for building apps on the runtime |
| `apps/*` | Stablecoin, AMM, orderbook, lending, identity, gallery, compute exchange, bounty board, nameservice, governed-namespace |

## Privacy Model

Three verification modes from the same Datalog rules:

| Mode | Verifier Learns | Proof Size |
|------|----------------|-----------|
| Trusted | Full cleartext + trace | 0 |
| Selective Disclosure | Chosen facts + conclusion | ~45 KB |
| Fully Private | One bit (allow/deny) | ~80 KB |

All modes work offline. Proofs are post-quantum secure (BabyBear STARK + FRI).

## Trust Model

11 guarantees (capability confinement, turn atomicity, non-forgeable references, offline verification, proof-carrying state, monotonic attenuation, nullifier-based double-spend prevention, handoff integrity, forward secrecy, conservation, causal ordering).

7 assumptions (honest supermajority for ordering, partial synchrony, collision-resistant hashing, discrete log for classical crypto, correct local execution, bounded staleness for delegation, relay liveness for availability).

## Links

- [Paper](https://pyana.dev/paper.html)
- [Documentation](https://pyana.dev/docs/)
- [Playground](https://pyana.dev/playground/)
- [Explorer](https://pyana.dev/explorer/)

## Status: Experimental

Research software under active development. The proof system is real (Plonky3 STARKs with algebraic Poseidon2 constraints, 2000+ tests). The networking and consensus layers are functional but not battle-tested. Do not use for anything security-critical without independent audit.

## License

MIT OR Apache-2.0
