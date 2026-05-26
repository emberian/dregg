# `dregg` - Dragon's Egg

\[fka. Pyana, working on the rename!\]

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a direct expression of my original impetus to build <https://rbg.systems>. Maybe Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs have to say about it:

(end-of-human-text)

## The Model

Pyana is a **unified fabric**: a shared blocklace (DAG) where groups form emergently through mutual acknowledgment. There are no fixed federations to join or leave. Nodes participate in strands; reference groups crystallize from repeated interaction. Your phone is a node. A cloud cluster is a node. The sovereignty spectrum is continuous.

Cells are isolated objects. Turns are atomic state transitions. The Effect VM proves each turn in a single STARK. CapTP sessions carry capability references across the fabric. Intents broadcast needs; ring trades solve them trustlessly.

## Key Capabilities

- **CapTP** -- Capability transport protocol. Sessions, sturdy refs, distributed GC, three-party handoff, store-and-forward.
- **Programmable Queues** -- Merkle queues with attached DSL programs. Every enqueue/dequeue is proven in-circuit.
- **DFA Routing** -- Governance-controlled route tables compiled to prefix-trie state machines. Constitutional amendments via threshold voting.
- **Nameservice** -- Hierarchical names with rent-based anti-squatting, sub-delegation, cross-federation resolution.
- **Intent Solving** -- Privacy-preserving marketplace. Commit-reveal frontrunning protection. Ring trades without a coordinator.
- **Effect VM** -- Abstract instruction set proven per-turn in one STARK. Transfer, seal, factory, CapTP ops, queue ops, all in circuit.

## Quick Start

```sh
# Build
git clone https://github.com/emberian/dregg && cd dregg
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

## Links

- [Paper](https://pyana.dev/paper.html)
- [Documentation](https://pyana.dev/docs/)
- [Playground](https://pyana.dev/playground/)
- [Explorer](https://pyana.dev/explorer/)

## Status: Experimental

Research software under active development. The proof system is real (Plonky3 STARKs with algebraic Poseidon2 constraints, 2000+ tests). The networking and consensus layers are functional but not battle-tested. Do not use for anything security-critical without independent audit.

## License

MIT OR Apache-2.0
