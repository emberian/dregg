# pyana

Pyana is a distributed object-capability runtime where agents hold unforgeable capabilities, delegate them with attenuation-only narrowing, and prove authorization with zero-knowledge STARKs. Objects are isolated cells, messages are atomic turns, and the network is a sealed capability marketplace with privacy-preserving discovery. Verification is offline, proofs are post-quantum, and agents can exit any federation at any time carrying their full history as portable proof chains.

## Quick start

```sh
# Build the full workspace (26 crates)
cargo build

# Run all tests (2141 tests)
cargo test

# Run the end-to-end demo suite (37 scenarios)
cargo run -p pyana-demo-agent --example unified_harness

# Launch a 4-node devnet (requires Docker)
cd docker && docker compose up

# Build the browser WASM module
cargo build -p pyana-wasm --target wasm32-unknown-unknown

# Build and load the browser extension
cd extension && ./build.sh

# Start a federation node with MCP server
cargo run -p pyana-node -- run --enable-faucet

# Start MCP server (for AI agent interaction)
cargo run -p pyana-node -- mcp
```

## Architecture

```
+-------------------------------------------------------------------------+
|                    Browser Extension (wallet)                             |
|  window.pyana · progressive disclosure · SLIP-10 keys · auto-lock        |
+-------------------------------------------------------------------------+
|                    WASM Playground (pyana-wasm)                           |
|  43 exports · full system simulation in browser                          |
+-------------------------------------------------------------------------+
|                    SDK Layer (pyana-sdk)                                  |
|  AgentWallet · AgentRuntime · SiloClient · HD wallet · IT-PIR           |
+-------------------------------------------------------------------------+
|                    Intent Engine (pyana-intent)                           |
|  Gossip broadcast · local Datalog matching · commit-reveal · IT-PIR     |
+-------------------------------------------------------------------------+
|                    Node / Network Layer                                   |
|  pyana-node (daemon, HTTP API, MCP server, gossip sync)                 |
|  pyana-net (Quinn QUIC, Plumtree gossip, 4 topics)                      |
|  wire (TCP postcard framing, STARK verification on receive)             |
+-------------------------------------------------------------------------+
|                    Federation Layer                                       |
|  federation (Ed25519 consensus, state roots, light client)              |
|  morpheus (adaptive BFT, 2-QC finality)                                 |
|  hints (BLS12-381 threshold sigs, KZG + SNARK)                          |
+-------------------------------------------------------------------------+
|                    Coordination (coord)                                   |
|  Causal DAG · 2PC atomic · Stingray bounded counters                    |
+-------------------------------------------------------------------------+
|                    Execution Layer                                        |
|  cell (isolated objects, c-lists, notes, revocation channels, OT)       |
|  turn (atomic txns, call forests, pipeline execution, encrypted turns)  |
+-------------------------------------------------------------------------+
|                    Proof Layer (circuit)                                  |
|  Plonky3 STARK (358-col, width-16 Poseidon2, 21 rounds)                |
|  17+ AIRs · programmable predicates · IVC · recursive verification      |
+-------------------------------------------------------------------------+
|                    Commitment Layer (commit)                              |
|  4-ary Merkle (BLAKE3 fast / Poseidon2 ZK) · fold deltas               |
+-------------------------------------------------------------------------+
|                    Policy Layer                                           |
|  trace (Datalog, deny-overrides-allow) · token (Macaroon + Biscuit)     |
|  tokenizer (X25519-ChaCha20Poly1305 seal/unseal)                       |
+-------------------------------------------------------------------------+
|                    Storage Layer                                          |
|  store (redb ACID) · secrets (keychain + AES-256-GCM) · audit           |
+-------------------------------------------------------------------------+
```

## Feature highlights

**Proof system**
- BabyBear STARK with Plonky3 backend, real algebraic constraints (not vacuous)
- Poseidon2 width-16, 8+13 rounds, Grain LFSR constants from p3-baby-bear
- 17+ specialized AIRs: Merkle, fold, derivation, predicates, note spending, IVC, block transition, QC, signatures
- Programmable predicates: `PredicateExpr` -> compiled AIR plan -> composed STARK proof
- Sub-second proof generation on Apple M-series

**Privacy (anonymous credential parity)**
- Ring membership (issuer anonymity via blinded Merkle)
- Unlinkable multi-show (fresh presentation tag per show)
- Committed selective disclosure (choose what to reveal)
- Predicate proofs: range, compound, temporal, relational, arithmetic, committed threshold
- IT-PIR for private intent discovery
- Oblivious transfer (Chou-Orlandi 1-of-N from X25519)
- Three verification modes: trusted (8us), selective (~200ms), fully private (~500ms)

**Federation**
- Simplified BFT with Ed25519 (vote verification, signed proposals, pacemaker)
- Morpheus adaptive BFT (2-QC finality, DAG-based)
- BLS12-381 threshold signatures (KZG + SNARK aggregate)
- State roots in every block (pre/post, note tree, nullifier set)
- LightClientProof for external verification
- Per-block state transition STARKs
- Proof-carrying QC (WOTS+ signatures in AIR)

**Execution**
- Atomic multi-party turns with call forest composition
- Journal-based rollback on any failure
- Promise pipelining (EventualRef, topological batch execution)
- Three-party introduction (no global directory)
- Two-phase cross-federation bridge (lock/receipt/cancel)
- Conservation invariant (value never created or destroyed)

**Economic model**
- Fee distribution: 50% proposer / 30% treasury / 20% burned
- Conditional deposit anti-griefing
- Stingray bounded counters (coordination-free local budgets)
- Epoch-scoped stake nullifiers (K=5)

**Tooling**
- MCP server (15+ tools for AI agent interaction)
- 4-node Docker devnet (one command)
- Chain explorer (web UI)
- WASM playground (43 exports, full simulation)
- Browser extension (Firefox + Chrome, progressive disclosure UX)
- 37 end-to-end demo scenarios
- AWS Graviton deployment (systemd + Caddy + ZeroSSL)

## Workspace

26 crates, ~184k LOC Rust, 2,141 tests:

| Crate | LOC | Purpose |
|-------|-----|---------|
| `circuit` | 43.0k | STARK prover/verifier, 17+ AIRs, IVC, Plonky3, recursive verification, predicate programs |
| `turn` | 18.8k | TurnExecutor: call forests, journal rollback, pipeline execution, encrypted turns |
| `demo-agent` | 18.7k | 37 end-to-end examples covering full pipeline |
| `cell` | 9.3k | Isolated objects, c-lists, notes, revocation channels, oblivious transfer |
| `federation` | 8.7k | Ed25519 consensus, state roots, epoch reconfig, LightClientProof |
| `intent` | 6.5k | Intent engine: gossip, Datalog matching, commit-reveal, IT-PIR |
| `bridge` | 6.3k | Token-to-circuit: presentation builder, predicate proofs |
| `tests` | 6.2k | Integration tests: adversarial, Byzantine, soundness, fuzz |
| `token` | 6.0k | AuthToken: Macaroon (HMAC-SHA256) + Biscuit (Ed25519+Datalog) |
| `wire` | 5.4k | TCP wire protocol, postcard framing, action binding |
| `morpheus` | 5.4k | Adaptive BFT (Lewis-Pye & Shapiro), 2-QC finality |
| `node` | 5.1k | Federation daemon: HTTP API, MCP server, gossip sync |
| `sdk` | 5.0k | Agent SDK: wallet, runtime, HD keys, IT-PIR discovery |
| `commit` | 4.5k | 4-ary Merkle trees, fold deltas, symbol table |
| `coord` | 4.4k | Causal DAG, 2PC, Stingray bounded counters |
| `hints` | 3.8k | BLS12-381 threshold signatures (KZG + SNARK) |
| `store` | 3.8k | redb ACID persistence, note tree, nullifier set |
| `net` | 3.8k | Quinn QUIC, Plumtree gossip |
| `trace` | 3.7k | Datalog evaluator, derivation traces, deny-overrides-allow |
| `wasm` | 2.8k | Browser WASM bindings (43 exports) |
| `demo` | 2.7k | CLI demos and key generation |
| `audit` | 2.5k | Usage logging, budget enforcement |
| `macaroon` | 2.0k | HMAC-chain bearer tokens |
| `tokenizer` | 1.6k | X25519-ChaCha20Poly1305 seal/unseal |
| `types` | 1.3k | CellId, Ed25519, AttestedRoot, causal DAG types |
| `secrets` | 1.1k | OS keychain + encrypted file store |

Plus: `chain/` (SP1/EVM settlement), `extension/` (browser wallet), `site/` (explorer + playground), `docker/` (devnet).

## Interaction methods

**MCP server** -- AI agents interact via `cargo run -p pyana-node -- mcp`. 15+ JSON-RPC tools: create agents, submit turns, post intents, manage capabilities, generate proofs.

**Browser extension** -- `window.pyana` injected into every page. Authorize, post intents, offer capabilities, provision wallets. Progressive disclosure UX for verification mode selection.

**WASM playground** -- Full system simulation at `site/playground/`. Create cells, submit turns, bridge notes, generate STARK proofs -- all client-side in the browser.

**Chain explorer** -- Block viewer and federation status at `site/explorer/`.

**HTTP API** -- Node exposes localhost REST API for turn submission, state queries, intent posting.

**Docker devnet** -- `cd docker && docker compose up` for a 4-node federation with faucet.

## Verification modes

| Mode | Verifier sees | Latency | Use case |
|------|--------------|---------|----------|
| **Trusted** | Full cleartext token + Datalog trace | ~8 us | Same-org, same-trust-domain |
| **Selective** | Chosen facts + STARK proof | ~200 ms | Cross-org, partial disclosure |
| **Fully Private** | One bit (allow/deny) + STARK proof | ~500 ms | Zero-knowledge presentation |

All three modes work offline. No federation liveness required.

## Honest status

**What works today:**
- Real STARK proofs with full Poseidon2 algebraic constraints (358 columns, 21 rounds). 513 circuit tests.
- Full privacy pipeline through Phase 5 (ring membership, unlinkable multi-show, selective disclosure, predicate proofs)
- Complete token-to-proof-to-turn-execution pipeline
- Federation consensus with state roots, vote verification, LightClientProof
- Gossip hookup: consensus messages over QUIC (4 topics)
- Two-phase cross-federation bridge with STARK binding
- IT-PIR private discovery + oblivious transfer
- Docker devnet, chain explorer, WASM playground, browser extension, MCP server
- 37 end-to-end demo scenarios
- Comprehensive security hardening (verify_strict, domain separation, zeroization, fail-closed)

**What is in progress:**
- Recursive proof composition works for pairs; arbitrary-N heterogeneous AIR composition not yet operational
- Dual Merkle systems (BLAKE3 / Poseidon2) not yet unified
- Encrypted turns (Phase 6 federation privacy) prototyped but not in production consensus path
- Morpheus BFT proven sound but simplified consensus is the tested production path
- Multi-hop gossip not yet proven at scale

**What is designed but unimplemented:**
- Post-quantum migration for classical components (waiting on NIST)
- Full constant-size recursive composition of heterogeneous AIRs
- SP1/EVM settlement (`chain/` workspace, excluded from build)

## Design documents

- [`PYANA_DESIGN.md`](PYANA_DESIGN.md) -- Full architecture, security model, and system comparison
- [`docs/privacy-architecture.md`](docs/privacy-architecture.md) -- 6-phase privacy roadmap
- [`docs/federation-architecture.md`](docs/federation-architecture.md) -- Federation design
- [`docs/programmable-predicates.md`](docs/programmable-predicates.md) -- Predicate compilation pipeline
- [`docs/economic-model.md`](docs/economic-model.md) -- Fee distribution, anti-griefing
- [`docs/agent-substrate.md`](docs/agent-substrate.md) -- seL4-to-Pyana mapping, MCP integration
- [`docs/proof-carrying-state.md`](docs/proof-carrying-state.md) -- Receipt chains, IVC, federation exit
- [`docs/private-information-retrieval.md`](docs/private-information-retrieval.md) -- IT-PIR protocol
- [`docs/accumulators.md`](docs/accumulators.md) -- Polynomial accumulator design
- [`docs/pq-roadmap.md`](docs/pq-roadmap.md) -- Post-quantum migration path
- [`docs/infrastructure.md`](docs/infrastructure.md) -- Deployment (Docker, AWS Graviton)

Plus 16 additional research documents in `docs/`.

## License

MIT OR Apache-2.0
