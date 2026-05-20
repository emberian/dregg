# pyana

Your agents hold unforgeable capabilities, delegate them with attenuation-only narrowing, prove authorization with zero-knowledge STARKs, discover each other through privacy-preserving intents, and carry their own state as proof chains that no federation can censor. Pyana is a distributed object-capability runtime where objects are isolated cells, messages are atomic turns, and the network is a sealed capability marketplace. You get the security properties of consensus systems without the liveness dependency: verification is offline, proofs are post-quantum, and agents can exit any federation at any time carrying their full history.

## Core concepts

**Cells** -- Isolated objects with a capability list (c-list), balance, nonce, program predicates, and private notes. The unit of identity and state.

**Turns** -- Atomic state transitions composed from call forests. A turn either fully commits or fully rolls back. Multi-party turns compose across cells with journal-based atomicity.

**Capabilities** -- Unforgeable references from one cell to another. Only created by introduction or minting; only narrowed, never amplified. Attenuation is the fundamental delegation primitive.

**Three-party introduction** -- Alice introduces Bob to Carol by emitting an `Introduce` effect during a turn. Bob gains a capability to Carol, constrained to at most what Alice herself holds. This is how new communication paths form without a global directory.

**Sealer/unsealer** -- X25519-ChaCha20Poly1305 keypairs held by the tokenizer daemon. Encrypt a credential under a capability token; only the holder of both the capability and the unsealer key can recover the plaintext. Enables partition-tolerant offline transfer: hand someone a sealed bundle and they can use it later without contacting you.

**Intents** -- Privacy-preserving capability marketplace. A page broadcasts "I need capability X" as a public intent; wallets privately evaluate whether they can satisfy it using local Datalog; fulfillment proves satisfaction with a STARK without revealing what token, delegation chain, or other capabilities the satisfier holds.

**Notes** -- Anonymous cells for private value transfer. A note commits to (owner, value, randomness); spending produces a position-independent nullifier that prevents double-spend without revealing which note was consumed.

**STARK proofs** -- BabyBear field + FRI + Poseidon2 algebraic hash. Real proofs (~24 KiB, sub-second generation). Three AIR circuits: fold (attenuation chain), derivation (Datalog authorization), Merkle membership.

**Federation** -- BFT ordering service (Morpheus adaptive consensus, 3-64 nodes). Attests to nullifier and note tree roots. Does NOT hold cell state -- agents own their own state as receipt chains.

**Receipt chains** -- Every committed turn produces a `TurnReceipt` with pre/post state hashes. The chain of receipts IS the agent's state proof. IVC compresses the chain to constant size. You can exit a federation by simply leaving with your proof chain.

## Quick example

```rust
use pyana_sdk::{AgentWallet, AgentRuntime};
use pyana_token::Attenuation;
use pyana_turn::{TurnBuilder, Effect};

// Agent spawns a sub-agent with attenuated capabilities
let mut wallet = AgentWallet::new();
let root = wallet.mint_token(b"secret-key-material-32-bytes!!!!", "inventory-service");
let child_token = wallet.attenuate(&root, &Attenuation {
    services: vec![("inventory".into(), "read".into())],
    max_ttl: Some(std::time::Duration::from_secs(3600)),
    ..Default::default()
}).unwrap();

// The sub-agent proves authorization to a third party
// without revealing the delegation chain.
let proof = wallet.present_private(&child_token, "inventory", "read").unwrap();
// proof is a ~24 KiB STARK. The verifier learns ONE BIT: authorized or not.
```

## Verification modes

| Mode | Verifier sees | Latency | Use case |
|------|--------------|---------|----------|
| **Trusted** | Full cleartext token + Datalog trace | ~8 us | Same-org, same-trust-domain |
| **Selective** | Chosen facts + STARK proof | ~2 ms | Cross-org, partial disclosure |
| **Fully Private** | One bit (allow/deny) + STARK proof | ~2 ms | Zero-knowledge presentation |

All three modes work offline. No federation liveness required -- proof + attested root is complete.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       Browser Extension (wallet)                         │
│  window.pyana: authorize · postIntent · offerCapability · provision      │
├─────────────────────────────────────────────────────────────────────────┤
│                       SDK Layer (pyana-sdk)                              │
│  AgentWallet · AgentRuntime · SiloClient                                │
├─────────────────────────────────────────────────────────────────────────┤
│                       Intent Engine (pyana-intent)                       │
│  Gossip broadcast · local Datalog matching · STARK fulfillment proofs   │
├─────────────────────────────────────────────────────────────────────────┤
│                       Node / Network Layer                               │
│  pyana-node (federation daemon) · pyana-relay (QUIC relay)              │
│  TCP wire protocol · postcard framing · STARK verification on receive   │
├─────────────────────────────────────────────────────────────────────────┤
│                       Federation Layer                                   │
│  morpheus (adaptive BFT) · hints (BLS12-381 threshold sigs)             │
│  federation (Ed25519 consensus, epoch reconfig, revocation trees)        │
├─────────────────────────────────────────────────────────────────────────┤
│                       Coordination Layer (coord)                         │
│  Causal DAG · 2PC atomic · bounded counters (Stingray budget channels)  │
├─────────────────────────────────────────────────────────────────────────┤
│                       Execution Layer                                    │
│  cell (isolated objects + c-lists) · turn (atomic txns, call forests)   │
│  Three-party introduction · routing directives                          │
├─────────────────────────────────────────────────────────────────────────┤
│                       Proof Layer (circuit)                              │
│  BabyBear STARK + FRI (~24 KiB, sub-second) · Poseidon2 (in-circuit)   │
│  IVC fold chains · AIR: fold, derivation, Merkle membership             │
├─────────────────────────────────────────────────────────────────────────┤
│                       Commitment Layer (commit)                          │
│  4-ary Merkle trees (BLAKE3 fast / Poseidon2 ZK) · fold deltas         │
├─────────────────────────────────────────────────────────────────────────┤
│                       Policy Layer                                       │
│  trace (Datalog evaluator + derivation traces)                          │
│  token (AuthToken: Macaroon HMAC + Biscuit Ed25519+Datalog)             │
│  tokenizer (X25519-ChaCha20Poly1305 seal/unseal daemon)                 │
├─────────────────────────────────────────────────────────────────────────┤
│                       Storage Layer                                      │
│  store (redb ACID) · secrets (OS keychain + encrypted file)             │
│  Note commitment tree · nullifier set · audit log                       │
└─────────────────────────────────────────────────────────────────────────┘
```

## Workspace

26 crates (~97k LOC Rust, 1200+ tests):

| Crate | Purpose |
|-------|---------|
| `cell` | Isolated objects with capability lists, notes, programs, state visibility |
| `turn` | Atomic transaction executor (call forests, journal rollback, two-phase fee, three-party introduction) |
| `coord` | Multi-silo coordination: causal DAG, 2PC, bounded counters (Stingray) |
| `circuit` | STARK prover/verifier, Poseidon2 AIR, Datalog-in-STARK, IVC, Plonky3 |
| `commit` | 4-ary Merkle trees, fold deltas, symbol table |
| `trace` | Datalog evaluator with derivation trace extraction |
| `token` | AuthToken trait -- Macaroon (HMAC-SHA256) + Biscuit (Ed25519 + Datalog) |
| `tokenizer` | X25519-ChaCha20Poly1305 seal/unseal daemon |
| `macaroon` | HMAC-chain bearer tokens with constant-time verify |
| `secrets` | OS keychain + encrypted file store |
| `types` | Canonical types: CellId, Ed25519, AttestedRoot, causal DAG |
| `federation` | Ed25519 consensus nodes, epoch reconfiguration, revocation trees |
| `morpheus` | Adaptive BFT (Lewis-Pye & Shapiro) |
| `hints` | BLS12-381 threshold signatures (KZG + SNARK) |
| `wire` | TCP wire protocol, federation bridge, multi-node demo |
| `store` | redb persistence, note commitment tree, nullifier set |
| `audit` | Usage logging, consistency proofs, budget enforcement |
| `bridge` | Connects token pipeline to circuit (presentation builder) |
| `sdk` | Agent SDK: wallet, runtime, verification modes |
| `wasm` | Browser WASM bindings (12 exported functions) |
| `node` | Federation node daemon -- consensus participant, localhost API |
| `relay` | Lightweight QUIC relay -- attested roots, peer connection relay, root token minting |
| `intent` | Distributed intent engine -- gossip broadcast, local matching, STARK fulfillment |
| `demo` | CLI demos |
| `demo-agent` | End-to-end scenarios (full token-to-STARK-to-turn-execution pipeline) |
| `tests` | Integration tests |

Plus `chain/` (standalone workspace for SP1/EVM settlement) and the browser `extension/`.

## Getting started

```sh
# Build the full workspace
cargo build

# Run all tests
cargo test

# Run the end-to-end demo (federation + token + STARK + turn execution)
cargo run -p pyana-demo-agent

# Build the browser WASM module
cargo build -p pyana-wasm --target wasm32-unknown-unknown

# Build and load the browser extension (Chrome/Firefox)
cd extension && ./build.sh
# Then load extension/manifest.json as an unpacked extension

# Open the auth demo page
open site/examples/auth-demo.html
```

The extension injects `window.pyana` into every page. Try it:

```js
// Check connection
await pyana.isConnected();

// Broadcast "I need read access to documents/*"
await pyana.postIntent({
  actions: [{ action: "read", resource: "documents/*" }],
  constraints: [{ Service: "storage" }]
});

// Listen for matches
pyana.onMatch(match => console.log("Found:", match));
```

## Live infrastructure

The federation runs on GitHub Actions as persistent scheduled workflows:

| Workflow | Schedule | Role |
|---------|----------|------|
| `federation-node-1.yml` | Every 5 hours | Consensus participant, state persistence via artifacts |
| `federation-node-2.yml` | Every 5 hours | Consensus participant |
| `federation-node-3.yml` | Every 5 hours | Consensus participant |
| `intent-service.yml` | Every 5 hours (offset) | Intent pool gossip relay |
| `relay.yml` | Continuous | QUIC relay for peer connections |

State persists across runs via GitHub Actions artifacts. The federation produces attested roots (threshold-signed Merkle roots over the nullifier set) that any offline verifier can use as freshness anchors.

To connect a local node to the live federation:

```sh
cargo run -p pyana-node -- --federation-peers=github
```

## Design documents

- [`PYANA_DESIGN.md`](PYANA_DESIGN.md) -- Full architecture, security model, and comparison
- [`docs/proof-carrying-state.md`](docs/proof-carrying-state.md) -- Federation-as-ordering-service model
- [`docs/verification-modes.md`](docs/verification-modes.md) -- Three-mode verification spec
- [`docs/infrastructure.md`](docs/infrastructure.md) -- GitHub Actions federation deployment
- [`docs/pq-roadmap.md`](docs/pq-roadmap.md) -- Post-quantum migration path
- [`docs/research-recursive-stark.md`](docs/research-recursive-stark.md) -- Recursive STARK-in-STARK plan
- [`paper/pyana.typ`](paper/pyana.typ) -- Whitepaper (typst)

## Comparison

| System | What pyana adds |
|--------|----------------|
| **Cap'n Proto** | Cap'n Proto is a serialization format with RPC. Pyana is a capability *runtime* with ZK-private delegation, multi-party atomic turns, and cryptographic proof that a capability chain is valid without revealing it. |
| **UCAN** | UCAN delegation chains are transparent -- every verifier sees the full chain. Pyana proves the same authorization relationship as a STARK without revealing any intermediate authorities. |
| **Mina Protocol** | Shared DNA (zkApp model, call forests, cells-as-accounts). Pyana applies this to authorization and distributed object semantics rather than financial transactions, with federated BFT instead of global Ouroboros. |
| **Midnight** | Privacy DeFi on Cardano. Pyana is not a payment network -- it is a general-purpose object-capability runtime where "value" is just one kind of capability. |
| **Cosmos IBC** | IBC requires active relayer liveness for cross-chain messages. Pyana verification is fully offline (proof + root), and the capability model replaces channel-based permissions with unforgeable object references. |

## Honest status

What works today:
- Real STARK proofs (BabyBear + FRI + Poseidon2), sub-second generation, ~24 KiB
- Full token-to-proof-to-turn-execution pipeline
- 3-node federation with Morpheus BFT consensus and BLS12-381 threshold signatures
- Browser extension wallet with intent matching
- TCP wire protocol with STARK verification on receive
- 20+ end-to-end demo scenarios

What is in progress:
- Recursive proof aggregation uses hash-chain accumulation, not true STARK-in-STARK (proof size grows with chain length)
- Gossip layer is one-hop (QUIC relay exists, but no authenticated multi-hop delivery)
- Dual Merkle systems (BLAKE3 fast path vs Poseidon2 ZK path) not yet unified
- Federation consensus messages don't yet flow over the wire protocol (currently in-process channels)

## License

MIT OR Apache-2.0
