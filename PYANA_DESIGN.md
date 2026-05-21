# Pyana: Technical Design

## 1. What is Pyana

Pyana is a distributed object-capability runtime where isolated objects (cells) communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. It is not an auth library bolted onto an existing system -- the authorization structure IS the computational structure. Cells hold unforgeable references to each other, messages are atomic state transitions with journal rollback, and the network is a sealed capability marketplace with privacy-preserving discovery.

The system implements E-style distributed object semantics (promise pipelining, three-party introduction, sealer/unsealer), Mina-style execution (cells as zkApp accounts, turns as ZkappCommands, call forests), seL4-style capability derivation (recast as a proof structure for asynchronous distributed systems), and proof-carrying state (receipt chains as the primary state representation, with federation reduced to an ordering service). Agents own their own state, can exit any federation carrying their full history, and verify each other offline using only STARK proofs and attested Merkle roots.

## 2. Core Insight

**Capability attenuation IS incrementally verifiable computation.** Every time a capability is delegated with restrictions (narrowed to fewer services, shorter time windows, reduced budget), that attenuation step is a fold over a committed fact set -- removing facts, never adding them. Each fold produces a strictly smaller successor state. This monotonic narrowing forms a chain of state transitions that IVC was designed to prove. The prover demonstrates "I hold a valid attenuation chain from a federation-registered issuer, ending at a capability set that satisfies your request." The verifier checks a single STARK proof without seeing any intermediate states, delegation chain, or other capabilities. We get zero-knowledge presentation for free from the capability model -- the authorization structure is the computation being proved.

## 3. Architecture

```
+-------------------------------------------------------------------------+
|                    Browser Extension (wallet)                             |
|  window.pyana: authorize, postIntent, offerCapability, provision         |
+-------------------------------------------------------------------------+
|                    SDK Layer (pyana-sdk)                                  |
|  AgentWallet · AgentRuntime · SiloClient · HD wallet (BIP39)            |
+-------------------------------------------------------------------------+
|                    Intent Engine (pyana-intent)                           |
|  Gossip broadcast · local Datalog matching · commit-reveal · STARK proof |
+-------------------------------------------------------------------------+
|                    Node / Network Layer                                   |
|  pyana-node (federation daemon, localhost API)                           |
|  pyana-relay (QUIC relay, attested roots, peer connection)              |
|  pyana-net (Quinn QUIC, Plumtree gossip, topic-based dissemination)     |
|  wire (TCP postcard framing, STARK verification on receive)             |
+-------------------------------------------------------------------------+
|                    Federation Layer                                       |
|  morpheus (adaptive BFT, Lewis-Pye & Shapiro)                           |
|  hints (BLS12-381 threshold sigs, KZG + SNARK aggregate verification)   |
|  federation (Ed25519 consensus, epoch reconfig, revocation trees)        |
+-------------------------------------------------------------------------+
|                    Coordination Layer (coord)                             |
|  Causal DAG · 2PC atomic · bounded counters (Stingray budget channels)  |
+-------------------------------------------------------------------------+
|                    Execution Layer                                        |
|  cell (isolated objects, c-lists, notes, programs, state visibility)    |
|  turn (atomic executor, call forests, journal rollback, two-phase fee)  |
|  Three-party introduction · EventualRef · routing directives            |
+-------------------------------------------------------------------------+
|                    Proof Layer (circuit)                                  |
|  BabyBear STARK + FRI (~24 KiB, sub-second)                            |
|  BabyBear4 extension field (124-bit security)                           |
|  Poseidon2 in-circuit hash (width 8, alpha=7, 8+22 rounds)             |
|  AIRs: Poseidon2, Merkle membership, note spending, multi-step         |
|         derivation, fold chain, IVC accumulation, recursive verifier    |
|  Backends: BabyBear STARK, Plonky3, Halo2, Nova, Binius                |
+-------------------------------------------------------------------------+
|                    Commitment Layer (commit)                              |
|  4-ary Merkle trees (BLAKE3 fast path / Poseidon2 ZK path)             |
|  Fold deltas (monotonic state transitions) · symbol table               |
+-------------------------------------------------------------------------+
|                    Policy Layer                                           |
|  trace (Datalog evaluator + derivation trace extraction)                |
|  token (AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog)      |
|  tokenizer (X25519-ChaCha20Poly1305 seal/unseal)                       |
+-------------------------------------------------------------------------+
|                    Storage Layer                                          |
|  store (redb ACID, note commitment tree, nullifier set)                 |
|  secrets (OS keychain + AES-256-GCM encrypted file store)              |
|  audit (usage log, budget enforcement, consistency proofs)              |
+-------------------------------------------------------------------------+
```

## 4. Execution Model

### Cells

A cell is the fundamental unit of isolated state. Each cell holds:

- Content-addressed identity (`CellId`, 256 bits)
- 8 generic field slots in F_p where p = 2^31 - 2^27 + 1 (BabyBear prime)
- A capability list (c-list): the set of capabilities the cell may exercise
- Permission requirements per action type
- Balance (computrons), nonce (replay protection)
- Optional programs (predicates, circuits) defining valid state transitions
- Private notes (anonymous cells for shielded value transfer)

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

### Turns

A turn is an atomic transaction over one or more cells. It contains:

- A call forest: a tree of actions, executed depth-first
- A fee in computrons covering execution cost
- A nonce (monotonically increasing per cell)
- Authorization: Ed25519 signature, ZK proof, or both

If any action in the call forest fails, all effects roll back via journal replay. The executor enforces a conservation invariant: sum of balance changes + fee = 0. Value cannot be created or destroyed within a turn.

### Pipelines (EventualRef and Topological Execution)

The executor processes batches of turns with declared dependency edges as a DAG. A `PipelinedSend` targets an `EventualRef` -- a reference to the output of a pending turn, identified by the turn's hash and an output slot index:

```
Target = Concrete(CellId) | Eventual(source_turn: [u8; 32], slot: u32)
```

When a source turn commits, its outputs populate a resolution table and dependent turns rewrite their targets to concrete CellIds. If turn t_i fails and t_j depends on t_i, then t_j receives `DependencyFailed` without executing. This eliminates round-trip latency in distributed object protocols (E-style promise pipelining).

### Call Forests

Actions within a turn form a tree (call forest), executed depth-first. Child actions run within the scope of their parent -- if a child fails, the parent's sub-effects roll back but the parent can catch the failure. Call forests compose: a multi-party turn merges forests from multiple cells into a single atomic execution.

### Three-Party Introduction

Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by emitting an `Effect::Introduce` during a turn. This produces a `RoutingDirective`:

```
RoutingDirective { sender: CellId, target: CellId, authorizing_turn: [u8; 32], expires: Option<u64> }
```

The node's routing table is populated from these directives. No global directory exists -- all communication paths form through introductions, not discovery.

### Delegation (Snapshot + Refresh)

A child cell receives a point-in-time snapshot of its parent's c-list:

```
DelegatedRef { source, snapshot: [CapabilityRef], epoch, refreshed_at, max_staleness }
```

The child acts offline using the snapshot. Verifiers reject presentations where `now - refreshed_at > max_staleness`. This creates a configurable tradeoff between availability and revocation freshness. Epoch-based revocation: the parent bumps the epoch, invalidating all outstanding snapshots until children refresh.

## 5. Capability Model

### C-Lists and Confinement

Each cell holds a c-list: the exhaustive set of capabilities it may exercise. `GrantCapability` checks that the granting cell actually holds authority over the source. A cell cannot delegate what it does not have.

### Attenuation (Monotonic Narrowing)

Delegation chains can only restrict, never expand. A root token grants `{all services, infinite TTL, full budget}`. Each attenuation step produces a new token with a strictly smaller capability set. The fold delta captures exactly what was removed: `Delta = { f in F_old | f not in F_new }`. The fold AIR constraint enforces that only removals (never additions) occur.

### Capability Derivation Tree (CDT)

The distributed analog of seL4's kernel-enforced CDT. Each delegation step records:

```
DelegationEdge { parent: CapHash, child: CapHash, attenuation: Delta, epoch: u64 }
```

These edges form a Merkle-committed tree. The key duality: seL4 ENFORCES the tree (kernel walks it synchronously for revocation); Pyana PROVES the tree (delegator proves their capability descends from a valid root, revoker proves non-membership in the current valid set).

### Sealer/Unsealer (Offline Transfer)

X25519-ChaCha20Poly1305 keypairs enable partition-tolerant offline capability transfer. The sender seals a capability under the recipient's public key with a fresh ephemeral keypair (forward secrecy). The sealed box traverses untrusted channels revealing nothing. The recipient unseals with their private key when they come online. A BLAKE3 commitment binds the ciphertext to the capability without revealing it.

### Breadstuff Tokens (Bearer Authorization)

Capabilities are encoded as Datalog fact sets within bearer tokens. Two token backends:

- **Macaroon**: HMAC-SHA256 chain. Each caveat attenuates the fact set. Constant-time verification.
- **Biscuit**: Ed25519 signature + embedded Datalog policy. Decentralized verification without sharing the root key.

## 6. Proof System

### BabyBear STARK with Real Poseidon2 Constraints

All proofs use BabyBear4 (degree-4 extension field, |F_{p^4}| ~ 2^124, providing 124-bit challenge security). FRI with 50 queries and blowup factor 4 gives ~100-bit soundness. Poseidon2 (width 8, alpha=7, 8 external + 22 internal rounds) serves as the in-circuit hash. Proofs are ~24 KiB, generated in sub-second time on Apple M-series.

### AIR Circuits

1. **Poseidon2 Permutation**: Proves y = Poseidon2(x). Constraint degree 7.
2. **Merkle Membership**: Proves leaf exists under root in 4-ary tree. Position validity + hash binding per level.
3. **Note Spending**: Proves knowledge of spending key, commitment preimage, and Merkle membership. Produces a position-independent nullifier preventing double-spend. Single AIR with 12 columns.
4. **Multi-Step Derivation**: Proves N valid Datalog rule applications produce ALLOW. 92 columns, 19 constraint families. Handles substitution, equal/memberof/GTE checks, accumulated hash chain.
5. **Fold Chain (Attenuation)**: Proves monotonic fact removal from old root to new root. Only removals possible (membership proofs under old root required for each removed fact).
6. **IVC Accumulation**: Proves a sequence of N valid fold steps with root continuity and hash chain binding. Constant-size output regardless of N.
7. **Recursive Verifier**: Encodes STARK verification (Fiat-Shamir replay, FRI folding, constraint evaluation) as an AIR. Collapses N sub-proofs into one.

### Body Fact Membership Composition

The full authorization proof composes:

```
Derivation Proof (N rule steps -> ALLOW)
+ Body Membership Proofs (each body fact in tree under R_0)
+ Fold Chain Proof (R_issuer -> R_0 via attenuation)
+ Issuer Membership Proof (issuer in federation Merkle tree)
```

Binding via shared public inputs: derivation's state root = fold chain's final root; fold chain's initial root = issuer's committed capability root; issuer membership root = federation attested root.

### IVC (State Transition Proofs)

Receipt chains (TurnReceipts with pre/post state hashes) are compressed via IVC into constant-size proofs. A verifier needs only: the IVC proof, current state commitment, and nullifier non-membership proof.

### Proof Backends

| Backend | Field | Proof Size | PQ? | Recursion |
|---------|-------|-----------|-----|-----------|
| BabyBear STARK | F_{2^31-2^27+1} + FRI | ~24 KiB | Yes | Via Plonky3 |
| Binius | GF(2) tower + Groestl-256 | ~1-4 KiB | Yes | No |
| Halo2 | BN254/Pasta + KZG | ~1-5 KiB | No | Yes |
| Nova | Pasta cycle (Pallas/Vesta) | ~10 KiB | No | IVC native |

Multi-hash roots (Poseidon2, Groestl256, PoseidonBN254) let each backend reference its native commitment.

### Recursive Verification

Recursive verification collapses N proofs into 1: generate each sub-proof independently, recursively verify each inside a new STARK circuit, chain the recursive proofs. The Plonky3-based recursive verifier is implemented and working for pairs of proofs. Arbitrary-N chaining via `build_recursive_ivc_chain` uses sequential composition. Full heterogeneous AIR composition (derivation + fold + membership in one recursive proof) is designed but not yet operational.

## 7. Privacy Model

### Three Verification Modes

| Mode | Verifier Learns | Latency | Proof Size |
|------|----------------|---------|-----------|
| **Trusted** | Full cleartext token + Datalog trace | ~8 us | 0 |
| **Selective Disclosure** | Chosen facts + conclusion | ~200 ms | ~45 KB |
| **Fully Private** | One bit (allow/deny) | ~500 ms | ~80 KB |

All three modes work offline. The same Datalog rules yield the same answer; what changes is how much the verifier learns. Mode selection: hold root key -> Trusted; need partial facts -> Selective; need anonymity -> Private.

### Progressive Disclosure

Cell fields are tagged `Public`, `Committed`, or `SelectivelyDisclosable`. When presenting state, the agent reveals chosen fields from their proof chain. The verifier checks consistency with the state commitment without seeing hidden fields.

### Notes (Anonymous Cells)

A note commits to (owner, value, asset_type, creation_nonce, randomness) via Poseidon2. Spending produces a nullifier = Poseidon2(commitment, spending_key, nonce) that is position-independent -- preventing double-spend without revealing which note was consumed. The note commitment tree is federation-maintained; spending proofs demonstrate knowledge of the spending key + Merkle membership without revealing the note.

### Intent Matching (Private Discovery)

Agents broadcast needs as public intents ("I need capability matching spec S"). Wallets evaluate locally using Datalog: "does any token in my wallet satisfy S?" This evaluation never leaves the wallet. If a match exists, the wallet generates a STARK proof of capability satisfaction without revealing which token, what delegation chain, or what else it holds.

## 8. Intent Engine

### Architecture

1. **Pool**: Content-addressed intents identified by blinded CommitmentIds. Broadcast via gossip.
2. **Match**: Wallets evaluate intents locally against their c-lists using Datalog. No capability information leaves the wallet.
3. **Commit-Reveal**: Satisfier publishes C = H(intent_id || satisfier_secret) before revealing proof. Prevents frontrunning.
4. **Fulfill**: STARK proof of capability satisfaction. Verifier learns only that someone can satisfy the intent.

### MatchSpec Language

Intents declare the shape of needed capability via MatchSpec predicates: required actions, target resources, constraint atoms. The spec reveals what is NEEDED, never what is HELD.

### Stake Requirement

Intent submission requires a Poseidon2 Merkle proof demonstrating the submitter has a valid note commitment in the note tree (proving economic stake without revealing balance or identity).

### Privacy Properties

The gossip network sees intents (public needs) but never capabilities (private holdings). The requester learns only that someone can satisfy their need. The satisfier reveals only that they can satisfy it. Limitation: the push model means satisfiers must be online and subscribed to the gossip topic.

## 9. Federation

### Morpheus Adaptive BFT

Federation consensus uses Morpheus (Lewis-Pye & Shapiro): adaptive Byzantine consensus tolerating up to f Byzantine nodes in a 3f+1 committee, with view-change and block finalization. Committee size: 3-64 nodes.

### BLS12-381 Threshold Signatures

A quorum certificate is a single aggregate BLS12-381 threshold signature via real KZG polynomial commitments + SNARK proof for aggregate verification. Verification cost is constant regardless of committee size.

### Epoch Reconfiguration

Federation membership changes occur at epoch boundaries. Each epoch carries a new committee set and updated threshold parameters. DelegatedRefs track the epoch at which they were issued.

### Attested Roots

The federation attests to:

```
AttestedRoot { nullifier_root, note_tree_root, height, timestamp, qc }
```

The federation does NOT attest to cell state. Cell state is proved by the cell's own receipt chain. The separation means the federation provides anti-double-spend ordering while agents own their own state.

### RevocationChannel (Opt-in Synchrony)

For applications requiring near-instant revocation: a `RevocationChannel` is a circuit breaker between revoker and subjects. Subjects voluntarily subscribe and check channel state (Active/Tripped) before exercising gated capabilities. Trip propagates via federation attestation gossip within one consensus round. Degrades gracefully offline (bounded staleness). Designed but not yet implemented.

### Federation as Ordering Service

The federation is NOT a state container. It orders nullifiers and attests to note tree roots. Agents carry their own state as proof chains. This enables trivial federation exit: stop submitting nullifiers, take your proof chain, join another ordering service or operate standalone.

## 10. Proof-Carrying State

### Receipt Chains

Every committed turn produces a `TurnReceipt` with pre/post state hashes, effects hash, and computron cost. Receipts chain: `receipt[n].post_state_hash == receipt[n+1].pre_state_hash`. The chain IS the state proof -- anyone can verify from genesis without contacting a federation.

### Executor Signatures

Each receipt carries the executor's Ed25519 signature attesting to valid execution (preconditions checked, programs satisfied, conservation enforced).

### IVC Compression

The IVC layer compresses an arbitrary-length receipt chain into a constant-size proof. A verifier needs: (1) the IvcProof (proves chain validity from genesis), (2) current state commitment, (3) nullifier non-membership proof.

### Federation Exit

An agent leaves by stopping nullifier submission. Their proof chain is portable -- it proves state validity from genesis without referencing federation-specific data. The agent can join another ordering service or operate standalone.

### Dual Merkle (BLAKE3 Fast + Poseidon2 ZK)

The commitment layer maintains parallel Merkle trees: BLAKE3 for fast operational hashing, Poseidon2 for in-circuit ZK verification. These are not yet unified -- currently the BLAKE3 Merkle proofs cannot be directly verified inside a STARK. Unification is a known priority.

## 11. Networking

### Quinn QUIC (pyana-net)

All inter-silo communication uses QUIC via Quinn with multiplexed streams and 0-RTT resumption. The relay crate provides a lightweight QUIC relay for peer connection brokering and attested root distribution.

### Plumtree Gossip

Topic-based hybrid push dissemination: eager push (degree 3) for spanning-tree delivery, lazy push (IHave notifications) for redundancy, periodic Bloom filter anti-entropy. Four gossip topics: turns, revocations, intents, attested roots.

### Wire Protocol (TCP)

Postcard-framed TCP for direct silo-to-silo communication. Messages carry STARK proofs verified on receive. Three variants: Presentation (authorization proof), Revocation (non-membership proof), TurnSubmission.

### Node HTTP/WS API

`pyana-node` exposes a localhost HTTP/WebSocket API for local clients. Supports: turn submission, state query, intent posting, federation status.

### Browser Extension

Injects `window.pyana` into every page. API surface: `authorize`, `postIntent`, `offerCapability`, `provision`, `isConnected`, `onMatch`. Communicates with a local pyana-node or the live federation via discovery.json.

## 12. Storage

- **redb**: ACID crash-safe persistence for cell state, note commitment trees, and nullifier sets
- **Encrypted keychain**: OS keychain integration (via `keyring` crate) + AES-256-GCM encrypted file store for Ed25519 identity keys and sealed secrets
- **Note trees**: 4-ary Poseidon2 Merkle tree of note commitments, maintained by the federation
- **Nullifier sets**: Append-only set with ordered leaves enabling non-membership proofs (prove the gap)

## 13. SDK

- **AgentWallet**: Token management, attenuation, presentation (all three modes), proof generation, receipt chain maintenance
- **AgentRuntime**: Turn construction, pipeline submission, effect handling, intent broadcasting
- **HD Wallet (BIP39)**: Hierarchical deterministic key derivation for stable agent identities across restarts
- **Verification API**: `wallet.authorize(&token, &request, mode)` returns mode-appropriate `AuthorizationPresentation`
- **SiloClient**: Federation connection, state sync, nullifier submission

## 14. Security Model

### Trust Boundaries

Everything that crosses a trust boundary is post-quantum secure (STARK proofs, Poseidon2/BLAKE3 Merkle commitments, HMAC chains). Classical cryptography (Ed25519, BLS12-381, X25519) exists only between parties that already trust each other within a federation.

### Resolved Audit Findings (All 8)

1. Turn executor verifies Ed25519 signatures via `verify_authorization`
2. Turn executor verifies ZK proofs via `ProofVerifier` trait
3. Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`
4. Wire protocol uses 64-byte signatures (via pyana-types)
5. Integer overflow in excess tracking replaced with checked arithmetic
6. `CreateCell` rejects non-zero balance (prevents minting from nothing)
7. QC forgery bypass (aggregate_qc short-circuit) removed
8. Body fact membership proven via Poseidon2 Merkle STARKs (not just asserted)

### Post-Quantum Roadmap

- Phase 1 (current): STARK path is PQ today
- Phase 2: BLS12-381 -> lattice threshold signatures (Hermine/Oriole/TalonG, pending NIST 2026/2027)
- Phase 3: Ed25519 -> ML-DSA
- Phase 4: X25519 -> ML-KEM

### Bounded Counters (Stingray)

Each silo holds a local budget slice: `slice(i) = balance * (f+1) / (2f+1)`. Debits locally without coordination until exhaustion. The executor checks `fee <= remaining` before execution (fail-fast) and debits atomically upon commit. Even f Byzantine silos cannot overspend the agent's true balance. Checked arithmetic throughout -- overflow produces an error, never wraps.

## 15. Comparison

| Property | Pyana | UCAN | Cap'n Proto | Mina | Midnight | seL4 | Cosmos IBC |
|----------|-------|------|-------------|------|----------|------|------------|
| Primary use | Agent auth + runtime | Decentralized auth | RPC framework | General L1 | Privacy DeFi | Kernel security | Cross-chain msg |
| Proof system | BabyBear STARK | None | None | Kimchi (Plonk) | Plonk | Formal verification | None |
| Privacy | Full ZK presentation | Transparent chains | None | Succinct (not private) | Shielded txns | N/A | Transparent |
| Capability model | Object-cap + Datalog + CDT | UCAN delegation | E-style + 3-party intro | Account perms | UTXO-based | CDT (kernel) | ICS-20 channels |
| Offline verify | Yes (proof + root) | Yes (no privacy) | No (live vat) | Yes | Partial | N/A | No (relayer) |
| PQ-ready | External: yes | No | No | No | No | N/A | No |
| Consensus | Federated BFT (3-64) | None (P2P) | None | Ouroboros | Ouroboros variant | Single machine | Tendermint |
| State model | Proof-carrying chains | Token chains | Live objects | Global ledger | Global ledger | Kernel memory | Per-chain ledger |
| Promise pipelining | Yes (EventualRef) | No | Yes | No | No | No | No |
| Revocation | CDT + epochs + channels | Token expiry | Vat GC | N/A | N/A | CDT (instant) | N/A |

## 16. Current Status

### What Works Today

- Real STARK proofs with real Poseidon2 constraints over BabyBear4 (124-bit security). No vacuous proofs.
- Full token-to-proof-to-turn-execution pipeline with pipeline execution and topological ordering
- 3-node federation with Morpheus BFT consensus and BLS12-381 threshold signatures
- Browser extension wallet with intent matching, local Datalog evaluation, STARK fulfillment
- TCP wire protocol with STARK verification on receive
- Sealer/unsealer with X25519-ChaCha20Poly1305 for offline capability transfer
- Promise pipelining with EventualRef resolution and three-party introduction
- Note spending proofs with nullifier-based double-spend prevention
- 20+ end-to-end demo scenarios covering delegation, revocation, multi-party turns, intents, pipelines
- Live federation infrastructure on GitHub Actions (3 nodes + intent service, staggered scheduled workflows)

### In Progress

- Recursive proof composition: Plonky3 recursive verifier works for pairs; arbitrary-N chaining uses sequential composition. Full heterogeneous AIR composition not yet operational.
- IVC state-transition proofs produce hash-chain binding (not real STARKs) -- the recursive path exists for fold proofs specifically
- Gossip is one-hop; multi-hop Plumtree forwarding is implemented but not wired between federation nodes
- Dual Merkle systems (BLAKE3 fast / Poseidon2 ZK) not yet unified end-to-end

### Designed but Unimplemented

- RevocationChannel (opt-in synchrony primitive) -- fully specified, not coded
- Post-quantum migration for classical components (waiting on NIST standardization)
- Full constant-size recursive composition of heterogeneous AIRs in a single proof
- Multi-hop authenticated gossip delivery with bounded delivery guarantees
- SP1/EVM settlement via the `chain/` workspace (excluded from main build)

## 17. Crate Table

27 workspace members, ~125k LOC Rust, ~1500 tests:

| Crate | LOC | Purpose |
|-------|-----|---------|
| `cell` | 5.9k | Isolated objects with c-lists, notes, programs, nullifier sets, state visibility |
| `turn` | 12.2k | Atomic transaction executor: call forests, journal rollback, two-phase fee, conservation, pipeline execution |
| `coord` | 4.3k | Multi-silo coordination: causal DAG, 2PC atomic commit, Stingray bounded counters |
| `circuit` | 20.0k | STARK prover/verifier, all 7 AIRs, IVC, Plonky3 recursive verification, proof composition |
| `commit` | 3.3k | 4-ary Merkle trees (BLAKE3 + Poseidon2), fold deltas, symbol table |
| `trace` | 3.5k | Datalog evaluator with derivation trace extraction and verification |
| `token` | 5.6k | AuthToken trait: Macaroon (HMAC-SHA256) + Biscuit (Ed25519+Datalog), datalog_verify |
| `tokenizer` | 1.4k | X25519-ChaCha20Poly1305 seal/unseal daemon |
| `macaroon` | 1.9k | HMAC-chain bearer tokens with constant-time verification |
| `secrets` | 0.8k | OS keychain + AES-256-GCM encrypted file store, atomic writes |
| `types` | 1.2k | Canonical types: CellId, Ed25519 (64-byte sigs), AttestedRoot, causal DAG |
| `federation` | 5.1k | Ed25519 consensus nodes, epoch reconfiguration, revocation trees |
| `morpheus` | 4.8k | Adaptive BFT consensus (Lewis-Pye & Shapiro), view-change, block finalization |
| `hints` | 3.7k | BLS12-381 threshold signatures via KZG polynomial commitments + SNARK |
| `bridge` | 4.4k | Connects token pipeline to circuit: presentation builder, mode dispatch |
| `wire` | 4.6k | TCP wire protocol, postcard framing, federation bridge, multi-node demo |
| `net` | 3.2k | Quinn QUIC transport, Plumtree gossip, topic-based dissemination |
| `node` | 1.6k | Federation node daemon: consensus participant, localhost HTTP/WS API |
| `relay` | 1.0k | Lightweight QUIC relay: attested root distribution, peer connection broker |
| `intent` | 3.9k | Distributed intent engine: gossip broadcast, local Datalog matching, commit-reveal, STARK fulfillment |
| `store` | 3.2k | redb persistence, note commitment tree, nullifier set |
| `audit` | 2.4k | Usage logging, consistency proofs, budget enforcement |
| `sdk` | 4.8k | Agent SDK: wallet, runtime, verification modes, HD key derivation |
| `wasm` | 0.9k | Browser WASM bindings (12 exported functions) |
| `demo` | 2.7k | CLI demos and key generation |
| `demo-agent` | 14.5k | End-to-end scenarios: full token-to-STARK-to-turn-execution pipeline, 20+ scenarios |
| `tests` | 3.5k | Integration tests across crate boundaries |

Plus: `chain/` (standalone workspace for SP1/EVM settlement), `extension/` (browser extension), `site/` (demo pages + discovery.json).

---

License: MIT OR Apache-2.0
