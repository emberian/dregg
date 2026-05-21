# Pyana: Technical Design

## 1. What is Pyana

Pyana is a distributed object-capability runtime where isolated objects (cells) communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. The authorization structure IS the computational structure. Cells hold unforgeable references to each other, messages are atomic state transitions with journal rollback, and the network is a sealed capability marketplace with privacy-preserving discovery.

The system implements E-style distributed object semantics (promise pipelining, three-party introduction, sealer/unsealer), Mina-style execution (cells as zkApp accounts, turns as ZkappCommands, call forests), seL4-style capability derivation (recast as a proof structure for asynchronous distributed systems), and proof-carrying state (receipt chains as the primary state representation, with federation reduced to an ordering service). Agents own their own state, can exit any federation carrying their full history, and verify each other offline using only STARK proofs and attested Merkle roots.

## 2. Core Insight

**Capability attenuation IS incrementally verifiable computation.** Every time a capability is delegated with restrictions (narrowed to fewer services, shorter time windows, reduced budget), that attenuation step is a fold over a committed fact set -- removing facts, never adding them. Each fold produces a strictly smaller successor state. This monotonic narrowing forms a chain of state transitions that IVC was designed to prove. The prover demonstrates "I hold a valid attenuation chain from a federation-registered issuer, ending at a capability set that satisfies your request." The verifier checks a single STARK proof without seeing any intermediate states, delegation chain, or other capabilities.

## 3. Architecture

```
+-------------------------------------------------------------------------+
|                    Browser Extension (wallet)                             |
|  Progressive disclosure UX · SLIP-10 key derivation · auto-lock          |
|  Per-method origin permissions · encrypted secrets at rest               |
+-------------------------------------------------------------------------+
|                    WASM Playground (pyana-wasm)                           |
|  43 wasm_bindgen exports · full system simulation in browser             |
|  Turns, cells, capabilities, federation, intents, conditional turns      |
+-------------------------------------------------------------------------+
|                    SDK Layer (pyana-sdk)                                  |
|  AgentWallet · AgentRuntime · SiloClient · HD wallet (BIP39)            |
|  Private intent discovery via 2-server IT-PIR                            |
+-------------------------------------------------------------------------+
|                    Intent Engine (pyana-intent)                           |
|  Gossip broadcast · local Datalog matching · commit-reveal · STARK proof |
|  IT-PIR for private discovery · epoch-scoped stake nullifiers            |
+-------------------------------------------------------------------------+
|                    Node / Network Layer                                   |
|  pyana-node (federation daemon, HTTP API, MCP server, gossip sync)      |
|  pyana-net (Quinn QUIC, Plumtree gossip, topic-based dissemination)     |
|  wire (TCP postcard framing, STARK verification on receive)             |
+-------------------------------------------------------------------------+
|                    Federation Layer                                       |
|  federation (Ed25519 consensus, state roots in blocks, light client)    |
|  morpheus (adaptive BFT, Lewis-Pye & Shapiro, 2-QC finality)           |
|  hints (BLS12-381 threshold sigs, KZG + SNARK aggregate verification)   |
+-------------------------------------------------------------------------+
|                    Coordination Layer (coord)                             |
|  Causal DAG · 2PC atomic · bounded counters (Stingray budget channels)  |
+-------------------------------------------------------------------------+
|                    Execution Layer                                        |
|  cell (isolated objects, c-lists, notes, programs, revocation channels) |
|  turn (TurnExecutor, call forests, journal rollback, two-phase fee)     |
|  Encrypted turns (threshold decryption for federation privacy)           |
|  Two-phase bridge (lock/receipt/cancel, destination_federation binding)  |
|  Three-party introduction · EventualRef · routing directives            |
|  Oblivious transfer (1-of-N from X25519 Chou-Orlandi)                  |
+-------------------------------------------------------------------------+
|                    Proof Layer (circuit)                                  |
|  Plonky3 production STARK: P3MerklePoseidon2Air (358 cols, 21 rounds)  |
|  17 specialized AIRs (see below)                                        |
|  Programmable predicates (PredicateExpr -> compiled AIR plan -> STARK)  |
|  IVC fold chains · recursive verification                                |
+-------------------------------------------------------------------------+
|                    Commitment Layer (commit)                              |
|  4-ary Merkle trees (BLAKE3 fast path / Poseidon2 ZK path)             |
|  Fold deltas (monotonic state transitions) · symbol table               |
+-------------------------------------------------------------------------+
|                    Policy Layer                                           |
|  trace (Datalog evaluator + derivation trace, deny overrides allow)     |
|  token (AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog)      |
|  tokenizer (X25519-ChaCha20Poly1305 seal/unseal)                       |
+-------------------------------------------------------------------------+
|                    Storage Layer                                          |
|  store (redb ACID, note commitment tree, nullifier set)                 |
|  secrets (OS keychain + AES-256-GCM encrypted file store, zeroize)     |
|  audit (usage log, budget enforcement, consistency proofs)              |
+-------------------------------------------------------------------------+
```

## 4. Execution Model

### Cells

A cell is the fundamental unit of isolated state. Each cell holds:

- Content-addressed identity (`CellId`, 256 bits)
- 8 generic field slots in F_p where p = 2^31 - 2^27 + 1 (BabyBear prime)
- A capability list (c-list): the set of capabilities the cell may exercise
- Permission requirements per action type (all effects mapped to permission requirements)
- Balance (computrons), nonce (replay protection)
- Optional programs (predicates, circuits) defining valid state transitions
- Private notes (anonymous cells for shielded value transfer)
- Cell hash covers ALL fields (prevents partial state manipulation)

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

### Turns

A turn is an atomic transaction over one or more cells. It contains:

- A call forest: a tree of actions, executed depth-first
- A fee in computrons covering execution cost
- A nonce (monotonically increasing per cell)
- Authorization: Ed25519 signature, ZK proof, or both
- Signing message covers balance_change + preconditions + call_forest (prevents malleability)

Turn submission is real: the node receives a turn, executes it via TurnExecutor, and produces a TurnReceipt. Gossip validation verifies turns before rebroadcasting.

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

The child acts offline using the snapshot. The executor enforces staleness: presentations where `now - refreshed_at > max_staleness` are rejected in both delegation paths. Epoch-based revocation: the parent bumps the epoch, invalidating all outstanding snapshots until children refresh.

### Two-Phase Bridge (Cross-Federation Value Transfer)

Notes are transferred between federations via a lock/receipt/cancel protocol:

1. **BridgeLock**: Notes are locked (not burned) with a `destination_federation` binding. The lock is proven in a STARK that commits `destination_federation` as a public input, preventing cross-federation replay.
2. **BridgeReceipt**: Once the destination federation finalizes the credit, it emits a receipt. The receipt is presented to the source federation to complete the bridge (unlock/burn the note).
3. **BridgeCancel**: After a timeout, if no receipt arrives, the lock is cancelled and value is returned to the sender.

### Encrypted Turns (Federation Privacy)

The `turn/src/encrypted.rs` module (336 LOC) implements encrypted turn submission for transaction privacy. Turns are encrypted before broadcast; validators perform threshold decryption to execute. This is prototyped but not yet integrated into the production consensus path.

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

### Oblivious Transfer

1-of-N oblivious transfer built from ceil(log2(N)) instances of Chou-Orlandi 1-of-2 OT over X25519. Used for private capability selection in multi-party protocols where the receiver should learn exactly one of N options without revealing which.

### Breadstuff Tokens (Bearer Authorization)

Capabilities are encoded as Datalog fact sets within bearer tokens. Two token backends:

- **Macaroon**: HMAC-SHA256 chain. Each caveat attenuates the fact set. Constant-time verification. Unknown caveats fail-closed.
- **Biscuit**: Ed25519 signature + embedded Datalog policy. Decentralized verification without sharing the root key. Deny overrides allow in Datalog evaluation.

## 6. Proof System

### Production Backend: Plonky3

Plonky3 is the production proof backend. The `P3MerklePoseidon2Air` uses width-16 Poseidon2 with 8 external + 13 internal rounds (21 total), producing a 358-column trace (5 control + 352 auxiliary round states + 1 root). Round constants are derived via the Grain LFSR, matching the proven parameters from `p3-baby-bear`. This is a real STARK with real algebraic constraints.

All proofs use BabyBear4 (degree-4 extension field, |F_{p^4}| ~ 2^124, providing 124-bit challenge security). FRI with 80 queries and blowup factor 4 gives 160-bit soundness; the system bottleneck is the ~124-bit challenge security from BabyBear4, comfortably exceeding NIST PQ Level 1. Proofs are generated in sub-second time on Apple M-series.

The custom `stark.rs` implementation (FRI from scratch) has been demoted to `circuit/examples/fri_from_scratch.rs` as a pedagogical reference.

### AIR Circuits (17 Specialized)

| AIR | File | Width | Purpose |
|-----|------|-------|---------|
| P3MerklePoseidon2 | `plonky3_prover.rs` | 358 | Production Merkle membership, full Poseidon2 inlined |
| BlindedMerkle | `poseidon2_air.rs` | 8 | Ring membership for issuer anonymity |
| Poseidon2 Permutation | `poseidon2_air.rs` | 6/8 | Proves y = Poseidon2(x), degree-7 constraints |
| Merkle Membership | `merkle_air.rs` | varies | 4-ary tree membership with position validity |
| Note Spending | `note_spending_air.rs` | 12 | Spending key + commitment + nullifier generation |
| Multi-Step Derivation | `multi_step_air.rs` | 178 | N valid Datalog rule applications -> ALLOW |
| Derivation | `derivation_air.rs` | 173 | Single-step Datalog proof with LessThan |
| Fold Chain | `fold_air.rs` | 12 | Monotonic fact removal, old->new root |
| NonRevocation | `non_revocation_air.rs` | varies | Sorted-set non-membership, adjacency verified |
| Predicate | `predicate_air.rs` | 36 | Range/set proof leaf predicate |
| Compound Predicate | `compound_predicate_air.rs` | varies | AND/OR/NOT composition over predicates |
| Temporal Predicate | `temporal_predicate_air.rs` | varies | Time-bounded validity windows |
| Relational Predicate | `relational_predicate_air.rs` | 38 | Cross-fact relational constraints |
| Committed Threshold | `committed_threshold.rs` | 38 | Threshold proofs with committed values |
| Arithmetic | `arithmetic_predicate_air.rs` | varies | Arithmetic constraints over field elements |
| Accumulator | `accumulator_air.rs` | 32 | Polynomial accumulator for O(1) non-revocation |
| Block Transition | `block_transition_air.rs` | 6 | Per-block state transition STARK |
| Turn Validity | `turn_validity_air.rs` | varies | Turn authorization proof |
| Native Signature | `native_signature_air.rs` | 5-6 | WOTS+ signature verification in AIR |
| QC | `qc_air.rs` | 8 | Quorum certificate proof |
| IVC Accumulation | `ivc.rs` | 7 | N-fold chain with root continuity |
| Recursive Verifier | `plonky3_recursion.rs` | varies | STARK verification encoded as AIR |

### Programmable Predicates

`PredicateExpr` provides a programmable predicate compilation pipeline:

```rust
enum PredicateExpr {
    Range { field, min, max },
    Set { field, values },
    And(Vec<PredicateExpr>),
    Or(Vec<PredicateExpr>),
    Not(Box<PredicateExpr>),
    Temporal { not_before, not_after },
    Relational { left_field, op, right_field },
    Arithmetic { left, op, right, result },
    CommittedThreshold { field, threshold, commitment },
}
```

A `PredicateProgram` compiles a `PredicateExpr` tree into a plan that selects appropriate AIRs, generates witness data, and produces a composed STARK proof. The bridge crate exposes this via `BridgePredicateProof`.

### Unified Action Binding

`compute_action_binding(action, resource)` produces a single commitment used consistently by prover, wire protocol, and executor. This ensures the proof, the wire message, and the execution all reference the same action-resource pair.

### Body Fact Membership Composition

The full authorization proof composes:

```
Derivation Proof (N rule steps -> ALLOW)
+ Body Membership Proofs (each body fact in tree under R_0)
+ Fold Chain Proof (R_issuer -> R_0 via attenuation)
+ Issuer Ring Membership (BlindedMerklePoseidon2StarkAir)
```

Binding via shared public inputs: derivation's state root = fold chain's final root; fold chain's initial root = issuer's committed capability root; issuer membership uses blinded leaf for anonymity within federation.

### IVC (State Transition Proofs)

Receipt chains (TurnReceipts with pre/post state hashes) are compressed via IVC into constant-size proofs. A verifier needs only: the IVC proof, current state commitment, and nullifier non-membership proof. The IVC accumulation AIR (7 columns) proves a sequence of N valid fold steps with root continuity and hash chain binding.

### Proof Backends

| Backend | Field | Proof Size | PQ? | Status |
|---------|-------|-----------|-----|--------|
| BabyBear STARK + Plonky3 | F_{2^31-2^27+1} + FRI | ~38 KiB | Yes | **Production** |
| BabyBear STARK (custom) | Same | ~24 KiB | Yes | Pedagogical (`examples/fri_from_scratch.rs`) |
| Binius | GF(2) tower + Groestl-256 | ~1-4 KiB | Yes | Research (optional dep) |
| Halo2 | BN254/Pasta + KZG | ~1-5 KiB | No | Designed |
| Nova | Pasta cycle (Pallas/Vesta) | ~10 KiB | No | Designed |

## 7. Privacy Model

### Anonymous Credential Properties (Achieved)

Pyana's privacy system provides properties comparable to Idemix/BBS+ anonymous credential systems:

1. **Issuer anonymity within federation** (Phase 1): `BlindedMerklePoseidon2StarkAir` proves the issuer is a valid federation member without revealing which one. Ring membership via blinded Merkle leaf.

2. **Unlinkable multi-show** (Phase 2): `presentation_tag = Poseidon2(final_root, presentation_randomness)`. Fresh per presentation, unlinkable across shows. `initial_root` and `final_root` REMOVED from public inputs -- they are now private witness only.

3. **Committed selective disclosure** (Phase 3): `revealed_facts_commitment` is a STARK public input. The prover chooses which facts to reveal; the proof cryptographically guarantees binding between revealed facts and the derivation trace.

4. **STARK-proven fold chain / validated IVC** (Phase 4): Receipt chains compressed via IVC accumulation AIR with root continuity verification.

5. **Predicate proofs** (Phase 5): Range, compound, temporal, relational, committed threshold, arithmetic predicates -- all compiled from PredicateExpr into composed STARK proofs.

6. **Federation privacy** (Phase 6 -- prototyped): Encrypted turns with threshold decryption. Turn content hidden from non-validators. Conflict set analysis. 336 LOC prototype in `turn/src/encrypted.rs`.

### IT-PIR for Private Intent Discovery

2-server information-theoretic PIR (`intent/src/pir.rs`, `sdk/src/discovery.rs`). The client generates additive secret shares as query vectors; each server computes a dot product with its database share; the client XORs responses to recover the target row. The servers learn nothing about which intent was queried.

### Oblivious Transfer

Chou-Orlandi 1-of-2 OT from X25519 Diffie-Hellman, extended to 1-of-N via binary decomposition (`cell/src/oblivious_transfer.rs`). Enables private selection in multi-party capability transfer.

### Public Inputs (Current State)

A fully private, unlinkable presentation proof exposes only:

```
PresentationPublicInputs {
    federation_root: BabyBear,          // which federation (public, shared)
    request_predicate: BabyBear,        // what is being authorized
    presentation_tag: BabyBear,         // blinded, unlinkable per-show tag
    revealed_facts_commitment: BabyBear, // zero if fully private
    revocation_set_root: BabyBear,      // proves non-revocation
}
```

Removed from public/wire: `initial_root`, `final_root`, `chain_length`. These are private witness.

### Three Verification Modes

| Mode | Verifier Learns | Latency | Proof Size |
|------|----------------|---------|-----------|
| **Trusted** | Full cleartext token + Datalog trace | ~8 us | 0 |
| **Selective Disclosure** | Chosen facts + conclusion | ~200 ms | ~45 KB |
| **Fully Private** | One bit (allow/deny) | ~500 ms | ~80 KB |

All three modes work offline. The same Datalog rules yield the same answer; what changes is how much the verifier learns.

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

Intent submission requires a Poseidon2 Merkle proof demonstrating the submitter has a valid note commitment in the note tree (proving economic stake without revealing balance or identity). Epoch-scoped stake nullifiers (K=5 per note per epoch) prevent a single note from proving unlimited identities.

### Privacy Properties

The gossip network sees intents (public needs) but never capabilities (private holdings). The requester learns only that someone can satisfy their need. The satisfier reveals only that they can satisfy it. Limitation: the push model means satisfiers must be online and subscribed to the gossip topic. IT-PIR provides a pull-based private discovery alternative for agents who want to query the intent pool without revealing which intents they are interested in.

## 9. Federation

### Simplified BFT Consensus (Hardened)

Federation consensus uses a simplified BFT protocol with Ed25519 signatures. The implementation is hardened:

- **Vote signatures verified**: Individual Ed25519 vote signatures are checked against registered voter public keys. Legacy mode (empty `config.members`) no longer bypasses verification.
- **Proposals signed**: Each proposal carries the proposer's Ed25519 signature, proving authority.
- **Pacemaker/view-change**: 30-second proposal timeout with signed view-change messages. View advances when n-f view-change votes collected.
- **State roots in blocks**: Every finalized block commits to `pre_state_root`, `post_state_root`, `note_tree_root`, and `nullifier_set_root`. Nodes detect divergence immediately after finalization.

### Morpheus Adaptive BFT

Full DAG-based adaptive consensus (Lewis-Pye & Shapiro) with 2-QC finality. Implemented in `morpheus/` (5,396 LOC) with proper pacemaker, view changes, and block finalization. Wired into the devnet via `--morpheus` flag but the simplified consensus is the more tested path.

### BLS12-381 Threshold Signatures

A quorum certificate is a single aggregate BLS12-381 threshold signature via real KZG polynomial commitments + SNARK proof for aggregate verification. Verification cost is constant regardless of committee size.

### Proof-Carrying QC

The `qc_air.rs` (8-column AIR) and `native_signature_air.rs` (WOTS+ signatures, XMSS key trees) enable post-quantum quorum certificate verification inside STARKs.

### LightClientProof

External verifiers can validate federation state without running a full node:

```
LightClientProof { block_hash, height, state_root, qc }
```

Produced automatically on each finalization. Enables SPV-style verification of attested roots.

### Epoch Reconfiguration

Federation membership changes occur at epoch boundaries. Each epoch carries a new committee set and updated threshold parameters. DelegatedRefs track the epoch at which they were issued. Quorum of current members must approve reconfiguration.

### Per-Block State Transition STARKs

The `block_transition_air.rs` (6-column AIR) encodes the state transition function within a STARK, enabling lightweight verification that a block correctly transitions from pre to post state.

### Net/Gossip Hookup

Consensus messages flow over the QUIC gossip layer. The `node/src/federation_sync.rs` module initializes a GossipNetwork, joins canonical topics (turns, revocations, intents, roots), and bridges gossip events to local node state.

### Checkpoint-Based Pruning

Nodes can prune historical state beyond finalized checkpoints while retaining provability via the IVC chain. Bootstrap from checkpoint + proof rather than replaying from genesis.

### RevocationChannel

For applications requiring near-instant revocation: a `RevocationChannel` is a circuit breaker between revoker and subjects. Subjects voluntarily subscribe and check channel state (Active/Tripped) before exercising gated capabilities. Trip propagates via federation attestation gossip within one consensus round. Degrades gracefully offline (bounded staleness).

### Federation as Ordering Service

The federation is NOT a state container. It orders nullifiers and attests to note tree roots. Agents carry their own state as proof chains. This enables trivial federation exit: stop submitting nullifiers, take your proof chain, join another ordering service or operate standalone.

## 10. Economic Model

### Fee Distribution

Fees collected from turns are distributed:

- **50% to block proposer** (incentivizes running validators)
- **30% to treasury** (funds public goods, governance-controlled)
- **20% burned** (deflationary pressure)

### Anti-Griefing

- **Conditional deposit**: `deposit = 500 + 10 * blocks_until_deadline`. Prevents conditional turn spam by making long-horizon conditions expensive.
- **Epoch-scoped stake nullifiers**: K=5 per note per epoch. A single note cannot prove unlimited identities across intent pools within one epoch.
- **ProofObligation bonds**: Locked note value slashed on timeout.

### Bounded Counters (Stingray)

Each silo holds a local budget slice: `slice(i) = balance * (f+1) / (2f+1)`. Debits locally without coordination until exhaustion. The executor checks `fee <= remaining` before execution (fail-fast) and debits atomically upon commit. Even f Byzantine silos cannot overspend the agent's true balance. Checked arithmetic throughout -- overflow produces an error, never wraps.

### Intent Fulfillment Payments

Intent fulfillment triggers automatic ConditionalTurn payment from requester to satisfier upon verified proof submission.

## 11. Coordination

### Async Resolution

PendingTurnRegistry with cascading resolution and broken promise propagation. When a conditional turn's dependency fails, the failure propagates to all downstream dependents.

### Cross-Federation EventualRef

References that resolve across federation boundaries via the two-phase bridge protocol.

### Two-Phase Conditional Note Bridge

Lock -> receipt -> finalize OR timeout -> cancel. Full destination_federation binding prevents replay.

### Intent Marketplace

Intents declare predicate requirements; fulfillment generates a STARK proof and triggers payment. The marketplace is decentralized (gossip-based) with commit-reveal frontrunning protection.

### Honest Pipeline Semantics

TurnBatch/OutputRef -- turns declare exactly which outputs they produce and which inputs they consume. No overclaiming. E-style promise semantics.

## 12. Proof-Carrying State

### Receipt Chains

Every committed turn produces a `TurnReceipt` with pre/post state hashes, effects hash, and computron cost. Receipts chain: `receipt[n].post_state_hash == receipt[n+1].pre_state_hash`. The chain IS the state proof -- anyone can verify from genesis without contacting a federation.

### Executor Signatures

Each receipt carries the executor's Ed25519 signature attesting to valid execution (preconditions checked, programs satisfied, conservation enforced). Signatures use `verify_strict` (no malleability).

### IVC Compression

The IVC layer compresses an arbitrary-length receipt chain into a constant-size proof. A verifier needs: (1) the IvcProof (proves chain validity from genesis), (2) current state commitment, (3) nullifier non-membership proof.

### Federation Exit

An agent leaves by stopping nullifier submission. Their proof chain is portable -- it proves state validity from genesis without referencing federation-specific data. The agent can join another ordering service or operate standalone.

### Dual Merkle (BLAKE3 Fast + Poseidon2 ZK)

The commitment layer maintains parallel Merkle trees: BLAKE3 for fast operational hashing, Poseidon2 for in-circuit ZK verification. These are not yet unified -- currently the BLAKE3 Merkle proofs cannot be directly verified inside a STARK. Unification is a known priority.

## 13. Networking

### Quinn QUIC (pyana-net)

All inter-node communication uses QUIC via Quinn with multiplexed streams and 0-RTT resumption. The pyana-net crate handles peer connection brokering and attested root distribution directly within the node.

### Plumtree Gossip

Topic-based hybrid push dissemination: eager push (degree 3) for spanning-tree delivery, lazy push (IHave notifications) for redundancy, periodic Bloom filter anti-entropy. Four gossip topics: turns, revocations, intents, attested roots.

Gossip validation: incoming turns are verified and executed before rebroadcasting. Revocations are verified (signature + non-membership proof). Attested roots are verified against the QC.

### Wire Protocol (TCP)

Postcard-framed TCP for direct silo-to-silo communication. Messages carry STARK proofs verified on receive. Three variants: Presentation (authorization proof), Revocation (non-membership proof), TurnSubmission.

### Node HTTP/WS API

`pyana-node` exposes a localhost HTTP/WebSocket API for local clients. Features:
- Turn submission (executed via TurnExecutor, produces receipts)
- State query, intent posting, federation status
- CORS middleware, rate limiting, body size limits
- Graceful shutdown (SIGINT)
- Passphrase persisted + node identity loaded from `node.key`

### MCP Server (AI Agent Interface)

`pyana-node mcp` exposes 15+ tools over JSON-RPC 2.0 (stdio transport) for AI assistant interaction:

`pyana_get_status`, `pyana_create_agent`, `pyana_authorize`, `pyana_submit_turn`, `pyana_grant_capability`, `pyana_revoke_capability`, `pyana_post_intent`, `pyana_fulfill_intent`, `pyana_delegate`, `pyana_check_capabilities`, `pyana_read_cell`, `pyana_get_receipt_chain`, `pyana_seal_data`, `pyana_unseal_data`, `pyana_bridge_note`.

### Browser Extension

Injects `window.pyana` into every page. Security model:
- Progressive disclosure UX (privacy picker popup for mode selection)
- Secrets always encrypted at rest (Web Crypto AES-GCM)
- Deterministic key derivation without WASM (SLIP-10 via HMAC-SHA512)
- `authorize` requires explicit user consent (popup confirmation)
- Per-method, time-limited origin permissions
- Auto-lock timeout (5 minutes)
- Recovery phrase backup flow

## 14. Tooling

### Docker Compose Devnet

4-node federation devnet with a single command:

```sh
cd docker && docker compose up
```

Nodes communicate over internal network, expose HTTP APIs on ports 8420-8423. Includes Morpheus consensus, pruning, and faucet endpoint on node-0.

### Chain Explorer

Web-based explorer (`site/explorer/`) with block viewer, transaction detail, and federation status pages. Communicates with node HTTP API.

### WASM Playground

Interactive browser playground (`site/playground/`) with 43 wasm_bindgen exports. Full system simulation: create cells, submit turns, mint capabilities, post intents, bridge notes, generate proofs -- all running client-side.

### Genesis Tooling

Key generation and federation configuration for bootstrapping new networks. Node identity (Ed25519) generated and persisted as `node.key`.

### AWS Graviton Deployment

Production deployment target: ARM64 (Graviton) with systemd service management, Caddy reverse proxy, and ZeroSSL certificates. See `docs/infrastructure.md`.

## 15. Storage

- **redb**: ACID crash-safe persistence for cell state, note commitment trees, and nullifier sets
- **Encrypted keychain**: OS keychain integration (via `keyring` crate) + AES-256-GCM encrypted file store for Ed25519 identity keys and sealed secrets. All secret material uses `zeroize` on drop.
- **Note trees**: 4-ary Poseidon2 Merkle tree of note commitments, maintained by the federation
- **Nullifier sets**: Append-only set with ordered leaves enabling non-membership proofs (adjacency verified for soundness)

## 16. SDK

- **AgentWallet**: Token management, attenuation, presentation (all three modes), proof generation, receipt chain maintenance. Wallet keys zeroized on drop.
- **AgentRuntime**: Turn construction, pipeline submission, effect handling, intent broadcasting
- **HD Wallet (BIP39)**: Hierarchical deterministic key derivation for stable agent identities across restarts
- **Verification API**: `wallet.authorize(&token, &request, mode)` returns mode-appropriate `AuthorizationPresentation`
- **SiloClient**: Federation connection, state sync, nullifier submission
- **Private Discovery**: IT-PIR client for querying intent pools without revealing interest

## 17. Security Model

### Trust Boundaries

Everything that crosses a trust boundary is post-quantum secure (STARK proofs, Poseidon2/BLAKE3 Merkle commitments, HMAC chains). Classical cryptography (Ed25519, BLS12-381, X25519) exists only between parties that already trust each other within a federation.

### Security Hardening (Comprehensive)

1. Turn executor verifies Ed25519 signatures via `verify_authorization` with `verify_strict` (no signature malleability)
2. Turn executor verifies ZK proofs via `ProofVerifier` trait
3. Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`
4. Wire protocol uses 64-byte signatures (via pyana-types)
5. Integer overflow in excess tracking replaced with checked arithmetic
6. `CreateCell` rejects non-zero balance (prevents minting from nothing)
7. QC forgery bypass (aggregate_qc short-circuit) removed
8. Body fact membership proven via Poseidon2 Merkle STARKs (not just asserted)
9. Signing message covers balance_change + preconditions + call_forest (prevents malleability/downgrade)
10. Domain separation on all signature contexts (STARK, IVC, wallet)
11. Wallet key zeroization complete (sdk, secrets, tokenizer, node, hints)
12. Unknown caveats fail-closed (token, bridge, trace -- 3 enforcement sites)
13. Deny overrides allow in Datalog policy evaluation
14. Non-membership proofs sound (left/right neighbor adjacency verified)
15. Staleness enforced in executor for both delegation paths
16. All effects mapped to permission requirements
17. Federation-bound + nonce-bound signatures (no cross-context replay)
18. Polynomial accumulator for O(1) non-revocation (alongside sorted-Merkle as canonical database)

### Post-Quantum Roadmap

- Phase 1 (current): STARK path is PQ today. WOTS+/XMSS signatures in `native_signature_air.rs`.
- Phase 2: BLS12-381 -> lattice threshold signatures (pending NIST 2026/2027)
- Phase 3: Ed25519 -> ML-DSA
- Phase 4: X25519 -> ML-KEM

## 18. Current Status (Honest)

### What Works Today

- Real STARK proofs with real Poseidon2 constraints (Plonky3: 358 columns, 21 rounds inlined algebraically). No vacuous proofs. 513 tests in `circuit/` alone.
- Full privacy pipeline: ring membership, unlinkable multi-show, committed selective disclosure, predicate proofs (range, compound, temporal, relational, committed threshold, arithmetic)
- Programmable predicate compilation: PredicateExpr -> composed AIR plan -> STARK proof
- Full token-to-proof-to-turn-execution pipeline with pipeline execution and topological ordering
- Turn submission with real execution (TurnExecutor produces receipts, gossip validates before relay)
- Federation with state roots in blocks, vote signature verification, signed proposals, pacemaker/view-change, LightClientProof
- Federation gossip hookup: consensus messages over QUIC gossip (4 topics)
- Two-phase bridge with destination_federation STARK binding
- IT-PIR for private intent discovery (2-server additive protocol)
- Oblivious transfer (Chou-Orlandi 1-of-N from X25519)
- RevocationChannel implemented (opt-in instant revocation)
- Fee distribution (50/30/20), conditional deposit anti-griefing, epoch-scoped stake nullifiers
- Browser extension with progressive disclosure UX, SLIP-10 keys, encrypted secrets, per-method origin permissions, auto-lock
- WASM playground with 43 exports (full system simulation in browser)
- MCP server with 15+ tools for AI agent interaction
- 4-node Docker devnet (one command)
- Chain explorer (web UI)
- TCP wire protocol with STARK verification on receive
- Sealer/unsealer with X25519-ChaCha20Poly1305 for offline capability transfer
- Promise pipelining with EventualRef resolution and three-party introduction
- Note spending proofs with nullifier-based double-spend prevention
- Unified action binding used by prover/wire/executor
- verify_strict everywhere, domain separation on all signatures
- Wallet key zeroization, unknown caveats fail-closed, deny overrides allow
- 37 end-to-end demo scenarios covering full pipeline
- BLS12-381 threshold signatures via KZG + SNARK
- Per-block state transition AIR
- Proof-carrying QC (WOTS+/XMSS in AIR)
- Polynomial accumulator for O(1) non-revocation

### In Progress

- Recursive proof composition: Plonky3 recursive verifier works for pairs; arbitrary-N chaining uses sequential composition. Full heterogeneous AIR composition (derivation + fold + membership in one recursive proof) not yet operational.
- Dual Merkle systems (BLAKE3 fast / Poseidon2 ZK) not yet unified end-to-end
- Encrypted turns (federation privacy): prototyped (336 LOC) but not integrated into production consensus
- Morpheus (full DAG-based BFT) proven sound but simplified consensus is the production path
- Multi-hop Plumtree forwarding: implemented in net, wired for gossip, not yet proven at scale

### Designed but Unimplemented

- Post-quantum migration for classical components (waiting on NIST standardization)
- Full constant-size recursive composition of heterogeneous AIRs in a single proof
- Federation transaction privacy (full encrypted execution, not just encrypted submission)
- SP1/EVM settlement via the `chain/` workspace (excluded from main build)
- Cross-verifier unlinkability guarantees (Phase 6 completion)

## 19. Crate Table

26 workspace members, ~184k LOC Rust, 2,141 tests:

| Crate | LOC | Purpose |
|-------|-----|---------|
| `circuit` | 43.0k | STARK prover/verifier, 17+ AIRs, IVC, Plonky3, recursive verification, predicate programs |
| `turn` | 18.8k | TurnExecutor: call forests, journal rollback, two-phase fee, conservation, pipeline execution, conditional turns, encrypted turns |
| `demo-agent` | 18.7k | 37 end-to-end examples: delegation, revocation, multi-party, intents, pipelines, cross-fed, bridge, privacy |
| `cell` | 9.3k | Isolated objects with c-lists, notes, programs, nullifier sets, revocation channels, bridge, oblivious transfer |
| `federation` | 8.7k | Ed25519 consensus, state roots in blocks, vote verification, epoch reconfig, LightClientProof, revocation trees |
| `intent` | 6.5k | Distributed intent engine: gossip broadcast, local Datalog matching, commit-reveal, IT-PIR, epoch-scoped nullifiers |
| `bridge` | 6.3k | Connects token pipeline to circuit: presentation builder, blinded membership, predicate proofs, mode dispatch |
| `tests` | 6.2k | Integration tests: adversarial boundaries, Byzantine, soundness, fuzz, budget, commitment |
| `token` | 6.0k | AuthToken trait: Macaroon (HMAC-SHA256) + Biscuit (Ed25519+Datalog), fail-closed caveats |
| `wire` | 5.4k | TCP wire protocol, postcard framing, federation bridge, action binding |
| `morpheus` | 5.4k | Adaptive BFT consensus (Lewis-Pye & Shapiro), 2-QC finality, view-change |
| `node` | 5.1k | Federation daemon: HTTP API, MCP server (15+ tools), gossip sync, CORS, rate limiting |
| `sdk` | 5.0k | Agent SDK: wallet (zeroize), runtime, verification modes, HD key derivation, IT-PIR discovery |
| `commit` | 4.5k | 4-ary Merkle trees (BLAKE3 + Poseidon2), fold deltas, symbol table |
| `coord` | 4.4k | Multi-silo coordination: causal DAG, 2PC atomic commit, Stingray bounded counters |
| `hints` | 3.8k | BLS12-381 threshold signatures via KZG polynomial commitments + SNARK |
| `store` | 3.8k | redb persistence, note commitment tree, nullifier set |
| `net` | 3.8k | Quinn QUIC transport, Plumtree gossip, topic-based dissemination |
| `trace` | 3.7k | Datalog evaluator with derivation trace extraction, deny-overrides-allow policy |
| `wasm` | 2.8k | Browser WASM bindings (43 exports, full simulation) |
| `demo` | 2.7k | CLI demos and key generation |
| `audit` | 2.5k | Usage logging, consistency proofs, budget enforcement |
| `macaroon` | 2.0k | HMAC-chain bearer tokens with constant-time verification |
| `tokenizer` | 1.6k | X25519-ChaCha20Poly1305 seal/unseal daemon |
| `types` | 1.3k | Canonical types: CellId, Ed25519 (64-byte sigs, verify_strict), AttestedRoot, causal DAG |
| `secrets` | 1.1k | OS keychain + AES-256-GCM encrypted file store, atomic writes, zeroize |

Plus: `chain/` (standalone workspace for SP1/EVM settlement), `extension/` (browser extension, Firefox + Chrome), `site/` (explorer, playground, demo pages, discovery.json), `docker/` (4-node devnet).

## 20. Design Documents (27)

| Document | Scope |
|----------|-------|
| `docs/privacy-architecture.md` | 6-phase roadmap to anonymous credential parity |
| `docs/federation-architecture.md` | Full federation design, current/missing analysis |
| `docs/federation-privacy.md` | Encrypted turns, threshold decryption, conflict sets |
| `docs/economic-model.md` | Fee distribution, anti-griefing, sustainability |
| `docs/agent-substrate.md` | seL4-to-Pyana mapping, agent lifecycle, MCP integration |
| `docs/pq-roadmap.md` | Post-quantum migration timeline |
| `docs/proof-carrying-state.md` | Receipt chains, IVC compression, federation exit |
| `docs/verification-modes.md` | Three-mode verification analysis |
| `docs/synchrony-primitive.md` | RevocationChannel design |
| `docs/svenvs-bridge.md` | Cross-federation bridge protocol |
| `docs/programmable-predicates.md` | PredicateExpr compilation pipeline |
| `docs/private-predicates.md` | Range/set/threshold proofs without revealing values |
| `docs/private-information-retrieval.md` | 2-server IT-PIR for private discovery |
| `docs/accumulators.md` | Polynomial accumulator for O(1) non-revocation |
| `docs/recursive-composition.md` | Heterogeneous AIR composition strategy |
| `docs/recursion-strategy.md` | Recursive STARK verification approach |
| `docs/succinct-history.md` | Succinct state history via IVC |
| `docs/garbled-circuits.md` | Garbled circuit integration for MPC |
| `docs/mpcith-predicates.md` | MPC-in-the-head predicate proofs |
| `docs/mcp-integration.md` | MCP server tool design |
| `docs/infrastructure.md` | AWS Graviton deployment, Docker devnet |
| `docs/mina-model-analysis.md` | Comparison with Mina's zkApp model |
| `docs/research-binius.md` | Binius (binary field) research |
| `docs/research-nova-folding.md` | Nova/IVC folding research |
| `docs/research-recursive-stark.md` | Recursive STARK-in-STARK plan |
| `docs/private-state-research.md` | Private state transition research |
| `docs/xfed-routing.md` | Cross-federation routing |

## 21. Comparison

| Property | Pyana | UCAN | Cap'n Proto | Mina | Midnight | seL4 | Cosmos IBC |
|----------|-------|------|-------------|------|----------|------|------------|
| Primary use | Agent auth + runtime | Decentralized auth | RPC framework | General L1 | Privacy DeFi | Kernel security | Cross-chain msg |
| Proof system | BabyBear STARK (Plonky3) | None | None | Kimchi (Plonk) | Plonk | Formal verification | None |
| Privacy | Unlinkable ZK (Idemix-class) | Transparent chains | None | Succinct (not private) | Shielded txns | N/A | Transparent |
| Capability model | Object-cap + Datalog + CDT | UCAN delegation | E-style + 3-party intro | Account perms | UTXO-based | CDT (kernel) | ICS-20 channels |
| Offline verify | Yes (proof + root) | Yes (no privacy) | No (live vat) | Yes | Partial | N/A | No (relayer) |
| PQ-ready | External: yes | No | No | No | No | N/A | No |
| Consensus | Federated BFT (3-64) | None (P2P) | None | Ouroboros | Ouroboros variant | Single machine | Tendermint |
| State model | Proof-carrying chains | Token chains | Live objects | Global ledger | Global ledger | Kernel memory | Per-chain ledger |
| Promise pipelining | Yes (EventualRef) | No | Yes | No | No | No | No |
| Revocation | CDT + epochs + channels | Token expiry | Vat GC | N/A | N/A | CDT (instant) | N/A |
| Multi-show unlinkable | Yes | No | N/A | No | Yes | N/A | N/A |

---

License: MIT OR Apache-2.0
