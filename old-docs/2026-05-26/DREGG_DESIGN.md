# `dregg`: Architectural Overview

## The Fabric

One DAG, many groups, emergent membership.

The blocklace is a content-addressed DAG where every block references its causal predecessors. There are no fixed federations -- reference groups form when nodes repeatedly acknowledge each other's blocks. Finality emerges from supermajority acknowledgment within a group. Any node can participate in multiple groups simultaneously.

The ordering service (what we used to call "federation") stores only nullifiers and attested roots. Agents carry their own state as proof chains. Exit at any time -- stop submitting nullifiers, take your chain, join another group or operate standalone.

## Cells and Turns

Cells are isolated objects. Each holds a capability list (c-list), balance, nonce, and optional programs defining valid state transitions. Cells are confined: they can only reference capabilities in their c-list.

Turns are atomic transactions over one or more cells. A call forest (tree of actions) executes depth-first. If any action fails, all effects roll back via journal replay. The executor enforces conservation: sum of balance changes + fee = 0. Promise pipelining via EventualRef eliminates round-trip latency.

## Proofs: The Effect VM

The Effect VM is a 24-effect instruction set where each turn's effects are proven in a single STARK:

Transfer, SetField, GrantCapability, NoteSpend, NoteCreate, CreateObligation, FulfillObligation, Custom (program dispatch), SlashObligation, Seal, Unseal, MakeSovereign, CreateCellFromFactory, ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff, AllocateQueue, EnqueueMessage, DequeueMessage, and more.

One trace row per effect. BabyBear field + FRI (Plonky3). ~38 KiB proofs, sub-second generation, post-quantum secure. IVC compresses receipt chains to constant size.

## CapTP

Capability Transport Protocol carries unforgeable references across the fabric:

- **Sessions**: Track import/export state between peers. Swiss numbers as bearer secrets.
- **Handoff**: Cryptographically signed certificates for three-party introduction.
- **Distributed GC**: Reference counting across groups. Drop propagation.
- **Store-and-forward**: X25519-encrypted messages for partition-tolerant delivery.

## Storage

Programmable queues are Merkle queues with attached DSL programs proven in-circuit. Every enqueue/dequeue operation satisfies the program's constraints or produces an invalid proof.

Relay operators provide bonded storage with erasure coding. Inboxes accumulate messages for offline recipients. Content-addressing (BLAKE3) guarantees integrity; availability is probabilistically verified via erasure sampling.

DFA-governed routing compiles path patterns into prefix-trie state machines. Constitutional governance (threshold voting) controls route amendments.

## Intent Solving

Agents broadcast needs as intents (public). Wallets evaluate privately using local Datalog (never leaves the device). Fulfillment is a STARK proof that leaks nothing about the satisfier.

Ring trades: multi-party cycles where A needs what B has, B needs what C has, C needs what A has. Settled atomically without a coordinator via commit-reveal + STARK fulfillment proofs.

IT-PIR (2-server) provides pull-based private discovery for agents who want to query the intent pool without revealing which intents interest them.

## Bridges

- **Mina**: Level 2 proof-carrying. STARK proofs wrapped in Kimchi/Pickles for recursive constant-size verification on Mina.
- **EVM**: SP1 sovereign cells. `dregg` STARKs wrapped in Groth16 for on-chain verification (~200k gas). VK governance for upgrade safety. Deposit/withdraw cycle.
- **Midnight**: DSL compiles to ZKIR v3 natively. Attestation bridge to Cardano. Same constraints, different settlement venue.

## Trust Model

**11 Guarantees:**
Capability confinement, turn atomicity, non-forgeable references, offline verification, proof-carrying state, monotonic attenuation, nullifier-based double-spend prevention, handoff integrity, forward secrecy, conservation, causal ordering.

**7 Assumptions:**
Honest supermajority (for ordering only), partial synchrony, collision-resistant hashing, discrete log (classical crypto path), correct local execution, bounded staleness (delegation), relay liveness (availability).

The key insight: the ordering service is NOT a state container. It orders nullifiers and attests roots. Everything else is locally verifiable from proofs alone.
