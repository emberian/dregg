# STORAGE-REFLECTIVITY-RBG-DFA-AUDIT

**Date:** 2026-05-24. **Status:** read-only investigation. Answers the
designer's five questions about (1) the `storage/` crate primitives and
whether they're reflective into pyana userspace, (2) `rbg/` — the
workspace-excluded Robigalia-heritage exploration, (3) the DFA router,
(4) how all three relate to the 16 missing primitives in
`APPS-AS-USERSPACE-AUDIT.md`, and (5) where the factory abstraction
lives.

Cross-cuts: `APPS-AS-USERSPACE-AUDIT.md`, `apps/subscription/CLAUDIT.md`,
`storage/STORAGE-POSEIDON2-AUDIT.md`, `rbg/README.md`,
`storage/plans/storage-as-queues.md`.

---

## Q1 — Storage crate primitives and reflectivity

### 1.1 What the storage crate provides

`storage/` (`pyana-storage`, in the workspace `exclude` list because of
KZG / ark deps, but it takes a path dep on `pyana-circuit`) is a
single-crate kitchen sink of "blob-as-queue" abstractions plus their
typed Poseidon2/BLAKE3 commitment plumbing. Inventory by module:

| Module | LOC | What it provides |
|---|---:|---|
| `lib.rs` | 105 | `ContentHash([u8;32])`, `QuotaId(u64)`, `ComputronRefund`, `StorageError`. The crate-level error/identity vocabulary. |
| `commitment.rs` | 890 | **Typed dual-form commitments**: `Commitment<T>` / `Commitment4<T>` carrying a BLAKE3 form (out-of-circuit identity) and a 1- or 4-felt Poseidon2 form (in-circuit). 12 domain tags (`TAG_QUEUE_ENTRY`, `TAG_BLINDED_ITEM`, etc.). Sister to `commit/src/typed.rs`. |
| `content.rs` | 188 | Content-addressed blob store (BLAKE3 → bytes), with `splice`-shaped mutation. |
| `queue.rs` | 620 | **`MerkleQueue`**: content-addressed append-only queue. Each state has a unique Merkle root. `QueueEntry`, `DequeueProof`. WAL-backed durable mode. The base primitive everything else wraps. |
| `inbox.rs` | 588 | **`CapInbox`**: queue specialized for HandoffCertificate / SturdyRef / encrypted-payload delivery. `InboxMessage` enum, min-deposit anti-spam, backpressure. Built on `MerkleQueue`. |
| `pubsub.rs` | 531 | **`PubSubTopic`**: one publisher, multi-subscriber cursors over a shared `MerkleQueue`. Per-subscriber heads. |
| `relay.rs` | 365 | **Metered store-and-forward** — captp store-and-forward concept with TTL-based pricing on top of `MerkleQueue`. |
| `programmable.rs` | 1330 | **`ProgrammableQueue`** — a `MerkleQueue` paired with a `QueueProgram` (`QueueConstraint` enum: `SenderAuthorized`, `ContentPattern`, `MinDeposit`, `MaxSize`, `RateLimit`, `MonotonicSequence`, `TemporalGate`, `PreimageGate`, `Custom`). A `QueueFactory` (storage-local, separate from `cell::factory`) governs which programs can instantiate. **Designer's "programmable queues" commit.** |
| `blinded.rs` | 914 | **`BlindedQueue`** — commitments in, nullifiers out, no linkage. Reuses `NoteSpendingAir` against the queue's commitment tree instead of the note tree. Private-consumption proof. |
| `atomic.rs` | 460 | **`QueueTransaction`** — multi-queue atomic txn (`QueueOp::Enqueue` / `Dequeue` / `AssertRoot`). |
| `dataflow.rs` | 673 | **`Pipeline`** — queue-to-queue staged dataflow (`Source/Filter/Transform/Router/Sink/FanOut`). The "unix pipes for queues" model. |
| `dedup.rs` | 171 | `DeduplicationFilter` (used by `pubsub` for idempotent publish). |
| `erasure.rs` | 265 | Erasure-coding chunks + reconstruction for availability sampling. |
| `multi_asset.rs` | 404 | `FeePolicy` / `ExchangeRate` / `FeePayment` — fee accounting in non-computron assets. |
| `namespace_mount.rs` | 466 | **`StorageMount`** — mount-point binding a path in the governed namespace to a storage primitive (`StorageMountKind::{Inbox, PubSub, WorkQueue, Bulletin}`) with fee policy + capacity. |
| `operator.rs` | 738 | **`RelayOperator`** — bonded relay (computron bond, slashable on `DeliveryDispute::DisputeOutcome::Slash`). Hosts `CapInbox`es; pays GC fees, refunds expired-message deposits. |
| `metering.rs` | 169 | Computron metering + per-op cost tables. |
| `quota.rs` | 213 | `SpaceBank` — byte-cap + computron quota enforcement. |
| `sharding.rs` | 347 | Shard-set commitments + lookup. |
| `wal.rs` | 536 | Append-only write-ahead log used by `MerkleQueue::with_wal`. |
| `poly_queue.rs` | 1456 | KZG-backed polynomial queue (feature-gated, `kzg`). |
| `tests.rs` | 1216 | In-crate tests. |

Cross-cutting: every authoritative commitment in storage carries a
dual-form (BLAKE3 + Poseidon2) per `commitment.rs`. There is NO BLAKE3
inside a STARK by design (`DESIGN-commitment-framework.md` §2.2).

### 1.2 API surface pyana-core consumes — and via what

Two **separate** reflectivity surfaces exist:

**(A) The `Effect` enum (turn-level / circuit-level reflectivity).**
`turn/src/action.rs:636-689` declares the six **queue effects** that
are first-class in pyana's effect-VM:

- `Effect::QueueAllocate { capacity, program_vk: Option<[u8;32]> }`
- `Effect::QueueEnqueue { queue: CellId, message_hash, deposit }`
- `Effect::QueueDequeue { queue: CellId }`
- `Effect::QueueResize { queue, new_capacity }`
- `Effect::QueueAtomicTx { operations: Vec<QueueTxOp> }`
- `Effect::QueuePipelineStep { pipeline_id, source, sinks }`

These appear in the executor at `turn/src/executor.rs:7128-7544` (the
hot paths) and `:1922-2010` (the `simulate` paths), in the cost table
at `:7905-7910`, and project to AIR selectors in
`circuit/src/effect_vm.rs` alongside `CreateCellFromFactory` and the
core CapTP effects. SDK wrappers exist in `sdk/src/wallet.rs`:

- `AgentWallet::allocate_queue` at `:5513-5563`
- `AgentWallet::enqueue_message` at `:5579-5640`
- `AgentWallet::dequeue` at `:5649` (`Effect::QueueDequeue`)
- `AgentWallet::queue_atomic_tx` at `:5715` (`Effect::QueueAtomicTx`)
- (no SDK wrapper for `QueueResize` or `QueuePipelineStep`)

The executor implementation **does not import `pyana-storage`**. The
queue state lives in a regular cell's `state.fields[0..3]`
(`fields[0]` = capacity, `fields[1]` = current length, `fields[2]` =
owner cell id, `fields[3]` = program VK hash) — see `executor.rs:
7167-7175`. The `pyana-storage::queue::MerkleQueue` data structure is
*not* what the executor manipulates; the on-chain queue is its own
field-encoded form. This is the **first major reflectivity gap**: the
ledger's queue is a single cell with four felts of state; the storage
crate's `MerkleQueue` has a content-addressed root, WAL durability,
DequeueProofs, capacity-bound entries with per-message size, etc. The
two are semantically siblings, not the same object.

**(B) The HTTP / `app-framework` surface (operator-level reflectivity).**
`app-framework/src/{inbox_endpoint,queue_endpoint,blinded_endpoint}.rs`
wraps the storage primitives in axum routers:

- `InboxEndpoint` (`app-framework/src/inbox_endpoint.rs:113`) wraps an
  `Arc<Mutex<CapInbox>>` with HTTP `POST /send`, `GET /next`, `GET /status`.
- `QueueEndpoint` wraps a `ProgrammableQueue`.
- `BlindedEndpoint` wraps a `BlindedQueue`.

These are *operator-level* objects: instantiated by an HTTP server
process (`apps/identity/`, `apps/gallery/`, `apps/amm/`,
`apps/subscription/` all use them — see grep result). They run in the
relay node's own memory, accept HTTP traffic, and the messages
themselves don't go through turns. The `sender_hex` is request-body
claimed (subscription audit §P0-5, `apps/subscription/CLAUDIT.md`
line "POST /inbox/subscribers/send").

### 1.3 Is storage "reflective" into pyana core?

**Partial. Here's the breakdown of what's reflected vs. what isn't:**

| Storage primitive | Reflected as `Effect`? | Reflected in SDK? | Reflected as on-chain state? | Caveat / cell-program access? |
|---|---|---|---|---|
| `MerkleQueue` (raw) | yes — but **degraded** (queue is 4 felts in a cell, no Merkle root on-chain) | yes (alloc / enqueue / dequeue / atomic tx) | partial: cell holds capacity, length, owner, program-vk hash — **not the queue root** | no |
| `ProgrammableQueue` (program-validated) | partial — `QueueAllocate { program_vk: Some(...) }` records the VK but the executor does NOT run the validation program — the VK is metadata. The constraint vocabulary (`SenderAuthorized`, `RateLimit`, ...) is **storage-local Rust enums**, never interpreted by the executor. | only via the alloc effect's `program_vk` arg | only program VK in `fields[3]` | no |
| `CapInbox` | no | no — no `Effect::InboxRegister` or `Effect::InboxSend` | only as the same generic queue effect | no |
| `PubSubTopic` | no | no | no | no |
| `BlindedQueue` | no — even though it reuses `NoteSpendingAir`, no `Effect::BlindedConsume` exists | no | no | no |
| `QueueTransaction` (atomic multi-queue) | yes — `Effect::QueueAtomicTx` | yes — `queue_atomic_tx` | partial (operates on the field-encoded queues) | no |
| `Pipeline` (dataflow) | yes — `Effect::QueuePipelineStep` | no | partial (pipeline_id passed through, but routing not enforced in-circuit) | no |
| Relay store-and-forward (`RelayOperator`) | no | no | no — the relay's bond and slashing are in the storage-crate's own `RelayOperator` struct, not in the ledger | no |
| `StorageMount` (namespace mount) | no — see Q1.5 (governed-namespace) | no | no | no |
| Dual-form commitments (`Commitment<T>`) | **partially** — they're what the Poseidon2/AIR side reads, but pyana's core `commit/src/typed.rs` is the canonical home and the storage crate duplicates the pattern (it's a leaf, not a base) | no | no | no |
| `BulletinBoard` / `WorkQueue` (namespace kinds) | no | no | no — kinds exist as enum variants in `StorageMountKind` but the executor never sees them | no |
| Erasure coding / availability sampling | no | no | no | no |

**The reflectivity verdict: only the "generic Merkle queue" is in the
effect surface, and even then, lossily.** The richer programmable
queues, capability inboxes, pub-sub topics, blinded queues, relay
operators, namespace mounts — all are *out-of-band Rust objects*
running in operator processes and reachable only via HTTP/cap-TP, not
via turns. The constraint vocabulary in
`storage::programmable::QueueConstraint` is a **closed Rust enum** —
it doesn't live in `cell::program::StateConstraint`, so cell programs
can't reason about it.

Practical implication: when an app wants to constrain its inbox
("only members can enqueue"), it ends up reaching into
`app-framework` HTTP layer (no auth — see G1 gap) instead of
expressing the constraint as a turn-level cell program. The
subscription app is the case-in-point (subscription CLAUDIT §P0-5).

### 1.4 Partial reflectivity: which primitives are reflected, which aren't

Concretely:

**Reflected (in `Effect` and AIR):**
- Generic queue allocation/enqueue/dequeue/resize (lossy: state is 4
  felts, not a Merkle root)
- Atomic multi-queue transactions
- Pipeline step dispatch (pipeline_id passed as identifier; routing
  enforcement is off-circuit)

**Reflected only as HTTP/app-framework surface (operator-trusted):**
- `CapInbox` send/receive
- `ProgrammableQueue` constraint validation
- `BlindedQueue` blind-consume (off-circuit, then ProofBlob ferried)
- `PubSubTopic`
- `BulletinBoard` (only as an enum variant in `StorageMountKind`)

**Not reflected at all (Rust-only):**
- `RelayOperator` bonding / slashing — sits in `storage::operator`
  and is never crossed into `Effect` or AIR
- `StorageMount` — exists as a config object; never `Effect::Mount`
- Erasure coding — purely off-line availability
- Dual-form commitments per se — they're plumbing, not user-visible
- `QueueProgram` / `QueueConstraint` constraint vocabulary

### 1.5 Cross-reference: `apps/subscription/` as a storage-layer example

Confirmed. Per `apps/subscription/CLAUDIT.md`:

- Subscription's `delivery.rs:141` uses `CapInbox::receive_at(msg, 0,
  item.epoch)` — **the only "real Pyana primitive use" in the app
  beyond signed-delegation** (CLAUDIT §"Verdict").
- The inbox is shared across all subscribers (capacity 1024,
  `min_deposit: 0`, `enqueued_at: 0`).
- The inbox is **not** behind a turn — it's behind the
  framework's HTTP `POST /inbox/subscribers/send`, with
  client-asserted `sender_hex`.
- No `Effect::QueueEnqueue` for this inbox. No on-chain root. No
  audit trail.

Subscription demonstrates **two things**:

1. The storage crate's primitive (`CapInbox`) is the right *shape*
   for "store-and-forward subscriber delivery." Using it is correct.
2. But the storage crate is **operator-trusted, not turn-mediated**:
   it lives one layer below the effect-VM, so any app that uses it
   inherits operator trust. The subscription app then layers
   ChaCha20-Poly1305 + ed25519-signed-delegation on top to get
   confidentiality and one piece of authenticated authority — but the
   inbox itself is open-mic.

Subscription is the **first example of why storage-level primitives
need to be reflected into the effect-VM surface, not just exposed as
operator-side libraries.** If `Effect::InboxSend { inbox_cell,
sender_pk, payload_commitment }` existed and the cell-program could
predicate on `sender_pk ∈ subscribers_set_root`, the whole CLAUDIT
verdict ("BROKEN") would collapse to a small set of localized fixes.

---

## Q2 — RBG (Robigalia)

### 2.1 What it is

`rbg/` = **Robigalia-inspired exploration**. From its README:

> Exploring how Robigalia's capability-secure OS designs map to
> pyana's distributed runtime.

The crate name `pyana-rbg` and description "Robigalia-inspired
VFS/storage layer for pyana's capability-secure distributed runtime"
make it explicit. It is **not** "Recursive Block Generator" nor
"Random Beacon Generation"; **RBG = Robigalia**, the
seL4-on-Rust capability-secure microkernel research from
~2014-2017. The README maps Robigalia concepts to pyana 1:1:

| Robigalia | Pyana mapping (per `rbg/README.md`) |
|---|---|
| Transaction Protocol (Submit/Execute/Retrieve/Reap) | Turn (submit/execute/receipt/advance) |
| Promise Pipelining (dep bitmask, Consuming state) | CapTP `pipeline.rs` |
| Concurrent Executor (indexed slots) | Effect VM (14 effects per turn, parallel-provable) |
| Nameless Writes (content-addressed storage) | Note commitments |
| Capability-Secure VFS (Volume / Blob / Directory) | Cell model (c-list as directory) |
| **DFA Message Routing** | gossip topic matching / intent `MatchSpec` |
| SturdyRefs | `pyana://` URIs |
| Automata packet classification | Could enhance wire protocol routing |

### 2.2 Design intent and inspiration

Inspiration is explicit, named, and grounded in three sources:

1. **Robigalia's Transaction Protocol** — the seL4-style async-RPC
   protocol with a formal liveness proof. Pyana's turn protocol is
   isomorphic; the "Consuming" state ≈ "Tentative" finality, the
   generation counter ≈ nonce + block height binding.

2. **Robigalia's VFS** (`rbg/src/vfs.rs`) — `Volume` (resource quota
   / computron budget), `Blob` (content-addressed = note commitment),
   `Directory` (c-list + factory provenance). `splice()` → Effect VM
   atomic turn; `swap()` → `SetField` with nonce precondition.

3. **Nameless Writes** (Zhang et al., cited in the README as
   `~/Desktop/zhang2-7-12.pdf`) — clients write data, storage picks
   the location, returns the address. Pyana notes ARE this: commit a
   value, get back the commitment hash as its address.

### 2.3 State of the crate

**Working prototype + design exploration. Three modules, ~4,500 LOC, no in-tree consumers.**

- `rbg/src/vfs.rs` (1517 LOC) — `Volume`, `Blob`, `Directory`,
  `VfsEffect` (mirrors `Effect` from `turn`), full `Vfs` aggregate,
  capability permission bitmask, blob splice, directory swap. The
  module's top comment says: *"This maps Robigalia's VFS design into
  pyana's distributed runtime."* — but it uses **stub types**
  (`CellId(pub [u8; 32])`, `NoteCommitment([u8;32])`, `Permissions(u32)`)
  rather than importing `pyana-cell` / `pyana-types`. So it's a
  parallel implementation that *demonstrates* the userspace VFS
  pattern by re-implementing pyana primitives.

- `rbg/src/routing.rs` (1346 LOC) — **complete DFA implementation**
  with NFA → DFA subset construction, NFA combinators (concat /
  union / star), bit/byte/range/word patterns, `PacketSource` +
  `Classifier` (capability-secure source splitting), `FilterTree`
  (revocable composition tree), `AirTraceRow` + `generate_air_trace`
  + `verify_air_trace` for in-circuit proofs, `TopicFilter` for
  gossip. **This is materially more capable than the one in
  `wire/src/dfa_router.rs`** (which is a flat trie-to-DFA compiler
  with only URL-style patterns).

- `rbg/src/directory.rs` (1707 LOC) — **Scoped Intent Directories**:
  directories-as-capabilities, with `DirectoryCell`, `Listing`,
  `ScopedIntent`, `ScopedIntentPool`, `MetaDirectory` (yellow
  pages), `DirectoryFactory`, `TopicSubscriptionManager`,
  `AudienceBoundClaim`. Problem statement: the intent engine
  (`intent/`) broadcasts to ALL peers; this scopes it.

### 2.4 Why it's excluded from the workspace

Documented in `Cargo.toml:10-12`:

```
# rbg/ is an experimental Robigalia-inspired VFS sketch (edition 2021,
# no in-tree consumers) — kept excluded until either integrated or removed.
exclude = ["chain", "chain/program", "rbg"]
```

Three reasons stack:

1. **Edition 2021** vs. workspace's edition 2024.
2. **Stub types** — `rbg::vfs::CellId` etc. are local, not
   `pyana-types::CellId`. Re-integration requires plumbing real
   pyana types through.
3. **No in-tree consumers.** Nobody in `apps/` or the core crates
   imports `pyana-rbg`. The exclusion is bookkeeping: it builds
   independently when invoked but isn't part of `cargo test`.

### 2.5 What re-integration would look like

Three integration paths, in order of increasing leverage:

**Path A — Promote `rbg::routing` into `wire/`.**
The DFA in `wire/src/dfa_router.rs` is a simple flat-trie compiler
with `RouteTarget::{Cell, Handler, Federation, Drop}`. The DFA in
`rbg/src/routing.rs` is the full theoretical apparatus: NFA →
subset-construction DFA, regex combinators, capability-secure source
splitting via `PacketSource` / `FilterTree`, AIR trace generation
already factored. Re-integration: swap `wire/src/dfa_router.rs`'s
internal compiler for `rbg::routing::Pattern → Nfa → Dfa`, add
`PacketSource`-style source splitting on top of the existing
`Router`. The `GovernedRouter` (committee-signed table swap) and
`compile_routes` URL-pattern surface stay; the engine gets more
expressive. Effort: ~1-2 weeks. Unlocks: gossip-topic filtering
(currently flat broadcast in `intent/src/gossip.rs`), wire-level
packet classification, in-circuit DFA proofs (the AIR primitives
already exist).

**Path B — Promote `rbg::directory` into a new `pyana-directory`
crate, federate it with `intent/` and `captp/`.**
The "scoped intent directories" pattern is the **answer** to several
of the 16 missing primitives (see Q4 below). Concretely:
`ScopedIntentPool` = MatchSpec scoped to a directory's membership,
`DirectoryCell` = a `CommittedMap` with cell-state-bound semantics,
`MetaDirectory` = the yellow-pages / nameservice pattern. This is
the largest payoff. Effort: 3-4 weeks. Unlocks: nameservice
(pure-userspace), intent scoping (vs. flat global pool), discovery
without information leakage.

**Path C — Promote `rbg::vfs` into `pyana-storage` or its own
crate, replace the field-encoded queue with the proper VFS
abstractions.**
The on-chain queue today is "four felts in a cell". The
`storage::MerkleQueue` is the real shape. The `rbg::vfs::Blob` /
`Volume` / `Directory` triple is the *user-facing* shape that
explains why the storage primitive is what it is. Re-integration
would replace `storage`'s ad-hoc inbox/queue/pubsub variants with
the unified Blob/Volume/Directory + interpretation overlays. Effort:
large (storage refactor + AIR rebinding). Unlocks: a coherent
userspace storage model.

### 2.6 What rbg offers that pyana-core lacks

The single highest-value thing rbg provides that core doesn't: a
**formal compositional model for userspace** built on three small
operators (Volume, Blob, Directory) plus capability-secure source
splitting. The current pyana-core has *cells*, *capabilities*,
*notes*, and a *swiss table* — all good — but no unified
"namespace" or "container" abstraction beyond ad-hoc per-app cell
hierarchies. The rbg directory-as-capability model is exactly what
the apps audit (`APPS-AS-USERSPACE-AUDIT.md` §7.1 #10
`CommittedMap<K,V>`) is reaching for.

---

## Q3 — DFA router

### 3.1 Locating it

Two implementations exist:

| Crate / file | Status | Role |
|---|---|---|
| `wire/src/dfa_router.rs` | live; in `pyana-wire` | Production. URL-pattern route table compiled to flat-trie DFA. Governance-controlled atomic swap (`GovernedRouter`). |
| `rbg/src/routing.rs` | workspace-excluded | Full NFA → DFA theoretical implementation. AIR-trace generation. Capability-secure source splitting. |

### 3.2 What it is and what it routes

**`pyana-wire::dfa_router`** (`wire/src/dfa_router.rs:1-700`):

- A **deterministic finite automaton** ingesting raw message bytes
  or URL-style paths and dispatching to a `RouteTarget`:
  - `RouteTarget::Cell(CellId)` — route to a specific cell
  - `RouteTarget::Handler(String)` — route to a named handler
    (e.g., `"intent_pool"`, `"admin"`)
  - `RouteTarget::Federation(GroupId)` — forward to another group
  - `RouteTarget::Drop` — silently discard (revocation, blocked
    topic)
- The transition table is **flat** (`transitions[state*256 + byte]`),
  cache-friendly, with state 0 as the dead/reject state.
- The table's `commitment: [u8;32]` is `BLAKE3` of the serialized
  transition table — for binding into governance constitutions.

**Key surface:**

- `compile_routes(&[(pattern, target)]) -> RouteTable` — compile
  URL patterns (literal segments + wildcard suffix `/*` + exact
  match) into a route table (`:158+`).
- `Router::new(table)` — live dispatch engine; `classify(message)`
  / `classify_path(path)` (`:88-136`).
- `GovernedRouter` (`:322+`) — wraps `Router` with atomic table
  swap, requiring a `GovernanceProof` signature. Used for
  constitution-controlled route updates.
- `dispatch_path` helper (used by tests / preflight).

### 3.3 How it's wired into the system today

**Mostly vestigial.** Grep results for usage (outside `dfa_router.rs`
itself and inline tests):

- `teasting/tests/dfa_routing.rs` — full integration test of route
  compile + classify + governed update.
- `teasting/tests/fault_byzantine.rs:344-395` — Byzantine route
  table tests.
- `teasting/src/{mesh_sim,router_sim}.rs` — `SimRouter` wraps
  `GovernedRouter` for mesh-simulation tests.
- `preflight/src/checks/routing.rs` — preflight check.
- `apps/governed-namespace/src/main.rs:1139-1177` — **the one real
  production-shaped consumer**: a "namespace_dfa_routing" test that
  routes `/namespace/public/*` and `/namespace/members/*` paths to
  different access-control regimes.

**Not wired into:**

- `wire/src/server.rs` — wire-level dispatch does NOT run the
  DFA router. Messages are parsed by postcard, dispatched by
  `Message` enum match.
- `intent/src/gossip.rs` — intent gossip is flat broadcast.
- CapTP — sturdy refs route by swiss number, not via the DFA.
- The Effect VM — there's a DFA-lookup *constraint* in
  `circuit/src/dsl/circuit.rs:1711` and `tests/src/dfa_circuit.rs`
  shows DFA-in-AIR (proving correct DFA execution), but the
  production router doesn't generate STARK proofs of its routing
  decisions.

**Verdict: vestigial outside `apps/governed-namespace/` and tests.**
The DFA router is built, governance-bound, AIR-compatible — and
unconsumed.

### 3.4 Cross-reference with CapTP / wire

CapTP and the wire layer use point-to-point dispatch keyed on
sturdy-number (swiss table lookup) and message-type (postcard
enum match). Neither benefits *today* from the DFA's
pattern-classification strength. The latent value is in **gossip
topic filtering** (intent pool, blocklace gossip) where the DFA's
constant-space, linear-time, atomically-swappable filter table is
the right shape — but that integration hasn't happened.

---

## Q4 — Apps-to-core promotion candidates

Cross-referencing the 16 missing primitives in
`APPS-AS-USERSPACE-AUDIT.md` §7.1 against storage / rbg / DFA.

### 4.1 The 16, re-listed for reference

| # | Tier | Primitive | Source crate(s) it lives in today |
|---|---|---|---|
| 1 | T1 | Transition-aware `CellProgram` constraints | needs `cell/src/program.rs` extension |
| 2 | T1 | `EscrowCondition::PredicateSatisfied` impl (G18) | `turn/src/executor.rs` |
| 3 | T1 | `AuthenticatedRequest<C>` axum extractor (G1) | `app-framework/src/auth.rs` |
| 4 | T1 | Federation clock (G16) | new `app-framework/src/clock.rs` + `node/src/clock.rs` |
| 5 | T1 | Generic claim-slot / nullifier-set primitive (`Effect::ClaimSlot`) | new in `turn/src/action.rs` |
| 6 | T2 | Paired-escrow / atomic-swap primitive | new in `app-framework::swap` or as effect |
| 7 | T2 | Promote `bridge::present` to `pyana-credentials` | refactor `bridge/src/present.rs` |
| 8 | T2 | Scheduled-effect primitive (`Effect::FireAt`) | new `node/src/scheduler.rs` |
| 9 | T2 | Cell-program `ExpressionEquals` (math gadget registry) | new in `cell::program` + DSL |
| 10 | T2 | `CommittedMap<K, V>` storage primitive | new in `pyana-storage` |
| 11 | T3 | Subscription / streaming caps | `captp` + `Caveat::EventFilter` |
| 12 | T3 | `BlindedQueue` payload return channel | `storage/src/blinded.rs` (extend `Consumed`) |
| 13 | T3 | Trusted-attester registry (G26) | new `pyana-attesters` crate |
| 14 | T3 | Coordinator-key threshold-decrypt primitive | `coord/` + `Effect::CoordinatorDecrypt` |
| 15 | T3 | Blob primitive (`Effect::BindBlob`) | new in `pyana-storage` |
| 16 | T3 | Window-bounded caveats (`Caveat::CommitWindow` etc.) | `turn/src/cap_caveats.rs` |

### 4.2 Unlocked by promoting storage primitives to userspace

Storage already contains real implementations of several of these,
just one-layer-below the effect VM. Promotion targets:

- **#10 `CommittedMap<K, V>`** — *direct hit.* The plumbing exists
  in `storage::commitment::Commitment4` (dual-form Merkle roots) and
  in `storage::queue::MerkleQueue` (content-addressed root with
  membership/dequeue proofs). Promotion: lift the
  `MerkleQueue::root` + `DequeueProof` shape into a generic
  `CommittedMap<K, V>` and reflect it as effects
  (`Effect::CommittedMapInsert / Update / Delete` with AIR
  bindings). The Poseidon2 4-felt form is already AIR-ready.
- **#12 `BlindedQueue` payload return channel** — *direct hit, small.*
  `storage::blinded::Consumed` already has `nullifier`; just add
  `payload: Vec<u8>` to its `Consume` return per the audit's
  recommendation.
- **#15 Blob primitive (`Effect::BindBlob`)** — *direct hit.*
  `storage::content::ContentStore` provides exactly this shape
  (BLAKE3 → bytes, splice mutation). Promotion: declare
  `Effect::BindBlob { cell, hash, uri }` and have the executor
  call into the relay layer (`storage::operator::RelayOperator`)
  to assert availability.
- **#5 Generic claim-slot / nullifier-set primitive
  (`Effect::ClaimSlot`)** — *unlocked indirectly.* `BlindedQueue`
  already does the nullifier-set part; what's missing is the
  generic `Effect::ClaimSlot { domain, key, proof }` and a
  per-cell `nullifier_root` in `CellState`. The audit names this
  as Tier-1.
- **#11 Subscription / streaming caps** — *unlocked indirectly.*
  `PubSubTopic` is the data shape; what's missing is the *caveat*
  to attenuate a streaming cap. The storage side has the right
  abstraction (publisher / subscribers / cursors); core needs
  `Caveat::EventFilter` and `Caveat::RateLimit` integrated with
  CapTP.

**Storage promotion targets (concrete movements):**

| What | From | To |
|---|---|---|
| `MerkleQueue::root` Merkle-rooting | `storage/src/queue.rs` | reflect into the executor's cell-state encoding so the queue's `fields[1]` becomes the **Merkle root**, not the length |
| `DequeueProof` verification | `storage/src/queue.rs:verify_dequeue_proof` | wire into `Effect::QueueDequeue` AIR row |
| `ProgrammableQueue` constraint vocabulary | `storage::programmable::QueueConstraint` | promote variants into `cell::program::StateConstraint` (transition-aware) and `turn::cap_caveats::Caveat` (window-bounded) — closes T1 #1 and T3 #16 |
| `BlindedQueue` payload return | `storage::blinded::Consumed { nullifier }` | extend to `{ nullifier, payload }` |
| `ContentStore` BLAKE3 blob store | `storage::content::ContentStore` | wire into `Effect::BindBlob` |
| `RelayOperator` bond + dispute | `storage::operator::RelayOperator` | reflect into core as a deposit/slash effect tied to cell-state, à la `Effect::CreateObligation` |
| `StorageMount` (namespace mount kinds) | `storage::namespace_mount::StorageMountKind` | reflect into the governed namespace as cell-program-validated mount records (T2 #10 sibling) |

### 4.3 Unlocked by re-integrating rbg

The rbg crate is uniquely positioned to address the *namespace /
discovery* gaps that storage doesn't cover:

- **#10 `CommittedMap<K, V>` (T2)** — *direct hit.* `rbg::directory::
  DirectoryCell` is exactly the shape: a content-addressed,
  capability-gated, versioned key-value directory. Storage gives the
  Merkle-root machinery; rbg gives the *user-facing data structure*.
- **Nameservice as pure userspace** (audit §1.3) — *direct hit.*
  `rbg::directory::DirectoryCell` + `MetaDirectory` collapses the
  nameservice's `BTreeMap<String, NameEntry>` (`apps/nameservice/
  src/registry.rs:18`) into a real cell-bound primitive.
- **#11 Subscription / streaming caps** — *partially unlocked.*
  `rbg::directory::TopicSubscriptionManager` provides the topic
  subscription bookkeeping; combined with storage's `PubSubTopic`,
  this is the streaming-cap substrate.
- **Intent scoping** (not in the 16, but a major gap noted in
  rbg's README and the intent audit) — *direct hit.* `rbg::
  directory::ScopedIntentPool` replaces the flat global intent
  pool in `intent/`.
- **Audience-bound claims** — `rbg::directory::AudienceBoundClaim`
  is sibling to the `Presented<P>` extractor in audit #7 (T2).

**RBG promotion targets:**

| What | From | To |
|---|---|---|
| `Pattern → Nfa → Dfa` regex combinators + AIR trace | `rbg::routing` | merge into `wire::dfa_router` (replacing the trie-only compiler) |
| `PacketSource` / `FilterTree` capability-secure source splitting | `rbg::routing` | promote into a new `wire::source_capability` module |
| `DirectoryCell` / `Listing` / `swap`-on-nonce | `rbg::directory` | promote into a new `pyana-directory` crate, or into `cell` as a built-in cell-program |
| `ScopedIntentPool` + `MatchPattern` | `rbg::directory` | replace the global pool in `intent/src/lib.rs` |
| `MetaDirectory` (yellow pages) | `rbg::directory` | use it as the substrate for nameservice |
| `DirectoryFactory` | `rbg::directory` | unify with `cell::factory::FactoryDescriptor` |
| `AudienceBoundClaim` | `rbg::directory` | merge with `bridge::present` for `pyana-credentials` (#7 T2) |
| `Blob` / `Volume` / `Directory` triple | `rbg::vfs` | refactor `pyana-storage` to use this triple as its top-level vocabulary (overlay protocols ride on top) |

### 4.4 Unlocked by exposing DFA routing as a userspace primitive

The DFA-routing surface is less directly load-bearing for the 16 than
storage or rbg, but it does unlock:

- **Intent matching at scale** — `MatchSpec` → DFA compilation (the
  rbg README explicitly names this). The audit's gallery (§4) and
  prediction-market (§3) both want subscription-by-pattern.
- **Gossip topic filtering** — intent scoping requires per-topic
  routing; the DFA is the right shape.
- **Capability revocation as DFA recompile** — the rbg README's
  "revocation = recompile DFA without the revoked filter" model
  maps to the revocation-tree pattern; integration would let
  per-cell capability revocation propagate through the routing
  fabric atomically.
- **Provable routing decisions** (`tests/src/dfa_circuit.rs` already
  proves DFA execution in-circuit) — the `Effect::DfaClassify` (not
  in the 16; orthogonal) would let cells reason about routing
  decisions in their own proofs.

**DFA promotion targets:**

| What | From | To |
|---|---|---|
| `rbg::routing::Pattern` regex combinators | `rbg/src/routing.rs` | `wire::dfa_router` (replacing trie-only compiler) |
| `PacketSource` source splitting | `rbg::routing` | `wire::source_capability` |
| AIR trace + verify | `rbg::routing::generate_air_trace` | `circuit::dsl::circuit` (already partially there via `tests/src/dfa_circuit.rs`) |
| `MatchSpec` → DFA compiler | (proposed) | new module bridging `intent::matcher` and `wire::dfa_router` |
| Per-topic gossip DFA | (proposed) | `intent::gossip` integration |
| Governance-bound route table (already implemented) | `wire::dfa_router::GovernedRouter` | stays; wire it into the constitution machinery |

---

## Q5 — Factories

### 5.1 What and where

Two factory concepts exist, **distinct**:

**(A) `cell::factory` — the core cell factory.**
`cell/src/factory.rs:163` `FactoryDescriptor` is "constructor
transparency" for cells: a factory is a cell-program (`CellProgram`)
that constrains what new cells it can create. The descriptor is
inspectable by anyone without running the circuit. Key types:

- `FactoryDescriptor` (`:163`):
  `{ factory_vk, child_program_vk, child_vk_strategy,
  allowed_cap_templates, field_constraints, default_mode,
  creation_budget }`
- `ChildVkStrategy` (`:22-38`): `Fixed(Option<vk>)` /
  `Derived { base_vk }` (computable child VK =
  `Poseidon2(factory_vk || param_hash)`) /
  `FromSet { approved_vks }` (Merkle membership).
- `CapTemplate` (`:297`), `CapTarget` (`:338`), `FieldConstraint`
  (`:349`) — the building blocks of allowed-grant constraints.
- `FactoryCreationParams` (`:455`) — what a creation effect sends.
- `Provenance` (`:472`) — what's recorded on the child cell.
- `FactoryRegistry` (`:630`) — federation-wide deployed factories.

**Reflection: `Effect::CreateCellFromFactory`**
(`turn/src/action.rs:625`). The AIR variant lives in
`circuit/src/effect_vm.rs:864` (selector `CREATE_CELL_FROM_FACTORY`,
aux columns for `factory_vk` and `child_vk_derived`). Executor
implementation at `turn/src/executor.rs:7100-7125`.

**(B) `storage::programmable::QueueFactory` — a storage-local factory.**
`storage/src/programmable.rs:286` is **a separate, lighter
factory** specifically for `ProgrammableQueue`. It maintains a
whitelist of permitted `QueueConstraint` kinds and limits on
constraint-count and lookup-table size. It is **not** reflected as
an effect; it lives in operator-process memory. The naming overlap
is unfortunate.

### 5.2 What factories do

The `cell::factory` factory enforces "branded constructor"
semantics:

- A factory's `factory_vk` is its identity (BLAKE3 of its
  descriptor).
- Created cells inherit the factory's `default_mode` (Hosted /
  Sovereign).
- Initial capabilities granted to children must each fit within
  some `CapTemplate` in `allowed_cap_templates`.
- Field constraints (`FieldConstraint::{Range, OneOf, Exact}`) bound
  the initial state.
- `creation_budget` (per-epoch) caps how many cells the factory
  can mint.
- `ChildVkStrategy` controls whether children all share a program
  (`Fixed`), derive theirs from creation params (`Derived` —
  enables "branded but customized" children), or pick from a set
  of approved VKs (`FromSet`).
- The child cell records `Provenance { factory_vk, proof_hash,
  height }` — anyone inspecting a cell can see which factory
  spawned it and verify the chain.

### 5.3 How factories compose with cells

- A factory is itself a cell (or a deployed program record in
  `FactoryRegistry`).
- `Effect::CreateCellFromFactory { factory_vk, owner_pubkey,
  token_id, params }` runs the factory's `validate_creation`
  (`cell/src/factory.rs:235`); on success, the executor mints a
  new cell with `Provenance::from_factory(factory_vk, ...)` in
  its metadata.
- The created cell's `program_vk` is determined by the strategy:
  fixed / derived / approved-set.
- Sub-factories: a factory can itself be created by a parent
  factory, with templates restricting what *kinds* of factories
  it can spawn. The `FactoryRegistry::record_creation` enforces
  per-factory budgets.

### 5.4 Apps that use them

`grep -rn "FactoryDescriptor\|CreateCellFromFactory"` would find
demos in `demo/`, `teasting/`, and the executor's tests. **No
production app in `apps/` uses factories today** — every audited app
either uses cells without provenance (nameservice's HashMap) or
hand-rolls deployment without going through the factory machinery.
This is **another reflectivity gap**: factories exist in core but
are unused at the user surface.

### 5.5 Cross-reference with rbg

`rbg::directory::DirectoryFactory` (`:846`) is a *parallel*
factory abstraction specifically for `DirectoryCell`. The
re-integration plan (Q2.5 Path B) would unify this with
`cell::factory::FactoryDescriptor` — the rbg directory factory
becomes just a specific `FactoryDescriptor` configuration whose
`child_vk_strategy` produces directory-program-VK children.

---

## Designer summary

**Five answers, designer-shaped:**

**1. Storage primitives — yes, but only barely reflective.**
The crate has 22 modules and ~13,000 LOC of provable, content-addressed,
quota-bounded queue / inbox / pubsub / pipeline / blinded-consumption /
relay / mount machinery. **Only the generic `MerkleQueue` is reflected
into the effect VM**, and even that is lossy: the on-chain queue is
four felts in a cell (capacity, length, owner, program VK hash), not
the Merkle root the storage crate computes. `Effect::QueueAllocate /
Enqueue / Dequeue / Resize / AtomicTx / PipelineStep` exist in
`turn/src/action.rs:636-689` and are SDK-callable in
`sdk/src/wallet.rs:5513-5715`. **Everything richer — `CapInbox`,
`ProgrammableQueue`'s constraint vocabulary, `PubSubTopic`,
`BlindedQueue`, `RelayOperator`, `StorageMount` — lives one layer
below the effect VM** and is reachable only via `app-framework`'s
HTTP wrappers. Apps that use them inherit operator trust
(unauthenticated `sender_hex` in the inbox endpoint — see
`apps/subscription/CLAUDIT.md` §P0-5). `apps/subscription/` is the
clean case study: its `delivery.rs:141` use of `CapInbox::receive_at`
is correct primitive use, but the surrounding framework gaps make the
whole app BROKEN. **The promotion targets** (Q4.2): lift
`ProgrammableQueue`'s `QueueConstraint` variants into
`cell::program::StateConstraint` (this *is* the audit's Tier-1 #1
"transition-aware constraints"); reflect `ContentStore` as
`Effect::BindBlob` (audit #15); extend
`BlindedQueue::Consumed` with payload return (audit #12); turn
`MerkleQueue::root` into the queue cell's actual `fields[1]`.

**2. RBG = Robigalia, not "Recursive Block Generator".** A 4,500-LOC
exploration mapping seL4-style capability-secure OS designs onto
pyana's distributed runtime: Volume / Blob / Directory triple, full
NFA → DFA with regex combinators and AIR-trace generation, scoped
intent directories with meta-directories and topic subscription
managers, `AudienceBoundClaim` for presented credentials. **Working
prototype state**, with one `Cargo.toml` block from being absorbed:
edition mismatch (2021 vs 2024), stub types instead of `pyana-types`
imports, and no in-tree consumers. The exclusion is explicitly
documented as "kept excluded until either integrated or removed."
**The highest-leverage re-integration is Path B (Q2.5):** the
`DirectoryCell` / `ScopedIntentPool` / `MetaDirectory` cluster is
the answer to several Tier-2 gaps in the apps audit (#10
`CommittedMap`, nameservice-as-pure-userspace, intent scoping). Path
A (DFA routing engine swap) is a 1-2 week refactor that gives wire
& gossip a real router. Path C (VFS as the unifying storage
vocabulary) is large but conceptually clarifying.

**3. DFA router — built, governance-bound, AIR-aware, almost
unconsumed.** `wire/src/dfa_router.rs` (URL-pattern → flat-trie DFA)
+ `GovernedRouter` (signed table swap) is real and tested. **Used
in production only by `apps/governed-namespace/`** (`main.rs:1139`).
Wire-level dispatch doesn't run it; intent gossip is flat broadcast;
CapTP routes by swiss number. The rbg crate has a materially more
capable DFA engine (full NFA + combinators + capability-secure
source splitting + AIR trace). Re-integration would swap the
trie-only compiler for the regex one, then wire the result into
gossip filtering, intent matching, and capability revocation.

**4. Apps-to-core promotion priorities** (Q4 summary):

| Subsystem | Top promotion targets | Audit-# unlocked |
|---|---|---|
| storage | `QueueConstraint` → `StateConstraint` (transition variants); `ContentStore` → `Effect::BindBlob`; `BlindedQueue::Consumed` + payload; queue cell `fields[1]` ← Merkle root; `RelayOperator` → on-chain deposit/slash | #1 (T1), #5 (T1), #11 (T3), #12 (T3), #15 (T3), partial #10 (T2) |
| rbg | `DirectoryCell` + `ScopedIntentPool` + `MetaDirectory` → new `pyana-directory`; `DirectoryFactory` ⊆ `cell::factory`; `AudienceBoundClaim` → `pyana-credentials` (with `bridge::present`); `Blob/Volume/Directory` → `pyana-storage` refactor | #10 (T2), #7 (T2), nameservice purity (audit §1) |
| DFA | `rbg::routing` regex engine → `wire::dfa_router`; `PacketSource` → `wire::source_capability`; `MatchSpec`→DFA → `intent::matcher`; gossip DFA → `intent::gossip` | intent scoping; revocation; partial #11 (T3) |

**The top promotion — if you do one thing — is:** lift the
`ProgrammableQueue` constraint vocabulary into
`cell::program::StateConstraint` with transition variants. This is
the audit's named Tier-1 #1 ("Transition-aware `CellProgram`
constraints"), and storage *already has working Rust implementations*
of `MinDeposit`, `MaxSize`, `RateLimit`, `MonotonicSequence`,
`TemporalGate`, `PreimageGate`, `SenderAuthorized` — they need to
move from `storage::programmable::QueueConstraint` (operator-side
Rust enum) into `cell::program::StateConstraint` (turn-side
predicate variants with `old_state` access) so cell programs can
predicate on them. Side benefit: closes most of `apps/subscription`'s
P0s (`max_per_epoch` becomes a real per-period quota).

**5. Factories — two factory concepts, both load-bearing, none used by
apps.**

- `cell::factory::FactoryDescriptor` (`cell/src/factory.rs:163`) is
  the **branded-constructor pattern**: a cell program that
  constrains what cells it spawns. Three `ChildVkStrategy` modes
  (Fixed / Derived / FromSet) cover "all children identical" /
  "computable from params" / "approved-from-set" branding.
  Reflected as `Effect::CreateCellFromFactory`
  (`turn/src/action.rs:625`) with full AIR support
  (`circuit/src/effect_vm.rs:864`). The `Provenance` record on
  each created cell + the federation-wide `FactoryRegistry`
  (`cell/src/factory.rs:630`) make factory chains inspectable.
  **No `apps/*` actually uses this** — it's perfectly built and
  perfectly unconsumed.
- `storage::programmable::QueueFactory` (`storage/src/programmable.rs:286`)
  is a **separate, storage-local factory** that whitelists queue
  programs at creation time. Unrelated to `cell::factory` except by
  name; not reflected as an effect; operator-side.
- `rbg::directory::DirectoryFactory` is a *third* factory, in the
  excluded crate, for scoping `DirectoryCell` creation. Path B
  re-integration would unify it with `cell::factory`.

**Composition with cells:** a factory IS a cell with a constraining
program. Apps would compose factories with cells by minting their
domain types (orders, intents, directory entries, queue cells)
through factory effects, getting branded `Provenance` for each. The
audit's #10 (`CommittedMap`) would naturally be created by a
factory; nameservice's per-name cells (audit §1.3) would all carry
the nameservice factory's `factory_vk`. **The gap is not the
factory machinery — it's that no app reaches for it.**

---

## File pointers (key citations)

- Storage modules: `/Users/ember/dev/breadstuffs/storage/src/*.rs`
- Storage lib: `/Users/ember/dev/breadstuffs/storage/src/lib.rs:40-60`
- Storage commitment framework: `/Users/ember/dev/breadstuffs/storage/src/commitment.rs:38-52`
- Storage plans: `/Users/ember/dev/breadstuffs/storage/plans/storage-as-queues.md`
- Storage Poseidon2 audit: `/Users/ember/dev/breadstuffs/storage/STORAGE-POSEIDON2-AUDIT.md`
- Queue effects (declaration): `/Users/ember/dev/breadstuffs/turn/src/action.rs:636-689`
- Queue effects (executor): `/Users/ember/dev/breadstuffs/turn/src/executor.rs:7100-7544`
- SDK queue wrappers: `/Users/ember/dev/breadstuffs/sdk/src/wallet.rs:5513-5715`
- App-framework storage endpoints:
  - `/Users/ember/dev/breadstuffs/app-framework/src/inbox_endpoint.rs:113`
  - `/Users/ember/dev/breadstuffs/app-framework/src/queue_endpoint.rs`
  - `/Users/ember/dev/breadstuffs/app-framework/src/blinded_endpoint.rs`
- RBG crate: `/Users/ember/dev/breadstuffs/rbg/{Cargo.toml,README.md,src/{lib,routing,directory,vfs}.rs}`
- Workspace exclusion: `/Users/ember/dev/breadstuffs/Cargo.toml:10-12`
- Wire DFA router: `/Users/ember/dev/breadstuffs/wire/src/dfa_router.rs:53-160, :322-360`
- DFA router consumer (production): `/Users/ember/dev/breadstuffs/apps/governed-namespace/src/main.rs:1139-1177`
- DFA in-circuit: `/Users/ember/dev/breadstuffs/circuit/src/dsl/circuit.rs:1711-1941`, `/Users/ember/dev/breadstuffs/tests/src/dfa_circuit.rs`
- Subscription as storage-layer case study: `/Users/ember/dev/breadstuffs/apps/subscription/CLAUDIT.md`
- Subscription `CapInbox` usage: `/Users/ember/dev/breadstuffs/apps/subscription/src/delivery.rs:141`
- Factories (core): `/Users/ember/dev/breadstuffs/cell/src/factory.rs:163-273, :297-538, :630-700`
- Factory effect: `/Users/ember/dev/breadstuffs/turn/src/action.rs:625-634`
- Factory AIR: `/Users/ember/dev/breadstuffs/circuit/src/effect_vm.rs:864-880, :4260-4267`
- Factory executor: `/Users/ember/dev/breadstuffs/turn/src/executor.rs:7100-7125`
- Apps-as-userspace audit: `/Users/ember/dev/breadstuffs/APPS-AS-USERSPACE-AUDIT.md`
