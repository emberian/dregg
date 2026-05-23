# CapTP / OCapN Integration into Pyana

## 1. What the Spritely Whitepapers Contain

The `~/src/spritely-whitepapers/` collection includes:

### spritely-core.org ("The Heart of Spritely")
The primary technical paper by Christine Lemmer-Webber, Randy Farmer, and Juliana Sims. Covers:

- **Goblins**: Distributed object programming with transactional turns, encapsulated behavior, `bcom` (become) for state transitions
- **Vat model**: Event loops containing near objects (synchronous `$`) and far objects (asynchronous `<-`), with actormaps as transactional heaps
- **CapTP**: Capability Transport Protocol providing distributed GC, promise pipelining across network boundaries, and transport-agnostic netlayers
- **OCapN**: The full Object Capability Network stack = CapTP + Netlayers + URI structure
- **Promise pipelining**: Send messages to unresolved promises; reduces round trips from `B => A => B => A => B` to `B => A => B`
- **Sealers/unsealers**: Rights amplification without cryptography (language-level public-key equivalent)
- **Unum pattern**: One conceptual object, many presences (canonical + replicated), with asymmetric authority
- **Safe serialization**: Objects self-describe persistence using only capabilities they hold ("uneval/unapply")
- **Portable encrypted storage**: Content-addressed, location-agnostic, encrypted, chunked documents

### petnames.org
Petname systems for mapping human-readable names to cryptographic identifiers. Three name types: petnames (local), edge names (from contacts), proposed names (self-claimed). Directly relevant to how users would reference capabilities across federations.

### content-addressed-descriptors-and-interfaces.org
Content Addressed Descriptors (CADs): hash a description to create a universally unique method/type identifier. Used for interface discovery across networks. Includes an IDL sketch using Preserves Schema. Uses "wards and incanters" (energetic secrets from Joule) for hidden behavior that only authorized parties can invoke.

## 2. CapTP Concepts Mapped to Pyana Equivalents

| CapTP/OCapN Concept | Pyana Equivalent | Gap/Notes |
|---|---|---|
| **Object reference** (near/far) | `CellId` | Pyana cells are the atomic unit; near = same-federation, far = cross-federation |
| **Vat** (event loop + actormap) | Federation executor within a silo | Our "vat" is the single-threaded TurnExecutor processing one turn atomically |
| **Turn** (atomic message processing) | `Turn` struct (forest of actions + effects) | Nearly identical semantically; pyana turns are already transactional |
| **`$` synchronous call** | Effects within a single turn | Effects in a turn tree are synchronous; cross-cell effects within one action forest |
| **`<-` asynchronous send** | Intent submission / cross-federation EventualRef | Intents are "fire and await"; EventualRef awaits cross-fed resolution |
| **Promise** | `EventualRef` / `PendingEntry` | EventualRef references future turn output; PendingTurnRegistry handles resolution |
| **Promise pipelining** | `Effect::PipelinedSend` | Already exists! Sends action to an eventual target resolved during pipeline execution |
| **Three-party introduction** | `Effect::Introduce` | Already exists! Emits `RoutingDirective` telling network layer a new path is valid |
| **Capability reference** | c-list entries + `BearerCapProof` | c-list = persistent; BearerCapProof = ephemeral inline delegation |
| **Facets (attenuated views)** | `EffectMask` on capabilities | Already implemented; restricts which effect kinds a delegated cap can exercise |
| **Revocation** | `RevocationChannelSet` + `Effect::RevokeCapability` | Both token-level and channel-level revocation exist |
| **Sealer/unsealer** | `Effect::CreateSealPair` / `Effect::Seal` / `Effect::Unseal` | Already exists! Language-level rights amplification |
| **Netlayer** (transport abstraction) | `wire` crate (TCP + postcard framing) | Functions as the netlayer; gossip overlay adds p2p |
| **Sturdy reference** (serializable long-lived cap) | **MISSING** | No equivalent of `ocapn://` durable refs that survive disconnection |
| **Distributed GC** | **MISSING** | No mechanism to drop remote capability references when unreachable |
| **Handoff** (transparent reference migration) | **MISSING** | Cannot transfer a live reference to a third party without original holder |
| **Content Addressed Descriptors** | Intent `sse.rs` (SSE search tokens) | Partial overlap; intents have searchable descriptors but not CAD-style hashed interfaces |
| **Petnames** | **MISSING** | No human-friendly naming layer for cross-federation references |
| **Unum pattern** (distributed presence) | Partially via blocklace sync + bridge node | Bridge nodes have multiple presences in different federations |

## 3. What's MISSING That We Should Build

### Critical (enables new capabilities)

#### 3.1 Sturdy References (`pyana://` URIs)
**What**: A serializable, long-lived capability URI that can be stored, shared out-of-band, and rehydrated into a live capability reference.

**Why**: Currently, all capability references are ephemeral (c-list entries or BearerCapProofs). If a phone goes offline, all references to it are gone. Sturdy refs let you bookmark a capability.

**Design sketch**:
```
pyana://<federation-id-base58>/<cell-id-base58>/<swiss-number>
```
The swiss number is a secret known only to the holder and the target cell. Presenting it over CapTP "enlivens" the reference into a live capability. This is exactly how Goblins' `ocapn://` URIs work.

#### 3.2 Distributed Reference Counting / GC
**What**: A protocol for peers to inform each other when they no longer hold a reference to a remote capability, allowing the holder to reclaim resources.

**Why**: Without this, every introduced capability lives forever (or until manual revocation). On resource-constrained phones, this matters enormously.

**Design sketch**: 
- Each cross-federation capability gets a refcount at the holder.
- When a federation drops all references to a remote cell, it sends a `DropRef` wire message.
- The target federation decrements its export count; when zero, the cell can revoke the routing directive.
- Acyclic first (simple); cyclic GC deferred (requires mark-and-sweep with trial deletion).

#### 3.3 Handoff Protocol (Reference Transfer Without Introducer)
**What**: C gives B a capability to something on A, without A or C needing to be online simultaneously.

**Why**: Offline-first mobile scenario. Alice shares a cap with Bob via QR code; Bob can contact the target federation directly.

**Difference from Introduce**: `Effect::Introduce` requires the introducer to be executing a turn. Handoff works via signed delegation certificates that travel out-of-band.

**Design sketch**:
- Introducer signs a `HandoffCertificate { target, recipient_pk, permissions, expires, swiss }`.
- Recipient presents this certificate to the target federation's netlayer.
- Target federation validates signature chain back to a known exporter, creates a routing entry.
- This is close to what `BearerCapProof::SignedDelegation` already does, but at the *network* layer rather than the *executor* layer.

### Important (improves the model)

#### 3.4 Cross-Federation Promise Pipelining
**What**: Send a message to an unresolved promise on a remote federation.

**Why**: Currently `PipelinedSend` only works within a local pipeline batch. True E-style pipelining would let phone A say "send this to the result of that pending turn on federation B" without waiting for B's receipt.

**Design sketch**:
- Extend `PendingTurnRegistry` to accept pipeline-able messages for unresolved cross-federation EventualRefs.
- When the receipt arrives and resolves the promise, enqueue the pipelined messages for the resolved cell.
- On broken promise: propagate failure to all pipelined messages (already partially implemented in pending.rs).

#### 3.5 Store-and-Forward Netlayer
**What**: An OCapN netlayer that works over intermittent connectivity (phone mesh, offline-first).

**Why**: The "phones meshing with cloud nodes" vision requires messages to be queued when the target is offline and delivered when connectivity resumes.

**Design sketch**:
- Extend the gossip layer to support delayed delivery queues per destination federation.
- Messages are encrypted to the destination's public key and stored on relay nodes.
- When the destination reconnects, pending messages are delivered in causal order.

### Nice-to-Have (improves UX)

#### 3.6 Petname Registry
Local petname mapping: `"Alice's phone" -> pyana://3eF.../cell-abc.../swiss`

#### 3.7 Content Addressed Descriptors for Cell Interfaces
Extend cell metadata to include a CAD-style interface descriptor (what methods/effects the cell supports), queryable over the wire.

## 4. What Integration Would Look Like

### Wire Protocol Changes

```rust
// New WireMessage variants
enum WireMessage {
    // ... existing ...
    
    // CapTP session management
    CapHello { exported_swiss: Vec<SwissEntry> },
    CapGoodbye { dropped_refs: Vec<CellId> },
    
    // Sturdy ref resolution
    EnlivenSturdyRef { uri: PyanaUri, requester_pk: [u8; 32] },
    EnlivenResponse { cell_id: CellId, routing_token: [u8; 32] },
    
    // Distributed GC
    DropRemoteRef { cell_id: CellId, federation_id: [u8; 32] },
    
    // Cross-federation promise pipelining
    PipelinedMessage { 
        eventual_ref: EventualRef, 
        action: Action,
        sender_federation: [u8; 32],
    },
    
    // Handoff certificate presentation
    PresentHandoff { certificate: HandoffCertificate },
    HandoffAccepted { routing_token: [u8; 32] },
    
    // Store-and-forward
    QueuedDelivery { 
        dest_federation: [u8; 32],
        encrypted_payload: Vec<u8>,
        causal_order: u64,
    },
}
```

### Executor Changes

```rust
// New effects
enum Effect {
    // ... existing ...
    
    /// Export a cell as a sturdy reference, returning a swiss number.
    ExportSturdyRef { cell: CellId },
    
    /// Revoke a sturdy reference (invalidate the swiss number).
    RevokeSturdyRef { swiss: [u8; 32] },
    
    /// Register an interface descriptor for a cell.
    SetInterfaceDescriptor { cell: CellId, descriptor: InterfaceCAD },
}
```

### New Module: `captp/` Crate

```
captp/
  src/
    lib.rs           -- CapTP session state machine
    session.rs       -- Per-peer session (export table, import table, promise table)
    sturdy.rs        -- SturdyRef creation/resolution/revocation
    gc.rs            -- Reference counting + drop protocol
    handoff.rs       -- Handoff certificate creation/validation
    pipeline.rs      -- Cross-federation promise pipeline registry
    uri.rs           -- pyana:// URI parsing and construction
```

### SDK Changes

For the phone/agent SDK:
- `SturdyRef::new(cell_id) -> PyanaUri` -- export a capability as a durable link
- `SturdyRef::enliven(uri) -> LiveRef` -- connect to a sturdy ref
- `LiveRef::send(action) -> EventualRef` -- send a message, get a promise
- `EventualRef::pipeline(action) -> EventualRef` -- pipeline a message to an unresolved promise
- Automatic reference counting: when a `LiveRef` is dropped, send `DropRemoteRef`

## 5. Priority Order

### Phase 1: Sturdy References (highest value, enables everything else)
- Define `pyana://` URI scheme
- Implement swiss number table in executor
- Wire message for enliven/resolve
- **Unlocks**: Offline sharing, QR code delegation, bookmark-able capabilities

### Phase 2: Distributed GC
- Export/import tables per CapTP session
- Refcount protocol in wire layer
- Drop propagation
- **Unlocks**: Resource reclamation on phones, scalable long-running federations

### Phase 3: Handoff Protocol
- HandoffCertificate struct (extends BearerCapProof to network layer)
- Wire presentation + validation
- Routing table population from certificates
- **Unlocks**: Offline delegation, mesh network sharing

### Phase 4: Cross-Federation Promise Pipelining
- Extend PendingTurnRegistry with queued pipelined messages
- Wire messages for forwarding pipelines to remote federations
- Broken-promise cascade across federation boundaries
- **Unlocks**: Latency reduction for multi-hop operations

### Phase 5: Store-and-Forward Netlayer
- Message queueing on relay nodes
- Encrypted-to-destination storage
- Causal delivery on reconnection
- **Unlocks**: True offline-first mobile operation

### Phase 6: Petnames + Interface Descriptors
- Local petname database
- CAD generation for cell interfaces
- Interface discovery protocol
- **Unlocks**: Human-friendly UX, programmatic discovery

## 6. Relationship to "Phones Meshing with Cloud Nodes"

The ultimate vision: phones form a local mesh, cloud nodes provide persistence and availability, capabilities flow freely between them.

### What CapTP integration enables for this:

**Sturdy refs** allow a phone to share a QR code containing a `pyana://` URI. The recipient scans it, their phone enlivens it (either through the mesh if the source is nearby, or via a cloud relay), and they have a live reference. No centralized directory required.

**Distributed GC** means phones don't accumulate unbounded state from old interactions. When you stop using a capability, the source learns this and can reclaim resources. Critical for resource-constrained devices.

**Handoff** means delegation works even when the original holder is offline. Alice delegates to Bob at a coffee shop (BLE mesh); Bob uses it later from home via cloud. Alice's phone doesn't need to be on.

**Store-and-forward** means the mesh is resilient to connectivity gaps. A phone can compose a multi-step operation, submit it, go offline, and the cloud nodes ensure it resolves. When the phone reconnects, it receives the results.

**Promise pipelining across networks** means a phone can say "transfer X to the result of this pending operation on that cloud node" in a single message, without waiting for the cloud's response before composing the next step. This is the difference between 4 round trips and 1.

### The architectural picture:

```
Phone A ←──mesh──→ Phone B
   │                    │
   └──cloud──→ Federation Node ←──cloud──┘
                    │
              CapTP session
                    │
              Other Federations
```

- Phones export sturdy refs to each other via mesh (BLE/WiFi-Direct)
- Cloud nodes are "always-on presences" (unum pattern) that relay and persist
- Cross-federation operations use CapTP sessions between cloud nodes
- Phones can be offline; store-and-forward ensures nothing is lost
- GC keeps state bounded on all devices

### What we already have that makes this feasible:

- `Effect::Introduce` = three-party introduction (the hardest CapTP concept)
- `BearerCapProof` = ephemeral capability delegation (handoff precursor)
- `EventualRef` = promise references with cross-federation support
- `PipelinedSend` = local promise pipelining (needs network extension)
- `RoutingDirective` = dynamic routing from introductions
- `PendingTurnRegistry` = broken-promise propagation
- Gossip overlay = p2p transport substrate (netlayer candidate)
- Bridge nodes = multi-federation presence (unum pattern)

The gap is primarily at the **session management** layer: we have the primitives but not the persistent session state that CapTP requires (export tables, swiss numbers, refcounts). Phase 1-2 close this gap; Phase 3-5 complete the mobile story.
