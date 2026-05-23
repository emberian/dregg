# Protocol Unification: Old Cross-Federation Mechanisms vs CapTP

## Executive Summary

The codebase now has two generations of cross-federation machinery. After reading all relevant source files, the overlap is significant but not total. The old mechanisms are primarily **executor-level** (turns, effects, ledger state) while CapTP is **network/session-level** (peer protocol, message delivery, offline delegation). In most cases the correct answer is LAYER (CapTP wraps old mechanisms) rather than outright removal.

---

## 1. EventualRef (turn/eventual.rs) vs PipelineRegistry (captp/pipeline.rs)

### What each does

**EventualRef / Pipeline (turn/eventual.rs):**
- Synchronous, batched execution within a single node
- `Pipeline` = a set of turns submitted together with dependency edges
- Topologically sorted and executed by `TurnExecutor` in one pass
- `EventualRef` = "output slot N of turn with hash X" (resolved during local execution)
- `Effect::PipelinedSend` = dispatch an action to a resolved eventual target
- The module explicitly says: "This is NOT async promise pipelining in the E-language sense. All execution is synchronous and local."

**PipelineRegistry (captp/pipeline.rs):**
- True E-style cross-federation promise pipelining
- Messages sent to UNRESOLVED promises on remote federations
- `PipelinedMessage` queued until promise resolves, then delivered
- `CrossFedPipelineBridge` coordinates per-peer registries with wire message exchange
- `PipelineWireMessage` protocol for cross-federation promise resolution/breakage
- Eliminates round-trips in cross-fed communication

### Overlap analysis

These are **different layers**, not duplicates:
- `EventualRef` operates WITHIN a single turn batch (synchronous, local, no network)
- `PipelineRegistry` operates BETWEEN federations (async, networked, wire protocol)

The `PendingTurnRegistry` (turn/pending.rs) is the bridge between them: it tracks turns awaiting external resolution (including remote federation receipts), which is exactly where CapTP's pipeline should connect.

### Recommendation: **Layer**

- `EventualRef` / `Pipeline` remain the local batched execution primitive
- `PipelineRegistry` wraps it for cross-federation communication
- `PendingTurnRegistry` becomes the integration point: when CapTP resolves a cross-fed promise, it feeds the result into the pending registry which cascades to local execution

**Code changes needed:**
- In `turn/src/pending.rs`: add a method `resolve_from_captp(turn_hash, captp_pipeline_result)` that converts `PipelineResultValue` into `ResolutionOutcome`
- In `wire/src/server.rs`: when handling `PipelineWireMessage::PromiseResolved`, call through to the pending turn registry
- `EventualRef::federation_id` field already exists for this purpose (it marks cross-fed refs)

---

## 2. Effect::Introduce vs HandoffCertificate (captp/handoff.rs)

### What each does

**Effect::Introduce (turn/executor.rs line 4680):**
- In-band, synchronous, requires introducer to execute a turn NOW
- Checks introducer has capabilities to both recipient and target
- Grants recipient a capability to target (with attenuation, expiry)
- Emits a `RoutingDirective` for the network layer
- All three parties (introducer, recipient, target) must be on the same federation
- The capability is live immediately

**HandoffCertificate (captp/handoff.rs):**
- Out-of-band, asynchronous, parties need NOT be online simultaneously
- Signed certificate travels via QR code, email, BLE, file
- Recipient presents certificate to TARGET federation (can be a different federation)
- Validates swiss number, introducer signature, recipient identity
- Works CROSS-FEDERATION (target_federation can differ from introducer's federation)
- Swiss number must be pre-registered at target

### Overlap analysis

These solve the SAME problem (3-party introduction) but at different layers and with different connectivity assumptions:
- `Effect::Introduce` = online, same-federation, immediate, executor-level
- `HandoffCertificate` = offline-capable, cross-federation, deferred, network-level

They are complementary, not conflicting.

### Recommendation: **Keep both**

- `Effect::Introduce` remains the fast path for same-federation introductions (no crypto overhead, immediate, atomic within a turn)
- `HandoffCertificate` handles the general case (cross-federation, offline, out-of-band)
- When an `Effect::Introduce` targets a cell on another federation, it should internally generate a `HandoffCertificate` and route it via CapTP store-and-forward

**Code changes needed:**
- Add a check in the Introduce handler: if `target` is on a remote federation (detectable via a federation registry), convert to a HandoffCertificate flow instead of local capability grant
- Add `Effect::PresentHandoff { certificate: Vec<u8> }` for the recipient to enliven a received handoff via the executor (tying network-layer handoff back into the effect system)
- The `RoutingDirective` emitted by Introduce should also record the equivalent swiss number in CapTP state for distributed GC

---

## 3. BridgeLock/BridgeFinalize (cell/note_bridge.rs) vs CapTP Sessions

### What each does

**BridgeLock/BridgeFinalize (note_bridge.rs):**
- VALUE TRANSFER (fungible notes) between federations
- Two-phase commit: lock note -> destination confirms mint -> finalize burn
- Security: STARK proofs, destination-bound nullifiers, trusted roots, Ed25519 receipts
- Operates on the NOTE layer (privacy-preserving value commitments)
- Atomic: either both sides commit or the note is returned after timeout

**CapTP Sessions (session.rs + gc.rs):**
- CAPABILITY TRANSFER between federations
- Import/export tables tracking who can access what
- Distributed GC for reference lifecycle
- No value semantics, no STARK proofs, no nullifiers
- Operates on the CAPABILITY layer (who can invoke methods on whom)

### Overlap analysis

These are **completely independent concerns**:
- Note bridge = value transfer (money/tokens between chains, ZK-proven)
- CapTP sessions = capability transfer (access rights between peers)

They share zero logic. The note bridge cares about nullifiers, Merkle trees, and STARK proofs. CapTP sessions care about import/export tables and reference counts.

However, they DO interact: a cross-federation bridge operation USES CapTP for message delivery. The `BridgeReceipt` could travel via CapTP's store-and-forward layer.

### Recommendation: **Independent** (with CapTP as transport)

- `BridgeLock/BridgeFinalize` stays exactly as-is (value transfer logic)
- CapTP provides the TRANSPORT for bridge receipts and portable proofs
- `store_forward.rs` becomes the delivery mechanism for bridge messages

**Code changes needed:**
- In the bridge executor handler: when sending a `PortableNoteProof` to a remote federation, route it via `StoreForwardClient::prepare_message` rather than requiring a live TCP connection
- The `BridgeReceipt` delivery path should use CapTP pipeline promises: lock creates a promise, finalize resolves it
- No changes to the core bridge logic itself

---

## 4. RoutingDirective (turn/routing.rs) vs RoutingTable (node/routing_table.rs) vs CapTP Sessions

### What each does

**RoutingDirective (turn/routing.rs):**
- A single data record: "sender S can now reach target T, authorized by turn X, expires at Y"
- Emitted by the executor when `Effect::Introduce` succeeds
- Pure data (45 bytes), no behavior

**RoutingTable (node/routing_table.rs):**
- The node-level table consuming routing directives
- Maps CellId -> set of (peer_address, introducer, expiry) entries
- Network-level routing: "to talk to cell X, send to peer at address Y"
- Bounded (MAX_ROUTES_PER_CELL, MAX_TOTAL_ROUTES)

**CapTP CapSession exports/imports:**
- Per-peer capability tables: "peer P has imported cells [A, B, C] from us"
- Reference-counted (GC on drop)
- Not routing information per se, but authorization information

### Overlap analysis

These are **different layers of the same operation**:
1. Executor emits `RoutingDirective` (authorization layer)
2. `RoutingTable` uses it for network-level routing (transport layer)
3. `CapSession` should also use it to populate the export table (capability layer)

Currently, step 3 is NOT happening: `RoutingDirective` populates `RoutingTable` but does NOT record an export in `ExportGcManager`. This means the distributed GC system is unaware of capabilities created via `Effect::Introduce`.

### Recommendation: **Layer** (RoutingDirective -> RoutingTable AND CapTP export)

- `RoutingDirective` remains the authority record
- `RoutingTable` remains network-level routing
- When processing a `RoutingDirective`, ALSO record an export in `ExportGcManager`
- When a `DropRef` arrives via CapTP GC, remove the corresponding `RoutingTable` entry

**Code changes needed:**
- In `node/src/routing_table.rs`: `apply_directive()` should also call `export_gc.record_export(directive.target, peer_federation_id, current_height)`
- When `ExportGcManager::process_drop()` returns `CanRevoke`: remove the route entry from `RoutingTable`
- Add a `FederationId` to `RouteEntry` so we can match GC messages to routes

---

## 5. PendingTurnRegistry (turn/pending.rs) vs PipelineRegistry (captp/pipeline.rs)

### What each does

**PendingTurnRegistry:**
- Tracks turns that cannot execute yet (awaiting receipt, condition, or height)
- Resolution conditions: `AwaitReceipt { turn_hash, federation_id }`, `AwaitCondition`, `AwaitHeight`
- Cascading resolution: when A resolves, dependents of A become ready
- Cascading breakage: when A breaks (timeout, rejected), dependents break too
- Produces `ResolutionEvent` (Resolved | ReadyToExecute | Broken)
- Operates at the TURN level (whole turns pending execution)

**PipelineRegistry (captp/pipeline.rs):**
- Tracks pipelined MESSAGES awaiting promise resolution
- Messages are fire-and-forget actions sent to unresolved remote promises
- Resolution: promise resolves to a cell, queued messages are delivered
- Breakage: promise breaks, cascading failure to result promises
- Operates at the MESSAGE level (individual method calls on promises)

### Overlap analysis

These are **the same abstraction at different granularities**:
- `PendingTurnRegistry` = coarse-grained (whole turns blocked on conditions)
- `PipelineRegistry` = fine-grained (individual messages blocked on promises)

The `PendingTurnRegistry` is ALSO used for cross-federation awaits (its `AwaitReceipt` has an optional `federation_id`). The `PipelineRegistry` also handles cross-federation message delivery.

The doc comment in `captp/pipeline.rs` even says: "`CrossFedPipelineBridge` bridges the local `PendingTurnRegistry` with per-peer pipeline registries." They are explicitly designed to work together.

### Recommendation: **Layer** (PipelineRegistry feeds PendingTurnRegistry)

- `PipelineRegistry` handles cross-federation message pipelining (network layer)
- When a pipelined message resolves and produces a `PipelineResultValue::Success`, the corresponding `PendingTurnRegistry` entry is resolved via `ResolutionOutcome::Resolved`
- `PendingTurnRegistry` remains the authority on whether a local turn can execute

**Code changes needed:**
- Implement the actual bridge: when `CrossFedPipelineBridge::on_pipeline_result()` returns resolved messages, feed them into `PendingTurnRegistry::resolve()`
- When `PendingTurnRegistry` resolves a turn that has cross-fed dependents, notify `CrossFedPipelineBridge` to send `PipelineWireMessage::PromiseResolved` to the waiting peer
- Unify the broken-promise types: `BrokenReason` (pending.rs) and `PipelinePromiseState::Broken` (pipeline.rs) should use a shared `BrokenReason` enum

---

## 6. Gossip (node/gossip.rs + node/bridge.rs) vs CapTP Store-and-Forward (captp/store_forward.rs)

### What each does

**Gossip/Bridge (node/gossip.rs, node/bridge.rs):**
- `GossipHandle`: pub/sub topics for turns, revocations, intents, roots, checkpoints
- Bridge node: joins MULTIPLE federations' gossip networks, relays messages between them
- Always-on, real-time: messages flow as soon as they're published
- Unencrypted topics (messages are public within the topic's scope)
- No queuing for offline peers (gossip is ephemeral)

**Store-and-Forward (captp/store_forward.rs):**
- `MessageRelay`: stores encrypted messages for offline destinations
- `BlocklaceEnvelope`: messages embedded in blocklace blocks for DAG-based delivery
- End-to-end encrypted (X25519 + ChaCha20-Poly1305)
- Causal ordering, TTL-based expiry, priority queuing
- Designed for offline-first mobile

### Overlap analysis

These are **different delivery models**, not duplicates:
- Gossip = ephemeral broadcast, online-only, pub/sub topics
- Store-and-forward = durable unicast, offline-capable, encrypted, ordered

They complement each other:
- Gossip handles the happy path (everyone online, realtime propagation)
- Store-and-forward handles the unhappy path (destination offline, mobile scenario)

The bridge node (node/bridge.rs) is the cross-federation equivalent of a gossip relay, while CapTP store-and-forward is the cross-federation equivalent of a persistent message queue.

### Recommendation: **Keep both** (different delivery guarantees)

- Gossip remains the real-time broadcast layer for public messages (turns, roots, revocations)
- Store-and-forward remains the durable delivery layer for private capability messages
- The bridge node should use store-and-forward as a fallback when a remote federation's gossip subscriber is unreachable

**Code changes needed:**
- In `node/src/bridge.rs`: when relay delivery fails (remote federation unreachable), queue the message via `StoreForwardClient` instead of dropping it
- Add a `TOPIC_CAPTP` gossip topic for CapTP wire messages that need broadcast semantics (e.g., `DropRef` notifications to all holders)
- `BlocklaceEnvelope` is already designed to ride the existing blocklace sync; no changes needed there

---

## Summary Table

| Old Mechanism | CapTP Equivalent | Relationship | Recommendation |
|---|---|---|---|
| `EventualRef` / `Pipeline` | `PipelineRegistry` | Different layers (local vs network) | **Layer**: CapTP wraps local pipeline for cross-fed |
| `Effect::Introduce` | `HandoffCertificate` | Same problem, different connectivity | **Keep both**: Introduce = fast local, Handoff = offline cross-fed |
| `BridgeLock/BridgeFinalize` | CapTP sessions | Independent concerns (value vs capability) | **Independent**: bridge uses CapTP for transport only |
| `RoutingDirective` / `RoutingTable` | CapTP export tables | Different layers of same operation | **Layer**: directive feeds BOTH routing table and GC |
| `PendingTurnRegistry` | `PipelineRegistry` | Same abstraction, different granularity | **Layer**: pipeline feeds pending registry |
| Gossip / bridge relay | Store-and-forward | Different delivery guarantees | **Keep both**: gossip = realtime, S&F = offline |

---

## Priority Order for Implementation

1. **Wire PendingTurnRegistry to PipelineRegistry** (5 of the integration gaps funnel through here)
   - Location: new glue code in `wire/src/server.rs` or a new `node/src/captp_bridge.rs`
   - When WireMessage::PipelineResult arrives, resolve the corresponding pending turn
   - When a turn with cross-fed dependents resolves, send PromiseResolved to peers

2. **RoutingDirective -> ExportGcManager** (closes the GC gap for Introduce-created capabilities)
   - Location: `node/src/routing_table.rs` + integration with `CapTpState`
   - Small change, big correctness win (without it, introduced caps leak forever)

3. **Store-and-forward fallback for bridge relay** (robustness)
   - Location: `node/src/bridge.rs`
   - When remote federation is unreachable, queue via S&F instead of dropping

4. **Cross-federation Introduce -> HandoffCertificate conversion** (new capability)
   - Location: `turn/src/executor.rs` Effect::Introduce handler
   - If target is remote, generate HandoffCertificate instead of local grant

5. **BridgeReceipt delivery via CapTP** (cleaner transport)
   - Location: bridge executor handler
   - Use store-and-forward for receipt delivery, pipeline promise for the 2-phase flow

---

## Conflicts Found

**No true conflicts.** The systems were designed at different layers and their assumptions are compatible:
- Old system assumes synchronous local execution + bridge nodes for cross-fed
- CapTP assumes asynchronous networked execution + store-and-forward for offline
- They compose cleanly: old = internal mechanics, CapTP = external protocol

The only "smell" is that `RoutingDirective` currently bypasses CapTP entirely (no GC tracking, no export recording), which means capabilities created via `Effect::Introduce` are invisible to distributed GC. This is a correctness gap, not a conflict.
