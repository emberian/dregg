# Cross-Federation Routing Protocol

## Problem Statement

Authority and reachability are orthogonal. A `CapabilityRef` encodes *permission* (target CellId, slot, permissions, breadstuff hash) but not *location*. Within a single federation this is fine -- the node's routing table, populated by `RoutingDirective`s from 3PI turns, maps CellIds to local peers. But when Alice (federation A) introduces Bob (federation A) to Carol (federation B), the resulting RoutingDirective contains Carol's CellId without any information about how to reach federation B's network. Bob holds authority he cannot exercise.

The invariant we must preserve: capabilities remain unforgeable, confinement-respecting, and attenuatable. Routing metadata is operational, not a security property -- it guides message delivery but never expands authority.

## Design Space

### Option 1: Routing Hints in CapabilityRef

Add `routing_hint: Option<RoutingHint>` to `CapabilityRef`. A `RoutingHint` carries the target's federation ID (a 32-byte BLAKE3 hash of the federation's genesis attested root) and one or more relay addresses.

**Pros**: Self-contained -- the holder can reach the target without any out-of-band lookup. Works offline (no directory query needed). Composable with sealed boxes (hint travels inside the ciphertext).

**Cons**: Enlarges every CapabilityRef even for intra-federation caps. Leaks federation membership to anyone who inspects the c-list. Stale if the federation's relay moves. Breaks the principle that CapabilityRef is purely about authority.

### Option 2: Federation Directory (discovery.json)

Each federation publishes a signed discovery document at a well-known location. Relays maintain a cache of known federation endpoints. To reach a cross-fed target, the node resolves `federation_id -> relay_address` from the directory.

**Pros**: Clean separation (cap = authority, directory = location). Federation can rotate relays without invalidating capabilities. Small caps.

**Cons**: Requires online directory access (breaks offline exercise). Introduces a discovery dependency -- if the directory is down, cross-fed caps are unexercisable. Centralizes routing knowledge.

### Option 3: Relay-Mediated Routing

Bob's relay brokers connections. Bob sends `RouteRequest { target: CellId, federation_hint: Option<FederationId> }` to his relay. The relay looks up which peer federation hosts that CellId (via inter-relay gossip or directory) and establishes a QUIC connection to the remote relay, which forwards to Carol's node.

**Pros**: Relay already exists in the architecture. No cap changes. Relay can enforce rate limits and access control. NAT-friendly (both sides connect out to their relay).

**Cons**: Relay becomes a routing bottleneck and single point of failure. Adds latency (two relay hops). Relay learns who is talking to whom (metadata leakage).

### Option 4: Scoped Capabilities

`CapabilityRef` gains `scope: FederationScope` (Local | CrossFed(FederationId)). Exercising a CrossFed cap triggers an explicit bridge operation: the node wraps the message in a `BridgeEnvelope` with the scope, and hands it to the relay for cross-federation delivery.

**Pros**: Explicit about cross-fed exercise (no silent failures). Enables federation-level policy (e.g., "no outbound caps to federation X"). Scope is a security-relevant annotation, not just metadata.

**Cons**: Complicates attenuation (scope must be preserved or narrowed through delegation). Introduction logic must decide scope at grant time. Adds a new dimension to capability comparison.

### Option 5: Content-Addressed Routing (Privacy-Preserving)

Route by `H(CellId)` through a DHT-like overlay, similar to iroh's content-addressed networking. The routing layer maps `H(CellId) -> relay_endpoint` without revealing which federation the cell belongs to. Federation membership is hidden from intermediaries.

**Pros**: Maximum privacy -- routing reveals only a hash, not federation identity. Works across federations without explicit federation discovery. Aligns with pyana's ZK philosophy.

**Cons**: Requires a global overlay network (DHT or gossip). DHT maintenance has churn costs. Sybil resistance needed. Higher latency than direct relay-to-relay. CellId stability assumption (if cells migrate between federations, routing entries must update).

## Recommended Approach: Layered (Options 1 + 3 + 5)

Use a three-layer design:

1. **RoutingHint as metadata, not in CapabilityRef.** The `RoutingDirective` (already emitted by 3PI) gains an optional `hint: Option<RoutingHint>`. The node stores hints in its routing table alongside the CellId mapping. Hints are mutable operational state, not part of the capability's identity or hash.

2. **Relay-mediated cross-federation delivery.** When a node cannot locally resolve a CellId, it queries its relay with a `CrossFedRoute` request. The relay maintains a federation peer table (populated from discovery documents exchanged during inter-relay handshake). The relay establishes a QUIC stream to the remote federation's relay and forwards the envelope.

3. **CellId-hash overlay for privacy (progressive enhancement).** For cells that opt into private routing, their relay publishes `H(CellId || routing_nonce)` to a lightweight gossip overlay. Senders who hold the routing_nonce (delivered inside the RoutingHint at introduction time) can compute the lookup key without revealing the CellId to the overlay.

### Why not embed in CapabilityRef?

CapabilityRef participates in commitment hashes (breadstuff verification, fold chain membership proofs, sealed box ciphertext). Adding routing metadata would bloat proofs and couple location to authority. Instead, routing hints live in the RoutingDirective (which is already ephemeral, non-committed state).

## Interactions

### With 3PI

`Effect::Introduce` already emits a `RoutingDirective`. For cross-fed introductions, the introducer (Alice) must supply a `RoutingHint` for the target. The executor attaches it to the directive. The introducer knows the hint because she already communicates with the target (she holds a live route).

### With Delegation (DelegatedRef)

When a child refreshes its snapshot and the snapshot contains cross-fed capabilities, the refresh response includes updated routing hints. Hints are not part of the `DelegatedRef` struct (they are in the routing table), so epoch-based revocation does not invalidate them -- but the refresh can update stale relay addresses.

### With Sealed Boxes

A sealed capability can include routing metadata inside the ciphertext (alongside the serialized CapabilityRef). The unsealer gets both the authority and the route. Since sealed boxes are encrypted, this does not leak federation membership to intermediaries.

### With Intents

Intent matching is unaffected -- intents are broadcast by topic, not routed to specific cells. When an intent is fulfilled and a capability is transferred, the transfer message includes routing hints for any cross-fed targets in the granted capabilities.

## Struct Changes

```rust
// In turn/src/routing.rs -- extend RoutingDirective
pub struct RoutingDirective {
    pub sender: CellId,
    pub target: CellId,
    pub authorizing_turn: [u8; 32],
    pub expires: Option<u64>,
    pub hint: Option<RoutingHint>,  // NEW
}

// New type (in types crate or turn crate)
pub struct RoutingHint {
    /// Target's federation identity (BLAKE3 of genesis attested root).
    pub federation_id: [u8; 32],
    /// One or more relay endpoints (QUIC SocketAddr or DNS name).
    pub relays: Vec<RelayEndpoint>,
    /// Optional nonce for private DHT lookup: H(CellId || nonce) is the lookup key.
    pub routing_nonce: Option<[u8; 32]>,
}

pub struct RelayEndpoint {
    pub addr: SocketAddr,       // or String for DNS
    pub public_key: [u8; 32],   // relay's Ed25519 public key (for TLS verification)
}
```

`CapabilityRef` is UNCHANGED. Routing hints are operational, not committed.

## Node/Relay Changes

**Node routing table**: Extend from `HashMap<CellId, PeerAddr>` to `HashMap<CellId, RouteEntry>` where `RouteEntry` is `Local(PeerAddr) | Remote(RoutingHint)`. On message send, if the entry is `Remote`, delegate to relay.

**Relay**: Add a `CrossFedRoute` request type. On receipt, the relay resolves the target federation from its peer table, opens (or reuses) a QUIC stream to the remote relay, and forwards the message envelope. The remote relay delivers locally.

**Inter-relay handshake**: When two relays connect, they exchange signed discovery documents (federation_id, supported CellId prefixes or bloom filter, public key). This populates the peer table without requiring a global directory.

**Privacy overlay (optional)**: A relay can participate in a lightweight gossip-based routing overlay. It publishes `H(CellId || nonce)` entries for cells that opt in. Remote relays query the overlay to discover which relay serves a given hash.

## Open Questions

1. **Hint staleness**: How long is a routing hint valid? Should hints carry a TTL, or should nodes fall back to relay query on delivery failure?
2. **Multi-home cells**: A cell might be reachable via multiple federations (after exit+rejoin). Should RoutingHint be a list of alternatives, and if so, what ordering/priority?
3. **Relay trust**: The relay sees cross-fed message metadata (source federation, target federation, message size). Is onion-routing between relays worth the complexity?
4. **Overlay protocol**: If we adopt the privacy DHT, what protocol? Iroh's content routing is attractive but adds a dependency. A simpler gossip-based approach (publish hints to Plumtree topics) may suffice at small scale.
5. **Federation exit**: When a cell exits federation A and joins federation B, all outstanding routing hints pointing to A become stale. The cell must proactively notify holders (but it may not know who holds caps to it). Fallback: relay query after hint failure.
6. **Proof interaction**: RoutingDirective.hash() is used in receipts. Adding the hint changes the hash. Should the hint be excluded from the receipt hash (keeping receipts routing-agnostic)?
