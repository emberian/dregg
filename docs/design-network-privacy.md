# Network-Layer Privacy for pyana-net

## Problem

The QUIC gossip network (Plumtree over quinn) has zero privacy protections:

- **IP visibility**: Peers see each other's IP via `conn.remote_address()`.
- **Timing correlation**: Eager-push forwarding is immediate; an observer on the spanning tree can correlate message origin by arrival time.
- **Size fingerprinting**: STARK proofs are 48-432 KiB, turns are ~1 KiB, intents are ~2 KiB. Message size alone reveals type.
- **Global observer**: A peer in the eager set of multiple topics sees all traffic for those topics in real time.

## Design Options

| Approach | Latency | Bandwidth Overhead | Complexity | Anonymity | QUIC Compatible |
|---|---|---|---|---|---|
| Tor hidden services | +300-600ms/hop | Low (just Tor overhead) | Medium (arti crate) | Strong (large set) | Yes (TCP-over-Tor, or arti QUIC tunneling) |
| Custom mixnet (Loopix) | +200-2000ms tunable | High (cover traffic) | High (mix infra) | Provable unlinkability | Yes (mix nodes wrap QUIC) |
| Dandelion++ | +50-200ms (stem) | Near zero | Low | Origin hiding only | Native (gossip-level) |
| Message padding | None | Up to 500x for small msgs | Trivial | Size only | Native |
| Constant-rate noise | None | O(n^2) for n peers | Medium | Strong timing privacy | Native |

## Staged Approach

### Phase 1 (NOW): Dandelion++ + Two-Bucket Padding

**Dandelion++ integration point**: At the gossip level, inside `GossipNetwork::publish()` and `handle_envelope()`. The stem phase replaces eager-push for the first few hops.

**Code changes required:**

1. **Add `StemState` to `GossipState`** -- track which messages are in stem phase vs fluff phase. New field: `stem_messages: HashMap<MessageHash, StemInfo>` where `StemInfo` holds the chosen stem relay and a timeout.

2. **Modify `GossipNetwork::publish()`** -- instead of immediately sending to all eager peers, select one random peer as the stem relay. Send only to that peer with a new `GossipEnvelope::Stem { ... }` variant.

3. **Add `GossipEnvelope::Stem` variant** -- identical to `FullMessage` but signals the receiver should continue stem-forwarding (probability 0.9) or transition to fluff/eager-push (probability 0.1). Each hop flips a biased coin.

4. **Stem timeout in `ihave_timeout_loop`** -- if a stem message is not seen back via fluff within 5 seconds, the originator falls back to normal eager-push (prevents black-hole attacks).

5. **Two-bucket padding in `send_to_peers()`** -- before writing to the QUIC stream, pad all payloads to either 4 KiB (small: turns, intents, revocations) or 512 KiB (large: STARK proofs, checkpoints). Padding is random bytes appended after a length delimiter already present in the framing.

6. **Strip padding in `read_signed_envelope()`** -- use the existing 4-byte length prefix to identify real payload boundary; ignore trailing pad bytes.

Files touched: `net/src/gossip.rs` (bulk of changes), `net/src/message.rs` (padding helpers).

### Phase 2 (SOON): Tor Hidden Services for Inter-Federation

Route cross-federation gossip through Tor. Each federation gateway node runs an `arti` embedded client and exposes a `.onion` address. Intra-federation traffic stays on direct QUIC (low latency matters for consensus).

Integration: New `net/src/tor_transport.rs` module implementing a `Transport` trait that `GossipNetwork` dispatches to based on whether the target peer is local or remote federation.

### Phase 3 (LATER): Intra-Federation Mix Layer

Sphinx-packet-based mix network for messages within a federation. Three mix nodes (from the federation's own validator set) add Poisson-distributed delays. Cover traffic at 1 msg/sec per peer pair masks real activity.

Integration: Below gossip, above QUIC. A `MixLayer` sits between `GossipNetwork::send_to_peers()` and the raw `conn.open_uni()` call, buffering and reordering outgoing messages.

## Architectural Decision: Gossip-Level, Not Transport-Level

Mixing plugs in at the gossip layer (`OutgoingGossip` dispatch) rather than the transport layer (quinn `Endpoint`). Reasons:

1. QUIC connections are long-lived and multiplexed -- wrapping at transport level would require tunneling entire QUIC connections through a mix, adding complexity with no benefit.
2. The `SignedEnvelope` already provides authenticated message boundaries -- the mix layer can operate on individual envelopes.
3. Stem routing (Dandelion++) is inherently a gossip-topology decision, not a transport decision.
4. The existing `send_to_peers()` function is the natural interception point for all outgoing traffic.
