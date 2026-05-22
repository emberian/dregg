# Evaluation: Should pyana replace net/ with iroh?

## Summary

**Recommendation: Do not replace. Use iroh as an optional transport layer beneath the existing gossip protocol, if and when NAT traversal becomes a deployment blocker.**

The net/ crate is lean (3,888 lines), domain-specific, recently hardened, and well-understood. iroh solves a different problem (connectivity in hostile NAT environments) at the cost of a massive dependency surface and loss of protocol control. The value proposition does not justify a rewrite today.

---

## 1. What pyana's net/ currently provides

| Capability | Implementation |
|---|---|
| QUIC transport | quinn 0.11 (direct dep, 1 layer) |
| Mutual TLS | rustls 0.23, self-signed certs, ALPN `pyana/p2p/1` |
| Peer identity | blake3(cert_der) -> NodeId (32 bytes) |
| Ed25519 signed envelopes | Asymmetric per-node signing; receivers verify via peer registry |
| PlumTree gossip | Eager/lazy push, Graft/Prune tree repair |
| HyParView-style | Implicit via eager degree cap (DEFAULT_EAGER_DEGREE=3) |
| Anti-entropy | Periodic capped hash digest exchange (30s interval, max 1024 hashes) |
| Deduplication | BoundedSeenSet (100k entries, 5min TTL, FIFO eviction) |
| Message cache | Bounded to 10k entries for Graft responses |
| Connection limits | 256 max connections, per-IP rate limiting (10/min) |
| Per-peer stream limits | MAX_STREAMS_PER_PEER=64 prevents stream flooding |
| Allowlist verifier | Runtime-mutable NodeId allowlist for Sybil resistance |
| Domain messages | PublishTurn, AttestedRootUpdate, RevocationGossip, ProposeAtomicTurn, VoteAtomicTurn, CommitAtomicTurn, PublishCheckpoint, PublishPipeline, PublishIntent, CellStateRequest/Response |
| Causal DAG | Tracks happened-before ordering with topological sort, frontier merge |
| Wire format | postcard + 4-byte length prefix |

Total dependency count: 6 direct (quinn, rustls, rcgen, tokio, postcard, blake3, ring, rand, serde -- well-known, stable crates).

---

## 2. What iroh provides that pyana does not have

| Capability | Value to pyana |
|---|---|
| NAT traversal / hole punching | HIGH -- but only matters when peers are behind symmetric NATs |
| Relay fallback | HIGH -- guarantees connectivity when direct path fails |
| "Connect by public key" (NodeId routing) | MEDIUM -- eliminates need to know IP:port a priori |
| DNS-based discovery (pkarr) | LOW -- pyana uses federation config for peer discovery |
| magicsock (path selection) | MEDIUM -- auto-selects best path (relay vs direct) |
| WASM support | Partial -- iroh has `wasm_browser` cfg gates, but with reduced functionality (no UDP, no hole punching) |
| Production scale testing | MEDIUM -- iroh is used in production at n0 |

---

## 3. What pyana has that iroh does NOT provide

| Capability | Notes |
|---|---|
| Domain-specific message types | 12+ variants (turns, roots, intents, atomic coordination, checkpoints, pipelines) -- iroh gossip deals only in opaque `Bytes` |
| Causal DAG with topological ordering | Not in iroh; purely application logic |
| Federation-aware authentication | Ed25519 peer registry, signed envelopes verified against known federation members |
| Custom anti-entropy with bounded digests | iroh-gossip has its own but with different guarantees (HyParView passive view shuffle) |
| Tight integration with consensus | ProposeAtomicTurn/VoteAtomicTurn/CommitAtomicTurn are protocol-level messages in the gossip layer |
| Postcard wire format | iroh-gossip also uses postcard, so this is compatible |
| Minimal dependency surface | 6 crates vs iroh's 47+ direct dependencies |

---

## 4. Migration complexity analysis

### net/ breakdown by concern:

- **Transport (node.rs, ~960 lines):** Quinn endpoint setup, TLS config, connection management, rate limiting. This is what iroh would replace.
- **Gossip protocol (gossip.rs, ~1942 lines):** PlumTree implementation, signed envelopes, anti-entropy, deduplication. This is domain logic that iroh-gossip partially replaces but with different semantics.
- **Domain messages (message.rs, ~230 lines):** PeerMessage enum. Iroh-gossip would treat these as opaque bytes.
- **Causal ordering (causal.rs, ~403 lines):** Independent of transport. Stays regardless.

### Three possible integration strategies:

**A) Replace quinn with iroh as transport only (keep our gossip):**
- Replace `PeerNode` (960 lines) with iroh `Endpoint`
- Keep `GossipNetwork` intact, just change how connections are established
- Effort: ~1-2 weeks
- Benefit: NAT traversal, relay fallback
- Risk: Low -- minimal protocol changes

**B) Replace both transport AND gossip with iroh + iroh-gossip:**
- Replace everything except message.rs and causal.rs
- iroh-gossip delivers opaque Bytes; we serialize PeerMessage into those bytes
- Lose: custom anti-entropy parameters, signed envelope verification at gossip layer, per-topic eager degree control
- Gain: HyParView membership protocol (more sophisticated than our implicit eager cap), battle-tested PlumTree
- Effort: ~3-4 weeks
- Benefit: Full iroh stack benefits
- Risk: HIGH -- lose domain-specific optimizations, harder to debug, massive dependency tree

**C) Hybrid: iroh transport + our gossip protocol, with iroh-gossip available for non-critical topics:**
- Use iroh `Endpoint` for connectivity
- Keep our `GossipNetwork` for federation-critical topics (turns, attestations, consensus)
- Optionally use iroh-gossip for lower-priority broadcast (telemetry, discovery)
- Effort: ~2-3 weeks
- Risk: Medium -- two gossip systems to maintain

---

## 5. Risks of adopting iroh

| Risk | Severity | Notes |
|---|---|---|
| Dependency on external project | MEDIUM | n0 is VC-funded; if funding dries up, 25k LOC of networking code becomes unmaintained. Their GitHub shows active development as of 2025, but enterprise dependencies have been abandoned before. |
| Version churn | HIGH | iroh uses their own quinn fork (`iroh-quinn`), their own blake3 fork (`iroh-blake3`). Version 0.35 -- still pre-1.0. Breaking changes between 0.x versions. |
| WASM story | WEAK | iroh's WASM support is browser-only with `wasm-bindgen-futures`, no UDP (no hole punching in browser), effectively relay-only. pyana's WASM crate currently does not include networking at all. |
| Dependency weight | HIGH | iroh pulls in 47+ direct deps including `reqwest`, `hickory-resolver`, `igd-next`, `portmapper`, `surge-ping`, `pkarr`, `crypto_box`, etc. Compile time impact would be severe. |
| Authentication model mismatch | MEDIUM | iroh uses ed25519 `SecretKey`/`PublicKey` (ed25519-dalek) for node identity. pyana uses `blake3(cert_der)` for NodeId + separate Ed25519 signing keys from `pyana-types`. These are reconcilable but require adapter code. |
| Gossip semantics mismatch | MEDIUM | iroh-gossip has a 4KB default max message size (`DEFAULT_MAX_MESSAGE_SIZE`). Pyana messages (turns with data, forest data for atomic turns) can be larger. Configurable but shows different design assumptions. |
| Loss of protocol visibility | HIGH | With our gossip, we control every envelope, can add fields, change serialization. With iroh-gossip, we are a consumer of an opaque protocol. |
| Forked quinn | HIGH | iroh uses `iroh-quinn` 0.13, a fork. If upstream quinn evolves (currently 0.11 in pyana), we would be locked into iroh's fork decisions. |

---

## 6. Risks of NOT adopting iroh

| Risk | Severity | Notes |
|---|---|---|
| No NAT traversal | HIGH (for public deployment) | Peers behind symmetric NATs cannot connect. Currently mitigated by federation topology (known endpoints). |
| No relay fallback | MEDIUM | If direct QUIC fails, connection is lost. |
| Maintaining QUIC ourselves | LOW | Quinn is stable and well-maintained. pyana just uses it; we don't maintain QUIC itself. |
| Less battle-tested | LOW | Our gossip is ~1900 lines with comprehensive tests. The protocol (PlumTree) is well-understood from academia. |
| Peer discovery | LOW | Pyana uses federation config. We don't need DNS-based discovery. |

---

## 7. Honest assessment

**What looks impressive but isn't (per ember's warning):**

- iroh-gossip's PlumTree implementation is fundamentally the same algorithm we already have. Ours is simpler (1942 lines vs 7749 lines for iroh-gossip), which is a feature not a bug.
- iroh's "connect by public key" is elegant but assumes you use their relay infrastructure. For a federated system where node addresses are in genesis config, this solves a non-problem.
- iroh-blobs is entirely irrelevant to pyana's use case (we don't transfer large files via gossip).
- The HyParView membership protocol in iroh-gossip is more sophisticated than our eager degree cap, but our federation has a known, small participant set (not thousands of anonymous peers). HyParView matters when you have 1000+ nodes with churn. Pyana federations are typically 3-21 nodes.

**What is genuinely valuable:**

- NAT traversal and relay fallback. This is the one thing that is genuinely hard to build yourself and that iroh does well. If pyana ever needs to work across residential NATs without a VPN or known public endpoints, iroh's magicsock is the right answer.
- The relay infrastructure is real and operational.

---

## 8. Recommendation

**Do not migrate today.** The net/ crate is fit for purpose:

1. It implements the same PlumTree algorithm as iroh-gossip, with fewer lines and tighter domain integration.
2. It was recently hardened (Ed25519 auth, bounded caches, stream limits, signed envelopes).
3. Pyana's deployment model (federated nodes with known addresses) sidesteps iroh's primary value proposition (NAT traversal for unknown peers).
4. The dependency cost is enormous (6 deps -> 47+ deps, forked quinn).
5. The WASM story doesn't help us (iroh WASM is relay-only; pyana WASM doesn't include networking).

**Consider iroh as transport-only (Strategy A) when:**
- Pyana needs to support nodes behind residential NATs (not just data center or known-endpoint deployments).
- There is a concrete deployment scenario where relay fallback would save users.
- iroh reaches 1.0 and stabilizes its API.

**Practical next step if NAT becomes a blocker:**
Abstract `PeerNode` behind a trait (`Transport`) so the gossip layer is transport-agnostic. Then iroh's `Endpoint` becomes one implementation. This is ~200 lines of refactoring and preserves optionality without committing to iroh's dependency tree today.
