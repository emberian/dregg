# Pyana: Distributed Object-Capability Authorization with Zero-Knowledge Presentation

## 1. What is Pyana?

Pyana is a distributed authorization system that lets AI agents prove they are authorized to act across organizational boundaries, without revealing their delegation chain, the identities of intermediate authorities, or what other capabilities they hold. It combines capability-security semantics (object-capability model) with zero-knowledge proofs (STARKs) and federated BFT consensus to create an offline-verifiable, post-quantum-ready authorization layer.

### Key Properties

- **Distributed object-capability authorization.** Agents hold capabilities (unforgeable references to resources) in per-cell c-lists. Capabilities can only be attenuated (restricted), never amplified.
- **ZK-private cross-domain verification.** Present authorization to an untrusted verifier as a STARK proof. The verifier learns only that the presenter is authorized for the specific action requested — nothing about the delegation chain, other capabilities, or intermediate authorities.
- **Designed for AI agent execution across trust domains.** The execution model (Cells, Turns, Call Forests) is built for agents that span multiple organizations, each with independent security policies.
- **Post-quantum ready.** The external verification interface is entirely hash-based (STARK proofs, Merkle commitments). Classical signatures (Ed25519, BLS12-381) are confined within federation trust boundaries.
- **Offline verification.** No blockchain liveness dependency. Federation roots provide freshness bounds; verification requires only the proof and the federation's attested root.
- **Inspired by Mina Protocol's zkApp model.** One of pyana's architects was a founding architect of Mina. The execution model (Turns = ZkappCommands, Cells = Accounts, Call Forests) is adapted from Mina's architecture, recontextualized for authorization rather than financial transactions.

---

## 2. Core Insight

> **Capability attenuation IS incrementally verifiable computation.**

Every time a capability is delegated with restrictions (narrowed to fewer services, shorter time windows, reduced budget), that attenuation step is a *fold* over a committed fact set. Each fold produces a new state that is strictly smaller than its predecessor. This monotonic narrowing forms a chain of state transitions — exactly the structure that IVC (Incrementally Verifiable Computation) was designed to prove.

The prover demonstrates: "I hold a valid chain of attenuations starting from an issuer in the federation, ending with a capability set that satisfies your request." The verifier checks a single STARK proof without seeing any intermediate states.

This insight means we get zero-knowledge presentation *for free* from the capability model — we don't bolt privacy onto an existing system; the authorization structure *is* the computation being proved.

---

## 3. Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SDK Layer (pyana-sdk)                            │
│  AgentWallet · AgentRuntime · SiloClient                                │
├─────────────────────────────────────────────────────────────────────────┤
│                         Network Layer (wire)                             │
│  TCP wire protocol · postcard framing · STARK verification on receive   │
│  QUIC gossip (Plumtree lazy-push) [planned]                            │
├─────────────────────────────────────────────────────────────────────────┤
│                         Federation Layer                                 │
│  morpheus — Adaptive BFT consensus (Lewis-Pye & Shapiro)                │
│  hints — BLS12-381 threshold signatures (KZG + SNARK proof)             │
│  federation — Ed25519 consensus, revocation trees                       │
├─────────────────────────────────────────────────────────────────────────┤
│                         Coordination Layer (coord)                       │
│  Causal: async DAG (partial-order event tracking)                       │
│  Atomic: 2PC with threshold quorum certificate                          │
│  Budget: Bounded counters (Stingray) — local spend, periodic rebalance  │
├─────────────────────────────────────────────────────────────────────────┤
│                         Execution Layer                                  │
│  cell — Isolated accounts with c-lists (capability sets)                │
│  turn — Atomic transactions (call forests, nonces, fees)                │
│  coord — Multi-silo coordination (2PC + causal ordering)                │
├─────────────────────────────────────────────────────────────────────────┤
│                         Proof Layer (circuit)                            │
│  BabyBear STARK with FRI (real proofs, ~24 KiB, sub-second gen)         │
│  Poseidon2 algebraic hash (SNARK-friendly, in-circuit)                  │
│  IVC: hash-chain accumulation (recursive STARK-in-STARK planned)        │
│  AIR constraints: fold, derivation, Merkle membership                   │
├─────────────────────────────────────────────────────────────────────────┤
│                         Commitment Layer (commit)                        │
│  4-ary Merkle trees (BLAKE3 fast path, Poseidon2 ZK path)              │
│  Fold deltas: monotonic state transitions on committed fact sets         │
│  Symbol table: interned predicate/term identifiers                      │
├─────────────────────────────────────────────────────────────────────────┤
│                         Policy Layer (trace + token)                     │
│  trace — Datalog evaluator with derivation traces                       │
│  token — AuthToken trait: Macaroon (HMAC) + Biscuit (Ed25519+Datalog)  │
│  tokenizer — X25519-ChaCha20Poly1305 seal/unseal                       │
├─────────────────────────────────────────────────────────────────────────┤
│                         Storage Layer                                    │
│  store — redb (ACID, crash-safe) persistence + encrypted keys           │
│  secrets — OS keychain + encrypted file store (atomic writes)           │
│  audit — Usage log, budget enforcement, consistency proofs              │
└─────────────────────────────────────────────────────────────────────────┘
```

### Data Flow: ZK Presentation

```
  Issuer mints root token (macaroon, 32-byte HMAC key)
       │
       ▼
  Attenuate: restrict to {service: "dns", access: "read", ttl: 3600}
       │
       ▼
  Commit: fact set → 4-ary Merkle tree leaf, fold delta recorded
       │
       ▼
  Trace: Datalog evaluation proves authorization (derivation trace)
       │
       ▼
  Circuit: fold witness + derivation witness + Merkle membership
       │
       ▼
  STARK prove: ~24 KiB proof, ~300-560ms generation
       │
       ▼
  Wire: send proof + public inputs to verifier silo (TCP)
       │
       ▼
  Verify: check STARK proof against federation root (sub-millisecond)
```

---

## 4. Key Capabilities

### Capability Attenuation

Delegation chains can only restrict, never expand. A root token grants `{all services, infinite TTL, full budget}`. Each attenuation step produces a new token with a *strictly smaller* capability set. The type system enforces monotonic narrowing:

```rust
pub struct Attenuation {
    pub services: Vec<(String, String)>,  // (service, max_access_level)
    pub max_ttl: Option<Duration>,
    pub max_uses: Option<u64>,
    pub require_ip: Option<IpNet>,
}
```

The fold delta captures exactly what was removed, enabling efficient in-circuit verification that the new state is a valid restriction of the old.

### ZK Presentation

Present authorization to an untrusted verifier without revealing:
- The delegation chain (who delegated to whom)
- Intermediate authorities (organizational structure)
- Other capabilities the agent holds
- The original token's scope (only the requested action is checked)

The verifier sees: a STARK proof (~24 KiB), the federation root hash, and the authorization request. Nothing else.

### Federation Consensus

Federations are small groups of organizations (3-64 nodes) that share a trust root. The `morpheus` crate implements adaptive BFT consensus (Lewis-Pye & Shapiro): it tolerates up to f Byzantine nodes in a 3f+1 committee, with view-change and block finalization. The `hints` crate provides BLS12-381 threshold signatures via real KZG polynomial commitments + SNARK proofs for aggregate verification.

Federation roots are attested periodically. These attestations (threshold-signed Merkle roots) are the freshness anchors for offline verification.

### Offline Verification

No chain liveness is required to verify a presentation. The verifier needs:
1. A STARK proof (self-contained)
2. The federation root (attested by the last finalized block or out-of-band)
3. The authorization request

If the federation root is stale, the verifier can still accept (with a freshness warning) or reject. There is no "call home" requirement.

### Computron Budgets

Adapted from Stingray (arXiv:2501.06531). An agent's total computation budget is split across silos using bounded counters:

```
slice = balance * (f+1) / (2f+1)
```

Each silo can debit locally up to its slice without coordination. This enables parallel multi-silo execution without per-operation consensus, while guaranteeing that even f Byzantine silos cannot overspend the agent's true balance.

### Post-Quantum Security

| Layer | Scheme | PQ-secure? |
|-------|--------|:----------:|
| External proofs (STARKs) | BabyBear + Poseidon2 + FRI | Yes |
| Merkle commitments | BLAKE3 / Poseidon2 | Yes |
| Macaroon HMAC chain | HMAC-SHA256 | Yes (128-bit vs Grover) |
| Federation QCs | BLS12-381 | No (inside trust boundary) |
| Node identity | Ed25519 | No (inside trust boundary) |
| Sealed secrets | X25519 + ChaCha20 | No (inside trust boundary) |

The critical property: **everything that crosses a trust boundary is PQ-secure.** Classical signatures exist only within federations where members already trust each other. The PQ migration path (lattice threshold sigs: Hermine, Oriole, TalonG) is designed but waiting on NIST standardization (late 2026/2027).

---

## 5. Security Model

### Trust Boundaries

```
                    ┌─────────────────────────────────┐
                    │     Federation Trust Boundary     │
                    │                                   │
                    │  Ed25519 identity, BLS threshold  │
                    │  (classical — PQ migration path)  │
                    │                                   │
                    │    ┌─────────┐   ┌─────────┐    │
                    │    │ Silo A  │   │ Silo B  │    │
                    │    └────┬────┘   └────┬────┘    │
                    │         │              │         │
                    └─────────┼──────────────┼────────┘
                              │              │
                         STARK proofs only (PQ)
                              │              │
                    ┌─────────▼──────────────▼────────┐
                    │       External Verifiers          │
                    │  (see only: proof + public inputs)│
                    └──────────────────────────────────┘
```

### Key Invariants

- **Capability confinement:** `GrantCapability` checks that the granting cell actually holds authority over the source. You cannot delegate what you don't have.
- **Monotonic attenuation:** Fold deltas can only remove facts (capabilities), never add them. Enforced by the fold AIR constraint.
- **Fail-closed verification:** STARK verification returns `Err` on any failure (malformed proof, wrong public inputs, FRI check failure). No "soft fail" mode.
- **Non-membership proofs for revocation:** Prove a token is NOT in the revocation set without enumerating the set. Uses 4-ary Merkle non-membership (ordered leaves, prove the gap).
- **Replay protection:** Turns carry nonces (monotonically increasing per cell). Duplicate nonce = reject.
- **Budget atomicity:** Computron debits are atomic with turn execution. Abort = fast unlock (no dangling locks).

### What We Assume

- Federation members are honest-majority (standard BFT: tolerate < n/3 Byzantine).
- The hash functions (BLAKE3, Poseidon2) are collision-resistant.
- BabyBear field arithmetic is correct (p = 2^31 - 2^27 + 1).
- The prover is computationally bounded (STARK soundness depends on this).

---

## 6. Comparison

| Property | Pyana | Mina Protocol | Midnight | Cosmos IBC | UCAN/ZCAP-LD |
|----------|-------|---------------|----------|------------|--------------|
| **Primary use** | Agent authorization | General L1 | Privacy DeFi | Cross-chain messaging | Decentralized auth |
| **Proof system** | BabyBear STARK + FRI | Kimchi (Plonk variant) | Plonk | None (light clients) | None |
| **Privacy model** | Full ZK presentation | Succinct state (not privacy) | Shielded transactions | Transparent | Transparent chains |
| **Consensus** | Federated BFT (3-64 nodes) | Ouroboros Samasika | Ouroboros variant | Tendermint per chain | None (P2P) |
| **Offline verify** | Yes (proof + root) | Yes (succinct state) | Partial | No (needs relayer) | Yes (but no privacy) |
| **PQ-ready** | External interface: yes | No (elliptic curves) | No (elliptic curves) | No | No |
| **Capability model** | Object-capability + Datalog | Account permissions | UTXO-based | ICS-20 channels | UCAN delegation |
| **Target scale** | 3-64 federation nodes | Global (thousands) | Global | Global (100s of chains) | Peer-to-peer |
| **Liveness requirement** | None for verification | None for verification | Chain liveness | Relayer liveness | None |

**Key differentiators:**
- vs. Mina: Pyana is an authorization system, not a cryptocurrency. Shared DNA (zkApp model, call forests), different application domain.
- vs. UCAN: UCAN delegation chains are transparent. Pyana proves the same authorization relationship without revealing the chain.
- vs. Cosmos IBC: IBC requires active relayers and chain liveness. Pyana verification is fully offline.

---

## 7. Current Status

### Codebase: ~69k LOC, 22 crates, 976 tests

| Layer | Crates | Status |
|-------|--------|--------|
| Token + Secrets | macaroon, secrets, token, tokenizer | Production-ready. HMAC chains, Biscuit+Datalog, constant-time verify, encrypted keychain. |
| Commitment | commit | Solid. 4-ary Merkle, fold deltas, symbol table. |
| Policy | trace | Solid. Datalog evaluator with derivation traces and trace verification. |
| Proof | circuit | Functional. Real STARK proofs (BabyBear + FRI + Poseidon2). ~24 KiB proofs, sub-second generation. |
| Bridge | bridge | ~80%. Connects token pipeline to circuit. 8 test failures remaining (API mismatches). |
| Execution | cell, turn, coord | Working. Cells with c-lists, Turn executor, 2PC coordinator, bounded counters. |
| Federation | federation, morpheus, hints | Working. Ed25519 BFT consensus, adaptive Morpheus protocol, BLS12-381 threshold sigs. |
| Network | wire | Real TCP. Multi-node demo (3 nodes) with real STARK verification over wire. ~560ms end-to-end. |
| Storage | store, audit | Working. redb persistence, encrypted keys, budget enforcement. |
| SDK | sdk | Functional. AgentWallet, SiloClient, AgentRuntime. |

### What's Real (Cryptographic Security)

- STARK proof generation and verification (FRI + Merkle + Fiat-Shamir)
- Poseidon2 hash over BabyBear field (in-circuit)
- Ed25519 signatures for federation consensus
- BLS12-381 threshold signatures with KZG + SNARK proof
- HMAC-SHA256 macaroon chains with constant-time verification
- AES-256-GCM encrypted secret storage
- X25519-ChaCha20Poly1305 sealed secrets
- TCP wire protocol with real STARK proof verification
- 4-ary Merkle membership AND non-membership proofs
- Multi-node demo: 3 federation nodes, real STARK over real TCP

### Known Gaps (Honest Assessment)

1. **No recursive proof composition.** IVC currently uses hash-chain accumulation (prove each step individually, verify the chain). True STARK-in-STARK recursion (a single proof that verifies a previous proof) is not yet implemented. This means proof size grows with chain length rather than staying constant.

2. **Dual Merkle systems.** `commit/` uses BLAKE3 (fast but not algebraic); `circuit/` uses Poseidon2 (algebraic, provable in-circuit). These need unification -- currently the commit layer's Merkle proofs cannot be directly verified inside a STARK.

3. **Bridge integration incomplete.** Some test failures remain from API mismatches between `bridge/` and `token/`. The presentation builder works end-to-end but has rough edges.

4. **~~Audit-identified critical issues.~~** 7 of 8 critical audit findings are now FIXED (signature verification in turn executor, proof verification via ProofVerifier trait, coordinator vote sig checks, pyana-types with 64-byte signatures, journal-based atomicity, multi-limb bridge encoding). One partial: atomic turn gas metering struct exists but call-site audit needed. See AUDIT-FINDINGS.md.

5. **Federation-to-wire integration.** Federation consensus currently uses in-process channels. The wire protocol exists and works for presentation/revocation, but federation consensus messages don't yet flow over it.

6. **Gossip protocol.** The `net/` crate (excluded from workspace currently) has a QUIC-based gossip layer but it's one-hop only, has no authentication, and has no delivery guarantees. Not production-ready.

---

## 8. Relationship to Zenith

Pyana is designed as the authorization substrate for Zenith, an AI agent orchestration platform. The integration points:

- **secS-daemon (Secrets Daemon):** Runs on each worker node. Holds the node's Ed25519 identity key and sealed secrets. When an agent presents a capability token, secS-daemon verifies the STARK proof against the federation root before granting access to the requested resource.

- **Hub worker authorization:** The Hub dispatches agent tasks to workers across organizational boundaries. Each dispatch includes an attenuated capability token (restricted to the specific task, time window, and resource budget). The worker verifies independently — no callback to the Hub required.

- **Sub-agent delegation:** When an agent spawns sub-agents, it attenuates its own token for the sub-agent's scope. The sub-agent can prove its authorization to any silo in the federation without revealing the parent agent's full capabilities.

- **Cross-organization execution:** Zenith workflows can span multiple organizations (e.g., Agent A in Org 1 needs to call a service in Org 2). Pyana's ZK presentation lets Org 2 verify authorization without learning anything about Org 1's internal delegation structure.

The pyana-sdk crate (`AgentWallet`, `AgentRuntime`, `SiloClient`) is the integration surface — a Zenith worker imports the SDK, receives tokens from the Hub, and uses the wallet to sign turns and present proofs.

---

## 9. References

1. **Stingray: Bounded Counters for BFT Payment Channels** (Auvolat, Beyer, Kuznetsov). arXiv:2501.06531. The bounded-counter model adapted for pyana's computron budgets.

2. **Morpheus: Adaptive BFT Consensus** (Lewis-Pye & Shapiro). The adaptive Byzantine consensus protocol used for federation finalization. Tolerates dynamic adversary with honest-majority assumption.

3. **Macaroons: Cookies with Contextual Caveats** (Birgisson et al., Google). The HMAC-chain bearer token model. Pyana extends this with ZK presentation (prove you hold a valid macaroon without revealing it).

4. **Mina Protocol** (O(1) Labs). The recursive-SNARK L1 blockchain. Pyana adapts Mina's execution model (accounts/cells, zkApp commands/turns, call forests) for authorization rather than financial state transitions.

5. **Poseidon2** (Grassi et al.). SNARK-friendly hash function used in pyana's in-circuit Merkle operations. Enables proving Merkle membership inside the STARK without expensive bit-decomposition.

6. **FRI: Fast Reed-Solomon IOP of Proximity** (Ben-Sasson et al.). The low-degree test at the core of pyana's STARK proof system. Hash-based (no trusted setup, PQ-secure).

7. **Biscuit: Authorization Tokens with Decentralized Verification** (Sonntag). Ed25519 + Datalog policy language. Pyana uses Biscuit as an alternative token backend alongside macaroons.

8. **BLS12-381** (Bowe). The pairing-friendly curve used for threshold signatures in federation quorum certificates. Inside trust boundary only; PQ migration planned.

---

## Contributing

The codebase is at `github.com/pyana-dev/breadstuffs`. Priority work items:

1. ~~Fix the 8 critical audit findings~~ (7/8 DONE, see AUDIT-FINDINGS.md)
2. Unify the Merkle systems (Poseidon2 end-to-end for provable path)
3. Complete bridge integration (remaining test failures)
4. Wire federation consensus into the TCP protocol
5. Recursive STARK-in-STARK for constant-size IVC proofs
6. Fix BabyBear field (currently Mersenne prime 2^31-1, should be 2^31-2^27+1 for NTT support)
7. Cache Poseidon2 round constants (trivial but high-impact performance fix)

License: MIT OR Apache-2.0.
