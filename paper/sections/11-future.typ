// =============================================================================
// Section 11: Future Work
// =============================================================================

= Future Work

== Recursive Proof Composition

Recursive verification is operational for pairs of proofs (verified via Plonky3) and sequential IVC chains (`build_recursive_ivc_chain`). STARK-in-Pickles wrapping produces constant-size recursive SNARKs for Mina-compatible verification. The remaining work is composing heterogeneous AIRs (derivation + fold + membership + Effect VM) in a single recursive proof. The DSL composition operators (`compose_chain`, `compose_aggregate`) provide the structural framework; the circuit-level integration for arbitrary AIR widths is the primary remaining proof-system work.

== Full Privacy Pipeline

The privacy migration (Section 5) proceeds through six phases. The most impactful near-term change---removing `final_root` from public inputs and replacing it with a blinded presentation tag---provides full unlinkability with minimal circuit additions. The unified recursive proof (Phase 4) eliminates structural information leakage from the multi-proof composition.

== Federation Privacy

Encrypted turn ordering (Section 6) requires either threshold decryption ceremonies or full validity proofs for every turn. The recommended intermediate step is validium-style blind ordering: Bloom filter conflict sets for parallelism detection, lightweight STARKs for nonce/fee validity, and threshold decryption after ordering. Full elimination of decryption (Layer 3) requires encoding conservation and authorization verification in the validity AIR.

== Multi-Hop Gossip

Gossip is currently one-hop for cross-silo dissemination. Multi-hop Plumtree forwarding and Dandelion++ stem routing are implemented for transaction privacy, but cross-silo multi-hop gossip for block propagation is not yet wired between federation nodes. The protocol exists; the integration is pending.

== Formal Verification

seL4's claim to fame is formal verification. Pyana's path:
- STARK proof system provides computational soundness (cheating is exponentially unlikely)
- Capability model is formally expressible (Datalog policies are decidable)
- Conservation invariant is checked by the executor
- Open: formal model of the full system (federation + cells + turns + proofs) in a proof assistant
- Possible: extract the executor's critical path into a verified implementation

== Agent Standard Library

Common patterns that could become protocol-level primitives:
- Request/response (turn + EventualRef)
- Publish/subscribe (intent + routing directive)
- Task queue (intent pool + fulfillment)
- Auction (competitive intent fulfillment with bond comparison)
- Escrow (conditional turn with timeout)
- Reputation oracle (receipt chain aggregation service)

== Proof System Performance

Current targets for agent-scale operation:
- Sub-10ms proof generation for simple authority checks (latency-sensitive coordination)
- Sub-1 KiB proofs for bandwidth-constrained gossip (Binius backend may deliver this)
- Full heterogeneous recursive composition for constant-size multi-capability proofs
- Hardware acceleration (GPU/FPGA proving for throughput)
- Effect VM optimization: batch proving multiple turns in a single trace (amortized cost)

== EVM Bridge Maturation

The SP1-based EVM bridge is architecturally complete but the guest program requires regeneration against the current Plonky3 backend. Remaining work:
- Regenerate SP1 guest ELF against Plonky3 STARK verifier
- Deploy VK registry contract with governance (multisig parameter updates)
- Production incremental Merkle tree for deposits
- Gas optimization for the on-chain verification path
- Cross-chain message passing (Base $arrow.r$ Pyana deposit confirmations)

== Post-Quantum Migration

The STARK path is post-quantum today. Classical components have a staged migration: BLS12-381 threshold signatures $arrow.r$ lattice threshold (awaiting standardization), Ed25519 $arrow.r$ ML-DSA, X25519 $arrow.r$ ML-KEM. These migrations are confined within federation trust boundaries and can be executed per-federation without protocol-wide coordination.

== Open Questions

- *Genesis ceremony design*: How is authority bootstrapped without a single root of trust?
- *Shared mutable state*: How do agents share state that multiple parties can read/write?
- *Heterogeneous agents*: Human-in-the-loop, deterministic services, IoT devices, cross-federation agents
- *Federation scaling*: For very large committees (N > 100), committee-sampling approaches
- *Treasury governance*: Voting mechanism for treasury spending (deferred to governance design)
