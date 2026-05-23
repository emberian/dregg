// =============================================================================
// Section 10: Related Work and Comparison
// =============================================================================

= Related Work and Comparison

== Mina Protocol

*Mina Protocol* @mina. Pyana's execution model (cells $equiv$ accounts, turns $equiv$ ZkappCommands, call forests) derives from Mina. The key divergences: Pyana manages authorization state with federated BFT rather than global Ouroboros, implements distributed object semantics absent from Mina, carries state as proof chains rather than compressing a global ledger, and provides capability-based authority rather than address-based access control.

== seL4

*seL4* @sel4. seL4's CDT is the gold standard for capability revocation: kernel-enforced, synchronous, formally verified. Pyana's CDT is the distributed dual---replacing kernel authority with cryptographic proof, synchronous traversal with bounded-staleness snapshots, and single-machine scope with cross-federation reach. The tradeoff is revocation latency for distribution.

The correspondence runs deep: cells are processes, c-lists are CNodes, turns are IPC, receipt chains are execution traces, the federation is the kernel. But the key insight is architectural, not merely analogical: any security invariant maintained synchronously by a kernel can be maintained asynchronously by a proof system, trading latency for distribution.

== Cap'n Proto

*Cap'n Proto* @capnproto. Cap'n Proto provides the closest existing implementation of E-style promise pipelining in production. Pyana extends the model with: ZK-private authorization at each pipeline step, offline verification (no live vat needed), and proof that the pipeline was authorized without revealing the capability chain. Cap'n Proto operates within a single trust domain; Pyana operates across trust boundaries.

== Anonymous Credentials

*Idemix/BBS+/Coconut* @coconut. These systems provide attribute-based anonymous credentials with selective disclosure. Pyana differs in three fundamental ways: (1) it supports full delegation/attenuation semantics (not just "has attribute X" but "can do Y on Z, delegated from A through B"), (2) it achieves issuer anonymity within a ring (no existing anonymous credential system provides this), and (3) it is post-quantum via STARKs rather than relying on bilinear pairings. The tradeoff: larger proofs ($tilde$48--80 KiB vs 1--5 KiB) and slower generation ($tilde$200--500ms vs 10--100ms).

== Blockchain Systems

=== Ethereum

Ethereum achieves global consensus over shared state. Pyana differs fundamentally: local autonomy with federated coordination, private by default (ZK proofs for verification), isolated cells rather than global shared state, and portable proof-carrying state (no lock-in). An AI agent does not need the entire world to agree on its state---it needs to prove its state to specific counterparties.

=== Cosmos/IBC

*Cosmos* @ibc provides inter-chain communication via light client verification. Pyana's cross-federation protocol is analogous but uses STARK proofs rather than light clients for cross-domain verification. Pyana's federations are smaller and purpose-built (3--20 nodes vs 100+), non-inflationary, and privacy-preserving.

=== Midnight

*Midnight* @midnight. Privacy-focused blockchain using Plonk proofs. Unlike Pyana, Midnight targets DeFi, requires chain liveness, and lacks capability delegation semantics. Midnight provides privacy for _transactions_; Pyana provides privacy for _authority_ (who delegated what to whom). Pyana's DSL includes a ZKIR v3 backend that compiles constraint programs to Midnight-compatible contracts, enabling observation-based bridging (the same pattern used for Midnight-Cardano interop). This is not a consensus bridge---it is a proof-translation layer that allows a Midnight contract to verify Pyana state transitions natively.

=== Zcash

Zcash pioneered shielded transactions with SNARK proofs. Pyana adapts the note/nullifier model (Poseidon2 commitments, spending proofs, non-membership) but extends it to capability delegation. Zcash proves "I can spend this value"; Pyana proves "I am authorized to perform this action, via a delegation chain I won't reveal."

== Authorization Systems

=== UCAN

*UCAN* @ucan. Correct delegation semantics (attenuation, invocation) but transparent chains. Pyana proves the same relationship without revealing intermediate authorities. UCANs require the verifier to see the full chain; Pyana's verifier sees only a conclusion bit and a proof.

=== Google Macaroons

*Macaroons* @macaroons. HMAC-chained bearer tokens with contextual caveats. Pyana uses macaroons as the encoding format for capability tokens; the contribution is proving properties of the chain in zero knowledge rather than presenting the chain itself.

=== Biscuit

*Biscuit* @biscuit. Datalog-based authorization tokens with offline verification. Closest to Pyana's authorization semantics (both use Datalog). Biscuit lacks: zero-knowledge presentation, distributed delegation tracking, economic model, and proof-carrying state.

== Distributed Systems

=== Stingray

*Stingray* @stingray. Bounded counters for BFT payment channels. Pyana adapts the split-balance formula directly for concurrent resource budgets across silos. The key innovation from Stingray: local operation without coordination is safe even under Byzantine faults, with periodic rebalancing.

=== E Language

*E* @elang. E's distributed object semantics---promise pipelining, three-party introduction, sealer/unsealer pairs---form the communication model's foundation. Pyana extends E's model to the trustless setting: proofs where E uses live vats, cryptography where E uses confinement within a single runtime.

== Summary of Positioning

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, center, center, center, center),
    table.header([*Property*], [*Pyana*], [*Ethereum*], [*Zcash*], [*seL4*]),
    [Privacy], [Full ZK], [Transparent], [Shielded tx], [N/A],
    [Delegation], [Full CDT], [None], [None], [Full CDT],
    [Distribution], [Federated], [Global], [Global], [Single machine],
    [Offline verify], [Yes], [No], [No], [N/A],
    [Post-quantum], [STARK path], [No], [No (SNARKs)], [N/A],
    [Authority model], [Capability], [Address], [Address], [Capability],
    [Economic model], [Federated], [PoS global], [PoW global], [N/A],
    [Agent support], [Native], [Smart contracts], [None], [Processes],
    [Sovereign state], [Yes (default)], [No (global)], [No (global)], [No (kernel)],
    [Multi-backend proofs], [8 backends], [1 (EVM)], [1 (Groth16)], [N/A],
    [EVM interop], [SP1/Groth16], [Native], [No], [N/A],
  ),
  caption: [System positioning. Pyana combines capability-based authority with zero-knowledge privacy, sovereign state ownership, and federated distribution.],
)
