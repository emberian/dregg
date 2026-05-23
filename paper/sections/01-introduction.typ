// =============================================================================
// Section 1: Introduction
// =============================================================================

= Introduction

Cross-domain authorization for autonomous agents presents a challenge that existing systems address incompletely. Consider an AI agent dispatched by Organization A to invoke a service hosted by Organization B. The agent must prove it is authorized---but without revealing Organization A's internal delegation structure, the identities of intermediate signatories, or what other capabilities the agent holds.

Existing approaches each fail along a different axis:

- *UCAN/ZCAP-LD* @ucan provide delegation chains but require revealing the full chain to the verifier. Privacy is absent.
- *Coconut credentials* @coconut offer selective disclosure of attributes but lack the delegation semantics needed for capability attenuation.
- *Cap'n Proto RPC* provides promise pipelining and E-style messaging but operates within a single trust domain with no privacy, no proof of authorization, and no offline verification.
- *Blockchain-based authorization* achieves transparency but requires chain liveness, incurs gas costs, and exposes all authorization state on-chain.
- *seL4* @sel4 provides a rigorous Capability Derivation Tree with synchronous kernel-enforced revocation, but requires a single address space and cannot distribute across trust boundaries.

Pyana's contributions span five architectural layers:

*Authorization and Privacy:* (1) proving monotonic attenuation of a bearer token chain in zero knowledge with backend-agnostic commitment; (2) a distributed CDT that replaces kernel enforcement with cryptographic proof; (3) faceted and bearer capabilities extending E-semantics to fine-grained effect control; (4) a privacy-preserving intent marketplace for capability discovery.

*Distributed Object Runtime:* (5) E-style messaging semantics (promise pipelining, three-party introduction) integrated with proof-carrying state; (6) sovereign cells that own their state while using the federation as a notary, not a host; (7) EROS-style factories for constrained cell creation with machine-auditable constructor transparency; (8) a Capability Transport Protocol (CapTP) with sturdy refs, distributed GC, three-party handoff, store-and-forward, and 4 provable effects in the Effect VM.

*Unified Fabric:* (9) emergent federations as reference groups over a shared blocklace with three governance modes (constitutional, open, invite-only); (10) interest-based dissemination with subscription-filtered block propagation; (11) strand-based addressing replacing federation-scoped routing; (12) DFA-based governable routing with constitutional amendment and STARK-proved classification; (13) a service mesh with governed namespaces, mount/discover/resolve semantics, and petname-based nameservice.

*Proof System:* (14) a backend-agnostic constraint DSL compiling circuit specifications to 8 target proof systems from a single source; (15) an Effect VM proving arbitrary turns in one STARK; (16) a typed composition checker with 30-circuit catalog, 11 cryptographic guarantees, and 7 explicit trust assumptions; (17) cross-chain bridges via proof translation---EVM (SP1/Groth16, $tilde$200K gas), Mina (native Pickles recursion), and Midnight (optimistic with dispute window).

*Economics and Agents:* (18) storage economics with space banks, MerkleQueue inboxes, blinded queues, programmable queue pipelines, and erasure coding; (19) a trustless 7-layer intent solving protocol with threshold encryption, open solver competition, STARK-proved solutions, and ring trade discovery; (20) executor delegation with batch proving, challenge protocols, and a trust spectrum from full sovereignty to delegated execution; (21) an economic model for federated validation with privacy-compatible staking; (22) an AI agent coordination substrate built on capability-based authority; (23) cell migration with IVC proof continuity; and (24) deep garbage collection with state lifecycle phases, storage rent, and epoch rotation.

The design draws from Mina Protocol's execution model (cells as zkApp accounts, turns as ZkappCommands, call forests), E's distributed object semantics (eventual sends, three-party handoff, sealer/unsealer pairs), seL4's capability derivation (recast as a proof structure for asynchronous distributed systems), EROS's factory pattern (constrained constructors with auditable verification keys), and Stingray's bounded counters for BFT budget channels.
