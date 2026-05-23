// =============================================================================
// Section 2: System Model
// =============================================================================

= System Model

== Cells

A _cell_ is the fundamental unit of isolated state, analogous to a Mina zkApp account or an E object. Each cell holds:

- A content-addressed identity $"CellId" in {0,1}^(256)$.
- Mutable state: 8 generic field slots $s_0, ..., s_7 in FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear prime).
- A _capability list_ (c-list): the set of capabilities the cell may exercise.
- Permission requirements specifying what authorization kind is needed for each action type.
- An optional verification key for ZK proof validation.

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

=== Sovereign Cells

Cells are _sovereign_ by default: the federation stores only a 32-byte state commitment per cell, not the cell's full state. The cell's owner maintains full state locally and proves state transitions via STARK proofs. Sovereignty provides:

- *Self-custody of state*: The agent controls its own data; the federation cannot inspect or withhold cell contents.
- *On-demand federation interaction*: Sovereign cells register with a federation to participate in ordering (nullifier publication, discovery), and deregister when they no longer need it.
- *Peer-to-peer operation*: Two sovereign cells can interact directly via STARK proofs without requiring any federation round-trip, provided they share a recent root for freshness anchoring.
- *TTL-based registration*: Sovereign registrations carry a time-to-live. The federation garbage-collects expired registrations without explicit deregistration.

A cell transitions from sovereign to hosted (federation stores full state) by submitting its current state. The reverse transition---hosted to sovereign---requires proving current state ownership and extracting a commitment.

=== Faceted Capabilities and EffectMask

Each capability carries an _EffectMask_---a 32-bit bitmask of permitted effects (set field, transfer, grant capability, revoke, emit event, create cell, seal, bridge, introduce, etc.). Delegation can only _narrow_ the mask (bitwise AND with the parent's mask), enforcing monotonic attenuation at the effect level. This provides fine-grained control beyond predicate-based attenuation:

$ "EffectMask"_"child" = "EffectMask"_"parent" & "mask"_"delegation" $

The narrowing invariant is enforced both by the runtime (for trusted-mode evaluation) and provable in zero knowledge (for STARK presentations).

=== Bearer Capabilities

In addition to c-list-mediated capabilities, Pyana supports _bearer capabilities_: tokens that grant authority immediately upon presentation, without requiring storage in the recipient's c-list. Bearer capabilities follow E-semantics for immediate grants---useful for one-shot authorizations, tickets, and ephemeral access tokens. A bearer capability is consumed on exercise; it does not persist in any c-list.

== Turns

A _turn_ is an atomic transaction over one or more cells, analogous to a Mina ZkappCommand or an E turn. A turn contains:

- A _call forest_: a tree of actions, executed depth-first.
- A fee (in computrons) covering execution cost.
- A nonce (monotonically increasing per cell) for replay protection.
- Authorization: Ed25519 signature, ZK proof, or both.

If any action in the call forest fails, all effects are rolled back via journal replay. This provides atomicity.

== Silos and Federations

A _silo_ is a node that participates in federation consensus, verifies proofs, and anchors state roots. For hosted cells, a silo stores full state; for sovereign cells (the default), it stores only the 32-byte commitment. A _federation_ is a committee of 1--64 silos sharing a trust root. Federation members run the Blocklace @blocklace protocol with Cordial Miners $tau$ for total ordering, achieving 3-round BFT finality under the standard $< n\/3$ Byzantine assumption. Constitutional Consensus governs membership changes (democratic admission via h-rule, timeout-leave for inactive nodes).

The federation's role is deliberately minimal: ordering, nullifier deduplication, root anchoring, and discovery. It is NOT an execution layer for sovereign cells---verification only. Sovereign cells prove their own state transitions; the federation merely attests that proofs were valid at a given height. The system operates in three tiers: sovereign execution (no federation), optimistic coordination (Stingray bounded counters), and ordered consensus (Cordial Miners)---agents escalate only when needed.

== EROS-Style Factories

A _factory_ is a cell program that constrains what new cells it can create. Inspired by EROS's constructor transparency @eros, a factory publishes a `FactoryDescriptor` that is the complete constructor contract---anyone can inspect exactly what capabilities the factory grants to its creations, what verification keys they will use, and what initial state they receive.

Factory-created cells have _computable child verification keys_:

- *Fixed*: Every child uses the same VK (the factory's own).
- *Derived*: Child VK is deterministically computed from factory VK and creation parameters: $"child_vk" = "BLAKE3"("pyana-derived-child-vk" || "factory_vk" || "param_hash")$.
- *FromSet*: Child VK must be a member of a pre-approved set.

Factory creation is a composable effect within atomic turns---enabling flash-loan-style patterns where a factory spawns a child cell, the child performs work, and the parent observes the result, all within a single atomic turn with journal-based rollback on failure. Provenance tracking records which factory created each cell, enabling machine-auditable supply chains of cell construction.

== Trust Assumptions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, center),
    table.header([*Layer*], [*Assumption*], [*PQ?*]),
    [External proofs (STARKs)], [Collision-resistant hash], [Yes],
    [Merkle commitments], [Collision-resistant hash], [Yes],
    [Macaroon HMAC chain], [PRF security of HMAC-SHA256], [Yes],
    [Federation QCs (BLS12-381)], [Bilinear DH in $GG_1 times GG_2$], [No],
    [Node identity (Ed25519)], [DLP in twisted Edwards], [No],
    [Sealed secrets (X25519)], [CDH in Curve25519], [No],
  ),
  caption: [Trust assumptions by layer. Items marked "No" are confined within federation trust boundaries.],
)

The critical invariant: *everything that crosses a trust boundary is post-quantum secure*. Classical cryptography exists only between parties that already trust each other.

== Execution Model

=== Pipeline Execution with Topological Ordering

The executor processes turns not only individually but in _pipelines_: batches of turns with declared dependency edges. A pipeline $P = (T, E)$ where $T = {t_0, ..., t_n}$ and $E subset.eq T times T$ is a DAG of dependency edges. The executor computes a topological ordering and processes turns in causal order. If turn $t_i$ fails and $t_j$ depends on $t_i$, then $t_j$ receives a `DependencyFailed` error without executing.

=== BudgetGate Integration

Every turn pays a fee in _computrons_. The executor integrates Stingray @stingray bounded counters directly: each silo holds a local budget slice $"slice"(i) = "balance" dot (f+1)/(2f+1)$ and debits locally without coordination until exhaustion. The executor checks $"fee" <= "remaining"$ before execution (fail-fast) and debits atomically upon commit. Budget accounting uses checked arithmetic throughout---overflow produces an executor error, never wraps.

=== Conservation Invariant

For any turn $t$ with actions $a_1, ..., a_k$, the executor enforces:

$ sum_i "balance_change"(a_i) + "fee"(t) = 0 $

Value cannot be created or destroyed within a turn. The fee is debited from the agent cell and does not reappear---it is the cost of execution.

== E-Style Distributed Object Semantics

=== EventualRef and Promise Pipelining

In E @elang, a message send returns a _promise_ that resolves when the target processes the message. Multiple messages can be sent to the resolution of a pending promise without waiting for it to resolve---_promise pipelining_ eliminates round-trip latency in distributed object protocols.

Pyana implements this via `EventualRef`: a reference to the output of a pending turn, identified by the turn's hash and an output slot index. A turn may target an `EventualRef` rather than a concrete `CellId`, declaring a dependency that the executor resolves during pipeline execution. The `Target` type is a sum:

$ "Target" = "Concrete"("CellId") | "Eventual"("source_turn": ["u8"; 32], "slot": "u32") $

When the source turn commits, its outputs (granted capabilities, created cells, state updates) populate a resolution table. Dependent turns rewrite their `EventualRef` targets to concrete `CellId` values before execution.

=== Three-Party Introduction

Object-capability systems form new communication paths through _introductions_: Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by granting Bob a (possibly attenuated) capability to Carol. In Pyana, an `Effect::Introduce` during a turn emits a `RoutingDirective`:

$ "RoutingDirective" = ("sender": "CellId", "target": "CellId", "authorizing_turn": ["u8"; 32], "expires": "Option"("u64")) $

The node's routing table is populated from these directives. No global directory exists---all communication paths are introduced, not discovered.

=== Comparison with E and Cap'n Proto

E's promise pipelining requires a live vat (process) hosting the target object. Cap'n Proto @capnproto extends this to RPC with three-party handoff across address spaces, but within a single trust domain. Pyana differs in three respects:

+ *Proof-carrying*: A pipelined message carries (or can generate) a STARK proof that the sender is authorized to invoke the target. No live vat is needed to check authorization---verification is offline.
+ *Asynchronous, no blocking IPC*: Pipelines are submitted as batches with explicit dependency DAGs. There is no synchronous call semantics.
+ *Privacy*: The introduction graph is private to the parties involved. A routing directive is visible only to the node executing the turn and the introduced parties.
