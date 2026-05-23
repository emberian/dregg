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

== Capability Transport Protocol (CapTP) <sec-captp>

CapTP is the wire-level protocol for distributed capability invocation. It extends Cap'n Proto's three-party handoff with store-and-forward semantics and provable effects:

=== Sturdy References

A _sturdy ref_ is a serializable, revocable capability reference that survives network partition and process restart. Unlike live references (which require the target vat to be reachable), sturdy refs are self-contained: they encode the target cell, a Swiss number (unforgeable designator), and an optional routing hint. Resolution proceeds:

+ Holder presents the sturdy ref to any node in the target's federation.
+ The node verifies the Swiss number against the target cell's c-list.
+ A live reference is returned (or an error if revoked / expired).

Sturdy refs are the persistence boundary: they survive serialization to disk, transmission via sealed boxes, and federation restarts. Live refs exist only within an active session.

=== Distributed Garbage Collection

CapTP implements distributed reference counting with three mechanisms:

- *Export/import tables*: Each CapTP session maintains tables mapping local capabilities to remote proxies. When a remote proxy is dropped, the exporter is notified.
- *Weak references with liveness probes*: For long-lived capabilities crossing federation boundaries, weak refs avoid preventing GC. Periodic liveness probes detect unreachable targets.
- *Third-party handoff*: When Alice introduces Bob to Carol, the handoff transfers the export entry directly---Alice's export table entry is replaced by a direct Bob-Carol binding, and Alice's reference count decrements.

=== Pipelining and Store-and-Forward

CapTP messages to offline targets are queued in _MerkleQueue inboxes_ (see @sec-storage-economics). The sender pays a deposit proportional to message size and TTL. Messages are delivered in causal order when the target becomes reachable. Pipeline messages (targeting an `EventualRef`) are queued against the resolution---when the promise resolves, queued messages are delivered without additional round-trips.

=== Provable Effects in CapTP

Four CapTP operations are encoded as provable Effect VM effects:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*CapTP Operation*], [*Effect VM Effect*], [*What the STARK Proves*]),
    [Send (invoke remote)], [Invoke], [Sender held authority for this invocation at send-time],
    [Introduce (3-party)], [Introduce], [Introducer held caps to both parties; attenuation is monotonic],
    [Grant (delegate cap)], [GrantCapability], [Granted cap is a valid attenuation of grantor's cap],
    [Handoff (transfer export)], [Transfer], [Export entry moved atomically; no duplication],
  ),
  caption: [CapTP operations as provable effects. Each operation produces a STARK proof checkable offline.],
)

=== Comparison with Cap'n Proto RPC

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Property*], [*Cap'n Proto*], [*Pyana CapTP*]),
    [Trust domain], [Single (shared secret)], [Cross-federation (ZK proofs)],
    [Offline targets], [Error], [Store-and-forward (MerkleQueue)],
    [Persistence], [No (live refs only)], [Sturdy refs survive restart],
    [GC], [Reference counting], [Distributed RC + weak refs + handoff],
    [Verifiability], [None (trusted transport)], [STARK proof per operation],
    [Privacy], [None], [Zero-knowledge (verifier learns only conclusion)],
  ),
  caption: [CapTP extends Cap'n Proto RPC to the trustless, partition-tolerant, privacy-preserving setting.],
)

== DFA Routing and Governed Namespaces <sec-dfa-routing>

=== URL-Style Capability Addresses

Capabilities are addressed via a URL-style path scheme: `federation://namespace/service/action`. Each path segment is classified by a deterministic finite automaton (DFA) that enforces governance rules. The DFA state machine is compiled from a constitutional rule set and proved in-circuit via STARK lookup tables.

=== DFA Classification

A _route classifier_ is a DFA with states $Q$, alphabet $Sigma$ (path characters), transition function $delta: Q times Sigma -> Q$, start state $q_0$, and accept states $F subset.eq Q$. Classification proceeds:

$ "classify"("path") = cases("Accept"("policy") & "if" delta^*("path") in F, "Reject" & "otherwise") $

The STARK proves correct DFA evaluation via lookup tables: each $(q_i, c_i, q_(i+1))$ transition is checked against a committed transition table. The proof size is $O(|"path"|)$ rows with constant-width columns.

=== Constitutional Amendment

Governance rules (which namespaces exist, who can mount services, ACL policies) are encoded in the DFA's transition table. Amendments follow the federation's Constitutional Consensus:

+ A member proposes a new DFA transition table (adding/removing routes).
+ $h$ members must reference the proposal in their blocks (same h-rule as membership).
+ On acceptance, the new DFA table is committed and its hash becomes part of the attested root.
+ Existing capabilities referencing removed routes become invalid at the next epoch boundary.

=== DFA-Based Access Control Lists

Each accept state in the DFA carries an ACL policy: a set of cell IDs (or capability predicates) permitted to invoke that route. The classifier proof demonstrates both "this path is well-formed" AND "the invoker satisfies the route's ACL." This replaces traditional string-matching ACLs with a provable, governance-amendable policy engine.

== Service Mesh <sec-service-mesh>

The service mesh is a governed namespace acting as a capability registry. It provides mount/discover/resolve semantics for services within a federation.

=== Mounting Services

A cell _mounts_ a service at a namespace path by presenting:

+ A capability proving authority to mount at that path (DFA-classified, ACL-checked).
+ A `ServiceDescriptor` specifying the service's interface (accepted effect types, required capabilities, pricing).
+ An optional verification key for callers to verify the service's responses.

Mounting is an atomic turn effect (`Effect::Mount`) that updates the federation's service registry---a Merkle-committed map from paths to `ServiceDescriptor` entries.

=== Discovery

Service discovery uses three mechanisms:

- *Direct resolution*: Given a full path, resolve to the mounted cell and descriptor in $O(log n)$ via Merkle lookup.
- *Prefix enumeration*: Given a namespace prefix, enumerate all services mounted under it (governance-gated: enumeration requires a read capability on the prefix).
- *Intent-based discovery*: Broadcast a need ("I require a service matching spec $S$") via the intent marketplace. Services self-identify privately via STARK proof.

=== Resolution Protocol

Resolution is a two-phase lookup:

+ *Route classification*: The DFA classifier proves the path is well-formed and the invoker satisfies the ACL.
+ *Service binding*: The registry returns the mounted cell's sturdy ref (CapTP) and service descriptor. The caller now has a live capability to the service.

The entire resolution is a single turn (atomic, journal-rollback on failure). Failed resolution does not leak which services exist---the DFA classifier rejects invalid paths without distinguishing "path exists but unauthorized" from "path does not exist."

== Nameservice <sec-nameservice>

=== Petname Architecture

Pyana's nameservice follows the petname model: names are always relative to the namer, never globally authoritative.

- *Petnames* (local): Private, per-agent mappings from human-readable strings to cell IDs. Stored in the agent's sealed state. Never published.
- *Edge names*: Names that one agent publishes about another (e.g., "Alice calls Bob 'my-accountant'"). Visible to third parties who query Alice's directory.
- *Proposed names*: Names that a cell proposes for itself (self-description). Advisory only---never authoritative.

=== Hierarchical Resolution

Names resolve hierarchically through delegation:

$ "resolve"("alice/contacts/bob") = "alice"."edge_names"["contacts/bob"] $

Sub-delegation creates paths: Alice delegates naming authority for `alice/services/*` to a registry cell. The registry can create edge names under that prefix without Alice's per-name approval.

=== Rental and Dispute

Namespace paths under governed prefixes may be rented:

- *Rental*: A cell pays a per-epoch fee (computrons) to hold a name. Non-payment triggers release after a grace period.
- *Dispute*: If two cells claim the same proposed name, the DFA governance process adjudicates. Constitutional amendment can reassign contested names.
- *Sub-delegation*: A name holder can sub-delegate portions of their namespace (e.g., `example.pyana/` holder delegates `example.pyana/api/` to a service cell).

== Cell Migration and Teleportation <sec-cell-migration>

=== Teleportation Between Federations

A sovereign cell can _teleport_ from federation A to federation B:

+ Cell deregisters from federation A (publishes final commitment + IVC proof).
+ Cell registers with federation B (presents IVC proof as genesis state).
+ Federation B verifies the IVC proof covers valid history from genesis.
+ Cell is now sovereign under federation B's ordering service.

The IVC proof carries the cell's entire history in constant size. No state is lost. The cell's identity ($"CellId"$) is unchanged---only the ordering service changes.

=== Vat Splitting and Merging

Complex agents may split into multiple cells or merge:

- *Splitting*: A cell spawns $N$ child cells via factory, partitions its state across them, and proves (via STARK) that the partition is complete and non-overlapping. The parent cell's commitment becomes the Merkle root of the children's commitments.
- *Merging*: $N$ cells with the same owner combine their state into a single cell. A STARK proves that the merged state is the union of the children's states, with conservation (no value created/destroyed in the merge).

=== Fluid Trust Boundaries

Trust boundaries are not static. A cell that begins sovereign under federation A may:

+ Teleport to federation B (different ordering service, different trust assumptions).
+ Split across federations (child cells in different federations, parent tracks them via IVC).
+ Merge with cells from other federations (requires cross-federation atomic coordination).

The IVC proof ensures continuity: regardless of how many times a cell teleports, splits, or merges, its verifiable history is a single constant-size proof from genesis.

== Deep Garbage Collection and State Lifecycle <sec-deep-gc>

=== State Lifecycle Phases

Every cell follows a four-phase lifecycle:

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Phase*], [*Condition*], [*Storage*], [*Behavior*]),
    [Birth], [Factory creation or genesis], [Full state], [Active participant],
    [Active], [Recent turn within TTL], [Commitment (sovereign) or full (hosted)], [Normal operation],
    [Decay], [No turn for $>$ TTL, storage rent unpaid], [Commitment only (frozen)], [Cannot execute turns; can pay rent to reactivate],
    [Forced Sovereignty], [Decay exceeds grace period], [Ejected from federation], [Must self-host or lose state],
  ),
  caption: [Cell lifecycle phases. Decay is reversible (pay rent); forced sovereignty is permanent ejection from hosted state.],
)

=== Storage Rent

Hosted cells (federation stores full state) pay storage rent proportional to their state size:

$ "rent"_"epoch" = "state_size_bytes" times "rent_rate_per_byte" $

The rent rate is governance-adjustable. Rent is deducted automatically at epoch boundaries from the cell's computron balance. If balance is insufficient, the cell enters Decay. Sovereign cells (32-byte commitment only) pay a fixed minimal fee regardless of actual state size---the federation stores only the commitment.

=== Epoch Rotation

The GC cycle runs at epoch boundaries (governance-configurable, typically every 1000 blocks):

+ Enumerate all hosted cells with $"balance" < "rent_owed"$.
+ Transition insufficient-balance cells to Decay (freeze state, stop accepting turns).
+ Enumerate all Decay cells with $"decay_duration" > "grace_period"$.
+ Force-sovereignty expired cells: delete state from federation storage, retain only commitment.
+ Prune expired sovereign registrations (TTL exceeded, no renewal).

Forced sovereignty is not state deletion---the cell's owner retains their IVC proof and can re-register at any time by presenting it. The federation merely stops hosting the state.
